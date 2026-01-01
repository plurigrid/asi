#!/usr/bin/env python3
"""
Zig Version Detection Script

Detects the Zig compiler version using multiple strategies:
1. Runtime detection via `zig version` command
2. Static analysis of build.zig for API patterns
3. Parsing build.zig.zon for minimum_zig_version
4. Scanning source files for syntax markers

Usage:
    python detect_version.py [--dir <project_directory>] [--verbose]

Output:
    JSON with detected version, confidence level, and detection source
    Example: {"version": "0.15.2", "confidence": "high", "source": "zig_command"}
"""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, Optional, Tuple


class ZigVersionDetector:
    """Detects Zig version using multiple strategies."""

    # Supported versions for reference
    SUPPORTED_VERSIONS = [
        '0.2.0', '0.3.0', '0.6.0', '0.7.1', '0.8.1',
        '0.9.1', '0.10.1', '0.11.0', '0.12.1',
        '0.13.0', '0.14.1', '0.15.2', 'master'
    ]

    # Detection confidence levels
    CONFIDENCE_HIGH = "high"      # From zig version command or explicit specification
    CONFIDENCE_MEDIUM = "medium"  # From multiple code markers
    CONFIDENCE_LOW = "low"        # From single marker or heuristic

    def __init__(self, project_dir: Path, verbose: bool = False):
        self.project_dir = project_dir
        self.verbose = verbose

    def log(self, message: str):
        """Print verbose logging messages."""
        if self.verbose:
            print(f"[DEBUG] {message}", file=sys.stderr)

    def detect(self) -> Dict[str, str]:
        """
        Run all detection strategies in order of reliability.
        Returns: dict with version, confidence, and source
        """
        # Strategy 1: Runtime detection
        result = self._detect_from_command()
        if result:
            return result

        # Strategy 2: Check build.zig.zon
        result = self._detect_from_build_zon()
        if result:
            return result

        # Strategy 3: Static analysis of build.zig
        result = self._detect_from_build_zig()
        if result:
            return result

        # Strategy 4: Scan source files for syntax markers
        result = self._detect_from_source_files()
        if result:
            return result

        # Default fallback
        self.log("No version detected, defaulting to 0.15.2")
        return {
            "version": "0.15.2",
            "confidence": self.CONFIDENCE_LOW,
            "source": "default",
            "note": "No detection markers found, using current stable version"
        }

    def _detect_from_command(self) -> Optional[Dict[str, str]]:
        """Try to run `zig version` command."""
        try:
            self.log("Attempting to run 'zig version' command")
            result = subprocess.run(
                ["zig", "version"],
                capture_output=True,
                text=True,
                timeout=5
            )

            if result.returncode == 0:
                version = result.stdout.strip()
                self.log(f"Found version from command: {version}")
                return {
                    "version": version,
                    "confidence": self.CONFIDENCE_HIGH,
                    "source": "zig_command"
                }
        except FileNotFoundError:
            self.log("zig command not found in PATH")
        except subprocess.TimeoutExpired:
            self.log("zig version command timed out")
        except Exception as e:
            self.log(f"Error running zig version: {e}")

        return None

    def _detect_from_build_zon(self) -> Optional[Dict[str, str]]:
        """Check build.zig.zon for minimum_zig_version."""
        build_zon_path = self.project_dir / "build.zig.zon"

        if not build_zon_path.exists():
            self.log("No build.zig.zon found")
            return None

        try:
            self.log(f"Reading {build_zon_path}")
            content = build_zon_path.read_text()

            # Look for .minimum_zig_version = "X.Y.Z"
            match = re.search(r'\.minimum_zig_version\s*=\s*"([^"]+)"', content)
            if match:
                version = match.group(1)
                self.log(f"Found minimum_zig_version: {version}")
                return {
                    "version": version,
                    "confidence": self.CONFIDENCE_HIGH,
                    "source": "build.zig.zon",
                    "note": "This is the minimum version, actual version may be newer"
                }
        except Exception as e:
            self.log(f"Error reading build.zig.zon: {e}")

        return None

    def _detect_from_build_zig(self) -> Optional[Dict[str, str]]:
        """Analyze build.zig for API patterns."""
        build_zig_path = self.project_dir / "build.zig"

        if not build_zig_path.exists():
            self.log("No build.zig found")
            return None

        try:
            self.log(f"Analyzing {build_zig_path}")
            content = build_zig_path.read_text()

            # Modern API markers (0.11+)
            has_std_build = bool(re.search(r'\bstd\.Build\b', content))
            has_b_path = bool(re.search(r'\bb\.path\(', content))
            has_struct_literal_add = bool(re.search(r'addExecutable\(\.\{', content))

            # Legacy API markers (pre-0.11)
            has_std_build_builder = bool(re.search(r'\bstd\.build\.Builder\b', content))
            has_legacy_add = bool(re.search(r'addExecutable\("[^"]+",\s*"[^"]+"', content))

            if has_std_build or has_b_path or has_struct_literal_add:
                self.log("Detected modern build API (0.11+)")
                # Could be 0.11-0.15, default to current stable
                return {
                    "version": "0.15.2",
                    "confidence": self.CONFIDENCE_MEDIUM,
                    "source": "build.zig_modern_api",
                    "note": "Detected 0.11+ API, exact version unknown"
                }

            if has_std_build_builder or has_legacy_add:
                self.log("Detected legacy build API (pre-0.11)")
                return {
                    "version": "0.10.1",
                    "confidence": self.CONFIDENCE_MEDIUM,
                    "source": "build.zig_legacy_api",
                    "note": "Detected pre-0.11 API"
                }

        except Exception as e:
            self.log(f"Error analyzing build.zig: {e}")

        return None

    def _detect_from_source_files(self) -> Optional[Dict[str, str]]:
        """Scan .zig source files for syntax markers."""
        zig_files = list(self.project_dir.rglob("*.zig"))

        if not zig_files:
            self.log("No .zig source files found")
            return None

        self.log(f"Scanning {len(zig_files)} .zig files for syntax markers")

        has_modern_for_loop = False
        has_async_await = False

        for zig_file in zig_files:
            try:
                content = zig_file.read_text()

                # Modern for loop syntax (0.13+)
                if re.search(r'for\s*\([^)]+,\s*0\.\.\)', content):
                    has_modern_for_loop = True
                    self.log(f"Found modern for loop in {zig_file.name}")

                # Async/await (0.9-0.10)
                if re.search(r'\b(async|await)\b', content):
                    has_async_await = True
                    self.log(f"Found async/await in {zig_file.name}")

            except Exception as e:
                self.log(f"Error reading {zig_file}: {e}")

        # Determine version from markers
        if has_modern_for_loop:
            return {
                "version": "0.13.0",
                "confidence": self.CONFIDENCE_MEDIUM,
                "source": "source_syntax_for_loop",
                "note": "Detected modern for loop syntax (0.13+)"
            }

        if has_async_await:
            return {
                "version": "0.10.1",
                "confidence": self.CONFIDENCE_MEDIUM,
                "source": "source_syntax_async",
                "note": "Detected async/await keywords (0.9-0.10)"
            }

        return None


def main():
    parser = argparse.ArgumentParser(
        description="Detect Zig compiler version from project structure and code"
    )
    parser.add_argument(
        "--dir",
        type=Path,
        default=Path.cwd(),
        help="Project directory to analyze (default: current directory)"
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Enable verbose debug logging to stderr"
    )

    args = parser.parse_args()

    if not args.dir.exists():
        print(json.dumps({
            "error": f"Directory not found: {args.dir}"
        }), file=sys.stderr)
        sys.exit(1)

    detector = ZigVersionDetector(args.dir, verbose=args.verbose)
    result = detector.detect()

    # Output JSON result to stdout
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
