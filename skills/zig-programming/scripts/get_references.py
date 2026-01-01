#!/usr/bin/env python3
"""
get_references.py - Returns the correct reference path for a Zig version

This utility determines which reference documentation directory to use based on
the detected or specified Zig version. It supports both JSON output for
programmatic use and human-readable output for manual use.

Usage:
    # Auto-detect version and get reference path
    python get_references.py

    # Specify version explicitly
    python get_references.py --version 0.15.2

    # Get JSON output for scripting
    python get_references.py --json

    # Specify project directory for detection
    python get_references.py --dir /path/to/project

    # Verbose mode
    python get_references.py --verbose

Examples:
    $ python get_references.py
    references/v0.15.2

    $ python get_references.py --json
    {"version": "0.15.2", "path": "references/v0.15.2", "confidence": "high", "fallback": false}

    $ python get_references.py --version 0.14.1
    Warning: No references for 0.14.1, using 0.15.2
    references/v0.15.2
"""

import argparse
import json
import os
import sys
import subprocess
from pathlib import Path


# Available reference versions (in order of preference for fallbacks)
AVAILABLE_REFERENCE_VERSIONS = [
    "0.15.2",  # Current stable
    # Add more versions as they become available:
    # "0.14.1",
    # "0.13.0",
    # "0.11.0",
]

# Version compatibility mapping (which version should fall back to which)
VERSION_FALLBACK_MAP = {
    # 0.15.x series -> 0.15.2
    "0.15.0": "0.15.2",
    "0.15.1": "0.15.2",

    # 0.14.x series -> 0.15.2 (close enough, minor changes)
    "0.14.0": "0.15.2",
    "0.14.1": "0.15.2",

    # 0.13.x series -> 0.15.2 (for loop syntax same, stdlib similar)
    "0.13.0": "0.15.2",
    "0.13.1": "0.15.2",

    # 0.12.x series -> 0.15.2 (with warning about for loops)
    "0.12.0": "0.15.2",
    "0.12.1": "0.15.2",

    # 0.11.x series -> 0.15.2 (build API same, for loops different)
    "0.11.0": "0.15.2",
    "0.11.1": "0.15.2",

    # Older versions -> 0.15.2 (significant differences, warn heavily)
    "0.10.0": "0.15.2",
    "0.10.1": "0.15.2",
    "0.9.0": "0.15.2",
    "0.9.1": "0.15.2",

    # Master/development -> latest
    "master": "latest",
    "dev": "latest",
}


def get_skill_root():
    """
    Get the root directory of the Zig skill.

    Returns the zig-programming directory path, which is the parent of scripts/.
    """
    script_dir = Path(__file__).parent
    skill_root = script_dir.parent
    return skill_root


def detect_zig_version(project_dir=None, verbose=False):
    """
    Detect Zig version by running detect_version.py script.

    Args:
        project_dir: Project directory to analyze (default: current directory)
        verbose: Enable verbose output

    Returns:
        dict with keys: version, confidence, source
    """
    script_path = Path(__file__).parent / "detect_version.py"

    if not script_path.exists():
        # Fallback: assume latest if detection script doesn't exist
        return {
            "version": "0.15.2",
            "confidence": "low",
            "source": "default_fallback"
        }

    cmd = [sys.executable, str(script_path)]

    if project_dir:
        cmd.extend(["--dir", project_dir])

    if verbose:
        cmd.append("--verbose")

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=True
        )

        # Parse JSON output from detect_version.py
        output = json.loads(result.stdout)
        return output

    except subprocess.CalledProcessError as e:
        if verbose:
            print(f"Error running detect_version.py: {e}", file=sys.stderr)
            print(f"stderr: {e.stderr}", file=sys.stderr)
        # Fallback to default
        return {
            "version": "0.15.2",
            "confidence": "low",
            "source": "detection_failed"
        }
    except json.JSONDecodeError as e:
        if verbose:
            print(f"Error parsing detect_version.py output: {e}", file=sys.stderr)
        return {
            "version": "0.15.2",
            "confidence": "low",
            "source": "parse_error"
        }


def get_reference_path_for_version(version: str, verbose: bool = False):
    """
    Get the appropriate reference path for a given Zig version.

    Args:
        version: Zig version string (e.g., "0.15.2", "0.14.1")
        verbose: Print verbose debugging information

    Returns:
        dict with keys:
            - version: The requested version
            - reference_version: The version of references to use
            - path: Relative path to reference directory
            - absolute_path: Absolute path to reference directory
            - exists: Whether the directory exists
            - fallback: Whether a fallback version is being used
            - fallback_reason: Why the fallback was chosen (if applicable)
            - warnings: List of warning messages
    """
    warnings = []
    fallback = False
    fallback_reason = None

    # Normalize version string
    version = version.strip()
    if version.startswith('v'):
        version = version[1:]

    # Check if this exact version has references available
    if f"{version}" in AVAILABLE_REFERENCE_VERSIONS:
        reference_version = version
        if verbose:
            print(f"Exact match found for version {version}", file=sys.stderr)
    else:
        # Check if there's a fallback mapping
        if version in VERSION_FALLBACK_MAP:
            reference_version = VERSION_FALLBACK_MAP[version]
            fallback = True
            fallback_reason = f"No references for {version}, using {reference_version}"
            warnings.append(fallback_reason)

            # Add specific warnings based on version differences
            if version.startswith("0.12") or version.startswith("0.11"):
                warnings.append("Note: For loop syntax differs from 0.13+. See references/version-differences.md")
            elif version.startswith("0.10") or version.startswith("0.9"):
                warnings.append("Warning: Major differences (async/await removed in 0.11+, build API changed)")
                warnings.append("Strongly recommend upgrading to 0.15.2. See references/version-differences.md")
            elif version.startswith("0.8") or int(version.split('.')[1]) < 9:
                warnings.append("Warning: Very old version. References may not be applicable.")
                warnings.append("Highly recommend upgrading to 0.15.2")
        else:
            # No fallback mapping, use latest
            reference_version = "0.15.2"  # Default to current stable
            fallback = True
            fallback_reason = f"Unknown version {version}, defaulting to {reference_version}"
            warnings.append(fallback_reason)
            warnings.append("Consider upgrading to a supported version")

    # Construct reference path
    skill_root = get_skill_root()

    if reference_version == "latest":
        rel_path = "references/latest"
    else:
        rel_path = f"references/v{reference_version}"

    abs_path = skill_root / rel_path
    exists = abs_path.exists() and abs_path.is_dir()

    if not exists:
        warnings.append(f"Warning: Reference directory {rel_path} does not exist!")
        warnings.append("Run consolidator.py to generate references for this version")

    return {
        "version": version,
        "reference_version": reference_version,
        "path": rel_path,
        "absolute_path": str(abs_path),
        "exists": exists,
        "fallback": fallback,
        "fallback_reason": fallback_reason,
        "warnings": warnings,
    }


def main():
    parser = argparse.ArgumentParser(
        description="Get the correct reference path for a Zig version",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Auto-detect version and show reference path
  python get_references.py

  # Specify version explicitly
  python get_references.py --version 0.15.2

  # JSON output for scripting
  python get_references.py --json

  # Specify project directory
  python get_references.py --dir /path/to/project

  # Show detailed information
  python get_references.py --verbose --full
        """
    )

    parser.add_argument(
        "--version",
        help="Zig version to get references for (e.g., '0.15.2'). If not specified, auto-detects."
    )

    parser.add_argument(
        "--dir",
        default=".",
        help="Project directory to analyze for version detection (default: current directory)"
    )

    parser.add_argument(
        "--json",
        action="store_true",
        help="Output JSON format for programmatic use"
    )

    parser.add_argument(
        "--full",
        action="store_true",
        help="Show full information including warnings and paths"
    )

    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Verbose output (shows detection process)"
    )

    args = parser.parse_args()

    # Determine Zig version
    if args.version:
        version = args.version
        confidence = "explicit"
        source = "command_line"
        if args.verbose:
            print(f"Using explicitly specified version: {version}", file=sys.stderr)
    else:
        # Auto-detect version
        if args.verbose:
            print("Auto-detecting Zig version...", file=sys.stderr)

        detection_result = detect_zig_version(args.dir, verbose=args.verbose)
        version = detection_result["version"]
        confidence = detection_result["confidence"]
        source = detection_result["source"]

        if args.verbose:
            print(f"Detected version: {version} (confidence: {confidence}, source: {source})", file=sys.stderr)

    # Get reference path for this version
    ref_info = get_reference_path_for_version(version, verbose=args.verbose)
    ref_info["confidence"] = confidence
    ref_info["source"] = source

    # Output results
    if args.json:
        # JSON output for programmatic use
        output = {
            "version": ref_info["version"],
            "reference_version": ref_info["reference_version"],
            "path": ref_info["path"],
            "absolute_path": ref_info["absolute_path"],
            "exists": ref_info["exists"],
            "confidence": confidence,
            "source": source,
            "fallback": ref_info["fallback"],
            "fallback_reason": ref_info["fallback_reason"],
            "warnings": ref_info["warnings"],
        }
        print(json.dumps(output, indent=2))
    elif args.full:
        # Full human-readable output
        print(f"Zig Version: {ref_info['version']}")
        print(f"Reference Version: {ref_info['reference_version']}")
        print(f"Detection Confidence: {confidence}")
        print(f"Detection Source: {source}")
        print(f"Reference Path: {ref_info['path']}")
        print(f"Absolute Path: {ref_info['absolute_path']}")
        print(f"Directory Exists: {'Yes' if ref_info['exists'] else 'No'}")
        print(f"Using Fallback: {'Yes' if ref_info['fallback'] else 'No'}")

        if ref_info['fallback_reason']:
            print(f"Fallback Reason: {ref_info['fallback_reason']}")

        if ref_info['warnings']:
            print("\nWarnings:")
            for warning in ref_info['warnings']:
                print(f"  - {warning}")
    else:
        # Simple output: just the path (most common use case)
        # Print warnings to stderr, path to stdout
        if ref_info['warnings'] and not args.json:
            for warning in ref_info['warnings']:
                print(warning, file=sys.stderr)

        print(ref_info['path'])

    # Exit with code 0 if directory exists, 1 if it doesn't
    sys.exit(0 if ref_info['exists'] else 1)


if __name__ == "__main__":
    main()
