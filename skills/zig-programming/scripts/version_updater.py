#!/usr/bin/env python3
"""
Update the Zig skill when new versions are released.

This script automates the process of updating the skill's documentation
and patterns when a new version of Zig is released.
"""

import argparse
import json
import logging
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)

# Current supported versions
CURRENT_VERSIONS = [
    '0.2.0', '0.3.0', '0.6.0', '0.7.1', '0.8.1',
    '0.9.1', '0.10.1', '0.11.0', '0.12.1', '0.13.0',
    '0.14.1', '0.15.2', 'master'
]


class VersionUpdater:
    """Update Zig skill for new versions."""

    def __init__(self, skill_dir: Path):
        """Initialize updater with skill directory."""
        self.skill_dir = skill_dir
        self.scripts_dir = skill_dir / 'scripts'
        self.references_dir = skill_dir / 'references'
        self.docs_dir = skill_dir.parent / 'docs-master'

    def check_new_version(self, version: str) -> bool:
        """Check if a version is new and needs processing."""
        versions_file = self.skill_dir / 'versions.json'

        if versions_file.exists():
            with open(versions_file, 'r') as f:
                known_versions = json.load(f)
                return version not in known_versions

        return True

    def update_documentation(self, version: str):
        """Update documentation for a new version."""
        logger.info(f"Updating documentation for version {version}")

        # Step 1: Convert HTML to Markdown
        logger.info("Step 1: Converting HTML documentation to Markdown")
        converter_script = self.scripts_dir / 'zig_docs_converter.py'

        cmd = [
            'python', str(converter_script),
            '--version', version
        ]

        try:
            subprocess.run(cmd, check=True, capture_output=True, text=True)
            logger.info(f"  ✓ Converted documentation for {version}")
        except subprocess.CalledProcessError as e:
            logger.error(f"  ✗ Failed to convert documentation: {e.stderr}")
            raise

        # Step 2: Consolidate documentation
        logger.info("Step 2: Consolidating documentation")
        consolidator_script = self.scripts_dir / 'consolidator.py'
        docs_dir = self.skill_dir.parent / f'docs-{version}'
        knowledge_dir = self.skill_dir / 'knowledge-temp'

        cmd = [
            'python', str(consolidator_script),
            str(docs_dir),
            str(knowledge_dir),
            '--version', version
        ]

        try:
            subprocess.run(cmd, check=True, capture_output=True, text=True)
            logger.info(f"  ✓ Consolidated documentation for {version}")
        except subprocess.CalledProcessError as e:
            logger.error(f"  ✗ Failed to consolidate: {e.stderr}")
            raise

        # Step 3: Extract patterns
        logger.info("Step 3: Extracting patterns")
        extractor_script = self.scripts_dir / 'pattern_extractor.py'
        patterns_dir = self.skill_dir / 'patterns-temp'

        cmd = [
            'python', str(extractor_script),
            str(knowledge_dir),
            str(patterns_dir)
        ]

        try:
            subprocess.run(cmd, check=True, capture_output=True, text=True)
            logger.info(f"  ✓ Extracted patterns for {version}")
        except subprocess.CalledProcessError as e:
            logger.error(f"  ✗ Failed to extract patterns: {e.stderr}")
            raise

    def merge_updates(self, version: str):
        """Merge updates into existing skill."""
        logger.info(f"Merging updates for version {version}")

        knowledge_dir = self.skill_dir / 'knowledge-temp'
        patterns_dir = self.skill_dir / 'patterns-temp'

        # Load and merge version differences
        version_diff_file = knowledge_dir / 'version-differences.md'
        if version_diff_file.exists():
            self.update_version_differences(version, version_diff_file)

        # Update patterns if significantly different
        new_patterns_file = patterns_dir / 'patterns.json'
        if new_patterns_file.exists():
            self.merge_patterns(new_patterns_file)

        # Clean up temp directories
        import shutil
        if knowledge_dir.exists():
            shutil.rmtree(knowledge_dir)
        if patterns_dir.exists():
            shutil.rmtree(patterns_dir)

        logger.info(f"  ✓ Merged updates for {version}")

    def update_version_differences(self, version: str, diff_file: Path):
        """Update version differences documentation."""
        target_file = self.references_dir / 'version-differences.md'

        if not target_file.exists():
            # Just copy the new file
            diff_file.rename(target_file)
            return

        # Read existing content
        existing_content = target_file.read_text(encoding='utf-8')
        new_content = diff_file.read_text(encoding='utf-8')

        # Simple merge: append new version info
        # In practice, this would be more sophisticated
        lines = existing_content.split('\n')
        insert_idx = None

        for i, line in enumerate(lines):
            if f'### {version}' in line:
                logger.info(f"Version {version} already documented")
                return
            if line.startswith('### 0.') or line.startswith('### master'):
                if insert_idx is None:
                    insert_idx = i

        if insert_idx:
            # Extract version-specific content from new file
            new_lines = new_content.split('\n')
            version_section = []
            in_version = False

            for line in new_lines:
                if f'{version}' in line:
                    in_version = True
                elif in_version and line.startswith('### '):
                    break
                elif in_version:
                    version_section.append(line)

            if version_section:
                lines[insert_idx:insert_idx] = [f"### {version}"] + version_section + ['']
                target_file.write_text('\n'.join(lines), encoding='utf-8')
                logger.info(f"  ✓ Updated version differences for {version}")

    def merge_patterns(self, new_patterns_file: Path):
        """Merge new patterns into existing patterns."""
        target_file = self.references_dir / 'patterns.json'

        if not target_file.exists():
            new_patterns_file.rename(target_file)
            return

        with open(target_file, 'r') as f:
            existing = json.load(f)

        with open(new_patterns_file, 'r') as f:
            new = json.load(f)

        # Merge categories
        for category, data in new.get('categories', {}).items():
            if category not in existing.get('categories', {}):
                existing.setdefault('categories', {})[category] = data
            else:
                # Merge examples
                existing_examples = {
                    ex['code'] for ex in existing['categories'][category].get('examples', [])
                }
                for example in data.get('examples', []):
                    if example['code'] not in existing_examples:
                        existing['categories'][category].setdefault('examples', []).append(example)

        # Update metadata
        existing['metadata']['last_updated'] = new.get('metadata', {}).get('last_updated', '')

        with open(target_file, 'w') as f:
            json.dump(existing, f, indent=2)

        logger.info("  ✓ Merged patterns")

    def update_skill_metadata(self, version: str):
        """Update skill metadata with new version."""
        skill_md = self.skill_dir / 'SKILL.md'

        content = skill_md.read_text(encoding='utf-8')

        # Update version in description
        if 'latest stable' in content:
            import re
            content = re.sub(
                r'Default to Zig \d+\.\d+\.\d+',
                f'Default to Zig {version}',
                content
            )
            skill_md.write_text(content, encoding='utf-8')

        # Update versions.json
        versions_file = self.skill_dir / 'versions.json'
        if versions_file.exists():
            with open(versions_file, 'r') as f:
                versions = json.load(f)
        else:
            versions = []

        if version not in versions:
            versions.append(version)
            versions.sort()
            with open(versions_file, 'w') as f:
                json.dump(versions, f, indent=2)

        logger.info(f"  ✓ Updated skill metadata for {version}")

    def generate_changelog(self, version: str):
        """Generate changelog entry for version update."""
        changelog_file = self.skill_dir / 'CHANGELOG.md'

        from datetime import datetime
        date = datetime.now().strftime('%Y-%m-%d')

        entry = f"""
## [{version}] - {date}

### Added
- Documentation for Zig {version}
- Patterns extracted from {version} documentation

### Updated
- Version differences documentation
- Default version recommendation

"""

        if changelog_file.exists():
            existing = changelog_file.read_text(encoding='utf-8')
            if f'[{version}]' not in existing:
                # Insert after header
                lines = existing.split('\n')
                for i, line in enumerate(lines):
                    if line.startswith('## ['):
                        lines.insert(i, entry)
                        break
                else:
                    lines.append(entry)
                changelog_file.write_text('\n'.join(lines), encoding='utf-8')
        else:
            header = "# Changelog\n\nAll notable changes to the Zig programming skill.\n"
            changelog_file.write_text(header + entry, encoding='utf-8')

        logger.info(f"  ✓ Updated changelog for {version}")

    def run_update(self, version: str, skip_download: bool = False):
        """Run full update process for a new version."""
        logger.info(f"Starting update process for Zig {version}")

        try:
            if not skip_download:
                self.update_documentation(version)

            self.merge_updates(version)
            self.update_skill_metadata(version)
            self.generate_changelog(version)

            logger.info(f"✓ Successfully updated skill for Zig {version}")

        except Exception as e:
            logger.error(f"✗ Update failed: {e}")
            raise

    def check_all_versions(self):
        """Check for updates across all tracked versions."""
        import requests

        logger.info("Checking for new Zig versions...")

        # Check ziglang.org for available versions
        # This is a simplified check - in practice would parse the downloads page
        url = "https://ziglang.org/download/"

        try:
            response = requests.get(url, timeout=10)
            if response.status_code == 200:
                # Simple pattern matching for version numbers
                import re
                pattern = r'(\d+\.\d+\.\d+)'
                versions = set(re.findall(pattern, response.text))

                new_versions = []
                for v in versions:
                    if self.check_new_version(v):
                        new_versions.append(v)

                if new_versions:
                    logger.info(f"Found new versions: {new_versions}")
                    return new_versions
                else:
                    logger.info("No new versions found")
                    return []

        except Exception as e:
            logger.error(f"Failed to check for versions: {e}")
            return []


def main():
    """Main entry point for version updater."""
    parser = argparse.ArgumentParser(
        description='Update Zig skill for new versions'
    )
    parser.add_argument(
        'skill_dir',
        help='Path to the skill directory'
    )
    parser.add_argument(
        '--version',
        help='Specific version to update'
    )
    parser.add_argument(
        '--check-all',
        action='store_true',
        help='Check for all new versions'
    )
    parser.add_argument(
        '--skip-download',
        action='store_true',
        help='Skip downloading documentation (use existing)'
    )
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Enable verbose logging'
    )

    args = parser.parse_args()

    # Configure logging
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    # Create updater
    skill_dir = Path(args.skill_dir)
    if not skill_dir.exists():
        logger.error(f"Skill directory not found: {skill_dir}")
        sys.exit(1)

    updater = VersionUpdater(skill_dir)

    # Run update
    if args.check_all:
        new_versions = updater.check_all_versions()
        if new_versions:
            for version in new_versions:
                try:
                    updater.run_update(version, args.skip_download)
                except Exception as e:
                    logger.error(f"Failed to update {version}: {e}")
    elif args.version:
        updater.run_update(args.version, args.skip_download)
    else:
        logger.error("Please specify --version or --check-all")
        sys.exit(1)


if __name__ == '__main__':
    main()