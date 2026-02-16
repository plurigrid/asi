#!/usr/bin/env python3
"""
Package and validate a skill for distribution.

This script validates the skill structure and creates a distributable zip file.
"""

import argparse
import json
import logging
import re
import sys
import zipfile
from pathlib import Path
from typing import Dict, List, Tuple

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)


class SkillValidator:
    """Validate skill structure and content."""

    def __init__(self, skill_dir: Path):
        """Initialize validator with skill directory."""
        self.skill_dir = skill_dir
        self.errors = []
        self.warnings = []

    def validate(self) -> bool:
        """Run all validation checks."""
        logger.info("Validating skill structure...")

        # Check required files
        self.check_required_files()

        # Validate SKILL.md
        self.validate_skill_md()

        # Check directory structure
        self.check_directory_structure()

        # Validate file references
        self.validate_file_references()

        # Report results
        if self.errors:
            logger.error("Validation failed with errors:")
            for error in self.errors:
                logger.error(f"  ✗ {error}")

        if self.warnings:
            logger.warning("Validation warnings:")
            for warning in self.warnings:
                logger.warning(f"  ⚠ {warning}")

        if not self.errors:
            logger.info("✓ Validation passed")
            return True

        return False

    def check_required_files(self):
        """Check for required files."""
        skill_md = self.skill_dir / 'SKILL.md'

        if not skill_md.exists():
            self.errors.append("SKILL.md is required but not found")

    def validate_skill_md(self):
        """Validate SKILL.md content and metadata."""
        skill_md = self.skill_dir / 'SKILL.md'

        if not skill_md.exists():
            return

        content = skill_md.read_text(encoding='utf-8')

        # Check for YAML frontmatter
        if not content.startswith('---'):
            self.errors.append("SKILL.md must start with YAML frontmatter")
            return

        # Extract frontmatter
        try:
            parts = content.split('---', 2)
            if len(parts) < 3:
                self.errors.append("Invalid YAML frontmatter format")
                return

            frontmatter = parts[1].strip()

            # Parse YAML (simple parsing for basic validation)
            has_name = False
            has_description = False

            for line in frontmatter.split('\n'):
                if line.startswith('name:'):
                    has_name = True
                    name = line.split(':', 1)[1].strip()
                    if not name:
                        self.errors.append("'name' field in frontmatter cannot be empty")
                    elif not re.match(r'^[a-z0-9-]+$', name):
                        self.warnings.append(f"Skill name '{name}' should use lowercase letters, numbers, and hyphens only")

                elif line.startswith('description:'):
                    has_description = True
                    desc = line.split(':', 1)[1].strip()
                    if not desc and '>' not in frontmatter:
                        self.errors.append("'description' field in frontmatter cannot be empty")

            if not has_name:
                self.errors.append("'name' field is required in frontmatter")

            if not has_description:
                self.errors.append("'description' field is required in frontmatter")

        except Exception as e:
            self.errors.append(f"Error parsing frontmatter: {e}")

        # Check content quality
        body = parts[2] if len(parts) >= 3 else ""

        if len(body) < 100:
            self.warnings.append("SKILL.md body seems very short")

        if len(body) > 20000:
            self.warnings.append("SKILL.md body is very long (>20k chars), consider moving content to references/")

        # Check for second-person usage
        second_person_patterns = [
            r'\byou\s+should\b',
            r'\byou\s+can\b',
            r'\byou\s+will\b',
            r'\byou\s+must\b',
            r'\byour\s+',
        ]

        for pattern in second_person_patterns:
            if re.search(pattern, body, re.IGNORECASE):
                self.warnings.append("Avoid second-person language (you/your) in skills")
                break

    def check_directory_structure(self):
        """Check optional directory structure."""
        expected_dirs = ['scripts', 'references', 'assets']

        for dir_name in expected_dirs:
            dir_path = self.skill_dir / dir_name

            if dir_path.exists():
                if not dir_path.is_dir():
                    self.errors.append(f"{dir_name} exists but is not a directory")
                elif not any(dir_path.iterdir()):
                    self.warnings.append(f"{dir_name}/ directory is empty")

    def validate_file_references(self):
        """Validate that referenced files exist."""
        skill_md = self.skill_dir / 'SKILL.md'

        if not skill_md.exists():
            return

        content = skill_md.read_text(encoding='utf-8')

        # Find file references
        patterns = [
            r'`scripts/([^`]+)`',
            r'`references/([^`]+)`',
            r'`assets/([^`]+)`',
        ]

        for pattern in patterns:
            matches = re.findall(pattern, content)

            for match in matches:
                file_path = self.skill_dir / match

                if not file_path.exists():
                    self.warnings.append(f"Referenced file not found: {match}")


class SkillPackager:
    """Package skill into distributable zip file."""

    def __init__(self, skill_dir: Path, output_dir: Path):
        """Initialize packager with directories."""
        self.skill_dir = skill_dir
        self.output_dir = output_dir

    def package(self) -> Path:
        """Create zip package of the skill."""
        # Get skill name from SKILL.md
        skill_name = self.get_skill_name()

        if not skill_name:
            skill_name = self.skill_dir.name

        # Create output directory
        self.output_dir.mkdir(parents=True, exist_ok=True)

        # Create zip file
        zip_path = self.output_dir / f"{skill_name}.zip"

        logger.info(f"Creating package: {zip_path}")

        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zf:
            # Add all files
            for file_path in self.skill_dir.rglob('*'):
                if file_path.is_file():
                    # Skip certain files
                    if file_path.name.startswith('.'):
                        continue
                    if file_path.suffix == '.pyc':
                        continue
                    if '__pycache__' in str(file_path):
                        continue

                    # Calculate archive path
                    arcname = file_path.relative_to(self.skill_dir.parent)

                    # Add to zip
                    zf.write(file_path, arcname)
                    logger.debug(f"  Added: {arcname}")

        # Check package size
        size_mb = zip_path.stat().st_size / (1024 * 1024)

        if size_mb > 10:
            logger.warning(f"Package is large ({size_mb:.1f} MB), consider reducing size")
        else:
            logger.info(f"Package size: {size_mb:.1f} MB")

        return zip_path

    def get_skill_name(self) -> str:
        """Extract skill name from SKILL.md."""
        skill_md = self.skill_dir / 'SKILL.md'

        if not skill_md.exists():
            return None

        content = skill_md.read_text(encoding='utf-8')

        # Extract name from frontmatter
        if content.startswith('---'):
            parts = content.split('---', 2)

            if len(parts) >= 2:
                for line in parts[1].split('\n'):
                    if line.startswith('name:'):
                        return line.split(':', 1)[1].strip()

        return None


def main():
    """Main entry point for skill packager."""
    parser = argparse.ArgumentParser(
        description='Package and validate a skill for distribution'
    )
    parser.add_argument(
        'skill_dir',
        help='Path to the skill directory'
    )
    parser.add_argument(
        'output_dir',
        nargs='?',
        default='.',
        help='Output directory for the package (default: current directory)'
    )
    parser.add_argument(
        '--skip-validation',
        action='store_true',
        help='Skip validation checks'
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

    # Validate paths
    skill_dir = Path(args.skill_dir)

    if not skill_dir.exists():
        logger.error(f"Skill directory not found: {skill_dir}")
        sys.exit(1)

    output_dir = Path(args.output_dir)

    # Validate skill
    if not args.skip_validation:
        validator = SkillValidator(skill_dir)

        if not validator.validate():
            logger.error("Validation failed. Use --skip-validation to package anyway")
            sys.exit(1)

    # Package skill
    packager = SkillPackager(skill_dir, output_dir)

    try:
        zip_path = packager.package()
        logger.info(f"✓ Successfully packaged skill: {zip_path}")

    except Exception as e:
        logger.error(f"Packaging failed: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()