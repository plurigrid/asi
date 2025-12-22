# Changelog

All notable changes to this project will be documented in this file.

## [1.1.0] - 2024-12-20

### Added
- **Dry-run mode**: Preview installations with `--dry-run` flag
- **Config file support**: `~/.agent-skills.json` for default settings
- **Update notifications**: See available updates when listing installed skills
- **Update all**: `update --all` to update all installed skills at once
- **Category filter**: `list --category development` to filter skills
- **Tag support**: Search now includes tags
- **"Did you mean" suggestions**: Typo-tolerant skill name matching
- **Config command**: `config --default-agent cursor` to set defaults
- **Security validation**: Block path traversal attacks in skill names
- **Size limit**: 50MB max skill size to prevent abuse
- **Proper error handling**: Graceful failures with helpful messages
- **Test suite**: `npm test` runs validation tests
- **Enhanced CI**: Schema validation, duplicate detection, frontmatter checks

### Changed
- Bump to version 1.1.0 (semver: new features)
- Node.js 14+ now required (was implicit, now explicit)
- CLI shows skill size on install
- Better help output with categories section

### Fixed
- JSON parsing errors now show helpful messages instead of crashing
- File operation errors properly caught and reported
- Partial installs cleaned up on failure

### Security
- Skill names validated against path traversal patterns (`../`, `\`)
- Max file size enforced during copy operations

## [1.0.8] - 2024-12-20

### Added
- `uninstall` command to remove installed skills
- `update` command to update skills to latest version
- `list --installed` flag to show installed skills per agent
- Letta agent support (`--agent letta`)
- Command aliases: `add`, `remove`, `rm`, `find`, `show`, `upgrade`

### Fixed
- Description truncation now only adds "..." when actually truncated

## [1.0.7] - 2024-12-19

### Added
- Credits & Attribution section in README
- npm downloads badge
- Full skill listing in README (all 38 skills now documented)

### Fixed
- `--agent` flag parsing improvements
- Codex agent support

## [1.0.6] - 2024-12-18

### Added
- 15 new skills from ComposioHQ ecosystem:
  - `artifacts-builder` - Interactive React/Tailwind components
  - `changelog-generator` - Generate changelogs from git commits
  - `competitive-ads-extractor` - Analyze competitor ads
  - `content-research-writer` - Research and write with citations
  - `developer-growth-analysis` - Track developer metrics
  - `domain-name-brainstormer` - Generate domain name ideas
  - `file-organizer` - Organize files and find duplicates
  - `image-enhancer` - Improve image quality
  - `invoice-organizer` - Organize invoices for tax prep
  - `lead-research-assistant` - Identify and qualify leads
  - `meeting-insights-analyzer` - Analyze meeting transcripts
  - `raffle-winner-picker` - Select contest winners
  - `slack-gif-creator` - Create animated GIFs for Slack
  - `theme-factory` - Professional font and color themes
  - `video-downloader` - Download videos from platforms
- Cross-link to Awesome Agent Skills repository

## [1.0.5] - 2024-12-17

### Fixed
- VS Code install message now correctly shows `.github/skills/`

## [1.0.4] - 2024-12-17

### Fixed
- VS Code path corrected to `.github/skills/` (was `.vscode/`)

## [1.0.3] - 2024-12-17

### Added
- `job-application` skill for cover letters and applications

## [1.0.2] - 2024-12-17

### Added
- Multi-agent support with `--agent` flag
- Support for Claude Code, Cursor, Amp, VS Code, Goose, OpenCode
- Portable install option with `--agent project`

## [1.0.1] - 2024-12-16

### Added
- `qa-regression` skill for automated Playwright testing
- GitHub issue templates and PR templates
- CI validation workflow
- Funding configuration

## [1.0.0] - 2024-12-16

### Added
- Initial release with 20 curated skills
- NPX installer (`npx ai-agent-skills install <name>`)
- Skills from Anthropic's official examples
- Core document skills: `pdf`, `xlsx`, `docx`, `pptx`
- Development skills: `frontend-design`, `mcp-builder`, `skill-creator`
- Creative skills: `canvas-design`, `algorithmic-art`
