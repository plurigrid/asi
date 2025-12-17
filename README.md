# SkillCreator Skills

The curated collection of production-ready Claude skills, ranked by GitHub stars.

## Why This Exists

Other directories have 26,000+ skills. Most are noise.

We curate the **top 100** that actually work, ranked by community validation (GitHub stars).

## Browse Skills

Visit [skillcreator.ai/discover](https://skillcreator.ai/discover) to browse, search, and install.

## Categories

| Category | Skills | Description |
|----------|--------|-------------|
| Development | 25 | MCP, TDD, debugging, testing |
| Document | 10 | Word, PDF, Excel, PowerPoint |
| Productivity | 15 | File org, changelog, automation |
| Business | 12 | Leads, ads, research |
| Creative | 10 | Art, design, GIFs |
| Data | 8 | Analytics, visualization |
| Content | 10 | Writing, research, video |
| Lifestyle | 10 | Personal productivity |

## Install a Skill

```bash
# One-liner install
curl -fsSL https://skillcreator.ai/install/[skill-name] | bash

# Or manually
git clone https://github.com/skillcreator/skillcreator-skills
cp -r skills/[category]/[skill-name] ~/.claude/skills/
```

## Create Your Own

Generate a skill in 30 seconds: [skillcreator.ai/build](https://skillcreator.ai/build)

## Ranking Algorithm

Skills are ranked by GitHub stars. We scrape daily and update rankings.

```
score = github_stars * recency_boost * quality_multiplier
```

## Contributing

1. Fork this repo
2. Add your skill to the appropriate category
3. Include SKILL.md with proper frontmatter
4. Submit PR

We accept skills with 2+ GitHub stars or exceptional quality.

## License

MIT
