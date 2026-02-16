# Publishing Books as Skills

## Workflow: Book → Skill → Plurigrid/ASI

### 1. Extract Structure
```bash
# From HTML book
curl -s "https://book-url.com" | \
  pup 'h1, h2, h3' | \
  nl -ba > chapters.txt

# From PDF
pdftotext -layout book.pdf - | \
  grep -E '^(Chapter|[0-9]+\.)' > chapters.txt

# From EPUB
unzip -p book.epub OEBPS/*.xhtml | \
  grep -oP '(?<=<title>).*(?=</title>)' > chapters.txt
```

### 2. Assign Colors (via Gay.jl)
```bash
# Each chapter gets deterministic color from seed
bb book-to-skill.bb $SEED > skill-manifest.json
```

### 3. Create Skill Directory
```
book-name/
├── SKILL.md      # Main documentation
├── GAY.md        # Color assignments
├── UNWORLD_CHAPTERS.md  # Derivational ordering
├── book-to-skill.bb     # Generator script
└── resources/
    ├── chapters/        # Per-chapter extracts
    └── tools/           # Command-line tools from book
```

### 4. Push to plurigrid/asi
```bash
# Fork and clone
gh repo fork plurigrid/asi --clone

# Add skill
cp -r book-name ~/.agents/skills/
git add .agents/skills/book-name
git commit -m "Add book-name skill (trit: -1, #HEXCOLOR)"

# Verify GF(3) conservation
bb verify-gf3.bb

# Push and PR
git push origin main
gh pr create --title "skill: book-name" --body "Trit: -1, Color: #HEXCOLOR"
```

## Template for New Books

```markdown
# {Book Title} Skill

**Color**: #{HEX}
**Trit**: {-1|0|+1}
**Author**: {Author Name}
**Source**: {URL or ISBN}

## Unworlded Structure

| Trit | Chapters |
|------|----------|
| +1   | {generative chapters} |
| 0    | {coordinating chapters} |
| -1   | {validating chapters} |

## Key Commands/Concepts

{extracted from book}

## Triad Bundles

```
{this-skill} ⊗ {skill-2} ⊗ {skill-3} = 0 ✓
```
```

## Books → Skills Pipeline

```
┌─────────────┐    ┌──────────────┐    ┌─────────────┐
│  Book/PDF   │───→│ book-to-skill│───→│   SKILL.md  │
│  EPUB/HTML  │    │     .bb      │    │   GAY.md    │
└─────────────┘    └──────────────┘    └─────────────┘
                          │
                          ▼
                   ┌──────────────┐
                   │ UNWORLD_     │
                   │ CHAPTERS.md  │
                   └──────────────┘
                          │
                          ▼
                   ┌──────────────┐
                   │ plurigrid/   │
                   │ asi PR       │
                   └──────────────┘
```
