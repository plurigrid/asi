---
name: unironic-sun-emoji
description: "☼ - NaNoWriMo novel project: experimental/literary fiction with 949 documents (886 with body content, 1.3M characters). Scrivener project created 2018-11-04 on DESKTOP-9BE0I4B. Query via scrivener.duckdb. Use when referencing the ☼ manuscript, its structure, characters, labels, or writing history."
---

# ☼ — Unironic Sun Emoji

A NaNoWriMo novel project. 949 binder items, 886 documents with body text, totaling 1,304,622 characters.

## Identity

- **Title:** [(unironic) SUN EMOJI]
- **Scrivener Creator:** SCRWIN-3.0.1.0
- **Device:** DESKTOP-9BE0I4B
- **Identifier:** C161C8C9-6662-4BE0-8CB2-BEBED4332392
- **Created:** 2018-11-04 (NaNoWriMo template)
- **Last Modified:** 2021-07-20
- **Draft Target:** 50,000 words
- **Session Target:** 1,667 words
- **Template:** No (instantiated from NaNoWriMo template)

## Structure

All content is flat under a single `NaNoWriMo Template` root — 949 text items at depth 1, no folders or sub-hierarchy. This is a stream-of-consciousness / fragmentary manuscript.

### Opening Sections (sample)

1. [(unironic) SUN EMOJI]
2. This book is
3. Epilogue 3
4. A Letter From The Narrator
5. A throat is cleared.
6. The eye contact of guards exchanging duty across...
7. Slices of the milky way shone through distant...
8. Rules, rules, rules. There were no rules in her...
9. Words whispered outside the mouth of a cave,...
10. These lovely watching eyes.

### Longest Documents

| Chars | Title |
|------:|-------|
| 33,010 | will they say your name |
| 20,648 | "Orange/Blue" 1 [] Chapter 17: Orange/Blue |
| 18,673 | [] Chapter 18: Faithful Host |
| 15,531 | NaNoWriMo Template |
| 14,872 | [] Chapter 20: beggars and braggers |
| 13,587 | [] Chapter 21: Rebel without applause |
| 12,537 | [] Chapter 13: moon above, sun below |
| 12,262 | [] Chapter 14: Gilt |

## Labels

| ID | Name | Color (RGB float) |
|----|------|-------------------|
| -1 | No Label | — |
| 1 | Idea | 0.953 0.918 0.329 (yellow) |
| 2 | Chapter | 0.282 0.702 0.000 (green) |
| 4 | Scene | 0.275 0.557 1.000 (blue) |
| 5 | Notes | 0.894 0.529 0.220 (orange) |
| 6 | Character Notes | 0.914 0.098 0.184 (red) |

Labels in use: Chapter (1 doc), Scene (1), Notes (1), Character Notes (1).

## Statuses

| ID | Name |
|----|------|
| -1 | No Status |
| 1 | To Do |
| 2 | First Draft |
| 3 | Revised Draft |
| 4 | Final Draft |
| 5 | Done |
| 6 | Title Page |

Statuses in use: Title Page (3 docs), First Draft (1 doc).

## Section Types

- Heading
- Sub-Heading
- Section
- Section Start
- N/A

## Styles

| Name | Type | Shortcut |
|------|------|----------|
| Title | Para+Char | — |
| Heading 1 | Para+Char | 4 |
| Heading 2 | Para+Char | 5 |
| Centered Text | Para | 1 |
| Block Quote | Para | 2 |
| Attribution | Para | — |
| Code Block | Para+Char | — |
| Verse | Para | — |

## Bookmarks

- [NaNoWriMo Home](http://nanowrimo.org)
- [NaNoWriMo Forums](http://www.nanowrimo.org/forums)
- Binder ref: C693BFB4-198D-4AC4-AFF2-21D80F3839C9

## Content Stats

| Type | Count | Characters |
|------|------:|----------:|
| RTF | 886 | 1,304,622 |
| PDF | 2 | — |
| JPG | 2 | — |
| (empty) | 59 | — |

946 of 949 documents have `IncludeInCompile = Yes`.

## Comments

13 inline comments found across the project (XML with RTF annotations). Samples:
- "what..."
- "Stop relying on memory for this. What was said?"

## Database Access

All data is in `scrivener.duckdb` at `/Users/alice/v/scrivener.duckdb`.

```sql
-- All ☼ documents
SELECT * FROM documents WHERE project = '☼';

-- ☼ content with body text
SELECT d.title, c.body, c.body_length
FROM documents d JOIN content c ON d.uuid = c.uuid AND d.project = c.project
WHERE d.project = '☼' AND c.body_length > 0
ORDER BY c.body_length DESC;

-- ☼ labels
SELECT * FROM labels WHERE project = '☼';

-- ☼ comments
SELECT * FROM comments WHERE project = '☼';

-- Full text search across ☼
SELECT d.title, c.body_length
FROM documents d JOIN content c ON d.uuid = c.uuid AND d.project = c.project
WHERE d.project = '☼' AND c.body LIKE '%search_term%';
```

## Source

Scrivener project bundle: `/Users/alice/Desktop/☼.scriv/`
