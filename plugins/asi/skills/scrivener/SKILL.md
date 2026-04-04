---
name: scrivener
version: 1.0.0
description: |
  Scrivener project format internals, data model, and programmatic access.
  Use when parsing .scriv bundles, querying DuckDB exports, extracting
  manuscript text, or building AI-assisted novel tools from Scrivener data.
  Covers Windows-origin projects, cross-platform migration, and RTF content.
---

# Scrivener: Project Format, Data Model & Programmatic Access

**Trit**: -1 (MINUS - validator/extractor)
**Color**: #E91A2F (Character Notes red)

## When to use this skill

- Parsing or inspecting `.scriv` project bundles (XML, RTF, metadata)
- Querying a DuckDB export of Scrivener data (documents, content, labels)
- Extracting manuscript text, character info, or synopses programmatically
- Migrating projects across Scrivener versions or platforms (Windows ↔ macOS)
- Building tools that read/write Scrivener project structures

## File Format: .scriv Bundle

A `.scriv` project is a directory. On macOS it displays as a single file (document package); on Windows it's a regular folder.

```
MyProject.scriv/
├── Files/
│   ├── Data/
│   │   ├── <UUID>/
│   │   │   ├── content.rtf       # Document body (RTF format)
│   │   │   ├── notes.rtf         # Inspector notes (RTF)
│   │   │   ├── synopsis.txt      # Synopsis text
│   │   │   └── snapshot-*.rtf    # Version snapshots
│   │   └── docs.checksum         # Integrity checksums
│   ├── binder.autosave           # Auto-saved binder state
│   ├── binder.backup             # Binder backup
│   ├── search.indexes            # Full-text search index
│   ├── styles.xml                # Document styles
│   ├── version.txt               # Format version
│   └── writing.history           # Session word counts
├── <ProjectName>.scrivx           # Master XML: binder tree + metadata
├── Settings/
│   ├── recents.txt               # Recent documents
│   ├── ui-common.xml             # Cross-platform UI state
│   └── ui.ini                    # Platform-specific UI state
└── QuickLook/
    └── Preview.html              # Finder preview (macOS only)
```

## Version History & Cross-Platform Migration

The ☼ project was **created on Windows** and has been migrated through multiple Scrivener versions:

| Version | Platform | Format | Notes |
|---------|----------|--------|-------|
| Scrivener 1 (Win) | Windows | XML `.scrivx` v1 + RTF | Original Windows port. `.scriv` is a visible folder. |
| Scrivener 1 (Mac) | macOS | Binary plist `.scrivproj` + RTF | macOS only, different format entirely. |
| Scrivener 2 (Mac) | macOS | Binary plist → XML | Transitional. No Windows v2 existed. |
| Scrivener 3 (Win) | Windows | XML `.scrivx` v2 + RTF | **Current**. Creator tag: `SCRWIN-3.x.x.x` |
| Scrivener 3 (Mac) | macOS | XML `.scrivx` v2 + RTF | **Current**. Creator tag: `SCRMAC-3.x.x` |

### Windows → macOS migration

- `.scriv` folder on Windows is a regular directory; on macOS it becomes a document package (UTI: `com.literatureandlatte.scrivener3.scriv`)
- Copy the entire `.scriv` folder to macOS and open with Scrivener 3 — it auto-upgrades
- The `Creator` attribute in `.scrivx` preserves origin: `SCRWIN-3.1.5.1` means Windows Scrivener 3.1.5.1
- `ui.ini` stores platform-specific UI state; `ui-common.xml` stores cross-platform state
- QuickLook/ only generated on macOS
- Line endings in RTF may differ (CRLF from Windows, LF on macOS) — both parse correctly

### Version upgrade path

Windows v1 → Windows v3: Scrivener auto-converts on open. Creates backup of v1 project first. Binder structure, labels, statuses, and content preserved. Custom metadata fields may need manual re-setup.

## .scrivx XML Schema

The `.scrivx` file is the master index:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<ScrivenerProject Template="No" Version="2.0"
    Identifier="UUID" Creator="SCRWIN-3.1.5.1"
    Device="HOSTNAME" Modified="2025-03-14 22:15:28 -0600"
    ModID="UUID">
  <Binder>
    <BinderItem UUID="..." Type="DraftFolder" Created="..." Modified="...">
      <Title>Draft</Title>
      <MetaData>
        <IncludeInCompile>Yes</IncludeInCompile>
      </MetaData>
      <Children>
        <BinderItem UUID="..." Type="Text" Created="..." Modified="...">
          <Title>Chapter 1</Title>
          <MetaData>
            <LabelID>2</LabelID>
            <StatusID>-1</StatusID>
            <IncludeInCompile>Yes</IncludeInCompile>
            <SectionType>-1</SectionType>
          </MetaData>
        </BinderItem>
      </Children>
    </BinderItem>
  </Binder>
  <LabelSettings>
    <Labels>
      <Label ID="0" Color="0.993 0.227 0.172">Red</Label>
    </Labels>
  </LabelSettings>
  <StatusSettings>
    <StatusItems>
      <Status ID="1">To Do</Status>
      <Status ID="2">In Progress</Status>
      <Status ID="3">First Draft</Status>
    </StatusItems>
  </StatusSettings>
  <ProjectProperties>
    <ProjectTitle>My Novel</ProjectTitle>
    <FullName>Author Name</FullName>
  </ProjectProperties>
</ScrivenerProject>
```

### BinderItem Types

| Type | Description |
|------|-------------|
| `DraftFolder` | Manuscript root (compile target) |
| `ResearchFolder` | Research materials container |
| `TrashFolder` | Deleted items |
| `Folder` | User-created folder |
| `Text` | Document (main content unit) |
| `PDF` | Imported PDF |
| `Image` | Imported image |
| `WebArchive` | Saved web page |

### Document Content Storage

Each document's UUID maps to `Files/Data/<UUID>/`:

- **content.rtf**: Body text. Contains inline annotations via `{\Scrv_fn=...}` custom tags.
- **notes.rtf**: Inspector notes pane.
- **synopsis.txt**: Plain text synopsis (corkboard cards).
- **snapshot-YYYY-MM-DD-HH-MM-SS.rtf**: Version snapshots.

### Color Values

Colors in `.scrivx` are space-separated RGB floats (0.0–1.0):

```python
# "0.952941 0.917647 0.329412" → #F3EB54
hex_color = f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}"
```

## DuckDB Export Schema

When exported to DuckDB (via `build_sun_org.py` or similar):

### `documents`
```sql
CREATE TABLE documents (
    project VARCHAR,          -- e.g. '☼'
    uuid VARCHAR PRIMARY KEY,
    title VARCHAR,
    parent_uuid VARCHAR,
    depth_int INT,            -- Nesting depth in binder
    item_type VARCHAR,        -- 'Text', 'Folder', etc.
    label_id INT,
    status_id INT,
    include_in_compile VARCHAR,
    binder_id VARCHAR,        -- Binder sort order
    section_type INT
);
```

### `content`
```sql
CREATE TABLE content (
    project VARCHAR,
    uuid VARCHAR,             -- FK to documents
    body TEXT,                -- Full RTF body
    synopsis TEXT,
    notes TEXT,
    body_length INT,
    content_file_type VARCHAR
);
```

### `labels`, `statuses`, `comments`
```sql
CREATE TABLE labels (project VARCHAR, label_id INT, name VARCHAR, color VARCHAR);
CREATE TABLE statuses (project VARCHAR, status_id INT, name VARCHAR);
CREATE TABLE comments (project VARCHAR, uuid VARCHAR, comment_text TEXT, position INT);
```

Additional tables: `collections`, `bookmarks`, `styles`, `section_types`, `projects`.

## Common Queries

### Manuscript text in binder order
```sql
SELECT d.uuid, d.title, c.body, c.synopsis
FROM documents d
JOIN content c ON d.uuid = c.uuid AND d.project = c.project
WHERE d.project = '☼'
  AND d.item_type = 'Text'
  AND d.include_in_compile = 'Yes'
  AND c.body IS NOT NULL
ORDER BY d.binder_id;
```

### Find documents mentioning a character
```sql
SELECT d.uuid, d.title, d.binder_id, length(c.body) AS bodylen
FROM documents d
JOIN content c ON d.uuid = c.uuid AND d.project = c.project
WHERE d.project = '☼' AND c.body ILIKE '%edith%'
ORDER BY d.binder_id;
```

### Strip Scrivener RTF tags
```python
import re
clean = re.sub(r'\{\\Scrv_fn=.*?\\end_Scrv_fn\}', '', body)
```

## RTF Content Notes

- **Inline annotations**: `{\Scrv_fn=footnote ...text... \end_Scrv_fn}`
- **Comments**: Stored in `comments` table with position offsets
- **Styles**: Referenced by name from `styles.xml`
- **Images**: Embedded as RTF `\pict` objects or referenced externally
- **Links**: Internal links use `scrivener://` protocol with UUID targets

## Character Data Extraction

Scrivener fiction templates include a Characters folder with sketch documents (Role, Occupation, Physical Description, etc.) — but these are **plain RTF**, not structured data. In the ☼ project, the Characters folder contains only a blank template.

Characters must be detected from prose:

```python
import duckdb

con = duckdb.connect('scrivener.duckdb', read_only=True)

def character_chunks(char_name: str) -> list:
    return con.execute("""
        SELECT d.title, left(c.body, 500) as preview, d.binder_id
        FROM documents d
        JOIN content c ON d.uuid = c.uuid AND d.project = c.project
        WHERE d.project = '☼'
          AND c.body ILIKE ?
          AND length(c.body) > 50
        ORDER BY d.binder_id
    """, [f'%{char_name}%']).fetchall()

# ☼ characters: she, narrator, ack, edith, deb, rad, glen, will, hub
```

## macOS vs Windows Differences

| Aspect | macOS | Windows |
|--------|-------|---------|
| `.scriv` appearance | Document package (single file) | Regular folder |
| Browse internals | Right-click → Show Package Contents | Open folder normally |
| UTI | `com.literatureandlatte.scrivener3.scriv` | N/A |
| QuickLook preview | Generated automatically | Not available |
| Spotlight indexing | Via `mdls` metadata | Windows Search indexes RTF |
| Line endings in RTF | LF | CRLF |
| Creator tag | `SCRMAC-3.x.x` | `SCRWIN-3.x.x.x` |

## Verify it worked

After parsing a `.scriv` project:

1. Check that the `.scrivx` XML parses and contains `<Binder>` with at least one `<BinderItem>`
2. Verify UUID directories exist under `Files/Data/` for documents listed in the binder
3. Confirm `content.rtf` files are valid RTF (start with `{\rtf1`)
4. If using DuckDB export: `SELECT count(*) FROM documents` should match binder item count

## What not to do

- Don't modify `.scriv` files while Scrivener has the project open — it uses file locks
- Don't assume synopsis or notes fields are populated — many projects leave them empty
- Don't parse RTF with regex for anything beyond stripping Scrivener tags — use a real RTF parser for styled content
- Don't assume macOS package structure on Windows — `.scriv` is just a folder there
- Don't delete `docs.checksum` — Scrivener uses it for integrity verification on open

## ☼ Project Specifics

- **949 documents**: 900 Text, 42 Folders, 2 PDF, 2 Image
- **432 manuscript chunks** with body > 50 chars
- **Labels**: Idea (#F3EB54), Chapter (#48B300), Scene (#468EFF), Notes (#E48738), Character Notes (#E91A2F)
- **Characters folder**: Only a blank template (unfilled)
- **No synopsis metadata** (1 boilerplate entry on Title Page)
- **2 inline comments**: Both authorial reminders
- **Origin**: Created on Windows Scrivener, migrated through version updates

## References

- [Literature & Latte](https://www.literatureandlatte.com/)
- [Scrivener 3 User Manual (macOS PDF)](https://www.literatureandlatte.com/docs/Scrivener_Manual-Mac.pdf)
- [File format analysis (Obsolete Thor)](https://preservation.tylerthorsted.com/2025/03/21/scrivener/)
- [Archive Team: Scrivener](http://justsolve.archiveteam.org/wiki/Scrivener)
- [Character management blog](https://www.literatureandlatte.com/blog/how-to-manage-your-characters-in-scrivener)

## GF(3) Triads

```
scrivener (-1) + catcolab-schemas (+1) + database-design (0) = 0
scrivener (-1) + build-sun-org (+1) + duckdb-ies (0) = 0
```
