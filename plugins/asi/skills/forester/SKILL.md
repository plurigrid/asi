---
name: forester
description: Jon Sterling's forester tool for tending mathematical forests — syntax, escaping, verbatim, tree files, skill2tree conversion
version: 3.0.0
trit: 0
tags: [markup, math, documentation, bci-horse]
---

# Forester

Jon Sterling's ocaml-forester builds hypertext forests from .tree files. LaTeX-like but NOT LaTeX.

## One Construct

Everything is a command: backslash-name-braces. Example: backslash p brace-open text brace-close.

## Special Characters (Learned the Hard Way, 2026-04-04)

Forester requires balanced braces AND balanced parentheses. All of these are parse errors:

- Percent sign comments out the rest of the line (like LaTeX). Escape with backslash-percent.
- Hash introduces math mode when followed by brace-open. Bare hash without brace is fine.
- Backslash starts a command. Any backslash-word in text is parsed as a command name.
- Unbalanced brace-open or brace-close is a parse error.
- Unbalanced open-paren or close-paren is a parse error. "1) foo" breaks because close-paren has no matching open-paren.
- Dollar sign is fine as literal text. Do NOT escape as backslash-dollar (that breaks).
- Underscore is fine. Do NOT escape as backslash-underscore.
- Unicode (em-dash, multiplication sign, Greek letters) all work.

## Verbatim Spans

The verbatim mechanism uses a start-keyword and stop-keyword pair. Everything between them is literal — no parsing.

CRITICAL: The stop-keyword inside a verbatim block terminates it. There is no escape. You cannot represent the literal stop-keyword inside a verbatim block without splitting.

Workaround for content containing the stop-keyword: split into multiple verbatim spans, emitting the backslash separately via its own span, then "stopverb" as regular text. This is what skill2tree.hy's safe-verbatim function does.

The start-keyword must be followed by whitespace. Otherwise forester parses start-keyword-plus-text as a single unknown command name.

## Math

Forester uses hash-brace for math, NOT dollar-sign. Example: hash-brace-open x + y brace-close.

LaTeX math like dollar-sign-backslash-triangleleft-dollar-sign does NOT work in forester. If source markdown has LaTeX math, emit as verbatim.

## Commands

p, em, strong, code, pre, ul, ol, li, blockquote, subtree, title, taxon, meta, tag, import, transclude, def, author, date.

Double-bracket addr links to another tree.

## Tables

NOT built-in. Use HTML namespace macros from macros.tree: import macros, then use table, tr, th, td.

## Images

Via macro: image command with source argument. Put images in assets directory.

## Quiver Diagrams

Uses tikzcd via LaTeX. Requires latex binary. If missing, build crashes on those trees but all non-quiver trees parse fine.

## Config

forest.toml with trees (list of directories), assets, theme, root, base_url fields.

Build: forester build forest.toml (positional arg, not --config flag).

## skill2tree.hy Conversion Lessons (2026-04-04)

Bugs fixed during the session that converted 2053 skills to .tree files for bci.horse:

1. Path.parent and Path.name are properties, not methods. In Hy, use dot-attribute syntax, not method-call syntax.
2. Heading collection must track fence state. Hash-comments inside code blocks were being parsed as markdown headings, breaking subtree nesting.
3. Code blocks use pre-with-verbatim. The old pre-brace approach fails because braces inside code can't be escaped with backslash-brace (forester doesn't support that).
4. Percent must be escaped. It silently comments out the rest of the line including closing braces, causing "unexpected EOF" errors.
5. Hash does NOT need escaping. Bare hash is fine. Backslash-hash is an unknown TeX control sequence.
6. Code spans use verbatim-inside-code. Backslash-brace doesn't work for literal braces.
7. Start-keyword needs trailing space. Without it, start-keyword-plus-content is parsed as a single unknown command.
8. Parentheses must balance. Forester treats parens like braces. "1) foo" or "CVSS (v4.0" with unmatched paren is a parse error. Wrap unbalanced parens in verbatim.
9. Dangerous content detection. Paragraphs, list items, blockquotes, meta descriptions, and subtree titles containing backslashes, dollar signs, percent signs, or unbalanced parens/braces get emitted as verbatim instead of parsed inline.
10. Follow symlinks. Python Path.rglob does not follow symlinks. Use glob.glob which does.
11. Content containing the stop-keyword must be split into multiple verbatim spans.

## bci.horse Repo

plurigrid/horse on GitHub. CI via nix build with texliveFull. Deploy to Cloudflare Pages.

Tree prefixes: bcf- for BCI Factory content, skill-trees/ for converted skills.

The duplicate captp tree (exists in both trees/ and skill-trees/) is a non-fatal warning.

Transclude new devices in both bcf-0003.tree (The Stack) and bcf-0009.tree (Modalities Index).

### Critical: \import{macros} scoping

The Nix forester build (used for CI/deploy) scopes `\import` to the subtree it appears in. Sibling subtrees CANNOT see imports from other subtrees. 

**ALWAYS put `\import{macros}` at the TOP LEVEL of any tree that uses `\table`, `\image`, or other macro-defined commands.** Never nest it inside a `\subtree{}`.

This is the #1 cause of Nix build failures that pass local `forester build` — the local binary may be more lenient about scoping than the Nix derivation's version.

## Scope of import macros (learned 2026-04-04)

In forester, import is scoped to the subtree it appears in. If you import macros inside one subtree, sibling subtrees in the same file cannot use those macros. Always put import macros at the file's top level, not inside a subtree, unless you intentionally want to limit scope. The bcf-0036.tree CI failure was caused by import macros being inside one subtree while a sibling subtree used table.

## Duplicate tree addresses

If two .tree files resolve to the same address (filename without .tree), forester logs "skipping duplicate tree at address X". This is a warning, not fatal. In bci.horse, the captp tree exists in both trees/ and skill-trees/. Rename one or remove the duplicate if it matters.

## CI pipeline (plurigrid/horse)

The nix build runs forester with texliveFull. Any parse error or resolution error is fatal and fails the build. The localcharts sub-build has continue-on-error: true due to pre-existing missing-macros issues. The main bci-horse-forest build does NOT have continue-on-error. Deploy goes to Cloudflare Pages.

## skill2tree.hy

A 237-line Hy script at ~/worlds/skill2tree.hy that converts SKILL.md files to forester .tree files. Run as: hy skill2tree.hy ~/.claude/skills ./horse/skill-trees

Key functions: parse-frontmatter, convert-body, cvt-inline, escape-forester, has-dangerous-chars?, has-unbalanced?, safe-verbatim, eat-fence, eat-heading, eat-table, eat-list, eat-bquote, eat-para.

The dispatch table uses predicate dispatch (SDF pattern) to select the right block handler for each line type.
