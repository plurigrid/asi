---
name: worlding-calendar
description: Calendar events tied to 26 letter-worlds via org-mode. Links events to beeper messages, voice notes, and Goblins capabilities. Replaces 13K-token Google Calendar MCP with CalDAV + DuckDB interactome.
version: 1.0.0
trit: 0
role: ERGODIC
color: "#fabd2f"
hue: 45
tags: [calendar, org-mode, caldav, beeper, goblins, worlds, emacs]
deployed: 2026-03-26
evolves: calendar-acset
---

# Worlding Calendar

Every calendar event contributes to a world. This skill manages that mapping.

## Architecture

```
                CalDAV (Google)
                     │
   voice notes ──→ org-worlding-calendar.el ←── beeper messages
                     │
              ~/worlds/p/calendar.org
                     │
        ┌────────────┼────────────┐
        ▼            ▼            ▼
   :WORLD: a    :WORLD: b    :WORLD: g ...
   ~/worlds/a/  ~/worlds/b/  ~/worlds/g/
```

## Three Layers

| Layer | Source | Function |
|-------|--------|----------|
| **Org** | `~/worlds/p/calendar.org` | Canonical event store with world tags |
| **DuckDB** | `~/worlds/beeper_interactome.duckdb` | Contact→world inference from messaging history |
| **Emacs** | `~/.emacs.d/lisp/org-worlding-calendar.el` | UI, transient menus, agenda views |

## World Inference

Events are auto-tagged with `:WORLD:` letter based on content:

```
"barton bci meeting" → :WORLD: b
"goblins ocapn sync" → :WORLD: g
"vivarium hackathon" → :WORLD: v
"plurigrid standup"  → :WORLD: p
```

Inference uses regex patterns + DuckDB interactome queries on beeper contact names.

## Properties Per Event

```org
* RISING Yoyo hackathon prep
:PROPERTIES:
:WORLD: y
:WORLD_PATH: ~/worlds/y/
:BEEPER_CHAT: !0xZ1HWPM91hEOzuwxzBR:beeper.local
:VOICE_NOTE: ~/Library/Application Support/BeeperTexts/media/...
:OCAPN_REF: ocapn://...
:CREATED: [2026-03-26 Thu]
:END:
<2026-03-26 Thu 14:00>--<2026-03-26 Thu 16:00>
```

## Worlding States (from org-worlding.el)

Events use worlding states instead of TODO/DONE:

| State | Meaning | Calendar use |
|-------|---------|-------------|
| SEEDING | Sub-threshold | Tentative, not confirmed |
| RISING | Gaining amplitude | Confirmed, approaching |
| RESONANT | Phase-locked | Happening NOW |
| WAVE | Self-sustaining | Recurring/habit |
| ERGODIC | Full exploration | Open-ended session |
| ACTIVE | Self-sustaining | Ongoing project event |
| BEATING | Interference | Conflict/double-booked |
| DRIVEN | Externally forced | Obligation/external |
| STABLE | Fixed point | Completed, archived |
| FADED | Below threshold | Cancelled/no-showed |

## Emacs Keybindings

```
C-c w c e  → Create world-tagged event
C-c w c v  → Link voice note to event
C-c w c b  → Link beeper message to event
C-c w c c  → Set OCapN capability ref
C-c w c C  → Agenda grouped by world
C-c w W    → Worlding dashboard
```

## Querying from Claude Code

### List events by world
```bash
grep -A5 ":WORLD: b" ~/worlds/p/calendar.org
```

### Query interactome for contact→world mapping
```bash
duckdb ~/worlds/beeper_interactome.duckdb -c "
SELECT name, protocol, sent, total
FROM interactome
WHERE lower(name) LIKE '%barton%'
"
```

### Create event from CLI
```bash
emacsclient -e '(org-worlding-calendar-new-event "Boris sync" "2026-03-27" "2026-03-27" "b")'
```

### View calendar agenda
```bash
emacsclient -e '(org-agenda nil "C")'
```

## CalDAV Sync (Planned)

Google Calendar CalDAV endpoint: `https://apidata.googleusercontent.com/caldav/v2/`

Auth via OAuth2 token from `fnox get GOOGLE_CLIENT_SECRET_PATH`. Bidirectional sync:
- Google → org: pull events, auto-tag with :WORLD:
- org → Google: push world-tagged events to specific sub-calendars per letter

Replaces Anthropic's `claude_ai_Google_Calendar` MCP (13,566 tokens) with ~0 tokens (local org files + emacsclient calls).

## Goblins Integration

Each event source is modeled as a Goblins capability:

```scheme
;; CalDAV server as actor
(define caldav-cap
  (vat-spawn vat
    (lambda (bcom)
      (methods
        ((list-events start end) ...)
        ((create-event title start end world) ...)))))

;; Beeper chat as capability reference
(define beeper-cap
  (vat-spawn vat
    (lambda (bcom)
      (methods
        ((search query) ...)
        ((send chat-id text) ...)))))
```

Events store their source capability as `:OCAPN_REF:` — a sturdyref URI that can be resolved at runtime to interact with the originating system.

## Files

| File | Purpose |
|------|---------|
| `~/.emacs.d/lisp/org-worlding-calendar.el` | Emacs integration |
| `~/worlds/p/calendar.org` | Event store |
| `~/worlds/beeper_interactome.duckdb` | Contact intelligence |
| `~/.claude/skills/worlding-calendar/SKILL.md` | This skill |

## Relation to Other Skills

- **beeper** — message source, contact→world inference
- **calendar-acset** — predecessor (GF(3) theoretical framework)
- **goblins** — capability model for event sources
- **emacs** / **org** — UI layer
- **sdf** — if events need spatial world coordinates
- **tree-sitter** — if parsing structured event descriptions
