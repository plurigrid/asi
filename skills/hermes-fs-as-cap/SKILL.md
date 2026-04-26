---
name: hermes-fs-as-cap
description: Replace Hermes' ambient filesystem authority (validate-then-open) with a Goblins single-directory capability. The LLM never holds an absolute path — it holds a forwarder cap that mediates every read/write. Capability discipline replaces guard-rail discipline.
type: bridge
parent: hermes-goblins-bridge
row: 16
proto: R
polarity: -1
status: stub
---

# hermes-fs-as-cap

Phase 1 (security floor). Closes the largest single source of LLM-prompt-injection blast radius: ambient access to the user's filesystem.

## Hermes signature

`/Users/bob/i/hermes-agent/tools/path_security.py`

```python
def validate_within_dir(path: Path, root: Path) -> Optional[str]:
    # Path.resolve() + relative_to(root) — returns error str, or None if safe
def has_traversal_component(path_str: str) -> bool:
    # parts contains '..'
```

Used by: `skill_manager_tool`, `skills_tool`, `skills_hub`, `cronjob_tools`, `credential_files`. Each tool re-validates on every call. Authority pattern: **validate-then-open** (TOCTOU-prone, depends on every caller remembering to call the validator).

`run_agent.py:327 _paths_overlap` adds parallelism safety on top.

## Goblins signature

`/Users/bob/i/goblins-adapter/` — a `^fs-cap` actor parameterised by a single allowed root, exposing `read`, `write`, `list`, `stat`, `subdir`. The LLM-side never sees an absolute path; the cap *is* the path-prefix.

```scheme
(define (^fs-cap bcom root)        ; root captured at construction; never serialized to LLM
  (methods
    ((read rel-path)   ...)
    ((write rel-path bytes) ...)
    ((list rel-path)   ...)
    ((subdir rel-path) (spawn ^fs-cap (path-append root rel-path)))))  ; attenuation
```

Subdirectory access = call `(<- root-cap 'subdir "skills")` — get back a *new cap* scoped to that subtree. Revocation = drop the forwarder.

## Translation table

| Hermes call | Goblins message | Notes |
|---|---|---|
| `open(path, "r")` | `(<- fs-cap 'read rel-path)` | rel-path is relative to cap's root, never absolute |
| `open(path, "w")` | `(<- fs-cap 'write rel-path bytes)` | atomic; no partial-write window |
| `os.listdir(d)` | `(<- fs-cap 'list rel-path)` | returns names, not Path objects |
| `validate_within_dir(p, root)` | (deleted) | impossible to violate — cap *is* the root |
| sub-tool with narrower scope | `(<- fs-cap 'subdir "skills")` | attenuation by construction |

## Failure modes (closed by this bridge)

- **TOCTOU between `validate_within_dir` and `open`** — Hermes resolves once then opens via raw `Path`; cap collapses both into one mediated op.
- **Symlink escape mid-write** — `^fs-cap` re-checks containment at the kernel-call boundary inside the vat.
- **Forgotten validator call** — every callsite that did `open(p)` without `validate_within_dir` is a vuln; with caps, there is no `open` to forget.
- **Prompt-injection-driven path crafting** — LLM cannot mention an absolute path because no cap to it exists in its scope.

## Failure modes (introduced; must mitigate)

- **Cap leakage via tool output** — if a tool returns a serialized cap to the LLM context, that's exactly what we want (the LLM can use it via the goblins-adapter Syrup socket); but if it leaks across session boundaries via memory backend, attenuation is lost. → Use Mandy nonce-registry pattern (Pattern B in parent SKILL): mount cap behind `/object/<base32-id>` URL; LLM context only contains the URL string.

## Test vector

```python
# Hermes-shaped entrypoint must reject:
fs.read("../../../etc/passwd")     # → CapError("path escapes")
fs.read("/etc/passwd")             # → CapError("absolute paths forbidden")
fs.read("symlink-to-outside")      # → CapError("resolved outside root")

# And accept:
sub = fs.subdir("skills")          # → returns new cap
sub.read("hermes-fs-as-cap/SKILL.md")   # OK — within sub.root
sub.read("../other-skill/SKILL.md")     # → CapError (sub is attenuated)
```

## Capability diff

| Property | Hermes (status quo) | Goblins (this bridge) |
|---|---|---|
| Authority source | ambient (process FS perms) | explicit cap reference |
| Revocation | restart process | drop forwarder |
| Attenuation | new validator + re-audit | `subdir` returns scoped cap |
| Audit trail | per-tool logging if remembered | every `<-` traversal goes through one chokepoint |
| Failure mode | forgotten check = silent escape | no cap = no call |

## Test-harness location

`~/i/goblins-adapter/tests/fs-cap-bisim.scm` (todo) — bisimulation against Python entrypoint shim. Passes iff Hermes call sequence and Goblins call sequence produce the same observable I/O for an oracle-chosen test set.

## Status: stub

Phase 1 priority. Blocks `hermes-skill-as-cap-module` (row 3), since skill loading reads from the FS.
