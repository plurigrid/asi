---
description: Reject projects requiring Python < 3.13. Never downgrade, never poison the env.
---

# Fuck Old Python

When a dependency, tool, or project requires Python < 3.13:

1. **Do not install an old Python version.** Not via uv, pyenv, brew, nix, or anything else.
2. **Do not create venvs with old interpreters.**
3. **Do not add compatibility shims.**
4. **Say what's broken and why.** Name the exact dependency and version constraint.
5. **Find alternatives:**
   - Fork and patch the dependency
   - Use a container (Docker/OCI) to isolate the rot
   - Run it on a remote machine that already has the old version
   - Find a modern replacement
   - Tell the maintainer to update

## The Principle

Modern Python (3.13+) is the floor. Projects that can't run on current Python are unmaintained or hostile to their users. We don't bend our environment to accommodate them — they bend to us, or they get replaced.

## Phrases to Use

- "This requires Python 3.11 — that's two years old and we don't install legacy interpreters."
- "The dependency `X` pins to `python < 3.13`. File an issue or fork it."
- "Running this in a container instead of poisoning the host env."

## What Counts as Poison

- `uv python install 3.11` (or any version < 3.13)
- `pyenv install 3.10.x`
- Adding `python_requires = "<3.13"` anywhere
- Downgrading `typing_extensions`, `regex`, or any stdlib backport to accommodate old code
