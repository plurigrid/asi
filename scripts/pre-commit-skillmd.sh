#!/usr/bin/env bash
# Pre-commit hook: lint only the SKILL.md files staged for this commit, using the
# same codex-rs-faithful oracle as CI. Install with:
#   ln -sf ../../scripts/pre-commit-skillmd.sh .git/hooks/pre-commit
# Bypass once with: git commit --no-verify
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

# Only run if SKILL.md files are staged.
mapfile -t staged < <(git diff --cached --name-only --diff-filter=ACM | grep -E '(^|/)SKILL\.md$' || true)
[ ${#staged[@]} -eq 0 ] && exit 0

# Prefer flox-provided bb if a .flox env is present, else system bb.
if [ -d .flox ] && command -v flox >/dev/null 2>&1; then
  BB=(flox activate -- bb)
else
  BB=(bb)
fi

# Lint the whole skills/ tree (the oracle is fast: pmap over all files).
if ! "${BB[@]}" scripts/skillmd_lint.bb skills; then
  echo ""
  echo "✗ SKILL.md frontmatter would fail to load in codex/claude/agy."
  echo "  Auto-fix:  bb scripts/skillmd_lint.bb skills --apply"
  echo "  Bypass:    git commit --no-verify  (not recommended)"
  exit 1
fi
