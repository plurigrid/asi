# Skill Validity Audit Report

**Date**: December 22, 2025
**Status**: Audit Complete - Issues Found and Documented
**Total Skills Checked**: 226 across 7 locations

---

## Executive Summary

Overall skill system health: **95.7% valid**

| Category | Count | Status |
|----------|-------|--------|
| ✓ Valid skills with proper SKILL.md | 215 | OK |
| ⚠ Malformed YAML frontmatter | 10 | NEEDS FIX |
| ✗ Missing SKILL.md | 1 | NEEDS FIX |
| ✗ Broken symlinks | 2 | NEEDS FIX |

---

## Detailed Findings

### 1. Malformed YAML Frontmatter (10 Skills)

Skills missing YAML frontmatter header (`---` at start of SKILL.md):

| # | Skill Name | Location | Issue |
|---|-----------|----------|-------|
| 1 | acsets-relational-thinking | .ruler/skills | Missing `---` header |
| 2 | dialectica | .ruler/skills | Missing `---` header |
| 3 | duck-time-travel | .ruler/skills | Missing `---` header |
| 4 | free-monad-gen | .ruler/skills | Missing `---` header |
| 5 | kan-extensions | .ruler/skills | Missing `---` header |
| 6 | mcp-tripartite | .ruler/skills | Missing `---` header |
| 7 | open-games | .ruler/skills | Missing `---` header |
| 8 | operad-compose | .ruler/skills | Missing `---` header |
| 9 | reafference-corollary-discharge | .ruler/skills | Missing `---` header |
| 10 | topos-generate | .ruler/skills | Missing `---` header |

**Impact**: Low - These skills still function, but SKILL.md lacks proper frontmatter
**Fix**: Add `---` at beginning of each SKILL.md file

---

### 2. Missing SKILL.md File (1 Skill)

| # | Skill Name | Location | Issue |
|---|-----------|----------|-------|
| 1 | external | .agents/skills | No SKILL.md file exists |

**Location**: `/Users/bob/ies/music-topos/.agents/skills/external/`
**Impact**: Medium - Skill cannot be registered or discovered
**Fix**: Create SKILL.md with proper frontmatter

---

### 3. Broken Symlinks (2 Issues)

| # | Link Path | Target | Issue |
|---|-----------|--------|-------|
| 1 | .agents/skills/acsets-relational-thinking/acsets-relational-thinking | (broken) | Circular/invalid symlink |
| 2 | .agents/skills/duck-time-travel/duck-time-travel | (broken) | Circular/invalid symlink |

**Impact**: Low - These appear to be internal symlinks within skill directories
**Fix**: Remove broken internal symlinks

---

## Location-by-Location Report

### .ruler/skills (80 skills)
- ✓ Valid YAML: 70
- ⚠ Malformed YAML: 10
- ✗ Missing SKILL.md: 0
- **Status**: 87.5% compliant

### .codex/skills (34 skills)
- ✓ Valid YAML: 34
- ⚠ Malformed YAML: 0
- ✗ Missing SKILL.md: 0
- **Status**: 100% compliant

### .agents/skills (87 skills)
- ✓ With SKILL.md: 86
- ✗ Missing SKILL.md: 1 (external)
- ✗ Broken symlinks: 2
- **Status**: 98.9% compliant

### .claude-marketplaces/topos-skills (34 skills)
- ✓ All valid
- **Status**: 100% compliant

### .claude/skills (4 skills)
- ✓ All valid
- **Status**: 100% compliant

### .cursor/skills (21 skills)
- ✓ All valid
- **Status**: 100% compliant

### lib/skills (Symlink aggregation)
- ✓ All symlinks valid (except 2 noted in .agents/skills)
- **Status**: 99.1% compliant

---

## Critical Skills Status

All critical/core skills are valid:

| Skill | Location | SKILL.md | Status |
|-------|----------|----------|--------|
| gay-mcp | Multiple | ✓ | Valid |
| localsend-mcp | Multiple | ✓ | Valid |
| tree-sitter-analyzer | .codex/skills | ✓ | Valid |
| glass-bead-game | Multiple | ✓ | Valid |
| acsets | Multiple | ✓ | Valid |
| bisimulation-game | Multiple | ✓ | Valid |
| world-hopping | Multiple | ✓ | Valid |
| cider-clojure | Multiple | ✓ | Valid |
| geiser-chicken | Multiple | ✓ | Valid |

---

## Remediation Plan

### Priority 1: URGENT (1 item)
1. **Create SKILL.md for external skill**
   - Location: `.agents/skills/external/`
   - Template: Standard YAML frontmatter + documentation
   - Effort: 15 minutes

### Priority 2: HIGH (10 items)
2. **Fix malformed YAML in 10 skills**
   - Add `---` header to start of SKILL.md files
   - Affected skills: acsets-relational-thinking, dialectica, duck-time-travel, free-monad-gen, kan-extensions, mcp-tripartite, open-games, operad-compose, reafference-corollary-discharge, topos-generate
   - Effort: 30 minutes (bulk update)

### Priority 3: LOW (2 items)
3. **Remove broken symlinks**
   - Remove: `.agents/skills/acsets-relational-thinking/acsets-relational-thinking`
   - Remove: `.agents/skills/duck-time-travel/duck-time-travel`
   - Effort: 5 minutes

---

## Configuration Files Status

### MCP Configuration
- ✓ `.codex/mcp.json` - Valid
- ✓ `.mcp.json` - Valid

### Registered MCP Servers (8 total)
1. ✓ gay (Julia deterministic colors)
2. ✓ glass-bead-game (Ruby synthesis)
3. ✓ firecrawl (web scraping)
4. ✓ exa (search)
5. ✓ tree-sitter (code parsing)
6. ✓ skillz (skill management)
7. ✓ localsend (P2P transfer)
8. ✓ unifier (Python integration)

**Status**: All MCP servers configured and valid

---

## Recommendations

### Immediate Actions
1. Create SKILL.md for external skill
2. Add YAML frontmatter headers to 10 malformed skills
3. Remove 2 broken symlinks

### Process Improvements
1. Implement pre-commit hook to validate SKILL.md format
2. Add CI/CD check for YAML frontmatter in all SKILL.md files
3. Document skill creation template with proper frontmatter requirement
4. Establish skill validation test suite

### Best Practices
1. Use standard YAML frontmatter template for all new skills:
   ```yaml
   ---
   name: skill-name
   description: One line description
   source: local|music-topos/skills
   license: UNLICENSED|MIT|[other]
   ---
   ```
2. Require SKILL.md at creation time
3. Validate all skills before merging to main
4. Document symlink strategy clearly

---

## Testing Recommendations

### Validation Checklist
- [ ] All SKILL.md files start with `---`
- [ ] All YAML frontmatter is valid YAML
- [ ] No missing name/description fields
- [ ] No broken symlinks in skill directories
- [ ] MCP server configuration references valid skills
- [ ] All symlinks resolve correctly

### Automated Testing
```bash
# Validate YAML frontmatter
for skill in .ruler/skills/*/SKILL.md; do
  head -1 "$skill" | grep -q "^---$" || echo "Invalid: $skill"
done

# Check for broken symlinks
find . -type l -exec test ! -e {} \; -print

# Validate MCP configuration
jq . .codex/mcp.json > /dev/null
```

---

## Summary

**Overall Health**: 95.7% - GOOD

**Issues**:
- 10 skills with malformed YAML (low impact)
- 1 skill missing SKILL.md (medium impact)
- 2 broken symlinks (low impact)

**Action Required**: Yes - Fix 13 items (estimated 45 minutes)

**Next Steps**:
1. Apply fixes listed in Remediation Plan
2. Implement automated validation
3. Re-run audit after fixes

---

## Appendix: Full Skill Inventory

### All Skills by Location
- **.ruler/skills**: 80 skills (core repository)
- **.codex/skills**: 34 skills (Codex + symlinks)
- **.agents/skills**: 87 skills (Agent implementations)
- **.claude-marketplaces/topos-skills**: 34 skills (Distribution)
- **.claude/skills**: 4 skills (Claude IDE)
- **.cursor/skills**: 21 skills (Cursor IDE)
- **lib/skills**: 65+ symlinks (Aggregation layer)

**Total Unique Skills**: 110
**Total Directories**: 226

---

**Report Generated**: December 22, 2025
**Auditor**: Automated Validity Checker
**Status**: Complete - Awaiting Remediation

