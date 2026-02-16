#!/bin/bash
# validate_plugin.sh - Trail of Bits style plugin validation
# Usage: ./scripts/validate_plugin.sh

set -e

PLUGIN_DIR="plugins/asi"
MARKETPLACE=".claude-plugin/marketplace.json"

echo "=== ASI Plugin Validation ==="
echo ""

# Check 1: Marketplace exists and has plugins array
echo "1. Checking marketplace.json..."
if [ -f "$MARKETPLACE" ]; then
    if jq -e '.plugins | length > 0' "$MARKETPLACE" > /dev/null 2>&1; then
        PLUGIN_COUNT=$(jq '.plugins | length' "$MARKETPLACE")
        echo "   ✓ marketplace.json has $PLUGIN_COUNT plugin(s)"
    else
        echo "   ✗ marketplace.json missing plugins array"
        exit 1
    fi
else
    echo "   ✗ marketplace.json not found"
    exit 1
fi

# Check 2: Plugin directory exists
echo "2. Checking plugin directory..."
if [ -d "$PLUGIN_DIR" ]; then
    echo "   ✓ $PLUGIN_DIR exists"
else
    echo "   ✗ $PLUGIN_DIR not found"
    exit 1
fi

# Check 3: Plugin has .claude-plugin/plugin.json
echo "3. Checking plugin.json..."
if [ -f "$PLUGIN_DIR/.claude-plugin/plugin.json" ]; then
    NAME=$(jq -r '.name' "$PLUGIN_DIR/.claude-plugin/plugin.json")
    VERSION=$(jq -r '.version' "$PLUGIN_DIR/.claude-plugin/plugin.json")
    echo "   ✓ plugin.json: $NAME v$VERSION"
else
    echo "   ✗ plugin.json not found in $PLUGIN_DIR/.claude-plugin/"
    exit 1
fi

# Check 4: Skills have valid frontmatter
echo "4. Validating SKILL.md frontmatter..."
SKILL_COUNT=0
MISSING_NAME=0
MISSING_DESC=0

for skill in "$PLUGIN_DIR/skills/"*/SKILL.md; do
    if [ -f "$skill" ]; then
        SKILL_COUNT=$((SKILL_COUNT + 1))
        
        if ! head -30 "$skill" | grep -qE '^name:'; then
            echo "   ✗ Missing name: $skill"
            MISSING_NAME=$((MISSING_NAME + 1))
        fi
        
        if ! head -30 "$skill" | grep -qE '^description:'; then
            echo "   ✗ Missing description: $skill"
            MISSING_DESC=$((MISSING_DESC + 1))
        fi
    fi
done

if [ $MISSING_NAME -eq 0 ] && [ $MISSING_DESC -eq 0 ]; then
    echo "   ✓ All $SKILL_COUNT skills have valid frontmatter"
else
    echo "   ✗ $MISSING_NAME missing name, $MISSING_DESC missing description"
    exit 1
fi

# Check 5: Skill connectivity (Tier 1 = present in all AI tools)
echo "5. Checking skill connectivity..."
TIER1_COUNT=$(comm -12 <(ls ~/.claude/skills 2>/dev/null | sort) <(ls ~/.codex/skills 2>/dev/null | sort) 2>/dev/null | \
              comm -12 - <(ls ~/.gemini/skills 2>/dev/null | sort) 2>/dev/null | \
              comm -12 - <(ls ~/.config/goose/skills 2>/dev/null | sort) 2>/dev/null | wc -l | tr -d ' ')
echo "   ✓ $TIER1_COUNT Tier 1 skills (present in Claude + Codex + Gemini + Goose)"

echo ""
echo "=== Validation Complete ==="
echo "Total skills: $SKILL_COUNT"
echo "Tier 1 skills: $TIER1_COUNT"
echo ""
echo "To install:"
echo "  /plugin marketplace add ./"
echo "  /plugin install asi@asi"
