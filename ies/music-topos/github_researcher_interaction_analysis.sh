#!/bin/bash
#
# GitHub Researcher Interaction Analysis
# Analyzes interactions between Terence Tao, Knoroiov researchers, and Jonathan Gorard
# Uses: gh CLI + jq for parsing
#

set -e

WORK_DIR="/tmp/github_research_analysis"
mkdir -p "$WORK_DIR"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${BLUE}=== GitHub Researcher Interaction Analysis ===${NC}\n"

# ============================================================================
# FUNCTION: Execute GraphQL query
# ============================================================================

execute_gh_query() {
  local query_name="$1"
  local query_string="$2"
  local output_file="${WORK_DIR}/${query_name}.json"

  echo -e "${YELLOW}[Query]${NC} Executing: $query_name"

  # Execute gh graphql and save to file
  if gh api graphql -f "query=$query_string" > "$output_file" 2>/dev/null; then
    local count=$(jq '.data.search.issueCount // 0' "$output_file" 2>/dev/null || echo 0)
    echo -e "${GREEN}✓${NC} Found $count results\n"
    echo "$output_file"
  else
    echo -e "${RED}✗ Query failed${NC}\n"
    echo ""
  fi
}

# ============================================================================
# FUNCTION: Extract interactions with participant count
# ============================================================================

extract_high_impact_interactions() {
  local json_file="$1"
  local min_participants="${2:-3}"
  local output_file="${WORK_DIR}/high_impact.json"

  jq --arg min_p "$min_participants" '.data.search.edges[] |
    select(.node.participants.totalCount >= ($min_p | tonumber)) |
    {
      id: .node.id,
      title: .node.title,
      url: .node.url,
      author: .node.author.login,
      created_at: .node.createdAt,
      updated_at: .node.updatedAt,
      participant_count: .node.participants.totalCount,
      participants: [.node.participants.edges[].node.login],
      comments_count: .node.comments.totalCount
    }' "$json_file" > "$output_file" 2>/dev/null

  echo "$output_file"
}

# ============================================================================
# FUNCTION: Find temporal overlaps
# ============================================================================

find_temporal_overlaps() {
  local file1="$1"
  local file2="$2"
  local window_days="${3:-30}"
  local output_file="${WORK_DIR}/temporal_overlaps.json"

  jq -s --arg days "$window_days" '
    ([.[0][] | .created_at] | sort) as $first_dates |
    ([.[1][] | .created_at] | sort) as $second_dates |
    [
      range(0; .[0] | length) as $i |
      range(0; .[1] | length) as $j |
      {
        interaction1: .[0][$i],
        interaction2: .[1][$j],
        shared_participants: (([.[0][$i].participants, .[1][$j].participants] | flatten | unique) as $all | $all)
      } |
      select((.interaction1.created_at | fromdateiso8601) -
             (.interaction2.created_at | fromdateiso8601) |
             fabs <= ($days | tonumber * 86400))
    ] |
    sort_by((.shared_participants | length)) | reverse
  ' "$file1" "$file2" > "$output_file" 2>/dev/null

  echo "$output_file"
}

# ============================================================================
# QUERY 1: Terence Tao interactions
# ============================================================================

echo -e "${BLUE}[1] Terence Tao Interactions${NC}"

TAO_QUERY='query {
  search(query: "author:terrytao type:issue", type: ISSUE, first: 50) {
    issueCount
    edges {
      node {
        ... on Issue {
          id
          title
          url
          createdAt
          updatedAt
          author {
            login
          }
          comments(first: 50) {
            totalCount
          }
          participants(first: 50) {
            totalCount
            edges {
              node {
                login
              }
            }
          }
        }
      }
    }
  }
}'

TAO_FILE=$(execute_gh_query "tao_interactions" "$TAO_QUERY")

# ============================================================================
# QUERY 2: Knoroiov/Kolmogorov related interactions
# ============================================================================

echo -e "${BLUE}[2] Knoroiov/Kolmogorov Theory Interactions${NC}"

KNOR_QUERY='query {
  search(query: "Knoroiov OR Kolmogorov OR \"metric space complexity\" type:issue",
         type: ISSUE, first: 50) {
    issueCount
    edges {
      node {
        ... on Issue {
          id
          title
          url
          createdAt
          updatedAt
          author {
            login
          }
          comments(first: 50) {
            totalCount
          }
          participants(first: 50) {
            totalCount
            edges {
              node {
                login
              }
            }
          }
        }
      }
    }
  }
}'

KNOR_FILE=$(execute_gh_query "knoroiov_interactions" "$KNOR_QUERY")

# ============================================================================
# QUERY 3: Tao × Knoroiov Intersection
# ============================================================================

echo -e "${BLUE}[3] Tao × Knoroiov Intersection${NC}"

CROSS_QUERY='query {
  search(query: "(terrytao OR Tao) AND (Knoroiov OR Kolmogorov OR complexity-theory) type:issue",
         type: ISSUE, first: 50) {
    issueCount
    edges {
      node {
        ... on Issue {
          id
          title
          url
          createdAt
          updatedAt
          author {
            login
          }
          comments(first: 50) {
            totalCount
          }
          participants(first: 50) {
            totalCount
            edges {
              node {
                login
              }
            }
          }
        }
      }
    }
  }
}'

CROSS_FILE=$(execute_gh_query "tao_knoroiov_cross" "$CROSS_QUERY")

# ============================================================================
# QUERY 4: Jonathan Gorard interactions
# ============================================================================

echo -e "${BLUE}[4] Jonathan Gorard Interactions${NC}"

GORARD_QUERY='query {
  search(query: "author:jonathangorard type:issue", type: ISSUE, first: 50) {
    issueCount
    edges {
      node {
        ... on Issue {
          id
          title
          url
          createdAt
          updatedAt
          author {
            login
          }
          comments(first: 50) {
            totalCount
          }
          participants(first: 50) {
            totalCount
            edges {
              node {
                login
              }
            }
          }
        }
      }
    }
  }
}'

GORARD_FILE=$(execute_gh_query "gorard_interactions" "$GORARD_QUERY")

# ============================================================================
# FILTER HIGH-IMPACT (3+ participants)
# ============================================================================

echo -e "${BLUE}[5] Filtering High-Impact Interactions (3+ participants)${NC}\n"

if [ -f "$TAO_FILE" ]; then
  TAO_IMPACT=$(extract_high_impact_interactions "$TAO_FILE" 3)
  TAO_COUNT=$(jq 'length' "$TAO_IMPACT" 2>/dev/null || echo 0)
  echo -e "${GREEN}✓${NC} Tao high-impact: $TAO_COUNT interactions"
fi

if [ -f "$KNOR_FILE" ]; then
  KNOR_IMPACT=$(extract_high_impact_interactions "$KNOR_FILE" 3)
  KNOR_COUNT=$(jq 'length' "$KNOR_IMPACT" 2>/dev/null || echo 0)
  echo -e "${GREEN}✓${NC} Knoroiov high-impact: $KNOR_COUNT interactions"
fi

if [ -f "$CROSS_FILE" ]; then
  CROSS_IMPACT=$(extract_high_impact_interactions "$CROSS_FILE" 3)
  CROSS_COUNT=$(jq 'length' "$CROSS_IMPACT" 2>/dev/null || echo 0)
  echo -e "${GREEN}✓${NC} Tao × Knoroiov high-impact: $CROSS_COUNT interactions\n"
fi

# ============================================================================
# FIND TEMPORAL OVERLAPS
# ============================================================================

echo -e "${BLUE}[6] Finding Temporal Alignments with Gorard${NC}\n"

if [ -f "$CROSS_IMPACT" ] && [ -f "$GORARD_FILE" ]; then
  GORARD_IMPACT=$(extract_high_impact_interactions "$GORARD_FILE" 1)
  OVERLAPS=$(find_temporal_overlaps "$CROSS_IMPACT" "$GORARD_IMPACT" 60)

  OVERLAP_COUNT=$(jq 'length' "$OVERLAPS" 2>/dev/null || echo 0)
  echo -e "${GREEN}✓${NC} Found $OVERLAP_COUNT temporal alignments\n"

  # Show top alignments
  echo -e "${YELLOW}=== TOP TEMPORAL ALIGNMENTS ===${NC}\n"
  jq -r '.[:5][] |
    "• Tao interaction: \(.interaction1.title)\n" +
    "  Author: \(.interaction1.author)\n" +
    "  Gorard interaction: \(.interaction2.title)\n" +
    "  Shared participants: \(.shared_participants | length)\n"' \
    "$OVERLAPS" 2>/dev/null || echo "No alignments found"
fi

# ============================================================================
# ANALYZE PARTICIPANT NETWORKS
# ============================================================================

echo -e "\n${BLUE}[7] Analyzing Participant Networks${NC}\n"

if [ -f "$CROSS_IMPACT" ]; then
  echo -e "${YELLOW}=== Most Active Participants in Tao × Knoroiov ===${NC}\n"

  jq -r '.[] | .participants[]' "$CROSS_IMPACT" 2>/dev/null | \
    sort | uniq -c | sort -rn | head -10 | \
    awk '{print "  " $2 ": " $1 " interactions"}' || echo "  No data"
fi

# ============================================================================
# CLUSTER BY CONCEPTUAL THEME
# ============================================================================

echo -e "\n${BLUE}[8] Clustering by Conceptual Theme${NC}\n"

if [ -f "$CROSS_IMPACT" ]; then
  echo -e "${YELLOW}=== Theme Distribution ===${NC}\n"

  jq -r '.[] | .title' "$CROSS_IMPACT" 2>/dev/null | \
    grep -o 'complexity\|metric\|space\|algorithm\|theorem\|proof' | \
    sort | uniq -c | sort -rn | \
    awk '{print "  " $2 ": " $1 " mentions"}' || echo "  No theme data"
fi

# ============================================================================
# GENERATE SHORTLIST REPORT
# ============================================================================

echo -e "\n${BLUE}[9] Generating Shortlist Report${NC}\n"

REPORT_FILE="${WORK_DIR}/SHORTLIST_REPORT.md"

cat > "$REPORT_FILE" << 'EOF'
# GitHub Researcher Interaction Analysis Report

## Executive Summary

This analysis examines high-impact interactions between:
- **Terence Tao** (@terrytao) - Mathematics researcher
- **Knoroiov Theory** - Researchers working on Kolmogorov complexity & metric spaces
- **Jonathan Gorard** (@jonathangorard) - Computational research

### Methodology
1. Queried GitHub issues/PRs authored or participated by each researcher
2. Filtered for high-impact interactions (3+ participants)
3. Analyzed temporal overlap windows (60-day sliding window)
4. Identified shared participant networks
5. Clustered by conceptual theme

EOF

if [ -f "$CROSS_IMPACT" ]; then
  CROSS_COUNT=$(jq 'length' "$CROSS_IMPACT" 2>/dev/null || echo 0)

  cat >> "$REPORT_FILE" << EOF

## Key Findings

### Tao × Knoroiov Interactions: $CROSS_COUNT high-impact instances

#### Top Interactions by Participant Count

EOF

  jq -r '.[] |
    "- **\(.title)**\n" +
    "  - Author: \(.author)\n" +
    "  - Participants: \(.participant_count)\n" +
    "  - URL: \(.url)\n" +
    "  - Created: \(.created_at)\n"' \
    "$CROSS_IMPACT" 2>/dev/null | head -20 >> "$REPORT_FILE"
fi

if [ -f "$OVERLAPS" ]; then
  OVERLAP_COUNT=$(jq 'length' "$OVERLAPS" 2>/dev/null || echo 0)

  cat >> "$REPORT_FILE" << EOF

### Gorard Temporal Alignments: $OVERLAP_COUNT instances

#### Instances where Gorard participated temporally near Tao × Knoroiov interactions

EOF

  jq -r '.[:5][] |
    "- Gorard: **\(.interaction2.title)**\n" +
    "  Tao: \(.interaction1.title)\n" +
    "  Gap: \((.interaction2.created_at | fromdateiso8601) - (.interaction1.created_at | fromdateiso8601) | . / 86400 | floor) days\n" +
    "  Shared: \(.shared_participants | join(\", \"))\n\n"' \
    "$OVERLAPS" 2>/dev/null >> "$REPORT_FILE" || true
fi

cat >> "$REPORT_FILE" << 'EOF'

## Recommendations

1. **Follow highest-impact clusters**: Interactions with 5+ participants
2. **Track temporal alignments**: Monitor when all three researchers are active
3. **Monitor cross-repository initiatives**: Look for coordinated projects
4. **Analyze participant flow**: Trace knowledge transfer between researchers

---

*Report generated by GitHub Researcher Interaction Analysis*
EOF

echo -e "${GREEN}✓${NC} Report saved to: $REPORT_FILE\n"

# ============================================================================
# FINAL SUMMARY
# ============================================================================

echo -e "${GREEN}=== Analysis Complete ===${NC}\n"
echo "Results saved to: $WORK_DIR"
echo ""
echo "Files generated:"
ls -lh "$WORK_DIR" | tail -n +2 | awk '{print "  - " $9 " (" $5 ")"}'

echo ""
echo -e "${BLUE}Next steps:${NC}"
echo "1. Review: cat $REPORT_FILE"
echo "2. Analyze: jq '.[]' ${WORK_DIR}/high_impact.json"
echo "3. Export: cp ${WORK_DIR}/*.json /Users/bob/ies/music-topos/"
