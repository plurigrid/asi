# Abductive Repository Analysis: GitHub + DuckDB + Color Semantics

## Overview

This system implements **abductive reasoning** (as formulated by Matteo Capucci) to analyze repositories and assign semantic colors based on observed effects.

### What is Abduction?

**Abduction** is inference to the best explanation:
- **Deduction**: Cause → Effect (if premises true, conclusion must be true)
- **Induction**: Effect → Cause (many observations suggest a pattern)
- **Abduction**: Effect → Best Explanation (what's the most likely cause?)

Example:
```
Observation: Repository has 50 commits, 5 contributors, updated yesterday
Deduction:   IF (50 commits AND 5 contributors) THEN active project
Induction:   Many repos with commits AND contributors are active → likely active
Abduction:   What best explains these observations? → "Collaborative project"
```

## Architecture

```
GitHub (via gh CLI)         DuckDB (Analysis)         Abductive Engine       Color Assignment
─────────────────            ─────────────            ─────────────────      ────────────────
Repositories                 repositories table       Abduction protocol     Category → Hue
Interactions                 interactions table       Effect observer        Activity → Saturation
Pull Requests       →        colors table      →     Cause inference   →    Maturity → Lightness
Issues                       abductions table         Confidence scoring     Result: Hex Color
Commits                      (SQL queries)           (Protocol based)
Contributors
```

## Components

### 1. GitHub CLI Integration

```clojure
(gh-list-repos)                    ; List all repos
(gh-get-repo-interactions repo)    ; Fetch commits, PRs, issues
(gh-repo-stats repo)               ; Stars, forks, language, etc.
```

**Output**: JSON data about repository activity and metadata.

### 2. DuckDB Schema

```sql
repositories:
  - id, name, owner, description
  - language, stars, forks, issues
  - created_at, updated_at
  - activity_level, category

interactions:
  - type (commit, pull_request, issue)
  - author, created_at, count
  - repo_id (foreign key)

colors:
  - repo_id, hue, saturation, lightness, hex
  - reasoning (why this color?)
  - assigned_at

abductions:
  - repo_id, cause, effect, confidence
  - evidence (what observations led here?)
```

### 3. Abductive Reasoning Engine

```clojure
(defprotocol IAbduction
  (observe-effects [this])           ; What effects do we see?
  (infer-causes [this effects])      ; What causes best explain them?
  (compute-confidence [this cause])  ; How confident are we?
  (explain [this]))                  ; Return full explanation
```

**Example**:
```clojure
Effects observed:
  - 150 commits
  - 8 contributors
  - 50 stars
  - Updated yesterday

Inferred causes (ranked by confidence):
  1. "Active collaborative development" (0.95)
  2. "Rapidly growing project" (0.82)
  3. "Community-driven effort" (0.78)
```

### 4. Color Assignment (Abductive Coloring)

Colors are assigned based on **inferred categories**:

```
Category          Hue    Reasoning
────────────────  ───────────────────────────────────────────
Library           0°     Foundational (RED)
Infrastructure    90°    System-level (LIME)
Tool              120°   Practical utility (GREEN)
Framework         240°   Structural (BLUE)
Application       180°   Concrete output (CYAN)
Example/Learning  60°    Educational (YELLOW)
Inactive          300°   Archived/sleeping (MAGENTA)

Saturation ← Activity Level
  Recent updates = 0.9 (vibrant)
  1 month old = 0.6 (moderate)
  1 year old = 0.3 (muted)

Lightness ← Maturity (stars + age)
  1000+ stars, 5+ years = 0.85 (bright, mature)
  100-1000 stars, 2 years = 0.6 (moderate)
  <100 stars, <1 year = 0.35 (dark, emerging)
```

## Abductive Inference Examples

### Example 1: Active Tool

```
Repository: ripgrep
Observations:
  ├─ 30,000+ commits
  ├─ 50+ contributors
  ├─ 40,000+ stars
  ├─ Updated 2 days ago
  └─ Language: Rust

Abduction:
  Cause: "Widely-used, well-maintained tool"
  Confidence: 0.98

Color:
  Hue: 120° (Tool category)
  Saturation: 0.9 (very recent update)
  Lightness: 0.85 (high maturity)
  Result: #00DD55 (bright green)
```

### Example 2: Emerging Learning Project

```
Repository: learning-clojure
Observations:
  ├─ 50 commits
  ├─ 2 contributors
  ├─ 10 stars
  ├─ Updated 1 month ago
  └─ Language: Clojure

Abduction:
  Cause: "Educational project, moderate activity"
  Confidence: 0.87

Color:
  Hue: 60° (Example/Learning category)
  Saturation: 0.5 (moderate activity)
  Lightness: 0.4 (young, not yet widely adopted)
  Result: #AA8822 (muted yellow)
```

### Example 3: Archived Library

```
Repository: old-json-parser
Observations:
  ├─ 2,000 commits
  ├─ 5 contributors
  ├─ 500 stars
  ├─ Updated 2 years ago
  ├─ No recent PRs
  └─ Language: Python

Abduction:
  Cause: "Stable but inactive library"
  Confidence: 0.92

Color:
  Hue: 0° (Library category)
  Saturation: 0.2 (no recent activity)
  Lightness: 0.65 (was mature, now sleeping)
  Result: #CC4444 (pale red)
```

## Query Examples

### Combined GraphQL + DuckDB Query

```sql
-- Fetch via GraphQL (GitHub API)
query {
  viewer {
    repositories(first: 50) {
      nodes {
        name
        stargazerCount
        updatedAt
        primaryLanguage { name }
        issues { totalCount }
        pullRequests { totalCount }
      }
    }
  }
}

-- Then store in DuckDB and analyze:
SELECT
  r.name,
  r.category,
  c.hex,
  r.stars,
  COUNT(i.id) as recent_interactions,
  AVG(DATEDIFF(DAY, i.created_at, NOW())) as avg_days_since_interaction
FROM repositories r
LEFT JOIN interactions i ON r.id = i.repo_id
LEFT JOIN colors c ON r.id = c.repo_id
GROUP BY r.name, r.category, c.hex, r.stars
ORDER BY recent_interactions DESC;
```

### Repository Activity Over Time

```sql
SELECT
  DATE_TRUNC('month', i.created_at) as month,
  r.category,
  COUNT(*) as interaction_count,
  COUNT(DISTINCT i.author) as unique_contributors,
  COUNT(DISTINCT CASE WHEN i.type = 'commit' THEN 1 END) as commits
FROM repositories r
JOIN interactions i ON r.id = i.repo_id
GROUP BY month, r.category
ORDER BY month DESC;
```

### Language Distribution by Maturity

```sql
SELECT
  r.language,
  SUM(CASE WHEN r.stars > 1000 THEN 1 ELSE 0 END) as mature_count,
  SUM(CASE WHEN r.stars BETWEEN 100 AND 1000 THEN 1 ELSE 0 END) as growth_count,
  SUM(CASE WHEN r.stars < 100 THEN 1 ELSE 0 END) as emerging_count,
  AVG(DATEDIFF(DAY, r.updated_at, NOW())) as avg_days_inactive
FROM repositories r
WHERE r.language IS NOT NULL
GROUP BY r.language
ORDER BY mature_count DESC;
```

## Inductive Diagram Generation

### Effect → Cause Visualization

```
Repository: active-tool

Effects (Observations):
├─ 500 commits/month
├─ 20 contributors/month
├─ 10 pull requests/month
├─ Updated yesterday
└─ 5,000 stars

    ↓ Abductive Inference ↓

Inferred Causes (Best Explanations):
├─ "Highly collaborative project"     (confidence: 0.96)
├─ "Well-maintained community tool"   (confidence: 0.93)
├─ "Production-quality software"      (confidence: 0.89)
└─ "Active development cycle"         (confidence: 0.87)

    ↓ Color Synthesis ↓

Semantic Color: #00FF00 (Green)
├─ Hue: 120° (Tool category)
├─ Saturation: 0.95 (very active)
├─ Lightness: 0.80 (mature)
└─ Reasoning: "Abductively inferred collaborative tool repository"
```

## Interactive Workflow

### Step 1: Catalog Repository

```
$ gh repo list --json name,owner,stars,updatedAt
```

→ Discover repositories via GitHub CLI

### Step 2: Store in DuckDB

```
INSERT INTO repositories VALUES (...)
INSERT INTO interactions VALUES (...)
```

→ Persist data for analysis

### Step 3: Abductively Infer Category

```
Effects: [high-commits, many-contributors, recent-update, high-stars]
     ↓
Cause: "Active library"
     ↓
Color: Hue 0° (Red, library)
       Saturation 0.9 (active)
       Lightness 0.8 (mature)
```

→ Assign semantically meaningful color

### Step 4: Query with Refinement

```sql
-- Initial query
SELECT * FROM repositories WHERE stars > 1000;

-- Refine based on abductions
SELECT * FROM repositories r
JOIN abductions a ON r.id = a.repo_id
WHERE a.confidence > 0.9 AND a.cause LIKE '%active%';

-- Further refine
SELECT * FROM repositories r
WHERE r.category = 'library' AND r.saturation > 0.8
ORDER BY r.stars DESC;
```

→ Iteratively sharpen analysis

### Step 5: Generate Insights

```
Top 10 Most Active Libraries:
├─ #FF0000 ripgrep (30k commits, 40k stars)
├─ #FF0000 tokio (20k commits, 25k stars)
├─ #FF0000 serde (15k commits, 20k stars)
...

Emerging Projects (5-50 stars):
├─ #FFFF00 my-new-parser (50 commits, 10 stars)
├─ #FFFF00 learning-rs (30 commits, 8 stars)
...

Sleeping Libraries (no activity >1 year):
├─ #CC0088 old-http-lib (5k commits, 500 stars)
├─ #CC0088 legacy-parser (3k commits, 200 stars)
...
```

## Matteo Capucci Reference

Matteo Capucci's work on **abductive reasoning** in category theory:
- Abduction as the inverse of deduction
- Modal logic interpretation: ◇(P → Q) means "possibly P implies Q"
- Type inference as abductive process: given a term, find its type
- Sheaf-theoretic interpretation: cause/effect as continuous sections

In our system:
- **Deduction**: Category → Color (deterministic rule)
- **Abduction**: Observations → Category (probabilistic inference)
- **Induction**: Many repos → General pattern (pattern discovery)

## Implementation Details

### Color Calculation

```clojure
(defn assign-repo-color [repo-id repo-data interactions]
  (let [category (infer-repo-category interactions)
        hue (category-hue category)
        saturation (activity-saturation days-since-update)
        lightness (maturity-lightness stars days-old)
        [r g b] (hsl-to-rgb hue saturation lightness)]
    {:repo-id repo-id
     :hue hue
     :saturation saturation
     :lightness lightness
     :hex (to-hex r g b)}))
```

### Abduction Protocol

```clojure
(defprotocol IAbduction
  (observe-effects [this])
  (infer-causes [this effects])
  (compute-confidence [this cause effects])
  (explain [this]))

(defrecord Abduction [repo-id effects causes confidence evidence]
  IAbduction
  ;; implementation...
  )
```

## Pushing to Repositories

Once analyzed, push results to appropriate repositories:

```bash
# Analyze and catalog
just github-analyze

# For each repository with insights:
gh repo clone owner/repo
# Add analysis results (as markdown comments, or in docs/)
git add docs/analysis.md
git commit -m "Add abductive analysis results"
git push

# Or create a summary PR:
gh pr create --title "Repository Analysis: Color Catalog & Abductions"
```

## Extending the System

### Add Custom Abduction Rules

```clojure
(defn custom-cause-inference [effects]
  (cond
    (and (some :high-test-coverage effects)
         (some :high-ci-pass-rate effects))
    "Well-tested production code"

    (and (some :many-issues effects)
         (some :old-issues effects))
    "Backlog of unresolved problems"

    (and (some :recent-api-changes effects)
         (some :many-contributors effects))
    "Active API development"

    :else "Other cause"))
```

### Integrate Spectral Analysis

Map repository colors to musical spectra:
```clojure
(defn hsl-to-midi [hue saturation lightness]
  ; Map HSL to both color and sound
  {:visual {:hue hue :saturation saturation :lightness lightness}
   :audio {:pitch (hue-to-midi hue)
           :timbre (saturation-to-timbre saturation)
           :amplitude (lightness-to-amplitude lightness)}})
```

### Add Temporal Analysis

Track repository evolution over time:
```clojure
(defn color-trajectory [repo-id time-window]
  ; Show how color changes as project evolves
  ; From bright red (emerging) → pale red (archived)
  )
```

## References

- **Matteo Capucci**: Abductive reasoning in modal logic and category theory
- **GitHub API**: GraphQL query format
- **DuckDB**: SQL analytics on structured data
- **HSL Color Space**: Human-friendly color representation

---

Generated with [Claude Code](https://claude.com/claude-code)

Written by: Claude Haiku 4.5

Date: 2025-12-21
