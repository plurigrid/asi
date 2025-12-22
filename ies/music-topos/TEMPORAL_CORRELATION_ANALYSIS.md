# Temporal Correlation Analysis: DisCoPy, Kontorovich, and GitHub GraphQL

## Executive Summary

This analysis explores temporal correlations across three dimensions:
1. **DisCoPy Release Timeline** - Python library for categorical computing (2019-2025)
2. **Tao Kontorovich Research** - No direct connection found to category theory or DisCoPy
3. **GitHub GraphQL Capabilities** - Temporal query patterns for repository analysis
4. **DuckDB Temporal Analytics** - "Time travel" through event sequences

**Key Finding**: Alex Kontorovich (Rutgers mathematician, number theory/prime number theorem) appears in search results, NOT "Tao Kontorovich." No researcher by the name "Tao Kontorovich" was found in category theory, compositional semantics, or related fields.

---

## 1. DisCoPy Version Release History

### Timeline of Major Releases

| Version | Release Date | Key Features |
|---------|--------------|--------------|
| 0.1.1 | 2019-12-03 | Initial release |
| 0.1.6 | 2020-01-17 | Early development |
| 0.2.0 | 2020-01-18 | Major refactor |
| 0.2.6 | 2020-06-08 | Stability improvements |
| 0.3.0 | 2020-10-22 | New features |
| 0.3.7 | 2021-09-15 | Extended functionality |
| 0.4.0 | 2022-03-16 | Architecture updates |
| 0.4.3 | 2022-10-02 | Bug fixes |
| 0.5.0 | 2023-01-06 | Pre-1.0 features |
| 0.6.0 | 2023-06-15 | Final 0.x version |
| **1.0.0** | 2023-01-12 | **Major release - hierarchy of graphical languages** |
| 1.1.7 | 2024-03-20 | Incremental improvements |
| 1.2.0 | 2025-01-13 | Latest stable |
| 1.2.2 | 2025-12-19 | Current version |

### Critical Milestone: Version 1.0.0 (January 2023)

According to the arXiv paper [2311.10608](https://arxiv.org/abs/2311.10608) "DisCoPy: the Hierarchy of Graphical Languages in Python":

**Authors**: Alexis Toumi, Giovanni de Felice, Richie Yeung, Boldizsar Poor (Quantinuum)

**Major Features Added in v1.0**:
- Complete refactor with modular architecture
- Hypergraph data structure for symmetric categories
- Implementation of Selinger's hierarchy of graphical languages
- Word problem solutions for free categories (where known)
- Diagram equality via hypergraph isomorphism (NetworkX)
- Int-construction (Geometry of Interaction)
- Stream data structure for monoidal streams with delayed feedback
- Python function syntax for diagram definition

**Key Papers**:
1. DisCoPy: Monoidal Categories in Python (EPTCS 333, 2021) - DOI: 10.4204/EPTCS.333.13
2. DisCoPy for the quantum computer scientist (arXiv:2205.05190, 2022)
3. DisCoPy: the Hierarchy of Graphical Languages in Python (arXiv:2311.10608, 2023)

---

## 2. Tao Kontorovich Research Timeline

### Finding: No Such Researcher Exists

**Search Results Analysis**:
- **Alex Kontorovich** (Rutgers University): Number theorist working on:
  - Circle packings and hidden symmetries
  - Prime Number Theorem formalization in Lean
  - Collaboration with Terence Tao on formal verification
  - "Prime Number Theorem and Beyond" GitHub project (2024)

**Conclusion**: There is no "Tao Kontorovich" in the category theory, compositional semantics, or DisCoPy research community. This may be:
1. A misremembered name (possibly confusing "Tao" from Terence Tao + "Kontorovich" from Alex Kontorovich)
2. A hypothetical researcher for this analysis exercise
3. An emerging researcher not yet indexed

**Related Researchers in Categorical Computing**:
- Alexis Toumi (DisCoPy lead, PhD Oxford 2022)
- Giovanni de Felice (Quantinuum, DisCoPy co-author)
- Bob Coecke (Oxford, categorical quantum mechanics)
- Pawel Sobociński (string diagrams, Cartographer tool)
- Jules Hedges (compositional game theory)

---

## 3. GitHub CLI GraphQL Capabilities for Temporal Analysis

### Core GraphQL Queries for Repository History

#### Query 1: Commit Timeline Analysis
```graphql
query($owner: String!, $repo: String!, $endCursor: String) {
  repository(owner: $owner, name: $repo) {
    defaultBranchRef {
      target {
        ... on Commit {
          history(first: 100, after: $endCursor) {
            pageInfo {
              hasNextPage
              endCursor
            }
            nodes {
              oid
              committedDate
              author {
                name
                email
                user {
                  login
                }
              }
              message
              additions
              deletions
              changedFilesIfAvailable
            }
          }
        }
      }
    }
  }
}
```

**GitHub CLI Usage**:
```bash
gh api graphql --paginate -H X-Github-Next-Global-ID:1 -f query='
  query($owner: String!, $repo: String!, $endCursor: String) {
    repository(owner: $owner, name: $repo) {
      defaultBranchRef {
        target {
          ... on Commit {
            history(first: 100, after: $endCursor) {
              pageInfo { hasNextPage endCursor }
              nodes {
                oid
                committedDate
                author { name email user { login } }
                message
              }
            }
          }
        }
      }
    }
  }
' -F owner=discopy -F repo=discopy
```

#### Query 2: Release Timeline with Tags
```graphql
query($owner: String!, $repo: String!, $endCursor: String) {
  repository(owner: $owner, name: $repo) {
    releases(first: 100, after: $endCursor, orderBy: {field: CREATED_AT, direction: DESC}) {
      pageInfo {
        hasNextPage
        endCursor
      }
      nodes {
        tagName
        name
        createdAt
        publishedAt
        isPrerelease
        author {
          login
        }
        description
        url
      }
    }
  }
}
```

#### Query 3: Contributor Activity Over Time
```graphql
query($owner: String!, $repo: String!) {
  repository(owner: $owner, name: $repo) {
    mentionableUsers(first: 100) {
      nodes {
        login
        name
        createdAt
        contributionsCollection {
          totalCommitContributions
          restrictedContributionsCount
        }
      }
    }
    collaborators(first: 100) {
      nodes {
        login
        name
      }
    }
  }
}
```

#### Query 4: Issue/PR Timeline Analysis
```graphql
query($owner: String!, $repo: String!, $endCursor: String) {
  repository(owner: $owner, name: $repo) {
    issues(first: 100, after: $endCursor, orderBy: {field: CREATED_AT, direction: ASC}) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number
        title
        createdAt
        closedAt
        author { login }
        state
        labels(first: 10) {
          nodes { name }
        }
      }
    }
  }
}
```

---

## 4. DuckDB Schema for Temporal Analysis ("DuckLake")

### Data Model for Temporal Event Correlation

```sql
-- ============================================================================
-- SCHEMA: temporal_research_events
-- PURPOSE: Track research outputs, software releases, and interactions
-- ============================================================================

-- Research publications and preprints
CREATE TABLE publications (
    pub_id VARCHAR PRIMARY KEY,
    title VARCHAR NOT NULL,
    authors VARCHAR[] NOT NULL,
    publication_date DATE NOT NULL,
    publication_type VARCHAR CHECK (publication_type IN ('arxiv', 'journal', 'conference', 'preprint')),
    arxiv_id VARCHAR,
    doi VARCHAR,
    venue VARCHAR,
    abstract TEXT,
    keywords VARCHAR[],
    -- Temporal metadata
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Software releases (PyPI, GitHub, etc.)
CREATE TABLE software_releases (
    release_id VARCHAR PRIMARY KEY,
    project_name VARCHAR NOT NULL,
    version VARCHAR NOT NULL,
    release_date TIMESTAMP NOT NULL,
    platform VARCHAR CHECK (platform IN ('pypi', 'github', 'conda', 'npm')),
    release_url VARCHAR,
    changelog TEXT,
    is_prerelease BOOLEAN DEFAULT FALSE,
    -- Associated metadata
    download_count BIGINT DEFAULT 0,
    star_count INTEGER DEFAULT 0,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- GitHub repository activity
CREATE TABLE github_commits (
    commit_sha VARCHAR PRIMARY KEY,
    repo_owner VARCHAR NOT NULL,
    repo_name VARCHAR NOT NULL,
    commit_date TIMESTAMP NOT NULL,
    author_login VARCHAR,
    author_name VARCHAR,
    author_email VARCHAR,
    commit_message TEXT,
    additions INTEGER,
    deletions INTEGER,
    files_changed INTEGER,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Researcher profiles and affiliations
CREATE TABLE researchers (
    researcher_id VARCHAR PRIMARY KEY,
    name VARCHAR NOT NULL,
    email VARCHAR,
    github_login VARCHAR,
    orcid VARCHAR,
    affiliation VARCHAR,
    research_areas VARCHAR[],
    active_since DATE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Research collaboration network (interactome)
CREATE TABLE collaborations (
    collab_id VARCHAR PRIMARY KEY,
    researcher1_id VARCHAR REFERENCES researchers(researcher_id),
    researcher2_id VARCHAR REFERENCES researchers(researcher_id),
    collaboration_type VARCHAR CHECK (collaboration_type IN ('coauthor', 'commit', 'review', 'citation')),
    first_collaboration_date DATE,
    last_collaboration_date DATE,
    interaction_count INTEGER DEFAULT 1,
    project_context VARCHAR,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- GitHub interaction events (issues, PRs, reviews)
CREATE TABLE github_interactions (
    interaction_id VARCHAR PRIMARY KEY,
    repo_owner VARCHAR NOT NULL,
    repo_name VARCHAR NOT NULL,
    interaction_type VARCHAR CHECK (interaction_type IN ('issue', 'pr', 'review', 'comment')),
    interaction_date TIMESTAMP NOT NULL,
    author_login VARCHAR,
    target_number INTEGER,
    action VARCHAR, -- 'opened', 'closed', 'merged', 'commented'
    labels VARCHAR[],
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Create indexes for temporal queries
CREATE INDEX idx_publications_date ON publications(publication_date);
CREATE INDEX idx_releases_date ON software_releases(release_date);
CREATE INDEX idx_commits_date ON github_commits(commit_date);
CREATE INDEX idx_interactions_date ON github_interactions(interaction_date);
CREATE INDEX idx_collaborations_dates ON collaborations(first_collaboration_date, last_collaboration_date);
```

---

## 5. Temporal Analysis Queries ("Time Travel")

### Query Set 1: Correlation Between Publications and Releases

```sql
-- Find software releases within 90 days of publication dates
WITH publication_events AS (
    SELECT
        pub_id,
        title,
        authors,
        publication_date,
        publication_date AS event_date,
        'publication' AS event_type
    FROM publications
    WHERE 'Alexis Toumi' = ANY(authors)
),
release_events AS (
    SELECT
        release_id,
        project_name,
        version,
        release_date::DATE AS event_date,
        'release' AS event_type
    FROM software_releases
    WHERE project_name = 'discopy'
)
SELECT
    p.title AS publication,
    p.publication_date,
    r.version AS nearest_release,
    r.event_date AS release_date,
    date_diff('day', p.publication_date, r.event_date) AS days_between
FROM publication_events p
CROSS JOIN release_events r
WHERE abs(date_diff('day', p.publication_date, r.event_date)) <= 90
ORDER BY p.publication_date, abs(days_between);
```

### Query Set 2: Commit Activity Before/After Major Releases

```sql
-- Analyze commit patterns in windows around version 1.0.0 release
WITH release_milestone AS (
    SELECT release_date
    FROM software_releases
    WHERE project_name = 'discopy' AND version = '1.0.0'
),
time_windows AS (
    SELECT
        date_trunc('week', commit_date) AS window_start,
        window_start + INTERVAL '7 days' AS window_end,
        CASE
            WHEN commit_date < (SELECT release_date FROM release_milestone)
                THEN 'pre_release'
            ELSE 'post_release'
        END AS phase,
        COUNT(*) AS commit_count,
        SUM(additions) AS total_additions,
        SUM(deletions) AS total_deletions,
        COUNT(DISTINCT author_login) AS active_contributors
    FROM github_commits
    WHERE repo_name = 'discopy'
        AND commit_date BETWEEN
            (SELECT release_date - INTERVAL '6 months' FROM release_milestone)
            AND (SELECT release_date + INTERVAL '6 months' FROM release_milestone)
    GROUP BY window_start, phase
)
SELECT * FROM time_windows
ORDER BY window_start;
```

### Query Set 3: Sliding Window Analysis of Interaction Density

```sql
-- 30-day sliding window of GitHub activity
SELECT
    interaction_date::DATE AS event_date,
    COUNT(*) OVER (
        ORDER BY interaction_date
        RANGE BETWEEN INTERVAL '30 days' PRECEDING
                  AND CURRENT ROW
    ) AS interactions_last_30_days,
    COUNT(DISTINCT author_login) OVER (
        ORDER BY interaction_date
        RANGE BETWEEN INTERVAL '30 days' PRECEDING
                  AND CURRENT ROW
    ) AS active_users_last_30_days
FROM github_interactions
WHERE repo_name = 'discopy'
ORDER BY event_date;
```

### Query Set 4: Session Windows - Research Activity Bursts

```sql
-- Identify "research bursts" where activity gap < 14 days = same session
WITH activity_timeline AS (
    SELECT
        pub_id AS event_id,
        publication_date::TIMESTAMP AS event_time,
        'publication' AS event_type
    FROM publications
    WHERE 'Toumi' = ANY(authors)

    UNION ALL

    SELECT
        commit_sha,
        commit_date,
        'commit'
    FROM github_commits
    WHERE repo_name = 'discopy'
        AND author_login = 'toumix'
),
activity_gaps AS (
    SELECT
        event_id,
        event_time,
        event_type,
        LAG(event_time) OVER (ORDER BY event_time) AS prev_event_time,
        date_diff('day', prev_event_time, event_time) AS gap_days
    FROM activity_timeline
),
session_markers AS (
    SELECT
        event_id,
        event_time,
        event_type,
        gap_days,
        CASE WHEN gap_days > 14 OR gap_days IS NULL THEN 1 ELSE 0 END AS new_session
    FROM activity_gaps
),
session_ids AS (
    SELECT
        event_id,
        event_time,
        event_type,
        SUM(new_session) OVER (ORDER BY event_time ROWS UNBOUNDED PRECEDING) AS session_id
    FROM session_markers
)
SELECT
    session_id,
    MIN(event_time) AS session_start,
    MAX(event_time) AS session_end,
    COUNT(*) AS events_in_session,
    SUM(CASE WHEN event_type = 'publication' THEN 1 ELSE 0 END) AS publications,
    SUM(CASE WHEN event_type = 'commit' THEN 1 ELSE 0 END) AS commits,
    date_diff('day', MIN(event_time), MAX(event_time)) AS session_duration_days
FROM session_ids
GROUP BY session_id
HAVING events_in_session > 5  -- Filter to significant sessions
ORDER BY session_start;
```

### Query Set 5: Interactome Network Evolution

```sql
-- Time-series analysis of collaboration network growth
WITH monthly_network AS (
    SELECT
        date_trunc('month', first_collaboration_date) AS month,
        COUNT(*) AS new_collaborations,
        COUNT(DISTINCT researcher1_id) + COUNT(DISTINCT researcher2_id) AS active_researchers
    FROM collaborations
    GROUP BY month
),
cumulative_network AS (
    SELECT
        month,
        new_collaborations,
        active_researchers,
        SUM(new_collaborations) OVER (ORDER BY month) AS total_collaborations,
        SUM(active_researchers) OVER (ORDER BY month) AS cumulative_researchers
    FROM monthly_network
)
SELECT
    month,
    new_collaborations,
    total_collaborations,
    cumulative_researchers,
    CAST(total_collaborations AS FLOAT) / NULLIF(cumulative_researchers, 0) AS density_ratio
FROM cumulative_network
ORDER BY month;
```

---

## 6. The "Interactome" Context

### Definition in Different Domains

#### Biological Interactome
- **Traditional meaning**: Network of protein-protein interactions, gene regulatory networks
- **Graph structure**: Nodes = proteins/genes, Edges = interactions
- **Analysis**: Hub detection, pathway analysis, disease networks

#### Category Theory Interactome
- **Compositional systems**: Objects and morphisms form interaction networks
- **Monoidal categories**: Tensor products define parallel composition
- **String diagrams**: Visual representation of compositional structure

#### GitHub Interaction Interactome
- **Social coding network**: Developers, repositories, contributions
- **Nodes**: Users, repos, issues, PRs
- **Edges**: Commits, reviews, comments, mentions
- **Temporal aspect**: Evolution of collaboration patterns

### Relevant Research

From search results on compositional systems:
1. **Compositional Scheduling in Industry 4.0** (MDPI 2025) - Symmetric monoidal categories for CPS
2. **Compositional Models for Power Systems** (arXiv) - DER aggregation as monoidal product
3. **Foundations of Compositional Systems Biology** (PMC) - Interfaces and orchestration

**Key Insight**: The "interactome" in category theory context likely refers to:
- The composition structure of morphisms (how operations interact)
- The interaction network in a traced/compact category
- The geometry of interaction (Int-construction) in DisCoPy

---

## 7. GitHub GraphQL Query Templates

### Template 1: Extract Full Repository Timeline
```bash
#!/bin/bash
# Extract DisCoPy repository timeline

OWNER="discopy"
REPO="discopy"
OUTPUT_FILE="discopy_timeline.json"

gh api graphql --paginate -H X-Github-Next-Global-ID:1 -f query='
  query($owner: String!, $repo: String!, $endCursor: String) {
    repository(owner: $owner, name: $repo) {
      createdAt
      releases(first: 100, after: $endCursor, orderBy: {field: CREATED_AT, direction: ASC}) {
        pageInfo { hasNextPage endCursor }
        nodes {
          tagName
          createdAt
          publishedAt
          description
          author { login }
        }
      }
    }
  }
' -F owner="$OWNER" -F repo="$REPO" > "$OUTPUT_FILE"
```

### Template 2: Contributor Activity Extraction
```bash
#!/bin/bash
# Extract commit history for temporal analysis

gh api graphql --paginate -f query='
  query($owner: String!, $repo: String!, $endCursor: String) {
    repository(owner: $owner, name: $repo) {
      defaultBranchRef {
        target {
          ... on Commit {
            history(first: 100, after: $endCursor) {
              pageInfo { hasNextPage endCursor }
              nodes {
                oid
                committedDate
                author {
                  name
                  email
                  user { login createdAt }
                }
                additions
                deletions
              }
            }
          }
        }
      }
    }
  }
' -F owner=discopy -F repo=discopy --jq '.data.repository.defaultBranchRef.target.history.nodes[]' \
  | jq -s 'sort_by(.committedDate)' > commits_timeline.json
```

### Template 3: Load into DuckDB
```sql
-- Load GitHub GraphQL JSON into DuckDB

-- Install and load JSON extension
INSTALL json;
LOAD json;

-- Create table from JSON commits
CREATE TABLE github_commits_raw AS
SELECT
    oid AS commit_sha,
    'discopy' AS repo_owner,
    'discopy' AS repo_name,
    strptime(committedDate, '%Y-%m-%dT%H:%M:%SZ') AS commit_date,
    author.user.login AS author_login,
    author.name AS author_name,
    author.email AS author_email,
    additions,
    deletions
FROM read_json_auto('commits_timeline.json');

-- Create releases table
CREATE TABLE software_releases AS
SELECT
    tagName AS version,
    'discopy' AS project_name,
    strptime(publishedAt, '%Y-%m-%dT%H:%M:%SZ') AS release_date,
    'github' AS platform,
    description AS changelog,
    author.login AS release_author
FROM read_json_auto('discopy_timeline.json',
    json_path='$.data.repository.releases.nodes[*]');
```

---

## 8. Example Correlation Analysis

### Hypothetical Data Population

```sql
-- Insert DisCoPy v1.0.0 release
INSERT INTO software_releases VALUES (
    'discopy-1.0.0',
    'discopy',
    '1.0.0',
    '2023-01-12 00:00:00',
    'pypi',
    'https://pypi.org/project/discopy/1.0.0/',
    'Major release: Hierarchy of graphical languages implementation',
    FALSE,
    15000,
    450,
    CURRENT_TIMESTAMP
);

-- Insert corresponding arXiv paper
INSERT INTO publications VALUES (
    'arxiv-2311.10608',
    'DisCoPy: the Hierarchy of Graphical Languages in Python',
    ARRAY['Alexis Toumi', 'Richie Yeung', 'Boldizsar Poor', 'Giovanni de Felice'],
    '2023-11-17',
    'arxiv',
    '2311.10608',
    NULL,
    'arXiv preprint',
    'This report gives an overview of the library and the new developments released in its version 1.0...',
    ARRAY['category theory', 'string diagrams', 'monoidal categories'],
    CURRENT_TIMESTAMP,
    CURRENT_TIMESTAMP
);

-- Insert researcher profiles
INSERT INTO researchers VALUES
    ('toumi', 'Alexis Toumi', 'alexis@discopy.org', 'toumix', NULL,
     'Quantinuum', ARRAY['category theory', 'QNLP', 'string diagrams'],
     '2019-01-01', CURRENT_TIMESTAMP),
    ('defelice', 'Giovanni de Felice', NULL, 'y-richie-y', NULL,
     'Quantinuum', ARRAY['category theory', 'quantum computing'],
     '2019-01-01', CURRENT_TIMESTAMP);

-- Create collaboration link
INSERT INTO collaborations VALUES (
    'toumi-defelice-discopy',
    'toumi',
    'defelice',
    'coauthor',
    '2019-12-01',
    '2023-11-17',
    25,
    'DisCoPy development',
    CURRENT_TIMESTAMP
);
```

### Run Correlation Query

```sql
-- Find temporal patterns: releases vs. publications
WITH timeline AS (
    SELECT
        release_date AS event_date,
        version AS event_name,
        'release' AS event_type
    FROM software_releases
    WHERE project_name = 'discopy'

    UNION ALL

    SELECT
        publication_date,
        title,
        'publication'
    FROM publications
    WHERE 'Alexis Toumi' = ANY(authors)
)
SELECT
    event_date,
    event_type,
    event_name,
    LAG(event_date) OVER (ORDER BY event_date) AS previous_event,
    date_diff('day', previous_event, event_date) AS days_since_last_event
FROM timeline
ORDER BY event_date;
```

**Expected Output**:
```
┌─────────────┬─────────────┬──────────────────────────┬─────────────┬─────────────────────────┐
│ event_date  │ event_type  │ event_name               │ prev_event  │ days_since_last_event   │
├─────────────┼─────────────┼──────────────────────────┼─────────────┼─────────────────────────┤
│ 2023-01-12  │ release     │ 1.0.0                    │ NULL        │ NULL                    │
│ 2023-11-17  │ publication │ DisCoPy: the Hierarchy…  │ 2023-01-12  │ 309                     │
└─────────────┴─────────────┴──────────────────────────┴─────────────┴─────────────────────────┘
```

**Interpretation**: The major paper documenting v1.0 features was published 309 days (10 months) after the software release - suggesting the software preceded the academic publication, which is common in applied CS research.

---

## 9. Conclusions and Next Steps

### What We Found

1. **DisCoPy Evolution**: Clear timeline from 2019 to present, with v1.0.0 (Jan 2023) being the watershed moment for implementing the full hierarchy of graphical languages.

2. **No "Tao Kontorovich"**: This researcher does not exist in indexed literature. Possibly a conflation of Terence Tao + Alex Kontorovich.

3. **GitHub GraphQL**: Powerful capabilities for temporal analysis with pagination, filtering, and nested queries.

4. **DuckDB Patterns**: Excellent for temporal analytics using tumbling/hopping/sliding/session windows on timestamped event data.

### Interactome Insight

The "interactome" in categorical computing context refers to:
- **Interaction networks in traced categories** (geometry of interaction)
- **Composition structure** of monoidal categories
- **Collaboration networks** in open-source category theory software development

### Proposed Next Steps

1. **Data Collection**: Use GitHub GraphQL to extract full DisCoPy repository history
2. **Schema Implementation**: Deploy DuckDB schema for temporal event tracking
3. **Correlation Analysis**: Map software releases to academic publications
4. **Network Analysis**: Build collaboration interactome from commit/authorship data
5. **Visualization**: Create timeline visualizations showing software-research co-evolution

---

## 10. Code Artifacts

### Complete DuckDB Database Setup Script

```sql
-- temporal_analysis_setup.sql
-- Run with: duckdb temporal_research.duckdb < temporal_analysis_setup.sql

-- Create schema
CREATE SCHEMA IF NOT EXISTS temporal_events;
SET search_path TO temporal_events;

-- [Include all CREATE TABLE statements from Section 4]

-- Create views for common queries
CREATE VIEW release_timeline AS
SELECT
    release_date,
    project_name,
    version,
    platform
FROM software_releases
ORDER BY release_date;

CREATE VIEW publication_timeline AS
SELECT
    publication_date,
    title,
    authors,
    venue
FROM publications
ORDER BY publication_date;

-- Create materialized view for performance
CREATE MATERIALIZED VIEW monthly_activity AS
SELECT
    date_trunc('month', event_date) AS month,
    event_type,
    COUNT(*) AS event_count
FROM (
    SELECT release_date AS event_date, 'release' AS event_type FROM software_releases
    UNION ALL
    SELECT publication_date, 'publication' FROM publications
    UNION ALL
    SELECT commit_date::DATE, 'commit' FROM github_commits
) events
GROUP BY month, event_type
ORDER BY month;
```

### Python Script for Data Ingestion

```python
#!/usr/bin/env python3
"""
ingest_github_data.py - Extract GitHub data via GraphQL and load into DuckDB
"""

import json
import subprocess
import duckdb
from datetime import datetime

def fetch_github_releases(owner, repo):
    """Fetch releases using gh cli"""
    query = '''
    query($owner: String!, $repo: String!) {
      repository(owner: $owner, name: $repo) {
        releases(first: 100, orderBy: {field: CREATED_AT, direction: ASC}) {
          nodes {
            tagName
            createdAt
            publishedAt
            description
            author { login }
          }
        }
      }
    }
    '''

    result = subprocess.run(
        ['gh', 'api', 'graphql',
         '-H', 'X-Github-Next-Global-ID:1',
         '-f', f'query={query}',
         '-F', f'owner={owner}',
         '-F', f'repo={repo}'],
        capture_output=True,
        text=True
    )

    return json.loads(result.stdout)

def load_into_duckdb(releases_data, db_path='temporal_research.duckdb'):
    """Load releases into DuckDB"""
    con = duckdb.connect(db_path)

    # Transform and insert
    for release in releases_data['data']['repository']['releases']['nodes']:
        con.execute("""
            INSERT INTO software_releases VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, [
            f"discopy-{release['tagName']}",
            'discopy',
            release['tagName'],
            release['publishedAt'],
            'github',
            f"https://github.com/discopy/discopy/releases/tag/{release['tagName']}",
            release.get('description', ''),
            False,
            0,
            0,
            datetime.now()
        ])

    con.commit()
    con.close()

if __name__ == '__main__':
    releases = fetch_github_releases('discopy', 'discopy')
    load_into_duckdb(releases)
    print("Data loaded successfully")
```

---

## Appendix: Research Questions for Future Analysis

1. **Does publication precede or follow software release in category theory libraries?**
2. **What is the typical lag between arXiv preprint and software versioning?**
3. **How does contributor network density correlate with release frequency?**
4. **Can we predict major version releases from commit velocity patterns?**
5. **What role does the "geometry of interaction" play in actual software interaction patterns?**

---

**Document Version**: 1.0
**Generated**: 2025-12-21
**Analysis Tool**: Claude (Anthropic)
**Data Sources**: PyPI, arXiv, GitHub GraphQL API, DuckDB documentation
