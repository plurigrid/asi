# gh-graphql-ducklake

GitHub GraphQL queries stored as DuckLake incremental snapshots with ACSet schema.

## Core Concept

```
gh api graphql → JSON → DuckLake snapshot → Time-travel queries
     ↓              ↓           ↓
   Query         Parse      Version (t)
```

## ACSet Schema for GitHub Data

```julia
@present SchGitHubGraph(FreeSchema) begin
  Repo::Ob
  Issue::Ob
  PR::Ob
  User::Ob

  repo_owner::Hom(Repo, User)
  issue_repo::Hom(Issue, Repo)
  pr_repo::Hom(PR, Repo)
  issue_author::Hom(Issue, User)
  pr_author::Hom(PR, User)

  # Attributes
  Name::AttrType
  Count::AttrType
  Timestamp::AttrType

  repo_name::Attr(Repo, Name)
  stars::Attr(Repo, Count)
  issue_title::Attr(Issue, Name)
  snapshot_time::Attr(Repo, Timestamp)
end
```

## DuckLake Snapshot Pattern

```sql
-- Initialize lake
ATTACH 'ducklake:gh_snapshots.ducklake' AS lake;

-- Create versioned table
CREATE TABLE lake.repos AS
SELECT * FROM read_json_auto('repos.json');

-- Each query creates new snapshot
INSERT INTO lake.repos
SELECT *, now() as snapshot_time FROM read_json_auto('repos_new.json');

-- Time travel query
SELECT * FROM lake.repos AT SNAPSHOT 'v1';
SELECT * FROM lake.repos AT TIMESTAMP '2025-01-01';
```

## Babashka Script

```clojure
#!/usr/bin/env bb
(require '[babashka.process :as p]
         '[cheshire.core :as json]
         '[babashka.fs :as fs])

(def graphql-query
  "{ viewer {
       repositories(first: 100) {
         nodes { name stargazerCount updatedAt }
       }
     }
   }")

(defn fetch-repos []
  (-> (p/shell {:out :string}
        "gh" "api" "graphql" "-f" (str "query=" graphql-query))
      :out
      (json/parse-string true)
      :data :viewer :repositories :nodes))

(defn snapshot-to-ducklake [repos]
  (let [json-file "/tmp/gh_repos_snapshot.json"
        lake-file "gh_snapshots.ducklake"]
    (spit json-file (json/generate-string repos))
    (p/shell "duckdb" "-c"
      (format "LOAD ducklake;
               ATTACH 'ducklake:%s' AS lake;
               INSERT INTO lake.repos SELECT *, now() as snapshot_time
               FROM read_json_auto('%s');"
              lake-file json-file))))

;; Main
(-> (fetch-repos)
    (snapshot-to-ducklake))
```

## GF(3) Triadic Assignment

```
MINUS (-1): DuckLake storage (validator/constraint)
ERGODIC (0): ACSet schema (coordinator/structure)
PLUS (+1): gh CLI queries (generator/executor)

Conservation: -1 + 0 + 1 = 0 ✓
```

## Incremental Queries

```bash
# Initial snapshot
gh api graphql -f query='{ viewer { repositories(first:100) { nodes { name stargazerCount } } } }' \
  | duckdb -c "LOAD ducklake; ATTACH 'ducklake:gh.ducklake' AS l;
               CREATE OR REPLACE TABLE l.repos AS SELECT *, now() as t FROM read_json_auto('/dev/stdin');"

# Incremental (new version)
gh api graphql -f query='...' \
  | duckdb -c "LOAD ducklake; ATTACH 'ducklake:gh.ducklake' AS l;
               INSERT INTO l.repos SELECT *, now() as t FROM read_json_auto('/dev/stdin');"

# Time travel diff
duckdb -c "LOAD ducklake; ATTACH 'ducklake:gh.ducklake' AS l;
           SELECT name,
                  old.stargazerCount as was,
                  new.stargazerCount as now,
                  new.stargazerCount - old.stargazerCount as delta
           FROM l.repos AT SNAPSHOT 'v1' old
           JOIN l.repos new USING (name)
           WHERE delta != 0;"
```

## SICP Stream Pattern

Lazy evaluation for pagination:

```clojure
;; SICP-style stream of pages
(defn gh-page-stream [query cursor]
  (lazy-seq
    (let [result (fetch-page query cursor)
          items (:nodes result)
          next-cursor (-> result :pageInfo :endCursor)]
      (if next-cursor
        (concat items (gh-page-stream query next-cursor))
        items))))

;; Consume lazily, snapshot incrementally
(doseq [batch (partition-all 100 (gh-page-stream query nil))]
  (snapshot-to-ducklake batch))
```

## Commands

```bash
# Initialize lake
just gh-lake-init

# Fetch and snapshot
just gh-snapshot repos
just gh-snapshot issues --repo owner/name

# Time travel
just gh-diff v1 v2
just gh-at "2025-01-01"
```

## Voice Announcement

```bash
say -v Samantha "GitHub snapshot $(date +%H:%M): $(wc -l < /tmp/repos.json) repos captured"
```

## Parallel Worlds Demo (2026-01-01)

```
┌────────────────┬───────┬─────────┬───────┬────────┐
│     world      │ trit  │  color  │ repos │ stars  │
├────────────────┼───────┼─────────┼───────┼────────┤
│ bmorphism      │    -1 │ #3B82F6 │     5 │    216 │
│ plurigrid      │     0 │ #10B981 │     5 │     25 │
│ AlgebraicJulia │     1 │ #F59E0B │     5 │   1033 │
└────────────────┴───────┴─────────┴───────┴────────┘

GF(3) Conservation: (-1) + (0) + (+1) = 0 ✓
```

## Integration Points

- **acsets**: Schema definition for typed storage
- **babashka**: Scripting without JVM startup
- **ducklake-time-travel**: Snapshot versioning
- **sicp**: Lazy streams for pagination
- **say**: Voice narration of snapshots
- **parallel-fanout**: GF(3) triadic world queries
