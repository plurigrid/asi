---
name: restricted-bigquery-dbt-environment
description: 'Safe dbt development against BigQuery using test schema isolation. Prevents accidental production writes. Triggers: dbt, bigquery, test schema, production safety.'
---

# Restricted BigQuery dbt Environment

Prevent accidental writes to production schemas by temporarily adding `schema='test'` to model config during local development.

## Workflow

### 1. Add schema='test' to model config (always at the top to minimize diff)

```sql
{{
  config(
    schema='test',
    materialized='incremental',
    ...
  )
}}
```

### 2. Verify with compile

```bash
uv run dbt compile --select <model_name> --profiles-dir ~/.dbt --no-use-colors
```

Confirm output contains `test` schema.

### 3. Run (REQUIRES user permission + test schema confirmation)

```bash
uv run dbt run --select <model_name> --profiles-dir ~/.dbt --no-use-colors
uv run dbt test --select <model_name> --profiles-dir ~/.dbt --no-use-colors
```

### 4. Remove schema='test' before committing

Verify with `git diff` that `schema='test'` is removed.

## Hard Rules

- NEVER commit with `schema='test'` included
- NEVER run dbt run without `schema='test'` (production write risk)
- ALWAYS get user permission before `dbt run`
