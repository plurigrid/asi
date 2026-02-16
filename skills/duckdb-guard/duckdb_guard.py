#!/usr/bin/env python3
"""
duckdb-guard: Pre-query schema validation for DuckDB

Trit: 0 (ERGODIC)
Seed: 137508

Prevents:
- Schema mismatch (column not found)
- Constraint violations (NOT NULL)
- Unsafe INSERT OR IGNORE patterns
"""

import duckdb
import json
import sys
from pathlib import Path
from typing import Optional


def levenshtein(s1: str, s2: str) -> int:
    """Calculate Levenshtein distance between two strings"""
    if len(s1) < len(s2):
        return levenshtein(s2, s1)
    if len(s2) == 0:
        return len(s1)
    
    previous_row = range(len(s2) + 1)
    for i, c1 in enumerate(s1):
        current_row = [i + 1]
        for j, c2 in enumerate(s2):
            insertions = previous_row[j + 1] + 1
            deletions = current_row[j] + 1
            substitutions = previous_row[j] + (c1 != c2)
            current_row.append(min(insertions, deletions, substitutions))
        previous_row = current_row
    
    return previous_row[-1]


def validate_schema(db_path: str, table: str, columns: list[str]) -> dict:
    """
    Validate columns exist before query.
    
    Returns:
        {
            "valid": bool,
            "missing": list[str],
            "suggestions": dict[str, str],  # missing -> suggested
            "existing": list[str]
        }
    """
    con = duckdb.connect(db_path, read_only=True)
    
    try:
        existing = con.execute(f"""
            SELECT column_name FROM information_schema.columns 
            WHERE table_name = '{table}'
        """).fetchall()
        existing_cols = {r[0] for r in existing}
    except duckdb.CatalogException:
        return {
            "valid": False,
            "missing": [table],
            "suggestions": {},
            "existing": [],
            "error": f"Table '{table}' does not exist"
        }
    finally:
        con.close()
    
    missing = [c for c in columns if c not in existing_cols]
    suggestions = {}
    
    for m in missing:
        # Find similar columns (Levenshtein distance 1-2)
        similar = [e for e in existing_cols if levenshtein(m.lower(), e.lower()) <= 2]
        if similar:
            # Sort by distance, take closest
            similar.sort(key=lambda x: levenshtein(m.lower(), x.lower()))
            suggestions[m] = similar[0]
    
    return {
        "valid": len(missing) == 0,
        "missing": missing,
        "suggestions": suggestions,
        "existing": list(existing_cols)
    }


def describe_table(db_path: str, table: str) -> dict:
    """Get full schema information for a table"""
    con = duckdb.connect(db_path, read_only=True)
    
    try:
        columns = con.execute(f"""
            SELECT column_name, data_type, is_nullable, column_default
            FROM information_schema.columns 
            WHERE table_name = '{table}'
            ORDER BY ordinal_position
        """).fetchall()
        
        return {
            "table": table,
            "columns": [
                {
                    "name": c[0],
                    "type": c[1],
                    "nullable": c[2] == "YES",
                    "default": c[3]
                }
                for c in columns
            ]
        }
    except duckdb.CatalogException:
        return {"error": f"Table '{table}' does not exist"}
    finally:
        con.close()


def check_constraints(db_path: str, table: str) -> dict:
    """List NOT NULL and CHECK constraints for a table"""
    con = duckdb.connect(db_path, read_only=True)
    
    try:
        # Get NOT NULL columns
        not_null = con.execute(f"""
            SELECT column_name 
            FROM information_schema.columns 
            WHERE table_name = '{table}' AND is_nullable = 'NO'
        """).fetchall()
        
        return {
            "table": table,
            "not_null": [c[0] for c in not_null],
        }
    except duckdb.CatalogException:
        return {"error": f"Table '{table}' does not exist"}
    finally:
        con.close()


def safe_insert(
    db_path: str, 
    table: str, 
    data: dict, 
    on_conflict: str = "NOTHING"
) -> dict:
    """
    Safe INSERT with explicit column handling.
    
    Args:
        db_path: Path to DuckDB file
        table: Target table name
        data: Dict of column -> value
        on_conflict: "NOTHING", "REPLACE", or column-specific handling
    
    Returns:
        {"success": bool, "fixed_columns": list, "error": str}
    """
    # Validate columns first
    columns = list(data.keys())
    validation = validate_schema(db_path, table, columns)
    
    fixed_columns = []
    if not validation["valid"]:
        # Try suggestions
        fixed_data = {}
        for k, v in data.items():
            if k in validation["suggestions"]:
                new_col = validation["suggestions"][k]
                fixed_data[new_col] = v
                fixed_columns.append(f"{k} -> {new_col}")
            elif k in validation["existing"]:
                fixed_data[k] = v
            # else: skip unknown column
        data = fixed_data
    
    if not data:
        return {
            "success": False,
            "error": "No valid columns after fixing",
            "validation": validation
        }
    
    # Check NOT NULL constraints
    constraints = check_constraints(db_path, table)
    missing_required = [
        c for c in constraints.get("not_null", [])
        if c not in data and c not in ["id", "rowid"]  # Skip auto-gen columns
    ]
    
    if missing_required:
        return {
            "success": False,
            "error": f"Missing required columns: {missing_required}",
            "fixed_columns": fixed_columns
        }
    
    # Build safe INSERT
    con = duckdb.connect(db_path)
    try:
        cols = ", ".join(data.keys())
        placeholders = ", ".join(["?" for _ in data])
        
        if on_conflict.upper() == "REPLACE":
            sql = f"INSERT OR REPLACE INTO {table} ({cols}) VALUES ({placeholders})"
        else:
            sql = f"INSERT INTO {table} ({cols}) VALUES ({placeholders}) ON CONFLICT DO {on_conflict}"
        
        con.execute(sql, list(data.values()))
        
        return {
            "success": True,
            "fixed_columns": fixed_columns,
            "sql": sql
        }
    except Exception as e:
        return {
            "success": False,
            "error": str(e),
            "fixed_columns": fixed_columns
        }
    finally:
        con.close()


def list_tables(db_path: str) -> list[str]:
    """List all tables in database"""
    con = duckdb.connect(db_path, read_only=True)
    try:
        tables = con.execute("""
            SELECT table_name FROM information_schema.tables 
            WHERE table_schema = 'main'
        """).fetchall()
        return [t[0] for t in tables]
    finally:
        con.close()


# CLI interface
if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(json.dumps({
            "usage": "duckdb_guard.py <command> [args...]",
            "commands": {
                "validate": "validate <db> <table> <col1,col2,...>",
                "describe": "describe <db> <table>",
                "constraints": "constraints <db> <table>",
                "tables": "tables <db>",
                "insert": "insert <db> <table> <json_data> [on_conflict]"
            }
        }, indent=2))
        sys.exit(0)
    
    cmd = sys.argv[1]
    
    if cmd == "validate" and len(sys.argv) >= 5:
        db, table, cols = sys.argv[2], sys.argv[3], sys.argv[4].split(",")
        print(json.dumps(validate_schema(db, table, cols), indent=2))
    
    elif cmd == "describe" and len(sys.argv) >= 4:
        db, table = sys.argv[2], sys.argv[3]
        print(json.dumps(describe_table(db, table), indent=2))
    
    elif cmd == "constraints" and len(sys.argv) >= 4:
        db, table = sys.argv[2], sys.argv[3]
        print(json.dumps(check_constraints(db, table), indent=2))
    
    elif cmd == "tables" and len(sys.argv) >= 3:
        db = sys.argv[2]
        print(json.dumps(list_tables(db), indent=2))
    
    elif cmd == "insert" and len(sys.argv) >= 5:
        db, table = sys.argv[2], sys.argv[3]
        data = json.loads(sys.argv[4])
        on_conflict = sys.argv[5] if len(sys.argv) > 5 else "NOTHING"
        print(json.dumps(safe_insert(db, table, data, on_conflict), indent=2))
    
    else:
        print(json.dumps({"error": f"Unknown command: {cmd}"}))
        sys.exit(1)
