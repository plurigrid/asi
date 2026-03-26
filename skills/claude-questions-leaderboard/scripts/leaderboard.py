#!/usr/bin/env python3
"""Claude questions leaderboard — DuckDB operations."""
import sys
import duckdb

DB = '/Users/alice/v/claude_questions_leaderboard.duckdb'

def connect():
    return duckdb.connect(DB)

def init():
    con = connect()
    con.execute("""
        CREATE TABLE IF NOT EXISTS bad_questions (
            id INTEGER PRIMARY KEY,
            question TEXT NOT NULL,
            context TEXT,
            why_bad TEXT,
            date DATE DEFAULT CURRENT_DATE
        );
        CREATE TABLE IF NOT EXISTS good_questions (
            id INTEGER PRIMARY KEY,
            question TEXT NOT NULL,
            context TEXT,
            why_insightful TEXT,
            date DATE DEFAULT CURRENT_DATE
        );
        CREATE SEQUENCE IF NOT EXISTS bad_seq START 1;
        CREATE SEQUENCE IF NOT EXISTS good_seq START 1;
    """)
    con.close()

def add(table, question, context, reason):
    con = connect()
    seq = 'bad_seq' if table == 'bad' else 'good_seq'
    col = 'why_bad' if table == 'bad' else 'why_insightful'
    con.execute(
        f"INSERT INTO {table}_questions VALUES (nextval('{seq}'), ?, ?, ?, CURRENT_DATE)",
        [question, context, reason]
    )
    con.close()

def show(table=None):
    con = connect()
    for t in ([table] if table else ['bad', 'good']):
        print(f"\n=== {t}_questions ===")
        df = con.execute(f"SELECT * FROM {t}_questions ORDER BY date DESC").fetchdf()
        print(df.to_string() if len(df) > 0 else "(empty)")
    con.close()

if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'show'
    if cmd == 'init':
        init()
    elif cmd == 'show':
        show(sys.argv[2] if len(sys.argv) > 2 else None)
    elif cmd in ('bad', 'good'):
        add(cmd, sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        print(f"Usage: {sys.argv[0]} [init|show|bad|good] [args...]")
