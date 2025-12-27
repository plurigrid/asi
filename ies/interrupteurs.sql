-- Interrupteurs: GF(3)-conserved session interrupt tracking
-- World/Coworld derivational flow with balanced trit sums

CREATE TABLE IF NOT EXISTS trit (
    id INTEGER PRIMARY KEY,
    value INTEGER NOT NULL CHECK (value IN (-1, 0, 1)),
    symbol VARCHAR NOT NULL  -- 'MINUS', 'ERGODIC', 'PLUS'
);

INSERT INTO trit VALUES (1, -1, 'MINUS'), (2, 0, 'ERGODIC'), (3, 1, 'PLUS')
ON CONFLICT DO NOTHING;

CREATE TABLE IF NOT EXISTS balance (
    id INTEGER PRIMARY KEY,
    minus INTEGER DEFAULT 0,
    ergodic INTEGER DEFAULT 0,
    plus INTEGER DEFAULT 0,
    sum INTEGER GENERATED ALWAYS AS (minus * -1 + ergodic * 0 + plus * 1) VIRTUAL
);

CREATE TABLE IF NOT EXISTS session (
    id INTEGER PRIMARY KEY,
    start_id INTEGER,
    end_id INTEGER,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE IF NOT EXISTS intake (
    id INTEGER PRIMARY KEY,
    session INTEGER REFERENCES session(id),
    trit INTEGER REFERENCES trit(id),
    name VARCHAR NOT NULL,
    color VARCHAR(7),  -- Gay.jl hex color
    clock INTEGER NOT NULL,  -- Logical clock
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE IF NOT EXISTS interrupt (
    id INTEGER PRIMARY KEY,
    ends_session INTEGER REFERENCES session(id),
    starts_session INTEGER REFERENCES session(id),
    balance_at INTEGER REFERENCES balance(id),
    type VARCHAR NOT NULL,  -- 'user', 'timeout', 'error', 'fork'
    gap_seconds FLOAT,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE IF NOT EXISTS concept (
    id INTEGER PRIMARY KEY,
    source_intake INTEGER REFERENCES intake(id),
    name VARCHAR NOT NULL,
    freq INTEGER DEFAULT 1
);

-- View: Session derivation with GF(3) balance
CREATE OR REPLACE VIEW session_balance AS
SELECT 
    s.id as session_id,
    COUNT(CASE WHEN t.value = -1 THEN 1 END) as minus_count,
    COUNT(CASE WHEN t.value = 0 THEN 1 END) as ergodic_count,
    COUNT(CASE WHEN t.value = 1 THEN 1 END) as plus_count,
    SUM(t.value) as gf3_sum,
    SUM(t.value) % 3 = 0 as conserved
FROM session s
LEFT JOIN intake i ON i.session = s.id
LEFT JOIN trit t ON i.trit = t.id
GROUP BY s.id;

-- View: Interrupt flow graph
CREATE OR REPLACE VIEW interrupt_flow AS
SELECT 
    i.id,
    i.type,
    es.id as from_session,
    ss.id as to_session,
    b.sum as balance_sum,
    i.gap_seconds
FROM interrupt i
LEFT JOIN session es ON i.ends_session = es.id
LEFT JOIN session ss ON i.starts_session = ss.id
LEFT JOIN balance b ON i.balance_at = b.id;
