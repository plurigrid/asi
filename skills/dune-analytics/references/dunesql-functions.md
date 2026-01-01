# DuneSQL Functions Reference

## Blockchain-Specific Functions

### Address Handling

```sql
-- Convert to checksummed address
SELECT get_href(get_chain_explorer_address('ethereum', address), address)

-- Lowercase for joins
SELECT lower('0xAbC...')
```

### Varbinary Functions

```sql
-- Hex to varbinary
SELECT from_hex('0x1234')

-- Varbinary to hex string
SELECT to_hex(data)

-- Byte slicing
SELECT bytearray_substring(data, 1, 4)  -- First 4 bytes

-- Concatenate
SELECT bytearray_concat(a, b)
```

### EVM Decoding

```sql
-- Decode event logs manually
SELECT
    bytearray_to_uint256(bytearray_substring(data, 1, 32)) as amount,
    bytearray_to_address(topic1) as from_address
FROM ethereum.logs
WHERE topic0 = 0xddf252ad...  -- Transfer event
```

---

## Date/Time Functions

### Truncation
```sql
DATE_TRUNC('hour', block_time)
DATE_TRUNC('day', block_time)
DATE_TRUNC('week', block_time)
DATE_TRUNC('month', block_time)
```

### Intervals
```sql
-- Relative time
WHERE block_time > now() - interval '24' hour
WHERE block_time > now() - interval '7' day
WHERE block_time > now() - interval '30' day

-- Date arithmetic
SELECT block_time + interval '1' day
```

### Formatting
```sql
SELECT date_format(block_time, '%Y-%m-%d %H:%i')
SELECT format_datetime(block_time, 'yyyy-MM-dd')
```

### Extraction
```sql
SELECT
    year(block_time),
    month(block_time),
    day(block_time),
    hour(block_time),
    day_of_week(block_time)
```

---

## Numeric Functions

### Decimal Handling
```sql
-- Token amounts (handle decimals)
CAST(value AS DOUBLE) / POWER(10, decimals)

-- Safe division
COALESCE(a / NULLIF(b, 0), 0)
```

### Aggregations
```sql
SUM(amount)
AVG(amount)
MIN(amount)
MAX(amount)
COUNT(*)
COUNT(DISTINCT address)
```

### Percentiles
```sql
APPROX_PERCENTILE(amount, 0.5)   -- Median
APPROX_PERCENTILE(amount, 0.95)  -- 95th percentile
```

### Rounding
```sql
ROUND(value, 2)
FLOOR(value)
CEIL(value)
TRUNCATE(value, 2)
```

---

## String Functions

### Basic Operations
```sql
LOWER(symbol)
UPPER(symbol)
CONCAT(a, '-', b)
LENGTH(name)
TRIM(name)
```

### Pattern Matching
```sql
-- LIKE patterns
WHERE name LIKE 'Uniswap%'
WHERE symbol LIKE '%ETH'

-- Regex
WHERE regexp_like(name, '^[A-Z]+$')
SELECT regexp_extract(name, '([0-9]+)', 1)
```

### Splitting/Joining
```sql
SPLIT(path, '/')
ARRAY_JOIN(symbols, ', ')
```

---

## Array Functions

```sql
-- Array creation
SELECT ARRAY['ETH', 'BTC', 'USDC']

-- Array access
SELECT tokens[1]  -- First element (1-indexed)

-- Array contains
SELECT contains(tokens, 'ETH')

-- Array aggregation
SELECT ARRAY_AGG(symbol) as all_symbols

-- Unnest arrays
SELECT * FROM UNNEST(ARRAY[1,2,3]) as t(num)
```

---

## Window Functions

### Ranking
```sql
SELECT
    project,
    volume,
    ROW_NUMBER() OVER (ORDER BY volume DESC) as rank,
    RANK() OVER (ORDER BY volume DESC) as rank_with_ties,
    DENSE_RANK() OVER (ORDER BY volume DESC) as dense_rank
FROM protocol_stats
```

### Running Totals
```sql
SELECT
    block_time,
    volume,
    SUM(volume) OVER (ORDER BY block_time) as cumulative_volume
FROM daily_volumes
```

### Partitioned Windows
```sql
SELECT
    blockchain,
    project,
    volume,
    SUM(volume) OVER (PARTITION BY blockchain) as chain_total,
    volume / SUM(volume) OVER (PARTITION BY blockchain) as market_share
FROM protocol_stats
```

### LAG/LEAD
```sql
SELECT
    day,
    volume,
    LAG(volume, 1) OVER (ORDER BY day) as prev_day_volume,
    volume - LAG(volume, 1) OVER (ORDER BY day) as daily_change
FROM daily_stats
```

---

## Conditional Functions

### CASE
```sql
SELECT
    CASE
        WHEN amount_usd > 1000000 THEN 'whale'
        WHEN amount_usd > 10000 THEN 'large'
        ELSE 'retail'
    END as trade_size
FROM dex.trades
```

### COALESCE/NULLIF
```sql
COALESCE(symbol, 'UNKNOWN')
NULLIF(value, 0)  -- Returns NULL if value is 0
```

### IF
```sql
IF(amount > 0, 'positive', 'negative')
```

---

## JSON Functions

```sql
-- Extract from JSON
JSON_EXTRACT(metadata, '$.name')
JSON_EXTRACT_SCALAR(metadata, '$.symbol')

-- JSON array
JSON_ARRAY_LENGTH(data)
```

---

## Type Casting

```sql
CAST(value AS VARCHAR)
CAST(value AS DOUBLE)
CAST(value AS BIGINT)
CAST(value AS DECIMAL(38, 18))

-- Implicit via TRY (returns NULL on failure)
TRY_CAST(value AS BIGINT)
```

---

## Query Optimization Tips

### Use Partitions
```sql
-- Filter by block_time first (partitioned column)
WHERE block_time > now() - interval '7' day
  AND blockchain = 'ethereum'
```

### Limit Early
```sql
-- Apply LIMIT in subqueries
SELECT * FROM (
    SELECT * FROM large_table
    WHERE condition
    LIMIT 1000
) t
```

### Avoid SELECT *
```sql
-- Only select needed columns
SELECT block_time, tx_hash, amount_usd
FROM dex.trades
```

### Use APPROX Functions
```sql
-- For large datasets
APPROX_DISTINCT(address)  -- Instead of COUNT(DISTINCT)
APPROX_PERCENTILE(amount, 0.5)
```

---

## Common Patterns

### Daily Aggregation
```sql
SELECT
    DATE_TRUNC('day', block_time) as day,
    SUM(amount_usd) as daily_volume
FROM dex.trades
WHERE block_time > now() - interval '30' day
GROUP BY 1
ORDER BY 1
```

### Top N with Ranking
```sql
WITH ranked AS (
    SELECT
        project,
        SUM(amount_usd) as volume,
        ROW_NUMBER() OVER (ORDER BY SUM(amount_usd) DESC) as rank
    FROM dex.trades
    WHERE block_time > now() - interval '24' hour
    GROUP BY 1
)
SELECT * FROM ranked WHERE rank <= 10
```

### Period-over-Period Change
```sql
WITH daily AS (
    SELECT
        DATE_TRUNC('day', block_time) as day,
        SUM(amount_usd) as volume
    FROM dex.trades
    GROUP BY 1
)
SELECT
    day,
    volume,
    volume - LAG(volume) OVER (ORDER BY day) as change,
    (volume - LAG(volume) OVER (ORDER BY day)) / LAG(volume) OVER (ORDER BY day) * 100 as pct_change
FROM daily
```
