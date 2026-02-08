---
name: duckdb-spatial
description: DuckDB Spatial Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# DuckDB Spatial Skill

H3 hexagonal indexing, PostGIS-compatible spatial queries, and geographic analysis with GF(3) coloring.

## Trigger
- Spatial SQL queries, geographic data analysis
- H3 hexagonal grid operations
- Point-in-polygon, distance queries
- Geospatial joins, spatial indexing

## GF(3) Trit: 0 (Ergodic/Coordinator)
Coordinates spatial data flow and transforms between coordinate systems.

## Installation

```sql
INSTALL spatial;
LOAD spatial;

-- Also useful
INSTALL h3 FROM community;
LOAD h3;
```

## Core Spatial Types

```sql
-- Point, LineString, Polygon, MultiPoint, etc.
SELECT ST_Point(-122.4194, 37.7749) as san_francisco;
SELECT ST_GeomFromText('POLYGON((0 0, 1 0, 1 1, 0 1, 0 0))') as square;

-- GeoJSON parsing
SELECT ST_GeomFromGeoJSON('{"type":"Point","coordinates":[-122.4,37.7]}');
```

## Colored Spatial Table Schema

```sql
CREATE TABLE geo_features (
    feature_id VARCHAR PRIMARY KEY,
    name VARCHAR,
    geometry GEOMETRY,
    feature_type VARCHAR,
    -- GF(3) coloring
    seed BIGINT,
    gay_color VARCHAR,
    gf3_trit INTEGER,
    -- Metadata
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Insert with color derivation
INSERT INTO geo_features VALUES (
    'sf-001',
    'San Francisco',
    ST_Point(-122.4194, 37.7749),
    'city',
    4815162342,  -- seed
    '#DC6B3B',   -- gay_color
    1,           -- trit (+1)
    CURRENT_TIMESTAMP
);
```

## H3 Hexagonal Indexing

```sql
-- Convert lat/lon to H3 index at resolution 9
SELECT h3_latlng_to_cell(37.7749, -122.4194, 9) as h3_index;

-- Get cell boundary as polygon
SELECT h3_cell_to_boundary_wkt(h3_latlng_to_cell(37.7749, -122.4194, 9));

-- Get neighbors (k-ring)
SELECT h3_grid_disk(h3_latlng_to_cell(37.7749, -122.4194, 9), 1) as neighbors;

-- Color H3 cells
CREATE TABLE h3_colored AS
SELECT 
    h3_latlng_to_cell(lat, lon, 9) as h3_index,
    COUNT(*) as point_count,
    -- Color from H3 index
    h3_latlng_to_cell(lat, lon, 9) % 3 - 1 as gf3_trit
FROM points
GROUP BY 1