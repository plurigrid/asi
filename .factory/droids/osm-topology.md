---
name: osm-topology
description: OSM Topology Skill
model: inherit
tools: read-only
---

# OSM Topology Skill

OpenStreetMap graph analysis: road networks, routing, and topological structure with GF(3) coloring.

## Trigger
- OpenStreetMap data processing
- Road network analysis, routing
- Graph-based geographic queries
- Street network topology

## GF(3) Trit: -1 (Validator)
Validates topological consistency of geographic networks.

## OSM Data Model

OSM uses three primitives:
- **Nodes**: Points with lat/lon
- **Ways**: Ordered lists of nodes (roads, boundaries)
- **Relations**: Groups of nodes/ways (routes, multipolygons)

## DuckDB OSM Integration

```sql
-- Read OSM PBF files (requires osm extension)
-- Install from: https://github.com/duckdb/duckdb_osm

-- Alternative: Use pre-processed Parquet
CREATE TABLE osm_nodes AS 
SELECT * FROM read_parquet('osm_nodes.parquet');

CREATE TABLE osm_ways AS
SELECT * FROM read_parquet('osm_ways.parquet');

-- Schema for colored OSM data
CREATE TABLE osm_network (
    way_id BIGINT,
    name VARCHAR,
    highway_type VARCHAR,
    geometry GEOMETRY,
    node_ids BIGINT[],
    -- Topology
    start_node BIGINT,
    end_node BIGINT,
    length_m DOUBLE,
    -- GF(3) coloring
    seed BIGINT,
    gay_color VARCHAR,
    gf3_trit INTEGER
);
```

## Graph Extraction

```python
import duckdb
import networkx as nx

def extract_road_graph(osm_parquet_path):
    """Extract road network as colored graph."""
    conn = duckdb.connect()
    conn.execute("INSTALL spatial; LOAD spatial;")
    
    # Load ways with road tags
    conn.execute(f"""
        CREATE TABLE roads AS
        SELECT 
            way_id,
            tags->>'name' as name,
            tags->>'highway' as highway,
            nodes,
            ST_Length_Spheroid(ST_MakeLine(
                LIST_TRANSFORM(nodes, n -> ST_Point(n.lon, n.lat))
            )) as length_m
        FROM read_parquet('{osm_parquet_path}')
        WHERE tags->>'highway' IS NOT NULL
    """)
    
    # Build graph
    G = nx.DiGraph()
    
    roads = conn.execute("""
        SELEC