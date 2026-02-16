# Graph Investigation Skill

**Trit**: +1 (PLUS - Generator)
**Category**: investigative-journalism
**Source**: Project Domino, ICIJ, Neo4j

## Overview

Large-scale graph analytics for entity resolution, network analysis, and relationship mapping. Based on methodologies from Project Domino (1B+ node COVID misinformation graphs) and ICIJ's Panama/Paradise Papers investigations.

## Core Tools

### Neo4j Graph Database

Already available via MCP: `mcp__mcp-neo4j-cypher__*`

```cypher
// Create person nodes from document entities
LOAD CSV WITH HEADERS FROM 'file:///entities.csv' AS row
WITH row WHERE row.type = 'PERSON'
MERGE (p:Person {name: row.name})
SET p.mention_count = toInteger(row.count);

// Create co-occurrence relationships
LOAD CSV WITH HEADERS FROM 'file:///cooccurrences.csv' AS row
MATCH (a:Person {name: row.source})
MATCH (b:Person {name: row.target})
MERGE (a)-[r:MENTIONED_WITH]->(b)
SET r.weight = toInteger(row.weight);

// Find central figures (PageRank)
CALL gds.pageRank.stream('person-network')
YIELD nodeId, score
RETURN gds.util.asNode(nodeId).name AS name, score
ORDER BY score DESC LIMIT 20;

// Community detection (Louvain)
CALL gds.louvain.stream('person-network')
YIELD nodeId, communityId
RETURN communityId, collect(gds.util.asNode(nodeId).name) AS members
ORDER BY size(members) DESC;
```

### PyGraphistry (Large-Scale Visualization)

```python
import graphistry
import pandas as pd

# Register (free tier available)
graphistry.register(api=3, protocol="https", server="hub.graphistry.com",
                   username="user", password="pass")

# Load edges from DuckDB
import duckdb
con = duckdb.connect("efta_documents.duckdb")
edges_df = con.execute("""
    SELECT e1.entity_value as src, e2.entity_value as dst,
           COUNT(*) as weight
    FROM entities e1
    JOIN entities e2 ON e1.document_id = e2.document_id AND e1.id < e2.id
    WHERE e1.entity_type = 'PERSON' AND e2.entity_type = 'PERSON'
    GROUP BY e1.entity_value, e2.entity_value
""").df()

# Visualize
g = graphistry.edges(edges_df, 'src', 'dst')
g = g.settings(url_params={'pointSize': 0.3, 'edgeCurvature': 0.1})
g.plot()
```

### NVIDIA RAPIDS cuGraph (GPU-Accelerated)

```python
import cudf
import cugraph

# Load edges to GPU
edges_gdf = cudf.read_csv('cooccurrences.csv')

# Create graph
G = cugraph.Graph()
G.from_cudf_edgelist(edges_gdf, source='source', destination='target',
                     edge_attr='weight')

# PageRank on GPU (1B+ nodes feasible)
pagerank = cugraph.pagerank(G)

# Louvain community detection
parts, modularity = cugraph.louvain(G)

# Connected components
components = cugraph.connected_components(G)
```

### NetworkX (CPU, smaller graphs)

```python
import networkx as nx
import duckdb

# Load from DuckDB
con = duckdb.connect("efta_documents.duckdb")
edges = con.execute("""
    SELECT source, target, weight FROM entity_cooccurrence
""").fetchall()

# Build graph
G = nx.Graph()
G.add_weighted_edges_from(edges)

# Analysis
centrality = nx.betweenness_centrality(G)
communities = nx.community.louvain_communities(G)
bridges = list(nx.bridges(G))

# Find shortest paths between entities of interest
path = nx.shortest_path(G, source="Person A", target="Person B")
```

## Graph Patterns for Investigations

### Entity Resolution

```cypher
// Find potential duplicates (fuzzy matching)
MATCH (p1:Person), (p2:Person)
WHERE p1.name <> p2.name
  AND apoc.text.jaroWinklerDistance(p1.name, p2.name) > 0.85
RETURN p1.name, p2.name, apoc.text.jaroWinklerDistance(p1.name, p2.name) AS similarity
ORDER BY similarity DESC;

// Merge duplicates
MATCH (p1:Person {name: 'Jeffrey Epstein'}), (p2:Person {name: 'J. Epstein'})
CALL apoc.refactor.mergeNodes([p1, p2], {properties: 'combine'})
YIELD node
RETURN node;
```

### Network Centrality

```cypher
// Degree centrality (most connected)
MATCH (p:Person)-[r]-()
RETURN p.name, count(r) AS connections
ORDER BY connections DESC LIMIT 20;

// Betweenness centrality (brokers/gatekeepers)
CALL gds.betweenness.stream('person-network')
YIELD nodeId, score
RETURN gds.util.asNode(nodeId).name AS name, score
ORDER BY score DESC LIMIT 20;

// Closeness centrality (fastest access to all others)
CALL gds.closeness.stream('person-network')
YIELD nodeId, score
RETURN gds.util.asNode(nodeId).name AS name, score
ORDER BY score DESC LIMIT 20;
```

### Temporal Network Analysis

```cypher
// Relationship evolution over time
MATCH (p1:Person)-[r:CONNECTED]->(p2:Person)
WHERE r.first_seen IS NOT NULL
RETURN p1.name, p2.name, r.first_seen, r.last_seen,
       duration.between(r.first_seen, r.last_seen) AS duration
ORDER BY r.first_seen;

// Activity bursts
MATCH (p:Person)-[r:MENTIONED_IN]->(d:Document)
WITH p, d.date AS date, count(*) AS mentions
RETURN p.name, date, mentions
ORDER BY p.name, date;
```

### Shell Company Detection

```cypher
// Find entities connected only through intermediaries
MATCH path = (company1:Company)-[:OFFICER*2..4]-(company2:Company)
WHERE NOT (company1)-[:OFFICER]-(company2)
  AND company1 <> company2
RETURN company1.name, company2.name,
       [n in nodes(path) | n.name] AS chain,
       length(path) AS hops
ORDER BY hops;

// Circular ownership patterns
MATCH path = (c:Company)-[:OWNS*3..6]->(c)
RETURN [n in nodes(path) | n.name] AS cycle,
       length(path) AS cycle_length;
```

## DuckDB Graph Analytics

```sql
-- PageRank approximation in SQL
WITH RECURSIVE pagerank AS (
    -- Initial rank
    SELECT entity_value AS node, 1.0 / COUNT(*) OVER () AS rank, 0 AS iteration
    FROM entities WHERE entity_type = 'PERSON'

    UNION ALL

    -- Iterate
    SELECT
        e.target AS node,
        0.15 / (SELECT COUNT(DISTINCT entity_value) FROM entities WHERE entity_type = 'PERSON')
        + 0.85 * SUM(pr.rank / outdegree.cnt),
        pr.iteration + 1
    FROM pagerank pr
    JOIN entity_cooccurrence e ON pr.node = e.source
    JOIN (
        SELECT source, COUNT(*) AS cnt FROM entity_cooccurrence GROUP BY source
    ) outdegree ON e.source = outdegree.source
    WHERE pr.iteration < 10
    GROUP BY e.target, pr.iteration
)
SELECT node, rank FROM pagerank WHERE iteration = 10
ORDER BY rank DESC LIMIT 20;

-- Community detection via connected components
WITH RECURSIVE components AS (
    SELECT entity_value AS node, entity_value AS component
    FROM entities WHERE entity_type = 'PERSON'

    UNION

    SELECT e.target, LEAST(c.component, e.source)
    FROM components c
    JOIN entity_cooccurrence e ON c.node = e.source
)
SELECT component, COUNT(*) AS size, array_agg(node) AS members
FROM (SELECT node, MIN(component) AS component FROM components GROUP BY node)
GROUP BY component
ORDER BY size DESC;
```

## Integration with EpsteinGeoACSet

```julia
# Export ACSet to Neo4j format
function export_to_neo4j(acset)
    # Export persons as nodes
    persons_csv = open("persons.csv", "w")
    println(persons_csv, "id:ID,name,role,:LABEL")
    for p in parts(acset, :Person)
        println(persons_csv, "$(p),$(acset[p, :person_name]),$(acset[p, :person_role]),Person")
    end
    close(persons_csv)

    # Export co-locations as edges
    edges_csv = open("colocations.csv", "w")
    println(edges_csv, ":START_ID,:END_ID,property,start_date,end_date,:TYPE")
    for col in parts(acset, :CoLocationEvent)
        tw = acset[col, :coloc_timewindow]
        prop = acset[col, :coloc_property]
        presences = filter(p -> acset[p, :pres_colocation] == col, parts(acset, :Presence))
        person_ids = [acset[p, :pres_person] for p in presences]

        # Create edges between all pairs
        for i in 1:length(person_ids)
            for j in (i+1):length(person_ids)
                println(edges_csv,
                    "$(person_ids[i]),$(person_ids[j])," *
                    "$(acset[prop, :property_name])," *
                    "$(acset[tw, :tw_start]),$(acset[tw, :tw_end])," *
                    "CO_LOCATED")
            end
        end
    end
    close(edges_csv)
end

# Import Neo4j analysis back to ACSet
function import_centrality!(acset, centrality_csv)
    for row in CSV.File(centrality_csv)
        person_id = findfirst(p -> acset[p, :person_name] == row.name, parts(acset, :Person))
        if person_id !== nothing
            set_subpart!(acset, person_id, :person_centrality, row.score)
        end
    end
end
```

## GF(3) Triad

```
citizen-lab-forensics (-1) ⊗ icij-document-analysis (0) ⊗ graph-investigation (+1) = 0 ✓
```

## CLI Recipes

```bash
# Import to Neo4j
neo4j-admin database import full \
  --nodes=Person=persons.csv \
  --nodes=Company=companies.csv \
  --nodes=Property=properties.csv \
  --relationships=colocations.csv \
  --relationships=flights.csv \
  epstein-graph

# Run GDS algorithms
cypher-shell -u neo4j -p password <<'CYPHER'
CALL gds.graph.project('epstein', 'Person', 'CO_LOCATED');
CALL gds.pageRank.write('epstein', {writeProperty: 'pagerank'});
CALL gds.louvain.write('epstein', {writeProperty: 'community'});
CYPHER

# Export high-centrality nodes
cypher-shell -u neo4j -p password --format plain <<'CYPHER'
MATCH (p:Person)
WHERE p.pagerank > 0.01
RETURN p.name, p.pagerank, p.community
ORDER BY p.pagerank DESC
CYPHER

# Visualize with PyGraphistry
python -c "
import graphistry
graphistry.register(api=3, server='hub.graphistry.com', username='$USER', password='$PASS')
from neo4j import GraphDatabase
driver = GraphDatabase.driver('bolt://localhost:7687', auth=('neo4j', 'password'))
with driver.session() as session:
    result = session.run('MATCH (a)-[r]->(b) RETURN a.name AS src, b.name AS dst, type(r) AS rel')
    edges = [dict(r) for r in result]
import pandas as pd
g = graphistry.edges(pd.DataFrame(edges), 'src', 'dst')
print(g.plot())
"
```

## Scale Considerations

| Scale | Tool | Notes |
|-------|------|-------|
| < 100K nodes | NetworkX | In-memory, CPU |
| 100K - 10M nodes | Neo4j | Disk-backed, indexed |
| 10M - 100M nodes | Neo4j + GDS | Graph Data Science library |
| 100M - 1B+ nodes | RAPIDS cuGraph | GPU required (A100 recommended) |
| Distributed | Neo4j Fabric / Spark GraphX | Multi-machine |

## References

- Neo4j GDS: https://neo4j.com/docs/graph-data-science/
- PyGraphistry: https://github.com/graphistry/pygraphistry
- RAPIDS cuGraph: https://docs.rapids.ai/api/cugraph/stable/
- Project Domino: (Stanford Internet Observatory methodology)
- ICIJ Tech Blog: https://www.icij.org/inside-icij/tech/

## See Also

- `citizen-lab-forensics` - Device forensics (trit -1)
- `icij-document-analysis` - Document processing (trit 0)
- `neo4j-cypher` (MCP) - Cypher queries
- `neo4j-data-modeling` (MCP) - Schema design
- `duckdb-ies` - Interactome analytics
