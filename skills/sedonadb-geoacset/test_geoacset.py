#!/usr/bin/env python3
"""SedonaDB GeoACSet Operations Test Suite"""

import sedonadb as sd

def test_all():
    db = sd.connect()
    print("=" * 60)
    print("SEDONADB GEOACSET OPERATIONS TEST")
    print("=" * 60)

    # 1. Create spatial hierarchy
    print("\n1. Creating OLC Tile Hierarchy...")
    result = db.sql("""
        WITH olc_tiles AS (
            SELECT '87' as code, 2 as precision, 
                   ST_GeomFromText('POLYGON((-80 40, -60 40, -60 60, -80 60, -80 40))') as bounds, 
                   0 as trit, CAST(NULL AS VARCHAR) as parent
            UNION ALL
            SELECT '87G8', 4, 
                   ST_GeomFromText('POLYGON((-74 40, -73 40, -73 41, -74 41, -74 40))'), 
                   1, '87'
            UNION ALL
            SELECT '87G9', 4,
                   ST_GeomFromText('POLYGON((-74 41, -73 41, -73 42, -74 42, -74 41))'),
                   -1, '87'
            UNION ALL
            SELECT '87G8Q2', 6,
                   ST_GeomFromText('POLYGON((-73.98 40.71, -73.93 40.71, -73.93 40.76, -73.98 40.76, -73.98 40.71))'),
                   0, '87G8'
        )
        SELECT code, precision, trit, parent
        FROM olc_tiles ORDER BY precision, code
    """)
    df = result.to_pandas()
    assert len(df) == 4, "Expected 4 tiles"
    print(f"   ✓ Created {len(df)} tiles")

    # 2. Up-traversal
    print("\n2. Up-traversal (P6 → P4 → P2)...")
    result = db.sql("""
        WITH RECURSIVE olc_tiles AS (
            SELECT '87' as code, 2 as precision, CAST(NULL AS VARCHAR) as parent
            UNION ALL SELECT '87G8', 4, '87'
            UNION ALL SELECT '87G9', 4, '87'
            UNION ALL SELECT '87G8Q2', 6, '87G8'
        ),
        ancestors AS (
            SELECT code, parent, precision, 1 as level
            FROM olc_tiles WHERE code = '87G8Q2'
            UNION ALL
            SELECT t.code, t.parent, t.precision, a.level + 1
            FROM olc_tiles t JOIN ancestors a ON t.code = a.parent
        )
        SELECT code, precision, level FROM ancestors ORDER BY level
    """)
    df = result.to_pandas()
    assert len(df) == 3, "Expected 3 ancestors"
    assert df.iloc[0]['code'] == '87G8Q2', "Should start at P6"
    assert df.iloc[2]['code'] == '87', "Should end at P2"
    print(f"   ✓ Traversed {len(df)} levels")

    # 3. Point-in-tile
    print("\n3. Point-in-tile query...")
    result = db.sql("""
        WITH olc_tiles AS (
            SELECT '87G8Q2' as code,
                   ST_GeomFromText('POLYGON((-73.98 40.71, -73.93 40.71, -73.93 40.76, -73.98 40.76, -73.98 40.71))') as bounds
        )
        SELECT ST_Contains(bounds, ST_Point(-73.9615, 40.7175)) as contains
        FROM olc_tiles
    """)
    assert result.to_pandas().iloc[0]['contains'] == True
    print("   ✓ Brass Factory contained in tile")

    # 4. GF(3) conservation
    print("\n4. GF(3) Conservation...")
    result = db.sql("""
        WITH trits AS (
            SELECT 0 as trit UNION ALL SELECT 1 UNION ALL SELECT -1 UNION ALL SELECT 0
        )
        SELECT SUM(trit) as total, SUM(trit) % 3 = 0 as balanced FROM trits
    """)
    df = result.to_pandas()
    assert df.iloc[0]['balanced'] == True
    print(f"   ✓ Sum={df.iloc[0]['total']}, Balanced={df.iloc[0]['balanced']}")

    # 5. Spatial join
    print("\n5. Spatial join (tiles containing point)...")
    result = db.sql("""
        WITH olc_tiles AS (
            SELECT '87' as code, 2 as precision, 
                   ST_GeomFromText('POLYGON((-80 40, -60 40, -60 60, -80 60, -80 40))') as bounds
            UNION ALL SELECT '87G8', 4, 
                   ST_GeomFromText('POLYGON((-74 40, -73 40, -73 41, -74 41, -74 40))')
            UNION ALL SELECT '87G8Q2', 6,
                   ST_GeomFromText('POLYGON((-73.98 40.71, -73.93 40.71, -73.93 40.76, -73.98 40.76, -73.98 40.71))')
        )
        SELECT code FROM olc_tiles
        WHERE ST_Contains(bounds, ST_Point(-73.9615, 40.7175))
    """)
    assert len(result.to_pandas()) == 3
    print("   ✓ Point in 3 hierarchical tiles")

    # 6. KNN
    print("\n6. KNN query...")
    result = db.sql("""
        WITH points AS (
            SELECT 'A' as id, ST_Point(-73.5, 40.5) as geom
            UNION ALL SELECT 'B', ST_Point(-73.955, 40.735)
            UNION ALL SELECT 'C', ST_Point(-74.5, 41.5)
        )
        SELECT id FROM points
        ORDER BY ST_Distance(geom, ST_Point(-73.9615, 40.7175))
        LIMIT 1
    """)
    assert result.to_pandas().iloc[0]['id'] == 'B'
    print("   ✓ Nearest point found")

    # 7. Fokker-Planck neighbors
    print("\n7. Fokker-Planck neighbors...")
    result = db.sql("""
        WITH tiles AS (
            SELECT '87G8' as code, 
                   ST_GeomFromText('POLYGON((-74 40, -73 40, -73 41, -74 41, -74 40))') as bounds
            UNION ALL SELECT '87G9', 
                   ST_GeomFromText('POLYGON((-74 41, -73 41, -73 42, -74 42, -74 41))')
        )
        SELECT a.code, b.code as neighbor
        FROM tiles a, tiles b
        WHERE a.code < b.code AND ST_Touches(a.bounds, b.bounds)
    """)
    assert len(result.to_pandas()) == 1
    print("   ✓ Found 1 touching pair")

    print("\n" + "=" * 60)
    print("✓ ALL 7 TESTS PASSED")
    print("=" * 60)

if __name__ == "__main__":
    test_all()
