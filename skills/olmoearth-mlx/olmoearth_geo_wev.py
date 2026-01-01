#!/usr/bin/env python3
"""
OlmoEarth Geographic WEV Extraction
AI2 OlmoEarth + Dune.xyz + GeoACSet Integration

Maps crypto wallet activity to geographic impact areas using:
1. OlmoEarth embeddings for satellite imagery context
2. Dune.xyz queries for on-chain geographic signals
3. GeoACSet categorical structures for spatial reasoning
4. GF(3) triadic classification for WEV extraction
"""

import json
import math
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from enum import Enum

GOLDEN = 0x9E3779B97F4A7C15

class Trit(Enum):
    MINUS = -1
    ERGODIC = 0
    PLUS = 1

@dataclass
class GeoLocation:
    """Geographic location with metadata."""
    lat: float
    lon: float
    name: str
    country: str
    region: str
    
    def haversine_distance(self, other: 'GeoLocation') -> float:
        """Calculate great-circle distance in km."""
        R = 6371
        dlat = math.radians(other.lat - self.lat)
        dlon = math.radians(other.lon - self.lon)
        a = (math.sin(dlat/2)**2 + 
             math.cos(math.radians(self.lat)) * 
             math.cos(math.radians(other.lat)) * 
             math.sin(dlon/2)**2)
        return 2 * R * math.atan2(math.sqrt(a), math.sqrt(1-a))

@dataclass
class ImpactZone:
    """Protocol Labs impact zone."""
    name: str
    center: GeoLocation
    radius_km: float
    zone_type: str  # high_density, emerging, frontier
    trit: Trit

@dataclass
class GeoWEVEvent:
    """Geographic World Extractable Value event."""
    id: str
    location: GeoLocation
    zone: Optional[ImpactZone]
    trit: Trit
    value_usd: float
    source: str  # dune query name
    category: str  # genesis, arbitrage, sunset, etc.
    timestamp: float
    embedding: Optional[List[float]] = None  # OlmoEarth embedding

@dataclass
class GeoACSetNode:
    """Node in the GeoACSet categorical structure."""
    id: int
    node_type: str  # Region, District, Parcel, Building
    parent_id: Optional[int]
    location: Optional[GeoLocation]
    trit: Trit
    metadata: Dict = field(default_factory=dict)

class ProtocolLabsImpactMap:
    """Map of Protocol Labs infrastructure impact zones."""
    
    def __init__(self):
        self.zones: List[ImpactZone] = []
        self._init_zones()
    
    def _init_zones(self):
        """Initialize PL impact zones globally."""
        
        # HIGH DENSITY (+1): Core infrastructure hubs
        high_density = [
            ("SF Bay Area", 37.7749, -122.4194, "US", "California", 100),
            ("Greater NYC", 40.7128, -74.0060, "US", "New York", 80),
            ("Singapore", 1.3521, 103.8198, "SG", "Singapore", 50),
            ("London", 51.5074, -0.1278, "UK", "England", 60),
            ("Tokyo", 35.6762, 139.6503, "JP", "Tokyo", 70),
        ]
        
        # EMERGING (0): Growth potential zones
        emerging = [
            ("Shenzhen", 22.5431, 114.0579, "CN", "Guangdong", 60),
            ("Berlin", 52.5200, 13.4050, "DE", "Berlin", 40),
            ("Bangalore", 12.9716, 77.5946, "IN", "Karnataka", 50),
            ("Seoul", 37.5665, 126.9780, "KR", "Seoul", 50),
            ("Amsterdam", 52.3676, 4.9041, "NL", "North Holland", 35),
            ("Toronto", 43.6532, -79.3832, "CA", "Ontario", 45),
        ]
        
        # FRONTIER (-1): Adoption catalyst zones
        frontier = [
            ("Lagos", 6.5244, 3.3792, "NG", "Lagos", 30),
            ("São Paulo", -23.5505, -46.6333, "BR", "São Paulo", 60),
            ("Jakarta", -6.2088, 106.8456, "ID", "Jakarta", 40),
            ("Nairobi", -1.2921, 36.8219, "KE", "Nairobi", 25),
            ("Mexico City", 19.4326, -99.1332, "MX", "CDMX", 50),
            ("Buenos Aires", -34.6037, -58.3816, "AR", "Buenos Aires", 45),
        ]
        
        for name, lat, lon, country, region, radius in high_density:
            self.zones.append(ImpactZone(
                name=name,
                center=GeoLocation(lat, lon, name, country, region),
                radius_km=radius,
                zone_type="high_density",
                trit=Trit.PLUS
            ))
        
        for name, lat, lon, country, region, radius in emerging:
            self.zones.append(ImpactZone(
                name=name,
                center=GeoLocation(lat, lon, name, country, region),
                radius_km=radius,
                zone_type="emerging",
                trit=Trit.ERGODIC
            ))
        
        for name, lat, lon, country, region, radius in frontier:
            self.zones.append(ImpactZone(
                name=name,
                center=GeoLocation(lat, lon, name, country, region),
                radius_km=radius,
                zone_type="frontier",
                trit=Trit.MINUS
            ))
    
    def classify(self, lat: float, lon: float) -> Tuple[Optional[ImpactZone], float]:
        """Classify a location into the nearest impact zone."""
        loc = GeoLocation(lat, lon, "", "", "")
        
        best_zone = None
        best_dist = float('inf')
        
        for zone in self.zones:
            dist = loc.haversine_distance(zone.center)
            if dist <= zone.radius_km and dist < best_dist:
                best_zone = zone
                best_dist = dist
        
        return best_zone, best_dist

class DuneGeographicQueries:
    """Simulated Dune.xyz queries for geographic crypto data."""
    
    QUERIES = {
        "filecoin_storage_providers": """
            SELECT provider_id, lat, lon, country, region, 
                   deal_count, total_bytes, revenue_fil
            FROM filecoin.storage_providers_geo
            WHERE active = true
        """,
        "fvm_contract_deployments": """
            SELECT creator_address, lat, lon, country,
                   contract_count, gas_used, timestamp
            FROM filecoin.fvm_contracts_geo
            WHERE timestamp > NOW() - INTERVAL '30 days'
        """,
        "bridge_transactions": """
            SELECT source_chain, dest_chain,
                   sender_lat, sender_lon, receiver_lat, receiver_lon,
                   amount_usd, timestamp
            FROM bridges.transactions_geo
            WHERE (source_chain = 'filecoin' OR dest_chain = 'filecoin')
        """,
        "grant_disbursements": """
            SELECT recipient_address, lat, lon, country, region,
                   grant_amount_usd, program, timestamp
            FROM filecoin.grants_geo
            WHERE timestamp > NOW() - INTERVAL '90 days'
        """
    }
    
    @staticmethod
    def simulate_results(query_name: str, limit: int = 20) -> List[Dict]:
        """Simulate Dune query results with realistic geographic distribution."""
        import random
        random.seed(0x42D)
        
        # Sample locations weighted by PL activity
        locations = [
            (37.7749, -122.4194, "US", "California", 0.25),      # SF
            (40.7128, -74.0060, "US", "New York", 0.12),         # NYC
            (1.3521, 103.8198, "SG", "Singapore", 0.10),         # Singapore
            (51.5074, -0.1278, "UK", "England", 0.08),           # London
            (52.5200, 13.4050, "DE", "Berlin", 0.07),            # Berlin
            (22.5431, 114.0579, "CN", "Guangdong", 0.08),        # Shenzhen
            (35.6762, 139.6503, "JP", "Tokyo", 0.06),            # Tokyo
            (-23.5505, -46.6333, "BR", "São Paulo", 0.05),       # São Paulo
            (6.5244, 3.3792, "NG", "Lagos", 0.04),               # Lagos
            (12.9716, 77.5946, "IN", "Karnataka", 0.05),         # Bangalore
            (-6.2088, 106.8456, "ID", "Jakarta", 0.03),          # Jakarta
            (52.3676, 4.9041, "NL", "North Holland", 0.04),      # Amsterdam
            (37.5665, 126.9780, "KR", "Seoul", 0.03),            # Seoul
        ]
        
        results = []
        for i in range(limit):
            # Weighted random selection
            r = random.random()
            cumulative = 0
            selected = locations[0]
            for loc in locations:
                cumulative += loc[4]
                if r <= cumulative:
                    selected = loc
                    break
            
            lat, lon, country, region, _ = selected
            # Add some jitter
            lat += random.gauss(0, 0.5)
            lon += random.gauss(0, 0.5)
            
            results.append({
                "id": f"{query_name}_{i}",
                "lat": lat,
                "lon": lon,
                "country": country,
                "region": region,
                "value_usd": random.uniform(100, 100000),
                "timestamp": time.time() - random.uniform(0, 86400 * 30)
            })
        
        return results

class OlmoEarthEmbedder:
    """Simulated OlmoEarth embedding generator."""
    
    def __init__(self, model_size: str = "base"):
        self.model_size = model_size
        self.embed_dim = {"nano": 192, "tiny": 384, "base": 768, "large": 1024}[model_size]
    
    def embed(self, lat: float, lon: float) -> List[float]:
        """Generate embedding for a geographic location."""
        import random
        # Deterministic seed based on location
        seed = int((lat * 1000 + lon) * 1000) % (2**31)
        random.seed(seed)
        
        # Generate pseudo-embedding (in real impl, would use actual model)
        embedding = [random.gauss(0, 1) for _ in range(self.embed_dim)]
        
        # Normalize
        norm = math.sqrt(sum(x*x for x in embedding))
        return [x / norm for x in embedding]

class GeoACSet:
    """Categorical structure for geographic crypto data."""
    
    def __init__(self):
        self.nodes: Dict[int, GeoACSetNode] = {}
        self.next_id = 1
        self.morphisms: List[Tuple[int, int, str]] = []  # (source, target, type)
    
    def add_node(self, node_type: str, parent_id: Optional[int] = None,
                 location: Optional[GeoLocation] = None, trit: Trit = Trit.ERGODIC,
                 **metadata) -> int:
        """Add a node to the ACSet."""
        node_id = self.next_id
        self.next_id += 1
        
        self.nodes[node_id] = GeoACSetNode(
            id=node_id,
            node_type=node_type,
            parent_id=parent_id,
            location=location,
            trit=trit,
            metadata=metadata
        )
        
        if parent_id:
            self.morphisms.append((node_id, parent_id, "contained_in"))
        
        return node_id
    
    def get_by_type(self, node_type: str) -> List[GeoACSetNode]:
        """Get all nodes of a given type."""
        return [n for n in self.nodes.values() if n.node_type == node_type]
    
    def gf3_sum(self) -> int:
        """Calculate GF(3) sum of all node trits."""
        return sum(n.trit.value for n in self.nodes.values())
    
    def materialize_from_wev(self, events: List[GeoWEVEvent]) -> 'GeoACSet':
        """Materialize ACSet structure from WEV events."""
        # Group by region
        regions: Dict[str, List[GeoWEVEvent]] = {}
        for event in events:
            key = f"{event.location.country}_{event.location.region}"
            if key not in regions:
                regions[key] = []
            regions[key].append(event)
        
        # Create hierarchical structure
        for region_key, region_events in regions.items():
            country, region = region_key.split("_", 1)
            
            # Add region node
            region_id = self.add_node(
                "Region",
                location=region_events[0].location,
                trit=region_events[0].trit,
                country=country,
                region=region
            )
            
            # Add district nodes (cluster nearby events)
            for event in region_events:
                district_id = self.add_node(
                    "District",
                    parent_id=region_id,
                    location=event.location,
                    trit=event.trit,
                    value_usd=event.value_usd
                )
                
                # Add parcel (individual event)
                self.add_node(
                    "Parcel",
                    parent_id=district_id,
                    location=event.location,
                    trit=event.trit,
                    event_id=event.id,
                    source=event.source,
                    embedding=event.embedding
                )
        
        return self

class GeoWEVEngine:
    """Main engine for geographic WEV extraction."""
    
    def __init__(self, seed: int = 0x42D):
        self.seed = seed
        self.impact_map = ProtocolLabsImpactMap()
        self.embedder = OlmoEarthEmbedder("base")
        self.events: List[GeoWEVEvent] = []
        self.geoacset = GeoACSet()
    
    def extract_from_dune(self, query_name: str, limit: int = 20) -> List[GeoWEVEvent]:
        """Extract geographic WEV from Dune query."""
        results = DuneGeographicQueries.simulate_results(query_name, limit)
        
        events = []
        for row in results:
            # Classify impact zone
            zone, dist = self.impact_map.classify(row["lat"], row["lon"])
            
            # Determine trit
            if zone:
                trit = zone.trit
            else:
                trit = Trit.ERGODIC  # Default for unclassified
            
            # Get OlmoEarth embedding
            embedding = self.embedder.embed(row["lat"], row["lon"])
            
            # Create event
            event = GeoWEVEvent(
                id=row["id"],
                location=GeoLocation(
                    lat=row["lat"],
                    lon=row["lon"],
                    name=zone.name if zone else "Global",
                    country=row["country"],
                    region=row["region"]
                ),
                zone=zone,
                trit=trit,
                value_usd=row["value_usd"],
                source=query_name,
                category=self._categorize_query(query_name),
                timestamp=row["timestamp"],
                embedding=embedding[:10]  # Truncate for display
            )
            events.append(event)
        
        self.events.extend(events)
        return events
    
    def _categorize_query(self, query_name: str) -> str:
        """Map query to WEV category."""
        categories = {
            "filecoin_storage_providers": "genesis",
            "fvm_contract_deployments": "narrative",
            "bridge_transactions": "arbitrage",
            "grant_disbursements": "liquidity"
        }
        return categories.get(query_name, "unknown")
    
    def materialize_geoacset(self) -> GeoACSet:
        """Materialize GeoACSet from extracted events."""
        self.geoacset = GeoACSet()
        self.geoacset.materialize_from_wev(self.events)
        return self.geoacset
    
    def status(self) -> Dict:
        """Get engine status."""
        zone_counts = {"high_density": 0, "emerging": 0, "frontier": 0, "global": 0}
        value_by_zone = {"high_density": 0.0, "emerging": 0.0, "frontier": 0.0, "global": 0.0}
        
        for event in self.events:
            zone_type = event.zone.zone_type if event.zone else "global"
            zone_counts[zone_type] += 1
            value_by_zone[zone_type] += event.value_usd
        
        return {
            "total_events": len(self.events),
            "zone_counts": zone_counts,
            "value_by_zone": {k: round(v, 2) for k, v in value_by_zone.items()},
            "geoacset_nodes": len(self.geoacset.nodes),
            "geoacset_morphisms": len(self.geoacset.morphisms),
            "gf3_sum": self.geoacset.gf3_sum() if self.geoacset.nodes else 0
        }

def main():
    """Run geographic WEV extraction."""
    print("=" * 70)
    print("OLMOEARTH GEOGRAPHIC WEV EXTRACTION")
    print("AI2 OlmoEarth + Dune.xyz + GeoACSet + GF(3)")
    print("=" * 70)
    
    engine = GeoWEVEngine()
    
    # Extract from multiple Dune queries
    queries = [
        "filecoin_storage_providers",
        "fvm_contract_deployments",
        "bridge_transactions",
        "grant_disbursements"
    ]
    
    print("\n--- Extracting Geographic WEV ---")
    for query in queries:
        events = engine.extract_from_dune(query, limit=15)
        print(f"  {query}: {len(events)} events")
    
    # Materialize GeoACSet
    print("\n--- Materializing GeoACSet ---")
    geoacset = engine.materialize_geoacset()
    
    # Display by node type
    for node_type in ["Region", "District", "Parcel"]:
        nodes = geoacset.get_by_type(node_type)
        print(f"  {node_type}: {len(nodes)} nodes")
    
    # Status
    print("\n--- Geographic Impact Analysis ---")
    status = engine.status()
    
    print(f"\nZone Distribution:")
    for zone_type, count in status["zone_counts"].items():
        trit_sym = {"high_density": "[+]", "emerging": "[○]", "frontier": "[-]", "global": "[?]"}[zone_type]
        value = status["value_by_zone"][zone_type]
        print(f"  {trit_sym} {zone_type:<12}: {count:>3} events, ${value:>12,.2f}")
    
    print(f"\nGeoACSet:")
    print(f"  Nodes: {status['geoacset_nodes']}")
    print(f"  Morphisms: {status['geoacset_morphisms']}")
    print(f"  GF(3) Sum: {status['gf3_sum']}")
    
    # Top locations
    print("\n--- Top Impact Locations ---")
    location_values: Dict[str, float] = {}
    for event in engine.events:
        key = event.location.name
        location_values[key] = location_values.get(key, 0) + event.value_usd
    
    for loc, value in sorted(location_values.items(), key=lambda x: -x[1])[:10]:
        print(f"  {loc:<20}: ${value:>12,.2f}")
    
    # Export
    with open("geo_wev_status.json", "w") as f:
        json.dump(status, f, indent=2)
    
    print("\n✓ Status exported to geo_wev_status.json")
    
    return status

if __name__ == "__main__":
    main()
