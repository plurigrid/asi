---
name: glass-line
description: Physical substrate layer for Plurigrid ASI — co-deployed fiber optic + geothermal infrastructure providing sensing, communication, energy, and materials extraction through a single bore.
version: 0.1.0
trit: -1
bundle: infrastructure
extends: plurigrid-asi-integrated
---

# Glass Line

> The bore hole is the conduit. The fiber is the sensor. The heat is the energy. The observation channel and the communication channel are the same physical object.

## Position in ASI Lattice

```
                    ┌─────────────────┐
                    │  glass-bead-game │
                    │  (synthesis)     │
                    └────────┬────────┘
                             │
         ┌───────────────────┼───────────────────┐
         │                   │                   │
┌────────▼────────┐ ┌────────▼────────┐ ┌────────▼────────┐
│  world-hopping  │ │  bisimulation   │ │  triad-interleave│
│  (navigation)   │ │  (dispersal)    │ │  (scheduling)    │
└────────┬────────┘ └────────┬────────┘ └────────┬────────┘
         │                   │                   │
         └───────────────────┼───────────────────┘
                             │
                    ┌────────▼────────┐
                    │     gay-mcp      │
                    │  (coloring)      │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │     acsets       │
                    │  (data model)    │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │   glass-line     │  ← NEW: physical substrate
                    │  (substrate)     │
                    └─────────────────┘
```

## Four Outputs From One Bore

| Output | Mechanism | Maps To |
|--------|-----------|---------|
| **Energy** | Geothermal heat → turbine or heat exchange | DGX Spark cluster power + cooling |
| **Communication** | Glass fiber in bore casing | Low-latency backhaul for hamming swarm |
| **Sensing** | Distributed Temperature Sensing (DTS) via Rayleigh/Brillouin scattering | Real-time thermal gradient monitoring |
| **Materials** | Brine extraction (lithium, rare earths) | Hardware supply chain (Cornwall model) |

## Schema

```julia
@present SchGlassLine(FreeSchema) begin
  Bore::Ob
  Fiber::Ob
  Sensor::Ob
  Well::Ob

  # A bore contains fibers and connects to wells
  contains::Hom(Bore, Fiber)
  taps::Hom(Bore, Well)

  # A fiber is simultaneously a sensor and a communication channel
  senses::Hom(Fiber, Sensor)
  communicates::Hom(Fiber, Fiber)  # self-referential: the medium IS the message

  # Attributes
  Depth::AttrType
  Temperature::AttrType
  Wavelength::AttrType
  Trit::AttrType

  depth::Attr(Bore, Depth)
  thermal_gradient::Attr(Well, Temperature)
  wavelength::Attr(Fiber, Wavelength)     # 1550nm C-band for telecom, 1064nm for DTS
  trit::Attr(Bore, Trit)                  # GF(3) coloring of physical sites
end
```

## DTS (Distributed Temperature Sensing)

The fiber IS the sensor. No separate instruments needed.

```
Technique          Resolution    Range     Mechanism
─────────────────────────────────────────────────────
Raman DTS          1m spatial    10km      Anti-Stokes/Stokes ratio
Brillouin OTDR     1m spatial    50km      Frequency shift ∝ temperature
Rayleigh OFDR      1mm spatial   70m       Phase-sensitive backscatter
```

For a geothermal bore (typically 2-5km depth):
- Raman DTS at 1550nm: continuous thermal profile of entire bore
- Same fiber carries 100Gbps+ telecom in separate wavelength band (WDM)
- Temperature data streams to DuckDB via MQTT → glass-line sensor table

## Site Selection Criteria

```sql
-- Optimal co-location: geothermal gradient + fiber trunk + compute
SELECT site, geothermal_gradient_c_per_km,
       distance_to_fiber_trunk_km,
       distance_to_compute_facility_km,
       (geothermal_gradient_c_per_km * 10
        - distance_to_fiber_trunk_km
        - distance_to_compute_facility_km * 2) AS score
FROM candidate_sites
WHERE geothermal_gradient_c_per_km > 30  -- minimum viable gradient
  AND distance_to_fiber_trunk_km < 50
ORDER BY score DESC;
```

### Known Candidate Regions

| Region | Gradient | Fiber | Compute | Notes |
|--------|----------|-------|---------|-------|
| Portland/Cascadia | 40-60°C/km | Major hub (NWAX) | Existing warehouse | Your DGX cluster |
| Cornwall UK | 35-40°C/km | Subsea cables | New facility | Lithium co-extraction proven |
| Reykjavik | 100+°C/km | IRIS submarine | Verne Global | Already operational |
| Nevada/Great Basin | 50-80°C/km | Las Vegas trunk | Switch datacenters | BLM land available |
| Pennsylvania mines | Variable | Northeast corridor | Planned 13GW DCs | Abandoned mine cooling |

## Integration With Hamming Swarm

Each physical glass-line site becomes a world in the 26-letter mesh:

```python
# A glass-line site binds to a world wallet
class GlassLineSite:
    def __init__(self, letter: str, bore_depth_m: float, fiber_count: int):
        self.letter = letter
        self.world_wallet = WORLD_WALLETS[letter]
        self.bore_depth = bore_depth_m
        self.fiber_count = fiber_count
        self.dts_stream = None  # MQTT topic for thermal data

    def bind_to_swarm(self, mesh: HammingSwarm):
        """Physical site joins the multisig mesh"""
        # The site's thermal output backs the world's DeFi position
        # Geothermal energy production → staking yield analogy:
        # constant baseload output, no intermittency,
        # 90%+ capacity factor (like Amnis stAPT stability)
        mesh.register_site(self.letter, self)

    def sense(self) -> dict:
        """DTS reading from fiber"""
        # Returns temperature profile along entire bore
        # This IS the observation — no separate measurement needed
        return self.dts_stream.latest()
```

## Energy Economics

```
Geothermal LCOE:    $0.04-0.08/kWh (baseload, 90%+ capacity factor)
Grid power (US avg): $0.12/kWh
DGX Spark (3 nodes): ~6kW sustained
Annual energy cost:
  Grid:        6kW × 8760h × $0.12 = $6,307/yr
  Geothermal:  6kW × 8760h × $0.05 = $2,628/yr
  Savings:     $3,679/yr (~58%)

Cooling savings (ground loop vs HVAC):
  ~40% reduction in cooling energy
  Additional $1,500-2,500/yr savings

Total annual savings: ~$5,000-6,000/yr
  = ~700 APT/yr at current price
  > 5x the entire DeFi yield (10.8 APT/yr)
```

The physical substrate dominates the digital yield.

## GF(3) Triad

| Trit | Layer | Role |
|------|-------|------|
| -1 | **glass-line** | Physical substrate (sensing, energy, materials) |
| 0 | acsets + gay-mcp | Data model + coloring (digital structure) |
| +1 | glass-bead-game | Synthesis (emergent coordination) |

Conservation: the physical (-1) grounds the digital (0) which enables the emergent (+1).

## Monitoring

```bash
# Stream DTS data to DuckDB
mosquitto_sub -t "glassline/+/dts" | \
  duckdb ~/i.duckdb -c "
    INSERT INTO glass_line_dts
    SELECT * FROM read_json('/dev/stdin', auto_detect=true);"

# Thermal gradient alert
duckdb ~/i.duckdb -c "
  SELECT site, depth_m, temp_c,
         temp_c - LAG(temp_c) OVER (ORDER BY depth_m) AS gradient
  FROM glass_line_dts
  WHERE site = 'portland'
  ORDER BY depth_m DESC LIMIT 20;"

# Energy production vs DeFi yield comparison
duckdb ~/i.duckdb -c "
  SELECT
    'geothermal' AS source, annual_kwh * 0.05 AS annual_usd,
    annual_kwh * 0.05 / 7.5 AS annual_apt  -- at $7.50/APT
  FROM glass_line_sites
  UNION ALL
  SELECT 'defi_yield', 10.84 * 7.5, 10.84
  FROM (SELECT 1);"
```

## Related Skills

- `plurigrid-asi-integrated` — parent lattice
- `glass-bead-game` — synthesis layer above
- `acsets` — data model for bore/fiber/sensor schema
- `defillama-api` — DeFi yield comparison
- `duckdb-ies` — simultaneity_surfaces view for co-temporal sensing
- `warehouse-network` — DGX cluster coordination
- `gx10-offload` — compute offload to cluster nodes
