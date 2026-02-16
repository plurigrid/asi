#!/usr/bin/env python3
"""
Build an isometric view for OlmoEarth relational structures in a clocked
information space.

This script reuses existing OlmoEarthW
VE extraction code and emits a static HTML file that:

- lays out GeoACSet nodes (Region/District/Parcel) in 2.5D isometric space
- encodes parent/child structure with edges
- maps node timestamps to a 12-hour informational clock ring
- color-codes GF(3) trits for relational balance
"""

from __future__ import annotations

import argparse
import json
import math
import time
from collections import defaultdict
from dataclasses import asdict
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional

from olmoearth_geo_wev import GeoWEVEngine, GeoACSetNode, Trit, GeoWEVEvent


TRIT_STYLES = {
    Trit.PLUS.value: {
        "label": "PLUS",
        "bg": "#2ECC71",
        "light": "#58D68D",
        "border": "#196F3D",
    },
    Trit.MINUS.value: {
        "label": "MINUS",
        "bg": "#E74C3C",
        "light": "#F1948A",
        "border": "#922B21",
    },
    Trit.ERGODIC.value: {
        "label": "ERGODIC",
        "bg": "#5DADE2",
        "light": "#85C1E9",
        "border": "#2471A3",
    },
}

TYPE_STYLES = {
    "Region": {
        "width": 120,
        "height": 70,
        "depth": 22,
        "z": 0,
    },
    "District": {
        "width": 96,
        "height": 58,
        "depth": 18,
        "z": 1,
    },
    "Parcel": {
        "width": 78,
        "height": 48,
        "depth": 14,
        "z": 2,
    },
}


def _clock_hour(event_time: float, granularity: int = 2) -> int:
    """Map epoch seconds to clock sectors. granularity=hours per sector (1,2,3,6)."""
    return int(datetime.fromtimestamp(event_time).hour / granularity)


def _clock_label(hour_sector: int, granularity: int = 2) -> str:
    return f"{(hour_sector * granularity):02d}:00"


def _iso_project(x: float, y: float, z: float) -> tuple[int, int]:
    """Project 3D integer lattice coordinates into isometric pixel space."""
    sx = int((x - y) * 28)
    sy = int((x + y) * 16 - z * 14)
    return sx, sy


def _shape_payload(nodes: Dict[int, GeoACSetNode], events: Dict[str, GeoWEVEvent], engine: GeoWEVEngine, granularity: int = 2):
    children_by_parent: Dict[Optional[int], list[int]] = defaultdict(list)
    for child_id, parent_id, _ in engine.geoacset.morphisms:
        children_by_parent[parent_id].append(child_id)

    # Index timestamp by node using event id when available, with region/district
    # aggregations derived from descendants.
    event_ts_by_id: Dict[str, float] = {evt.id: evt.timestamp for evt in events.values()}

    _time_cache: Dict[int, Optional[float]] = {}

    def resolve_node_time(node_id: int) -> Optional[float]:
        if node_id in _time_cache:
            return _time_cache[node_id]
        node = nodes[node_id]
        if node.node_type == "Parcel":
            event_id = node.metadata.get("event_id")
            if isinstance(event_id, str):
                result = event_ts_by_id.get(event_id)
                _time_cache[node_id] = result
                return result

        child_times = [
            t for cid in children_by_parent.get(node_id, [])
            if (t := resolve_node_time(cid)) is not None
        ]
        result = sum(child_times) / len(child_times) if child_times else None
        _time_cache[node_id] = result
        return result

    regions = [n for n in nodes.values() if n.node_type == "Region"]
    for n in nodes.values():
        if n.location and hasattr(n.location, "name"):
            _ = n.location.name

    # Group parcels into region and timestamp buckets.
    region_nodes = [n for n in regions]
    region_order = []
    for region in region_nodes:
        ts = resolve_node_time(region.id)
        if ts is None:
            ts = 0.0
        region_order.append((region.id, _clock_hour(ts, granularity), ts, region))

    region_order.sort(key=lambda item: (item[1], item[2]))

    # Layout roots on clock positions.
    layout = {}
    for idx, (region_id, hour_sector, _ts, region_node) in enumerate(region_order):
        angle = math.tau * (idx / max(1, len(region_order)))
        ring_radius = 8
        region_x = ring_radius * math.cos(angle)
        region_y = ring_radius * math.sin(angle)
        layout[region_id] = {
            "node_id": region_id,
            "x": region_x,
            "y": region_y,
            "depth": TYPE_STYLES[region_node.node_type]["z"],
            "clock": hour_sector,
            "parent": region_node.parent_id,
        }

    # Place children relative to region location.
    for region_id in children_by_parent:
        parent = nodes[region_id]
        if parent.node_type != "Region":
            continue
        r = layout[region_id]
        for di, child_id in enumerate(children_by_parent.get(region_id, [])):
            child = nodes[child_id]
            if child.node_type != "District":
                continue
            child_clock = _clock_hour(resolve_node_time(child_id) or time.time(), granularity)
            c = children_by_parent.get(child_id, [])
            col = (di % 4) - 1.5
            row = di // 4
            layout[child_id] = {
                "node_id": child_id,
                "x": r["x"] + col * 1.2,
                "y": r["y"] + row * 1.0,
                "depth": TYPE_STYLES[child.node_type]["z"] + (child_clock * 0.05),
                "clock": child_clock,
                "parent": child.parent_id,
            }
            for pi, parcel_id in enumerate(children_by_parent.get(child_id, [])):
                parcel = nodes[parcel_id]
                if parcel.node_type != "Parcel":
                    continue
                pclock = _clock_hour(resolve_node_time(parcel_id) or time.time(), granularity)
                pcol = (pi % 3) - 1
                prow = pi // 3
                layout[parcel_id] = {
                    "node_id": parcel_id,
                    "x": layout[child_id]["x"] + pcol * 0.6,
                    "y": layout[child_id]["y"] + 0.6 + prow * 0.8,
                    "depth": TYPE_STYLES[parcel.node_type]["z"] + (pclock * 0.05),
                    "clock": pclock,
                    "parent": parcel.parent_id,
                }

    payload_nodes = []
    for nid, node in nodes.items():
        layout_info = layout.get(nid, {"x": 0, "y": 0, "depth": 0, "clock": 0, "parent": node.parent_id})
        trit_value = node.trit.value if hasattr(node.trit, "value") else node.trit
        style = TRIT_STYLES.get(trit_value, TRIT_STYLES[0])
        size = TYPE_STYLES[node.node_type]
        payload_nodes.append(
            {
                "id": nid,
                "type": node.node_type,
                "label": node.node_type,
                "trit": trit_value,
                "trit_label": style["label"],
                "bg": style["bg"],
                "light": style["light"],
                "border": style["border"],
                "clock": layout_info["clock"],
                "clock_label": _clock_label(layout_info["clock"], granularity),
                "value": float(node.metadata.get("value_usd", 0.0)),
                "country": node.metadata.get("country", ""),
                "region": node.metadata.get("region", ""),
                "parent": layout_info["parent"],
                "iso_x": node.location.lat if node.location else 0.0,
                "iso_y": node.location.lon if node.location else 0.0,
                "depth": layout_info["depth"],
                "grid_x": size["width"],
                "grid_y": size["height"],
                "depth_size": size["depth"],
                "x": layout_info["x"],
                "y": layout_info["y"],
            }
        )

    edges = []
    for child_id, parent_id, _ in engine.geoacset.morphisms:
        if parent_id is None:
            continue
        edges.append({"from": child_id, "to": parent_id})

    return payload_nodes, edges


def build_html(payload_nodes: List[dict], edges: List[dict], granularity: int = 2) -> str:
    min_x = min((node["x"] for node in payload_nodes), default=0)
    max_x = max((node["x"] for node in payload_nodes), default=0)
    min_y = min((node["y"] for node in payload_nodes), default=0)

    # Shift to positive screen space with extra margins.
    for node in payload_nodes:
        sx, sy = _iso_project(node["x"] - min_x, node["y"] - min_y, node["depth"])
        node["screen_x"] = sx + 700
        node["screen_y"] = sy + 340

    clock_bins = ", ".join(f"{i * granularity:02d}" for i in range(24 // granularity))
    clock_legend = f"Clock sectors ({granularity}-hr bins): {clock_bins}"

    return f"""<!doctype html>
<html lang=\"en\">
<head>
  <meta charset=\"utf-8\" />
  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\" />
  <title>OlmoEarth Information Clock</title>
  <style>
    :root {{
      color-scheme: dark;
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      font-family: Inter, ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Helvetica, Arial, sans-serif;
      background: radial-gradient(circle at 20% 10%, #1b1f31 0%, #0b0f1a 70%);
      color: #e8ebff;
    }}
    .wrap {{
      min-height: 100vh;
      padding: 16px;
    }}
    h1 {{
      margin: 0 0 8px;
      font-size: 28px;
      letter-spacing: 0.01em;
    }}
    p {{
      margin: 0 0 12px;
      color: #b5bfd8;
    }}
    #canvas {{
      position: relative;
      width: 100%;
      height: 80vh;
      border-radius: 16px;
      overflow: hidden;
      border: 1px solid #2a3352;
      background:
        linear-gradient(90deg, transparent 0, transparent 49px, #2e3654 50px),
        linear-gradient(0deg, transparent 0, transparent 49px, #2e3654 50px),
        #11182d;
      background-size: 50px 50px;
    }}
    .clock {{
      position: absolute;
      top: 18px;
      left: 18px;
      padding: 12px 14px;
      border-radius: 10px;
      border: 1px solid #45517a;
      background: rgba(10, 16, 32, 0.75);
      backdrop-filter: blur(3px);
      font-size: 12px;
    }}
    .node {{
      position: absolute;
      border-radius: 10px;
      border: 1px solid;
      transform: translate(-50%, -100%);
      box-shadow: 0 12px 20px rgba(0, 0, 0, 0.55);
      transition: transform 120ms ease;
      cursor: default;
    }}
    .node:hover {{
      z-index: 10;
      transform: translate(-50%, -100%) scale(1.04);
    }}
    .node .top {{
      position: absolute;
      inset: 0;
      border-radius: 10px;
      padding: 6px 8px 5px;
      background: linear-gradient(180deg, rgba(255,255,255,0.16), transparent 45%);
      border-bottom: 1px solid rgba(255,255,255,0.18);
      font-weight: 600;
      white-space: nowrap;
      overflow: hidden;
      text-overflow: ellipsis;
    }}
    .node .meta {{
      position: absolute;
      bottom: 6px;
      left: 8px;
      right: 8px;
      font-size: 10px;
      color: rgba(236, 240, 255, 0.88);
      display: flex;
      justify-content: space-between;
      align-items: flex-end;
    }}
    .node .label {{
      position: absolute;
      inset: auto;
      right: 8px;
      top: 8px;
      font-size: 10px;
      color: rgba(255,255,255,0.85);
    }}
    .edge {{
      position: absolute;
      width: 2px;
      transform-origin: 0 0;
      z-index: 0;
      opacity: 0.6;
      background: linear-gradient(90deg, rgba(130, 145, 210, 0.95), rgba(130,145,210,0.05));
    }}
    .legend {{
      display: grid;
      gap: 6px;
      margin-top: 10px;
      grid-template-columns: repeat(3, minmax(120px, 1fr));
      max-width: 680px;
      font-size: 12px;
      color: #d5ddff;
    }}
    .legend-item {{
      border: 1px solid #45517a;
      border-radius: 8px;
      padding: 6px 8px;
      display: flex;
      align-items: center;
      gap: 8px;
      background: rgba(13, 20, 39, 0.74);
    }}
    .dot {{
      width: 11px;
      height: 11px;
      border-radius: 50%;
      border: 1px solid rgba(255,255,255,.4);
    }}
  </style>
</head>
<body>
  <div class="wrap">
    <h1>OlmoEarth relational structures: isometric information clock</h1>
    <p>
      New clock-aware projection in isometric space. Nodes encode Region → District → Parcel
      structure and are grouped by a 2-hour informational clock sector inferred from event time.
    </p>
    <div id="canvas"></div>
    <div class="legend">
      <div class="legend-item"><span class="dot" style="background:#2ECC71"></span> plus (+1)</div>
      <div class="legend-item"><span class="dot" style="background:#5DADE2"></span> ergodic (0)</div>
      <div class="legend-item"><span class="dot" style="background:#E74C3C"></span> minus (-1)</div>
    </div>
  </div>

<script>
const nodes = {json.dumps(payload_nodes)};
const edges = {json.dumps(edges)};

const canvas = document.getElementById('canvas');
canvas.innerHTML = '<div class="clock">{clock_legend}</div>';

const pos = Object.create(null);
for (const node of nodes) {{
  pos[node.id] = {{ x: node.screen_x, y: node.screen_y }};
}}

for (const e of edges) {{
  const from = pos[e.from];
  const to = pos[e.to];
  if (!from || !to) continue;

  const dx = to.x - from.x;
  const dy = to.y - from.y;
  const length = Math.hypot(dx, dy) || 1;
  const angle = Math.atan2(dy, dx) * 180 / Math.PI;

  const edge = document.createElement('div');
  edge.className = 'edge';
  edge.style.left = `${{from.x}}px`;
  edge.style.top = `${{from.y}}px`;
  edge.style.height = `${{length}}px`;
  edge.style.transform = `rotate(${{angle + 90}}deg)`;
  canvas.appendChild(edge);
}}

for (const node of nodes) {{
  const tile = document.createElement('div');
  tile.className = 'node';
  tile.style.left = `${{node.screen_x}}px`;
  tile.style.top = `${{node.screen_y}}px`;
  tile.style.width = `${{node.grid_x}}px`;
  tile.style.height = `${{node.grid_y}}px`;
  tile.style.borderColor = node.border;
  tile.style.background = `linear-gradient(120deg, ${{node.light}}, ${{node.bg}} 65%)`;

  const top = document.createElement('div');
  top.className = 'top';
  top.textContent = `${{node.label}} #${{node.id}}`;

  const label = document.createElement('div');
  label.className = 'label';
  label.textContent = `${{node.trit_label}}`;

  const meta = document.createElement('div');
  meta.className = 'meta';
  const left = document.createElement('span');
  left.textContent = node.country || node.region || 'global';
  const right = document.createElement('span');
  right.textContent = `clock ${{node.clock_label}}`;
  meta.appendChild(left);
  meta.appendChild(right);

  tile.appendChild(top);
  tile.appendChild(label);
  tile.appendChild(meta);
  canvas.appendChild(tile);
}}

</script>
</body>
</html>"""


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build isometric OlmoEarth info-clock view from GeoWEV structures."
    )
    parser.add_argument(
        "--out",
        default="olmoearth_isometric_clock_view.html",
        help="output HTML file",
    )
    parser.add_argument(
        "--queries",
        nargs="+",
        default=[
            "filecoin_storage_providers",
            "fvm_contract_deployments",
            "bridge_transactions",
            "grant_disbursements",
        ],
        help="Dune query names to simulate",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=12,
        help="number of rows per query",
    )
    parser.add_argument(
        "--granularity",
        type=int,
        default=2,
        choices=[1, 2, 3, 6],
        help="hours per clock sector (1=24 sectors, 2=12, 3=8, 6=4)",
    )
    args = parser.parse_args()

    engine = GeoWEVEngine()
    for query in args.queries:
        engine.extract_from_dune(query, limit=args.limit)
    geoacset = engine.materialize_geoacset()

    events = {e.id: e for e in engine.events}
    nodes_payload, edges_payload = _shape_payload(geoacset.nodes, events, engine, args.granularity)

    html = build_html(nodes_payload, edges_payload, args.granularity)
    out = Path(args.out)
    out.write_text(html, encoding="utf-8")

    status = engine.status()
    status_path = out.with_suffix(".status.json")
    status_payload = {
        "nodes": len(nodes_payload),
        "edges": len(edges_payload),
        "query_count": len(args.queries),
        "status": status,
        "output": str(out),
    }
    status_path.write_text(json.dumps(status_payload, indent=2), encoding="utf-8")

    print(f"✓ isometric clock view written to {out}")
    print(f"✓ status written to {status_path}")


if __name__ == "__main__":
    main()
