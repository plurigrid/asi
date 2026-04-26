---
name: hermes-mem-as-dataspace
description: Collapse Hermes' 8 memory backends (honcho/mem0/supermemory/hindsight/retaindb/openviking/holographic/byterover) into one Syndicate dataspace + Mandy bcom+gset persistent collection. Memory becomes published facts subscribers react to, not a polled provider plugin. Goblins vat-snapshot replaces 8 storage adapters.
type: bridge
parent: hermes-goblins-bridge
row: 9
proto: D
polarity: 0
status: stub
---

# hermes-mem-as-dataspace

Phase 2 (state). The witness-row archetype: shared knowledge, no RPC needed.

## Hermes signature

`/Users/bob/i/hermes-agent/agent/memory_manager.py:82`

```python
class MemoryManager:
    """Plugin-based memory store with provider failover."""
    providers: Dict[str, MemoryProvider]   # 8 backends
    async def remember(self, fact, **kwargs): ...
    async def recall(self, query, **kwargs): ...
    async def forget(self, fact_id): ...
```

`plugins/memory/{honcho,mem0,supermemory,hindsight,retaindb,openviking,holographic,byterover}/` — each with own `__init__.py` + `plugin.yaml`. Each provider re-implements: store, semantic search, eviction, multi-session scoping, schema versioning.

Authority pattern: **provider plugins behind a router**. Each backend is its own service (most are hosted SaaS). Authority leaks: each backend holds its own auth token; memory facts cross 8 different vendors' servers.

## Goblins signature

One `^memory-collection` actor backed by Mandy Pattern D (`bcom`+`gset`) + Syndicate dataspace for the *facts-as-published* surface. Vat-snapshot/restore replaces every backend's persistence layer.

```scheme
;; Mandy Pattern D — bcom+gset persistent collection
(define (^memory-collection bcom)
  (define facts (gset))
  (define ds (spawn ^dataspace))
  (methods
    ((remember fact #:allow-other-keys . opts)
     (define fact-id (mint-fact-id))
     (assert! ds `(memory ,fact-id ,fact ,@opts))
     (gset-add! facts (cons fact-id fact))
     fact-id)
    ((recall query)
     (filter (lambda (f) (matches? f query)) (gset->list facts)))
    ((forget fact-id)
     (retract! ds `(memory ,fact-id . _))
     (gset-remove-by! facts (lambda (f) (eq? (car f) fact-id))))
    ((subscribe pattern observer)
     (observe ds pattern observer))))   ; ← Syndicate dual: react to memory churn
```

Persistence = `vat-snapshot` to disk; restore on cold start. No 8 vendor accounts; one local vat with optional remote replicas via OCapN.

## Translation table

| Hermes call | Goblins message | Notes |
|---|---|---|
| `mm.remember(fact, tags=…)` | `(<- coll 'remember fact #:tags …)` | `#:allow-other-keys` keeps loose-dict ergonomics |
| `mm.recall(query, k=10)` | `(<- coll 'recall query)` | local first; remote replicas via subscribe |
| `mm.forget(id)` | `(<- coll 'forget id)` + retract! | retraction propagates to subscribers |
| provider failover | replicas via OCapN — subscribe to peer dataspaces | not 8 adapters, N peers |
| schema migration | snapshot/restore round-trip with transformer | one schema, not 8 |
| semantic search | embedded vector index in vat (or HNSW cap) | one place to optimize |

## Failure modes (closed by this bridge)

- **Memory facts spread across 8 vendor backends with 8 auth tokens** — single local vat, snapshotted; remote replication is opt-in via OCapN, not "where the SaaS lives".
- **Backend-specific schema drift** — one schema, one migration path.
- **Polling-based recall** — subscribe to dataspace pattern; observers wake on relevant facts (Syndicate's whole point).
- **Forget that doesn't actually forget on the SaaS** — retraction is local + crypto-deniable in the snapshot; no third party to trust.
- **Per-provider rate limits** — local vat, no external API quotas.

## Failure modes (introduced; must mitigate)

- **Vat snapshot corruption = total memory loss** — keep N rolling snapshots; verify with hash-chain on restore (Mandy pattern).
- **Single-vat scaling ceiling** — if memory grows beyond one vat's working set, shard via OCapN: each shard = its own `^memory-collection`, observer-pattern across shards.

## Test vector

```python
mm = memory_collection()
fid = mm.remember({'note': 'user prefers terse'}, tags=['preference'])
assert fid in [f for f in mm.recall({'tags': ['preference']})]

# Subscribe — Syndicate-style
seen = []
mm.subscribe('(memory ?id ? #:tags (... preference ...))',
             lambda f: seen.append(f))
mm.remember({'note': 'no emoji'}, tags=['preference'])
assert len(seen) == 1   # observer woke on relevant fact

mm.forget(fid)
assert fid not in [f.id for f in mm.recall(...)]

# Cross-restart:
snap = vat_snapshot(mm)
mm2 = vat_restore(snap)
assert mm.recall(q) == mm2.recall(q)
```

## Capability diff

| Property | Hermes (status quo) | Goblins (this bridge) |
|---|---|---|
| Backends | 8 plugins, 8 auth surfaces | 1 vat, optional N OCapN peers |
| Persistence | per-backend (SaaS or local) | vat-snapshot |
| Recall model | poll | poll + Syndicate subscribe |
| Schema | 8 drift paths | 1, snapshot-versioned |
| Forget guarantee | depends on vendor | local cryptographic retraction |
| Failure mode | vendor outage = memory loss | local always available |

## Test-harness location

`~/i/goblins-adapter/tests/mem-dataspace-bisim.scm` (todo). Bisim probe must include subscribe-side semantics — Hermes can't subscribe (no dataspace), so the comparison is asymmetric: cap version is strictly more capable, and the equivalence is "Hermes recall ⊆ Goblins recall + subscribe".

## Cross-impl notes

This is the prototypical **D row**. Troupe-Haskell's NLnet bundle includes Syndicate explicitly — once landed, this row gets a typed bisim peer (memory `troupe-syndicate-haskell.md`).

## Status: stub

Phase 2 priority. Eliminates the largest bespoke-plugin surface in Hermes (8 backends → 1 vat). Pairs with `hermes-session-as-snapshot` (row 10) — both use vat-snapshot; same persistence story.
