# INTERLEAVED: finder-color-walk (4-corpus weave)

This document is a crosswalk between:
1. asi-main doctrine (triadic fanout, GF(3) invariants, dispatch),
2. RelationalThinking book (schemas/instances, Δ/Σ intuition),
3. CatColab (diagrammatic schema/migration/UI),
4. py-acsets (runtime validation + tests-as-proofs).

## Minimal categorical core

### Target ACSet view
We model coloring as an attributed structure on Files:
- objects: File, Fiber, Step, Walk, ColorTrit
- attributes: path(File), trit(ColorTrit)∈{0,1,2}
- morphisms: file_fiber: File→Fiber, step_file: Step→File, step_walk: Step→Walk

### Triadic split = function
file_fiber is a total function into a 3-element object; fibers are its pullback/fibers.

### GF(3) conservation = equation on triplets
For aligned step index i across the three fibers:
t0(i)+t1(i)+t2(i)=0 mod 3.
This is enforced by construction (t2 := -t0-t1).

## Where each corpus contributes
- **asi-main**: triadic routing + conservation as invariant, not runtime convention.
- **RelationalThinking**: schemas as presentations; invariants live at the schema/instance boundary.
- **CatColab**: render/inspect the schema, plus rewrite-based reasoning about equivalences.
- **py-acsets**: property tests: SPI + GF(3) as executable checks.

## Practical interleave
1. Catlab schema (schema.jl) is the single source of truth.
2. Babashka scripts implement deterministic transforms that produce instances.
3. spi_test.py plays the role of a small proof assistant: falsify violations quickly.
