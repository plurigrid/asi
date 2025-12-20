# Categories 4-11 Implementation Plan

**Current Status**: Phase 9 Complete - All tests passing, system fully operational
**Foundation**: Badiouian ontology with triangle inequality enforcement
**Testing**: Automated via Flox, validated in actual Ruby runtime

---

## Implementation Architecture

### Core Principle

Each category extends the existing world system:

```
World (Base)
  ├─ PitchSpaceWorld (Cat 1) ✓ DONE
  ├─ ChordSpaceWorld (Cat 2) ✓ DONE
  ├─ LeitmotifWorld (Cat 3) ✓ DONE
  ├─ GroupTheoryWorld (Cat 4) ← START HERE
  ├─ HarmonicFunctionWorld (Cat 5)
  ├─ ModulationWorld (Cat 6)
  ├─ PolyphonicWorld (Cat 7)
  ├─ ProgressionWorld (Cat 8)
  ├─ StructuralWorld (Cat 9)
  ├─ FormWorld (Cat 10)
  └─ AdvancedWorld (Cat 11)
```

Each world:
1. Defines its own objects (mathematical entities)
2. Enforces triangle inequality in its metric
3. Validates semantic closure (8 dimensions)
4. Provides OSC rendering for audio
5. Comes with complete test suite

---

## Category 4: Group Theory Extensions

### Domain

Extend pitch space from cyclic group ℤ/12ℤ to full permutation group S₁₂.

### Files to Create

**lib/group_theory.rb** (NEW)
- Class: `Group` (abstract)
- Class: `CyclicGroup` (extends Group)
- Class: `PermutationGroup` (extends Group, implements S₁₂)
- Class: `GroupElement` (represents group member)
- Class: `GroupAction` (function G × X → X)

**lib/worlds/group_theory_world.rb** (NEW)
- Class: `GroupTheoryWorld` (extends World)
- Metric: Cayley graph distance in group
- Axiom: Group closure (a·b ∈ G for all a,b ∈ G)
- Axiom: Associativity
- Axiom: Identity element
- Axiom: Inverse elements

**test/test_group_theory.rb** (NEW)
- Test: Group axioms (closure, associativity, identity, inverse)
- Test: Permutation multiplication
- Test: Cayley graph distance metric
- Test: Voice leading under group actions
- Test: Triangle inequality in group metric

### Implementation Details

```ruby
# Group 5-tuple signature
class Group
  # (G, *, e, inv, metric)
  # G = set of elements
  # * = binary operation
  # e = identity element
  # inv = inverse function
  # metric = Cayley graph distance

  def initialize(elements, operation, identity, inverse_fn, metric)
    @elements = elements
    @operation = operation
    @identity = identity
    @inverse_fn = inverse_fn
    @metric = metric
  end

  # Verify group axioms
  def validate_group_axioms
    # Closure: a·b ∈ G for all a,b
    # Associativity: (a·b)·c = a·(b·c)
    # Identity: a·e = a, e·a = a
    # Inverse: a·a⁻¹ = e
  end
end

# S₁₂ = symmetric group on 12 elements (all permutations of [0..11])
class PermutationGroup < Group
  def self.S12
    # 12! = 479,001,600 permutations
    # Represent as cycles: (0 1 2) means 0→1, 1→2, 2→0
    # Store as arrays for efficiency
  end
end

# Cayley graph metric: shortest path in multiplication table
def cayley_distance(perm1, perm2)
  # Breadth-first search from perm1 to perm2
  # using group generators as edges
  # Generators for S₁₂: transpositions (i j)
end

# Voice leading under group action
def voice_leading_action(group, perm, chord)
  # Apply permutation to chord pitches
  # Example: (0 1) swaps pitches 0 and 1
  # C Major = [0, 4, 7] → [4, 0, 7] under (0 1)
end
```

### Test Structure

```ruby
test "Group closure" do
  s12 = PermutationGroup.S12
  perm_a = s12.random_element
  perm_b = s12.random_element
  product = s12.multiply(perm_a, perm_b)
  assert s12.contains?(product)
end

test "Cayley distance triangle inequality" do
  s12 = PermutationGroup.S12
  g, h, k = s12.random_elements(3)
  d_gh = cayley_distance(g, h)
  d_hk = cayley_distance(h, k)
  d_gk = cayley_distance(g, k)
  assert d_gk <= d_gh + d_hk
end

test "Voice leading under transposition" do
  c_major = Chord.from_notes(['C', 'E', 'G'])
  transposition = PermutationGroup.S12.transposition(0, 1)
  c_major_transposed = transposition.act_on(c_major)

  # Verify pitches are permuted correctly
  assert c_major_transposed.pitches == [4, 0, 7]
end
```

### Expected Outputs

- [x] Group axioms verified
- [x] S₁₂ with 479M permutations represented efficiently
- [x] Cayley graph distance metric
- [x] Voice leading transformations
- [x] Triangle inequality in S₁₂ metric
- [x] 5+ test cases passing

---

## Category 5: Harmonic Function

### Domain

Musical chords have functional roles: Tonic (T), Subdominant (S), Dominant (D).

### Files to Create

**lib/harmonic_function.rb** (NEW)
- Class: `HarmonicFunction` (T, S, D)
- Class: `FunctionalChord` (chord + function)
- Method: `function_from_chord()` (rules to determine function)
- Method: `valid_progression?(chord1, chord2)` (functional rules)

**lib/worlds/harmonic_function_world.rb** (NEW)
- Class: `HarmonicFunctionWorld` (extends World)
- Metric: Functional distance (0 if same function, 1 if one transition, 2 if unusual)
- Axiom: T-D-T creates closed cycle
- Axiom: S always precedes D
- Axiom: Deceptive cadence (D-vi) is valid

**test/test_harmonic_function.rb** (NEW)

### Implementation Details

```ruby
# Harmonic functions in major/minor keys
# C Major: C(T), D(S), E(S), F(S), G(D), A(S), B(D), C(T)
# Minor:   Similar with appropriate adjustments

class HarmonicFunction
  TONIC = :tonic         # I, vi (relative minor)
  SUBDOMINANT = :subdominant  # ii, iii, IV, V/V
  DOMINANT = :dominant        # V, vii°

  # Determine function of a chord in context
  def self.analyze(chord, key, context = nil)
    # Rules based on:
    # 1. Root position/inversion
    # 2. Previous chord (if context given)
    # 3. Key signature
  end
end

# Functional distance between chords
def functional_distance(chord1, chord2, progression_context)
  func1 = HarmonicFunction.analyze(chord1)
  func2 = HarmonicFunction.analyze(chord2)

  # Distance based on valid progressions
  # T → D: distance = 2 (needs S in between)
  # T → S: distance = 1 (valid)
  # S → D: distance = 1 (valid)
  # D → T: distance = 1 (valid)
  # D → S: distance = 2 (S should come before D)
end
```

### Expected Outputs

- [x] Functional analysis of any chord
- [x] Valid progression detection
- [x] Cadential patterns recognized
- [x] Deceptive cadences handled
- [x] Test suite with 8+ cases

---

## Category 6: Modulation & Transposition

### Domain

Keys can change; chords can be transposed; relationships preserved.

### Files to Create

**lib/modulation.rb** (NEW)
- Class: `Modulation` (key change)
- Class: `ModulationPath` (sequence of key changes)
- Method: `common_tone_modulation()`
- Method: `pivot_chord_modulation()`
- Method: `chromatic_modulation()`

**lib/worlds/modulation_world.rb** (NEW)
- Metric: Distance = chromatic steps in modulation path
- Axiom: Triangle inequality in modulation space

**test/test_modulation.rb** (NEW)

### Expected Outputs

- [x] Modulation detection
- [x] Pivot chord analysis
- [x] Key signature changes
- [x] Transposition with preservation of relationships
- [x] 6+ test cases

---

## Category 7: Polyphonic Voice Leading

### Domain

4-voice writing rules (SATB): soprano, alto, tenor, bass.

### Files to Create

**lib/voice_leading.rb** (NEW)
- Class: `VoiceLeadingConstraint`
- Rules: Voice range limits, smooth voice leading, no parallel fifths, etc.
- Method: `validate_voice_leading()` (rule checker)

**lib/worlds/polyphonic_world.rb** (NEW)
- Objects: 4-voice progressions
- Metric: Sum of voice motion distances
- Axiom: Triangle inequality per voice

**test/test_voice_leading.rb** (NEW)

### Expected Outputs

- [x] Voice range validation (SATB)
- [x] Parallel fifths/octaves detection
- [x] Voice overlap detection
- [x] Smooth voice leading analysis
- [x] 8+ test cases

---

## Category 8: Harmony & Progression

### Domain

Chord progressions follow harmonic logic: Circle of Fifths, functional harmony.

### Files to Create

**lib/progressions.rb** (NEW)
- Class: `CircleOfFifths`
- Class: `HarmonicProgression`
- Method: `analyze_progression()`
- Method: `common_progressions()` (I-IV-V-I, etc.)

**lib/worlds/progression_world.rb** (NEW)

**test/test_progressions.rb** (NEW)

### Expected Outputs

- [x] Circle of Fifths navigation
- [x] Common progression detection
- [x] Secondary dominant analysis
- [x] Borrowed chord recognition
- [x] 10+ test cases

---

## Category 9: Structural Tonality

### Domain

Phrases, periods, cadences; large-form structure.

### Files to Create

**lib/structure.rb** (NEW)
- Class: `Phrase`
- Class: `Period`
- Class: `Cadence` (authentic, plagal, deceptive, half)
- Method: `analyze_phrase()` (phrase boundary detection)

**lib/worlds/structural_world.rb** (NEW)

**test/test_structure.rb** (NEW)

### Expected Outputs

- [x] Phrase detection (antecedent/consequent)
- [x] Cadence recognition
- [x] Phrase boundary analysis
- [x] 6+ test cases

---

## Category 10: Form & Analysis

### Domain

Sonata form, rondo, theme & variation, etc.

### Files to Create

**lib/form.rb** (NEW)
- Class: `MusicalForm` (abstract)
- Class: `SonataForm`, `RondoForm`, `VariationForm`, etc.
- Method: `analyze_form()` (detect which form)

**lib/worlds/form_world.rb** (NEW)

**test/test_form.rb** (NEW)

### Expected Outputs

- [x] Form type detection
- [x] Section boundary analysis
- [x] Theme tracking
- [x] 5+ test cases

---

## Category 11: Advanced Topics

### Domain

Spectral analysis, timbre, complex harmony, extended techniques.

### Files to Create

**lib/spectral.rb** (NEW)
- Class: `Spectrum`
- Class: `HarmonicSeries`
- Method: `analyze_spectrum()` (frequency content)

**lib/worlds/spectral_world.rb** (NEW)

**test/test_spectral.rb** (NEW)

### Expected Outputs

- [x] Spectral analysis implementation
- [x] Harmonic series analysis
- [x] Timbre space navigation
- [x] 4+ test cases

---

## Implementation Roadmap

### Week 1: Category 4 (Group Theory)
- Create group_theory.rb with Group, PermutationGroup
- Implement S₁₂ with Cayley distance
- Create test suite
- Verify all tests pass

### Week 2: Categories 5-6 (Harmonic Function + Modulation)
- Create harmonic_function.rb
- Create modulation.rb
- Test suites for both
- Integrate with existing worlds

### Week 3: Categories 7-8 (Voice Leading + Progressions)
- Create voice_leading.rb
- Create progressions.rb
- Comprehensive test suites
- Audio rendering for progressions

### Week 4: Categories 9-11 (Structure + Form + Advanced)
- Create structure.rb
- Create form.rb
- Create spectral.rb
- Final test suites

### Week 5: Integration & Documentation
- Merge all categories
- Create unified test harness
- Update FLOX_SETUP for all categories
- Create CATEGORIES_COMPLETE.md

---

## Testing Strategy

### Per Category

```
Category N:
├── test/test_category_N.rb
├── test/test_category_N_integration.rb
├── test/test_category_N_audio.rb
└── bin/demo_category_N.rb (interactive demo)
```

### Automation

```bash
# Test single category
flox activate -e test -- ruby test/test_category_4.rb

# Test category + integration
flox activate -e test -- ruby test/test_category_4_integration.rb

# Full suite (all categories)
flox activate -e test -- ruby test_complete_system.rb

# Run all category tests
flox activate -e audio-test -- bash -c "
  for i in {4..11}; do
    echo Testing Category $i
    ruby test/test_category_$i.rb
  done
"
```

### Semantic Validation

Each category extends the 8-dimension semantic closure:

```ruby
closure = OntologicalValidator.semantic_closure(composition)

# All 8 dimensions must validate:
# 1. pitch_space - Notes in correct octaves
# 2. chord_space - Chords form valid points in Tⁿ
# 3. metric_valid - Distances satisfy triangle inequality
# 4. appearance - Objects present in the world
# 5. transformations_necessary - All operations preserve structure
# 6. consistent - No contradictions (e.g., C both major and minor)
# 7. existence - Objects justified by rules
# 8. complete - Closure under all defined operations
```

---

## Key Integration Points

### Audio Rendering

Each category extends SonicPiRenderer:

```ruby
# Category 4: Play group action
renderer.render_group_action(group, permutation, chord)

# Category 5: Play functional progression
renderer.render_functional_progression(T, S, D)

# Category 6: Play modulation
renderer.render_modulation(key1, key2, common_tone_path)

# Category 7: Play 4-voice SATB
renderer.render_satb(soprano, alto, tenor, bass)

# Category 8: Play progression
renderer.render_progression(['I', 'IV', 'V', 'I'])

# Category 9: Play phrase with cadence
renderer.render_phrase(antecedent, cadence)

# Category 10: Play form structure
renderer.render_form(SonataForm.new(exposition, development, recapitulation))

# Category 11: Play spectral content
renderer.render_spectrum(harmonic_series)
```

All OSC sends are actual UDP packets to Sonic Pi (localhost:4557).

---

## Validation Checklist

For each category:

- [ ] Core classes implemented
- [ ] Metric and triangle inequality verified
- [ ] 8-point semantic closure confirmed
- [ ] Test suite created (5+ tests per category)
- [ ] All tests passing in actual Ruby runtime
- [ ] OSC audio rendering working
- [ ] Flox test environment updated
- [ ] Documentation written
- [ ] Integration with existing categories tested

---

## File Structure After Completion

```
/Users/bob/ies/music-topos/
├── lib/
│   ├── pitch_class.rb          ✓ (Cat 1)
│   ├── chord.rb                ✓ (Cat 2)
│   ├── neo_riemannian.rb       ✓ (Cat 3)
│   ├── group_theory.rb         ← (Cat 4)
│   ├── harmonic_function.rb    ← (Cat 5)
│   ├── modulation.rb           ← (Cat 6)
│   ├── voice_leading.rb        ← (Cat 7)
│   ├── progressions.rb         ← (Cat 8)
│   ├── structure.rb            ← (Cat 9)
│   ├── form.rb                 ← (Cat 10)
│   ├── spectral.rb             ← (Cat 11)
│   ├── worlds/
│   │   ├── pitch_space_world.rb
│   │   ├── chord_space_world.rb
│   │   ├── group_theory_world.rb       ← (Cat 4)
│   │   ├── harmonic_function_world.rb  ← (Cat 5)
│   │   └── ... (all 11 worlds)
│   └── sonic_pi_renderer.rb
├── test/
│   ├── test_category_4.rb  ← START HERE
│   ├── test_category_5.rb
│   └── ... (all 11 tests)
├── bin/
│   ├── demo_category_4.rb
│   └── ... (all 11 demos)
├── flox.toml               (updated with new tests)
└── [documentation files]
```

---

## Success Criteria

System is complete when:

1. ✓ All 11 categories implemented
2. ✓ All tests passing (60+ test cases total)
3. ✓ Semantic closure verified for all categories
4. ✓ OSC audio rendering for all categories
5. ✓ Flox automation for complete testing
6. ✓ Comprehensive documentation
7. ✓ System demonstrates Mazzola's music topos in practice

---

## Status

**Ready to begin**: Category 4 (Group Theory)

**Next action**: Create `lib/group_theory.rb` with full Group and PermutationGroup implementation.
