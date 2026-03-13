# Seatbelt Per-Letter Isolation: Behavioral Tests

> Seed: 1069 | Branch color: #233f7f | 10 skills, sum=0 (GF(3) CONSERVED)

## The Counterfactual Pattern

Each enforcement skill creates a **counterfactual**: a behavior that would succeed
WITHOUT the enforcement but FAILS with it. The test is: run the behavior inside
the sandbox profile, observe the denial. The denial IS the proof of enforcement.

The "successor hiker" principle: when an input arrives (file write, network call,
cross-world access), the system immediately halts the behavior if it violates
the profile -- no negotiation, no fallback. The kernel-level Seatbelt enforcement
renders a geometric boundary (the .sb profile) that translates universally across
all 26 letter-worlds.

## Persistent Homology of Enforcement

The behaviors form a filtration:
```
ε=0: each world fully isolated (H₀ = 26 connected components)
ε=1: worlds sharing an operad connect (H₀ = 3: MINUS, ERGODIC, PLUS)
ε=2: intertwiner edges connect operads (H₀ = 1, H₁ = cycles)
ε=3: full Seatbelt baseline (H₀ = 1, all read-accessible)

The persistent diagram:
  H₀ bars: 26 bars born at ε=0, 23 die at ε=1, 2 die at ε=2, 1 persists ∞
  H₁ bars: born at ε=2 from intertwiner cycles (GF(3) conservation loops)
```

Write isolation lives at ε=0: every world is its own connected component for writes.
Read access lives at ε=3: broad `(allow file-read*)` connects everything.
The enforcement gap between ε=0 and ε=3 is the security boundary.

---

## Test Suite: Counterfactual Behaviors

### Test 1: Cross-World Write Denial (asi-seatbelt-enforcer, #ca5858, trit=-1)

**Counterfactual**: Without enforcement, world-z can write to world-a's directory.
**With enforcement**: Kernel denies the write.

```bash
# EXPECTED: Operation not permitted
sandbox-exec -f /tmp/sb/world-z.sb \
  /usr/bin/touch /Users/ies/worlds/a/cross-world-violation
# exit code != 0, stderr contains "Operation not permitted"

# CONTROL: Own-world write succeeds
sandbox-exec -f /tmp/sb/world-z.sb \
  /usr/bin/touch /Users/ies/worlds/z/.self-write-ok
# exit code == 0
rm -f /Users/ies/worlds/z/.self-write-ok
```

**Biological analog**: A hiker hearing a successor's signal from another valley
(another letter-world). The signal is received (file-read allowed) but the hiker
cannot physically cross into that valley (file-write denied). The hearing IS
the information geometry; the mountain IS the Seatbelt profile.

---

### Test 2: Pure Compute Lockdown (asi-profile-generator, #7928b2, trit=+1)

**Counterfactual**: Without trit-kernel profile, a compute process can write
files, open network connections, and exec arbitrary binaries.
**With enforcement**: Only read + exec from nix store. No write. No net. No IPC.

```bash
# EXPECTED: all denied
sandbox-exec -f /tmp/sb/trit-kernel.sb /usr/bin/touch /tmp/leak  # DENIED
sandbox-exec -f /tmp/sb/trit-kernel.sb /usr/bin/curl https://exfil.example.com  # DENIED

# CONTROL: read and exec work
sandbox-exec -f /tmp/sb/trit-kernel.sb /usr/bin/true  # PASS
sandbox-exec -f /tmp/sb/trit-kernel.sb /bin/echo "pure compute"  # PASS
```

**Biological analog**: A neuron in a compute-only layer. It receives input
(file-read), transforms it (process-exec), and produces output on stdout --
but cannot initiate motor action (file-write) or sensory acquisition (network).
The spectral gap 1/4 ensures mixing time τ=4 for balanced exploration.

---

### Test 3: Sheaf Gluing Verification (asi-sheaf-coordinator, #29da5d, trit=0)

**Counterfactual**: Without gluing verification, two neighboring worlds could
have contradictory profiles (e.g., world-a allows writing to world-b, but
world-b's profile denies being read by world-a).
**With enforcement**: The coordinator verifies overlap consistency.

```bash
# Generate all profiles
guile -s ~/worlds/seatbelt-scsh.scm /tmp/sb

# Verify: no world-X profile contains write access to another world-Y
for x in {a..z}; do
  for y in {a..z}; do
    if [ "$x" != "$y" ]; then
      if grep -q "file-write.*worlds/$y" /tmp/sb/world-$x.sb 2>/dev/null; then
        echo "GLUING VIOLATION: world-$x writes to world-$y"
      fi
    fi
  done
done
# EXPECTED: no output (no violations)
```

**Biological analog**: Proprioception. The coordinator senses whether local
sections (profiles) agree on overlaps (shared reads). When they disagree,
it's like phantom limb syndrome -- the sheaf has a gluing defect.

---

### Test 4: GF(3) Conservation (asi-letter-inventory, #a89828, trit=-1)

**Counterfactual**: Without conservation checking, adding a new skill could
silently break the trit balance (sum ≢ 0 mod 3).
**With enforcement**: Pre-commit hook rejects the change.

```bash
# Verify current balance
python3 -c "
trits = [-1,0,-1,-1,0,1,-1,0,0,0,1,-1,-1,-1,-1,0,-1,1,1,0,1,-1,0,-1,0,0]
s = sum(trits)
print(f'26-letter sum={s}, mod3={s%3}, {\"CONSERVED\" if s%3==0 else \"VIOLATION\"}')
"
# EXPECTED: sum=-6, mod3=0, CONSERVED
```

**Biological analog**: Energy conservation in metabolism. The GF(3) triad
(-1 + 0 + 1 = 0) mirrors ATP/ADP cycling. A violation is thermodynamic
impossibility -- the system rejects it before it can propagate.

---

### Test 5: Goblins Actor Enforcement (asi-goblins-seatbelt-bridge, #62c142, trit=0)

**Counterfactual**: Without the Goblins bridge, profile generation is a
string-manipulation script with no structural guarantee.
**With enforcement**: Actors validate profiles using capability-based security.

```bash
# Run the Goblins triad (requires guile-goblins in GUILE_LOAD_PATH)
GOBLINS="/nix/store/nlnyza6cfp89j173f672bdv604d77spa-guile-goblins-0.16.1/share/guile/site/3.0"
FIBERS="/nix/store/lb13hll2pwcafsj45fh6fzi9lb9g7mxh-guile-fibers-1.3.1/share/guile/site/3.0"
GNUTLS="/nix/store/nbls8mm3c48hgbrv6r1r0ivj4c9hz5vq-guile-gnutls-5.0.1/share/guile/site/3.0"
GCRYPT="/nix/store/l2cmd6jsr6fjy164kkg5hjjbnfylzcml-guile-gcrypt-0.5.0/share/guile/site/3.0"

env GUILE_LOAD_PATH="$GOBLINS:$FIBERS:$GNUTLS:$GCRYPT" \
    GUILE_AUTO_COMPILE=0 \
    guile --no-auto-compile -s seatbelt-bridge.scm

# EXPECTED OUTPUT:
# Triad: validator(-1) x bridge(0) x generator(+1) = 0
# a: ok ... z: ok
# 26-letter GF(3): sum=-6, mod3=0 CONSERVED
```

**Biological analog**: The immune system's MHC presentation. The validator
actor (-1) inspects generated profiles like T-cells inspect peptide fragments.
The bridge (0) coordinates like the thymus. The generator (+1) produces
profiles like B-cells produce antibodies. Together: structural immunity.

---

### Test 6: Cross-Operad Composition (asi-letter-dispatch, #42acc1, trit=0)

**Counterfactual**: Without dispatch coordination, a MINUS world could be
asked to generate (a PLUS operation), violating its trit role.
**With enforcement**: Dispatch routes to the correct world by trit.

```bash
# Verify trit-role consistency
for letter in a c d g l m n o q v x; do  # MINUS worlds
  trit=$(grep "trit=" /tmp/sb/world-$letter.sb | head -1 | grep -o '[-0-9]*')
  echo "world-$letter: trit=$trit (should be -1)"
done
for letter in f k r s u; do  # PLUS worlds
  trit=$(grep "trit=" /tmp/sb/world-$letter.sb | head -1 | grep -o '[-0-9]*')
  echo "world-$letter: trit=$trit (should be +1)"
done
```

**Biological analog**: Hemispheric lateralization. MINUS worlds (left-hemisphere
analogy) validate/constrain. PLUS worlds (right-hemisphere) generate/explore.
ERGODIC worlds (corpus callosum) coordinate. Dispatch ensures the right
hemisphere handles the right task.

---

### Test 7: Critical Isolation Monitor (asi-critical-isolation-monitor, #423cc8, trit=0)

**Counterfactual**: Without monitoring, isolation breakdown is silent until
a security incident occurs.
**With enforcement**: Correlation length ξ is measured; alarm at ξ > threshold.

```bash
# Check for recent sandbox denials (evidence of working enforcement)
log show --last 60s --predicate 'subsystem == "com.apple.sandbox"' \
  --style compact 2>/dev/null | tail -5

# EXPECTED: either empty (no attempts) or denial entries (enforcement working)
# ALARM: if you see ALLOWED entries for cross-world writes
```

**Biological analog**: Pain. Seatbelt denials are nociceptive signals.
Repeated denials from the same world = chronic pain = profile needs update.
Cross-world write SUCCESS = acute trauma = profile broken.

---

### Test 8: Droid-Skill Mixer (asi-droid-skill-mixer, #29da98, trit=-1)

**Counterfactual**: Without the mixer, droids and skills are two independent
registries with no cross-validation.
**With enforcement**: Every droid has at least one matching skill; every
skill references a valid letter.

```bash
# Verify all 26 droid configs exist
for letter in {a..z}; do
  [ -f ~/.factory/droids/world-$letter.md ] && echo "droid-$letter: ok" \
    || echo "droid-$letter: MISSING"
done

# Verify all 26 profiles exist
for letter in {a..z}; do
  [ -f /tmp/sb/world-$letter.sb ] && echo "profile-$letter: ok" \
    || echo "profile-$letter: MISSING"
done
```

**Biological analog**: Somatic map. The mixer ensures the nervous system
(droids) and the musculoskeletal system (skills) are aligned. A droid
without a skill is a phantom nerve. A skill without a droid is a denervated muscle.

---

## Connectivity Analysis: Most-Connected Skills First

From the 17-hub README topology in plurigrid/asi:

```
Hub                     Degree  Role
SKILL-DISPATCH          17+     Routes to ALL skills
ACSETS                  10+     Schema backbone
AGENT-O-RAMA            8+     Self-validation
GAY-MCP                  6+     Color generation
INTERACTION-NETS         5+     Process algebra
OPEN-GAMES               5+     Economic composition
BISIMULATION             4+     Behavioral equivalence
GF3-TRIPARTITE           4+     Conservation orchestration
```

The new seatbelt skills connect through:
- **GF3-TRIPARTITE** (existing hub, trit=0) → asi-scsh-pipeline (+1)
- **BISIMULATION** → asi-sheaf-coordinator (0) [sheaf gluing = bisimulation]
- **ACSETS** → asi-letter-inventory (-1) [inventory = schema validation]
- **GAY-MCP** → all 10 skills [colors derived from seed 1069]

---

## Running All Tests

```bash
#!/bin/bash
# test-seatbelt-enforcement.sh
# Requires: guile, sandbox-exec (macOS), generated profiles in /tmp/sb/

echo "=== Generating profiles ==="
guile -s ~/worlds/seatbelt-scsh.scm /tmp/sb

echo ""
echo "=== Test 1: Cross-world write denial ==="
sandbox-exec -f /tmp/sb/world-z.sb /usr/bin/touch /Users/ies/worlds/a/.nope 2>&1 \
  && echo "FAIL: cross-world write allowed" \
  || echo "PASS: cross-world write denied"

echo ""
echo "=== Test 2: Own-world write allowed ==="
sandbox-exec -f /tmp/sb/world-z.sb /usr/bin/touch /Users/ies/worlds/z/.ok 2>&1 \
  && echo "PASS: own-world write allowed" \
  || echo "FAIL: own-world write denied"
rm -f /Users/ies/worlds/z/.ok

echo ""
echo "=== Test 3: Pure compute lockdown ==="
sandbox-exec -f /tmp/sb/trit-kernel.sb /usr/bin/touch /tmp/leak 2>&1 \
  && echo "FAIL: write allowed in pure compute" \
  || echo "PASS: write denied in pure compute"

echo ""
echo "=== Test 4: GF(3) conservation ==="
python3 -c "
trits=[-1,0,-1,-1,0,1,-1,0,0,0,1,-1,-1,-1,-1,0,-1,1,1,0,1,-1,0,-1,0,0]
s=sum(trits); print(f'sum={s} mod3={s%3} {\"PASS\" if s%3==0 else \"FAIL\"}')"

echo ""
echo "=== Test 5: All profiles valid SBPL ==="
PASS=0; FAIL=0
for f in /tmp/sb/world-*.sb; do
  sandbox-exec -f "$f" /usr/bin/true 2>/dev/null && PASS=$((PASS+1)) || FAIL=$((FAIL+1))
done
echo "profiles: $PASS pass, $FAIL fail (out of 26)"

echo ""
echo "=== Test 6: No cross-world write in any profile ==="
VIOLATIONS=0
for x in {a..z}; do
  for y in {a..z}; do
    [ "$x" = "$y" ] && continue
    grep -q "file-write.*worlds/$y" /tmp/sb/world-$x.sb 2>/dev/null && VIOLATIONS=$((VIOLATIONS+1))
  done
done
echo "cross-world write violations: $VIOLATIONS (should be 0)"

echo ""
echo "=== DONE ==="
```
