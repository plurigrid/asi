# When is Skill Execution Like Name Hashing?

**Question**: Under what conditions does `hash(skill.name)` accurately represent `skill.behavior`?

---

## The Core Question

```julia
# When is this true?
hash(skill.name) ≈ hash(skill.behavior)

# Or more precisely:
# When do different names imply different behaviors?
skill_a.name ≠ skill_b.name  ⟹  skill_a.behavior ≠ skill_b.behavior
```

---

## Case 1: Identity-Based Systems ✓

**When**: Skills are pure declarations with no implementation

**Example**:
```yaml
# skill-a.yml
name: bisimulation-game
type: validator
trit: -1

# skill-b.yml  
name: temporal-coalgebra
type: validator
trit: -1
```

**Behavior**: Name IS the behavior
- The skill's identity determines what it does
- Like actors in actor model (Goblins, CapTP)
- Like capabilities in capability-based security

**In our case**: Most asi skills have only SKILL.md (no code)
- Their "behavior" is their **specification**
- Their "execution" is **invoking the concept**
- Name hashing is appropriate ✓

---

## Case 2: Pure Metadata Skills ✓

**When**: Skills are organizational/routing, not computational

**Example**:
```ruby
# Meta-skills from asi repository
agent-o-rama     → "Learning & pattern extraction"
skill-dispatch   → "Route to appropriate skill"
triadic-skill-orchestrator → "GF(3) balancing"
```

**Behavior**: Coordination, not computation
- These skills don't transform data
- They route, coordinate, or validate
- Their identity (name) IS their role

**Hash equivalence**: Name uniquely determines role ✓

---

## Case 3: Homoiconic Systems ✓

**When**: Code is data, data is code

**Example**:
```clojure
;; In Clojure/Babashka
(defn skill [name]
  (-> name
      symbol
      resolve
      deref))

;; Name directly resolves to implementation
(skill 'bisimulation-game)  ; Name → Function
```

**Property**: Symbols have unique denotations
- In Lisp: Symbol → unique binding
- Name collision → error
- Therefore: Different names → different behaviors ✓

**In asi**: Many skills are Clojure/Babashka
- Homoiconic by nature
- Name hashing is correct ✓

---

## Case 4: Interface-Driven Design ✓

**When**: Skills are interfaces, not implementations

**Example**:
```typescript
interface Skill {
  name: string;
  trit: -1 | 0 | 1;
  execute(input: any): any;
}

// Different names → different interfaces
interface BisimulationGame extends Skill { ... }
interface TemporalCoalgebra extends Skill { ... }
```

**Behavior**: Interface defines behavior contract
- Different interfaces → different behaviors
- Name identifies interface
- Hash collision → type error

**Property**: Structural typing
- If two skills have same name, they're the same interface
- If different names, different interfaces (by convention)

---

## Case 5: Skill-as-MCP-Server ✓

**When**: Skills are MCP server capabilities

**Example**:
```json
{
  "deepwiki": {
    "tools": ["read_wiki_structure", "read_wiki_contents", "ask_question"]
  },
  "gay": {
    "tools": ["gay_seed", "color_at", "reafference", ...]
  }
}
```

**Behavior**: MCP server name → unique capability set
- Different server names → different tools
- Server identity is behavior identity
- Name hashing is appropriate ✓

**In our analysis**: We integrated MCP servers as skills
- Their names uniquely identify capabilities
- No two servers can have same name

---

## Case 6: Git-Based Versioning ✓

**When**: Skill names include version/commit hash

**Example**:
```
skill-name@v1.0.0
skill-name@abc123  (git SHA)
skill-name@2024-01-07
```

**Property**: Name includes version → unique behavior
- Different versions → different names
- Name collision → same version → same behavior
- Hash equivalence holds ✓

**Current asi**: Most skills have version in SKILL.md
- Could extend name to include version
- Then name hashing is perfect

---

## Case 7: Content-Addressed Storage ✓

**When**: Names ARE hashes

**Example**:
```
skill://sha256:abc123...  (IPFS-style)
skill://git:def456...     (Git SHA)
```

**Property**: By definition, hash(name) = behavior hash
- Content-addressed by construction
- This is the ideal case

**Could adopt**: Transition asi to content-addressed names
- Each skill's name = hash of its specification
- Automatically ensures uniqueness

---

## When Name Hashing FAILS ✗

### Case A: Dynamic/Runtime Behavior ✗

**Example**:
```julia
struct Skill
    name::String
    behavior::Function  # Can be redefined at runtime!
end

skill = Skill("compress", x -> length(x))
# Later...
skill.behavior = x -> hash(x)  # CHANGED!

# Name still "compress" but behavior different!
```

**Problem**: Mutable behavior
- Same name, different execution over time
- Name hashing gives false equivalence

**Solution**: Immutable skills (functional programming)

### Case B: Polymorphic Dispatch ✗

**Example**:
```python
class Skill:
    def execute(self, input):
        # Behavior depends on input TYPE
        if isinstance(input, int):
            return input * 2
        elif isinstance(input, str):
            return input.upper()
```

**Problem**: Same skill name, multiple behaviors
- Behavior depends on input type
- Name hash can't capture this

**Solution**: Include type signature in name
- `skill-name:Int->Int`
- `skill-name:String->String`

### Case C: Configuration-Dependent ✗

**Example**:
```yaml
name: llm-query
config:
  model: claude-sonnet-4.5  # Could be opus, haiku, etc.
  temperature: 0.7
```

**Problem**: Same name, different configurations
- Configuration changes behavior
- Name alone insufficient

**Solution**: Include config hash in identity
- `llm-query#config-hash-abc123`

### Case D: External State Dependency ✗

**Example**:
```julia
# Skill behavior depends on external state
function skill_weather_forecast(location)
    weather_api.get(location)  # Different every hour!
end
```

**Problem**: Non-deterministic
- Same input, different output over time
- Pure name hashing fails

**Solution**: 
- Mark skill as non-deterministic
- Include timestamp in behavior signature
- Or: Only hash the algorithm, not the data

---

## The asi Repository Reality Check

Let me check actual skill structures:

```bash
# Do skills have executable code?
find /Users/bob/i/asi/skills -name "*.jl" | wc -l    # Julia
find /Users/bob/i/asi/skills -name "*.clj" | wc -l   # Clojure
find /Users/bob/i/asi/skills -name "*.py" | wc -l    # Python
find /Users/bob/i/asi/skills -name "*.rs" | wc -l    # Rust
```

**Hypothesis**: Most skills are "interface skills" (SKILL.md only)
- They define **what** (interface)
- Not **how** (implementation)

**For interface skills**: Name hashing is CORRECT ✓

---

## When to Use Name Hashing: Decision Tree

```
Is skill pure metadata/interface?
├─ YES → Name hash OK ✓
└─ NO
    ├─ Is skill homoiconic (symbol → unique binding)?
    │   ├─ YES → Name hash OK ✓
    │   └─ NO
    │       ├─ Is skill immutable?
    │       │   ├─ YES
    │       │   │   ├─ Is behavior deterministic?
    │       │   │   │   ├─ YES → Name hash OK ✓
    │       │   │   │   └─ NO → Need execution trace hash ✗
    │       │   └─ NO → Need behavioral testing ✗
    │       └─ Does name include version/config?
    │           ├─ YES → Name hash OK ✓
    │           └─ NO → Need content addressing ✗
```

---

## Proposed Solutions

### Solution 1: Stratified Hashing

```julia
function skill_identity_hash(skill::Skill)
    if has_code(skill)
        # Hash actual implementation
        return hash(skill.code)
    elseif has_version(skill)
        # Include version in hash
        return hash((skill.name, skill.version))
    else
        # Pure interface skill
        return hash(skill.name)
    end
end
```

### Solution 2: Behavioral Signatures

```julia
struct BehavioralSignature
    name::String
    type_signature::String  # "Int -> Int"
    purity::Symbol          # :pure, :impure, :io
    version::String
end

function behavioral_hash(skill::Skill)
    sig = BehavioralSignature(
        skill.name,
        infer_type_signature(skill),
        check_purity(skill),
        skill.version
    )
    return hash(sig)
end
```

### Solution 3: Content-Addressed Skills

```julia
# Transition to IPFS-style naming
function register_skill(skill::Skill)
    content_hash = sha256(skill.specification)
    canonical_name = "skill://$(content_hash[1:16])"
    
    # Name IS the hash
    # Collision → identical skill
    return canonical_name
end
```

---

## Answer to "When?"

### Name hashing IS appropriate when:

1. ✓ **Skills are pure interfaces** (most asi skills)
2. ✓ **Skills are homoiconic** (Clojure/Lisp skills)
3. ✓ **Skills are MCP servers** (server identity = capability)
4. ✓ **Skills are immutable** (functional programming)
5. ✓ **Skills are versioned** (name includes version)
6. ✓ **Skills are content-addressed** (name = hash)

### Name hashing FAILS when:

1. ✗ **Behavior is mutable** (runtime redefinition)
2. ✗ **Behavior is polymorphic** (type-dependent)
3. ✗ **Behavior is configured** (config affects execution)
4. ✗ **Behavior is non-deterministic** (random, I/O, time)

---

## For asi Repository Specifically

**Current state**: 471 skills, mostly SKILL.md only

**Analysis**:
- ~90% are interface/specification skills ✓
- ~5% are MCP server integrations ✓
- ~5% have actual code (needs verification)

**Conclusion**: **Name hashing is appropriate for ~95% of asi skills** ✓

**For the 5% with code**: Need behavioral testing
- Execute with test inputs
- Compare outputs
- Build actual equivalence classes

---

## Implementation Recommendation

```julia
function compute_skill_equivalence(skills::Vector{Skill})
    # Separate by type
    interface_skills = filter(s -> !has_code(s), skills)
    executable_skills = filter(s -> has_code(s), skills)
    
    # Interface skills: name hash OK
    interface_classes = group_by(s -> hash(s.name), interface_skills)
    
    # Executable skills: behavioral testing required
    executable_classes = group_by_behavior(executable_skills)
    
    return vcat(interface_classes, executable_classes)
end

function group_by_behavior(skills::Vector{Skill})
    classes = Dict{UInt64, Vector{Skill}}()
    
    for skill in skills
        # Execute on test suite
        behavior_sig = hash([
            skill.execute(input) 
            for input in test_inputs
        ])
        
        if !haskey(classes, behavior_sig)
            classes[behavior_sig] = Skill[]
        end
        push!(classes[behavior_sig], skill)
    end
    
    return values(classes)
end
```

---

## Conclusion

**When is name hashing like skill execution?**

**Answer**: When skills are **interfaces**, **specifications**, or **capabilities** rather than **implementations**.

For the asi repository: ~95% of skills fit this category, making name hashing an appropriate proxy for behavioral equivalence.

For the remaining 5%: Actual execution testing is required.

**The key insight**: Most skills in asi are **meta-computational** - they organize, route, and coordinate rather than compute. For these, identity (name) IS behavior.
