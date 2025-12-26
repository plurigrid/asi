# mruler - Meta-Ruler Skill Governance

**Trit: 0 (ERGODIC - Coordinator)**

Ensures ALL skills are used maximally, correctly, and precisely at all times.

## Purpose

The mruler is the governance layer that:
1. **Monitors** skill loading and invocation
2. **Enforces** GF(3) conservation across skill triads
3. **Validates** skill composition correctness
4. **Maximizes** skill utilization efficiency

## Laws Enforced

```
LAW 1: TRIADIC LOADING
  On EVERY interaction, load exactly 3 skills with Σ trits = 0
  
LAW 2: GF(3) CONSERVATION
  Every skill composition must satisfy: Σ trits ≡ 0 (mod 3)
  
LAW 3: MAXIMUM UTILIZATION
  Prefer skills that haven't been used recently
  Track skill invocation frequency
  
LAW 4: CORRECT INVOCATION
  Match skill to task domain
  Verify skill prerequisites are met
  
LAW 5: PRECISE EXECUTION
  Skills must complete with verifiable output
  Output must satisfy skill's contract
```

## Skill Registry

```clojure
(def SKILL-REGISTRY
  {:generators   {:trit +1 :count 61 :examples ["gay-mcp" "parallel-fanout" "world-hopping"]}
   :coordinators {:trit  0 :count 61 :examples ["asi-integrated" "triad-interleave" "unworld"]}
   :validators   {:trit -1 :count 61 :examples ["bisimulation-game" "spi-parallel-verify" "three-match"]}})
;; 183 total skills, balanced 61-61-61
```

## Governance Protocol

### On Session Start
```bash
# Pull fresh skills
npx ai-agent-skills install plurigrid/asi --agent amp

# Verify skill count
ls ~/.agents/skills/ | wc -l  # Should be 183+
```

### On Every Interaction
```python
def mruler_enforce(interaction):
    # 1. Select triadic skills based on task
    skills = select_triad(interaction, unused_first=True)
    
    # 2. Verify GF(3) balance
    assert sum(s.trit for s in skills) % 3 == 0
    
    # 3. Load skills
    for skill in skills:
        load_skill(skill)
        log_invocation(skill)
    
    # 4. Execute with validation
    results = [skill.execute(interaction) for skill in skills]
    
    # 5. Verify outputs
    for skill, result in zip(skills, results):
        assert skill.validate_output(result)
    
    return merge_results(results)
```

## Skill Utilization Tracking

```sql
CREATE TABLE skill_invocations (
    invocation_id VARCHAR PRIMARY KEY,
    skill_name VARCHAR NOT NULL,
    trit INT CHECK (trit IN (-1, 0, 1)),
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    thread_id VARCHAR,
    success BOOLEAN,
    duration_ms INT
);

CREATE VIEW skill_utilization AS
SELECT 
    skill_name,
    trit,
    COUNT(*) as invocations,
    AVG(duration_ms) as avg_duration,
    SUM(CASE WHEN success THEN 1 ELSE 0 END)::FLOAT / COUNT(*) as success_rate
FROM skill_invocations
GROUP BY skill_name, trit
ORDER BY invocations DESC;

CREATE VIEW underutilized_skills AS
SELECT skill_name, trit
FROM all_skills
WHERE skill_name NOT IN (
    SELECT DISTINCT skill_name 
    FROM skill_invocations 
    WHERE timestamp > NOW() - INTERVAL '7 days'
);
```

## Correctness Validation

### Domain Matching
```clojure
(def SKILL-DOMAINS
  {"aptos-agent"      #{:blockchain :transfer :stake}
   "gay-mcp"          #{:color :deterministic :gf3}
   "parallel-fanout"  #{:parallel :triadic :fanout}
   "bisimulation-game" #{:verification :equivalence :dispersal}
   "world-hopping"    #{:navigation :worlds :triangle-inequality}})

(defn validate-domain-match [skill task]
  (let [task-keywords (extract-keywords task)
        skill-domain (get SKILL-DOMAINS (:name skill) #{})]
    (> (count (clojure.set/intersection task-keywords skill-domain)) 0)))
```

### Output Contracts
```clojure
(defn validate-output [skill result]
  (case (:name skill)
    "gay-mcp"          (and (contains? result :hex) (contains? result :trit))
    "parallel-fanout"  (and (= 3 (count (:children result))) 
                            (zero? (reduce + (map :trit (:children result)))))
    "bisimulation-game" (boolean? (:equivalent? result))
    true))  ; Default: accept any output
```

## Maximum Utilization Algorithm

```clojure
(defn select-triad [task loaded-skills invocation-history]
  (let [domain (classify-domain task)
        candidates (filter #(matches-domain? % domain) all-skills)
        
        ;; Prefer underutilized skills
        scored (map (fn [s] 
                      {:skill s 
                       :score (- (get invocation-history (:name s) 0))})
                    candidates)
        sorted (sort-by :score > scored)
        
        ;; Select balanced triad
        plus-skill   (first (filter #(= +1 (:trit (:skill %))) sorted))
        minus-skill  (first (filter #(= -1 (:trit (:skill %))) sorted))
        ergodic-skill (first (filter #(= 0 (:trit (:skill %))) sorted))]
    
    [(:skill plus-skill) (:skill ergodic-skill) (:skill minus-skill)]))
```

## Integration with AGENTS.md

Add to your AGENTS.md:

```markdown
## mruler Governance

**Rule M1: Triadic Skill Loading**
- Load exactly 3 skills per interaction
- Trits must sum to 0

**Rule M2: Skill Rotation**
- Prefer skills not used in last 10 interactions
- Track utilization in DuckDB

**Rule M3: Output Validation**
- Every skill output must be validated
- Failed validations trigger retry with alternate skill

**Rule M4: Maximum Awareness**
- All 183 skills are available
- Cross-domain composition encouraged
- Interstellar hops (stream × world × skill) preferred
```

## Commands

```bash
# Check skill utilization
just mruler-utilization

# Find underutilized skills
just mruler-underutilized

# Validate last N invocations
just mruler-validate 10

# Force rotation to unused skills
just mruler-rotate

# Full governance report
just mruler-report
```

## Justfile Recipes

```just
# mruler skill governance
mruler-utilization:
    duckdb ~/.topos/ducklake.duckdb "SELECT * FROM skill_utilization ORDER BY invocations DESC LIMIT 20;"

mruler-underutilized:
    duckdb ~/.topos/ducklake.duckdb "SELECT * FROM underutilized_skills;"

mruler-validate COUNT="10":
    bb scripts/mruler_validate.bb {{COUNT}}

mruler-rotate:
    bb scripts/mruler_rotate.bb

mruler-report:
    @echo "╔═══════════════════════════════════════════════════════════════╗"
    @echo "║              MRULER GOVERNANCE REPORT                         ║"
    @echo "╚═══════════════════════════════════════════════════════════════╝"
    @just mruler-utilization
    @echo ""
    @just mruler-underutilized
```

## GF(3) Verification

Every mruler action verifies:

```
Σ (loaded_skills.trit) ≡ 0 (mod 3)
Σ (invoked_skills.trit) ≡ 0 (mod 3)  
Σ (output_trits) ≡ 0 (mod 3)
```

If any check fails, mruler auto-corrects by adding balancing skill.

## See Also

- `maximum-awareness` - Composition primitives
- `parallel-fanout` - Triadic dispatch
- `triad-interleave` - Stream interleaving
- `asi-integrated` - Skill lattice
- `spi-parallel-verify` - Parallelism verification
