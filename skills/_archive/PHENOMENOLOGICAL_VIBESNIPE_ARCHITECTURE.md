# Phenomenological Vibesnipe Architecture

## Domain Reframing: From GitHub Issues to Whole-Brain Phenomenology

The original vibesnipe failed because it chose the wrong domain (GitHub issues → speculative compute markets). The **correct domain** is **whole-brain electricity circuitry and phenomenology** - not clinical genes.

### The Missed Causal Chain

```
Original: GitHub issues → developer challenges → APT settlement
Failed: No market maker, illiquid, ~$0 value

Intended: ArkhaiPufferEnv → CoopHive RL → vibesnipe → MNX perp execution  
Missed: Compute/AI exchange with leverage → $25M+ potential

Correct: Phenomenal states → neural oracles → prediction markets → settlement
Domain: Whole-brain phenomenology, NOT clinical genetics
```

## Core Architecture: RGB-ECS for Phenomenology

Inspired by [andrewgazelka/rgb](https://github.com/andrewgazelka/rgb) Minecraft server:

### RGB Spatial Partitioning for Phenomenal States

```
Brain Region RGB Coloring (for parallel processing):
┌─────────────────────────────────────────────────────────────┐
│  RED (Phase 1)    │  GREEN (Phase 2)   │  BLUE (Phase 3)    │
├───────────────────┼────────────────────┼────────────────────┤
│  Prefrontal       │  Temporal          │  Parietal          │
│  Motor cortex     │  Auditory          │  Somatosensory     │
│  Anterior cingul. │  Hippocampus       │  Visual cortex     │
│  Broca's area     │  Amygdala          │  Wernicke's area   │
└───────────────────┴────────────────────┴────────────────────┘

Processing: RED → GREEN → BLUE → RED (lock-free parallelism)
Same as Minecraft server: same-colored regions process in parallel
```

### GF(3) Trit Mapping to Phenomenal Qualities

```julia
# From Gay.jl color system
@enum PhenomenalTrit begin
    MINUS = -1   # Inhibitory, negative valence, contraction
    ERGODIC = 0  # Neutral, exploratory, transition
    PLUS = +1    # Excitatory, positive valence, expansion
end

# Balanced quads for challenge validation
sum(challenge_trits) ≡ 0 (mod 3)  # GF(3) conservation
```

### Phenomenological Challenge Types (26 Goblin Slots)

| Slot | Challenge Type | Oracle | GF(3) Trit |
|------|---------------|--------|------------|
| 1 | EEG Microstate A→B Transition | Microstate classifier | MINUS |
| 2 | Alpha Power Prediction (8-12 Hz) | FFT spectral | ERGODIC |
| 3 | P300 Amplitude Detection | ERP averaging | PLUS |
| 4 | Default Mode Network Activation | fMRI/fNIRS | MINUS |
| 5 | Flow State Entry | HRV + pupillometry | PLUS |
| 6 | MMN (Mismatch Negativity) | Auditory ERP | MINUS |
| 7 | Theta-Gamma Coupling | Phase-amplitude | ERGODIC |
| 8 | Meditation Depth | Alpha/theta ratio | PLUS |
| 9 | Salience Network Switch | dACC activation | ERGODIC |
| 10 | Beta Desynchronization | Motor prep signal | MINUS |
| 11 | N400 Semantic Surprise | Language ERP | MINUS |
| 12 | Pupil Dilation (LC-NE) | Pupillometry | PLUS |
| 13 | GSR Arousal Response | Electrodermal | PLUS |
| 14 | Heart Rate Variability | RSA/RMSSD | ERGODIC |
| 15 | ERN (Error-Related Negativity) | ACC ERP | MINUS |
| 16 | Gamma Synchrony (>30 Hz) | High-freq binding | PLUS |
| 17 | Sleep Spindles | Sigma band | ERGODIC |
| 18 | K-Complex Detection | Sleep N2 marker | MINUS |
| 19 | Dream Lucidity | REM + gamma | PLUS |
| 20 | Pain Matrix Activation | Anterior insula | MINUS |
| 21 | Placebo Response | Expectation → physio | ERGODIC |
| 22 | IIT Φ Estimation | Integrated information | PLUS |
| 23 | Global Workspace Ignition | P3b + late positivity | PLUS |
| 24 | Habituation Curve | Response decrement | MINUS |
| 25 | Neuromodulator Transition | DA/5HT/ACh balance | ERGODIC |
| 26 | Metastability Index | Criticality measure | ERGODIC |

## Oracle System: Non-Invasive Verifiable Signals

### Tier 1: Consumer-Grade (BCI headsets)
- **EEG**: Muse, OpenBCI, Emotiv (4-64 channels)
- **Pupillometry**: Eye trackers (Tobii, webcam-based)
- **HRV**: Chest straps, smartwatches (Polar, Apple Watch)
- **GSR**: Wrist sensors (Empatica, custom Arduino)

### Tier 2: Research-Grade (Lab partnerships)
- **fNIRS**: Prefrontal hemodynamics
- **MEG**: Millisecond magnetic fields
- **High-density EEG**: 128-256 channels

### Tier 3: Clinical (Hospital partnerships)
- **fMRI**: BOLD response (delayed settlement)
- **PET**: Neurotransmitter binding
- **iEEG**: Intracranial (epilepsy patients)

### Oracle Attestation Protocol

```move
struct PhenomenalOracle has key {
    oracle_id: u64,
    modality: u8,          // EEG=1, pupil=2, HRV=3, GSR=4, fNIRS=5
    sampling_rate_hz: u32,
    attestation_key: vector<u8>,  // Ed25519 pubkey
    reputation_score: u64,
    challenges_attested: u64,
}

struct ChallengeAttestation has drop {
    challenge_id: u64,
    oracle_id: u64,
    timestamp_ms: u64,
    measurement: vector<u8>,  // Serialized phenomenal data
    signature: vector<u8>,
}
```

## Settlement Mechanism: Active Inference Stakes

### Precision-Weighted Betting

```julia
# Active inference formulation
struct PhenomenalChallenge
    # World-model belief (what participant expects to experience)
    μ_prior::Vector{Float64}      # Prior mean
    Σ_prior::Matrix{Float64}      # Prior covariance
    
    # Precision (confidence/stake)
    β::Float64                    # Inverse variance = skin in game
    
    # Outcome
    μ_posterior::Vector{Float64}  # Observed phenomenal state
    
    # Free energy = prediction error
    F = (μ_posterior - μ_prior)' * inv(Σ_prior) * (μ_posterior - μ_prior)
end

# Settlement: lower free energy = better prediction = win
reward = exp(-F / temperature)
```

### Aptos Move Contract Integration

```move
module vibesnipe::phenomenal_challenge {
    use std::signer;
    use aptos_framework::coin;
    use aptos_framework::aptos_coin::AptosCoin;
    
    const PLATFORM_FEE_BPS: u64 = 250;  // 2.5%
    
    struct PhenomenalChallenge has key {
        challenger: address,
        responder: address,
        challenge_type: u8,           // 1-26 goblin slots
        stake_amount: u64,
        precision_beta: u64,          // Fixed-point β * 1e6
        prior_mean: vector<u64>,      // Fixed-point μ * 1e6
        oracle_id: u64,
        deadline_ms: u64,
        gf3_trit: u8,                 // 0=MINUS, 1=ERGODIC, 2=PLUS
    }
    
    public entry fun create_phenomenal_challenge(
        challenger: &signer,
        challenge_type: u8,
        stake_amount: u64,
        precision_beta: u64,
        prior_mean: vector<u64>,
        oracle_id: u64,
        duration_ms: u64,
    ) acquires ChallengeStore {
        // Validate GF(3) balance with existing active challenges
        assert!(is_gf3_balanced(challenger, challenge_type), E_UNBALANCED_TRITS);
        
        // Lock stake
        let stake = coin::withdraw<AptosCoin>(challenger, stake_amount);
        
        // Create challenge entity
        // ...
    }
    
    public entry fun resolve_with_oracle(
        oracle: &signer,
        challenge_id: u64,
        observed_mean: vector<u64>,
        attestation_signature: vector<u8>,
    ) acquires ChallengeStore, OracleRegistry {
        // Verify oracle attestation
        // Compute free energy
        // Distribute rewards based on prediction accuracy
    }
}
```

## RGB-ECS Component Architecture

### Components (POD only, no collections)

```rust
// From andrewgazelka/rgb pattern
#[derive(Component, Clone)]
struct PhenomenalState {
    microstate: u8,           // A, B, C, D, E, F, G
    alpha_power: f32,         // 8-12 Hz
    theta_power: f32,         // 4-8 Hz
    gamma_power: f32,         // 30-100 Hz
    valence: f32,             // -1.0 to +1.0
    arousal: f32,             // 0.0 to 1.0
    gf3_trit: i8,             // -1, 0, +1
}

#[derive(Component, Clone)]
struct OracleReading {
    modality: u8,
    timestamp_ns: u64,
    values: [f32; 8],         // Fixed array, no Vec
    confidence: f32,
}

#[derive(Component, Clone)]
struct ChallengeEntity {
    challenge_id: u64,
    goblin_slot: u8,          // 1-26
    stake_apt: u64,
    precision_beta: f32,
    prior_mean: [f32; 4],
    deadline_ns: u64,
}

// Relations replace collections
struct ParticipantOf;  // Participant --ParticipantOf--> Challenge
struct AttestedBy;     // Challenge --AttestedBy--> Oracle
struct InRegion;       // Entity --InRegion--> BrainRegion (RGB colored)
```

### Systems Pipeline

```rust
// Phase 1: Ingress (sequential)
fn system_oracle_ingress(world: &World) {
    // Poll oracle data streams
    // Create OracleReading entities
}

// Phase 2: RED regions (parallel)
fn system_process_red_regions(world: &World) {
    // Prefrontal, motor, ACC, Broca
    // Update PhenomenalState for entities in RED regions
}

// Phase 3: GREEN regions (parallel)  
fn system_process_green_regions(world: &World) {
    // Temporal, auditory, hippocampus, amygdala
}

// Phase 4: BLUE regions (parallel)
fn system_process_blue_regions(world: &World) {
    // Parietal, somatosensory, visual, Wernicke
}

// Phase 5: Settlement (sequential)
fn system_settle_challenges(world: &World) {
    // Compute free energy for mature challenges
    // Emit settlement transactions
}
```

## Value Capture Mechanism

### Market Structure

```
Phenomenal Prediction Markets:
┌─────────────────────────────────────────────────────────┐
│  Challenge Creator (Challenger)                          │
│  - Stakes APT + precision β                              │
│  - Specifies prior belief μ about own phenomenal state   │
│  - Selects goblin slot (challenge type)                  │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│  Oracle Network                                          │
│  - Consumer BCI devices (Muse, OpenBCI)                  │
│  - Attests to observed phenomenal measurements           │
│  - Earns attestation fees                                │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│  Settlement Engine                                       │
│  - Computes free energy F = prediction error             │
│  - Distributes stake based on accuracy                   │
│  - Platform takes 2.5% fee                               │
└─────────────────────────────────────────────────────────┘
```

### Revenue Streams

1. **Platform fee**: 2.5% of all settled stakes
2. **Oracle fees**: Per-attestation micropayments
3. **Data marketplace**: Anonymized phenomenal data for research
4. **Premium challenges**: High-precision research-grade oracles
5. **Enterprise**: Corporate wellness/productivity tracking

### TAM Analysis

```
Consumer BCI market: $1.8B (2024) → $5.5B (2030)
Meditation app market: $2.5B (2024) → $6.2B (2030)  
Neurofeedback market: $1.1B (2024) → $2.8B (2030)
Prediction markets: $12B (2024) → $50B+ (2030)

Combined addressable: ~$20B by 2030
Capture 0.5%: $100M ARR potential
```

## Implementation Roadmap

### Phase 1: MVP (3 months)
- Single oracle modality (EEG microstates via Muse)
- 4 challenge types (slots 1-4)
- Basic Aptos settlement
- Web dashboard

### Phase 2: Multi-Oracle (6 months)
- Add pupillometry, HRV, GSR
- 13 challenge types (slots 1-13)
- Oracle reputation system
- Mobile app

### Phase 3: Research Grade (12 months)
- fNIRS partnerships
- Full 26 goblin slots
- Enterprise API
- Data marketplace

### Phase 4: Scale (18+ months)
- MEG/fMRI integration (delayed settlement)
- Cross-chain (Solana, Sui)
- DAO governance
- International expansion

## Key Differentiators from Failed vibesnipe

| Aspect | Failed vibesnipe | Phenomenal vibesnipe |
|--------|------------------|----------------------|
| Domain | GitHub issues (illiquid) | Phenomenal states (universal) |
| Oracle | Human judgment | Objective BCI signals |
| Market | Developer niche | Everyone with a brain |
| Verifiability | Subjective | Cryptographic attestation |
| Settlement | Manual | Algorithmic (free energy) |
| Scalability | Per-issue | Data-parallel (RGB) |

## Salvaged Components from Original

| Component | Original Use | Phenomenal Use |
|-----------|--------------|----------------|
| GF(3) trit system | Challenge balance | Phenomenal quality mapping |
| 26 goblin slots | GitHub issue types | Phenomenal challenge types |
| Aptos Move contracts | APT settlement | Same, enhanced |
| ACP agent protocol | Bot coordination | Oracle coordination |
| ACSet infrastructure | Issue graphs | Phenomenal state graphs |
| OCapN CapTP | Agent communication | Oracle attestation |

## Conclusion

The phenomenological vibesnipe reframes the domain from illiquid developer challenges to universal whole-brain phenomenology. By using:

1. **RGB-ECS parallelism** from andrewgazelka/rgb
2. **GF(3) conservation** for balanced prediction markets
3. **Active inference** (precision-weighted free energy) for settlement
4. **Non-invasive BCI oracles** for verifiable measurements

We capture the original vibesnipe infrastructure while targeting a market with:
- Universal appeal (everyone experiences phenomenal states)
- Objective verifiability (BCI attestations)
- Growing TAM ($20B+ by 2030)
- Clear value capture (2.5% platform fee)

The key insight: **consciousness is the most liquid market** - everyone participates, continuously.
