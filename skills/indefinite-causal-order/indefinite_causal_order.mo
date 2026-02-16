package IndefiniteCausalOrder
  "Indefinite Causal Order over GF(3) — Modelica acausal formulation.
   Process matrices, quantum switch, affordance-gated supermaps.

   GF(3) Trit: 0 (ERGODIC — coordination between causal orders)
   Refs: Oreshkov-Costa-Brukner 2012, Chiribella et al. 2013"

  // ════════════════════════════════════════════════════════════
  // GF(3) Arithmetic
  // ════════════════════════════════════════════════════════════

  function gf3add "GF(3) addition: (a + b) mod 3 in {-1, 0, +1}"
    input Integer a;
    input Integer b;
    output Integer c;
  algorithm
    c := a + b;
    if c > 1 then c := c - 3;
    elseif c < -1 then c := c + 3;
    end if;
  end gf3add;

  function gf3mul "GF(3) multiplication: (a × b) mod 3"
    input Integer a;
    input Integer b;
    output Integer c;
  algorithm
    c := a * b;
    if c > 1 then c := c - 3;
    elseif c < -1 then c := c + 3;
    end if;
  end gf3mul;

  // ════════════════════════════════════════════════════════════
  // Channel: 3×3 affine map over GF(3)
  // ════════════════════════════════════════════════════════════

  record Channel "C(x) = Mx + b over GF(3)^3"
    Integer M[3,3] "3×3 matrix over {-1,0,+1}";
    Integer b[3] "offset vector";
  end Channel;

  function channelApply "y = M·x + b over GF(3)"
    input Channel ch;
    input Integer x[3];
    output Integer y[3];
  protected
    Integer s;
  algorithm
    for i in 1:3 loop
      s := ch.b[i];
      for j in 1:3 loop
        s := gf3add(s, gf3mul(ch.M[i,j], x[j]));
      end for;
      y[i] := s;
    end for;
  end channelApply;

  function channelCompose "(A ∘ B)(x) = A(B(x))"
    input Channel A;
    input Channel B;
    output Channel C;
  protected
    Integer s;
  algorithm
    // Matrix: A.M × B.M
    for i in 1:3 loop
      for j in 1:3 loop
        s := 0;
        for k in 1:3 loop
          s := gf3add(s, gf3mul(A.M[i,k], B.M[k,j]));
        end for;
        C.M[i,j] := s;
      end for;
    end for;
    // Offset: A.M × B.b + A.b
    for i in 1:3 loop
      s := A.b[i];
      for j in 1:3 loop
        s := gf3add(s, gf3mul(A.M[i,j], B.b[j]));
      end for;
      C.b[i] := s;
    end for;
  end channelCompose;

  function channelAdd "Element-wise GF(3) addition of two channels"
    input Channel A;
    input Channel B;
    output Channel C;
  algorithm
    for i in 1:3 loop
      for j in 1:3 loop
        C.M[i,j] := gf3add(A.M[i,j], B.M[i,j]);
      end for;
      C.b[i] := gf3add(A.b[i], B.b[i]);
    end for;
  end channelAdd;

  // ════════════════════════════════════════════════════════════
  // Quantum Switch: The Core ICO Construction
  // ════════════════════════════════════════════════════════════

  function quantumSwitch
    "S(C1, C2, control): GF(3)-controlled causal order.
     control=0: C1∘C2, control=+1: C2∘C1, control=-1: C1⊕₃C2"
    input Channel C1;
    input Channel C2;
    input Integer control "GF(3) trit: {-1, 0, +1}";
    output Channel result;
  protected
    Channel fwd, rev;
  algorithm
    if control == 0 then
      result := channelCompose(C1, C2);
    elseif control == 1 then
      result := channelCompose(C2, C1);
    else
      fwd := channelCompose(C1, C2);
      rev := channelCompose(C2, C1);
      result := channelAdd(fwd, rev);
    end if;
  end quantumSwitch;

  // ════════════════════════════════════════════════════════════
  // Phase Cell: 27-element GF(3)^3 state
  // ════════════════════════════════════════════════════════════

  record PhaseCell "Point in RF phase space"
    Integer freq "frequency band {-1,0,+1}";
    Integer phase "carrier phase {-1,0,+1}";
    Integer amp "signal amplitude {-1,0,+1}";
  end PhaseCell;

  function phaseParity "GF(3) parity: conservation invariant"
    input PhaseCell pc;
    output Integer p;
  algorithm
    p := gf3add(gf3add(pc.freq, pc.phase), pc.amp);
  end phaseParity;

  // ════════════════════════════════════════════════════════════
  // Affordance: Phase-space region × capability
  // ════════════════════════════════════════════════════════════

  function evaluateAffordance
    "Gibson affordance: +1=available, 0=uncertain, -1=blocked"
    input PhaseCell state;
    input Integer minFreq;
    input Integer minPhase;
    input Integer minAmp;
    output Integer trit;
  protected
    Integer matches;
  algorithm
    if state.freq >= minFreq and state.phase >= minPhase and state.amp >= minAmp then
      trit := 1;
    else
      matches := 0;
      if state.freq >= minFreq then matches := matches + 1; end if;
      if state.phase >= minPhase then matches := matches + 1; end if;
      if state.amp >= minAmp then matches := matches + 1; end if;
      if matches >= 2 then trit := 0; else trit := -1; end if;
    end if;
  end evaluateAffordance;

  // ════════════════════════════════════════════════════════════
  // ICO System Model (continuous-time DAE)
  // ════════════════════════════════════════════════════════════

  model ICOSystem
    "Continuous-time indefinite causal order system.
     Two agents observe a shared landscape; their causal order
     is determined by a control signal that evolves via Langevin dynamics."

    // Parameters
    parameter Real beta = 1.0 "Inverse temperature";
    parameter Real sigma = 0.3 "Langevin noise amplitude";
    parameter Real dt = 0.02 "Time step for discretized updates";

    // State: continuous control signal
    Real controlSignal(start=0.0) "Continuous control (quantized to GF(3))";
    Integer controlTrit "Quantized control trit";

    // Two channels (represented by their determinants for DAE tractability)
    Real detC1(start=1.0) "det(Channel 1)";
    Real detC2(start=1.0) "det(Channel 2)";
    Real detSwitch "det(quantum switch output)";

    // Landscape energy (from affective taxis bridge)
    Real energy(start=0.0) "Energy at current state";
    Real valence "Directional derivative of energy";

    // GF(3) accumulator
    Integer gf3Sum(start=0) "Running GF(3) sum of control trits";

    // Affordance evaluation
    Integer affCommunicate "communicate affordance";
    Integer affSense "sense affordance";
    Integer affActuate "actuate affordance";

    // Phase cell state (discretized from continuous)
    PhaseCell state;

  equation
    // Langevin dynamics on control signal
    der(controlSignal) = -beta * controlSignal + sigma * sin(time * 7.3);

    // Quantize to GF(3) trit
    controlTrit = if controlSignal > 0.33 then 1
                  elseif controlSignal < -0.33 then -1
                  else 0;

    // Channel determinants evolve (simplified DAE)
    der(detC1) = -0.1 * (detC1 - cos(time));
    der(detC2) = -0.1 * (detC2 - sin(time));

    // Quantum switch determinant depends on control
    detSwitch = if controlTrit == 0 then detC1 * detC2
                elseif controlTrit == 1 then detC2 * detC1
                else detC1 + detC2;  // superposition case

    // Energy from landscape
    energy = 0.5 * (detC1^2 + detC2^2);
    valence = der(energy);

    // Phase cell from continuous state (discretized)
    state.freq = if detC1 > 0.33 then 1 elseif detC1 < -0.33 then -1 else 0;
    state.phase = if detC2 > 0.33 then 1 elseif detC2 < -0.33 then -1 else 0;
    state.amp = if abs(detSwitch) > 0.5 then 1 elseif abs(detSwitch) > 0.1 then 0 else -1;

    // Affordance evaluation
    affCommunicate = evaluateAffordance(state, -1, -1, 0);
    affSense = evaluateAffordance(state, -1, 0, -1);
    affActuate = evaluateAffordance(state, 0, 0, 0);

  end ICOSystem;

  // ════════════════════════════════════════════════════════════
  // Multi-Agent ICO
  // ════════════════════════════════════════════════════════════

  model MultiAgentICO
    "Three agents with pairwise quantum switches.
     GF(3) conservation: Σ control trits ≡ 0 (mod 3)."

    parameter Real beta = 1.0;
    parameter Real sigma = 0.2;

    // Three agents
    Real control1(start=0.0);
    Real control2(start=0.3);
    Real control3(start=-0.3);

    Integer trit1, trit2, trit3;
    Integer gf3Sum "Sum of trits mod 3";

    // Pairwise switch determinants
    Real detSwitch12, detSwitch23, detSwitch13;

    // Agent energies (landscape)
    Real energy1, energy2, energy3;
    Real totalEnergy;

  equation
    // Coupled Langevin dynamics (agents influence each other)
    der(control1) = -beta * control1 + 0.1 * (control2 - control3) + sigma * sin(time * 3.7);
    der(control2) = -beta * control2 + 0.1 * (control3 - control1) + sigma * cos(time * 5.3);
    der(control3) = -beta * control3 + 0.1 * (control1 - control2) + sigma * sin(time * 7.1);

    // Quantize
    trit1 = if control1 > 0.33 then 1 elseif control1 < -0.33 then -1 else 0;
    trit2 = if control2 > 0.33 then 1 elseif control2 < -0.33 then -1 else 0;
    trit3 = if control3 > 0.33 then 1 elseif control3 < -0.33 then -1 else 0;

    // GF(3) sum
    gf3Sum = gf3add(gf3add(trit1, trit2), trit3);

    // Switch determinants
    detSwitch12 = if trit1 == 0 then cos(time) elseif trit1 == 1 then sin(time) else cos(time) + sin(time);
    detSwitch23 = if trit2 == 0 then sin(time) elseif trit2 == 1 then cos(2*time) else sin(time) + cos(2*time);
    detSwitch13 = if trit3 == 0 then cos(2*time) elseif trit3 == 1 then cos(time) else cos(2*time) + cos(time);

    // Agent energies
    energy1 = 0.5 * (control1^2 + detSwitch12^2);
    energy2 = 0.5 * (control2^2 + detSwitch23^2);
    energy3 = 0.5 * (control3^2 + detSwitch13^2);
    totalEnergy = energy1 + energy2 + energy3;

  end MultiAgentICO;

  // ════════════════════════════════════════════════════════════
  // Taxis Bridge
  // ════════════════════════════════════════════════════════════

  model TaxisICOBridge
    "Bridge between affective taxis and indefinite causal order.
     Valence (directional derivative) determines causal order:
       positive → sense then act (standard taxis)
       negative → act then sense (proactive)
       near-zero → indefinite (genuine ICO)"

    parameter Real threshold = 0.1;
    parameter Real landscapeFreq = 0.5 "Landscape oscillation frequency";
    parameter Real agentSpeed = 0.3;

    // Landscape
    Real energy;
    Real valence;

    // Agent
    Real position(start=0.0);
    Real velocity(start=0.1);

    // ICO control
    Integer causalOrder "0=sense→act, +1=act→sense, -1=indefinite";
    Integer gf3Accumulator(start=0);

  equation
    // Energy landscape (oscillating Gaussian)
    energy = exp(-position^2) * (1 + 0.3 * sin(landscapeFreq * time));
    valence = der(energy);

    // Agent dynamics
    der(position) = velocity;
    der(velocity) = -0.5 * velocity + 0.3 * valence;

    // Causal order from valence
    causalOrder = if valence > threshold then 0
                  elseif valence < -threshold then 1
                  else -1;

  end TaxisICOBridge;

  // ════════════════════════════════════════════════════════════
  // Canonical Channels
  // ════════════════════════════════════════════════════════════

  constant Channel IDENTITY(
    M = [1, 0, 0; 0, 1, 0; 0, 0, 1],
    b = {0, 0, 0});

  constant Channel CNOT_FREQ_PHASE(
    M = [1, 0, 0; 1, 1, 0; 0, 0, 1],
    b = {0, 0, 0});

  constant Channel PERMUTE(
    M = [0, 1, 0; 0, 0, 1; 1, 0, 0],
    b = {0, 0, 0});

end IndefiniteCausalOrder;
