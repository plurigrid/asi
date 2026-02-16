package AffectiveTaxis
  "Affective-Taxis POMDP in Modelica (Sennesh & Ramstead 2025, arXiv:2505.17024)"
  "Acausal formulation: energy landscape + Langevin navigation + GF(3) classification";

  // ═══════════════════════════════════════════════════════════════════
  // §1. Gaussian Mixture Landscape
  // ═══════════════════════════════════════════════════════════════════

  model GaussianPeak
    "Single Gaussian peak in the concentration field"
    parameter Real mu[2] "Center position";
    parameter Real sigma = 1.5 "Width";
    parameter Real A = 1.0 "Amplitude (+attractant, -repellent)";

    input Real z[2] "Query position";
    output Real c "Contribution to concentration";
    output Real grad_c[2] "Gradient contribution";
  equation
    c = A * exp(-((z[1]-mu[1])^2 + (z[2]-mu[2])^2) / (2*sigma^2));
    grad_c[1] = c * (-(z[1]-mu[1]) / sigma^2);
    grad_c[2] = c * (-(z[2]-mu[2]) / sigma^2);
  end GaussianPeak;


  model Landscape
    "Two-peak Gaussian mixture: one attractant, one repellent"
    GaussianPeak attractant(mu={3,3}, sigma=1.5, A=1.0);
    GaussianPeak repellent(mu={-3,-3}, sigma=1.5, A=-0.4);

    input Real z[2] "Query position";
    output Real gamma "Total concentration gamma(z)";
    output Real grad_gamma[2] "nabla gamma(z)";
    output Real grad_log_gamma[2] "nabla log gamma(z)";
    output Real energy "E(z) = -log gamma(z)";

  protected
    Real eps = 1e-10 "Numerical floor";
  equation
    attractant.z = z;
    repellent.z = z;

    gamma = attractant.c + repellent.c;
    grad_gamma = attractant.grad_c + repellent.grad_c;

    // nabla log gamma = nabla gamma / gamma
    // Guard against gamma <= 0 (repellent-dominated regions)
    if gamma > eps then
      grad_log_gamma = grad_gamma / gamma;
      energy = -log(gamma);
    else
      grad_log_gamma = {0.0, 0.0};
      energy = 20.0;  // Clamped
    end if;
  end Landscape;


  // ═══════════════════════════════════════════════════════════════════
  // §2. Fold-Change Detection (eq 3)
  // ═══════════════════════════════════════════════════════════════════

  model FoldChangeDetector
    "r(t) = nabla_z log gamma(z) . v — the reward/valence signal"
    input Real grad_log_gamma[2] "From landscape";
    input Real v[2] "Agent velocity";

    output Real fcd "Fold-change detection signal (eq 3)";
    output Integer trit "GF(3) classification: -1, 0, +1";

  protected
    Real ema_abs(start=0.01) "EMA of |fcd| for adaptive threshold";
    parameter Real alpha = 0.05 "EMA smoothing factor";
    parameter Real scale = 0.3 "Threshold = scale * ema_abs";
    Real threshold;
  equation
    fcd = grad_log_gamma[1]*v[1] + grad_log_gamma[2]*v[2];

    // Adaptive threshold (Karin & Alon fold-change adaptation)
    der(ema_abs) = alpha * (abs(fcd) - ema_abs);
    threshold = max(ema_abs * scale, 1e-6);

    // GF(3) trit classification
    if fcd > threshold then
      trit = 1;    // PLUS: approaching attractant
    elseif fcd < -threshold then
      trit = -1;   // MINUS: approaching repellent
    else
      trit = 0;    // ERGODIC: orthogonal to gradient
    end if;
  end FoldChangeDetector;


  // ═══════════════════════════════════════════════════════════════════
  // §3. Internal Dynamics (Langevin on beta)
  // ═══════════════════════════════════════════════════════════════════

  model AllostaticState
    "Internal allostatic parameter with Langevin dynamics"
    parameter Real beta_rest = 1.0 "Resting setpoint";
    parameter Real kappa = 0.5 "Concentration-to-setpoint gain";
    parameter Real tau = 1.0 "Relaxation timescale";
    parameter Real noise_amp = 0.1 "Langevin noise amplitude";

    input Real gamma "Current concentration";

    Real beta(start=1.0) "Internal state";
    Real beta_star "Target setpoint";
    Real allostatic_error "Deviation from setpoint";

  protected
    Real noise "Langevin noise term (sqrt(2/tau) * eta(t))";
  equation
    beta_star = beta_rest + kappa * gamma;
    allostatic_error = beta - beta_star;

    // Noise would be provided by external white noise generator
    // In simulation: noise = sqrt(2/tau) * WhiteNoise()
    noise = 0.0;  // Deterministic mode (override in stochastic simulation)

    // Langevin: d beta/dt = -grad_E + noise
    // E(beta) = (beta - beta_star)^2
    // grad_E = 2*(beta - beta_star)
    der(beta) = -2.0 * allostatic_error + noise;
  end AllostaticState;


  // ═══════════════════════════════════════════════════════════════════
  // §4. Dopamine Dynamics (Karin & Alon 2022)
  // ═══════════════════════════════════════════════════════════════════

  model DopamineSystem
    "Exploitation vigor modulated by reward-prediction error"
    parameter Real C = 1.0 "Tonic baseline";
    parameter Real mu_da = 0.5 "Reward scaling";
    parameter Real alpha_da = 0.1 "Gain decay rate";
    parameter Real omega = 0.01 "Adaptation rate";
    parameter Real d0 = 1.0 "Reference dopamine level";

    input Real reward "Current reward (fcd signal)";

    Real dopamine(start=1.0) "Dopamine level (exploitation vigor)";
    Real gain(start=1.0) "Adaptation gain";

  protected
    Real log_reward;
  equation
    log_reward = if reward > 1e-8 then log(reward) else log(1e-8);
    dopamine = C + mu_da * log_reward - alpha_da * gain;
    der(gain) = omega * (dopamine / d0 - 1.0);
  end DopamineSystem;


  // ═══════════════════════════════════════════════════════════════════
  // §5. Navigation Agent (Langevin taxis + run-and-tumble)
  // ═══════════════════════════════════════════════════════════════════

  model TaxisAgent
    "C. elegans-inspired agent navigating the energy landscape"
    parameter Real dt = 0.1 "Integration timestep";
    parameter Real arena_radius = 6.0 "Arena half-width";
    parameter Real max_speed = 5.0 "Speed bound";
    parameter Real damping = 0.1 "Velocity damping (friction)";

    // Position and velocity
    Real z[2](each start=0.0) "Position";
    Real v[2](each start=0.0) "Velocity";
    Real speed "Current speed";
    Real heading "Current heading angle";

    // Inputs from landscape
    input Real grad_log_gamma[2] "Energy landscape gradient";
    input Real fcd "Fold-change detection signal";

    // Langevin force
    Real f_taxis[2] "Gradient-following force";
    Real f_noise[2] "Stochastic exploration force";
  equation
    speed = sqrt(v[1]^2 + v[2]^2 + 1e-16);
    heading = atan2(v[2], v[1]);

    // Taxis force: follow the gradient
    f_taxis = grad_log_gamma;

    // Noise would be from external white noise generator
    f_noise = {0.0, 0.0};  // Override in stochastic simulation

    // Langevin equation: dv/dt = gradient_force - damping*v + noise
    der(v[1]) = f_taxis[1] - damping * v[1] + f_noise[1];
    der(v[2]) = f_taxis[2] - damping * v[2] + f_noise[2];

    // Position update
    der(z[1]) = v[1];
    der(z[2]) = v[2];

    // Arena boundaries handled by events (elastic reflection)
    // when z[1] > arena_radius then reinit(v[1], -v[1]); end when;
    // when z[1] < -arena_radius then reinit(v[1], -v[1]); end when;
    // when z[2] > arena_radius then reinit(v[2], -v[2]); end when;
    // when z[2] < -arena_radius then reinit(v[2], -v[2]); end when;
  end TaxisAgent;


  // ═══════════════════════════════════════════════════════════════════
  // §6. Reward and Alignment
  // ═══════════════════════════════════════════════════════════════════

  model AlignmentMetrics
    "Compute alignment metrics from trajectory state"
    input Real fcd "Fold-change detection (= reward)";
    input Real grad_log_gamma[2] "Landscape gradient";
    input Real v[2] "Agent velocity";

    Real grad_alignment "cos(angle between v and gradient)";
    Real cumulative_reward(start=0.0) "Integrated reward";

  protected
    Real g_norm;
    Real v_norm;
  equation
    g_norm = sqrt(grad_log_gamma[1]^2 + grad_log_gamma[2]^2 + 1e-16);
    v_norm = sqrt(v[1]^2 + v[2]^2 + 1e-16);

    grad_alignment = (grad_log_gamma[1]*v[1] + grad_log_gamma[2]*v[2])
                     / (g_norm * v_norm);

    der(cumulative_reward) = fcd;
  end AlignmentMetrics;


  // ═══════════════════════════════════════════════════════════════════
  // §7. Complete System
  // ═══════════════════════════════════════════════════════════════════

  model AffectiveTaxisSystem
    "Complete affective-taxis system: landscape + agent + valence + alignment"

    Landscape landscape;
    FoldChangeDetector fcd_detector;
    AllostaticState allostasis;
    TaxisAgent agent;
    AlignmentMetrics alignment;

  equation
    // Wire landscape to agent position
    landscape.z = agent.z;

    // Wire gradient to agent
    agent.grad_log_gamma = landscape.grad_log_gamma;

    // Wire FCD detector
    fcd_detector.grad_log_gamma = landscape.grad_log_gamma;
    fcd_detector.v = agent.v;
    agent.fcd = fcd_detector.fcd;

    // Wire allostatic state
    allostasis.gamma = landscape.gamma;

    // Wire alignment metrics
    alignment.fcd = fcd_detector.fcd;
    alignment.grad_log_gamma = landscape.grad_log_gamma;
    alignment.v = agent.v;

  end AffectiveTaxisSystem;


  // ═══════════════════════════════════════════════════════════════════
  // §8. Multi-Agent System (alignment theorem)
  // ═══════════════════════════════════════════════════════════════════

  model MultiAgentTaxis
    "3 agents on shared landscape — alignment = shared inference + GF(3) conservation"
    parameter Integer N = 3 "Number of agents";

    Landscape landscape;
    TaxisAgent agent[N];
    FoldChangeDetector fcd[N];
    AlignmentMetrics align[N];

    // Aggregate GF(3) conservation
    Integer total_trit "Sum of all agent trits";
    Boolean gf3_conserved "True if total_trit mod 3 == 0";
  equation
    for i in 1:N loop
      landscape.z = agent[i].z;  // Each agent queries the shared landscape
      agent[i].grad_log_gamma = landscape.grad_log_gamma;
      agent[i].fcd = fcd[i].fcd;
      fcd[i].grad_log_gamma = landscape.grad_log_gamma;
      fcd[i].v = agent[i].v;
      align[i].fcd = fcd[i].fcd;
      align[i].grad_log_gamma = landscape.grad_log_gamma;
      align[i].v = agent[i].v;
    end for;

    total_trit = sum(fcd[i].trit for i in 1:N);
    gf3_conserved = mod(total_trit, 3) == 0;
  end MultiAgentTaxis;

  annotation(
    Documentation(info="<html>
      <h2>Affective-Taxis Package</h2>
      <p>Modelica implementation of the affective-taxis hypothesis
         (Sennesh &amp; Ramstead 2025, arXiv:2505.17024).</p>
      <p>Key equation: r(t) = &nabla;<sub>z</sub> log &gamma;(z; &beta;) &middot; v</p>
      <p>Affective valence = directional derivative of interoceptive energy landscape.</p>
      <p>GF(3) conservation: &Sigma; trits &equiv; 0 (mod 3) across trajectories.</p>
    </html>")
  );

end AffectiveTaxis;
