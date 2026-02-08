---
name: hythermal
description: HyThermal Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# HyThermal Skill

> Hy + Thermal: Relational ACSet dynamics with Langevin temperature control

**Version**: 1.0.0
**Trit**: 0 (ERGODIC - bridges relational structure and thermal flow)
**Bundle**: dynamics
**Fusion of**: `hyjax-relational` + `langevin-dynamics`

---

## Overview

**HyThermal** fuses relational thinking (ACSets/C-Sets) with Langevin dynamics for temperature-controlled exploration of concept spaces. Instead of treating thread analysis as static graphs, HyThermal models concepts as particles in a thermal bath:

- **Concepts** = Particles with positions in embedding space
- **Relations** = Potential energy between particles
- **Temperature** = Exploration vs exploitation control
- **Fokker-Planck** = Equilibrium distribution of concept activations

## Core Equation

```
dC(t) = -∇E(C(t)) dt + √(2T) dW(t)

Where:
  C = concept embedding positions
  E = relational energy (sum of edge potentials)
  T = temperature (exploration parameter)
  dW = Brownian motion (seeded via Gay.jl)
```

At equilibrium: `p∞(C) ∝ exp(-E(C)/T)` — Concepts cluster near low-energy (high-coherence) configurations.

## Hy Syntax for Thermal ACSet

```hy
;; Define thermal schema
(defschema ThermalThread
  (Ob Thread Message Concept)
  (Hom thread_msg (-> Message Thread)
       discusses (-> Message Concept)
       related (-> Concept Concept))
  (Attr position (-> Concept R^n)
        temperature (-> Thread Float)
        energy (-> Concept Float)))

;; Langevin step in Hy
(defn thermal-step [acset dt T seed]
  (let [concepts (parts acset :Concept)
        gradient (compute-relational-gradient acset)
        noise (gay-randn seed (len concepts))]
    (for [c concepts]
      (setv (. acset [:position c])
            (+ (. acset [:position c])
               (* (- dt) (get gradient c))
               (* (sqrt (* 2 T dt)) (get noise c)))))))

;; Run to equilibrium
(defn thermal-equilibrate [acset T n-steps seed]
  (for [step (range n-steps)]
    (thermal-step acset 0.01 T (gay-split se