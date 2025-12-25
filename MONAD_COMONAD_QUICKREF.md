# Monad/Comonad GF(3) Quick Reference

## Trit Assignments

| Structure | Trit | Role | Dual |
|-----------|------|------|------|
| **Free** | +1 | Generator | Cofree |
| **Cofree** | -1 | Observer | Free |
| **Just/Identity** | 0 | Neutral | Identity |
| **Maybe (Nothing)** | -1 | Failure | — |
| **IO** | +1 | World effect | — |
| **State (get)** | -1 | Extract | put |
| **State (put)** | +1 | Generate | get |
| **State (modify)** | 0 | Transform | — |
| **Reader** | 0 | Transport | Env |
| **Writer** | +1 | Accumulate | Traced |
| **Store** | -1 | Focus | — |
| **Env** | -1 | Context | Reader |
| **Traced** | -1 | History | Writer |
| **Cont** | 0 | Control | — |
| **List** | len%3 | Nondeterminism | — |

## Core Laws

```
L1: trit(m >>= f) ≡ trit(m) + trit(f(a)) (mod 3)
L2: trit(extend f w) ≡ trit(w) + trit(f) (mod 3)
L3: Free (+1) runs-on Cofree (-1) = 0 ✓
L4: Adjoint pairs sum to 0
```

## Valid Skill Triads

```
+1: free-monad-gen, unworld, gay-mcp, operad-compose
 0: kan-extensions, dialectica, acsets, glass-bead-game
-1: temporal-coalgebra, sheaf-cohomology, bisimulation-game
```

## Pattern

```
Generator (+1) ⊗ Transporter (0) ⊗ Validator (-1) = 0 ✓
```
