---
name: cats-focus-monad
description: "Cats Focus + Monad: Lawful composition for effect management"
metadata:
  trit: 0
  seed: 1069
  version: "2.13"
---
# Cats Focus + Monad

> *flatMap that shit*

## Core Laws

```scala
// Monad Laws
pure(a).flatMap(f) === f(a)                    // Left identity
fa.flatMap(pure) === fa                        // Right identity  
fa.flatMap(f).flatMap(g) === fa.flatMap(a => f(a).flatMap(g))  // Associativity
```

## Focus (Monocle Optics)

```scala
import monocle.Focus
import monocle.syntax.all._

case class State(entropy: Long, archive: List[HyDefn])

// Lens into nested structure
val entropyLens = Focus[State](_.entropy)
val archiveLens = Focus[State](_.archive)

// Compose
state.focus(_.archive).modify(_ :+ newDefn)
```

## Monad Composition Pattern

```scala
import cats.Monad
import cats.syntax.all._

def godelStep[F[_]: Monad](state: State): F[State] =
  for {
    entropy  <- nextEntropy[F](state.entropy)
    hydefn   <- generateHyDefn[F](entropy)
    proven   <- attemptProof[F](hydefn)
    newState <- if (proven) 
                  Monad[F].pure(state.focus(_.archive).modify(_ :+ hydefn))
                else 
                  Monad[F].pure(state)
  } yield newState
```

## GF(3) Trit

```
cats-focus-monad (0) ⊕ cats-effect (+1) ⊕ validation (-1) = 0 ✓
```

## Commands

```bash
# Add to build.sbt
libraryDependencies ++= Seq(
  "org.typelevel" %% "cats-core" % "2.13.0",
  "dev.optics" %% "monocle-core" % "3.3.0",
  "dev.optics" %% "monocle-macro" % "3.3.0"
)
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
