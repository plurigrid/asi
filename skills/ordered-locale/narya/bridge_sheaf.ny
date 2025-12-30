{- Bridge Sheaf: Sheaves Respecting Bridges
   
   Implements sheaf-theoretic structure on ordered locales
   where restrictions respect the way-below relation.
   
   Key insight: Sheaf sections must be compatible with
   the causal/directed structure of bridges.
-}

import "ordered_locale"
import "gf3"

{- Presheaf on opens -}
def Presheaf : Type := sig (
  section : Open → Type,
  restrict : (U V : Open) → Included V U → section U → section V
)

{- Section over an open set -}
def Section (F : Presheaf) (U : Open) : Type := F .section U

{- Restriction map -}
def restrict 
  (F : Presheaf) 
  (U V : Open) 
  (inc : Included V U) 
  : Section F U → Section F V := 
  F .restrict U V inc

{- Sheaf condition: sections agree on overlaps -}
def SheafCondition (F : Presheaf) : Type := sig (
  {- Gluing: compatible local sections give global section -}
  glue : (U V : Open) 
       → (sU : Section F U) 
       → (sV : Section F V)
       → ((x : 𝟚) → (hU : U x) → (hV : V x) → 
            Id (F .section (λ y ↦ meet U V y)) 
               (restrict F U (meet U V) (λ y p ↦ p .left) sU)
               (restrict F V (meet U V) (λ y p ↦ p .right) sV))
       → Section F (join U V),
  {- Uniqueness: global section determined by locals -}
  unique : (U : Open) (s t : Section F U)
         → ((x : 𝟚) → (h : U x) → 
              Id (F .section (λ y ↦ sig (p : U y, q : Id 𝟚 y x))) 
                 (restrict F U _ (λ y p ↦ (p, refl.)) s)
                 (restrict F U _ (λ y p ↦ (p, refl.)) t))
         → Id (Section F U) s t
)

{- Bridge-respecting presheaf: restrictions compatible with ≪ -}
def BridgePresheaf : Type := sig (
  base : Presheaf,
  directional : (U V : Open) 
              → WayBelow U V 
              → (s : Section base V) 
              → Section base U
)

{- The directional restriction factors through the bridge -}
def DirectionalFactorization (F : BridgePresheaf) : Type :=
  (U V : Open) 
  → (wb : WayBelow U V)
  → (inc : Included U V)
  → (s : Section (F .base) V)
  → Id (Section (F .base) U)
       (restrict (F .base) V U inc s)
       (F .directional U V wb s)

{- Cosheaf: dual notion, sections extend forward -}
def CosheafCondition (F : Presheaf) : Type := sig (
  extend : (U V : Open)
         → Included U V
         → Section F U
         → Section F V,
  compatible : (U V W : Open)
             → (uv : Included U V)
             → (vw : Included V W)
             → (s : Section F U)
             → Id (Section F W)
                  (extend V W vw (extend U V uv s))
                  (extend U W (λ x h ↦ vw x (uv x h)) s)
)

{- Bridge sheaf: combines sheaf and directional structure -}
def BridgeSheaf : Type := sig (
  presheaf : BridgePresheaf,
  sheaf_cond : SheafCondition (presheaf .base),
  {- Directional compatibility: restrictions along bridges preserve gluing -}
  bridge_compat : (U V W : Open)
                → (wb_UV : WayBelow U V)
                → (wb_VW : WayBelow V W)
                → (s : Section (presheaf .base) W)
                → Id (Section (presheaf .base) U)
                     (presheaf .directional U V wb_UV 
                       (presheaf .directional V W wb_VW s))
                     (presheaf .directional U W 
                       (waybelow_compose U V W wb_UV wb_VW) s)
)

{- Composition of way-below witnesses -}
def waybelow_compose 
  (U V W : Open) 
  (uv : WayBelow U V) 
  (vw : WayBelow V W) 
  : WayBelow U W := (
  bridge := λ t ↦ match t [
    | zero. ↦ uv .bridge zero.
    | one. ↦ vw .bridge one.
  ],
  at_zero := uv .at_zero,
  at_one := vw .at_one,
  directed := λ s t leq x h ↦ 
    {- Use transitivity of the bridges -}
    match s [
    | zero. ↦ match t [
      | zero. ↦ h
      | one. ↦ vw .at_one x (uv .at_one x (uv .directed zero. one. tt. x h))
    ]
    | one. ↦ vw .directed s t leq x h
    ]
)

{- Stalk at a point: colimit of sections over opens containing the point -}
def Stalk (F : Presheaf) (x : 𝟚) : Type := sig (
  U : Open,
  x_in_U : U x,
  germ : Section F U
)

{- Stalks equivalent for equivalent germs -}
def StalkEquiv (F : Presheaf) (x : 𝟚) (s t : Stalk F x) : Type := sig (
  W : Open,
  W_sub_U : Included W (s .U),
  W_sub_V : Included W (t .U),
  x_in_W : W x,
  agree : Id (Section F W)
            (restrict F (s .U) W W_sub_U (s .germ))
            (restrict F (t .U) W W_sub_V (t .germ))
)

{- Triadic section: section with GF(3) coloring -}
def TriadicSection (F : Presheaf) (U : Open) : Type := sig (
  section : Section F U,
  color : TriadicColor,
  trit : Trit
)

{- Triadic sheaf: sections carry GF(3) structure -}
def TriadicSheaf : Type := sig (
  sheaf : BridgeSheaf,
  color_section : (U : Open) → TriadicSection (sheaf .presheaf .base) U → Trit,
  {- GF(3) conservation under restriction -}
  conserved : (U V W : Open)
            → (sU : TriadicSection (sheaf .presheaf .base) U)
            → (sV : TriadicSection (sheaf .presheaf .base) V)
            → (sW : TriadicSection (sheaf .presheaf .base) W)
            → GF3Conserved (sU .trit) (sV .trit) (sW .trit)
)

{- Čech cohomology placeholder -}
def CechCohomology (F : BridgeSheaf) (U : Open) (n : Nat) : Type := sig (
  cochains : Nat → Type,
  differential : (k : Nat) → cochains k → cochains (suc. k),
  closed : cochains n → Type,
  exact : cochains n → Type
)
