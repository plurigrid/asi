{- Ordered Locale: Core Definitions
   
   Implements Heunen-style ordered locales with bridge types
   for modeling causal structure in topological spaces.
   
   Bridge types model the "way below" relation U ≪ V in the locale.
   
   Trit: +1 (PLUS/GENERATOR)
   GF(3): Conserved by construction
-}

{- Directed interval (the walking arrow 0 → 1) -}
def 𝟚 : Type := data [
  | zero.
  | one.
]

{- Ordering on 𝟚: zero ≤ one -}
def 𝟚_leq (a b : 𝟚) : Type := match a [
  | zero. ↦ Unit
  | one. ↦ match b [
    | zero. ↦ Empty
    | one. ↦ Unit
  ]
]

{- Unit type for trivial witnesses -}
def Unit : Type := data [ | tt. ]

{- Empty type (no inhabitants) -}
def Empty : Type := data []

{- Open sets in the ordered locale -}
def Open : Type := 𝟚 → Type

{- Bridge type: directed path from A to B
   This models U ≪ V (way below) in the ordered locale.
   A bridge is a function from the directed interval
   with boundary conditions. -}
def Bridge (A B : Type) : Type := sig (
  path : 𝟚 → Type,
  start : path zero. → A,
  end : B → path one.
)

{- Witness that U is way-below V (U ≪ V) -}
def WayBelow (U V : Open) : Type := sig (
  bridge : (t : 𝟚) → Open,
  at_zero : (x : 𝟚) → bridge zero. x → U x,
  at_one : (x : 𝟚) → V x → bridge one. x,
  directed : (s t : 𝟚) → 𝟚_leq s t → (x : 𝟚) → bridge s x → bridge t x
)

{- Frame operations -}

{- Meet (intersection) of opens -}
def meet (U V : Open) : Open := λ x ↦ sig (
  left : U x,
  right : V x
)

{- Join (union) of opens - using sum type -}
def Sum (A B : Type) : Type := data [
  | inl. (a : A)
  | inr. (b : B)
]

def join (U V : Open) : Open := λ x ↦ Sum (U x) (V x)

{- Top open (whole space) -}
def top_open : Open := λ x ↦ Unit

{- Bottom open (empty set) -}
def bot_open : Open := λ x ↦ Empty

{- Inclusion of opens -}
def Included (U V : Open) : Type := (x : 𝟚) → U x → V x

{- Heyting implication: V ⇒ W is the largest U such that U ∧ V ⊆ W -}
def heyting_impl (V W : Open) : Open := λ x ↦ 
  (p : V x) → W x

{- Heyting negation -}
def heyting_neg (U : Open) : Open := heyting_impl U bot_open

{- Up-closure (causal future): all points reachable from U -}
def up_closure (U : Open) : Open := λ y ↦ sig (
  witness : 𝟚,
  source : U witness,
  reach : 𝟚_leq witness y
)

{- Down-closure (causal past): all points that can reach into U -}
def down_closure (U : Open) : Open := λ x ↦ sig (
  target : 𝟚,
  destination : U target,
  reach : 𝟚_leq x target
)

{- Open cone condition: U is upward-directed
   For any two points in U, there exists a common upper bound in U -}
def OpenCone (U : Open) : Type := sig (
  apex : 𝟚,
  apex_in_U : U apex,
  cone_property : (x y : 𝟚) → U x → U y → 
    sig (
      upper : 𝟚,
      upper_in_U : U upper,
      x_leq_upper : 𝟚_leq x upper,
      y_leq_upper : 𝟚_leq y upper
    )
)

{- Interpolation property: key for ordered locales
   If U ≪ V then there exists W with U ≪ W ≪ V -}
def Interpolates (U V : Open) (witness : WayBelow U V) : Type := sig (
  W : Open,
  U_below_W : WayBelow U W,
  W_below_V : WayBelow W V
)

{- Approximation: V is the join of all U ≪ V -}
def Approximates (V : Open) : Type := 
  (x : 𝟚) → V x → sig (
    U : Open,
    way_below : WayBelow U V,
    x_in_U : U x
  )

{- Ordered locale axiom: every open is approximated -}
def OrderedLocaleAxiom : Type := (V : Open) → Approximates V

{- Bridge composition: if we have A →bridge B and B →bridge C,
   we get A →bridge C -}
def bridge_compose 
  (A B C : Type) 
  (ab : Bridge A B) 
  (bc : Bridge B C) 
  : Bridge A C := (
  path := λ t ↦ match t [
    | zero. ↦ ab .path zero.
    | one. ↦ bc .path one.
  ],
  start := ab .start,
  end := bc .end
)

{- Identity bridge -}
def bridge_id (A : Type) : Bridge A A := (
  path := λ t ↦ A,
  start := λ a ↦ a,
  end := λ a ↦ a
)

{- Directed frame homomorphism preserves order -}
def DirectedFrameHom (f : Open → Open) : Type := sig (
  preserves_meet : (U V : Open) (x : 𝟚) → 
    f (meet U V) x → meet (f U) (f V) x,
  preserves_join : (U V : Open) (x : 𝟚) → 
    f (join U V) x → join (f U) (f V) x,
  preserves_way_below : (U V : Open) → 
    WayBelow U V → WayBelow (f U) (f V)
)
