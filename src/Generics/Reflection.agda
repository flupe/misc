module Generics.Reflection where

open import Agda.Builtin.Reflection
open import Builtin.Reflection

open import Tactic.Reflection
open import Tactic.Reflection.DeBruijn
open import Tactic.Reflection.Substitute

open import Generics.Prelude
open import Generics.Desc

import Agda.Builtin.Unit
open Agda.Builtin.Unit


record HasDesc {a} {I : Set a} (A : I → Set a) : Set (lsuc a) where
  field
    n : Nat
    D : Desc {a} I n

    to   : ∀ {i} → A i → μ {a} D i
    from : {i : I} → μ D i → A i

    to∘from : ∀ {i} (x : μ D i) → to (from x) ≡ x
    from∘to : ∀ {i} (x : A i)   → from (to x) ≡ x

hr : ∀ {a} {A : Set a} → A → Arg A
hr t = arg (arg-info hidden relevant) t

vr : ∀ {a} {A : Set a} → A → Arg A
vr t = arg (arg-info visible relevant) t

uhr : Arg Term
uhr = hr unknown

uvr : Arg Term
uvr = vr unknown

last : List (Arg Term) → Arg Term
last [] = vr (con (quote Agda.Builtin.Unit.tt) [])
last (x ∷ []) = x
last (x ∷ xs) = last xs

-- | Unwraps the value of a Maybe A into TC A,
-- | fails with given error message if there is no value.
unwrap : ∀ {a} {A : Set a} → String → Maybe A → TC A
unwrap msg nothing  = typeError (strErr msg ∷ [])
unwrap _   (just x) = returnTC x

mkCon : Name → Nat → Type → TC Term
mkCon t nb (def f args)  = return (con (quote ConDesc.κ) (last args ∷ []))
mkCon t nb (pi (arg i a) (abs n b)) = do
 case a of λ where
   (def f args) →
     case (t == f) of λ where
         (yes _) → do
              b′ ← mkCon t nb b
                   >>= unwrap "Constructor uses recursive value as argument."
                     ∘ strengthen 1
              return (con (quote ConDesc.ι) (last args ∷ vr b′ ∷ []))
         (no  _) → do
              b′ ← mkCon t nb b
              return (con (quote ConDesc.π) (vr a ∷ vr (lam visible (abs n b′)) ∷ []))
   _ → do b′ ← mkCon t nb b
          return (con (quote ConDesc.π) (vr a ∷ vr (lam visible (abs n b′)) ∷ []))

mkCon _ _ _ = typeError (strErr "Cannot convert type to constructor description." ∷ [])

specialize : Type → List (Arg Term) → TC Type
specialize xt []       = return xt
specialize (pi (arg i a) (abs n b)) (arg _ x ∷ xs) with maybeSafe x
... | just xsafe = specialize (substTerm (xsafe ∷ []) b) xs
... | nothing    = typeError (strErr "Trying to specialize with an unsafe term." ∷ [])
specialize _ _   = typeError (strErr "Ill-formed constructor type." ∷ [])

mkDesc : Name → List (Arg Term) → Nat → List Name → TC Term
mkDesc t params nb [] = return (con (quote Vec.[]) [])
mkDesc t params nb (x ∷ xs) = do
  xt  ← getType x
  x′  ← specialize xt params >>= mkCon t nb
  xs′ ← mkDesc t params nb xs
  return (con (quote Vec._∷_) (vr x′ ∷ vr xs′ ∷ []))

macro 
  deriveDesc : Term → Term → TC ⊤
  deriveDesc (def n params) hole = do
    x ← getDefinition n
    case x of λ where
      (data-type pars cs) → mkDesc n params pars cs >>= unify hole
      _ → typeError (strErr "Given argument is NOT a datatype." ∷ [])
  deriveDesc _ _ = typeError (strErr "Given argument is NOT a datatype." ∷ [])
