{-# OPTIONS --cumulativity #-}

module Generics.Reflection where

open import Agda.Builtin.Reflection
open import Builtin.Reflection

open import Tactic.Reflection
open import Tactic.Reflection.DeBruijn

open import Generics.Prelude
open import Generics.Desc

import Agda.Builtin.Unit
open Agda.Builtin.Unit

record HasDesc {a} {I : Set (lsuc a)} (A : I → Set a) : Set (lsuc a) where
  field
    n : Nat
    D : Desc {a} I n

    to   : ∀ {i} → A i → μ {a} D i
    from : {i : I} → μ D i → A i

    to∘from : ∀ {i} (x : μ D i) → _≡_ {a = lsuc a} (to (from x)) x
    from∘to : ∀ {i} (x : A i) → _≡_ {a = lsuc a} (from (to x)) x


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

unwrap : ∀ {a} {A : Set a} → Maybe A → TC A
unwrap nothing  = typeError (strErr "TODO" ∷ [])
unwrap (just x) = returnTC x

mkCon : Name → Nat → Type → TC Term
mkCon t nb (def f args)  = return (con (quote ConDesc.κ) (last args ∷ []))
mkCon t nb (pi (arg i a) (abs n b)) = do
 case a of λ where
   (def f args) →
     case (t == f) of λ where
         (yes _) → do
              b′ ← mkCon t nb b
              b′ ← unwrap (strengthen 1 b′)
              return (con (quote ConDesc.ι) (last args ∷ vr b′ ∷ []))
         (no  _) → do
              b′ ← mkCon t nb b
              return (con (quote ConDesc.π) (vr a ∷ vr (lam visible (abs n b′)) ∷ []))
   _ → do b′ ← mkCon t nb b
          return (con (quote ConDesc.π) (vr a ∷ vr (lam visible (abs n b′)) ∷ []))

mkCon _ _ _ = typeError (strErr "Cannot convert type to constructor description." ∷ [])


mkDesc : Name → Nat → List Name → TC Term
mkDesc t nb [] = return (con (quote Vec.[]) [])
mkDesc t nb (x ∷ xs) = do
  x′ ← getType x >>= mkCon t nb
  xs′ ← mkDesc t nb xs
  return (con (quote Vec._∷_) (vr x′ ∷ vr xs′ ∷ []))


macro 
  deriveDesc : Name → Term → TC ⊤
  deriveDesc n hole = do
    x ← getDefinition n
    case x of λ where
      (data-type pars cs) → mkDesc n pars cs >>= unify hole
      _ → typeError (strErr "Given argument is NOT a datatype." ∷ [])


