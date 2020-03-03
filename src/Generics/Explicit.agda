module Generics.Explicit where

open import Prelude hiding (abs)
open import Tactic.Reflection

{-# TERMINATING #-}
explicitify : Type → Term → TC Term
explicitify t u = reduce t >>= λ where
  (pi (dom@(arg i@(arg-info vis rel) a)) (abs s b)) → do
    let u' = safeApply (weaken 1 u) [ arg i (safe (var 0 []) _) ]
    u'' ← extendContext dom (explicitify b u')
    return (lam visible (abs s u''))
  _ → return u

macro
  makeExplicit : Term → Term → TC ⊤
  makeExplicit u hole = do
    t ← inferType hole
    t-impl ← inferType u
    u' ← explicitify t-impl u
    unify hole u'

postulate
  f : {x : Nat} (y : Nat) {z : Nat} → Nat

test : _
test = makeExplicit f
