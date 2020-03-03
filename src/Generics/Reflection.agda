{-# OPTIONS --cumulativity #-}

module Generics.Reflection where

open import Generics.Prelude
open import Generics.Desc


record HasDesc {a} {I : Set (lsuc a)} (A : I → Set a) : Set (lsuc a) where
  field
    n : Nat
    D : Desc {a} I n

    to   : ∀ {i} → A i → μ {a} D i
    from : {i : I} → μ D i → A i

    to∘from : ∀ {i} (x : μ D i) → _≡_ {a = lsuc a} (to (from x)) x
    from∘to : ∀ {i} (x : A i) → _≡_ {a = lsuc a} (from (to x)) x

