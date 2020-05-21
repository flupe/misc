{-# OPTIONS --safe --without-K #-}

open import Generics.Prelude

module Generics.Prelude.Properties (Eq : Equality) where

open Equality Eq


lookupTabulate : ∀ {a n} {A : Set a} (f : Fin n → A)
               → (k : Fin n) → lookup (tabulate f) k ≡ f k
lookupTabulate {n = suc n} f zero    = refl
lookupTabulate {n = suc n} f (suc k) = lookupTabulate (f ∘ suc) k
