module Generics.Prelude where

open import Agda.Primitive        public
open import Agda.Builtin.Equality public

open import Prelude hiding (abs)  public
open import Prelude.Equality      public

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

data Lift {a b} (A : Set a) : Set (a ⊔ b) where
  lift : A → Lift A

