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

data VecAll {a b} {A : Set a} (P : A → Set b) : {n : Nat} → Vec A n → Set (a ⊔ b) where
  []  : VecAll P []
  _∷_ : ∀ {n x xs} (p : P x) (ps : VecAll P {n} xs) → VecAll P (x ∷ xs)

data ⋆ {a} : Set a where
  ∗ : ⋆

lookupAll : ∀ {a b n} {A : Set a} {P : A → Set b} {xs} (ps : VecAll P xs) (k : Fin n) → P (indexVec xs k)
lookupAll (p ∷ ps) zero    = p
lookupAll (p ∷ ps) (suc k) = lookupAll ps k
