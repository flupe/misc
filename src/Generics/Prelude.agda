{-# OPTIONS --safe #-}
module Generics.Prelude where

open import Agda.Primitive        public
open import Agda.Builtin.Unit     public
open import Agda.Builtin.Sigma    public
open import Agda.Builtin.Nat      public hiding (_==_)
open import Agda.Builtin.List     public
open import Agda.Builtin.Equality public

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

const : ∀ {a b} {A : Set a} → A → {B : Set b} → B → A
const a b = a

infixr 10 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ {x} → B x → Set c}
      (g : ∀ {x} → (y : B x) → C y) (f : (x : A) → B x)
    → (x : A) → C (f x)
_∘_ g f x = g (f x)

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infixr 20 _×_

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A λ _ → B


data Fin : Nat → Set where
  ze : ∀ {n} → Fin (suc n)
  su : ∀ {n} → Fin n → Fin (suc n)

data Vec {a} (A : Set a) : Nat → Set a where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

lookup : ∀ {a n} {A : Set a} → Vec A n → Fin n → A
lookup (x ∷ xs) ze     = x
lookup (x ∷ xs) (su n) = lookup xs n


record Monad {i j} (M : Set i → Set j) : Set (lsuc (i ⊔ j)) where
  field
    return : {A : Set i} → A → M A
    _>>=_   : {A B : Set i} → M A → (A → M B) → M B
open Monad {{...}}

_>>_ : ∀ {i j} {A B : Set i} {M : Set i → Set j} {{_ : Monad M}}
     → (a : M A) (b : M B) → M B
a >> b = a >>= (const b)

data Lift {a b} (A : Set a) : Set (a ⊔ b) where
  lift : A → Lift A

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl
