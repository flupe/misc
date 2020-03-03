{-# OPTIONS --cubical --safe #-}

module UnivalentParam where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Cubical.Glue
open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

id : ∀ {i} {A : Set i} → A → A
id x = x

↑ : ∀ {i} {A B : Set i} ⦃ E : A ≃ B ⦄ → A → B
↑ ⦃ E = E ⦄ = fst E

↓ : ∀ {i} {A B : Set i} ⦃ E : A ≃ B ⦄ → B → A
↓ ⦃ E = E ⦄ = invEq E


-- Univalent Logic Relation
record _⋈_ {i} (A B : Set i) : Set (lsuc i) where
  constructor UR
  field
    ur : A → B → Set i
open _⋈_

_≈_ : ∀ {i} {A B : Set i} ⦃ R : A ⋈ B ⦄
    → A → B → Set i
_≈_ ⦃ R ⦄ = ur R


Coh : ∀ {i} {A B : Set i} (R : A ⋈ B) (E : A ≃ B) → Set i
Coh {i} {A} {B} R E = (a : A) → (b : B) → (ur R a b) ≃ (a ≡ ↓ ⦃ E ⦄ b)

record URSetdef {i} (A B : Set i) : Set (lsuc i) where
  field
    rel   : A ⋈ B
    equiv : A ≃ B
    coh   : Coh rel equiv
open URSetdef

URForallSetdef : ∀ {i} {A B : Set i} ⦃ R : A ⋈ B ⦄
               → (P : A → Set i) (Q : B → Set i)
               → Set (lsuc i)
URForallSetdef {A = A} {B} P Q = (x : A) (y : B) → x ≈ y → P x ⋈ Q y

instance
  URSet : ∀ {i} → Set i ⋈ Set i
  URSet = UR URSetdef

  URForallType : ∀ {i} {A B : Set i} ⦃ R : A ⋈ B ⦄
               → (A → Set i) ⋈ (B → Set i)
  URForallType = UR URForallSetdef

  -- URForall : ∀ {i} {A B : Set i} ⦃ RA : A ⋈ B ⦄
  --            {P : A → Set i} {Q : B → Set i}
  --            {RF : (x : A) (y : B) → x ≈ y → P x ⋈ Q y}
  --          → ((x : A) → P x) ⋈ ((y : B) → Q y)
  -- URForall {A = A} {B} {P = P} {Q = Q} {RF = RF} =
  --   UR λ f g → (x : A) (y : B) (H : x ≈ y) → ur (RF x y H) (f x) (g y)

  -- non-dependent setting, let's see if this works
  URArrow : ∀ {i} {A B : Set i} ⦃ RA : A ⋈ B ⦄
             {P : Set i} {Q : Set i} ⦃ RF : P ⋈ Q ⦄ 
           → ((x : A) → P) ⋈ ((y : B) → Q)
  URArrow {A = A} {B} {P = P} {Q} ⦃ RF ⦄ =
    UR λ f g → (x : A) (y : B) (H : x ≈ y) → ur RF (f x) (g y)


CanonicalUR : ∀ {i} {A B : Set i} (E : A ≃ B) → A ≈ B
CanonicalUR E =
  record { rel   = UR (λ a b → a ≡ ↓ ⦃ E ⦄ b)
         ; equiv = E
         ; coh   = λ a b → idEquiv (a ≡ ↓ ⦃ E ⦄ b)
         }


module FundamentalProperties where
  Set≈Set : ∀ {i} → Set i ≈ Set i
  Set≈Set {i} =
    record { rel   = URSet
           ; equiv = idEquiv (Set i)
           ; coh   = λ A B → (λ R → ua (equiv R)) , {!!}
           }


module Example where

  open import Agda.Builtin.Nat
  open import Data.Bin renaming (_+_ to _+Bin_)
  open import Cubical.Foundations.Prelude

  toℕ∘fromℕ : (n : Nat) → toℕ (fromℕ n) ≡ n
  toℕ∘fromℕ 0       = refl
  toℕ∘fromℕ (suc n) = {!!}

  fromℕ∘toℕ : (n : Bin) → fromℕ (toℕ n) ≡ n
  fromℕ∘toℕ 0#      = refl
  fromℕ∘toℕ (bs 1#) = {!!}

  instance
    Nat≃Bin : Nat ≃ Bin
    Nat≃Bin = isoToEquiv (iso fromℕ toℕ fromℕ∘toℕ toℕ∘fromℕ)

  Nat≈Bin : Nat ≈ Bin
  Nat≈Bin = CanonicalUR Nat≃Bin

  instance
    URNatBin : Nat ⋈ Bin
    URNatBin = rel Nat≈Bin

  test : (x y : Nat) → x + y ≡ ↓ (↑ x +Bin ↑ y)
  test 0 0       = refl
  test 0 (suc y) = {!!}
  test (Nat.suc x) y = {!!}

  plus≈add : _+_ ≈ _+Bin_
  plus≈add = λ x₁ x₂ Hx y₁ y₂ Hy → {!!}
