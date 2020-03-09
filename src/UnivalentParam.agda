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

_∘_ : ∀ {i j} {A B : Set i} {P : B → Set j} (f : (y : B) → P y) (g : A → B)
    → (x : A) → P (g x)
_∘_ f g x = f (g x)


-- Univalent Logical Relation
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


instance
  URSet : ∀ {i} → Set i ⋈ Set i
  URSet = UR URSetdef

  URForallType : ∀ {i} {A B : Set i} ⦃ R : A ⋈ B ⦄
               → (A → Set i) ⋈ (B → Set i)
  URForallType {A = A} {B} =
    UR λ P Q → ∀ x y → x ≈ y → P x ⋈ Q y

  -- URForall : ∀ {i} {A B : Set i} ⦃ RA : A ⋈ B ⦄
  --            {P : A → Set i} {Q : B → Set i}
  --            {RF : (x : A) (y : B) → x ≈ y → P x ⋈ Q y}
  --          → ((x : A) → P x) ⋈ ((y : B) → Q y)
  -- URForall {A = A} {B} {P = P} {Q = Q} {RF = RF} =
  --   UR λ f g → (x : A) (y : B) (H : x ≈ y) → ur (RF x y H) (f x) (g y)

  -- non-dependent function type, let's see if this works
  URArrow : ∀ {i} {A B : Set i} ⦃ RA : A ⋈ B ⦄ {P Q : Set i} ⦃ RF : P ⋈ Q ⦄ 
           → ((x : A) → P) ⋈ ((y : B) → Q)
  URArrow {A = A} {B} =
    UR λ f g → ∀ x y → x ≈ y → f x ≈ g y


CanonicalUR : ∀ {i} {A B : Set i} (E : A ≃ B) → A ≈ B
CanonicalUR E =
  record { rel   = UR (λ a b → a ≡ ↓ ⦃ E ⦄ b)
         ; equiv = E
         ; coh   = λ a b → idEquiv (a ≡ ↓ ⦃ E ⦄ b)
         }

URRefl : ∀ {i} {A : Set i} → A ⋈ A
URRefl {A = A} = UR _≡_


module FundamentalProperties where
  open import Agda.Builtin.Sigma
  
  ≈-refl : ∀ {i} (A : Set i) → A ≈ A
  ≈-refl A =
    record { rel   = URRefl
           ; equiv = idEquiv A
           ; coh   = λ a b → idEquiv (ur URRefl a b)
           }

  Set≈Set : ∀ {ℓ} → Set ℓ ≈ Set ℓ
  Set≈Set {ℓ} =
    record { rel   = URSet
           ; equiv = idEquiv (Set ℓ)
           ; coh   = λ A B → isoToEquiv
               (iso (λ A≈B → ua (equiv A≈B))
                    (λ A≡B → transport (λ i → URSetdef A (A≡B i)) (≈-refl A))
                    (J (λ B A≡B → ua (transport (λ i → A ≃ A≡B i) (idEquiv A)) ≡ A≡B) {!!})
                    (λ A≈B → {!!}))
           }

module Example where

  open import Agda.Builtin.Nat

  data Bin : Set where
    0b     : Bin
    2[1+_] : Bin → Bin
    1+[2_] : Bin → Bin

  succ : Bin → Bin
  succ 0b       = 1+[2 0b ]
  succ 2[1+ x ] = 1+[2 succ x ]
  succ 1+[2 x ] = 2[1+ x ]

  add : Bin → Bin → Bin
  add 0b y = y
  add x 0b = x
  add 2[1+ x ] 2[1+ y ] = 2[1+ succ (add x y) ]
  add 2[1+ x ] 1+[2 y ] = succ 2[1+ (add x y) ]
  add 1+[2 x ] 2[1+ y ] = succ 2[1+ (add x y) ]
  add 1+[2 x ] 1+[2 y ] = succ 1+[2 (add x y) ]

  toℕ : Bin → Nat
  toℕ 0b       = 0
  toℕ 2[1+ x ] = 2 * suc (toℕ x)
  toℕ 1+[2 x ] = suc (2 * toℕ x)

  fromℕ : Nat → Bin
  fromℕ zero    = 0b
  fromℕ (suc x) = succ (fromℕ x)

  +-suc : ∀ n m → n + suc m ≡ suc (n + m)
  +-suc zero m    = refl
  +-suc (suc n) m = cong suc (+-suc n m)

  toℕ-suc : (n : Bin) → toℕ (succ n) ≡ suc (toℕ n)
  toℕ-suc 0b       = refl
  toℕ-suc 2[1+ n ] = cong (suc ∘ (2 *_)) (toℕ-suc n)
  toℕ-suc 1+[2 n ] = cong suc (+-suc (toℕ n) (toℕ n + 0))

  toℕ∘fromℕ : (n : Nat) → toℕ (fromℕ n) ≡ n
  toℕ∘fromℕ 0       = refl
  toℕ∘fromℕ (suc n) = toℕ (succ (fromℕ n))   ≡⟨ toℕ-suc (fromℕ n) ⟩
                      suc (toℕ (fromℕ n))    ≡⟨ cong suc (toℕ∘fromℕ n) ⟩
                      suc n                  ∎

  fromℕ∘toℕ : (n : Bin) → fromℕ (toℕ n) ≡ n
  fromℕ∘toℕ 0b       = refl
  fromℕ∘toℕ 2[1+ n ] = succ (fromℕ (toℕ n + suc (toℕ n + 0))) ≡⟨ cong (succ ∘ fromℕ) (+-suc (toℕ n) _) ⟩
                       {!!}
  fromℕ∘toℕ 1+[2 n ] = {!!}

  instance
    Nat≃Bin : Nat ≃ Bin
    Nat≃Bin = isoToEquiv (iso fromℕ toℕ fromℕ∘toℕ toℕ∘fromℕ)

  Nat≈Bin : Nat ≈ Bin
  Nat≈Bin = CanonicalUR Nat≃Bin

  instance
    URNatBin : Nat ⋈ Bin
    URNatBin = rel Nat≈Bin

  test : (x y : Nat) → x + y ≡ ↓ (add (↑ x) (↑ y))
  test 0 0       = refl
  test 0 (suc y) = sym (toℕ∘fromℕ (suc y))
  test (suc x) 0 = suc (x + 0)    ≡⟨ cong suc (test x 0) ⟩
                   {!!}
  test (suc x) (suc y) = {!!}

  plus≈add : _+_ ≈ add
  plus≈add = λ x₁ x₂ Hx y₁ y₂ Hy → {!!}
