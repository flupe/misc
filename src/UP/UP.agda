{-# OPTIONS --cubical #-}

module UP.UP where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.List

open import UP.Prelude public


-- ·⋈·
------------------------------------------------------------

record _⋈_ (A B : Set i) : Set (lsuc i) where
  constructor UR
  field
    ur : A → B → Set i
open _⋈_ public

_≈_ : {A B : Set i} ⦃ E : A ⋈ B ⦄ → A → B → Set i
_≈_ ⦃ E ⦄ x y = ur E x y

⋈-refl : (A : Set i) → A ⋈ A
⋈-refl _ = UR _≡_

⋈-sym : {A B : Set i} → A ⋈ B → B ⋈ A
⋈-sym RAB = UR (λ b a → ur RAB a b)

⋈-comp : {A B C : Set i} → A ⋈ B → B ⋈ C → A ⋈ C
⋈-comp {B = B} RAB RBC = UR (λ a c → Σ _ λ b → ur RAB a b × ur RBC b c)


-- Set ⋈ Set
------------------------------------------------------------

record UR-Set (A B : Set i) : Set (lsuc i) where
  field
    rel : A ⋈ B
    eq  : A ≡ B
    coh : ur rel ≡ [ eq ]_≡_
open UR-Set public

instance
  ⋈-Set : Set i ⋈ Set i
  ⋈-Set = UR UR-Set

≡⇒≈ : {A B : Set i} → A ≡ B → A ≈ B
≡⇒≈ A≡B = record
  { rel = UR [ A≡B ]_≡_
  ; eq  = A≡B
  ; coh = refl
  }

≃⇒≈ : {A B : Set i} → A ≃ B → A ≈ B
≃⇒≈ = ≡⇒≈ ∘ ua


-- (∀ x → P x) ⋈ (∀ y → Q y)
------------------------------------------------------------

∀≡∀ : {A B : Set i} (A≡B : A ≡ B)
    → {P : A → Set j} {Q : B → Set j}
    → (P=Q : ∀ {a b} (H : [ A≡B ] a ≡ b) → P a ≡ Q b)
    → (∀ a → P a) ≡ (∀ b → Q b)
∀≡∀ A≡B P=Q i = (x : A≡B i) → funExt′ A≡B P=Q i x 

⋈-∀ : ∀ {A B : Set i} (A⋈B : A ⋈ B)
    → {P : A → Set j} {Q : B → Set j}
    → (P≈Q : ∀ {a b} (H : ur A⋈B a b) → P a ⋈ Q b)
    → (∀ a → P a) ⋈ (∀ b → Q b)
⋈-∀ A⋈B P≈Q = UR (λ f g → ∀ {x y} (H : ur A⋈B x y) → ur (P≈Q H) (f x) (g y))

postulate
  ∀≈∀ : ∀ {A B : Set i} (A≈B : A ≈ B)
      → {P : A → Set j} {Q : B → Set j}
      → (P≈Q : ∀ {a b} (H : ur (rel A≈B) a b) → P a ≈ Q b)
      → (∀ a → P a) ≈ (∀ b → Q b)
{-
∀≈∀ A≈B P≈Q = record
  { rel = ⋈-∀ (rel A≈B) (rel ∘ P≈Q)
  ; eq  = ∀≡∀ (eq A≈B)  {!eq ∘ P≈Q!}
  ; coh = {!!}
  } -}

-- List A ⋈ List B
------------------------------------------------------------

List≡List : {A B : Set i} → A ≡ B → List A ≡ List B
List≡List A≡B i = List (A≡B i)

instance
  -- might be too easy
  ⋈-List : {A B : Set i} ⦃ R : A ≈ B ⦄ → List A ⋈ List B
  ⋈-List ⦃ R ⦄ = UR [ List≡List (eq R) ]_≡_


-- Σ A P ⋈ Σ B Q
------------------------------------------------------------

Σ≡Σ : {A B : Set i} (A≡B : A ≡ B)
      {P : A → Set j} {Q : B → Set j}
    → (∀ {a b} (H : [ A≡B ] a ≡ b) → P a ≡ Q b)
    → Σ A P ≡ Σ B Q
Σ≡Σ A≡B P=Q i = Σ (A≡B i) (funExt′ A≡B P=Q i)


-- Set i ≈ Set i
------------------------------------------------------------
postulate
  test : {A B : Set i} → UR-Set A B ≃ (A ≡ B)

-- test .fst = eq
-- test .snd .equiv-proof A≡B
--   = (record { rel = UR [ A≡B ]_≡_ ; eq = A≡B ; coh = refl } , refl)
--   , λ where (A⋈B , eqA⋈B) → {!!}

Set≈Set : Set i ≈ Set i
Set≈Set .rel = ⋈-Set
Set≈Set .eq  = refl
Set≈Set .coh i A B = ua (test {A = A} {B}) i


-- black box fundamental property
------------------------------------------------------------

■ : {A B : Set i} (A≈B : A ≈ B)
  → ∀ x → ur (rel A≈B) x (transport (eq A≈B) x)
■ A≈B x = transport (λ i → coh A≈B (~ i) x (transport (eq A≈B) x))
                    (transport-filler (eq A≈B) x)
