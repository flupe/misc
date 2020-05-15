{-# OPTIONS --cubical #-}

module UP.UP where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.List

open import Agda.Primitive.Cubical renaming (primTransp to transp) public
open import Agda.Builtin.Cubical.Path using (PathP; _≡_) public

variable i j : Level


-- prelude
------------------------------------------------------------

infixr -1 _$_

const : {A : Set i} → A → {B : Set j} → B → A
const x _ = x

_$_ : {A : Set i} {P : A → Set j} (f : ∀ x → P x) (x : A) → P x
f $ x = f x

id : {A : Set i} → A → A
id x = x

_×_ : (A B : Set i) → Set i
A × B = Σ A (const B)

case_of_ : {A : Set i} {P : A → Set j} (x : A) → ((x : A) → P x) → P x
case x of f = f x

instance
  refl : {A : Set i} {x : A} → x ≡ x
  refl {x = x} i = x

[_]_≡_ : {A B : Set i} (E : A ≡ B) → A → B → Set i
[ E ] x ≡ y = PathP (λ i → E i) x y

funExt : {A : Set i} {P Q : A → Set j}
       → (∀ {x y} → x ≡ y → P x ≡ Q y)
       → P ≡ Q
funExt P=Q i x = P=Q {x} refl i

≡pred : {A B : Set i} → A ≡ B → (A → Set j) ≡ (B → Set j)
≡pred {j = j} A≡B i = A≡B i → Set j

postulate
  funExt′ : {A B : Set i} (A≡B : A ≡ B)
            {P : A → Set j} {Q : B → Set j}
          → (∀ {x y} → [ A≡B ] x ≡ y → P x ≡ Q y)
          → [ ≡pred A≡B ] P ≡ Q


-- type-indexed univalent relation ·⋈·
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
open UR-Set

instance
  ⋈-Set : Set i ⋈ Set i
  ⋈-Set = UR UR-Set

postulate
  Set≈Set : Set i ≈ Set i


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
