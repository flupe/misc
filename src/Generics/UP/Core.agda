{-# OPTIONS --cubical --without-K #-}
module Generics.UP.Core where

open import Generics.UP.Prelude


record _⋈_ (A B : Set i) : Set (lsuc i) where
  field
    ur : A → B → Set i
    eq : A ≃ B
    co : ∀ x y → ur x (eq .fst y) ≃ (x ≡ y)
open _⋈_ public

[_]_≈_ : {A B : Set i} → A ⋈ B → A → B → Set i
[ A⋈B ] x ≈ y = ur A⋈B x y

_≈_ : {A B : Set i} ⦃ A⋈B : A ⋈ B ⦄ → A → B → Set i
_≈_ ⦃ A⋈B ⦄ = [ A⋈B ]_≈_


-- transport
-------------------------------------------------------------

module _ {A B : Set i} (A⋈B : A ⋈ B) where

  infixr 5 _↑_ _↓_

  _↑_ : A → B
  _↑_ = A⋈B .eq .fst

  _↓_ : B → A
  _↓_ = invEq (A⋈B .eq)


  -- black box fundamental property
  
  ■ : ∀ x → [ A⋈B ] x ≈ (_↑_ x)
  ■ x = invEq (co A⋈B x x) refl

  ■′ : ∀ y → [ A⋈B ] _↓_ y ≈ y
  ■′ y = transport (λ i → [ A⋈B ] _↓_ y ≈ retEq (eq A⋈B) y i) (■ (_↓_ y))

  _↑↓_ : ∀ y → _↑_ (_↓_ y) ≡ y
  _↑↓_ = retEq (eq A⋈B)

  _↓↑_ : ∀ x → _↓_ (_↑_ x) ≡ x
  _↓↑_ = secEq (eq A⋈B)

  ⋈⇒≃ : A ≃ B
  ⋈⇒≃ = eq A⋈B

  ⋈⇒≡ : A ≡ B
  ⋈⇒≡ = ua ⋈⇒≃

≃⇒⋈ : {A B : Set i} → A ≃ B → A ⋈ B
≃⇒⋈ A≃B .ur x y = x ≡ invEq A≃B y
≃⇒⋈ A≃B .eq = A≃B
≃⇒⋈ A≃B .co x x′ = todo


-- Set i ⋈ Set i
-------------------------------------------------------------

instance
  Set⋈Set : Set i ⋈ Set i
  Set⋈Set .ur = _⋈_
  Set⋈Set {i} .eq = ≃-refl (Set i)
  Set⋈Set .co A B = todo


-- (∀ a → P a) ⋈ (∀ b → Q b)
-------------------------------------------------------------

∀⋈∀ : {A B : Set i} (A⋈B : A ⋈ B)
    → {P : A → Set j} {Q : B → Set j}
    → (P≈Q : ∀ {a b} (H : ur A⋈B a b) → P a ⋈ Q b)
    → (∀ a → P a) ⋈ (∀ b → Q b)

∀⋈∀ A⋈B P≈Q .ur f g = ∀ {x y} ⦃ x≈y : [ A⋈B ] x ≈ y ⦄ → [ P≈Q x≈y ] f x ≈ g y 
∀⋈∀ A⋈B P≈Q .eq .fst f y = P≈Q (■′ A⋈B y) ↑ f (A⋈B ↓ y)
∀⋈∀ A⋈B P≈Q .eq .snd  = todo
∀⋈∀ A⋈B P≈Q .co = todo


instance
  →⋈→ : {A B : Set i} ⦃ A⋈B : A ⋈ B ⦄
        {C D : Set j} ⦃ C⋈D : C ⋈ D ⦄
      → (A → C) ⋈ (B → D)
  →⋈→ ⦃ A⋈B ⦄ ⦃ C⋈D ⦄ = ∀⋈∀ A⋈B (const C⋈D)
