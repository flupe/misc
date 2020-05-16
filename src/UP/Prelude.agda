{-# OPTIONS --cubical #-}
module UP.Prelude where

open import Agda.Primitive
-- open import Agda.Primitive.Cubical
--   renaming ( primTransp to transp
--            ; primINeg to ~_
--            ; primIMin to _∧_
--            ; primIMax to _∨_
--            ; primHComp to hcomp
--            ; primComp to comp
--            ) public

open import Cubical.Foundations.Prelude hiding (_∎; _≡⟨_⟩_) renaming (_∙_ to trans) public
open import Cubical.Foundations.Equiv.Base renaming (idEquiv to ≃-refl) public
open import Cubical.Foundations.Univalence public
open import Agda.Builtin.Sigma

variable i j k : Level

infixr -1 _$_


id : {A : Set i} → A → A
id x = x

const : {A : Set i} → A → {B : Set j} → B → A
const x _ = x

_$_ : {A : Set i} {P : A → Set j} (f : ∀ x → P x) (x : A) → P x
f $ x = f x

_×_ : (A B : Set i) → Set i
A × B = Σ A (const B)

case_of_ : {A : Set i} {P : A → Set j} (x : A) → ((x : A) → P x) → P x
case x of f = f x

_∘_ : {A : Set i} {P : A → Set j} {Q : {x : A} → P x → Set k}
      (g : {x : A} → (y : P x) → Q y) (f : (x : A) → P x)
    → (x : A) → Q (f x)
_∘_ g f x = g (f x)


[_]_≡_ : {A B : Set i} (E : A ≡ B) → A → B → Set i
[ E ] x ≡ y = PathP (λ i → E i) x y

≡pred : {A B : Set i} → A ≡ B → (A → Set j) ≡ (B → Set j)
≡pred {j = j} A≡B i = A≡B i → Set j


postulate
  funExt′ : {A B : Set i} (A≡B : A ≡ B)
            {P : A → Set j} {Q : B → Set j}
          → (∀ {x y} → [ A≡B ] x ≡ y → P x ≡ Q y)
          → [ ≡pred A≡B ] P ≡ Q


-- rip-off from the stdlib, but for cubical
module ≡-Reasoning {A : Set i} where
  infix 3 _∎
  infixr 2 _≡⟨⟩_ step-≡ step-≡˘
  infix 1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ y≡z x≡y = trans x≡y y≡z

  step-≡˘ : ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
  step-≡˘ _ y≡z y≡x = trans (sym y≡x) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl

  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
