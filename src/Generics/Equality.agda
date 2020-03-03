module Generics.Equality where

open import Generics.Prelude

data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
  refl : x ≅ x

sym : ∀ {a} {A : Set a} {x y : A}
    → x ≅ y → y ≅ x
sym refl = refl

cong : ∀ {a b} {A : Set a} {B : Set b}
     → ∀ {x y} (f : A → B) (e : x ≅ y) → f x ≅ f y
cong f refl = refl

trans : ∀ {ℓ} {A B C : Set ℓ} {x : A} {y : B} {z : C}
      → x ≅ y → y ≅ z → x ≅ z
trans refl refl = refl

subst : ∀ {a b} {A : Set a} (B : A → Set b) {x y} → x ≅ y → B x → B y
subst B refl bx = bx

_==_ : ∀ {a b} {A : Set a} {B : A → Set b}
     → (f g : (x : A) → B x) → Set (a ⊔ b)
f == g = ∀ x → f x ≅ g x

postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
         → f == g → f ≅ g

cong2 : ∀ {a b} {A : Set a} {B : A → Set b} 
      → {f g : (x : A) → B x}
      → f ≅ g
      → ∀ {x y}
      → x ≅ y → f x ≅ g y
cong2 refl refl = refl
