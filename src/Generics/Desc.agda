module Generics.Desc where

open import Generics.Prelude
open import Prelude.Unit
open import Prelude.Vec

record Semantics {a b} (A : Set a) : Set (a ⊔ lsuc b) where
  field
    {⟦⟧-Type} : Set b
    ⟦_⟧ : A → ⟦⟧-Type
open Semantics ⦃ ... ⦄


data ConDesc {ℓ} (I : Set ℓ) : Set (lsuc ℓ) where
  -- poor choice of naming
  κ : (k : I)                           → ConDesc I
  ι : (i : I)     → (D : ConDesc I)     → ConDesc I
  π : (S : Set ℓ) → (D : S → ConDesc I) → ConDesc I

⟦_⟧ᶜ : ∀ {ℓ} {I : Set ℓ} → ConDesc I → (I → Set ℓ) → I → Set ℓ
⟦ ι γ D ⟧ᶜ X i = X γ × ⟦ D ⟧ᶜ X i
⟦ κ k   ⟧ᶜ X i = k ≡ i
⟦ π S D ⟧ᶜ X i = Σ[ s ∈ S ] (⟦ D s ⟧ᶜ X i)

syntax π A (λ s → D) = π[ s ∈ A ] D

instance
  CS : ∀ {ℓ} {I : Set ℓ} → Semantics {b = lsuc ℓ} (ConDesc {ℓ} I)
  CS = record { ⟦_⟧ = ⟦_⟧ᶜ }

Desc : ∀ {ℓ} (I : Set ℓ) → Nat → Set (lsuc ℓ)
Desc {ℓ} I = Vec (ConDesc I)

⟦_⟧ᵈ : ∀ {ℓ n} {I : Set ℓ} → Desc I n → (I → Set ℓ) → I → Set ℓ
⟦_⟧ᵈ {n = n} D X i = Σ[ k ∈ Fin n ] (⟦ indexVec D k ⟧ X i)

instance
  DS : ∀ {i n} {I : Set i} → Semantics (Desc {i} I n)
  DS = record { ⟦_⟧ = ⟦_⟧ᵈ }

data μ {i n} {I : Set i} (D : Desc I n) (γ : I) : Set i where
  ⟨_⟩ : ⟦ D ⟧ (μ D) γ → μ D γ


data VecAll {a b} {A : Set a} (P : A → Set b) : {n : Nat} → Vec A n → Set (a ⊔ b) where
  []  : VecAll P []
  _∷_ : ∀ {n x xs} (p : P x) (ps : VecAll P {n} xs) → VecAll P (x ∷ xs)

lookupAll : ∀ {a b n} {A : Set a} {P : A → Set b} {xs} (ps : VecAll P xs) (k : Fin n) → P (indexVec xs k)
lookupAll (p ∷ ps) zero    = p
lookupAll (p ∷ ps) (suc k) = lookupAll ps k

ConInstance : ∀ {i j} (M : Set i → Set j) {I : Set i} (C : ConDesc I) → Set (i ⊔ j)
ConInstance M (κ k)   = ⊤′
ConInstance M (ι i D) = ConInstance M D
ConInstance M (π S D) = M S × ((s : S) → ConInstance M (D s))

DescInstance : ∀ {i j} (M : Set i → Set j) {n} {I : Set i} (D : Desc I n) → Set (lsuc i ⊔ j)
DescInstance M {n} D = VecAll (ConInstance M) D
