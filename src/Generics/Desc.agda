{-# OPTIONS --cumulativity #-}
module Generics.Desc where

open import Generics.Prelude


record Semantics {a b} (A : Set a) : Set (a ⊔ lsuc b) where
  field
    {⟦⟧-Type} : Set b
    ⟦_⟧ : A → ⟦⟧-Type
open Semantics ⦃ ... ⦄


data ConDesc {ℓ} (I : Set (lsuc ℓ)) : Set (lsuc ℓ) where
  -- poor choice of naming
  κ : (k : I)                           → ConDesc I
  ι : (i : I)     → (D : ConDesc I)     → ConDesc I
  π : (S : Set ℓ) → (D : S → ConDesc I) → ConDesc I

⟦_⟧ᶜ : ∀ {ℓ} {I : Set (lsuc ℓ)} → ConDesc I → (I → Set (lsuc ℓ)) → I → Set (lsuc ℓ)
⟦ ι γ D ⟧ᶜ X i = X γ × ⟦ D ⟧ᶜ X i
⟦ κ k   ⟧ᶜ X i = k ≡ i
⟦ π S D ⟧ᶜ X i = Σ[ s ∈ S ] (⟦ D s ⟧ᶜ X i)

syntax π A (λ s → D) = π[ s ∈ A ] D

instance
  CS : ∀ {ℓ} {I : Set (lsuc ℓ)} → Semantics {b = lsuc (lsuc ℓ)} (ConDesc {ℓ} I)
  CS = record { ⟦_⟧ = ⟦_⟧ᶜ }


Desc : ∀ {ℓ} (I : Set (lsuc ℓ)) → Nat → Set (lsuc ℓ)
Desc {ℓ} I = Vec {lsuc ℓ} (ConDesc I)

⟦_⟧ᵈ : ∀ {ℓ n} {I : Set (lsuc ℓ)} → Desc I n → (I → Set (lsuc ℓ)) → I → Set (lsuc ℓ)
⟦_⟧ᵈ {n = n} D X i = Σ[ k ∈ Fin n ] (⟦ indexVec D k ⟧ X i)

instance
  DS : ∀ {ℓ n} {I : Set (lsuc ℓ)} → Semantics {b = lsuc (lsuc ℓ)} (Desc {ℓ} I n)
  DS = record { ⟦_⟧ = ⟦_⟧ᵈ }


data μ {ℓ n} {I : Set (lsuc ℓ)} (D : Desc I n) (γ : I) : Set (lsuc ℓ) where
  ⟨_⟩ : ⟦ D ⟧ (μ D) γ → μ D γ

