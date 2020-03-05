module Generics.Constructions where

open import Generics.Prelude
open import Generics.Desc
open import Generics.Reflection


module Induction {i j n} {I : Set i} (D : Desc I n) (P : ∀ {γ} → μ D γ → Set j) where

  ConAll : ∀ {γ} {C : ConDesc I} (x : ⟦ C ⟧ᶜ (μ D) γ) → Set j
  ConAll {C = κ _}   (refl ) = ⋆
  ConAll {C = ι _ _} (x , d) = P x × ConAll d
  ConAll {C = π _ _} (_ , d) = ConAll d

  DescAll : ∀ {γ} (x : μ D γ) → Set j
  DescAll ⟨ k , x ⟩ = ConAll x

  mutual
    all-con : (f : ∀ {γ} (x : μ D γ) → DescAll x → P x)
            → {C : ConDesc I}
            → {γ : I} (x : ⟦ C ⟧ᶜ (μ D) γ)
            → ConAll x
    all-con f {κ _}   (refl ) = ∗
    all-con f {ι _ _} (x , d) = ind f x , all-con f d
    all-con f {π S D} (_ , d) = all-con f d

    all : (f : ∀ {γ} (x : μ D γ) → DescAll x → P x)
        → {γ : I} (x : μ D γ)
        → DescAll x
    all f ⟨ k , x ⟩ = all-con f x
  
    ind : (f : ∀ {γ} (x : μ D γ) → DescAll x → P x)
        → {γ : I} (x : μ D γ)
        → P x
    ind f x = f x (all f x)
