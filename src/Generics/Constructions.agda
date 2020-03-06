module Generics.Constructions where

open import Generics.Prelude
open import Generics.Desc
open import Generics.Reflection


module Induction {i j n} {I : Set i} (D : Desc {i} I n) (P : ∀ {γ} → μ D γ → Set j) where

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

open Induction

module _ {i} {I : Set i} (A : I → Set i) (H : HasDesc {i} A) where

  open HasDesc

  {- WITH CUMULATIVITY -}
  {-
  unfold : ∀ {j} (P : {γ : I} → A γ → Set j) (C : ConDesc I)
       → (tie : {γ : I} → ⟦ C ⟧ᶜ (μ (D H)) γ → Set (i ⊔ j))
       → Set (i ⊔ j)
  unfold P (κ k)   tie = tie refl
  unfold {j} P (ι γ C) tie = (x : A γ) → P x → unfold {j} P (C  ) (λ d → tie (to H x , d))
  unfold {j} P (π S C) tie = (x : S)         → unfold {j} P (C x) (λ d → tie (x , d))

  con-type : ∀ {j} (P : {γ : I} → A γ → Set j) (k : Fin (n H)) (C : ConDesc I)
           → _≡_ {lsuc i} C (indexVec (D H) k) → Set (i ⊔ j)
           → Set (i ⊔ j)
  con-type {j} P k C p T = unfold P C pack → T
    where 
    pack : {γ : I} → ⟦ C ⟧ᶜ (μ (D H)) γ → Set (i ⊔ j)
    pack {γ} X = P {γ} (from H ⟨ (k , transport {lsuc i} {i} (λ C → ⟦ C ⟧ᶜ (μ {i} (D H)) γ) p X) ⟩)
            
  ind-type : ∀ {j} (P : {γ : I} → A γ → Set j) → Set (i ⊔ j)
  ind-type {j} P = foldi {lsuc i} {lsuc (i ⊔ j)} (D H) (con-type {j} P) ({γ : I} → (x : A γ) → P x)

-}

  -- WITHOUT CUMULATIVITY

  unfold : ∀ {j} (P : {γ : I} → A γ → Set j) (C : ConDesc I)
       → (tie : {γ : I} → ⟦ C ⟧ᶜ (μ (D H)) γ → Set (i ⊔ j))
       → Set (i ⊔ j)
  unfold P (κ k)   tie = tie refl
  unfold P (ι γ C) tie = (x : A γ) → P x → unfold P (C  ) (tie ∘ (to H x ,_))
  unfold P (π S C) tie = (x : S)         → unfold P (C x) (tie ∘ (x ,_))

  con-type : ∀ {j} (P : {γ : I} → A γ → Set j) (k : Fin (n H)) (C : ConDesc I)
           → _≡_ {lsuc i} C (indexVec (D H) k) → Set (i ⊔ j)
           → Set (i ⊔ j)
  con-type {j} P k C p T = unfold P C pack → T
    where 
    pack : {γ : I} → ⟦ C ⟧ᶜ (μ (D H)) γ → Set (i ⊔ j)
    pack {γ} X = ⋆ {i ⊔ j} → P {γ} (from H ⟨ (k , transport (λ C → ⟦ C ⟧ᶜ (μ (D H)) γ) p X) ⟩)
            
  ind-type : ∀ {j} (P : {γ : I} → A γ → Set j) → Set (i ⊔ j)
  ind-type {j} P = foldi (D H) (con-type {j} P) ({γ : I} → (x : A γ) → P x)

-- elim : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc A ⦄
--      → ∀ {j} (P : {γ : I} → A γ → Set j) → ind-type A H P
-- elim A ⦃ H ⦄ P = {!!}
