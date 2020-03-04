{-# OPTIONS --cumulativity #-}

module Generics.Example where

open import Generics.Prelude
open import Generics.Desc
open import Generics.Reflection


module NatDesc where

  natD : Desc ⊤ 2
  natD = deriveDesc Nat
  
  nat : Set
  nat = μ natD tt
  
  ze′ : nat
  ze′ = ⟨ zero , refl ⟩
  
  su′ : nat → nat
  su′ n = ⟨ suc zero , n , refl ⟩
  
  -- TODO: AUTOMATE EVERYTHING
  to′ : Nat → nat
  to′ zero    = ze′
  to′ (suc n) = su′ (to′ n)
  
  from′ : nat → Nat
  from′ ⟨ zero , refl ⟩        = zero
  from′ ⟨ suc zero , n , refl ⟩ = suc (from′ n)
  
  to∘from : ∀ x → to′ (from′ x) ≡ x
  to∘from ⟨ zero , refl ⟩        = refl
  to∘from ⟨ suc zero , n , refl ⟩ = cong (λ n′ → ⟨ suc zero , n′ , refl ⟩) (to∘from n)
  
  from∘to : ∀ x → from′ (to′ x) ≡ x
  from∘to zero    = refl
  from∘to (suc n) = cong suc (from∘to n)


module VecDesc {a} (A : Set a) where

  vecD : Desc {a} Nat 2
  vecD = deriveDesc (Vec {a} A)
  
  vec : Nat → Set a
  vec = μ vecD
  
  nil′ : vec 0
  nil′ = ⟨ zero , refl ⟩
  
  cons′ : ∀ {n} → A → vec n → vec (suc n)
  cons′ {n = n} x xs = ⟨ suc zero , n , x , xs , refl ⟩

  to : ∀ {n} → Vec A n → vec n
  to []       = nil′
  to (x ∷ xs) = cons′ x (to xs)

  from : ∀ {n} → vec n → Vec A n
  from ⟨ zero , refl ⟩ = []
  from ⟨ suc zero , n , x , xs , refl ⟩ = x ∷ from xs

  to∘from : ∀ {n} (x : vec n) → to (from x) ≡ x
  to∘from ⟨ zero , refl ⟩ = refl
  to∘from ⟨ suc zero , n , x , xs , refl ⟩ =
    cong (λ xs′ → ⟨ suc zero , n , x , xs′ , refl ⟩)
         (to∘from xs)

  from∘to : ∀ {n} (x : Vec A n) → from (to x) ≡ x
  from∘to []       = refl
  from∘to (x ∷ xs) = cong (x ∷_) (from∘to xs)


module Operations where

  open import Prelude.Show
  open import Prelude.String

  module ShowMu {i n} {I : Set i} {D : Desc {i} I n} {DI : DescInstance {j = i} Show D} where
    mutual
      showCon : {C : ConDesc {i} I} {CI : ConInstance {j = i} Show C} {γ : I} → ⟦ C ⟧ᶜ (μ D) γ → String
      showCon {C = κ k  } refl    = ""
      showCon {C = ι i D} {CI} (x , d) = "(" <> showMu x <> ")" <> showCon {CI = CI} d
      showCon {C = π S D} {CI = XI , SI} (s , d) = show ⦃ XI ⦄ s <> " " <> showCon {CI = SI s} d

      showDesc : {γ : I} → ⟦ D ⟧ᵈ (μ D) γ → String
      showDesc (k , x) = "con" <> show k <> " " <> showCon {CI = lookupAll DI k} x 

      showMu : {γ : I} → μ D γ → String
      showMu ⟨ x ⟩ = showDesc x

  instance
    ShowCon : ∀ {i n} {I : Set i} {D : Desc {i} I n} {γ : I} ⦃ DI : DescInstance {j = i} Show D ⦄ → Show (μ D γ)
    ShowCon ⦃ DI = DI ⦄ = simpleShowInstance (ShowMu.showMu {DI = DI})

open NatDesc
open VecDesc {lzero} Nat

instance
  NatI : DescInstance Show natD
  NatI = unit ∷ unit ∷ []

  VecI : DescInstance Show vecD
  VecI = unit ∷ (ShowNat , const (ShowNat , (const unit))) ∷ []

test1 = su′ (su′ (su′ ze′))
test2 = cons′ 2 (cons′ 3 nil′)
