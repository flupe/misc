{-# OPTIONS --cumulativity #-}

module Generics.Example where

open import Generics.Prelude
open import Generics.Desc
open import Generics.Reflection


module NatDesc where

  natD : Desc {lzero} ⊤ 2
  natD = κ tt
       ∷ ι tt (κ tt)
       ∷ []
  
  -- for now our encoding is one level too high
  -- oh well
  nat : Set₁
  nat = μ natD tt
  
  ze′ : nat
  ze′ = ⟨ ze , refl ⟩
  
  su′ : nat → nat
  su′ n = ⟨ su ze , n , refl ⟩
  
  to′ : Nat → nat
  to′ zero    = ze′
  to′ (suc n) = su′ (to′ n)
  
  from′ : nat → Nat
  from′ ⟨ ze , refl ⟩        = zero
  from′ ⟨ su ze , n , refl ⟩ = suc (from′ n)
  
  to∘from : ∀ x → to′ (from′ x) ≡ x
  to∘from ⟨ ze , refl ⟩        = refl
  to∘from ⟨ su ze , n , refl ⟩ = cong (λ n′ → ⟨ su ze , n′ , refl ⟩) (to∘from n)
  
  from∘to : ∀ x → from′ (to′ x) ≡ x
  from∘to zero    = refl
  from∘to (suc n) = cong suc (from∘to n)


module VecDesc {a} (A : Set a) where

  vecD : Desc {a} Nat 2
  vecD = κ 0
       ∷ π[ n ∈ Nat ] π[ x ∈ A ] ι n (κ (suc n))
       ∷ []
  
  vec : Nat → Set (lsuc a)
  vec = μ vecD
  
  nil′ : vec 0
  nil′ = ⟨ ze , refl ⟩
  
  cons′ : ∀ {n} → A → vec n → vec (suc n)
  cons′ {n = n} x xs = ⟨ su ze , n , x , xs , refl ⟩

  to : ∀ {n} → Vec A n → vec n
  to []       = nil′
  to (x ∷ xs) = cons′ x (to xs)

  from : ∀ {n} → vec n → Vec A n
  from ⟨ ze , refl ⟩ = []
  from ⟨ su ze , n , x , xs , refl ⟩ = x ∷ from xs

  to∘from : ∀ {n} (x : vec n) → to (from x) ≡ x
  to∘from ⟨ ze , refl ⟩ = refl
  to∘from ⟨ su ze , n , x , xs , refl ⟩ =
    cong (λ xs′ → ⟨ su ze , n , x , xs′ , refl ⟩)
         (to∘from xs)

  from∘to : ∀ {n} (x : Vec A n) → from (to x) ≡ x
  from∘to []       = refl
  from∘to (x ∷ xs) = cong (x ∷_) (from∘to xs)
