{-# OPTIONS --cumulativity #-}

module Generics.Example where

open import Generics.Prelude
open import Generics.Desc
open import Generics.Reflection

open Generics.Reflection.Deriving
open Generics.Reflection.Deriving.Common

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

open NatDesc
open VecDesc {lzero} Nat

data Tree : Set where
  leaf : Tree
  node : Tree → Tree → Tree

treeD : Desc ⊤ 2
treeD = deriveDesc Tree

tree : Set
tree = μ treeD tt

leaf′ : tree
leaf′ = ⟨ zero , refl ⟩

node′ : tree → tree → tree
node′ l r = ⟨ suc zero , l , r , refl ⟩

finD : Desc {lzero} Nat 2
finD = deriveDesc Fin

nat1 = su′ (su′ (su′ ze′))
nat2 = su′ (su′ ze′)

tree1 = node′ (node′ leaf′ (node′ leaf′ leaf′)) (node′ (node′ leaf′ leaf′) leaf′)

vec1 = cons′ 2 (cons′ 3 nil′)
