{-# OPTIONS --cumulativity #-}

module Generics.Example where

open import Generics.Prelude
open import Generics.Desc
open import Generics.Reflection
open import Generics.Constructions

open Generics.Reflection.Deriving
open Generics.Reflection.Deriving.Common


module NatDesc where

  data nat : ⊤ → Set where
    ze : nat tt
    su : nat tt → nat tt

  natD : Desc ⊤ 2
  natD = deriveDesc nat
  
  nat′ : Set
  nat′ = μ natD tt
  
  ze′ : nat′
  ze′ = ⟨ zero , refl ⟩
  
  su′ : nat′ → nat′
  su′ n = ⟨ suc zero , n , refl ⟩
  
  to′ : nat tt → nat′
  to′ ze     = ze′
  to′ (su n) = su′ (to′ n)
  
  from′ : nat′ → nat tt
  from′ ⟨ zero , refl ⟩        = ze
  from′ ⟨ suc zero , n , refl ⟩ = su (from′ n)
  
  to∘from : ∀ x → to′ (from′ x) ≡ x
  to∘from ⟨ zero , refl ⟩        = refl
  to∘from ⟨ suc zero , n , refl ⟩ = cong (λ n′ → ⟨ suc zero , n′ , refl ⟩) (to∘from n)
  
  from∘to : ∀ x → from′ (to′ x) ≡ x
  from∘to ze     = refl
  from∘to (su n) = cong su (from∘to n)

  instance
    natHasDesc : HasDesc nat
    natHasDesc =
      record { D = natD
             ; to = to′
             ; from = from′
             ; to∘from = to∘from
             ; from∘to = from∘to
             ; constr = (λ { zero → ze ; (suc zero) → su })
             ; constr-proof = λ { zero → refl ; (suc zero) → λ x → cong su (sym (from∘to x)) }
             }

  instance
    natEq : Eq (nat tt)
    natEq = deriveEq nat

    natShow : Show (nat tt)
    natShow = deriveShow nat

  n1 : nat tt
  n1 = su (su ze)

  n2 : nat tt
  n2 = su (su (su ze))

  check : (n1 == n2) ≡ no _
  check = refl

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
