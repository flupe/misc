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
    natHasDesc : HasDesc {lzero} nat
    natHasDesc =
      record { D = natD
             ; to = to′
             ; from = from′
             ; to∘from = to∘from
             ; from∘to = from∘to
             ; constr = (λ { zero → ze ; (suc zero) → su })
             ; constr-proof = λ { zero → refl ; (suc zero) → λ x → cong su (sym (from∘to x)) }
             }

  elim-nat : ∀ {i} (P : nat tt → Set i) → elim-type nat P
  elim-nat P = get-elim nat P

  -- instance
  --   natEq : Eq (nat tt)
  --   natEq = deriveEq nat

  --   natShow : Show (nat tt)
  --   natShow = deriveShow nat

  -- n1 : nat tt
  -- n1 = su (su ze)

  -- n2 : nat tt
  -- n2 = su (su (su ze))

  -- check : (su n1 == n2) ≡ yes refl
  -- check = refl

module VecDesc (A : Set) where

  vecD : Desc Nat 2
  vecD = deriveDesc (Vec A)
  
  vec : Nat → Set
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

  instance
    vecHasDesc : HasDesc {lzero} (Vec A)
    vecHasDesc = record
                  { D = vecD
                  ; to = to
                  ; from = from
                  ; to∘from = to∘from
                  ; from∘to = from∘to
                  ; constr = λ { zero → []; (suc zero) → λ n x xs → x ∷ xs }
                  ; constr-proof = λ { zero → refl; (suc zero) → λ n x xs → cong (x ∷_) (sym (from∘to xs))}
                  }

  elim-vec : ∀ {i} (P : ∀ {n} → Vec A n → Set i) → elim-type (Vec A) P
  elim-vec P = get-elim (Vec A) P

