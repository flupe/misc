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

module TreeDesc {A : Set} where

  data Tree : ⊤ → Set where
    leaf : Tree tt
    node : Tree tt → Tree tt → Tree tt

  treeD : Desc ⊤ 2
  treeD = κ tt ∷ ι tt (ι tt (κ tt)) ∷ []

  tree : Set
  tree = μ treeD tt

  to : Tree tt → tree
  to leaf       = ⟨ zero , refl ⟩
  to (node l r) = ⟨ suc zero , to l , to r , refl ⟩

  from : tree → Tree tt
  from ⟨ zero , refl ⟩ = leaf
  from ⟨ suc zero , l , r , refl ⟩ = node (from l) (from r)

  postulate
    to∘from : ∀ x → to (from x) ≡ x
    from∘to : ∀ x → from (to x) ≡ x

  instance
    treeHasDesc : HasDesc Tree
    treeHasDesc = record
                    { D = treeD
                    ; to = to
                    ; from = from
                    ; to∘from = to∘from
                    ; from∘to = from∘to
                    ; constr = λ { zero → leaf ; (suc zero) → node }
                    ; constr-proof = λ { zero → refl ; (suc zero) → {!!} }
                    }

  elim-tree : ∀ {i} (P : Tree tt → Set i) → elim-type Tree P
  elim-tree P = get-elim Tree P


module IdDesc (A : Set) where

  data _≅_ (x : A) : A → Set where
    refl : x ≅ x

  idD : (x : A) → Desc A 1
  idD x = κ x ∷ []

  to : ∀ x {y} → x ≅ y → μ (idD x) y
  to x refl = ⟨ zero , refl ⟩

  from : ∀ x {y} → μ (idD x) y → x ≅ y
  from x ⟨ zero , refl ⟩ = refl

  postulate
    to∘from : ∀ x {y} (p : μ (idD x) y) → to x (from x p) ≡ p
    from∘to : ∀ x {y} (p : x ≅ y) → from x (to x p) ≡ p

  instance
    idHasDesc : ∀ {x} → HasDesc (_≅_ x)
    idHasDesc {x} = record
                    { D = idD x
                    ; to = to x
                    ; from = from x
                    ; to∘from = to∘from x 
                    ; from∘to = from∘to x
                    ; constr = λ { zero → refl }
                    ; constr-proof = λ { zero → refl }
                    }
  
  elim-id : ∀ x {i} (P : ∀ {y} → x ≅ y → Set i) → elim-type (_≅_ x) P
  elim-id x P = get-elim (_≅_ x) P


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

