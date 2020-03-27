{-# OPTIONS --rewriting #-}

module Generics.Prelude where

open import Agda.Primitive        public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite

open import Prelude hiding (abs)  public
open import Prelude.Equality      public


infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

data Lift {a b} (A : Set a) : Set (a ⊔ b) where
  lift : A → Lift A

data VecAll {a b} {A : Set a} (P : A → Set b) : {n : Nat} → Vec A n → Set (a ⊔ b) where
  []  : VecAll P []
  _∷_ : ∀ {n x xs} (p : P x) (ps : VecAll P {n} xs) → VecAll P (x ∷ xs)

data ⋆ {a} : Set a where
  ∗ : ⋆

lookupAll : ∀ {a b n} {A : Set a} {P : A → Set b} {xs} (ps : VecAll P xs) (k : Fin n) → P (indexVec xs k)
lookupAll (p ∷ ps) zero    = p
lookupAll (p ∷ ps) (suc k) = lookupAll ps k

decEqIso : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {g : B → A}
           (retract : ∀ x → g (f x) ≡ x)
         → ∀ {x y} → Dec (f x ≡ f y)
         → Dec (x ≡ y)
decEqIso {g = g} retr {x} {y} (yes fx≡fy) =
  yes (trans (sym (retr x)) (trans (cong g fx≡fy) (retr y)))
decEqIso {f = f} retr (no fx≢fy) = no λ x≢y → fx≢fy (cong f x≢y)

data Members {a} : {n : Nat} → Vec (Set a) n → Set (lsuc a) where
  []  : Members []
  _∷_ : ∀ {n A AS} → A → Members {n = n} AS → Members (A ∷ AS)

lookupMember : ∀ {a n} {xs : Vec (Set a) n} → Members xs → (k : Fin n) → indexVec xs k
lookupMember (x ∷ xs) zero    = x
lookupMember (x ∷ xs) (suc k) = lookupMember xs k

curryMembersType : ∀ {a b n} {xs : Vec (Set a) n} {B : Set (a ⊔ b)}
                → (f : Members xs → B) → Set (a ⊔ b)
curryMembersType {a} {b} {xs = xs} {B} f = aux xs
  where
    aux : ∀ {n} → Vec (Set a) n → Set (a ⊔ b)
    aux []       = B
    aux (A ∷ AS) = A → aux AS

declareMembers : ∀ {a n} {xs : Vec (Set a) n}
               → (f : (k : Fin n) → indexVec xs k)
               → Members xs
declareMembers {xs = []}     f = []
declareMembers {xs = A ∷ xs} f = f zero ∷ declareMembers (f ∘ suc)

curryMembers : ∀ {a b n} {xs : Vec (Set a) n} {B : Set (a ⊔ b)}
            → (f : Members xs → B)
            → curryMembersType {b = b} f
curryMembers {xs = []}     f = f []
curryMembers {xs = A ∷ AS} f = λ x → curryMembers (f ∘ (x ∷_))

indexTabulate : ∀ {a n} {A : Set a} (f : Fin n → A)
              → (k : Fin n) → indexVec (tabulate f) k ≡ f k
indexTabulate {n = suc n} f zero    = refl
indexTabulate {n = suc n} f (suc k) = indexTabulate (f ∘ suc) k

{-# REWRITE indexTabulate #-}

mapMembers : ∀ {a n} {xs ys : Vec (Set a) n}
           → (f : (k : Fin n) → indexVec xs k → indexVec ys k)
           → Members xs
           → Members ys
mapMembers {ys = []}     f []       = []
mapMembers {ys = y ∷ ys} f (z ∷ zs) = (f zero z) ∷ mapMembers (f ∘ suc) zs

-- ideally we should reverse the list
sigmatize : ∀ {a} → List (Set a) → Set a
sigmatize []       = ⋆
sigmatize (x ∷ xs) = x × sigmatize xs
