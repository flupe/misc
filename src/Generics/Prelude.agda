module Generics.Prelude where

open import Agda.Primitive        public
open import Agda.Builtin.Equality public

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

fin : (n : Nat) → Vec (Fin n) n
fin zero    = []
fin (suc n) = zero ∷ fmap suc (fin n)

-- very inefficient (n²), oh well
foldi : ∀ {a b n} {A : Set a} {B : Set b}
      → (xs : Vec A n)
      → (f : (k : Fin n) (x : A) → (x ≡ indexVec xs k) → B → B)
      → B → B
foldi {n = n} {A} {B} xs f e = 
  foldi′ (fin n)
  where
    foldi′ : ∀ {m} → Vec (Fin n) m → B
    foldi′ [] = e
    foldi′ (k ∷ ks) = f k (indexVec xs k) refl (foldi′ ks)

