{-# OPTIONS --safe --without-K #-}

module Generics.Prelude where

open import Agda.Primitive public
open import Agda.Builtin.List public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Nat public hiding (_==_)
open import Agda.Builtin.Unit public

variable a b i j k : Level


-- Utils
-------------------------------------------------------------

infixr -1 _$_
infixl 2 _∘_

id : {A : Set i} → A → A
id x = x

const : {A : Set i} → A → {B : Set j} → B → A
const x _ = x

_$_ : {A : Set i} {P : A → Set j} (f : ∀ x → P x) (x : A) → P x
f $ x = f x

_×_ : (A B : Set i) → Set i
A × B = Σ A (const B)

case_of_ : {A : Set i} {P : A → Set j} (x : A) → ((x : A) → P x) → P x
case x of f = f x

_∘_ : {A : Set i} {P : A → Set j} {Q : {x : A} → P x → Set k}
      (g : {x : A} → (y : P x) → Q y) (f : (x : A) → P x)
    → (x : A) → Q (f x)
_∘_ g f x = g (f x)


-- Σ
-------------------------------------------------------------

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


-- Fin
-------------------------------------------------------------

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)


-- Vec
-------------------------------------------------------------

data Vec (A : Set a) : Nat → Set a where
  []  : Vec A 0
  _∷_ : A → ∀ {n} → Vec A n → Vec A (suc n)

data VecAll {A : Set i} (P : A → Set j) : {n : Nat} → Vec A n → Set (i ⊔ j) where
  []  : VecAll P []
  _∷_ : ∀ {x} → P x → ∀ {n xs} → VecAll P {n} xs → VecAll P (x ∷ xs)

lookup : {A : Set a} {n : Nat} → Vec A n → Fin n → A
lookup (x ∷ _) zero = x
lookup (_ ∷ xs) (suc k) = lookup xs k

map : {A : Set a} {B : Set b} (f : A → B) {n : Nat}
    → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

mapi : {A : Set a} {B : Set b} {n : Nat}
       (f : Fin n → A → B) → Vec A n → Vec B n
mapi f [] = []
mapi f (x ∷ xs) = f zero x ∷ mapi (f ∘ suc) xs


lookupAll : {A : Set a} {P : A → Set b} {n : Nat} {xs : Vec A n}
          → VecAll P xs → (k : Fin n) → P (lookup xs k)
lookupAll (p ∷ ps) zero    = p
lookupAll (p ∷ ps) (suc k) = lookupAll ps k

tabulate : {A : Set a} {n : Nat}
         → (Fin n → A) → Vec A n
tabulate {n = zero} f = []
tabulate {n = suc n} f = f zero ∷ tabulate (f ∘ suc)



-- Members
-------------------------------------------------------------

-- how is this called in real life??
data Members {a} : {n : Nat} → Vec (Set a) n → Set (lsuc a) where
  []  : Members []
  _∷_ : ∀ {n A AS} → A → Members {n = n} AS → Members (A ∷ AS)

lookupMember : ∀ {n} {xs : Vec (Set a) n} → Members xs → ∀ k → lookup xs k
lookupMember (x ∷ _) zero = x
lookupMember (_ ∷ xs) (suc k) = lookupMember xs k

curryMembersType : ∀ {a b n} {xs : Vec (Set a) n} {B : Set (a ⊔ b)}
                 → (f : Members xs → B) → Set (a ⊔ b)
curryMembersType {a} {b} {xs = xs} {B} f = aux xs
  where
    aux : ∀ {n} → Vec (Set a) n → Set (a ⊔ b)
    aux []       = B
    aux (A ∷ AS) = A → aux AS

declareMembers : ∀ {a n} {xs : Vec (Set a) n}
               → (f : (k : Fin n) → lookup xs k)
               → Members xs
declareMembers {xs = []}     f = []
declareMembers {xs = A ∷ xs} f = f zero ∷ declareMembers (f ∘ suc)

curryMembers : ∀ {a b n} {xs : Vec (Set a) n} {B : Set (a ⊔ b)}
             → (f : Members xs → B)
             → curryMembersType {b = b} f
curryMembers {xs = []}     f = f []
curryMembers {xs = A ∷ AS} f = λ x → curryMembers (f ∘ (x ∷_))

mapP : {A : Set a} {P : A → Set b} (f : (x : A) → P x) {n : Nat}
       (xs : Vec A n) → Members (map P xs)
mapP f [] = []
mapP f (x ∷ xs) = (f x) ∷ (mapP f xs)

mapMembers : ∀ {a n} {xs ys : Vec (Set a) n}
           → (f : (k : Fin n) → lookup xs k → lookup ys k)
           → Members xs
           → Members ys
mapMembers {ys = []}     f []       = []
mapMembers {ys = y ∷ ys} f (z ∷ zs) = (f zero z) ∷ mapMembers (f ∘ suc) zs

mapMembers′ : ∀ {a n} {B : Set b} {xs : Vec (Set a) n}
           → (f : (k : Fin n) → lookup xs k → B)
           → Members xs
           → Vec B n
mapMembers′ f []       = []
mapMembers′ f (z ∷ zs) = (f zero z) ∷ mapMembers′ (f ∘ suc) zs

-- Lift
-------------------------------------------------------------

data Lift {a b} (A : Set a) : Set (a ⊔ b) where
  lift : A → Lift A

data ⊤′ {a} : Set a where
  instance tt : ⊤′


-- Equality
-------------------------------------------------------------

record Equality : Setω where
  field
    _≡_  : {A : Set a} → A → A → Set a

    refl : {A : Set a} {x : A} → x ≡ x

    sym  : {A : Set a} {x y : A} → x ≡ y → y ≡ x
    
    transport : {A : Set a} (P : A → Set b) {x y : A} → x ≡ y → P x → P y

    subst : {A B : Set a} → A ≡ B → A → B

    cong : {A : Set a} {B : Set b} (f : A → B) {x y : A}
         → x ≡ y → f x ≡ f y

    J : {A : Set a} {x : A} (P : ∀ y → x ≡ y → Set b)
      → P x refl → ∀ {y} → (p : x ≡ y) →  P y p

    JRefl : {A : Set a} {x : A} (P : ∀ y → x ≡ y → Set a)
            (d : P x refl) → J P d refl ≡ d


{-




decEqIso : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {g : B → A}
           (retract : ∀ x → g (f x) ≡ x)
         → ∀ {x y} → Dec (f x ≡ f y)
         → Dec (x ≡ y)
decEqIso {g = g} retr {x} {y} (yes fx≡fy) =
  yes (trans (sym (retr x)) (trans (cong g fx≡fy) (retr y)))
decEqIso {f = f} retr (no fx≢fy) = no λ x≢y → fx≢fy (cong f x≢y)





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

-}
