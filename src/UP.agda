{-# OPTIONS --cubical #-}

module UP where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.List

open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Function using (_∘_; const)
open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.HalfAdjoint using (congEquiv)
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport

variable i j : Level

------------------------------------------------------------

infixr 1 _$_

_$_ : {A : Set i} {P : A → Set j} (f : ∀ x → P x) (x : A) → P x
f $ x = f x

id : {A : Set i} → A → A
id x = x

_×_ : (A B : Set i) → Set i
A × B = Σ A (const B)

case_of_ : {A : Set i} {P : A → Set j} (x : A) → ((x : A) → P x) → P x
case x of f = f x

------------------------------------------------------------

REL : (A B : Set i) → Set (lsuc i)
REL {i} A B = A → B → Set i

REL-inv : {A B : Set i} → REL A B → REL B A
REL-inv R = λ b a → R a b

REL-comp : {A B C : Set i} → REL A B → REL B C → REL A C
REL-comp RAB RBC = λ a c → Σ _ λ b → RAB a b × RBC b c

record _⋈_ (A B : Set i) : Set (lsuc i) where
  constructor UR
  field ur : REL A B
open _⋈_

_≈_ : {A B : Set i} ⦃ E : A ⋈ B ⦄ → A → B → Set i
_≈_ ⦃ E ⦄ x y = ur E x y

⋈-refl : (A : Set i) → A ⋈ A
⋈-refl _ = UR _≡_

⋈-sym : {A B : Set i} → A ⋈ B → B ⋈ A
⋈-sym RAB = UR (REL-inv (ur RAB))

⋈-trans : {A B C : Set i} → A ⋈ B → B ⋈ C → A ⋈ C
⋈-trans {B = B} RAB RBC = UR (REL-comp (ur RAB) (ur RBC))

------------------------------------------------------------

instance
  ⋈-Set : Set i ⋈ Set i
  ⋈-Set = UR _≡_

Set≈Set : ur ⋈-Set (Set i) (Set i)
Set≈Set = refl

[_]_≋_ : {A B : Set i} (E : A ≈ B) → A → B → Set i
[ E ] x ≋ y = PathP (λ i → E i) x y

postulate
  -- is this needed if we do not care about the FP?
  ∀≡∀ : {A B : Set i} (A≈B : A ≈ B)
      → {P : A → Set j} {Q : B → Set j}
      → (P≈Q : ∀ {a b} (H : [ A≈B ] a ≋ b) → P a ≈ Q b)
      → (∀ a → P a) ≡ (∀ b → Q b)

⋈-∀ : ∀ {A B : Set i} (A⋈B : A ⋈ B)
    → {P : A → Set j} {Q : B → Set j}
    → (P≈Q : ∀ {a b} (H : ur A⋈B a b) → P a ⋈ Q b)
    → (∀ a → P a) ⋈ (∀ b → Q b)
⋈-∀ A⋈B P≈Q = UR (λ f g → ∀ {x y} (H : ur A⋈B x y) → ur (P≈Q H) (f x) (g y))

instance
  List≈List : {A B : Set i} ⦃ R : A ≡ B ⦄ → List A ≈ List B
  List≈List {A = A} {B} ⦃ R ⦄ i = List (R i)

  ⋈-List : {A B : Set i} ⦃ R : A ≡ B ⦄ → List A ⋈ List B
  ⋈-List ⦃ R ⦄ = UR [ List≈List ⦃ R ⦄ ]_≋_


module Reflection where

  open import Data.Nat.Base as ℕ
  open import Agda.Builtin.Reflection
  open import Agda.Builtin.Unit
  
  pattern ahr x = arg (arg-info hidden relevant) x
  pattern avr x = arg (arg-info visible relevant) x
  pattern sort s = agda-sort s
  
  infixl 10 _>>=_
  _>>=_  = bindTC
  _>>_ : {A : Set i} {B : Set j} → TC A → TC B → TC B
  a >> b = bindTC a (const b)
  return = returnTC
  
  to-level : ℕ → Level
  to-level zero    = lzero
  to-level (suc n) = lsuc (to-level n)
  
  
  it : (A : Set i) ⦃ x : A ⦄ → A
  it _ ⦃ x ⦄ = x
  

  ⟦_∣_⟧′ : (A B : Term) → TC Term

  -- TODO: take care of applications
  ⟦ A@(def n₁ []) ∣ B@(def n₂ []) ⟧′ =
    return $ def (quote it) (avr (def (quote _⋈_) (avr A ∷ avr B ∷ [])) ∷ [])

  ⟦ pi (avr a₁) (abs n₁ b₁) ∣ pi (avr a₂) (abs n₂ b₂) ⟧′ = do
       A ← ⟦ a₁ ∣ a₂ ⟧′
       B ← ⟦ b₁ ∣ b₂ ⟧′
       return $ def (quote ⋈-∀) (avr A ∷ avr (lam visible (abs n₁ B)) ∷ [])

  ⟦ sort s ∣ sort _ ⟧′ =
    case s of λ where
      (set l) → return $ def (quote ⋈-Set) (ahr l ∷ []) 
      (lit l) → do
        l′ ← quoteTC (to-level l)
        return $ def (quote ⋈-Set) (ahr l′ ∷ [])
      unknown → return $ def (quote ⋈-Set) (ahr unknown ∷ []) 

  ⟦ lam visible (abs n a) ∣ lam visible (abs _ b) ⟧′ = do
    t ← ⟦ a ∣ b ⟧′
    return $ lam hidden  $ abs "x"
           $ lam hidden  $ abs "y"
           $ lam visible $ abs "R" t

  -- TODO: applications!!1!
  ⟦ var x [] ∣ var _ [] ⟧′ = return (var (x * 3) [])

  ⟦ _ ∣ _ ⟧′ = typeError (strErr "Not supported" ∷ [])
  

  ⟦_∣_⟧ : (A B : Set i) → Term → TC ⊤
  ⟦ A ∣ B ⟧ hole = do
    A′ ← quoteTC A
    B′ ← quoteTC B
    ⟦ A′ ∣ B′ ⟧′ >>= unify hole
  
  _≈′_ : {A B : Set i} → A → B → {@(tactic ⟦ A ∣ B ⟧) E : A ⋈ B} → Set i
  _≈′_ x y {E} = ur E x y

  convert : Term → TC Term
  convert = {!!}

  macro
    ⟦_⟧ : Term → Term → TC ⊤
    ⟦ A ⟧ hole = ⟦ A ∣ A ⟧′ >>= unify hole

    convert⟨_⟩ : ∀ {A B : Set i} {R : A ⋈ B} {f g} (helper : ur R f g)
               → Term → Term → TC ⊤
    convert⟨ helper ⟩ t hole = do
      A ← inferType t
      B ← inferType hole
      {!!}
      -- A⋈B ← ⟦ A ∣ B ⟧′
  
open Reflection  

module Example where

  open import Data.Nat.Base as ℕ
  open import Cubical.Data.Nat.Properties as ℕ
  open import Data.Nat.Binary.Base as ℕᵇ using (ℕᵇ; fromℕ; toℕ)
  open import Data.Nat.Binary.Properties
  
  ℕ≈ℕᵇ : ℕ ≈ ℕᵇ
  ℕ≈ℕᵇ = ua (isoToEquiv (iso fromℕ toℕ {!!} {!!}))
  
  instance
    ℕ⋈ℕᵇ : ℕ ⋈ ℕᵇ
    ℕ⋈ℕᵇ = UR [ ℕ≈ℕᵇ ]_≋_

    ℕ⋈ℕ : ℕ ⋈ ℕ
    ℕ⋈ℕ = ⋈-refl ℕ
  
  postulate
    add≈addᵇ : _+_  ≈′ ℕᵇ._+_
    mul≈mulᵇ : _*_  ≈′ ℕᵇ._*_
    0≈0ᵇ     : zero ≈  ℕᵇ.zero

  cube : ℕ → ℕ
  cube x = x * x * x

  cubeᵇ : ℕᵇ → ℕᵇ
  cubeᵇ = {!convert⟨ mul≈mulᵇ ⟩ cube!}

  idd : ℕ → ℕ
  idd x = x

  ttt = ⟦ (λ (x : ℕ) → x) ⟧
