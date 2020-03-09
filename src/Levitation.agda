module Levitation where

open import Agda.Builtin.Size
open import Agda.Primitive
open import Level using (Lift; lift)

open import Data.Nat using (ℕ; zero; suc; _≤?_)
open import Data.Fin using (Fin; zero; suc)
open import Data.String.Base
open import Data.Product
open import Data.Unit.Base
open import Agda.Builtin.Nat

infixr 10 _$_

_$_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → A → B
f $ x = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x


-- all of this is taken directly from The Gentle Art of Levitation
--                                    Chapman, Dagand, McBride & Morris

module Enumerations where

  -- enumeration universe
  -- here we do not really care about named tags
  En : Set
  En = ℕ

  #_ : ℕ → Set
  #_ = Fin

  π : ∀ {ℓ} (E : En) (P : # E → Set ℓ) → Set ℓ
  π {ℓ} zero    P = Lift ℓ ⊤
  π     (suc n) P = P zero × π n λ x → P (suc x)

  switch : (E : En) (P : # E → Set) → π E P → (x : # E) → P x
  switch (suc n) P (π₀ , _) zero    = π₀
  switch (suc n) P (_ , π₁) (suc x) = switch n (λ x → P (suc x)) π₁ x


module Inductive where

  open import Data.Vec.Base using (Vec; _∷_; []; here; there; lookup)

  open Enumerations

  data Desc {ℓ} : Set (lsuc ℓ) where
    ′1    :                                    Desc
    ′Σ    : (S : Set ℓ) → (D : S → Desc {ℓ}) → Desc
    ′ind× : Desc {ℓ}                         → Desc

  ⟦_⟧ : ∀ {ℓ} → Desc {ℓ} → Set ℓ → Set ℓ
  ⟦_⟧ {ℓ} ′1  X = Lift ℓ ⊤
  ⟦ ′Σ S D ⟧  X = Σ S λ s → ⟦ D s ⟧ X
  ⟦ ′ind× D ⟧ X = X × ⟦ D ⟧ X


  -- a terser way to describe datatype constructors
  [_] : ∀ {n} → Vec (Desc) n → Desc
  [_] {n} v = ′Σ (# n) (lookup v)

  NatD : Desc
  NatD = [ ′1 ∷ ′ind× ′1 ∷ [] ]

  ListD : Set → Desc
  ListD X = [ ′1 ∷ ′Σ X (λ _ → ′ind× ′1) ∷ [] ]

  TreeD : Set → Desc
  TreeD X = [ ′1 ∷ ′ind× (′Σ X (λ _ → ′ind× ′1)) ∷ [] ]


  data μ {l} (D : Desc {l}) {s : Size} : Set l where
    ⟨_⟩ : {t : Size< s} → ⟦ D ⟧ (μ D {t}) → μ D {s}


  unit : ∀ {ℓ} → Lift ℓ ⊤
  unit = lift tt

{-
  Nat : Set
  Nat = μ NatD

  ze : Nat
  ze = ⟨ zero , unit ⟩

  su : Nat → Nat
  su x = ⟨ suc zero , x , unit ⟩

  Tree : Set → Set
  Tree X = μ (TreeD X)

  leaf : ∀ {X} → Tree X
  leaf = ⟨ zero , unit ⟩

  node : ∀ {X} → Tree X → X → Tree X → Tree X
  node l x r = ⟨ suc zero , l , x , r , unit ⟩


  map-fold : ∀ {D} (D′ : Desc) (X : Set) (P : ⟦ D ⟧ X → X) (x : ⟦ D′ ⟧ (μ D)) → ⟦ D′ ⟧ X
  fold     :       (D  : Desc) (X : Set) (P : ⟦ D ⟧ X → X) (x : μ D)          → X

  fold D X P ⟨ x ⟩ = P (map-fold D X P x)

  map-fold      ′1        X P x       = lift tt
  map-fold      (′Σ S D)  X P (s , d) = s , (map-fold (D s) X P d)
  map-fold {D′} (′ind× D) X P (x , d) = fold D′ X P x , map-fold D X P d


  All : ∀ {ℓ} (D : Desc {ℓ}) (X : Set ℓ) (P : X → Set ℓ) (xs : ⟦ D ⟧ X) → Set (lsuc ℓ)
  All {ℓ} ′1    X P _       = Lift (lsuc ℓ) ⊤
  All (′Σ S D)  X P (s , d) = All (D s) X P d
  All (′ind× D) X P (x , d) = P x × All D X P d

  all : ∀ {ℓ} (D : Desc {ℓ}) (X : Set ℓ) (P : X → Set ℓ)
      → (p : (x : X) → P x)
      → (xs : ⟦ D ⟧ X)
      → All D X P xs
  all ′1        X P p _       = unit
  all (′Σ S D)  X P p (s , d) = all (D s) X P p d
  all (′ind× D) X P p (x , d) = p x , all D X P p d

  ind : ∀ {ℓ s} (D : Desc {ℓ}) (P : ∀ {s} → μ D {s} → Set ℓ)
      → (∀ {s} {t : Size< s} (d : ⟦ D ⟧ (μ D {t})) → All D (μ D {t}) P d → P {s} ⟨ d ⟩)
      → (x : μ D {s})
      → P x

  ind D P m ⟨ d ⟩ = m d (all D (μ D) P (ind D P m) d)

-}

module Families where

  record _►_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      top : A
      pop : B top

  mutual

    infixl 1 _▷_ _▷′_

    data Ctx {ℓ} : Set (lsuc ℓ) where
      _▷_ : (Γ : Ctx {ℓ}) (S : ⟦ Γ ⟧ → Set ℓ) → Ctx
      ε   : Ctx

    ⟦_⟧ : ∀ {ℓ} → Ctx {ℓ} → Set ℓ
    ⟦ Γ ▷ S ⟧ = ⟦ Γ ⟧ ► S
    ⟦ ε ⟧     = Lift _ ⊤

    _▷′_ : ∀ {ℓ} → Ctx {ℓ} → Set ℓ → Ctx {ℓ}
    Γ ▷′ S = Γ ▷ λ _ → S

    t = ε ▷′ Set

    aa = ⟦ t ⟧

open Families public
