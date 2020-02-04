module Levitation where

open import Agda.Primitive
open import Level
open import Data.String.Base
open import Data.Product
open import Data.Unit.Base
open import Data.List.Base hiding (all)
open import Agda.Builtin.Size

infixr 10 _$_

_$_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → A → B
f $ x = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

-- all of this is taken directly from The Gentle Art of Levitation
--                                    Chapman, Dagand, McBride & Morris

module Enumerations where

  infix 30 ′_
  
  data Tag : Set where
    ′_ : String → Tag

  -- enumeration universe
  En : Set
  En = List Tag

  -- tag choices
  data #_ : En → Set where
    ze : ∀ {t E}             → # (t ∷ E)
    su : ∀ {t E} → (n : # E) → # (t ∷ E)

  π : ∀ {ℓ} (E : En) (P : # E → Set ℓ) → Set ℓ
  π {ℓ} []  P = Lift ℓ ⊤
  π (t ∷ E) P = P ze × π E λ x → P (su x)

  switch : (E : En) (P : # E → Set) → π E P → (x : # E) → P x
  switch (t ∷ E) P (π₀ , _) ze     = π₀
  switch (t ∷ E) P (_ , π₁) (su x) = switch E (λ x → P (su x)) π₁ x


module Inductive where

  open Enumerations

  data Desc {ℓ} : Set (lsuc ℓ) where
    ′1    :                                    Desc
    ′Σ    : (S : Set ℓ) → (D : S → Desc {ℓ}) → Desc
    ′ind× : Desc {ℓ}                         → Desc

  ⟦_⟧ : ∀ {ℓ} → Desc {ℓ} → Set ℓ → Set ℓ
  ⟦_⟧ {ℓ} ′1  t = Lift ℓ ⊤
  ⟦ ′Σ S D ⟧  t = Σ S λ s → ⟦ D s ⟧ t
  ⟦ ′ind× D ⟧ t = t × ⟦ D ⟧ t

  NatD : Desc
  NatD = ′Σ (# (′ "zero" ∷ ′ "suc" ∷ [])) λ where
    ze      → ′1
    (su ze) → ′ind× ′1

  injzero : ∀ {Z} → ⟦ NatD ⟧ Z
  injzero = ze , lift tt

  injsucc : ∀ {Z} → Z → ⟦ NatD ⟧ Z
  injsucc n = su ze , n , lift tt

  ListD : Set → Desc
  ListD X = ′Σ (# (′ "nil" ∷ ′ "cons" ∷ [])) λ where
    ze      → ′1
    (su ze) → ′Σ X λ _ → ′ind× ′1

  TreeD : Set → Desc
  TreeD X = ′Σ (# (′ "leaf" ∷ ′ "node" ∷ [])) λ where
    ze      → ′1
    (su ze) → ′ind× (′Σ X λ _ → ′ind× ′1)

  data μ {l} (D : Desc {l}) {s : Size} : Set l where
    ⟨_⟩ : {t : Size< s} → ⟦ D ⟧ (μ D {t}) → μ D {s}

  Nat : Set
  Nat = μ NatD

  zz : Nat
  zz = ⟨ ze , lift tt ⟩

  ss : Nat → Nat
  ss x = ⟨ su ze , x , lift tt ⟩

  All : ∀ {ℓ} (D : Desc {ℓ}) (X : Set ℓ) (P : X → Set ℓ) (xs : ⟦ D ⟧ X) → Set (lsuc ℓ)
  All {ℓ} ′1    X P _       = Lift (lsuc ℓ) ⊤
  All (′Σ S D)  X P (s , d) = All (D s) X P d
  All (′ind× D) X P (x , d) = P x × All D X P d

  all : ∀ {ℓ} (D : Desc {ℓ}) (X : Set ℓ) (P : X → Set ℓ)
      → (p : (x : X) → P x)
      → (xs : ⟦ D ⟧ X)
      → All D X P xs
  all ′1        X P p _       = lift tt
  all (′Σ S D)  X P p (s , d) = all (D s) X P p d
  all (′ind× D) X P p (x , d) = p x , all D X P p d

  ind : ∀ {ℓ s} (D : Desc {ℓ}) (P : ∀ {s} → μ D {s} → Set ℓ)
      → (∀ {s} {t : Size< s} (d : ⟦ D ⟧ (μ D {t})) → All D (μ D {t}) P d → P {s} ⟨ d ⟩)
      → (x : μ D {s})
      → P x

  ind D P m ⟨ d ⟩ = m d (all D (μ D) P (ind D P m) d)
