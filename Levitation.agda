module Levitation where

open import Data.String
open import Data.Product
open import Data.Unit
open import Data.Unit

-- all of this is taken directly from The Gentle Art of Levitation
--                                    Chapman, Dagand, McBride & Morris

module Enumerations where

  infix 30 ′_
  infixr 20 _∷_
  
  data Tag : Set where
    ′_ : String → Tag

  -- enumeration universe
  data En : Set where
    []  : En
    _∷_ : (t : Tag) → (E : En) → En

  -- tag choices
  data #_ : En → Set where
    ze : ∀ {t E}             → # (t ∷ E)
    su : ∀ {t E} → (n : # E) → # (t ∷ E)

  π : (E : En) (P : # E → Set) → Set
  π []      P = ⊤
  π (t ∷ E) P = P ze × π E λ x → P (su x)

  switch : (E : En) (P : # E → Set) → π E P → (x : # E) → P x
  switch (t ∷ E) P (π₀ , _) ze     = π₀
  switch (t ∷ E) P (_ , π₁) (su x) = switch E (λ x → P (su x)) π₁ x


module Inductive where

  open Enumerations

  data Desc : Set₁ where
    ′1    :                              Desc
    ′Σ    : (S : Set) → (D : S → Desc) → Desc
    ′ind× : Desc                       → Desc

  ⟦_⟧ : Desc → Set → Set
  ⟦ ′1 ⟧      t = ⊤
  ⟦ ′Σ S D ⟧  t = Σ S λ s → ⟦ D s ⟧ t
  ⟦ ′ind× D ⟧ t = t × ⟦ D ⟧ t

  NatD : Desc
  NatD = ′Σ (# (′ "zero" ∷ ′ "suc" ∷ [])) λ where
    ze      → ′1
    (su ze) → ′ind× ′1

  injzero : ∀ {Z} → ⟦ NatD ⟧ Z
  injzero = ze , tt

  injsucc : ∀ {Z} → Z → ⟦ NatD ⟧ Z
  injsucc n = su ze , n , tt

  ListD : Set → Desc
  ListD X = ′Σ (# (′ "nil" ∷ ′ "cons" ∷ [])) λ where
    ze      → ′1
    (su ze) → ′Σ X λ _ → ′ind× ′1

  TreeD : Set → Desc
  TreeD X = ′Σ (# (′ "leaf" ∷ ′ "node" ∷ [])) λ where
    ze      → ′1
    (su ze) → ′ind× (′Σ X λ _ → ′ind× ′1)
