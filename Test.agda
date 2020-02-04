open import Data.Bool
open import Data.Unit


data Code : Set where
  unit : Code
  sum  : (a b : Code) → Code


module Interpretor (t : Set) where

  data ⟦_⟧ : Code → Set where
    unit : t                       → ⟦ unit    ⟧
    sum  : ∀ {a b} → ⟦ a ⟧ → ⟦ b ⟧ → ⟦ sum a b ⟧

  RecType       : ∀ {c} → ⟦ c ⟧ → Set → Set
  RecTypeHelper : ∀ {c} → ⟦ c ⟧ → Set → Set

  -- probably still wrong somewhat
  RecType (unit x) t′ = t → t′ → t′
  RecType i        t′ = t → RecTypeHelper i t′

  RecTypeHelper (unit x)    t′ = t′
  RecTypeHelper (sum i₁ i₂) t′ = RecTypeHelper i₁ t′ → RecTypeHelper i₂ t′ → t′


record Interp (A : Set) : Set₁ where
  open Interpretor A

  field
    code   : Code
    interp : ⟦ code ⟧
    elim   : ∀ {t} → RecType interp t

open Interp ⦃ ... ⦄ public


module BoolInterp where

  open Interpretor Bool

  instance
    interpBool : Interp Bool
    code   ⦃ interpBool ⦄ = sum unit unit
    interp ⦃ interpBool ⦄ = sum (unit true) (unit true)
    elim   ⦃ interpBool ⦄ = if_then_else_


module UnitInterp where

  open Interpretor ⊤

  instance
    interp⊤ : Interp ⊤
    code   ⦃ interp⊤ ⦄ = unit
    interp ⦃ interp⊤ ⦄ = unit tt
    elim   ⦃ interp⊤ ⦄ tt x = x
