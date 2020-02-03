open import Data.Bool


data Code : Set where
  unit : Code
  sum  : (a b : Code) → Code


module Interpretor (t : Set) where

  data ⟦_⟧ : Code → Set where
    unit : t                       → ⟦ unit    ⟧
    sum  : ∀ {a b} → ⟦ a ⟧ → ⟦ b ⟧ → ⟦ sum a b ⟧

  RecType       : ∀ {c} → ⟦ c ⟧ → Set → Set
  RecTypeHelper : ∀ {c} → ⟦ c ⟧ → Set → Set

  RecType i t′ = t → RecTypeHelper i t′

  RecTypeHelper (unit x)    t′ = t′
  RecTypeHelper (sum i₁ i₂) t′ = RecTypeHelper i₁ t′ → RecTypeHelper i₂ t′ → t′


module BoolInterp where

  open Interpretor Bool

  interp : ⟦ sum unit unit ⟧
  interp = sum (unit true) (unit false)

  recursor : ∀ {t} → RecType interp t
  recursor = if_then_else_
