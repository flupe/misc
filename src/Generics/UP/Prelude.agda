{-# OPTIONS --cubical --without-K #-}

module Generics.UP.Prelude where

open import Generics.Prelude public
open import Agda.Builtin.Cubical.Path public
open import Cubical.Foundations.Prelude hiding (Lift; Σ-syntax) public
open import Cubical.Foundations.Equiv
  renaming ( invEquiv to ≃-sym
           ; idEquiv  to ≃-refl
           )
  public
open import Cubical.Foundations.Univalence public

Eq : Equality
Eq = record
  { _≡_  = _≡_
  ; refl = refl
  ; sym  = sym
  ; transport = λ P x y → subst P x y
  ; subst = transport -- I know, I know
  ; cong = λ f p → cong f p
  ; J = J
  ; JRefl = JRefl
  }

open import Generics.Desc Eq public
open import Generics.Data Eq public
open import Generics.Constructions Eq public
