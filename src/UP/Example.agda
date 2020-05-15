{-# OPTIONS --cubical #-}

module UP.Example where

open import UP.UP
open import UP.Reflection

open import Data.Nat.Base as ℕ
open import Data.Nat.Binary.Base as ℕᵇ using (ℕᵇ; fromℕ; toℕ)
open import Data.Nat.Binary.Properties

postulate
 ℕ≡ℕᵇ : ℕ ≡ ℕᵇ

instance
  ℕ⋈ℕᵇ : ℕ ⋈ ℕᵇ
  ℕ⋈ℕᵇ = UR [ ℕ≡ℕᵇ ]_≡_
  
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
