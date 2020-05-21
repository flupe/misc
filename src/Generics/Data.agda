{-# OPTIONS --safe --without-K #-}

open import Generics.Prelude

module Generics.Data (Eq : Equality) where

open import Generics.Desc Eq
open Equality Eq

open Simple


module _ {I : Set a} {A : I → Set a} where

  -- type of a constructor given its description
  con-type : ConDesc I → Set a
  con-type (κ γ)   = A γ 
  con-type (ι γ C) = A γ     → con-type C
  con-type (π S C) = (s : S) → con-type (C s)

  con-proof-type′ : ∀ {n} {D : Desc I n} 
              → (to : {γ : I} → A γ → μ D γ)
              → {C : ConDesc I} (tie : {γ : I} → ⟦ C ⟧ᶜ (μ D) γ → A γ → Set a)
              → con-type C → Set a
  con-proof-type′ to {κ γ}   tie c = tie refl c
  con-proof-type′ to {ι γ C} tie c = (x : A γ) → con-proof-type′ to {C = C} (tie ∘ (to x ,_)) (c x)
  con-proof-type′ to {π S C} tie c = (s : S)   → con-proof-type′ to {C = C s} (tie ∘ (s ,_)) (c s) 

  -- predicate that a given function is equivalent to the described constructor
  -- pretty sure this is saying that our function is univalently related to
  -- the interpretation of the constructor description at the constructor type
  con-proof-type : ∀ {n} {D : Desc I n} 
                   (to   : {γ : I} → A γ → μ D γ)
                   (from : {γ : I} → μ D γ → A γ)
                 → ∀ {k} (constr : con-type (lookup D k))
                 → Set a
  con-proof-type {D = D} to from {k} constr =
    con-proof-type′ to {lookup D k} tie constr
    where
      tie : {γ : I} → ⟦ lookup D k ⟧ᶜ (μ D) γ → A γ → Set a
      tie X′ X = X ≡ from ⟨ k , X′ ⟩

  

record HasDesc {I : Set a} (A : I → Set a) : Set (lsuc a) where
  field
    {n} : Nat
    D : Desc {a} I n

    to   : ∀ {i} → A i → μ D i
    from : {i : I} → μ D i → A i

    to∘from : ∀ {i} (x : μ D i) → to (from x) ≡ x
    from∘to : ∀ {i} (x : A i)   → from (to x) ≡ x

    step   : ∀ {i} → A i → ⟦ D ⟧ᵈ A i
    unstep : ∀ {i} → ⟦ D ⟧ᵈ A i → A i

    unstep∘step : ∀ {i} (x : A i) → unstep (step x) ≡ x
    step∘unstep : ∀ {i} (x : ⟦ D ⟧ᵈ A i) → step (unstep x) ≡ x

    -- | constructors of A
    constr : (k : Fin n) → con-type (lookup D k)

    -- | A proof that constr contains the constructors of A
    constr-proof : (k : Fin n) → con-proof-type to from (constr k)
