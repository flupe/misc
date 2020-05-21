{-# OPTIONS --cubical --without-K #-}
module Generics.UP.Generic where

open import Generics.UP.Prelude
open import Generics.UP.Core

open Simple

module Indexed {I : Set a} {n} (D : Desc I n) where
  
  UR-Con : (γ₁ γ₂ : I) (C : ConDesc I)
           (f : ⟦ C ⟧ᶜ (μ D) γ₁ → μ D γ₁)
           (g : ⟦ C ⟧ᶜ (μ D) γ₂ → μ D γ₂)
         → ConDesc (Σ I (μ D) × Σ I (μ D))

  UR-Con γ₁ γ₂ (κ γ) f g = π[ p ∈ γ ≡ γ₁ ]
                           π[ q ∈ γ ≡ γ₂ ]
                           κ ((γ₁ , f p) , (γ₂ , g q))

  UR-Con γ₁ γ₂ (ι γ C) f g = π[ x ∈ μ D γ ]
                             π[ y ∈ μ D γ ]
                             ι ((γ , x) , (γ , y))
                               (UR-Con γ₁ γ₂ C (f ∘ (x ,_)) (g ∘ (y ,_)))

  -- this is bad: we want to have s : A, t : A, [ A⋈B ] s ≈ t
  -- notice how if we do this, we cannot possibly have F s = F t
  -- this is because our encoding is not restrictive enough
  UR-Con γ₁ γ₂ (π S F) f g = π[ s ∈ S ]
                             UR-Con γ₁ γ₂ (F s) (f ∘ (s ,_)) (g ∘ (s ,_))

  UR-μ : {γ₁ γ₂ : I} → Desc (Σ I (μ D) × Σ I (μ D)) n
  UR-μ {γ₁} {γ₂} = mapi (λ k C → UR-Con γ₁ γ₂ C {!!} {!!}) D

  data UR : ∀ {γ₁ γ₂} → μ D γ₁ → μ D γ₂ → Set a where
    con : ∀ {γ₁ γ₂} {x : μ D γ₁} {y : μ D γ₂}
        → μ (UR-μ {γ₁} {γ₂}) ((γ₁ , x) , (γ₂ , y))
        → UR x y

  -- μ≈μ : ∀ {i₁ i₂} → [ I⋈I ] i₁ ≈ i₂ → μ D i₁ ⋈ μ D i₁
  -- μ≈μ i₁≈i₂ .ur = UR
  -- μ≈μ i₁≈i₂ .eq = {!!}
  -- μ≈μ i₁≈i₂ .co = {!!}


module Example where
  natD : Desc ⊤ 2
  natD = κ tt
       ∷ ι tt (κ tt)
       ∷ []

  nat : Set
  nat = μ natD tt

  ze : nat
  ze = ⟨ zero , refl ⟩

  su : nat → nat
  su n = ⟨ suc zero , n , refl ⟩

  finD : Desc nat 2
  finD = π[ n ∈ nat ] κ (su n)
       ∷ π[ n ∈ nat ] ι n (κ (su n))
       ∷ []

  fin : nat → Set
  fin n = μ finD n
