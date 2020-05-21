{-# OPTIONS --safe --without-K #-}

open import Generics.Prelude

module Generics.Desc (Eq : Equality) where

open Equality Eq using (_≡_; refl)


module Simple where

  data ConDesc {ℓ} (I : Set ℓ) : Set (lsuc ℓ) where
    κ : (γ : I)                           → ConDesc I
    ι : (γ : I)     → (C : ConDesc I)     → ConDesc I
    π : (S : Set ℓ) → (C : S → ConDesc I) → ConDesc I
  
  ⟦_⟧ᶜ : ∀ {ℓ} {I : Set ℓ} → ConDesc I → (I → Set ℓ) → I → Set ℓ
  ⟦ ι γ D ⟧ᶜ X i = X γ × ⟦ D ⟧ᶜ X i
  ⟦ κ k   ⟧ᶜ X i = k ≡ i
  ⟦ π S D ⟧ᶜ X i = Σ[ s ∈ S ] (⟦ D s ⟧ᶜ X i)
  
  syntax π A (λ s → D) = π[ s ∈ A ] D
  
  
  Desc : ∀ {ℓ} (I : Set ℓ) → Nat → Set (lsuc ℓ)
  Desc {ℓ} I = Vec (ConDesc I)
  
  ⟦_⟧ᵈ : ∀ {ℓ n} {I : Set ℓ} → Desc I n → (I → Set ℓ) → I → Set ℓ
  ⟦_⟧ᵈ {n = n} D X i = Σ[ k ∈ Fin n ] (⟦ lookup D k ⟧ᶜ X i)
  
  
  data μ {i n} {I : Set i} (D : Desc I n) (γ : I) : Set i where
    ⟨_⟩ : ⟦ D ⟧ᵈ (μ D) γ → μ D γ


module Parametrized where

  infixl 3 _▷_

  data Tele (k : Level) : Set (lsuc k)
  data ExTele {k : Level} : Tele k → Set (lsuc k)
  ⟦_⟧ᵗ : Tele k → Set k
  ⟦_⟧ˣᵗ : {T : Tele k} → ExTele T → Set k

  
  data Tele k where
    ε   : Tele k
    _▷_ : (T : Tele k) → (⟦ T ⟧ᵗ → Set k) → Tele k

  _▷′_ : Tele k → Set k → Tele k
  T ▷′ S = T ▷ const S

  ⟦ ε ⟧ᵗ     = ⊤′
  ⟦ T ▷ F ⟧ᵗ = Σ ⟦ T ⟧ᵗ F

  -- extension of telescopes
  data ExTele {k} where
    tele : ∀ T → ExTele T
    _▷_  : ∀ {T} → (Γ : ExTele T) → (⟦ Γ ⟧ˣᵗ → Set k) → ExTele T

  ⟦_⟧ˣᵗ (tele T) = ⟦ T ⟧ᵗ
  ⟦ T ▷ F ⟧ˣᵗ = Σ ⟦ T ⟧ˣᵗ F

  -- given an interpretation of an extended telescope, we can truncate
  drop : {T : Tele k} (Γ : ExTele T) → ⟦ Γ ⟧ˣᵗ → ⟦ T ⟧ᵗ
  drop (tele _) γ = γ
  drop (Γ ▷ F) (γ , _) = drop Γ γ

  data ConDesc {P : Tele k} (Γ : ExTele P) (I : ⟦ P ⟧ᵗ → Set k) : Set (lsuc k)

  data ConDesc {k} {P} Γ I where
    κ : ((γ : ⟦ Γ ⟧ˣᵗ) → I (drop Γ γ)) → ConDesc Γ I
    ι : (⟦ Γ ⟧ˣᵗ → ⟦ P ▷ I ⟧ᵗ) → ConDesc Γ I → ConDesc Γ I
    π : (S : ⟦ Γ ⟧ˣᵗ → Set k) → ConDesc (Γ ▷ S) I → ConDesc Γ I

  ⟦_⟧ᶜ : {P : Tele k} {Γ : ExTele P} {I : ⟦ P ⟧ᵗ → Set k}
       → ConDesc Γ I → (⟦ P ▷ I ⟧ᵗ → Set k) → Σ ⟦ Γ ⟧ˣᵗ (I ∘ drop Γ) → Set k
  ⟦ κ f ⟧ᶜ X (g , i)   = f g ≡ i
  ⟦ ι f C ⟧ᶜ X (g , i) = (X (f g)) × ⟦ C ⟧ᶜ X (g , i)
  ⟦ π S C ⟧ᶜ X (g , i) = Σ[ s ∈ S g ] ⟦ C ⟧ᶜ X ((g , s) , i)

  Desc : (P : Tele k) (I : ⟦ P ⟧ᵗ → Set k) → Nat → Set (lsuc k)
  Desc P I = Vec (ConDesc (tele P) I)

  ⟦_⟧ᵈ : {P : Tele k} {I : ⟦ P ⟧ᵗ → Set k} {n : Nat}
       → Desc P I n → (⟦ P ▷ I ⟧ᵗ → Set k) → ⟦ P ▷ I ⟧ᵗ → Set k
  ⟦ D ⟧ᵈ X gi = Σ[ k ∈ Fin _ ] ⟦ lookup D k ⟧ᶜ X gi

  data μ {n} {P : Tele k} {I : ⟦ P ⟧ᵗ → Set k} (D : Desc P I n) (gi : ⟦ P ▷ I ⟧ᵗ) : Set k where
    ⟨_⟩ : ⟦ D ⟧ᵈ (μ D) gi → μ D gi
  

  natD : Desc ε (const ⊤) 2
  natD = κ (const tt)
       ∷ ι (const (tt , tt)) (κ (const tt))
       ∷ []

  nat : Set
  nat = μ natD (tt , tt)

  nze : nat
  nze = ⟨ zero , refl ⟩

  nsu : nat → nat
  nsu n = ⟨ suc zero , n , refl ⟩


  finD : Desc ε (const nat) 2
  finD = π (const nat) (κ (nsu ∘ snd))
       ∷ π (const nat) (ι ((tt ,_) ∘ snd) (κ (nsu ∘ snd)))
       ∷ []

  fin : nat → Set
  fin n = μ finD (tt , n)

  fze : ∀ {n} → fin (nsu n)
  fze {n} = ⟨ zero , n , refl ⟩

  fsu : ∀ {n} → fin n → fin (nsu n)
  fsu {k} n = ⟨ suc zero , k , n , refl ⟩


  listD : Desc (ε ▷ const (Set k)) (const ⊤′) 2
  listD = κ (const tt)
        ∷ π (Lift ∘ snd) (ι (λ where (γ , _) → γ , tt) (κ λ γ → tt))
        ∷ []

  list : Set k → Set (lsuc k)
  list A = μ listD ((tt , A) , tt)

  nil : {A : Set k} → list A
  nil {A} = ⟨ zero , refl ⟩

  cons : {A : Set k} → A → list A → list A
  cons x xs = ⟨ suc zero , lift x , xs , refl ⟩


  -- hack because universes are annoying
  data N {k} : Set k where
    Z : N
    S : N {k} → N

  
  vecD : Desc (ε ▷ const (Set k)) (const N) 2
  vecD = κ (const Z)
       ∷ π (const N) (π (Lift ∘ snd ∘ fst) (ι fst (κ (S ∘ (snd ∘ fst)))))
       ∷ []

  vec : Set k → N → Set (lsuc k)
  vec A n = μ vecD ((tt , A) , n)

  vnil : {A : Set k} → vec A Z
  vnil = ⟨ zero , refl ⟩

  vcons : {A : Set k} {n : N} → A → vec A n → vec A (S n)
  vcons {n = n} x xs = ⟨ suc zero , n , lift x , xs , refl ⟩
