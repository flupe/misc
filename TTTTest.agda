{-# OPTIONS --type-in-type #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma


_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

data nat : Set where
  ze : nat
  su : nat → nat
{-# BUILTIN NATURAL nat #-}

data fin : nat → Set where
  ze : ∀ {n} → fin (su n)
  su : ∀ {n} → fin n → fin (su n)


module NonParametrized where

  infixr 5 _⊗_ 
  infixr 4 _∣_ 
  
  data ConDesc : Set where
    ι : ConDesc
    _⊗_ : (S : Set) → (D : S → ConDesc) → ConDesc
    rec-⊗_ : (D : ConDesc) → ConDesc
  
  data DatDesc : nat → Set where
    ε : DatDesc 0
    _∣_ : ∀ {n} → (C : ConDesc) → (D : DatDesc n) → DatDesc (su n)
  
  lookup : ∀ {n} → DatDesc n → fin n → ConDesc
  lookup (C ∣ D) ze     = C
  lookup (C ∣ D) (su k) = lookup D k
  
  ⟦_⟧c : ConDesc → Set → Set
  ⟦ ι ⟧c X       = ⊤
  ⟦ S ⊗ D ⟧c X   = Σ S λ s → ⟦ D s ⟧c X
  ⟦ rec-⊗ D ⟧c X = X × ⟦ D ⟧c X
  
  ⟦_⟧d : ∀ {n} → DatDesc n → Set → Set
  ⟦_⟧d {n} D X = Σ (fin n) λ k → ⟦ lookup D k ⟧c X
  
  natD : DatDesc 2
  natD = ι ∣ rec-⊗ ι ∣ ε
  
  data μ {n} (D : DatDesc n) : Set where
    ⟨_⟩ : ⟦ D ⟧d (μ D) → μ D
  
  nat′ : Set
  nat′ = μ natD
  
  ze′ : nat′
  ze′ = ⟨ ze , tt ⟩
  
  su′ : nat′ → nat′
  su′ x = ⟨ su ze , x , tt ⟩
  

  {- data natlist : Set where
       nil : natlist
       cons : nat → natlist → nat -}

  natlistD : DatDesc 2
  natlistD = ι ∣ nat ⊗ (λ _ → rec-⊗ ι) ∣ ε

  natlist = μ natlistD

  nil′ : natlist
  nil′ = ⟨ ze , tt ⟩

  cons′ : nat → natlist → natlist
  cons′ x l = ⟨ su ze , x , l , tt ⟩


module Parametrized where

  mutual

    infixl 5 _▷_
    infixl 5 _▷′_
    infixr 4 _∣_
    infixr 5 _⊗_
  
    data Ctx : Set where
        ε   : Ctx
        _▷_ : (Γ : Ctx) (S : ⟦ Γ ⟧Ctx → Set) → Ctx

    _▷′_ : Ctx → Set → Ctx
    Γ ▷′ B = Γ ▷ λ _ → B

    ⟦_⟧Ctx : Ctx → Set
    ⟦ ε ⟧Ctx     = ⊤
    ⟦ Γ ▷ S ⟧Ctx = Σ ⟦ Γ ⟧Ctx S


  data ConDesc (Γ : Ctx) : Set where
    ι      : ConDesc Γ
    _⊗_    : (S : ⟦ Γ ⟧Ctx → Set) → (D : ConDesc (Γ ▷ S)) → ConDesc Γ
    rec-⊗_ : (D : ConDesc Γ) → ConDesc Γ
  

  data DatDesc (Γ : Ctx) : nat → Set where
    ε : DatDesc Γ 0
    _∣_ : ∀ {n} → (C : ConDesc Γ) → (D : DatDesc Γ n) → DatDesc Γ (su n)

  lookup : ∀ {Γ n} → DatDesc Γ n → fin n → ConDesc Γ
  lookup (C ∣ D) ze     = C
  lookup (C ∣ D) (su k) = lookup D k
  

  ⟦_⟧c : ∀ {Γ} → ConDesc Γ → ⟦ Γ ⟧Ctx → Set → Set
  ⟦ ι ⟧c γ X = ⊤
  ⟦ S ⊗ D ⟧c γ X = Σ (S γ) λ s → ⟦ D ⟧c (γ , s) X
  ⟦ rec-⊗ D ⟧c γ X = X × ⟦ D ⟧c γ X
  
  ⟦_⟧d : ∀ {Γ n} → DatDesc Γ n → ⟦ Γ ⟧Ctx → Set → Set
  ⟦_⟧d {n = n} D γ X = Σ (fin n) λ k → ⟦ lookup D k ⟧c γ X


  data μ {n Γ} (D : DatDesc Γ n) (γ : ⟦ Γ ⟧Ctx) : Set where
    ⟨_⟩ : ⟦ D ⟧d γ (μ D γ) → μ D γ
  

  listD : DatDesc (ε ▷′ Set) 2
  listD = ι ∣ snd ⊗ rec-⊗ ι ∣ ε

  list : Set → Set
  list A = μ listD (tt , A)

  nil : ∀ {A} → list A
  nil = ⟨ ze , tt ⟩

  cons : ∀ {A} → A → list A → list A
  cons x xs = ⟨ su ze , x , xs , tt ⟩

  t : list nat
  t = cons 5 (cons 3 nil)

