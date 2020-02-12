{-# OPTIONS --type-in-type #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma


_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

const : {A B : Set} → B → A → B
const x = λ _ → x

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
_∘_ g f x = g (f x)

data nat : Set where
  ze : nat
  su : nat → nat
{-# BUILTIN NATURAL nat #-}

data fin : nat → Set where
  ze : ∀ {n} → fin (su n)
  su : ∀ {n} → fin n → fin (su n)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x


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
  natlistD = ι ∣ nat ⊗ const (rec-⊗ ι) ∣ ε

  natlist = μ natlistD

  nil′ : natlist
  nil′ = ⟨ ze , tt ⟩

  cons′ : nat → natlist → natlist
  cons′ x l = ⟨ su ze , x , l , tt ⟩


  {- data homlist : Set where
       nil : homlist
       cons : (A : Set) → A → natlist → homlist -}

  homlistD : DatDesc 2
  homlistD = ι ∣ Set ⊗ (λ A → A ⊗ const (rec-⊗ ι)) ∣ ε

  homlist = μ homlistD

  nil″ : homlist
  nil″ = ⟨ ze , tt ⟩

  cons″ : ∀ {A} A → homlist → homlist
  cons″ {A} x l = ⟨ su ze , A , x , l , tt ⟩


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
    Γ ▷′ B = Γ ▷ const B

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


module Indexed where

  infixr 4 _∣_
  infixr 5 _⊗_

  open Parametrized using (Ctx; _▷_; ε; _▷′_; ⟦_⟧Ctx)

  data ConDesc (Γ : Ctx) (I : Ctx) : Set where
    ι       : (⟦ Γ ⟧Ctx → ⟦ I ⟧Ctx) → ConDesc Γ I
    _⊗_    : (S : ⟦ Γ ⟧Ctx → Set) → (D : ConDesc (Γ ▷ S) I) → ConDesc Γ I
    rec_⊗_ : (r : ⟦ Γ ⟧Ctx → ⟦ I ⟧Ctx) → (D : ConDesc Γ I) → ConDesc Γ I

  data DatDesc (Γ : Ctx) (I : Ctx) : nat → Set where
    ε : DatDesc Γ I 0
    _∣_ : ∀ {n} → (C : ConDesc Γ I) → (D : DatDesc Γ I n) → DatDesc Γ I (su n)

  lookup : ∀ {Γ I n} → DatDesc Γ I n → fin n → ConDesc Γ I
  lookup (C ∣ D) ze     = C
  lookup (C ∣ D) (su k) = lookup D k

  ⟦_⟧c : ∀ {Γ I} → ConDesc Γ I → ⟦ Γ ⟧Ctx → (⟦ I ⟧Ctx → Set) → (⟦ I ⟧Ctx → Set)
  ⟦ ι f ⟧c γ X i = f γ ≡ i
  ⟦ S ⊗ D ⟧c γ X i = Σ (S γ) λ s → ⟦ D ⟧c (γ , s) X i
  ⟦ rec r ⊗ D ⟧c γ X i = X (r γ) × ⟦ D ⟧c γ X i

  ⟦_⟧d : ∀ {Γ I n} → DatDesc Γ I n → ⟦ Γ ⟧Ctx → (⟦ I ⟧Ctx → Set) → (⟦ I ⟧Ctx → Set)
  ⟦_⟧d {n = n} D γ X i = Σ (fin n) λ k → ⟦ lookup D k ⟧c γ X i


  data μ {n Γ I} (D : DatDesc Γ I n) (γ : ⟦ Γ ⟧Ctx) (i : ⟦ I ⟧Ctx) : Set where
    ⟨_⟩ : ⟦ D ⟧d γ (μ D γ) i → μ D γ i

  vecD : DatDesc (ε ▷′ Set) (ε ▷′ nat) 2
  vecD = ι (const (tt , 0))
       ∣ const nat ⊗ snd ∘ fst ⊗ rec (λ γ → tt , snd (fst γ)) ⊗ ι (λ γ → tt , su (snd (fst γ)))
       ∣ ε

  vec : Set → nat → Set
  vec A n = μ vecD (tt , A) (tt , n)

  nil : ∀ {A} → vec A 0
  nil = ⟨ ze , refl ⟩

  cons : ∀ {A n} → A → vec A n → vec A (su n)
  cons {n = n} x xs = ⟨ su ze , n , x , xs , refl ⟩

  v₁ : vec nat 2
  v₁ = cons 3 (cons 1 nil)
