{-# OPTIONS --type-in-type #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.List

module TTTTest where

_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

const : {A B : Set} → B → A → B
const x = λ _ → x

case_of_ : {A B : Set} → A → (A → B) → B
case x of f = f x

infixr 10 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
_∘_ g f x = g (f x)

data bool : Set where
  tt ff : bool

data fin : Nat → Set where
  ze : ∀ {n} → fin (suc n)
  su : ∀ {n} → fin n → fin (suc n)

data either (A B : Set) : Set where
  inl : A → either A B
  inr : B → either A B

data maybe (A : Set) : Set where
  just : A → maybe A
  nothing : maybe A

data _≡_ {A : Set} (x : A) : {B : Set} → B → Set where
  refl : x ≡ x


cong : ∀ {A B x y} (f : A → B) (e : x ≡ y) → f x ≡ f y
cong f refl = refl

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≢_ : {A : Set} {B : Set} (x : A) (y : B) → Set
x ≢ y = ¬ (x ≡ y)

data dec (A : Set) : Set where
  yes : A   → dec A
  no  : ¬ A → dec A

bimap : ∀ {A C : Set} {x y : A} → (x ≡ y → C) → (x ≢ y → ¬ C) → dec (x ≡ y) → dec C
bimap f g (yes a) = yes (f a)
bimap f g (no  b) = no (g b)

injsu : ∀ {n} {x y : fin n} → _≡_ {fin (suc n)} (su x) {fin (suc n)} (su y) → x ≡ y
injsu refl = refl

contr : ∀ {A B} (f : A → B) → ¬ B → ¬ A
contr f ¬B a = ¬B (f a)

-- bad naming
path_sigma : {A : Set} {B : A → Set} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
           → a₁ ≡ a₂ → b₁ ≡ b₂ → _≡_ {Σ A B} (a₁ , b₁) {Σ A B} (a₂ , b₂)
path_sigma refl refl = refl

path_sigma₁ : {A : Set} {B : A → Set} {a b : Σ A B}
            → a ≡ b → fst a ≡ fst b
path_sigma₁ refl = refl

path_sigma₂ : {A : Set} {B : A → Set} {a b : Σ A B}
            → a ≡ b → snd a ≡ snd b
path_sigma₂ refl = refl

path_sigma_neq : {A : Set} {B : A → Set} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
           → either (a₁ ≢ a₂) (b₁ ≢ b₂) → ¬ (_≡_ {Σ A B} (a₁ , b₁) {Σ A B} (a₂ , b₂))
path_sigma_neq (inl a₁≢a₂) = λ a≡b → a₁≢a₂ (path_sigma₁ a≡b) 
path_sigma_neq (inr b₁≢b₂) = λ a≡b → b₁≢b₂ (path_sigma₂ a≡b)


record eq (A : Set) : Set where
  field
    _≟_ : (x y : A) → dec (x ≡ y)

open eq {{...}}

_==_ : {A : Set} {{eqA : eq A}} (x y : A) → bool
_==_ {{eqA}} x y with x ≟ y
...                 | yes _ = tt
...                 | no  _ = ff

instance
  eqfin : ∀ {n} → eq (fin n)
  _≟_ ⦃ eqfin ⦄ ze ze         = yes refl
  _≟_ ⦃ eqfin ⦄ ze (su b)     = no λ ()
  _≟_ ⦃ eqfin ⦄ (su a) ze     = no λ ()
  _≟_ ⦃ eqfin ⦄ (su a) (su b) = bimap (cong su) (_∘ injsu) (a ≟ b) 

record Monad (M : Set → Set) : Set where
  field
    return : {A : Set} → A → M A
    _>>=_   : {A B : Set} → M A → (A → M B) → M B
open Monad {{...}}

_>>_ : {A B : Set} {M : Set → Set} {{_ : Monad M}} (a : M A) (b : M B) → M B
a >> b = a >>= (const b)

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

length : {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

finlist : (n : Nat) → List (fin n)
finlist 0       = []
finlist (suc n) = ze ∷ map su (finlist n)

module NonParametrized where

  infixr 5 _⊗_ 
  infixr 4 _∣_ 
  
  data ConDesc : Set where
    ι : ConDesc
    _⊗_ : (S : Set) → (D : S → ConDesc) → ConDesc
    rec-⊗_ : (D : ConDesc) → ConDesc
  
  data DatDesc : Nat → Set where
    ε : DatDesc 0
    _∣_ : ∀ {n} → (C : ConDesc) → (D : DatDesc n) → DatDesc (suc n)
  
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
  natlistD = ι ∣ Nat ⊗ const (rec-⊗ ι) ∣ ε

  natlist = μ natlistD

  nil′ : natlist
  nil′ = ⟨ ze , tt ⟩

  cons′ : Nat → natlist → natlist
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

  infixl 20 _▷_ _▷′_
  infixl 20 _▶_

  mutual

    infixr 4 _∣_
    infixr 5 _⊗_
  
    data Ctx : Set where
        ε   : Ctx
        _▷_ : (Γ : Ctx) (S : ⟦ Γ ⟧Ctx → Set) → Ctx

    ⟦_⟧Ctx : Ctx → Set
    ⟦ ε     ⟧Ctx = ⊤
    ⟦ Γ ▷ S ⟧Ctx = Σ ⟦ Γ ⟧Ctx S

  _▷′_ : Ctx → Set → Ctx
  Γ ▷′ B = Γ ▷ const B

  _▶_ : ∀ {Γ S} → (γ : ⟦ Γ ⟧Ctx) → S γ → ⟦ Γ ▷ S ⟧Ctx
  _▶_ = _,_

  module _ where
    
    ex₁ : ⟦ ε ⟧Ctx
    ex₁ = tt

    ex₂ : ⟦ ε ▷′ Set ▷ snd ⟧Ctx
    ex₂ = tt ▶ Nat ▶ 3

  data ConDesc (Γ : Ctx) : Set where
    ι      : ConDesc Γ
    _⊗_    : (S : ⟦ Γ ⟧Ctx → Set) → (D : ConDesc (Γ ▷ S)) → ConDesc Γ
    rec-⊗_ : (D : ConDesc Γ) → ConDesc Γ
  

  data DatDesc (Γ : Ctx) : Nat → Set where
    ε : DatDesc Γ 0
    _∣_ : ∀ {n} → (C : ConDesc Γ) → (D : DatDesc Γ n) → DatDesc Γ (suc n)

  lookup : ∀ {Γ n} → DatDesc Γ n → fin n → ConDesc Γ
  lookup (C ∣ D) ze     = C
  lookup (C ∣ D) (su k) = lookup D k
  

  ⟦_⟧c : ∀ {Γ} → ConDesc Γ → ⟦ Γ ⟧Ctx → Set → Set
  ⟦ ι       ⟧c γ X = ⊤
  ⟦ S ⊗ D   ⟧c γ X = Σ (S γ) λ s → ⟦ D ⟧c (γ , s) X
  ⟦ rec-⊗ D ⟧c γ X = X × ⟦ D ⟧c γ X
  
  ⟦_⟧d : ∀ {Γ n} → DatDesc Γ n → ⟦ Γ ⟧Ctx → Set → Set
  ⟦_⟧d {n = n} D γ X = Σ (fin n) λ k → ⟦ lookup D k ⟧c γ X


  data μ {n Γ} (D : DatDesc Γ n) (γ : ⟦ Γ ⟧Ctx) : Set where
    ⟨_⟩ : ⟦ D ⟧d γ (μ D γ) → μ D γ
  

  listD : DatDesc (ε ▷′ Set) 2
  listD = ι ∣ snd ⊗ rec-⊗ ι ∣ ε

  list : Set → Set
  list A = μ listD (tt ▶ A)

  nil : ∀ {A} → list A
  nil = ⟨ ze , tt ⟩

  cons : ∀ {A} → A → list A → list A
  cons x xs = ⟨ su ze , x , xs , tt ⟩

  t : list Nat
  t = cons 1 (cons 0 nil)


module Indexed where

  infixr 4 _∣_
  infixr 5 _⊗_

  open Parametrized using (Ctx; _▷_; ε; _▷′_; _▶_; ⟦_⟧Ctx)

  data ConDesc (Γ : Ctx) (I : Ctx) : Set where
    ι       : (⟦ Γ ⟧Ctx → ⟦ I ⟧Ctx) → ConDesc Γ I
    _⊗_    : (S : ⟦ Γ ⟧Ctx → Set) → (D : ConDesc (Γ ▷ S) I) → ConDesc Γ I
    rec_⊗_ : (r : ⟦ Γ ⟧Ctx → ⟦ I ⟧Ctx) → (D : ConDesc Γ I) → ConDesc Γ I

  data DatDesc (Γ : Ctx) (I : Ctx) : Nat → Set where
    ε   : DatDesc Γ I 0
    _∣_ : ∀ {n} → (C : ConDesc Γ I) → (D : DatDesc Γ I n) → DatDesc Γ I (suc n)

  rec′_⊗_ : ∀ {Γ S I i} (r : ⟦ Γ ⟧Ctx → S) → (D : ConDesc Γ (I ▷ const S)) → ConDesc Γ (I ▷ const S)
  rec′_⊗_  {i = i} r D = rec (λ γ → i , r γ) ⊗ D

  ι′ : ∀ {Γ S I i} (r : ⟦ Γ ⟧Ctx → S) → ConDesc Γ (I ▷ const S)
  ι′ {i = i} r = ι (λ γ → i , r γ)
  
  lookup : ∀ {Γ I n} → DatDesc Γ I n → fin n → ConDesc Γ I
  lookup (C ∣ D) ze     = C
  lookup (C ∣ D) (su k) = lookup D k

  ⟦_⟧c : ∀ {Γ I} → ConDesc Γ I → ⟦ Γ ⟧Ctx → (⟦ I ⟧Ctx → Set) → (⟦ I ⟧Ctx → Set)
  ⟦ ι f       ⟧c γ X i = f γ ≡ i
  ⟦ S ⊗ D     ⟧c γ X i = Σ (S γ) λ s → ⟦ D ⟧c (γ , s) X i
  ⟦ rec r ⊗ D ⟧c γ X i = X (r γ) × ⟦ D ⟧c γ X i

  ⟦_⟧d : ∀ {Γ I n} → DatDesc Γ I n → ⟦ Γ ⟧Ctx → (⟦ I ⟧Ctx → Set) → (⟦ I ⟧Ctx → Set)
  ⟦_⟧d {n = n} D γ X i = Σ (fin n) λ k → ⟦ lookup D k ⟧c γ X i

  data μ {n Γ I} (D : DatDesc Γ I n) (γ : ⟦ Γ ⟧Ctx) (i : ⟦ I ⟧Ctx) : Set where
    ⟨_⟩ : ⟦ D ⟧d γ (μ D γ) i → μ D γ i

  coninj : ∀ {Γ I n} {D : DatDesc Γ I n} {γ : ⟦ Γ ⟧Ctx} {i : ⟦ I ⟧Ctx}
         → {a b : ⟦ D ⟧d γ (μ D γ) i}
         → ⟨ a ⟩ ≡ ⟨ b ⟩
         → a ≡ b
  coninj {a = a} {b = b} refl = refl

  coninj′ : ∀ {Γ I n} {D : DatDesc Γ I n} {γ : ⟦ Γ ⟧Ctx} {i : ⟦ I ⟧Ctx}
         → {a b : ⟦ D ⟧d γ (μ D γ) i}
         → a ≢ b
         → ⟨ a ⟩ ≢ ⟨ b ⟩
  coninj′ = contr coninj

  ⟦_⟧eqc : ∀ {Γ I} (D : ConDesc Γ I) → ⟦ Γ ⟧Ctx → Set
  ⟦ ι x ⟧eqc γ = ⊤
  ⟦_⟧eqc {Γ} (S ⊗ C) γ = eq (S γ) × ((s : S γ) → ⟦ C ⟧eqc (γ , s))
  ⟦ rec r ⊗ C ⟧eqc γ = ⟦ C ⟧eqc γ

  ⟦_⟧eqd : ∀ {Γ I n} (D : DatDesc Γ I n) → ⟦ Γ ⟧Ctx → Set
  ⟦ ε     ⟧eqd γ = ⊤
  ⟦ C ∣ D ⟧eqd γ = ⟦ C ⟧eqc γ × ⟦ D ⟧eqd γ

  lookupeq : ∀ {Γ I n} {D : DatDesc Γ I n} {γ : ⟦ Γ ⟧Ctx}
           → ⟦ D ⟧eqd γ → (k : fin n) → ⟦ lookup D k ⟧eqc γ
  lookupeq {D = C ∣ D} (eqc , eqd) ze = eqc
  lookupeq {D = C ∣ D} (eqc , eqd) (su n) = lookupeq eqd n


  module Eq {Γd I n} {D : DatDesc Γd I n} where
    mutual
      ceq : ∀ {Γ} {γd : ⟦ Γd ⟧Ctx} {i : ⟦ I ⟧Ctx} {C : ConDesc Γ I} {γ : ⟦ Γ ⟧Ctx} 
          → {e : ⟦ D ⟧eqd γd }
          → (e′ : ⟦ C ⟧eqc γ)
          → (a b : ⟦ C ⟧c γ (μ D γd) i)
          → dec (a ≡ b)

      ceq {C = ι x} e′ refl refl = yes refl

      ceq {γd = γd} {C = S ⊗ C} {γ = γ} {e} (f , dₑ) (s₁ , d₁) (s₂ , d₂) =
        case _≟_ {{f}} s₁ s₂ of λ where
          (no  s₁≢s₂) → no (path_sigma_neq (inl s₁≢s₂))
          (yes refl) →
            case ceq {γd = γd} {γ = γ , s₁} {e} (dₑ s₁) d₁ d₂ of λ where
              (no d₁≢d₂) → no (path_sigma_neq (inr d₁≢d₂))
              (yes d₁≡d₂) → yes (path_sigma refl d₁≡d₂)

      ceq {C = rec r ⊗ D} {e = e} e′ (x₁ , d₁) (x₂ , d₂) =
        case deq e x₁ x₂ of λ where
          (no x₁≢x₂) → no (path_sigma_neq (inl x₁≢x₂))
          (yes x₁≡x₂) → 
            case ceq {e = e} e′ d₁ d₂ of λ where
              (no d₁≢d₂) → no (path_sigma_neq (inr d₁≢d₂))
              (yes d₁≡d₂) → yes (path_sigma x₁≡x₂ d₁≡d₂)

      deq : {γ : ⟦ Γd ⟧Ctx} {i : ⟦ I ⟧Ctx} (e : ⟦ D ⟧eqd γ) (a b : μ D γ i)
          → dec (a ≡ b)

      deq e ⟨ k₁ , v₁ ⟩ ⟨ k₂ , v₂ ⟩ = 
          case k₁ ≟ k₂ of λ where
          (no  k₁≢k₂) → no (coninj′ (path_sigma_neq (inl k₁≢k₂))) 
          (yes refl) → 
            case ceq {e = e} (lookupeq e k₁) v₁ v₂ of λ where
              (no v₁≢v₂) → no (coninj′ (path_sigma_neq (inr v₁≢v₂)))
              (yes v₁≡v₂) → yes (cong ⟨_⟩ (path_sigma refl v₁≡v₂))

  open Eq using (deq)

  module Sample where

    natD : DatDesc ε ε 2
    natD = ι (const tt)
         ∣ rec const tt ⊗ ι (const tt)
         ∣ ε

    `nat : Set
    `nat = μ natD tt tt

    `ze : `nat
    `ze = ⟨ ze , refl ⟩

    `su : `nat → `nat
    `su n = ⟨ su ze , n , refl ⟩

    eqnadw : ⟦ natD ⟧eqd tt
    eqnadw = tt , tt , tt

    instance
      Eqμnat : eq `nat
      _≟_ {{Eqμnat}} = deq eqnadw


    listD : DatDesc (ε ▷′ Set) ε 2
    listD = ι (const tt)
          ∣ snd ⊗ rec const tt ⊗ ι (const tt)
          ∣ ε

    `list : Set → Set
    `list A = μ listD (tt , A) tt

    `nil : ∀ {A} → `list A
    `nil = ⟨ ze , refl ⟩

    `cons : ∀ {A} → A → `list A → `list A
    `cons x xs = ⟨ su ze , x , xs , refl ⟩

    eqlistw : ∀ {A} {r : eq A} → ⟦ listD ⟧eqd (tt , A)
    eqlistw {r = r} = tt , (r , const tt) , tt

    instance
      Eqμlist : ∀ {A} {r : eq A} → eq (`list A)
      _≟_ {{Eqμlist {A} {r}}} = deq (eqlistw {A} {r})


    vecD : DatDesc (ε ▷′ Set) (ε ▷′ `nat) 2
    vecD = ι′ (const `ze)
         ∣ const `nat ⊗ snd ∘ fst ⊗ rec′ (snd ∘ fst) ⊗ ι′ (`su ∘ snd ∘ fst)
         ∣ ε

    vec : Set → `nat → Set
    vec A n = μ vecD (tt , A) (tt , n)

    nil : ∀ {A} → vec A `ze
    nil = ⟨ ze , refl ⟩

    cons : ∀ {A n} → A → vec A n → vec A (`su n)
    cons {n = n} x xs = ⟨ su ze , n , x , xs , refl ⟩

    eqvecw : ∀ {A} {r : eq A} → ⟦ vecD ⟧eqd (tt , A)
    eqvecw {r = r} = tt , (Eqμnat , const (r , const tt)) , tt

    instance
      Eqμvec : ∀ {A n} {r : eq A} → eq (vec A n)
      _≟_ {{Eqμvec {A} {r = r}}} = deq (eqvecw {A} {r})


    finD : DatDesc ε (ε ▷′ `nat) 2
    finD = const `nat ⊗ ι′ (`su ∘ snd)
         ∣ const `nat ⊗ rec′ snd ⊗ ι′ (`su ∘ snd)
         ∣ ε

    `fin : `nat → Set
    `fin n = μ finD tt (tt , n)

    eqfinw : ⟦ finD ⟧eqd tt
    eqfinw = (Eqμnat , const tt) , (Eqμnat , const tt) , tt

    instance
      Eqμfin : ∀ {n} → eq (`fin n)
      _≟_ {{Eqμfin}} = deq eqfinw


module Automated where

  open import Agda.Builtin.Reflection hiding (nat)
  open import Agda.Builtin.List
  open import Agda.Builtin.Bool
  import Agda.Builtin.Equality
  open import Agda.Builtin.TrustMe
  open Parametrized using (Ctx; ⟦_⟧Ctx; ε)
  open Indexed using (DatDesc; ConDesc; μ; ⟨_⟩)
  open Indexed.Sample using (natD; `nat; `ze; `su)

  record HasDesc (A : Set) : Set where
    field
      {n}  : Nat
      {Γ} {I} : Ctx
      desc : DatDesc Γ I n
      {γ}    : ⟦ Γ ⟧Ctx
      {i}    : ⟦ I ⟧Ctx
      to   : A → μ desc γ i
      from : μ desc γ i → A
      
      from∘to : (x : A) → from (to x) ≡ x
      to∘from : (x : μ desc γ i) → to (from x) ≡ x
  open HasDesc {{...}}

  instance
    {-# TERMINATING #-}
    natHasDesc : HasDesc Nat
    Γ    {{natHasDesc}} = ε
    I    {{natHasDesc}} = ε
    n    {{natHasDesc}} = 2
    desc {{natHasDesc}} = natD
    γ    {{natHasDesc}} = tt
    i    {{natHasDesc}} = tt

    to ⦃ natHasDesc ⦄ = λ where
      0       → `ze 
      (suc n) → `su (to n)

    from ⦃ natHasDesc ⦄ = λ where
      ⟨ ze , refl ⟩        → 0
      ⟨ su ze , n , refl ⟩ → suc (from n)

    from∘to ⦃ natHasDesc ⦄ = λ where
      0      → refl
      (suc n) → cong suc (from∘to n)

    to∘from ⦃ natHasDesc ⦄ = λ where
      ⟨ ze , refl ⟩        → refl
      ⟨ su ze , n , refl ⟩ → cong (λ p → ⟨ su ze , p , refl ⟩) (to∘from n) 

  instance
    TCMonad : Monad TC
    return ⦃ TCMonad ⦄ = returnTC
    _>>=_ ⦃ TCMonad ⦄ = bindTC

  converteq : {A : Set} {x y : A} → Agda.Builtin.Equality._≡_ x y → x ≡ y
  converteq Agda.Builtin.Equality._≡_.refl = refl

  instance
    eqName : eq Name
    _≟_ {{eqName}} x y with primQNameEquality x y
    ... | true  = yes (converteq (primTrustMe {x = x} {y = y}))
    ... | false = no λ x≡y → trustme
        where postulate trustme : _
    
  {-
  data ConDesc (Γ : Ctx) (I : Ctx) : Set where
    ι       : (⟦ Γ ⟧Ctx → ⟦ I ⟧Ctx) → ConDesc Γ I
    _⊗_    : (S : ⟦ Γ ⟧Ctx → Set) → (D : ConDesc (Γ ▷ S) I) → ConDesc Γ I
    rec_⊗_ : (r : ⟦ Γ ⟧Ctx → ⟦ I ⟧Ctx) → (D : ConDesc Γ I) → ConDesc Γ I

  data DatDesc (Γ : Ctx) (I : Ctx) : nat → Set where
    ε   : DatDesc Γ I ze
    _∣_ : ∀ {n} → (C : ConDesc Γ I) → (D : DatDesc Γ I n) → DatDesc Γ I (su n)
    -}

  hidrel : ArgInfo
  hidrel = arg-info hidden relevant

  visrel : ArgInfo
  visrel = arg-info visible relevant

  hr : ∀ {A} → A → Arg A
  hr t = arg hidrel  t

  vr : ∀ {A} → A → Arg A
  vr t = arg visrel t

  uhr : Arg Term
  uhr = hr unknown

  uvr : Arg Term
  uvr = vr unknown

  conDesc : (dn : Name) → Term → TC Term
  conDesc dn (pi (arg _ t) (abs _ rt)) = do
    rest ← conDesc dn rt
    case t of λ where
      (def dn args) →
        return (con (quote ConDesc.rec_⊗_)
                    -- TODO: take care of indices
                    ( vr (lam visible (abs "γ" (quoteTerm ⊤.tt)))
                    ∷ vr rest
                    ∷ []))
      _ →
        return (con (quote ConDesc._⊗_) ( vr (lam visible (abs "γ" t)) ∷ vr rest ∷ []))

  conDesc dn _ =
    return (con (quote ConDesc.ι)
                -- TODO: take care of indices
                ( vr (lam visible (abs "γ" (con (quote ⊤.tt) [])))
                ∷ []))

  makeDesc : (dn : Name) → List Name → TC Term
  makeDesc dn []       = return (con (quote DatDesc.ε) [])
  makeDesc dn (x ∷ xs) = do
    descxs ← makeDesc dn xs
    ct     ← getType x
    descx  ← conDesc dn ct
    return (con (quote DatDesc._∣_) ( uhr ∷ vr descx ∷ vr descxs ∷ []))

  deriveDesc : Name → Nat → List Name → TC Term
  deriveDesc d n cs = do
    desc ← makeDesc d cs
    return desc

  macro
    derive-desc : Name → Term →  TC ⊤
    derive-desc d hole = do
      x ← getDefinition d
      case x of λ where
        (data-type n cs) → deriveDesc d n cs >>= unify hole
        _                → typeError (strErr "Argument is not a datatype." ∷ [])


  pair : Term → Term → Term
  pair a b = con (quote Σ._,_)
             ( uhr ∷ uhr ∷ uhr ∷ uhr
             ∷ vr a
             ∷ vr b
             ∷ [])

  buildClause : Name → Type → Term → TC (List Pattern × Term)
  buildClause _ _ (con (quote ConDesc.ι) args) = return ([] , con (quote _≡_.refl) [])

  buildClause fn (pi _ (abs vn ct)) (con (quote ConDesc._⊗_) (_ ∷ arg _ D ∷ [])) = do
    cpat , dtup ← buildClause fn ct D
    return (var vn ∷ cpat , pair (var 0 []) dtup)

  buildClause fn (pi _ (abs vn ct)) (con (quote ConDesc.rec_⊗_) (_ ∷ arg _ D ∷ [])) = do
    cpat , dtup ← buildClause fn ct D
    return (var vn ∷ cpat , pair (def fn (vr (var 0 []) ∷ [])) dtup)

  buildClause _ _ _    = typeError (strErr "Ill-formed description for constructor" ∷ [])

  makeClause : ∀ {n} → Name → fin n → Name → Term → TC Clause
  makeClause fn n cn cd = do
    ct ← getType cn
    cpat , dtup ← buildClause fn ct cd
    n′ ← quoteTC n
    return (clause (vr (con cn (map vr cpat)) ∷ [])
                   (con (quote μ.⟨_⟩) (vr (pair n′ dtup) ∷ [])))

  makeClauses : ∀ {n} → Name → List (fin n) → List Name → Term → TC (List Clause)
  makeClauses fn (n ∷ ns) (x ∷ xs) (con (quote DatDesc._∣_) (_ ∷ arg _ dx ∷ arg _ dxs ∷ [])) = do
    cl  ← makeClause fn n x dx
    cls ← makeClauses fn ns xs dxs
    return (cl ∷ cls)

  makeClauses _ _ [] (con (quote DatDesc.ε) _) = return []
  makeClauses _ _ _  _ = typeError (strErr "Ill-formed description for datatype." ∷ [])

  derive-to : Name → Name → TC ⊤
  derive-to fname dat = do
    xdat ← getDefinition dat
    case xdat of λ where
      (data-type n cs) → do
        xdes  ← deriveDesc dat n cs

        declareDef (vr fname)
                   (pi (vr (def dat []))
                       (abs "x" (def ((quote μ))
                                ( uhr ∷ uhr ∷ uhr
                                ∷ vr xdes
                                ∷ vr (con (quote ⊤.tt) [])
                                ∷ vr (con (quote ⊤.tt) [])
                                ∷ []))))

        clauses ← makeClauses fname (finlist (length cs)) cs xdes

        defineFun fname clauses

      _ → typeError (strErr "Argument is not a datatype." ∷ [])

  unquoteDecl natToDesc = derive-to natToDesc (quote Nat)

  check : natToDesc 1 ≡ ⟨ su ze , ⟨ ze , refl ⟩ , refl ⟩
  check = refl

open import Agda.Builtin.Reflection public hiding (nat)
open import Agda.Builtin.Bool public
open Monad public
open Automated public
