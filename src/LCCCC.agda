module LCCCC where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ)

variable
  A : Set
  n : ℕ

infixl 4 _,_

data Typ : Set where
  unit    : Typ
  arr prod : (a b : Typ) → Typ

data Ctx : ℕ → Set where
  ε   : Ctx 0
  _,_ : Ctx n → Typ → Ctx (suc n)

variable
  a b : Typ
  Γ   : Ctx n

data Var : Ctx n → Typ → Set where
  here  : Var (Γ , a) a
  there : Var Γ a → Var (Γ , b) a

-- well-typed stlc terms
data Tm : Ctx n → Typ → Set where
  lam  : Tm (Γ , a) b → Tm Γ (arr a b)
  var  : Var Γ a → Tm Γ a
  app  : Tm Γ (arr a b) → Tm Γ a → Tm Γ b
  tt   : Tm Γ unit
  p₁   : Tm Γ (prod a b) → Tm Γ a
  p₂   : Tm Γ (prod a b) → Tm Γ b
  pair : Tm Γ a → Tm Γ b → Tm Γ (prod a b)


data _⊢_∋_≡_ : (Γ : Ctx n) (t : Typ) → Tm Γ t → Tm Γ t → Set where
  refl  : ∀ {u    } → Γ ⊢ a ∋ u ≡ u
  sym   : ∀ {u v  } → Γ ⊢ a ∋ u ≡ v → Γ ⊢ a ∋ v ≡ u
  trans : ∀ {u v w} → Γ ⊢ a ∋ u ≡ v → Γ ⊢ a ∋ v ≡ w → Γ ⊢ a ∋ u ≡ w
  abs   : ∀ {u v} → (Γ , a) ⊢ b ∋ u ≡ v → Γ ⊢ arr a b ∋ lam u ≡ lam v
  app   : ∀ {u₁ u₂ v₁ v₂}
        → Γ ⊢ arr a b ∋ u₁        ≡ u₂
        → Γ ⊢ a       ∋ v₁        ≡ v₂
        → Γ ⊢ b       ∋ app u₁ v₁ ≡ app u₂ v₂

  p₁    : ∀ {u v} → Γ ⊢ prod a b ∋ u ≡ v → Γ ⊢ a ∋ p₁ u ≡ p₁ v
  p₂    : ∀ {u v} → Γ ⊢ prod a b ∋ u ≡ v → Γ ⊢ b ∋ p₂ u ≡ p₂ v
  -- TODO : β and η equality


record CCC : Set₁ where
  infixr 5 _∘_
  infix  4 _~_
  infixr 5 _×_
  infix  6 _^_
  field
    Ob  : Set
    Hom : (a b : Ob) → Set
    _~_ : ∀ {a b} (x y : Hom a b) → Set
    _∘_ : ∀ {a b c} → Hom b c → Hom a b → Hom a c
    id  : (a : Ob) → Hom a a

    𝟙   : Ob
    t   : ∀ {a} → Hom a 𝟙

    _×_   : (a b : Ob) → Ob
    ⟨_,_⟩ : ∀ {a b c} (f : Hom a b) (g : Hom a c) → Hom a (b × c)
    π₁    : ∀ {a b} → Hom (a × b) a
    π₂    : ∀ {a b} → Hom (a × b) b

    _^_   : (b a : Ob) → Ob
    eval  : ∀ {a b} → Hom (b ^ a × a) b
    curry : ∀ {a b c} (f : Hom (c × a) b) → Hom c (b ^ a)

  field
    -- _~_ is an equivalence relation
    ~-refl  : ∀ {a b} {f     : Hom a b} → f ~ f
    ~-sym   : ∀ {a b} {f g   : Hom a b} → f ~ g → g ~ f
    ~-trans : ∀ {a b} {f g h : Hom a b} → f ~ g → g ~ h → f ~ h

    -- _∘_ is associative, has left and right unit, preserves _~_
    ∘-assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d)
            → (h ∘ g) ∘ f ~ h ∘ (g ∘ f)
    ∘-unitˡ : ∀ {a b} (f : Hom a b) → id b ∘ f ~ f
    ∘-unitʳ : ∀ {a b} (f : Hom a b) → f ∘ id a ~ f
    ∘-cong  : ∀ {a b c} {f₁ f₂ : Hom a b} {g₁ g₂ : Hom b c}
            → f₁ ~ f₂ → g₁ ~ g₂ → g₁ ∘ f₁ ~ g₂ ∘ f₂

    t-uniq : ∀ {a} (f : Hom a 𝟙) → f ~ t

    ⟨⟩-resp-~ : ∀ {a b c} {f₁ f₂ : Hom a b} {g₁ g₂ : Hom a c}
              → f₁ ~ f₂ → g₁ ~ g₂ → ⟨ f₁ , g₁ ⟩ ~ ⟨ f₂ , g₂ ⟩
    π₁∘⟨⟩ : ∀ {a b c} (f : Hom a b) (g : Hom a c) → π₁ ∘ ⟨ f , g ⟩ ~ f
    π₂∘⟨⟩ : ∀ {a b c} (f : Hom a b) (g : Hom a c) → π₂ ∘ ⟨ f , g ⟩ ~ g

    -- TODO: properties of _^_, curry, eval
    curry-resp-∼ : ∀ {a b c} {f g : Hom (c × a) b} → f ~ g → curry f ~ curry g

module Example1 (C : CCC) where
  open CCC C

  -- interpreting types as objects
  ⟦_⟧Typ : Typ → Ob
  ⟦ unit     ⟧Typ = 𝟙
  ⟦ arr a b  ⟧Typ = ⟦ b ⟧Typ ^ ⟦ a ⟧Typ
  ⟦ prod a b ⟧Typ = ⟦ a ⟧Typ × ⟦ b ⟧Typ

  -- interpreting contexts as objects
  ⟦_⟧Ctx : Ctx n → Ob
  ⟦ ε     ⟧Ctx = 𝟙
  ⟦ Γ , x ⟧Ctx = ⟦ Γ ⟧Ctx × ⟦ x ⟧Typ

  -- interpreting variables as arrows
  ⟦_⟧Var : Var Γ a → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Typ
  ⟦ here    ⟧Var = π₂
  ⟦ there v ⟧Var = ⟦ v ⟧Var ∘ π₁

  ⟦_⟧ : Tm Γ a → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Typ
  ⟦ lam u    ⟧ = curry ⟦ u ⟧
  ⟦ var v    ⟧ = ⟦ v ⟧Var
  ⟦ app u v  ⟧ = eval ∘ ⟨ ⟦ u ⟧ , ⟦ v ⟧ ⟩
  ⟦ tt       ⟧ = t
  ⟦ p₁ u     ⟧ = π₁ ∘ ⟦ u ⟧
  ⟦ p₂ u     ⟧ = π₂ ∘ ⟦ u ⟧
  ⟦ pair u v ⟧ = ⟨ ⟦ u ⟧ , ⟦ v ⟧ ⟩

  -- interpreting judgemental equality as equivalence
  ⟦_⟧Eq : ∀ {u v} → Γ ⊢ a ∋ u ≡ v → ⟦ u ⟧ ~ ⟦ v ⟧
  ⟦ refl      ⟧Eq = ~-refl
  ⟦ sym p     ⟧Eq = ~-sym ⟦ p ⟧Eq 
  ⟦ trans p q ⟧Eq = ~-trans ⟦ p ⟧Eq ⟦ q ⟧Eq
  ⟦ abs p     ⟧Eq = curry-resp-∼ ⟦ p ⟧Eq
  ⟦ app p q   ⟧Eq = ∘-cong (⟨⟩-resp-~ ⟦ p ⟧Eq ⟦ q ⟧Eq) ~-refl
  ⟦ p₁ p      ⟧Eq = ∘-cong ⟦ p ⟧Eq ~-refl
  ⟦ p₂ p      ⟧Eq = ∘-cong ⟦ p ⟧Eq ~-refl
    
{-

record Model : Set₁ where
  field Carrier : Set

  Env : ℕ → Set
  Env = Vec Carrier

  infix  6 _⟦_⟧
  infixl 5 _·_

  field
    _·_     : Carrier → Carrier → Carrier
    _⟦_⟧    : Env n → Exp n → Carrier

    -- ⟦⟧-var : {ρ : Env n} {k : Fin n}   → ρ ⟦ var k   ⟧ ≡ lookup ρ k
    -- ⟦⟧-app : {ρ : Env n} {u v : Exp n} → ρ ⟦ app u v ⟧ ≡ ρ ⟦ u ⟧ · ρ ⟦ v ⟧
    -- ⟦⟧-lam : ∀ {ρ : Env n} {u x}
    --        → ρ ⟦ lam u ⟧ · x ≡ (x ∷ ρ) ⟦ u ⟧
    -- ⟦⟧-abs : ∀ {ρ : Env n} {u v}
    --        → (∀ x → (x ∷ ρ) ⟦ u ⟧ ≡ (x ∷ ρ) ⟦ v ⟧)
    --        → ρ ⟦ lam u ⟧ ≡ ρ ⟦ lam v ⟧


-}
