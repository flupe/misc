module LCCCC where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit


module STLC where

  variable
    n m p q : ℕ
  
  data Typ : Set where
    𝟙       : Typ
    _⇒_ _×_ : (a b : Typ) → Typ
  
  data ⊥ : Set where
  
  infixl 4 _,_
  data Ctx : ℕ → Set where
    ε   : Ctx 0
    _,_ : Ctx n → Typ → Ctx (suc n)
  
  variable
    a b : Typ
    Γ   : Ctx n
    Δ   : Ctx m
    E   : Ctx p
    ϕ   : Ctx q
  
  data Var : Ctx n → Typ → Set where
    here  : Var (Γ , a) a
    there : Var Γ a → Var (Γ , b) a
  
  data Tm  : Ctx n → Typ → Set
  data Sub : Ctx n → Ctx m → Set
  
  
  -- well-typed stlc terms
  data Tm where
    lam   : Tm (Γ , a) b → Tm Γ (a ⇒ b)
    var   : Var Γ a → Tm Γ a
    app   : Tm Γ (a ⇒ b) → Tm Γ a → Tm Γ b
    tt    : Tm Γ 𝟙
    π₁    : Tm Γ (a × b) → Tm Γ a
    π₂    : Tm Γ (a × b) → Tm Γ b
    _,_   : Tm Γ a → Tm Γ b → Tm Γ (a × b)
    _[_]  : Tm Δ a → Sub Γ Δ → Tm Γ a
  
  
-- explicit substitutions
  data Sub where
    idS : Sub Γ Γ
    ε   : Sub Γ ε
    _,_ : Sub Γ Δ → Tm Γ a → Sub Γ (Δ , a)
    ↑   : Sub (Γ , a) Γ
    _∘_ : Sub Δ E → Sub Γ Δ → Sub Γ E
  
  variable
    u v w      : Tm Γ a
    u₁ u₂      : Tm Γ a
    v₁ v₂      : Tm Γ b
    u,v        : Tm Γ (a × b)
    f          : Tm Γ (a ⇒ b)
    ρ ρ₁ ρ₂ ρ₃ : Sub Γ Δ
    σ σ₁ σ₂    : Sub Δ E
    τ          : Sub E ϕ
    t t₁ t₂    : Tm Δ a
    y          : Tm (Γ , a) b
    z          : Tm E a
  
  
  infix 8 _≐_
  infix 8 _≅_
  infixl 9 _[_]
  
  data _≐_ : Sub Γ Δ → Sub Γ Δ → Set
  
  data _≅_ : Tm Γ a → Tm Γ a → Set where
    refl  : u ≅ u
    sym   : u ≅ v → v ≅ u
    trans : u ≅ v → v ≅ w → u ≅ w
  
    β     : app (lam y) u ≅ y [ (idS , u) ]
    η     : f ≅ lam (app (f [ ↑ ]) (var here))
  
    lam   : u ≅ v → lam u ≅ lam v
    app   : u₁ ≅ u₂ → v₁ ≅ v₂ → app u₁ v₁ ≅ app u₂ v₂
  
    π₁    : u ≅ v → π₁ u ≅ π₁ v
    π₂    : u ≅ v → π₂ u ≅ π₂ v
    _,_   : u₁ ≅ u₂ → v₁ ≅ v₂ → (u₁ , v₁) ≅ (u₂ , v₂)
  
    βπ₁   : u ≅ π₁ (u , v)
    βπ₂   : v ≅ π₂ (u , v)
    ηpair : u,v ≅ (π₁ u,v , π₂ u,v)
    tt    : u ≅ tt
  
    _[_]         : t₁ ≅ t₂ → ρ₁ ≐ ρ₂ → t₁ [ ρ₁ ] ≅ t₂ [ ρ₂ ]
    []-assoc     : z [ σ ] [ ρ ] ≅ z [ σ ∘ ρ ]
    []-id        : u [ idS ] ≅ u
    []-var-here  : var here [ ρ , u ] ≅ u
    []-var-there : {v : Var (Γ , b) a} → var (there v) [ ρ , u ] ≅ var v [ ρ ]
    []-app       : app f u [ ρ ] ≅ app (f [ ρ ]) (u [ ρ ])
    []-lam       : lam y [ ρ ] ≅ lam (y [ ρ ∘ ↑ , var here ])
  
  data _≐_ where
    refl    : σ ≐ σ
    sym     : ρ₁ ≐ ρ₂ → ρ₂ ≐ ρ₁
    trans   : ρ₁ ≐ ρ₂ → ρ₂ ≐ ρ₃ → ρ₁ ≐ ρ₃
    ∘-assoc : (τ ∘ σ) ∘ ρ ≐ τ ∘ (σ ∘ ρ)
    ∘-unitˡ : idS ∘ σ ≐ σ
    ∘-unitʳ : σ ∘ idS ≐ σ
    ,-∘     : (σ , t) ∘ ρ ≐ (σ ∘ ρ , t [ ρ ])
    β       : ↑ ∘ (ρ , t) ≐ ρ
    η       : idS ≐ (↑ , t)
    ε       : (σ : Sub Γ ε) → σ ≐ ε
    _∘_     : ρ₁ ≐ ρ₂ → σ₁ ≐ σ₂ → σ₁ ∘ ρ₁ ≐ σ₂ ∘ ρ₂
    _,_     : ρ₁ ≐ ρ₂ → t₁ ≅ t₂ → (ρ₁ , t₁) ≐ (ρ₂ , t₂)


record CCC : Set₁ where
  infixr 5 _∘_
  infix  4 _~_
  infixr 5 _×_
  infix  6 _^_
  field
    Ob  : Set
    Hom : (a b : Ob) → Set

    _~_     : ∀ {a b} (x y : Hom a b) → Set
    ~-refl  : ∀ {a b} {f     : Hom a b} → f ~ f
    ~-sym   : ∀ {a b} {f g   : Hom a b} → f ~ g → g ~ f
    ~-trans : ∀ {a b} {f g h : Hom a b} → f ~ g → g ~ h → f ~ h

    _∘_ : ∀ {a b c} → Hom b c → Hom a b → Hom a c
    id  : (a : Ob) → Hom a a

    ∘-assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d)
            → (h ∘ g) ∘ f ~ h ∘ (g ∘ f)
    ∘-unitˡ : ∀ {a b} (f : Hom a b) → id b ∘ f ~ f
    ∘-unitʳ : ∀ {a b} (f : Hom a b) → f ∘ id a ~ f
    ∘-cong  : ∀ {a b c} {f₁ f₂ : Hom a b} {g₁ g₂ : Hom b c}
            → f₁ ~ f₂ → g₁ ~ g₂ → g₁ ∘ f₁ ~ g₂ ∘ f₂

    𝟙 : Ob
    t : ∀ {a} → Hom a 𝟙
    t-uniq : ∀ {a} (f : Hom a 𝟙) → f ~ t

    _×_   : (a b : Ob) → Ob
    ⟨_,_⟩ : ∀ {a b c} (f : Hom a b) (g : Hom a c) → Hom a (b × c)
    π₁    : ∀ {a b} → Hom (a × b) a
    π₂    : ∀ {a b} → Hom (a × b) b

    ⟨⟩-cong₂ : ∀ {a b c} {f₁ f₂ : Hom a b} {g₁ g₂ : Hom a c}
              → f₁ ~ f₂ → g₁ ~ g₂ → ⟨ f₁ , g₁ ⟩ ~ ⟨ f₂ , g₂ ⟩
    ∘-distribʳ-⟨⟩ : ∀ {a b c d} {f : Hom a b} {g : Hom a c} {h : Hom d a}
                  → ⟨ f , g ⟩ ∘ h ~ ⟨ f ∘ h , g ∘ h ⟩
    π₁∘⟨⟩ : ∀ {a b c} (f : Hom a b) (g : Hom a c) → π₁ ∘ ⟨ f , g ⟩ ~ f
    π₂∘⟨⟩ : ∀ {a b c} (f : Hom a b) (g : Hom a c) → π₂ ∘ ⟨ f , g ⟩ ~ g
    ⟨⟩∘π  : ∀ {a b c} (p : Hom a (b × c)) → p ~ ⟨ π₁ ∘ p , π₂ ∘ p ⟩

    _^_   : (b a : Ob) → Ob
    eval  : ∀ {a b} → Hom (b ^ a × a) b
    curry : ∀ {a b c} (f : Hom (c × a) b) → Hom c (b ^ a)
    curry-resp-∼ : ∀ {a b c} {f g : Hom (c × a) b} → f ~ g → curry f ~ curry g
    -- TODO: even more properties

-- interpreting stlc in any ccc
module Interpretation (C : CCC) where
  open CCC C
  module L = STLC
  open L hiding (_×_; 𝟙; π₂; π₁; _∘_; t)

  ⟦_⟧Typ : L.Typ → Ob
  ⟦ L.𝟙     ⟧Typ = 𝟙
  ⟦ a L.⇒ b ⟧Typ = ⟦ b ⟧Typ ^ ⟦ a ⟧Typ
  ⟦ a L.× b ⟧Typ = ⟦ a ⟧Typ × ⟦ b ⟧Typ

  ⟦_⟧Ctx : Ctx n → Ob
  ⟦ ε     ⟧Ctx = 𝟙
  ⟦ Γ , x ⟧Ctx = ⟦ Γ ⟧Ctx × ⟦ x ⟧Typ

  ⟦_⟧Var : Var Γ a → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Typ
  ⟦ here    ⟧Var = π₂
  ⟦ there v ⟧Var = ⟦ v ⟧Var ∘ π₁

  ⟦_⟧S : Sub Γ Δ → Hom ⟦ Γ ⟧Ctx ⟦ Δ ⟧Ctx
  ⟦_⟧  : Tm Γ a → Hom ⟦ Γ ⟧Ctx ⟦ a ⟧Typ

  ⟦ idS     ⟧S = id _
  ⟦ ε       ⟧S = t
  ⟦ σ , x   ⟧S = ⟨ ⟦ σ ⟧S , ⟦ x ⟧ ⟩
  ⟦ ↑       ⟧S = π₁
  ⟦ σ L.∘ ρ ⟧S = ⟦ σ ⟧S ∘ ⟦ ρ ⟧S

  ⟦ lam u   ⟧ = curry ⟦ u ⟧
  ⟦ var v   ⟧ = ⟦ v ⟧Var
  ⟦ app u v ⟧ = eval ∘ ⟨ ⟦ u ⟧ , ⟦ v ⟧ ⟩
  ⟦ tt      ⟧ = t
  ⟦ L.π₁ u  ⟧ = π₁ ∘ ⟦ u ⟧
  ⟦ L.π₂ u  ⟧ = π₂ ∘ ⟦ u ⟧
  ⟦ u , v   ⟧ = ⟨ ⟦ u ⟧ , ⟦ v ⟧ ⟩
  ⟦ u [ σ ] ⟧ = ⟦ u ⟧ ∘ ⟦ σ ⟧S

  ⟦_⟧≐  : ρ₁ ≐ ρ₂ → ⟦ ρ₁ ⟧S ~ ⟦ ρ₂ ⟧S
  ⟦_⟧Eq : u ≅ v → ⟦ u ⟧ ~ ⟦ v ⟧

  ⟦ refl      ⟧≐ = ~-refl
  ⟦ sym σ     ⟧≐ = ~-sym ⟦ σ ⟧≐
  ⟦ trans σ ρ ⟧≐ = ~-trans ⟦ σ ⟧≐ ⟦ ρ ⟧≐
  ⟦ ∘-assoc   ⟧≐ = CCC.∘-assoc C _ _ _
  ⟦ ∘-unitˡ   ⟧≐ = CCC.∘-unitˡ C _
  ⟦ ∘-unitʳ   ⟧≐ = CCC.∘-unitʳ C _
  ⟦ ,-∘       ⟧≐ = ∘-distribʳ-⟨⟩
  ⟦ β         ⟧≐ = π₁∘⟨⟩ _ _
  ⟦ η         ⟧≐ = {!!}
  ⟦ ε _       ⟧≐ = t-uniq _
  ⟦ p L.∘ q   ⟧≐ = ∘-cong ⟦ p ⟧≐ ⟦ q ⟧≐
  ⟦ p , q     ⟧≐ = ⟨⟩-cong₂ ⟦ p ⟧≐ ⟦ q ⟧Eq

  ⟦ refl         ⟧Eq = ~-refl
  ⟦ sym p        ⟧Eq = ~-sym ⟦ p ⟧Eq
  ⟦ trans p q    ⟧Eq = ~-trans ⟦ p ⟧Eq ⟦ q ⟧Eq
  ⟦ β            ⟧Eq = {!!}
  ⟦ η            ⟧Eq = {!!}
  ⟦ lam p        ⟧Eq = curry-resp-∼ ⟦ p ⟧Eq
  ⟦ app p q      ⟧Eq = ∘-cong (⟨⟩-cong₂ ⟦ p ⟧Eq ⟦ q ⟧Eq) ~-refl
  ⟦ L.π₁ p       ⟧Eq = ∘-cong ⟦ p ⟧Eq ~-refl
  ⟦ L.π₂ p       ⟧Eq = ∘-cong ⟦ p ⟧Eq ~-refl
  ⟦ p L., q      ⟧Eq = ⟨⟩-cong₂ ⟦ p ⟧Eq ⟦ q ⟧Eq
  ⟦ βπ₁          ⟧Eq = ~-sym (π₁∘⟨⟩ _ _)
  ⟦ βπ₂          ⟧Eq = ~-sym (π₂∘⟨⟩ _ _)
  ⟦ ηpair        ⟧Eq = ⟨⟩∘π _
  ⟦ tt           ⟧Eq = t-uniq _
  ⟦ p [ q ]      ⟧Eq = ∘-cong ⟦ q ⟧≐ ⟦ p ⟧Eq

  ⟦ []-assoc     ⟧Eq = CCC.∘-assoc C _ _ _
  ⟦ []-id        ⟧Eq = CCC.∘-unitʳ C _
  ⟦ []-var-here  ⟧Eq = π₂∘⟨⟩ _ _
  ⟦ []-var-there ⟧Eq = ~-trans (CCC.∘-assoc C _ _ _) (∘-cong (π₁∘⟨⟩ _ _) ~-refl)
  ⟦ []-app       ⟧Eq = ~-trans (CCC.∘-assoc C _ _ _) (∘-cong ∘-distribʳ-⟨⟩ ~-refl)
  ⟦ []-lam       ⟧Eq = {!!}

{-

open CCC


-- objects are either types or contexts
data λOb : Set where
  typ : Typ   → λOb
  ctx : Ctx n → λOb

LCCC : CCC
LCCC .Ob = λOb

-- arrows are terms that go from ctx Γ to type t
-- and from types to types (we need t → 𝟙 for terminal objects, and ⟨_,_⟩ leads to t → 𝟙 × 𝟙 ...
LCCC .Hom (ctx Γ) (typ t) = Tm Γ t
LCCC .Hom (typ a) (typ b) = ⊤
LCCC .Hom _       _       = ⊥

-- we relate arrows for terms that are βη-convertible
LCCC ._~_ {ctx Γ} {typ t} = Γ ⊢ t ∋_≡_
LCCC ._~_ {ctx _} {ctx _} _ _ = ⊤
LCCC ._~_ {typ _} {ctx _} _ _ = ⊤
LCCC ._~_ {typ _} {typ _} _ _ = ⊤

LCCC .~-refl {ctx Γ} {typ t} = refl
LCCC .~-refl {ctx _} {ctx _} = tt
LCCC .~-refl {typ _} {ctx _} = tt
LCCC .~-refl {typ _} {typ _} = tt

LCCC .~-sym {ctx Γ} {typ t} = sym
LCCC .~-sym {ctx _} {ctx _} _ = tt
LCCC .~-sym {typ _} {ctx _} _ = tt
LCCC .~-sym {typ _} {typ _} _ = tt

LCCC .~-trans {ctx Γ} {typ t} = trans
LCCC .~-trans {ctx _} {ctx _} _ _ = tt
LCCC .~-trans {typ _} {ctx _} _ _ = tt
LCCC .~-trans {typ _} {typ _} _ _ = tt

-- no meaningful composition for terms
LCCC ._∘_ {ctx Γ} {typ t} {typ c} = {!!}
LCCC ._∘_ {_    } {_    } = {!!}

-- likewise, no meaningful identity
LCCC .id  = {!!}

-- this we can ignore
LCCC .∘-assoc = {!!}
LCCC .∘-unitˡ = {!!}
LCCC .∘-unitʳ = {!!}
LCCC .∘-cong  = {!!}

LCCC .𝟙   = typ unit
LCCC .t {ctx Γ} = tt
LCCC .t {typ _} = tt

LCCC .t-uniq {ctx Γ} f = tt f
LCCC .t-uniq {typ t} f = tt

-- incredibly arbitrary definition
LCCC ._×_ (typ a) (typ b) = typ (prod a b)
LCCC ._×_ (typ a) (ctx _) = typ a
LCCC ._×_ (ctx _) (typ b) = typ b
LCCC ._×_ (ctx _) (ctx _) = ctx ε

LCCC .⟨_,_⟩ {ctx _} {ctx Γ} ()
LCCC .⟨_,_⟩ {typ _} {ctx Γ} ()
LCCC .⟨_,_⟩ {ctx Γ} {typ b} {typ c} = pair
LCCC .⟨_,_⟩ {typ a} {typ b} {typ c} _ _ = tt

LCCC .π₁ {ctx Γ} {typ b} = {!!}
LCCC .π₁ {ctx Γ} {ctx b} = {!!}
LCCC .π₁ {typ a} = {!!}
LCCC .π₂ = {!!}

LCCC .⟨⟩-resp-~ = {!!}
LCCC .π₁∘⟨⟩ = {!!}
LCCC .π₂∘⟨⟩ = {!!}
LCCC .⟨⟩∘π  = {!!}
LCCC ._^_   = {!!}
LCCC .eval  = {!!}
LCCC .curry = {!!}
LCCC .curry-resp-∼ = {!!}


unfold decode : Typ → Σ ℕ Ctx
unfold (prod a b) = suc (fst p) , (snd p , b)
  where p = unfold a
unfold t = 1 , (ε , t)

decode (prod a b) = unfold (prod a b)
decode _          = 0 , ε

-- we can synthesize a term of any type
syn : (t : Typ) → Tm Γ t
syn unit = tt
syn (arr a b) = lam (syn b)
syn (prod a b) = pair (syn a) (syn b)

typ : Tm Γ a → Typ
typ {a = a} t = a

-- that is convertible to any other term of same type
coh : (t : Tm Γ a) → Γ ⊢ a ∋ syn a ≡ t
coh (lam u) = abs (coh _)
coh {a = unit} (var x) = sym (tt _)
coh {a = arr a b} (var x) = {!!}
coh {a = prod a b} (var x) = trans (pair (coh _) (coh _)) (sym (ηpair _))
coh {a = unit} (app u v) = sym (tt _)
coh {a = arr a b} (app u v) = {!!}
coh {a = prod a a₁} (app t₁ t₂) = {!!}
coh tt = refl
coh (p₁ t) = trans (βp₁ _ {!!}) {!!}
coh (p₂ t) = trans {!βp₂!} (p₂ (coh {!!}))
coh (pair t₁ t₂) = pair (coh _) (coh _)

LCCC : CCC
LCCC .Ob = Typ

-- arrows are terms that go from ctx Γ to type t
-- and from types to types (we need t → 𝟙 for terminal objects, and ⟨_,_⟩ leads to t → 𝟙 × 𝟙 ...
LCCC .Hom  Γ t = Tm (decode Γ .snd) t

-- we relate arrows for terms that are βη-convertible
LCCC ._~_  {Γ} {t} = _ ⊢ _ ∋_≡_
LCCC .~-refl  = refl
LCCC .~-sym   = sym
LCCC .~-trans = trans

-- cheating a bit
_∘_ LCCC _ _ = syn _
LCCC .id t = syn t
LCCC .∘-assoc {a} {b} {c} f g h = refl
LCCC .∘-unitˡ {_} {unit} f = sym (tt f)
LCCC .∘-unitˡ {_} {arr a b} f = {!!}
LCCC .∘-unitˡ {_} {prod a b} f = sym {!!}
LCCC .∘-unitʳ = {!!}
LCCC .∘-cong  = {!!}

LCCC .𝟙 = unit
LCCC .t = tt
LCCC .t-uniq = tt

-- incredibly arbitrary definition
LCCC ._×_   = prod
LCCC .⟨_,_⟩ = pair

LCCC .π₁ = syn _
LCCC .π₂ = syn _

LCCC .⟨⟩-resp-~ = pair
LCCC .π₁∘⟨⟩ = {!!}
LCCC .π₂∘⟨⟩ = {!!}
LCCC .⟨⟩∘π  = {!!}
LCCC ._^_   = arr
LCCC .eval  = {!!}
LCCC .curry = {!!}
LCCC .curry-resp-∼ = {!!}
{-

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

-}
