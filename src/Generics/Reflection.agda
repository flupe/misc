module Generics.Reflection where

open import Agda.Builtin.Reflection
open import Builtin.Reflection

open import Tactic.Reflection
open import Tactic.Reflection.DeBruijn
open import Tactic.Reflection.Substitute

open import Generics.Prelude
open import Generics.Desc

import Agda.Builtin.Unit
open Agda.Builtin.Unit


con-type : ∀ {a} {I : Set a} (A : I → Set a) → ConDesc I → Set a
con-type A (κ γ)   = A γ 
con-type A (ι γ C) = A γ → con-type A C
con-type A (π S C) = (s : S) → con-type A (C s)

con-proof′ : ∀ {a n} {I : Set a} {A : I → Set a} {D : Desc I n} 
           → (to : {γ : I} → A γ → μ D γ)
           → {C : ConDesc I} (tie : {γ : I} → ⟦ C ⟧ᶜ (μ D) γ → A γ → Set a)
           → con-type A C → Set a
con-proof′ {A = A} to {κ γ}   tie c = tie refl c
con-proof′ {A = A} to {ι γ C} tie c = (x : A γ) → con-proof′ to {C = C} (tie ∘ (to x ,_)) (c x)
con-proof′ {A = A} to {π S C} tie c = (s : S)   → con-proof′ to {C = C s} (tie ∘ (s ,_)) (c s) 

con-proof : ∀ {a n} {I : Set a} {A : I → Set a} {D : Desc I n} 
           → (to : {γ : I} → A γ → μ D γ) (from : {γ : I} → μ D γ → A γ)
           → ∀ {k} (constr : con-type A (indexVec D k))
           → Set a
con-proof {a} {I = I} {A} {D} to from {k} constr = con-proof′ to tie constr
  where
    tie : {γ : I} → ⟦ indexVec D k ⟧ᶜ (μ D) γ → A γ → Set a
    tie X′ X = X ≡ from ⟨ k , X′ ⟩



record HasDesc {a} {I : Set a} (A : I → Set a) : Set (lsuc a) where
  field
    {n} : Nat
    D : Desc {a} I n

    to   : ∀ {i} → A i → μ {a} D i
    from : {i : I} → μ D i → A i

    to∘from : ∀ {i} (x : μ D i) → to (from x) ≡ x
    from∘to : ∀ {i} (x : A i)   → from (to x) ≡ x

    -- | A map from a position in the datatype to the actual constructor
    constr : (k : Fin n) → con-type A (indexVec D k)

    -- | A proof that constr indeed holds the constructors of A
    constr-proof : (k : Fin n) → con-proof to from (constr k)

open HasDesc ⦃ ... ⦄

hr : ∀ {a} {A : Set a} → A → Arg A
hr t = arg (arg-info hidden relevant) t

ir : ∀ {a} {A : Set a} → A → Arg A
ir t = arg (arg-info instance′ relevant) t

vr : ∀ {a} {A : Set a} → A → Arg A
vr t = arg (arg-info visible relevant) t

uhr : Arg Term
uhr = hr unknown

uvr : Arg Term
uvr = vr unknown

last : List (Arg Term) → Arg Term
last [] = vr (con (quote Agda.Builtin.Unit.tt) [])
last (x ∷ []) = x
last (x ∷ xs) = last xs

last′ : List (Arg Term) → Term
last′ [] = con (quote Agda.Builtin.Unit.tt) []
last′ (arg _ x ∷ []) = x
last′ (x ∷ xs) = last′ xs

-- | Unwraps the value of a Maybe A into TC A,
-- | fails with given error message if there is no value.
unwrap : ∀ {a} {A : Set a} → String → Maybe A → TC A
unwrap msg nothing  = typeError (strErr msg ∷ [])
unwrap _   (just x) = returnTC x

-- TODO: rewrite this, it′s ugly and too verbose
mkCon : Name → Nat → Type → TC Term
mkCon t nb (def f args)  = return (con (quote ConDesc.κ) (last args ∷ []))
mkCon t nb (pi (arg i a) (abs n b)) = do
 case a of λ where
   (def f args) →
     case (t == f) of λ where
         (yes _) → do
              b′ ← mkCon t nb b
                   >>= unwrap "Constructor uses recursive value as argument."
                     ∘ strengthen 1
              return (con (quote ConDesc.ι) (last args ∷ vr b′ ∷ []))
         (no  _) → do
              b′ ← mkCon t nb b
              return (con (quote ConDesc.π) (vr a ∷ vr (lam visible (abs n b′)) ∷ []))
   _ → do b′ ← mkCon t nb b
          return (con (quote ConDesc.π) (vr a ∷ vr (lam visible (abs n b′)) ∷ []))

mkCon _ _ _ = typeError (strErr "Cannot convert type to constructor description." ∷ [])

specialize : Type → List (Arg Term) → TC Type
specialize xt []       = return xt
specialize (pi (arg i a) (abs n b)) (arg _ x ∷ xs) with maybeSafe x
... | just xsafe = specialize (substTerm (xsafe ∷ []) b) xs
... | nothing    = typeError (strErr "Trying to specialize with an unsafe term." ∷ [])
specialize _ _   = typeError (strErr "Ill-formed constructor type." ∷ [])

mkDesc : Name → List (Arg Term) → Nat → List Name → TC Term
mkDesc t params nb [] = return (con (quote Vec.[]) [])
mkDesc t params nb (x ∷ xs) = do
  xt  ← getType x
  x′  ← specialize xt params >>= mkCon t nb
  xs′ ← mkDesc t params nb xs
  return (con (quote Vec._∷_) (vr x′ ∷ vr xs′ ∷ []))

macro 
  deriveDesc : Term → Term → TC ⊤
  deriveDesc (def n params) hole = do
    x ← getDefinition n
    case x of λ where
      (data-type pars cs) → mkDesc n params pars cs >>= unify hole
      _ → typeError (strErr "Given argument is NOT a datatype." ∷ [])
  deriveDesc _ _ = typeError (strErr "Given argument is NOT a datatype." ∷ [])


module Deriving where

  ConInstance : ∀ {i j} (M : Set i → Set j) {I : Set i} (C : ConDesc I) → Set (i ⊔ j)

  record ConΣ {i j} (M : Set i → Set j) {I : Set i} (S : Set i) (D : S → ConDesc I): Set (i ⊔ j) where
    inductive
    constructor _,_
    field
      ms : M S
      md : (s : S) → ConInstance M (D s)

  ConInstance M (κ k)   = ⋆
  ConInstance M (ι i D) = ConInstance M D
  ConInstance M (π S D) = ConΣ M S D

  DescInstance : ∀ {i j} (M : Set i → Set j) {n} {I : Set i} (D : Desc I n) → Set (lsuc i ⊔ j)
  DescInstance M {n} D = VecAll (ConInstance M) D


  instance
    κ-inst : ∀ {i j} {M : Set i → Set j} {I : Set i} {k : I} → ConInstance M (κ k)
    κ-inst = ∗

    ι-inst : ∀ {i j} {M : Set i → Set j} {I : Set i} {r : I} {D : ConDesc I}
           → ⦃ ConInstance M D ⦄ → ConInstance M (ι r D)
    ι-inst ⦃ MD ⦄ = MD

    π-inst : ∀ {i j} {M : Set i → Set j} {I : Set i} {S : Set i} {D : S → ConDesc I}
           → ⦃ M S ⦄ → ⦃ ∀ {s} → ConInstance M (D s) ⦄
           → ConInstance M (π S D)
    π-inst ⦃ MS ⦄ ⦃ MD ⦄ = MS , λ s → MD
    
    desc-[]-inst : ∀ {i j} {M : Set i → Set j} {I : Set i} → DescInstance M {I = I} []
    desc-[]-inst = []

    desc-∷-inst : ∀ {i j} {M : Set i → Set j} {I : Set i} {n} {C : ConDesc I} {D : Desc I n}
                → ⦃ ConInstance M C ⦄ → ⦃ DescInstance M D ⦄
                → DescInstance M (C ∷ D)
    desc-∷-inst ⦃ MC ⦄ ⦃ MD ⦄ = MC ∷ MD
                

  module Common where
  
    open import Prelude.Show
    open import Prelude.String
    open import Prelude.Equality
  

    module ShowMu {i n} {I : Set i} {D : Desc {i} I n} {DI : DescInstance Show D} where
      mutual
        showCon : {C : ConDesc I} {CI : ConInstance Show C} {γ : I} → ⟦ C ⟧ᶜ (μ D) γ → String
        showCon {C = κ k  } refl = ""
        showCon {C = ι i D} {CI} (x , d) = " (" <> showMu x <> ")" <> showCon {CI = CI} d
        showCon {C = π S D} {CI = XI , SI} (s , d) = " " <> show ⦃ XI ⦄ s <> showCon {CI = SI s} d
  
        showDesc : {γ : I} → ⟦ D ⟧ᵈ (μ D) γ → String
        showDesc (k , x) = "con" <> show k <> showCon {CI = lookupAll DI k} x 
  
        showMu : {γ : I} → μ D γ → String
        showMu ⟨ x ⟩ = showDesc x
  
    instance
      ShowCon : ∀ {i n} {I : Set i} {D : Desc I n} {γ : I} ⦃ DI : DescInstance Show D ⦄ → Show (μ D γ)
      ShowCon ⦃ DI ⦄ = simpleShowInstance (ShowMu.showMu {DI = DI})

    deriveShow : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc A ⦄ {γ : I}
               → ⦃ E : Show (μ D γ) ⦄ → Show (A γ)
    deriveShow A ⦃ H ⦄ ⦃ E ⦄ = simpleShowInstance (show ⦃ E ⦄ ∘ to)


    module EqMu {i n} {I : Set i} {D : Desc I n} {DI : DescInstance Eq D} where
  
      private
        Σeq₁ : ∀ {a b} {A : Set a} {B : A → Set b} {x y : Σ A B}
             → x ≡ y → fst x ≡ fst y
        Σeq₁ refl = refl
  
        Σeq₂ : ∀ {a b} {A : Set a} {B : A → Set b} {s x y}
             → _≡_ {A = Σ A B} (s , x) (s , y) → x ≡ y
        Σeq₂ refl = refl
  
        Σdeqinj₂ : ∀ {a b} {A : Set a} {B : A → Set b} {s x y}
             → Dec (x ≡ y) → Dec (_≡_ {A = Σ A B} (s , x) (s , y))
        Σdeqinj₂ (yes x≡y) = yes (case x≡y of λ { refl → refl })
        Σdeqinj₂ {a} {b} (no x≢y) = no (x≢y ∘ Σeq₂)
  
      mutual
        eqCon : {C : ConDesc I} {CI : ConInstance Eq C} {γ : I}
              → (x y : ⟦ C ⟧ᶜ (μ D) γ) → Dec (x ≡ y)
        eqCon {C = κ k } refl refl = yes refl
  
        eqCon {C = ι r D} {CI} (x₁ , d₁) (x₂ , d₂) with eqMu x₁ x₂
        ... | no x₁≢x₂ = no (x₁≢x₂ ∘ Σeq₁)
        ... | yes refl = Σdeqinj₂ (eqCon {CI = CI} d₁ d₂)
  
        eqCon {C = π S D} {CI = XI , SI} (s₁ , d₁) (s₂ , d₂) with _==_ ⦃ XI ⦄ s₁ s₂
        ... | no s₁≢s₂ = no (s₁≢s₂ ∘ Σeq₁)
        ... | yes refl =  Σdeqinj₂ (eqCon {CI = SI s₁} d₁ d₂)
  
        eqDesc : {γ : I} → (x y : ⟦ D ⟧ᵈ (μ D) γ) → Dec (x ≡ y)
        eqDesc (k₁ , x) (k₂ , y) with k₁ == k₂
        ... | no k₁≢k₂ = no (k₁≢k₂ ∘ Σeq₁)
        ... | yes refl = Σdeqinj₂ (eqCon {CI = lookupAll DI k₁} x y)
  
        eqMu : {γ : I} → (x y : μ D γ) → Dec (x ≡ y)
        eqMu ⟨ x ⟩ ⟨ y ⟩ = decEq₁ (λ { refl → refl }) (eqDesc x y)
  
    instance
      EqCon : ∀ {i n} {I : Set i} {D : Desc I n} {γ : I} ⦃ DI : DescInstance Eq D ⦄ → Eq (μ D γ)
      _==_ ⦃ EqCon ⦃ DI ⦄ ⦄ = EqMu.eqMu {DI = DI}

    deriveEq : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc A ⦄ {γ : I}
             → ⦃ E : Eq (μ D γ) ⦄ → Eq (A γ)
    _==_ ⦃ deriveEq A ⦃ H ⦄ ⦃ E ⦄ ⦄ x y =
      decEqIso {f = to} {g = from} from∘to (_==_ ⦃ E ⦄ (to x) (to y))

