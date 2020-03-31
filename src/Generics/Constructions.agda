{-# OPTIONS --rewriting #-}
module Generics.Constructions where

open import Generics.Prelude
open import Generics.Desc
open import Generics.Reflection


module SingleStep {i} {I : Set i} {A : I → Set i} ⦃ H : HasDesc {i} A ⦄ where

  open HasDesc ⦃ ... ⦄

  -- VERY BAD
  step : ∀ {γ} → A γ → ⟦ D ⟧ᵈ A γ
  step {γ} x with to x
  ... | ⟨ k , x′ ⟩ = k , aux x′
    where
      aux : ∀ {C} → ⟦ C ⟧ᶜ (μ D) γ → ⟦ C ⟧ᶜ A γ
      aux {κ γ} refl      = refl
      aux {ι γ C} (x , d) = from x , aux d
      aux {π S C} (s , d) = s      , aux d

  -- VERY BAD TOO
  unstep : ∀ {γ} → ⟦ D ⟧ᵈ A γ → A γ
  unstep {γ} (k , x) = from ⟨ k , aux x ⟩
    where
      aux : ∀ {C} → ⟦ C ⟧ᶜ A γ → ⟦ C ⟧ᶜ (μ D) γ
      aux {κ γ  } refl    = refl
      aux {ι γ C} (x , d) = to x , aux d
      aux {π S C} (s , d) = s , aux d

  postulate
    unstep∘step : ∀ {γ} (x : A γ) → unstep (step x) ≡ x


module Induction {i n} {I : Set i} (D : Desc {i} I n) {j} (P : {γ : I} → μ D γ → Set j) where

  -- | Predicate stating that P holds for every recursive subobject in x
  AllCon : ∀ {C γ} (x : ⟦ C ⟧ᶜ (μ D) γ) → Set j
  AllCon {κ _  } (refl ) = ⋆
  AllCon {ι _ _} (x , d) = P x × AllCon d
  AllCon {π _ _} (_ , d) = AllCon d

  -- | Predicate stating that P holds for every recursive subobject in x
  All : ∀ {γ} (x : μ D γ) → Set j
  All ⟨ k , x ⟩ = AllCon x

  mutual
    all-con : (f : ∀ {γ} (x : μ D γ) → All x → P x)
            → ∀ {C γ} (x : ⟦ C ⟧ᶜ (μ D) γ)
            → AllCon x
    all-con f {κ _  } (refl ) = ∗
    all-con f {ι _ _} (x , d) = ind f x , all-con f d
    all-con f {π _ _} (_ , d) = all-con f d

    all : (f : ∀ {γ} (x : μ D γ) → All x → P x)
        → ∀ {γ} (x : μ D γ)
        → All x
    all f ⟨ k , x ⟩ = all-con f x
  
    -- | The generalized induction principle
    ind : (f : ∀ {γ} (x : μ D γ) → All x → P x) -- ^ The induction hypothesis
        → ∀ {γ} (x : μ D γ)
        → P x
    ind f x = f x (all f x)


module Eliminator {i} {I : Set i} (A : I → Set i) (H : HasDesc {i} A)
                  {j} (P : {γ : I} → A γ → Set j) where

  open HasDesc

  unfold : ∀ C → con-type A C → (∀ {γ} → A γ → Set (i ⊔ j)) → Set (i ⊔ j)
  unfold (κ _  ) con tie = tie con
  unfold (ι γ C) con tie = (x : A γ) → P x → unfold (C  ) (con x) tie
  unfold (π S C) con tie = (x : S)         → unfold (C x) (con x) tie 

  -- | Returns the type of the induction method for the kᵗʰ constructor
  con-method : Fin (n H) → Set (i ⊔ j)
  con-method k = unfold (indexVec (D H) k) (constr H k) λ x → ⋆ {i ⊔ j} → P x

  -- | A vector containing the types of every constructor's induction method
  elim-methods : Vec (Set (i ⊔ j)) (n H)
  elim-methods = tabulate (con-method)

  P′ : {γ : I} → μ (D H) γ → Set j
  P′ x′ = P (from H x′)


  module Ind = Induction (D H) P′


  module _ (methods : Members elim-methods) where

    -- we derive the induction hypothesis on μ D from the methods
    to-hypothesis : {γ : I} → (x : μ (D H) γ) → Ind.All x → P′ x
    to-hypothesis {γ} X@(⟨ k , x ⟩) IH = 
      walk (constr-proof H k) method id pack x IH refl
      where
        -- we retrieve the correct induction method from our little bag
        method = lookupMember methods k
        C      = indexVec (D H) k

        -- this function gets called at the end and finishes the proof
        pack : ∀ {x₁ x₂} → x₂ ≡ from H ⟨ k , x₁ ⟩ → x ≡ x₁ → (⋆ → P x₂) → P′ X
        pack p refl Px₂ = transport P p (Px₂ ∗)

        -- the entire point of this little walk is to construct x₁ and x₂
        walk : ∀ {C′} {f : ∀ {γ} → ⟦ C′ ⟧ᶜ (μ (D H)) γ → A γ → Set i} {g : ∀ {γ} → A γ → Set (i ⊔ j)}
             → {cons : con-type A C′}     -- ^ partial constructor in A γ
             → con-proof′ (to H) f cons   -- ^ partial proof that cons is related to C
             → unfold C′ cons g           -- ^ partial induction method for C
             → (mk : ⟦ C′ ⟧ᶜ (μ (D H)) γ → ⟦ C ⟧ᶜ (μ (D H)) γ)
             → (∀ {x₁ x₂} → f x₁ x₂ → x ≡ mk x₁ → g x₂ → P′ X)
             → ∀ x′ → Ind.AllCon x′ → x ≡ mk x′
             → P′ X

        walk {κ _  } p Px _ tie refl _ w = tie p w Px

        walk {ι _ _} {f} mkp mkP mk tie (x , d) (Px , Pd) =
          walk (mkp (from H x)) (mkP (from H x) Px) (mk ∘ (x ,_))
               (tie ∘ (transport (λ x → f (x , _) _) (to∘from H x)))
               d Pd

        walk {π _ _} mkp mkP mk tie (s , d) =
          walk (mkp s) (mkP s) (mk ∘ (s ,_)) tie d

    -- then, it's only a matter of applying the generalized induction principle
    elim : {γ : I} → (x : A γ) → P x
    elim x = transport P (from∘to H x) (Ind.ind to-hypothesis (to H x))


-- | Returns the type of the eliminator for the given datatype
elim-type : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
              {b} (P : {γ : I} → A γ → Set b)
          → Set (a ⊔ b)
elim-type A ⦃ H ⦄ {b} P = curryMembersType {b = b} (Eliminator.elim A H P)

-- | Returns the eliminator for the given datatype
get-elim : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
             {b} (P : {γ : I} → A γ → Set b)
         → elim-type A P
get-elim A ⦃ H ⦄ P = curryMembers (Eliminator.elim A H P)


module Case {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
            {b} (P : {γ : I} → A γ → Set b) where

  open HasDesc

  unfold : ∀ C → con-type A C → (∀ {γ} → A γ → Set (a ⊔ b)) → Set (a ⊔ b)
  unfold (κ _  ) con tie = tie con
  unfold (ι γ C) con tie = (x : A γ) → unfold (C  ) (con x) tie
  unfold (π S C) con tie = (x : S)   → unfold (C x) (con x) tie 

  -- | Returns the type of the case method for the kᵗʰ constructor
  con-method : Fin (n H) → Set (a ⊔ b)
  con-method k = unfold (indexVec (D H) k) (constr H k) λ x → ⋆ {a ⊔ b} → P x

  -- | A vector containing the types of every constructor's case method
  case-methods : Vec (Set (a ⊔ b)) (n H)
  case-methods = tabulate (con-method)

  module Elim = Eliminator A H P

  -- | Converts a kᵗʰ case method to a kᵗʰ elim method
  case-to-elim : (k : Fin (n H)) → con-method k → Elim.con-method k
  case-to-elim k method =
    walk (indexVec (D H) k) method
    where
      walk : ∀ C {con} → unfold C con _ → Elim.unfold C con _
      walk (κ γ  ) m = m
      walk (ι γ C) m = λ x _ → walk C (m x)
      walk (π S C) m = λ s   → walk (C s) (m s)

  -- | The generalized case analysis principle
  case : Members case-methods → {γ : I} (x : A γ) → P x
  case = Elim.elim ∘ mapMembers case-to-elim 


-- | Returns the type of the case analysis principle for the given datatype
case-type : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
              {b} (P : {γ : I} → A γ → Set b)
          → Set (a ⊔ b)
case-type A ⦃ H ⦄ {b} P = curryMembersType {b = b} (Case.case A P)

-- | Returns the case analysis principle for the given datatype
get-case : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
             {b} (P : {γ : I} → A γ → Set b)
         → case-type A P
get-case A ⦃ H ⦄ P = curryMembers (Case.case A P)


{-
through-elim : ∀ {a b} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
             → (membersP : Members (Eliminator.elim-methods A H (const (Set b))))
             -- simply put: case analysis on the constructor to build P
             → {!!}
             → {γ : I} (x : A γ)
             → Eliminator.elim A H (const (Set b)) membersP x
through-elim {a} {b} A ⦃ H ⦄ mems _ x =
  Eliminator.elim A H (Eliminator.elim A H (const (Set b)) mems)
    {!!}
    x
    -}


module Recursion {i n} {I : Set i} (D : Desc {i} I n)
                 {j} (P : ∀ {γ} → μ D γ → Set j) where

  mutual
    -- | Predicate stating that P holds for every recursive subobject
    -- | *guarded by constructors* in x
    BelowCon : ∀ {C γ} (x : ⟦ C ⟧ᶜ (μ D) γ) → Set j
    BelowCon {κ _  } _       = ⋆
    BelowCon {ι _ _} (x , d) = (P x × Below x) × BelowCon d
    BelowCon {π _ _} (_ , d) = BelowCon d

    -- | Predicate stating that P holds for every recursive subobject
    -- | *guarded by constructors* in x
    Below : ∀ {γ} (x : μ D γ) → Set j
    Below ⟨ _ , x ⟩ = BelowCon x

  module _ (p : ∀ {γ} (x : μ D γ) → Below x → P x) where

    step : ∀ {γ} (x : μ D γ) → Below x → P x × Below x
    step x m = p x m , m

    mutual
      below-con : ∀ {C γ} (x : ⟦ C ⟧ᶜ (μ D) γ) → BelowCon x
      below-con {κ _  } _       = ∗
      below-con {ι _ _} (x , d) = step x (below x) , below-con d
      below-con {π _ _} (_ , d) = below-con d

      below : ∀ {γ} (x : μ D γ) → Below x
      below ⟨ _ , x ⟩ = below-con x
  
    -- | The generalized structural recursion principle
    rec : ∀ {γ} (x : μ D γ) → P x
    rec x = p x (below x)


module Recursor {i} {I : Set i} (A : I → Set i) ⦃ H : HasDesc {i} A ⦄
                {j} (P : {γ : I} → A γ → Set j) where

  open HasDesc ⦃ ... ⦄
  open SingleStep ⦃ ... ⦄
  module R = Recursion D (P ∘ from)

  Below : ∀ {γ} → A γ → Set j
  Below x = R.Below (to x)

  rec : (∀ {γ} (x : A γ) → Below x → P x) → ∀ {γ} (x : A γ) → P x
  rec f x = transport P (from∘to x) px
    where
      px : P (from (to x))
      px = R.rec (λ x′ bx′ → f (from x′) (transport R.Below (sym (to∘from x′)) bx′))
                 (to x)

  {-

  Below-method : (k : Fin (n H)) → indexVec (Elim.elim-methods (const (Set j))) k
  Below-method k =
    let meth = walk (indexVec (D H) k) (constr H k) (λ x _ _ → x) []
    in transport id (sym (indexTabulate (Elim.con-method (const (Set j))) k)) meth
    where
      walk : (C : ConDesc I)
           → (con : con-type A C)
           → {f : ∀ {γ} → A γ → Set (i ⊔ lsuc j)}
           → (tie : Set j → ∀ {γ} (x : A γ) → f x)
           → List (Set j)
           → Elim.unfold (const (Set j)) C con f
      walk (κ _  ) con tie acc = tie {!!} con
      walk (ι γ C) con tie acc = λ x Px → walk C (con x) tie ((Px × P x) ∷ acc)
      walk (π _ C) con tie acc = λ s → walk (C s) (con s) tie acc

  -- | Predicate stating that P holds for every recursive subobject
  -- | *guarded by constructors* in x
  -- Below using the eliminator
  Below : ∀ {γ} (x : A γ) → Set j
  Below = Elim.elim _ (declareMembers Below-method)


  -- below-method : (k : Fin (n H)) → indexVec (Elim.elim-methods Below) k
  -- below-method k =
  --   let meth = walk (indexVec (D H) k) (constr H k) λ x → {!!}
  --   in transport id (sym (indexTabulate (Elim.con-method Below) k)) {!!}
  --   where
  --     walk : (C : ConDesc I)
  --          → (con : con-type A C)
  --          → {f : ∀ {γ} → (x : A γ) → Set (i ⊔ j)}
  --          → (tie : ∀ {γ} (x : A γ) → f x)
  --          → Elim.unfold Below C con f
  --     walk (κ _  ) con tie = {!!}
  --     walk (ι γ C) con tie = λ x Bx → {!!}
  --     walk (π _ C) con tie = λ s → walk (C s) (con s) {!!}


  below : (∀ {γ} (x : A γ) → Below x → P x)
        → ∀ {γ} (x : A γ) → Below x
  below P x = {!through-elim!} -- Elim.elim Below (declareMembers below-method)

  rec : (∀ {γ} (x : A γ) → Below x → P x)
      → ∀ {γ} (x : A γ) → P x
  rec f x = f x (below f x)
  -}

module SoIAmConfusion {a n} {I : Set a} (D : Desc {a} I n)
                 (X : I → Set a) where

  -- | Relation between two interpretations of the same constructor
  -- maybe we should use JMeq instead?
  NoConfusionCon : ∀ {C γ} (x y : ⟦ C ⟧ᶜ X γ) → Set a
  NoConfusionCon {κ _  } (refl  ) (refl  ) = ⊤′
  NoConfusionCon {ι _ _} (x , dx) (y , dy) = x ≡ y × NoConfusionCon dx dy
  NoConfusionCon {π _ _} (x , dx) (y , dy) = Σ (x ≡ y) λ { refl → NoConfusionCon dx dy }

  NoConfusion : ∀ {γ} (x y : ⟦ D ⟧ᵈ X γ) → Set a
  NoConfusion (kx , x) (ky , y) with kx == ky
  ... | yes refl = NoConfusionCon x y
  ... | no kx≢ky = ⊥′

  noConfRefl : ∀ {C γ} (x : ⟦ C ⟧ᶜ X γ) → NoConfusionCon x x
  noConfRefl {κ γ  } refl    = unit
  noConfRefl {ι γ C} (x , d) = refl , noConfRefl d
  noConfRefl {π S C} (s , d) = refl , noConfRefl d

  noConf : ∀ {γ} {x y : ⟦ D ⟧ᵈ X γ} → x ≡ y → NoConfusion x y
  noConf {x = kx , x} {ky , y} refl with kx == ky
  ... | yes refl = noConfRefl x
  ... | no kx≢ky = ⊥-elim (kx≢ky refl) 

  noConfCon : ∀ {C γ} {x y : ⟦ C ⟧ᶜ X γ} → NoConfusionCon x y → x ≡ y
  noConfCon {κ γ  } {x = refl} {refl} nc = refl
  noConfCon {ι γ C} (refl , nc) = cong _ (noConfCon nc)
  noConfCon {π S C} (refl , nc) = cong _ (noConfCon nc)

  noConf₂ : ∀ {γ} {x y : ⟦ D ⟧ᵈ X γ} → NoConfusion x y → x ≡ y
  noConf₂ {x = kx , x} {ky , y} with kx == ky
  ... | yes refl = cong (kx ,_) ∘ noConfCon
  ... | no kx≢ky = λ ()


module NoConfusion {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄ where

  open HasDesc ⦃ ... ⦄
  module C = SoIAmConfusion D A
  open SingleStep ⦃ ... ⦄

  NoConfusion : ∀ {γ} (x y : A γ) → Set a
  NoConfusion x y = C.NoConfusion (step x) (step y)

  noConf : ∀ {γ} {x y : A γ} → x ≡ y → NoConfusion x y
  noConf {x = x} {y} = C.noConf ∘ cong step

  noConf₂ : ∀ {γ} {x y : A γ} → NoConfusion x y → x ≡ y
  noConf₂ {x = x} {y} = aux ∘ C.noConf₂
    where
      aux : step x ≡ step y → x ≡ y
      aux p = trans (sym $ unstep∘step x)
            $ trans (cong unstep p) (unstep∘step y)
