module Generics.Constructions where

open import Generics.Prelude
open import Generics.Desc
open import Generics.Reflection


module Induction {i n} {I : Set i} (D : Desc {i} I n) {j} (P : {γ : I} → μ D γ → Set j) where

  -- | Predicate stating that P holds for every recursive subobject in x
  AllCon : ∀ {C γ} (x : ⟦ C ⟧ᶜ (μ D) γ) → Set j
  AllCon {κ _}   _       = ⋆
  AllCon {ι _ _} (x , d) = P x × AllCon d
  AllCon {π _ _} (_ , d) = AllCon d

  -- | Predicate stating that P holds for every recursive subobject in x
  All : ∀ {γ} (x : μ D γ) → Set j
  All ⟨ k , x ⟩ = AllCon x

  mutual
    all-con : (f : ∀ {γ} (x : μ D γ) → All x → P x)
            → ∀ {C γ} (x : ⟦ C ⟧ᶜ (μ D) γ)
            → AllCon x
    all-con f {κ _}   (refl ) = ∗
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


-- module NoConfusion {i n} {I : Set i} (D : Desc {i} I n) where
-- 
--   NoConfusionCon : ∀ {C γ} (x y : ⟦ C ⟧ᶜ (μ D) γ) → Set i → Set i
--   NoConfusionCon {κ _} _ _   P = P → P
--   NoConfusionCon {ι γ C} x y P = {!!}
--   NoConfusionCon {π S C} (s₁ , x) (s₂ , y) P = {!!}
-- 
--   NoConfusion : ∀ {γ} (x y : μ D γ) → Set (lsuc i)
--   NoConfusion ⟨ k , x ⟩ ⟨ m , y ⟩ with k == m
--   ... | yes refl = (P : Set i) → NoConfusionCon x y P
--   ... | no  _    = (P : Set i) → P


module Eliminator {i} {I : Set i} (A : I → Set i) (H : HasDesc {i} A)
                  {j} (P : {γ : I} → A γ → Set j) where

  open HasDesc

  unfold : ∀ C → con-type A C → (∀ {γ} → A γ → Set (i ⊔ j)) → Set (i ⊔ j)
  unfold (κ _)   con tie = tie con
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
        method = transport id (indexTabulate con-method k) (lookupMember methods k)
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


module Recursor {i} {I : Set i} (A : I → Set i) (H : HasDesc {i} A)
                {j} (P : {γ : I} → A γ → Set j) where

  open HasDesc

  mutual
    {-# TERMINATING #-}
    BelowCon : ∀ {C γ} (x : ⟦ C ⟧ᶜ (μ (D H)) γ) → Set j
    BelowCon {κ _  } _       = ⋆
    BelowCon {ι _ _} (x , d) = (P (from H x) × Below (from H x)) × BelowCon d
    BelowCon {π _ _} (_ , d) = BelowCon d

    {-# TERMINATING #-}
    Below : ∀ {γ} (x : A γ) → Set j
    Below {γ} x with to H x
    ... | ⟨ _ , x′ ⟩ = BelowCon x′

  P′ : {γ : I} → μ (D H) γ → Set j
  P′ x′ = P (from H x′)

  module Rec = Recursion (D H) P′

  module _ (p : ∀ {γ} (x : A γ) → Below x → P x) where

    mutual
      below-con : ∀ {C γ}
                → {x : ⟦ C ⟧ᶜ (μ (D H)) γ}
                → Rec.BelowCon x
                → BelowCon x
      below-con {κ _  } ∗ = ∗
      below-con {ι _ C} ((Px , bx) , bd) = (Px , below bx) , below-con {C} bd
      below-con {π S C} {x = s , _} b = below-con {C s} b

      below : ∀ {γ} {x : μ (D H) γ} → Rec.Below x → Below (from H x)
      below {x = x@(⟨ k , x′ ⟩)} b rewrite (to∘from H x) = below-con {indexVec (D H) k} b

    to-hypothesis : ∀ {γ} (x′ : μ (D H) γ) → Rec.Below x′ → P′ x′
    to-hypothesis {γ} X′@(⟨ k , x ⟩) B = p (from H X′) (below B)

    rec : ∀ {γ} (x : A γ) → P x
    rec x = transport P (from∘to H x) (Rec.rec to-hypothesis (to H x))
