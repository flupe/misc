module Generics.Constructions where

open import Generics.Prelude
open import Generics.Desc
open import Generics.Reflection


module Induction {i n} {I : Set i} (D : Desc {i} I n) {j} (P : {γ : I} → μ D γ → Set j) where

  -- | Predicate stating that P holds for every recursive argument inside x
  ConAll : ∀ {γ} {C : ConDesc I} (x : ⟦ C ⟧ᶜ (μ D) γ) → Set j
  ConAll {C = κ _}   (refl ) = ⋆
  ConAll {C = ι _ _} (x , d) = P x × ConAll d
  ConAll {C = π _ _} (_ , d) = ConAll d

  -- | Predicate stating that P holds for every recursive argument inside x
  DescAll : ∀ {γ} (x : μ D γ) → Set j
  DescAll ⟨ k , x ⟩ = ConAll x

  mutual
    all-con : (f : ∀ {γ} (x : μ D γ) → DescAll x → P x)
            → {C : ConDesc I}
            → {γ : I} (x : ⟦ C ⟧ᶜ (μ D) γ)
            → ConAll x
    all-con f {κ _}   (refl ) = ∗
    all-con f {ι _ _} (x , d) = ind f x , all-con f d
    all-con f {π S D} (_ , d) = all-con f d

    all : (f : ∀ {γ} (x : μ D γ) → DescAll x → P x)
        → {γ : I} (x : μ D γ)
        → DescAll x
    all f ⟨ k , x ⟩ = all-con f x
  
    -- | The generalized induction principle
    ind : (f : ∀ {γ} (x : μ D γ) → DescAll x → P x) -- ^ The induction hypothesis
        → {γ : I} (x : μ D γ)
        → P x
    ind f x = f x (all f x)


module Eliminator {i} {I : Set i} (A : I → Set i) (H : HasDesc {i} A)
                  {j} (P : {γ : I} → A γ → Set j) where

  open HasDesc

  unfold : (C : ConDesc I) (bow : con-type A C)
         → (tie : {γ : I} → A γ → Set (i ⊔ j)) → Set (i ⊔ j)
  unfold (κ k)   bow tie = tie bow
  unfold (ι γ C) bow tie = (x : A γ) → P x → unfold (C  ) (bow x) tie
  unfold (π S C) bow tie = (x : S)         → unfold (C x) (bow x) tie 

  -- | Returns the type of the induction method for the kᵗʰ constructor
  con-method : Fin (n H) → Set (i ⊔ j)
  con-method k = unfold (indexVec (D H) k) (constr H k) λ x → ⋆ {i ⊔ j} → P x

  -- | A vector containing the types of every constructor's induction method
  elim-methods : Vec (Set (i ⊔ j)) (n H)
  elim-methods = tabulate (con-method)

  P′ : {γ : I} → μ (D H) γ → Set j
  P′ x′ = P (from H x′)

  module Ind = Induction (D H) P′

  module _ (methods : Members (elim-methods)) where

    -- the goal is to derive the induction hypothesis on μ D
    to-hypothesis : {γ : I} → (x : μ (D H) γ) → Ind.DescAll x → P′ x
    to-hypothesis {γ} X@(⟨ k , x ⟩) = 
      walk (constr H k) (constr-proof H k) method  id pack x refl
      where
        -- we simply pick the right induction method out of our little bag,
        method  = transport id (indexTabulate (con-method) k) (lookupMember methods k)

        -- the kᵗʰ constructor
        con″    = indexVec (D H) k

        pack : {x₁ : ⟦ con″ ⟧ᶜ (μ (D H)) γ} → x ≡ x₁ → {x₂ : A γ} → x₂ ≡ from H ⟨ k , x₁ ⟩ → (⋆ → P x₂) → P′ X
        pack refl p Hx₂ = transport P p (Hx₂ ∗)

        walk : {C : ConDesc I} {f : ∀ {γ} → ⟦ C ⟧ᶜ (μ (D H)) γ → A γ → Set i} {g : ∀ {γ} →  A γ → Set (i ⊔ j)}
             → (cons : con-type A C)
             → con-proof′ (to H) f cons
             → unfold C cons g
             → (bow : ⟦ C ⟧ᶜ (μ (D H)) γ → ⟦ con″ ⟧ᶜ (μ (D H)) γ)
             → (tie : {x₁ : ⟦ C ⟧ᶜ (μ (D H)) γ} → x ≡ bow x₁ → {x₂ : A γ} → f x₁ x₂ → g x₂ → P′ X)
             → (x′ : ⟦ C ⟧ᶜ (μ (D H)) γ)
             → x ≡ bow x′
             → Ind.ConAll x′
             → P′ X
        walk {κ _  } cons cons′ meth bow tie refl    w p         = tie w cons′ meth
        walk {ι γ C} {f} cons cons′ meth bow tie (x , d) w (px , pd) =
          walk (cons (from H x)) (cons′ (from H x)) (meth (from H x) px) (bow ∘ (x ,_))
               -- ok maybe it would be best to simplify this
               (λ {x₂} x₁ {x₅} x₃ x₄ → tie x₁ (transport (λ x₇ → f (x₇ , x₂) x₅) (to∘from H x) x₃) x₄) d w pd
        walk {π S C} cons cons′ meth bow tie (s , d) w p =
          walk (cons s) (cons′ s) (meth s) (bow ∘ (s ,_)) tie d w p

    -- then, it's only a matter of applying the generalized induction principle
    elim : {γ : I} → (x : A γ) → P x
    elim {γ} x = transport P (from∘to H x) (Ind.ind to-hypothesis (to H x))


elim-type : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
          → ∀ {b} (P : {γ : I} → A γ → Set b) → Set (a ⊔ b)
elim-type A ⦃ H ⦄ {b} P = curryMemberType {b = b} (Eliminator.elim A H P)

get-elim : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
         → ∀ {b} (P : {γ : I} → A γ → Set b)
         → elim-type A P
get-elim A ⦃ H ⦄ P = curryMember (Eliminator.elim A H P)
