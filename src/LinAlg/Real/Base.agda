module LinAlg.Real.Base where

import Data.Nat as ℕ
import Data.Integer as ℤ
import Data.Integer.Properties as ℤ

open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
import Data.Rational.Unnormalised as ℚu
import Data.Rational.Unnormalised.Properties as ℚu
open import Data.Rational.Properties as ℚ
open import Data.Empty using (⊥-elim)
open import Data.Product
open import Data.Sum.Base

open import Level using (0ℓ)
open import Function.Base using (_∘_)

open import Relation.Unary using (Pred; _∈_; _∉_; _∩_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Binary.Definitions

open import Algebra.Definitions {A = ℚu.ℚᵘ} _≡_
open import Algebra.Structures {A = ℚ} _≡_
open import Algebra.Properties.Group ℚ.+-0-group

------------------------------------------------------------------------
-- Real numbers using Dedekind cuts.

record ℝ : Set₁ where
  field
    lower : Pred ℚ 0ℓ
    upper : Pred ℚ 0ℓ
    lower-inhabited : ∃ lower
    upper-inhabited : ∃ upper
    lower-open : ∀ {x} → x ∈ lower → ∃[ y ] (x ℚ.< y × y ∈ lower)
    upper-open : ∀ {y} → y ∈ upper → ∃[ x ] (x ℚ.< y × x ∈ upper)
    ordered : ∀ {x y} → x ∈ lower → y ∈ upper → x ℚ.< y
    located : ∀ {x y} → x ℚ.< y → x ∈ lower ⊎ y ∈ upper

  disjoint : ∀ x → x ∉ (lower ∩ upper)
  disjoint x (x∈L , x∈U) =
    ⊥-elim (ℚ.<-irrefl refl (ordered x∈L x∈U))

open ℝ

------------------------------------------------------------------------
-- Additional properties on unnormalized rationals.
-- Perhaps this should be moved to the stdlib?

ℚu-≤-<-trans : Trans ℚu._≤_ ℚu._<_ ℚu._<_
ℚu-≤-<-trans {p} {q} {r} (ℚu.*≤* p≤q) (ℚu.*<* q<r) = ℚu.*<*
  (ℤ.*-cancelʳ-<-non-neg _ (begin-strict
  let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; sd₁ = ↧ p; sd₂ = ↧ q; sd₃ = ↧ r in
  (n₁  *  sd₃) * sd₂  ≡⟨ ℤ.*-assoc n₁ sd₃ sd₂ ⟩
   n₁  * (sd₃  * sd₂) ≡⟨ cong (n₁ *_) (ℤ.*-comm sd₃ sd₂) ⟩
   n₁  * (sd₂  * sd₃) ≡⟨ sym (ℤ.*-assoc n₁ sd₂ sd₃) ⟩
  (n₁  *  sd₂) * sd₃  ≤⟨ ℤ.*-monoʳ-≤-pos (ℕ.pred (↧ₙ r)) p≤q ⟩
  (n₂  *  sd₁) * sd₃  ≡⟨ cong (_* sd₃) (ℤ.*-comm n₂ sd₁) ⟩
  (sd₁ *  n₂)  * sd₃  ≡⟨ ℤ.*-assoc sd₁ n₂ sd₃ ⟩
   sd₁ * (n₂   * sd₃) <⟨ ℤ.*-monoˡ-<-pos (ℕ.pred (↧ₙ p)) q<r ⟩
   sd₁ * (n₃   * sd₂) ≡⟨ sym (ℤ.*-assoc sd₁ n₃ sd₂) ⟩
  (sd₁ *  n₃)  * sd₂  ≡⟨ cong (_* sd₂) (ℤ.*-comm sd₁ n₃) ⟩
  (n₃  *  sd₁) * sd₂  ∎))
  where open ℤ.≤-Reasoning
        open import Data.Rational.Unnormalised hiding (_*_)
        open import Data.Integer.Base using (_*_)

ℚu-<-≤-trans : Trans ℚu._<_ ℚu._≤_ ℚu._<_
ℚu-<-≤-trans {p} {q} {r} (ℚu.*<* p<q) (ℚu.*≤* q≤r) = *<*
  (ℤ.*-cancelʳ-<-non-neg _ (begin-strict
  let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; sd₁ = ↧ p; sd₂ = ↧ q; sd₃ = ↧ r in
  (n₁  *  sd₃) * sd₂  ≡⟨ ℤ.*-assoc n₁ sd₃ sd₂ ⟩
   n₁  * (sd₃  * sd₂) ≡⟨ cong (n₁ *_) (ℤ.*-comm sd₃ sd₂) ⟩
   n₁  * (sd₂  * sd₃) ≡⟨ sym (ℤ.*-assoc n₁ sd₂ sd₃) ⟩
  (n₁  *  sd₂) * sd₃  <⟨ ℤ.*-monoʳ-<-pos (ℕ.pred (↧ₙ r)) p<q ⟩
  (n₂  *  sd₁) * sd₃  ≡⟨ cong (_* sd₃) (ℤ.*-comm n₂ sd₁) ⟩
  (sd₁ *  n₂)  * sd₃  ≡⟨ ℤ.*-assoc sd₁ n₂ sd₃ ⟩
   sd₁ * (n₂   * sd₃) ≤⟨ ℤ.*-monoˡ-≤-pos (ℕ.pred (↧ₙ p)) q≤r ⟩
   sd₁ * (n₃   * sd₂) ≡⟨ sym (ℤ.*-assoc sd₁ n₃ sd₂) ⟩
  (sd₁ *  n₃)  * sd₂  ≡⟨ cong (_* sd₂) (ℤ.*-comm sd₁ n₃) ⟩
  (n₃  *  sd₁) * sd₂  ∎))
  where open ℤ.≤-Reasoning
        open import Data.Rational.Unnormalised hiding (_*_)
        open import Data.Integer.Base using (_*_)

ℚu-<⇒≤ : ℚu._<_ ⇒ ℚu._≤_
ℚu-<⇒≤ (ℚu.*<* p<q) = ℚu.*≤* (ℤ.<⇒≤ p<q)

ℚu-<-trans : Transitive ℚu._<_
ℚu-<-trans p<q = ℚu-≤-<-trans (ℚu-<⇒≤ p<q)

ℚu-↥-neg : ∀ p → ℚu.↥ (ℚu.- p) ≡ ℤ.- (ℚu.↥ p)
ℚu-↥-neg (ℚu.mkℚᵘ ℤ.-[1+ _ ] _) = refl
ℚu-↥-neg (ℚu.mkℚᵘ ℤ.+0       _) = refl
ℚu-↥-neg (ℚu.mkℚᵘ ℤ.+[1+ _ ] _) = refl

ℚu-↧-neg : ∀ p → ℚu.↧ (ℚu.- p) ≡ (ℚu.↧ p)
ℚu-↧-neg (ℚu.mkℚᵘ ℤ.-[1+ _ ] _) = refl
ℚu-↧-neg (ℚu.mkℚᵘ ℤ.+0       _) = refl
ℚu-↧-neg (ℚu.mkℚᵘ ℤ.+[1+ _ ] _) = refl

ℚu-neg-mono-<-> : ℚu.-_ Preserves  ℚu._<_ ⟶ ℚu._>_
ℚu-neg-mono-<-> {m} {n} (ℚu.*<* m<n) = *<* (begin-strict
    ↥ (- n) * ↧ (- m) ≡⟨ cong (_* ↧ (- m)) (ℚu-↥-neg n) ⟩
    ℤ.- ↥ n * ↧ (- m) ≡⟨ cong (ℤ.- ↥ n *_) (ℚu-↧-neg m) ⟩
    ℤ.- ↥ n * ↧ m     ≡⟨ sym (ℤ.neg-distribˡ-* (↥ n) (↧ m)) ⟩
    ℤ.- (↥ n * ↧ m)   <⟨ ℤ.neg-mono-<-> m<n ⟩
    ℤ.- (↥ m * ↧ n)   ≡⟨ ℤ.neg-distribˡ-* (↥ m) (↧ n) ⟩
    ℤ.- ↥ m * ↧ n     ≡⟨ cong (ℤ.- ↥ m *_) (sym (ℚu-↧-neg n)) ⟩
    ℤ.- ↥ m * ↧ (- n) ≡⟨ cong ((_* ↧ (- n))) (sym (ℚu-↥-neg m)) ⟩
    ↥ (- m) * ↧ (- n) ∎
  )
  where open ℤ.≤-Reasoning
        open import Data.Rational.Unnormalised hiding (_*_)
        open import Data.Integer.Base using (_*_)

ℚu-<-respʳ-≈ : ℚu._<_ Respectsʳ ℚu._≃_
ℚu-<-respʳ-≈ {p} {q} {r} (ℚu.*≡* q≡r) (ℚu.*<* p<q) = ℚu.*<*
  (ℤ.*-cancelʳ-<-non-neg _ (begin-strict (
    let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; sd₁ = ↧ p; sd₂ = ↧ q; sd₃ = ↧ r in
    (n₁ *  sd₃) * sd₂  ≡⟨ ℤ.*-assoc n₁ sd₃ sd₂ ⟩
     n₁ * (sd₃  * sd₂) ≡⟨ cong (n₁ *_) (ℤ.*-comm sd₃ sd₂) ⟩
     n₁ * (sd₂  * sd₃) ≡⟨ sym (ℤ.*-assoc n₁ sd₂ sd₃) ⟩
    (n₁ *  sd₂) * sd₃  <⟨ ℤ.*-monoʳ-<-pos (ℕ.pred (↧ₙ r)) p<q ⟩
    (n₂ *  sd₁) * sd₃  ≡⟨ ℤ.*-assoc n₂ sd₁ sd₃ ⟩
     n₂ * (sd₁  * sd₃) ≡⟨ cong (n₂ *_) (ℤ.*-comm sd₁ sd₃) ⟩
     n₂ * (sd₃  * sd₁) ≡⟨ sym (ℤ.*-assoc n₂ sd₃ sd₁) ⟩
    (n₂ *  sd₃) * sd₁  ≡⟨ cong (_* sd₁) q≡r ⟩
    (n₃ *  sd₂) * sd₁  ≡⟨ ℤ.*-assoc n₃ sd₂ sd₁ ⟩
     n₃ * (sd₂  * sd₁) ≡⟨ cong (n₃ *_) (ℤ.*-comm sd₂ sd₁) ⟩
     n₃ * (sd₁  * sd₂) ≡⟨ sym (ℤ.*-assoc n₃ sd₁ sd₂) ⟩
    (n₃ *  sd₁) * sd₂  ∎
  )))
  where open ℤ.≤-Reasoning
        open import Data.Rational.Unnormalised hiding (_*_)
        open import Data.Integer.Base using (_*_)

ℚu-neg-involutive : Involutive (ℚu.-_)
ℚu-neg-involutive (ℚu.mkℚᵘ n dm) = cong (λ n → ℚu.mkℚᵘ n dm) (ℤ.neg-involutive n)

ℚu-<-respˡ-≈ : ℚu._<_ Respectsˡ ℚu._≃_
ℚu-<-respˡ-≈ {p} {q} {r} q≃r q<p =
  subst (ℚu._< _) (ℚu-neg-involutive _)
    (subst (_ ℚu.<_) (ℚu-neg-involutive _)
      (ℚu-neg-mono-<-> (ℚu-<-respʳ-≈ (ℚu.-‿cong q≃r) (ℚu-neg-mono-<-> q<p))))

ℚu-<-resp-≈ : ℚu._<_ Respects₂ ℚu._≃_
ℚu-<-resp-≈ = ℚu-<-respʳ-≈ , ℚu-<-respˡ-≈

module ℚu-≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ℚu.≤-isPreorder
    ℚu-<-trans
    ℚu-<-resp-≈
    ℚu-<⇒≤
    ℚu-<-≤-trans
    ℚu-≤-<-trans

postulate
  ℚu-+-monoʳ-< : ∀ x → (x ℚu.+_) Preserves ℚu._<_ ⟶ ℚu._<_

ℚu-+-monoˡ-< : ∀ x → (ℚu._+ x) Preserves ℚu._<_ ⟶ ℚu._<_
ℚu-+-monoˡ-< x {i} {j} i<j
  rewrite ℚu.+-comm-≡ i x
        | ℚu.+-comm-≡ j x
        = ℚu-+-monoʳ-< x i<j

ℚu-+-mono-< : ℚu._+_ Preserves₂ ℚu._<_ ⟶ ℚu._<_ ⟶ ℚu._<_
ℚu-+-mono-< x<y u<v = {!!}
  where open ℤ.≤-Reasoning


------------------------------------------------------------------------
-- Operations on reals.

infix 8 -_
infixl 7 _*_
infixl 6 _-_ _+_

-- addition

_+_ : ℝ → ℝ → ℝ
r₁ + r₂ = record
  { lower = λ z → ∃[ x ] ∃[ y ] (z ≡ x ℚ.+ y × lower r₁ x × lower r₂ y)
  ; upper = λ z → ∃[ x ] ∃[ y ] (z ≡ x ℚ.+ y × upper r₁ x × upper r₂ y)
  ; lower-inhabited =
      let x , x∈L₁ = lower-inhabited r₁
          y , y∈L₂ = lower-inhabited r₂
      in x ℚ.+ y , x , y , refl , x∈L₁ , y∈L₂
  ; upper-inhabited =
      let x , x∈U₁ = upper-inhabited r₁
          y , y∈U₂ = upper-inhabited r₂
      in x ℚ.+ y , x , y , refl , x∈U₁ , y∈U₂
  ; lower-open = λ {z} z∈L →
      let _ , _ , z≡x+y , x∈L₁ , y∈L₂ = z∈L
          x′ , x<x′ , x′∈L₁ = lower-open r₁ x∈L₁
          y′ , y<y′ , y′∈L₂ = lower-open r₂ y∈L₂
      in x′ ℚ.+ y′
       , {!!}
       , (x′ , y′ , refl , x′∈L₁ , y′∈L₂)
  ; upper-open = λ {z} z∈U →
      let _ , _ , z≡x+y , x∈U₁ , y∈U₂ = z∈U
          x′ , x<x′ , x′∈U₁ = upper-open r₁ x∈U₁
          y′ , y<y′ , y′∈U₂ = upper-open r₂ y∈U₂
      in x′ ℚ.+ y′
       , {!!}
       , (x′ , y′ , refl , x′∈U₁ , y′∈U₂)
  ; ordered = λ {z₁} {z₂} z₁∈L z₂∈U →
      let x₁ , y₁ , z₁≡x₁+y₁ , x₁∈L₁ , y₁∈L₂ = z₁∈L
          x₂ , y₂ , z₂≡x₂+y₂ , x₂∈U₁ , y₂∈U₂ = z₂∈U
          x₁<x₂ = ordered r₁ x₁∈L₁ x₂∈U₁
          y₁<y₂ = ordered r₂ y₁∈L₂ y₂∈U₂
      in {!!}
  ; located = {!!}
  }

{-
-- multiplication

_*_ : ℝ → ℝ → ℝ
r₁ * r₂ = record
  { lower = λ z → ∃[ x ] ∃[ y ] (z ≡ x ℚ.* y × lower r₁ x × lower r₂ y)
  ; upper = λ z → ∃[ x ] ∃[ y ] (z ≡ x ℚ.* y × upper r₁ x × upper r₂ y)
  ; lower-inhabited =
      let x , x∈L₁ = lower-inhabited r₁
          y , y∈L₂ = lower-inhabited r₂
      in x ℚ.* y , x , y , refl , x∈L₁ , y∈L₂
  ; upper-inhabited =
      let x , x∈U₁ = upper-inhabited r₁
          y , y∈U₂ = upper-inhabited r₂
      in x ℚ.* y , x , y , refl , x∈U₁ , y∈U₂
  ; lower-open = {!!}
  ; upper-open = {!!}
  ; ordered = {!!}
  ; located = {!!}
  }

-- negation

-_ : ℝ → ℝ
- r = record
  { lower = upper r ∘ ℚ.-_
  ; upper = lower r ∘ ℚ.-_
  ; lower-inhabited =
      let x , x∈upper = upper-inhabited r
      in ℚ.- x , subst (upper r) (sym (⁻¹-involutive x)) x∈upper
  ; upper-inhabited =
      let y , y∈lower = lower-inhabited r
      in ℚ.- y , subst (lower r) (sym (⁻¹-involutive y)) y∈lower

  ; lower-open = λ {y} -y∈U →
      let x , x<-y , x∈U = upper-open r -y∈U
      in ℚ.- x , {!!} , {!!}
  ; upper-open = {!!}
  ; ordered = {!!}
  ; located = {!!}
  }

_-_ : ℝ → ℝ → ℝ
x - y = x + - y

------------------------------------------------------------------------
-- Constructing reals from rationals.

fromℚ : ℚ → ℝ
fromℚ q = record
  { lower = ℚ._< q
  ; upper = q ℚ.<_
  ; lower-inhabited = {!!}
  ; upper-inhabited = {!!}
  ; lower-open = {!!}
  ; upper-open = {!!}
  ; ordered = {!!}
  ; located = {!!}
  }

------------------------------------------------------------------------
-- Some constants

0ℝ : ℝ
0ℝ = fromℚ 0ℚ

1ℝ : ℝ
1ℝ = fromℚ 1ℚ


-}
