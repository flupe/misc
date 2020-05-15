{-# OPTIONS --cubical #-}

module UP.Reflection where

open import UP.UP
open import Data.Nat.Base as ℕ
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Primitive
open import Agda.Builtin.List
  

infixl 10 _>>=_
_>>=_  = bindTC
_>>_ : {A : Set i} {B : Set j} → TC A → TC B → TC B
a >> b = bindTC a (const b)
return = returnTC

  
pattern ahr x = arg (arg-info hidden relevant) x
pattern avr x = arg (arg-info visible relevant) x
pattern sort s = agda-sort s
  

to-level : ℕ → Level
to-level zero    = lzero
to-level (suc n) = lsuc (to-level n)
  
it : (A : Set i) ⦃ x : A ⦄ → A
it _ ⦃ x ⦄ = x
  


⟦_∣_⟧′ : (A B : Term) → TC Term

-- TODO: take care of applications
⟦ A@(def n₁ []) ∣ B@(def n₂ []) ⟧′ =
  return $ def (quote it) (avr (def (quote _⋈_) (avr A ∷ avr B ∷ [])) ∷ [])

⟦ pi (avr a₁) (abs n₁ b₁) ∣ pi (avr a₂) (abs n₂ b₂) ⟧′ = do
     A ← ⟦ a₁ ∣ a₂ ⟧′
     B ← ⟦ b₁ ∣ b₂ ⟧′
     return $ def (quote ⋈-∀) (avr A ∷ avr (lam visible (abs n₁ B)) ∷ [])

⟦ sort s ∣ sort _ ⟧′ =
  case s of λ where
    (set l) → return $ def (quote ⋈-Set) (ahr l ∷ []) 
    (lit l) → do
      l′ ← quoteTC (to-level l)
      return $ def (quote ⋈-Set) (ahr l′ ∷ [])
    unknown → return $ def (quote ⋈-Set) (ahr unknown ∷ []) 

⟦ lam visible (abs n a) ∣ lam visible (abs _ b) ⟧′ = do
  t ← ⟦ a ∣ b ⟧′
  return $ lam hidden  $ abs "x"
         $ lam hidden  $ abs "y"
         $ lam visible $ abs "R" t

-- TODO: applications!!1!
⟦ var x [] ∣ var _ [] ⟧′ = return (var (x * 3) [])

⟦ _ ∣ _ ⟧′ = typeError (strErr "Not supported" ∷ [])


⟦_∣_⟧ : (A B : Set i) → Term → TC ⊤
⟦ A ∣ B ⟧ hole = do
  A′ ← quoteTC A
  B′ ← quoteTC B
  ⟦ A′ ∣ B′ ⟧′ >>= unify hole


_≈′_ : {A B : Set i} → A → B → {@(tactic ⟦ A ∣ B ⟧) E : A ⋈ B} → Set i
_≈′_ x y {E} = ur E x y


macro
  ⟦_⟧ : Term → Term → TC ⊤
  ⟦ A ⟧ hole = ⟦ A ∣ A ⟧′ >>= unify hole

  -- convert⟨_⟩ : ∀ {A B : Set i} {R : A ⋈ B} {f g} (helper : ur R f g)
  --            → Term → Term → TC ⊤
  --convert⟨ helper ⟩ t hole = do
  --  A ← inferType t
  --  B ← inferType hole
  --  {!!}
    -- A⋈B ← ⟦ A ∣ B ⟧′
