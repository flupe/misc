module tel where

open import Agda.Primitive
open import Data.Unit
open import Data.Product
open import Data.Empty
open import Data.Fin.Base
open import Data.Nat.Base hiding (_⊔_)
open import Function.Base using (const; id; _∘_)
open import Data.String

data Tel : Setω
-- data _≼_ : Tel → Tel → Setω
lvlTel : Tel → Level
_≼_ : (A B : Tel) → Set (lvlTel A ⊔ lvlTel B)
tel : (T : Tel) → Set (lvlTel T)
-- ≼tel : ∀ {A B} → A ≼ B → tel B → tel A

infixl 8 _⊢<_>_
infix 7 _≼_

data Tel where
  ε      : Tel
  _⊢<_>_ : ∀ T {R a} → R ≼ T → (f : tel R → Set a) → Tel

lvlTel ε = lzero
lvlTel (_⊢<_>_ T {a = a} _ f) = lvlTel T ⊔ a

A ≼ B = tel B → tel A

tel ε       = ⊤
tel (T ⊢< R≼T > f) = Σ (tel T) (f ∘ R≼T)

≼-refl : ∀ {T} → T ≼ T
≼-refl = id

≼-trans : ∀ {A B C} → A ≼ B → B ≼ C → A ≼ C
≼-trans A≼B B≼C = A≼B ∘ B≼C 

≼-drop : ∀ {A B a R} {R≼B : R ≼ B} {f : tel R → Set a}
       → A ≼ B
       → A ≼ B ⊢< R≼B > f
≼-drop A≼B = A≼B ∘ proj₁

≼-keep : ∀ {A B a R} {R≼A : R ≼ A} {f : tel R → Set a}
         (A≼B : A ≼ B)
       → A ⊢< R≼A > f ≼ B ⊢< ≼-trans R≼A A≼B > f
≼-keep A≼B (tb , sf) = A≼B tb , sf


lvlHelper : Tel → Level
lvlHelper ε = lzero
lvlHelper (_⊢<_>_ T {R} {a} x f) = lvlHelper T ⊔ lvlTel R ⊔ a

Curry : ∀ T {a} → (tel T → Set a) → Set (lvlTel T ⊔ a)
Curry ε g = g tt
Curry (T ⊢< R≼T > f) g = Curry T (λ x → {y : f (R≼T x)} → g (x , y))

Helper : (M : ∀ {a} → Set a → Set a) (T : Tel) → Set (lvlHelper T)
Helper M (ε         ) = ⊤
Helper M (T ⊢< R≼T > f) = Helper M T × Curry _ λ x → M (f x)

Show : ∀ {a} → Set a → Set a
Show X = X → String

A : Tel
A = ε ⊢< ≼-refl                              > const ℕ
      ⊢< ≼-drop {R = ε} {f = const ℕ} ≼-refl > const ℕ
      ⊢< ≼-drop ≼-refl > {!!}


{-

a : tel A
a = (tt , 2) , 3 , ?

postulate
  showℕ : ℕ → String
  showF : ∀ {n} → Fin n → String

h : Helper Show A
h = (tt , showℕ) , showℕ


data _≼_ where
  base : ε ≼ ε
  keep : ∀ (A B R : Tel) {a} (f : tel R → Set a)
         (A≼B : A ≼ B)
         (R≼A : R ≼ A)
         (R≼B : R ≼ B)
       → (A ⊢< R≼A > f) ≼ (B ⊢< R≼B > f) 
  drop : ∀ (A B R : Tel) {a} (f : tel R → Set a)
         (A≼B : A ≼ B)
         (R≼B : R ≼ B)
       → A ≼ (B ⊢< R≼B > f)

≼-refl : ∀ {T} → T ≼ T
≼-refl {ε} = base
≼-refl {T ⊢< x > f} = keep T T _ f ≼-refl x x

T≼T⊢ : ∀ {T R} {R≼T : R ≼ T} {a} {f : tel R → Set a}
     → T ≼ T ⊢< R≼T > f
T≼T⊢ = drop _ _ _ _ ≼-refl _



A : Tel
A = ε ⊢< base   > const Set
      ⊢< ≼-refl > proj₂ 
      ⊢< T≼T⊢   > proj₂

snd : Tel
snd = ε ⊢< base   > const Set
        ⊢< ≼-refl > proj₂

ttt : snd ≼ A
ttt = keep _ _ _ proj₂ (drop _ _ _ proj₂ ≼-refl _) _ _


-- ≼-trans : ∀ {A B C} → Thinning A B → Thinning B C → Thinning A C
-- ≼-trans {C = ε} base Y = base
-- ≼-trans {C = C ⊢< x > f} base ()
-- ≼-trans (keep T T′ C f X X₁ X₂) Y = {!!}
-- ≼-trans (drop T _ C f X X₁) Y = {!!}

ε≼ : ∀ T → ε ≼ T
ε≼ ε = base
ε≼ (T ⊢< x > f) = drop ε T _ f (ε≼ T) x

≼-trans : ∀ {A B C} → A ≼ B → B ≼ C → A ≼ C
≼-trans {A = ε} A≤B B≤C = ε≼ _
≼-trans {A = A ⊢< x > f} A≤B B≤C = {!!}


≼tel {B = .ε} base t = tt
≼tel {B = .(B ⊢< R≼B > f)} (keep A B R f A≼B R≼A R≼B) (tb , ftrb) = ≼tel A≼B tb , {!!}
≼tel {B = .(B ⊢< R≼B > f)} (drop _ B R f A≼B R≼B) (tb , _) = ≼tel A≼B tb

-- T : Tel
-- T = ε ⊢ const Set
--       ⊢ const Set

-}
