{-# OPTIONS --cubical #-}

module UP.Example where

open import UP.UP
open import UP.Reflection

open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat as ℕ using () renaming (Nat to ℕ)
open import Cubical.Foundations.Isomorphism using (isoToEquiv; iso)


module ℕᵇ where

  data ℕᵇ : Set where
    zero   : ℕᵇ
    2[1+_] : ℕᵇ → ℕᵇ
    1+[2_] : ℕᵇ → ℕᵇ

  suc : ℕᵇ → ℕᵇ
  suc zero     = 1+[2 zero ]
  suc 2[1+ x ] = 1+[2 suc x ]
  suc 1+[2 x ] = 2[1+ x ]

  double : ℕᵇ → ℕᵇ
  double zero     = zero
  double 2[1+ x ] = 2[1+ 1+[2 x ] ]
  double 1+[2 x ] = 2[1+ double x ]

  infixl 6 _+_
  infixl 7 _*_

  _+_ : ℕᵇ → ℕᵇ → ℕᵇ
  zero     + y        = y
  x        + zero     = x
  2[1+ x ] + 2[1+ y ] = 2[1+ suc (x + y) ]
  2[1+ x ] + 1+[2 y ] = suc 2[1+ x + y ]
  1+[2 x ] + 2[1+ y ] = suc 2[1+ x + y ]
  1+[2 x ] + 1+[2 y ] = suc 1+[2 x + y ]

  _*_ : ℕᵇ → ℕᵇ → ℕᵇ
  zero * y = zero
  x * zero = zero
  2[1+ x ] * 2[1+ y ] = double 2[1+ x + y + x * y ]
  2[1+ x ] * 1+[2 y ] = 2[1+ x + y * 2[1+ x ] ]
  1+[2 x ] * 2[1+ y ] = 2[1+ y + x * 2[1+ y ] ]
  1+[2 x ] * 1+[2 y ] = 1+[2 x + y * 1+[2 x ] ]


open ℕᵇ using (ℕᵇ; zero; 2[1+_]; 1+[2_])

doubleℕ : ℕ → ℕ
doubleℕ 0 = 0
doubleℕ (ℕ.suc n) = ℕ.suc (ℕ.suc (doubleℕ n))

toℕᵇ : ℕ → ℕᵇ
toℕᵇ 0 = zero
toℕᵇ (ℕ.suc x) = ℕᵇ.suc (toℕᵇ x)

fromℕᵇ : ℕᵇ → ℕ
fromℕᵇ zero = 0
fromℕᵇ 2[1+ x ] = ℕ.suc (ℕ.suc (doubleℕ $ fromℕᵇ x))
fromℕᵇ 1+[2 x ] = ℕ.suc (doubleℕ $ fromℕᵇ x)

fromℕᵇ-suc : ∀ x → fromℕᵇ (ℕᵇ.suc x) ≡ ℕ.suc (fromℕᵇ x)
fromℕᵇ-suc zero = refl
fromℕᵇ-suc 2[1+ x ] i = ℕ.suc (doubleℕ (fromℕᵇ-suc x i))
fromℕᵇ-suc 1+[2 x ] = refl

double-toℕᵇ-suc : ∀ x → ℕᵇ.suc (toℕᵇ (doubleℕ x)) ≡ 1+[2 toℕᵇ x ]
double-toℕᵇ-suc 0 = refl
double-toℕᵇ-suc (ℕ.suc x) i = ℕᵇ.suc (ℕᵇ.suc (double-toℕᵇ-suc x i))

toℕᵇ∘fromℕᵇ : ∀ x → toℕᵇ (fromℕᵇ x) ≡ x
toℕᵇ∘fromℕᵇ zero     = refl
toℕᵇ∘fromℕᵇ 2[1+ x ] = begin
   toℕᵇ (fromℕᵇ 2[1+ x ])                      ≡⟨⟩
   ℕᵇ.suc (ℕᵇ.suc (toℕᵇ (doubleℕ (fromℕᵇ x)))) ≡⟨ cong ℕᵇ.suc (double-toℕᵇ-suc (fromℕᵇ x)) ⟩
   ℕᵇ.suc 1+[2 toℕᵇ (fromℕᵇ x) ]               ≡⟨ cong (ℕᵇ.suc ∘ 1+[2_]) (toℕᵇ∘fromℕᵇ x) ⟩
   2[1+ x ]                                    ∎
  where open ≡-Reasoning

toℕᵇ∘fromℕᵇ 1+[2 x ] = begin
  toℕᵇ (fromℕᵇ 1+[2 x ]) ≡⟨⟩
  ℕᵇ.suc (toℕᵇ (doubleℕ (fromℕᵇ x))) ≡⟨ double-toℕᵇ-suc (fromℕᵇ x) ⟩
  1+[2 toℕᵇ (fromℕᵇ x) ]             ≡⟨ cong 1+[2_] (toℕᵇ∘fromℕᵇ x) ⟩
  1+[2 x ] ∎
  where open ≡-Reasoning

fromℕᵇ∘toℕᵇ : ∀ x → fromℕᵇ (toℕᵇ x) ≡ x
fromℕᵇ∘toℕᵇ 0 = refl
fromℕᵇ∘toℕᵇ (ℕ.suc x) = begin
  fromℕᵇ (ℕᵇ.suc (toℕᵇ x)) ≡⟨ fromℕᵇ-suc (toℕᵇ x) ⟩
  ℕ.suc (fromℕᵇ (toℕᵇ x))  ≡⟨ cong ℕ.suc (fromℕᵇ∘toℕᵇ x) ⟩
  ℕ.suc x                  ∎
  where open ≡-Reasoning

ℕ≃ℕᵇ : ℕ ≃ ℕᵇ
ℕ≃ℕᵇ = isoToEquiv (iso toℕᵇ fromℕᵇ toℕᵇ∘fromℕᵇ fromℕᵇ∘toℕᵇ)

ℕ≈ℕᵇ : ℕ ≈ ℕᵇ
ℕ≈ℕᵇ = ≃⇒≈ ℕ≃ℕᵇ

instance
  ℕ⋈ℕᵇ : ℕ ⋈ ℕᵇ
  ℕ⋈ℕᵇ = rel ℕ≈ℕᵇ
  
  ℕ⋈ℕ : ℕ ⋈ ℕ
  ℕ⋈ℕ = ⋈-refl ℕ

0≈0ᵇ : 0 ≈ ℕᵇ.zero
0≈0ᵇ = ■ ℕ≈ℕᵇ 0

postulate
  add≈addᵇ : ℕ._+_ ≈′ ℕᵇ._+_
  mul≈mulᵇ : ℕ._*_ ≈′ ℕᵇ._*_

cube : ℕ → ℕ
cube x = x ℕ.* x ℕ.* x
