{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Prelude
import homotopy.ConstantToSetExtendsToProp as ConstExt
open import Pigeonhole

module FinSet where

-- the explicit type of finite sets
FinSet-exp : Type lone
FinSet-exp = Σ ℕ λ n → BAut (Fin n)

FinSet-prop : SubtypeProp Type₀ lone
FinSet-prop = (λ A → Trunc -1 (Σ ℕ λ n → Fin n == A)) , λ A → Trunc-level

-- the implicit type of finite sets
FinSet : Type lone
FinSet = Subtype FinSet-prop

Fin-inj-lemma : {n m : ℕ} → n < m → Fin m == Fin n → ⊥
Fin-inj-lemma {n} {m} n<m p = i≠j (<– (ap-equiv (coe-equiv p) i j) q)
  where
    i : Fin m
    i = fst (pigeonhole n<m (coe p))

    j : Fin m
    j = fst (snd (pigeonhole n<m (coe p)))

    i≠j : i ≠ j
    i≠j = fst (snd (snd (pigeonhole n<m (coe p))))

    q : coe p i == coe p j
    q = snd (snd (snd (pigeonhole n<m (coe p))))
    
Fin-inj : (n m : ℕ) → Fin n == Fin m → n == m
Fin-inj n m p with ℕ-trichotomy n m
Fin-inj n m p | inl q = q
Fin-inj n m p | inr (inl q) = ⊥-rec (Fin-inj-lemma q (! p))
Fin-inj n m p | inr (inr q) = ⊥-rec (Fin-inj-lemma q p)

FinSet-aux-prop : (A : Type₀) → SubtypeProp ℕ lone
FinSet-aux-prop A = (λ n → Trunc -1 (Fin n == A)) , (λ n → Trunc-level)
  
FinSet-aux : (A : FinSet) → Subtype (FinSet-aux-prop (fst A))
FinSet-aux (A , tz) = CE.ext tz
  where
    to : (Σ ℕ λ n → Fin n == A) → Subtype (FinSet-aux-prop A)
    to (n , p) = n , [ p ]

    to-const : (z₁ z₂ : Σ ℕ λ n → Fin n == A) → to z₁ == to z₂
    to-const (n₁ , p₁) (n₂ , p₂) = Subtype=-out (FinSet-aux-prop A) (Fin-inj n₁ n₂ (p₁ ∙ ! p₂))

    module CE =
      ConstExt (Subtype-level (FinSet-aux-prop A) ℕ-is-set) to to-const

card : FinSet → ℕ
card A = fst (FinSet-aux A)

card-eq : (A : FinSet) (n : ℕ) → Trunc -1 (Fin n == fst A) → card A == n
card-eq (A , tz) n tp = Trunc-rec (ℕ-is-set (card (A , tz)) n) (λ p →
  ap card (Subtype=-out FinSet-prop {A , tz} {Fin n , [ n , idp ]} (! p)) ) tp

FinSet-equiv : FinSet-exp ≃ FinSet
FinSet-equiv = equiv to from to-from from-to
  where
    to : FinSet-exp → FinSet
    to (n , A , tp) = A , Trunc-rec Trunc-level (λ p → [ n , p ]) tp

    from : FinSet → FinSet-exp
    from A = card A , fst A , snd (FinSet-aux A)

    to-from : (A : FinSet) → to (from A) == A
    to-from A = pair= idp (prop-has-all-paths Trunc-level (snd (to (from A))) (snd A))

    from-to : (A : FinSet-exp) → from (to A) == A
    from-to A = pair= (card-eq (to A) (fst A) (snd (snd A)))
      (↓-Subtype-cst-in (λ n → BAut-prop (Fin n)) idp)

_⊎_ : FinSet → FinSet → FinSet
(A , tz) ⊎ (B , tw) = A ⊔ B , Trunc-rec Trunc-level
  (λ { (n , p) → Trunc-rec Trunc-level
    (λ { (m , q) → [ n +' m , Fin-add-eq n m ∙ ap (λ C → C ⊔ Fin m) p ∙ ap (λ C → A ⊔ C) q ]}) tw}) tz

Unit-FinSet : FinSet
Unit-FinSet = ⊤ , [ S O , ua Fin-equiv-Coprod ∙ ap (λ C → C ⊔ ⊤) (ua Fin-equiv-Empty) ∙ Coprod-empty-eq ⊤ ]
