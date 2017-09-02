{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Prelude where

lone : ULevel
lone = lsucc lzero

_F≟_ : {n : ℕ} → has-dec-eq (Fin n)
(k , k<n) F≟ (l , l<n) with ℕ-has-dec-eq k l
(k , k<n) F≟ (l , l<n) | inl p = inl (pair= p (from-transp _ p (<-has-all-paths _ _)))
(k , k<n) F≟ (l , l<n) | inr ¬p = inr λ q → ¬p (ap fst q)

BAut : ∀ {i} → Type i → Type (lsucc i)
BAut {i} A = Σ (Type i) λ X → Trunc -1 (A == X)

pBAut : ∀ {i} → Type i → Ptd (lsucc i)
de⊙ (pBAut A) = BAut A
pt (pBAut A) = A , [ idp ]

BAut-trunc-path : ∀ {i} (A X : Type i) → (tp : Trunc -1 (A == X)) → Trunc -1 ((A , [ idp ]) == (X , tp) :> BAut A)
BAut-trunc-path {i} A X = Trunc-elim (λ p → Trunc-level) λ p → [ pair= p (from-transp _ _ (prop-has-all-paths Trunc-level _ _)) ]

BAut-conn : ∀ {i} (A : Type i) → is-connected 0 (BAut A)
fst (BAut-conn A) = [ pt (pBAut A) ]
snd (BAut-conn A) = Trunc-elim (λ x → raise-level (from-nat 0) Trunc-level [ A , [ idp ] ] x)
                               (λ { (X , tp) → <– (Trunc=-equiv [ A , [ idp ] ] [ X , tp ])
                                                  (BAut-trunc-path A X tp) })

Coprod-empty-eq : ∀ {i} (A : Type i) → ⊥ ⊔ A == A
Coprod-empty-eq {i} (A) = ua (equiv to from to-from from-to)
  where
    to : ⊥ ⊔ A → A
    to (inl ())
    to (inr a) = a

    from : A → ⊥ ⊔ A
    from a = inr a

    to-from : (a : A) → to (from a) == a
    to-from a = idp

    from-to : (x : ⊥ ⊔ A) → from (to x) == x
    from-to (inl ())
    from-to (inr a) = idp

Fin-O-eq : Fin O == ⊥
Fin-O-eq = ua Fin-equiv-Empty

Fin-S-eq : (n : ℕ) → Fin (S n) == Fin n ⊔ ⊤
Fin-S-eq n = ua Fin-equiv-Coprod

ℕ-eq-⊤-⊔-ℕ : ℕ == ⊤ ⊔ ℕ
ℕ-eq-⊤-⊔-ℕ = ua (equiv to from to-from from-to)
  where
    to : ℕ → ⊤ ⊔ ℕ
    to O     = inl unit
    to (S n) = inr n

    from : ⊤ ⊔ ℕ → ℕ
    from (inl _) = O
    from (inr n) = S n

    to-from : (x : ⊤ ⊔ ℕ) → to (from x) == x
    to-from (inl unit) = idp
    to-from (inr n)    = idp

    from-to : (n : ℕ) → from (to n) == n
    from-to O     = idp
    from-to (S n) = idp

add-unit : (n : ℕ) → BAut (Fin n) → BAut (Fin (S n))
add-unit n (X , tp) = X ⊔ ⊤ , Trunc-rec Trunc-level (λ p → [ Fin-S-eq n ∙ ap (λ A → A ⊔ ⊤) p ]) tp

Coprod-swap : (A B : Set) → A ⊔ B → B ⊔ A
Coprod-swap A B (inl a) = inr a
Coprod-swap A B (inr b) = inl b

Coprod-swap-swap : (A B : Set) → (x : A ⊔ B) → Coprod-swap B A (Coprod-swap A B x) == x
Coprod-swap-swap A B (inl a) = idp
Coprod-swap-swap A B (inr b) = idp

Coprod-comm : (A B : Set) → A ⊔ B == B ⊔ A
Coprod-comm A B = ua (equiv (Coprod-swap A B) (Coprod-swap B A) (Coprod-swap-swap B A) (Coprod-swap-swap A B))

Coprod-assoc : (A B C : Set) → A ⊔ (B ⊔ C) == (A ⊔ B) ⊔ C
Coprod-assoc A B C = ua (equiv to from to-from from-to)
  where
    to : A ⊔ (B ⊔ C) → (A ⊔ B) ⊔ C
    to (inl a) = inl (inl a)
    to (inr (inl b)) = inl (inr b)
    to (inr (inr c)) = inr c

    from : (A ⊔ B) ⊔ C → A ⊔ (B ⊔ C)
    from (inl (inl a)) = inl a
    from (inl (inr b)) = inr (inl b)
    from (inr c) = inr (inr c)

    to-from : (x : (A ⊔ B) ⊔ C) → to (from x) == x
    to-from (inl (inl a)) = idp
    to-from (inl (inr b)) = idp
    to-from (inr c) = idp

    from-to : (x : A ⊔ (B ⊔ C)) → from (to x) == x
    from-to (inl a) = idp
    from-to (inr (inl b)) = idp
    from-to (inr (inr c)) = idp
    
unit-add : (n : ℕ) → BAut (Fin n) → BAut (Fin (S n))
unit-add n (X , tp) = ⊤ ⊔ X , Trunc-rec Trunc-level (λ p → [ Fin-S-eq n ∙ ap (λ A → A ⊔ ⊤) p ∙ Coprod-comm X ⊤ ]) tp

infixl 80 _+'_

-- we need the version of addition defined by recursion on the second argument
_+'_ : ℕ → ℕ → ℕ
n +' O = n
n +' S m = S (n +' m)

Fin-add-eq : (n m : ℕ) → Fin (n +' m) == Fin n ⊔ Fin m
Fin-add-eq n O = ! (Coprod-comm (Fin n) (Fin O) ∙ ap (λ A → A ⊔ Fin n) Fin-O-eq ∙ Coprod-empty-eq (Fin n))
Fin-add-eq n (S m) =
  Fin (n +' S m)      =⟨ Fin-S-eq (n +' m) ⟩ 
  Fin (n +' m) ⊔ ⊤    =⟨ ap (λ A → A ⊔ ⊤) (Fin-add-eq n m) ⟩
  (Fin n ⊔ Fin m) ⊔ ⊤ =⟨ ! (Coprod-assoc (Fin n) (Fin m) ⊤) ⟩
  Fin n ⊔ (Fin m ⊔ ⊤) =⟨ ap (λ A → Fin n ⊔ A) (! (Fin-S-eq m)) ⟩
  Fin n ⊔ Fin (S m)   ∎
  
fin-add : (n m : ℕ) → BAut (Fin m) → BAut (Fin (n +' m))
fin-add n m (Y , tq) = Fin n ⊔ Y , Trunc-rec Trunc-level (λ q → [ Fin-add-eq n m ∙ ap (λ A → Fin n ⊔ A) q ]) tq

is-prop-not : (A : Type₀) → is-prop (¬ A)
is-prop-not A = all-paths-is-prop λ f g → λ= λ a → ⊥-rec (f a)

has-all-paths-Dec : (A : Type₀) → is-prop A → has-all-paths (Dec A)
has-all-paths-Dec A d (inl p)  (inl q)  = ap inl (prop-has-all-paths d p q)
has-all-paths-Dec A d (inl p)  (inr ¬q) = ⊥-rec (¬q p)
has-all-paths-Dec A d (inr ¬p) (inl q)  = ⊥-rec (¬p q)
has-all-paths-Dec A d (inr ¬p) (inr ¬q) = ap inr (prop-has-all-paths (is-prop-not A) ¬p ¬q)

is-prop-has-dec-eq : (A : Set) → is-prop (has-dec-eq A)
is-prop-has-dec-eq A = all-paths-is-prop λ h k → λ= λ a → λ= λ b →
  has-all-paths-Dec (a == b) (dec-eq-is-set k a b) (h a b) (k a b)

has-dec-eq-Coprod : (A B : Set) → has-dec-eq A → has-dec-eq B → has-dec-eq (A ⊔ B)
has-dec-eq-Coprod A B dA dB (inl a₁) (inl a₂) with dA a₁ a₂
has-dec-eq-Coprod A B dA dB (inl a₁) (inl a₂) | inl p = inl (ap inl p)
has-dec-eq-Coprod A B dA dB (inl a₁) (inl a₂) | inr ¬p = inr λ { idp → ¬p idp }
has-dec-eq-Coprod A B dA dB (inl a)  (inr b)  = inr λ { () }
has-dec-eq-Coprod A B dA dB (inr b)  (inl a)  = inr λ { () }
has-dec-eq-Coprod A B dA dB (inr b₁) (inr b₂) with dB b₁ b₂
has-dec-eq-Coprod A B dA dB (inr b₁) (inr b₂) | inl p = inl (ap inr p)
has-dec-eq-Coprod A B dA dB (inr b₁) (inr b₂) | inr ¬p = inr λ { idp → ¬p idp }
