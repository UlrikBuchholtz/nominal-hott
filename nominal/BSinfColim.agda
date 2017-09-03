{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Prelude
open import FinSet

module BSinf where

-- here we define the untyped λ-calculus parametrized by
-- any index type I with a shift operator S,
-- and a type of atoms, A, with decidable equality
-- (this will go in a separate file / be merged with Lambda)

-- now let us instantiate this with the finitary symmetric group

BΣ∞ : Set₁
BΣ∞ = ℕColim add-unit

BΣ∞-conn : is-connected 0 BΣ∞
BΣ∞-conn = ncolim-conn add-unit (from-nat 0) λ n → BAut-conn (Fin n)

-- explicit constructors
i-exp : FinSet-exp → BΣ∞
i-exp (n , A) = ncin n A

g-exp : (A : FinSet-exp) → i-exp A == i-exp (S (fst A) , add-unit (fst A) (snd A))
g-exp (n , A) = ncglue n A

-- implicit constructors
i : FinSet → BΣ∞
i A = i-exp (<– FinSet-equiv A)

g : (A : FinSet) → i A == i (A ⊎ Unit-FinSet)
g A = g-exp (<– FinSet-equiv A) ∙ ap i-exp (<– (ap-equiv FinSet-equiv _ _) (Subtype=-out FinSet-prop idp))

BΣ∞-elim : ∀ {ℓ} {P : BΣ∞ → Type ℓ} (Pi : (A : FinSet) → P (i A))
           (Pg : (A : FinSet) → Pi A == Pi (A ⊎ Unit-FinSet) [ P ↓ g A ])
           (X : BΣ∞) → P X
BΣ∞-elim {ℓ} {P} Pi Pg X = ℕColimElim.f add-unit {P = P}
  (λ n A → transport (P ∘ i-exp) (<–-inv-l FinSet-equiv ((n , A))) (Pi (–> FinSet-equiv (n , A))))
  (λ n A → {!!}) X

BΣ∞-rec : ∀ {ℓ} {P : Type ℓ} (Pi : FinSet → P) (Pg : (A : FinSet) → Pi A == Pi (A ⊎ Unit-FinSet))
          → BΣ∞ → P
BΣ∞-rec Pi Pg X = BΣ∞-elim Pi (λ A → ↓-cst-in (Pg A)) X

{-
add-unit-add : {n : ℕ} → (X : BAut (Fin n)) → add-unit (S n) (unit-add n X) == unit-add (S n) (add-unit n X)
add-unit-add (X , tp) = pair= (! (Coprod-assoc ⊤ X ⊤)) (from-transp _ _ (prop-has-all-paths Trunc-level _ _))

shift : BΣ∞ → BΣ∞
shift = ℕColimRec.f add-unit (λ n X → i (unit-add n X)) lemma
  where
    lemma : (n : ℕ) → (X : BAut (Fin n)) → i (unit-add n X) == i (unit-add (S n) (add-unit n X))
    lemma n X = g (unit-add n X) ∙ ap i (add-unit-add X)

add-unit-fin : (n : ℕ) → {m : ℕ} → (X : BAut (Fin m))
               → add-unit (n +' m) (fin-add n m X) == fin-add n (S m) (add-unit m X)
add-unit-fin n {m} (X , tp) = pair= (! (Coprod-assoc (Fin n) X ⊤))
                                    ((from-transp _ _ (prop-has-all-paths Trunc-level _ _)))

fin-shift : ℕ → BΣ∞ → BΣ∞
fin-shift n = ℕColimRec.f add-unit (λ m X → i (fin-add n m X)) lemma
  where
    lemma : (m : ℕ) → (X : BAut (Fin m)) → i (fin-add n m X) == i (fin-add n (S m) (add-unit m X))
    lemma m X = g (fin-add n m X) ∙ ap i (add-unit-fin n X)

fin-shift' : ℕ → BΣ∞ → BΣ∞
fin-shift' O X = X
fin-shift' (S n) X = shift (fin-shift' n X)

Atom : BΣ∞ → Type₀
Atom = ℕColimRec.f add-unit (λ n X → fst X ⊔ ℕ) lemma
  where
    lemma : (n : ℕ) → (X : BAut (Fin n)) → fst X ⊔ ℕ == fst (add-unit n X) ⊔ ℕ
    lemma n (X , tp) = ap (λ A → X ⊔ A) ℕ-eq-⊤-⊔-ℕ ∙ Coprod-assoc X ⊤ ℕ

has-dec-eq-prop : (x : BΣ∞) → hProp lzero
fst (has-dec-eq-prop x) = has-dec-eq (Atom x)
snd (has-dec-eq-prop x) = is-prop-has-dec-eq (Atom x)

Atom-has-dec-eq : {x : BΣ∞} → has-dec-eq (Atom x)
Atom-has-dec-eq {x} = prop-over-connected {lone} {lzero} {BΣ∞} {i ( Fin O , [ idp ] )}
           BΣ∞-conn has-dec-eq-prop (has-dec-eq-Coprod (Fin O) ℕ (_F≟_ {O}) ℕ-has-dec-eq) x

swap : {X : BΣ∞} → (a b : Atom X) → X == X
swap {X} = ℕColim-elim add-unit (λ n A → {!!}) {!!} X

-- better interface using i : FinSet → BΣ∞, g : (A : FinSet) → i A == i (A ⊔ ⊤)?
-- hiding all numbers in prop.trunc.?
-- i A == i (Fin O ⊔ A) is just ap i (ua ...) instead of something uglier

--fs : ∀ {u} {X : BΣ∞ → hSet u} {B : BΣ∞} (x : fst (X B)) → hProp u
--fst (fs x) = Trunc (from-neg 1) (Σ ℕ λ n → {!!})
--snd (fs x) = Trunc-level

-- module ΛNom = Lambda {lsucc lzero} {BΣ∞} shift atoms _A≟_
-}
