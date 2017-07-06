{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Prelude

module BSinf where

-- here we define the untyped λ-calculus parametrized by
-- any index type I with a shift operator S,
-- and a type of atoms, A, with decidable equality
-- (this will go in a separate file / be merged with Lambda)

module Lambda {ℓ} {I : Set ℓ} (S : I → I)
  (A : I → Set lzero) (_A≟_ : {i : I} → has-dec-eq (A i)) where

  data Λ : I → Set ℓ where
    var : {i : I} → A i → Λ i
    app : {i : I} → Λ i → Λ i → Λ i
    lam : {i : I} → Λ (S i) → Λ i

  Λ-var-is-inj : {i : I} → {x y : A i} → var x == var y → x == y
  Λ-var-is-inj idp = idp

  Λ-app-is-inj₁ : {i : I} → {s₁ s₂ t₁ t₂ : Λ i} → app s₁ s₂ == app t₁ t₂ → s₁ == t₁
  Λ-app-is-inj₁ idp = idp

  Λ-app-is-inj₂ : {i : I} → {s₁ s₂ t₁ t₂ : Λ i} → app s₁ s₂ == app t₁ t₂ → s₂ == t₂
  Λ-app-is-inj₂ idp = idp

  Λ-lam-is-inj : {i : I} → {s t : Λ (S i)} → lam s == lam t → s == t
  Λ-lam-is-inj idp = idp

  Λ-var-is-not-app : {i : I} → {x : A i} → {s t : Λ i}
                     → var x == app s t → ⊥
  Λ-var-is-not-app ()

  Λ-var-is-not-lam : {i : I} → {x : A i} → {s : Λ (S i)}
                     → var x == lam s → ⊥
  Λ-var-is-not-lam ()

  Λ-app-is-not-lam : {i : I} → {s t : Λ i} → {u : Λ (S i)}
                     → app s t == lam u → ⊥
  Λ-app-is-not-lam ()

  _≟_ : {i : I} → has-dec-eq (Λ i)
  var x ≟ var y with x A≟ y
  var x ≟ var y | inl p = inl (ap var p)
  var x ≟ var y | inr ¬p = inr λ q → ¬p (Λ-var-is-inj q)
  var x ≟ app t₁ t₂ = inr Λ-var-is-not-app
  var x ≟ lam t = inr Λ-var-is-not-lam
  app s₁ s₂ ≟ var y = inr λ q → Λ-var-is-not-app (! q)
  app s₁ s₂ ≟ app t₁ t₂ with s₁ ≟ t₁
  app s₁ s₂ ≟ app t₁ t₂ | inl p with s₂ ≟ t₂
  app s₁ s₂ ≟ app t₁ t₂ | inl p | inl q = inl (ap2 app p q)
  app s₁ s₂ ≟ app t₁ t₂ | inl p | inr ¬q = inr λ r → ¬q (Λ-app-is-inj₂ r)
  app s₁ s₂ ≟ app t₁ t₂ | inr ¬p = inr λ q → ¬p (Λ-app-is-inj₁ q)
  app s₁ s₂ ≟ lam t = inr Λ-app-is-not-lam
  lam s ≟ var y = inr λ q → Λ-var-is-not-lam (! q)
  lam s ≟ app t₁ t₂ = inr λ q → Λ-app-is-not-lam (! q)
  lam s ≟ lam t with s ≟ t
  lam s ≟ lam t | inl p = inl (ap lam p)
  lam s ≟ lam t | inr ¬p = inr λ q → ¬p (Λ-lam-is-inj q)

-- now let us instantiate this with the de Bruijn indices

module ΛdB = Lambda S Fin _F≟_

-- now let us instantiate this with the finitary symmetric group

BΣ∞ : Set₁
BΣ∞ = ℕColim add-unit

BΣ∞-conn : is-connected 0 BΣ∞
BΣ∞-conn = ncolim-conn add-unit (from-nat 0) λ n → BAut-conn (Fin n)

i : {n : ℕ} → BAut (Fin n) → BΣ∞
i {n} X = ncin n X

g : {n : ℕ} → (X : BAut (Fin n)) → i X == i (add-unit n X)
g {n} X = ncglue n X

add-unit-add : {n : ℕ} → (X : BAut (Fin n)) → add-unit (S n) (unit-add n X) == unit-add (S n) (add-unit n X)
add-unit-add (X , tp) = pair= (! (Coprod-assoc ⊤ X ⊤)) (from-transp _ _ (prop-has-all-paths Trunc-level _ _))

shift : BΣ∞ → BΣ∞
shift = ℕColimRec.f add-unit (λ n X → i (unit-add n X)) lemma
  where
    lemma : (n : ℕ) → (X : BAut (Fin n)) → i (unit-add n X) == i (unit-add (S n) (add-unit n X))
    lemma n X = g (unit-add n X) ∙ ap i (add-unit-add X)
    
atoms : BΣ∞ → Type₀
atoms = ℕColimRec.f add-unit (λ n X → fst X ⊔ ℕ) lemma
  where
    lemma : (n : ℕ) → (X : BAut (Fin n)) → fst X ⊔ ℕ == fst (add-unit n X) ⊔ ℕ
    lemma n (X , tp) = ap (λ A → X ⊔ A) ℕ-eq-⊤-⊔-ℕ ∙ Coprod-assoc X ⊤ ℕ

has-dec-eq-prop : (x : BΣ∞) → hProp lzero
fst (has-dec-eq-prop x) = has-dec-eq (atoms x)
snd (has-dec-eq-prop x) = is-prop-has-dec-eq (atoms x)

_A≟_ : {x : BΣ∞} → has-dec-eq (atoms x)
_A≟_ {x} = prop-over-connected {lsucc lzero} {lzero} {BΣ∞} {i ( Fin O , [ idp ] )}
           BΣ∞-conn has-dec-eq-prop (has-dec-eq-Coprod (Fin O) ℕ (_F≟_ {O}) ℕ-has-dec-eq) x

--fs : ∀ {u} {X : BΣ∞ → hSet u} {B : BΣ∞} (x : fst (X B)) → hProp u
--fst (fs x) = Trunc (from-neg 1) (Σ ℕ λ n → {!!})
--snd (fs x) = Trunc-level

-- module ΛNom = Lambda {lsucc lzero} {BΣ∞} shift atoms _A≟_
