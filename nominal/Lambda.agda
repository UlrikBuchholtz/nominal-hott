{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Prelude

module Lambda where

module LambdaGeneric {ℓ} {I : Set ℓ} (S : I → I)
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

-- simply typed lambda-calculus
-- parametrized by index type

module MΛ {u} {I : Type u} (S : I → I) (A : I → Type₀)
  (lawA : {i : I} → A (S i) ≃ ⊤ ⊔ A i)
  (_A≟_ : {i : I} → has-dec-eq (A i)) where

  newA : {i : I} → A (S i)
  newA = <– lawA (inl unit)

  wkA : {i : I} → A i → A (S i)
  wkA x = <– lawA (inr x)
  
  data Λ : I → Type u where
    var : {i : I} → A i → Λ i
    app : {i : I} → Λ i → Λ i → Λ i
    lam : {i : I} → Λ (S i) → Λ i
  open Λ public

  sub : (i : I) → Λ (S i) → Λ i → Λ i
  sub i (var x) t = {!!}
  sub i (app s s') t = app (sub i s t) (sub i s' t)
  sub i (lam s) t = lam (sub (S i) s {!!})
  
  absA : {i : I} → A i → A i → A (S i)
  absA a b with a A≟ b
  absA a b | inl _ = newA
  absA a b | inr _ = wkA b

  appA : {i : I} → A (S i) → A i → A i
  appA a b with –> lawA a
  appA a b | inl _ = b
  appA a b | inr x = x

  drop-new : {i : I} → List (A (S i)) → List (A i)
  drop-new nil = nil
  drop-new (x :: xs) with –> lawA x
  drop-new (x :: xs) | inl _ = drop-new xs
  drop-new (x :: xs) | inr y = y :: drop-new xs
  
  fv : {i : I} → Λ i → List (A i)
  fv (var x) = x :: nil
  fv (app s t) = fv s ++ fv t
  fv (lam s) = drop-new (fv s)
  
--  appA-absA : {i : I} → (a b : A i) → appA (absA a b) a == b
--  appA-absA a b with a A≟ b
--  appA-absA a b | inl p = {!!}
--  appA-absA a b | inr ¬p = {!!}
  
  absΛ : {i : I} → A i → Λ i → Λ (S i)
  absΛ a (var b) = var (absA a b) 
  absΛ a (app s t) = app (absΛ a s) (absΛ a t)
  absΛ a (lam s) = lam (absΛ (wkA a) s)

  appΛ : {i : I} → Λ (S i) → A i → Λ i
  appΛ (var x) a = var (appA x a)
  appΛ (app s t) a = app (appΛ s a) (appΛ t a)
  appΛ (lam s) a = lam (appΛ s (wkA a))

--module FΛ {u₁ u₂} {I₁ : Type u₁} {I₂ : Type u₂}
--  (S₁ : I₁ → I₁) (A₁ : I₁ → Type₀)
--  (S₂ : I₂ → I₂) (A₂ : I₂ → Type₀)
--  (f : I₁ → I₂) (FA : {i : I₁} → A₁ i → A₂ (f i))
--  (fcoh : {i : I₁} → f (S₁ i) == S₂ (f i)) where
--
--  open MΛ S₁ A₁ renaming (Λ to Λ₁; var to var₁; app to app₁; lam to lam₁)
--  
--  open MΛ S₂ A₂ renaming (Λ to Λ₂; var to var₂; app to app₂; lam to lam₂)
--
--  F : {i : I₁} → Λ₁ i → Λ₂ (f i)
--  F (var₁ x) = var₂ (FA x)
--  F (app₁ s t) = app₂ (F s) (F t)
--  F (lam₁ s) = lam₂ (transport Λ₂ fcoh (F s))
--
--
