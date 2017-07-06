{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Prelude

module Lambda where

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
