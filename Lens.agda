{-# OPTIONS --cubical #-}
module Lens where

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

private
  variable
    𝓤 𝓥 𝓦 : Level
    A : Type 𝓤

-- Lens A R B is inhabited then, a type A can
-- be split into a remainder r : R and a value
-- b : B r

Lens : Type 𝓤 → (R : Type 𝓥) → (R → Type 𝓦) → Type _
Lens A R B = A ≃ Σ R B

module Lens {R : Type 𝓥} {B : R → Type 𝓦} (lens : Lens A R B) where

  remainder : A → R
  remainder a = fst ((equivFun lens) a)

  getter : (a : A) → B (remainder a)
  getter a = snd ((equivFun lens) a)

  setter : (a : A) → B (remainder a) → A
  setter a b = (equivFun (invEquiv lens)) (remainder a , b)

  modify : (a : A) → (B (remainder a) → B (remainder a)) → A
  modify a f = setter a (f (getter a))
