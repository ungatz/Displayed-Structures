{-# OPTIONS --cubical #-}
module ReflexiveGraphLenses where

import Agda.Builtin.Cubical.Path as Path
import Cubical.Foundations.Prelude as Prelude
open Path using (PathP) public
open Prelude using (_≡_ ; refl ; cong ; funExt; transport ; subst ; J; isSet) public
open import Agda.Primitive renaming (Set to Type; Setω to Typeω; Level to Universe)  public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Unit renaming (⊤ to Unit) public
open import Agda.Builtin.Nat renaming (Nat to ℕ) public
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Binary
open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst

private
 variable
  𝓤 𝓥 𝓦 ℓ ℓ' 𝓤' 𝓥' : Universe

Π : (A : Type 𝓤) (B : A → Type 𝓥) → Type (𝓤 ⊔ 𝓥)
Π A B = (x : A) → B x

_×_ : (A : Type 𝓤) (B : Type 𝓥) → Type (𝓤 ⊔ 𝓥)
A × B = Σ A (λ x → B)

infixr 10 _×_

idn-fun : (A : Type 𝓤) → A → A
idn-fun A a = a

_∘_
 : {A : Type 𝓤} {B : A → Type 𝓥} {C : {x : A} → B x → Type 𝓦}
 → (g : {x : A} (y : B x) → C y)
 → (f : (x : A) → B x)
 → (x : A) → C (f x)
(g ∘ f) x = g (f x)

infixl 10 _∘_

open import Cubical.Foundations.Prelude
-- We cannot define this using Jon's definition of reflexive graphs
𝒮-Univ : ∀ ℓ → UARel (Type ℓ) ℓ
𝒮-Univ ℓ .UARel._≅_ = _≃_
𝒮-Univ ℓ .UARel.ua _ _ = isoToEquiv (invIso univalenceIso)

 -- The type of sets.
HSet : ∀ ℓ → Type (lsuc ℓ)
HSet ℓ = Σ (Type ℓ) isSet

𝒮-Set : ∀ ℓ → UARel (Σ (Type ℓ) isSet) (ℓ-suc ℓ)
(𝒮-Set ℓ UARel.≅ A) B = fst A ≡ fst B
fst (UARel.ua (𝒮-Set ℓ) Ha Hb) x = {!!}
snd (UARel.ua (𝒮-Set ℓ) Ha Hb) = {!!}

𝒮ᴰ-Set : ∀ ℓ → DUARel (𝒮-Univ ℓ) (λ X → isSet X) ℓ
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Set ℓ) x p y = PathP (λ i → isSet (UARel.≅→≡ (𝒮-Univ ℓ) p i)) x y
DUARel.uaᴰ (𝒮ᴰ-Set ℓ) b p b' = isProp→PathP (λ i → {!(isPropIsSet' (UARel.≅→≡ (𝒮-Univ ℓ) p i))!}) b b' {!i!}
  where
    isPropIsSet' : ∀ {ℓ} (A : Type ℓ) → isProp (isSet A)
    isPropIsSet' A = isPropΠ2 λ x y → isPropIsProp

∫𝓢ᴰ-Set : ∀ ℓ → UARel (Σ (Type ℓ) isSet) ℓ
∫𝓢ᴰ-Set ℓ = ∫ (𝒮ᴰ-Set ℓ)

𝒮ᴰ-PtdSet : ∀ ℓ → DUARel (∫𝓢ᴰ-Set ℓ) (λ X → (fst X)) ℓ
(𝒮ᴰ-PtdSet ℓ DUARel.≅ᴰ⟨ x ⟩ p) y = (fst (fst p)) x ≡ y
DUARel.uaᴰ (𝒮ᴰ-PtdSet ℓ) = {!!}

𝒮ᴰ-PtdTyp : ∀ ℓ → DUARel (𝒮-Univ ℓ) (λ X → X) ℓ
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-PtdTyp ℓ) x e y = (fst e) x ≡ y
DUARel.uaᴰ (𝒮ᴰ-PtdTyp ℓ) b p b' = {!!}

𝒮ᴰ-Magma : ∀ ℓ → DUARel (∫𝓢ᴰ-Set ℓ) (λ X → (fst X) → (fst X) → (fst X)) ℓ
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Magma ℓ) {a} ∘ₐ p ∘ₓ = ∀ (x y : fst a) → fst (fst p) (∘ₐ x y) ≡ ∘ₓ ((fst (fst p)) x) ((fst (fst p)) y)
DUARel.uaᴰ (𝒮ᴰ-Magma ℓ) = {!!}


-- 𝒮-PtdSet : ∀ ℓ → DUARel (𝒮-Set ℓ) (λ X → fst X) (ℓ-suc ℓ)
-- (𝒮-PtdSet ℓ DUARel.≅ᴰ⟨ A ⟩ A≃B) B = transport {!A≃B!} {!!}
-- DUARel.uaᴰ (𝒮-PtdSet ℓ) = {!!}

-- 𝒮ᴰ-Set : ∀ ℓ → DUARel (𝒮-Univ ℓ) (λ X → HSet ℓ) ℓ
-- DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Set ℓ) x e y = Σ (fst x ≃ fst y)
--                                     (λ f → PathP (λ i → isSet (UARel.≅→≡ (𝒮-Univ ℓ) e i))
--                                                 (transport (λ i → isSet {!(UARel.≅→≡ (𝒮-Univ ℓ) e i)!}) (snd x)) {!!})
-- fst (DUARel.uaᴰ (𝒮ᴰ-Set ℓ) b p b') = {!!}
-- snd (DUARel.uaᴰ (𝒮ᴰ-Set ℓ) b p b') = {!!}
