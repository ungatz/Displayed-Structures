{-# OPTIONS --cubical #-}
module ReflexiveGraphLenses where

import Agda.Builtin.Cubical.Path as Path
import Cubical.Foundations.Prelude as Prelude
open Path using (PathP) public
open Prelude using (_≡_ ; refl ; cong ; funExt; transport ; subst ; J; isSet) public
open import Agda.Primitive renaming (Set to Type; Setω to Typeω; Level to Universe)  public
-- open import Agda.Builtin.Sigma public
open import Agda.Builtin.Unit renaming (⊤ to Unit) public
open import Agda.Builtin.Nat renaming (Nat to ℕ) public
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Binary
open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

private
 variable
  𝓤 𝓥 𝓦 ℓ ℓ' 𝓤' 𝓥' : Universe

Π : (A : Type 𝓤) (B : A → Type 𝓥) → Type (𝓤 ⊔ 𝓥)
Π A B = (x : A) → B x

-- _×_ : (A : Type 𝓤) (B : Type 𝓥) → Type (𝓤 ⊔ 𝓥)
-- A × B = Σ A (λ x → B)

-- infixr 10 _×_

idn-fun : (A : Type 𝓤) → A → A
idn-fun A a = a

_∘_
 : {A : Type 𝓤} {B : A → Type 𝓥} {C : {x : A} → B x → Type 𝓦}
 → (g : {x : A} (y : B x) → C y)
 → (f : (x : A) → B x)
 → (x : A) → C (f x)
(g ∘ f) x = g (f x)

infixl 10 _∘_

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
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Set ℓ) x p y = Unit*
-- PathP (λ i → isSet (UARel.≅→≡ (𝒮-Univ ℓ) p i)) x y
DUARel.uaᴰ (𝒮ᴰ-Set ℓ) x p y = invEquiv (isContr→≃Unit* (isProp→isContrPathP (λ i → isPropIsSet) x y))
-- idEquiv (PathP (λ i → isSet (UARel.≅→≡ (𝒮-Univ ℓ) p i)) x y)

∫𝓢ᴰ-Set : ∀ ℓ → UARel (Σ (Type ℓ) isSet) ℓ
∫𝓢ᴰ-Set ℓ = ∫ (𝒮ᴰ-Set ℓ)

𝒮ᴰ-PtdSet : ∀ ℓ → DUARel (∫𝓢ᴰ-Set ℓ) (λ X → (fst X)) ℓ
(𝒮ᴰ-PtdSet ℓ DUARel.≅ᴰ⟨ x ⟩ p) y = (fst (fst p)) x ≡ y
DUARel.uaᴰ (𝒮ᴰ-PtdSet ℓ) {(X , _)} {(Y , _)} x (e , tt*) y = {!UARel.≅→≡ (∫𝓢ᴰ-Set ℓ) (e , tt*)!}
  -- where
  --   pPath = UARel.∫𝓢ᴰ-Set (≅→≡ ℓ) p

  --   to : fst (fst p) x ≡ y → PathP (λ i → fst (UARel.≅→≡ (∫𝓢ᴰ-Set ℓ) p i)) x y
  --   to q i = subst (λ X → fst X ) (λ j → pPath {!!}) (q i)

  --   from : PathP (λ i → fst (UARel.≅→≡ (∫𝓢ᴰ-Set ℓ) p i)) x y → fst (fst p) x ≡ y
  --   from q i = subst (λ X → fst X) (λ j → pPath {!!}) (q i)

  --   sect : section to from
  --   sect q = λ i j → subst (λ X → fst X) (λ k → pPath {!!}) (q j)

  --   retr : retract to from
  --   retr q = λ i j → subst (λ X → fst X) (λ k → pPath {!!}) (q j)

𝒮ᴰ-PtdTyp : ∀ ℓ → DUARel (𝒮-Univ ℓ) (λ X → X) ℓ
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-PtdTyp ℓ) x e y = (fst e) x ≡ y
DUARel.uaᴰ (𝒮ᴰ-PtdTyp ℓ) b p b' = compEquiv {!!} {!ΣPath≅PathΣ!}

𝒮ᴰ-Magma : ∀ ℓ → DUARel (∫𝓢ᴰ-Set ℓ) (λ X → (fst X) → (fst X) → (fst X)) ℓ
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Magma ℓ) {a} ∘ₐ p ∘ₓ = ∀ (x y : fst a) →
                                          fst (fst p) (∘ₐ x y) ≡
                                          ∘ₓ ((fst (fst p)) x) ((fst (fst p)) y)
DUARel.uaᴰ (𝒮ᴰ-Magma ℓ) = {!!}

𝒮ᴰ-const : ∀ {ℓA ℓ≅A ℓB ℓ≅B}
           {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
           {B : Type ℓB} (𝒮-B : UARel B ℓ≅B)
           → DUARel 𝒮-A (λ _ → B) ℓ≅B
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-const 𝒮-A 𝒮-B) = (λ b _ b' → (𝒮-B UARel.≅ b) b')
DUARel.uaᴰ (𝒮ᴰ-const {A} 𝒮-A {B} 𝒮-B) b p b' = compEquiv (UARel.ua 𝒮-B b b') {!!}

_×𝒮_ : ∀ {ℓA ℓ≅A ℓB ℓ≅B}
       {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
       {B : Type ℓB} (𝒮-B : UARel B ℓ≅B)
       → UARel (A × B) (ℓ-max ℓ≅A ℓ≅B)
𝒮-A ×𝒮 𝒮-B = ∫ (𝒮ᴰ-const 𝒮-A 𝒮-B)

_×ᴰ_ : ∀ {ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C}
       {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
       {B : A → Type ℓB} {C : A → Type ℓC}
       (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
       (𝒮ᴰ-C : DUARel 𝒮-A C ℓ≅C)
       → DUARel 𝒮-A (λ a → B a × C a) (ℓ-max ℓ≅B ℓ≅C)
(𝒮ᴰ-B ×ᴰ 𝒮ᴰ-C) .DUARel._≅ᴰ⟨_⟩_ (b , c) e (b' , c') =
  (𝒮ᴰ-B .DUARel._≅ᴰ⟨_⟩_ b e b') × (𝒮ᴰ-C .DUARel._≅ᴰ⟨_⟩_ c e c')
(𝒮ᴰ-B ×ᴰ 𝒮ᴰ-C) .DUARel.uaᴰ (b , c) e (b' , c') = {!!}

∫𝓢ᴰ-PtdSet : ∀ ℓ → UARel (Σ (Σ (Type ℓ) isSet) (λ X → fst X)) ℓ
∫𝓢ᴰ-PtdSet ℓ = ∫ (𝒮ᴰ-PtdSet ℓ)

∫𝓢ᴰ-Magma : ∀ ℓ → UARel (Σ (Σ (Type ℓ) isSet) (λ X → fst X → fst X → fst X)) ℓ
∫𝓢ᴰ-Magma ℓ = ∫ (𝒮ᴰ-Magma ℓ)

∫𝓢ᴰ-PtdSetMagma : ∀ ℓ → UARel (Σ (Σ (Type ℓ) isSet) (λ X → fst X × (fst X → fst X → fst X))) ℓ
∫𝓢ᴰ-PtdSetMagma ℓ = ∫ ((𝒮ᴰ-PtdSet ℓ) ×ᴰ (𝒮ᴰ-Magma ℓ))

𝒮ᴰ-Monoid' : ∀ ℓ → DUARel (∫𝓢ᴰ-PtdSetMagma ℓ)
             (λ X → (∀ x → (snd (snd X) x (fst (snd X)) ≡ x) ×
                           (snd (snd X) (fst (snd X)) x ≡ x)) ×
                           (∀ x y z → snd (snd X) (snd (snd X) x y) z ≡ snd (snd X) x (snd (snd X) y z))) ℓ
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Monoid' ℓ) {X} {Y} m e n =
  let
    eₓ = fst e
    e₊ = fst (snd e)
    e∙ = snd (snd e)
    in
      (∀ x → PathP (λ i → {!e∙ ? ?!}) {!!} {!!}) ×
      (∀ x → PathP (λ i → {!!}) {!!} {!!}) ×
      (∀ x y z → PathP (λ i → {!!}) {!!} {!!})
DUARel.uaᴰ (𝒮ᴰ-Monoid' ℓ) = {!!}

𝒮ᴰ-Monoid : ∀ ℓ → DUARel (∫𝓢ᴰ-Set ℓ)
  (λ X → Σ[ ptd ∈ (λ Y → fst Y) X ]
         Σ[ op ∈ (λ Y → (fst Y) → (fst Y) → (fst Y)) X ]
         (∀ x → (op x ptd ≡ x) × (op ptd x ≡ x)) ×
         (∀ x y z → op (op x y) z ≡ op x (op y z))) ℓ
(𝒮ᴰ-Monoid ℓ DUARel.≅ᴰ⟨ x ⟩ x₁) x₂ = {!!}
DUARel.uaᴰ (𝒮ᴰ-Monoid ℓ) = {!!}


-- 𝒮-PtdSet : ∀ ℓ → DUARel (𝒮-Set ℓ) (λ X → fst X) (ℓ-suc ℓ)
-- (𝒮-PtdSet ℓ DUARel.≅ᴰ⟨ A ⟩ A≃B) B = transport {!A≃B!} {!!}
-- DUARel.uaᴰ (𝒮-PtdSet ℓ) = {!!}

-- 𝒮ᴰ-Set : ∀ ℓ → DUARel (𝒮-Univ ℓ) (λ X → HSet ℓ) ℓ
-- DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Set ℓ) x e y = Σ (fst x ≃ fst y)
--                                     (λ f → PathP (λ i → isSet (UARel.≅→≡ (𝒮-Univ ℓ) e i))
--                                                 (transport (λ i → isSet {!(UARel.≅→≡ (𝒮-Univ ℓ) e i)!}) (snd x)) {!!})
-- fst (DUARel.uaᴰ (𝒮ᴰ-Set ℓ) b p b') = {!!}
-- snd (DUARel.uaᴰ (𝒮ᴰ-Set ℓ) b p b') = {!!}
