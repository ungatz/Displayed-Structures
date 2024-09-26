{-# OPTIONS --cubical #-}
module ReflexiveGraphLenses where

open import Agda.Primitive public
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
open import Cubical.Displayed.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

𝒮-Univ : ∀ ℓ → UARel (Type ℓ) ℓ
𝒮-Univ ℓ .UARel._≅_ = _≃_
𝒮-Univ ℓ .UARel.ua _ _ = isoToEquiv (invIso univalenceIso)

 -- The type of sets.
HSet : ∀ ℓ → Type (lsuc ℓ)
HSet ℓ = Σ (Type ℓ) isSet

𝒮-Set : ∀ ℓ → UARel (HSet ℓ) (ℓ-suc ℓ)
𝒮-Set ℓ .UARel._≅_ A B = fst A ≡ fst B
𝒮-Set ℓ .UARel.ua (A , _) (B , _) = invEquiv (cong fst , isEmbeddingFstΣProp (λ X → isPropIsSet))

𝒮ᴰ-Set : ∀ ℓ → DUARel (𝒮-Univ ℓ) (λ X → isSet X) ℓ
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Set ℓ) x p y = Unit*
DUARel.uaᴰ (𝒮ᴰ-Set ℓ) x p y = invEquiv (isContr→≃Unit* (isProp→isContrPathP (λ i → isPropIsSet) x y))

∫𝓢ᴰ-Set : ∀ ℓ → UARel (HSet ℓ) ℓ
∫𝓢ᴰ-Set ℓ = ∫ (𝒮ᴰ-Set ℓ)

𝒮ᴰ-PtdTyp : ∀ ℓ → DUARel (𝒮-Univ ℓ) (λ X → X) ℓ
𝒮ᴰ-PtdTyp ℓ .DUARel._≅ᴰ⟨_⟩_ a e b = equivFun e a ≡ b
𝒮ᴰ-PtdTyp ℓ .DUARel.uaᴰ {A} {B} a e b =
  invEquiv (compEquiv (PathP≃Path _ a b) (compPathlEquiv (sym (uaβ e a))))

𝒮ᴰ-PtdSet : ∀ ℓ → DUARel (∫𝓢ᴰ-Set ℓ) (λ X → (fst X)) ℓ
𝒮ᴰ-PtdSet ℓ .DUARel._≅ᴰ⟨_⟩_ {(A , _)} {(B , _)} a (e , tt*) b = equivFun e a ≡ b
𝒮ᴰ-PtdSet ℓ .DUARel.uaᴰ a (e , tt*) b =
  invEquiv (compEquiv (PathP≃Path _ a b) (compPathlEquiv (sym (uaβ e a))))

𝒮ᴰ-const : ∀ {ℓA ℓ≅A ℓB ℓ≅B}
           {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
           {B : Type ℓB} (𝒮-B : UARel B ℓ≅B)
           → DUARel 𝒮-A (λ _ → B) ℓ≅B
𝒮ᴰ-const 𝒮-A 𝒮-B .DUARel._≅ᴰ⟨_⟩_ b p b' = 𝒮-B .UARel._≅_ b b'
𝒮ᴰ-const 𝒮-A 𝒮-B .DUARel.uaᴰ b p b' = 𝒮-B .UARel.ua b b'

𝒮ᴰ-Magma : ∀ ℓ → DUARel (∫𝓢ᴰ-Set ℓ) (λ X → (fst X) → (fst X) → (fst X)) ℓ
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Magma ℓ) {a} ∘ₐ p ∘ₓ = ∀ (x y : fst a) →
                                          fst (fst p) (∘ₐ x y) ≡
                                          ∘ₓ ((fst (fst p)) x) ((fst (fst p)) y)
DUARel.uaᴰ (𝒮ᴰ-Magma ℓ) = {!!}

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
