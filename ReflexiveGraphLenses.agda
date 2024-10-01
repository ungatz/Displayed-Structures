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
open import Cubical.Foundations.Transport
open import Cubical.Relation.Binary
open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst
open import Cubical.Displayed.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv

-- URG on Type
𝒮-Univ : ∀ ℓ → UARel (Type ℓ) ℓ
𝒮-Univ ℓ .UARel._≅_ = _≃_
𝒮-Univ ℓ .UARel.ua _ _ = invEquiv univalence

-- URG on hSet
𝒮-Set : ∀ ℓ → UARel (hSet ℓ) ℓ
𝒮-Set ℓ .UARel._≅_ (A , _) (B , _) = A ≃ B
𝒮-Set ℓ .UARel.ua (A , _) (B , _) =
  A ≃ B ≃⟨ invEquiv univalence ⟩
  A ≡ B ≃⟨ Σ≡PropEquiv (λ _ → isPropIsSet) ⟩
  (A , _) ≡ (B , _) ■

-- another way of defining the URG on hSet
𝒮ᴰ-Set : ∀ ℓ → DUARel (𝒮-Univ ℓ) isSet ℓ
DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-Set ℓ) x p y = Unit*
DUARel.uaᴰ (𝒮ᴰ-Set ℓ) x p y = invEquiv (isContr→≃Unit* (isProp→isContrPathP (λ i → isPropIsSet) x y))

∫𝓢ᴰ-Set : ∀ ℓ → UARel (hSet ℓ) ℓ
∫𝓢ᴰ-Set ℓ = ∫ (𝒮ᴰ-Set ℓ)

-- URG on pointed types
𝒮ᴰ-PtdTyp : ∀ ℓ → DUARel (𝒮-Univ ℓ) (λ X → X) ℓ
𝒮ᴰ-PtdTyp ℓ .DUARel._≅ᴰ⟨_⟩_ a e b = equivFun e a ≡ b
𝒮ᴰ-PtdTyp ℓ .DUARel.uaᴰ {A} {B} a e b =
  invEquiv (compEquiv (PathP≃Path _ a b) (compPathlEquiv (sym (uaβ e a))))

-- URG on pointed hSets
𝒮ᴰ-PtdSet : ∀ ℓ → DUARel (𝒮-Set ℓ) (λ (X , _) → X) ℓ
𝒮ᴰ-PtdSet ℓ .DUARel._≅ᴰ⟨_⟩_ {(A , _)} {(B , _)} a e b = equivFun e a ≡ b
𝒮ᴰ-PtdSet ℓ .DUARel.uaᴰ a e b =
  invEquiv (compEquiv (PathP≃Path _ a b) (compPathlEquiv (sym (uaβ e a))))

∫𝓢ᴰ-PtdSet : ∀ ℓ → UARel (Σ (hSet ℓ) (λ (X , _) → X)) ℓ
∫𝓢ᴰ-PtdSet ℓ = ∫ (𝒮ᴰ-PtdSet ℓ)

-- URG on magmas
𝒮ᴰ-Magma : ∀ ℓ → DUARel (𝒮-Set ℓ) (λ (X , _) → X → X → X) ℓ
𝒮ᴰ-Magma ℓ .DUARel._≅ᴰ⟨_⟩_ {(A , _)} {(B , _)} ∘A (e , _) ∘B =
  ∀ (x y : A) → e (∘A x y) ≡ ∘B (e x) (e y)
𝒮ᴰ-Magma ℓ .DUARel.uaᴰ {(A , _)} {(B , _)} ∘A e ∘B =
  invEquiv (compEquiv (PathP≃Path _ ∘A ∘B)
                      (compEquiv (invEquiv funExt₂Equiv)
                                 (equivΠ (invEquiv e)
                                         (λ b → equivΠ (invEquiv e)
                                                (λ b' → compEquiv (PathP≃Path _ _ _)
                                                                  (compEquiv (compPathlEquiv (sym (transportRefl _)))
                                                                             (compEquiv (compPathlEquiv (sym (transportRefl _)))
                                                                                        (lem b b'))))))))
  where
  f : A → B
  f = e .fst
  g : B → A
  g = invEquiv e .fst
  cancel : (b : B) → f (g b) ≡ b
  cancel b = equivToIso e .Iso.rightInv b
  lem : (b b' : B) → (f (∘A (g (transport (λ _ → B) b)) (g (transport (λ _ → B) b'))) ≡ ∘B b b') ≃ (f (∘A (g b) (g b')) ≡ ∘B (f (g b)) (f (g b')))
  lem b b' =
    (f (∘A (g (transport (λ _ → B) b)) (g (transport (λ _ → B) b'))) ≡ ∘B b b') ≃⟨ compPathlEquiv (sym λ i → f (∘A (g (transportRefl b i)) (g (transportRefl b' i)))) ⟩
    (f (∘A (g b) (g b')) ≡ ∘B b b') ≃⟨ compPathrEquiv (sym λ i → ∘B (cancel b i) (cancel b' i)) ⟩
    (f (∘A (g b) (g b')) ≡ ∘B (f (g b)) (f (g b'))) ■

∫𝓢ᴰ-Magma : ∀ ℓ → UARel (Σ (hSet ℓ) (λ (X , _) → X → X → X)) ℓ
∫𝓢ᴰ-Magma ℓ = ∫ (𝒮ᴰ-Magma ℓ)

∫𝓢ᴰ-PtdSetMagma : ∀ ℓ → UARel (Σ (hSet ℓ) (λ (X , _) → X × (X → X → X))) ℓ
∫𝓢ᴰ-PtdSetMagma ℓ = ∫ ((𝒮ᴰ-PtdSet ℓ) ×𝒮ᴰ (𝒮ᴰ-Magma ℓ))

𝒮ᴰ-Monoid' : ∀ ℓ → DUARel (∫𝓢ᴰ-PtdSetMagma ℓ) (λ ((X , _) , pt , op) →
  ((∀ x → op x pt ≡ x) × (∀ x → op pt x ≡ x)) × (∀ x y z → op x (op y z) ≡ op (op x y) z)) ℓ
𝒮ᴰ-Monoid' ℓ .DUARel._≅ᴰ⟨_⟩_ {((A , _) , ptA , opA)} {((B , _) , ptB , opB)} axA (e , e-ptd , e-op) axB = Unit*
𝒮ᴰ-Monoid' ℓ .DUARel.uaᴰ {((A , isSetA) , _)} {((B , isSetB) , _)} ax1 _ ax2 =
  invEquiv (isContr→≃Unit* (isProp→isContrPathP (λ i → isProp× (isProp× (isPropΠ {!!})
                                                                        (isPropΠ {!!}))
                                                               (isPropΠ (λ x →
                                                                           isPropΠ (λ y →
                                                                                      isPropΠ λ z → {!!}))))
                           ax1 ax2))

𝒮ᴰ-Monoid : ∀ ℓ → DUARel (𝒮-Set ℓ)
  (λ (X , _) → Σ[ pt ∈ X ]
               Σ[ op ∈ (X → X → X) ]
               (∀ x → (op x pt ≡ x) × (op pt x ≡ x)) ×
               (∀ x y z → op (op x y) z ≡ op x (op y z))) ℓ
𝒮ᴰ-Monoid ℓ .DUARel._≅ᴰ⟨_⟩_ {(A , _)} {(B , _)} (ptA , opA , axA) e (ptB , opB , axB) = {!!}
DUARel.uaᴰ (𝒮ᴰ-Monoid ℓ) = {!!}
