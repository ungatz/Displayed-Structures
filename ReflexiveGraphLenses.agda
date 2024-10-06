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
𝒮ᴰ-Magma ℓ .DUARel.uaᴰ {(A , _)} {(B , _)} ∘A e ∘B = invEquiv (
  PathP (λ i → ua e i → ua e i → ua e i) ∘A ∘B                                ≃⟨ PathP≃Path _ _ _ ⟩
  transport (λ i → ua e i → ua e i → ua e i) ∘A ≡ ∘B                          ≃⟨ invEquiv funExt₂Equiv ⟩
  ((b b' : B) → transport (λ i → ua e i → ua e i → ua e i) ∘A b b' ≡ ∘B b b') ≃⟨ equivΠ (invEquiv e) (λ b → equivΠ (invEquiv e) (λ b' → lem b b')) ⟩
  ((a a' : A) → f (∘A a a') ≡ ∘B (f a) (f a')) ■)
  where
  f : A → B
  f = equivFun e
  g : B → A
  g = equivFun (invEquiv e)
  fg~id : (b : B) → f (g b) ≡ b
  fg~id b = equivToIso e .Iso.rightInv b
  lem : (b b' : B) → (transport (λ i → ua e i → ua e i → ua e i) ∘A b b' ≡ ∘B b b') ≃ (f (∘A (g b) (g b')) ≡ ∘B (f (g b)) (f (g b')))
  lem b b' =
    transport (λ i → ua e i → ua e i → ua e i) ∘A b b' ≡ ∘B b b'                     ≃⟨ idEquiv _ ⟩
    transport refl (f (∘A (g (transport refl b)) (g (transport refl b')))) ≡ ∘B b b' ≃⟨ compPathlEquiv (sym (transportRefl _)) ⟩
    f (∘A (g (transport refl b)) (g (transport refl b'))) ≡ ∘B b b'                  ≃⟨ compPathlEquiv (sym λ i → f (∘A (g (transportRefl b i)) (g (transportRefl b' i)))) ⟩
    f (∘A (g b) (g b')) ≡ ∘B b b'                                                    ≃⟨ compPathrEquiv (sym λ i → ∘B (fg~id b i) (fg~id b' i)) ⟩
    f (∘A (g b) (g b')) ≡ ∘B (f (g b)) (f (g b')) ■

∫𝓢ᴰ-Magma : ∀ ℓ → UARel (Σ (hSet ℓ) (λ (X , _) → X → X → X)) ℓ
∫𝓢ᴰ-Magma ℓ = ∫ (𝒮ᴰ-Magma ℓ)

RawSemiGroup : ∀ ℓ → Type (lsuc ℓ)
RawSemiGroup ℓ = Σ[ (X , _) ∈ (hSet ℓ) ] (X → X → X)

SemiGroupAxioms : ∀ ℓ → RawSemiGroup ℓ → Type ℓ
SemiGroupAxioms ℓ ((X , _) , op) = ∀ x y z → op x (op y z) ≡ op (op x y) z

𝓢ᴰ-SemiGroup : ∀ ℓ → DUARel (∫𝓢ᴰ-Magma ℓ) (SemiGroupAxioms ℓ) ℓ
DUARel._≅ᴰ⟨_⟩_ (𝓢ᴰ-SemiGroup ℓ) {(A , _) , oA} {(B , _) , oB} ax (e , e-op) ax' = Unit*
DUARel.uaᴰ (𝓢ᴰ-SemiGroup ℓ) {(A , isSetA) , oA} {(B , isSetB) , oB} ax M ax' =
  invEquiv (isContr→≃Unit* (subst⁻ isContr (PathP≡Path _ _ _)
    (isProp→isContrPath (isPropΠ3 (λ _ _ _ →  isSetB _ _)) _ _)))

∫𝓢ᴰ-RawMonoid : ∀ ℓ → UARel (Σ (hSet ℓ) (λ (X , _) → X × (X → X → X))) ℓ
∫𝓢ᴰ-RawMonoid ℓ = ∫ ((𝒮ᴰ-PtdSet ℓ) ×𝒮ᴰ (𝒮ᴰ-Magma ℓ))

RawMonoid : ∀ ℓ → Type (lsuc ℓ)
RawMonoid ℓ = Σ[ (X , _) ∈ (hSet ℓ) ] X × (X → X → X)

MonoidAxioms : ∀ ℓ → RawMonoid ℓ → Type ℓ
MonoidAxioms ℓ ((X , _) , pt , op) = (∀ x → op x pt ≡ x) × (∀ x → op pt x ≡ x) × (∀ x y z → op x (op y z) ≡ op (op x y) z)

𝒮ᴰ-Monoid : ∀ ℓ → DUARel (∫𝓢ᴰ-RawMonoid ℓ) (MonoidAxioms ℓ) ℓ
𝒮ᴰ-Monoid ℓ .DUARel._≅ᴰ⟨_⟩_ {((A , _) , eA , ∘A)} {((B , _) , eB , ∘B)} axA (e , e-ptd , e-op) axB = Unit*
𝒮ᴰ-Monoid ℓ .DUARel.uaᴰ {((A , isSetA) , eA , ∘A)} {((B , isSetB) , eB , ∘B)} ax M ax' =
  invEquiv (isContr→≃Unit* (subst⁻ isContr (PathP≡Path _ _ _)
    (isProp→isContrPath (isProp×2 (isPropΠ (λ _ → isSetB _ _)) (isPropΠ (λ _ → isSetB _ _)) (isPropΠ3 λ _ _ _ → isSetB _ _))
      _ _)))

∫𝓢ᴰ-Monoid : ∀ ℓ → UARel (Σ[ X ∈ RawMonoid ℓ ] MonoidAxioms ℓ X) ℓ
∫𝓢ᴰ-Monoid ℓ = ∫ (𝒮ᴰ-Monoid ℓ)

Monoid : ∀ ℓ → Type (lsuc ℓ)
Monoid ℓ = Σ[ X ∈ RawMonoid ℓ ] MonoidAxioms ℓ X

MonoidEquiv : ∀ ℓ → (M M' : Monoid ℓ) → Type (lsuc ℓ)
MonoidEquiv ℓ M@(((X , _) , (e , ∘)) , _) M'@(((X' , _) , (e' , ∘')) , _) =
  Σ (X ≃ X') (λ (f , _) → Lift (f e ≡ e') × ∀ (x y : X) → f (∘ x y) ≡ ∘' (f x) (f y))

MonoidUnivalence : ∀ ℓ → (M M' : Monoid ℓ) → MonoidEquiv ℓ M M' → M ≡ M'
MonoidUnivalence ℓ M M' me = equivFun (∫𝓢ᴰ-Monoid ℓ .UARel.ua M M') ((fst me , lower (fst (snd me)) , snd (snd me)) , tt*)
