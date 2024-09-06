{-# OPTIONS --cubical #-}
module ReflexiveGraphLenses where

import Agda.Builtin.Cubical.Path               as Path
import Cubical.Foundations.Prelude             as Prelude

open Path using (PathP) public
open Prelude using (_≡_ ; refl ; cong ; funExt
                        ; transport ; subst ; J; isSet) public
open import Agda.Primitive
 renaming (Set to Type; Setω to Typeω; Level to Universe)
 public

open import Agda.Builtin.Sigma public
open import Agda.Builtin.Unit renaming (⊤ to Unit) public
open import Agda.Builtin.Nat renaming (Nat to ℕ) public

private
 variable
  𝓤 𝓥 𝓦 ℓ : Universe

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

record is-contr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor contr
  field
    centre : A
    paths  : (x : A) → centre ≡ x

is-prop : {𝓤 : Universe} (A : Type 𝓤) → Type 𝓤
is-prop A = (x y : A) → x ≡ y

record reflexive-graph 𝓤 𝓤' : Type (lsuc (𝓤 ⊔ 𝓤')) where
 constructor make-reflexive-graph
 field
  tp : Type 𝓤
  edge : tp → tp → Type 𝓤'
  rx : (x : tp) → edge x x

 _≈_ = edge

 edges : Type (𝓤 ⊔ 𝓤')
 edges = Σ tp λ x → Σ tp λ y → edge x y

 ⟨_⟩+ : tp → Type (𝓤 ⊔ 𝓤')
 ⟨ x ⟩+ = Σ tp (x ≈_)

 ⟨_⟩- : tp → Type (𝓤 ⊔ 𝓤')
 ⟨ x ⟩- = Σ tp (_≈ x)

 ⟪_⟫+ : (x : tp) → ⟨ x ⟩+
 ⟪ x ⟫+ = x , rx x

 ⟪_⟫- : (x : tp) → ⟨ x ⟩-
 ⟪ x ⟫- = x , rx x

 is-univalent : Type (𝓤 ⊔ 𝓤')
 is-univalent = (x : tp) → is-prop ⟨ x ⟩+

 unext : {x y : tp} → x ≡ y → x ≈ y
 unext {x} {y} p = transport ((λ i → edge x (p i))) ((rx x))

record
  is-identity-system {ℓ ℓ'} {A : Type ℓ}
    (R : A → A → Type ℓ')
    (refl : ∀ a → R a a)
    : Type (ℓ ⊔ ℓ')
  where
  no-eta-equality
  field
    to-path      : ∀ {a b} → R a b → a ≡ b
    to-path-over : ∀ {a b} (p : R a b)
                   → PathP (λ i → R a (to-path p i)) (refl a) p

  is-contr-ΣR : ∀ {a} → is-contr (Σ A (R a))
  is-contr-ΣR .is-contr.centre    = _ , refl _
  is-contr-ΣR .is-contr.paths x i = to-path (x .snd) i , to-path-over (x .snd) i

set-identity-system : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ x → R x x}
                      → (∀ x y → is-prop (R x y))
                      → (∀ {x y} → R x y → x ≡ y)
                      → is-identity-system R r
set-identity-system rprop rpath .is-identity-system.to-path = rpath
set-identity-system rprop rpath .is-identity-system.to-path-over p =
  Prelude.isProp→PathP (λ i → rprop _ _) _ p

set-rg : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ x → R x x}
         → (∀ x y → is-prop (R x y))
         → (∀ {x y} → R x y → x ≡ y)
         → reflexive-graph ℓ ℓ'
reflexive-graph.tp (set-rg {ℓ} {ℓ'} {A} x x₁) = A
reflexive-graph.edge (set-rg {ℓ} {ℓ'} {A} {R} x x₁) = R
reflexive-graph.rx (set-rg {ℓ} {ℓ'} {A} {R} {r} x x₁) = λ x → r x

open import Cubical.Data.Unit
open import Cubical.Data.Empty

-- Observational Equality for ℕ.
Eq-ℕ : ℕ → ℕ → Type
Eq-ℕ zero zero = Unit
Eq-ℕ zero (suc x) = ⊥
Eq-ℕ (suc x) zero = ⊥
Eq-ℕ (suc x) (suc y) = Eq-ℕ x y
-- Reflexivity datum.
refl-Eq-ℕ : (m : ℕ) → Eq-ℕ m m
refl-Eq-ℕ zero = tt
refl-Eq-ℕ (suc m) = refl-Eq-ℕ m

-- ℕ-identity-system
--   : (∀ x y → is-prop (Eq-ℕ x y))
--   → (∀ {x y} → Eq-ℕ x y → x ≡ y)
--   → is-identity-system Eq-ℕ refl-Eq-ℕ
-- is-identity-system.to-path (ℕ-identity-system rprop rpath) = rpath
-- is-identity-system.to-path-over (ℕ-identity-system rprop rpath) = λ p → Prelude.isProp→PathP (λ i → rprop _ _) _ p

ℕ-rg = make-reflexive-graph ℕ Eq-ℕ refl-Eq-ℕ


isMonoid : (C : Type ℓ) → (C → C → C) → C → Type ℓ
isMonoid C _∙_ id =
  -- C is a set.
  isSet C ×
  -- Left and right identity laws.
  (∀ x → id ∙ x ≡ x) ×
  (∀ x → x ∙ id ≡ x) ×
  -- Associativity.
  (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z)

-- Monoids (on sets).
Monoid : {ℓ : Universe} → (Type (lsuc ℓ))
Monoid {ℓ} =
  -- Carrier.
  Σ (Type ℓ) λ C →
  -- Binary operation.
  Σ (C → C → C) λ _∙_ →
  -- Identity.
  Σ C λ id →
  -- Laws.
  isMonoid C _∙_ id

-- The carrier type.
Carrier : Monoid → Type ℓ
Carrier M = fst M

-- The binary operation.
op : (M : Monoid {ℓ}) → Carrier M → Carrier M → Carrier M
op M = fst (snd M)

-- The identity element.
id : (M : Monoid {ℓ}) → Carrier M
id M = fst (snd (snd M))

-- The monoid laws.
laws : (M : Monoid {ℓ}) → isMonoid (Carrier M) (op M) (id M)
laws M = snd (snd (snd M))

-- Monoid morphisms.
isMonoidHomomorphism : (M₁ M₂ : Monoid) → (Carrier M₁ → Carrier M₂) → Type ℓ
isMonoidHomomorphism M₁ M₂ f = (∀ x y → f (op M₁ x y) ≡ op M₂ (f x) (f y)) × (f (id M₁) ≡ id M₂)

-- Monoid isomorphisms.
import Cubical.Foundations.Equiv as Equivalences
open Equivalences using (_≃_)

_≅_ : {ℓ : Universe} → Monoid {ℓ} → Monoid {ℓ} → Type ℓ
M₁ ≅ M₂ = Σ (Carrier M₁ ≃ Carrier M₂) λ f → isMonoidHomomorphism M₁ M₂ (fst f)

refl-≅ : (m : Monoid {ℓ}) → m ≅ m
refl-≅ m = (reflexive-graph.rx ? ?) , {!!}

-- monoid-rg
--   : ∀ {ℓ ℓ'} {A : Monoid} {r : ∀ x → x ≅ x}
--   → (∀ x y → is-prop (x ≅ y))
--   → (∀ {x y} → x ≅ y → x ≡ y)
--   → reflexive-graph (lsuc lzero) ℓ
-- reflexive-graph.tp (monoid-rg {ℓ} {ℓ'} {A} x x₁) = Monoid
-- reflexive-graph.edge (monoid-rg {ℓ} {ℓ'} {A} {R} x x₁) = λ M N → M ≅ N
-- reflexive-graph.rx (monoid-rg {ℓ} {ℓ'} {A} {r} x x₁) = λ x → r x

monoidrg = make-reflexive-graph Monoid ((λ M N → M ≅ N)) refl-≅

-- record Monoid {ℓ} : Type (lsuc ℓ) where
--   field S   : Type ℓ
--         ε   : S
--         _•_ : S → S → S
--         lid : ∀{m} → ε • m ≡ m
--         rid : ∀{m} → m • ε ≡ m
--         ass : ∀{m n o} → (m • n) • o ≡ m • (n • o)

-- Monoid-rg = make-reflexive-graph Monoid {!!} {!!}

record path-object 𝓤 𝓤' : Type (lsuc (𝓤 ⊔ 𝓤')) where
 constructor make-path-object
 field
  tp : Type 𝓤
  edge : tp → tp → Type 𝓤'
  rx : (x : tp) → edge x x

 to-rx-gph : reflexive-graph 𝓤 𝓤'
 to-rx-gph = make-reflexive-graph tp edge rx

module _ {𝓤 𝓤'} (𝓐 : reflexive-graph 𝓤 𝓤') where
 private module 𝓐 = reflexive-graph 𝓐

 family-of-reflexive-graphs : (𝓥 𝓥' : Universe) → Type (𝓤 ⊔ lsuc (𝓥 ⊔ 𝓥'))
 family-of-reflexive-graphs 𝓥 𝓥' = 𝓐.tp → reflexive-graph 𝓥 𝓥'

 family-of-path-objects : (𝓥 𝓥' : Universe) → Type (𝓤 ⊔ lsuc (𝓥 ⊔ 𝓥'))
 family-of-path-objects 𝓥 𝓥' = 𝓐.tp → path-object 𝓥 𝓥'

 module family-of-reflexive-graphs {𝓥 𝓥'} (𝓑 : family-of-reflexive-graphs 𝓥 𝓥') where
  module _ (x : 𝓐.tp) where
   open reflexive-graph (𝓑 x) public using (tp)
  module _ {x : 𝓐.tp} where
   open reflexive-graph (𝓑 x) public hiding (tp)

record oplax-covariant-lens {𝓤 𝓤' 𝓥 𝓥'} (𝓐 : reflexive-graph 𝓤 𝓤') (𝓑 : family-of-reflexive-graphs 𝓐 𝓥 𝓥') : Type (𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥') where
 constructor make-oplax-covariant-lens
 private
  module 𝓐 = reflexive-graph 𝓐
  module 𝓑 = family-of-reflexive-graphs 𝓐 𝓑

 field
  push＠ : (a0 a1 : 𝓐.tp) (a01 : a0 𝓐.≈ a1) → 𝓑.tp a0 → 𝓑.tp a1

 push : {a0 a1 : 𝓐.tp} (a01 : a0 𝓐.≈ a1) → 𝓑.tp a0 → 𝓑.tp a1
 push = push＠ _ _

 field
  push-rx : (a : 𝓐.tp) (b : 𝓑.tp a) → push (𝓐.rx a) b 𝓑.≈ b

 definitional-covariant-lens : oplax-covariant-lens 𝓐 𝓑
 push＠ definitional-covariant-lens a0 a1 a01 x = push a01 x
 push-rx definitional-covariant-lens a b = (push-rx a b)

-- oplonmonoid = make-oplax-covariant-lens monoidrg ?
