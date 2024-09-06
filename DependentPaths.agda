{-# OPTIONS --cubical #-}
module DependentPaths where
-- open import Cubical.Foundations.Prelude using (transport)

-- ordinary identity types

data _≡_ {A : Set} : A → A → Set where
  refl : (a : A) → a ≡ a

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym (refl x) = refl x

_·_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(refl x) · p = p

-- dependent identity types

data ≡d {A : Set} {B : A → Set} : {a a' : A} → a ≡ a' → B a → B a' → Set where
  refld : {a : A} {b : B a} → ≡d (refl a) b b

symd : {A : Set} {B : A → Set} {x y : A} {p : x ≡ y}
       {xd : B x} {yd : B y} → ≡d p xd yd → ≡d (sym p) yd xd
symd refld = refld

_·d_ : {A : Set} {B : A → Set} {x y z : A} {p : x ≡ y} {q : y ≡ z}
       {xd : B x} {yd : B y} {zd : B z} → ≡d p xd yd → ≡d q yd zd → ≡d (p · q) xd zd
refld ·d pd = pd

-- Exercise: give an alternate definition of dependent identity types in terms
-- of _≡_ and transport (i.e., without defining a new data type) and prove sym/trans.
id : {A : Set} → A → A
id a = a

id' : (A : Set) → A → A
id' A = id

transport : {A : Set} (B : A → Set) {a a' : A} → a ≡ a' → B a → B a'
transport B (refl a) = id' (B a)

transport⁻ : {A : Set} (B : A → Set) {a a' : A} → a ≡ a' → B a' → B a
transport⁻ B (refl a') = id' (B a')

𝕁 : (X : Set) (A : (x y : X) → x ≡ y → Set)
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p
𝕁 X A f x x (refl x) = f x

depId : {A : Set} (B : A → Set) → {a a' : A} → a ≡ a' → B a → B a' → Set
depId B p b b' = transport B p b ≡ b'

depId' : {A : Set} (B : A → Set) → {a a' : A} → a ≡ a' → B a → B a' → Set
depId' B p b b' = transport⁻ B ((sym p)) b ≡ b'

-- depId𝕁 : {A : Set} (B : A → Set) → {a a' : A} → a ≡ a' → B a → B a' → Set
-- depId𝕁 {A} B {a} {a'} p b b' = 𝕁 A {!(λ x y _ → B x → B y)!} ((λ x → id' (B x))) a a' {!p!} {!!}

symd' : {A : Set} {B : A → Set} {x y : A} {p : x ≡ y}
        {xd : B x} {yd : B y} → depId B p xd yd → depId B (sym p) yd xd
symd' {p = (refl x)} (refl yd) = refl yd

_·d'_ : {A : Set} {B : A → Set} {x y z : A} {p : x ≡ y} {q : y ≡ z}
       {xd : B x} {yd : B y} {zd : B z} →
       depId B p xd yd → depId B q yd zd → depId B (p · q) xd zd
_·d'_ {p = (refl x)} {q = q} (refl yd) qd = qd


-- open import HoTT-UF-Agda using (_,_ ; _×_)

-- Shallow charactarisation of binary product.
record Σ {𝓤 𝓥} {X : Set} (Y : X → Set) : Set  where
  constructor
   _,_
  field
   x : X
   y : Y x

pr₁ : {X : Set} {Y : X → Set} → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : Set} {Y : X → Set} → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

-Σ : (X : Set) (Y : X → Set) → Set
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ꞉ X , y

_×_ : Set → Set → Set
X × Y = Σ x ꞉ X , Y

splitId : {A B : Set} (x y : A) (u v : B) →
          (x , u) ≡ (y , v) → (x ≡ y) × (u ≡ v)
splitId x y u v (refl _) = (refl x , refl u)

-- Deep charactarisation, replace A and B with relexive graphs 𝓐 and 𝓑.
record RG (𝓐 : Set) : Set₁ where
 field
   _≅_ : 𝓐 → 𝓐 → Set
   rx𝓐 : (x : 𝓐) → x ≅ x

 idToEdge : {𝓖 : Set} → (x y : RG 𝓖) → x ≡ y → x ≅ y
 idToEdge = ?

-- Given a reflexive graph 𝓖 it is univalent.
idToEdge : {𝓖 : Set} → (x y : RG 𝓖) → x ≡ y → x RG.≅ y
idToEdge = ?

-- path objects are basically a URG
