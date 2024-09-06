{-# OPTIONS --cubical #-}

module RepresentationIndependence where


-- 2.1
import Agda.Builtin.Cubical.Path               as Path
import Cubical.Foundations.Prelude             as Prelude
-- 2.2
import Cubical.Foundations.Univalence          as Univalence
import Cubical.Foundations.HLevels             as HLevels
import Cubical.Foundations.Equiv               as Equivalences
import Cubical.Data.Sigma.Properties           as Sigma
-- 2.3
import Cubical.HITs.PropositionalTruncation    as PropositionalTruncation
import Cubical.HITs.Cost.Base                  as CostMonad
import Cubical.HITs.SetQuotients               as SetQuotients
import Cubical.Data.Rationals                  as SetQuoQ
import Cubical.Data.Rationals.MoreRationals.SigmaQ
                                               as SigmaQ
-- 3.1
import Cubical.Foundations.SIP                 as SIP
import Cubical.Structures.Axioms               as Axioms
import Cubical.Algebra.Semigroup.Base          as Semigroup
import Cubical.Algebra.Monoid.Base             as Monoid
open import Cubical.Data.Sigma.Base
-- 3.2
import Cubical.Structures.Pointed              as PointedStr
import Cubical.Structures.Constant             as ConstantStr
import Cubical.Structures.Product              as ProductStr
import Cubical.Structures.Function             as FunctionStr
import Cubical.Structures.Maybe                as MaybeStr
import Cubical.Foundations.Structure           as Structure
import Cubical.Structures.Auto                 as Auto
open import Cubical.Data.Maybe.Base
-- 4.1
import Cubical.Data.Vec.Base                   as Vector
import Cubical.Algebra.Matrix                  as Matrices
import Cubical.Data.FinData.Base               as Finite
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Bool.Base
-- 4.2
import Cubical.Structures.Queue                as Queues
import Cubical.Data.Queue.Truncated2List       as BatchedQueues
-- 5.1
import Cubical.Relation.Binary.Base            as BinRel
import Cubical.Relation.ZigZag.Base            as QER
import Cubical.Relation.ZigZag.Applications.MultiSet
                                               as MultiSets
-- 5.2
import Cubical.Foundations.RelationalStructure as RelStructure
import Cubical.Structures.Relational.Function  as RelFunction



-------------------------------------------------------------------------
-- 2. Programming in Cubical Type Theory
-- 2.1 Equalities as Paths
-- 2.2 Univalence
-- 2.3 Higher Inductive Types
-------------------------------------------------------------------------


-- 2.1 Equalities as Paths
open Path using (PathP) public
open Prelude using (_≡_ ; refl ; cong ; funExt
                        ; transport ; subst ; J) public


-- 2.2 Univalence
open Univalence using (ua ; uaβ) public

-- Sets and Propositions
open Prelude using (isProp ; isSet) public
open HLevels using (isPropΠ) public
open Prelude using (isContr) public

-- Equivalences and Isomorphisms
open Equivalences using (isEquiv ; _≃_) public
open Equivalences renaming (fiber to preim) public
open Sigma using (ΣPath≃PathΣ) public
open Equivalences renaming (propBiimpl→Equiv to prop≃) public


-- 2.3 Higher Inductive Types
-- Propositional Truncation
open PropositionalTruncation using (∥_∥₁ ; map) public
open CostMonad using (Cost ; Cost≡ ; _>>=_ ; return
                           ; fib ; fibTail) public
-- Computation
_ : fib 20 ≡ (6765 , PropositionalTruncation.∣ 21890 ∣₁)
_ = refl

_ : fibTail 20 ≡ (6765 , PropositionalTruncation.∣ 19 ∣₁)
_ = refl

-- Set Quotients
open SetQuotients using (_/_ ; setQuotUniversal) public
-- Rational Numbers
open SetQuoQ using (_∼_ ; ℚ) public
open SigmaQ renaming (ℚ to ℚ') public



-------------------------------------------------------------------------
-- 3. The Structure Identity Principle
-- 3.1 Structures
-- 3.2 Building Strucutres
-------------------------------------------------------------------------

-- 3.1 Structures
open SIP using (TypeWithStr ; StrEquiv ; _≃[_]_
                            ; UnivalentStr ; SIP ; sip) public

-- the last two terms above correspond to lemma 3.3
-- and corollary 3.4 respectively
open Axioms using ( AxiomsStructure ; AxiomsEquivStr
                  ; axiomsUnivalentStr ; transferAxioms) public

-- Monoids are defined using records and Σ-types in the library
RawMonoidStructure : Type → Type
RawMonoidStructure X = X × (X → X → X)

MonoidAxioms : (M : Type) → RawMonoidStructure M → Type
MonoidAxioms M (e , _·_) = Semigroup.IsSemigroup _·_
                         × ((x : M) → (x · e ≡ x) × (e · x ≡ x))

MonoidStructure : Type → Type
MonoidStructure = AxiomsStructure RawMonoidStructure MonoidAxioms

Monoid : Type₁
Monoid = TypeWithStr ℓ-zero MonoidStructure

MonoidEquiv : (M N : Monoid) → fst M ≃ fst N → Type
MonoidEquiv (_ , (εᴹ , _·_) , _) (_ , (εᴺ , _∗_) , _) (φ , _) =
  (φ εᴹ ≡ εᴺ) × (∀ x y → φ (x · y) ≡ (φ x) ∗ (φ y))

MonoidEquiv' : (M N : Monoid) → Type
-- MonoidEquiv' (_ , (εᴹ , _·_) , _) (_ , (εᴺ , _∗_) , _)  = Σ (fst M ≃ fst N)  (φ εᴹ ≡ εᴺ) × (∀ x y → φ (x · y) ≡ (φ x) ∗ (φ y))

-- URG Structure
is-prop : {ℓ : Level} (A : Type ℓ) → Type ℓ
is-prop A = (x y : A) → x ≡ y

record reflexive-graph ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
 constructor make-reflexive-graph
 field
  tp : Type ℓ
  edge : tp → tp → Type ℓ'
  rx : (x : tp) → edge x x

 _≈_ = edge

 edges : Type (ℓ-max ℓ ℓ')
 edges = Σ tp λ x → Σ tp λ y → edge x y

 ⟨_⟩+ : tp → Type (ℓ-max ℓ ℓ')
 ⟨ x ⟩+ = Σ tp (x ≈_)

 ⟨_⟩- : tp → Type (ℓ-max ℓ ℓ')
 ⟨ x ⟩- = Σ tp (_≈ x)

 ⟪_⟫+ : (x : tp) → ⟨ x ⟩+
 ⟪ x ⟫+ = x , rx x

 ⟪_⟫- : (x : tp) → ⟨ x ⟩-
 ⟪ x ⟫- = x , rx x

 is-univalent : Type (ℓ-max ℓ ℓ')
 is-univalent = (x : tp) → is-prop ⟨ x ⟩+

 unext : {x y : tp} → x ≡ y → x ≈ y
 unext p = {!!}

-- URG structure on type of monoids i.e. SIP for monoids
-- i.e. an identification of monoids valued in a univalent
-- universe is precisely a monoid isomorphism
𝒮-monoid : reflexive-graph (ℓ-suc ℓ-zero) (ℓ-suc (ℓ-suc ℓ-zero))
𝒮-monoid = make-reflexive-graph {!!} {!!} {!!}
-- 𝒮-monoid : reflexive-graph (ℓ-suc ℓ-zero) (ℓ-suc (ℓ-suc ℓ-zero))
-- 𝒮-monoid = make-reflexive-graph Monoid ((λ M N → Σ (fst M ≃ fst N) (λ f → MonoidEquiv M N f))) ?



-- 3.2 Building Structures
-- Constant and Pointed Structures
open PointedStr using (PointedStructure ; PointedEquivStr
                                        ; pointedUnivalentStr) public
open ConstantStr using (ConstantStructure ; ConstantEquivStr
                                          ; constantUnivalentStr) public

-- Product Structures
open ProductStr using (ProductStructure ; ProductEquivStr
                                        ; productUnivalentStr) public

-- Function Structures
open FunctionStr using (FunctionEquivStr) public

-- Maybe Structures
open MaybeStr using (MaybeEquivStr) public

-- Transport Structures
open Structure using (EquivAction) public
open SIP using (TransportStr ; TransportStr→UnivalentStr
                             ; UnivalentStr→TransportStr) public
open Structure using (EquivAction→StrEquiv) public
open FunctionStr using (FunctionEquivStr+) public

-- Monoids Revisited

RawMonoid : Type₁
RawMonoid = TypeWithStr _ RawMonoidStructure

Monoid→RawMonoid : Monoid → RawMonoid
Monoid→RawMonoid (A , r , _) = (A , r)

RawMonoidEquivStr = Auto.AutoEquivStr RawMonoidStructure

rawMonoidUnivalentStr : UnivalentStr _ RawMonoidEquivStr
rawMonoidUnivalentStr = Auto.autoUnivalentStr RawMonoidStructure

isPropMonoidAxioms : (M : Type) (s : RawMonoidStructure M) → isProp (MonoidAxioms M s)
isPropMonoidAxioms M (e , _·_) =
  HLevels.isPropΣ
    (Semigroup.isPropIsSemigroup _·_)
    (λ α → isPropΠ λ _ →
      HLevels.isProp×
        (Semigroup.IsSemigroup.is-set α _ _)
        (Semigroup.IsSemigroup.is-set α _ _))

MonoidEquivStr : StrEquiv MonoidStructure ℓ-zero
MonoidEquivStr = AxiomsEquivStr RawMonoidEquivStr MonoidAxioms

monoidUnivalentStr : UnivalentStr MonoidStructure MonoidEquivStr
monoidUnivalentStr = axiomsUnivalentStr _ isPropMonoidAxioms rawMonoidUnivalentStr

MonoidΣPath : (M N : Monoid) → (M ≃[ MonoidEquivStr ] N) ≃ (M ≡ N)
MonoidΣPath = SIP monoidUnivalentStr

InducedMonoid : (M : Monoid) (N : RawMonoid) (e : M .fst ≃ N .fst)
                → RawMonoidEquivStr (Monoid→RawMonoid M) N e → Monoid
InducedMonoid M N e r =
  Axioms.inducedStructure rawMonoidUnivalentStr M N (e , r)

InducedMonoidPath : (M : Monoid) (N : RawMonoid) (e : M .fst ≃ N .fst)
                    (E : RawMonoidEquivStr (Monoid→RawMonoid M) N e)
                    → M ≡ InducedMonoid M N e E
InducedMonoidPath M N e E =
  MonoidΣPath M (InducedMonoid M N e E) .fst (e , E)

-- Automation
open Auto using (Transp[_] ; AutoEquivStr ; autoUnivalentStr) public
module _ (A : Type) (Aset : isSet A) where
 RawQueueEquivStr =
   AutoEquivStr (λ (X : Type) → X × (A → X → X) × (X → Transp[ Maybe (X × A) ]))


-- Groups can also be defined using records and Σ-types
RawGroupStructure : {ℓ : Level} → Type ℓ → Type ℓ
RawGroupStructure X = X × (X → X → X) × (X → X)

GroupAxioms : {ℓ : Level} (G : Type ℓ) → RawGroupStructure G → Type ℓ
GroupAxioms G (1g , _·_ , inv) = (Monoid.IsMonoid 1g _·_)
                               × (((x : G) → (x · inv x ≡ 1g) × (inv x · x ≡ 1g)))

GroupStructure : {ℓ : Level} → Type ℓ → Type ℓ
GroupStructure = AxiomsStructure RawGroupStructure GroupAxioms

Group : {ℓ : Level} → Type (ℓ-suc ℓ-zero)
Group = TypeWithStr ℓ-zero GroupStructure

GroupEquiv : (G 𝓖 : Group) → fst G ≃ fst 𝓖 → Type
GroupEquiv (_ , (1g , _·_ , invᴳ) , _) (_ , (1ℊ , _*_ , invᵍ) , _) (φ , _) =
  (φ 1g ≡ 1ℊ) × (∀ x y → φ (x · y) ≡ (φ x) * (φ y)) × ((∀ x → (φ (invᴳ x)) ≡ (invᵍ (φ x))))

-- GroupEquiv′ : {ℓ : Level} (G : Group) → (𝓖 : Group) → fst G ≃ fst 𝓖 → Type ℓ
-- GroupEquiv′ (_ , (1g , _·_ , invᴳ) , _) (_ , (1ℊ , _*_ , invᵍ) , _) (φ , _) =
--   (φ 1g ≡ 1ℊ) × (∀ x y → φ (x · y) ≡ (φ x) * (φ y)) × ((∀ x → (φ (invᴳ x)) ≡ (invᵍ (φ x))))


-- record displayed-reflexive-graph {ℓ ℓ' 𝓥 𝓥'} (𝓐 : reflexive-graph ℓ ℓ') 𝓥 𝓥' : Type (ℓ-max ℓ ℓ' (ℓ-suc (ℓ-max 𝓥 𝓥'))) where
--  constructor make-displayed-reflexive-graph
--  private module 𝓐 = reflexive-graph 𝓐

--  field
--   tp : 𝓐.tp → Type 𝓥
--   edge : (a0 a1 : 𝓐.tp) (a01 : a0 𝓐.≈ a1) (b0 : tp a0) (b1 : tp a1) → Type 𝓥'

--  _≈[_]_ : {a0 a1 : 𝓐.tp} (b0 : tp a0) (a01 : a0 𝓐.≈ a1) (b1 : tp a1) → Type 𝓥'
--  b0 ≈[ p ] b1 = edge _ _ p b0 b1

--  field
--   rx : (a : 𝓐.tp) (b : tp a) → b ≈[ 𝓐.rx a ] b

--  diagonal : 𝓐.tp → reflexive-graph 𝓥 𝓥'
--  diagonal x = make-reflexive-graph (tp x) (edge x x (𝓐.rx x)) (rx x)

--  module diagonal {x} = reflexive-graph (diagonal x)

--  is-univalent : Type (ℓ-max ℓ 𝓥 𝓥')
--  is-univalent = (x : 𝓐.tp) → diagonal.is-univalent {x}

-- -- URG structure on the type of groups
-- 𝒮-group : URG Group ℓ-zero
-- 𝒮-group = urgstr (λ G 𝓖 → GroupEquiv G 𝓖 {!!}) {!!}

-------------------------------------------------------------------------
-- 4. Representation Independence through the SIP
-- 4.1 Matrices
-- 4.2 Queues
-------------------------------------------------------------------------


-- 4.1 Matrices
open Vector using (Vec) public
open Finite using (Fin ; _==_) public
open Matrices using (VecMatrix ; FinMatrix ; FinMatrix≡VecMatrix
                                           ; FinMatrix≃VecMatrix) public
open Matrices.FinMatrixAbGroup using (addFinMatrix ; addFinMatrixComm) public

-- example (not in the library)
open import Cubical.Data.Int hiding (-_)

ℤ-AbGroup : AbGroup ℓ-zero
ℤ-AbGroup = makeAbGroup {G = ℤ} 0 _+_ -_ isSetℤ +Assoc (λ x _ → x) rem +Comm
    where
    -_ : ℤ → ℤ
    - x = 0 - x
    rem : (x : ℤ) → x + (- x) ≡ 0
    rem x =  +Comm x (pos 0 - x) Prelude.∙ minusPlus x 0

module experiment where
  open Prelude

  M : FinMatrix ℤ 2 2
  M i j = if i == j then 1 else 0

  N : FinMatrix ℤ 2 2
  N i j = if i == j then 0 else 1

  replaceGoal : {A B : Type} {x y : A} → (e : A ≃ B)
                (h : invEq e (equivFun e x) ≡ invEq e (equivFun e y)) → x ≡ y
  replaceGoal e h = sym (retEq e _) ∙∙ h ∙∙ retEq e _

  _ : addFinMatrix ℤ-AbGroup M N ≡ (λ _ _ → 1)
  _ = replaceGoal (FinMatrix≃VecMatrix) refl


-- 4.2 Queues
open Queues.Queues-on using (RawQueueStructure ; QueueAxioms) public
open BatchedQueues.Truncated2List renaming (Q to BatchedQueueHIT)
                                  using (Raw-1≡2 ; WithLaws) public



-------------------------------------------------------------------------
-- 5. Structured Equivalences from Structured Relations
-- 5.1 Quasi-Equivalence Relations
-- 5.2 Structured Relations
-------------------------------------------------------------------------


-- 5.1 Quasi-Equivalence Relations
--Lemma (5.1)
open BinRel using (idPropRel ; invPropRel
                             ; compPropRel ; graphRel) public
-- Definitions (5.2) and (5.3)
open QER using (isZigZagComplete ; isQuasiEquivRel) public
-- Lemma (5.4)
open QER.QER→Equiv using (Thm ; bwd≡ToRel) public
-- Multisets
open MultiSets renaming (AList to AssocList) public
open MultiSets.Lists&ALists using (addIfEq ; R ; φ ; ψ
                                           ; List/Rᴸ≃AList/Rᴬᴸ) public
open MultiSets.Lists&ALists.L using (insert ; union ; count)
open MultiSets.Lists&ALists.AL using (insert ; union ; count)


-- 5.2 Structured Relations
open RelStructure using (StrRel) public
-- Definition (5.6)
open RelStructure using (SuitableStrRel) public
-- Theorem (5.7)
open RelStructure using (structuredQER→structuredEquiv) public
-- Definition (5.9)
open RelStructure using (StrRelAction) public
-- Lemma (5.10)
open RelStructure using (strRelQuotientComparison) public
-- Definition (5.11)
open RelStructure using (PositiveStrRel) public
-- Theorem (5.12)
open RelFunction using (functionSuitableRel) public
-- Multisets
-- (main is applying 5.7 to the example)
open MultiSets.Lists&ALists using (multisetShape ; isStructuredR ; main ; List/Rᴸ≡AList/Rᴬᴸ)
                            renaming ( hasAssociativeUnion to unionAssocAxiom
                                     ; LQassoc to LUnionAssoc
                                     ; ALQassoc to ALUnionAssoc) public
