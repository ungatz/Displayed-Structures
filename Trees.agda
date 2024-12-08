{-# OPTIONS --safe --cubical #-}
module Trees where

open import Agda.Primitive public
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Relation.Everything
open import Cubical.Displayed.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv
open import Cubical.Structures.Axioms using (AxiomsStructure; AxiomsEquivStr; axiomsUnivalentStr)
open import Cubical.Structures.Macro
open import Cubical.Structures.Auto
open import Cubical.Foundations.SIP
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.List
open import Cubical.Relation.ZigZag.Base
open import Cubical.HITs.SetQuotients hiding ([_])
open import Cubical.HITs.PropositionalTruncation

-- Ord on ℕ
_<_ : ℕ → ℕ → Bool
_     < zero  = false
zero  < suc _ = true
suc n < suc m = n < m

_>_ : ℕ → ℕ → Bool
n > m = m < n

_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc m = false
suc n == zero = false
suc n == suc m = n == m

module LST where
 memberL? : ℕ → List ℕ → Bool
 memberL? y [] = false
 memberL? y (x ∷ xs) = (x == y) or (memberL? y xs)

 insertL : ℕ → List ℕ → List ℕ
 insertL x [] = x ∷ []
 insertL x (y ∷ ys) with x < y
 ... | true  = x ∷ y ∷ ys
 ... | false = y ∷ insertL x ys

 sortList : List ℕ → List ℕ
 sortList [] = []
 sortList (x ∷ xs) = insertL x (sortList xs)

module BST where
  Key = ℕ

  -- binary search tree
  data BinarySearchTree : Type where
    emptyTree : BinarySearchTree
    tree : (l : BinarySearchTree)   -- left subtree
         -> Key                     -- key in current node
         -> (r : BinarySearchTree)  -- right subtree
         -> BinarySearchTree

  bound? : Key → BinarySearchTree → Bool
  bound? k emptyTree         = false
  bound? k (tree tl k2 tr) =
    if k < k2
    then bound? k tl
    else (
      if k > k2
      then bound? k tr
      else true )

  inorder : BinarySearchTree → List ℕ
  inorder emptyTree = []
  inorder (tree tl k tr) = inorder tl ++ [ k ] ++ inorder tr

  preorder : BinarySearchTree → List ℕ
  preorder emptyTree = []
  preorder (tree tl k tr) = [ k ] ++ preorder tl ++ preorder tr

  open LST
  member? : Key → BinarySearchTree → Bool
  member? x emptyTree = false
  member? x (tree tl k tr) = (k == x) or (LST.memberL? x (inorder tl)) or (LST.memberL? x (inorder tr))

  -- member? k emptyTree        = false
  -- member? k (tree tl k2 tr) with k < k2
  -- ...  | true  = member? k tl
  -- ...  | false with k > k2
  -- ...    | true  = member? k tr
  -- ...    | false = true

  insert : Key → BinarySearchTree → BinarySearchTree
  insert k emptyTree = tree emptyTree k emptyTree  -- new node with key k
  insert k (tree tl k2 tr) with k < k2
  ... | true  = tree (insert k tl) k2 tr  -- If k < k2, insert in the left subtree
  ... | false with k > k2
  ...   | true  = tree tl k2 (insert k tr)  -- If k > k2, insert in the right subtree
  ...   | false = tree tl k tr  -- If k == k2, just return the tree as it is

 -- incomplete, supposed to be faster union
 -- merge : BinarySearchTree → BinarySearchTree → BinarySearchTree
 -- merge emptyTree r = r
 -- merge l emptyTree = l
 -- merge l (tree rl k rr) = tree (merge l rl) k rr

  -- Union of two trees, inserting elements from the second into the first
  union : BinarySearchTree → BinarySearchTree → BinarySearchTree
  union t1 emptyTree = t1
  union emptyTree t2 = t2
  union (tree tl k tr) t2 = insert k (union tl (union tr t2))

  -- depends on merge
  remove : Key → BinarySearchTree → BinarySearchTree
  remove k emptyTree = emptyTree
  remove k (tree tl k2 tr) with k < k2
  ... | true  = tree (remove k tl) k2 tr
  ... | false with k > k2
  ...   | true  = tree tl k2 (remove k tr)
  ...   | false = union tl tr  -- if key matches, merge left and right]

  testTree : BinarySearchTree
  testTree = tree (tree emptyTree 2 emptyTree) 4 (tree emptyTree 5 emptyTree)

  testInsert : insert 5
                      (insert 2
                        (insert 4 emptyTree)) ≡ testTree
  testInsert = refl

  testMember?1 : member? 5 testTree ≡ true
  testMember?1 = refl

  tree1 : BinarySearchTree
  tree1 = tree (tree emptyTree 1 emptyTree) 3 (tree emptyTree 5 emptyTree)

  tree2 : BinarySearchTree
  tree2 = tree (tree emptyTree 2 emptyTree) 4 (tree emptyTree 6 emptyTree)

module RBT where
  Key = ℕ

  data Color : Type where
    Red   : Color
    Black : Color

  data RedBlackTree : Type where
    emptyRBT : RedBlackTree
    rbtree   : (c : Color)
             → (left : RedBlackTree)
             → (k : Key)
             → (right : RedBlackTree)
             → RedBlackTree

  inorder : RedBlackTree → List ℕ
  inorder emptyRBT = []
  inorder (rbtree c tl k tr) = inorder tl ++ (k ∷ inorder tr)

  preorder : RedBlackTree → List ℕ
  preorder emptyRBT = []
  preorder (rbtree c tl k tr) = [ k ] ++ preorder tl ++ preorder tr

  open LST
  member? : Key → RedBlackTree → Bool
  member? x emptyRBT = false
  member? x (rbtree _ tl k tr) = (k == x) or (LST.memberL? x (inorder tl)) or (LST.memberL? x (inorder tr))

  balance : Color → RedBlackTree → Key → RedBlackTree → RedBlackTree
  balance Red   tl k tr = rbtree Red tl k tr
  balance Black tl k tr = checkL tl tr
    where
      checkR : RedBlackTree → RedBlackTree → RedBlackTree
      -- if Red Red t
      checkR tl (rbtree Red (rbtree Red b y tr2) z tr3) =
        rbtree Red (rbtree Black tl k b) y (rbtree Black tr2 z tr3)
      -- if Red t Red
      checkR tl (rbtree Red b@emptyRBT y (rbtree Red tl2 z tr2)) =
        rbtree Red (rbtree Black tl k b) y (rbtree Black tl2 z tr2)
      checkR tl (rbtree Red b@(rbtree Black _ _ _) y (rbtree Red tl2 z tr2)) =
        rbtree Red (rbtree Black tl k b) y (rbtree Black tl2 z tr2)
      -- specific case for Red with two Black subtrees
      checkR tl (rbtree Red (rbtree Black tl1 x tr1) k1 (rbtree Black tl2 y tr2)) =
        rbtree Black tl k (rbtree Red (rbtree Black tl1 x tr1) k1 (rbtree Black tl2 y tr2))
      -- missing cases for Red with empty children in various configurations
      checkR tl (rbtree Red emptyRBT y emptyRBT) =
        rbtree Black tl k (rbtree Red emptyRBT y emptyRBT)
      checkR tl (rbtree Red emptyRBT y (rbtree Black tl2 z tr2)) =
        rbtree Black tl k (rbtree Red emptyRBT y (rbtree Black tl2 z tr2))
      checkR tl (rbtree Red (rbtree Black tl1 x tr1) y emptyRBT) =
        rbtree Black tl k (rbtree Red (rbtree Black tl1 x tr1) y emptyRBT)
      -- general case for Black subtree
      checkR tl (rbtree Black tl1 x tr1) = rbtree Black tl k (rbtree Black tl1 x tr1)
      -- case for empty right subtree
      checkR tl emptyRBT = rbtree Black tl k emptyRBT

      checkL : RedBlackTree → RedBlackTree → RedBlackTree
      -- if Red Red t
      checkL (rbtree Red (rbtree Red a x b) y c) tr =
        rbtree Red (rbtree Black a x b) y c
      -- if Red t Red
      checkL (rbtree Red (a @ (rbtree Black _ _ _)) x (rbtree Red b y c)) tr =
        rbtree Red (rbtree Black a x b) y (rbtree Black c k tr)
      checkL (rbtree Red (a @ emptyRBT) x (rbtree Red b y c)) tr =
        rbtree Red (rbtree Black a x b) y (rbtree Black c k tr)
      -- otherwise check right tree
      checkL tl@(rbtree Red emptyRBT          _ (rbtree Black _ _ _))    = checkR tl
      checkL tl@(rbtree Red (rbtree Black _ _ _) _ (rbtree Black _ _ _)) = checkR tl
      checkL tl@(rbtree Red (rbtree Black _ _ _) _ emptyRBT)             = checkR tl
      checkL tl@(rbtree Red emptyRBT          _ emptyRBT)                = checkR tl
      checkL tl@(rbtree Black _ _ _)                                     = checkR tl
      checkL tl@emptyRBT                                                 = checkR tl

  ins : Key → RedBlackTree → RedBlackTree
  ins key emptyRBT            = rbtree Red emptyRBT key emptyRBT
  ins key (rbtree c tl k2 tr) with key < k2
  ... | true = balance c (ins key tl) k2 tr
  ... | false with k2 < key
  ...   | true  = balance c tl k2 (ins key tr)
  ...   | false = rbtree c tl key tr

  makeBlack : RedBlackTree → RedBlackTree
  makeBlack emptyRBT           = emptyRBT
  makeBlack (rbtree c tl k tr) = rbtree Black tl k tr

  insert : Key → RedBlackTree → RedBlackTree
  insert k t = makeBlack (ins k t)

  -- merge : RedBlackTree → RedBlackTree → RedBlackTree
  -- merge emptyRBT t = t
  -- merge t emptyRBT = t
  -- merge (rbtree Black tl1 k1 tr1) (rbtree Black tl2 k2 tr2) =
  --   balance Black (rbtree Black tl1 k1 tr1) k2 (rbtree Black tl2 k2 tr2)
  -- merge (rbtree Red tl1 k1 tr1) t2 =
  --   rbtree Red (merge tl1 t2) k1 tr1
  -- merge t1 (rbtree Red tl2 k2 tr2) =
  --   rbtree Red t1 k2 (merge tl2 tr2)

  union : RedBlackTree → RedBlackTree → RedBlackTree
  union t1 emptyRBT = t1
  union emptyRBT t2 = t2
  union (rbtree c tl k tr) t2 = insert k (union tl (union tr t2))

  remove : Key → RedBlackTree → RedBlackTree
  remove k emptyRBT = emptyRBT
  remove k (rbtree c tl k2 tr) with k < k2
  ... | true  = balance c (remove k tl) k2 tr
  ... | false with k2 < k
  ...   | true  = balance c tl k2 (remove k tr)
  ...   | false = union tl tr  -- Key matches; merge subtrees

module SetOf {A : Type} where
  open BST renaming (inorder to inorderBST ; insert to insertBST ; union to unionBST ; member? to memberBST)
  open RBT renaming (inorder to inorderRBT ; insert to insertRBT ; union to unionRBT ; member? to memberRBT)
  open LST renaming (memberL? to memberLST)

  R : BinarySearchTree → List ℕ → Type
  R bst lst = ∀ x → memberBST x bst ≡ memberLST x lst

  R' : RedBlackTree → List ℕ → Type
  R' rbt lst = ∀ x → memberRBT x rbt ≡ memberLST x lst

  -- inorder flattening
  bst-to-lst : BinarySearchTree → List ℕ
  bst-to-lst = inorderBST

  rbt-to-lst : RedBlackTree → List ℕ
  rbt-to-lst = inorderRBT

  lst-to-bst : List ℕ → BinarySearchTree
  lst-to-bst = foldr (tree emptyTree) emptyTree

  lst-to-rbt : List ℕ → RedBlackTree
  lst-to-rbt = foldr (rbtree Black emptyRBT) emptyRBT

  -- what do the above functions preserve?
  -- ordering?
  -- number of elements?
  -- membership
  -- ...
  -- they preserve R.

  or-assoc' : ∀ b₁ b₂ b₃ → b₁ or (b₂ or b₃) ≡ b₂ or (b₁ or b₃)
  or-assoc' b₁ b₂ b₃ =  b₁ or b₂ or b₃            ≡⟨ or-assoc b₁ b₂ b₃ ⟩
                        (b₁ or b₂) or b₃          ≡⟨ cong (_or b₃) (or-comm b₁ b₂) ⟩
                        (b₂ or b₁) or b₃          ≡⟨ sym (or-assoc b₂ b₁ b₃) ⟩
                        b₂ or b₁ or b₃ ∎

  lem1 : ∀ x k l1 l2 → memberLST x (l1 ++ [ k ] ++ l2) ≡ (k == x) or (memberLST x l1) or (memberLST x l2)
  lem1 x k [] l2 = refl
  lem1 x k (y ∷ ys) l2 =
    (y == x) or memberLST x (ys ++ k ∷ l2)                       ≡⟨ cong (_or_ (y == x)) (lem1 x k ys l2) ⟩
    (y == x) or (k == x) or memberLST x ys or memberLST x l2     ≡⟨ or-assoc' (y == x) (k == x) (memberLST x ys or memberLST x l2) ⟩
    (k == x) or (y == x) or memberLST x ys or memberLST x l2     ≡⟨ cong (k == x or_) (or-assoc (y == x) (memberLST x ys) (memberLST x l2)) ⟩
    (k == x) or ((y == x) or memberLST x ys) or memberLST x l2   ∎

  lem : ∀ ys → ys ≡ (inorderBST (foldr (tree emptyTree) emptyTree ys))
  lem [] = refl
  lem (y ∷ ys) = cong (y ∷_) (lem ys)

  lem3 : ∀ ls x → memberLST x ls ≡ memberBST x (foldr (tree emptyTree) emptyTree ls)
  lem3 [] x = refl
  lem3 (y ∷ ys) x with y == x
  ... | true = refl
  ... | false = memberLST x ys                                                  ≡⟨ cong (memberLST x) (lem ys) ⟩
                memberLST x (inorderBST (foldr (tree emptyTree) emptyTree ys))  ∎

  lem2' : ∀ x ys → memberRBT x (foldr (rbtree Black emptyRBT) emptyRBT ys) ≡ memberLST x (inorderRBT (foldr (rbtree Black emptyRBT) emptyRBT ys))
  lem2' x [] = refl
  lem2' x (y ∷ ys) = refl

  lem3' : ∀ ls x → memberLST x ls ≡ memberRBT x (foldr (rbtree Black emptyRBT) emptyRBT ls)
  lem3' [] x = refl
  lem3' (y ∷ ys) x with y == x
  ... | true = refl
  ... | false = memberLST x ys                                                  ≡⟨ lem3' ys x ⟩
                memberRBT x (foldr (rbtree Black emptyRBT) emptyRBT ys)         ≡⟨ lem2' x ys ⟩
                memberLST x (inorderRBT (foldr (rbtree Black emptyRBT) emptyRBT ys))  ∎

  η : ∀ bst → R bst (bst-to-lst bst)
  η emptyTree x = refl
  η (tree tl k tr) x = sym (lem1 x k (inorderBST tl) (inorderBST tr))

  η' : ∀ rbt → R' rbt (rbt-to-lst rbt)
  η' emptyRBT x = refl
  η' (rbtree _ tl k tr) x = sym (lem1 x k (inorderRBT tl) (inorderRBT tr))

  ε : ∀ lst → R (lst-to-bst lst) lst
  ε ls x = sym (lem3 ls x)

  ε' : ∀ lst → R' (lst-to-rbt lst) lst
  ε' ls x = sym (lem3' ls x)

  QuasiR : QuasiEquivRel _ _ lzero
  QuasiR .fst .fst = R
  QuasiR .fst .snd _ _ = isPropΠ λ x → isSetBool _ _
  QuasiR .snd .isQuasiEquivRel.zigzag r r' r'' a = (r a) ∙∙ sym (r' a) ∙∙ (r'' a)
  QuasiR .snd .isQuasiEquivRel.fwd a = ∣ bst-to-lst a , η a ∣₁
  QuasiR .snd .isQuasiEquivRel.bwd b = ∣ lst-to-bst b , ε b ∣₁

  QuasiR' : QuasiEquivRel _ _ lzero
  QuasiR' .fst .fst = R'
  QuasiR' .fst .snd _ _ = isPropΠ λ x → isSetBool _ _
  QuasiR' .snd .isQuasiEquivRel.zigzag r r' r'' a = (r a) ∙∙ sym (r' a) ∙∙ (r'' a)
  QuasiR' .snd .isQuasiEquivRel.fwd a = ∣ rbt-to-lst a , η' a ∣₁
  QuasiR' .snd .isQuasiEquivRel.bwd b = ∣ lst-to-rbt b , ε' b ∣₁

  module E = QER→Equiv QuasiR
  module E' = QER→Equiv QuasiR'
  open E renaming (Rᴸ to Rᴮ; Rᴿ to Rᴸ)
  open E' renaming (Rᴸ to Rᴿ; Rᴿ to Rᴸ̂)

  List/Rᴸ = (List ℕ) / Rᴸ
  List/Rᴸ̂ = (List ℕ) / Rᴸ̂

  BST/Rᴮ = BinarySearchTree / Rᴮ
  RBT/Rᴿ = RedBlackTree / Rᴿ

  List/Rᴸ≃BST/Rᴮ :  BST/Rᴮ ≃ List/Rᴸ
  List/Rᴸ≃BST/Rᴮ = E.Thm

  List/Rᴸ≃RBT/Rᴿ :  RBT/Rᴿ ≃ List/Rᴸ̂
  List/Rᴸ≃RBT/Rᴿ = E'.Thm

  𝓡 : BinarySearchTree → RedBlackTree → Type₁
  𝓡 bst rbt = ∀ lst → R bst lst ≡ R' rbt lst

  φ : BinarySearchTree → RedBlackTree
  φ bst = lst-to-rbt (bst-to-lst bst)

  ψ : RedBlackTree → BinarySearchTree
  ψ rbt = lst-to-bst (rbt-to-lst rbt)

  lem4 : ∀ bst lst → ((x : ℕ) → memberBST x bst ≡ memberLST x lst) ≡ ((x : ℕ) → memberLST x (bst-to-lst bst) ≡ memberLST x lst)
  lem4 bst lst = {!η bst!} ∙ {!ε lst!}

  lem5 : ∀ bst lst → ((x : ℕ) → memberLST x (bst-to-lst bst) ≡ memberLST x lst) ≡ ((x : ℕ) → memberRBT x (φ bst) ≡ memberLST x lst)
  lem5 bst lst = {!!}

  epsilon : ∀ bst → 𝓡 bst (φ bst)
  epsilon bst lst = ((x : ℕ) → memberBST x bst ≡ memberLST x lst) ≡⟨ lem4 bst lst ⟩
                    (((x : ℕ) → memberLST x (bst-to-lst bst) ≡ memberLST x lst) ) ≡⟨ lem5 bst lst ⟩
                    ((x : ℕ) → memberRBT x (φ bst) ≡ memberLST x lst) ∎

  lem6 : ∀ rbt lst → ((x : ℕ) → memberBST x (foldr (tree emptyTree) emptyTree (inorderRBT rbt)) ≡ memberLST x lst)
                      ≡
                     ((x : ℕ) → memberLST x (inorderBST (foldr (tree emptyTree) emptyTree (inorderRBT rbt))) ≡ memberLST x lst)
  lem6 emptyRBT lst = refl
  lem6 (rbtree c tl k tr) lst = {!!}

  lem7 : ∀ rbt lst → ((x : ℕ) → memberLST x (inorderBST (foldr (tree emptyTree) emptyTree (inorderRBT rbt))) ≡ memberLST x lst)
                     ≡ ((x : ℕ) → memberLST x (inorderRBT rbt) ≡ memberLST x lst)
  lem7 rbt lst = {!!}

  eta : ∀ lst → 𝓡 (ψ lst) lst
  eta rbt lst = ((x : ℕ) → memberBST x (foldr (tree emptyTree) emptyTree (inorderRBT rbt)) ≡ memberLST x lst) ≡⟨ lem6 rbt lst ⟩
                (((x : ℕ) → memberLST x (inorderBST (foldr (tree emptyTree) emptyTree (inorderRBT rbt))) ≡ memberLST x lst)) ≡⟨ {!!} ⟩
                ((x : ℕ) → memberLST x (inorderRBT rbt) ≡ memberLST x lst) ≡⟨ {!!} ⟩
                ((x : ℕ) → memberRBT x rbt ≡ memberLST x lst) ∎

-- compose to form a path.
-- form an interface.
-- prove stuff that inorder is sorted and ...
-- get a function to check if a BST has the needed invariant
