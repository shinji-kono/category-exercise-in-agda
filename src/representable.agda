{-# OPTIONS --cubical-compatible --safe #-}

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
open import Category.Sets 

module representable 
   where

open import HomReasoning
open import Definitions hiding (Yoneda ; Representable )
open import Relation.Binary.Core
open import Function
open import freyd2 

open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym ; resp )

-- A is localy small
-- postulate ≡←≈ :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a b : Obj A } { x y : Hom A a b } →  (x≈y : A [ x ≈ y  ]) → x ≡ y

import Axiom.Extensionality.Propositional
-- Extensionality a b = {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g → ( λ x → f x ≡ λ x → g x )
-- postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Axiom.Extensionality.Propositional.Extensionality c₂ c₂

----
--
--  Hom ( a, - ) is Object mapping in Yoneda Functor
--
----

open NTrans 
open Functor
open Limit
open IsLimit
open import Category.Cat

hom-product : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  → Functor A A
hom-product = ?
