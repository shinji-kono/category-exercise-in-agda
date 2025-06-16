{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Ordinals
open import logic
open import Relation.Nullary

open import Level
open import Ordinals
import HODBase
import OD
open import Relation.Nullary
module Sheaf {n : Level } (O : Ordinals {n})   (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
       (AC : OD.AxiomOfChoice O HODAxiom ) where


open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Binary.Definitions

open import Data.Empty

import OrdUtil

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
import ODUtil

open import logic
open import nat

open OrdUtil O
open ODUtil O HODAxiom  ho<

open _∧_
open _∨_
open Bool

open  HODBase._==_

open HODBase.ODAxiom HODAxiom  
open OD O HODAxiom

open HODBase.HOD

open AxiomOfChoice AC
open import ODC O HODAxiom AC as ODC

open import Level
open import Ordinals

open import Relation.Nullary 
-- open import Relation.Binary hiding ( _⇔_ )
open import Data.Empty 
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
import BAlgebra 

open import ZProduct O HODAxiom ho<
open import filter O HODAxiom ho< AC
open import filter-util O HODAxiom ho< AC

import Relation.Binary.Reasoning.Setoid as EqHOD

open import Topology O HODAxiom ho< AC

open Filter
open Topology

open import CCC
open import Level
open import Category
open import Definitions
open import HomReasoning
open import Data.Unit

SetsC :  Category (suc n) n Level.zero
SetsC  = record {  Obj = HOD
   ; Hom = _⊆_
   ; Id = λ {a} {e} ae → ae
   ; _o_ = λ a b → λ x → a (b x)
   ; _≈_ = λ a b → ⊤
   ; isCategory = record { isEquivalence = record { refl  = tt
      ; sym   = λ {φ ψ} → λ x → x
      ; trans = λ {φ ψ σ} → λ _ _ → tt }
      ; identityL = tt
      ; identityR = tt
      ; o-resp-≈ = λ _ _ → tt
      ; associative = tt
     }
    }

OSC : {P : HOD} (TP : Topology P) → Category _ n Level.zero
OSC {P} TP = FullSubCategory SetsC (λ x → OS TP  ∋ x )

--   module _ {P : HOD} (TP : Topology P) (small : Small n (Category.op (OSC TP))) where
--      open import yoneda (OSC TP) small
--      sheaf : Functor ? ?
--      sheaf =  ?

open import Category.Sets hiding (_==_)

Presheaf : {P : HOD} (TP : Topology P) → Set (suc (suc (suc n)))
Presheaf {P} TP = Functor (Category.op  (OSC TP)) (Sets {n})

--
--  G  
--
--     F(U)   → F(Uα) 
--       ↓       ↓
--     F(Uβ)  → F(Uα ∩ Uβ)
--
--  u  : G → F(U)
--  fα : G → F(Uα)
--  fβ : G → F(Uβ)
--

record IU {P : HOD} (TP : Topology P) (I : Set n) (Ui : I → Obj (OSC TP)) (x : Ordinal)  : Set n where
    field
       i : I
       x=Ui : x ≡ & (SObj.s (Ui i))

open Functor

is-sheaf : {P : HOD} (TP : Topology P) → (I : Set n) → (I → Obj (OSC TP)) → (a b : I) → (F : Presheaf TP)  → Set (suc n)
is-sheaf {P} TP I Ui a b F = IsPullback Sets {FObj F (Ui a)} {FObj F (Ui b)} {FObj F Uab} {FObj F U} f1 f2 f3 f4  where
    UI : HOD
    UI = record { od = record { def = λ x → IU TP I Ui x } ; odmax = & (OS TP) ; <odmax = UI-lem } where
       UI-lem : {y : Ordinal} → IU TP I Ui y → y o< & (OS TP) 
       UI-lem record { i = i ; x=Ui = refl } = odef< (SObj.p (Ui i)) 
    U : Obj (OSC TP)
    U = record { s = Union UI ; p = o∪ TP U-lem } where
        U-lem : UI ⊆ OS TP
        U-lem record { i = i ; x=Ui = x=Ui } = subst (λ k → odef (OS TP) k) (sym x=Ui) (SObj.p (Ui i))
    Uab : Obj (OSC TP)
    Uab = record { s = SObj.s (Ui a) ∩ (SObj.s (Ui b)) ; p = o∩ TP (SObj.p (Ui a)) (SObj.p (Ui b)) }
    f1 : Hom Sets (FObj F (Ui a)) (FObj F Uab)
    f1 = FMap F (λ q → proj1 q )
    f2 : Hom Sets (FObj F (Ui b)) (FObj F Uab)
    f2 = FMap F (λ q → proj2 q )
    f3 : Hom Sets (FObj F U) (FObj F (Ui a))
    f3 = FMap F f3lem  where
        f3lem : {x : Ordinal } → odef (SObj.s (Ui a)) x → odef (Union UI) x
        f3lem {x} uix = record { owner = & (SObj.s (Ui a)) ; ao = record { i = a ; x=Ui = refl } ; ox = eq← *iso uix } 
    f4 : Hom Sets (FObj F U) (FObj F (Ui b))
    f4 = FMap F f3lem  where
        f3lem : {x : Ordinal } → odef (SObj.s (Ui b)) x → odef (Union UI) x
        f3lem {x} uix = record { owner = & (SObj.s (Ui b)) ; ao = record { i = b ; x=Ui = refl } ; ox = eq← *iso uix } 











