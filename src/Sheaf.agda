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
open import Definitions
open import CCC
open import Level
open import Category
open import HomReasoning
open import Data.Unit
module Sheaf {n : Level } (O : Ordinals {n})   (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
    (AC : OD.AxiomOfChoice O HODAxiom ) 
    (FT : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (C : Category c₁ c₂ ℓ) (D : Category c₁' c₂' ℓ') {a b c : Obj C } → FreeTheorem C D  {a} {b} {c} )
       where

--
-- From Lambek , Scott, Introduction to Higher Order Categorical Logic
--    page 179  Sheaf categories and their semantics, Type theory and toposes
--

open import  Relation.Binary.PropositionalEquality hiding ( [_] ; resp )
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
-- open import Relation.Binary.PropositionalEquality
-- open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )
import BAlgebra

open import ZProduct O HODAxiom ho<
open import filter O HODAxiom ho< AC
open import filter-util O HODAxiom ho< AC

import Relation.Binary.Reasoning.Setoid as EqHOD

open import Topology O HODAxiom ho< AC

open Filter
open Topology

import Relation.Binary.Reasoning.Setoid as EqR

open Functor

UniquenessOfFunctor :  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (C : Category c₁ c₂ ℓ) (D : Category c₁' c₂' ℓ')  (F : Functor C D)
  {a b : Obj C } { f : Hom C a b } → ( fmap : {a : Obj C } {b : Obj C } → Hom C a b → Hom D (FObj F a) ( FObj F b) )
      → ( {b : Obj C } → D [ fmap  (id1 C b) ≈  id1 D (FObj F b) ] )
      → D [ fmap f ≈  FMap F f ]
UniquenessOfFunctor C D F {a} {b} {f} fmap eq = begin
        fmap f 
     ≈↑⟨ idL ⟩
        id1 D (FObj F b)  o  fmap f 
     ≈↑⟨ car ( IsFunctor.identity (isFunctor F )) ⟩
        FMap F (id1 C b)  o  fmap f 
     ≈⟨ FT C D F  fmap lem ⟩ -- (IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory C ))) ⟩ 
        fmap  (id1 C b)  o  FMap F f  
     ≈⟨ car eq ⟩
        id1 D (FObj F b)  o  FMap F f  
     ≈⟨ idL ⟩
        FMap F f 
     ∎  
   where 
       lem : C [ C [ id1 C b o f ] ≈ C [ id1 C b o f ] ]
       lem = refl-hom where open ≈-Reasoning C 
       open ≈-Reasoning D 

--
-- Category of Toplogy space and ⊆
--

SetsC :  Category (suc n) n Level.zero
SetsC  = record {  Obj = HOD
   ; Hom = _⊆_
   ; Id = λ {a} ae → ae
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


--
-- Category of Topology Space and Continuous Functions
--

record TopObj : Set (suc n) where
   field
     space : HOD
     topology : Topology space

open TopObj

-- FuncID : (a : HOD) → Func a a
-- FuncID a = record { func = λ {x} ax → x
--           ; is-func = λ {x} ax → ax
--           ; func-wld = λ _ _ eq → eq }

IMFuncID : (a x : HOD) → x ⊆ a → x =h= HODInverseImage (FuncID a) (& x)
IMFuncID a x x⊆a = record { eq→ = λ lt → imf00 _ lt  ; eq← = imf01 } where
   imf00 : (y : Ordinal) → odef x y → odef (HODInverseImage (FuncID a) (& x)) y
   imf00 y xy = record { y∈P = x⊆a xy ; is-inverse = eq← *iso xy  }
   imf01 : {y : Ordinal} → odef (HODInverseImage (FuncID a) (& x)) y → odef x y
   imf01 {y} record { y∈P = y∈P ; is-inverse = rev } = eq→  *iso rev


import Relation.Binary.Reasoning.Setoid as EqR

IdTop : (a : TopObj) →  ContFunc (topology a) (topology a)
IdTop a = record {
       func = FuncID (space a)
     ; continuous = λ {x} ax → subst (λ k → odef (OS (topology a)) k ) (lem _ ax) ax
  } where
     lem : (x : Ordinal) → odef (OS (topology a)) x → x ≡ & (HODInverseImage (FuncID (space a)) x)
     lem x ax = trans (sym &iso) ( ==→o≡ ( begin
        * x ≈⟨ IMFuncID (space a) (* x) lem00 ⟩
        HODInverseImage (FuncID (space a)) (& (* x))  ≈⟨ ord→== ( cong (λ k → & (HODInverseImage (FuncID (space a)) k ) ) &iso)  ⟩
        HODInverseImage (FuncID (space a)) x  ∎  ) )
        where
             open EqR ==-Setoid
             lem00 : * x ⊆ space a
             lem00 {y} lt = OS⊆PL (topology a) ax _ lt

TopComp : {a b c : TopObj} →  (f : ContFunc (topology b) (topology c)) →  (g : ContFunc (topology a) (topology b)) →   ContFunc (topology a) (topology c)
TopComp {a} {b} {c} f g = record {
       func = record { func = λ {x} ax → Func.func (ContFunc.func f) (Func.is-func (ContFunc.func g) ax)
          ; is-func = λ {x} ax →  Func.is-func (ContFunc.func f) (Func.is-func (ContFunc.func g) ax)
          ; func-wld = λ {x y} ax ay eq → Func.func-wld (ContFunc.func f) (Func.is-func (ContFunc.func g) ax) (Func.is-func (ContFunc.func g) ay)
             (Func.func-wld (ContFunc.func g) ax ay eq)
          }
     ; continuous = λ {x} cx → subst (λ k → odef (OS (topology a)) k ) (cont-eq cx) ( ContFunc.continuous g (ContFunc.continuous f cx )  )
  } where
     comp-func : Func (space a) (space c)
     comp-func =  record { func = λ {x} ax → Func.func (ContFunc.func f) (Func.is-func (ContFunc.func g) ax)
          ; is-func = λ {x} ax →  Func.is-func (ContFunc.func f) (Func.is-func (ContFunc.func g) ax)
          ; func-wld = λ {x y} ax ay eq → Func.func-wld (ContFunc.func f) (Func.is-func (ContFunc.func g) ax) (Func.is-func (ContFunc.func g) ay)
             (Func.func-wld (ContFunc.func g) ax ay eq)
          }
     cont-eq : {x : Ordinal} → (cx : odef (OS (topology c)) x) →
        & ( (HODInverseImage (ContFunc.func g) (& (HODInverseImage (ContFunc.func f) x)))) ≡ & (HODInverseImage comp-func x )
     cont-eq {x} cx = ==→o≡ record {
           eq→ = λ {y} lt → record { y∈P = InverseImage.y∈P lt ; is-inverse = lem00 y lt }
         ; eq← = λ {y} lt → record { y∈P = InverseImage.y∈P lt ; is-inverse = lem10 y lt }
        } where
            lem00 : (y : Ordinal) → (lt : odef ( HODInverseImage (ContFunc.func g) (& (HODInverseImage (ContFunc.func f) x))) y  )
               →  odef (* x) (Func.func (ContFunc.func f) (Func.is-func (ContFunc.func g) (InverseImage.y∈P lt)))
            lem00 y lt = lem02 where
               lem06 : odef (space a) y
               lem06 = InverseImage.y∈P lt
               lem01 : odef (HODInverseImage (ContFunc.func f) x) (Func.func (ContFunc.func g) (InverseImage.y∈P lt))
               lem01 = eq→  *iso (InverseImage.is-inverse lt)
               lem02 : odef (* x) (Func.func (ContFunc.func f) (Func.is-func (ContFunc.func g) (InverseImage.y∈P lt)))
               lem02 = subst (λ k → odef (* x) k) (Func.func-wld (ContFunc.func f)
                   (InverseImage.y∈P (eq→ *iso (InverseImage.is-inverse lt)))  (Func.is-func (ContFunc.func g) lem06)  refl) ( InverseImage.is-inverse lem01 )
            lem10 : (y : Ordinal) → (lt : odef (HODInverseImage comp-func x) y )
                    →  odef (* (& (HODInverseImage (ContFunc.func f) x))) (Func.func (ContFunc.func g) (InverseImage.y∈P lt))
            lem10 y lt = eq← *iso record { y∈P = Func.is-func (ContFunc.func g) lem11  ; is-inverse = lem13 }  where
               lem11 : odef (space a) y
               lem11 = InverseImage.y∈P lt
               lem13 : odef (* x) (Func.func (ContFunc.func f) (Func.is-func (ContFunc.func g) lem11))
               lem13 = InverseImage.is-inverse lt

top : Category (suc n) n n
top = record { Obj = TopObj
   ; Hom = λ a b → ContFunc (topology a ) (topology b )
   ; Id = λ {a} → IdTop a
   ; _o_ = λ a b → TopComp a b
   ; _≈_ = λ {A} {B} a b → (x : Ordinal) → (ax : odef (space A) x ) → FuncEQ (ContFunc.func a) (ContFunc.func b) x ax
   ; isCategory = record { isEquivalence = record { refl  = λ {f} → FE-refl (ContFunc.func f)
      ; sym   = λ {φ ψ} eq x ax → FE-sym (ContFunc.func φ) (ContFunc.func ψ) x ax (eq x ax)
      ; trans = λ {φ ψ σ} f=g g=h x ax → FE-trans  (ContFunc.func φ) (ContFunc.func ψ) (ContFunc.func σ) x ax (f=g x ax) (g=h x ax)}
      ; identityL = λ {A} {B} {f} x ax → refl
      ; identityR = λ {A} {B} {f} x ax → refl
      ; o-resp-≈ = λ {A} {B} {C} {f} {g} {h} {i} → o-resp  {A} {B} {C} {f} {g} {h} {i}
      ; associative = λ {A B C D} {f} {g} {h} → assoc {A} { B} { C} { D} {f} {g} {h}
     }
    } where
        o-resp : {A B C : TopObj} {f g : ContFunc (topology A) (topology B)} {h i : ContFunc (topology B) (topology C)}
           → ((x : Ordinal) (ax : odef (space A) x) → FuncEQ (ContFunc.func f) (ContFunc.func g) x ax)
           → ((x : Ordinal) (ax : odef (space B) x) → FuncEQ (ContFunc.func h) (ContFunc.func i) x ax)
           → (x : Ordinal) (ax : odef (space A) x) → FuncEQ (ContFunc.func (TopComp h f)) (ContFunc.func (TopComp i g)) x ax
        o-resp {A} {B} {C} {f} {g} {h} {i} f=g h=i x ax = begin
            Func.func (ContFunc.func h) (Func.is-func (ContFunc.func f) ax)  ≡⟨ Func.func-wld (ContFunc.func h) _ _ (f=g x ax) ⟩

            Func.func (ContFunc.func h) (Func.is-func (ContFunc.func g) ax)  ≡⟨ h=i (Func.func (ContFunc.func g) ax) (Func.is-func (ContFunc.func g) ax) ⟩
            Func.func (ContFunc.func i) (Func.is-func (ContFunc.func g) ax)   ∎ where open ≡-Reasoning
        assoc : {A B C D : TopObj} {f : ContFunc (topology C) (topology D)}
            {g : ContFunc (topology B) (topology C)} {h : ContFunc (topology A) (topology B)} (x : Ordinal)
            (ax : odef (space A) x) → FuncEQ (ContFunc.func (TopComp f (TopComp g h))) (ContFunc.func (TopComp (TopComp f g) h)) x ax
        assoc {A} {B} {C} {D} {f} {g} {h} x ax = refl

--
-- Sets defined in HOD
--

HODSets : Category (suc n) n n
HODSets  = record { Obj = HOD
   ; Hom = λ a b → Func a b
   ; Id = λ {a} → FuncID a
   ; _o_ = λ a b → record { func = λ {x} ax → Func.func a (Func.is-func b ax)
          ; is-func = λ {x} ax → Func.is-func a (Func.is-func b ax)
          ; func-wld = λ {x y} ax ay eq → Func.func-wld a (Func.is-func b ax) (Func.is-func b ay)
             (Func.func-wld b ax ay eq)
          }
   ; _≈_ = λ {A} {B} a b → (x : Ordinal) → (ax : odef A x ) → FuncEQ a b x ax
   ; isCategory = record { isEquivalence = record { refl  = λ {f} → FE-refl f
      ; sym   = λ {φ ψ} eq x ax → FE-sym φ ψ x ax (eq x ax)
      ; trans = λ {φ ψ σ} f=g g=h x ax → FE-trans  φ ψ σ x ax (f=g x ax) (g=h x ax)}
      ; identityL = λ {A} {B} {f} x ax → refl
      ; identityR = λ {A} {B} {f} x ax → refl
      ; o-resp-≈ = λ {A} {B} {C} {f} {g} {h} {i} f=g h=i x ax  → trans (Func.func-wld h _ _ (f=g x ax)) ( h=i (Func.func g ax) (Func.is-func g ax ) )
      ; associative = λ {A B C D} {f} {g} {h} x ax → refl
     }
    }

open NTrans

HODSetsAop :  {c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) →  Category (suc (suc n) ⊔ suc c₁ ⊔ suc c₂ ⊔ suc ℓ)  (suc (suc n) ⊔ suc c₁ ⊔ suc c₂ ⊔ suc ℓ) (n ⊔ c₁)
HODSetsAop {c₁} {c₂} {ℓ } A = record { Obj = YObj
         ; Hom = YHom
         ; _o_ = _+_
         ; _≈_ = _=d=_
         ; Id  = Yid
         ; isCategory = record  {
              isEquivalence =  record {refl = λ {i} x ax → refl  ; trans = λ {i} {j} {k} → trans1 {_} {_} {i} {j} {k}  ; sym = λ {i j} → sym1 {_} {_} {i} {j}}
            ; identityL = λ {a} {b} {f} y ay  → refl
            ; identityR = λ {a} {b} {f} y ay  → refl
            ; o-resp-≈ =  λ{a b c f g h i } → o-resp-≈      {a} {b} {c} {f} {g} {h} {i}
            ; associative = λ {a b c d f g h} y ay  → refl
        } } where
            YObj : Set (suc (suc n) ⊔ suc c₁ ⊔ suc c₂ ⊔ suc ℓ)
            YObj  = Functor (Category.op A) HODSets
            YHom : ( f : YObj  ) → (g : YObj  ) →  Set (suc (suc n) ⊔ suc c₁ ⊔ suc c₂ ⊔ suc ℓ)
            YHom  f g = NTrans (Category.op A) HODSets f g

            Yid : {a : YObj } → YHom a a
            Yid {a} = record { TMap = λ b → FuncID (FObj a b) ; isNTrans = isNTrans1 {a} } where
               isNTrans1 : {a : YObj } → IsNTrans (Category.op A) (HODSets ) a a (λ b → FuncID (FObj a b) )
               isNTrans1 {a} = record { commute = λ {a} {b} {f} x ax → refl }

            _+_ : {a b c : YObj} → YHom b c → YHom a b → YHom a c
            _+_ {a} {b} {c} f g  =
                   record { TMap = λ x → HODSets [ TMap f x o TMap g x ]
                 ; isNTrans = record { commute = λ {a₁ b₁ h} → commute1 a b c f g a₁ b₁ h }  } where
               commute1 :  (a b c : YObj ) (f : YHom b c)  (g : YHom a b )
                        (a₁ b₁ : Obj (Category.op A)) (h : Hom (Category.op A) a₁ b₁) →
                                    HODSets [ HODSets [ FMap c h o HODSets [ TMap f a₁ o TMap g a₁ ] ] ≈
                                    HODSets [ HODSets [ TMap f b₁ o TMap g b₁ ] o FMap a h ] ]
               commute1  a b c f g a₁ b₁ h =  begin
                    FMap c h  o ( TMap f a₁ o TMap g a₁ )  ≈⟨ assoc {_} {_} {_} {_} {FMap c h } {TMap f a₁} {TMap g a₁}  ⟩
                    ( FMap c h o TMap f a₁ ) o TMap g a₁  ≈⟨ car {FObj b a₁} {_} {_} {FMap c h o TMap f a₁} {TMap f b₁ o FMap b h} {TMap g a₁} (nat f) ⟩
                    ( TMap f b₁ o FMap b h ) o TMap g a₁  ≈↑⟨ assoc {_} {_} {_} {_} { TMap f b₁} {FMap b h } {TMap g a₁}⟩
                    TMap f b₁ o ( FMap b h  o TMap g a₁ )  ≈⟨ cdr {FObj a a₁} {_} {_} {FMap b h o TMap g a₁} {TMap g b₁ o FMap a h} { TMap f b₁} (nat g) ⟩
                    TMap f b₁ o ( TMap g b₁  o FMap a h )  ≈↑⟨ assoc  {_} {_} {_} {_} {TMap f b₁} {TMap g b₁} { FMap a h}  ⟩
                    ( TMap f b₁ o TMap g b₁ ) o FMap a h ∎
                       where open ≈-Reasoning HODSets

            _=d=_  :  {a b : YObj} → YHom a b → YHom a b → Set (n ⊔ c₁)
            _=d=_  f g = ∀{x : Obj (Category.op A)} → HODSets [ TMap f x ≈ TMap g x ]

            sym1 : {a b : YObj } {i j : YHom a b } → i =d= j → j =d= i
            sym1 {a} {b} {i} {j} eq {x} y ay = sym (eq {x} y ay)
            trans1 : {a b : YObj } {i j k : YHom a b} → i =d= j → j =d= k → i =d= k
            trans1 {a} {b} {i} {j} {k} i=j j=k {x} y ay =  trans (i=j _ ay ) (j=k _ ay )
            o-resp-≈ : {A₁ B C : YObj} {f g : YHom A₁ B} {h i : YHom B C} →
                f =d= g → h =d= i → (h + f) =d= (i + g)
            o-resp-≈ {a} {b} {c} {f} {g} {h} {i} f=g h=i {x} y ay = trans (h=i _ lem01 ) (Func.func-wld (TMap i x) lem01 lem02 (f=g y ay)) where
                lem01 : odef (FObj b x) (Func.func (TMap f x) ay)
                lem01 = Func.is-func (TMap f x) ay
                lem02 : odef (FObj b x) (Func.func (TMap g x) ay)
                lem02 = Func.is-func (TMap g x) ay

--
-- Contravariant functor from OSC to HOD-Sets
--
HOD-OSCA : {P : HOD} (TP : Topology P) →  Category (suc (suc (suc n))) (suc (suc (suc n))) (suc (suc n))
HOD-OSCA {P} TP = HODSetsAop (OSC TP)


--
-- Slice Category of top
--
open import Category.Constructions.Slice

topX : (X : Obj top) → Category (n ⊔ suc n) (n ⊔ suc n) n
topX X =  top / X

--    Definition of Sheaf
---   https://qiita.com/9_ties/items/30fe2f48f8727adf70c1

HODPresheaf : {P : HOD} (TP : Topology P) → Set (suc (suc (suc n)))
HODPresheaf {P} TP = Functor (Category.op  (OSC TP)) HODSets

record IU {P : HOD} (TP : Topology P) (I : Set n) (Ui : I → Obj (OSC TP)) (x : Ordinal)  : Set n where
    field
       i : I
       x=Ui : x ≡ & (SObj.s (Ui i))

module Is-sheaf {P : HOD} (TP : Topology P)  (I : Set n)  (Ui : I → Obj (OSC TP))  (F : HODPresheaf TP) where

    UI : HOD
    UI = record { od = record { def = λ x → IU TP I Ui x } ; odmax = & (OS TP) ; <odmax = UI-lem } where
       UI-lem : {y : Ordinal} → IU TP I Ui y → y o< & (OS TP)
       UI-lem record { i = i ; x=Ui = refl } = odef< (SObj.p (Ui i))
    U : Obj (OSC TP)
    U = record { s = Union UI ; p = o∪ TP U-lem } where
        U-lem : UI ⊆ OS TP
        U-lem record { i = i ; x=Ui = x=Ui } = subst (λ k → odef (OS TP) k) (sym x=Ui) (SObj.p (Ui i))
    Uab : (a b : I) → Obj (OSC TP)
    Uab a b = record { s = SObj.s (Ui a) ∩ (SObj.s (Ui b)) ; p = o∩ TP (SObj.p (Ui a)) (SObj.p (Ui b)) }
    Ui⊆UI : {x : Ordinal } → (a : I) → odef (SObj.s (Ui a)) x → odef (Union UI) x
    Ui⊆UI {x} a uix = record { owner = & (SObj.s (Ui a)) ; ao = record { i = a ; x=Ui = refl } ; ox = eq← *iso uix }
    f1 : (a b : I) → Hom HODSets (FObj F (Ui a)) (FObj F (Uab a b))
    f1 a b = FMap F (λ q → proj1 q )
    f2 : (a b : I) → Hom HODSets (FObj F (Ui b)) (FObj F (Uab a b ))
    f2 a b = FMap F (λ q → proj2 q )
    f3 : (a b : I) → Hom HODSets (FObj F U) (FObj F (Ui a))
    f3 a b = FMap F (Ui⊆UI a)
    f4 : (a b : I) → Hom HODSets (FObj F U) (FObj F (Ui b))
    f4 a b = FMap F (Ui⊆UI b)

    -- Is-sheaf-1 : (a b : I) →  Set (suc n)
    -- Is-sheaf-1 a b = IsPullback HODSets {FObj F (Ui a)} {FObj F (Ui b)} {FObj F (Uab a b)} {FObj F U} (f1 a b ) (f2 a b ) (f3 a b ) (f4 a b )

    -- we cannot use Pullback directly because the limit is shared by all parwises
    -- and we cannot write it in HOD form easily in Equalizer. So we copy and modify the pull back

    record IsMultiPullback {a : I → Obj HODSets} {ab : Obj HODSets} {c : (i j : I) → Obj HODSets}
          ( f : (i j : I) → Hom HODSets (a i) (c i j ))    ( g : (i j : I )→ Hom HODSets (a j) (c i j) )
          ( π1 : (i : I) → Hom HODSets ab (a i))
             : Set  (suc n) where
       A = HODSets
       field
          commute : (i j : I) → A [ A [ f i j o π1 i ] ≈ A [ g i j o π1 j ] ]
          pullback : { d : Obj A } → { π1' : (i : I) → Hom A d (a i) }
             → (eq : (i j : I) → A [ A [ f i j o π1' i ] ≈ A [ g i j o π1' j ] ]) → Hom A d ab
          π1p=π1 :  { d : Obj A } → { π1' : (i : I ) → Hom A d (a i)}
                 → (eq : (i j : I) → A [ A [ f i j o π1' i ] ≈ A [ g i j o π1' j ] ])
                 →  (i : I) → A [ A [ π1 i  o pullback {_} {π1'}  eq ] ≈  π1' i ]
          uniqueness : { d : Obj A } → ( p' : Hom A d ab ) → ( π1' : (i : I) → Hom A d (a i) )
                 → (eq : (i j : I) → A [ A [ f i j o π1' i ] ≈ A [ g i j o π1' j ] ])
                 →  ( π1p=π1' : (i : I) → A [ A [ π1  i o p'  ] ≈  π1' i ] )
                 →  A [ pullback {_} {π1'}  eq  ≈ p' ]

    Is-sheaf : Set (suc n)
    Is-sheaf = IsMultiPullback {λ a → FObj F (Ui a)}
        {FObj F U} {λ a b → FObj F (Uab a b)}  f1 f2   (λ a → FMap F (Ui⊆UI a))

--   -- Π (FObj F (Ui a))
--   -- Π (FObj F (Uiab a b))
--
--   Is-sheaf : Set (suc n)
--   Is-sheaf = Equalizer HODSets p1 p2
--
-- The adjoint functor Γ : top / X → OSCA (topology X) s
--
--
-- Γ(p)(U) ≡ {s : U → Y | ps = incl(U/X) }
--

record ΓCont {U Y X : HOD} (TU :  Topology U) (TY : Topology Y) (TX : Topology X) (p : ContFunc TY TX ) (x : Ordinal) : Set n where
   field
     s : ContFunc TU TY
     x=func : & ( F→FuncHOD ( ContFunc.func s)) ≡ x
     inclusion : {x : Ordinal } → (ux :  odef U x ) → ( Func.func (ContFunc.func p) (Func.is-func (ContFunc.func s) ux )) ≡ x
   s-injection : {x y : Ordinal } → (ux :  odef U x ) (uy :  odef U y ) → Func.func (ContFunc.func s) ux ≡ Func.func (ContFunc.func s) uy → x ≡ y
   s-injection {x} ux uy eq = trans (sym (inclusion ux)) (trans (Func.func-wld (ContFunc.func p) _ _ eq ) (inclusion uy))

ΓCont-eq : {U Y X : HOD} {TU :  Topology U} {TY : Topology Y} {TX : Topology X} {p : ContFunc TY TX } {x y : Ordinal}
    → (gx : ΓCont TU TY TX p x ) → (gy : ΓCont TU TY TX p y ) → x ≡ y → (z : Ordinal) → (uz : odef U z)
    → FuncEQ (ContFunc.func (ΓCont.s gx)) (ContFunc.func (ΓCont.s gy)) z uz
ΓCont-eq gx gy x=y z uz = F→FuncHOD-EQ (ContFunc.func (ΓCont.s gx)) (ContFunc.func (ΓCont.s gy))
    (ord→==  (trans (ΓCont.x=func gx) (trans x=y (sym (ΓCont.x=func gy)) ))) z uz

module HODShAdjoint (X : Obj top) where

       OX = Category.op (OSC (topology X))

       Γo : (p : Obj (top / X)) → Obj (Category.op (OSC (topology X))) → Obj HODSets
       Γo p record { s = U ; p = oU } = record { od = record { def = λ x →
           ΓCont  (SubTopology (topology X) U⊆SX ) (topology (SliceObj.X p)) (topology X) (SliceObj.arrow p) x } ; odmax = _ ; <odmax = lem  } where
             U⊆SX : U ⊆  space X
             U⊆SX = os⊆L (topology X) oU
             lem :  {y : Ordinal} → (hdc : ΓCont (SubTopology (topology X) U⊆SX) (topology (SliceObj.X p)) (topology X) (SliceObj.arrow p) y )
                → y o< (& (Funcs U (space (SliceObj.X p))))
             lem {y} hdc = record-hod1 (ΓCont.x=func hdc) (Funcs∋FuncHOD {_} {_} {ContFunc.func (ΓCont.s hdc)} )

       dfunc : (p : Obj (top / X)) → {a b : Obj OX}
           → (b⊆a : Hom OX a b )
           → {y : Ordinal} → odef (Γo p a) y → Func (SObj.s b) (space (SliceObj.X p))
       dfunc p b⊆a gpa = record { func = λ {x} dx → Func.func (ContFunc.func (ΓCont.s gpa) ) (b⊆a dx)
              ; is-func = λ {x} dx → Func.is-func (ContFunc.func (ΓCont.s gpa)) (b⊆a dx)
                  ; func-wld = λ {x} {y} dx dy → Func.func-wld (ContFunc.func (ΓCont.s gpa)) (b⊆a dx) (b⊆a dy)  }

       dfunc-eq : (p : Obj (top / X)) → {a b : Obj OX}
           → (b⊆a b⊆a' : Hom OX a b )
           → {y : Ordinal} → (oy : odef (Γo p a) y) → (x : Ordinal) → (bx : odef (SObj.s b) x) → FuncEQ  (dfunc p {a} {b} b⊆a oy) (dfunc p {a} {b} b⊆a' oy) _ bx
       dfunc-eq p {a} {b} b⊆a b⊆a' {y} oy x bx = begin
           Func.func (ContFunc.func (ΓCont.s oy)) (b⊆a bx) ≡⟨
                Func.func-wld (ContFunc.func (ΓCont.s oy)) (b⊆a bx) (b⊆a' bx) refl ⟩
           Func.func (ContFunc.func (ΓCont.s oy)) (b⊆a' bx) ∎ where open ≡-Reasoning

       SO⊆SX : (b : Obj OX) → SObj.s b ⊆ space X
       SO⊆SX b = os⊆L (topology X) (SObj.p b)

       Γo-dcontinuous : (p : Obj (top / X)) → {a b : Obj OX}
          → (b⊆a : Hom OX a b )
          → {y : Ordinal} → (gpa : odef (Γo p a) y ) → {x : Ordinal} → odef (OS (topology (SliceObj.X p))) x →
                        odef (OS (SubTopology {SObj.s b} (topology X) (SO⊆SX b))) (& (HODInverseImage (dfunc p {a} {b} b⊆a gpa) x))
       Γo-dcontinuous p {a} {b} b⊆a gpa {x} cx = record { R = SubElement.R scont ; OR = SubElement.OR scont ; x=R = ==→o≡ lem00 } where
               scont : odef (OS (SubTopology {SObj.s a} (topology X) (SO⊆SX a) )) (& (HODInverseImage (ContFunc.func (ΓCont.s gpa )) x))
               scont = ContFunc.continuous (ΓCont.s gpa) cx
               lem01 : HODInverseImage (ContFunc.func (ΓCont.s gpa )) x =h= (* (SubElement.R scont) ∩ SObj.s a)
               lem01 = ord→== ( SubElement.x=R scont )
               lem00 : HODInverseImage (dfunc p {a} {b} b⊆a gpa) x =h= (* (SubElement.R scont) ∩ SObj.s b)
               lem00 = record {
                   eq→ = λ {y} lt → ⟪ proj1 ( eq→ lem01 record { y∈P = b⊆a (InverseImage.y∈P lt) ; is-inverse
                      = InverseImage.is-inverse lt } )  , InverseImage.y∈P lt ⟫
                ;  eq← = λ {y} lt → record { y∈P = proj2 lt  ; is-inverse
                    = subst (λ k → odef (* x) k) (Func.func-wld (ContFunc.func (ΓCont.s gpa )) _ _ refl
                       ) (InverseImage.is-inverse (eq← lem01 ⟪ proj1 lt , b⊆a (proj2 lt) ⟫)) }
                }
       Γo-⊆ : (p : Obj (top / X)) → {a b : Obj OX} → (b⊆a : ((SObj.s b) ⊆ (SObj.s a)) )
           → { q : Ordinal } → (qs : odef (Γo p a) q ) → odef (Γo p b) (& (F→FuncHOD (dfunc p {a} {b} b⊆a qs)))
       Γo-⊆ p {a} {b}  b⊆a {q} qs = record { s = record { func = dfunc p {a} {b} b⊆a qs ; continuous =  Γo-dcontinuous p {a} {b} b⊆a qs }
            ; x=func = refl ; inclusion = λ ux → trans (Func.func-wld (ContFunc.func (SliceObj.arrow p)) _ _ refl) (ΓCont.inclusion qs (b⊆a ux )  )  }

       Γo-wld : (p : Obj (top / X)) → {x y : Ordinal } → {a : Obj OX}
           → (ax : odef (Γo p a)  x) → (ay : odef (Γo p a)  y)
           → x ≡ y
           → top [ ΓCont.s ax ≈ ΓCont.s ay ]
       Γo-wld p {x} {y} ax ay eq _ = FuncHOD-EQ lem00 lem01 (trans (ΓCont.x=func ax) (trans eq (sym (ΓCont.x=func ay) ) ))  where
            lem00 : FuncHOD _ _ (& (F→FuncHOD ( ContFunc.func (ΓCont.s ax))))
            lem00 = felm ( ContFunc.func (ΓCont.s ax))
            lem01 : FuncHOD _ _ (& (F→FuncHOD ( ContFunc.func (ΓCont.s ay))))
            lem01 = felm ( ContFunc.func (ΓCont.s ay))

       Γm : (p : Obj (top / X)) → {A B : Obj OX} → Hom OX A B → Hom HODSets (Γo p A) (Γo p B)
       Γm p {a} {b} b⊆a = record {
                 func = λ qs → & (F→FuncHOD (dfunc p {a} {b} b⊆a qs) )
               ; is-func = Γo-⊆ p {a} {b} b⊆a
               ; func-wld = lem02
             } where
           lem02 : {x y : Ordinal} (ax : odef (Γo p a) x) (ay : odef (Γo p a) y) → x ≡ y
               →  & (F→FuncHOD (dfunc p {a} {b} b⊆a ax)) ≡ & (F→FuncHOD (dfunc p {a} {b} b⊆a ay))
           lem02  {x} {y} ax ay eq = ==→o≡ ( FuncEQ→HODEQ (dfunc p {a} {b} b⊆a  ax) (dfunc p {a} {b} b⊆a ay) lem10 )  where
                -- lem10 it will take long time to check, so we need abstract
               abstract
                   lem10 : (z : Ordinal) (az : odef (SObj.s b) z) → FuncEQ (dfunc p {a} {b} b⊆a ax) (dfunc p {a} {b} b⊆a ay) z az
                   lem10 z az = begin
                      Func.func (dfunc p {a} {b} b⊆a ax) az  ≡⟨ ΓCont-eq ax ay eq z (b⊆a az) ⟩
                      Func.func (dfunc p {a} {b} b⊆a ay) az  ∎  where open ≡-Reasoning

       ΓObj : Obj ( top / X ) → Obj (HOD-OSCA (topology X) )
       ΓObj p = record { FObj = Γo p ; FMap = λ {a} {b} f → Γm p {a} {b} f ; isFunctor = record {
             ≈-cong = λ {a} {b} {f} {g} f=g → cong1 {a} {b} {f} {g} f=g
          ;  identity = λ {a} → identity1 a
          ;  distr = λ {a} {b} {c} {f} {g} → distr {a} {b} {c} {f} {g}
         } } where
           cong1 :  {A B : Obj OX} {f g : Hom OX A B}
             → ⊤ → HODSets [ Γm p {A} {B} f ≈ Γm p {A} {B} g ]
             -- → Category.op (OSC (topology X)) [ f ≈ g ] → HODSets [ Γm p {A} {B} f ≈ Γm p {A} {B} g ]
           cong1 {a} {b} {f} {g} f=g q sq = lem01 sq where
               lem00 : {z : Ordinal } → (oz : odef (Γo p a) z) → (w : Ordinal) → (ow :  odef (SObj.s b) w)
                  → FuncEQ (dfunc p {a} {b} f oz) (dfunc p {a} {b} g oz)  w ow
               lem00 {z} oz w ow = dfunc-eq p {a} {b} f g oz w ow
               lem01 :  {q : Ordinal } → (sq : odef (Γo p a) q)  → FuncEQ (Γm p {a} {b} f) (Γm p {a} {b} g) q sq
               lem01 {q} sq = ==→o≡ ( FuncEQ→HODEQ (dfunc p {a} {b} f sq) (dfunc p {a} {b} g sq) (lem00 sq)  )
           identity1 :  (a : Obj OX) → HODSets [ Γm p {a} {a} (id1 OX a) ≈ id1 HODSets  (Γo p a) ]
           identity1 a q sq = trans (==→o≡ ( FuncEQ→HODEQ (dfunc p {a} {a} (λ x → x) sq) id01 id02  )) (ΓCont.x=func sq) where
                id01 :  Func (SObj.s a) (space (SliceObj.X p))
                id01 = ContFunc.func (ΓCont.s sq)
                id02 :  (x : Ordinal) (ax : odef (SObj.s a) x) → FuncEQ (dfunc p {a} {a} (λ x₁ → x₁) sq) id01 x ax
                id02 x ax = Func.func-wld (ContFunc.func (ΓCont.s sq)) ax ax refl
           distr :  {a b c : Obj OX} {f : Hom OX a b} {g : Hom OX b c} →
                HODSets [ Γm p {a} {c} (λ x → f (g x)) ≈ HODSets [ Γm p {b} {c} g o Γm p {a} {b} f ] ]
           distr {a} {b} {c} {f} {g} q sq = ==→o≡ ( FuncEQ→HODEQ id01 id03 (λ x ax → (
                  begin
                  Func.func id01 ax ≡⟨ refl ⟩
                  Func.func (ContFunc.func (ΓCont.s sq) ) (f (g ax))  ∎ ))) where
                open ≡-Reasoning
                id01 :  Func (SObj.s c) (space (SliceObj.X p))
                id01  = dfunc p {a} {c} (λ x → f (g x)) sq
                id04 : (b⊆a : ((SObj.s b) ⊆ (SObj.s a))) → (qs : odef (Γo p a) q) → odef (Γo p b) (& (F→FuncHOD (dfunc p {a} {b} b⊆a qs)))
                id04 b⊆a qs =  Γo-⊆ p {a} {b}  b⊆a {q} qs
                id03 :  Func (SObj.s c) (space (SliceObj.X p))
                id03  = dfunc p {b} {c} g (id04 f sq)

       ΓTMap : {a b : Obj (top / X)} → (f : Hom (top / X) a b) → (A : Obj OX) → Hom HODSets (Γo a A) (Γo b A)
       ΓTMap {a} {b} f A = record {
                 func = lem00
               ; is-func = lem01
               ; func-wld = λ {x} {y} ax ay eq →  ==→o≡ (FuncEQ→HODEQ (ContFunc.func (lem02 ax)) (ContFunc.func (lem02 ay)) (lem03 ax ay eq))
             } where
           af : ContFunc (topology (SliceObj.X a)) (topology X)
           af  = SliceObj.arrow a
           bf : ContFunc (topology (SliceObj.X b)) (topology X)
           bf  = SliceObj.arrow b
           ff : ContFunc (topology (SliceObj.X a)) (topology (SliceObj.X b))
           ff = _⟶_.arrow f
           fp : top [ af ≈ top [ bf o ff ] ]
           fp = _⟶_.proof f
           gs : {y : Ordinal} → (gpa : odef (Γo a A) y) → ContFunc (SubTopology {SObj.s A} (topology X) (SO⊆SX A)) (topology (SliceObj.X a ))
           gs gpa = ΓCont.s gpa
           gd : {y : Ordinal } → (gpa : odef (Γo a A) y) → ContFunc (SubTopology {SObj.s A} (topology X) (SO⊆SX A) ) (topology (SliceObj.X b ))
           gd gpa = top [ _⟶_.arrow f o ΓCont.s gpa ]
           gs-incl : {y : Ordinal } → (gpa : odef (Γo a A) y ) → {x : Ordinal} (ux : odef (SObj.s A) x) → Func.func (ContFunc.func (SliceObj.arrow a))
              (Func.is-func (ContFunc.func (gs gpa)) ux ) ≡ x
           gs-incl gpa = ΓCont.inclusion gpa
           lem02 : {x : Ordinal} → odef (Γo a A) x →  ContFunc (SubTopology {SObj.s A} (topology X) (SO⊆SX A)  ) (topology (SliceObj.X b))
           lem02 {x} gpa = top [ _⟶_.arrow f o ΓCont.s gpa ]
           lem00 : {x : Ordinal} → odef (Γo a A) x → Ordinal
           lem00 {x} gpa = & (F→FuncHOD (ContFunc.func (lem02 gpa)))
           lem01 : {x : Ordinal} (ax : odef (Γo a A) x) → odef (Γo b A) (lem00 ax)
           lem01 {x} gpa = record { s = record { func = ContFunc.func (lem02 gpa) ; continuous =  ContFunc.continuous (lem02 gpa) }
            ; x=func = refl ; inclusion = λ {y} uy → begin
               Func.func (ContFunc.func (SliceObj.arrow b)) (Func.is-func (ContFunc.func (lem02 gpa)) uy)  ≡⟨⟩
               Func.func (ContFunc.func (SliceObj.arrow b)) (Func.is-func (ContFunc.func ff) (Func.is-func (ContFunc.func (gs gpa)) uy))
                  ≡⟨ sym (fp _ (Func.is-func (ContFunc.func (gs gpa)) uy)) ⟩
               Func.func (ContFunc.func (SliceObj.arrow a)) (Func.is-func (ContFunc.func (gs gpa)) uy) ≡⟨  ΓCont.inclusion gpa uy ⟩
               y ∎ }
                  where open ≡-Reasoning
           lem04 : {x y : Ordinal} → (ax  : odef (Γo a A) x) (ay : odef (Γo a A) y)
                → x ≡ y
                → top [ ΓCont.s ax ≈ ΓCont.s ay ]
                → top [ top [ _⟶_.arrow f o ΓCont.s ax ] ≈ top [ _⟶_.arrow f o ΓCont.s ay ] ]
           lem04 {x} {y} ax ay x=y eq1 = resp {_} {_} {_} {ΓCont.s ax} {ΓCont.s ay} {_⟶_.arrow f} {_⟶_.arrow f} eq1
                  (refl-hom {_} {_} {_⟶_.arrow f}) where
              open ≈-Reasoning top
           lem03 : {x y : Ordinal} → (ax  : odef (Γo a A) x) (ay : odef (Γo a A) y) → (eq : x ≡ y)
               → (z : Ordinal) (az : odef (SObj.s A) z) → FuncEQ (ContFunc.func (lem02 ax)) (ContFunc.func (lem02 ay)) z az
           lem03 {x} {y} ax ay eq z az = lem04 ax ay eq (Γo-wld a {x} {y} {A} ax ay eq) z az

       ΓMap : {A B : Obj (top / X)} → Hom (top / X) A B → Hom (HOD-OSCA (topology X) ) (ΓObj A) (ΓObj B)
       ΓMap {a} {b} f = record { TMap = ΓTMap f ; isNTrans = record { commute = λ {p} {q} {g} → lem00 {p} {q} {g} } } where
           lem00 : {p : Obj OX} {q : Obj OX} {g : Hom OX p q} → HODSets [ HODSets [ Γm b {p} {q} g o ΓTMap f p ] ≈ HODSets [ ΓTMap f q o Γm a {p} {q} g ] ]
           lem00 {p} {q} {g} z az =  refl

       Γ : Functor ( top / X ) (HOD-OSCA (topology X) )
       Γ = record { FObj = ΓObj ; FMap = ΓMap ; isFunctor = record {
            identity = λ {a} z az →  ΓCont.x=func az
         ;  ≈-cong = λ {a} {b} {f} {g} f=g {p} → lem01 {a} {b} {f} {g} f=g {p}
         ;  distr = λ {a} {b} {c} {f} {g} {p} → lem04 {a} {b} {c} {f} {g} {p}
         } } where
             lem00 : (a : Obj (top / X )) → HOD-OSCA (topology X) [ ΓMap (Id {_} {_} {_} {top / X} a) ≈ Id {_} {_} {_} {HOD-OSCA (topology X)} (ΓObj a) ]
             lem00 a z az = ΓCont.x=func az
             lem01 : {a b : Obj (top / X)} {f g : Hom (top / X) a b} → (top / X) [ f ≈ g ] → HOD-OSCA (topology X) [ ΓMap f ≈ ΓMap g ]
             lem01  {a} {b} {f} {g} f=g {p} z az = ==→o≡ (
                FuncEQ→HODEQ (ContFunc.func (top [ _⟶_.arrow f o ΓCont.s az ])) (ContFunc.func (top [ _⟶_.arrow g o ΓCont.s az ])) lem03 )  where
                     lem03 : top [ top [ _⟶_.arrow f o ΓCont.s az ] ≈ top [ _⟶_.arrow g o ΓCont.s az ] ]
                     lem03 = resp {_} {_} {_} { ΓCont.s az } { ΓCont.s az } {_⟶_.arrow f} {_⟶_.arrow g} (refl-hom {_} {_} { ΓCont.s az } ) f=g where
                         open  ≈-Reasoning top
             lem04 :  {a b c : Obj (top / X)} {f : Hom (top / X) a b} {g : Hom (top / X) b c}
                 → HOD-OSCA (topology X) [ ΓMap ((top / X) [ g o f ]) ≈ HOD-OSCA (topology X) [ ΓMap g o ΓMap f ] ]
             lem04  {a} {b} {c} {f} {g} {p} z az = ==→o≡ (
                FuncEQ→HODEQ (ContFunc.func (top [ _⟶_.arrow ( (top / X) [ g o f ] )  o ΓCont.s az ]))
                        (ContFunc.func (top [ _⟶_.arrow g  o top [ _⟶_.arrow f o  ΓCont.s az ]   ] )) lem05 ) where
                     lem05 : top [ top [ _⟶_.arrow ( (top / X) [ g o f ] )  o ΓCont.s az ]
                                 ≈ top [ _⟶_.arrow g o top [ _⟶_.arrow f o  ΓCont.s az ]   ] ]
                     lem05 = assoc {_} {_} {_} {_} { _⟶_.arrow g} { _⟶_.arrow f} { ΓCont.s az} where
                         open  ≈-Reasoning top

       Γp-is-sheaf : (I : Set n) → (Ui : I → Obj (OSC (topology X))) → (p : Obj ( top / X ))
          → Is-sheaf.Is-sheaf (topology X) I Ui (ΓObj p)
       Γp-is-sheaf I Ui p = record {
              commute = lem00
           ;  pullback = λ {d} {p1}  eq → lem01 {d} {p1}  eq
           ;  π1p=π1 = λ {d} {π1'}  eq i x ax → lem02 {d} {π1'} eq i x ax
           ;  uniqueness = λ {d} p1 π1'  eq mp=p x ax → lem03 {d} p1 π1' eq mp=p x ax
            } where
                open  Is-sheaf (topology X) I Ui (ΓObj p)
                p1 : SliceObj top X
                p1 = p
                dfunc1 : ContFunc (topology (SliceObj.X p)) (topology X)
                dfunc1 = SliceObj.arrow p
                F : Functor OX HODSets -- Obj (HOD-OSCA (topology X))
                F = ΓObj p
                Uiab : (a b : I) → Obj OX
                Uiab a b = record { s = (SObj.s (Ui a)) ∩ (SObj.s (Ui b)) ; p = o∩ (topology X) (SObj.p (Ui a)) (SObj.p (Ui b)) }
                record UInv {d : Obj HODSets} {x : Ordinal} (dx : odef d x) (π1' : (i : I) → Hom HODSets d (Γo p (Ui i))) (y z : Ordinal ) : Set n where
                   field
                      i : I
                      is-union : & (HODInverseImage (ContFunc.func (ΓCont.s (Func.is-func (π1' i ) dx))) y) ≡ z
                Uinverse : {d : Obj HODSets} {x : Ordinal} (dx : odef d x) (π1' : (i : I) → Hom HODSets d (Γo p (Ui i))) (y : Ordinal ) → HOD
                Uinverse {d} dx π1' y = record { od = record { def = λ z → UInv dx π1' y z }; odmax = osuc (& (space X))
                     ; <odmax = λ {z} lt →  subst (λ k → k o< osuc (& (space X)) ) &iso ( ⊆→o≤ (lem04 lt))} where
                         lem04 : {x y z : Ordinal} → UInv dx π1' y z → odef (* z) x → odef (space X) x
                         lem04 {x} {y} {z} uiz zx = lem06 where
                            lem03 : odef (OS (topology X)) (& (SObj.s (Ui (UInv.i uiz))))
                            lem03 = SObj.p (Ui (UInv.i uiz))
                            lem05 : odef (SObj.s (Ui (UInv.i uiz))) x
                            lem05 = InverseImage.y∈P (eq→ (ord→== (trans &iso (sym (UInv.is-union uiz)  ))) zx)
                            lem06 : odef (space X) x
                            lem06 = OS⊆PL (topology X) lem03 _ (eq← *iso lem05)
                U→I : {y : Ordinal} →  odef (SObj.s U) y → I
                U→I {y} record { owner = owner ; ao = record { i = i ; x=Ui = x=Ui } ; ox = ox } = i
                U→Si : {y : Ordinal} →  (sy : odef (SObj.s U) y) → odef (SObj.s (Ui (U→I sy))) y
                U→Si {y} record { owner = owner ; ao = record { i = i ; x=Ui = x=Ui } ; ox = ox } = eq→ (ord→== (trans &iso x=Ui)) ox
                Uyz : {y z : Ordinal} (sy : odef (SObj.s U) y) (sz : odef (SObj.s U) z) → y ≡ z → odef (SObj.s (Uab (U→I sy) (U→I sz))) y
                Uyz sy sz y=z = ⟪ U→Si sy , subst (λ k → odef (SObj.s (Ui (U→I sz))) k) (sym y=z) ( U→Si sz)  ⟫
                lem00 :  (a b : I) → HODSets [ HODSets [ f1 a b o f3 a b  ] ≈ HODSets [ f2 a b o f4 a b ] ]
                lem00 a b c cx = begin
                    Func.func (f1 a b) (Func.is-func (f3 a b) cx)  ≡⟨⟩
                    Func.func (FMap F {Ui a} {Uiab a b} proj1) (Func.is-func (FMap F {U} {Ui a} (λ {x} → (Ui⊆UI {x} a))) cx)  ≡⟨⟩
                    Func.func (FMap F {U} {Uiab a b} (λ {y} iy → (Ui⊆UI  a (proj1 iy)) )) cx  ≡⟨
                        IsFunctor.≈-cong (isFunctor F) {U} {Uiab a b} {λ iy → Ui⊆UI  a (proj1 iy)} {λ iy → Ui⊆UI  b (proj2 iy)} tt c cx ⟩
                    Func.func (FMap F {U} {Uiab a b} (λ {y} iy → (Ui⊆UI  b (proj2 iy)) )) cx  ≡⟨⟩
                    Func.func (FMap F {Ui b} {Uiab a b} proj2) (Func.is-func (FMap F {U} {Ui b} (λ {x} → (Ui⊆UI {x} b))) cx)  ≡⟨⟩
                    Func.func (f2 a b) (Func.is-func (f4 a b) cx)   ∎ where open ≡-Reasoning

                module SheafEQ {d : Obj HODSets} {π1' : (i : I) → Hom HODSets d (Γo p (Ui i))}
                    (eq : (i j : I) → HODSets [ HODSets [ f1 i j o π1' i ] ≈ HODSets [ f2 i j o π1' j ] ])  where

                       --
                       -- sfunc can be define without eq, it requires only π1'
                       --
                       sfunc : {x : Ordinal } → (dx : odef d x) → {y : Ordinal} → odef (SObj.s U) y → Ordinal
                       sfunc dx {y} su = Func.func (ContFunc.func (ΓCont.s (Func.is-func (π1' (U→I su) ) dx))) (U→Si su)
                       is-sfunc : {x : Ordinal } → (dx : odef d x) → {y : Ordinal} → (sy : odef (SObj.s U) y) → odef (space (SliceObj.X p)) (sfunc dx sy)
                       is-sfunc dx {y} su = Func.is-func (ContFunc.func (ΓCont.s (Func.is-func (π1' (U→I su) ) dx))) (U→Si su)
                       --
                       -- Welldefiness of sfunc is given by equlity of the pull back diagram
                       --
                       sfunc-wld : {x : Ordinal } → (dx : odef d x)
                           → {y z : Ordinal} → (sy : odef (SObj.s U) y) (sz : odef (SObj.s U) z) → y ≡ z → sfunc dx sy ≡ sfunc dx sz
                       sfunc-wld dx {y} {z} sy sz y=z = lem11 where
                           i = U→I sy
                           iz = U→I sz
                           fy = ContFunc.func (ΓCont.s (Func.is-func (π1' (U→I sy) ) dx))
                           fz = ContFunc.func (ΓCont.s (Func.is-func (π1' (U→I sz) ) dx))
                           lem11 : Func.func fy (U→Si sy) ≡ Func.func fz (U→Si sz)
                           lem11 = begin
                               Func.func fy (U→Si sy) ≡⟨⟩
                               Func.func fy (proj1 (Uyz sy sz y=z) )
                                  ≡⟨ F→FuncHOD-EQ (dfunc p {Ui i}  {Uab i iz} (λ q → proj1 q) (Func.is-func (π1' i)  dx))
                                                  (dfunc p {Ui iz} {Uab i iz} (λ q → proj2 q) (Func.is-func (π1' iz) dx))
                                                     (ord→== (eq i iz _ dx )) _ (Uyz sy sz y=z ) ⟩
                               Func.func fz (proj2 (Uyz sy sz y=z)) ≡⟨ Func.func-wld fz _ _ y=z ⟩
                               Func.func fz (U→Si sz)  ∎ where open ≡-Reasoning
                       efunc : {x : Ordinal } → (dx : odef d x) → Func (SObj.s U) (space (SliceObj.X p))
                       efunc dx = record {
                                func = λ {x} sx → sfunc dx sx
                              ; is-func = is-sfunc dx
                              ; func-wld = sfunc-wld dx
                              }
                       lem30 : {A B R : HOD} → A ⊆ B → ( R ∩ A ) =h= ( (R ∩ A) ∩ B )
                       lem30 {A} {B} {R} a⊆b = record {
                               eq→ = λ {x} lt → ⟪ ⟪ proj1 lt , proj2 lt  ⟫ , a⊆b (proj2 lt) ⟫
                            ;  eq← = λ {x} lt → ⟪ proj1 (proj1 lt) , proj2 (proj1 lt)  ⟫
                          }
                       lem32 : {P Q R S : HOD} → P =h= R → Q =h= S  → ( P ∩ Q ) =h= ( R ∩ S)
                       lem32 p=r q=s  = record {
                               eq→ = λ {x} lt → ⟪ eq→ p=r (proj1 lt) , eq→ q=s (proj2 lt) ⟫
                            ;  eq← = λ {x} lt → ⟪ eq← p=r (proj1 lt) , eq← q=s (proj2 lt) ⟫
                          }
                       --
                       -- continuity of sfunc is given by the fact that the InverseImage is a Union of each π1' i
                       --
                       econt : {x : Ordinal } → (dx : odef d x) → {y : Ordinal} → odef (OS (topology (SliceObj.X p))) y
                           → odef (OS (SubTopology {SObj.s U} {space X} (topology X) (SO⊆SX U))) (& (HODInverseImage (efunc dx) y))
                       econt dx {y} oy = subst (λ k → odef (OS (SubTopology {SObj.s U} {space X} (topology X) (SO⊆SX U))) k) (sym (==→o≡ lem14)) lem19 where
                         lem14 : HODInverseImage (efunc dx) y =h= Union (Uinverse  dx π1' y)
                         lem14 = record {
                              eq→  = lem15
                            ; eq←  = lem16
                            } where
                               lem15 : {x : Ordinal} → odef (HODInverseImage (efunc dx) y) x → odef (Union (Uinverse dx π1' y)) x
                               lem15 {x} record { y∈P = record { owner = owner ; ao = ao ; ox = ox } ; is-inverse = ys }
                                 = record { owner = u00 ; ao = record { i = IU.i ao ; is-union = refl }  ; ox = u01  } where
                                   i = IU.i ao
                                   u00 = & (HODInverseImage (ContFunc.func (ΓCont.s (Func.is-func (π1' i) dx))) y)
                                   u01 : odef (* u00) x
                                   u01  = eq← *iso record { y∈P = u02 ; is-inverse = u03 } where
                                       u02 : odef (SObj.s (Ui (IU.i ao))) x
                                       u02 = eq→ (ord→== (trans &iso (IU.x=Ui ao))) ox
                                       u03 : odef (* y) (Func.func (ContFunc.func (ΓCont.s (Func.is-func (π1' (IU.i ao)) dx))) u02)
                                       u03 = ys
                               lem16 : {x : Ordinal}  → odef (Union (Uinverse dx π1' y)) x → odef (HODInverseImage (efunc dx) y) x
                               lem16 {x} record { owner = owner ; ao = ao ; ox = ox } = record { y∈P = u00 ; is-inverse = u03 } where
                                   u02 : UInv dx π1' y owner -- odef (Uinverse dx π1' y) owner
                                   u02 = ao
                                   i = UInv.i ao
                                   u04 : & (HODInverseImage (ContFunc.func (ΓCont.s (Func.is-func (π1' i ) dx))) y) ≡ owner
                                   u04 = UInv.is-union ao
                                   u05 : odef (HODInverseImage (ContFunc.func (ΓCont.s (Func.is-func (π1' i ) dx))) y) x
                                   u05 = eq← (ord→== (trans u04 (sym &iso))) ox
                                   u06 : odef (SObj.s (Ui i)) x
                                   u06 = InverseImage.y∈P u05
                                   u11 : odef (* y) (Func.func (ContFunc.func (ΓCont.s (Func.is-func (π1' i ) dx))) u06)
                                   u11 = InverseImage.is-inverse u05
                                   u00 :  odef (SObj.s U) x
                                   u00 =  record { owner = & (SObj.s (Ui i)) ; ao = record { i = UInv.i ao ; x=Ui = refl } ; ox = eq← *iso u06 }
                                   u03 : odef (* y) (sfunc dx u00)
                                   u03 = subst (λ k → odef (* y) k) (Func.func-wld  (ContFunc.func (ΓCont.s (Func.is-func (π1' i ) dx)))
                                       u06 _ refl ) u11
                                   u07 : odef (space (SliceObj.X p)) (Func.func (ContFunc.func (ΓCont.s (Func.is-func (π1' i ) dx))) u06)
                                   u07 = Func.is-func (ContFunc.func (ΓCont.s (Func.is-func (π1' i ) dx))) u06
                         lem15 : (i : I) → odef (OS (SubTopology {SObj.s (Ui i)} {space X} (topology X) (SO⊆SX (Ui i))))
                                  (& (HODInverseImage (ContFunc.func (ΓCont.s (Func.is-func (π1' i ) dx))) y))
                         lem15 i = ContFunc.continuous (ΓCont.s (Func.is-func (π1' i ) dx))  oy
                         lem19 :  odef (OS (SubTopology {SObj.s U} {space X} (topology X) (SO⊆SX U))) (& (Union (Uinverse  dx π1' y)))
                         lem19 = o∪ (SubTopology {SObj.s U} {space X} (topology X) (SO⊆SX U)) lem20 where
                            lem20 :  {x : Ordinal} → odef (Uinverse dx π1' y) x  → SubElement (topology X) (SObj.s U) x
                            lem20 {x} lt =  lem24 where
                               i =  UInv.i lt
                               lem22 = HODInverseImage (ContFunc.func (ΓCont.s (Func.is-func (π1' i ) dx))) y
                               lem21 : & lem22 ≡ x
                               lem21 = UInv.is-union lt
                               lem23 : odef (OS (SubTopology {SObj.s (Ui i)} {space X} (topology X) (SO⊆SX (Ui i)))) (& lem22)
                               lem23 = lem15 (UInv.i lt)
                               lem24 : SubElement (topology X) (SObj.s U) x
                               lem24 with lem15 (UInv.i lt)
                               ... | record { R = R ; OR = OR ; x=R = x=R } =  record { R = & (* R ∩ SObj.s (Ui (UInv.i lt)))
                                        ; OR = lem31 ; x=R = lem26 }  where
                                   lem25 :  & (HODInverseImage (ContFunc.func (ΓCont.s (Func.is-func (π1' (UInv.i lt)) dx))) y)
                                        ≡ & (* R ∩ SObj.s (Ui (UInv.i lt)))
                                   lem25 = x=R
                                   lem27 : x ≡ & (* R ∩ SObj.s (Ui (UInv.i lt)))
                                   lem27  = trans (sym lem21) lem25
                                   lem29 : odef (OS (topology X)) (& (SObj.s (Ui (UInv.i lt))))
                                   lem29 = SObj.p (Ui (UInv.i lt))
                                   lem33 : SObj.s (Ui (UInv.i lt)) ⊆ Union UI
                                   lem33 {x} lt1 = record { owner = & (SObj.s (Ui (UInv.i lt))) ; ao = record { i = UInv.i lt ; x=Ui = refl }
                                       ; ox = eq← *iso lt1 }
                                   lem26 : x ≡ & (* (& (* R ∩ SObj.s (Ui (UInv.i lt)))) ∩ Union UI)
                                   lem26  = trans lem27 (==→o≡ ( begin
                                      * R ∩ SObj.s (Ui (UInv.i lt)) ≈⟨ lem30 {SObj.s (Ui (UInv.i lt))}{Union UI} {* R} lem33 ⟩
                                      (* R ∩ SObj.s (Ui (UInv.i lt))) ∩ Union UI ≈⟨
                                         lem32 {* R ∩ SObj.s (Ui (UInv.i lt))} {Union UI}
                                             {* (& (* R ∩ SObj.s (Ui (UInv.i lt))))}{Union UI} (==-sym *iso)  ==-refl ⟩
                                      * (& (* R ∩ SObj.s (Ui (UInv.i lt)))) ∩ Union UI ∎ )) where
                                          open EqR ==-Setoid
                                   lem31 : odef (OS (topology X)) (& (* R ∩ SObj.s (Ui (UInv.i lt))))
                                   lem31  = o∩ (topology X) (subst (λ k → odef (OS (topology X)) k) (sym &iso) OR )  lem29
                       cfunc : {x : Ordinal } → (dx : odef d x) → ContFunc (SubTopology {SObj.s U} (topology X) (SO⊆SX U)) (topology (SliceObj.X p))
                       cfunc {x} dx = record { func = efunc dx ; continuous = econt dx }
                       cfunc-incl :  {x : Ordinal } → (dx : odef d x) → {z : Ordinal} (uz : odef (SObj.s U) z)
                          → Func.func (ContFunc.func (SliceObj.arrow p)) (Func.is-func (ContFunc.func (cfunc dx)) uz )≡ z
                       cfunc-incl dx uz = ΓCont.inclusion (Func.is-func (π1' (U→I uz) ) dx) (U→Si uz)
                       cfunc-wld : {x y : Ordinal} (ax : odef d x) (ay : odef d y) → x ≡ y → & (F→FuncHOD (efunc ax)) ≡ & (F→FuncHOD (efunc ay))
                       cfunc-wld {x} {y} ax ay x=y = ==→o≡ ( FuncEQ→HODEQ (efunc ax) (efunc ay)  lem10 ) where
                            lem10 : (z : Ordinal) (sz : odef (SObj.s U) z) → FuncEQ (efunc ax) (efunc ay) z sz
                            lem10 z sz = begin
                               Func.func (ContFunc.func (ΓCont.s (Func.is-func (π1' (U→I sz) ) ax))) (U→Si sz)
                                 ≡⟨ ΓCont-eq (Func.is-func (π1' (U→I sz) ) ax) (Func.is-func (π1' (U→I sz) ) ay) lem11 z (U→Si sz) ⟩
                               Func.func (ContFunc.func (ΓCont.s (Func.is-func (π1' (U→I sz) ) ay))) (U→Si sz)  ∎ where
                                  open ≡-Reasoning
                                  lem11 : Func.func (π1' (U→I sz)) ax  ≡ Func.func (π1' (U→I sz)) ay
                                  lem11 = Func.func-wld (π1' (U→I sz)) ax ay x=y
                lem01 : {d : Obj HODSets} {π1' : (i : I) → Hom HODSets d (Γo p (Ui i))}  →
                    ((i j : I) → HODSets [ HODSets [ f1 i j o π1' i ] ≈ HODSets [ f2 i j o π1' j ] ]) → Hom HODSets d (Γo p U)
                lem01 {d} {π1'}  eq  = record {
                     func = λ {x} dx → & (F→FuncHOD (ContFunc.func (cfunc dx)))
                  ;  is-func = λ {x} dx → record { s = cfunc dx ; x=func = refl ; inclusion = cfunc-incl dx }
                  ;  func-wld = cfunc-wld
                  } where open SheafEQ {d} {π1'} eq
                SUI : Obj (OSC (topology X))
                SUI = record { s = Union UI ; p = o∪ (topology X)
                    (λ {x} ui → subst (λ k → odef (OS (topology X)) k) (sym (IU.x=Ui ui)) (SObj.p (Ui (IU.i ui) ))) }
                lem02 : {d : Obj HODSets} {π1' : (i : I) → Hom HODSets d (Γo p (Ui i))} (eq : (i j : I) →
                       HODSets [ HODSets [ f1 i j o π1' i ] ≈ HODSets [ f2 i j o π1' j ] ]) (i : I) →
                        HODSets [ HODSets [ Γm p {SUI} {Ui i} (Ui⊆UI i) o lem01 {d} {π1'} eq ] ≈ π1' i ]
                lem02 {d} {π1'} eq i x ax = begin
                     & (F→FuncHOD (dfunc p {SUI} {Ui i} (Ui⊆UI i) (record { s = cfunc ax ; x=func = refl ; inclusion = cfunc-incl ax })))
                          ≡⟨ ==→o≡  (FuncEQ→HODEQ (dfunc p {SUI} {Ui i} (Ui⊆UI i) (record { s = cfunc ax ; x=func = refl ; inclusion = cfunc-incl ax }))
                           (ContFunc.func (ΓCont.s (Func.is-func (π1' i) ax))) lem25 )  ⟩
                     & (F→FuncHOD (ContFunc.func (ΓCont.s (Func.is-func (π1' i) ax))))  ≡⟨ ΓCont.x=func (Func.is-func (π1' i) ax ) ⟩
                     Func.func (π1' i) ax ∎
                   where
                     open ≡-Reasoning
                     open SheafEQ {d} {π1'} eq
                     lem25 : (z : Ordinal) (az : odef (SObj.s (Ui i)) z) → FuncEQ
                         (dfunc p {SUI} {Ui i} (Ui⊆UI i) (record { s = cfunc ax ; x=func = refl ; inclusion = cfunc-incl ax }))
                         (ContFunc.func (ΓCont.s (Func.is-func (π1' i) ax))) z az
                     lem25 z az = begin
                         Func.func (dfunc p {SUI} {Ui i} (Ui⊆UI i) (record { s = cfunc ax ; x=func = refl ; inclusion = cfunc-incl ax })) az ≡⟨ refl ⟩
                         Func.func (ContFunc.func (ΓCont.s (Func.is-func (π1' i) ax)))  (U→Si (Ui⊆UI i az))
                            ≡⟨ Func.func-wld (ContFunc.func (ΓCont.s (Func.is-func (π1' i) ax)))  (U→Si (Ui⊆UI i az)) az refl  ⟩
                         Func.func (ContFunc.func (ΓCont.s (Func.is-func (π1' i) ax))) az ∎
                            where open ≡-Reasoning
                lem03 : {d : Obj HODSets} (p' : Hom HODSets d (Γo p U)) (π1' : (i : I) → Hom HODSets d (Γo p (Ui i)))
                    (eq : (i j : I) → HODSets [ HODSets [ f1 i j o π1' i ] ≈ HODSets [ f2 i j o π1' j ] ]) →
                    ((i : I) → HODSets [ HODSets [ Γm p {SUI} {Ui i} (Ui⊆UI i) o p' ] ≈ π1' i ]) →
                    HODSets [ lem01 {d} {π1'} eq ≈ p' ]
                lem03 {d} p' π1' eq mpi=pi x dx = begin
                      & (F→FuncHOD (efunc dx)) ≡⟨ ==→o≡  (FuncEQ→HODEQ (efunc dx) (ContFunc.func (ΓCont.s (Func.is-func p' dx))) lem20 ) ⟩
                      & (F→FuncHOD (ContFunc.func (ΓCont.s (Func.is-func p' dx))))  ≡⟨ ΓCont.x=func (Func.is-func p' dx ) ⟩
                      Func.func p' dx ∎ where
                     open ≡-Reasoning
                     open SheafEQ {d} {π1'} eq
                     lem23 : (z : Ordinal) (az : odef (SObj.s U) z) → Func (SObj.s (Ui (U→I az))) (SObj.s U)
                     lem23 z az  = record {
                         func = λ {x} ax → x
                      ;  is-func = λ {x} ax → Ui⊆UI (U→I az) ax
                      ;  func-wld = λ {x} _ _ eq → eq
                      }
                     lem22 :  (z : Ordinal) (az : odef (SObj.s U) z) → Func (SObj.s (Ui (U→I az))) (space (SliceObj.X p))
                     lem22 z az = FuncComp (ContFunc.func (ΓCont.s (Func.is-func p' dx))) (lem23  _ az)
                     lem21 : (z : Ordinal) (az : odef (SObj.s U) z) → FuncEQ (lem22 z az)
                        (ContFunc.func (ΓCont.s (Func.is-func (π1' (U→I az) ) dx))) _ (U→Si az)
                     lem21 z az =  F→FuncHOD-EQ
                        (lem22 z az)
                        (ContFunc.func (ΓCont.s (Func.is-func (π1' (U→I az) ) dx)) )
                        (ord→== (trans ( mpi=pi (U→I az) x dx ) (sym (ΓCont.x=func (Func.is-func (π1' (U→I az) ) dx) ) ))) _ (U→Si az)
                     cpπ1 = ContFunc.func (ΓCont.s (Func.is-func p' dx))
                     lem20 : (z : Ordinal) (az : odef (SObj.s U) z) → FuncEQ (efunc dx) (ContFunc.func (ΓCont.s (Func.is-func p' dx))) z az
                     lem20 z az = begin
                        Func.func (efunc dx) az ≡⟨⟩
                        Func.func (ContFunc.func (ΓCont.s (Func.is-func (π1' (U→I az) ) dx))) (U→Si az) ≡⟨  sym (lem21 z az)  ⟩
                        Func.func cpπ1 (Ui⊆UI (U→I az) (U→Si az)) ≡⟨ Func.func-wld cpπ1 (Ui⊆UI (U→I az) (U→Si az)) az refl  ⟩
                        Func.func cpπ1 az ∎

       open import ZEquiv O HODAxiom ho<
       open import Relation.Binary.Core

       -- ( F : Obj (HOD-OSCA (topology X) ) ) means  F : Functor (op A) HODSets

       -- FCod : OD
       -- FCod = record { def = ? }
       --
       --   s|w = t|w,  s∈F(U), t∈F(V), U,V∈ OS(X),
       --
       --      v∈OSX : odef (OS (topology X)) v
       --      u∈OSX : odef (OS (topology X)) u

       -- Since HODOSCA is contravariant, if we have U ⊆ V in Obj HODSCCA,
       --     Fuv : FObj F U → FObj F V
       --     Fuv = Func.func (FMap F (λ q → V⊆U q))
       -- this is a restriction of Func (FObj F U) (FObj F V), that is if we  have (FUs : odef (FObj F U) s ),
       -- we have s|v = Func.func (FMap F (λ q → V⊆U q)) FUs,

       --   (F : Functor OX HODSets) is unbounded in HODSets, this is (LObj :  Obj (HOD-OSCA (topology X) )) also.
       --   To make the topology space from F, we need some restrition

       FLim : (F : Functor OX HODSets) → Set n
       FLim F = (x : Ordinal) → (ox : odef (OS (topology X)) (& (* x) ))
           → FObj F record { s = * x ; p = ox } ⊆ Power (space X)

       L00 : (a : Obj (HOD-OSCA (topology X))) → Functor OX HODSets
       L00 a = a

       --
       --  it looks like easy to prove, but we cannot prove it in safe mode
       --
       Fwld : (F : Functor OX HODSets) → Set (suc n)
       Fwld F = {a b : HOD } → a =h=  b → { pa : (OS (topology X)) ∋ a } { pb : (OS (topology X)) ∋ b }
               → FObj F record { s = a ; p = pa }  =h= FObj F record { s = b ; p = pb }

       Fid : (F : Functor OX HODSets) → (a : Obj OX) → (x : Ordinal) → (ax : odef (FObj F a) x) → Func.func (FMap F (λ fax → fax )) ax  ≡ x
       Fid F a x ax = IsFunctor.identity (isFunctor F) x ax

       Fdistr : (F : Functor OX HODSets) → {a b c : Obj OX}
           → (b⊆a : SObj.s b ⊆ SObj.s a)  → (c⊆b : SObj.s c ⊆ SObj.s b)
           → (x : Ordinal) → (ax : odef (FObj F a) x)
           → Func.func (FMap F {a} {c} (λ fcx → b⊆a (c⊆b fcx) )) ax
               ≡ Func.func (FMap F {b} {c} (λ fcx → c⊆b fcx )) (Func.is-func (FMap F {a} {b} (λ fbx → b⊆a fbx )) ax)
       Fdistr F {a} {b} {c} b⊆a c⊆b x ax = IsFunctor.distr (isFunctor F) {a} {b} {c} {b⊆a} {c⊆b} x ax

       -- FMap only depend on Ordinal, not on the proof of inclusion
       -- this is requied to prove equivalence class leads equation on FMap
       --    this is different from well definedness of FMap, because functions are not the same 
       --
       FO-wld : (F : Functor OX HODSets) → Set (suc (suc n))
       FO-wld F =  {a b c d : Obj OX}
           → (b⊆a : SObj.s b ⊆ SObj.s a)  → (d⊆c : SObj.s d ⊆ SObj.s c)
           → {x y : Ordinal} → (ax : odef (FObj F a) x)  → (cx : odef (FObj F c) y) → x ≡ y
           → Func.func (FMap F {a} {b} b⊆a ) ax ≡ Func.func (FMap F {c} {d} d⊆c ) cx

       -- I'm sure that this is correct
       -- 
       F-up : (F : Functor OX HODSets) → Set (suc (suc n))
       F-up F =  {a c : Obj OX}
           → (c⊆a : SObj.s c ⊆ SObj.s a)  
           → {x y : Ordinal} → (cx : odef (FObj F c) x)  → x ≡ y → odef (FObj F a) y

       OXFcong : (F : Functor OX HODSets ) → {a b : Obj OX} (f g : Hom OX a b) → {y z : Ordinal} → (cy : odef (FObj F a ) y ) (cz : odef (FObj F a ) z )
             → y ≡ z
             → Func.func (FMap F {a} {b} f) cy ≡  Func.func (FMap F {a} {b} g ) cz
       OXFcong F {a} {b} f g {y} {z} cy cz y=z  = trans (IsFunctor.≈-cong (isFunctor F) tt y cy) (Func.func-wld (FMap F {a} {b} g) cy cz y=z )


       module FLIM (FL : (F : Functor OX HODSets) →  FLim F ) (FW : (F : Functor OX HODSets) →  Fwld F ) 
          (FU : (F : Functor OX HODSets) →  F-up F ) 
          (FOW : (F : Functor OX HODSets) →  FO-wld F ) where

           --  s ∈ F(U) → V ⊆ U → s|v
           --
           restrict-func : {U V : Obj OX}
               → (F : Functor OX HODSets)
               → (V⊆U : SObj.s V ⊆ SObj.s U)
               → Func (FObj F U) (FObj F V)
           restrict-func {U} {V}  F V⊆U = FMap F (λ q → V⊆U q)

           OXID : (a b : Obj OX) → SObj.s a =h= SObj.s b → Hom OX a b
           OXID a b eq {x} ax = eq← eq ax

           --  ∃ w → s|w = t|w, w ⊆ u ∩ v, s.t. x∈w
           --
           record Feq
                   (F : Functor OX HODSets)
                   {x s t : Ordinal} (X∋x : odef (space X) x)
                   (U V : Obj OX )
                   (fus : odef (FObj F U) s) (fvt : odef (FObj F V) t)  : Set n where
              field
                 w : Ordinal
                 ow : OS (topology X) ∋ * w
                 w⊆u∩v : (* w) ⊆ ((SObj.s U) ∩ (SObj.s V) )
                 x∈w : odef (* w) x
              W : Obj  OX
              W = record { s = * w ; p = ow }
              W⊆U : SObj.s W ⊆ SObj.s U
              W⊆U {y} lt = proj1 (w⊆u∩v lt)
              W⊆V : SObj.s W ⊆ SObj.s V
              W⊆V {y} lt = proj2 (w⊆u∩v lt)
              field
                 feq : Func.func (FMap F {U} {W} W⊆U) fus ≡ Func.func (FMap F {V} {W} W⊆V) fvt

           --  [s]x
           --      equivalent class of ∃ w → s|w = t|w, w ⊆ u ∩ v, s.t. x∈w
           --
           module FEQ (F : Functor OX HODSets) {x : Ordinal }  (X∋x : odef (space X) x) where
               record SFU (s : Ordinal) : Set n where
                  field
                     su : Ordinal
                     osu : OS (topology X) ∋ * su
                  U : Obj OX
                  U = record { s = * su ; p = osu }
                  field
                     x∈su : odef (* su) x
                     s∈FU : odef (FObj F U ) s
                  lem00 : & (FObj F (record { s = * su  ; p = osu }))   o< osuc (& (Power (space X)))
                  lem00 =  ⊆→o≤ ( FL F _ osu  )
                  x<PSX : s o< osuc (& (Power (space X)))
                  x<PSX  = begin
                    s ≡⟨  sym &iso ⟩
                    & (* s)  <⟨  c<→o< {* s} {FObj F U} (subst (λ k → odef (FObj F U) k ) (sym &iso) s∈FU) ⟩
                    & (FObj F U) ≤⟨ ⊆→o≤ ( FL F _ osu  ) ⟩
                    (& (Power (space X)))  ∎ where
                        open o≤-Reasoning
                  PSX∋s : odef (Power (space X)) (& (* s) )
                  PSX∋s = FL F _ osu (subst (λ k → odef (FObj F U) k ) (sym &iso) s∈FU)

               HODSFU : HOD
               HODSFU = record { od = record { def = λ x → SFU x } ; odmax =  osuc (& (Power (space X))) ; <odmax = λ {z} lz → SFU.x<PSX lz }

               Fw : {a b : HODElement HODSFU}
                 → (Feq F X∋x (SFU.U (HODElement.A∋elt a)) (SFU.U (HODElement.A∋elt b))  (SFU.s∈FU (HODElement.A∋elt a)) (SFU.s∈FU (HODElement.A∋elt b)))
                 → Obj OX
               Fw {a} {b} fe = record { s = * (Feq.w fe) ; p = Feq.ow fe }

               Su : {s  : Ordinal} → SFU s → Obj OX
               Su {s} sfu = record { s = * (SFU.su sfu) ; p = SFU.osu sfu }

               _≐_ : Rel ( HODElement HODSFU ) n
               a ≐ b = Feq F X∋x (SFU.U (HODElement.A∋elt a)) (SFU.U (HODElement.A∋elt b))  (SFU.s∈FU (HODElement.A∋elt a)) (SFU.s∈FU (HODElement.A∋elt b))

               ≐-refl : {sy : HODElement HODSFU} → sy  ≐ sy
               ≐-refl {sy} = record { w = SFU.su (HODElement.A∋elt sy) ; ow = SFU.osu (HODElement.A∋elt sy) ; w⊆u∩v = λ lt → ⟪ lt , lt ⟫
                   ; x∈w = SFU.x∈su (HODElement.A∋elt sy) ; feq = refl }

               ≐-sym : {sy sz : HODElement HODSFU} → sy  ≐ sz → sz  ≐ sy
               ≐-sym {sy} {sz} y=z = record { w = Feq.w y=z ; ow = Feq.ow y=z ; w⊆u∩v = λ lt → ⟪ proj2 (Feq.w⊆u∩v y=z lt) , proj1 (Feq.w⊆u∩v y=z lt) ⟫
                   ; x∈w = Feq.x∈w y=z  ; feq = sym (Feq.feq y=z) }

               open HODElement

               ≐-trans : {sy sz sw : HODElement HODSFU} → sy  ≐ sz → sz  ≐ sw → sy  ≐ sw
               ≐-trans {sy} {sz} {sw} y=z z=w = record { w = & (* (Feq.w y=z) ∩ * (Feq.w z=w) ) ; ow = lem00 ; w⊆u∩v = lem02
                   ; x∈w = lem01  ; feq = lem05 } where
                    lem00 : OS (topology X) ∋ * (& (* (Feq.w y=z) ∩ * (Feq.w z=w)))
                    lem00 = subst (odef (OS (topology X))) (sym &iso) (o∩ (topology X) (Feq.ow y=z) (Feq.ow z=w))
                    lem01 : odef (* (& (* (Feq.w y=z) ∩ * (Feq.w z=w)))) x
                    lem01 = eq← *iso ⟪ Feq.x∈w y=z , Feq.x∈w z=w ⟫
                    lem02 : * (& (* (Feq.w y=z) ∩ * (Feq.w z=w))) ⊆ (* (SFU.su (A∋elt sy)) ∩ * (SFU.su (A∋elt sw)))
                    lem02 {z} lt = ⟪ proj1 lem03 , proj2 lem04 ⟫ where
                        lem03 : odef ( * (SFU.su (A∋elt sy)) ∩ * (SFU.su (A∋elt sz)) ) z
                        lem03 = Feq.w⊆u∩v y=z (proj1 (eq→ *iso lt))
                        lem04 : odef ( * (SFU.su (A∋elt sz)) ∩ * (SFU.su (A∋elt sw)) ) z
                        lem04 = Feq.w⊆u∩v z=w (proj2 (eq→ *iso lt))
                    lem06 :  Func.func (FMap F {Su (A∋elt sy)} {Fw {sy} {sz} y=z} (λ lt → proj1 (Feq.w⊆u∩v y=z lt))) (SFU.s∈FU (A∋elt sy))
                           ≡ Func.func (FMap F {Su (A∋elt sz)} {Fw {sy} {sz} y=z} (λ lt → proj2 (Feq.w⊆u∩v y=z lt))) (SFU.s∈FU (A∋elt sz))
                    lem06 = Feq.feq y=z
                    lem07 :  Func.func (FMap F {Su (A∋elt sz)} {Fw {sz} {sw} z=w} (λ lt → proj1 (Feq.w⊆u∩v z=w lt))) (SFU.s∈FU (A∋elt sz))
                           ≡ Func.func (FMap F {Su (A∋elt sw)} {Fw {sz} {sw} z=w} (λ lt → proj2 (Feq.w⊆u∩v z=w lt))) (SFU.s∈FU (A∋elt sw))
                    lem07 = Feq.feq z=w
                    os01 :  Obj OX
                    os01 = record { s = * (& (* (Feq.w y=z) ∩ * (Feq.w z=w))) ; p = lem00 }
                    lem05 :  Func.func (FMap F (λ lt → proj1 (lem02 lt))) (SFU.s∈FU (A∋elt sy)) ≡
                             Func.func (FMap F (λ lt → proj2 (lem02 lt))) (SFU.s∈FU (A∋elt sw))
                    lem05 = begin
                        Func.func (FMap F {Su (A∋elt sy)} {os01} (λ lt → proj1 (lem02 lt))) (SFU.s∈FU (A∋elt sy)) ≡⟨ Fdistr F _ _ _ _  ⟩
                        Func.func (FMap F {Fw {sy} {sz} y=z}  {os01}  (λ lt → proj1 ( eq→ *iso lt))) (Func.is-func (FMap F  {Su (A∋elt sy)} {Fw {sy} {sz} y=z}
                            (λ lt → proj1 (Feq.w⊆u∩v y=z lt)) ) (SFU.s∈FU (A∋elt sy))) ≡⟨ OXFcong F _ _ _ _ (Feq.feq y=z) ⟩
                        Func.func (FMap F {Fw {sy} {sz} y=z}  {os01}  (λ lt → proj1 ( eq→ *iso lt))) (Func.is-func (FMap F  {Su (A∋elt sz)} {Fw {sy} {sz} y=z}
                            (λ lt → proj2 (Feq.w⊆u∩v y=z lt)) ) (SFU.s∈FU (A∋elt sz)))
                             ≡⟨ sym (Fdistr F (λ lt → proj2 (Feq.w⊆u∩v y=z lt)) (λ lt → proj1 ( eq→ *iso lt)) _ _) ⟩
                        Func.func (FMap F (λ fcx → proj2 (Feq.w⊆u∩v y=z (proj1 (eq→ *iso fcx))))) (SFU.s∈FU (A∋elt sz)) ≡⟨ OXFcong F _ _ _ _ refl ⟩
                        Func.func (FMap F (λ fcx → proj1 (Feq.w⊆u∩v z=w (proj2 (eq→ *iso fcx))))) (SFU.s∈FU (A∋elt sz))
                             ≡⟨ Fdistr F (λ lt → proj1 (Feq.w⊆u∩v z=w lt)) (λ lt → proj2 ( eq→ *iso lt)) _ _ ⟩
                        Func.func (FMap F {Fw {sz} {sw} z=w} {os01} (λ lt → proj2 ( eq→ *iso lt))) (Func.is-func (FMap F  {Su (A∋elt sz)} {Fw {sz} {sw} z=w}
                            (λ lt → proj1 (Feq.w⊆u∩v z=w lt)) ) (SFU.s∈FU (A∋elt sz)))
                             ≡⟨ (OXFcong F _ _ _ _ (Feq.feq z=w)) ⟩
                        Func.func (FMap F {Fw {sz} {sw} z=w} {os01} (λ lt → proj2 ( eq→ *iso lt))) (Func.is-func (FMap F  {Su (A∋elt sw)} {Fw {sz} {sw} z=w}
                            (λ lt → proj2 (Feq.w⊆u∩v z=w lt)) ) (SFU.s∈FU (A∋elt sw))) ≡⟨ sym (Fdistr F _ _ _ _ ) ⟩
                        Func.func (FMap F {Su (A∋elt sw)} {os01} (λ lt → proj2 (lem02 lt))) (SFU.s∈FU (A∋elt sw)) ∎ where
                           open ≡-Reasoning

               --  [s]x   s ∈ F(U)
               --         equivalent class of ∃ w → s|w = t|w, w ⊆ u ∩ v, s.t. x∈w
               record SFUEQ {y : Ordinal} (sy : SFU y) (x : Ordinal) : Set n where
                  field
                     sx : SFU x
                     sfu-eq : Feq F X∋x (SFU.U sx) (SFU.U sy)  (SFU.s∈FU sx) (SFU.s∈FU sy)

               HODSFUEQ : {y : Ordinal}  → SFU y → HOD
               HODSFUEQ {y} sy = record { od = record { def = λ x → SFUEQ sy x } ; odmax = osuc (& (Power (space X)))
                   ; <odmax = λ lz → SFU.x<PSX (SFUEQ.sx lz) }

               eqy : {y : Ordinal}  → (sy : SFU y) → HODElement HODSFU
               eqy {y} sy = record { elt = y ; A∋elt = sy }

               eqz : {y z : Ordinal}  → (sy : SFU y) → odef (HODSFUEQ sy) z → HODElement HODSFU
               eqz {y} {z} sy syz = record { elt = z ; A∋elt = SFUEQ.sx syz }

               sy=sz : {y z w : Ordinal}  → {sf : SFU w}
                  → (sy : odef (HODSFUEQ sf) y)  → (sz : odef ( HODSFUEQ sf ) z )
                  → Feq F X∋x  (SFU.U (SFUEQ.sx sy)) (SFU.U (SFUEQ.sx sz))  (SFU.s∈FU (SFUEQ.sx sy)) (SFU.s∈FU (SFUEQ.sx sz))
               sy=sz {y} {z} {w} {sf} sy sz = a=b where
                  a : HODElement HODSFU
                  a = eqz sf sy
                  b : HODElement HODSFU
                  b = eqz sf sz
                  c : HODElement HODSFU
                  c = eqy sf
                  a=b : a ≐ b
                  a=b = ≐-trans {a} {c} {b} (SFUEQ.sfu-eq sy ) (≐-sym {b} {c} (SFUEQ.sfu-eq sz ) )

               sx-conv :  {w y z : Ordinal}  → {sy : SFU y} {sz : SFU z}
                  → Feq F X∋x (SFU.U sy) (SFU.U sz) (SFU.s∈FU sy) (SFU.s∈FU sz)
                  → SFUEQ sy w → SFUEQ sz w
               sx-conv {w} {y} {z} {sy} {sz} y=z record { sx = sw ; sfu-eq = w=y } = record { sx = sw ; sfu-eq = ≐-trans {ew} {ey} {ez} w=y y=z  }  where
                   ew : HODElement HODSFU
                   ew = record { elt = w ; A∋elt = sw }
                   ey : HODElement HODSFU
                   ey = record { elt = y ; A∋elt = sy }
                   ez : HODElement HODSFU
                   ez = record { elt = z ; A∋elt = sz }

               sxabz1  : {a : HODElement HODSFU} {z : Ordinal}  → (az : odef (HODSFUEQ (A∋elt a)) z) → a ≐ record { elt = z ; A∋elt = SFUEQ.sx az }
               sxabz1 {a} {z} az  = ≐-sym {record { elt = z ; A∋elt = SFUEQ.sx az }} {a} (SFUEQ.sfu-eq az)

               sxabz  : {a b : HODElement HODSFU} {z : Ordinal}  → (az : odef (HODSFUEQ (A∋elt a)) z) → (bz : odef (HODSFUEQ (A∋elt b) ) z)
                 → a ≐ b
               sxabz {a} {b} {z} az bz = ≐-trans {a} {c} {b} (≐-sym {c} {a} lem01) (≐-trans {c} {d} {b} lem00 lem02) where
                  lem01 : Feq F X∋x (SFU.U (SFUEQ.sx az)) (SFU.U (A∋elt a))  (SFU.s∈FU (SFUEQ.sx az)) (SFU.s∈FU (A∋elt a))
                  lem01 = SFUEQ.sfu-eq az
                  lem02 : Feq F X∋x (SFU.U (SFUEQ.sx bz)) (SFU.U (A∋elt b))  (SFU.s∈FU (SFUEQ.sx bz)) (SFU.s∈FU (A∋elt b))
                  lem02 = SFUEQ.sfu-eq bz 
                  osab : OS (topology X) ∋ * (& (* (SFU.su (SFUEQ.sx az)) ∩ * (SFU.su (SFUEQ.sx bz))))
                  osab = subst (odef (OS (topology X))) (sym &iso) (o∩ (topology X) (SFU.osu (SFUEQ.sx az)) (SFU.osu (SFUEQ.sx bz)))
                  sab : Obj OX
                  sab = record { s = * (& (* (SFU.su (SFUEQ.sx az)) ∩ * (SFU.su (SFUEQ.sx bz)))) ; p = osab } 
                  lem04 : odef (FObj F (record { s = * (SFU.su (SFUEQ.sx az)) ; p = SFU.osu (SFUEQ.sx az) })) z
                  lem04 = SFU.s∈FU (SFUEQ.sx az)
                  lem05 : odef (FObj F (record { s = * (SFU.su (SFUEQ.sx bz)) ; p = SFU.osu (SFUEQ.sx bz) })) z
                  lem05 = SFU.s∈FU (SFUEQ.sx bz)
                  lem07 : odef (* (& (* (SFU.su (SFUEQ.sx az)) ∩ * (SFU.su (SFUEQ.sx bz))))) x
                  lem07 = eq← *iso ⟪ SFU.x∈su (SFUEQ.sx az) , SFU.x∈su (SFUEQ.sx bz) ⟫
                  c = record { elt = z ; A∋elt = SFUEQ.sx az } 
                  d = record { elt = z ; A∋elt = SFUEQ.sx bz }
                  lem00 : record { elt = z ; A∋elt = SFUEQ.sx az } ≐ record { elt = z ; A∋elt = SFUEQ.sx bz }
                  lem00 = record { w = & (* (SFU.su (SFUEQ.sx az)) ∩ * (SFU.su (SFUEQ.sx bz)))  ; ow = osab ; w⊆u∩v = λ lt → eq→ *iso lt
                   ; x∈w = lem07 ; feq = FOW F (λ lt → proj1 (eq→ *iso lt)) (λ lt → proj2 (eq→ *iso lt)) lem04 lem05 refl}

               ≐→h  : {a b : HODElement HODSFU} → a ≐ b → HODSFUEQ (A∋elt a) =h= HODSFUEQ (A∋elt b)
               ≐→h {a} {b} a=b  = record { eq→ = lem00 a=b  ; eq← = lem00 (≐-sym {a} {b} a=b ) } where
                    lem00 : {y : Ordinal} → {a b : HODElement HODSFU} → a ≐ b → SFUEQ (A∋elt a) y → SFUEQ (A∋elt b) y
                    lem00 {y} {a} {b} a=b record { sx = sx ; sfu-eq = c=a } = record { sx = sx
                       ; sfu-eq = ≐-trans {eqy sx} {eqy (A∋elt a)} {eqy (A∋elt b)} c=a a=b }

               h→≐  : {a b : HODElement HODSFU}  → HODSFUEQ (A∋elt a) =h= HODSFUEQ (A∋elt b) → a ≐ b
               h→≐ {a} {b} eq = sxabz ha hba where
                    hea : SFU (elt a)
                    hea =  A∋elt a
                    heb : SFU (elt b)
                    heb =  A∋elt b
                    ha : odef (HODSFUEQ hea) (elt a)
                    ha = record { sx = hea ; sfu-eq = ≐-refl {a} }
                    hba : odef (HODSFUEQ heb) (elt a)
                    hba = sx-conv {_} {_} {_} {_} {_}  (≐-refl {b}) ( eq→ eq  record { sx = hea ; sfu-eq = ≐-refl {a} } )

               ≐-refl-wld : {sy sz : HODElement HODSFU} → elt sy ≡ elt sz  → sy ≐ sz
               ≐-refl-wld {a} {b} eq = sxabz ha hb where
                    hea : SFU (elt a)
                    hea =  A∋elt a
                    heb : SFU (elt b)
                    heb =  A∋elt b
                    ha : odef (HODSFUEQ hea) (elt a)
                    ha = record { sx = hea ; sfu-eq = ≐-refl {a} }
                    hb : odef (HODSFUEQ heb) (elt a)
                    hb = subst (λ k → odef (HODSFUEQ heb) k ) (sym eq) ( record { sx = heb ; sfu-eq = ≐-refl {b} } )

--              new-sfu : {y z w : Ordinal}  → (sw : SFU w) → (sy : SFU y)
--                 → * (SFU.su sw) ⊆ * (SFU.su sy)
--                 → (swz : odef (HODSFUEQ sw) z)  → odef ( HODSFUEQ sy ) z
--              new-sfu {y} {z} {w} sw sy lt record { sx = sz ; sfu-eq = eq } = record { sx = sz 
--                 ; sfu-eq = ≐-trans eq record { w = SFU.su sw ; ow = ? ; w⊆u∩v = ? ; x∈w = ? ; feq = ? } } where
--
--                    --                                  |x
--                    --      ow          |------------------------|
--                    --      oz                    |------------------------|
--                    --      Feq.w eq                  |-----|
--                    --      oy                 |------------------------|

           --
           -- |Yf| def≡ {<x,[s]x> | ∃v∈OS(topology X) → x∈ U, s∈F(U) }
           --    base set of target topology
           --
           record YF (F : Functor OX HODSets) (y : Ordinal) : Set n where
              field
                 x s u : Ordinal
                 ou : OS (topology X) ∋ * u
              U : Obj OX
              U = record { s = * u ; p = ou }
              field
                 x∈U : odef (SObj.s U) x
                 s∈FU : odef (FObj F U ) s
                 is-pair : y ≡ & < * x , FEQ.HODSFUEQ F (os⊆L (topology X) ou x∈U ) record { su = u ; osu = ou ; s∈FU = s∈FU ; x∈su = x∈U }  >
              EQ∈PSX :  odef (Power (Power (space X))) (& (FEQ.HODSFUEQ F (os⊆L (topology X) ou x∈U ) record { su = u ; osu = ou ; s∈FU = s∈FU ; x∈su = x∈U } ))
              EQ∈PSX z pz with eq→ *iso pz
              ... | record { sx = sx ; sfu-eq = sfu-eq } = subst (λ k → odef (Power (space X)) k) &iso lem00 where
                   lem00 : odef (Power (space X)) (& (* z) )
                   lem00 = FEQ.SFU.PSX∋s sx
              sx∋x : space X ∋ * x
              sx∋x  = subst ( λ k → odef (space X) k) (sym &iso) (os⊆L (topology X) ou x∈U )
              YFM = ZFP (space X) (Power (Power (space X)))
              y<YFM : odef (ZFP (space X) (Power (Power (space X)))) y
              y<YFM = subst (λ k → odef (ZFP (space X) (Power (Power (space X)))) k ) (sym is-pair) (ZFP→ sx∋x EQ∈PSX)

           YFHOD :  (F : Functor OX HODSets) → HOD
           YFHOD F = record { od = record { def = λ x → YF F x } ; odmax = & (ZFP (space X) (Power (Power (space X))))  ; <odmax = lem00 } where
              lem00 : {y : Ordinal} → YF F y → y o< & (ZFP (space X) (Power (Power (space X))))
              lem00 {y} yf = odef< ( YF.y<YFM yf )

           --
           --    open set of target topology
           --
           -- V(s,U) def≡ {<x,[s]x> | ∃v∈OS(topology X) → x∈ U }
           --    open set of target topology
           --
           record YFO (F : Functor OX HODSets) {u : Ordinal}
                 (ou : OS (topology X) ∋ * u) (y : Ordinal) : Set n where
              field
                 x s : Ordinal
                 x∈U : odef (* u) x
                 s∈FU : odef (FObj F (record { s = * u ; p = ou }) ) s
                 is-pair : y ≡ &  < * x , FEQ.HODSFUEQ F (os⊆L (topology X) ou x∈U ) record { su = u ; osu = ou ; s∈FU = s∈FU ; x∈su = x∈U }  >
              EQ∈PSX :  odef (Power (Power (space X))) (& (FEQ.HODSFUEQ F (os⊆L (topology X) ou x∈U ) record { su = u ; osu = ou ; s∈FU = s∈FU ; x∈su = x∈U } ))
              EQ∈PSX z pz with eq→ *iso pz
              ... | record { sx = sx ; sfu-eq = sfu-eq } = subst (λ k → odef (Power (space X)) k) &iso lem00 where
                   lem00 : odef (Power (space X)) (& (* z) )
                   lem00 = FEQ.SFU.PSX∋s sx
              sx∋x : space X ∋ * x
              sx∋x  = subst ( λ k → odef (space X) k) (sym &iso) (os⊆L (topology X) ou x∈U )
              YFM = ZFP (space X) (Power (Power (space X)))
              y<YFM : odef (ZFP (space X) (Power (Power (space X)))) y
              y<YFM = subst (λ k → odef (ZFP (space X) (Power (Power (space X)))) k ) (sym is-pair) (ZFP→ sx∋x EQ∈PSX)

           record YFOs (F : Functor OX HODSets) (y : Ordinal) : Set n where
              field
                 u : Ordinal
                 ou : OS (topology X) ∋ * u
              lem00 : {x : Ordinal} → YFO F ou x → x o< & (ZFP (space X) (Power (Power (space X))))
              lem00 {y} yf = odef< ( YFO.y<YFM yf )
              field
                 is-open : y ≡ & record { od = record { def = λ x → YFO F ou x } ; odmax =  & (ZFP (space X) (Power (Power (space X))))
                         ; <odmax = lem00 }

           YPP : HOD
           YPP = ZFP (space X) (Power (Power (space X)))

           YFO→SFU : (F : Functor OX HODSets) {u : Ordinal} (ou : OS (topology X) ∋ * u) (y : Ordinal) 
                → (yf : YFO F ou y )
                → FEQ.SFU F (os⊆L (topology X) ou (YFO.x∈U yf) ) (YFO.s yf) 
           YFO→SFU F {u} ou y yf = record { su = _ ; osu = ou ; x∈su = YFO.x∈U yf  ; s∈FU = YFO.s∈FU yf} 

           YFO→HODSFUEQ : (F : Functor OX HODSets) {u : Ordinal} (ou : OS (topology X) ∋ * u) (y : Ordinal) 
                → (yf : YFO F ou y )
                → odef (FEQ.HODSFUEQ F (os⊆L (topology X) ou (YFO.x∈U yf) ) (YFO→SFU F ou y yf)) (YFO.s yf)
           YFO→HODSFUEQ F {u} ou y yf = record { sx = YFO→SFU F ou y yf ; sfu-eq = FEQ.≐-refl F (os⊆L (topology X) ou (YFO.x∈U yf) ) 
               {FEQ.eqy F (os⊆L (topology X) ou (YFO.x∈U yf) )(YFO→SFU F ou y yf )} }

           YFOHOD : (F : Functor OX HODSets) → HOD
           YFOHOD F = record { od = record { def = λ x → YFOs F x } ; odmax = & (Power YPP) ; <odmax = lem00 } where
               lem01 : {y : Ordinal} → YFOs F y → odef (Power YPP) y
               lem01 {y} yf z az with eq→ *iso (subst (λ k → odef k z ) ((cong (*) (YFOs.is-open yf))) az)
               ... | yfo = YFO.y<YFM yfo
               lem00 :  {y : Ordinal} → YFOs F y → y o< & (Power YPP)
               lem00 {y} yf = odef< (lem01 yf)

           YFO-eq-y :  ( F : Functor OX HODSets) → {u r : Ordinal} → (ou : OS (topology X) ∋ * u) (or : OS (topology X) ∋ * r) {y : Ordinal }
              → (yf0 : YFO F ou y) (yf1 : YFO F or y) → Feq F (os⊆L (topology X) ou (YFO.x∈U yf0) ) _ _ (YFO.s∈FU yf0) (YFO.s∈FU yf1)
           YFO-eq-y F {u} {r} ou or yf0 yf1 = FEQ.h→≐ F (os⊆L (topology X) ou (YFO.x∈U yf0)) lem01 where
               lem00 : FEQ.HODSFUEQ F (os⊆L (topology X) ou (YFO.x∈U yf0))
                    (record { su = u ; osu = ou ; x∈su = YFO.x∈U yf0 ; s∈FU = YFO.s∈FU yf0 })
                 =h=
                    FEQ.HODSFUEQ F (os⊆L (topology X) or (YFO.x∈U yf1))
                    (record { su = r ; osu = or ; x∈su = YFO.x∈U yf1 ; s∈FU = YFO.s∈FU yf1 })
               lem00 = proj2 (prod-eq (ord→== (trans (sym (YFO.is-pair yf0)) (YFO.is-pair yf1 ))))
               lem02 : YFO.x yf0 ≡ YFO.x yf1
               lem02 = trans (sym &iso) (trans ( ==→o≡ (proj1 (prod-eq (ord→== (trans (sym (YFO.is-pair yf0)) (YFO.is-pair yf1 ))))) ) &iso )
               lem01 : FEQ.HODSFUEQ F (os⊆L (topology X) ou (YFO.x∈U yf0))
                    (record { su = u ; osu = ou ; x∈su = YFO.x∈U yf0 ; s∈FU = YFO.s∈FU yf0 })
                 =h=
                    FEQ.HODSFUEQ F (os⊆L (topology X) ou (YFO.x∈U yf0))
                    (record { su = r ; osu = or ; x∈su = subst (λ k → odef (* r) k ) (sym lem02) (YFO.x∈U yf1)  ; s∈FU = YFO.s∈FU yf1 })
               lem01 = ==-trans lem00 record { eq→ = λ {z} lt → lem06 lt ; eq← = lem07 } where
                   lem06 : {z : Ordinal} (lt : FEQ.SFUEQ F (os⊆L (topology X) or (YFO.x∈U yf1)) (record
                        { su = r ; osu = or ; x∈su = YFO.x∈U yf1 ; s∈FU = YFO.s∈FU yf1 }) z) 
                      →  FEQ.SFUEQ F (os⊆L (topology X) ou (YFO.x∈U yf0))
                        (record { su = r ; osu = or ; x∈su = subst (λ k → HODBase.OD.def (od (* r)) k) (sym lem02) (YFO.x∈U yf1) ; s∈FU = YFO.s∈FU yf1 }) z
                   lem06 record { sx = sx ; sfu-eq = sfu-eq } = record { sx = record { su =  FEQ.SFU.su sx  ; osu = FEQ.SFU.osu sx  ; x∈su = lem05 
                         ; s∈FU =  FEQ.SFU.s∈FU sx } 
                         ; sfu-eq = record { w = _ ; ow = Feq.ow sfu-eq ; w⊆u∩v = Feq.w⊆u∩v sfu-eq  ; x∈w = lem08 ; feq = Feq.feq sfu-eq  }}  where
                       lem08 : odef (* (Feq.w sfu-eq)) (YFO.x yf0) 
                       lem08 = subst (λ k → odef (* (Feq.w sfu-eq)) k) (sym lem02) ( Feq.x∈w sfu-eq )
                       lem05 :  odef (* (FEQ.SFU.su sx)) (YFO.x yf0)
                       lem05 = subst ( λ k → odef (* (FEQ.SFU.su sx)) k ) (sym lem02) ( FEQ.SFU.x∈su sx   )
                   lem07 :  {z : Ordinal} → FEQ.SFUEQ F (os⊆L (topology X) ou (YFO.x∈U yf0))
                       (record { su = r ; osu = or ; x∈su = subst (λ k → HODBase.OD.def (od (* r)) k) (sym lem02) (YFO.x∈U yf1) ; s∈FU = YFO.s∈FU yf1 }) z 
                      → FEQ.SFUEQ F (os⊆L (topology X) or (YFO.x∈U yf1)) (record { su = r ; osu = or ; x∈su = YFO.x∈U yf1 ; s∈FU = YFO.s∈FU yf1 }) z
                   lem07 record { sx = sx ; sfu-eq = sfu-eq } = record { sx = record { su =  FEQ.SFU.su sx  ; osu = FEQ.SFU.osu sx  ; x∈su = lem05 
                         ; s∈FU =  FEQ.SFU.s∈FU sx } 
                         ; sfu-eq = record { w = _ ; ow = Feq.ow sfu-eq ; w⊆u∩v = Feq.w⊆u∩v sfu-eq  ; x∈w = lem08 ; feq = Feq.feq sfu-eq  }}  where
                       lem08 : odef (* (Feq.w sfu-eq)) (YFO.x yf1) 
                       lem08 = subst (λ k → odef (* (Feq.w sfu-eq)) k) lem02 ( Feq.x∈w sfu-eq )
                       lem05 :  odef (* (FEQ.SFU.su sx)) (YFO.x yf1)
                       lem05 = subst ( λ k → odef (* (FEQ.SFU.su sx)) k ) lem02 ( FEQ.SFU.x∈su sx   )

           YFOHOD-phi : (F : Functor OX HODSets) → odef (YFOHOD F) o∅ 
           YFOHOD-phi F = record {  u = o∅  ; ou = lem00 ; is-open = trans (sym ord-od∅) (sym ( ¬x∋y→x≡od∅ (yfo _) )) } where
               lem00 : OS (topology X) ∋ * o∅
               lem00 = subst (λ k → odef (OS (topology X)) k) (trans ord-od∅ (sym &iso))  (OS∋od∅ (topology X)) 
               yfo : (x : Ordinal) → ¬ ( YFO F lem00 x )
               yfo x₁ record { x = x ; x∈U = x∈U ; is-pair = is-pair } = ¬x<0 (eq→ o∅==od∅ x∈U )

           YFOHOD-fu : (F : Functor OX HODSets) { p : HOD } → (op : YFOHOD F ∋ p ) → {y : Ordinal} → odef p y → YFO F {_}  (YFOs.ou op) y 
           YFOHOD-fu F {p} op {y} py = eq→ *iso {y} (subst (λ k → odef (* k) y ) (YFOs.is-open op) (eq← *iso py ) )  

           YFTopology : (F : Functor OX HODSets) → Topology (YFHOD F)
           YFTopology F = record {
                 OS = YFOHOD F
               ; OS⊆PL = lem00
               ; o∩ = lem02
               ; o∪ = lem05
               ; OS∋od∅  = subst (λ k → odef (YFOHOD F) k ) (sym ord-od∅) ( YFOHOD-phi F )
             } where
                lem00 : YFOHOD F ⊆ Power (YFHOD F)
                lem00 {x} record { u = u ;  ou = ou ;  is-open = is-open } y xy
                   = record  { x = YFO.x lem01 ; u = u ; x∈U = YFO.x∈U lem01 ;  is-pair = YFO.is-pair lem01 } where
                      lem01 : YFO F {u}  ou  y
                      lem01 = eq→ *iso {y} (subst (λ k → odef (* k) y ) is-open  xy )
                lem06 : {p q : HOD} → (& p ≡  o∅) ∨ (& q ≡ o∅)  → {x : Ordinal } → ¬ ( odef (p ∩ q) x )
                lem06 {p} {q} (case1 p=0) lt = ⊥-elim (¬x<0 (eq→ (≡o∅→=od∅ p=0) (proj1 lt) ))
                lem06 {p} {q} (case2 q=0) lt = ⊥-elim (¬x<0 (eq→ (≡o∅→=od∅ q=0) (proj2 lt) ))
                lem03 : {p q : HOD} → (& p ≡  o∅) ∨ (& q ≡ o∅)  → od∅ =h= (p ∩ q)
                lem03 {p} {q} eq = record { eq→ = λ lt → ⊥-elim (¬x<0 lt) ; eq← = λ lt → ⊥-elim (lem06 eq lt) }
                lem02 : {p q : HOD} → YFOHOD F ∋ p → YFOHOD F ∋ q → YFOHOD F ∋ (p ∩ q)
                lem02 {p} {q} op oq = record {  u = & ( * (YFOs.u op) ∩ * (YFOs.u oq))  
                           ; ou = subst (λ k → odef (OS (topology X)) k) (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))
                           ; is-open = ==→o≡ lem04 }  where
                      pox : Obj OX
                      pox = record { s = * (YFOs.u op) ; p = YFOs.ou op }
                      qox : Obj OX
                      qox = record { s = * (YFOs.u oq) ; p = YFOs.ou oq }
                      yp∩q : Obj OX
                      yp∩q = record { s = (* (YFOs.u op) ∩ * (YFOs.u oq)) ; p = o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)  }
                      lem04 : ( p ∩ q ) =h= record { od = record { def = λ x →  YFO F
                                (subst (λ k → odef (OS (topology X)) k) (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)))  x
                                   }  ; odmax = & (ZFP (space X) (Power (Power (space X))))
                                             ; <odmax = λ yf → odef< (YFO.y<YFM yf) }
                      lem04 = record { eq→ = lem10 ; eq← = lemr10 } where
                         lemr10 : {y : Ordinal} → YFO F (subst (λ k → odef (OS (topology X)) k)
                                 (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) y
                            → odef (p ∩ q) y
                         lemr10 {y} yf = ⟪ eq← (ord→== (YFOs.is-open  op)) lem31 , ? ⟫ where
                             lem30 : & p ≡ & record { od = record { def = λ x → YFO F (YFOs.ou op)  x }
                                 ; odmax =  & (ZFP (space X) (Power (Power (space X))))  ; <odmax = _ }
                             lem30 = YFOs.is-open  op
                             oxpq : Obj OX
                             oxpq = record { s = * (& (* (YFOs.u op) ∩ * (YFOs.u oq))) 
                                 ; p = subst (λ k → odef (OS (topology X)) k) (sym &iso) ( o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))  }
                             lem32 : odef (* (YFOs.u op) ∩ * (YFOs.u oq)) (YFO.x yf)
                             lem32 = eq→ *iso (YFO.x∈U yf)
                             lem34 : odef (FObj F oxpq ) (YFO.s yf)
                             lem34 = YFO.s∈FU yf
                             lem33 : odef (FObj F (record { s = * (YFOs.u op) ; p = YFOs.ou op })) (YFO.s yf)
                             lem33 = FU F (λ lt → proj1 (eq→ *iso lt))  (YFO.s∈FU yf) refl 
                             lem44 : odef (FObj F (record { s = * (YFOs.u oq) ; p = YFOs.ou oq })) (YFO.s yf)
                             lem44 = FU F (λ lt → proj2 (eq→ *iso lt))  (YFO.s∈FU yf) refl 
                             lem35 : FEQ.HODSFUEQ F (os⊆L (topology X)
                                     (subst (λ x → HODBase.OD.def (od (OS (topology X))) x) (sym &iso) 
                                         (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) (YFO.x∈U yf))
                                            (record
                                             { su = & (* (YFOs.u op) ∩ * (YFOs.u oq))
                                             ; osu = subst (λ x → HODBase.OD.def (od (OS (topology X))) x)
                                                 (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))
                                         ; x∈su = YFO.x∈U yf ; s∈FU = YFO.s∈FU yf })
                                 =h= FEQ.HODSFUEQ F (os⊆L (topology X) (YFOs.ou op) (proj1 lem32))
                                        (record { su = YFOs.u op ; osu = YFOs.ou op ; x∈su = proj1 lem32 ; s∈FU = lem33 })
                             lem35 = record { eq→ = lem36 ; eq← = lem37 } where
                                 lem36 : {x : Ordinal} → FEQ.SFUEQ F
                                    (os⊆L (topology X) (subst (λ x₁ → HODBase.OD.def (od (OS (topology X))) x₁)
                                      (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) (YFO.x∈U yf))
                                    (record { su = & (* (YFOs.u op) ∩ * (YFOs.u oq)) ; osu =
                                         subst (λ x₁ → HODBase.OD.def (od (OS (topology X))) x₁)
                                         (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)) ; x∈su = YFO.x∈U yf ; s∈FU = YFO.s∈FU yf
                                     }) x →
                                    FEQ.SFUEQ F (os⊆L (topology X) (YFOs.ou op) (proj1 lem32)) (record
                                     { su = YFOs.u op ; osu = YFOs.ou op ; x∈su = proj1 lem32 ; s∈FU = lem33 }) x
                                 lem36 record { sx = record { su = su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU } 
                                     ; sfu-eq = record { w = w ; ow = ow ; w⊆u∩v = w⊆u∩v ; x∈w = x∈w ; feq = feq } } = 
                                     record { sx = record { su = su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU } 
                                     ; sfu-eq = record { w = w ; ow = ow ; w⊆u∩v = lem37 ; x∈w = x∈w ; feq = lem38 } } where
                                        lem37 : * w ⊆ (* su ∩ * (YFOs.u op))
                                        lem37 lt = ⟪ proj1 (w⊆u∩v lt) , proj1 (eq→ *iso (proj2 (w⊆u∩v lt))) ⟫ 
                                        os05 : Obj OX
                                        os05 = record { s = * su ; ou = osu }
                                        os06 : Obj OX
                                        os06 = record { s = * w ; p = ow }
                                        lem38 : Func.func (FMap F {os05} {os06} (λ lt → proj1 (lem37 lt))) s∈FU 
                                             ≡ Func.func (FMap F {pox} {os06} (λ lt → proj2 (lem37 lt))) lem33
                                        lem38 = begin
                                           Func.func (FMap F (λ lt → proj1 (lem37 lt))) s∈FU ≡⟨ feq ⟩
                                           Func.func (FMap F (λ lt → proj2 (w⊆u∩v lt))) (YFO.s∈FU yf)  ≡⟨ FOW F _ _  _ _  refl ⟩
                                           Func.func (FMap F (λ lt → proj2 (lem37 lt))) lem33 ∎ 
                                             where 
                                               open ≡-Reasoning
                                 lem37 : {x : Ordinal} 
                                     → FEQ.SFUEQ F (os⊆L (topology X) (YFOs.ou op) (proj1 lem32)) (record
                                     { su = YFOs.u op ; osu = YFOs.ou op ; x∈su = proj1 lem32 ; s∈FU = lem33 }) x
                                     → FEQ.SFUEQ F
                                    (os⊆L (topology X) (subst (λ x₁ → HODBase.OD.def (od (OS (topology X))) x₁)
                                      (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) (YFO.x∈U yf))
                                        (record { su = & (* (YFOs.u op) ∩ * (YFOs.u oq)) ; osu =
                                             subst (λ x₁ → HODBase.OD.def (od (OS (topology X))) x₁)
                                             (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)) ; x∈su = YFO.x∈U yf ; s∈FU = YFO.s∈FU yf
                                         }) x 
                                 lem37 record { sx = record { su = su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU } 
                                     ; sfu-eq = record { w = w ; ow = ow ; w⊆u∩v = w⊆u∩v ; x∈w = x∈w ; feq = feq } } = 
                                     record { sx = record { su = su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU } 
                                     ; sfu-eq = record { w = & ( * w ∩ (* (YFOs.u oq))) ; ow = lem40 ; w⊆u∩v = lem39 ; x∈w = lem41 ; feq = lem38 } } where
                                        lem39 : * (& (* w ∩ * (YFOs.u oq))) ⊆ (* su ∩ * (& (* (YFOs.u op) ∩ * (YFOs.u oq))))
                                        lem39 {z} lt = ⟪ proj1 (w⊆u∩v lem40) ,  eq← *iso ⟪ proj2 (w⊆u∩v lem40)   , proj2 (eq→ *iso lt) ⟫ ⟫ where
                                            lem40 : odef (* w) z
                                            lem40 =  proj1 (eq→ *iso lt)
                                        lem40 : OS (topology X) ∋ * (& (* w ∩ * (YFOs.u oq)))
                                        lem40 = subst (λ k → odef (OS (topology X)) k ) (sym &iso) (o∩ (topology X) ow (YFOs.ou oq) ) 
                                        lem41 : odef (* (& (* w ∩ * (YFOs.u oq)))) (YFO.x yf)
                                        lem41 = eq← *iso ⟪  x∈w  , proj2 (eq→ *iso ( YFO.x∈U yf))  ⟫
                                        os05 : Obj OX
                                        os05 = record { s = * su ; p = osu }
                                        os06 : Obj OX
                                        os06 = record { s = * w ; p = ow }
                                        os07 : Obj OX
                                        os07 = record { s = * (& (* w ∩ * (YFOs.u oq))) ; p = lem40 }
                                        os09 : Obj OX
                                        os09 = record { s = * (& (* (YFOs.u op) ∩ * (YFOs.u oq))) 
                                             ; p = subst (λ k → odef (OS (topology X)) k) (sym &iso) ( o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))  }
                                        lem42 : Hom OX os06 os07
                                        lem42 lt = proj1 ( eq→ *iso lt )
                                        lem43 : Hom OX pox os07
                                        lem43 lt = proj2 ( w⊆u∩v (proj1 (eq→ *iso lt ) ) )
                                        lem38 : Func.func (FMap F (λ lt → proj1 (lem39 lt))) s∈FU ≡ Func.func (FMap F (λ lt → proj2 (lem39 lt))) (YFO.s∈FU yf)
                                        lem38 = begin
                                           Func.func (FMap F {os05} {os07} (λ lt → proj1 (lem39 lt))) s∈FU ≡⟨ Fdistr F _ _ _ _  ⟩
                                           Func.func (FMap F {os06} {os07} lem42) (Func.is-func (FMap F {os05} {os06} (λ lt → proj1 (w⊆u∩v lt))) s∈FU) 
                                               ≡⟨ OXFcong F _ _ _ _ feq  ⟩
                                           Func.func (FMap F {os06} {os07} lem42) (Func.is-func (FMap F {pox} {os06} (λ lt → proj2 (w⊆u∩v lt))) lem33) 
                                               ≡⟨  sym (Fdistr F _ _ _ _) ⟩
                                           Func.func (FMap F {pox} {os07} lem43) lem33 ≡⟨  FOW F _ _  _ _  refl ⟩
                                           Func.func (FMap F {os09} {os07} (λ lt → proj2 (lem39 lt))) (YFO.s∈FU yf) ∎ 
                                             where 
                                               open ≡-Reasoning
                             lem31 : YFO F (YFOs.ou op)  y
                             lem31 = record { x = YFO.x yf ; x∈U = proj1 lem32 ; s = YFO.s yf ;  s∈FU = lem33 
                                  ; is-pair = trans (YFO.is-pair yf) (==→o≡ (prod-cong-== ==-refl lem35 ) ) }
                             lem45 : FEQ.HODSFUEQ F (os⊆L (topology X)
                                     (subst (λ x → HODBase.OD.def (od (OS (topology X))) x) (sym &iso) 
                                         (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) (YFO.x∈U yf))
                                            (record
                                             { su = & (* (YFOs.u op) ∩ * (YFOs.u oq))
                                             ; osu = subst (λ x → HODBase.OD.def (od (OS (topology X))) x)
                                                 (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))
                                         ; x∈su = YFO.x∈U yf ; s∈FU = YFO.s∈FU yf })
                                 =h= FEQ.HODSFUEQ F (os⊆L (topology X) (YFOs.ou oq) (proj2 lem32))
                                        (record { su = YFOs.u oq ; osu = YFOs.ou oq ; x∈su = proj2 lem32 ; s∈FU = lem44 })
                             lem45 = record { eq→ = lem36 ; eq← = lem37 } where
                                 lem36 : {x : Ordinal} → FEQ.SFUEQ F
                                    (os⊆L (topology X) (subst (λ x₁ → HODBase.OD.def (od (OS (topology X))) x₁)
                                      (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) (YFO.x∈U yf))
                                    (record { su = & (* (YFOs.u op) ∩ * (YFOs.u oq)) ; osu =
                                         subst (λ x₁ → HODBase.OD.def (od (OS (topology X))) x₁)
                                         (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)) ; x∈su = YFO.x∈U yf ; s∈FU = YFO.s∈FU yf
                                     }) x →
                                    FEQ.SFUEQ F (os⊆L (topology X) (YFOs.ou oq) (proj2 lem32)) (record
                                     { su = YFOs.u oq ; osu = YFOs.ou oq ; x∈su = proj2 lem32 ; s∈FU = lem44 }) x
                                 lem36 record { sx = record { su = su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU } 
                                     ; sfu-eq = record { w = w ; ow = ow ; w⊆u∩v = w⊆u∩v ; x∈w = x∈w ; feq = feq } } = 
                                     record { sx = record { su = su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU } 
                                     ; sfu-eq = record { w = w ; ow = ow ; w⊆u∩v = lem37 ; x∈w = x∈w ; feq = lem38 } } where
                                        lem37 : * w ⊆ (* su ∩ * (YFOs.u oq))
                                        lem37 lt = ⟪ proj1 (w⊆u∩v lt) , proj2 (eq→ *iso (proj2 (w⊆u∩v lt))) ⟫ 
                                        os05 : Obj OX
                                        os05 = record { s = * su ; ou = osu }
                                        os06 : Obj OX
                                        os06 = record { s = * w ; p = ow }
                                        lem38 : Func.func (FMap F {os05} {os06} (λ lt → proj1 (lem37 lt))) s∈FU 
                                             ≡ Func.func (FMap F {qox} {os06} (λ lt → proj2 (lem37 lt))) lem44
                                        lem38 = begin
                                           Func.func (FMap F (λ lt → proj1 (lem37 lt))) s∈FU ≡⟨ feq ⟩
                                           Func.func (FMap F (λ lt → proj2 (w⊆u∩v lt))) (YFO.s∈FU yf)  ≡⟨ FOW F _ _  _ _  refl ⟩
                                           Func.func (FMap F (λ lt → proj2 (lem37 lt))) lem44 ∎ 
                                             where 
                                               open ≡-Reasoning
                                 lem37 : {x : Ordinal} 
                                     → FEQ.SFUEQ F (os⊆L (topology X) (YFOs.ou oq) (proj2 lem32)) (record
                                     { su = YFOs.u oq ; osu = YFOs.ou oq ; x∈su = proj2 lem32 ; s∈FU = lem44 }) x
                                     → FEQ.SFUEQ F
                                    (os⊆L (topology X) (subst (λ x₁ → HODBase.OD.def (od (OS (topology X))) x₁)
                                      (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) (YFO.x∈U yf))
                                        (record { su = & (* (YFOs.u op) ∩ * (YFOs.u oq)) ; osu =
                                             subst (λ x₁ → HODBase.OD.def (od (OS (topology X))) x₁)
                                             (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)) ; x∈su = YFO.x∈U yf ; s∈FU = YFO.s∈FU yf
                                         }) x 
                                 lem37 record { sx = record { su = su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU } 
                                     ; sfu-eq = record { w = w ; ow = ow ; w⊆u∩v = w⊆u∩v ; x∈w = x∈w ; feq = feq } } = 
                                     record { sx = record { su = su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU } 
                                     ; sfu-eq = record { w = & ( * w ∩ (* (YFOs.u op))) ; ow = lem40 ; w⊆u∩v = lem39 ; x∈w = lem41 ; feq = lem38 } } where
                                        lem39 : * (& (* w ∩ * (YFOs.u op))) ⊆ (* su ∩ * (& (* (YFOs.u op) ∩ * (YFOs.u oq))))
                                        lem39 {z} lt = ⟪ proj1 (w⊆u∩v lem40) ,  eq← *iso ⟪ proj2 (eq→ *iso lt) , proj2 (w⊆u∩v lem40) ⟫ ⟫ where 
                                            lem40 : odef (* w) z
                                            lem40 =  proj1 (eq→ *iso lt)
                                        lem40 : OS (topology X) ∋ * (& (* w ∩ * (YFOs.u op)))
                                        lem40 = subst (λ k → odef (OS (topology X)) k ) (sym &iso) (o∩ (topology X) ow (YFOs.ou op) ) 
                                        lem41 : odef (* (& (* w ∩ * (YFOs.u op)))) (YFO.x yf)
                                        lem41 = eq← *iso ⟪ x∈w , proj1 (eq→ *iso ( YFO.x∈U yf))  ⟫
                                        os05 : Obj OX
                                        os05 = record { s = * su ; p = osu }
                                        os06 : Obj OX
                                        os06 = record { s = * w ; p = ow }
                                        os07 : Obj OX
                                        os07 = record { s = * (& (* w ∩ * (YFOs.u op))) ; p = lem40 }
                                        os09 : Obj OX
                                        os09 = record { s = * (& (* (YFOs.u op) ∩ * (YFOs.u oq))) 
                                             ; p = subst (λ k → odef (OS (topology X)) k) (sym &iso) ( o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))  }
                                        lem42 : Hom OX os06 os07
                                        lem42 lt = proj1 ( eq→ *iso lt )
                                        lem43 : Hom OX qox os07
                                        lem43 lt = proj2 ( w⊆u∩v (proj1 (eq→ *iso lt ) ) )
                                        lem38 : Func.func (FMap F (λ lt → proj1 (lem39 lt))) s∈FU ≡ Func.func (FMap F (λ lt → proj2 (lem39 lt))) (YFO.s∈FU yf)
                                        lem38 = begin
                                           Func.func (FMap F {os05} {os07} (λ lt → proj1 (lem39 lt))) s∈FU ≡⟨ Fdistr F _ _ _ _  ⟩
                                           Func.func (FMap F {os06} {os07} lem42) (Func.is-func (FMap F {os05} {os06} (λ lt → proj1 (w⊆u∩v lt))) s∈FU) 
                                               ≡⟨ OXFcong F _ _ _ _ feq  ⟩
                                           Func.func (FMap F {os06} {os07} lem42) (Func.is-func (FMap F {qox} {os06} (λ lt → proj2 (w⊆u∩v lt))) lem44) 
                                               ≡⟨  sym (Fdistr F _ _ _ _) ⟩
                                           Func.func (FMap F {qox} {os07} lem43) lem44 ≡⟨  FOW F _ _  _ _  refl ⟩
                                           Func.func (FMap F {os09} {os07} (λ lt → proj2 (lem39 lt))) (YFO.s∈FU yf) ∎ 
                                             where 
                                               open ≡-Reasoning
                             lem41 : YFO F (YFOs.ou oq)  y
                             lem41 = record { x = YFO.x yf ; x∈U = proj2 lem32 ; s = YFO.s yf ;  s∈FU = lem44
                                  ; is-pair = trans (YFO.is-pair yf) (==→o≡ (prod-cong-== ==-refl lem45 ) ) }
                         lem10 : {y : Ordinal} → odef (p ∩ q) y →
                                YFO F (subst (λ k → odef (OS (topology X)) k)
                                 (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) y
                         lem10  {y} ⟪ opy , oqy ⟫ = record { x = YFO.x yqoy  ; x∈U = lem13  ; s = _ ; s∈FU = fupq ; is-pair = lem12 } where
                             ypoy : YFO F (YFOs.ou op)  y
                             ypoy = eq→ ( ord→== (YFOs.is-open op) ) opy
                             y=pxf : y ≡ &  < * (YFO.x ypoy) , FEQ.HODSFUEQ F (os⊆L (topology X) (YFOs.ou op) (YFO.x∈U ypoy)  )
                                 record { u = YFOs.u op ; ou = YFOs.ou op }  >
                             yqoy : YFO F (YFOs.ou oq)  y
                             yqoy = eq→ ( ord→== (YFOs.is-open oq) ) oqy
                             y=pxf = YFO.is-pair ypoy
                             y=qxf : y ≡ &  < * (YFO.x yqoy) , FEQ.HODSFUEQ F (os⊆L (topology X) (YFOs.ou oq) (YFO.x∈U yqoy)  )
                                 record { u = YFOs.u oq ; ou = YFOs.ou oq }  >
                             y=qxf = YFO.is-pair yqoy 
                             os03 : Obj OX
                             os03 = record { s = * (& (* (YFOs.u op) ∩ * (YFOs.u oq))) 
                                 ; p = subst (λ k → odef (OS (topology X)) k) (sym &iso) ( o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))  }
                             upq : Obj OX
                             upq = record { s = * (& (* (YFOs.u op) ∩ * (YFOs.u oq))) ; p =
                                  subst (odef (OS (topology X))) (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)) }
                             fupq : odef (FObj F upq) 
                                     (Func.func (FMap F (λ lt → proj2 (eq→ *iso lt) )) (YFO.s∈FU yqoy))
                             fupq = Func.is-func (FMap F (λ lt → proj2 (eq→ *iso lt) )) (YFO.s∈FU yqoy)
                             fupq-eq : Func.func (FMap F {qox} {os03} (λ lt → proj2 (eq→ *iso lt) )) (YFO.s∈FU yqoy) ≡ 
                                       Func.func (FMap F {qox} {qox} (λ lt → lt)) (YFO.s∈FU yqoy) 
                             fupq-eq = FOW F _ _  _ _  refl
                             lem14 : { x y : HOD } → & < x , y > ≡ & < x , * ( & y ) >
                             lem14 {x} {y} = ==→o≡ (prod-cong-== ==-refl (==-sym *iso) )
                             yp=yq : YFO.x ypoy ≡ YFO.x yqoy
                             yp=yq = proj1 ( prod-≡ (  trans (trans (sym lem14) (trans (sym y=pxf) y=qxf) ) lem14 ))
                             lem13 :  odef (* (& (* (YFOs.u op) ∩ * (YFOs.u oq)))) (YFO.x yqoy)
                             lem13  = eq← *iso ⟪ subst (λ k → odef (* (YFOs.u op)) k) yp=yq (YFO.x∈U ypoy)
                                               , subst (λ k → odef (* (YFOs.u oq)) k) refl (YFO.x∈U yqoy) ⟫
                             lem31 : FEQ.HODSFUEQ F (os⊆L (topology X) (YFOs.ou oq) (YFO.x∈U yqoy))
                                    record { u = YFOs.u oq ; ou = YFOs.ou oq }
                                 =h= FEQ.HODSFUEQ F (os⊆L (topology X) (YFOs.ou op) (YFO.x∈U ypoy)  )
                                    record { u = YFOs.u op ; ou = YFOs.ou op }
                             lem31 = ==-iso  ( proj2 ( prod-eq ( (ord→== ( trans (trans (sym lem14) (trans (sym y=qxf) y=pxf) ) lem14 )) )) )
                             lem32 :  odef (* (& (* (YFOs.u op) ∩ * (YFOs.u oq)))) (YFO.x yqoy)
                             lem32 = eq← *iso ⟪  subst (λ k → odef (* (YFOs.u op)) k) yp=yq (YFO.x∈U ypoy) , YFO.x∈U yqoy ⟫
                             lem30 : FEQ.HODSFUEQ F (os⊆L (topology X) (YFOs.ou oq) (YFO.x∈U yqoy))
                                (record { su = YFOs.u oq ; osu = YFOs.ou oq ; x∈su = YFO.x∈U yqoy ; s∈FU = YFO.s∈FU yqoy })
                                =h=
                                FEQ.HODSFUEQ F (os⊆L (topology X)
                                 (subst (λ x → odef (OS (topology X)) x) (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) lem13)
                                    (record { su = & (* (YFOs.u op) ∩ * (YFOs.u oq)) ; osu = subst (λ x → odef (OS (topology X)) x)
                                     (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)) ; x∈su = lem13 ; s∈FU = fupq })
                             lem30 = record { eq→ = lem34 ; eq← = lem50 } where
                                 lem34 : {z : Ordinal } → odef (FEQ.HODSFUEQ F (os⊆L (topology X) (YFOs.ou oq) (YFO.x∈U yqoy))
                                    (record { su = YFOs.u oq ; osu = YFOs.ou oq ; x∈su = YFO.x∈U yqoy ; s∈FU = YFO.s∈FU yqoy })) z
                                    → 
                                    odef (FEQ.HODSFUEQ F (os⊆L (topology X)
                                   (subst (λ x → odef (OS (topology X)) x) (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) lem13)
                                    (record { su = & (* (YFOs.u op) ∩ * (YFOs.u oq)) ; osu = subst (λ x → odef (OS (topology X)) x)
                                     (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)) ; x∈su = lem13 ; s∈FU = fupq })) z
                                 lem34 {z} record { sx = record { su = su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU } 
                                   ; sfu-eq = record { w = w ; ow = ow ; w⊆u∩v = w⊆u∩v ; x∈w = x∈w ; feq = feq } } = 
                                        record { sx = record { su =  su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU  } 
                                     ; sfu-eq = record { w = & (* w ∩ (* (YFOs.u op)))  ; ow = lem42 ; w⊆u∩v = lem35 ; x∈w = lem43 ; feq = lem36 } } where
                                         os01 : Obj OX
                                         os01 = record { s = * su ; p = osu }
                                         lem42 : OS (topology X) ∋ * (& (* w ∩ * (YFOs.u op)))
                                         lem42 = subst (λ k → odef (OS (topology X)) k) (sym &iso) (o∩ (topology X) ow (YFOs.ou op)) 
                                         os02 : Obj OX
                                         os02 = record { s = *  (& (* w  ∩ * (YFOs.u op))) ; p = lem42 }
                                         os04 : Obj OX
                                         os04 = record { s = *  w ; p = ow  }
                                         os05 : Obj OX
                                         os05 = record { s =  * (& ((* (YFOs.u op)) ∩ (* (YFOs.u oq))))  
                                              ; p = subst (λ k → odef (OS (topology X)) k) (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))}
                                         lem43 : odef (* (& (* w ∩ * (YFOs.u op)))) (YFO.x yqoy)
                                         lem43 = eq← *iso ⟪ x∈w  , proj1 (eq→ *iso lem45) ⟫ where
                                               lem45 :  odef (* (& (* (YFOs.u op) ∩ * (YFOs.u oq)))) (YFO.x yqoy)
                                               lem45 = lem13
                                         lem37 : Hom OX os04 os02
                                         lem37 lt = proj1 (eq→  *iso lt) 
                                         lem38 : Hom OX os03 os02
                                         lem38 lt = eq← *iso ⟪ proj2 lem39 , proj2 (w⊆u∩v (proj1 lem39)) ⟫ where
                                            lem39 = eq→  *iso lt
                                         lem40 : Hom OX qox os02
                                         lem40 lt = proj2 (w⊆u∩v (proj1 lem39))  where
                                            lem39 = eq→  *iso lt
                                         lem35  : * (& (* w ∩ (* (YFOs.u op)))) ⊆ (* su ∩ (* ( & (* (YFOs.u op) ∩ * (YFOs.u oq)))))
                                         lem35 {z} lt =  ⟪ proj1 (w⊆u∩v lem47) , eq← *iso ⟪ proj2  (eq→ *iso lt) , proj2 (w⊆u∩v lem47) ⟫ ⟫  where
                                             lem46  : * w  ⊆ (* su ∩ (* (YFOs.u oq)))
                                             lem46  = w⊆u∩v
                                             lem47 : odef (* w) z
                                             lem47 = proj1 (eq→ *iso lt)
                                         lem36 : Func.func (FMap F {os01} {os02} (λ lt → proj1 (lem35 lt))) s∈FU 
                                            ≡ Func.func  (FMap F {os03} {os02} (λ lt → proj2 (lem35 lt))) fupq
                                         lem36 = begin
                                            Func.func (FMap F {os01} {os02} (λ lt → proj1 (lem35 lt))) s∈FU ≡⟨ Fdistr F _ _ _ _ ⟩
                                            Func.func (FMap F {os04} {os02} lem37) (Func.is-func (FMap F (λ lt → proj1 (w⊆u∩v lt))) s∈FU) ≡⟨ OXFcong F _ _ _ _ feq ⟩
                                            Func.func (FMap F {os04} {os02} lem37) (Func.is-func (FMap F {qox} {os04} (λ lt → proj2 (w⊆u∩v lt))) (YFO.s∈FU yqoy)) 
                                                 ≡⟨ FOW F _ _ _ _ (FOW F _ _ _ _ refl ) ⟩
                                            Func.func (FMap F {os03} {os02} lem38) (Func.is-func (FMap F {qox} {os03} (λ lt → proj2 (eq→ *iso lt) )) (YFO.s∈FU yqoy)) 
                                                 ≡⟨ FOW F _ _  _ _ fupq-eq ⟩
                                            Func.func (FMap F {qox} {os02} lem40) (Func.is-func (FMap F {qox} {qox} (λ lt → lt)) (YFO.s∈FU yqoy)) 
                                                 ≡⟨ Func.func-wld (FMap F {qox} {os02} lem40) _ _ (Fid F _ _ _ )  ⟩
                                            Func.func (FMap F {qox} {os02} lem40) (YFO.s∈FU yqoy) ≡⟨ OXFcong F _ _ _ _ refl ⟩
                                            Func.func (FMap F {qox} {os02} _) (YFO.s∈FU yqoy) ≡⟨ Fdistr F _ _ _ _ ⟩
                                            Func.func (FMap F {os03} {os02} (λ lt → proj2 (lem35 lt))) fupq ∎ where
                                               open ≡-Reasoning
                                 lem50 : {z : Ordinal } → 
                                   odef (FEQ.HODSFUEQ F (os⊆L (topology X)
                                    (subst (λ x → odef (OS (topology X)) x) (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) lem13)
                                    (record { su = & (* (YFOs.u op) ∩ * (YFOs.u oq)) ; osu = subst (λ x → odef (OS (topology X)) x)
                                     (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)) ; x∈su = lem13 ; s∈FU = fupq })) z
                                    → odef (FEQ.HODSFUEQ F (os⊆L (topology X) (YFOs.ou oq) (YFO.x∈U yqoy))
                                    (record { su = YFOs.u oq ; osu = YFOs.ou oq ; x∈su = YFO.x∈U yqoy ; s∈FU = YFO.s∈FU yqoy })) z
                                 lem50 {z} record { sx = record { su = su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU } 
                                   ; sfu-eq = record { w = w ; ow = ow ; w⊆u∩v = w⊆u∩v ; x∈w = x∈w ; feq = feq } } = 
                                        record { sx = record { su =  su ; osu = osu ; x∈su = x∈su ; s∈FU = s∈FU  } 
                                     ; sfu-eq = record { w = w  ; ow = ow ; w⊆u∩v = lem52 ; x∈w = x∈w ; feq = lem51 } } where
                                        os05 : Obj OX
                                        os05 = record { s = * su ; p = osu }
                                        os06 : Obj OX
                                        os06 = record { s = * w ; p = ow }
                                        lem53 : Hom OX qox os06
                                        lem53 lt = proj2 ( eq→ *iso (proj2 ( w⊆u∩v lt )) )
                                        lem52 : * w ⊆ (* su ∩ * (YFOs.u oq) )
                                        lem52 lt =  ⟪ proj1 ( w⊆u∩v lt ) , proj2 (eq→ *iso (proj2 ( w⊆u∩v lt )) ) ⟫ 
                                        lem51 : Func.func (FMap F (λ lt → proj1 (lem52 lt))) s∈FU ≡ Func.func (FMap F (λ lt → proj2 (lem52 lt))) (YFO.s∈FU yqoy)
                                        lem51 = begin
                                           Func.func (FMap F {os05} {os06} (λ lt → proj1 (lem52 lt))) s∈FU ≡⟨ feq ⟩
                                           Func.func (FMap F (λ lt → proj2 (w⊆u∩v lt))) fupq  ≡⟨ FOW F _ _  _ _ fupq-eq ⟩
                                           Func.func (FMap F {qox} {os06} lem53) (Func.is-func (FMap F {qox} {qox} (λ lt → lt)) (YFO.s∈FU yqoy))  
                                               ≡⟨ sym ( Fdistr F _ _ _ _) ⟩
                                           Func.func (FMap F (λ lt → proj2 (lem52 lt))) (YFO.s∈FU yqoy) ∎  where
                                               open ≡-Reasoning
                             lem12 : y ≡ & < * (YFO.x yqoy) ,
                                        FEQ.HODSFUEQ F (os⊆L (topology X) (subst (odef (OS (topology X))) (sym &iso)
                                              (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq))) lem13)
                                    (record { su = & (* (YFOs.u op) ∩ * (YFOs.u oq))
                                     ; osu = subst (odef (OS (topology X))) (sym &iso) (o∩ (topology X) (YFOs.ou op) (YFOs.ou oq)) ; x∈su = lem13 ; s∈FU = fupq }) >
                             lem12 = trans y=qxf (==→o≡ (prod-cong-== ==-refl lem30 ) )
                lem05 : {P : HOD} → P ⊆ YFOHOD F → YFOHOD F ∋ Union P
                lem05 = ?

           --     [s]x modulo s|w = t|w
           --  |Yf| ≡ {(x,[s]x)|∃ U∈O(X) (x∈ U ∧ s∈ F(U)) } = ∪ (F x) x∈ X, where F x = lim F(U) = ∪ F(U)/~x --                                                                          x ∈ U
           --  OS |Yf|  ≡ {(x,[s]x)|x∈ U ∧ s ∈ F(U) }

           YFunc : (F : Functor OX HODSets) → Func (YFHOD F) (space X)
           YFunc F = ? -- record {
--                       func = λ {x} lt → YF.x lt
--                     ; is-func = λ {x} ax → OS⊆PL (topology X) (YF.ou ax ) _ (subst (λ k → odef _ k) (sym &iso) (YF.x∈U ax ) )
--                     ; func-wld = λ {x} {y} ax ay x=y → trans ? (trans ? ? ) }

           YFunc-is-x : (F : Functor OX HODSets) → {z : Ordinal} → (yz : odef (YFHOD F) z) → Func.func (YFunc F) yz ≡ YF.x yz
           YFunc-is-x F {x₁} record { x = x ; s = s ; u = u ; ou = ou ; x∈U = x∈U ; s∈FU = s∈FU ; is-pair = is-pair } = refl

           LObj :  Obj (HOD-OSCA (topology X) ) → Obj (top / X)
           LObj F =   ⟦ hom ⟧ where
               F-functor : Functor OX HODSets
               F-functor = F
               hom : Hom top record { space = YFHOD F ; topology = YFTopology F  } X
               hom = record  { func = YFunc F
                 ; continuous = ? --  lem00
                } -- where
--                   lem00 :  {x : Ordinal } → odef (OS (topology X)) x → odef (YFOHOD F) (& (HODInverseImage (YFunc F) x ))
--                   lem00 {x} ox = record { u = ? ; s = ? ; ou = ? ; s∈FU = ? ; is-open = ==→o≡ ? }

           -- Slice top on X    Obj   record field { Obj a  ; obj-arrow : Hom top a X }
           --                   Hom   record field { arrow : Hom (obj a) (obj b) ; proof : obj-arrow  f ≈ obj-arrow g o arrow }
           --
           --                   arrow a b
           --                 a → b
           ---                f\ /g    proof : f ≈ g o arrow
           --                   X
           --
           -- YFwld : {F : Functor OX HODSets}
           --      → {A B : Obj (HOD-OSCA (topology X))} → Hom (HOD-OSCA (topology X)) A B → ?
           -- YFwld = ?

           LFMap : {A B : Obj (HOD-OSCA (topology X))} → Hom (HOD-OSCA (topology X)) A B → Hom (top / X) (LObj A) (LObj B)
           LFMap {a} {b} nat = record { arrow = record { func = lem01 ; continuous = ? }  ; proof = lem02 }  where
               af : Functor OX HODSets
               af = a
               bf : Functor OX HODSets
               bf = b
               lem00 :  NTrans OX HODSets a b
               lem00 = nat
    -- FEQ.HODSFUEQ b (os⊆L (topology X) (YF.ou ax) (YF.x∈U ax))
    --             (record
    --              { u = YF.u ax
    --              ; ou = YF.ou ax
    --              ; s∈FU =
    --                  ZProduct.Func.is-func
    --                  (TMap nat (record { s = * (YF.u ax) ; p = YF.ou ax })) (YF.s∈FU ax)
    --              }))
               lem01 : Func (YFHOD a) (YFHOD b)
               lem01 = ? -- record {
--                   func = λ {x} ax → & < * (YF.x ax) , _ >
--                 ; is-func = λ {x} ax → record { x = YF.x ax
--                      ; s = Func.func (TMap nat record { s = * (YF.u ax) ; p = YF.ou ax }) (YF.s∈FU ax)
--                      ; s∈FU = Func.is-func (TMap nat record { s = * (YF.u ax) ; p = YF.ou ax }) (YF.s∈FU ax)
--                      ; u = YF.u ax ; ou = YF.ou ax ; x∈U = YF.x∈U ax
--                     ; is-pair = refl }
--                 ; func-wld = ?
--                }
               lem03 : Func (YFHOD a) (space X)
               lem03 = FuncComp (ContFunc.func (SliceObj.arrow (LObj b))) lem01
               lem02 : ( x : Ordinal ) ( ax : odef (YFHOD a) x ) → FuncEQ (ContFunc.func (SliceObj.arrow (LObj a))) lem03  x ax
               lem02 x ax = begin
                  Func.func (ContFunc.func (SliceObj.arrow (LObj a))) ax ≡⟨ YFunc-is-x a ax ⟩
                  YF.x ax ≡⟨ sym ( YFunc-is-x a ax)  ⟩
                  Func.func lem03 ax  ∎ where open ≡-Reasoning

           L : Functor (HOD-OSCA (topology X) ) ( top / X )
           L = ? -- record { FObj = ? ; FMap = ?; isFunctor = ? }

           open import Category.Cat

           eta : NTrans (HOD-OSCA (topology X)) (HOD-OSCA (topology X)) identityFunctor (Γ ○ L)
           eta = ? -- record { TMap = λ a → eta00 a ; isNTrans = record { commute = ? } } where
--               eta01 : (a : Obj (HOD-OSCA (topology X))) (b : Obj OX) → Hom HODSets (FObj a b) (Γo (? a) b)
--               eta01 a b  = eta02 where
--                   eta02 : Func (FObj a b) (Γo (? a) b)
--                   eta02 = record {
--                       func = λ  {x} fab →  & < * x , ? a ? record { u = ? ; ou = ? ; s∈FU = ? }  >
--                     ; is-func = ?
--                     ; func-wld = ?
--                    }
--               eta00 : (a : Obj (HOD-OSCA (topology X))) → Hom (HOD-OSCA (topology X)) a (ΓObj (? a))
--               eta00 a = record { TMap = eta01 a ; isNTrans = record { commute = ? } }

           epsrion : NTrans (top / X) (top / X) (L ○ Γ) identityFunctor
           epsrion = ? -- record { TMap = λ a → ep00 a ; isNTrans = record { commute = ? } } where
--               ep00 : ( a : Obj (top / X)) → Hom (top / X) (? (ΓObj a)) a
--               ep00 a = record { arrow = ? ; proof = ? }


           sheafAdj : Adjunction (HOD-OSCA (topology X) ) ( top / X )
           sheafAdj = ? -- record {
--               U = Γ
--             ; F = L
--             ; η  = ?
--             ; ε  = ?
--             ; isAdjunction = record {
--                    adjoint1 = ?
--                  ; adjoint2 = ?
--                }
--            }

