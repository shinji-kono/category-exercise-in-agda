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

--
-- From Lambek , Scott, Introduction to Higher Order Categorical Logic
--    page 179  Sheaf categories and their semantics, Type theory and toposes
--

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
-- open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
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

--
-- Category of Toplogy space and ⊆ 
--

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

--
-- Category of Topology Space and Continuous Functions
--

record TopObj : Set (suc n) where
   field
     space : HOD
     topology : Topology space

open TopObj

FuncID : (a : HOD) → Func a a
FuncID a = record { func = λ {x} ax → x
          ; is-func = λ {x} ax → ax
          ; func-wld = λ _ _ eq → eq }

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

-- we cannot prove the rule of functor of Γo on ΓCont.cond
---   https://qiita.com/9_ties/items/30fe2f48f8727adf70c1

HODPresheaf : {P : HOD} (TP : Topology P) → Set (suc (suc (suc n)))
HODPresheaf {P} TP = Functor (Category.op  (OSC TP)) HODSets 

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
    Ui⊆UI : {x : Ordinal } → {a : I} → odef (SObj.s (Ui a)) x → odef (Union UI) x
    Ui⊆UI {x} {a} uix = record { owner = & (SObj.s (Ui a)) ; ao = record { i = a ; x=Ui = refl } ; ox = eq← *iso uix } 
    f1 : (a b : I) → Hom HODSets (FObj F (Ui a)) (FObj F (Uab a b))
    f1 a b = FMap F (λ q → proj1 q )
    f2 : (a b : I) → Hom HODSets (FObj F (Ui b)) (FObj F (Uab a b ))
    f2 a b = FMap F (λ q → proj2 q )
    f3 : (a b : I) → Hom HODSets (FObj F U) (FObj F (Ui a))
    f3 a b = FMap F Ui⊆UI  
    f4 : (a b : I) → Hom HODSets (FObj F U) (FObj F (Ui b))
    f4 a b = FMap F Ui⊆UI  

    HOD-is-sheaf : (a b : I) →  Set (suc n)
    HOD-is-sheaf a b = IsPullback HODSets {FObj F (Ui a)} {FObj F (Ui b)} {FObj F (Uab a b)} {FObj F U} (f1 a b ) (f2 a b ) (f3 a b ) (f4 a b )  
--
-- The adjoint functor Γ : top / X → OSCA (topology X) s
--
--
-- Γ(p)(U) ≡ {s : U → Y | ps = incl(U/X) }
--
-- record ΓCont {U Y X : HOD} (TU :  Topology U) (TY : Topology Y) (TX : Topology X) (p : ContFunc TY TX ) : Set n where
--    field
--      s : ContFunc TU TY
--      cond : {x : Ordinal } → (ux :  odef U x ) → ( Func.func (ContFunc.func p) (Func.is-func (ContFunc.func s) ux )) ≡ x 


record HODΓCont {U Y X : HOD} (TU :  Topology U) (TY : Topology Y) (TX : Topology X) (p : ContFunc TY TX ) (x : Ordinal) : Set n where
   field
     s : ContFunc TU TY
     x=func : & ( F→FuncHOD ( ContFunc.func s)) ≡ x
     cond : {x : Ordinal } → (ux :  odef U x ) → ( Func.func (ContFunc.func p) (Func.is-func (ContFunc.func s) ux )) ≡ x 

module HODShAdjoint (X : Obj top) where 

       Γo : (p : Obj (top / X)) → Obj (Category.op (OSC (topology X))) → Obj HODSets
       Γo p record { s = U ; p = oU } = record { od = record { def = λ x → 
           HODΓCont  (SubTopology (topology X) U ) (topology (SliceObj.X p)) (topology X) (SliceObj.arrow p) x } ; odmax = ? ; <odmax = ?  }
       Γm : (p : Obj (top / X)) → {A B : Obj (Category.op (OSC (topology X)))} → Hom (Category.op (OSC (topology X))) A B → Hom HODSets (Γo p A) (Γo p B) 
       Γm p {a} {b} b⊆a = record {
                 func = lem00 
               ; is-func = lem01
               ; func-wld = ? 
             } where
           lem : SObj.s b ⊆ SObj.s a
           lem = b⊆a
           gs : {x : Ordinal} → odef (Γo p a) x → ContFunc (SubTopology (topology X) (SObj.s a)) (topology (SliceObj.X p))
           gs {x} gpa = HODΓCont.s gpa
           dfunc : {y : Ordinal} → odef (Γo p a) y → Func (SObj.s b) (space (SliceObj.X p))
           dfunc gpa = record { func = λ {x} dx → Func.func (ContFunc.func (gs gpa ) ) (b⊆a dx)  
              ; is-func = λ {x} dx → Func.is-func (ContFunc.func (gs gpa )) (b⊆a dx) 
                  ; func-wld = λ {x} {y} dx dy → Func.func-wld (ContFunc.func (gs gpa )) (b⊆a dx) (b⊆a dy)  }
           dcontinuous : {y : Ordinal} → (gpa : odef (Γo p a) y ) → {x : Ordinal} → odef (OS (topology (SliceObj.X p))) x →
                        odef (OS (SubTopology (topology X) (SObj.s b))) (& (HODInverseImage (dfunc gpa) x))
           dcontinuous gpa {x} cx = record { R = SubElement.R scont ; OR = SubElement.OR scont ; x=R = ==→o≡ lem00 } where  
               scont : odef (OS (SubTopology (topology X) (SObj.s a))) (& (HODInverseImage (ContFunc.func (gs gpa )) x))
               scont = ContFunc.continuous (gs gpa) cx
               lem01 : HODInverseImage (ContFunc.func (gs gpa )) x =h= (* (SubElement.R scont) ∩ SObj.s a)
               lem01 = ord→== ( SubElement.x=R scont )
               lem00 : HODInverseImage (dfunc gpa) x =h= (* (SubElement.R scont) ∩ SObj.s b)
               lem00 = record {
                   eq→ = λ {y} lt → ⟪ proj1 ( eq→ lem01 record { y∈P = b⊆a (InverseImage.y∈P lt) ; is-inverse 
                      = InverseImage.is-inverse lt } )  , InverseImage.y∈P lt ⟫
                ;  eq← = λ {y} lt → record { y∈P = proj2 lt  ; is-inverse 
                    = subst (λ k → odef (* x) k) (Func.func-wld (ContFunc.func (gs gpa )) _ _ refl
                       ) (InverseImage.is-inverse (eq← lem01 ⟪ proj1 lt , b⊆a (proj2 lt) ⟫)) }
                }
           gd : {y : Ordinal} → odef (Γo p a) y → ContFunc (SubTopology (topology X) (SObj.s b)) (topology (SliceObj.X p))
           gd gpa = record { func = (dfunc gpa ) ; continuous = dcontinuous gpa }  
           incl :  {y : Ordinal } → (gpa : odef (Γo p a) y )
              → {x : Ordinal} (ux : odef (SObj.s b) x) → Func.func (ContFunc.func (SliceObj.arrow p)) (Func.is-func (ContFunc.func (gs gpa )) (b⊆a ux)) ≡ x
           incl gpa {x} ux = trans (Func.func-wld (ContFunc.func (SliceObj.arrow p)) _ _ refl) (HODΓCont.cond gpa (b⊆a ux)  )
           lem00 : {x : Ordinal} → odef (Γo p a) x → Ordinal
           lem00 {x} gpa = & (F→FuncHOD (dfunc gpa))
           lem01 :  {x : Ordinal} (gpa : odef (Γo p a) x) → odef (Γo p b) (lem00 gpa)
           lem01 {x} gpa = record { s = record { func = dfunc gpa ; continuous = dcontinuous gpa }  ; x=func = refl ; cond = incl gpa  }


       ΓObj : Obj ( top / X ) → Obj (HOD-OSCA (topology X) )
       ΓObj p = record { FObj = Γo p ; FMap = λ {a} {b} f → Γm p {a} {b} f ; isFunctor = record { 
             ≈-cong = λ {a} {b} {f} {g} f=g ga → ?    -- we cannot prove the equality of the ΓCont.cond
          ;  identity = λ {a} ga → ?
          ;  distr = ?
         } }
       ΓTMap : {a b : Obj (top / X)} → (f : Hom (top / X) a b) → (A : Obj (Category.op (OSC (topology X)))) → Hom HODSets (Γo a A) (Γo b A)
       ΓTMap {a} {b} f A = record {
                 func = ? 
               ; is-func = ?
               ; func-wld = ? 
             } where
           gs : {y : Ordinal} → (gpa : odef (Γo a A) y) → ContFunc (SubTopology (topology X) (SObj.s A)) (topology (SliceObj.X a ))
           gs = ?
           gd : {y : Ordinal } → (gpa : odef (Γo a A) y) → ContFunc (SubTopology (topology X) (SObj.s A)) (topology (SliceObj.X b ))
           gd gpa = top [ _⟶_.arrow f o gs gpa ]
           gs-cond : {y : Ordinal } → (gpa : odef (Γo a A) y ) → {x : Ordinal} (ux : odef (SObj.s A) x) → Func.func (ContFunc.func (SliceObj.arrow a)) 
              (Func.is-func (ContFunc.func (gs gpa)) ux ) ≡ x
           gs-cond = ? -- ΓCont.cond ?
           cond : {y : Ordinal} → (gpa : odef (Γo a A) y) → {x : Ordinal} (ux : odef (SObj.s A) x) → Func.func (ContFunc.func (SliceObj.arrow b))
                (Func.is-func (ContFunc.func (top [ _⟶_.arrow f o gs gpa  ])) ux) ≡ x
           cond = ?
           lem00 : {x : Ordinal} → odef (Γo a A) x → Ordinal
           lem00 = ?

       ΓMap : {A B : Obj (top / X)} → Hom (top / X) A B → Hom (HOD-OSCA (topology X) ) (ΓObj A) (ΓObj B)
       ΓMap {a} {b} f = record { TMap = ΓTMap f ; isNTrans = record { commute = ? } }

       Γ : Functor ( top / X ) (HOD-OSCA (topology X) )
       Γ = record { FObj = ΓObj ; FMap = ΓMap ; isFunctor = ? }

       Γp-is-sheaf : (I : Set n) → (io : I → Obj (OSC (topology X))) → (a b : I ) → (p : Obj ( top / X )) 
           → Is-sheaf.HOD-is-sheaf (topology X) I io (ΓObj p) a b
       Γp-is-sheaf I Ui a b p = record { 
               commute = lem00
            ;  pullback = ?
            ;  π1p=π1 = ?
            ;  π2p=π2 = ?
            ;  uniqueness = ?
             } where
                 open  Is-sheaf (topology X) I Ui (ΓObj p) 
                 p1 : SliceObj top X
                 p1 = p
                 dfunc : ContFunc (topology (SliceObj.X p)) (topology X)
                 dfunc = SliceObj.arrow p
                 F : Functor (Category.op (OSC (topology X))) HODSets -- Obj (HOD-OSCA (topology X)) 
                 F = ΓObj p
                 dfuc-restrict : {c d : Obj (Category.op (OSC (topology X)))} → (d⊆c : SObj.s d ⊆ SObj.s c) → Func (Γo p c) (Γo p d)
                 dfuc-restrict d⊆c = FMap (ΓObj p) d⊆c
                 sx : SObj ? ?
                 sx = record { s = space (SliceObj.X p) ; p = ? }
                 dfuc-restrict-is-x : {d : Obj (Category.op (OSC (topology X)))} → (d⊆c : SObj.s d ⊆ space (SliceObj.X p))
                    → {x : Ordinal } → (cx : odef (Γo p sx) x)  → Func.func (ContFunc.func dfunc) ? ≡ Func.func (dfuc-restrict d⊆c) cx 
                 dfuc-restrict-is-x = ?
                 f21 : {c : Ordinal} → (cx : odef (Γo p U) c) → odef (Γo p (Ui a)) (Func.func (FMap F (λ {x} → (Ui⊆UI {x} {a}))) cx )
                 f21 cx = Func.is-func (FMap F Ui⊆UI) cx
                 lem00 :  HODSets [ HODSets [ f1 a b o f3 a b  ] ≈ HODSets [ f2 a b o f4 a b ] ]  
                 lem00 c cx = begin
                     Func.func (f1 a b) (Func.is-func (f3 a b) cx)  ≡⟨⟩
                     Func.func (FMap F proj1) (Func.is-func (FMap F (λ {x} uix → record { owner = & (SObj.s (Ui a)) ; ao = record { i = a ; x=Ui = refl }  ; ox = eq← *iso uix } )) cx)  ≡⟨ ? ⟩
                     Func.func (FMap F proj2) (Func.is-func (FMap F (λ {x} uix → record { owner = & (SObj.s (Ui b)) ; ao = record { i = b ; x=Ui = refl }  ; ox = eq← *iso uix } )) cx)  ≡⟨⟩
                     Func.func (f2 a b) (Func.is-func (f4 a b) cx)   ∎ where open ≡-Reasoning 

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
       --
       restrict-func : {U V : Obj (Category.op (OSC (topology X)))}  
           → (F : Functor (Category.op (OSC (topology X))) HODSets)
           → (V⊆U : SObj.s V ⊆ SObj.s U)
           → Func (FObj F U) (FObj F V)
       restrict-func {U} {V}  F V⊆U = record {
              func = λ {x} (FUs : odef (FObj F U) x ) → Func.func (FMap F (λ q → V⊆U q)) FUs 
            ; is-func = λ {x} (FUs : odef (FObj F U) x ) → Func.is-func (FMap F (λ q → V⊆U q)) FUs 
            ; func-wld = λ {x y} (FUx : odef (FObj F U) x ) (FUy : odef (FObj F U) y) eq → 
                Func.func-wld (FMap F (λ q → V⊆U q)) FUx FUy eq
          }

       record Feq 
               (F : Functor (Category.op (OSC (topology X))) HODSets)
               {x s t : Ordinal} (X∋x : odef (space X) x) 
               (U V : Obj (Category.op (OSC (topology X))) ) 
               (fus : odef (FObj F U) s) (fvt : odef (FObj F V) t)  : Set n where
          field 
             w : Ordinal
             ow : OS (topology X) ∋ * w
             w⊆u∩v : (* w) ⊆ ((SObj.s U) ∩ (SObj.s V) )
             x∈w : odef (* w) x
          W : Obj  (Category.op (OSC (topology X)))
          W = record { s = * w ; p = ow } 
          W⊆U : SObj.s W ⊆ SObj.s U 
          W⊆U {y} lt = proj1 (w⊆u∩v lt)
          W⊆V : SObj.s W ⊆ SObj.s V 
          W⊆V {y} lt = proj2 (w⊆u∩v lt)
          vv : odef (FObj F W) (Func.func (restrict-func {U} {W} F W⊆U) fus) 
          vv =  Func.is-func (restrict-func {U} {W} F W⊆U) fus 
          field 
             feq : Func.func (restrict-func {U} {W} F W⊆U) fus ≡ Func.func (restrict-func {V} {W} F W⊆V) fvt


       module FEQ (F : Functor (Category.op (OSC (topology X))) HODSets) {x : Ordinal }  (X∋x : odef (space X) x) where
           record SFU (x : Ordinal) : Set n where
              field
                 u : Ordinal
                 ou : OS (topology X) ∋ * u
              U : Obj (Category.op (OSC (topology X)))
              U = record { s = * u ; p = ou }
              field
                 s∈FU : odef (FObj F U ) x
           HODSFU : HOD
           HODSFU = record { od = record { def = λ x → SFU x } ; odmax = ? ; <odmax = ? }

           _≐_ : Rel ( HODElement HODSFU ) n
           a ≐ b = Feq F X∋x (SFU.U (HODElement.A∋elt a)) (SFU.U (HODElement.A∋elt b))  (SFU.s∈FU (HODElement.A∋elt a)) (SFU.s∈FU (HODElement.A∋elt b))

           record SFUEQ {y : Ordinal} (sy : SFU y) (x : Ordinal) : Set n where
              field
                 sx : SFU x
                 sfu-eq : Feq F X∋x (SFU.U sx) (SFU.U sy)  (SFU.s∈FU sx) (SFU.s∈FU sy)

           HODSFUEQ : {y : Ordinal}  → SFU y → HOD
           HODSFUEQ {y} sy = record { od = record { def = λ x → SFUEQ sy x } ; odmax = ? ; <odmax = ? }


       record YF (F : Functor (Category.op (OSC (topology X))) HODSets) (y : Ordinal) : Set n where
          field 
             x s u : Ordinal 
             ou : OS (topology X) ∋ * u
          U : Obj (Category.op (OSC (topology X)))
          U = record { s = * u ; p = ou }
          field 
             x∈U : odef (SObj.s U) x
             s∈FU : odef (FObj F U ) s
             is-pair : y ≡ & < * x , FEQ.HODSFUEQ F (os⊆L (topology X) ou x∈U ) record { u = u ; ou = ou ; s∈FU = s∈FU }  >

       YFHOD :  (F : Functor (Category.op (OSC (topology X))) HODSets) → HOD
       YFHOD F = record { od = record { def = λ x → YF F x } ; odmax = ? ; <odmax = ? }

       record YFO (F : Functor (Category.op (OSC (topology X))) HODSets) {u s : Ordinal}
             (ou : OS (topology X) ∋ * u)
             (s∈FU : odef (FObj F (record { s = * u ; p = ou }) ) s) (y : Ordinal) : Set n where
          field 
             x : Ordinal 
             x∈U : odef (* u) x
             is-pair : y ≡ &  < * x , FEQ.HODSFUEQ F (os⊆L (topology X) ou x∈U ) record { u = u ; ou = ou ; s∈FU = s∈FU }  > 

       record YFOs (F : Functor (Category.op (OSC (topology X))) HODSets) (y : Ordinal) : Set n where
          field 
             u s : Ordinal
             ou : OS (topology X) ∋ * u
             s∈FU : odef (FObj F (record { s = * u ; p = ou }) ) s
             is-open : y ≡ & record { od = record { def = λ x → YFO F ou s∈FU x } ; odmax = ? ; <odmax = ? }

       YFOHOD : (F : Functor (Category.op (OSC (topology X))) HODSets) → HOD
       YFOHOD F = record { od = record { def = λ x → YFOs F x } ; odmax = ? ; <odmax = ? }

       YFTopology : (F : Functor (Category.op (OSC (topology X))) HODSets) → Topology (YFHOD F)
       YFTopology F = record { 
             OS = YFOHOD F 
           ; OS⊆PL = lem00 
           ; o∩ = lem02 
           ; o∪ = ? 
           ; OS∋od∅  = ? 
         } where
            lem00 : YFOHOD F ⊆ Power (YFHOD F)
            lem00 {x} record { u = u ; s = s ; ou = ou ; s∈FU = s∈FU ; is-open = is-open } y xy 
               = record  { x = YFO.x lem01 ; s = s ; u = u ; x∈U = YFO.x∈U lem01 ; s∈FU  = s∈FU ; is-pair = YFO.is-pair lem01 } where
                  lem01 : YFO F {u} {s} ou s∈FU y
                  lem01 = eq→ *iso {y} (subst (λ k → odef (* k) y ) is-open  xy ) 
            lem02 : {p q : HOD} → YFOHOD F ∋ p → YFOHOD F ∋ q → YFOHOD F ∋ (p ∩ q)
            lem02 {p} {q} op oq  = record {  u = & ( * (YFOs.u op) ∩ * (YFOs.u oq))  ; s = & ( * (YFOs.s op) ∩ * (YFOs.s oq))
                       ; ou = ? ; s∈FU = ? ; is-open = ==→o≡ lem04 }  where
                  lem03 : (y : Ordinal) → YFO F ? ? y
                  lem03 = ?
                  lem04 : ( p ∩ q ) =h= record { od = record { def = λ x →  YFO F ? ? x  } ; odmax = ? ; <odmax = ? } 
                  lem04 = ?
            lem05 : {P : HOD} → P ⊆ YFOHOD F → YFOHOD F ∋ Union P
            lem05 = ?

       --     [s]x modulo s|w = t|w
       --  |Yf| ≡ {(x,[s]x)|∃ U∈O(X) (x∈ U ∧ s∈ F(U)) } = ∪ (F x) x∈ X, where F x = lim F(U) = ∪ F(U)/~x   
       --                                                                          x ∈ U
       --  OS |Yf|  ≡ {(x,[s]x)|x∈ U ∧ s ∈ F(U) }

       YFunc : (F : Functor (Category.op (OSC (topology X))) HODSets) → Func (YFHOD F) (space X)
       YFunc F = record {
                    func = λ {x} lt → YF.x lt
                  ; is-func = λ {x} ax → OS⊆PL (topology X) (YF.ou ax ) _ (subst (λ k → odef _ k) (sym &iso) (YF.x∈U ax ) )
                  ; func-wld = λ {x} {y} ax ay x=y → trans ? (trans ? ? ) }

       YFunc-is-x : (F : Functor (Category.op (OSC (topology X))) HODSets) → {z : Ordinal} → (yz : odef (YFHOD F) z) → Func.func (YFunc F) yz ≡ YF.x yz
       YFunc-is-x F {x₁} record { x = x ; s = s ; u = u ; ou = ou ; x∈U = x∈U ; s∈FU = s∈FU ; is-pair = is-pair } = refl

       LObj :  Obj (HOD-OSCA (topology X) ) → Obj (top / X)
       LObj F =   ⟦ hom ⟧ where
           F-functor : Functor (Category.op (OSC (topology X))) HODSets
           F-functor = F
           hom : Hom top record { space = YFHOD F ; topology = YFTopology F  } X
           hom = record  { func = YFunc F
             ; continuous =  lem00
            } where
                lem00 :  {x : Ordinal } → odef (OS (topology X)) x → odef (YFOHOD F) (& (HODInverseImage (YFunc F) x ))
                lem00 {x} ox = record { u = ? ; s = ? ; ou = ? ; s∈FU = ? ; is-open = ==→o≡ ? } 

       -- Slice top on X    Obj   record field { Obj a  ; obj-arrow : Hom top a X }
       --                   Hom   record field { arrow : Hom (obj a) (obj b) ; proof : obj-arrow  f ≈ obj-arrow g o arrow }
       --
       --                   arrow a b
       --                 a → b
       ---                f\ /g    proof : f ≈ g o arrow
       --                   X
       --
       -- YFwld : {F : Functor (Category.op (OSC (topology X))) HODSets} 
       --      → {A B : Obj (HOD-OSCA (topology X))} → Hom (HOD-OSCA (topology X)) A B → ?
       -- YFwld = ?

       LFMap : {A B : Obj (HOD-OSCA (topology X))} → Hom (HOD-OSCA (topology X)) A B → Hom (top / X) (LObj A) (LObj B)
       LFMap {a} {b} nat = record { arrow = record { func = lem01 ; continuous = ? }  ; proof = lem02 }  where
           af : Functor (Category.op (OSC (topology X))) HODSets
           af = a
           bf : Functor (Category.op (OSC (topology X))) HODSets
           bf = b
           lem00 :  NTrans (Category.op (OSC (topology X))) HODSets a b
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
           lem01 = record {
                func = λ {x} ax → & < * (YF.x ax) , _ >
              ; is-func = λ {x} ax → record { x = YF.x ax 
                   ; s = Func.func (TMap nat record { s = * (YF.u ax) ; p = YF.ou ax }) (YF.s∈FU ax)  
                   ; s∈FU = Func.is-func (TMap nat record { s = * (YF.u ax) ; p = YF.ou ax }) (YF.s∈FU ax)
                   ; u = YF.u ax ; ou = YF.ou ax ; x∈U = YF.x∈U ax 
                  ; is-pair = refl }
              ; func-wld = ? 
             } 
           lem03 : Func (YFHOD a) (space X)
           lem03 = FuncComp (ContFunc.func (SliceObj.arrow (LObj b))) lem01
           lem02 : ( x : Ordinal ) ( ax : odef (YFHOD a) x ) → FuncEQ (ContFunc.func (SliceObj.arrow (LObj a))) lem03  x ax
           lem02 x ax = begin
              Func.func (ContFunc.func (SliceObj.arrow (LObj a))) ax ≡⟨ YFunc-is-x a ax ⟩
              YF.x ax ≡⟨ sym ( YFunc-is-x a ax)  ⟩
              Func.func lem03 ax  ∎ where open ≡-Reasoning

       L : Functor (HOD-OSCA (topology X) ) ( top / X ) 
       L = record { FObj = LObj ; FMap = LFMap; isFunctor = ? }

       open import Category.Cat

       eta : NTrans (HOD-OSCA (topology X)) (HOD-OSCA (topology X)) identityFunctor (Γ ○ L)
       eta = record { TMap = λ a → eta00 a ; isNTrans = record { commute = ? } } where
            eta01 : (a : Obj (HOD-OSCA (topology X))) (b : Obj (Category.op (OSC (topology X)))) → Hom HODSets (FObj a b) (Γo (LObj a) b)
            eta01 a b  = eta02 where
                eta02 : Func (FObj a b) (Γo (LObj a) b)
                eta02 = record { 
                    func = λ  {x} fab →  & < * x , FEQ.HODSFUEQ a ? record { u = ? ; ou = ? ; s∈FU = ? }  >
                  ; is-func = ? 
                  ; func-wld = ? 
                 }
            eta00 : (a : Obj (HOD-OSCA (topology X))) → Hom (HOD-OSCA (topology X)) a (ΓObj (LObj a))
            eta00 a = record { TMap = eta01 a ; isNTrans = record { commute = ? } }

       epsrion : NTrans (top / X) (top / X) (L ○ Γ) identityFunctor
       epsrion = record { TMap = λ a → ep00 a ; isNTrans = record { commute = ? } } where
            ep00 : ( a : Obj (top / X)) → Hom (top / X) (LObj (ΓObj a)) a
            ep00 a = record { arrow = ? ; proof = ? }


       sheafAdj : Adjunction (HOD-OSCA (topology X) ) ( top / X )
       sheafAdj = record { 
            U = Γ
          ; F = L
          ; η  = ?
          ; ε  = ?
          ; isAdjunction = record {
                 adjoint1 = ?
               ; adjoint2 = ?
             }
         }

