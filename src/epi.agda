{-# OPTIONS --cubical-compatible --safe #-}
open import Category -- https://github.com/konn/category-agda
open import Level

module epi where

open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym )

open import Relation.Binary.Core

data  FourObject   : Set where
   ta : FourObject
   tb : FourObject
   tc : FourObject
   td : FourObject

data FourHom  : FourObject → FourObject → Set  where
   id-ta :    FourHom ta ta
   id-tb :    FourHom tb tb
   id-tc :    FourHom tc tc
   id-td :    FourHom td td
   arrow-ca :  FourHom tc ta
   arrow-ab :  FourHom ta tb
   arrow-bd :  FourHom tb td
   arrow-cb :  FourHom tc tb
   arrow-ad :  FourHom ta td
   arrow-cd :  FourHom tc td

--
--       epi and monic but does not have inverted arrow
--
--       +--------------------------+
--       |                          |
--       c-----------------+        |
--       |                 ↓        ↓
--       + ----→  a ----→  b ----→  d 
--                |                 ↑
--                +-----------------+
--


_・_ :  {a b c : FourObject } →  FourHom b c  →  FourHom a b   →  FourHom a c 
_・_ {x} {ta} {ta}  id-ta   y  = y
_・_ {x} {tb} {tb}  id-tb   y  = y
_・_ {x} {tc} {tc}  id-tc   y  = y
_・_ {x} {td} {td}  id-td   y  = y
_・_ {ta} {ta} {x}  y id-ta = y
_・_ {tb} {tb} {x}  y id-tb = y
_・_ {tc} {tc} {x}  y id-tc = y
_・_ {td} {td} {x}  y id-td = y
_・_ {tc} {ta} {tb} arrow-ab arrow-ca = arrow-cb
_・_ {ta} {tb} {td} arrow-bd arrow-ab = arrow-ad
_・_ {tc} {tb} {td} arrow-bd arrow-cb = arrow-cd
_・_ {tc} {ta} {td} arrow-ad arrow-ca = arrow-cd
_・_ {tc} {ta} {tc} () arrow-ca
_・_ {ta} {tb} {ta} () arrow-ab
_・_ {tc} {tb} {ta} () arrow-cb
_・_ {ta} {tb} {tc} () arrow-ab
_・_ {tc} {tb} {tc} () arrow-cb
_・_ {tb} {td} {ta} () arrow-bd
_・_ {ta} {td} {ta} () arrow-ad
_・_ {tc} {td} {ta} () arrow-cd
_・_ {tb} {td} {tb} () arrow-bd
_・_ {ta} {td} {tb} () arrow-ad
_・_ {tc} {td} {tb} () arrow-cd
_・_ {tb} {td} {tc} () arrow-bd
_・_ {ta} {td} {tc} () arrow-ad
_・_ {tc} {td} {tc} () arrow-cd

open FourHom


assoc-・ :    {a b c d : FourObject   }
       (f : FourHom c d ) → (g : FourHom b c ) → (h : FourHom a b ) →
       ( f ・ (g ・ h)) ≡ ((f ・ g) ・ h )
assoc-・  id-ta y z = refl
assoc-・  id-tb y z = refl
assoc-・  id-tc y z = refl
assoc-・  id-td y z = refl
assoc-・  arrow-ca id-tc z = refl
assoc-・  arrow-ab id-ta z = refl
assoc-・  arrow-ab arrow-ca id-tc = refl
assoc-・  arrow-bd id-tb z = refl
assoc-・  arrow-bd arrow-ab id-ta = refl
assoc-・  arrow-bd arrow-ab arrow-ca = refl
assoc-・  arrow-bd arrow-cb id-tc = refl
assoc-・  arrow-cb id-tc z = refl
assoc-・  arrow-ad id-ta z = refl
assoc-・  arrow-ad arrow-ca id-tc = refl
assoc-・  arrow-cd id-tc id-tc = refl

FourId :   (a : FourObject  ) →  (FourHom  a a )
FourId ta = id-ta 
FourId tb = id-tb 
FourId tc = id-tc 
FourId td = id-td 

open import Relation.Binary.PropositionalEquality 

FourCat :  Category   zero zero zero
FourCat    = record {
    Obj  = FourObject ;
    Hom = λ a b →   FourHom a b  ;
    _o_ =  λ{a} {b} {c} x y → _・_ x y ;
    _≈_ =  λ x y → x  ≡ y ;
    Id  =  λ{a} → FourId a ;
    isCategory  = record {
            isEquivalence =  record {refl = refl ; trans = trans ; sym = sym } ; identityL  = λ{a b f} → identityL {a} {b} {f} ;
            identityR  = λ{a b f} → identityR  {a} {b} {f} ;
            o-resp-≈  = λ{a b c f g h i} →  o-resp-≈   {a} {b} {c} {f} {g} {h} {i} ;
            associative  = λ{a b c d f g h } → assoc-・    f g h
       }
   }  where
        identityL :   {A B : FourObject } {f : ( FourHom A B) } →  ((FourId B)  ・ f)  ≡ f
        identityL  {ta} {ta} {id-ta} = refl
        identityL  {tb} {tb} {id-tb} = refl
        identityL  {tc} {tc} {id-tc} = refl
        identityL  {td} {td} {id-td} = refl
        identityL  {tc} {ta} {arrow-ca} = refl
        identityL  {ta} {tb} {arrow-ab} = refl
        identityL  {tb} {td} {arrow-bd} = refl
        identityL  {tc} {tb} {arrow-cb} = refl
        identityL  {ta} {td} {arrow-ad} = refl
        identityL  {tc} {td} {arrow-cd} = refl
        identityR :   {A B : FourObject } {f : ( FourHom A B) } →   ( f ・ FourId A )  ≡ f
        identityR  {ta} {ta} {id-ta} = refl
        identityR  {tb} {tb} {id-tb} = refl
        identityR  {tc} {tc} {id-tc} = refl
        identityR  {td} {td} {id-td} = refl
        identityR  {tc} {ta} {arrow-ca} = refl
        identityR  {ta} {tb} {arrow-ab} = refl
        identityR  {tb} {td} {arrow-bd} = refl
        identityR  {tc} {tb} {arrow-cb} = refl
        identityR  {ta} {td} {arrow-ad} = refl
        identityR  {tc} {td} {arrow-cd} = refl
        o-resp-≈ :   {A B C : FourObject   } {f g :  ( FourHom A B)} {h i : ( FourHom B C)} →
            f  ≡ g → h  ≡ i → ( h ・ f )  ≡ ( i ・ g )
        o-resp-≈  {a} {b} {c} {f} {x} {h} {y} refl refl = refl

epi :  {a b c : FourObject } (f₁ f₂ : Hom FourCat  a b ) ( h : Hom FourCat b c )
   →    h ・ f₁   ≡ h ・  f₂   → f₁  ≡  f₂
epi id-ta id-ta _ eq = refl
epi id-tb id-tb _ eq = refl
epi id-tc id-tc _ eq = refl
epi id-td id-td _ eq = refl
epi arrow-ca arrow-ca _ eq = refl
epi arrow-ab arrow-ab _ eq = refl
epi arrow-bd arrow-bd _ eq = refl
epi arrow-cb arrow-cb _ eq = refl
epi arrow-ad arrow-ad _ eq = refl
epi arrow-cd arrow-cd _ eq = refl

monic :  {a b c : FourObject } (g₁ g₂ : Hom FourCat  b c ) ( h : Hom FourCat  a b )
   →   g₁ ・ h  ≡ g₂ ・ h   → g₁  ≡  g₂
monic id-ta id-ta _ eq = refl
monic id-tb id-tb _ eq = refl
monic id-tc id-tc _ eq = refl
monic id-td id-td _ eq = refl
monic arrow-ca arrow-ca _ eq = refl
monic arrow-ab arrow-ab _ eq = refl
monic arrow-bd arrow-bd _ eq = refl
monic arrow-cb arrow-cb _ eq = refl
monic arrow-ad arrow-ad _ eq = refl
monic arrow-cd arrow-cd _ eq = refl

open import Definitions
open import Relation.Nullary
open import Data.Empty

record Rev  {a b : FourObject } (f : Hom FourCat a b ) : Set where
  field
     rev :   Hom FourCat b a
     eq  :   f ・ rev  ≡ id1 FourCat b

not-rev : ¬ ( {a b : FourObject } →  (f : Hom FourCat a b ) →  Rev f )
not-rev r =  lemma1 arrow-ab (Rev.rev (r  arrow-ab)) (Rev.eq (r  arrow-ab))  
  where
     lemma1 :  (f : Hom FourCat ta tb )  →  (e₁ : Hom FourCat tb ta )
          → ( f ・ e₁  ≡ id1 FourCat tb )  →  ⊥
     lemma1 _ () eq
