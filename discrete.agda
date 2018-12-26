open import Category -- https://github.com/konn/category-agda
open import Level

module discrete where

open import Relation.Binary.Core

data  TwoObject {c₁ : Level}  : Set c₁ where
   t0 : TwoObject
   t1 : TwoObject

---
---  two objects category  ( for limit to equalizer proof )
---
---          f
---       -----→
---     0         1
---       -----→
---          g
--
--     missing arrows are constrainted by TwoHom data

data TwoHom {c₁ c₂ : Level } : TwoObject {c₁}  → TwoObject {c₁} → Set c₂ where
   id-t0 :    TwoHom t0 t0
   id-t1 :    TwoHom t1 t1
   arrow-f :  TwoHom t0 t1
   arrow-g :  TwoHom t0 t1


_×_ :  ∀ {c₁  c₂}  → {a b c : TwoObject {c₁}} →  TwoHom {c₁} {c₂} b c  →  TwoHom {c₁} {c₂} a b   →  TwoHom {c₁} {c₂} a c 
_×_ {_}  {_}  {t0} {t1} {t1}  id-t1   arrow-f  = arrow-f 
_×_ {_}  {_}  {t0} {t1} {t1}  id-t1   arrow-g  = arrow-g 
_×_ {_}  {_}  {t1} {t1} {t1}  id-t1   id-t1    = id-t1 
_×_ {_}  {_}  {t0} {t0} {t1}  arrow-f id-t0    = arrow-f 
_×_ {_}  {_}  {t0} {t0} {t1}  arrow-g id-t0    = arrow-g 
_×_ {_}  {_}  {t0} {t0} {t0}  id-t0   id-t0    = id-t0 

open TwoHom

--          f    g    h
--       d <- c <- b <- a
--
--   It can be proved without TwoHom constraints

assoc-× :   {c₁  c₂ : Level } {a b c d : TwoObject  {c₁} }
       {f : (TwoHom {c₁}  {c₂ } c d )} → {g : (TwoHom b c )} → {h : (TwoHom a b )} →
       ( f × (g × h)) ≡ ((f × g) × h )
assoc-× {c₁} {c₂} {t0} {t0} {t0} {t0} { id-t0   }{ id-t0   }{ id-t0   } = refl
assoc-× {c₁} {c₂} {t0} {t0} {t0} {t1} { arrow-f }{ id-t0   }{ id-t0   } = refl
assoc-× {c₁} {c₂} {t0} {t0} {t0} {t1} { arrow-g }{ id-t0   }{ id-t0   } = refl
assoc-× {c₁} {c₂} {t0} {t0} {t1} {t1} { id-t1   }{ arrow-f }{ id-t0   } = refl
assoc-× {c₁} {c₂} {t0} {t0} {t1} {t1} { id-t1   }{ arrow-g }{ id-t0   } = refl
assoc-× {c₁} {c₂} {t0} {t1} {t1} {t1} { id-t1   }{ id-t1   }{ arrow-f } = refl
assoc-× {c₁} {c₂} {t0} {t1} {t1} {t1} { id-t1   }{ id-t1   }{ arrow-g } = refl
assoc-× {c₁} {c₂} {t1} {t1} {t1} {t1} { id-t1   }{ id-t1   }{ id-t1   } = refl

TwoId :  {c₁  c₂ : Level } (a : TwoObject  {c₁} ) →  (TwoHom {c₁}  {c₂ } a a )
TwoId {_} {_} t0 = id-t0 
TwoId {_} {_} t1 = id-t1 

open import Relation.Binary.PropositionalEquality renaming ( cong to ≡-cong )

TwoCat : {c₁ c₂ : Level  } →  Category   c₁  c₂  c₂
TwoCat   {c₁}  {c₂} = record {
    Obj  = TwoObject ;
    Hom = λ a b →   TwoHom a b  ;
    _o_ =  λ{a} {b} {c} x y → _×_ {c₁ } { c₂} {a} {b} {c} x y ;
    _≈_ =  λ x y → x  ≡ y ;
    Id  =  λ{a} → TwoId a ;
    isCategory  = record {
            isEquivalence =  record {refl = refl ; trans = trans ; sym = sym } ;
            identityL  = λ{a b f} → identityL {c₁}  {c₂ } {a} {b} {f} ;
            identityR  = λ{a b f} → identityR {c₁}  {c₂ } {a} {b} {f} ;
            o-resp-≈  = λ{a b c f g h i} →  o-resp-≈  {c₁}  {c₂ } {a} {b} {c} {f} {g} {h} {i} ;
            associative  = λ{a b c d f g h } → assoc-×   {c₁}  {c₂} {a} {b} {c} {d} {f} {g} {h}
       }
   }  where
        identityL :  {c₁  c₂ : Level } {A B : TwoObject {c₁}} {f : ( TwoHom {c₁}  {c₂ } A B) } →  ((TwoId B)  × f)  ≡ f
        identityL  {c₁}  {c₂}  {t1} {t1} { id-t1 } = refl
        identityL  {c₁}  {c₂}  {t0} {t0} { id-t0 } = refl
        identityL  {c₁}  {c₂}  {t0} {t1} { arrow-f } = refl
        identityL  {c₁}  {c₂}  {t0} {t1} { arrow-g } = refl
        identityR :  {c₁  c₂ : Level } {A B : TwoObject {c₁}} {f : ( TwoHom {c₁}  {c₂ } A B) } →   ( f × TwoId A )  ≡ f
        identityR  {c₁}  {c₂}  {t1} {t1} { id-t1  } = refl
        identityR  {c₁}  {c₂}  {t0} {t0} { id-t0 } = refl
        identityR  {c₁}  {c₂}  {t0} {t1} { arrow-f } = refl
        identityR  {c₁}  {c₂}  {t0} {t1} { arrow-g } = refl
        o-resp-≈ :  {c₁  c₂ : Level } {A B C : TwoObject  {c₁} } {f g :  ( TwoHom {c₁}  {c₂ } A B)} {h i : ( TwoHom B C)} →
            f  ≡ g → h  ≡ i → ( h × f )  ≡ ( i × g )
        o-resp-≈  {c₁}  {c₂} {a} {b} {c} {f} {.f} {h} {.h}  refl refl = refl


-- Category with no arrow but identity

record DiscreteHom { c₁ : Level} { S : Set c₁} (a : S) (b : S) 
      : Set c₁ where
   field
      discrete : a ≡ b     -- if f : a → b then a ≡ b
   dom : S
   dom = a

open DiscreteHom

_*_ :  ∀ {c₁}  →  {S : Set c₁} {a b c : S} →  DiscreteHom {c₁}  b c  →  DiscreteHom {c₁}  a b   →  DiscreteHom {c₁}  a c 
_*_ {_}  {a} {b} {c}  x y = record {discrete = trans ( discrete y) (discrete x) }

DiscreteId : { c₁ : Level} { S : Set c₁} ( a : S ) →  DiscreteHom {c₁}  a a
DiscreteId a = record { discrete = refl }

open  import  Relation.Binary.PropositionalEquality

assoc-* :   {c₁  : Level } { S : Set c₁} {a b c d : S}
       {f : (DiscreteHom  c d )} → {g : (DiscreteHom b c )} → {h : (DiscreteHom a b )} →
       dom ( f * (g * h)) ≡ dom ((f * g) * h )
assoc-* {c₁} {S} {a} {b} {c} {d} {f} {g} {h } = refl

DiscreteCat : {c₁ : Level  } →  (S : Set c₁) → Category   c₁   c₁   c₁  
DiscreteCat   {c₁}  S = record {
    Obj  = S ;
    Hom = λ a b →   DiscreteHom  {c₁} {S} a b  ;
    _o_ =  λ{a} {b} {c} x y → _*_ {c₁ } {S} {a} {b} {c} x y ;
    _≈_ =  λ x y → dom x  ≡ dom y ;   -- x ≡ y does not work because refl ≡ discrete f is failed as it should be
    Id  =  λ{a} → DiscreteId a ;
    isCategory  = record {
            isEquivalence =  record {refl = refl ; trans = trans ; sym = sym } ;
            identityL  = λ{a b f} → identityL  {a} {b} {f} ;
            identityR  = λ{a b f} → identityR  {a} {b} {f} ;
            o-resp-≈  = λ{a b c f g h i} →  o-resp-≈     {a} {b} {c} {f} {g} {h} {i} ;
            associative  = λ{a b c d f g h } → assoc-*  { c₁} {S}  {a} {b} {c} {d} {f} {g} {h}
       }
   }  where
        identityL :   {a b : S} {f : ( DiscreteHom {c₁}  a b) } →  dom ((DiscreteId b)  * f)  ≡ dom f
        identityL   {a} {b} {f} = refl
        identityR :   {A B : S} {f : ( DiscreteHom {c₁}   A B) } →  dom ( f * DiscreteId A )  ≡ dom f
        identityR   {a} {b} {f} = refl
        o-resp-≈ :   {A B C : S } {f g :  ( DiscreteHom {c₁}   A B)} {h i : ( DiscreteHom B C)} →
            dom f  ≡ dom g → dom h  ≡ dom i → dom ( h * f )  ≡ dom ( i * g )
        o-resp-≈  {a} {b} {c} {f} {g} {h} {i}  refl refl = refl






