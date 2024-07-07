{-# OPTIONS --cubical-compatible --safe #-}

open import Category -- https://github.com/konn/category-agda
open import Level

module graph where

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym )

record Graph  { v v' : Level } : Set (suc v ⊔ suc v' ) where
  field
    vertex : Set v
    edge : vertex  → vertex → Set v'

module graphtocat where

  open import Relation.Binary.PropositionalEquality 

  data Chain { v v' : Level } ( g : Graph {v} {v'} ) : ( a b : Graph.vertex g ) → Set (v ⊔ v' ) where
       id : ( a : Graph.vertex g ) → Chain g a a
       next : { a b c : Graph.vertex g } → (Graph.edge g b c ) → Chain g a b → Chain g a c

  _・_ :  {v v' : Level} { G : Graph {v} {v'} } {a b c : Graph.vertex G } (f : Chain G b c ) → (g : Chain G a b) → Chain G a c
  id _ ・ f = f
  (next x f) ・ g = next x ( f ・ g )

  GraphtoCat : {v v' : Level} (G : Graph {v} {v'} )  →  Category  v (v ⊔ v') (v ⊔ v')
  GraphtoCat G = record {
            Obj  = Graph.vertex G ;
            Hom = λ a b →  Chain G a b ;
            _o_ =  λ{a} {b} {c} x y → x ・ y ;
            _≈_ =  λ x y → x  ≡ y ;
            Id  =  λ{a} → id a ;
            isCategory  = record {
                    isEquivalence =  record {refl = refl ; trans = trans ; sym = sym } ;
                    identityL  = identityL; 
                    identityR  = identityR ; 
                    o-resp-≈  = o-resp-≈  ; 
                    associative  = λ{a b c d f g h } → associative  f g h
               }
           }  where
               open Chain
               obj = Graph.vertex G
               hom = Graph.edge G

               identityL : {A B : Graph.vertex G} {f : Chain G A B} → (id B ・ f) ≡ f
               identityL = refl
               identityR : {A B : Graph.vertex G} {f : Chain G A B} → (f ・ id A) ≡ f
               identityR {a} {_} {id a} = refl
               identityR {a} {b} {next x f} = cong ( λ k → next x k ) ( identityR {_} {_} {f} )
               o-resp-≈  : {A B C : Graph.vertex G} {f g : Chain G A B} {h i : Chain G B C} →
                            f ≡ g → h ≡ i → (h ・ f) ≡ (i ・ g)
               o-resp-≈  refl refl = refl
               associative : {a b c d : Graph.vertex G} (f : Chain G c d) (g : Chain G b c) (h : Chain G a b) →
                            (f ・ (g ・ h)) ≡ ((f ・ g) ・ h)
               associative (id a) g h = refl
               associative (next x f) g h = cong ( λ k → next x k ) ( associative f g h )



data  TwoObject   : Set  where
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

data TwoHom  : TwoObject   → TwoObject  → Set  where
   id-t0 :    TwoHom t0 t0
   id-t1 :    TwoHom t1 t1
   arrow-f :  TwoHom t0 t1
   arrow-g :  TwoHom t0 t1

TwoCat' : Category  Level.zero Level.zero Level.zero
TwoCat'  = GraphtoCat ( record { vertex = TwoObject ; edge = TwoHom } )
   where open graphtocat

_×_ :  {a b c : TwoObject } →  TwoHom   b c  →  TwoHom   a b   →  TwoHom   a c 
_×_ {t0} {t1} {t1}  id-t1   arrow-f  = arrow-f 
_×_ {t0} {t1} {t1}  id-t1   arrow-g  = arrow-g 
_×_ {t1} {t1} {t1}  id-t1   id-t1    = id-t1 
_×_ {t0} {t0} {t1}  arrow-f id-t0    = arrow-f 
_×_ {t0} {t0} {t1}  arrow-g id-t0    = arrow-g 
_×_ {t0} {t0} {t0}  id-t0   id-t0    = id-t0 


open TwoHom

--          f    g    h
--       d <- c <- b <- a
--
--   It can be proved without TwoHom constraints

assoc-× :    {a b c d : TwoObject   }
       {f : (TwoHom    c d )} → {g : (TwoHom b c )} → {h : (TwoHom a b )} →
       ( f × (g × h)) ≡ ((f × g) × h )
assoc-×   {t0} {t0} {t0} {t0} { id-t0   }{ id-t0   }{ id-t0   } = refl
assoc-×   {t0} {t0} {t0} {t1} { arrow-f }{ id-t0   }{ id-t0   } = refl
assoc-×   {t0} {t0} {t0} {t1} { arrow-g }{ id-t0   }{ id-t0   } = refl
assoc-×   {t0} {t0} {t1} {t1} { id-t1   }{ arrow-f }{ id-t0   } = refl
assoc-×   {t0} {t0} {t1} {t1} { id-t1   }{ arrow-g }{ id-t0   } = refl
assoc-×   {t0} {t1} {t1} {t1} { id-t1   }{ id-t1   }{ arrow-f } = refl
assoc-×   {t0} {t1} {t1} {t1} { id-t1   }{ id-t1   }{ arrow-g } = refl
assoc-×   {t1} {t1} {t1} {t1} { id-t1   }{ id-t1   }{ id-t1   } = refl

TwoId :   (a : TwoObject   ) →  (TwoHom    a a )
TwoId  t0 = id-t0 
TwoId   t1 = id-t1 

open import Relation.Binary.PropositionalEquality renaming ( cong to ≡-cong )

TwoCat :  Category  Level.zero Level.zero Level.zero   
TwoCat      = record {
    Obj  = TwoObject ;
    Hom = λ a b →   TwoHom a b  ;
    _≈_ =  λ x y → x  ≡ y ;
    Id  =  λ{a} → TwoId a ;
    isCategory  = record {
            isEquivalence =  record {refl = refl ; trans = trans ; sym = sym } ;
            identityL  = λ{a b f} → identityL    {a} {b} {f} ;
            identityR  = λ{a b f} → identityR    {a} {b} {f} ;
            o-resp-≈  = λ{a b c f g h i} →  o-resp-≈     {a} {b} {c} {f} {g} {h} {i} ;
            associative  = λ{a b c d f g h } → assoc-×      {a} {b} {c} {d} {f} {g} {h}
       }
   }  where
        identityL :   {A B : TwoObject } {f : ( TwoHom    A B) } →  ((TwoId B)  × f)  ≡ f
        identityL      {t1} {t1} { id-t1 } = refl
        identityL      {t0} {t0} { id-t0 } = refl
        identityL      {t0} {t1} { arrow-f } = refl
        identityL      {t0} {t1} { arrow-g } = refl
        identityR :   {A B : TwoObject } {f : ( TwoHom    A B) } →   ( f × TwoId A )  ≡ f
        identityR      {t1} {t1} { id-t1  } = refl
        identityR      {t0} {t0} { id-t0 } = refl
        identityR      {t0} {t1} { arrow-f } = refl
        identityR      {t0} {t1} { arrow-g } = refl
        o-resp-≈ :   {A B C : TwoObject   } {f g :  ( TwoHom    A B)} {h i : ( TwoHom B C)} →
            f  ≡ g → h  ≡ i → ( h × f )  ≡ ( i × g )
        o-resp-≈     {a} {b} {c} {f} {.f} {h} {.h}  refl refl = refl


-- Category with no arrow but identity


open import Data.Empty

DiscreteCat' : (S : Set) → Category  Level.zero Level.zero Level.zero
DiscreteCat'  S = GraphtoCat ( record { vertex = S ; edge = ( λ _ _ →  ⊥  ) } )
   where open graphtocat 

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
        o-resp-≈  {a} {b} {c} {f} {g} {h} {i}  eq _  = refl






