open import Level
open import Category 
module CCC where

open import HomReasoning
open import cat-utility
open import Data.Product renaming (_×_ to _∧_)
open import Category.Constructions.Product
open  import  Relation.Binary.PropositionalEquality

open Functor

--   ccc-1 : Hom A a 1 ≅ {*}
--   ccc-2 : Hom A c (a × b) ≅ (Hom A c a ) × ( Hom A c b )
--   ccc-3 : Hom A a (c ^ b) ≅ Hom A (a × b) c

record IsoS {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ') (a b : Obj A) ( a' b' : Obj B )
          :  Set ( c₁  ⊔  c₂ ⊔ ℓ ⊔  c₁'  ⊔  c₂' ⊔ ℓ' ) where
      field
           ≅→ :  Hom A a b   → Hom B a' b'
           ≅← :  Hom B a' b' → Hom A a b
           iso→  : {f : Hom B a' b' }  → B [ ≅→ ( ≅← f) ≈ f ]
           iso←  : {f : Hom A a b }    → A [ ≅← ( ≅→ f) ≈ f ]

data One {c : Level} : Set c where
  OneObj : One   -- () in Haskell ( or any one object set )

OneCat : Category Level.zero Level.zero Level.zero
OneCat = record {
    Obj  = One ;
    Hom = λ a b →   One  ;
    _o_ =  λ{a} {b} {c} x y → OneObj ;
    _≈_ =  λ x y → x ≡ y ;
    Id  =  λ{a} → OneObj ;
    isCategory  = record {
            isEquivalence =  record {refl = refl ; trans = trans ; sym = sym } ;
            identityL  = λ{a b f} → lemma {a} {b} {f} ;
            identityR  = λ{a b f} → lemma {a} {b} {f} ;
            o-resp-≈  = λ{a b c f g h i} _ _ →  refl ;
            associative  = λ{a b c d f g h } → refl 
       }
   }  where
         lemma : {a b : One {Level.zero}} → { f : One {Level.zero}} →  OneObj ≡ f
         lemma {a} {b} {f} with f
         ... | OneObj = refl


record IsCCC {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (one : Obj A)
          ( _*_ : Obj A → Obj A → Obj A  ) ( _^_ : Obj A → Obj A → Obj A  ) :  Set ( c₁  ⊔  c₂ ⊔ ℓ ) where
     field
       ccc-1 : {a : Obj A}     →  --   Hom A a one ≅ {*}
                          IsoS A OneCat  a one OneObj OneObj  
       ccc-2 : {a b c : Obj A} →  --  Hom A c ( a * b ) ≅ ( Hom A c a ) * ( Hom A c b )
                          IsoS A (A × A) c (a * b) (c , c) (a , b)
       ccc-3 : {a b c : Obj A} →  -- Hom A a ( c ^ b ) ≅ Hom A ( a * b ) c
                          IsoS A A  a (c ^ b) (a * b) c
        
        
record CCC {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) :  Set ( c₁  ⊔  c₂ ⊔ ℓ ) where
     field
       one : Obj A
       _*_ : Obj A → Obj A → Obj A
       _^_ : Obj A → Obj A → Obj A  
       isCCC : IsCCC A one _*_ _^_

record IsEqCCC {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (one : Obj A) ( oneT : ( a : Obj A ) → Hom A a one )
          ( _*_ : Obj A → Obj A → Obj A  ) ( _^_ : Obj A → Obj A → Obj A  ) :  Set ( c₁  ⊔  c₂ ⊔ ℓ ) where
     field
       e2  : {a : Obj A} { f : Hom A a one } →  A [ f ≈ oneT a ]
       e3a : {!!}

