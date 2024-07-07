{-# OPTIONS --cubical-compatible --safe #-}

open import Level
open import Category 
module Comma {c₁ c₂ ℓ c₁' c₂' ℓ' c₁'' c₂'' ℓ'' : Level} {A : Category c₁ c₂ ℓ} {B : Category c₁'' c₂'' ℓ''} {C : Category c₁' c₂' ℓ'} 
    ( F : Functor A C ) ( G : Functor B C ) where

open import HomReasoning
open import Definitions

--
--      F     G
--    A -> C <- B
--

open Functor

record CommaObj :  Set ( c₁  ⊔  c₁'' ⊔  c₂' ) where
     field
        obj : Obj A
        objb : Obj B
        hom : Hom C ( FObj F obj ) ( FObj G objb ) 

open CommaObj

record CommaHom ( a b :  CommaObj ) :  Set ( c₂ ⊔ c₂'' ⊔ ℓ' ) where
     field
        arrow  : Hom A ( obj a ) ( obj b )
        arrowg : Hom B ( objb a ) ( objb b )
        comm   :  C [ C [ FMap G arrowg  o hom a ]  ≈ C [ hom b  o  FMap F arrow ]  ]

open CommaHom

record _⋍_ { a b :  CommaObj } ( f g : CommaHom a b ) :  Set (ℓ ⊔ ℓ'' ) where
     field 
        eqa : A [ arrow f ≈ arrow g ] 
        eqb : B [ arrowg f ≈ arrowg g ]

open _⋍_

_∙_ :  {a b c : CommaObj } → CommaHom b c → CommaHom a b → CommaHom a c
_∙_ {a} {b} {c} f g = record { 
         arrow = A [ arrow f o arrow g ] ;
         arrowg = B [ arrowg f o arrowg g ] ;
         comm  = comm1
     } where
        comm1 :  C [ C [ FMap G (B [ arrowg f o arrowg g ] ) o hom a ]  ≈ C [ hom c  o  FMap F (A [ arrow f o arrow g ]) ]  ]
        comm1 =  let open ≈-Reasoning C in begin
               FMap G (B [ arrowg f o arrowg g ] ) o hom a    
           ≈⟨ car ( distr G ) ⟩
               ( FMap G (arrowg f)  o   FMap G (arrowg g )) o hom a    
           ≈↑⟨ assoc ⟩
               FMap G (arrowg f)  o ( FMap G (arrowg g )  o hom a )
           ≈⟨ cdr ( comm g ) ⟩
               FMap G (arrowg f)  o  ( hom b  o  FMap F (arrow g ) )
           ≈⟨ assoc  ⟩
               ( FMap G (arrowg f)  o  hom b) o  FMap F (arrow g ) 
           ≈⟨ car ( comm f ) ⟩
               ( hom c o FMap F (arrow f)  ) o  FMap F (arrow g ) 
           ≈↑⟨ assoc  ⟩
                hom c o ( FMap F (arrow f)   o  FMap F (arrow g ) )
           ≈↑⟨ cdr ( distr F) ⟩
                hom c o  FMap F (A [ arrow f o arrow g ])
           ∎ 

CommaId : { a : CommaObj } → CommaHom a a
CommaId {a} = record {  arrow = id1 A ( obj a ) ;  arrowg = id1 B ( objb a ) ;  
      comm = comm2 } where
        comm2 :  C [ C [ FMap G (id1 B (objb a)) o hom a ]  ≈ C [ hom a  o  FMap F (id1 A (obj a)) ]  ]
        comm2 =  let open ≈-Reasoning C in begin
                 FMap G (id1 B (objb a)) o hom a
           ≈⟨ car ( IsFunctor.identity ( isFunctor G ) )  ⟩
                 id1 C (FObj G (objb a))  o  hom a
           ≈⟨ idL  ⟩
                 hom a
           ≈↑⟨ idR  ⟩
                 hom a  o  id1 C (FObj F (obj a))
           ≈↑⟨ cdr ( IsFunctor.identity ( isFunctor F ) )⟩
                 hom a  o  FMap F (id1 A (obj a))
           ∎ 
  
isCommaCategory : IsCategory CommaObj CommaHom _⋍_  _∙_  CommaId
isCommaCategory = record  { 
          isEquivalence = record { refl =  record { eqa = let open ≈-Reasoning (A) in refl-hom ; eqb =  let open ≈-Reasoning (B) in refl-hom } ;
                  sym = λ {f} {g} f=g → record { eqa =  let open ≈-Reasoning (A) in sym ( eqa f=g) ; eqb =  let open ≈-Reasoning (B) in sym ( eqb f=g ) }   ;
                  trans = λ {f} {g} {h}  f=g g=h → record {
                     eqa =  let open ≈-Reasoning (A) in trans-hom (eqa f=g) (eqa g=h) 
                     ; eqb = let open ≈-Reasoning (B) in trans-hom (eqb f=g) (eqb g=h)  
              } }
        ; identityL = λ{a b f} →   record { 
                eqa = let open ≈-Reasoning (A) in idL {obj a} {obj b} {arrow f}
              ; eqb = let open ≈-Reasoning (B) in idL {objb a} {objb b} {arrowg f}
           }
        ; identityR = λ{a b f} →   record { 
                eqa = let open ≈-Reasoning (A) in idR {obj a} {obj b} {arrow f}
              ; eqb = let open ≈-Reasoning (B) in idR {objb a} {objb b} {arrowg f}
           }
        ; o-resp-≈ =    λ  {a b c  } {f g } {h i } f=g h=i → record {
                eqa = IsCategory.o-resp-≈ (Category.isCategory A)  (eqa f=g) (eqa h=i )
              ; eqb = IsCategory.o-resp-≈ (Category.isCategory B)  (eqb f=g) (eqb h=i )
           }
        ; associative = λ {a b c d} {f}  {g} {h} → record {
                eqa = IsCategory.associative (Category.isCategory A) 
              ; eqb = IsCategory.associative (Category.isCategory B) 
              }
        }  

CommaCategory   : Category  (c₂' ⊔ c₁ ⊔ c₁'') (ℓ' ⊔ c₂ ⊔ c₂'') (ℓ ⊔ ℓ'' )
CommaCategory  = record { Obj = CommaObj 
         ; Hom = CommaHom
         ; _o_ = _∙_
         ; _≈_ = _⋍_
         ; Id  = CommaId
         ; isCategory = isCommaCategory
         }

