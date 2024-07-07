{-# OPTIONS --cubical-compatible --safe #-}

open import Level
open import Category 
module Comma1 {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} {A : Category c₁ c₂ ℓ}  {C : Category c₁' c₂' ℓ'} 
    ( F : Functor A C ) ( G : Functor A C ) where

open import HomReasoning
open import Definitions

--
--      F     G
--    A -> C <- A
--

open Functor

record CommaObj :  Set ( c₁  ⊔  c₂' ) where
     field
        obj : Obj A
        hom : Hom C ( FObj F obj ) ( FObj G obj ) 

open CommaObj

record CommaHom ( a b :  CommaObj ) :  Set ( c₂ ⊔   ℓ' ) where
     field
        arrow  : Hom A ( obj a ) ( obj b )
        comm   :  C [ C [ FMap G arrow  o hom a ]  ≈ C [ hom b  o  FMap F arrow ]  ]

open CommaHom

_∙_ :  {a b c : CommaObj } → CommaHom b c → CommaHom a b → CommaHom a c
_∙_ {a} {b} {c} f g = record { 
         arrow = A [ arrow f o arrow g ] ;
         comm  = comm1
     } where
        comm1 :  C [ C [ FMap G (A [ arrow f o arrow g ] ) o hom a ]  ≈ C [ hom c  o  FMap F (A [ arrow f o arrow g ]) ]  ]
        comm1 =  let open ≈-Reasoning C in begin
               FMap G (A [ arrow f o arrow g ] ) o hom a    
           ≈⟨ car ( distr G ) ⟩
               ( FMap G (arrow f)  o   FMap G (arrow g )) o hom a    
           ≈↑⟨ assoc ⟩
               FMap G (arrow f)  o ( FMap G (arrow g )  o hom a )
           ≈⟨ cdr ( comm g ) ⟩
               FMap G (arrow f)  o  ( hom b  o  FMap F (arrow g ) )
           ≈⟨ assoc  ⟩
               ( FMap G (arrow f)  o  hom b) o  FMap F (arrow g ) 
           ≈⟨ car ( comm f ) ⟩
               ( hom c o FMap F (arrow f)  ) o  FMap F (arrow g ) 
           ≈↑⟨ assoc  ⟩
                hom c o ( FMap F (arrow f)   o  FMap F (arrow g ) )
           ≈↑⟨ cdr ( distr F) ⟩
                hom c o  FMap F (A [ arrow f o arrow g ])
           ∎ 

CommaId : { a : CommaObj } → CommaHom a a
CommaId {a} = record {  arrow = id1 A ( obj a ) ;  
      comm = comm2 } where
        comm2 :  C [ C [ FMap G (id1 A (obj a)) o hom a ]  ≈ C [ hom a  o  FMap F (id1 A (obj a)) ]  ]
        comm2 =  let open ≈-Reasoning C in begin
                 FMap G (id1 A (obj a)) o hom a
           ≈⟨ car ( IsFunctor.identity ( isFunctor G ) )  ⟩
                 id1 C (FObj G (obj a))  o  hom a
           ≈⟨ idL  ⟩
                 hom a
           ≈↑⟨ idR  ⟩
                 hom a  o  id1 C (FObj F (obj a))
           ≈↑⟨ cdr ( IsFunctor.identity ( isFunctor F ) )⟩
                 hom a  o  FMap F (id1 A (obj a))
           ∎ 
 
_⋍_ : { a b :  CommaObj } ( f g : CommaHom a b ) →  Set ℓ
f ⋍ g  = A [ arrow f ≈ arrow g ]

 
isCommaCategory : IsCategory CommaObj CommaHom _⋍_  _∙_  CommaId
isCommaCategory = record  { 
          isEquivalence = record { refl =  let open ≈-Reasoning (A) in refl-hom ;
                  sym = let open ≈-Reasoning (A) in sym ;
                  trans = let open ≈-Reasoning (A) in trans-hom 
              } 
        ; identityL = let open ≈-Reasoning (A) in idL
        ; identityR = let open ≈-Reasoning (A) in idR
        ; o-resp-≈ =   IsCategory.o-resp-≈ ( Category.isCategory A )
        ; associative =  IsCategory.associative ( Category.isCategory A )
        }  

CommaCategory   : Category  (c₂' ⊔ c₁) (ℓ' ⊔ c₂) ℓ
CommaCategory  = record { Obj = CommaObj 
         ; Hom = CommaHom
         ; _o_ = _∙_
         ; _≈_ = _⋍_
         ; Id  = CommaId
         ; isCategory = isCommaCategory
         }

open NTrans

nat-lemma : NTrans A C F G → Functor A CommaCategory
nat-lemma n = record {
        FObj = λ x → fobj x ;
        FMap = λ {a} {b} f → fmap {a} {b} f ;
        isFunctor = record {
             identity = λ{x} → identity x
             ; distr = λ {a} {b} {c} {f} {g}   → distr1 {a} {b} {c} {f} {g}
             ; ≈-cong = λ {a} {b} {c} {f}   → ≈-cong  {a} {b} {c} {f}
          }
   } where
        fobj :  Obj A → Obj CommaCategory
        fobj x = record { obj = x ; hom = TMap n x }
        fmap :  {a b : Obj A } → Hom A a b → Hom CommaCategory (fobj a) (fobj b )
        fmap f = record { arrow = f ; comm = IsNTrans.commute (isNTrans n ) }
        ≈-cong :  {a : Obj A} {b : Obj A} {f g : Hom A a b}  → A [ f ≈ g ]  → CommaCategory [ fmap f ≈ fmap g ]
        ≈-cong  {a} {b} {f} {g} f=g = f=g
        identity : (x : Obj A ) ->  CommaCategory [ fmap (id1 A x) ≈  id1 CommaCategory (fobj x) ]
        identity x = let open ≈-Reasoning (A) in  begin
                arrow (fmap (id1 A x))
             ≈⟨⟩
                id1 A x
             ≈⟨⟩
                arrow (id1 CommaCategory (fobj x))
             ∎
        distr1 : {a : Obj A} {b : Obj A} {c : Obj A} {f : Hom A a b} {g : Hom A b c} →
               CommaCategory [ fmap (A [ g o f ])  ≈  CommaCategory [ fmap g o fmap f ] ]
        distr1 = let open ≈-Reasoning (A) in  refl-hom

nat-f : Functor A C  → Functor A CommaCategory → Functor A C
nat-f F N = record {
        FObj = λ x → FObj F ( obj ( FObj N x )) ;
        FMap = λ {a} {b} f → FMap F (arrow (FMap N f))  ;
        isFunctor = record {
             identity = λ{x} → identity x
             ; distr = λ {a} {b} {c} {f} {g}   → distr1 {a} {b} {c} {f} {g}
             ; ≈-cong = λ {a} {b} {f} {g}   →  ≈-cong  {a} {b} {f} {g}
          }
   } where
        identity : (x : Obj A ) ->   C [ FMap F (arrow (FMap N (id1 A x))) ≈ id1 C (FObj F (obj (FObj N x))) ]
        identity x = let open ≈-Reasoning (C) in  begin
                 FMap F (arrow (FMap N (id1 A x)))
             ≈⟨ fcong F ( IsFunctor.identity ( isFunctor N)  ) ⟩
                 FMap F (id1 A (obj (FObj N x)))
             ≈⟨ IsFunctor.identity ( isFunctor F ) ⟩
                id1 C (FObj F (obj (FObj N x)))
             ∎
        distr1 : {a : Obj A} {b : Obj A} {c : Obj A} {f : Hom A a b} {g : Hom A b c} →
                C [ FMap F (arrow (FMap N (A [ g o f ]))) ≈
                C [ FMap F (arrow (FMap N g)) o FMap F (arrow (FMap N f)) ] ]
        distr1 {a} {b} {c} {f} {g} =  let open ≈-Reasoning (C) in  begin
                 FMap F (arrow (FMap N (A [ g o f ])))
             ≈⟨ fcong F ( IsFunctor.distr ( isFunctor N)  ) ⟩
                 FMap F (A [ arrow (FMap N g ) o arrow (FMap N f ) ] )
             ≈⟨ ( IsFunctor.distr ( isFunctor F )  ) ⟩
                FMap F (arrow (FMap N g)) o FMap F (arrow (FMap N f)) 
             ∎
        ≈-cong :  {a : Obj A} {b : Obj A} {f g : Hom A a b}  → A [ f ≈ g ]  → C [ FMap F (arrow (FMap N f)) ≈ FMap F (arrow (FMap N g)) ]
        ≈-cong  {a} {b} {f} {g} f=g = let open ≈-Reasoning (C) in  begin
                 FMap F (arrow (FMap N f)) 
             ≈⟨ fcong F (( IsFunctor.≈-cong ( isFunctor N)  ) f=g ) ⟩
                 FMap F (arrow (FMap N g)) 
             ∎

nat-lemma← : ( N : Functor A CommaCategory ) →  NTrans A C (nat-f F N) (nat-f G N)
nat-lemma← N = record {
        TMap = λ (a : Obj A ) →  tmap1 a
        ; isNTrans = record {
             commute = λ {a} {b} {f} → commute2 {a} {b} {f}
          }
   } where
       tmap1 : (a : Obj A ) →   Hom C (FObj F (obj ( FObj N a))) (FObj G (obj ( FObj N a)))
       tmap1 a = hom (FObj N a)
       commute2 :  {a b : Obj A } {f : Hom A a b  } →  
           C [ C [ FMap G ( arrow ( FMap N f)) o tmap1 a  ] ≈ C [ tmap1 b  o FMap F ( arrow ( FMap N f )) ]  ]
       commute2 {a} {b} {f} = comm ( FMap N f )


