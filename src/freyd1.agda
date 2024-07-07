{-# OPTIONS --cubical-compatible --safe #-}

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level

module freyd1 {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} {A : Category c₁ c₂ ℓ}  {C : Category c₁' c₂' ℓ'} 
    ( F : Functor A C ) ( G : Functor A C ) where

open import Definitions
open import HomReasoning
open Functor

open import Comma1 F G
-- open import freyd CommaCategory  -- we don't need this yet

open import Category.Cat  -- Functor composition
open NTrans
open Complete
open CommaObj
open CommaHom
open Limit
open IsLimit

--    
--
--  F : A → C
--  G : A → C
-- 
--  if A is complete and G preserve limit, Comma Category  F↓G is complete
--    i.e. it has limit for Γ : I → F↓G 
-- 
-- 
-- 

--- Get a functor Functor I A from a functor I CommaCategory
---
FIA : { I : Category c₁ c₂ ℓ } →  ( Γ : Functor I CommaCategory )  → Functor I A
FIA {I} Γ = record {
  FObj = λ x → obj (FObj Γ x ) ;
  FMap = λ {a} {b} f →  arrow (FMap Γ f )  ;
  isFunctor = record {
             identity = identity
             ; distr = IsFunctor.distr (isFunctor Γ) 
             ; ≈-cong = IsFunctor.≈-cong (isFunctor Γ) 
          }} where
      identity :  {x : Obj I } → A [ arrow (FMap Γ (id1 I x)) ≈ id1 A  (obj (FObj Γ x)) ]
      identity {x} = let  open ≈-Reasoning (A) in begin
             arrow (FMap Γ (id1 I x)) 
         ≈⟨ IsFunctor.identity (isFunctor Γ)   ⟩
             id1 A  (obj (FObj Γ x))     
         ∎

--- Get a nat on A from a nat on CommaCategory
--
NIA : { I : Category c₁ c₂ ℓ } →   ( Γ : Functor I CommaCategory ) 
     (c : Obj CommaCategory ) ( ta : NTrans I CommaCategory ( K I CommaCategory c ) Γ )  → NTrans I A ( K I A (obj c) )  (FIA Γ)
NIA  {I} Γ c ta = record {
        TMap = λ x → arrow (TMap ta x )
        ; isNTrans = record { commute = comm1 }
    }  where
        comm1 : {a b : Obj I} {f : Hom I a b} → 
             A [ A [ FMap (FIA Γ) f o arrow (TMap ta a) ] ≈ A [ arrow (TMap ta b) o FMap (K I A (obj c)) f ] ]
        comm1 {a} {b} {f} = IsNTrans.commute (isNTrans ta )


open LimitPreserve

-- Limit on A from Γ : I → CommaCategory
--
LimitC : { I : Category c₁ c₂ ℓ } → ( comp : Complete  {c₁} {c₂} {ℓ} A  ) 
    → ( Γ : Functor I CommaCategory ) 
    → ( glimit :  LimitPreserve I A C G )
    → Limit I C (G  ○  (FIA Γ)) 
LimitC  {I} comp Γ glimit  = plimit glimit (climit comp (FIA Γ))

tu :  { I : Category c₁ c₂ ℓ } →  ( comp : Complete  {c₁} {c₂} {ℓ} A ) →  ( Γ : Functor I CommaCategory )
    →   NTrans I C (K I C (FObj F (limit-c comp (FIA Γ)))) (G  ○  (FIA Γ))
tu {I} comp Γ = record {
      TMap  = λ i →  C [ hom ( FObj Γ i ) o  FMap F ( TMap (t0 ( climit comp (FIA Γ)))  i) ]
    ; isNTrans = record { commute = λ {a} {b} {f} → commute {a} {b} {f} }
  } where
        commute : {a b : Obj I} {f : Hom I a b}   →
              C [ C [ FMap (G  ○  (FIA Γ)) f o C [ hom (FObj Γ a) o FMap F (TMap (t0 ( climit comp (FIA Γ))) a) ] ] 
            ≈ C [ C [ hom (FObj Γ b) o FMap F (TMap (t0 ( climit comp (FIA Γ))) b) ] o FMap (K I C (FObj F (limit-c comp (FIA Γ)))) f ] ]
        commute  {a} {b} {f} =  let  open ≈-Reasoning (C) in begin
             FMap (G  ○  (FIA Γ)) f o ( hom (FObj Γ a) o FMap F (TMap (t0 ( climit comp (FIA Γ)))  a ))
         ≈⟨⟩
             FMap G (arrow (FMap Γ f ) ) o ( hom (FObj Γ a) o FMap F ( TMap (t0 ( climit comp (FIA Γ)))  a ))
         ≈⟨ assoc ⟩
             (FMap G (arrow (FMap Γ f ) ) o  hom (FObj Γ a)) o FMap F ( TMap (t0 ( climit comp (FIA Γ)))  a )
         ≈⟨ car ( comm (FMap Γ f))  ⟩
              (hom (FObj Γ b) o FMap F (arrow (FMap Γ f)) ) o FMap F ( TMap (t0 ( climit comp (FIA Γ)))  a )
         ≈↑⟨ assoc ⟩
              hom (FObj Γ b) o ( FMap F (arrow (FMap Γ f))  o FMap F ( TMap (t0 ( climit comp (FIA Γ)))  a ) )
         ≈↑⟨  cdr (distr F)  ⟩
              hom (FObj Γ b) o ( FMap F (A [ arrow (FMap Γ f)  o TMap (t0 ( climit comp (FIA Γ)))  a ] ) )
         ≈⟨⟩
              hom (FObj Γ b) o ( FMap F (A [ FMap (FIA Γ)  f  o TMap (t0 ( climit comp (FIA Γ)))  a ] ) )
         ≈⟨ cdr ( fcong F ( IsNTrans.commute (isNTrans (t0 ( climit comp (FIA Γ)))  ))) ⟩
              hom (FObj Γ b) o ( FMap F ( A [ (TMap (t0 ( climit comp (FIA Γ))) b) o FMap (K I A (a0 (climit comp (FIA Γ)))) f ] ))
         ≈⟨⟩
              hom (FObj Γ b) o ( FMap F ( A [ (TMap (t0 ( climit comp (FIA Γ))) b) o id1 A (limit-c comp (FIA Γ)) ] ))
         ≈⟨ cdr ( distr F ) ⟩
              hom (FObj Γ b) o ( FMap F (TMap (t0 ( climit comp (FIA Γ))) b) o FMap F (id1 A (limit-c comp (FIA Γ))))
         ≈⟨ cdr ( cdr ( IsFunctor.identity (isFunctor F) ) ) ⟩
              hom (FObj Γ b) o ( FMap F (TMap (t0 ( climit comp (FIA Γ))) b) o id1 C (FObj F (limit-c comp (FIA Γ))))
         ≈⟨ assoc ⟩
             ( hom (FObj Γ b) o FMap F (TMap (t0 ( climit comp (FIA Γ))) b)) o FMap (K I C (FObj F (limit-c comp (FIA Γ)))) f
         ∎
limitHom :  { I : Category c₁ c₂ ℓ } →  (comp : Complete  {c₁} {c₂} {ℓ} A ) →  ( Γ : Functor I CommaCategory )
    → ( glimit :  LimitPreserve I A C G ) → Hom C (FObj F (limit-c comp (FIA Γ ) )) (FObj G (limit-c comp (FIA Γ) ))
limitHom comp Γ glimit = limit (isLimit (LimitC comp Γ glimit  )) (FObj F ( limit-c  comp (FIA Γ))) (tu comp Γ )

commaLimit :  { I : Category c₁ c₂ ℓ } →  ( Complete  {c₁} {c₂} {ℓ} A ) →  ( Γ : Functor I CommaCategory )  
    → ( glimit :  LimitPreserve I A C G )
    →  Obj CommaCategory
commaLimit {I} comp Γ glimit = record {
      obj = limit-c  comp (FIA Γ)
      ; hom = limitHom comp Γ glimit
   } 


commaNat : { I : Category c₁ c₂ ℓ } →   ( comp : Complete  {c₁} {c₂} {ℓ} A ) →  ( Γ : Functor I CommaCategory ) 
     → ( glimit :   LimitPreserve I A C G )
     → NTrans I CommaCategory (K I CommaCategory (commaLimit {I} comp Γ glimit))  Γ
commaNat {I} comp  Γ glimit = record {
       TMap = λ x → record {
              arrow =  TMap ( limit-u comp (FIA Γ ) ) x 
            ; comm  = comm1 x
          } 
       ; isNTrans = record { commute = comm2 }
    } where
       comm1 : (x : Obj I )  →
              C [ C [ FMap G (TMap (limit-u comp (FIA Γ)) x) o hom (FObj (K I CommaCategory (commaLimit comp Γ glimit)) x) ] 
            ≈ C [ hom (FObj Γ x) o FMap F (TMap (limit-u comp (FIA Γ)) x) ] ] 
       comm1 x =  let  open ≈-Reasoning (C) in begin
              FMap G (TMap (limit-u comp (FIA Γ)) x) o hom (FObj (K I CommaCategory (commaLimit comp Γ glimit)) x)
         ≈⟨⟩
              FMap G (TMap (limit-u comp (FIA Γ)) x) o hom (commaLimit comp Γ glimit) 
         ≈⟨⟩
              FMap G (TMap (limit-u comp (FIA Γ)) x) o limit (isLimit (LimitC comp Γ glimit  )) (FObj F ( limit-c  comp (FIA Γ))) (tu comp Γ )
         ≈⟨⟩
              TMap (t0 ( LimitC comp Γ glimit )) x  o limit (isLimit (LimitC comp Γ glimit  )) (FObj F ( limit-c  comp (FIA Γ))) (tu comp Γ )
         ≈⟨ t0f=t ( isLimit (  LimitC comp Γ glimit ) ) ⟩
              TMap (tu comp Γ) x 
         ≈⟨⟩
              hom (FObj Γ x) o FMap F (TMap (limit-u comp (FIA Γ)) x)
         ∎
       comm2 : {a b : Obj I} {f : Hom I a b} →
          CommaCategory [ CommaCategory [ FMap Γ f o record { arrow = TMap (limit-u comp (FIA Γ)) a ; comm = comm1 a } ]
          ≈ CommaCategory [ record { arrow = TMap (limit-u comp (FIA Γ)) b ; comm = comm1 b } o FMap (K I CommaCategory (commaLimit comp Γ glimit)) f ] ]
       comm2 {a} {b} {f} =  let  open ≈-Reasoning (A) in begin
              FMap (FIA Γ) f  o TMap (limit-u comp (FIA Γ)) a 
         ≈⟨ IsNTrans.commute (isNTrans (limit-u comp (FIA Γ)))   ⟩
              TMap (limit-u comp (FIA Γ)) b  o FMap (K I A (limit-c comp (FIA Γ))) f 
         ∎

gnat :  { I : Category c₁ c₂ ℓ } →   ( Γ : Functor I CommaCategory )
     →  (a : CommaObj) → ( t : NTrans I CommaCategory (K I CommaCategory a)  Γ ) → 
              NTrans I C (K I C (FObj F (obj a))) (G ○ FIA Γ)
gnat {I} Γ a t = record {
       TMap = λ i → C [  hom ( FObj Γ i ) o FMap F ( TMap (NIA Γ a t) i ) ]
      ; isNTrans = record { commute = λ {x y f} → comm1 x y f }
    } where
       comm1 :  (x y : Obj I) (f : Hom I x y ) →
                C [ C [ FMap (G ○ FIA Γ) f o C [ hom (FObj Γ x) o FMap F (TMap (NIA Γ a t) x) ] ]
                ≈ C [ C [ hom (FObj Γ y) o FMap F (TMap (NIA Γ a t) y) ] o FMap (K I C (FObj F (obj a))) f ] ]
       comm1 x y f =  let  open ≈-Reasoning (C) in begin
             FMap (G ○ FIA Γ) f o ( hom (FObj Γ x) o FMap F (TMap (NIA Γ a t) x  ))
         ≈⟨⟩
             FMap G (FMap (FIA Γ) f) o ( hom (FObj Γ x) o FMap F (TMap (NIA Γ a t) x  ))
         ≈⟨ assoc ⟩
             (FMap G (FMap (FIA Γ) f) o ( hom (FObj Γ x))) o FMap F (TMap (NIA Γ a t) x  )
         ≈⟨ car ( comm (FMap Γ f) ) ⟩
             ( hom (FObj Γ y)  o  FMap F (FMap (FIA Γ) f )) o FMap F (TMap (NIA Γ a t) x  )
         ≈↑⟨ assoc ⟩
              hom (FObj Γ y)  o  ( FMap F (FMap (FIA Γ) f ) o FMap F (TMap (NIA Γ a t) x  ))
         ≈↑⟨ cdr (distr F) ⟩
              hom (FObj Γ y)  o  ( FMap F ( A [ FMap (FIA Γ) f  o TMap (NIA Γ a t) x  ])  )
         ≈⟨ cdr ( fcong F ( IsNTrans.commute ( isNTrans ( NIA Γ a t )))) ⟩
              hom (FObj Γ y)  o  ( FMap F ( A [ TMap (NIA Γ a t) y   o id1 A (obj a) ])  )
         ≈⟨ cdr ( fcong F ( IsCategory.identityR (Category.isCategory A)))  ⟩
              hom (FObj Γ y) o FMap F (TMap (NIA Γ a t) y)  
         ≈↑⟨ idR ⟩
             ( hom (FObj Γ y) o FMap F (TMap (NIA Γ a t) y) ) o FMap (K I C (FObj F (obj a))) f
         ∎


comma-a0 :  { I : Category c₁ c₂ ℓ } →   ( comp : Complete  {c₁} {c₂} {ℓ} A ) →  ( Γ : Functor I CommaCategory )
     → ( glimit :   LimitPreserve I A C G ) (a : CommaObj) → ( t : NTrans I CommaCategory (K I CommaCategory a)  Γ ) → Hom CommaCategory a (commaLimit comp Γ glimit)
comma-a0  {I} comp Γ glimit a t = record {
       arrow  = limit (isLimit ( climit comp (FIA Γ) ) ) (obj a ) (NIA  {I} Γ a t )
     ; comm = comm1
   } where
      comm1 : C [ C [ FMap G (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t)) o hom a ]
        ≈ C [ hom (commaLimit comp Γ glimit) o FMap F (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t)) ] ]
      comm1 =  let  open ≈-Reasoning (C) in begin
            FMap G (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t)) o hom a 
         ≈↑⟨ limit-uniqueness  (isLimit (LimitC comp Γ glimit  ))  ( λ {i} → begin
                     TMap (t0 (LimitC comp Γ glimit)) i o ( FMap G (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t)) o hom a )
                  ≈⟨ assoc  ⟩ 
                     ( TMap (t0 (LimitC comp Γ glimit)) i o  FMap G (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t))) o hom a 
                  ≈⟨⟩ 
                     ( FMap G ( TMap (limit-u comp (FIA Γ )) i ) o  FMap G (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t))) o hom a 
                  ≈↑⟨ car ( distr G ) ⟩ 
                     FMap G ( A [ TMap (limit-u comp (FIA Γ )) i  o  limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t) ] )  o hom a 
                  ≈⟨ car ( fcong G ( t0f=t (isLimit (climit comp (FIA Γ ))))) ⟩ 
                     FMap G (arrow (TMap t i))  o hom a 
                  ≈⟨ comm ( TMap t i) ⟩ 
                     hom ( FObj Γ i ) o FMap F ( TMap (NIA Γ a t) i )
                  ≈⟨⟩ 
                     TMap (gnat Γ a t) i
                  ∎
           ) ⟩
            limit (isLimit (LimitC comp Γ glimit  )) (FObj F (obj a)) (gnat Γ a t )
         ≈⟨ limit-uniqueness  (isLimit (LimitC comp Γ glimit  )) ( λ {i} → begin 
                      TMap (t0 (LimitC comp Γ glimit  )) i  o
                         ( limit (isLimit (LimitC comp Γ glimit  )) (FObj F ( limit-c  comp (FIA Γ))) (tu comp Γ )  
                          o FMap F (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t)) )
                   ≈⟨ assoc  ⟩ 
                      ( TMap (t0 (LimitC comp Γ glimit  )) i  o
                         ( limit (isLimit (LimitC comp Γ glimit  )) (FObj F ( limit-c  comp (FIA Γ))) (tu comp Γ )  ))
                          o FMap F (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t)) 
                   ≈⟨ car ( t0f=t ( isLimit (LimitC comp Γ glimit  )) ) ⟩ 
                         TMap (tu comp Γ ) i  o FMap F (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t)) 
                   ≈⟨⟩ 
                         ( hom ( FObj Γ i ) o  FMap F ( TMap (t0 ( climit comp (FIA Γ)))  i) )
                                o FMap F (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t)) 
                   ≈↑⟨ assoc ⟩ 
                           hom ( FObj Γ i ) o 
                              ((FMap F ( TMap (t0 ( climit comp (FIA Γ)))  i) ) o FMap F (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t)) )
                   ≈↑⟨ cdr (  distr F)  ⟩ 
                           hom ( FObj Γ i ) o  
                               FMap F ( A [ TMap (t0 ( climit comp (FIA Γ)))  i o limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t) ] )
                   ≈⟨ cdr ( fcong F ( t0f=t (isLimit (climit comp (FIA Γ))))) ⟩ 
                           hom ( FObj Γ i ) o FMap F ( TMap (NIA Γ a t) i )
                   ≈⟨⟩ 
                       TMap (gnat Γ a t ) i
                 ∎
           ) ⟩
            limit (isLimit (LimitC comp Γ glimit  )) (FObj F ( limit-c  comp (FIA Γ))) (tu comp Γ )  
                 o FMap F (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t))
         ≈⟨⟩
            hom (commaLimit comp Γ glimit) o FMap F (limit (isLimit (climit comp (FIA Γ))) (obj a) (NIA Γ a t))
         ∎

comma-t0f=t :  { I : Category c₁ c₂ ℓ } →   ( comp : Complete  {c₁} {c₂} {ℓ} A ) →  ( Γ : Functor I CommaCategory )
     → ( glimit :   LimitPreserve I A C G ) (a : CommaObj) → ( t : NTrans I CommaCategory (K I CommaCategory a)  Γ ) (i : Obj I )
     →   CommaCategory [ CommaCategory [ TMap (commaNat comp Γ glimit) i o comma-a0 comp Γ glimit a t ] ≈ TMap t i ]
comma-t0f=t  {I} comp Γ glimit a t i = let  open ≈-Reasoning (A) in begin
             TMap ( limit-u comp (FIA Γ ) ) i o limit (isLimit ( climit comp (FIA Γ) ) ) (obj a ) (NIA  {I} Γ a t )
         ≈⟨ t0f=t (isLimit ( climit comp (FIA Γ) ) )  ⟩
             TMap (NIA  {I} Γ a t ) i
         ∎

comma-uniqueness :  { I : Category c₁ c₂ ℓ } →   ( comp : Complete  {c₁} {c₂} {ℓ} A ) →  ( Γ : Functor I CommaCategory )
     → ( glimit :   LimitPreserve I A C G ) (a : CommaObj) → ( t : NTrans I CommaCategory (K I CommaCategory a)  Γ ) 
     →  ( f :  Hom CommaCategory a  (commaLimit comp Γ glimit)) 
     →   ( ∀ { i : Obj I } → CommaCategory [ CommaCategory [ TMap ( commaNat {  I} comp Γ glimit ) i o  f ]  ≈ TMap t i ] )
     → CommaCategory [ comma-a0 comp Γ glimit a t ≈ f ]
comma-uniqueness  {I} comp Γ glimit a t f t=f    = let  open ≈-Reasoning (A) in begin
             limit (isLimit ( climit comp (FIA Γ) ) ) (obj a ) (NIA  {I} Γ a t )
         ≈⟨ limit-uniqueness (isLimit ( climit comp (FIA Γ) ) )   t=f ⟩
             arrow f
         ∎

hasLimit : { I : Category c₁ c₂ ℓ } → ( comp : Complete  {c₁} {c₂} {ℓ} A  ) 
    → ( glimit :   LimitPreserve I A C G )
    → ( Γ : Functor I CommaCategory ) 
    → Limit I CommaCategory Γ 
hasLimit {I} comp glimit Γ = record {
     a0 = commaLimit {I} comp Γ glimit ;
     t0 = commaNat {  I} comp Γ glimit  ;
     isLimit = record {
             limit = λ a t → comma-a0 comp Γ glimit a t ;
             t0f=t = λ {a t i } →  comma-t0f=t  comp Γ glimit a t i ;
             limit-uniqueness =  λ {a} {t} {f} t=f →  comma-uniqueness  {I} comp Γ glimit a t f t=f
     }
   }
