-- {-# OPTIONS --cubical-compatible --safe #-}

open import Level
open import Category 
open import CCC
module CCCMonoidal {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) ( c : CCC A ) where

open import HomReasoning
open import Definitions
open import Data.Product renaming (_×_ to _/\_  ) hiding ( <_,_> )
open import Category.Constructions.Product
open import  Relation.Binary.PropositionalEquality as ER hiding ( [_] )

open Functor
open import monoidal

open CCC.CCC c
open CCC.IsCCC isCCC hiding ( _×_ )

CCCTensorProduct :  Functor ( A × A )  A
CCCTensorProduct =   record {
       FObj = λ x  →  proj₁ x ∧ proj₂ x
     ; FMap = λ {x : Obj ( A × A ) } {y} f → < A [ proj₁ f o π ] , A [ proj₂ f o π' ] >
     ; isFunctor = record {
             ≈-cong   = cc00
             ; identity = cc01
             ; distr    = cc02
     }
    }  where
        cc00 : {a b : Obj (A × A)}  {f g : Hom (A × A) a b } → (A × A) [ f ≈ g ] →
            A [ < A [ proj₁ f o π ] , A [ proj₂ f o π' ] > ≈ < A [ proj₁ g o π ] , A [ proj₂ g o π' ] > ]
        cc00 {a} {b} {f} {g} eq = begin
            <  proj₁ f o π  , proj₂ f o π'  > ≈⟨ π-cong (car (proj₁ eq)) (car (proj₂ eq)) ⟩
            <  proj₁ g o π  , proj₂ g o π'  > ∎ where open ≈-Reasoning A
        cc01 :  {a : Obj (A × A)} → A [ < A [ proj₁ (id1 (A × A) a) o π ] , A [ proj₂ (id1 (A × A) a) o π' ] > ≈ id1 A (proj₁ a ∧ proj₂ a) ]
        cc01 {a} = begin
            < proj₁ (id1 (A × A) a) o π  , proj₂ (id1 (A × A) a) o π' > ≈⟨ π-cong idL idL ⟩
            < π  ,  π' > ≈⟨ π-id ⟩
            id1 A (proj₁ a ∧ proj₂ a) ∎ where open ≈-Reasoning A
        cc02 : {a b c : Obj (A × A)}  {f : Hom (A × A) a b} {g : Hom (A × A) b c} →
            A [ < A [ proj₁ ((A × A) [ g o f ]) o π ] , A [ proj₂ ((A × A) [ g o f ]) o π' ] >
            ≈ A [ < A [ proj₁ g o π ] , A [ proj₂ g o π' ] > o < A [ proj₁ f o π ] , A [ proj₂ f o π' ] > ] ]
        cc02 {a} {b} {c} {f} {g} = begin
              < proj₁ ((A × A) [ g o f ]) o π  ,  proj₂ ((A × A) [ g o f ]) o π'  > ≈↑⟨ π-cong assoc assoc ⟩  
              < proj₁ g o (proj₁ f o π ) , proj₂ g o ( proj₂ f o π' ) > ≈↑⟨ π-cong (cdr e3a) (cdr e3b) ⟩  
              < proj₁ g o (π o < proj₁ f o π , proj₂ f o π' >) , proj₂ g o ( π' o < proj₁ f o π , proj₂ f o π' >) > ≈⟨ π-cong assoc assoc ⟩  
              < (proj₁ g o π) o < proj₁ f o π , proj₂ f o π' > , (proj₂ g o π') o < proj₁ f o π , proj₂ f o π' > > ≈↑⟨ distr-π ⟩  
              < proj₁ g o π  ,  proj₂ g o π'  > o <  proj₁ f o π  ,  proj₂ f o π' >
             ∎ where open ≈-Reasoning A

MonoidalCCC : Monoidal A
MonoidalCCC  = record {
      m-i = １ ;
      m-bi = CCCTensorProduct  ;
      isMonoidal = record {
              mα-iso  =  record { ≅→  =  mα→ ; ≅← =  mα← ; iso→  = ? ; iso← = ? } ;
              mλ-iso  =  record { ≅→  =  mλ→ ; ≅← =  mλ← ; iso→  = ? ; iso← = ? } ;
              mρ-iso  =  record { ≅→  =  mρ→ ; ≅← =  mρ← ; iso→  = ? ; iso← = ? } ;
              mα→nat1  = λ f → ? ;
              mα→nat2  =  λ f → ?  ;
              mα→nat3  =  λ f → ?  ;
              mλ→nat  =  λ f → ?  ;
              mρ→nat  =  λ f → ?  ;
              comm-penta  = ? ;
              comm-unit  = ?
      } } where
       open ≈-Reasoning A
       --  associative operations
       mα→ : {a b c : Obj A} →  Hom A ( ( a ∧ b ) ∧ c ) ( a ∧ ( b ∧ c ) )
       mα→ = α
       mα← : {a b c : Obj A} →  Hom A ( a ∧ ( b ∧ c ) ) ( ( a ∧ b ) ∧ c )
       mα← = α'
       mλ→ : {a  : Obj A} →  Hom A ( １ ∧ a ) a
       mλ→ {a} = π'
       mλ← : {a  : Obj A} →  Hom A  a ( １ ∧ a )
       mλ←  {a} = < ○ a , id1 A a >
       mλiso : {a : Obj A}  →  A [ A [ mλ← o mλ→ ] ≈ id1 A (１ ∧ a) ]
       mλiso = ?
       --  (a ∧ One) ⇔ a 
       mρ→ : {a  : Obj A} →  Hom A ( a ∧ １ )  a
       mρ→  {a} = π
       mρ← : {a  : Obj A} →  Hom A a ( a ∧ １ ) 
       mρ←  {a} = < id1 A a , ○ a >
       mρiso : {a : Obj A} →  A [ A [ mρ← o mρ→ ]  ≈ id1 A (a ∧ １)  ]
       mρiso = ?

-- This does not hold in general unlike Sets

open NTrans 

Monad→MonoidalFunctor : (m : Monad A) → CCCFunctor A A c c (Monad.T m)  → MonoidalFunctor MonoidalCCC MonoidalCCC
Monad→MonoidalFunctor  m cm = record {
         MF = Monad.T m
       ; ψ = cc11
       ; isMonodailFunctor = record {
          φab = ?
        ; associativity = ?
        ; unitarity-idr  =  ?
        ; unitarity-idl  = ?
       }
    } where
       open ≈-Reasoning A
       open CCCFunctor cm
       T = Monad.T m
       cc11 : Hom A １ (FObj (Monad.T m) １)
       cc11 = subst (λ k → Hom A １ k ) (ER.sym f１  ) (id1 A １ )
       tmap : (x y : Obj A) → Hom A ( FObj (Monad.T m) x ∧ FObj (Monad.T m) y) (FObj (Monad.T m) (x ∧ y))
       tmap x y = A [ cc12 o cc13 ]  where
           cc12 : Hom A ((((FObj T (FObj T (x ∧ y)) <= (FObj T x ∧ y)) ∧ (FObj T x ∧ y)) <= (x ∧ y)) ∧ (x ∧ y)) (FObj T (x ∧ y))
           cc12 =  TMap (Monad.μ m) (x ∧ y) o (  ε {FObj T (FObj T (x ∧ y))} {FObj T x ∧ y} o 
                           ( ε {(FObj T (FObj T (x ∧ y)) <= (FObj T x ∧ y)) ∧ (FObj T x ∧ y) } {x ∧ y}  ))
           cc13 : Hom A (FObj (Monad.T m) x ∧ FObj (Monad.T m) y) ((((FObj T (FObj T (x ∧ y)) <= (FObj T x ∧ y)) ∧ (FObj T x ∧ y)) <= (x ∧ y)) ∧ (x ∧ y))
           cc13 =  < ? , ? >  o _* ( ( FMap T ? o π ) o π   )
           -- ? o ( _* ? o _* ? )
           -- ? o < (FMap T ? o π ) , (FMap T ? o π' ) > 
       cc10 :  NTrans (A × A) A (Functor● A A MonoidalCCC (Monad.T m)) (Functor⊗ A A MonoidalCCC (Monad.T m))
       cc10 = record { TMap = λ a → tmap (proj₁ a) (proj₂ a) ; isNTrans = record { commute = ? } }

-- 
-- end
