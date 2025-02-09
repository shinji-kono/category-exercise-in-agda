{-# OPTIONS --cubical-compatible --safe #-}

-- -- -- -- -- -- -- -- 
--  Comparison Functor of Kelisli Category
--  defines U_K and F_K as a resolution of Monad
--  checks Adjointness
-- 
--   Shinji KONO <kono@ie.u-ryukyu.ac.jp>
-- -- -- -- -- -- -- -- 

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
--open import Category.HomReasoning                                                                                                               
open import HomReasoning
open import Definitions
open import Category.Cat
open import Relation.Binary.Core

module comparison-functor 
      { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ }
                 { T : Functor A A }
                 { η : NTrans A A identityFunctor T }
                 { μ : NTrans A A (T ○ T) T }
                 { M' : IsMonad A T η μ }
      {c₁' c₂' ℓ' : Level} ( B : Category c₁' c₂' ℓ' ) 
      { U_K : Functor B A } { F_K : Functor A B }
      { η_K : NTrans A A identityFunctor ( U_K ○ F_K ) }
      { ε_K : NTrans B B ( F_K ○ U_K ) identityFunctor } 
      { μ_K' : NTrans A A (( U_K ○ F_K ) ○ ( U_K ○ F_K )) ( U_K ○ F_K ) }
      ( AdjK : IsAdjunction A B U_K F_K η_K ε_K )
   where

open import adj-monad

T_K = U_K ○ F_K

μ_K : NTrans A A (( U_K ○ F_K ) ○ ( U_K ○ F_K )) ( U_K ○ F_K ) 
μ_K  = UεF A B U_K F_K ε_K 

M : IsMonad A (U_K ○ F_K ) η_K μ_K 
M = Monad.isMonad ( Adj2Monad A B ( record { U = U_K; F = F_K ; η = η_K ; ε = ε_K ; isAdjunction =  AdjK } ) )

open import kleisli {c₁} {c₂} {ℓ} {A} { U_K ○ F_K } { η_K } { μ_K } { M } 

T1 =  U_K ○ F_K

open Functor
open NTrans
open Adjunction
open MResolution

kfmap : {a b : Obj A} (f : Hom A a (FObj T1 b) ) → Hom B (FObj F_K a) (FObj F_K b)
kfmap {_} {b} f = B [ TMap ε_K (FObj F_K b) o FMap F_K (f) ]

K_T : Functor KleisliCategory B 
K_T = record {
          FObj = FObj F_K
        ; FMap = kfmap
        ; isFunctor = record
        {      ≈-cong   = ≈-cong
             ; identity = identity
             ; distr    = distr1
        }
     }  where
         identity : {a : Obj A} →  B [ kfmap (K-id {a}) ≈ id1 B (FObj F_K a) ]
         identity {a} = let open ≈-Reasoning (B) in
           begin
               kfmap (K-id {a})
           ≈⟨⟩
               TMap ε_K (FObj F_K a) o FMap F_K ((K-id {a}))
           ≈⟨⟩
              TMap ε_K (FObj F_K a) o FMap F_K (TMap η_K a)
           ≈⟨ IsAdjunction.adjoint2 AdjK ⟩
              id1 B (FObj F_K a)
           ∎
         ≈-cong : {a b : Obj A} → {f g : Hom A a (FObj T1 b)} → A [ f ≈ g ] → B [ kfmap f ≈ kfmap g ]
         ≈-cong {a} {b} {f} {g} f≈g = let open ≈-Reasoning (B) in
           begin
               kfmap f
           ≈⟨⟩
               TMap ε_K (FObj F_K b) o FMap F_K (f)
           ≈⟨ cdr ( fcong F_K f≈g)  ⟩
               TMap ε_K (FObj F_K b) o FMap F_K (g)
           ≈⟨⟩
               kfmap g
           ∎
         distr1 :  {a b c : Obj A} {f : Hom A a (FObj T1 b)} {g : Hom A b (FObj T1 c)} → B [ kfmap (g * f) ≈ (B [ kfmap g o kfmap f ] )]
         distr1 {a} {b} {c} {f} {g} = let open ≈-Reasoning (B) in
           begin
              kfmap (g * f)
           ≈⟨⟩
              TMap ε_K (FObj F_K c) o FMap F_K ((g * f))
           ≈⟨⟩
              TMap ε_K (FObj F_K c) o FMap F_K (A [ TMap μ_K c o A [ FMap ( U_K ○ F_K ) (g)  o f ] ] )
           ≈⟨ cdr ( distr F_K ) ⟩
              TMap ε_K (FObj F_K c) o ( FMap F_K (TMap μ_K c) o ( FMap F_K (A  [ FMap ( U_K ○ F_K ) (g)  o f ])))
           ≈⟨ cdr (cdr ( distr F_K )) ⟩
              TMap ε_K (FObj F_K c) o ( FMap F_K (TMap μ_K c) o (( FMap F_K (FMap ( U_K ○ F_K ) (g))) o (FMap F_K (f))))
           ≈⟨ cdr assoc ⟩
              TMap ε_K (FObj F_K c) o ((( FMap F_K (TMap μ_K c) o ( FMap F_K (FMap (U_K ○ F_K) (g))))) o (FMap F_K (f)))
           ≈⟨⟩
              TMap ε_K (FObj F_K c) o (( FMap F_K ( FMap U_K ( TMap ε_K ( FObj F_K c ) )) o 
                                  ( FMap F_K (FMap (U_K ○ F_K) (g)))) o (FMap F_K (f)))
           ≈⟨ sym (cdr assoc)  ⟩
              TMap ε_K (FObj F_K c) o (( FMap F_K ( FMap U_K ( TMap ε_K ( FObj F_K c ) ))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (g))) o (FMap F_K (f))))
           ≈⟨ assoc ⟩
              (TMap ε_K (FObj F_K c) o ( FMap F_K ( FMap U_K ( TMap ε_K ( FObj F_K c ) )))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (g))) o (FMap F_K (f)))
           ≈⟨ car (sym (nat ε_K)) ⟩
              (TMap ε_K (FObj F_K c) o ( TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c)))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (g))) o (FMap F_K (f)))
           ≈⟨ sym assoc ⟩
              TMap ε_K (FObj F_K c) o (( TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c))) o 
                                  ((( FMap F_K (FMap (U_K ○ F_K) (g)))) o (FMap F_K (f))))
           ≈⟨ cdr assoc ⟩
              TMap ε_K (FObj F_K c) o ((( TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (g))))) o (FMap F_K (f)))
           ≈⟨ cdr ( car (
               begin
                    TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c)) o ((FMap F_K (FMap (U_K ○ F_K) (g))))
                 ≈⟨⟩
                    TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c)) o  (FMap (F_K ○ U_K) (FMap F_K (g))) 
                 ≈⟨ sym (nat ε_K)  ⟩
                    ( FMap F_K (g)) o (TMap ε_K (FObj F_K b))
               ∎
           ))  ⟩
              TMap ε_K (FObj F_K c) o ((( FMap F_K (g)) o (TMap ε_K (FObj F_K b))) o FMap F_K (f))
           ≈⟨ cdr (sym assoc) ⟩
              TMap ε_K (FObj F_K c) o (( FMap F_K (g)) o (TMap ε_K (FObj F_K b) o FMap F_K (f)))
           ≈⟨ assoc ⟩
              (TMap ε_K (FObj F_K c) o FMap F_K (g)) o (TMap ε_K (FObj F_K b) o FMap F_K (f))
           ≈⟨⟩
              kfmap g o kfmap f
           ∎

Lemma-K1 : {a b : Obj A} ( f : Hom A a b ) → B [ FMap K_T ( FMap F_T f)  ≈ FMap F_K f ]
Lemma-K1 {a} {b} f = let open ≈-Reasoning (B) in
           begin
             FMap K_T ( FMap F_T f)  
           ≈⟨⟩
             TMap ε_K (FObj F_K b) o FMap F_K (( FMap F_T f))
           ≈⟨⟩
             TMap ε_K (FObj F_K b) o FMap F_K (A [ TMap η_K b o f ])
           ≈⟨ cdr ( distr F_K) ⟩
             TMap ε_K (FObj F_K b) o (FMap F_K (TMap η_K b)  o FMap F_K f )
           ≈⟨ assoc  ⟩
             (TMap ε_K (FObj F_K b) o FMap F_K (TMap η_K b))  o FMap F_K f 
           ≈⟨ car ( IsAdjunction.adjoint2 AdjK) ⟩
             id1 B (FObj F_K b)  o FMap F_K f 
           ≈⟨ idL  ⟩
             FMap F_K f 
           ∎

Lemma-K2 : {a b : Obj A} ( f : Hom A a (FObj T1 b) ) → A [ FMap U_K ( FMap K_T f)  ≈ FMap U_T f ]
Lemma-K2 {a} {b} f = let open ≈-Reasoning (A) in
           begin
              FMap U_K ( FMap K_T f)
           ≈⟨⟩
              FMap U_K ( B [  TMap ε_K (FObj F_K b) o FMap F_K (f) ] )
           ≈⟨ distr U_K ⟩
              FMap U_K ( TMap ε_K (FObj F_K b)) o FMap U_K (FMap F_K (f) )
           ≈⟨⟩  
              TMap μ_K b o FMap T_K (f) 
           ≈⟨⟩  -- the definition
              FMap U_T f
           ∎

Lemma-K3 : (b : Obj A)  → B [ FMap K_T (TMap η_K b) ≈ id1 B (FObj F_K b) ]
Lemma-K3 b = let open ≈-Reasoning (B) in
           begin
                 FMap K_T  (TMap η_K b)
           ≈⟨⟩  
                 TMap ε_K (FObj F_K b) o FMap F_K (TMap η_K b)
           ≈⟨  IsAdjunction.adjoint2 AdjK ⟩  
                 id1 B (FObj F_K b)
           ∎

Lemma-K4 : (b c : Obj A) (g : Hom A b (FObj T_K c)) → 
     B [ FMap K_T ( A [ (TMap η_K (FObj T_K c)) o g ] )  ≈ FMap F_K g ]
Lemma-K4 b c g = let open ≈-Reasoning (B) in
           begin
                FMap K_T ( A [ (TMap η_K (FObj T_K c)) o g ] ) 
           ≈⟨⟩
                TMap ε_K (FObj F_K (FObj T_K c)) o FMap F_K (A [ (TMap η_K (FObj T_K c)) o g ])
           ≈⟨ cdr (distr F_K) ⟩
                TMap ε_K (FObj F_K (FObj T_K c)) o ( FMap F_K (TMap η_K (FObj T_K c)) o FMap F_K g )
           ≈⟨ assoc ⟩
                (TMap ε_K (FObj F_K (FObj T_K c)) o ( FMap F_K (TMap η_K (FObj T_K c)))) o FMap F_K g 
           ≈⟨ car ( IsAdjunction.adjoint2 AdjK) ⟩  
                 id1 B (FObj F_K (FObj T_K c)) o FMap F_K g 
           ≈⟨ idL ⟩
                FMap F_K g 
           ∎

-- Lemma-K5 : (a : Obj A) → FObj U_K ( FObj K_T a ) = U_T a

Lemma-K6 : (b c : Obj A) (g : Hom A b (FObj T1 c)) → A [ FMap U_K ( FMap K_T g )  ≈ FMap U_T g ]
Lemma-K6 b c g =  let open ≈-Reasoning (A) in
           begin
                 FMap U_K ( FMap K_T g )
           ≈⟨⟩
                 FMap U_K ( B [ TMap ε_K ( FObj F_K c )  o FMap F_K (g) ] )
           ≈⟨ distr U_K ⟩
                 FMap U_K ( TMap ε_K ( FObj F_K c ))  o FMap U_K ( FMap F_K (g) )
           ≈⟨⟩
                 TMap μ_K c o FMap U_K ( FMap F_K (g) )
           ≈⟨⟩
                 FMap U_T g
           ∎


