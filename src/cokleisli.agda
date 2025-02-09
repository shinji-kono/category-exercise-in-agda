{-# OPTIONS --cubical-compatible --safe #-}

open import Category
open import Level
open import HomReasoning 
open import Definitions


module coKleisli { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } { S : Functor A A } (SM : coMonad A S)  where

    open coMonad 

    open Functor
    open NTrans

--
--  Hom in Kleisli Category
--

    S-id :  (a : Obj A) → Hom A (FObj S a) a
    S-id a = TMap (ε SM) a 

    open import Relation.Binary

    _⋍_ : { a : Obj A } { b : Obj A } (f g  : Hom A a b ) → Set ℓ 
    _⋍_ {a} {b} f g = A [ f ≈ g ]

    _*_ : { a b c : Obj A } → ( Hom A (FObj S b) c) → (  Hom A (FObj S a) b) → Hom A (FObj S a) c 
    _*_ {a} {b} {c} g f = coJoin SM {a} {b} {c} (g) (f) 

    isSCat : IsCategory ( Obj A ) (λ a b → Hom A (FObj S a) b)  _⋍_ _*_ (λ {a} → S-id a)
    isSCat  = record  { isEquivalence =  isEquivalence 
                    ; identityL =   SidL
                    ; identityR =   SidR
                    ; o-resp-≈ =    So-resp
                    ; associative = Sassoc
                    }
     where
         open ≈-Reasoning A 
         isEquivalence :  { a b : Obj A } → IsEquivalence {_} {_} {Hom A a b} _⋍_
         isEquivalence {C} {D} = record { refl  = refl-hom ; sym   = sym ; trans = trans-hom } 
         SidL : {a b : Obj A} → {f : Hom A (FObj S a) b} → (S-id _ * f) ⋍ f
         SidL {a} {b} {f} =  begin
             (S-id _ * f)  ≈⟨⟩
             (TMap (ε SM) b o (FMap S (f))) o TMap (δ SM) a ≈↑⟨ car (nat (ε SM)) ⟩
             (f o TMap (ε SM) (FObj S a)) o TMap (δ SM) a ≈↑⟨ assoc ⟩
              f o TMap (ε SM) (FObj S a) o TMap (δ SM) a  ≈⟨ cdr (IsCoMonad.unity1 (isCoMonad SM)) ⟩
              f o id1 A _  ≈⟨ idR ⟩
              f ∎ 
         SidR : {C D : Obj A} → {f : Hom A (FObj S C) D} → (f * S-id _ ) ⋍ f
         SidR {a} {b} {f} =  begin
               (f * S-id a) ≈⟨⟩
               (f o FMap S (TMap (ε SM) a)) o TMap (δ SM) a ≈↑⟨ assoc ⟩
               f o (FMap S (TMap (ε SM) a) o TMap (δ SM) a) ≈⟨ cdr (IsCoMonad.unity2 (isCoMonad SM)) ⟩
               f o id1 A _ ≈⟨ idR ⟩
              f ∎ 
         So-resp :  {a b c : Obj A} → {f g : Hom A (FObj S a) b } → {h i : Hom A  (FObj S b) c } → 
                          f ⋍ g → h ⋍ i → (h * f) ⋍ (i * g)
         So-resp {a} {b} {c} {f} {g} {h} {i} eq-fg eq-hi = resp refl-hom (resp (fcong S eq-fg ) eq-hi )
         Sassoc :   {a b c d : Obj A} → {f : Hom A (FObj S c) d } → {g : Hom A (FObj S b) c } → {h : Hom A (FObj S a) b } →
                          (f * (g * h)) ⋍ ((f * g) * h)
         Sassoc {a} {b} {c} {d} {f} {g} {h} =  begin
                (f * (g * h)) ≈⟨ car (cdr (distr S))  ⟩
                (f o ( FMap S (g o FMap S (h)) o FMap S (TMap (δ SM) a) )) o TMap (δ SM) a ≈⟨ car assoc ⟩
                ((f o  FMap S (g o FMap S (h))) o FMap S (TMap (δ SM) a) ) o TMap (δ SM) a ≈↑⟨ assoc ⟩
                (f o  FMap S (g o FMap S (h))) o (FMap S (TMap (δ SM) a)  o TMap (δ SM) a ) ≈↑⟨ cdr (IsCoMonad.assoc (isCoMonad SM)) ⟩
                  (f o (FMap S (g o FMap S (h)))) o ( TMap (δ SM) (FObj S a) o TMap (δ SM) a ) ≈⟨ assoc ⟩
                  ((f o (FMap S (g o FMap S (h)))) o  TMap (δ SM) (FObj S a) ) o TMap (δ SM) a  ≈⟨ car (car (cdr (distr S))) ⟩
                  ((f o (FMap S (g) o FMap S (FMap S (h)))) o  TMap (δ SM) (FObj S a) ) o TMap (δ SM) a  ≈↑⟨ car assoc ⟩
                  (f o ((FMap S (g) o FMap S (FMap S (h))) o  TMap (δ SM) (FObj S a) )) o TMap (δ SM) a  ≈↑⟨ assoc ⟩
                  f o (((FMap S (g) o FMap S (FMap S (h))) o  TMap (δ SM) (FObj S a) ) o TMap (δ SM) a)  ≈↑⟨ cdr (car assoc ) ⟩
                  f o ((FMap S (g) o (FMap S (FMap S (h)) o  TMap (δ SM) (FObj S a) )) o TMap (δ SM) a)  ≈⟨ cdr (car (cdr (nat (δ SM)))) ⟩
                  f o ((FMap S (g) o ( TMap (δ SM) b o FMap S (h))) o TMap (δ SM) a)  ≈⟨ assoc ⟩
                  (f o (FMap S (g) o ( TMap (δ SM) b o FMap S (h)))) o TMap (δ SM) a  ≈⟨ car (cdr assoc) ⟩
                  (f o ((FMap S (g) o  TMap (δ SM) b ) o FMap S (h))) o TMap (δ SM) a  ≈⟨ car assoc ⟩
                  ((f o (FMap S (g) o  TMap (δ SM) b )) o FMap S (h)) o TMap (δ SM) a  ≈⟨ car (car assoc) ⟩
                  (((f o FMap S (g)) o  TMap (δ SM) b ) o FMap S (h)) o TMap (δ SM) a  ≈⟨⟩
                ((f * g) * h) ∎ 

    SCat : Category c₁ c₂ ℓ
    SCat = record { Obj = Obj A ; Hom = λ a b → Hom A (FObj S a) b ; _o_ = _*_ ; _≈_ = _⋍_ ; Id  = λ {a} → S-id a ; isCategory = isSCat }

