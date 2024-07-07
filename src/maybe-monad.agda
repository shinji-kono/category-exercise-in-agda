{-# OPTIONS --cubical-compatible --safe #-}

open import Level
open import Category
open import Category.Sets
module maybe-monad  {c : Level} where

open import HomReasoning
open import Definitions
open import Relation.Binary.Core
open import Category.Cat

open import Relation.Binary.PropositionalEquality hiding ([_])
-- Extensionality a b = {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g → ( λ x → f x ≡ λ x → g x )
-- postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Relation.Binary.PropositionalEquality.Extensionality c₂ c₂

data maybe  (A : Set c) :  Set c where
    just :  A → maybe A
    nothing : maybe A

-- Maybe : A → ⊥ + A

A = Sets {c}

Maybe : Functor A A
Maybe = record {
      FObj = λ a → maybe a
    ; FMap = λ {a} {b} f → fmap f
    ; isFunctor = record {
             identity = λ {x} y → identity1 x y 
             ; distr = λ {a} {b} {c} {f} {g} w → distr2 a b c f g w 
             ; ≈-cong = λ {a} {b} {f} {g} f≈g z → ≈-cong1 a b f g z f≈g 
      }
  } where
     fmap : {a b : Obj A} → (f : Hom A a b ) → Hom A (maybe a) (maybe b)
     fmap f nothing = nothing
     fmap f (just x) = just (f x)
     identity1 : (x : Obj A) → (y : maybe x ) → fmap (id1 A x) y ≡ id1 A (maybe x) y
     identity1 x nothing = refl
     identity1 x (just y) = refl
     distr2 : (x y z : Obj A) (f : Hom A x y ) ( g : Hom A y z ) → (w : maybe x) →  fmap (λ w → g (f w)) w  ≡  fmap g ( fmap f w)
     distr2 x y z f g nothing = refl
     distr2 x y z f g (just w) = refl
     ≈-cong1 : (x y : Obj A) ( f g : Hom A x y ) → ( z : maybe x ) → Sets [ f ≈ g ] → fmap f z ≡ fmap g z
     ≈-cong1 x y f g nothing eq = refl
     ≈-cong1 x y f g (just z) eq = cong just ( eq z )

-- Maybe-η : 1 → M

open Functor
open NTrans

Maybe-η : NTrans A A identityFunctor Maybe 
Maybe-η = record {
       TMap = λ a → λ(x : a) →  just x ;
       isNTrans = record {
            commute = λ {a b : Obj A} {f : Hom A a b} → comm a b f 
       }
  } where
     comm1 : (a b : Obj A) (f : Hom A a b) → (x : a) →
       (A [ FMap Maybe f o just ]) x ≡ (A [ just o FMap (identityFunctor {_} {_} {_} {A}) f ]) x
     comm1 a b f x = refl
     comm : (a b : Obj A) (f : Hom A a b) → 
        A [ A [ Functor.FMap Maybe f o (λ x → just x) ] ≈
        A [ (λ x → just x) o FMap (identityFunctor {_} {_} {_} {A} ) f ] ]
     comm a b f x = comm1 a b f x 



-- Maybe-μ : MM → M

Maybe-μ : NTrans  A A ( Maybe ○ Maybe ) Maybe
Maybe-μ = record {
       TMap =  λ a →  tmap a
       ; isNTrans = record {
            commute = comm 
       }
  } where
     tmap : (a : Obj A) → Hom A (FObj (Maybe ○ Maybe) a) (FObj Maybe a )
     tmap a nothing = nothing
     tmap a (just nothing ) = nothing
     tmap a (just (just x) ) = just x
     comm1 : (a b : Obj A) (f : Hom A a b) → ( x : maybe ( maybe a) ) → 
        ( A [ FMap Maybe f o tmap a ] ) x ≡ ( A [ tmap b o FMap (Maybe ○ Maybe) f ]  ) x
     comm1 a b f nothing = refl
     comm1 a b f (just nothing )  = refl
     comm1 a b f (just (just x))  = refl
     comm : {a b : Obj A} {f : Hom A a b} →
        A [ A [ FMap Maybe f o tmap a ] ≈ A [ tmap b o FMap (Maybe ○ Maybe) f ] ]
     comm {a} {b} {f} x = comm1 a b f x 

MaybeMonad : Monad A 
MaybeMonad = record {
       T = Maybe
     ; η = Maybe-η
     ; μ = Maybe-μ
     ; isMonad = record {
           unity1 = unity1
           ; unity2 = unity2
           ; assoc  = assoc
       }  
   } where
      unity1-1  : (a : Obj A ) → (x : maybe a) → (A [ TMap Maybe-μ a o TMap Maybe-η (FObj Maybe a) ]) x ≡ id1 A (FObj Maybe a) x
      unity1-1  a nothing = refl
      unity1-1  a (just x) = refl
      unity2-1  : (a : Obj A ) → (x : maybe a) → (A [ TMap Maybe-μ a o FMap Maybe (TMap Maybe-η a) ]) x ≡ id1 A (FObj Maybe a) x
      unity2-1  a nothing = refl
      unity2-1  a (just x) = refl
      assoc-1 : (a : Obj A ) → (x : maybe (maybe (maybe a))) → (A [ TMap Maybe-μ a o TMap Maybe-μ (FObj Maybe a) ]) x ≡
                        (A [ TMap Maybe-μ a o FMap Maybe (TMap Maybe-μ a) ]) x
      assoc-1 a nothing = refl
      assoc-1 a (just nothing) = refl
      assoc-1 a (just (just nothing )) = refl
      assoc-1 a (just (just (just x) )) = refl
      unity1  : {a : Obj A} →
        A [ A [ TMap Maybe-μ a o TMap Maybe-η (FObj Maybe a) ] ≈ id1 A (FObj Maybe a) ]
      unity1  {a} x = unity1-1 a x 
      unity2 :  {a : Obj A} →
        A [ A [ TMap Maybe-μ a o FMap Maybe (TMap Maybe-η a) ] ≈ id1 A (FObj Maybe a) ]
      unity2  {a} x = unity2-1 a x 
      assoc :  {a : Obj A} → A [ A [ TMap Maybe-μ a o TMap Maybe-μ (FObj Maybe a) ] ≈
        A [ TMap Maybe-μ a o FMap Maybe (TMap Maybe-μ a) ] ]
      assoc  {a} x = assoc-1 a x 



