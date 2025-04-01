{-# OPTIONS --cubical-compatible --safe #-}

open import Level
open import Category
open import Definitions 
open Functor

--
-- To show Applicative functor is monoidal functor, uniquness of Functor is necessary, which is derived from the free theorem.
--
-- they say it is not possible to prove FreeTheorem in Agda nor Coq
--    https://stackoverflow.com/questions/24718567/is-it-possible-to-get-hold-of-free-theorems-as-propositional-equalities
-- so we postulate this

module applicative  (
    FT : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (C : Category c₁ c₂ ℓ) (D : Category c₁' c₂' ℓ') {a b c : Obj C } → FreeTheorem C D  {a} {b} {c} )
       where

open import Data.Product renaming (_×_ to _*_) hiding (_<*>_)
open import Category.Constructions.Product
open import HomReasoning
open import Relation.Binary.Core
open import Relation.Binary
open import monoidal
open import Relation.Binary.PropositionalEquality  hiding ( [_] )

-----
--
--  Applicative Functor
--
--    is a monoidal functor on Sets and it can be constructoed from Haskell monoidal functor and vais versa
--
----

-----
UniquenessOfFunctor :  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (C : Category c₁ c₂ ℓ) (D : Category c₁' c₂' ℓ')  (F : Functor C D)
  {a b : Obj C } { f : Hom C a b } → ( fmap : {a : Obj C } {b : Obj C } → Hom C a b → Hom D (FObj F a) ( FObj F b) )
      → ( {b : Obj C } → D [ fmap  (id1 C b) ≈  id1 D (FObj F b) ] )
      → D [ fmap f ≈  FMap F f ]
UniquenessOfFunctor C D F {a} {b} {f} fmap eq = begin
        fmap f 
     ≈↑⟨ idL ⟩
        id1 D (FObj F b)  o  fmap f 
     ≈↑⟨ car ( IsFunctor.identity (isFunctor F )) ⟩
        FMap F (id1 C b)  o  fmap f 
     ≈⟨ FT C D F  fmap (IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory C ))) ⟩ 
        fmap  (id1 C b)  o  FMap F f  
     ≈⟨ car eq ⟩
        id1 D (FObj F b)  o  FMap F f  
     ≈⟨ idL ⟩
        FMap F f 
     ∎  
   where open ≈-Reasoning D 

open import Category.Sets
import Relation.Binary.PropositionalEquality

_・_ : {c₁ : Level} { a b c : Obj (Sets {c₁} ) } → (b → c) → (a → b) → a → c
_・_ f g = λ x → f ( g x ) 
record IsApplicative {c₁ : Level} ( F : Functor (Sets {c₁}) (Sets {c₁}) )
    ( pure  : {a : Obj Sets} → Hom Sets a ( FObj F a ) )
    ( _<*>_ : {a b : Obj Sets} → FObj F ( a → b ) → FObj F a → FObj F b )
        : Set (suc (suc c₁)) where
  field
          identity : { a : Obj Sets } { u : FObj F a } → pure ( id1 Sets a )  <*> u ≡ u
          composition : { a b c : Obj Sets } { u : FObj F ( b → c ) } { v : FObj F (a → b ) } { w : FObj F a }
              → (( pure _・_ <*> u ) <*> v ) <*> w  ≡ u  <*> (v  <*> w)
          homomorphism : { a b : Obj Sets } { f : Hom Sets a b } { x : a }  → pure f <*> pure x ≡ pure (f x)
          interchange : { a b : Obj Sets } { u : FObj F ( a → b ) } { x : a } → u <*> pure x ≡ pure (λ f → f x) <*> u
          --  from  http://www.staff.city.ac.uk/~ross/papers/Applicative.pdf

record Applicative {c₁ : Level} ( F : Functor (Sets {c₁}) (Sets {c₁}) )
        : Set (suc (suc c₁)) where
  field
      pure  : {a : Obj Sets} → Hom Sets a ( FObj F a )
      <*>   : {a b : Obj Sets} → FObj F ( a → b ) → FObj F a → FObj F b
      isApplicative : IsApplicative F pure <*>

------
--
-- Appllicative Functor is a Monoidal Functor
--

Applicative→Monoidal :  {c : Level} ( F : Functor (Sets {c}) (Sets {c}) ) → (mf : Applicative F )
   → IsApplicative F ( Applicative.pure mf ) ( Applicative.<*> mf ) 
   → MonoidalFunctor {_} {c} {_} {Sets} {Sets} MonoidalSets MonoidalSets
Applicative→Monoidal {l} F mf ismf = record {
      MF = F
    ; ψ  = λ x → unit
    ; isMonodailFunctor = record {
             φab  = record { TMap = λ x → φ ; isNTrans = record { commute = φab-comm } }
         ;   associativity  = λ {a b c} → associativity {a} {b} {c}
         ;   unitarity-idr = λ {a b} → unitarity-idr {a} {b}
         ;   unitarity-idl = λ {a b} → unitarity-idl {a} {b}
      }
  } where
      open Monoidal 
      open IsMonoidal hiding ( _■_ ;  _□_ )
      M = MonoidalSets
      isM = Monoidal.isMonoidal MonoidalSets 
      unit = Applicative.pure mf OneObj
      _⊗_ : (x y : Obj Sets ) → Obj Sets
      _⊗_ x y =  (IsMonoidal._□_ (Monoidal.isMonoidal M) ) x y
      _□_ : {a b c d : Obj Sets } ( f : Hom Sets a c ) ( g : Hom Sets b d ) → Hom Sets ( a ⊗ b ) ( c ⊗ d )
      _□_ f g = FMap (m-bi M) ( f , g )
      φ : {x : Obj (Sets × Sets) } → Hom Sets (FObj (Functor● Sets Sets MonoidalSets F) x) (FObj (Functor⊗ Sets Sets MonoidalSets F) x)
      φ x = Applicative.<*> mf  (FMap F (λ j k → (j , k))  (proj₁ x )) (proj₂ x)
      _<*>_ :   {a b : Obj Sets} → FObj F ( a → b ) → FObj F a → FObj F b  
      _<*>_  = Applicative.<*> mf  
      left  :   {a b : Obj Sets} → {x y : FObj F ( a → b )} → {h : FObj F a  } → ( x ≡ y ) → x <*> h ≡ y <*> h
      left {_} {_} {_} {_} {h} eq = ≡-cong ( λ k → k <*> h ) eq 
      right  :   {a b : Obj Sets} → {h : FObj F ( a → b )} → {x y : FObj F a  } → ( x ≡ y ) → h <*> x ≡ h <*> y
      right {_} {_} {h} {_} {_} eq = ≡-cong ( λ k → h <*> k ) eq 
      id : { a : Obj Sets } → a → a 
      id x = x
      pure : {a : Obj Sets } → Hom Sets a ( FObj F a )
      pure a = Applicative.pure mf a
      -- special case
      F→pureid : {a b : Obj Sets } → (x : FObj F a ) →  FMap F id x ≡ pure id <*> x
      F→pureid {a} {b} x = sym ( begin
                 pure id <*> x
             ≡⟨ IsApplicative.identity ismf  ⟩
                 x
             ≡⟨ sym ( IsFunctor.identity (isFunctor F ) x ) ⟩ 
                 FMap F id x
             ∎ )
           where
                  open Relation.Binary.PropositionalEquality
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
      F→pure : {a b : Obj Sets } → { f : a → b } → {x : FObj F a } →  FMap F f x ≡ pure f <*> x
      F→pure {a} {b} {f} {x} = sym ( begin
                 pure f <*> x
             ≡⟨ (UniquenessOfFunctor Sets Sets F ( λ f x → pure f <*> x ) (λ x →  IsApplicative.identity ismf  )) x ⟩
                 FMap F f x
             ∎ )
           where
                  open Relation.Binary.PropositionalEquality
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
      p*p : { a b : Obj Sets } { f : Hom Sets a b } { x : a }  → pure f <*> pure x ≡ pure (f x)
      p*p =  IsApplicative.homomorphism ismf
      comp = IsApplicative.composition ismf
      inter = IsApplicative.interchange ismf
      pureAssoc :  {a b c : Obj Sets } ( f : b → c ) ( g : a → b ) ( h : FObj F a ) → pure f <*> ( pure g <*> h ) ≡ pure ( f ・ g ) <*> h
      pureAssoc f g h = trans ( trans (sym comp) (left (left p*p) )) ( left p*p  )
           where
                  open Relation.Binary.PropositionalEquality
      φab-comm0 : {a b :  Obj (Sets × Sets)} { f : Hom (Sets × Sets) a b}  (x : ( FObj F (proj₁ a) * FObj F (proj₂ a)) ) →
         (Sets [ FMap (Functor⊗ Sets Sets MonoidalSets F) f o φ ]) x ≡ (Sets [ φ o FMap (Functor● Sets Sets MonoidalSets F) f ]) x
      φab-comm0 {a} {b} {(f , g)} (x , y) = begin
                 ( FMap (Functor⊗ Sets Sets MonoidalSets F) (f , g) ) ( φ (x , y) )
             ≡⟨⟩
                 FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) ((FMap F (λ j k → j , k) x) <*> y)
             ≡⟨⟩
                 FMap F (map f g) ((FMap F (λ j k → j , k) x) <*> y)
             ≡⟨ F→pure  ⟩
                 (pure (map f g) <*> (FMap F (λ j k → j , k) x <*> y))
             ≡⟨ right ( left F→pure )  ⟩
                 (pure (map f g)) <*> ((pure (λ j k → j , k) <*> x) <*> y)
             ≡⟨ sym ( IsApplicative.composition ismf )  ⟩
                 (( pure _・_ <*> (pure (map f g))) <*> (pure (λ j k → j , k) <*> x)) <*> y
             ≡⟨ left ( sym ( IsApplicative.composition ismf ))  ⟩
                 ((( pure _・_ <*> (( pure _・_ <*> (pure (map f g))))) <*> pure (λ j k → j , k)) <*> x) <*> y
             ≡⟨ trans ( trans (left ( left (left (right  p*p )))) ( left ( left ( left p*p)))) (left (left p*p)) ⟩
                 (pure (( _・_ (( _・_ ((map f g))))) (λ j k → j , k)) <*> x) <*> y
             ≡⟨⟩
                (pure (λ j k → f j , g k) <*> x) <*> y
             ≡⟨⟩
                 ( pure ((_・_ (( _・_ ( ( λ h → h g ))) ( _・_ ))) ((λ j k → f j , k))) <*> x ) <*> y 
             ≡⟨ sym ( trans (left (left (left p*p))) (left ( left p*p)) ) ⟩
                ((((pure _・_ <*> pure ((λ h → h g) ・ _・_)) <*> pure (λ j k → f j , k)) <*> x) <*> y)
             ≡⟨ sym (trans ( left ( left ( left (right (left p*p) )))) (left ( left  (left (right p*p ))))) ⟩
                 (((pure  _・_ <*> (( pure  _・_ <*> ( pure ( λ h → h g ))) <*> ( pure _・_ ))) <*> (pure (λ j k → f j , k))) <*> x ) <*> y 
             ≡⟨ left ( ( IsApplicative.composition ismf ))  ⟩
                 ((( pure  _・_ <*> ( pure ( λ h → h g ))) <*> ( pure _・_ )) <*> (pure (λ j k → f j , k) <*> x )) <*> y 
             ≡⟨  left (IsApplicative.composition ismf )  ⟩
                 ( pure ( λ h → h g ) <*> ( pure _・_ <*> (pure (λ j k → f j , k) <*> x )) ) <*> y 
             ≡⟨ left (sym (IsApplicative.interchange ismf )) ⟩
                 (( pure _・_ <*> (pure (λ j k → f j , k) <*> x )) <*>  pure g) <*> y 
             ≡⟨  IsApplicative.composition ismf ⟩
                 (pure (λ j k → f j , k) <*> x) <*> (pure g <*> y)
             ≡⟨ sym ( trans (left F→pure ) ( right F→pure ) ) ⟩
                 (FMap F (λ j k → f j , k)  x) <*> (FMap F g y)
             ≡⟨    ≡-cong ( λ k → k   <*> (FMap F g y)) ( IsFunctor.distr (isFunctor F ) x ) ⟩
                 (FMap F (λ j k → j , k) (FMap F f x)) <*> (FMap F g y)
             ≡⟨⟩
                 φ ( ( FMap (Functor● Sets Sets MonoidalSets F) (f , g) ) ( x , y ) )
             ∎ 
           where
                  open Relation.Binary.PropositionalEquality
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
      φab-comm : {a b : Obj (Sets × Sets)} { f : Hom (Sets × Sets) a b} → Sets [ Sets [ FMap (Functor⊗ Sets Sets MonoidalSets F) f o φ  ]
        ≈ Sets [ φ  o FMap (Functor● Sets Sets MonoidalSets F) f ] ]
      φab-comm {a} {b} {f} =   λ (x : ( FObj F (proj₁ a) * FObj F (proj₂ a)) ) → φab-comm0 x 
      associativity0 :  {a b c : Obj Sets} → (x : ((FObj F a ⊗ FObj F b) ⊗ FObj F c) ) → (Sets [ φ  o Sets [ id1 Sets (FObj F a) □ φ  o Iso.≅→ (mα-iso isM) ] ]) x ≡
                (Sets [ FMap F (Iso.≅→ (mα-iso isM)) o Sets [ φ  o φ  □ id1 Sets (FObj F c) ] ]) x
      associativity0 {x} {y} {f} ((a , b) , c ) = begin
                  φ  (( id □ φ  ) ( ( Iso.≅→ (mα-iso isM) ) ((a , b) , c)))
               ≡⟨⟩
                 (FMap F (λ j k → j , k) a) <*> ( (FMap F (λ j k → j , k) b) <*> c)
               ≡⟨ trans (left  F→pure) (right (left F→pure) )  ⟩
                 (pure (λ j k → j , k) <*> a) <*> ( (pure (λ j k → j , k) <*> b) <*> c)
               ≡⟨ sym comp ⟩
                  ( ( pure _・_ <*> (pure (λ j k → j , k) <*> a)) <*>  (pure (λ j k → j , k) <*> b)) <*> c
               ≡⟨ sym ( left comp ) ⟩
                  (( (  pure _・_ <*> ( pure _・_ <*> (pure (λ j k → j , k) <*> a))) <*>  (pure (λ j k → j , k))) <*> b) <*> c
               ≡⟨ sym ( left ( left ( left (right comp )))) ⟩
                  (( (  pure _・_ <*> (( (pure _・_ <*> pure _・_ ) <*> (pure (λ j k → j , k))) <*> a)) <*>  (pure (λ j k → j , k))) <*> b) <*> c
               ≡⟨ trans (left ( left (left ( right (left ( left p*p )))))) (left ( left ( left (right (left p*p))))) ⟩
                  (( (  pure _・_ <*> ((pure ((_・_ ( _・_ )) ((λ j k → j , k)))) <*> a)) <*>  (pure (λ j k → j , k))) <*> b) <*> c
               ≡⟨ sym (left ( left ( left comp ) )) ⟩
                  (((( ( pure _・_  <*> (pure _・_ )) <*> (pure ((_・_ ( _・_ )) ((λ j k → j , k))))) <*> a) <*>  (pure (λ j k → j , k))) <*> b) <*> c
               ≡⟨  trans (left ( left ( left (left (left p*p))))) (left ( left ( left (left p*p ))))  ⟩
                  ((((pure ( ( _・_  (_・_ )) (((_・_ ( _・_ )) ((λ j k → j , k)))))) <*> a) <*>  (pure (λ j k → j , k))) <*> b) <*> c
               ≡⟨⟩
                  ((((pure (λ f g x y → f , g x y)) <*> a) <*> (pure (λ j k → j , k))) <*> b) <*> c
               ≡⟨ left ( left inter )  ⟩
                  (((pure (λ f → f (λ j k → j , k))) <*> ((pure (λ f g x y → f , g x y)) <*> a) ) <*> b) <*> c
               ≡⟨ sym ( left ( left comp )) ⟩
                  ((((   pure _・_   <*>  (pure (λ f → f (λ j k → j , k)))) <*> (pure (λ f g x y → f , g x y))) <*> a ) <*> b) <*> c
               ≡⟨ trans (left ( left (left (left p*p) ))) (left (left (left p*p ) )) ⟩
                   (((pure (λ f g h → f , g , h)) <*> a) <*> b) <*> c
               ≡⟨ sym (trans ( left ( left ( left (left (right (right p*p))) ) )) (trans (left (left( left (left (right p*p)))))
                       (trans (left (left (left (left p*p)))) (trans ( left (left (left (right (left (right p*p ))))))
                       (trans (left (left (left (right (left p*p))))) (trans (left (left (left (right p*p)))) (left (left (left p*p)))) ) ) )
                        ) ) ⟩
                    ((((pure _・_   <*> ((pure _・_   <*> ((pure _・_   <*> ( pure (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc))))))) <*>
                          (( pure _・_  <*> ( pure _・_  <*>  (pure (λ j k → j , k)))) <*> pure (λ j k → j , k))) <*> a) <*> b) <*> c
               ≡⟨ left (left comp )  ⟩
                    (((pure _・_   <*> ((pure _・_   <*> ( pure (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc))))) <*>
                          ((( pure _・_  <*> ( pure _・_  <*>  (pure (λ j k → j , k)))) <*> pure (λ j k → j , k)) <*> a)) <*> b) <*> c
               ≡⟨ left comp ⟩
                    ((pure _・_   <*> ( pure (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc))) <*>
                          (((( pure _・_  <*> ( pure _・_  <*>  (pure (λ j k → j , k)))) <*> pure (λ j k → j , k)) <*> a) <*> b)) <*> c
               ≡⟨ left ( right (left comp )) ⟩
                    ((pure _・_   <*> ( pure (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc))) <*>
                          ((( pure _・_  <*>  (pure (λ j k → j , k))) <*> (pure (λ j k → j , k) <*> a)) <*> b)) <*> c
               ≡⟨ left ( right comp ) ⟩
                    ((pure _・_   <*> ( pure (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc))) <*>
                            (pure (λ j k → j , k) <*> ( (pure (λ j k → j , k) <*> a) <*> b))) <*> c
               ≡⟨ comp ⟩
                  pure (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc) <*> ( (pure (λ j k → j , k) <*> ( (pure (λ j k → j , k) <*> a) <*> b)) <*> c)
               ≡⟨ sym ( trans ( trans F→pure (right (left F→pure ))) ( right ( left (right (left F→pure ))))) ⟩
                  FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc) ( (FMap F (λ j k → j , k) ( (FMap F (λ j k → j , k) a) <*> b)) <*> c)
               ≡⟨⟩
                 ( FMap F (Iso.≅→ (mα-iso isM))) (φ (( φ  □  id1 Sets (FObj F f) ) ((a , b) , c)))
             ∎
           where
                  open Relation.Binary.PropositionalEquality
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
      associativity : {a b c : Obj Sets} → Sets [ Sets [ φ 
           o Sets [  (id1 Sets (FObj F a) □ φ ) o Iso.≅→ (mα-iso isM) ] ]
        ≈ Sets [ FMap F (Iso.≅→ (mα-iso isM)) o Sets [ φ  o  (φ  □ id1 Sets (FObj F c)) ] ] ]
      associativity {a} {b} {c} x =  associativity0 x 
      unitarity-idr0 : {a b : Obj Sets} ( x : FObj F a * One )  → (  Sets [
         FMap F (Iso.≅→ (mρ-iso isM)) o Sets [ φ  o
             FMap (m-bi MonoidalSets) (id1 Sets (FObj F a) , (λ _ → unit )) ] ] ) x  ≡ Iso.≅→ (mρ-iso isM) x
      unitarity-idr0 {a} {b} (x , OneObj ) =  begin 
                 (FMap F (Iso.≅→ (mρ-iso isM))) ( φ ((  FMap (m-bi MonoidalSets) (id1 Sets (FObj F a) , (λ _ → unit))) (x , OneObj) ))
               ≡⟨⟩
                 FMap F proj₁ ((FMap F (λ j k → j , k) x) <*> (pure OneObj))
               ≡⟨ ≡-cong ( λ k → FMap F  proj₁ k) ( IsApplicative.interchange   ismf )  ⟩
                 FMap F proj₁ ((pure (λ f → f OneObj)) <*> (FMap F (λ j k → j , k) x))
               ≡⟨ ( trans  F→pure (right  ( right F→pure )) ) ⟩
                 pure proj₁ <*> ((pure (λ f → f OneObj)) <*> (pure (λ j k → j , k) <*> x))
               ≡⟨ sym ( right comp ) ⟩
                 pure proj₁ <*> (((pure _・_   <*> (pure (λ f → f OneObj))) <*> pure (λ j k → j , k)) <*> x)
               ≡⟨ sym  comp  ⟩
                 ( ( pure _・_   <*>  (pure proj₁ ) ) <*> ((pure _・_   <*> (pure (λ f → f OneObj))) <*> pure (λ j k → j , k))) <*> x
               ≡⟨ trans ( trans ( trans ( left ( left p*p)) ( left ( right (left p*p) ))) (left (right p*p) )  ) (left p*p) ⟩
                 pure ( ( _・_ (proj₁ {l} {l})) ((_・_  ((λ f → f OneObj))) (λ j k → j , k))) <*> x
               ≡⟨⟩
                 pure id <*> x
               ≡⟨ IsApplicative.identity ismf  ⟩
                 x
               ≡⟨⟩
                 Iso.≅→ (mρ-iso isM) (x , OneObj)
             ∎ 
           where
                  open Relation.Binary.PropositionalEquality
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
      unitarity-idr : {a b : Obj Sets} → Sets [ Sets [
         FMap F (Iso.≅→ (mρ-iso isM)) o Sets [ φ  o
             FMap (m-bi MonoidalSets) (id1 Sets (FObj F a) , (λ _ → unit )) ] ] ≈ Iso.≅→ (mρ-iso isM) ]
      unitarity-idr {a} {b} x =  unitarity-idr0 {a} {b} x 
      unitarity-idl0 : {a b : Obj Sets} ( x : One * FObj F b )  → (  Sets [
         FMap F (Iso.≅→ (mλ-iso isM)) o Sets [ φ  o
             FMap (m-bi MonoidalSets) ((λ _ → unit ) , id1 Sets (FObj F b) ) ] ] ) x  ≡ Iso.≅→ (mλ-iso isM) x
      unitarity-idl0 {a} {b} ( OneObj , x) =  begin 
                 (FMap F (Iso.≅→ (mλ-iso isM))) ( φ  ( unit , x ) )
               ≡⟨⟩
                  FMap F proj₂ ((FMap F (λ j k → j , k) (pure OneObj)) <*> x)
               ≡⟨ ( trans  F→pure (right  ( left F→pure )) ) ⟩
                  pure proj₂ <*> ((pure (λ j k → j , k) <*> (pure OneObj)) <*> x)
               ≡⟨ sym comp ⟩
                  ((pure  _・_  <*>  (pure proj₂)) <*> (pure (λ j k → j , k) <*> (pure OneObj))) <*> x
               ≡⟨ trans (trans (left (left p*p )) (left ( right p*p)) ) (left p*p)  ⟩
                  pure ((_・_  (proj₂ {l}) )((λ (j : One {l})  (k : b ) → j , k) OneObj)) <*> x
               ≡⟨⟩
                 pure id <*> x
               ≡⟨ IsApplicative.identity ismf  ⟩
                 x
               ≡⟨⟩
                 Iso.≅→ (mλ-iso isM) (  OneObj , x )
             ∎ 
           where
                  open Relation.Binary.PropositionalEquality
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
      unitarity-idl : {a b : Obj Sets} → Sets [ Sets [ FMap F (Iso.≅→ (mλ-iso isM)) o
        Sets [ φ  o FMap (m-bi MonoidalSets) ((λ _ → unit ) , id1 Sets (FObj F b)) ] ] ≈ Iso.≅→ (mλ-iso isM) ]
      unitarity-idl {a} {b} x =  unitarity-idl0 {a} {b} x 

----
--
-- Monoidal laws implies Applicative laws
--

HaskellMonoidal→Applicative : {c₁ : Level} ( F : Functor (Sets {c₁}) (Sets {c₁}) )
      ( Mono : HaskellMonoidalFunctor F ) 
         → Applicative F  
HaskellMonoidal→Applicative {c₁} F Mono = record {
        pure = pure ;
        <*> = _<*>_ ;
        isApplicative = record {
          identity = identity 
        ; composition = composition
        ; homomorphism = homomorphism
        ; interchange = interchange
        }
     }
     where 
          unit  : FObj F One 
          unit = HaskellMonoidalFunctor.unit Mono
          φ    : {a b : Obj Sets} → Hom Sets ((FObj F a) *  (FObj F b )) ( FObj F ( a * b ) ) 
          φ = HaskellMonoidalFunctor.φ Mono
          mono : IsHaskellMonoidalFunctor F unit φ 
          mono = HaskellMonoidalFunctor.isHaskellMonoidalFunctor Mono
          id : { a : Obj Sets } → a → a 
          id x = x
          isM  : IsMonoidal (Sets {c₁}) One SetsTensorProduct  
          isM = Monoidal.isMonoidal MonoidalSets 
          pure  :  {a : Obj Sets} → Hom Sets a ( FObj F a )
          pure {a} x = FMap F ( λ y → x ) (unit )
          _<*>_ :   {a b : Obj Sets} → FObj F ( a → b ) → FObj F a → FObj F b        
          _<*>_ {a} {b} x y = FMap F ( λ r →  ( proj₁ r )  ( proj₂  r ) )  (φ ( x , y ))
          -- right does not work right it makes yellows. why?
          -- right : {n : Level} { a b : Set n} → { x y : a } { h : a → b }  → ( x ≡ y ) → h x ≡ h y
          -- right {_} {_} {_} {_} {_} {h} eq = ≡-cong ( λ k → h k ) eq 
          left : {n : Level} { a b : Set n} → { x y : a → b } { h : a }  → ( x ≡ y ) → x h ≡ y h
          left {_} {_} {_} {_} {_} {h} eq = ≡-cong ( λ k → k h ) eq 
          open Relation.Binary.PropositionalEquality
          FφF→F : { a b c d e : Obj Sets } { g : Hom Sets a c } { h : Hom Sets b d }
              { f : Hom Sets (c * d) e }
                   { x :  FObj F a } { y :  FObj F b }
              →  FMap F f ( φ ( FMap F g x , FMap F h y ) )  ≡  FMap F ( Sets [ f o map g h ] ) ( φ ( x , y ) ) 
          FφF→F {a} {b} {c} {d} {e} {g} {h} {f} {x} {y} = sym ( begin
                  FMap F ( Sets [ f o map g h ] ) ( φ ( x , y ) ) 
               ≡⟨   IsFunctor.distr (isFunctor F) ( φ ( x , y )) ⟩
                  FMap F  f (( FMap F ( map g h ) ) ( φ ( x , y )))
               ≡⟨  ≡-cong ( λ k → FMap F f k ) ( IsHaskellMonoidalFunctor.natφ mono )  ⟩
                  FMap F f ( φ ( FMap F g x , FMap F h y ) )
             ∎  )
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
          u→F : {a : Obj Sets } {u : FObj F a} → u ≡ FMap F id u 
          u→F {a} {u} =  sym (  IsFunctor.identity ( isFunctor F ) u) 
          φunitr : {a : Obj Sets } {u : FObj F a} → φ ( unit , u) ≡ FMap F (Iso.≅← (IsMonoidal.mλ-iso isM)) u
          φunitr {a} {u} = sym ( begin 
                  FMap F (Iso.≅← (IsMonoidal.mλ-iso isM)) u
               ≡⟨  ≡-cong ( λ k → FMap F (Iso.≅← (IsMonoidal.mλ-iso isM)) k ) (sym (IsHaskellMonoidalFunctor.idlφ mono)) ⟩
                  FMap F (Iso.≅← (IsMonoidal.mλ-iso isM)) ( FMap F (Iso.≅→ (IsMonoidal.mλ-iso isM)) ( φ ( unit , u) ) )
               ≡⟨  sym ( IsFunctor.distr ( isFunctor F ) _ ) ⟩
                  (FMap F ( Sets [  (Iso.≅← (IsMonoidal.mλ-iso isM)) o   (Iso.≅→ (IsMonoidal.mλ-iso isM)) ] )) ( φ ( unit , u) )
               ≡⟨ IsFunctor.≈-cong ( isFunctor F ) (Iso.iso→ (IsMonoidal.mλ-iso isM)) _ ⟩
                  FMap F id ( φ ( unit , u) )
               ≡⟨ IsFunctor.identity ( isFunctor F ) _   ⟩
                  id ( φ ( unit , u) )
               ≡⟨⟩
                  φ ( unit , u)
             ∎  )
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
          φunitl : {a : Obj Sets } {u : FObj F a} → φ ( u , unit ) ≡ FMap F (Iso.≅← (IsMonoidal.mρ-iso isM)) u
          φunitl {a} {u} = sym ( begin 
                  FMap F (Iso.≅← (IsMonoidal.mρ-iso isM)) u
               ≡⟨  ≡-cong ( λ k → FMap F (Iso.≅← (IsMonoidal.mρ-iso isM)) k ) (sym (IsHaskellMonoidalFunctor.idrφ mono)) ⟩
                  FMap F (Iso.≅← (IsMonoidal.mρ-iso isM)) ( FMap F (Iso.≅→ (IsMonoidal.mρ-iso isM)) ( φ ( u , unit ) ) )
               ≡⟨  sym ( IsFunctor.distr ( isFunctor F ) _ ) ⟩
                  (FMap F (Sets [ (Iso.≅← (IsMonoidal.mρ-iso isM)) o   (Iso.≅→ (IsMonoidal.mρ-iso isM)) ] )) ( φ ( u , unit ) )
               ≡⟨ IsFunctor.≈-cong ( isFunctor F ) (Iso.iso→ (IsMonoidal.mρ-iso isM)) _ ⟩
                  FMap F id ( φ ( u , unit ) )
               ≡⟨  IsFunctor.identity ( isFunctor F ) _  ⟩
                  id ( φ ( u , unit ) )
               ≡⟨⟩
                  φ ( u , unit )
             ∎  )
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
          open IsMonoidal
          identity : { a : Obj Sets } { u : FObj F a } → pure ( id1 Sets a )  <*> u ≡ u
          identity {a} {u} = begin 
                 pure id <*> u
               ≡⟨⟩
                 ( FMap F ( λ r →  ( proj₁ r )  ( proj₂  r )) ) ( φ (  FMap F ( λ y → id ) unit  , u ) )
               ≡⟨   ≡-cong ( λ k → ( FMap F ( λ r →  ( proj₁ r )  ( proj₂  r )) ) ( φ ( FMap F ( λ y → id ) unit  ,  k  ))) u→F  ⟩
                 ( FMap F ( λ r →  ( proj₁ r )  ( proj₂  r )) ) ( φ (  FMap F ( λ y → id ) unit  , FMap F id u ) )
               ≡⟨ FφF→F ⟩
                   FMap F (λ x → proj₂ x ) (φ (unit , u ) )
               ≡⟨⟩
                   FMap F (Iso.≅→ (mλ-iso isM)) (φ (unit , u ))
               ≡⟨  IsHaskellMonoidalFunctor.idlφ mono   ⟩
                  u
             ∎ 
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
          composition : { a b c : Obj Sets } { u : FObj F ( b → c ) } { v : FObj F (a → b ) } { w : FObj F a }
              → (( pure _・_ <*> u ) <*> v ) <*> w  ≡ u  <*> (v  <*> w)
          composition {a} {b} {c} {u} {v} {w} = begin
                 FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ
                   (FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ y f g x → f (g x)) unit , u)) , v)) , w))
                ≡⟨  ≡-cong ( λ k → FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ y f g x → f (g x)) unit , k)) , v)) , w))  ) u→F  ⟩
                 FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ
                   (FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ y f g x → f (g x)) unit , FMap F id u )) , v)) , w))
                ≡⟨  ≡-cong ( λ k →  FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ ( k  , v)) , w))  ) FφF→F ⟩
                 FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ
                   (FMap F ( λ x → (λ (r : ((b → c) → _ ) * (b → c) ) → proj₁ r (proj₂ r)) ((map (λ y f g x → f (g x)) id ) x)) (φ ( unit , u)) , v)) , w))
                ≡⟨  ≡-cong ( λ k → ( FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ
                   (FMap F ( λ x → (λ (r : ((b → c) → _ ) * (b → c) ) → proj₁ r (proj₂ r)) ((map (λ y f g x → f (g x)) id ) x)) k , v)) , w))  ) ) φunitr ⟩
                 FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ
                   ( (FMap F ( λ x → (λ (r : ((b → c) → _ ) * (b → c) ) → proj₁ r (proj₂ r)) ((map (λ y f g x → f (g x)) id ) x)) (FMap F (Iso.≅← (mλ-iso isM)) u) ) , v)) , w))
                ≡⟨  ≡-cong ( λ k → FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ
                   (k  , v)) , w)) )  (sym ( IsFunctor.distr (isFunctor F ) _ ))  ⟩
                 FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ
                   ( FMap F (λ x → ((λ y f g x₁ → f (g x₁)) unit x) ) u , v)) , w))
                ≡⟨⟩
                 FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ
                   ( FMap F (λ x g h → x (g h) ) u , v)) , w))
                ≡⟨  ≡-cong ( λ k → FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ ( FMap F (λ x g h → x (g h) ) u , k)) , w))   ) u→F  ⟩
                     FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ x g h → x (g h)) u , FMap F id v)) , w))
                ≡⟨  ≡-cong ( λ k → FMap F (λ r → proj₁ r (proj₂ r)) (φ (k , w))  )  FφF→F  ⟩
                     FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (Sets [ (λ r → proj₁ r (proj₂ r)) o map (λ x g h → x (g h)) id ]) (φ (u , v)) , w))
                ≡⟨⟩
                     FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ x h → proj₁ x (proj₂ x h)) (φ (u , v)) , w))
                ≡⟨  ≡-cong ( λ k →  FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ x h → proj₁ x (proj₂ x h)) (φ (u , v)) , k))  ) u→F  ⟩
                     FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ x h → proj₁ x (proj₂ x h)) (φ (u , v)) , FMap F id w))
                ≡⟨  FφF→F  ⟩
                     FMap F (Sets [ (λ r → proj₁ r (proj₂ r)) o map (λ x h → proj₁ x (proj₂ x h)) id ] ) (φ (φ (u , v) , w))
                ≡⟨⟩
                    FMap F (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) (φ (φ (u , v) , w))
                ≡⟨  ≡-cong ( λ k → FMap F (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) k) (sym (IsFunctor.identity (isFunctor F ) _)) ⟩
                    FMap F (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) (FMap F id (φ (φ (u , v) , w)) )
                ≡⟨  ≡-cong ( λ k → FMap F (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) k ) (sym (IsFunctor.≈-cong (isFunctor F) (Iso.iso→  (mα-iso isM)) _)) ⟩
                    FMap F (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) (FMap F (Sets [ (Iso.≅← (mα-iso isM)) o  (Iso.≅→ (mα-iso isM)) ] ) (φ (φ (u , v) , w)) )
                ≡⟨  ≡-cong ( λ k →  FMap F (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) k) ( IsFunctor.distr (isFunctor F ) _ )  ⟩
                    FMap F (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) (FMap F  (Iso.≅← (mα-iso isM)) ( FMap F  (Iso.≅→ (mα-iso isM)) (φ (φ (u , v) , w)) ))
                ≡⟨ ≡-cong ( λ k →   FMap F (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) (FMap F  (Iso.≅← (mα-iso isM)) k) ) (sym ( IsHaskellMonoidalFunctor.assocφ mono ) ) ⟩
                     FMap F (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) (FMap F (Iso.≅← (mα-iso isM)) (φ (u , φ (v , w))))
                ≡⟨⟩
                     FMap F (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) (FMap F (λ r → (proj₁ r , proj₁ (proj₂ r)) , proj₂ (proj₂ r)) (φ (u , φ (v , w))))
                ≡⟨ (sym ( IsFunctor.distr (isFunctor F ) _ )) ⟩
                      FMap F (λ y → (λ x → proj₁ (proj₁ x) (proj₂ (proj₁ x) (proj₂ x))) ((λ r → (proj₁ r , proj₁ (proj₂ r)) , proj₂ (proj₂ r)) y )) (φ (u , φ (v , w)))
                ≡⟨⟩
                     FMap F (λ y → proj₁ y (proj₁ (proj₂ y) (proj₂ (proj₂ y)))) (φ (u , φ (v , w)))
                ≡⟨⟩
                 FMap F ( λ x → (proj₁ x) ((λ r → proj₁ r (proj₂ r)) (  proj₂ x)))  ( φ ( u , (φ (v , w))))
                ≡⟨ sym FφF→F ⟩
                 FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F id u , FMap F (λ r → proj₁ r (proj₂ r)) (φ (v , w))))
                ≡⟨   ≡-cong ( λ k → FMap F (λ r → proj₁ r (proj₂ r)) (φ (k , FMap F (λ r → proj₁ r (proj₂ r)) (φ (v , w)))) ) (sym u→F ) ⟩
                 FMap F (λ r → proj₁ r (proj₂ r)) (φ (u , FMap F (λ r → proj₁ r (proj₂ r)) (φ (v , w))))
              ∎ 
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
          homomorphism : { a b : Obj Sets } { f : Hom Sets a b } { x : a }  → pure f <*> pure x ≡ pure (f x)
          homomorphism {a} {b} {f} {x} = begin
                  pure f <*> pure x
                ≡⟨⟩
                        FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ y → f) unit , FMap F (λ y → x) unit))
                ≡⟨ FφF→F  ⟩
                        FMap F (Sets [ (λ r → proj₁ r (proj₂ r)) o map (λ y → f) (λ y → x) ] ) (φ (unit , unit))
                ≡⟨⟩
                        FMap F (λ y → f x) (φ (unit , unit))
                ≡⟨ ≡-cong ( λ k →  FMap F (λ y → f x) k ) φunitl ⟩
                        FMap F (λ y → f x) (FMap F (Iso.≅← (mρ-iso isM)) unit)
                ≡⟨⟩
                        FMap F (λ y → f x) (FMap F (λ y → (y , OneObj)) unit)
                ≡⟨ sym (IsFunctor.distr (isFunctor F)  _) ⟩
                        FMap F (λ y → f x) unit
                ≡⟨⟩
                  pure (f x)
              ∎ 
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
          interchange : { a b : Obj Sets } { u : FObj F ( a → b ) } { x : a } → u <*> pure x ≡ pure (λ f → f x) <*> u
          interchange {a} {b} {u} {x} =  begin
                  u <*> pure x 
              ≡⟨⟩
                  FMap F (λ r → proj₁ r (proj₂ r)) (φ (u , FMap F (λ y → x) unit))
              ≡⟨  ≡-cong ( λ k →  FMap F (λ r → proj₁ r (proj₂ r)) (φ (k , FMap F (λ y → x) unit))  ) u→F  ⟩
                  FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F id u , FMap F (λ y → x) unit))
              ≡⟨  FφF→F  ⟩
                   FMap F (Sets [ (λ r → proj₁ r (proj₂ r)) o map id (λ y → x) ] ) (φ (u , unit))
              ≡⟨⟩
                  FMap F (λ r → proj₁ r x) (φ (u , unit))
              ≡⟨  ≡-cong ( λ k →  FMap F (λ r → proj₁ r x) k ) φunitl ⟩
                  FMap F (λ r → proj₁ r x) (( FMap F (Iso.≅← (mρ-iso isM))) u )
              ≡⟨ ( sym ( IsFunctor.distr (isFunctor F ) _) ) ⟩
                  FMap F (Sets [ ( λ r → proj₁ r x)  o ((Iso.≅← (mρ-iso isM) )) ] ) u
              ≡⟨⟩
                  FMap F (Sets [( λ r → proj₂ r x)  o ((Iso.≅← (mλ-iso isM) )) ] ) u
              ≡⟨  IsFunctor.distr (isFunctor F ) _  ⟩
                  FMap F (λ r → proj₂ r x) (FMap F (Iso.≅← (IsMonoidal.mλ-iso isM)) u)
              ≡⟨  ≡-cong ( λ k →  FMap F (λ r → proj₂ r x) k ) (sym φunitr ) ⟩
                  FMap F (λ r → proj₂ r x) (φ (unit , u))
              ≡⟨⟩
                 FMap F (Sets [ (λ r → proj₁ r (proj₂ r)) o map (λ y f → f x) id ] ) (φ (unit , u)) 
              ≡⟨ sym FφF→F ⟩
                  FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ y f → f x) unit , FMap F id u))
              ≡⟨  ≡-cong ( λ k → FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ y f → f x) unit , k)) ) (sym u→F) ⟩
                  FMap F (λ r → proj₁ r (proj₂ r)) (φ (FMap F (λ y f → f x) unit , u))
              ≡⟨⟩
                  pure (λ f → f x) <*> u
              ∎
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning

----
--
-- Applicative functor implements Haskell Monoidal functor  
--    Haskell Monoidal functor is directly represents monoidal functor, it is easy to make it from a monoidal functor
--

Applicative→HaskellMonoidal : {c₁ : Level} ( F : Functor (Sets {c₁}) (Sets {c₁}) )
     ( App : Applicative F  )
       → HaskellMonoidalFunctor F 
Applicative→HaskellMonoidal {l}  F App = record {
      unit = unit ;
      φ = φ ;
      isHaskellMonoidalFunctor = record {
          natφ = natφ 
        ; assocφ =  assocφ  
        ; idrφ = idrφ 
        ; idlφ = idlφ  
      }
   } where
          pure = Applicative.pure App
          <*> = Applicative.<*> App
          app = Applicative.isApplicative App
          unit  :  FObj F One
          unit = pure OneObj
          φ :  {a b : Obj Sets} → Hom Sets ((FObj F a) *  (FObj F b )) ( FObj F ( a * b ) )
          φ = λ x →  <*> (FMap F (λ j k → (j , k)) ( proj₁ x)) ( proj₂ x)
          isM  : IsMonoidal (Sets {l}) One SetsTensorProduct
          isM = Monoidal.isMonoidal MonoidalSets
          MF :  MonoidalFunctor {_} {l} {_} {Sets} {Sets} MonoidalSets MonoidalSets
          MF = Applicative→Monoidal F App  app
          isMF = MonoidalFunctor.isMonodailFunctor MF
          natφ : { a b c d : Obj Sets } { x : FObj F a} { y : FObj F b} { f : a → c } { g : b → d  }
             → FMap F (map f g) (φ (x , y)) ≡ φ (FMap F f x , FMap F g y)
          natφ {a} {b} {c} {d} {x} {y} {f} {g} = begin
                   FMap F (map f g) (φ (x , y))
                ≡⟨⟩
                   FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) (<*> (FMap F (λ j k → j , k) x) y)
                ≡⟨   IsNTrans.commute ( NTrans.isNTrans ( IsMonoidalFunctor.φab isMF  )) _ ⟩
                   <*> (FMap F (λ j k → j , k) (FMap F f x)) (FMap F g y)
                ≡⟨⟩
                   φ (FMap F f x , FMap F g y)
             ∎   
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
          assocφ : { x y z : Obj Sets } { a : FObj F x } { b : FObj F y }{ c : FObj F z }
             → φ (a , φ (b , c)) ≡ FMap F (Iso.≅→ (IsMonoidal.mα-iso isM)) (φ (φ (a , b) , c))
          assocφ {x} {y} {z} {a} {b} {c} =  IsMonoidalFunctor.associativity isMF _
          idrφ : {a : Obj Sets } { x : FObj F a } → FMap F (Iso.≅→ (IsMonoidal.mρ-iso isM)) (φ (x , unit)) ≡ x
          idrφ {a} {x} =   IsMonoidalFunctor.unitarity-idr isMF {a} {One} (x , OneObj) 
          idlφ : {a : Obj Sets } { x : FObj F a } → FMap F (Iso.≅→ (IsMonoidal.mλ-iso isM)) (φ (unit , x)) ≡ x
          idlφ {a} {x} =  IsMonoidalFunctor.unitarity-idl isMF {One} {a} (OneObj , x) 

-- end
