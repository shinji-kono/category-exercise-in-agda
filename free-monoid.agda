-- Free Monoid and it's Universal Mapping 
---- using Sets and forgetful functor

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
module free-monoid { c c₁ c₂ ℓ : Level }   where

open import Category.Sets
open import Category.Cat
open import HomReasoning
open import cat-utility
open import Relation.Binary.Core
open import universal-mapping 
open import  Relation.Binary.PropositionalEquality 

-- from https://github.com/danr/Agda-projects/blob/master/Category-Theory/FreeMonoid.agda

open import Algebra.FunctionProperties using (Op₁; Op₂)
open import Algebra.Structures
open import Data.Product


record ≡-Monoid : Set (suc c) where
  infixr 9 _∙_
  field
    Carrier  : Set c
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≡_ _∙_ ε

open ≡-Monoid

≡-cong = Relation.Binary.PropositionalEquality.cong 

-- module ≡-reasoning (m : ≡-Monoid ) where

infixr 40 _::_
data  List  (A : Set c ) : Set c where
   [] : List A
   _::_ : A → List A → List A


infixl 30 _++_
_++_ :   {A : Set c } → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

list-id-l : { A : Set c } → { x : List A } →  [] ++ x ≡ x
list-id-l {_} {_} = refl
list-id-r : { A : Set c } → { x : List A } →  x ++ [] ≡ x
list-id-r {_} {[]} =   refl
list-id-r {A} {x :: xs} =  ≡-cong ( λ y → x :: y ) ( list-id-r {A} {xs} ) 
list-assoc : {A : Set c} → { xs ys zs : List A } →
      ( xs ++ ( ys ++ zs ) ) ≡ ( ( xs ++ ys ) ++ zs )
list-assoc  {_} {[]} {_} {_} = refl
list-assoc  {A} {x :: xs}  {ys} {zs} = ≡-cong  ( λ y  → x :: y ) 
         ( list-assoc {A} {xs} {ys} {zs} )
list-o-resp-≈ :  {A : Set c} →  {f g : List A } → {h i : List A } → 
                  f ≡  g → h ≡  i → (h ++ f) ≡  (i ++ g)
list-o-resp-≈  {A} refl refl = refl
list-isEquivalence : {A : Set c} → IsEquivalence {_} {_} {List A }  _≡_ 
list-isEquivalence {A} =      -- this is the same function as A's equivalence but has different types
   record { refl  = refl
     ; sym   = sym
     ; trans = trans
     } 


_<_∙_> :  (m : ≡-Monoid)  →   Carrier m → Carrier m → Carrier m
m < x ∙ y > = _∙_ m x y

infixr 9 _<_∙_>

record Monomorph ( a b : ≡-Monoid )  : Set c where
  field
      morph : Carrier a → Carrier b  
      identity     :  morph (ε a)  ≡  ε b
      homo :  ∀{x y} → morph ( a < x ∙ y > ) ≡ b < morph  x  ∙ morph  y >

open Monomorph

_+_ : { a b c : ≡-Monoid } → Monomorph b c → Monomorph a b → Monomorph a c
_+_ {a} {b} {c} f g =  record {
      morph = λ x →  morph  f ( morph g x ) ;
      identity  = identity1 ;
      homo  = homo1 
   } where
      identity1 : morph f ( morph g (ε a) )  ≡  ε c
      identity1 = let open ≡-Reasoning in begin
             morph f (morph g (ε a))
         ≡⟨  ≡-cong (morph f ) ( identity g )  ⟩
             morph f (ε b)
         ≡⟨  identity f  ⟩
             ε c
         ∎ 
      homo1 :  ∀{x y} → morph f ( morph g ( a < x ∙  y > )) ≡ ( c <   (morph f (morph  g x )) ∙(morph f (morph  g y) ) > )
      homo1 {x} {y} = let open ≡-Reasoning in begin
             morph f (morph g (a < x ∙ y >))
         ≡⟨  ≡-cong (morph f ) ( homo g) ⟩
             morph f (b < morph g x ∙ morph g y >)
         ≡⟨  homo f ⟩
              c < morph f (morph g x) ∙ morph f (morph g y) >
         ∎ 

M-id : { a : ≡-Monoid } → Monomorph a a 
M-id = record { morph = λ x → x  ; identity = refl ; homo = refl }

_==_ : { a b : ≡-Monoid } → Monomorph a b → Monomorph a b → Set c 
_==_  f g =  morph f ≡ morph g

-- Functional Extensionality Axiom (We cannot prove this in Agda / Coq, just assumming )
-- postulate extensionality : { a b : Obj A } {f g : Hom A a b } → (∀ {x} → (f x ≡ g x))  → ( f ≡ g ) 
postulate extensionality : Relation.Binary.PropositionalEquality.Extensionality c c 

isMonoids : IsCategory ≡-Monoid Monomorph _==_  _+_  (M-id)
isMonoids  = record  { isEquivalence =  isEquivalence1 
                    ; identityL =  refl
                    ; identityR =  refl
                    ; associative = refl
                    ; o-resp-≈ =    λ {a} {b} {c} {f} {g} {h} {i} → o-resp-≈ {a} {b} {c} {f} {g} {h} {i}
                    }
     where
        isEquivalence1 : { a b : ≡-Monoid } → IsEquivalence {_} {_} {Monomorph a b}  _==_ 
        isEquivalence1  =      -- this is the same function as A's equivalence but has different types
           record { refl  = refl
             ; sym   = sym
             ; trans = trans
             } 
        o-resp-≈ :  {a b c :  ≡-Monoid } {f g : Monomorph a b } → {h i : Monomorph b c }  → 
                          f ==  g → h ==  i → (h + f) ==  (i + g)
        o-resp-≈ {a} {b} {c} {f} {g} {h} {i} f==g h==i =  let open ≡-Reasoning in begin
             morph ( h + f )
         ≡⟨ ≡-cong ( λ  g → ( ( λ (x : Carrier a ) →  g x ) )) (extensionality {Carrier a} lemma11) ⟩
             morph ( i + g )
         ∎  
             where
                lemma11 : (x : Carrier a) → morph (h + f) x ≡ morph (i + g) x
                lemma11 x =   let open ≡-Reasoning in begin
                          morph ( h + f ) x
                     ≡⟨⟩
                          morph h ( ( morph f ) x )
                     ≡⟨  ≡-cong ( \y -> morph h ( y x ) )  f==g ⟩
                          morph h ( morph g x )
                     ≡⟨  ≡-cong ( \y -> y ( morph g  x ) )  h==i ⟩
                          morph i ( morph g x )
                     ≡⟨⟩
                          morph ( i + g ) x
                     ∎




Monoids : Category _ _ _
Monoids  =
  record { Obj =  ≡-Monoid 
         ; Hom = Monomorph
         ; _o_ = _+_  
         ; _≈_ = _==_
         ; Id  =  M-id
         ; isCategory = isMonoids 
           }

A = Sets {c}
B = Monoids  

open Functor

U : Functor B A
U = record {
       FObj = λ m → Carrier m ;
       FMap = λ f → morph f ;
       isFunctor = record {
              ≈-cong   = λ x → x
             ; identity = refl
             ; distr    = refl
       }
   } 

-- FObj 
list  : (a : Set c) → ≡-Monoid
list a = record {
    Carrier    =  List a
    ;  _∙_ = _++_
    ; ε        = []
    ; isMonoid = record {
          identity = ( ( λ x → list-id-l {a}  ) , ( λ x → list-id-r {a} ) ) ;
          isSemigroup = record {
               assoc =  λ x → λ y → λ z → sym ( list-assoc {a} {x} {y} {z} )
             ; isEquivalence = list-isEquivalence
             ; ∙-cong = λ x → λ y →  list-o-resp-≈ y x
          }
      }
    }

Generator : Obj A → Obj B
Generator s =  list s

-- solution

--   [a,b,c] → f(a) ∙ f(b) ∙ f(c)
Φ :  {a : Obj A } {b : Obj B} ( f : Hom A a (FObj U b) ) →  List a → Carrier b
Φ {a} {b} f [] = ε b
Φ {a} {b} f ( x :: xs ) = b < ( f x ) ∙ (Φ {a} {b} f xs ) >

solution : (a : Obj A ) (b : Obj B) ( f : Hom A a (FObj U b) ) →  Hom B (Generator a ) b 
solution a b f = record {
         morph = λ (l : List a) → Φ f l   ;
         identity = refl;
         homo = λ {x y} → homo1 x y 
    } where
        _*_ : Carrier b → Carrier b → Carrier b
        _*_  f g = b <  f ∙ g >
        homo1 : (x y : Carrier (Generator a)) → Φ f ( (Generator a) < x ∙  y > ) ≡ (Φ f x) * (Φ {a} {b} f y )
        homo1 [] y = sym (proj₁ ( IsMonoid.identity ( isMonoid b) ) (Φ f y))
        homo1 (x :: xs) y = let open ≡-Reasoning in 
             sym ( begin
                (Φ {a} {b} f (x :: xs)) * (Φ f y)
             ≡⟨⟩
                 ((f x) * (Φ f xs)) * (Φ f y)
             ≡⟨ ( IsMonoid.assoc ( isMonoid b )) _ _ _ ⟩
                (f x) * ( (Φ f xs)  * (Φ f y) )
             ≡⟨ sym ( (IsMonoid.∙-cong (isMonoid b)) refl (homo1 xs y )) ⟩
                (f x) * ( Φ f ( xs ++ y ) )
             ≡⟨⟩
                Φ {a} {b} f ( x :: ( xs ++ y ) )
             ≡⟨⟩
                Φ {a} {b} f ( (x ::  xs) ++ y ) 
             ≡⟨⟩
                Φ {a} {b} f ((Generator a) < ( x :: xs) ∙ y > ) 
             ∎ )

eta :  (a : Obj A) → Hom A a ( FObj U (Generator a) )
eta  a = λ ( x : a ) →  x :: []

FreeMonoidUniveralMapping : UniversalMapping A B U 
FreeMonoidUniveralMapping = 
    record {
       F = Generator ;
       η = eta ;
       _* = λ {a b} → λ f → solution a b f ; 
       isUniversalMapping = record {
             universalMapping = λ {a b f} → universalMapping {a} {b} {f} ; 
             uniquness = λ {a b f g} → uniquness {a} {b} {f} {g}
       }
    } where
        universalMapping :  {a : Obj A } {b : Obj B} { f : Hom A a (FObj U b) } →  FMap U ( solution a b f  ) o eta a   ≡ f
        universalMapping {a} {b} {f} = let open ≡-Reasoning in 
                     begin
                         FMap U ( solution a b f ) o eta a   
                     ≡⟨⟩
                         ( λ (x : a ) → Φ {a} {b} f (eta a x) )
                     ≡⟨⟩
                         ( λ (x : a ) → Φ {a} {b} f ( x :: [] ) )
                     ≡⟨⟩
                         ( λ (x : a ) →  b < ( f x ) ∙ (Φ {a} {b} f [] ) > )
                     ≡⟨⟩
                         ( λ (x : a ) →  b <    ( f x ) ∙ ( ε b ) > )
                     ≡⟨ ≡-cong ( λ  g → ( ( λ (x : a ) →  g x ) )) (extensionality {a} lemma-ext1) ⟩
                         ( λ (x : a ) →  f x  )
                     ≡⟨⟩
                          f
                     ∎  where
                        lemma-ext1 : ∀( x : a ) →  b <    ( f x ) ∙ ( ε b ) >  ≡ f x
                        lemma-ext1 x = ( proj₂ ( IsMonoid.identity ( isMonoid b) ) ) (f x)
        uniquness :  {a : Obj A } {b : Obj B} { f : Hom A a (FObj U b) } →
             { g :  Hom B (Generator a) b } → (FMap U g) o (eta a )  ≡ f  → B [ solution a b f ≈ g ]
        uniquness {a} {b} {f} {g} eq =  
                     extensionality  lemma-ext2 where
                        lemma-ext2 : ( ∀( x : List a ) → (morph ( solution a b f)) x  ≡ (morph g) x  )
                        -- (morph ( solution a b f)) []  ≡ (morph g) []  )
                        lemma-ext2 [] = let open ≡-Reasoning in
                             begin
                                (morph ( solution a b f)) []
                             ≡⟨ identity ( solution a b f) ⟩
                                ε b
                             ≡⟨ sym ( identity g ) ⟩
                                (morph g) []
                             ∎  
                        lemma-ext2 (x :: xs)  = let open ≡-Reasoning in
                             begin
                                (morph ( solution a b f)) ( x :: xs )
                             ≡⟨ homo ( solution a b f) {x :: []} {xs} ⟩
                                 b <   ((morph ( solution a b f)) ( x :: []) ) ∙ ((morph ( solution a b f)) xs ) >
                             ≡⟨  ≡-cong ( λ  k → (b <   ((morph ( solution a b f)) ( x :: []) ) ∙ k > )) (lemma-ext2 xs )   ⟩
                                 b <   ((morph ( solution a b f)) ( x :: []) )  ∙((morph g) ( xs )) >
                             ≡⟨  ≡-cong ( λ k → ( b <   ( k x ) ∙ ((morph g) ( xs )) >  )) (
                                 begin
                                     ( λ x → (morph ( solution a b f)) ( x :: [] ) )
                                 ≡⟨ extensionality {a} lemma-ext3 ⟩
                                     ( λ x → (morph g) ( x :: [] ) )
                                 ∎  
                             ) ⟩
                                 b <   ((morph g) ( x :: [] )) ∙((morph g) ( xs )) >
                             ≡⟨ sym ( homo g ) ⟩
                                (morph g) ( x :: xs )
                             ∎   where
                         lemma-ext3 :  ∀( x : a ) → (morph ( solution a b f)) (x :: [])  ≡ (morph g) ( x :: []  )
                         lemma-ext3 x = let open ≡-Reasoning in
                             begin
                               (morph ( solution a b f)) (x :: [])
                             ≡⟨  ( proj₂  ( IsMonoid.identity ( isMonoid b) )(f x) ) ⟩
                                f x
                             ≡⟨  sym ( ≡-cong (λ f → f x )  eq  ) ⟩
                               (morph g) ( x :: []  )
                             ∎   

open NTrans
--   fm-ε b = Φ

fm-ε :  NTrans B B ( ( FunctorF A B FreeMonoidUniveralMapping) ○ U) identityFunctor
fm-ε =  nat-ε A B FreeMonoidUniveralMapping 
--   TMap = λ a  →  solution (FObj U a) a (λ x → x ) ;
--   isNTrans = record {
--        commute =  commute1 
--     }
--   } where
--     commute1 :  {a b : Obj B} {f : Hom B a b} → let open ≈-Reasoning B  renaming (_o_ to _*_ ) in 
--                ( FMap (identityFunctor {_} {_} {_} {B}) f * solution (FObj U a) a (λ x → x) ) ≈
--                (  solution (FObj U b) b (λ x → x) * FMap (FunctorF A B FreeMonoidUniveralMapping ○ U) f )
--     commute1 {a} {b} {f} = let open ≡-Reasoning in begin
--              morph ((B ≈-Reasoning.o FMap identityFunctor f) (solution (FObj U a) a (λ x → x)))
--         ≡⟨ {!!}  ⟩
--             morph ((B ≈-Reasoning.o solution (FObj U b) b (λ x → x)) (FMap (FunctorF A B FreeMonoidUniveralMapping ○ U) f))
--         ∎


fm-η :  NTrans A A identityFunctor ( U ○ ( FunctorF A B FreeMonoidUniveralMapping) ) 
fm-η =  record { 
   TMap = λ a →  λ (x : a) → x :: [] ;
   isNTrans =  record {
       commute = commute1
     }
  } where
     commute1 :  {a b : Obj A} {f : Hom A a b} → let open ≈-Reasoning A  renaming (_o_ to _*_ ) in 
           (( FMap (U ○ FunctorF A B FreeMonoidUniveralMapping) f ) * (λ x → x :: []) ) ≈ ( (λ x → x :: []) * (λ z → FMap (identityFunctor {_} {_} {_} {A}) f z ) )
     commute1 {a} {b} {f} =  refl   --    λ (x : a ) → f x :: []
        

-- A = Sets {c}
-- B = Monoids  
-- U   underline funcotr
-- F   generator = x :: []
-- Eta          x :: []
-- Epsiron      morph = Φ

adj = UMAdjunction A B U FreeMonoidUniveralMapping 

 


