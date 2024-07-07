{-# OPTIONS --cubical-compatible --safe #-}

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
module free-monoid { c c₁ c₂ ℓ : Level }   where

-- Free Monoid and it's Universal Mapping 
---- using Sets and forgetful functor

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

open import Category.Sets hiding (_==_)
open import Category.Cat
open import HomReasoning
open import Definitions
open import Relation.Binary.Structures
open import universal-mapping 
open import Relation.Binary.PropositionalEquality 

-- from https://github.com/danr/Agda-projects/blob/master/Category-Theory/FreeMonoid.agda

open import Algebra.Definitions -- using (Op₁; Op₂)
open import Algebra.Core
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
_==_  {a} f g =  (x : Carrier a) → morph f x ≡ morph g x

isMonoids : IsCategory ≡-Monoid Monomorph _==_  _+_  (M-id)
isMonoids  = record  { isEquivalence =  isEquivalence1 
                    ; identityL =  λ {a} {b} {f} x →   refl
                    ; identityR =  λ {a} {b} {f} x →   refl
                    ; associative = λ x → refl
                    ; o-resp-≈ =    λ {a} {b} {c} {f} {g} {h} {i} → o-resp-≈ {a} {b} {c} {f} {g} {h} {i}
                    }
     where
        isEquivalence1 : { a b : ≡-Monoid } → IsEquivalence {_} {_} {Monomorph a b}  _==_ 
        isEquivalence1  =      -- this is the same function as A's equivalence but has different types
           record { refl  = λ x → refl
             ; sym   = λ {s} {t} s=t y →  sym ( s=t y )
             ; trans = λ a=b b=c x → trans (a=b x) (b=c x) 
             } 
        o-resp-≈ :  {a b c :  ≡-Monoid } {f g : Monomorph a b } → {h i : Monomorph b c }  → 
                          f ==  g → h ==  i → (h + f) ==  (i + g)
        o-resp-≈ {a} {b} {c} {f} {g} {h} {i} f==g h==i x =  let open ≡-Reasoning in begin
             morph ( h + f ) x
         ≡⟨ lemma11 x ⟩
             morph ( i + g ) x
         ∎  
             where
                lemma11 : (x : Carrier a) → morph (h + f) x ≡ morph (i + g) x
                lemma11 x =   let open ≡-Reasoning in begin
                          morph ( h + f ) x
                     ≡⟨⟩
                          morph h ( ( morph f ) x )
                     ≡⟨  ≡-cong ( λ y →   morph h y ) ( f==g x) ⟩
                          morph h ( morph g x )
                     ≡⟨ h==i _ ⟩
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

open Functor

U : Functor Monoids Sets
U = record {
       FObj = λ m → Carrier m ;
       FMap = λ f → morph f ;
       isFunctor = record {
              ≈-cong   = λ f=g x → f=g x
             ; identity = λ {a} x → refl
             ; distr    = λ {a b c} {f} {g} x → refl
             }
   } 

-- FObj 
list  : (a : Set c) → ≡-Monoid
list a = record {
    Carrier    =  List a
    ;  _∙_ = _++_
    ; ε        = []
    ;  isMonoid  = record { isSemigroup = record { isMagma = record {
       isEquivalence =  list-isEquivalence
       ; ∙-cong =  λ x → λ y →  list-o-resp-≈ y x }
       ; assoc = λ x → λ y → λ z → sym ( list-assoc {a} {x} {y} {z} ) }
       ; identity =  ( ( λ x → list-id-l {a}  ) , ( λ x → list-id-r {a} ) )
      } }

Generator : Obj Sets → Obj Monoids
Generator s =  list s

-- solution

--   [a,b,c] → f(a) ∙ f(b) ∙ f(c)
Φ :  {a : Obj Sets } {b : Obj Monoids} ( f : Hom Sets a (FObj U b) ) →  List a → Carrier b
Φ {a} {b} f [] = ε b
Φ {a} {b} f ( x :: xs ) = b < ( f x ) ∙ (Φ {a} {b} f xs ) >

solution : (a : Obj Sets ) (b : Obj Monoids) ( f : Hom Sets a (FObj U b) ) →  Hom Monoids (Generator a ) b 
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

eta :  (a : Obj Sets) → Hom Sets a ( FObj U (Generator a) )
eta  a = λ ( x : a ) →  x :: []

FreeMonoidUniveralMapping : UniversalMapping Sets Monoids U 
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
        universalMapping :  {a : Obj Sets } {b : Obj Monoids} { f : Hom Sets a (FObj U b) } →   Sets [ Sets [ Φ {a} {b} f o eta a ] ≈ f ]
        universalMapping {a} {b} {f} x = 
                     begin
                          Φ {a} {b} f ( eta a x) ≡⟨⟩
                          b < f x ∙ ε b > ≡⟨ lemma-ext1 x ⟩
                          f x
                     ∎  where
                        open ≡-Reasoning 
                        lemma-ext1 : ∀( x : a ) →  b <    ( f x ) ∙ ( ε b ) >  ≡ f x
                        lemma-ext1 x = ( proj₂ ( IsMonoid.identity ( isMonoid b) ) ) (f x)
        uniquness :  {a : Obj Sets } {b : Obj Monoids} { f : Hom Sets a (FObj U b) } →
             { g :  Hom Monoids (Generator a) b } →  Sets [ Sets [ morph g o eta a ] ≈ f ] → Monoids [ solution a b f ≈ g ]
        uniquness {a} {b} {f} {g} eq x = lemma-ext2 x where
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
                             begin (morph ( solution a b f)) ( x :: xs )
                             ≡⟨ homo ( solution a b f) {x :: []} {xs} ⟩
                                 b <   ((morph ( solution a b f)) ( x :: []) ) ∙ ((morph ( solution a b f)) xs ) >
                             ≡⟨  ≡-cong ( λ  k → (b <   ((morph ( solution a b f)) ( x :: []) ) ∙ k > )) (lemma-ext2 xs )   ⟩
                                 b <   ((morph ( solution a b f)) ( x :: []) )  ∙((morph g) ( xs )) >
                             ≡⟨  ≡-cong ( λ k → ( b <   k ∙ ((morph g) ( xs )) >  )) (
                                 begin
                                     morph ( solution a b f) ( x :: [] )
                                 ≡⟨ lemma-ext3 x ⟩
                                     morph g ( x :: [] ) 
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
                                 ≡⟨  sym (eq x) ⟩
                                   (morph g) ( x :: []  )
                                 ∎   

open NTrans
--   fm-ε b = Φ

fm-ε :  NTrans Monoids Monoids ( ( FunctorF Sets Monoids FreeMonoidUniveralMapping) ○ U) identityFunctor
fm-ε =  nat-ε Sets Monoids FreeMonoidUniveralMapping 

fm-η :  NTrans Sets Sets identityFunctor ( U ○ ( FunctorF Sets Monoids FreeMonoidUniveralMapping) ) 
fm-η =  record { 
   TMap = λ a →  λ (x : a) → x :: [] ;
   isNTrans =  record {
       commute = commute1
     }
  } where
     commute1 :  {a b : Obj Sets} {f : Hom Sets a b} → let open ≈-Reasoning Sets  renaming (_o_ to _*_ ) in 
           (( FMap (U ○ FunctorF Sets Monoids FreeMonoidUniveralMapping) f ) * (λ x → x :: []) ) ≈ ( (λ x → x :: []) * (λ z → FMap (identityFunctor {_} {_} {_} {Sets}) f z ) )
     commute1 {a} {b} {f} x =  begin 
         morph (solution a (list b) (λ y → (f y :: []))) ((λ x₁ → x₁ :: []) x)  ≡⟨ refl ⟩
        (λ x₁ → x₁ :: []) (f x) ∎  where open ≡-Reasoning 
        

-- Sets = Sets {c}
-- Monoids = Monoids  
-- U   underline funcotr
-- F   generator = x :: []
-- Eta          x :: []
-- Epsiron      morph = Φ

adj = UMAdjunction Sets Monoids U FreeMonoidUniveralMapping 

 


