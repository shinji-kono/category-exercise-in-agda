open import Level
open import Category
module monoidal where

open import Data.Product renaming (_×_ to _*_)
open import Category.Constructions.Product
open import HomReasoning
open import cat-utility
open import Relation.Binary.Core
open import Relation.Binary

open Functor

-- record Iso  {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ) 
--          (x y : Obj C )
--         : Set ( suc  (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁)) where
--    field
--          ≅→ :  Hom C x y 
--          ≅← :  Hom C y x 
--          iso→  :  C [ C [ ≅← o ≅→  ] ≈  id1 C x ]
--          iso←  :  C [ C [ ≅→ o ≅←  ] ≈  id1 C y ]

-- Monoidal Category

record IsMonoidal  {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ) (I : Obj C) ( BI : Functor ( C × C ) C )
        : Set ( suc  (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁)) where
  open Iso 
  infixr 9 _□_ _■_
  _□_ : ( x y : Obj C ) → Obj C
  _□_ x y = FObj BI ( x , y )
  _■_ : {a b c d : Obj C } ( f : Hom C a c ) ( g : Hom C b d ) → Hom C ( a □ b ) ( c □ d )
  _■_ f g = FMap BI ( f , g )
  field
      mα-iso : {a b c : Obj C} →  Iso C ( ( a □ b) □ c)  ( a □ ( b □ c ) ) 
      mλ-iso : {a : Obj C} →  Iso C ( I □ a)  a 
      mρ-iso : {a : Obj C} →  Iso C ( a □ I)  a 
      mα→nat1 : {a a' b c : Obj C} →  ( f : Hom C a a' ) →
         C [ C [ ( f ■ id1 C ( b □ c ))  o ≅→ (mα-iso {a} {b} {c}) ]  ≈
            C [   ≅→ (mα-iso )  o ( (f ■ id1 C b ) ■ id1 C c )    ] ]
      mα→nat2 : {a b b' c : Obj C} →  ( f : Hom C b b' ) →
         C [ C [ ( id1 C a ■ ( f ■ id1 C c ) ) o ≅→ (mα-iso {a} {b} {c} ) ]  ≈
            C [   ≅→ (mα-iso )  o ( (id1 C a ■ f )  ■ id1 C c ) ] ]
      mα→nat3 : {a b c c' : Obj C} →  ( f : Hom C c c' ) →
         C [ C [ ( id1 C a ■ ( id1 C b ■ f ) ) o ≅→ (mα-iso {a} {b} {c} ) ]  ≈
            C [   ≅→ (mα-iso )  o ( id1 C ( a □ b ) ■ f ) ] ]
      mλ→nat : {a a' : Obj C} →  ( f : Hom C a a' ) →
         C [ C [ f o ≅→ (mλ-iso {a} ) ]  ≈
            C [   ≅→ (mλ-iso )  o ( id1 C I  ■ f )    ] ]
      mρ→nat : {a a' : Obj C} →  ( f : Hom C a a' ) →
         C [ C [ f o ≅→ (mρ-iso {a} ) ]  ≈
            C [   ≅→ (mρ-iso )  o ( f ■ id1 C I  )    ] ]
      -- we should write naturalities for ≅← (maybe derived from above )
  αABC□1D : {a b c d e : Obj C } → Hom C (((a □ b) □ c ) □ d) ((a □ (b □ c)) □ d)
  αABC□1D {a} {b} {c} {d} {e} = (  ≅→ mα-iso  ■ id1 C d )
  αAB□CD : {a b c d e : Obj C } → Hom C  ((a □ (b □ c)) □ d) (a □ ((b □ c ) □ d))
  αAB□CD {a} {b} {c} {d} {e} =   ≅→ mα-iso
  1A□BCD : {a b c d e : Obj C } → Hom C  (a □ ((b □ c ) □ d)) (a □ (b □ ( c □ d) ))
  1A□BCD {a} {b} {c} {d} {e} = ( id1 C a ■   ≅→ mα-iso )
  αABC□D : {a b c d e : Obj C } → Hom C  (a □ (b □ ( c □ d) )) ((a □ b ) □ (c □ d))
  αABC□D {a} {b} {c} {d} {e} =  ≅← mα-iso  
  αA□BCD : {a b c d e : Obj C } → Hom C (((a □ b) □ c ) □ d) ((a □ b ) □ (c □ d))
  αA□BCD {a} {b} {c} {d} {e} =  ≅→ mα-iso  
  αAIB :  {a b  : Obj C } →  Hom C (( a □ I ) □ b ) (a □ ( I □ b ))
  αAIB {a} {b} = ≅→ mα-iso
  1A□λB : {a b  : Obj C } →  Hom C  (a □ ( I □ b )) ( a □ b )
  1A□λB {a} {b} =  id1 C a ■  ≅→ mλ-iso 
  ρA□IB : {a b  : Obj C } →  Hom C  (( a □ I ) □ b ) ( a □ b )
  ρA□IB {a} {b} = ≅→  mρ-iso  ■  id1 C b

  field
      comm-penta : {a b c d e : Obj C}
         → C [ C [ αABC□D {a} {b} {c} {d} {e} o  C [ 1A□BCD {a} {b} {c} {d} {e} o C [ αAB□CD {a} {b} {c} {d} {e} o αABC□1D {a} {b} {c} {d} {e} ] ] ]
             ≈ αA□BCD {a} {b} {c} {d} {e} ]
      comm-unit : {a b : Obj C}
         → C [ C [ 1A□λB {a} {b} o  αAIB ] ≈ ρA□IB {a} {b} ]

record Monoidal  {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ) 
        : Set ( suc  (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁)) where
  field
      m-i : Obj C
      m-bi : Functor ( C × C ) C 
      isMonoidal : IsMonoidal C m-i m-bi

---------
--
--  Lax Monoidal Functor
--
--    N → M
--
---------

---------
--
-- Two implementations of Functor ( C × C ) → D from F : Functor C → D (given)
--        dervied from F and two Monoidal Categories
--
--     F x ● F y
--     F ( x ⊗  y )
--
-- and a given natural transformation for them 
--
--      φ : F x ● F y  → F ( x ⊗  y )
--
--      TMap φ : ( x y : Obj C ) →  Hom D ( F x ● F y ) ( F ( x ⊗ y ))
--
-- a given unit arrow
--
--      ψ : IN → IM

Functor● :  {c₁ c₂ ℓ : Level} (C D : Category c₁ c₂ ℓ) ( N : Monoidal D )
      ( MF :   Functor C D ) →  Functor ( C × C ) D
Functor● C D N MF =  record {
       FObj = λ x  → (FObj MF (proj₁ x) ) ●  (FObj MF (proj₂ x) )
     ; FMap = λ {x : Obj ( C × C ) } {y} f →  (  FMap MF  (proj₁  f ) ■ FMap MF (proj₂ f)  )
     ; isFunctor = record {
             ≈-cong   = ≈-cong
             ; identity = identity
             ; distr    = distr
     }
    } where
  _●_ : (x y : Obj D ) → Obj D
  _●_ x y =  (IsMonoidal._□_ (Monoidal.isMonoidal N) ) x y
  _■_ : {a b c d : Obj D } ( f : Hom D a c ) ( g : Hom D b d ) → Hom D ( a ● b ) ( c ● d )
  _■_ f g = FMap (Monoidal.m-bi N) ( f , g )
  F : { a b : Obj C } → ( f : Hom C a b ) → Hom D (FObj MF a) (FObj MF b )
  F f = FMap MF f
  ≈-cong : {a b : Obj (C × C)} {f g : Hom (C × C) a b} → (C × C) [ f ≈ g ] →
        D [  (F (proj₁ f) ■ F (proj₂ f)) ≈  (F (proj₁ g) ■ F (proj₂ g)) ]
  ≈-cong {a} {b} {f} {g} f≈g = let open ≈-Reasoning D in begin
        F (proj₁ f) ■ F (proj₂ f)
     ≈⟨ fcong (Monoidal.m-bi N) (  fcong MF (  proj₁ f≈g ) , fcong MF ( proj₂ f≈g ))  ⟩
        F (proj₁ g) ■ F (proj₂ g)
     ∎ 
  identity : {a : Obj (C × C)} → D [  (F (proj₁ (id1 (C × C) a)) ■ F (proj₂ (id1 (C × C) a)))
        ≈ id1 D (FObj MF (proj₁ a) ● FObj MF (proj₂ a)) ]
  identity {a} =   let open ≈-Reasoning D in begin
         F (proj₁ (id1 (C × C) a)) ■ F (proj₂ (id1 (C × C) a))
     ≈⟨ fcong  (Monoidal.m-bi N) (  IsFunctor.identity (isFunctor MF )  ,  IsFunctor.identity (isFunctor MF ))  ⟩
         id1 D (FObj MF (proj₁ a)) ■ id1 D (FObj MF (proj₂ a))
     ≈⟨ IsFunctor.identity (isFunctor  (Monoidal.m-bi N)) ⟩
        id1 D (FObj MF (proj₁ a) ● FObj MF (proj₂ a))
     ∎
  distr : {a b c : Obj (C × C)} {f : Hom (C × C) a b} {g : Hom (C × C) b c} →
     D [  (F (proj₁ ((C × C) [ g o f ])) ■ F (proj₂ ((C × C) [ g o f ])))
       ≈ D [  (F (proj₁ g) ■ F (proj₂ g)) o  (F (proj₁ f) ■ F (proj₂ f)) ] ]
  distr {a} {b} {c} {f} {g} =  let open ≈-Reasoning D in begin
        (F (proj₁ ((C × C) [ g o f ])) ■ F (proj₂ ((C × C) [ g o f ])))
     ≈⟨ fcong (Monoidal.m-bi N) (  IsFunctor.distr ( isFunctor  MF) ,  IsFunctor.distr ( isFunctor MF )) ⟩
         ( F (proj₁ g)  o F (proj₁ f) ) ■ (  F (proj₂ g) o F (proj₂ f)  )
     ≈⟨ IsFunctor.distr ( isFunctor  (Monoidal.m-bi N)) ⟩
        (F (proj₁ g) ■ F (proj₂ g)) o  (F (proj₁ f) ■ F (proj₂ f))
     ∎

Functor⊗ :  {c₁ c₂ ℓ : Level} (C D : Category c₁ c₂ ℓ) ( M : Monoidal C ) 
      ( MF :   Functor C D ) →  Functor ( C × C ) D
Functor⊗ C D M MF =  record {
       FObj = λ x → FObj MF ( proj₁ x ⊗ proj₂ x )
     ; FMap = λ {a} {b} f →  F ( proj₁ f □ proj₂ f )
     ; isFunctor = record {
             ≈-cong   = ≈-cong
             ; identity = identity
             ; distr    = distr
     }
    } where
  _⊗_ : (x y : Obj C ) → Obj C
  _⊗_ x y =  (IsMonoidal._□_ (Monoidal.isMonoidal M) ) x y
  _□_ : {a b c d : Obj C } ( f : Hom C a c ) ( g : Hom C b d ) → Hom C ( a ⊗ b ) ( c ⊗ d )
  _□_ f g = FMap (Monoidal.m-bi M) ( f , g )
  F : { a b : Obj C } → ( f : Hom C a b ) → Hom D (FObj MF a) (FObj MF b )
  F f = FMap MF f
  ≈-cong : {a b : Obj (C × C)} {f g : Hom (C × C) a b} → (C × C) [ f ≈ g ] →
     D [ F ( (proj₁ f □ proj₂ f)) ≈ F ( (proj₁ g □ proj₂ g)) ]
  ≈-cong {a} {b} {f} {g} f≈g = IsFunctor.≈-cong (isFunctor MF ) ( IsFunctor.≈-cong (isFunctor  (Monoidal.m-bi M) ) f≈g  )
  identity : {a : Obj (C × C)} → D [ F ( (proj₁ (id1 (C × C) a) □ proj₂ (id1 (C × C) a)))
      ≈ id1 D (FObj MF (proj₁ a ⊗ proj₂ a)) ]
  identity {a} = let open ≈-Reasoning D in begin
        F ( (proj₁ (id1 (C × C) a) □ proj₂ (id1 (C × C) a)))
     ≈⟨⟩
        F (FMap (Monoidal.m-bi M) (id1 (C × C) a ) )
     ≈⟨ fcong MF ( IsFunctor.identity (isFunctor (Monoidal.m-bi M) )) ⟩
        F (id1 C (proj₁ a ⊗ proj₂ a))
     ≈⟨ IsFunctor.identity (isFunctor MF) ⟩
        id1 D (FObj MF (proj₁ a ⊗ proj₂ a))
     ∎
  distr : {a b c : Obj (C × C)} {f : Hom (C × C) a b} {g : Hom (C × C) b c} → D [
        F ( (proj₁ ((C × C) [ g o f ]) □ proj₂ ((C × C) [ g o f ])))
    ≈ D [ F ( (proj₁ g □ proj₂ g)) o F ( (proj₁ f □ proj₂ f)) ] ]
  distr {a} {b} {c} {f} {g} =  let open ≈-Reasoning D in begin
        F ( (proj₁ ((C × C) [ g o f ]) □ proj₂ ((C × C) [ g o f ])))
     ≈⟨⟩
        F (FMap (Monoidal.m-bi M) ( (C × C)  [ g o f ] ))
     ≈⟨ fcong MF ( IsFunctor.distr (isFunctor (Monoidal.m-bi M))) ⟩
        F (C [ FMap (Monoidal.m-bi M) g o FMap (Monoidal.m-bi M) f ])
     ≈⟨ IsFunctor.distr ( isFunctor MF ) ⟩
        F ( proj₁ g □ proj₂ g) o F ( proj₁ f □ proj₂ f) 
     ∎


record IsMonoidalFunctor {c₁ c₂ ℓ : Level} {C D : Category c₁ c₂ ℓ}  ( M : Monoidal C ) ( N : Monoidal D )
      ( MF :   Functor C D )
      ( ψ  :  Hom D (Monoidal.m-i N)  (FObj MF (Monoidal.m-i M) ) )
        : Set ( suc  (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁)) where
  _⊗_ : (x y : Obj C ) → Obj C
  _⊗_ x y =  (IsMonoidal._□_ (Monoidal.isMonoidal M) ) x y
  _□_ : {a b c d : Obj C } ( f : Hom C a c ) ( g : Hom C b d ) → Hom C ( a ⊗ b ) ( c ⊗ d )
  _□_ f g = FMap (Monoidal.m-bi M) ( f , g )
  _●_ : (x y : Obj D ) → Obj D
  _●_ x y =  (IsMonoidal._□_ (Monoidal.isMonoidal N) ) x y
  _■_ : {a b c d : Obj D } ( f : Hom D a c ) ( g : Hom D b d ) → Hom D ( a ● b ) ( c ● d )
  _■_ f g = FMap (Monoidal.m-bi N) ( f , g )
  F● :  Functor ( C × C ) D
  F●  =  Functor●  C D N MF
  F⊗ : Functor ( C × C ) D
  F⊗  =  Functor⊗  C D M MF
  field
      φab :  NTrans  ( C × C ) D  F● F⊗ 
  open Iso
  open Monoidal
  open IsMonoidal hiding ( _■_ ;  _□_ )
  αC :  {a b c : Obj C} → Hom C (( a ⊗ b ) ⊗ c ) ( a ⊗ ( b ⊗ c ) )
  αC {a} {b} {c} =  ≅→ (mα-iso (isMonoidal M) {a} {b} {c}) 
  αD :  {a b c : Obj D} → Hom D (( a ● b ) ● c ) ( a ● ( b ● c ) )
  αD {a} {b} {c} =  ≅→ (mα-iso (isMonoidal N) {a} {b} {c}) 
  F : Obj C → Obj D
  F x = FObj MF x
  φ : ( x y : Obj C ) →  Hom D ( FObj  F● (x , y) ) ( FObj F⊗ ( x , y ))
  φ x y = NTrans.TMap φab ( x , y )
  1●φBC :  {a b c : Obj C} → Hom D  ( F a ● ( F b ● F c ) ) ( F a ● ( F ( b ⊗ c ) ))
  1●φBC {a} {b} {c} =  id1 D (F a) ■  φ b c
  φAB⊗C :  {a b c : Obj C} → Hom D  ( F a ● ( F ( b ⊗ c ) )) (F ( a  ⊗ ( b  ⊗ c )))
  φAB⊗C {a} {b} {c} =   φ  a  (b ⊗ c )
  φAB●1 :  {a b c : Obj C} → Hom D  ( ( F a ●  F b ) ● F c ) ( F ( a ⊗ b ) ● F c )
  φAB●1 {a} {b} {c} =  φ a b ■ id1 D (F c)
  φA⊗BC :  {a b c : Obj C} → Hom D  ( F ( a ⊗ b ) ● F c ) (F ( (a  ⊗  b ) ⊗ c ))
  φA⊗BC {a} {b} {c} = φ ( a ⊗ b ) c
  FαC : {a b c : Obj C} → Hom D (F ( (a  ⊗  b ) ⊗ c )) (F ( a  ⊗ ( b  ⊗ c )))
  FαC {a} {b} {c} =  FMap MF ( ≅→ (mα-iso (isMonoidal M) {a} {b} {c}) )
  1●ψ : { a b : Obj C } → Hom D (F a  ● Monoidal.m-i N ) ( F a ● F ( Monoidal.m-i M ) )
  1●ψ{a} {b} =  id1 D (F a)  ■  ψ
  φAIC : { a b : Obj C } → Hom D  ( F a ● F ( Monoidal.m-i M ) ) (F ( a  ⊗ Monoidal.m-i M ))
  φAIC {a} {b} = φ a (  Monoidal.m-i M )
  FρC : { a b : Obj C } → Hom D   (F ( a  ⊗ Monoidal.m-i M ))( F a  )
  FρC {a} {b} = FMap MF (  ≅→ (mρ-iso (isMonoidal M) {a} ) )
  ρD : { a b : Obj C } → Hom D (F a  ● Monoidal.m-i N ) ( F a  )
  ρD {a} {b} =  ≅→ (mρ-iso (isMonoidal N) {F a} )
  ψ●1 : { a b : Obj C } → Hom D (Monoidal.m-i N ● F b  ) ( F ( Monoidal.m-i M )  ● F b  )
  ψ●1 {a} {b} =  ψ ■ id1 D (F b)
  φICB : { a b : Obj C } → Hom D  ( F ( Monoidal.m-i M )  ● F b  ) ( F (  ( Monoidal.m-i M )  ⊗ b ) )
  φICB {a} {b} = φ  ( Monoidal.m-i M ) b
  FλD : { a b : Obj C } → Hom D  ( F (  ( Monoidal.m-i M )  ⊗ b ) ) (F b ) 
  FλD {a} {b} = FMap MF ( ≅→ (mλ-iso (isMonoidal M) {b} ) )
  λD : { a b : Obj C } → Hom D  (Monoidal.m-i N ● F b  )  (F b ) 
  λD {a} {b} = ≅→ (mλ-iso (isMonoidal N) {F b} )
  field
     associativity : {a b c : Obj C } → D [ D [ φAB⊗C {a} {b} {c} o D [ 1●φBC o αD ] ]  ≈ D [ FαC  o  D [ φA⊗BC o φAB●1 ] ] ]
     unitarity-idr : {a b : Obj C } → D [ D [ FρC  {a} {b}  o D [ φAIC {a} {b} o  1●ψ{a} {b} ] ]  ≈ ρD {a} {b}  ]
     unitarity-idl : {a b : Obj C } → D [ D [ FλD  {a} {b}  o D [ φICB {a} {b} o  ψ●1 {a} {b} ] ]  ≈ λD {a} {b}  ]

record MonoidalFunctor {c₁ c₂ ℓ : Level} {C D : Category c₁ c₂ ℓ}  ( M : Monoidal C ) ( N : Monoidal D )
        : Set ( suc  (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁)) where
  field
      MF : Functor C D
      ψ  : Hom D (Monoidal.m-i N)  (FObj MF (Monoidal.m-i M) )
      isMonodailFunctor : IsMonoidalFunctor  M N MF ψ


open import Category.Sets

import Relation.Binary.PropositionalEquality
-- Extensionality a b = {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g → ( λ x → f x ≡ λ x → g x )
postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Relation.Binary.PropositionalEquality.Extensionality c₂ c₂

------
-- Data.Product as a Tensor Product for Monoidal Category
--

open import Relation.Binary.PropositionalEquality hiding ( [_] )

SetsTensorProduct : {c : Level} → Functor ( Sets {c} × Sets {c} )  (Sets {c})
SetsTensorProduct =   record {
       FObj = λ x  →  proj₁ x  *  proj₂ x
     ; FMap = λ {x : Obj ( Sets × Sets ) } {y} f → map (proj₁ f)  (proj₂ f)
     ; isFunctor = record {
             ≈-cong   = ≈-cong 
             ; identity = refl
             ; distr    = refl
     }
    } where
        ≈-cong : {a b : Obj (Sets × Sets)} {f g : Hom (Sets × Sets) a b} →
                (Sets × Sets) [ f ≈ g ] → Sets [ map (proj₁ f) (proj₂ f) ≈ map (proj₁ g) (proj₂ g) ]
        ≈-cong (refl , refl) =  refl

-----
--
-- Sets as Monoidal Category
--
--  almost all comutativities are refl
--
--
--

data One {c : Level} : Set c where
  OneObj : One   -- () in Haskell ( or any one object set )

MonoidalSets : {c : Level} → Monoidal (Sets {c})
MonoidalSets {c} = record {
      m-i = One {c} ;
      m-bi = SetsTensorProduct  ;
      isMonoidal = record {
              mα-iso  =  record { ≅→  =  mα→ ; ≅← =  mα← ; iso→  = refl ; iso← = refl } ;
              mλ-iso  =  record { ≅→  =  mλ→ ; ≅← =  mλ← ; iso→  = extensionality Sets ( λ x → mλiso x ) ; iso← = refl } ;
              mρ-iso  =  record { ≅→  =  mρ→ ; ≅← =  mρ← ; iso→  = extensionality Sets ( λ x → mρiso x ) ; iso← = refl } ;
              mα→nat1  = λ f → refl  ;
              mα→nat2  =  λ f → refl  ;
              mα→nat3  =  λ f → refl  ;
              mλ→nat  =  λ f → refl  ;
              mρ→nat  =  λ f → refl  ;
              comm-penta  = refl ;
              comm-unit  = refl
      }
   } where
       _⊗_ : ( a b : Obj Sets ) → Obj Sets
       _⊗_ a b = FObj SetsTensorProduct (a , b )
       --  associative operations
       mα→ : {a b c : Obj Sets} →  Hom Sets ( ( a ⊗ b ) ⊗ c ) ( a ⊗ ( b ⊗ c ) )
       mα→ ((a , b) , c ) =  (a , ( b , c ) )
       mα← : {a b c : Obj Sets} →  Hom Sets ( a ⊗ ( b ⊗ c ) ) ( ( a ⊗ b ) ⊗ c )
       mα← (a , ( b , c ) ) =  ((a , b) , c )
       --  (One , a) ⇔ a 
       mλ→ : {a  : Obj Sets} →  Hom Sets ( One ⊗ a ) a
       mλ→ (_ , a) =  a
       mλ← : {a  : Obj Sets} →  Hom Sets  a ( One ⊗ a )
       mλ←  a = ( OneObj , a )
       mλiso : {a : Obj Sets} (x : One ⊗ a) →  (Sets [ mλ← o mλ→ ]) x ≡ id1 Sets (One ⊗ a) x
       mλiso (OneObj , _ ) = refl
       --  (a , One) ⇔ a 
       mρ→ : {a  : Obj Sets} →  Hom Sets ( a ⊗ One )  a
       mρ→ (a , _) =  a
       mρ← : {a  : Obj Sets} →  Hom Sets a ( a ⊗ One ) 
       mρ←  a = ( a , OneObj )
       mρiso : {a : Obj Sets} (x : a ⊗ One ) →  (Sets [ mρ← o mρ→ ]) x ≡ id1 Sets (a ⊗ One) x
       mρiso (_ , OneObj ) = refl

≡-cong = Relation.Binary.PropositionalEquality.cong 

----
--
--  HaskellMonoidalFunctor is a monoidal functor on Sets
--
--


record IsHaskellMonoidalFunctor {c₁ : Level} ( F : Functor (Sets {c₁}) (Sets {c₁}) )
      ( unit  : FObj F One )
      ( φ    : {a b : Obj Sets} → Hom Sets ((FObj F a) *  (FObj F b )) ( FObj F ( a * b ) ) )
        : Set (suc (suc c₁)) where
  isM  : IsMonoidal (Sets {c₁}) One SetsTensorProduct  
  isM = Monoidal.isMonoidal MonoidalSets 
  open IsMonoidal
  field
          natφ : { a b c d : Obj Sets } { x : FObj F a} { y : FObj F b} { f : a → c } { g : b → d  }
             → FMap F (map f g) (φ (x , y)) ≡ φ (FMap F f x , FMap F g y)
          assocφ : { x y z : Obj Sets } { a : FObj F x } { b : FObj F y }{ c : FObj F z }
             → φ (a , φ (b , c)) ≡ FMap F (Iso.≅→ (mα-iso isM)) (φ (φ (a , b) , c))
          idrφ : {a : Obj Sets } { x : FObj F a } → FMap F (Iso.≅→ (mρ-iso isM)) (φ (x , unit)) ≡ x
          idlφ : {a : Obj Sets } { x : FObj F a } → FMap F (Iso.≅→ (mλ-iso isM)) (φ (unit , x)) ≡ x

--   http://www.staff.city.ac.uk/~ross/papers/Applicative.pdf
-- naturality of φ       fmap(f × g)(φ u v) = φ ( fmap f u) ( fmap g v )
-- left identity         fmap snd (φ unit v) = v
-- right identity        fmap fst (φ u unit) = u
-- associativity         fmap assoc  (φ u (φ v w)) = φ (φ u v) w


record HaskellMonoidalFunctor {c₁ : Level} ( F : Functor (Sets {c₁}) (Sets {c₁}) )
        : Set (suc (suc c₁)) where
  field
      unit  : FObj F One
      φ    : {a b : Obj Sets} → Hom Sets ((FObj F a) *  (FObj F b )) ( FObj F ( a * b ) )
      isHaskellMonoidalFunctor : IsHaskellMonoidalFunctor F unit φ


----
--
--  laws of HaskellMonoidalFunctor are directly mapped to the laws of Monoidal Functor
--
--

HaskellMonoidalFunctor→MonoidalFunctor :  {c : Level} ( F : Functor (Sets {c}) (Sets {c}) ) → (mf : HaskellMonoidalFunctor F )
   → MonoidalFunctor {_} {c} {_} {Sets} {Sets} MonoidalSets MonoidalSets
HaskellMonoidalFunctor→MonoidalFunctor {c} F mf = record {
      MF = F
    ; ψ  = λ _ → HaskellMonoidalFunctor.unit mf
    ; isMonodailFunctor = record {
             φab  = record { TMap = λ x →  φ ; isNTrans = record { commute = comm0 } }
         ;   associativity  = λ {a b c} → comm1 {a} {b} {c}
         ;   unitarity-idr = λ {a b} → comm2 {a} {b}
         ;   unitarity-idl = λ {a b} → comm3 {a} {b}
      }
  } where
      open Monoidal 
      open IsMonoidal hiding ( _■_ ;  _□_ )
      ismf : IsHaskellMonoidalFunctor F ( HaskellMonoidalFunctor.unit mf ) ( HaskellMonoidalFunctor.φ mf ) 
      ismf = HaskellMonoidalFunctor.isHaskellMonoidalFunctor mf
      M : Monoidal (Sets {c})
      M = MonoidalSets
      isM  : IsMonoidal (Sets {c}) One SetsTensorProduct  
      isM = Monoidal.isMonoidal MonoidalSets 
      unit : FObj F One
      unit = HaskellMonoidalFunctor.unit mf
      _⊗_ : (x y : Obj Sets ) → Obj Sets
      _⊗_ x y =  (IsMonoidal._□_ (Monoidal.isMonoidal M) ) x y
      _□_ : {a b c d : Obj Sets } ( f : Hom Sets a c ) ( g : Hom Sets b d ) → Hom Sets ( a ⊗ b ) ( c ⊗ d )
      _□_ f g = FMap (m-bi M) ( f , g )
      φ : {x : Obj (Sets × Sets) } → Hom Sets (FObj (Functor● Sets Sets MonoidalSets F) x) (FObj (Functor⊗ Sets Sets MonoidalSets F) x)
      φ z = HaskellMonoidalFunctor.φ mf z
      comm00 : {a b :  Obj (Sets × Sets)} { f : Hom (Sets × Sets) a b}  (x : ( FObj F (proj₁ a) * FObj F (proj₂ a)) ) →
         (Sets [ FMap (Functor⊗ Sets Sets MonoidalSets F) f o φ ]) x ≡ (Sets [ φ o FMap (Functor● Sets Sets MonoidalSets F) f ]) x
      comm00 {a} {b} {(f , g)} (x , y) = begin
                 (FMap (Functor⊗ Sets Sets MonoidalSets F) (f , g) ) (φ  (x , y))
             ≡⟨⟩
                 (FMap F ( f □ g ) ) (φ  (x , y))
             ≡⟨⟩
                 FMap F ( map f g ) (φ  (x , y))
             ≡⟨ IsHaskellMonoidalFunctor.natφ ismf ⟩
                 φ (  FMap F  f x , FMap F g  y )
             ≡⟨⟩
                 φ ( (  FMap F  f □ FMap F g ) (x , y) )
             ≡⟨⟩
                 φ ((FMap (Functor● Sets Sets MonoidalSets F) (f , g) ) (x , y) )
             ∎ 
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
      comm0 : {a b : Obj (Sets × Sets)} { f : Hom (Sets × Sets) a b} → Sets [ Sets [ FMap (Functor⊗ Sets Sets MonoidalSets F) f o φ  ]
        ≈ Sets [ φ  o FMap (Functor● Sets Sets MonoidalSets F) f ] ]
      comm0 {a} {b} {f} =  extensionality Sets ( λ (x : ( FObj F (proj₁ a) * FObj F (proj₂ a)) ) → comm00 x )
      comm10 :  {a b c : Obj Sets} → (x : ((FObj F a ⊗ FObj F b) ⊗ FObj F c) ) → (Sets [ φ  o Sets [ id1 Sets (FObj F a) □ φ  o Iso.≅→ (mα-iso isM) ] ]) x ≡
                (Sets [ FMap F (Iso.≅→ (mα-iso isM)) o Sets [ φ  o φ  □ id1 Sets (FObj F c) ] ]) x
      comm10 {x} {y} {f} ((a , b) , c ) = begin
                  φ  (( id1 Sets (FObj F x) □ φ  ) ( ( Iso.≅→ (mα-iso isM) ) ((a , b) , c)))
               ≡⟨⟩
                  φ  ( a , φ  (b , c)) 
               ≡⟨ IsHaskellMonoidalFunctor.assocφ ismf ⟩
                 ( FMap F (Iso.≅→ (mα-iso isM))) (φ (( φ  (a , b)) , c ))
               ≡⟨⟩
                 ( FMap F (Iso.≅→ (mα-iso isM))) (φ (( φ  □  id1 Sets (FObj F f) ) ((a , b) , c)))
             ∎
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
      comm1 : {a b c : Obj Sets} → Sets [ Sets [ φ 
           o Sets [  (id1 Sets (FObj F a) □ φ ) o Iso.≅→ (mα-iso isM) ] ]
        ≈ Sets [ FMap F (Iso.≅→ (mα-iso isM)) o Sets [ φ  o  (φ  □ id1 Sets (FObj F c)) ] ] ]
      comm1 {a} {b} {c} =  extensionality Sets ( λ x  → comm10 x )
      comm20 : {a b : Obj Sets} ( x : FObj F a * One )  → (  Sets [
         FMap F (Iso.≅→ (mρ-iso isM)) o Sets [ φ  o
             FMap (m-bi MonoidalSets) (id1 Sets (FObj F a) , (λ _ → unit )) ] ] ) x  ≡ Iso.≅→ (mρ-iso isM) x
      comm20 {a} {b} (x , OneObj ) =  begin 
                 (FMap F (Iso.≅→ (mρ-iso isM))) ( φ  ( x , unit ) )
               ≡⟨ IsHaskellMonoidalFunctor.idrφ ismf ⟩
                 x
               ≡⟨⟩
                 Iso.≅→ (mρ-iso isM) ( x , OneObj )
             ∎ 
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
      comm2 : {a b : Obj Sets} → Sets [ Sets [
         FMap F (Iso.≅→ (mρ-iso isM)) o Sets [ φ  o
             FMap (m-bi MonoidalSets) (id1 Sets (FObj F a) , (λ _ → unit )) ] ] ≈ Iso.≅→ (mρ-iso isM) ]
      comm2 {a} {b} =  extensionality Sets ( λ x  → comm20 {a} {b} x )
      comm30 : {a b : Obj Sets} ( x : One * FObj F b )  → (  Sets [
         FMap F (Iso.≅→ (mλ-iso isM)) o Sets [ φ  o
             FMap (m-bi MonoidalSets) ((λ _ → unit ) , id1 Sets (FObj F b) ) ] ] ) x  ≡ Iso.≅→ (mλ-iso isM) x
      comm30 {a} {b} ( OneObj , x) =  begin 
                 (FMap F (Iso.≅→ (mλ-iso isM))) ( φ  ( unit , x ) )
               ≡⟨ IsHaskellMonoidalFunctor.idlφ ismf ⟩
                 x
               ≡⟨⟩
                 Iso.≅→ (mλ-iso isM) (  OneObj , x )
             ∎ 
           where
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
      comm3 : {a b : Obj Sets} → Sets [ Sets [ FMap F (Iso.≅→ (mλ-iso isM)) o
        Sets [ φ  o FMap (m-bi MonoidalSets) ((λ _ → unit ) , id1 Sets (FObj F b)) ] ] ≈ Iso.≅→ (mλ-iso isM) ]
      comm3 {a} {b} =  extensionality Sets ( λ x  → comm30 {a} {b} x )

-- end
