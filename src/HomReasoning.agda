{-# OPTIONS --cubical-compatible --safe #-}
module HomReasoning  where 

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

open import Level
open import Category

module ≈-Reasoning {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) where
  open import Relation.Binary
  open Functor

  _o_ :  {a b c : Obj A } ( x : Hom A a b ) ( y : Hom A c a ) → Hom A c b
  x o y = A [ x o y ]

  _≈_ :  {a b : Obj A }   → Rel (Hom A a b) ℓ
  x ≈ y = A [ x ≈ y ]

  infixr 9 _o_
  infix  4 _≈_

  refl-hom :   {a b : Obj A } { x : Hom A a b }  →  x ≈ x 
  refl-hom =  IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory A ))

  trans-hom :   {a b : Obj A } { x y z : Hom A a b }  →
         x ≈ y →  y ≈ z  →  x ≈ z 
  trans-hom b c = ( IsEquivalence.trans (IsCategory.isEquivalence  ( Category.isCategory A ))) b c

  -- some short cuts

  car : {a b c : Obj A } {x y : Hom A a b } { f : Hom A c a } →
          x ≈ y  → ( x o f ) ≈ ( y  o f )
  car  eq = ( IsCategory.o-resp-≈ ( Category.isCategory A )) ( refl-hom  ) eq

  car1 : { c₁ c₂ ℓ : Level}  (A : Category c₁ c₂ ℓ) {a b c : Obj A } {x y : Hom A a b } { f : Hom A c a } →
          A [ x ≈ y ] → A [ A [  x o f ] ≈ A [  y  o f  ] ]
  car1 A  eq = ( IsCategory.o-resp-≈ ( Category.isCategory A )) ( IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory A ))  ) eq

  cdr : {a b c : Obj A } {x y : Hom A a b } { f : Hom A b c } →
          x ≈ y  →  f o x  ≈  f  o y 
  cdr eq = ( IsCategory.o-resp-≈ ( Category.isCategory A )) eq (refl-hom  ) 

  cdr1 : { c₁ c₂ ℓ : Level}  (A : Category c₁ c₂ ℓ) {a b c : Obj A } {x y : Hom A a b } { f : Hom A b c } →
          A [ x ≈ y ] →  A [ A [ f o x ]  ≈  A [ f  o y  ] ]
  cdr1 A eq = ( IsCategory.o-resp-≈ ( Category.isCategory A )) eq (IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory A ))  ) 

  id :  (a  : Obj A ) →  Hom A a a
  id a =  (Id {_} {_} {_} {A} a) 

  idL :  {a b : Obj A } { f : Hom A a b } →  id b o f  ≈ f 
  idL =  IsCategory.identityL (Category.isCategory A)

  idR :  {a b : Obj A } { f : Hom A a b } →  f o id a  ≈ f 
  idR =  IsCategory.identityR (Category.isCategory A)

  sym :  {a b : Obj A } { f g : Hom A a b } →  f ≈ g  →  g ≈ f
  sym   =  IsEquivalence.sym (IsCategory.isEquivalence (Category.isCategory A))

  sym-hom = sym

  -- working on another cateogry
  idL1 :  { c₁ c₂ ℓ : Level}  (A : Category c₁ c₂ ℓ) {a b : Obj A } { f : Hom A b a } →  A [ A [ Id {_} {_} {_} {A} a o f ] ≈ f  ]
  idL1 A =  IsCategory.identityL (Category.isCategory A)

  idR1 :  { c₁ c₂ ℓ : Level}  (A : Category c₁ c₂ ℓ) {a b : Obj A } { f : Hom A a b } →  A [ A [ f o Id {_} {_} {_} {A} a ] ≈ f  ]
  idR1 A =  IsCategory.identityR (Category.isCategory A)

  open import Relation.Binary.PropositionalEquality using ( _≡_ )
  ≈←≡ : {a b : Obj A } { x y : Hom A a b } →  (x≈y : x ≡ y ) → x ≈ y
  ≈←≡  _≡_.refl = refl-hom

-- Ho← to prove this?
--  ≡←≈ : {a b : Obj A } { x y : Hom A a b } →  (x≈y : x ≈ y ) → x ≡ y
--  ≡←≈  x≈y = irr x≈y

  ≡-cong : { c₁′ c₂′ ℓ′ : Level}  {B : Category c₁′ c₂′ ℓ′} {x y : Obj B } { a b : Hom B x y } {x' y' : Obj A }  →
             (f : Hom B x y → Hom A x' y' ) →  a ≡ b  → f a  ≈  f b
  ≡-cong f _≡_.refl =  ≈←≡ _≡_.refl

--  cong-≈ :  { c₁′ c₂′ ℓ′ : Level}  {B : Category c₁′ c₂′ ℓ′} {x y : Obj B } { a b : Hom B x y } {x' y' : Obj A }  → 
--             B [ a ≈ b ] → (f : Hom B x y → Hom A x' y' ) →  f a ≈ f b
--  cong-≈ eq f = {!!}

  assoc : {a b c d : Obj A }  {f : Hom A c d}  {g : Hom A b c} {h : Hom A a b}
                                  →   f o ( g o h )  ≈  ( f o g ) o h 
  assoc =  IsCategory.associative (Category.isCategory A)

  -- working on another cateogry
  assoc1 : { c₁ c₂ ℓ : Level}  (A : Category c₁ c₂ ℓ)   {a b c d : Obj A }  {f : Hom A c d}  {g : Hom A b c} {h : Hom A a b}
                                  →  A [ A [ f o ( A [ g o h ] ) ] ≈ A [ ( A [ f o g ] ) o h ] ]
  assoc1 A =  IsCategory.associative (Category.isCategory A)

  distr : { c₁ c₂ ℓ : Level}  {A : Category c₁ c₂ ℓ} 
         { c₁′ c₂′ ℓ′ : Level}  {D : Category c₁′ c₂′ ℓ′} (T : Functor D A) →  {a b c : Obj D} {g : Hom D b c} { f : Hom D a b }
     →   A [ FMap T ( D [ g o f ]  )  ≈  A [ FMap T g o FMap T f ] ]
  distr T = IsFunctor.distr ( isFunctor T )

  resp : {a b c : Obj A} {f g : Hom A a b} {h i : Hom A b c} → f ≈ g → h ≈ i → (h o f) ≈ (i o g)
  resp = IsCategory.o-resp-≈ (Category.isCategory A)

  fcong :  { c₁ c₂ ℓ : Level}  {C : Category c₁ c₂ ℓ}
         { c₁′ c₂′ ℓ′ : Level}  {D : Category c₁′ c₂′ ℓ′} {a b : Obj C} {f g : Hom C a b} → (T : Functor C D) → C [ f ≈ g ] → D [ FMap T f ≈ FMap T g ]
  fcong T = IsFunctor.≈-cong (isFunctor T) 

  infix  3 _∎
  infixr 2 _≈⟨_⟩_ _≈⟨⟩_ 
  infixr 2 _≈↑⟨_⟩_ 
  infix  1 begin_

------ If we have this, for example, as an axiom of a category, we can use ≡-Reasoning directly
--  ≈-to-≡ : {a b : Obj A } { x y : Hom A a b }  → A [ x ≈  y ] → x ≡ y
--  ≈-to-≡ refl-hom = refl

  data _IsRelatedTo_ { a b : Obj A } ( x y : Hom A a b ) :
                     Set (suc (c₁ ⊔ c₂ ⊔ ℓ ))  where
      relTo : (x≈y : x ≈ y ) → x IsRelatedTo y

  begin_ : { a b : Obj A } { x y : Hom A a b } →
           x IsRelatedTo y → x ≈ y 
  begin relTo x≈y = x≈y

  _≈⟨_⟩_ : { a b : Obj A } ( x : Hom A a b ) → { y z : Hom A a b } → 
           x ≈ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≈⟨ x≈y ⟩ relTo y≈z = relTo (trans-hom x≈y y≈z)

  _≈↑⟨_⟩_ : { a b : Obj A } ( x : Hom A a b ) → { y z : Hom A a b } → 
           y ≈ x → y IsRelatedTo z → x IsRelatedTo z
  _ ≈↑⟨ y≈x ⟩ relTo y≈z = relTo (trans-hom ( sym y≈x ) y≈z)

  _≈⟨⟩_ : { a b : Obj A } ( x : Hom A a b ) → { y : Hom A a b } → x IsRelatedTo y → x IsRelatedTo y
  _ ≈⟨⟩ x∼y = x∼y

  _∎ : { a b : Obj A } ( x : Hom A a b ) → x IsRelatedTo x
  _∎ _ = relTo refl-hom


-- examples

Lemma61 : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) →
                 { a : Obj A } ( b : Obj A ) →
                 ( f : Hom A a b )
                      →  A [ A [ (Id {_} {_} {_} {A} b) o f ]  ≈ f ]
Lemma61 c b g = -- IsCategory.identityL (Category.isCategory c) 
  let open ≈-Reasoning (c) in begin  
          c [ ( Id {_} {_} {_} {c} b ) o g ]
     ≈⟨ IsCategory.identityL (Category.isCategory c) ⟩
          g
     ∎

Lemma62 : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) →
                 { a b : Obj A }  →
                 ( f g : Hom A a b )
                      →  A [ A [ (Id {_} {_} {_} {A} b) o f ]  ≈  A [ (Id {_} {_} {_} {A} b) o g ]  ]
                      →  A [ g ≈ f ]
Lemma62 A {a} {b} f g 1g=1f = let open  ≈-Reasoning A in
     begin  
          g
     ≈↑⟨ idL  ⟩
          id b o g
     ≈↑⟨ 1g=1f ⟩
          id b o f
     ≈⟨ idL  ⟩
          f
     ∎
