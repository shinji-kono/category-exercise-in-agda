module HomReasoning  where 

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

open import Category -- https://github.com/konn/category-agda
open import Level
open Functor

--        F(f)
--   F(a) ---→ F(b)
--    |          |
--    |t(a)      |t(b)    G(f)t(a) = t(b)F(f)
--    |          |
--    v          v
--   G(a) ---→ G(b)
--        G(f)

record IsNTrans {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (D : Category c₁ c₂ ℓ) (C : Category c₁′ c₂′ ℓ′)
                 ( F G : Functor D C )
                 (TMap : (A : Obj D) → Hom C (FObj F A) (FObj G A))
                 : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    commute : {a b : Obj D} {f : Hom D a b} 
      → C [ C [ (  FMap G f ) o  ( TMap a ) ]  ≈ C [ (TMap b ) o  (FMap F f)  ] ]

record NTrans {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (domain : Category c₁ c₂ ℓ) (codomain : Category c₁′ c₂′ ℓ′) 
     (F G : Functor domain codomain )
       : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    TMap :  (A : Obj domain) → Hom codomain (FObj F A) (FObj G A)
    isNTrans : IsNTrans domain codomain F G TMap


module ≈-Reasoning {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) where
  open import Relation.Binary

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

  open NTrans 
  nat : { c₁ c₂ ℓ : Level}  {A : Category c₁ c₂ ℓ}  { c₁′ c₂′ ℓ′ : Level}  {D : Category c₁′ c₂′ ℓ′} 
         {a b : Obj D} {f : Hom D a b}  {F G : Functor D A }
      →  (η : NTrans D A F G )
      →   A [ A [ FMap G f  o  TMap η a ]  ≈ A [ TMap η b  o  FMap F f ] ]
  nat η  =  IsNTrans.commute ( isNTrans η  )

  nat1 : { c₁ c₂ ℓ : Level}  {A : Category c₁ c₂ ℓ}  { c₁′ c₂′ ℓ′ : Level}  {D : Category c₁′ c₂′ ℓ′} 
         {a b : Obj D}   {F G : Functor D A }
      →  (η : NTrans D A F G ) → (f : Hom D a b)
      →   A [ A [ FMap G f  o  TMap η a ]  ≈ A [ TMap η b  o  FMap F f ] ]
  nat1 η f =  IsNTrans.commute ( isNTrans η  )

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


  ---
  -- to avoid assoc storm, flatten composition according to the template
  --

  data MP : { a b : Obj A } ( x : Hom A a b ) → Set (c₁ ⊔  c₂  ⊔ ℓ ) where
            am  : { a b : Obj A } → (x : Hom A a b )   →  MP x
            _repl_by_  : { a b : Obj A } → (x y : Hom A a b ) → x ≈ y →  MP y
            _∙_ : { a b c : Obj A } {x : Hom A b c } { y : Hom A a b } →  MP x →  MP  y → MP  ( x o y )

  open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 

  mp-before : { a b : Obj A } { f : Hom A a b } → MP f → Hom A a b
  mp-before (am x) = x
  mp-before (x repl y by x₁) = x
  mp-before (m ∙ m₁) = mp-before m o mp-before m₁

  mp-after : { a b : Obj A } { f : Hom A a b } → MP f → Hom A a b
  mp-after (am x) = x
  mp-after (x repl y by x₁) = y
  mp-after (m ∙ m₁) = mp-before m o mp-before m₁

  mp≈ : { a b : Obj A } { f g : Hom A a b } → (m : MP f ) → mp-before m ≈ mp-after m
  mp≈ {a} {b} {f} {g} (am x) = refl-hom
  mp≈ {a} {b} {f} {g} (x repl y by x=y ) = x=y
  mp≈ {a} {b} {f} {g} (m ∙ m₁) = resp refl-hom refl-hom  

  mpf : {a b c : Obj A } {y : Hom A b c } → (m : MP y ) → Hom A a b → Hom A a c
  mpf (am x) y = x o y
  mpf (x repl y by eq ) z = y o z
  mpf (m ∙ m₁) y = mpf m ( mpf m₁ y )

  mp-flatten : {a b : Obj A } {x : Hom A a b } → (m : MP x ) → Hom A a b
  mp-flatten  m = mpf m (id _)

  mpl1 : {a b c : Obj A } → Hom A b c → {y : Hom A a b } → MP y → Hom A a c
  mpl1 x (am y) = x o y
  mpl1 x (z repl y by eq ) = x o y
  mpl1 x (y ∙ y1) = mpl1 ( mpl1 x y ) y1

  mpl : {a b c : Obj A } {x : Hom A b c } {z : Hom A a b } → MP x → MP z  → Hom A a c
  mpl (am x)  m = mpl1 x m
  mpl (y repl x by eq ) m  = mpl1 x m
  mpl (m ∙ m1) m2 = mpl m (m1 ∙ m2)

  mp-flattenl : {a b : Obj A } {x : Hom A a b } → (m : MP x ) → Hom A a b
  mp-flattenl m = mpl m (am (id _))

  _⁻¹ : {a b : Obj A } ( f : Hom A a b ) → Set c₂
  _⁻¹ {a} {b} f = Hom A b a

  test1 : {a b c : Obj A } ( f : Hom A b c ) ( g : Hom A a b ) → ( _⁻¹ : {a b : Obj A } ( f : Hom A a b ) → Hom A b a )   → Hom A c a
  test1 f g _⁻¹ = mp-flattenl ((am (g ⁻¹) ∙ am (f ⁻¹) ) ∙ ( (am f ∙ am g) ∙ am ((f o g) ⁻¹ )))

  test2 : {a b c : Obj A } ( f : Hom A b c ) ( g : Hom A a b ) → ( _⁻¹ : {a b : Obj A } ( f : Hom A a b ) → Hom A b a )  → test1 f g  _⁻¹ ≈  ((((g ⁻¹ o f ⁻¹ )o f ) o g ) o  (f o g) ⁻¹  ) o id  _
  test2 f g  _⁻¹ = refl-hom

  test3 : {a b c : Obj A } ( f : Hom A b c ) ( g : Hom A a b )  →  ( _⁻¹ : {a b : Obj A } ( f : Hom A a b ) → Hom A b a ) → Hom A c a
  test3 f g _⁻¹ = mp-flatten ((am (g ⁻¹) ∙ am (f ⁻¹) ) ∙ ( (am f ∙ am g) ∙ am ((f o g) ⁻¹ )))

  test4 : {a b c : Obj A } ( f : Hom A b c ) ( g : Hom A a b )  →  ( _⁻¹ : {a b : Obj A } ( f : Hom A a b ) → Hom A b a ) → test3 f g  _⁻¹ ≈ g ⁻¹ o (f ⁻¹ o (f o (g o ((f o g) ⁻¹ o id _))))
  test4 f g _⁻¹ = refl-hom

  o-flatten : {a b : Obj A } {x : Hom A a b } → (m : MP x ) → x ≈ mp-flatten m
  o-flatten (am y) = sym-hom (idR )
  o-flatten (y repl x by eq)  = sym-hom (idR )
  o-flatten (am x ∙ q) = resp ( o-flatten q ) refl-hom 
  o-flatten ((y repl x by eq)  ∙ q) = resp ( o-flatten q ) refl-hom 
  --  d <- c <- b <- a  ( p ∙ q ) ∙ r   ,    ( x o y ) o z
  o-flatten {a} {d} (_∙_ {a} {b} {d} {xy} {z} (_∙_ {b} {c} {d} {x} {y} p q) r) =
     lemma9 _ _ _ ( o-flatten {b} {d} {x o y } (p ∙ q )) ( o-flatten {a} {b} {z} r ) where
           mp-cong : { a b c : Obj A } → {p : Hom A b c} {q r : Hom A a b} → (P : MP p)  → q ≈ r → mpf P q ≈ mpf P r
           mp-cong (am x) q=r = resp q=r refl-hom 
           mp-cong (y repl x by eq)  q=r = resp q=r refl-hom 
           mp-cong (P ∙ P₁) q=r = mp-cong P ( mp-cong P₁ q=r )
           mp-assoc : {a b c d : Obj A } {p : Hom A c d} {q : Hom A b c} {r : Hom A a b} → (P : MP p)  → mpf P q o r ≈ mpf P (q o r )
           mp-assoc (am x) = sym-hom assoc
           mp-assoc (y repl x by eq ) = sym-hom assoc
           mp-assoc {_} {_} {_} {_} {p} {q} {r} (P ∙ P₁) = begin
               mpf P (mpf  P₁ q) o r ≈⟨ mp-assoc P ⟩
               mpf P (mpf P₁ q o r)  ≈⟨ mp-cong P (mp-assoc P₁)  ⟩ mpf P ((mpf  P₁) (q o r)) 
            ∎ 
           lemma9 : (x : Hom A c d) (y : Hom A b c) (z : Hom A a b) →  x o y ≈ mpf p (mpf q (id _))
               → z ≈ mpf r (id _)
               →  (x o y) o z ≈ mp-flatten ((p ∙ q) ∙ r)
           lemma9 x y z t s = begin
               (x o y) o z                    ≈⟨ resp refl-hom t ⟩
               mpf p (mpf q (id _)) o z ≈⟨ mp-assoc p ⟩
               mpf p (mpf q (id _) o z)          ≈⟨ mp-cong p (mp-assoc q ) ⟩
               mpf p (mpf q ((id _) o z))        ≈⟨ mp-cong p (mp-cong q idL) ⟩
               mpf p (mpf q z)              ≈⟨ mp-cong p (mp-cong q s) ⟩
               mpf p (mpf q (mpf r (id _)))
            ∎ 

-- an example

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
