{-# OPTIONS --cubical-compatible  --safe #-}
module Definitions where

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

    open import Level
    open import Category
    open import HomReasoning

    open Functor

    id1 :   ∀{c₁ c₂ ℓ  : Level} (A : Category c₁ c₂ ℓ)  (a  : Obj A ) →  Hom A a a
    id1 A a =  (Id {_} {_} {_} {A} a)
    -- We cannot make A implicit

    --
    -- one to one (without naturality)
    --
    record Iso  {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ)
             (x y : Obj C )
            : Set ( suc  (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁)) where
       field
             ≅→ :  Hom C x y
             ≅← :  Hom C y x
             iso→  :  C [ C [ ≅← o ≅→  ] ≈  id1 C x ]
             iso←  :  C [ C [ ≅→ o ≅←  ] ≈  id1 C y ]

    ≡-iso : {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ) (x : Obj C ) → Iso C x x
    ≡-iso C x = record { ≅→ = id1 C _ ; ≅← = id1 C _ ; iso→  = ≈-Reasoning.idL C ; iso←  =  ≈-Reasoning.idL C }
    sym-iso : {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ) {x y : Obj C } → Iso C x y → Iso C y x
    sym-iso C i = record { ≅→ = Iso.≅← i  ; ≅← = Iso.≅→ i ; iso→  = Iso.iso← i ; iso←  =  Iso.iso→ i }

    -- Iso with cong
    --
    record IsoS {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ') (a b : Obj A) ( a' b' : Obj B )
              :  Set ( c₁  ⊔  c₂ ⊔ ℓ ⊔  c₁'  ⊔  c₂' ⊔ ℓ' ) where
          field
               ≅→ :  Hom A a b   → Hom B a' b'
               ≅← :  Hom B a' b' → Hom A a b
               iso→  : {f : Hom B a' b' }  → B [ ≅→ ( ≅← f) ≈ f ]
               iso←  : {f : Hom A a b }    → A [ ≅← ( ≅→ f) ≈ f ]
               cong→ : {f g : Hom A a b }  → A [ f ≈ g ] →  B [ ≅→ f ≈ ≅→ g ]
               cong← : {f g : Hom B a' b'} → B [ f ≈ g ] →  A [ ≅← f ≈ ≅← g ]

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

    ----
    -- C is locally small i.e. Hom C i j is a set c₁
    --
    open import Data.Product renaming (_×_ to _∧_) hiding (_<*>_)
    open  import  Relation.Binary.PropositionalEquality as EqR using (_≡_)
    record Small  {  c₁ c₂ ℓ : Level} (c : Level) ( C : Category c₁ c₂ ℓ ) : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c)) where
       field
         I : Set c
         hom→ : {i j : Obj C } →    Hom C i j →  I
         s-dom : I → Obj C
         s-dom-iso : {i j : Obj C } → { f : Hom C i j } → i ≡ s-dom (hom→ f)
         s-cod : I → Obj C
         s-cod-iso : {i j : Obj C } → { f : Hom C i j } → j ≡ s-cod (hom→ f)
         hom← :  ( f : I ) →  Hom C (s-dom f) (s-cod f)
         hom-iso : {i j : Obj C } →  { f : Hom C i j } →   C [ hom← ( hom→ f )  ≈ EqR.subst₂ (λ j k → Hom C j k) s-dom-iso s-cod-iso f ]
         hom-rev : { f : I } →   hom→ ( hom←   f )  ≡ f
         hom-inject  : {i j k l : Obj C } →  { f : Hom C i j } →  { g : Hom C k l } →  hom→ f ≡ hom→ g →  (i ≡ k ) ∧  (j ≡ l) 
         -- this can be proved as subst-eq refl refl refl refl = refl-hom, if we have --with-K
         subst-eq : {a b c d : Obj C} → (a=b a=b' : a ≡ b ) → (c=d c=d' : c ≡ d )
            → {f : Hom C a c} 
            → C [ EqR.subst₂ (λ j k → Hom C j k ) a=b c=d f ≈  EqR.subst₂ (λ j k → Hom C j k ) a=b' c=d' f  ] 
         -- we cannot remove ≡←≈ in easy way, because it interferes with Sets and Yoneda Functor
         ≡←≈ : {i j : Obj C } →  { f g : Hom C i j } →  C [ f ≈ g ] →   f ≡ g
         -- we also having troube with cong below, it does not satisfy the resp
       hom→cong : {i j : Obj C } →  { f g : Hom C i j } → C [ f ≈ g ] → hom→ f ≡ hom→ g
       hom→cong {i} {j} {f} {g} f=g = EqR.cong hom→ (≡←≈ f=g)

    record IsUniversalMapping  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                     ( U : Functor B A )
                     ( F : Obj A → Obj B )
                     ( η : (a : Obj A) → Hom A a ( FObj U (F a) ) )
                     ( _* : { a : Obj A}{ b : Obj B} → ( Hom A a (FObj U b) ) →  Hom B (F a ) b )
                     : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
       field
           universalMapping :   {a : Obj A} { b : Obj B } → { f : Hom A a (FObj U b) } →
                         A [ A [ FMap U ( f * ) o  η a ]  ≈ f ]
           uniquness :   {a : Obj A} { b : Obj B } → { f : Hom A a (FObj U b) } → { g :  Hom B (F a) b } →
                         A [ A [ FMap U g o  η a ]  ≈ f ] → B [ f * ≈ g ]

    record UniversalMapping  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                     ( U : Functor B A )
                     : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
        infixr 11 _*
        field
           F : Obj A → Obj B
           η : (a : Obj A) → Hom A a ( FObj U (F a) )
           _* :  { a : Obj A}{ b : Obj B} → ( Hom A a (FObj U b) ) →  Hom B (F a ) b
           isUniversalMapping : IsUniversalMapping A B U F η _*

    record coIsUniversalMapping  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                     ( F : Functor A B )
                     ( U : Obj B → Obj A )
                     ( ε : (b : Obj B) → Hom B ( FObj F (U b) ) b )
                     ( _* : { b : Obj B}{ a : Obj A} → ( Hom B (FObj F a) b ) →  Hom A a (U b ) )
                     : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
       field
           couniversalMapping :   {b : Obj B} { a : Obj A } → { f : Hom B (FObj F a) b } →
                         B [ B [ ε b o FMap F ( f * )  ]  ≈ f ]
           uniquness :   {b : Obj B} { a : Obj A } → { f : Hom B (FObj F a) b } → { g :  Hom A a (U b) } →
                         B [ B [ ε b o FMap F g ]  ≈ f ] → A [ f * ≈ g ]

    record coUniversalMapping  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                     ( F : Functor A B )
                     : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
        infixr 11 _*
        field
           U : Obj B → Obj A
           ε : (b : Obj B) → Hom B ( FObj F (U b) ) b
           _* :  { b : Obj B}{ a : Obj A} → ( Hom B (FObj F a) b ) →  Hom A a (U b )
           iscoUniversalMapping : coIsUniversalMapping A B F U ε _*

    open NTrans
    open import Category.Cat
    record IsAdjunction  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                     ( U : Functor B A )
                     ( F : Functor A B )
                     ( η : NTrans A A identityFunctor ( U ○  F ) )
                     ( ε : NTrans B B  ( F ○  U ) identityFunctor )
                     : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
       field
           adjoint1 :   { b : Obj B } →
                         A [ A [ ( FMap U ( TMap ε b ))  o ( TMap η ( FObj U b )) ]  ≈ id1 A (FObj U b) ]
           adjoint2 :   {a : Obj A} →
                         B [ B [ ( TMap ε ( FObj F a ))  o ( FMap F ( TMap η a )) ]  ≈ id1 B (FObj F a) ]

    record Adjunction {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                     : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
        field
           U : Functor B A
           F : Functor A B
           η : NTrans A A identityFunctor ( U ○  F )
           ε : NTrans B B  ( F ○  U ) identityFunctor
           isAdjunction : IsAdjunction A B U F η ε
        U-functor =  U
        F-functor =  F
        Eta = η
        Epsiron = ε


    record IsMonad {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ)
                     ( T : Functor A A )
                     ( η : NTrans A A identityFunctor T )
                     ( μ : NTrans A A (T ○ T) T)
                     : Set (suc (c₁ ⊔ c₂ ⊔ ℓ )) where
       field
          assoc  : {a : Obj A} → A [ A [ TMap μ a o TMap μ ( FObj T a ) ] ≈  A [  TMap μ a o FMap T (TMap μ a) ] ]
          unity1 : {a : Obj A} → A [ A [ TMap μ a o TMap η ( FObj T a ) ] ≈ Id {_} {_} {_} {A} (FObj T a) ]
          unity2 : {a : Obj A} → A [ A [ TMap μ a o (FMap T (TMap η a ))] ≈ Id {_} {_} {_} {A} (FObj T a) ]

    record Monad {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ)
           : Set (suc (c₁ ⊔ c₂ ⊔ ℓ )) where
      field
        T : Functor A A
        η : NTrans A A identityFunctor T
        μ : NTrans A A (T ○ T) T
        isMonad : IsMonad A T η μ
         -- g ○ f = μ(c) T(g) f
      join : { a b : Obj A } → { c : Obj A } →
                          ( Hom A b ( FObj T c )) → (  Hom A a ( FObj T b)) → Hom A a ( FObj T c )
      join {_} {_} {c} g f = A [ TMap μ c  o A [ FMap T g o f ] ]

    record IsCoMonad {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ)
                     ( S : Functor A A )
                     ( ε : NTrans A A S identityFunctor )
                     ( δ : NTrans A A S (S ○ S) )
                     : Set (suc (c₁ ⊔ c₂ ⊔ ℓ )) where
       field
          assoc  : {a : Obj A} → A [ A [ TMap δ (FObj S a)  o TMap δ a ] ≈  A [ FMap S (TMap δ a) o TMap δ a ] ]
          unity1 : {a : Obj A} → A [ A [ TMap ε ( FObj S a ) o TMap δ a ] ≈ Id {_} {_} {_} {A} (FObj S a) ]
          unity2 : {a : Obj A} → A [ A [ (FMap S (TMap ε a )) o TMap δ a ] ≈ Id {_} {_} {_} {A} (FObj S a) ]

    record coMonad {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (S : Functor A A)
           : Set (suc (c₁ ⊔ c₂ ⊔ ℓ )) where
      field
        ε : NTrans A A S identityFunctor
        δ : NTrans A A S (S ○ S)
        isCoMonad : IsCoMonad A S ε δ
         -- g ○ f = g S(f) δ(a)
      coJoin : { a b : Obj A } → { c : Obj A } →
                          ( Hom A  (FObj S b ) c ) → (  Hom A ( FObj S a) b ) → Hom A ( FObj S a ) c
      coJoin {a} {_} {_} g f = A [ A [ g o FMap S f ] o TMap δ a ]

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


    Functor*Nat :  {c₁ c₂ ℓ c₁' c₂' ℓ' c₁'' c₂'' ℓ'' : Level} (A : Category c₁ c₂ ℓ) {B : Category c₁' c₂' ℓ'} (C : Category c₁'' c₂'' ℓ'')
        (F : Functor B C) → { G H : Functor A B } → ( n : NTrans A B G H ) → NTrans A C (F ○  G) (F ○ H)
    Functor*Nat A {B} C F {G} {H} n = record {
           TMap  = λ a → FMap F (TMap n a)
           ; isNTrans = record {
                commute = commute
           }
        } where
             commute : {a b : Obj A} {f : Hom A a b}
                → C [ C [ (FMap F ( FMap H f )) o  ( FMap F (TMap n a)) ]  ≈ C [ (FMap F (TMap n b )) o  (FMap F (FMap G f))  ] ]
             commute  {a} {b} {f}  = let open ≈-Reasoning (C) in
                begin
                   (FMap F ( FMap H f )) o  ( FMap F (TMap n a))
                ≈⟨ sym (distr F) ⟩
                   FMap F ( B [ (FMap H f)  o TMap n a ])
                ≈⟨ IsFunctor.≈-cong (isFunctor F) ( nat n ) ⟩
                   FMap F ( B [ (TMap n b ) o FMap G f ] )
                ≈⟨ distr F ⟩
                   (FMap F (TMap n b )) o  (FMap F (FMap G f))
                ∎

    Nat*Functor :  {c₁ c₂ ℓ c₁' c₂' ℓ' c₁'' c₂'' ℓ'' : Level} (A : Category c₁ c₂ ℓ) {B : Category c₁' c₂' ℓ'} (C : Category c₁'' c₂'' ℓ'')
        { G H : Functor B C } → ( n : NTrans B C G H ) → (F : Functor A B) → NTrans A C (G ○  F) (H ○ F)
    Nat*Functor A {B} C {G} {H} n F = record {
           TMap  = λ a → TMap n (FObj F a)
           ; isNTrans = record {
                commute = commute
           }
        } where
             commute : {a b : Obj A} {f : Hom A a b}
                → C [ C [ ( FMap H (FMap F f )) o  ( TMap n (FObj F a)) ]  ≈ C [ (TMap n (FObj F b )) o  (FMap G (FMap F f))  ] ]
             commute  {a} {b} {f}  =  IsNTrans.commute ( isNTrans n)

    record SObj {c₁ c₂ ℓ ℓ' : Level} (A : Category c₁ c₂ ℓ) (P : Obj A → Set ℓ' ) :  Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ ℓ')) where
        field
           s : Obj A
           p : P s

    FullSubCategory : {c₁ c₂ ℓ ℓ' : Level} (A : Category c₁ c₂ ℓ) (P : Obj A → Set ℓ' ) → Category (suc c₁ ⊔ suc c₂ ⊔ suc ℓ ⊔ suc ℓ')  c₂ ℓ
    FullSubCategory A P = record {
           Obj = SObj A P
         ; Hom = λ a b → Hom A (SObj.s a) (SObj.s b)  -- full
         ; _o_ = λ f g → A [ f o g ]
         ; _≈_ = λ f g → A [ f ≈ g ]
         ; Id = λ {a} → id1 A (SObj.s a)
         ; isCategory = record {
                isEquivalence = IsCategory.isEquivalence (Category.isCategory A )
              ; identityL = idL
              ; identityR = idR
              ; o-resp-≈ = resp
              ; associative = assoc
           }
      } where open ≈-Reasoning A

    InclusiveFunctor : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (P : Obj A → Set ℓ ) → Functor (FullSubCategory A P) A
    InclusiveFunctor A P = record {
         FObj = λ x → SObj.s x
       ; FMap = λ {a} {b} f → f
       ; isFunctor = record  {
              ≈-cong = λ eq → eq
            ; identity = refl-hom
            ; distr = refl-hom
          }
       }  where open ≈-Reasoning A

    -- T ≃  (U_R ○ F_R)
    -- μ = U_R ε F_R
    --      nat-ε
    --      nat-η     -- same as η but has different types

    record MResolution {c₁ c₂ ℓ  c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) ( B : Category c₁' c₂' ℓ' ) ( M : Monad A )
       : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
         field
          UR : Functor B A
          FR : Functor A B
          ηR : NTrans A A identityFunctor  ( UR ○ FR )
          εR : NTrans B B ( FR ○ UR ) identityFunctor
          μR : NTrans A A ( (UR ○ FR)  ○ ( UR ○ FR )) ( UR ○ FR  )
          Adj : IsAdjunction A B UR FR ηR εR
          T=UF  :  Monad.T M ≃  (UR ○ FR)
          μ=UεF : {x : Obj A } → A [ TMap μR x ≈ FMap UR ( TMap εR ( FObj FR x ) ) ]
                  -- ηR=η  : {x : Obj A } → A [ TMap ηR x  ≈  TMap η x ] -- We need T → UR FR conversion
                  -- μR=μ  : {x : Obj A } → A [ TMap μR x  ≈  TMap μ x ]


    --
    --         e             f          e
    --    c  -------→ a ---------→ b -------→ c
    --    ↑        .    ---------→   .        |
    --    |      .            g        .      |
    --    |k   .                         .    | k
    --    |  . h                        h  .  ↓
    --    d                                   d

    record IsEqualizer { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {c a b : Obj A} (e : Hom A c a) (f g : Hom A a b)  : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
       field
          fe=ge : A [ A [ f o e ] ≈ A [ g o e ] ]
          k : {d : Obj A}  (h : Hom A d a) → A [ A [ f  o  h ] ≈ A [ g  o h ] ] → Hom A d c
          ek=h : {d : Obj A}  → ∀ {h : Hom A d a} →  {eq : A [ A [ f  o  h ] ≈ A [ g  o h ] ] } →  A [ A [ e  o k {d} h eq ] ≈ h ]
          uniqueness : {d : Obj A} →  ∀ {h : Hom A d a} →  {eq : A [ A [ f  o  h ] ≈ A [ g  o h ] ] } →  {k' : Hom A d c } →
                  A [ A [ e  o k' ] ≈ h ] → A [ k {d} h eq  ≈ k' ]
       equalizer1 : Hom A c a
       equalizer1 = e

    record Equalizer { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) {a b : Obj A} (f g : Hom A a b) : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
       field
            equalizer-c : Obj A
            equalizer : Hom A equalizer-c a
            isEqualizer : IsEqualizer A equalizer f g

    record IsCoEqualizer { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {c a b : Obj A} (e : Hom A b c) (f g : Hom A a b)  : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
       field
          ef=eg : A [ A [ e o f ] ≈ A [ e o g ] ]
          k : {d : Obj A}  (h : Hom A b d) → A [ A [ h  o  f ] ≈ A [ h  o g ] ] → Hom A c d
          ke=h : {d : Obj A}  → ∀ {h : Hom A b d } →  {eq : A [ A [ h  o  f ] ≈ A [ h  o g ] ] } →  A [ A [ k {d} h eq o e ] ≈ h ]
          uniqueness : {d : Obj A} →  ∀ {h : Hom A b d } →  {eq : A [ A [ h  o  f ] ≈ A [ h  o g ] ] } →  {k' : Hom A c d} →
                  A [ A [ k' o e  ] ≈ h ] → A [ k {d} h eq  ≈ k' ]
       equalizer1 : Hom A b c
       equalizer1 = e

    record CoEqualizer { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) {a b : Obj A} (f g : Hom A a b) : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
       field
            coEqualizer-c : Obj A
            coEqualizer : Hom A coEqualizer-c a
            isCoEqualizer : IsEqualizer A coEqualizer f g

    --
    -- Product
    --
    --                c
    --        f       |        g
    --                |f×g
    --                v
    --    a <-------- ab ---------→ b
    --         π1            π2


    record IsProduct { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  (a b ab : Obj A)
          ( π1 : Hom A ab a )
          ( π2 : Hom A ab b )
                : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
       field
          _×_ : {c : Obj A} ( f : Hom A c a ) → ( g : Hom A c b ) → Hom A c ab
          π1fxg=f : {c : Obj A} { f : Hom A c a } → { g : Hom A c b } → A [ A [ π1  o ( f × g )  ] ≈  f ]
          π2fxg=g : {c : Obj A} { f : Hom A c a } → { g : Hom A c b } → A [ A [ π2  o ( f × g )  ] ≈  g ]
          uniqueness : {c : Obj A} { h : Hom A c ab }  → A [  ( A [ π1  o h  ] ) × ( A [ π2  o h  ] ) ≈  h ]
          ×-cong : {c : Obj A} { f f' : Hom A c a } → { g g' : Hom A c b } → A [ f ≈ f' ] → A [ g ≈ g' ] → A [ f × g ≈ f' × g' ]

    record Product { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) ( a b : Obj A )
                : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
       field
          product : Obj A
          π1 : Hom A product a
          π2 : Hom A product b
          isProduct : IsProduct A a b product π1 π2

    record IsCoProduct { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  (a b ab : Obj A)
          ( κ1 : Hom A a ab  )
          ( κ2 : Hom A b ab  )
                : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
       field
          _+_ : {c : Obj A} ( f : Hom A a c ) → ( g : Hom A b c ) → Hom A ab c
          κ1f+g=f : {c : Obj A} { f : Hom A a c } → { g : Hom A b c } → A [ A [ ( f + g ) o κ1    ] ≈  f ]
          κ2f+g=g : {c : Obj A} { f : Hom A a c } → { g : Hom A b c } → A [ A [ ( f + g ) o κ2    ] ≈  g ]
          uniqueness : {c : Obj A} { h : Hom A ab c }  → A [  ( A [ h o κ1  ] ) + ( A [ h o κ2  ] ) ≈  h ]
          +-cong : {c : Obj A} { f f' : Hom A a c } → { g g' : Hom A b c } → A [ f ≈ f' ] → A [ g ≈ g' ] → A [ f + g ≈ f' + g' ]

    record coProduct { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) ( a b : Obj A )
                : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
       field
          coproduct : Obj A
          κ1 : Hom A a coproduct
          κ2 : Hom A b coproduct
          isProduct : IsCoProduct A a b coproduct κ1 κ2

    -----
    --
    -- product on arbitrary index
    --

    record IsIProduct { c c₁ c₂ ℓ : Level} ( I : Set c) ( A : Category c₁ c₂ ℓ )
          ( p  : Obj A )                       -- product
          ( ai : I → Obj A )                   -- families
          ( pi :  (i : I ) → Hom A p ( ai i ) ) -- projections
                : Set  (c ⊔ ℓ ⊔ (c₁ ⊔ c₂)) where
       field
          iproduct : {q : Obj A}  → ( qi : (i : I) → Hom A q (ai i) ) → Hom A q p
          pif=q :   {q : Obj A}  → { qi : (i : I) → Hom A q (ai i) }
              → ∀ { i : I } → A [ A [ ( pi i )  o ( iproduct qi ) ] ≈  (qi i) ]
          ip-uniqueness :  {q : Obj A} { h : Hom A q p } → A [ iproduct ( λ (i : I) →  A [ (pi i)  o h ] )  ≈  h ]
          ip-cong : {q : Obj A}   → { qi : (i : I) → Hom A q (ai i) } → { qi' : (i : I) → Hom A q (ai i) }
                    → ( ∀ (i : I ) →  A [ qi i ≈ qi' i ] ) → A [ iproduct qi ≈ iproduct qi' ]
       -- another form of uniquness
       ip-uniqueness1 : {q : Obj A}  → ( qi : (i : I) → Hom A q (ai i) ) → ( product' : Hom A q p )
              → ( ∀ { i : I } →  A [ A [ ( pi i )  o product' ] ≈  (qi i) ] )
              → A [ product'  ≈ iproduct qi ]
       ip-uniqueness1 {a} qi product' eq =  let  open ≈-Reasoning (A) in begin
               product'
             ≈↑⟨ ip-uniqueness ⟩
               iproduct (λ i₁ → A [ pi i₁ o product' ])
             ≈⟨ ip-cong ( λ i → begin
               pi i o product'
             ≈⟨ eq {i} ⟩
               qi i
             ∎ ) ⟩
               iproduct qi
             ∎

    record IProduct { c c₁ c₂ ℓ : Level} ( I : Set c) ( A : Category c₁ c₂ ℓ )   (ai : I → Obj A) : Set  (c ⊔ ℓ ⊔ (c₁ ⊔ c₂)) where
        field
          iprod :  Obj A
          pi : (i : I ) → Hom A iprod  ( ai i )
          isIProduct :  IsIProduct I A iprod  ai  pi

    record IsICoProduct { c c₁ c₂ ℓ : Level} ( I : Set c) ( A : Category c₁ c₂ ℓ )
          ( p  : Obj A )                        -- coproduct
          ( ci : I → Obj A  )                   -- cases
          ( ki :  (i : I ) → Hom A ( ci i ) p ) -- coprojections
                : Set  (c ⊔ ℓ ⊔ (c₁ ⊔ c₂)) where
       field
          icoproduct : {q : Obj A}  → ( qi : (i : I) → Hom A (ci i)  q ) → Hom A p q
          kif=q :   {q : Obj A}  → { qi : (i : I) → Hom A (ci i) q }
              → ∀ { i : I } → A [ A [ ( icoproduct qi ) o ( ki i )  ] ≈  (qi i) ]
          icp-uniqueness :  {q : Obj A} { h : Hom A p q } → A [ icoproduct ( λ (i : I) →  A [ h o (ki i) ] )  ≈  h ]
          icp-cong : {q : Obj A}   → { qi : (i : I) → Hom A (ci i)  q} → { qi' : (i : I) → Hom A (ci i) q }
                    → ( ∀ (i : I ) →  A [ qi i ≈ qi' i ] ) → A [ icoproduct qi ≈ icoproduct qi' ]
       -- another form of uniquness
       icp-uniqueness1 : {q : Obj A}  → ( qi : (i : I) → Hom A (ci i) q ) → ( product' : Hom A p q  )
              → ( ∀ { i : I } →  A [ A [   product' o ( ki i )] ≈  (qi i) ] )
              → A [ product'  ≈ icoproduct qi ]
       icp-uniqueness1 {a} qi product' eq =  let  open ≈-Reasoning (A) in begin
               product'
             ≈↑⟨ icp-uniqueness ⟩
               icoproduct (λ i₁ → A [ product' o ki i₁ ])
             ≈⟨ icp-cong ( λ i → begin
               product' o ki i
             ≈⟨ eq {i} ⟩
               qi i
             ∎ ) ⟩
               icoproduct qi
             ∎

    record ICoProduct { c c₁ c₂ ℓ : Level} ( I : Set c) ( A : Category c₁ c₂ ℓ )   (ci : I → Obj A) : Set  (c ⊔ ℓ ⊔ (c₁ ⊔ c₂)) where
        field
          icoprod :  Obj A
          ki : (i : I ) → Hom A ( ci i )  icoprod
          isICoProduct :  IsICoProduct I A icoprod  ci  ki


    -- Pullback
    --         f
    --     a ------→ c
    --     ^          ^
    --  π1 |          |g
    --     |          |
    --    ab ------→ b
    --     ^   π2
    --     |
    --     d
    --
    record IsPullback { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a b c ab : Obj A}
          ( f : Hom A a c )    ( g : Hom A b c )
          ( π1 : Hom A ab a )  ( π2 : Hom A ab b )
             : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
       field
          commute : A [ A [ f  o π1 ] ≈ A [ g  o π2 ] ]
          pullback : { d : Obj A } → { π1' : Hom A d a } { π2' : Hom A d b } → A [ A [ f  o π1' ] ≈ A [ g  o π2' ] ] → Hom A d ab
          π1p=π1 :  { d : Obj A } → { π1' : Hom A d a } { π2' : Hom A d b } → { eq : A [ A [ f  o π1' ] ≈ A [ g  o π2' ]  ] }
                 →  A [ A [ π1  o pullback eq ] ≈  π1' ]
          π2p=π2 :  { d : Obj A } → { π1' : Hom A d a } { π2' : Hom A d b } → { eq : A [ A [ f  o π1' ] ≈ A [ g  o π2' ]  ] }
                 →  A [ A [ π2  o pullback eq ] ≈  π2' ]
          uniqueness : { d : Obj A } → ( p' : Hom A d ab ) → ( π1' : Hom A d a ) ( π2' : Hom A d b ) → ( eq : A [ A [ f  o π1' ] ≈ A [ g  o π2' ] ]  )
                 →  ( π1p=π1' : A [ A [ π1  o p' ] ≈  π1' ] )
                 →  ( π2p=π2' : A [ A [ π2  o p' ] ≈  π2' ] )
                 →  A [ pullback eq  ≈ p' ]

    record Pullback { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a b c : Obj A}
          ( f : Hom A a c )    ( g : Hom A b c )
             : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
       field
          ab  : Obj A
          π1 : Hom A ab a
          π2 : Hom A ab b
          isPullback : IsPullback A f g π1 π2

    --
    -- Limit
    --
    -----

    -- Constancy Functor

    K : { c₁' c₂' ℓ' : Level}  (I : Category c₁' c₂' ℓ') { c₁'' c₂'' ℓ'' : Level} ( A : Category c₁'' c₂'' ℓ'' )
        → ( a : Obj A ) → Functor I A
    K I A a = record {
          FObj = λ i → a ;
          FMap = λ f → id1 A a ;
            isFunctor = let  open ≈-Reasoning (A) in record {
                   ≈-cong   = λ f=g → refl-hom
                 ; identity = refl-hom
                 ; distr    = sym idL
            }
      }


    record IsLimit { c₁ c₂ ℓ : Level} { c₁' c₂' ℓ' : Level} ( I : Category c₁ c₂ ℓ ) ( A : Category c₁' c₂' ℓ' ) ( Γ : Functor I A )
         (a0 : Obj A ) (t0 : NTrans I A ( K I A a0 ) Γ  ) : Set (suc (c₁' ⊔ c₂' ⊔ ℓ' ⊔ c₁ ⊔ c₂ ⊔ ℓ )) where
      field
         limit :  ( a : Obj A ) → ( t : NTrans I A ( K I A a ) Γ ) → Hom A a a0
         t0f=t :  { a : Obj A } → { t : NTrans I A ( K I A a ) Γ } → ∀ { i : Obj I } →
             A [ A [ TMap t0 i o  limit a t ]  ≈ TMap t i ]
         limit-uniqueness : { a : Obj A } →  { t : NTrans I A ( K I A a ) Γ } → { f : Hom A a a0 } → ( ∀ { i : Obj I } →
             A [ A [ TMap t0 i o  f ]  ≈ TMap t i ] ) → A [ limit a t ≈ f ]

    record Limit { c₁ c₂ ℓ : Level} { c₁' c₂' ℓ' : Level}  ( I : Category c₁ c₂ ℓ ) ( A : Category c₁' c₂' ℓ' ) ( Γ : Functor I A )
           : Set (suc (c₁' ⊔ c₂' ⊔ ℓ' ⊔ c₁ ⊔ c₂ ⊔ ℓ )) where
      field
         a0 : Obj A
         t0 : NTrans I A ( K I A a0 ) Γ
         isLimit : IsLimit I A Γ a0 t0

    LimitNat : { c₁' c₂' ℓ' : Level} (I : Category c₁' c₂' ℓ') { c₁ c₂ ℓ : Level} ( B : Category c₁ c₂ ℓ ) { c₁'' c₂'' ℓ'' : Level}
         ( C : Category c₁'' c₂'' ℓ'' )
         ( Γ : Functor I B )
         ( lim : Obj B ) ( tb : NTrans I B ( K I B lim ) Γ ) →
             ( U : Functor B C)  → NTrans I C ( K I C (FObj U lim) ) (U  ○  Γ)
    LimitNat I B C Γ lim tb U = record {
                   TMap  = TMap (Functor*Nat I C U tb) ;
                   isNTrans = record { commute = λ {a} {b} {f} → let  open ≈-Reasoning (C) in begin
                         FMap (U ○ Γ) f o TMap (Functor*Nat I C U tb) a
                     ≈⟨ nat ( Functor*Nat I C U tb ) ⟩
                         TMap (Functor*Nat I C U tb) b o FMap (U ○ K I B lim) f
                     ≈⟨ cdr (IsFunctor.identity (isFunctor U) ) ⟩
                         TMap (Functor*Nat I C U tb) b o FMap (K I C (FObj U lim)) f
                     ∎
                   } }

    open Limit
    record LimitPreserve { c₁ c₂ ℓ : Level} { c₁' c₂' ℓ' : Level} ( I : Category c₁ c₂ ℓ ) ( A : Category c₁' c₂' ℓ' )
         { c₁'' c₂'' ℓ'' : Level} ( C : Category c₁'' c₂'' ℓ'' )
          (G : Functor A C) : Set (suc (c₁' ⊔ c₂' ⊔ ℓ' ⊔ c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁'' ⊔ c₂'' ⊔ ℓ'' )) where
      field
         preserve :  ( Γ : Functor I A ) → ( limita : Limit I A Γ  ) →
               IsLimit I C (G ○ Γ) (FObj G (a0 limita ) ) (LimitNat I A C Γ (a0 limita ) (t0 limita) G )
      plimit :  { Γ : Functor I A } → ( limita : Limit I A Γ  ) →  Limit I C (G  ○ Γ )
      plimit {Γ} limita =  record { a0 = (FObj G (a0 limita ))
         ; t0 =  LimitNat I A C Γ (a0 limita ) (t0 limita) G
         ; isLimit = preserve Γ limita }

    record Complete { c₁' c₂' ℓ' : Level} { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) : Set (suc (c₁' ⊔ c₂' ⊔ ℓ' ⊔ c₁ ⊔ c₂ ⊔ ℓ )) where
      field
         climit :  { I : Category c₁' c₂' ℓ' } ( Γ : Functor I A ) → Limit I A Γ
         cproduct : ( I : Set c₁' ) (fi : I → Obj A )  → IProduct I A fi -- c₁ should be a free level
         cequalizer : {a b : Obj A} (f g : Hom A a b)  → Equalizer A  f g
      open Limit
      limit-c :  {I : Category c₁' c₂' ℓ' } ( Γ : Functor I A ) → Obj A
      limit-c  Γ  = a0 ( climit Γ)
      limit-u : {I : Category c₁' c₂' ℓ' } ( Γ : Functor I A ) →  NTrans I A ( K I A (limit-c Γ )) Γ
      limit-u  Γ  = t0 ( climit Γ)
      open Equalizer
      equalizer-p : {a b : Obj A} (f g : Hom A a b)  → Obj A
      equalizer-p f g =  equalizer-c (cequalizer f g )
      equalizer-e : {a b : Obj A} (f g : Hom A a b)  → Hom A (equalizer-p f g) a
      equalizer-e f g = equalizer (cequalizer f g )


-- initial object

    record HasInitialObject {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (i : Obj A) : Set  (suc ℓ ⊔ (suc c₁ ⊔ suc c₂)) where
      field
         initial :  ∀( a : Obj A ) →  Hom A i a
         uniqueness  : { a : Obj A } →  ( f : Hom A i a ) → A [ f ≈  initial a ]

    record InitialObject {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) : Set  (suc ℓ ⊔ (suc c₁ ⊔ suc c₂)) where
      field
         initialObject :  Obj A
         hasInitialObject :  HasInitialObject A initialObject

    open import Category.Sets

    Yoneda : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )
       (a : Obj A) → (s : Small c₂ (Category.op A) ) → Functor (Category.op A) (Sets {c₂})
    Yoneda {c₁} {c₂} {ℓ} A a s = record {
        FObj = λ b → Hom A b a
      ; FMap = λ {x} {y} (f : Hom A y x ) ( g : Hom A x a ) →  A [ g o f ]
      ; isFunctor = record {
                 identity =  λ {b} x → ≡←≈ idR  
               ; distr = λ {a} {b} {c} {f} {g} x → ≡←≈ assoc
               ; ≈-cong = λ eq x → ≡←≈ ( resp eq refl-hom )
            }
        }  where
            open Small s
            open ≈-Reasoning  A


    --
    -- Representable  U  ≈　Hom(A,-)

    record Representable  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )
          ( s : Small c₂ (Category.op A))
          ( U : Functor  (Category.op A)  (Sets {c₂}) ) (a : Obj A) : Set  (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁ ))  where
       field
             -- FObj U x  :  A  → Set
             -- FMap U f  =  Set → Set (locally small)
             -- λ b → Hom (a,b) :  A → Set
             -- λ f → Hom (a,-) = λ b → Hom  a b

             repr→ : NTrans  (Category.op A)  (Sets {c₂}) U (Yoneda A a s )
             repr← : NTrans  (Category.op A)  (Sets {c₂}) (Yoneda A a s)  U
             reprId→  :  {x : Obj A} →  Sets [ Sets [ TMap repr→ x  o  TMap repr← x ] ≈ id1 (Sets {c₂}) (FObj (Yoneda A a s) x )]
             reprId←  :  {x : Obj A} →  Sets [ Sets [ TMap repr← x  o  TMap repr→ x ] ≈ id1 (Sets {c₂}) (FObj U x)]



    -- they say it is not possible to prove FreeTheorem in Agda nor Coq
    --    https://stackoverflow.com/questions/24718567/is-it-possible-to-get-hold-of-free-theorems-as-propositional-equalities
    -- so we postulate this
    FreeTheorem : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (C : Category c₁ c₂ ℓ) (D : Category c₁' c₂' ℓ') {a b c : Obj C }
       → Set (suc (c₁' ⊔ c₂' ⊔ ℓ' ⊔ c₁ ⊔ c₂ ⊔ ℓ ))
    FreeTheorem C D {a} {b} {c } =
       (F : Functor C D )
       → (fmap : {a : Obj C } {b : Obj C } → Hom C a b → Hom D (FObj F a) ( FObj F b) )
       → {h f : Hom C a b } →  {g k : Hom C b c }
       → C [  C  [ g o h ]  ≈  C [ k o f ]  ] →  D [ D [ FMap F g o fmap h ]  ≈  D [ fmap k o FMap F f ] ]


