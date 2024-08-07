{-# OPTIONS --cubical-compatible --safe #-}
module universal-mapping where

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

open import Category -- https://github.com/konn/category-agda
open import Level
open import HomReasoning
open import Definitions
open import Category.Cat

open Functor
open NTrans

--
--   Adjunction yields solution of universal mapping
--
--

Adj2UM : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
      → (adj : Adjunction A B ) → UniversalMapping A B (Adjunction.U adj) 
Adj2UM A B adj = record {
         F = FObj (Adjunction.F adj) ;
         η = TMap (Adjunction.η adj) ;
         _* = solution  ;
         isUniversalMapping = record {
                    universalMapping  = universalMapping;
                    uniquness = uniqueness
              }
      } where
         U : Functor B A 
         U = Adjunction.U adj
         F : Functor A B 
         F = Adjunction.F adj
         η : NTrans A A identityFunctor ( U ○  F ) 
         η = Adjunction.η adj
         ε : NTrans B B  ( F ○  U ) identityFunctor 
         ε = Adjunction.ε adj
         solution :  { a : Obj A} { b : Obj B} → ( f : Hom A a (FObj U b) ) →  Hom B (FObj F a ) b
         solution  {_} {b} f = B [ TMap ε b o FMap F f ]
         universalMapping :   {a' : Obj A} { b' : Obj B } → { f : Hom A a' (FObj U b') } →
                     A [ A [ FMap U ( solution f) o TMap η a' ]  ≈ f ]
         universalMapping {a} {b} {f} =
           let open ≈-Reasoning (A) in
              begin
                  FMap U ( solution  f) o TMap η a
              ≈⟨⟩
                  FMap U (  B [ TMap ε b o FMap F f ] ) o TMap η a
              ≈⟨ car (distr U ) ⟩
                 ( (FMap U (TMap ε b))  o (FMap U ( FMap F f )) ) o TMap η a
              ≈⟨ sym assoc ⟩
                  (FMap U (TMap ε b))  o ((FMap U ( FMap F f ))  o TMap η a )
              ≈⟨ cdr (nat η) ⟩
                  (FMap U (TMap ε b))  o ((TMap η (FObj U b )) o f )
              ≈⟨ assoc ⟩
                  ((FMap U (TMap ε b))  o (TMap η (FObj U b)))  o f
              ≈⟨ car ( IsAdjunction.adjoint1 ( Adjunction.isAdjunction adj))  ⟩
                  id (FObj U b) o f
              ≈⟨  idL  ⟩
                  f
              ∎
         lemma1 : (a : Obj A) ( b : Obj B ) ( f : Hom A a (FObj U b) ) → ( g :  Hom B (FObj F a) b) →
                A [ A [ FMap U g o  TMap η a ]  ≈ f ] →
                B [  (FMap F (A [ FMap U g o TMap η a ] )) ≈ FMap F f ]
         lemma1 a b f g k = IsFunctor.≈-cong (isFunctor F) k
         uniqueness :   {a' : Obj A} { b' : Obj B } → { f : Hom A a' (FObj U b') } → { g :  Hom B (FObj F a') b'} →
                     A [ A [ FMap U g o  TMap η a' ]  ≈ f ] → B [ solution f  ≈ g ]
         uniqueness {a} {b} {f} {g} k = let open ≈-Reasoning (B) in
              begin
                  solution f
              ≈⟨⟩
                  TMap ε b o FMap F f
              ≈⟨ cdr (sym ( lemma1 a b f g k )) ⟩
                  TMap ε b o FMap F ( A [ FMap U g o  TMap η a ] )
              ≈⟨ cdr (distr F )  ⟩
                  TMap ε b o ( FMap F ( FMap U g)  o FMap F ( TMap η a ) )
              ≈⟨ assoc  ⟩
                  ( TMap ε b o  FMap F ( FMap U g) ) o FMap F ( TMap η a )
              ≈⟨ sym ( car ( nat ε ))  ⟩
                  ( g o TMap ε ( FObj F a) )  o FMap F ( TMap η a )
              ≈⟨ sym assoc ⟩
                  g o ( TMap ε ( FObj F a)   o FMap F ( TMap η a ) )
              ≈⟨ cdr ( IsAdjunction.adjoint2 ( Adjunction.isAdjunction adj )) ⟩
                  g o id (FObj F a)
              ≈⟨ idR ⟩
                  g
              ∎

--
--
--  Universal mapping yields Adjunction
--
--


--
-- F is an functor
--

FunctorF : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
       { U : Functor B A }
       → UniversalMapping A B  U → Functor A B
FunctorF A B {U} um = record {
              FObj = F;
              FMap = myFMap ;
              isFunctor = myIsFunctor
       } where
    F : Obj A → Obj B 
    F = UniversalMapping.F um
    η : (a : Obj A) → Hom A a ( FObj U (F a) )
    η = UniversalMapping.η um
    _* : (UniversalMapping A B U ) →  { a : Obj A} { b : Obj B} → ( Hom A a (FObj U b) ) →  Hom B (F a ) b
    _* _ = UniversalMapping._* um 
    myFMap : {a b : Obj A} → Hom A a b → Hom B (F a) (F b)
    myFMap f = (_* um)  (A [  η (Category.cod A f )   o f ])
    lemma-id1 :  {a : Obj A} →  A [ A [ FMap U (id1 B (F a))  o  η a ]  ≈ (A [ (η a) o (id1 A a) ]) ]
    lemma-id1 {a} = let open ≈-Reasoning (A) in
       begin
           FMap U (id1 B (F a))  o  η a
       ≈⟨ ( car ( IsFunctor.identity ( isFunctor U )))  ⟩
           id (FObj U ( F a )) o  η a
       ≈⟨ idL  ⟩
           η a
       ≈⟨ sym idR  ⟩
           η a o id a
       ∎
    lemma-id :  {a : Obj A} →  B [ ( (_* um) (A [ (η a) o (id1 A a)] )) ≈ (id1 B (F a)) ]
    lemma-id {a} =   ( IsUniversalMapping.uniquness ( UniversalMapping.isUniversalMapping um ) ) lemma-id1
    lemma-cong2 : (a b : Obj A) (f g : Hom A a b) → A [ f ≈ g ] →
                A [ A [ FMap U ((_* um) (A [ η b  o  g ]) ) o  η a ] ≈  A [ η b  o  f ] ]
    lemma-cong2 a b f g eq =  let open ≈-Reasoning (A) in
       begin
          ( FMap U ((_* um) (A [ η b  o  g ]) )) o  η a
       ≈⟨  ( IsUniversalMapping.universalMapping ( UniversalMapping.isUniversalMapping um ))  ⟩
          η b  o  g
       ≈⟨ ( IsCategory.o-resp-≈ ( Category.isCategory A ) (sym eq) (refl-hom)  ) ⟩
          η b  o  f
       ∎
    lemma-cong1 : (a b : Obj A) (f g : Hom A a b) → A [ f ≈ g ] → B [ (_* um) (A [ η b  o  f ] ) ≈  (_* um) (A [ η b  o  g ]) ]
    lemma-cong1 a b f g eq = ( IsUniversalMapping.uniquness ( UniversalMapping.isUniversalMapping um ) ) ( lemma-cong2 a b f g eq )
    lemma-cong :  {a b : Obj A} {f g : Hom A a b} → A [ f ≈ g ] → B [ myFMap f ≈ myFMap g ]
    lemma-cong {a} {b} {f} {g} eq = lemma-cong1 a b f g eq
    lemma-distr2 :  (a b c : Obj A) (f : Hom A a b) (g : Hom A b c) →
            A [ A [ FMap U (B [(_* um) (A [ η c o g ]) o (_* um)( A [ η b  o f ]) ])  o  η a ] ≈ (A [ η c o A [ g o f ] ]) ]
    lemma-distr2 a b c f g = let open ≈-Reasoning (A) in
       begin
           ( FMap U (B [(_* um) (A [ η c o g ]) o (_* um)( A [ η b  o f ]) ] ) )  o  η a
       ≈⟨ car (distr U )  ⟩
           (( FMap U ((_* um) (A [ η c o g ])) o ( FMap U ((_* um)( A [ η b  o f ])))) )   o  η a
       ≈⟨ sym assoc ⟩
           ( FMap U ((_* um) (A [ η c o g ])) o (( FMap U ((_* um)( A [ η b  o f ]))))   o  η a )
       ≈⟨ cdr ( IsUniversalMapping.universalMapping ( UniversalMapping.isUniversalMapping um ))  ⟩
           ( FMap U ((_* um) (A [ η c o g ])) o ( η b  o f) )
       ≈⟨ assoc ⟩
           ( FMap U ((_* um) (A [ η c o g ])) o  η b)  o f
       ≈⟨ car ( IsUniversalMapping.universalMapping ( UniversalMapping.isUniversalMapping um ))  ⟩
           (  η c o g )  o f
       ≈⟨ sym assoc  ⟩
            η c o ( g o f )
       ∎
    lemma-distr1 :  (a b c : Obj A) (f : Hom A a b) (g : Hom A b c) →
            B [ (_* um) (A [ η c o A [ g o f ] ]) ≈ (B [(_* um) (A [ η c o g ]) o (_* um)( A [ η b  o f ]) ] )]
    lemma-distr1 a b c f g =  ( IsUniversalMapping.uniquness ( UniversalMapping.isUniversalMapping um )) (lemma-distr2 a b c f g )
    lemma-distr :  {a b c : Obj A} {f : Hom A a b} {g : Hom A b c} → B [ myFMap (A [ g o f ]) ≈ (B [ myFMap g o myFMap f ] )]
    lemma-distr {a} {b} {c} {f} {g} = lemma-distr1 a b c f g
    myIsFunctor : IsFunctor A B F myFMap
    myIsFunctor =
      record { ≈-cong   = lemma-cong
             ; identity = lemma-id
             ; distr    = lemma-distr
             }

--
-- naturality of η
--
nat-η : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                 { U : Functor B A }
                 → (um : UniversalMapping A B  U )  →
           NTrans  A A identityFunctor ( U ○ FunctorF A B um )
nat-η A B {U} um = record {
             TMap = η ; isNTrans = myIsNTrans
       } where
    F : Obj A → Obj B 
    F = UniversalMapping.F um
    η : (a : Obj A) → Hom A a ( FObj U (F a) ) 
    η = UniversalMapping.η um
    F' : Functor A B
    F' = FunctorF A B um
    _* : (UniversalMapping A B U ) →  { a : Obj A} { b : Obj B} → ( Hom A a (FObj U b) ) →  Hom B (F a ) b
    _* _ = UniversalMapping._* um 
    commute :  {a b : Obj A} {f : Hom A a b}
      → A [ A [ (FMap U (FMap F' f))  o  ( η a ) ]  ≈ A [ (η b ) o f ] ]
    commute {a} {b} {f} =   let open ≈-Reasoning (A) in
       begin
            (FMap U (FMap F' f))  o  ( η a )
       ≈⟨⟩
            (FMap U ((_* um)  (A [  η b  o f ])))   o  ( η a )
       ≈⟨ (IsUniversalMapping.universalMapping ( UniversalMapping.isUniversalMapping um ))  ⟩
            (η b ) o f
       ∎
    myIsNTrans : IsNTrans A A identityFunctor ( U ○  F' ) η
    myIsNTrans = record { commute = commute }

nat-ε : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                 { U : Functor B A }
       → (um : UniversalMapping A B  U )  →
           NTrans B B ( FunctorF A B um ○ U ) identityFunctor
nat-ε A B {U} um = record {
             TMap = ε ; isNTrans = myIsNTrans
       } where
    F : Obj A → Obj B
    F = UniversalMapping.F um
    η : (a : Obj A) → Hom A a ( FObj U (F a) )
    η = UniversalMapping.η um
    F' : Functor A B
    F' = FunctorF A B um
    _* : (UniversalMapping A B U ) →  { a : Obj A} { b : Obj B} → ( Hom A a (FObj U b) ) →  Hom B (F a ) b
    _* _ = UniversalMapping._* um 
    ε : ( b : Obj B ) → Hom B ( FObj F' ( FObj U b) ) b
    ε b = (_* um) ( id1 A (FObj U b))
    lemma-nat1 :  (a b : Obj B) (f : Hom B a b ) →
             A [ A [ FMap U ( B [ (um *) (id1 A (FObj U b)) o ((um *) (A [ η (FObj U b) o FMap U f ])) ] )  o η (FObj U a) ]
                 ≈ A [ FMap U f o id1 A (FObj U a) ] ]
    lemma-nat1 a b f = let open ≈-Reasoning (A) in
       begin
          FMap U ( B [ (um *) (id1 A (FObj U b)) o ((um *) ( η (FObj U b) o FMap U f )) ] )  o η (FObj U a)
       ≈⟨ car ( distr U  ) ⟩
          ( FMap U  ((um *) (id1 A (FObj U b))) o FMap U ((um *) ( η (FObj U b) o FMap U f )) )  o η (FObj U a)
       ≈⟨ sym assoc  ⟩
           FMap U  ((um *) (id1 A (FObj U b))) o ( FMap U ((um *) ( η (FObj U b) o FMap U f )))  o η (FObj U a)
       ≈⟨ cdr ((IsUniversalMapping.universalMapping ( UniversalMapping.isUniversalMapping um )) )  ⟩
           FMap U  ((um *) (id1 A (FObj U b))) o ( η (FObj U b) o FMap U f )
       ≈⟨ assoc  ⟩
           (FMap U  ((um *) (id1 A (FObj U b))) o  η (FObj U b)) o FMap U f
       ≈⟨ car ((IsUniversalMapping.universalMapping ( UniversalMapping.isUniversalMapping um )) ) ⟩
           id1 A (FObj U b) o FMap U f
       ≈⟨ idL ⟩
            FMap U f
       ≈⟨ sym idR ⟩
          FMap U f o id (FObj U a)
       ∎
    lemma-nat2 : (a b : Obj B) (f : Hom B a b ) → A [ A [ FMap U ( B [ f o ((um *) (id1 A (FObj U a ))) ] ) o η (FObj U a) ]
                                                        ≈ A [ FMap U f o id1 A (FObj U a) ] ]
    lemma-nat2 a b f = let open ≈-Reasoning (A) in
       begin
          FMap U ( B [ f o ((um *) (id1 A (FObj U a ))) ])  o η (FObj U a)
       ≈⟨ car ( distr U  ) ⟩
          (FMap U f o FMap U ((um *) (id1 A (FObj U a ))))  o η (FObj U a)
       ≈⟨ sym assoc  ⟩
          FMap U f o ( FMap U ((um *) (id1 A (FObj U a )))  o η (FObj U a)  )
       ≈⟨ cdr ( IsUniversalMapping.universalMapping ( UniversalMapping.isUniversalMapping um)) ⟩
          FMap U f o id (FObj U a )
       ∎
    commute : {a b : Obj B} {f : Hom B a b }
      →  B [ B [ f o (ε a) ] ≈ B [(ε b) o (FMap F' (FMap U f)) ] ]
    commute {a} {b} {f} = let open ≈-Reasoning (B) in
       sym ( begin
          ε b o (FMap F' (FMap U f))
       ≈⟨⟩
          ε b o ((_* um) (A [ η (FObj U b) o (FMap U f) ]))
       ≈⟨⟩
          ((_* um) ( id1 A (FObj U b))) o ((_* um) (A [ η (FObj U b) o (FMap U f) ]))
       ≈⟨ sym ( ( IsUniversalMapping.uniquness ( UniversalMapping.isUniversalMapping um )  (lemma-nat1 a b f))) ⟩
          (_* um) ( A [ FMap U f o id1 A (FObj U a) ] )
       ≈⟨ (IsUniversalMapping.uniquness ( UniversalMapping.isUniversalMapping um )  (lemma-nat2 a b f)) ⟩
          f o  ((_* um) ( id1 A (FObj U a)))
       ≈⟨⟩
          f o  (ε a)
       ∎ )
    myIsNTrans : IsNTrans B B ( F' ○ U ) identityFunctor　ε
    myIsNTrans = record { commute = commute }

------
--
--   Adjunction Construction from Universal Mapping
--
-----

UMAdjunction : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ') →
                ( U : Functor B A ) →
       (um : UniversalMapping A B U )  →
              Adjunction A B 
UMAdjunction A B U um = record {
           U = U  ;
           F = FunctorF A B um ;
           η = nat-η A B um ;
           ε = nat-ε A B um ;
           isAdjunction = record {
               adjoint1 = adjoint1 ;
               adjoint2 = adjoint2
           }
       } where
          F' : Obj A → Obj B 
          F' = UniversalMapping.F um
          η' : (a : Obj A) → Hom A a ( FObj U (F' a) )  
          η' = UniversalMapping.η um
          F : Functor A B
          F = FunctorF A B um
          η : NTrans A A identityFunctor ( U ○  F )
          η = nat-η A B um
          ε : NTrans B B  ( F ○  U ) identityFunctor
          ε = nat-ε A B um
          _* : UniversalMapping A B  U  →  { a : Obj A}{ b : Obj B} → ( Hom A a (FObj U b) ) →  Hom B (FObj F a ) b
          _* _ = UniversalMapping._* um
          isUniversalMapping = UniversalMapping.isUniversalMapping
          adjoint1 :   { b : Obj B } →
                     A [ A [ ( FMap U ( TMap ε b ))  o ( TMap η ( FObj U b )) ]  ≈ id1 A (FObj U b) ]
          adjoint1 {b} = let open ≈-Reasoning (A) in
             begin
               FMap U ( TMap ε b )  o  TMap η ( FObj U b )
             ≈⟨⟩
               FMap U ((_* um) ( id1 A (FObj U b)))  o  η' ( FObj U b )
             ≈⟨ IsUniversalMapping.universalMapping ( isUniversalMapping um )  ⟩
               id (FObj U b)
             ∎
          lemma-adj1 : (a : Obj A) →
             A [ A [ FMap U ((B [((_* um) ( id1 A (FObj U ( FObj F a )))) o (_* um) (A [  η' (FObj U ( FObj F a )) o ( η' a ) ]) ])) o η' a ]
               ≈ (η' a) ]
          lemma-adj1 a =  let open ≈-Reasoning (A) in
             begin
               FMap U ((B [((_* um) ( id1 A (FObj U ( FObj F a )))) o (_* um) (A [  η' (FObj U ( FObj F a )) o ( η' a ) ]) ])) o η' a
             ≈⟨ car (distr U)  ⟩
               (FMap U ((_* um) ( id1 A (FObj U ( FObj F a)))) o FMap U ((_* um) (A [  η' (FObj U ( FObj F a )) o ( η' a ) ]))) o η' a
             ≈⟨ sym assoc ⟩
               FMap U ((_* um) ( id1 A (FObj U ( FObj F a)))) o ( FMap U ((_* um) (A [  η' (FObj U ( FObj F a )) o ( η' a ) ])) o η' a )
             ≈⟨ cdr (IsUniversalMapping.universalMapping ( isUniversalMapping um)) ⟩
               FMap U ((_* um) ( id1 A (FObj U ( FObj F a)))) o ( η' (FObj U ( FObj F a )) o ( η' a ) )
             ≈⟨ assoc ⟩
               (FMap U ((_* um) ( id1 A (FObj U ( FObj F a)))) o ( η' (FObj U ( FObj F a )))) o ( η' a )
             ≈⟨ car (IsUniversalMapping.universalMapping ( isUniversalMapping um)) ⟩
                id (FObj U ( FObj F a)) o ( η' a )
             ≈⟨ idL ⟩
               η' a
             ∎
          lemma-adj2 : (a : Obj A) → A [ A [ FMap U (id1 B (FObj F a)) o η' a ] ≈  η' a ]
          lemma-adj2 a = let open ≈-Reasoning (A) in
             begin
               FMap U (id1 B (FObj F a)) o η' a
             ≈⟨  car ( IsFunctor.identity ( isFunctor U))  ⟩
               id (FObj U (FObj F a)) o η' a
             ≈⟨ idL ⟩
               η' a
             ∎
          adjoint2 :   {a : Obj A} →
                     B [ B [ ( TMap ε ( FObj F a ))  o ( FMap F ( TMap η a )) ]  ≈ id1 B (FObj F a) ]
          adjoint2 {a} = let open ≈-Reasoning (B) in
             begin
                TMap ε ( FObj F a )  o  FMap F ( TMap η a )
             ≈⟨⟩
                ((_* um) ( id1 A (FObj U ( FObj F a ))))  o  (_* um)  (A [  η' (FObj U ( FObj F a ))   o ( η' a ) ])
             ≈⟨ sym ( ( IsUniversalMapping.uniquness ( isUniversalMapping um )  (lemma-adj1 a))) ⟩
                (_* um)( η' a )
             ≈⟨  IsUniversalMapping.uniquness ( isUniversalMapping um )  (lemma-adj2 a) ⟩
                id1 B (FObj F a)
             ∎


------
--
--  Hom Set Adjunction
--
--   Hom(F(-),-) = Hom(-,U(-))
--       Unity of opposite
-----

--  Assuming 
--     naturality of left (Φ)
--     k = Hom A b b' ; f' = k o f                        h Hom A a' a  ; f' = f o h
--                        left                                               left
--    f : Hom A F(a)   b ←------- f* : Hom B a U(b)      f' : Hom A F(a')b ←------ f'* : Hom B a' U(b)
--       |               -------→        |                     |                               |
--       |k               right          |U(k)                 |F(h)                           |h
--       ↓                               ↓                     ↓                               ↓
--    f': Hom A F(a)   b'←------ f'* : Hom B a U(b')     f: Hom A F(a)  b ←-------- f* : Hom B a U(b)
--                        left                                               left

record UnityOfOppsite  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                         ( U : Functor B A )
                         ( F : Functor A B )
                         : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
           field
               left  : {a : Obj A} { b : Obj B } → Hom A a ( FObj U b ) → Hom B (FObj F a) b
               right   : {a : Obj A} { b : Obj B } → Hom B (FObj F a) b   → Hom A a ( FObj U b )
               left-injective : {a : Obj A} { b : Obj B } → {f : Hom A a (FObj U b) }  → A [ right ( left f ) ≈ f ]
               right-injective  : {a : Obj A} { b : Obj B } → {f : Hom B (FObj F a) b }  → B [ left ( right f ) ≈ f ]
               ---  naturality of Φ
               right-commute1 : {a : Obj A} {b b' : Obj B } →
                       { f : Hom B (FObj F a) b }  → { k : Hom B b b' } →
                        A [  right ( B [ k o  f ] )  ≈ A [ FMap U k o right f  ] ]
               right-commute2 : {a a' : Obj A} {b : Obj B } →
                       { f : Hom B (FObj F a) b }  → { h : Hom A a' a } →
                        A [ right ( B [ f  o  FMap F h ] )  ≈  A [ right f o h ] ]
               r-cong : {a : Obj A} { b : Obj B } → { f g : Hom A a ( FObj U b ) } →  A [ f  ≈ g ] → B [ left f ≈ left g ]
               l-cong : {a : Obj A} { b : Obj B } → { f g : Hom B (FObj F a) b }   →  B [ f  ≈ g ] → A [ right f ≈ right g   ]
           --  naturality of left (Φ-1)
           left-commute1 : {a : Obj A} {b b' : Obj B } →
                       { g : Hom A a (FObj U b)}  → { k : Hom B b b' } →
                        B [ B [ k o  left g ]   ≈ left ( A [ FMap U k o g  ] ) ]
           left-commute1 {a} {b} {b'} {g} {k} =  let open ≈-Reasoning (B) in
                     begin
                          k o  left g
                     ≈⟨ sym right-injective ⟩
                          left ( right ( k o  left g ) )
                     ≈⟨ r-cong right-commute1 ⟩
                          left ( A [ FMap U k o right ( left g ) ] )
                     ≈⟨ r-cong (lemma-1 g k) ⟩
                         left ( A [ FMap U k o g  ] )
                     ∎ where
                             lemma-1 : {a : Obj A} {b b' : Obj B } →
                               ( g : Hom A a (FObj U b))  → ( k : Hom B b b' ) →
                                A [ A [ FMap U k o right ( left g ) ]   ≈  A [ FMap U k o g  ] ]
                             lemma-1 g k = let open ≈-Reasoning (A) in
                                   begin
                                        FMap U k o right ( left g )
                                   ≈⟨ cdr ( left-injective) ⟩
                                        FMap U k o g
                                   ∎
           left-commute2 : {a a' : Obj A} {b : Obj B } →
                       { g : Hom A a (FObj U b) }  → { h : Hom A a' a } →
                        B [ B [ left g  o  FMap F h ]   ≈  left ( A [ g o h ] ) ]
           left-commute2 {a} {a'} {b} {g} {h} =  let open ≈-Reasoning (B) in
                     begin
                          left g  o  FMap F h
                     ≈⟨  sym right-injective ⟩
                          left ( right ( left g  o  FMap F h  ))
                     ≈⟨ r-cong  right-commute2  ⟩
                          left ( A [ right ( left g ) o h ] )
                     ≈⟨ r-cong ( lemma-2 g h  ) ⟩
                          left ( A [ g o h ] )
                     ∎  where
                           lemma-2 :  {a a' : Obj A} {b : Obj B } →
                               ( g : Hom A a (FObj U b))  → ( h : Hom A a' a ) →
                                A [ A [  right ( left g ) o h ]   ≈  A [ g o h  ] ]
                           lemma-2 g h  = let open ≈-Reasoning (A) in car ( left-injective  )

Adj2UO : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                 ( adj : Adjunction A B )  → UnityOfOppsite A B (Adjunction.U adj) (Adjunction.F adj)
Adj2UO A B adj = record {
            left =  left ;
            right  =  right ;
            left-injective =  left-injective  ;
            right-injective = right-injective  ;
            right-commute1 = right-commute1 ;
            right-commute2 = right-commute2 ;
            r-cong = r-cong ;
            l-cong = l-cong
      } where
            U : Functor B A 
            U = Adjunction.U adj
            F : Functor A B 
            F = Adjunction.F adj
            η : NTrans A A identityFunctor ( U ○  F ) 
            η = Adjunction.η adj
            ε : NTrans B B  ( F ○  U ) identityFunctor 
            ε = Adjunction.ε adj
            left  : {a : Obj A} { b : Obj B } → Hom A a ( FObj U b ) → Hom B (FObj F a) b
            left {a} {b} f = B [ TMap ε b o FMap F f ]
            right   : {a : Obj A} { b : Obj B } → Hom B (FObj F a) b   → Hom A a ( FObj U b )
            right  {a} {b} f = A [ FMap U f o (TMap η a)  ]
            left-injective : {a : Obj A} { b : Obj B } → {f : Hom A a (FObj U b) }  → A [ right ( left f ) ≈ f ]
            left-injective {a} {b} {f} =  let open ≈-Reasoning (A) in
                     begin
                         FMap U (B [ TMap ε b o FMap F f ]) o (TMap η a)
                     ≈⟨ car ( distr U ) ⟩
                         ( FMap U (TMap ε b) o FMap U (FMap F f )) o (TMap η a)
                     ≈↑⟨ assoc  ⟩
                         FMap U (TMap ε b) o ( FMap U (FMap F f ) o (TMap η a) )
                     ≈⟨ cdr ( nat η)  ⟩
                         FMap U (TMap ε b) o ((TMap η (FObj U b))  o f )
                     ≈⟨ assoc  ⟩
                         (FMap U (TMap ε b) o (TMap η (FObj U b)))  o f
                     ≈⟨  car  ( IsAdjunction.adjoint1 ( Adjunction.isAdjunction adj )) ⟩
                        id1 A (FObj U b) o f
                     ≈⟨ idL  ⟩
                        f
                     ∎
            right-injective  : {a : Obj A} { b : Obj B } → {f : Hom B (FObj F a) b }  → B [ left ( right f ) ≈ f ]
            right-injective {a} {b} {f} =  let open ≈-Reasoning (B) in
                     begin
                         TMap ε b o FMap F ( A [ FMap U f o (TMap η a)  ])
                     ≈⟨ cdr ( distr F ) ⟩
                         TMap ε b o ( FMap F (FMap U f) o FMap F (TMap η a))
                     ≈⟨ assoc  ⟩
                         ( TMap ε b o FMap F (FMap U f)) o FMap F (TMap η a)
                     ≈↑⟨ car (nat ε)  ⟩
                         ( f  o TMap ε ( FObj F a )) o ( FMap F ( TMap η a ))
                     ≈↑⟨ assoc  ⟩
                          f  o ( TMap ε ( FObj F a ) o ( FMap F ( TMap η a )))
                     ≈⟨  cdr  ( IsAdjunction.adjoint2 ( Adjunction.isAdjunction adj )) ⟩
                        f o id1 B (FObj F a)
                     ≈⟨ idR  ⟩
                        f
                     ∎
            right-commute1 : {a : Obj A} {b b' : Obj B } →
                       { f : Hom B (FObj F a) b }  → { k : Hom B b b' } →
                        A [  right ( B [ k o  f ] )  ≈ A [ FMap U k o right f  ] ]
            right-commute1 {a} {b} {b'} {f} {k} = let open ≈-Reasoning (A) in
                     begin
                         right ( B [ k o  f ] )
                     ≈⟨⟩
                         FMap U  ( B [ k o  f ] ) o (TMap η a) 
                     ≈⟨ car (distr U) ⟩
                         ( FMap U k o  FMap U f ) o (TMap η a) 
                     ≈↑⟨ assoc ⟩
                         FMap U k o  ( FMap U f o (TMap η a) )
                     ≈⟨⟩
                         FMap U k o right f  
                     ∎
            right-commute2 : {a a' : Obj A} {b : Obj B } →
                       { f : Hom B (FObj F a) b }  → { h : Hom A a' a}  →
                        A [ right ( B [ f  o  FMap F h ] )  ≈  A [ right f o h ] ]
            right-commute2 {a'} {a} {b} {f} {h} = let open ≈-Reasoning (A) in
                     begin
                         right ( B [ f  o  FMap F h ] )
                     ≈⟨⟩
                         FMap U (  B [ f  o  FMap F h ] )  o TMap η a
                     ≈⟨ car (distr U ) ⟩
                         (FMap U f  o  FMap U (FMap F h )) o TMap η a
                     ≈↑⟨ assoc ⟩
                         FMap U f o  ( FMap U (FMap F h ) o TMap η a )
                     ≈⟨ cdr ( nat η) ⟩
                         FMap U f o (TMap η a' o h )
                     ≈⟨ assoc ⟩
                         ( FMap U f  o TMap η a') o h
                     ≈⟨⟩
                         right f o h 
                     ∎

            r-cong : {a : Obj A} { b : Obj B } → { f g : Hom A a ( FObj U b ) } →  A [ f  ≈ g ] → B [ left f ≈ left g ]
            r-cong eq = let open ≈-Reasoning (B) in ( cdr ( fcong F  eq ) )
            l-cong : {a : Obj A} { b : Obj B } → { f g : Hom B (FObj F a) b }   →  B [ f  ≈ g ] → A [ right f ≈ right g   ]
            l-cong eq = let open ≈-Reasoning (A) in ( car ( fcong U  eq ) )


open UnityOfOppsite

--   f                            :    a ----------→ U(b)
--   1_F(a)                       :  F(a) ---------→ F(a)
--   ε(b) = left uo (1_F(a))      : UF(b) ---------→ a
--   η(a) = right  uo (1_U(a))    :    a ----------→ FU(a)

uo-solution  : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
     ( U : Functor B A ) ( F : Functor A B ) → ( uo : UnityOfOppsite A B U F)  →  {a : Obj A} {b : Obj B } 
     → ( f : Hom A a (FObj U b )) → Hom B (FObj F a) b
uo-solution A B U F uo {a} {b} f =  left uo f

--     F(ε(b)) o η(F(b))
--     F( left uo (id1 A (FObj U b))  ) o  right uo (id1 B (FObj F a)) ] == 1

UO2UM  : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                 ( U : Functor B A )
                 ( F : Functor A B ) →
                 ( uo : UnityOfOppsite A B U F)  → UniversalMapping A B U 
UO2UM  A B U F uo = record {
         F = FObj F ;
         η = λ a → right uo ( id1 B (FObj F a) ) ;
         _* = left uo  ; 
         isUniversalMapping = record {
                    universalMapping  = universalMapping;
                    uniquness = uniqueness
              }
      } where
         universalMapping :   {a : Obj A} { b : Obj B } → { f : Hom A a (FObj U b) } →
                     A [ A [ FMap U ( uo-solution A B U F uo f) o (  right uo ( id1 B (FObj F a)  )) ]  ≈ f ]
         universalMapping {a} {b} {f}  = let open ≈-Reasoning (A) in
               begin
                    FMap U ( left uo  f) o right uo ( id1 B (FObj F a)  )
               ≈↑⟨  right-commute1 uo   ⟩
                    right uo ( B [  left uo  f o  id1 B (FObj F a) ] )
               ≈⟨ l-cong uo lemma-1  ⟩
                    right uo ( left uo f )
               ≈⟨ left-injective uo ⟩
                    f
               ∎ where
                  lemma-1 :  B [ B [  left uo f o  id1 B (FObj F a) ] ≈ left uo f ]
                  lemma-1 = let open ≈-Reasoning (B) in idR
         uniqueness :   {a : Obj A} { b : Obj B } → { f : Hom A a (FObj U b) } → { g :  Hom B (FObj F a) b} →
                     A [ A [ FMap U g o right uo ( id1 B (FObj F a) ) ]  ≈ f ] → B [ uo-solution A B U F uo f  ≈ g ]
         uniqueness {a} {b} {f} {g} eq = let open ≈-Reasoning (B) in
               begin
                    uo-solution A B U F uo f
               ≈⟨⟩
                    left uo  f
               ≈↑⟨ r-cong uo eq ⟩
                    left uo  ( A [  FMap U g o  right uo ( id1 B (FObj F a) ) ] )
               ≈↑⟨ r-cong uo ( right-commute1 uo  ) ⟩
                    left uo ( right uo ( g  o ( id1 B (FObj F a) ) ) )
               ≈⟨ right-injective uo  ⟩
                    g  o ( id1 B (FObj F a) )
               ≈⟨ idR ⟩
                    g
               ∎


UO2Adj : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                 { U : Functor B A }
                 { F : Functor A B }
                 ( uo : UnityOfOppsite A B U F)
                    → Adjunction A B 
UO2Adj A B {U} {F} uo = record {
           U =  U ;
           F =  F ;
           η =  record { TMap  = λ a → right uo ( id1 B (FObj F a) ) ; isNTrans = record { commute = η-commute } } ;
           ε =  record { TMap  = λ b → left  uo ( id1 A (FObj U b) ) ; isNTrans = record { commute = ε-commute } } ;
           isAdjunction = record {
               adjoint1 = adjoint1 ;
               adjoint2 = adjoint2
           }
       } where
          η-commute :  {a b : Obj A} {f : Hom A a b}
              → A [ A [ (FMap U (FMap F f))  o (right uo ( id1 B (FObj F a) ) )  ]  ≈ A [ (right uo ( id1 B (FObj F b) )  ) o f ] ]
          η-commute {a} {b} {f} =   let open ≈-Reasoning (A) in
               begin
                    (FMap U (FMap F f))  o  (right uo ( id1 B (FObj F a) ) )
               ≈↑⟨ right-commute1 uo  ⟩
                    right uo ( B [ (FMap F f)  o  ( id1 B (FObj F a) ) ] )
               ≈⟨ l-cong uo (IsCategory.identityR (Category.isCategory B))  ⟩
                    right uo ( FMap F f )
               ≈↑⟨ l-cong uo (IsCategory.identityL (Category.isCategory B))  ⟩
                    right uo ( B [  ( id1 B (FObj F b ))  o  FMap F f ] )
               ≈⟨ right-commute2 uo   ⟩
                    (right uo ( id1 B (FObj F b) )  ) o f
               ∎ where
                  lemma-1 : B [ B [ (FMap F f)  o  ( id1 B (FObj F a) ) ]  ≈  FMap F f ]
                  lemma-1 = IsCategory.identityR (Category.isCategory B)
          ε :  (b : Obj B )  → Hom B (FObj F ( FObj U ( b ) )) b
          ε b = left uo ( id1 A (FObj U b) ) 
          ε-commute : {a b : Obj B} {f : Hom B a b }
              →  B [ B [ f o (ε a) ] ≈ B [(ε b) o (FMap F (FMap U f)) ] ]
          ε-commute {a} {b} {f} = let open ≈-Reasoning (B) in
               sym ( begin
                  ε b o (FMap F (FMap U f))
               ≈⟨⟩
                 left uo ( id1 A (FObj U b) )  o (FMap F (FMap U f))
               ≈⟨ left-commute2 uo ⟩
                 left uo ( A [ id1 A (FObj U b)   o FMap U f ] )
               ≈⟨ r-cong uo (IsCategory.identityL (Category.isCategory A))  ⟩
                 left uo (  FMap U f  )
               ≈↑⟨ r-cong uo (IsCategory.identityR (Category.isCategory A))  ⟩
                 left uo ( A [ FMap U f  o  id1 A (FObj U a) ] )
               ≈↑⟨ left-commute1 uo ⟩
                  f o  left uo ( id1 A (FObj U a) )
               ≈⟨⟩
                  f o  (ε a)
               ∎  )
          um = UO2UM A B U F uo
          adjoint1 :   { b : Obj B } →
                     A [ A [ ( FMap U (left uo (id1 A (FObj U b))) )  o (right uo (id1 B (FObj F (FObj U b)))) ]  ≈ id1 A (FObj U b) ]
          adjoint1 {b} = let open ≈-Reasoning (A) in
               begin
                    FMap U (left uo (id1 A (FObj U b))) o (right uo (id1 B (FObj F (FObj U b))))
               ≈↑⟨ right-commute1 uo ⟩
                    right uo ( B [ left uo (id1 A (FObj U b))  o id1 B (FObj F (FObj U b)) ] )
               ≈⟨ l-cong uo ((IsCategory.identityR (Category.isCategory B))) ⟩
                    right uo ( left uo (id1 A (FObj U b))  )
               ≈⟨ left-injective uo ⟩
                    id1 A (FObj U b)
               ∎
          adjoint2 :   {a : Obj A} →
                     B [ B [ left uo (Category.Category.Id A) o FMap F (right uo (id1 B (FObj F a))) ]  ≈ id1 B (FObj F a) ]
          adjoint2 {a} = let open ≈-Reasoning (B) in
               begin
                   left uo (Category.Category.Id A) o FMap F (right uo (id1 B (FObj F a)))
               ≈⟨ left-commute2  uo ⟩
                   left uo ( A [ (Category.Category.Id A)   o (right uo (id1 B (FObj F a))) ] )
               ≈⟨ r-cong uo ((IsCategory.identityL (Category.isCategory A))) ⟩
                   left uo ( right uo (id1 B (FObj F a)))
               ≈⟨  right-injective uo ⟩
                  id1 B (FObj F a)
               ∎


--  done!

