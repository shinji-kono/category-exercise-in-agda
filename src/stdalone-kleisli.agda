module stdalone-kleisli where

open import Level
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ( [_] )


--        h       g       f
--     a ---→ b ---→ c ---→ d
--

record IsCategory {l : Level} (  Obj : Set (suc l) ) (Hom : Obj → Obj → Set l )
     ( _o_ : { a b c : Obj } → Hom b c  → Hom a b →  Hom a c )
     ( id : ( a  : Obj ) → Hom a a )
         : Set (suc l) where
  field
       idL : { a b : Obj } { f : Hom a b } → ( id b o f ) ≡ f
       idR : { a b : Obj } { f : Hom a b } → ( f o id a ) ≡ f
       assoc : { a b c d : Obj } { f : Hom c d }{ g : Hom b c }{ h : Hom a b } →  f o ( g  o h ) ≡ ( f  o g )  o h

record Category {l : Level} : Set (suc (suc l)) where
  field
       Obj : Set (suc l)
       Hom : Obj → Obj → Set l
       _o_ : { a b c : Obj } → Hom b c  → Hom a b →  Hom a c
       id : ( a  : Obj ) → Hom a a
       isCategory : IsCategory Obj Hom _o_ id

Sets : Category
Sets = record {
       Obj = Set 
    ;  Hom =  λ a b → a → b
    ;  _o_ = λ f g x → f ( g x )
    ;  id = λ A  x → x
    ;  isCategory = record {
           idL = refl
         ; idR = refl
         ; assoc = refl
       }
   }


open Category

_[_o_] :  {l : Level} (C : Category {l} ) → {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
C [ f o g ] = Category._o_ C f g

--
--           f        g
--       a ----→ b -----→ c
--       |        |         |
--      T|       T|        T|
--       |        |         |
--       v        v         v
--      Ta ----→ Tb ----→ Tc
--           Tf       Tg


record IsFunctor {l : Level} (C D : Category {l} )
                 (FObj : Obj C → Obj D)
                 (FMap : {A B : Obj C} → Hom C A B → Hom D (FObj A) (FObj B))
                 : Set (suc l ) where
  field
    identity : {A : Obj C} →  FMap (id C A) ≡ id D (FObj A)
    distr : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
      → FMap ( C [ g o f ])  ≡ (D [ FMap g o FMap f ] )

record Functor {l : Level} (domain codomain : Category {l} )
  : Set (suc l) where
  field
    FObj : Obj domain → Obj codomain
    FMap : {A B : Obj domain} → Hom domain A B → Hom codomain (FObj A) (FObj B)
    isFunctor : IsFunctor domain codomain FObj FMap

open Functor

idFunctor : {l : Level } { C : Category {l} } → Functor C C
idFunctor = record {
        FObj = λ x → x
     ;  FMap = λ f → f
     ;  isFunctor = record {
           identity = refl
         ; distr = refl
       }
  }

open  import  Relation.Binary.PropositionalEquality hiding ( [_] )


_●_ : {l : Level} { A B C : Category {l} }  → ( S : Functor B C ) ( T : Functor A B ) →  Functor A C
_●_ {l} {A} {B} {C} S T  = record {
        FObj = λ x → FObj S ( FObj T x )
     ;  FMap = λ f → FMap S ( FMap T f )
     ;  isFunctor = record {
           identity = λ {a} → identity a
         ; distr = λ {a} {b} {c} {f} {g} → distr
       }
   } where
       identity :  (a : Obj A) → FMap S (FMap T (id A a)) ≡ id C (FObj S (FObj T a))
       identity a = let open ≡-Reasoning in begin
              FMap S (FMap T (id A a))
           ≡⟨ cong ( λ z → FMap S z ) ( IsFunctor.identity (isFunctor T )  ) ⟩
              FMap S (id B (FObj T a) )
           ≡⟨ IsFunctor.identity (isFunctor S )   ⟩
              id C (FObj S (FObj T a))
           ∎
       distr : {a b c : Obj A} { f : Hom A a b } { g : Hom A b c } → FMap S (FMap T (A [ g o f ])) ≡ (C [ FMap S (FMap T g) o FMap S (FMap T f) ])
       distr {a} {b} {c} {f} {g} =  let open ≡-Reasoning in begin
               FMap S (FMap T (A [ g o f ]))
           ≡⟨ cong ( λ z → FMap S z ) ( IsFunctor.distr (isFunctor T )  ) ⟩
               FMap S (  B [ FMap T g o FMap T f ] )
           ≡⟨  IsFunctor.distr (isFunctor S )    ⟩
              C [ FMap S (FMap T g) o FMap S (FMap T f) ]
           ∎


-- import Axiom.Extensionality.Propositional
-- postulate extensionality : {  c₂  : Level} ( A : Category  {c₂} ) → Axiom.Extensionality.Propositional.Extensionality c₂ c₂

--
--            t a 
--      F a -----→ G a
--        |           |
--    Ff  |           | Gf
--        v           v
--      F b ------→ G b
--            t b
--

record IsNTrans  { l : Level } (D C : Category {l} ) ( F G : Functor D C )
                 (TMap : (A : Obj D) → Hom C (FObj F A) (FObj G A))
                 : Set (suc l) where
  field
    commute : {a b : Obj D} {f : Hom D a b} 
      →  C [ (  FMap G f ) o  ( TMap a ) ]  ≡ C [ (TMap b ) o  (FMap F f)  ] 

record NTrans  {l : Level} {domain codomain : Category {l} } (F G : Functor domain codomain )
       : Set (suc l) where
  field
    TMap :  (A : Obj domain) → Hom codomain (FObj F A) (FObj G A)
    isNTrans : IsNTrans domain codomain F G TMap



open NTrans

--
--
--    η   : 1 ------→ T
--    μ   : TT -----→ T
--
--        η                       μT
--    T -----→ TT          TTT ------→ TT
--    |         |            |           |
-- Tη |         |μ        Tμ |           |Tμ
--    v         |            v           v
--   TT -----→ T           TT -------→ T
--        μ                       μT


record IsMonad {l : Level} { C : Category {l} } (T : Functor C C) ( η :  NTrans idFunctor T ) ( μ :  NTrans (T ● T) T )
      : Set (suc l) where
   field 
       assoc  : {a : Obj C} → C [ TMap μ a o TMap μ ( FObj T a ) ] ≡  C [  TMap μ a o FMap T (TMap μ a) ] 
       unity1 : {a : Obj C} → C [ TMap μ a o TMap η ( FObj T a ) ] ≡ id C (FObj T a) 
       unity2 : {a : Obj C} → C [ TMap μ a o (FMap T (TMap η a ))] ≡ id C (FObj T a) 


record Monad {l : Level} { C : Category {l} } (T : Functor C C) : Set (suc l) where
   field 
      η : NTrans idFunctor T
      μ :  NTrans (T ● T) T 
      isMonad : IsMonad T η μ

                          
Left : {l : Level} (C : Category {l} ) {a b c : Obj C } {f f' : Hom C b c } {g : Hom C a b } →  f ≡ f' → C [ f  o g ] ≡ C [ f'  o g ]
Left {l} C {a} {b} {c} {f} {f'} {g} refl = cong ( λ z → C [ z  o g  ] ) refl

Right : {l : Level} (C : Category {l} ) {a b c : Obj C } {f : Hom C b c } {g g' : Hom C a b } →  g ≡ g' → C [ f  o g ] ≡ C [ f  o g' ]
Right {l} C {a} {b} {c} {f} {g} {g'} refl = cong ( λ z → C [ f  o z  ] ) refl

Assoc : {l : Level} (C : Category {l} ) {a b c d : Obj C } {f : Hom C c d } {g : Hom C b c } { h : Hom C a b }
   → C [ f  o C [ g  o h ] ]  ≡ C [ C [ f   o g ] o h ]
Assoc {l} C = IsCategory.assoc ( isCategory C )


Kleisli : {l : Level} (C : Category {l} ) (T : Functor C C ) ( M : Monad T ) → Category {l}
Kleisli {l} C T M = record {
       Obj = Obj C 
    ;  Hom = λ a b → Hom C a ( FObj T b )
    ;  _o_ = λ {a} {b} {c} f g  → join {a} {b} {c} f g
    ;  id = λ a  → TMap (Monad.η M) a 
    ;  isCategory = record {
            idL = idL
          ; idR = idR
          ; assoc = assoc
       }
  } where
      open Monad M
      KleisliHom : (a b : Obj C) →  Set l
      KleisliHom a b = Hom C a ( FObj T b )
      join : { a b c : Obj C } → KleisliHom b c → KleisliHom a b → KleisliHom a c
      join {a} {b} {c} f g =  C [ TMap (Monad.μ M) c o  C [ FMap T ( f ) o  g  ] ] 
      idL : {a b : Obj C} {f : KleisliHom a b} → join (TMap η b ) f ≡ f
      idL {a} {b} {f} =  let open ≡-Reasoning in begin
              C [  TMap μ b o C [  FMap T (TMap η b) o f ] ] 
           ≡⟨ ( begin
                C [  TMap μ b o C [  FMap T (TMap η b) o f ] ]
             ≡⟨ IsCategory.assoc ( isCategory C ) ⟩
                C [  C [ TMap μ b o  FMap T (TMap η b) ] o f  ]
             ≡⟨ cong ( λ z → C [ z  o f ] ) ( IsMonad.unity2 (Monad.isMonad M )  )   ⟩
                C [ id C (FObj T b) o f  ]
             ≡⟨ IsCategory.idL ( isCategory C ) ⟩
                f
             ∎ ) ⟩
              f
            ∎
      idR : {a b : Obj C} {f : KleisliHom a b} → join f ( TMap η a ) ≡ f
      idR {a} {b} {f} =  let open ≡-Reasoning in begin
              C [ TMap μ b o C [ FMap T f o TMap η a ] ]  
           ≡⟨ ( begin
                C [ TMap μ b o C [ FMap T f o TMap η a ] ]
             ≡⟨  cong ( λ z → C [ TMap μ b  o z ] ) ( IsNTrans.commute (isNTrans  η ))  ⟩
                C [ TMap μ b o C [ TMap η (FObj T b) o  f  ] ]
             ≡⟨  IsCategory.assoc ( isCategory C )  ⟩
                C [ C [ TMap μ b o TMap η (FObj T b) ] o  f  ] 
             ≡⟨ cong ( λ z → C [ z  o f ] ) ( IsMonad.unity1 (Monad.isMonad M )  )  ⟩
                C [ id C  (FObj T b)  o  f  ] 
             ≡⟨ IsCategory.idL ( isCategory C )  ⟩
                f
             ∎ ) ⟩
              f 
           ∎
--
--        TMap μ d ・ (  FMap T f ・ (  TMap μ c ・ (  FMap T g ・ h ) ) ) ) 
--
--      h       T g               μ c          
--   a -→ T b -----→ T T c ---------------→ T c 
--        |          |                      |
--        |          |                      |
--        |          | T T f     NAT μ      | T f
--        |          |                      |
--        |          v            μ (T d)   v  
--        |distr T   T T T d -------------→ T T d 
--        |          |                      |
--        |          |                      |
--        |          | T μ d                | μ d
--        |          |      Monad-assoc     |
--        |          v                      v
--        +--------→ T T d ----------------→ T d 
--   T (μ d・T f・g)              μ d
--
--        TMap μ d ・ (  FMap T (( TMap μ d ・ (  FMap T f ・ g ) ) ) ・ h ) )  
--
      _・_ : {a b c : Obj C } ( f : Hom C b c ) ( g : Hom C a b ) → Hom C a c
      f ・ g  = C [ f  o g ]
      assoc :  {a b c d : Obj C} {f : KleisliHom c d} {g : KleisliHom b c} {h : KleisliHom a b} → join f (join g h) ≡ join (join f g) h
      assoc {a} {b} {c} {d} {f} {g} {h} =  let open ≡-Reasoning in begin
            join f (join g h)
         ≡⟨⟩
             TMap μ d ・ ( FMap T f ・ ( TMap μ c ・ ( FMap T g ・  h ))) 
         ≡⟨ ( begin
                 (  TMap μ d ・ (  FMap T f ・ (  TMap μ c ・ (  FMap T g ・ h ) ) ) ) 
             ≡⟨ Right C ( Right C (Assoc C)) ⟩
                 (  TMap μ d ・ (  FMap T f ・ (  ( TMap μ c ・ FMap T g ) ・ h ) ) ) 
             ≡⟨  Assoc C  ⟩
                 ( (  TMap μ d ・  FMap T f ) ・  ( ( TMap μ c ・ FMap T g ) ・ h ) ) 
             ≡⟨  Assoc C  ⟩
                 ( ( ( TMap μ d ・  FMap T f ) ・  ( TMap μ c ・ FMap T g ) )  ・ h  ) 
             ≡⟨ sym ( Left  C (Assoc C )) ⟩
                 ( (  TMap μ d  ・ (  FMap T f  ・  ( TMap μ c ・ FMap T g ) ) )  ・ h  ) 
             ≡⟨ Left C ( Right C (Assoc C)) ⟩
                 ( (  TMap μ d  ・ ( ( FMap T f   ・  TMap μ c )  ・  FMap T g  ) ) ・ h  ) 
             ≡⟨ Left C (Assoc C)⟩
                 ( (  ( TMap μ d  ・  ( FMap T f   ・  TMap μ c ) )  ・  FMap T g  ) ・ h  ) 
             ≡⟨ Left C ( Left C ( Right C  ( IsNTrans.commute (isNTrans  μ )  ) ))  ⟩
                ( ( ( TMap μ d ・ ( TMap μ (FObj T d) ・ FMap (T ● T) f ) ) ・ FMap T g ) ・ h )
             ≡⟨ sym ( Left  C (Assoc C)) ⟩
                ( ( TMap μ d ・ ( ( TMap μ (FObj T d) ・ FMap (T ● T) f ) ・ FMap T g ) ) ・ h )
             ≡⟨ sym ( Left C ( Right  C (Assoc C))) ⟩
                ( ( TMap μ d ・ ( TMap μ (FObj T d) ・ ( FMap (T ● T) f ・ FMap T g ) ) ) ・ h )
             ≡⟨ sym ( Left C ( Right C (Right C (IsFunctor.distr (isFunctor T ) ) ) )) ⟩
                ( ( TMap μ d ・ ( TMap μ (FObj T d) ・ FMap T (( FMap T f ・ g )) ) ) ・ h )
             ≡⟨ Left C (Assoc C)  ⟩
                ( ( ( TMap μ d ・ TMap μ (FObj T d) ) ・ FMap T (( FMap T f ・ g )) ) ・ h )
             ≡⟨ Left C (Left C ( IsMonad.assoc (Monad.isMonad M ) ) ) ⟩
                ( ( ( TMap μ d ・ FMap T (TMap μ d) ) ・ FMap T (( FMap T f ・ g )) ) ・ h )
             ≡⟨ sym ( Left C (Assoc C)) ⟩
                ( ( TMap μ d ・ ( FMap T (TMap μ d) ・ FMap T (( FMap T f ・ g )) ) ) ・ h )
             ≡⟨ sym (Assoc C) ⟩
                ( TMap μ d ・ ( ( FMap T (TMap μ d) ・ FMap T (( FMap T f ・ g )) ) ・ h ) )
             ≡⟨ sym (Right C ( Left C (IsFunctor.distr (isFunctor T ))))  ⟩
                 (  TMap μ d ・ (  FMap T (( TMap μ d ・ (  FMap T f ・ g ) ) ) ・ h ) )  
             ∎ ) ⟩
            TMap μ d ・ (  FMap T (( TMap μ d ・ (  FMap T f ・ g ) ) ) ・ h )   
         ≡⟨⟩
            join (join f g) h
         ∎

--
--       U : Functor C    D   
--       F : Functor D    C      
--
--       natural iso in Hom C    (F a) b   ←-→  Hom D    a U(b) 
--
--       Hom C    (F a) b     ←---→  Hom D    a U(b) 
--           |                       |
--         Ff|                      f|
--           |                       |
--           ↓                       ↓
--       Hom C    (F (f a)) b ←---→  Hom D    (f a) U(b)
--
--       Hom C    (F a) b     ←---→  Hom D    a U(b) 
--           |                       |
--           |f                      |Uf
--           |                       |  
--           ↓                       ↓ 
--       Hom C    (F a) (f b) ←---→  Hom D    a U(f b) 
--
--

record UnityOfOppsite ( C D : Category )  ( U : Functor C D ) ( F : Functor D C ) : Set (suc zero) where
     field
         left  : {a : Obj D} { b : Obj C } → Hom D a ( FObj U b ) → Hom C (FObj F a) b
         right   : {a : Obj D} { b : Obj C } → Hom C (FObj F a) b   → Hom D a ( FObj U b )
         left-injective : {a : Obj D} { b : Obj C } → {f : Hom D a (FObj U b) }  → right ( left f ) ≡ f 
         right-injective  : {a : Obj D} { b : Obj C } → {f : Hom C (FObj F a) b }  → left ( right f ) ≡ f 
         ---  naturality of Φ
         right-commute1 : {a : Obj D} {b b' : Obj C } →
                       { f : Hom C (FObj F a) b }  → { k : Hom C b b' } →
                        right ( C [ k o  f ] )  ≡ D [ FMap U k o right f  ] 
         right-commute2 : {a a' : Obj D} {b : Obj C } →
                       { f : Hom C (FObj F a) b }  → { h : Hom D a' a } →
                        right ( C [ f  o  FMap F h ] )  ≡  D [ right f o h ] 
     left-commute1 : {a : Obj D} {b b' : Obj C } →
                       { g : Hom D a (FObj U b)}  → { k : Hom C b b' } →
                         C [ k o  left g ]    ≡ left ( D [ FMap U k o g  ] ) 
     left-commute1 {a} {b} {b'} {g} {k} =  let open  ≡-Reasoning  in begin
            C [ k o  left g ] 
         ≡⟨ sym right-injective  ⟩
            left ( right ( C [ k o  left g ] ) )
         ≡⟨ cong ( λ z → left z  ) right-commute1 ⟩
            left (D [ FMap U k o right (left g) ])
         ≡⟨ cong ( λ z →  left ( D [ FMap U k o z ]  ))   left-injective    ⟩
            left ( D [ FMap U k o g  ] )
         ∎
     left-commute2 : {a a' : Obj D} {b : Obj C } →
                       { g : Hom D a (FObj U b) }  → { h : Hom D a' a } →
                         C [ left g  o  FMap F h ]    ≡  left ( D [ g o h ] ) 
     left-commute2 {a} {a'} {b} {g} {h} =  let open  ≡-Reasoning  in begin
            C [ left g o FMap F h ]
         ≡⟨  sym right-injective  ⟩
            left (right (C [ left g o FMap F h ]))
         ≡⟨ cong ( λ z →  left z ) right-commute2  ⟩
              left (D [ right (left g) o h ])
         ≡⟨ cong ( λ z →  left ( D [ z  o h ] )) left-injective   ⟩
            left (D [ g o h ])
         ∎


_・_ : {a b c : Obj Sets } ( f : Hom Sets b c ) ( g : Hom Sets a b ) → Hom Sets a c
f ・ g  = Sets [ f  o g ]

U :  ( T : Functor Sets Sets ) → { m : Monad T } → Functor (Kleisli  Sets T m)  Sets
U T {m} = record {
       FObj = FObj T
     ; FMap = λ {a} {b} f x → TMap ( μ m ) b ( FMap T ( f ) x )
     ; isFunctor = record { identity =  IsMonad.unity2 (isMonad m)  ; distr = distr }
  } where
      open Monad
      distr :  {a b c : Obj (Kleisli Sets T m)} {f : Hom (Kleisli Sets T m) a b} {g : Hom (Kleisli Sets T m) b c} → 
           (λ x → TMap (μ m) c (FMap T ((Kleisli Sets T m [ g o f ])) x))
               ≡ (( (λ x → TMap (μ m) c (FMap T g x)) ・ (λ x → TMap (μ m) b (FMap T f x)) ))  
      distr {a} {b} {c} {f} {g}  = let open ≡-Reasoning in begin
            ( TMap (μ m) c ・ FMap T ((Kleisli Sets T m [ g o f ])) )
         ≡⟨⟩
            ( TMap (μ m) c ・ FMap T ( ( TMap (μ m) c  ・ ( FMap T ( g ) ・ f ) ) ) )
         ≡⟨ Right Sets {_} {_} {_} {TMap (μ m) c} {_} {_} ( IsFunctor.distr (Functor.isFunctor T) )  ⟩
            ( TMap (μ m) c  ・ (  FMap T ( TMap (μ m) c) ・ FMap T ( ( FMap T g  ・ f ) ) ) ) 
         ≡⟨ sym ( Left Sets  (IsMonad.assoc (isMonad m )))  ⟩
           ( ( TMap (μ m) c ・ TMap (μ m) (FObj T c) ) ・ (FMap T (( FMap T g ・ f ))) )
         ≡⟨ Right Sets {_} {_} {_} {TMap (μ m) c} ( Right Sets {_} {_} {_} {TMap (μ m) (FObj T c)} ( IsFunctor.distr (Functor.isFunctor T) ) ) ⟩
           ( ( TMap (μ m) c ・ TMap (μ m) (FObj T c) ) ・ ( FMap T ( FMap T g) ・ FMap T ( f ) ) )
         ≡⟨ sym ( Right Sets {_} {_} {_} {TMap (μ m) c} ( Left Sets (IsNTrans.commute ( NTrans.isNTrans (μ m))))) ⟩
            ( ( TMap (μ m) c ・ FMap T g ) ・ ( TMap (μ m) b ・ FMap T f ) ) 
         ∎


F :  ( T : Functor Sets Sets ) → {m : Monad T} → Functor Sets ( Kleisli Sets T m)
F T {m} = record {
       FObj = λ a → a ; FMap = λ {a} {b} f →  λ x →  TMap (η m) b (f x) 
     ; isFunctor = record { identity = refl ; distr = distr }
  } where
      open Monad
      distr : {a b c : Obj Sets} {f : Hom Sets a b} {g : Hom Sets b c} →  (λ x → TMap (η m) c ((( g ・ f )) x))  ≡
          ( (Kleisli Sets T m ) [ (λ x → TMap (η m) c (g x))  o  (λ x → TMap (η m) b (f x) ) ] )
      distr {a} {b} {c} {f} {g}  = let open ≡-Reasoning in  ( begin
           ( TMap (η m) c ・ ( g ・ f ) )
         ≡⟨ Left Sets {_} {_} {_} {( TMap (η m) c ・ g ) } ( sym ( IsNTrans.commute ( NTrans.isNTrans (η m) ) ))  ⟩
           ( ( FMap T g  ・ TMap (η m) b )  ・ f )
         ≡⟨ sym ( IsCategory.idL ( Category.isCategory Sets )) ⟩
           ( ( λ x → x ) ・ ( ( FMap T g  ・ TMap (η m) b )  ・ f ) )
         ≡⟨ sym ( Left Sets  (IsMonad.unity2 (isMonad m ))) ⟩
            ( ( TMap (μ m) c ・ FMap T (TMap (η m) c) ) ・ ( FMap T g ・  ( TMap (η m) b ・ f ) ) )
         ≡⟨ sym ( Right Sets {_} {_} {_} {TMap (μ m) c} {_} ( Left Sets {_} {_} {_} { FMap T (( TMap (η m) c  ・ g ) )} ( IsFunctor.distr (Functor.isFunctor T) )))  ⟩
           ( TMap (μ m) c ・ ( (  FMap T (( TMap (η m) c  ・ g ) ) ・ ( TMap (η m) b  ・ f ) ) ) )
         ∎ )

--
--   Hom Sets     a         (FObj U b)   = Hom Sets a (T b)
--   Hom Kleisli (FObj F a) b            = Hom Sets a (T b)
--

lemma→ :  ( T : Functor Sets Sets ) → (m : Monad T ) → UnityOfOppsite (Kleisli Sets T m) Sets (U T {m} ) (F T {m})
lemma→ T m =
     let open Monad in
      record {
          left  = λ {a} {b} f → f
       ;  right   = λ {a} {b} f x → TMap (μ m) b ( TMap ( η m ) (FObj T b) ( f x ) )
       ;  left-injective = left-injective
       ;  right-injective = right-injective
       ;  right-commute1 = right-commute1
       ;  right-commute2 =  right-commute2 
     } where
         open Monad 
         left-injective : {a : Obj Sets} {b : Obj (Kleisli Sets T m)}
                {f : Hom Sets a (FObj (U T {m}) b)} → (λ x → TMap (μ m) b (TMap (η m) (FObj T b) (f x))) ≡ f
         left-injective {a} {b} {f} = let open ≡-Reasoning in begin
             ( TMap (μ m) b  ・ ( TMap (η m) (FObj T b)  ・ f ) )
           ≡⟨ Left Sets ( IsMonad.unity1 ( isMonad m )  )  ⟩
             ( id Sets (FObj (U T {m}) b)  ・ f ) 
           ≡⟨ IsCategory.idL ( isCategory Sets )  ⟩
             f
           ∎
         right-injective : {a : Obj Sets} {b : Obj (Kleisli Sets T m)} {f : Hom (Kleisli Sets T m) (FObj (F T {m}) a) b}
            →  (λ x → TMap (μ m) b (TMap (η m) (FObj T b) (f x)))  ≡ f
         right-injective {a} {b} {f} = let open ≡-Reasoning in ( begin
              ( TMap (μ m) b  ・ ( TMap (η m) (FObj T b)  ・ f ) )
           ≡⟨ Left Sets ( IsMonad.unity1 ( isMonad m ) )  ⟩
             f
           ∎ )
         right-commute1 : {a : Obj Sets} {b b' : Obj (Kleisli Sets T m)} {f : Hom (Kleisli Sets T m) (FObj (F T {m}) a) b} {k : Hom (Kleisli Sets T m) b b'} →
               (λ x → TMap (μ m) b' (TMap (η m) (FObj T b') ((Kleisli Sets T m [ k o f ] ) x)))
                  ≡ (( FMap (U T {m}) k ・ (λ x → TMap (μ m) b (TMap (η m) (FObj T b) (f x))) ))
         right-commute1 {a} {b} {b'} {f} {k} = let open ≡-Reasoning in begin
              ( TMap (μ m) b'  ・ ( TMap (η m) (FObj T b')  ・ (Kleisli Sets T m [ k o f ] ) ) )
            ≡⟨⟩
              TMap (μ m) b'  ・ ( TMap (η m) (FObj T b')  ・ ( TMap (μ m) b' ・ ( FMap T (k)  ・ f  )))
            ≡⟨ Left Sets  ( IsMonad.unity1 ( isMonad m ))  ⟩
              TMap (μ m) b'  ・ ( FMap T (k)  ・  f  )
            ≡⟨ Right Sets {_} {_} {_} {TMap ( μ m ) b' ・ FMap T ( k )} ( Left Sets ( sym ( IsMonad.unity1 ( isMonad m )  )  ) )  ⟩
              ( TMap ( μ m ) b' ・ FMap T ( k ) ) ・ ( TMap (μ m) b  ・ ( TMap (η m) (FObj T b)  ・ f ) ) 
            ≡⟨⟩
              ( FMap (U T {m}) k ・ ( TMap (μ m) b  ・ ( TMap (η m) (FObj T b)  ・ f ) ) )
            ∎ 
         right-commute2 :   {a a' : Obj Sets} {b : Obj (Kleisli Sets T m)} {f : Hom (Kleisli Sets T m) (FObj (F T {m}) a) b} {h : Hom Sets a' a} →
                (λ x → TMap (μ m) b (TMap (η m) (FObj T b) ((Kleisli Sets T m [ f o FMap (F T {m}) h ] ) x)))
                    ≡ (( (λ x → TMap (μ m) b (TMap (η m) (FObj T b) (f x)))・ h ))
         right-commute2 {a} {a'} {b} {f} {h} = let open ≡-Reasoning in begin
              TMap (μ m) b ・ (TMap (η m) (FObj T b) ・ ((Kleisli Sets T m [ f o FMap (F T {m}) h ] )))
            ≡⟨⟩
              TMap (μ m) b ・ (TMap (η m) (FObj T b) ・ ( (TMap (μ m) b ・ FMap T  f ) ・ ( TMap (η m) a ・ h )))
            ≡⟨  Left Sets (IsMonad.unity1 ( isMonad m ))  ⟩
              (TMap (μ m) b ・ FMap T  f ) ・ ( TMap (η m) a ・ h )
            ≡⟨  Right Sets {_} {_} {_} {TMap (μ m) b} ( Left Sets ( IsNTrans.commute ( isNTrans (η m)  )))    ⟩
              TMap (μ m) b ・ (( TMap (η m) (FObj T  b)・ f ) ・ h )
            ∎



lemma← :  ( U F : Functor Sets Sets ) → UnityOfOppsite Sets Sets U F → Monad ( U ● F )
lemma← U F uo = record {
       η = η
    ;  μ = μ
    ;  isMonad = record {
            unity1 = unity1
          ; unity2 = unity2
          ; assoc = assoc
       }
  } where
     open UnityOfOppsite
     T =  U ● F
     η-comm : {a b : Obj Sets} {f : Hom Sets a b} → ( FMap (U ● F) f ・ (λ x → right uo (λ x₁ → x₁) x) )
               ≡ (  (λ x → right uo (λ x₁ → x₁) x) ・ FMap (idFunctor {_} {Sets} ) f )
     η-comm {a} {b} {f} = let open ≡-Reasoning in begin
             FMap (U ● F) f ・ (right uo (λ x₁ → x₁) )
         ≡⟨ sym (right-commute1 uo) ⟩
             right uo ( FMap F f ・ (λ x₁ → x₁) )
         ≡⟨ right-commute2 uo ⟩
             right uo (λ x₁ → x₁)  ・ FMap ( idFunctor {_} {Sets} ) f 
         ∎
     η :  NTrans (idFunctor {_} {Sets}) T
     η =  record { TMap = λ a x → (right uo) (λ x → x ) x ; isNTrans = record { commute = η-comm  } }
     μ-comm : {a b : Obj Sets} {f : Hom Sets a b} → (( FMap T f ・ (λ x → FMap U (left uo (λ x₁ → x₁)) x) ))
         ≡ (( (λ x → FMap U (left uo (λ x₁ → x₁)) x) ・ FMap (T ● T) f ))
     μ-comm {a} {b} {f} = let open ≡-Reasoning in begin
            FMap T f ・  FMap U (left uo (λ x₁ → x₁)) 
         ≡⟨⟩
            FMap U (FMap F f ) ・  FMap U (left uo (λ x₁ → x₁)) 
         ≡⟨ sym ( IsFunctor.distr ( Functor.isFunctor U)) ⟩
            FMap U (FMap F f  ・ left uo (λ x₁ → x₁)) 
         ≡⟨ cong ( λ z → FMap U z ) (left-commute1 uo) ⟩
            FMap U ( left uo (FMap U (FMap F f) ・ (λ x₁ → x₁) ) )
         ≡⟨ sym ( cong ( λ z → FMap U z ) (left-commute2 uo)) ⟩
            FMap U ((left uo (λ x₁ → x₁))  ・ (FMap F (FMap U (FMap F f ))))
         ≡⟨  IsFunctor.distr ( Functor.isFunctor U) ⟩
            FMap U (left uo (λ x₁ → x₁))  ・ FMap U (FMap F (FMap U (FMap F f )))
         ≡⟨⟩
            FMap U (left uo (λ x₁ → x₁))  ・ FMap (T ● T) f
         ∎
     μ :  NTrans (T ● T) T
     μ = record { TMap = λ a x → FMap U ( left uo  (λ x → x)) x ; isNTrans = record { commute = μ-comm  } }
     unity1 : {a : Obj Sets} → (( TMap μ a ・ TMap η (FObj (U ● F) a) )) ≡ id Sets (FObj (U ● F) a)
     unity1 {a} =  let open ≡-Reasoning in begin
            TMap μ a ・ TMap η (FObj (U ● F) a)
         ≡⟨⟩
             FMap U (left uo (λ x₁ → x₁)) ・ right uo (λ x₁ → x₁)
         ≡⟨ sym  (right-commute1 uo )  ⟩
             right uo ( left uo (λ x₁ → x₁) ・ (λ x₁ → x₁) )
         ≡⟨  left-injective uo  ⟩
            id Sets (FObj (U ● F) a)
         ∎
     unity2 : {a : Obj Sets} →  (( TMap μ a ・ FMap (U ● F) (TMap η a) )) ≡ id Sets (FObj (U ● F) a)
     unity2 {a} =  let open ≡-Reasoning in begin
            TMap μ a ・ FMap (U ● F) (TMap η a)
         ≡⟨⟩
            FMap U (left uo (λ x₁ → x₁)) ・  FMap U (FMap F (right uo (λ x₁ → x₁)))
         ≡⟨ sym ( IsFunctor.distr (isFunctor U))  ⟩
            FMap U (left uo (λ x₁ → x₁) ・  FMap F (right uo (λ x₁ → x₁)))
         ≡⟨ cong ( λ z → FMap U z ) (left-commute2  uo)  ⟩
             FMap U (left uo ((λ x₁ → x₁) ・ right uo (λ x₁ → x₁) ))
         ≡⟨ cong ( λ z → FMap U z ) (right-injective  uo)  ⟩
             FMap U ( id Sets (FObj F a) )
         ≡⟨   IsFunctor.identity (isFunctor U) ⟩
            id Sets (FObj (U ● F) a)
         ∎
     assoc : {a : Obj Sets} → (( TMap μ a ・ TMap μ (FObj (U ● F) a) )) ≡ (( TMap μ a ・ FMap (U ● F) (TMap μ a) ))
     assoc {a} =  let open ≡-Reasoning in begin
            TMap μ a ・ TMap μ (FObj (U ● F) a)
         ≡⟨⟩
            FMap U (left uo (λ x₁ → x₁)) ・ FMap U (left uo (λ x₁ → x₁))
         ≡⟨ sym ( IsFunctor.distr (isFunctor U ))   ⟩  
            FMap U (left uo (λ x₁ → x₁) ・ left uo (λ x₁ → x₁))
         ≡⟨ cong ( λ z → FMap U z ) ( left-commute1 uo  )   ⟩
            FMap U (left uo ((λ x₁ → x₁) ・ FMap U  (left uo (λ x₁ → x₁))) ) 
         ≡⟨ sym ( cong ( λ z → FMap U z ) ( left-commute2 uo  )  ) ⟩
            FMap U (left uo (λ x₁ → x₁) ・ FMap F (FMap U (left uo (λ x₁ → x₁))))
         ≡⟨  IsFunctor.distr (isFunctor U )   ⟩
            FMap U (left uo (λ x₁ → x₁)) ・ FMap U (FMap F (FMap U (left uo (λ x₁ → x₁))))
         ≡⟨⟩
            TMap μ a ・ FMap (U ● F) (TMap μ a) 
         ∎

