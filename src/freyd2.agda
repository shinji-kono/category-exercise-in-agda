open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
open import Category.Sets renaming ( _o_ to _*_ )

module freyd2 
   where

open import HomReasoning
open import cat-utility 
open import Relation.Binary.Core
open import Function

----------
--
-- A is locally small complete and K{*}↓U has preinitial full subcategory, U is an adjoint functor
--
--    a : Obj A
--    U : A → Sets
--    U ⋍ Hom (a,-)
--

open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym ; resp )

-- A is localy small
postulate ≡←≈ :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a b : Obj A } { x y : Hom A a b } →  (x≈y : A [ x ≈ y  ]) → x ≡ y

import Axiom.Extensionality.Propositional
-- Extensionality a b = {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g → ( λ x → f x ≡ λ x → g x )
-- postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Axiom.Extensionality.Propositional.Extensionality c₂ c₂

----
--
--  Hom ( a, - ) is Object mapping in Yoneda Functor
--
----

open NTrans 
open Functor
open Limit
open IsLimit
open import Category.Cat

open Representable

_↓_ :  { c₁ c₂ ℓ : Level}  { c₁' c₂' ℓ' : Level} { A : Category c₁ c₂ ℓ } { B : Category c₁' c₂' ℓ' }
    →  ( F G : Functor A B )
    →  Category  (c₂' ⊔ c₁) (ℓ' ⊔ c₂) ℓ
_↓_   { c₁} {c₂} {ℓ} {c₁'} {c₂'} {ℓ'}  { A } { B } F G  = CommaCategory
         where open import Comma1 F G

open Complete
open HasInitialObject
open import Comma1
open CommaObj
open LimitPreserve

-- Representable Functor U preserve limit , so K{*}↓U is complete
--
--    Yoneda A b =  λ a → Hom A a b    : Functor A Sets
--                                     : Functor Sets A

YonedaFpreserveLimit0 : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (I : Category c₁ c₂ ℓ)
      (b : Obj A ) 
      (Γ : Functor I (Category.op A)) (limita : Limit I (Category.op A) Γ) →
        IsLimit I Sets (Yoneda A (≡←≈ A) b ○ Γ) (FObj (Yoneda A (≡←≈ A) b) (a0 limita)) (LimitNat I (Category.op A) Sets Γ (a0 limita) (t0 limita) (Yoneda A (≡←≈ A) b))
YonedaFpreserveLimit0 {c₁} {c₂} {ℓ} A I b Γ lim = record {
         limit = λ a t → ψ a t
       ; t0f=t = λ {a t i} → t0f=t0 a t i
       ; limit-uniqueness = λ {b} {t} {f} t0f=t → limit-uniqueness0 {b} {t} {f} t0f=t 
    } where 
      opA = Category.op A
      hat0 :  NTrans I Sets (K I Sets (FObj (Yoneda A (≡←≈ A) b) (a0 lim))) (Yoneda A (≡←≈ A) b ○ Γ)
      hat0 = LimitNat I opA Sets Γ (a0 lim) (t0 lim) (Yoneda A (≡←≈ A) b)
      haa0 : Obj Sets
      haa0 = FObj (Yoneda A (≡←≈ A) b) (a0 lim)
      ta : (a : Obj Sets) ( x : a ) ( t : NTrans I Sets (K I Sets a) (Yoneda A (≡←≈ A) b ○ Γ)) → NTrans I opA (K I opA b ) Γ
      ta a x t = record { TMap = λ i → (TMap t i ) x ; isNTrans = record { commute = commute1 } } where
         commute1 :  {a₁ b₁ : Obj I} {f : Hom I a₁ b₁} →
                opA [ opA [ FMap Γ f o TMap t a₁ x ] ≈ opA [ TMap t b₁ x o FMap (K I opA b) f ]  ]
         commute1  {a₁} {b₁} {f} = let open ≈-Reasoning opA in begin
                 FMap Γ f o TMap t a₁ x
             ≈⟨⟩
                 ( ( FMap (Yoneda A (≡←≈ A) b  ○ Γ ) f )  *  TMap t a₁ ) x
             ≈⟨ ≈←≡ ( cong (λ k → k x ) (IsNTrans.commute (isNTrans t)) ) ⟩
                 ( TMap t b₁ * ( FMap (K I Sets a) f ) ) x
             ≈⟨⟩
                 ( TMap t b₁ * id1 Sets a ) x
             ≈⟨⟩
                 TMap t b₁ x 
             ≈↑⟨ idR ⟩
                 TMap t b₁ x o id1 A b
             ≈⟨⟩
                 TMap t b₁ x o FMap (K I opA b) f 
             ∎ 
      ψ  :  (X : Obj Sets)  ( t : NTrans I Sets (K I Sets X) (Yoneda A (≡←≈ A) b ○ Γ))
          →  Hom Sets X (FObj (Yoneda A (≡←≈ A) b) (a0 lim))
      ψ X t x = FMap (Yoneda A (≡←≈ A) b) (limit (isLimit lim) b (ta X x t )) (id1 A b )
      t0f=t0 : (a : Obj Sets ) ( t : NTrans I Sets (K I Sets a) (Yoneda A (≡←≈ A) b ○ Γ)) (i : Obj I)
           → Sets [ Sets [ TMap (LimitNat I opA Sets Γ (a0 lim) (t0 lim) (Yoneda A (≡←≈ A) b)) i o ψ a t ] ≈ TMap t i ]
      t0f=t0 a t i = let open ≈-Reasoning opA in extensionality opA ( λ x →  (≡←≈ A) ( begin 
                 ( Sets [ TMap (LimitNat I opA Sets Γ (a0 lim) (t0 lim) (Yoneda A (≡←≈ A) b)) i o ψ a t  ] ) x
             ≈⟨⟩
                FMap (Yoneda A (≡←≈ A) b) ( TMap (t0 lim) i) (FMap (Yoneda A (≡←≈ A) b) (limit (isLimit lim) b (ta a x t )) (id1 A b ))
             ≈⟨⟩ -- FMap (Hom A b ) f g  = A [ f o g  ]
                TMap (t0 lim) i o (limit (isLimit lim) b (ta a x t ) o id1 A b )
             ≈⟨  cdr idR ⟩
                TMap (t0 lim) i o limit (isLimit lim) b (ta a x t ) 
             ≈⟨  t0f=t (isLimit lim) ⟩
                TMap (ta a x t) i
             ≈⟨⟩
                 TMap t i x
             ∎  ))
      limit-uniqueness0 :  {a : Obj Sets} {t : NTrans I Sets (K I Sets a) (Yoneda A (≡←≈ A) b ○ Γ)} {f : Hom Sets a (FObj (Yoneda A (≡←≈ A) b) (a0 lim))} →
        ({i : Obj I} → Sets [ Sets [ TMap (LimitNat I opA Sets Γ (a0 lim) (t0 lim) (Yoneda A (≡←≈ A) b)) i o f ] ≈ TMap t i ]) →
        Sets [ ψ a t ≈ f ]
      limit-uniqueness0 {a} {t} {f} t0f=t = let open ≈-Reasoning opA in extensionality A ( λ x →  (≡←≈ A) ( begin 
                  ψ a t x
             ≈⟨⟩
                 FMap (Yoneda A (≡←≈ A) b) (limit (isLimit lim) b (ta a x t )) (id1 A b )
             ≈⟨⟩
                 limit (isLimit lim) b (ta a x t ) o id1 A b 
             ≈⟨ idR ⟩
                 limit (isLimit lim) b (ta a x t ) 
             ≈⟨ limit-uniqueness (isLimit lim) ( λ {i} → ≈←≡ ( cong ( λ g → g x )( t0f=t {i} ))) ⟩
                  f x
             ∎  ))


YonedaFpreserveLimit : {c₁ c₂ ℓ : Level} (I : Category c₁ c₂ ℓ) (A : Category c₁ c₂ ℓ)
       (b : Obj A ) → LimitPreserve I (Category.op A) Sets (Yoneda A (≡←≈ A) b) 
YonedaFpreserveLimit I opA b = record {
       preserve = λ Γ lim → YonedaFpreserveLimit0 opA I b Γ lim
   } 


-- K{*}↓U has preinitial full subcategory if U is representable
--     if U is representable,  K{*}↓U has initial Object ( so it has preinitial full subcategory )

open CommaHom

data * {c : Level} : Set c where
  OneObj : *

KUhasInitialObj : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ)
      (a : Obj A )
      → HasInitialObject  ( K (Category.op A) Sets * ↓ (Yoneda A (≡←≈ A) a) ) ( record  { obj = a ; hom = λ x → id1 A a } )
KUhasInitialObj {c₁} {c₂} {ℓ} A a = record {
           initial =  λ b → initial0 b
         ; uniqueness =  λ f → unique f
     } where
         opA = Category.op A
         commaCat : Category  (c₂ ⊔ c₁) c₂ ℓ
         commaCat = K opA Sets * ↓ Yoneda A (≡←≈ A) a
         initObj  : Obj (K opA Sets * ↓ Yoneda A (≡←≈ A) a)
         initObj = record { obj = a ; hom = λ x → id1 A a }
         comm2 : (b : Obj commaCat) ( x : * ) → ( Sets [ FMap (Yoneda A (≡←≈ A) a) (hom b OneObj) o (λ x₁ → id1 A a) ] )  x ≡ hom b x
         comm2 b OneObj = let open ≈-Reasoning opA in  (≡←≈ A) ( begin
                ( Sets [ FMap (Yoneda A (≡←≈ A) a) (hom b OneObj) o (λ x₁ → id1 A a) ] ) OneObj
             ≈⟨⟩
                FMap (Yoneda A (≡←≈ A) a) (hom b OneObj) (id1 A a)
             ≈⟨⟩
                hom b OneObj o id1 A a
             ≈⟨ idR ⟩
                hom b OneObj 
             ∎  )
         comm1 : (b : Obj commaCat) → Sets [ Sets [ FMap (Yoneda A (≡←≈ A) a) (hom b OneObj) o hom initObj ] ≈ Sets [ hom b o FMap (K opA Sets *) (hom b OneObj) ] ]
         comm1 b = let open ≈-Reasoning Sets in begin
                FMap (Yoneda A (≡←≈ A) a) (hom b OneObj) o ( λ x → id1 A a )
             ≈⟨ extensionality A ( λ x → comm2 b x ) ⟩
                hom b 
             ≈⟨⟩
                hom b o FMap (K opA Sets *) (hom b OneObj) 
             ∎ 
         initial0 : (b : Obj commaCat) →
            Hom commaCat initObj b
         initial0 b = record {
                arrow = hom b OneObj
              ; comm = comm1 b }
         -- what is comm f ?
         comm-f :  (b : Obj (K opA Sets * ↓ (Yoneda A (≡←≈ A) a))) (f : Hom (K opA Sets * ↓ Yoneda A (≡←≈ A) a) initObj b)
            → Sets [ Sets [ FMap  (Yoneda A (≡←≈ A) a) (arrow f) o ( λ x → id1 A a ) ]
               ≈ Sets [ hom b  o  FMap  (K opA Sets *) (arrow f) ]  ] 
         comm-f b f = comm f
         unique : {b : Obj (K opA Sets * ↓ Yoneda A (≡←≈ A) a)}  (f : Hom (K opA Sets * ↓ Yoneda A (≡←≈ A) a) initObj b)
                → (K opA Sets * ↓ Yoneda A (≡←≈ A) a) [ f ≈ initial0 b ]
         unique {b} f = let open ≈-Reasoning opA in begin
                arrow f
             ≈↑⟨ idR ⟩
                arrow f o id1 A a
             ≈⟨⟩
                ( Sets [ FMap  (Yoneda A (≡←≈ A) a) (arrow f) o id1 Sets (FObj (Yoneda A (≡←≈ A) a) a)  ] ) (id1 A a)
             ≈⟨⟩
               ( Sets [ FMap  (Yoneda A (≡←≈ A) a) (arrow f) o ( λ x → id1 A a ) ] ) OneObj
             ≈⟨ ≈←≡ ( cong (λ k → k OneObj ) (comm f )) ⟩
               ( Sets [ hom b  o  FMap  (K opA Sets *) (arrow f) ]  ) OneObj
             ≈⟨⟩
                hom b OneObj
             ∎ 

            

-- A is complete and K{*}↓U has preinitial full subcategory and U preserve limit then U is representable

-- if U preserve limit,  K{*}↓U has initial object from freyd.agda

≡-cong = Relation.Binary.PropositionalEquality.cong


ub : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (U : Functor A (Sets {c₂}) )(b : Obj A) (x : FObj U b )
   → Hom Sets (FObj (K A Sets *) b) (FObj U b)
ub A U b x OneObj = x
ob : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (U : Functor A (Sets {c₂}) )(b : Obj A) (x : FObj U b )
   → Obj ( K A Sets * ↓ U)
ob A U b x = record { obj = b ; hom = ub A U b x}
fArrow : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (U : Functor A (Sets {c₂}) )  {a b : Obj A} (f : Hom A a b) (x : FObj U a )
   → Hom ( K A Sets * ↓ U) ( ob A U a x ) (ob A U b (FMap U f x) )
fArrow A U {a} {b} f x = record { arrow = f ; comm = fArrowComm a b f x }
  where
        fArrowComm1 : (a b : Obj A) (f : Hom A a b) (x : FObj U a ) → (y : * ) → FMap U f ( ub A U a x y ) ≡ ub A U b (FMap U f x) y
        fArrowComm1 a b f x OneObj = refl
        fArrowComm : (a b : Obj A) (f : Hom A a b) (x : FObj U a ) → 
         Sets [ Sets [ FMap U f o hom (ob A U a x) ] ≈ Sets [ hom (ob A U b (FMap U f x)) o FMap (K A Sets *) f ] ]
        fArrowComm a b f x = extensionality Sets ( λ y → begin 
                ( Sets [ FMap U f o hom (ob A U a x) ] ) y 
             ≡⟨⟩
                FMap U f ( hom (ob A U a x) y )
             ≡⟨⟩
                FMap U f ( ub A U a x y )
             ≡⟨ fArrowComm1 a b f x y ⟩
                ub A U b (FMap U f x) y
             ≡⟨⟩
                hom (ob A U b (FMap U f x)) y
             ∎ ) where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning


-- if K{*}↓U has initial Obj, U is representable

UisRepresentable : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) 
     (U : Functor (Category.op A) (Sets {c₂}) )
     ( i : Obj ( K (Category.op A) Sets * ↓ U) )
     (In : HasInitialObject ( K (Category.op A) Sets * ↓ U) i ) 
       → Representable A (≡←≈ A) U (obj i)
UisRepresentable A U i In = record {
        repr→ = record { TMap = tmap1 ; isNTrans = record { commute = comm1 } }
        ; repr← = record { TMap = tmap2 ; isNTrans = record { commute = comm2 } }
        ; reprId→  = iso→ 
        ; reprId←  = iso←
   } where
      opA = Category.op A
      comm11 : (a b : Obj opA) (f : Hom opA a b) (y : FObj U a ) →
         ( Sets [ FMap (Yoneda A (≡←≈ A) (obj i)) f o ( λ x → arrow (initial In (ob opA U a x))) ] ) y   
           ≡ (Sets [ ( λ x → arrow (initial In (ob opA U b x))) o FMap U f ] ) y
      comm11 a b f y = begin
               ( Sets [ FMap (Yoneda A (≡←≈ A) (obj i)) f o ( λ x → arrow (initial In (ob opA U a x))) ] ) y   
             ≡⟨⟩
                 opA [ f o arrow (initial In (ob opA U a y)) ]
             ≡⟨⟩
                 opA [ arrow ( fArrow opA U f y ) o arrow (initial In (ob opA U a y)) ]
             ≡⟨  (≡←≈ A) ( uniqueness In {ob opA U b (FMap U f y) } (( K opA Sets * ↓ U) [ fArrow opA U f y  o initial In (ob opA U a y)] ) ) ⟩
                arrow (initial In (ob opA U b (FMap U f y) ))
             ≡⟨⟩
                (Sets [ ( λ x → arrow (initial In (ob opA U b x))) o FMap U f ] ) y
             ∎  where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning
      tmap1 :  (b : Obj A) → Hom Sets (FObj U b) (FObj (Yoneda A (≡←≈ A) (obj i)) b)
      tmap1 b x = arrow ( initial In (ob opA U b x ) ) 
      comm1 : {a b : Obj opA} {f : Hom opA a b} → Sets [ Sets [ FMap (Yoneda A (≡←≈ A) (obj i)) f o tmap1 a ] ≈ Sets [ tmap1 b o FMap U f ] ]
      comm1 {a} {b} {f} = let open ≈-Reasoning Sets in begin
                FMap (Yoneda A (≡←≈ A) (obj i)) f o tmap1 a 
             ≈⟨⟩
                FMap (Yoneda A (≡←≈ A) (obj i)) f o ( λ x → arrow (initial In ( ob opA U a x )))  
             ≈⟨ extensionality Sets ( λ y → comm11 a b f y ) ⟩
                ( λ x → arrow (initial In (ob opA U b x))) o FMap U f 
             ≈⟨⟩
                tmap1 b o FMap U f 
             ∎ 
      comm21 : (a b : Obj opA) (f : Hom opA a b) ( y : Hom opA (obj i) a ) → 
          (Sets [ FMap U f o (λ x → FMap U x (hom i OneObj))] ) y ≡
                (Sets [ ( λ x → (FMap U x ) (hom i OneObj)) o (λ x → opA [ f o x ] ) ] )  y
      comm21 a b f y = begin
                FMap U f ( FMap U y (hom i OneObj))
             ≡⟨ ≡-cong ( λ k → k (hom i OneObj)) ( sym ( IsFunctor.distr (isFunctor U ) ) ) ⟩
                (FMap U (opA [ f o y ] ) ) (hom i OneObj) 
             ∎  where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning
      tmap2 :  (b : Obj A) → Hom Sets (FObj (Yoneda A (≡←≈ A) (obj i)) b) (FObj U b)
      tmap2 b x =  ( FMap U x ) ( hom i OneObj )
      comm2 : {a b : Obj opA} {f : Hom opA a b} → Sets [ Sets [ FMap U f o tmap2 a ] ≈
        Sets [ tmap2 b o FMap (Yoneda A (≡←≈ A) (obj i)) f ] ]
      comm2 {a} {b} {f} = let open ≈-Reasoning Sets in begin
                FMap U f o tmap2 a 
             ≈⟨⟩
                FMap U f o ( λ x → ( FMap U x ) ( hom i OneObj ) )
             ≈⟨ extensionality Sets ( λ y → comm21 a b f y ) ⟩
                ( λ x → ( FMap U x ) ( hom i OneObj ) ) o ( λ x → opA [ f o x  ]  )
             ≈⟨⟩
                ( λ x → ( FMap U x ) ( hom i OneObj ) ) o FMap (Yoneda A (≡←≈ A) (obj i)) f 
             ≈⟨⟩
                tmap2 b o FMap (Yoneda A (≡←≈ A) (obj i)) f 
             ∎
      iso0 : ( x : Obj opA) ( y : Hom opA (obj i ) x ) ( z : * )
         → ( Sets [ FMap U y o hom i ] ) z ≡ ( Sets [ ub opA U x (FMap U y (hom i OneObj)) o FMap (K opA Sets *) y ] ) z 
      iso0 x y  OneObj = refl
      iso→  : {x : Obj opA} → Sets [ Sets [ tmap1 x o tmap2 x ] ≈ id1 Sets (FObj (Yoneda A (≡←≈ A) (obj i)) x) ]
      iso→ {x} = let open ≈-Reasoning opA in extensionality Sets ( λ ( y : Hom opA (obj i ) x ) → (≡←≈ A) ( begin
               ( Sets [ tmap1 x o tmap2 x ] ) y
             ≈⟨⟩
                arrow ( initial In (ob opA U x (( FMap U y ) ( hom i OneObj ) ))) 
             ≈↑⟨  uniqueness In (record { arrow = y ; comm = extensionality Sets ( λ (z : * ) → iso0 x y z ) }  ) ⟩
               y
             ∎  ))
      iso←  : {x : Obj A} → Sets [ Sets [ tmap2 x o tmap1 x ] ≈ id1 Sets (FObj U x) ]
      iso← {x} = extensionality Sets ( λ (y : FObj U x ) → ( begin 
               ( Sets [ tmap2 x o tmap1 x ] ) y
             ≡⟨⟩
               ( FMap U ( arrow ( initial In (ob opA U x y ) ))  ) ( hom i OneObj )
             ≡⟨ ≡-cong (λ k → k OneObj) ( comm ( initial In (ob opA U x y ) )) ⟩
                 hom (ob opA U x y) OneObj
             ≡⟨⟩
               y
             ∎  ) ) where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning

-------------
-- Adjoint Functor Theorem
--

module Adjoint-Functor {c₁ c₂ ℓ : Level} (A B : Category c₁ c₂ ℓ) (I : Category c₁ c₂ ℓ) ( comp : Complete A I )
     (U : Functor A B )
     (i :  (b : Obj B) → Obj ( K A B b ↓ U) )
     (In :  (b : Obj B) → HasInitialObject ( K A B b ↓ U) (i b) ) 
        where

   tmap-η : (y : Obj B)  → Hom B y (FObj U (obj (i y)))
   tmap-η  y = hom (i y) 

   sobj  : {a : Obj B} {b : Obj A}  → ( f : Hom B a (FObj U b) ) → CommaObj (K A B a) U 
   sobj {a} {b} f = record {obj = b; hom =  f } 
   solution : {a : Obj B} {b : Obj A}  → ( f : Hom B a (FObj U b) ) → CommaHom (K A B a) U (i a) (sobj f)
   solution {a} {b} f = initial (In a) (sobj f)

   ηf : (a b  : Obj B)  → ( f : Hom B a b ) → Obj ( K A B a ↓ U)
   ηf a b f  = sobj ( B [ tmap-η b o f ]  )

   univ : {a : Obj B} {b : Obj A}  → (f : Hom B a (FObj U b))
       → B [ B [ FMap U (arrow (solution f)) o tmap-η a ]  ≈ f ]
   univ {a} {b} f = let open ≈-Reasoning B in begin
        FMap U (arrow (solution f)) o tmap-η a 
      ≈⟨ comm (initial (In a) (sobj f))  ⟩
        hom (sobj f) o FMap (K A B a) (arrow (initial (In a) (sobj f)))
      ≈⟨ idR ⟩
        f 
      ∎  

   unique : {a : Obj B} { b : Obj A } → { f : Hom B a (FObj U b) } → { g :  Hom A (obj (i a)) b} →
      B [ B [ FMap U g o  tmap-η a ]  ≈ f ] → A [ arrow (solution f)  ≈ g ]
   unique {a} {b} {f} {g} ugη=f = let open ≈-Reasoning A in begin
        arrow (solution f) 
      ≈↑⟨ ≈←≡ ( cong (λ k → arrow (solution k)) ( (≡←≈ B) ugη=f )) ⟩
        arrow (solution (B [ FMap U g o tmap-η a ] )) 
      ≈↑⟨ uniqueness (In a) (record { arrow = g ; comm = comm1 }) ⟩
        g 
      ∎  where
         comm1 : B [ B [ FMap U g o hom (i a) ] ≈ B [ B [ FMap U g o tmap-η a ] o FMap (K A B a) g ] ]
         comm1 = let open ≈-Reasoning B in sym idR

   UM : UniversalMapping B A U 
   UM = record {
         F = λ b → obj (i b) ;
         η = tmap-η ;
         _* = λ f → arrow (solution f)  ;
         isUniversalMapping = record {
            universalMapping  = λ {a} {b} {f} → univ f ;
            uniquness = unique
      }}

   -- Adjoint can be built as follows (same as univeral-mapping.agda )
   --
   -- F : Functor B A
   -- F = record {
   --  FObj = λ b →  obj (i b) 
   --  ; FMap = λ {x} {y} (f : Hom B x y ) → arrow (solution ( B [ tmap-η y o f ]  ))

   -- nat-ε : NTrans A A (F ○ U) identityFunctor
   -- nat-ε  = record {
   --       TMap = λ x → arrow ( solution (id1 B (FObj U x)))

   -- nat-η : NTrans B B identityFunctor (U ○ F)
   -- nat-η = record { TMap = λ y →  tmap-η y ; isNTrans = record { commute = comm1 } } where

   -- FisLeftAdjoint  : Adjunction B A U F nat-η nat-ε 
   -- FisLeftAdjoint  = record { isAdjunction = record {

open import Data.Product renaming (_×_ to _∧_  ) hiding ( <_,_> )
open import Category.Constructions.Product

module pro-ex {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) ( _*_ : Obj A → Obj A → Obj A ) 
      (*-iso : (a b c x : Obj A) → IsoS A (A × A)  x c (x , x ) (a , b  )) where

--  Hom A x c ≅ ( Hom A x a ) * ( Hom A x b )

    open IsoS

    import Axiom.Extensionality.Propositional
    postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m

    open import Category.Cat

    *eq :   {a b : Obj (A × A) } { x y : Hom (A × A) a b } →  (x≈y : (A × A) [ x ≈ y  ]) → x ≡ y
    *eq {a} {b} {x1 , x2} {y1 , y2} (eq1 , eq2) = cong₂ _,_ ( ≡←≈ A eq1 ) ( ≡←≈ A eq2 )

    opA = Category.op A
    prodFunctor : Functor (Category.op A) (Category.op (A × A))
    prodFunctor = record {
           FObj = λ x → x , x
         ; FMap = λ {x} {y} (f : Hom opA x y ) → f , f
         ; isFunctor = record { identity = ? ; distr = ? ; ≈-cong = ? }
      } 
    t00 : (a c d e : Obj opA) (f : Hom opA a c ) → Hom (A × A) (c , c) (d , e )
    t00 a c d e f = ≅→ (*-iso d e a  c) f  
    nat-* : {a b c : Obj A} → NTrans (Category.op A) (Sets {c₂}) (Yoneda A (≡←≈ A) c ) (Yoneda (A × A) *eq (a , b) ○ prodFunctor )   
    nat-* {a} {b} {c} = record { TMap = λ z f → ≅→ (*-iso a b c z) f  ; isNTrans = record { commute = nat-comm } } where
       nat-comm : {x y : Obj opA} {f : Hom opA x y} → 
            Sets [ Sets [ (λ g → opA [ f o proj₁ g ] , opA [ f o proj₂ g ]) o (λ f₁ → ≅→ (*-iso a b c x) f₁) ]
               ≈  Sets [ (λ f₁ → ≅→ (*-iso a b c y) f₁) o (λ g → opA [ f o g ])  ]  ]
       nat-comm {x} {y} {f} = f-extensionality (λ g → ( begin
          opA [ f o proj₁ (≅→ (*-iso a b c x) g) ] , opA [ f o proj₂ (≅→ (*-iso a b c x) g) ] ≡⟨ ? ⟩
          proj₁ (≅→ (*-iso a b c y) ( opA [ f o g ] )) , proj₂ (≅→ (*-iso a b c y) ( opA [ f o g ] ) ) ≡⟨ refl ⟩
          ≅→ (*-iso a b c y) ( opA [ f o g ] ) ∎ )  ) where open ≡-Reasoning


-- end

