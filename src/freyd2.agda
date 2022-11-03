open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
open import Category.Sets renaming ( _o_ to _*_ )

module freyd2 
   where

open import HomReasoning
open import cat-utility hiding (Yoneda ; Representable )
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

Yoneda : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) (a : Obj A) → Functor A (Sets {c₂})
Yoneda  {c₁} {c₂} {ℓ} A a = record {
    FObj = λ b → Hom A a b
  ; FMap = λ {x} {y} (f : Hom A x y ) → λ ( g : Hom A a x ) → A [ f o g ]    --   f : Hom A x y  → Hom Sets (Hom A a x ) (Hom A a y)
  ; isFunctor = record {
             identity =  λ {b} → extensionality A ( λ x → lemma-y-obj1 {b} x ) ;
             distr = λ {a} {b} {c} {f} {g} → extensionality A ( λ x → lemma-y-obj2 a b c f g x ) ;
             ≈-cong = λ eq → extensionality A ( λ x →  lemma-y-obj3 x eq ) 
        } 
    }  where
        lemma-y-obj1 : {b : Obj A } → (x : Hom A a b) →  A [ id1 A b o x ] ≡ x
        lemma-y-obj1 {b} x = let open ≈-Reasoning A  in ≡←≈ A idL
        lemma-y-obj2 :  (a₁ b c : Obj A) (f : Hom A a₁ b) (g : Hom A b c ) → (x : Hom A a a₁ )→ 
               A [ A [ g o f ] o x ] ≡ (Sets [ _[_o_] A g o _[_o_] A f ]) x
        lemma-y-obj2 a₁ b c f g x = let open ≈-Reasoning A in ≡←≈ A ( begin
               A [ A [ g o f ] o x ]
             ≈↑⟨ assoc ⟩
               A [ g o A [ f o x ] ]
             ≈⟨⟩
               ( λ x →  A [ g o x  ]  ) ( ( λ x → A [ f o x ] ) x )
             ∎ )
        lemma-y-obj3 :  {b c : Obj A} {f g : Hom A b c } → (x : Hom A a b ) → A [ f ≈ g ] →   A [ f o x ] ≡ A [ g o x ]
        lemma-y-obj3 {_} {_} {f} {g} x eq =  let open ≈-Reasoning A in ≡←≈ A ( begin
                A [ f o x ]
             ≈⟨ resp refl-hom eq ⟩
                A [ g o x ]
             ∎ )

-- -- Representable  U  ≈　Hom(A,-)

record Representable  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) ( U : Functor A (Sets {c₂}) ) (a : Obj A) : Set  (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁ ))  where
   field
         -- FObj U x  :  A  → Set
         -- FMap U f  =  Set → Set (locally small)
         -- λ b → Hom (a,b) :  A → Set
         -- λ f → Hom (a,-) = λ b → Hom  a b    

         repr→ : NTrans A (Sets {c₂}) U (Yoneda A a )
         repr← : NTrans A (Sets {c₂}) (Yoneda A a)  U
         reprId→  :  {x : Obj A} →  Sets [ Sets [ TMap repr→ x  o  TMap repr← x ] ≈ id1 (Sets {c₂}) (FObj (Yoneda A a) x )]
         reprId←  :  {x : Obj A} →  Sets [ Sets [ TMap repr← x  o  TMap repr→ x ] ≈ id1 (Sets {c₂}) (FObj U x)]

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
      (Γ : Functor I A) (limita : Limit I A Γ) →
        IsLimit I Sets (Yoneda A  b ○ Γ) (FObj (Yoneda A  b) (a0 limita)) (LimitNat I A Sets Γ (a0 limita) (t0 limita) (Yoneda A b))
YonedaFpreserveLimit0 {c₁} {c₂} {ℓ} A I b Γ lim = record {
         limit = λ a t → ψ a t
       ; t0f=t = λ {a t i} → t0f=t0 a t i
       ; limit-uniqueness = λ {b} {t} {f} t0f=t → limit-uniqueness0 {b} {t} {f} t0f=t 
    } where 
      hat0 :  NTrans I Sets (K I Sets (FObj (Yoneda A b) (a0 lim))) (Yoneda A b ○ Γ)
      hat0 = LimitNat I A Sets Γ (a0 lim) (t0 lim) (Yoneda A b)
      haa0 : Obj Sets
      haa0 = FObj (Yoneda A b) (a0 lim)
      ta : (a : Obj Sets) ( x : a ) ( t : NTrans I Sets (K I Sets a) (Yoneda A b ○ Γ)) → NTrans I A (K I A b ) Γ
      ta a x t = record { TMap = λ i → (TMap t i ) x ; isNTrans = record { commute = commute1 } } where
         commute1 :  {a₁ b₁ : Obj I} {f : Hom I a₁ b₁} →
                A [ A [ FMap Γ f o TMap t a₁ x ] ≈ A [ TMap t b₁ x o FMap (K I A b) f ]  ]
         commute1  {a₁} {b₁} {f} = let open ≈-Reasoning A in begin
                 FMap Γ f o TMap t a₁ x
             ≈⟨⟩
                 ( ( FMap (Yoneda A b  ○ Γ ) f )  *  TMap t a₁ ) x
             ≈⟨ ≈←≡ ( cong (λ k → k x ) (IsNTrans.commute (isNTrans t)) ) ⟩
                 ( TMap t b₁ * ( FMap (K I Sets a) f ) ) x
             ≈⟨⟩
                 ( TMap t b₁ * id1 Sets a ) x
             ≈⟨⟩
                 TMap t b₁ x 
             ≈↑⟨ idR ⟩
                 TMap t b₁ x o id1 A b
             ≈⟨⟩
                 TMap t b₁ x o FMap (K I A b) f 
             ∎ 
      ψ  :  (X : Obj Sets)  ( t : NTrans I Sets (K I Sets X) (Yoneda A b ○ Γ))
          →  Hom Sets X (FObj (Yoneda A b) (a0 lim))
      ψ X t x = FMap (Yoneda A b) (limit (isLimit lim) b (ta X x t )) (id1 A b )
      t0f=t0 : (a : Obj Sets ) ( t : NTrans I Sets (K I Sets a) (Yoneda A b ○ Γ)) (i : Obj I)
           → Sets [ Sets [ TMap (LimitNat I A Sets Γ (a0 lim) (t0 lim) (Yoneda A b)) i o ψ a t ] ≈ TMap t i ]
      t0f=t0 a t i = let open ≈-Reasoning A in extensionality A ( λ x →  ≡←≈ A ( begin 
                 ( Sets [ TMap (LimitNat I A Sets Γ (a0 lim) (t0 lim) (Yoneda A b)) i o ψ a t  ] ) x
             ≈⟨⟩
                FMap (Yoneda A b) ( TMap (t0 lim) i) (FMap (Yoneda A b) (limit (isLimit lim) b (ta a x t )) (id1 A b ))
             ≈⟨⟩ -- FMap (Hom A b ) f g  = A [ f o g  ]
                TMap (t0 lim) i o (limit (isLimit lim) b (ta a x t ) o id1 A b )
             ≈⟨  cdr idR ⟩
                TMap (t0 lim) i o limit (isLimit lim) b (ta a x t ) 
             ≈⟨  t0f=t (isLimit lim) ⟩
                TMap (ta a x t) i
             ≈⟨⟩
                 TMap t i x
             ∎  ))
      limit-uniqueness0 :  {a : Obj Sets} {t : NTrans I Sets (K I Sets a) (Yoneda A b ○ Γ)} {f : Hom Sets a (FObj (Yoneda A b) (a0 lim))} →
        ({i : Obj I} → Sets [ Sets [ TMap (LimitNat I A Sets Γ (a0 lim) (t0 lim) (Yoneda A b)) i o f ] ≈ TMap t i ]) →
        Sets [ ψ a t ≈ f ]
      limit-uniqueness0 {a} {t} {f} t0f=t = let open ≈-Reasoning A in extensionality A ( λ x →  ≡←≈ A ( begin 
                  ψ a t x
             ≈⟨⟩
                 FMap (Yoneda A b) (limit (isLimit lim) b (ta a x t )) (id1 A b )
             ≈⟨⟩
                 limit (isLimit lim) b (ta a x t ) o id1 A b 
             ≈⟨ idR ⟩
                 limit (isLimit lim) b (ta a x t ) 
             ≈⟨ limit-uniqueness (isLimit lim) ( λ {i} → ≈←≡ ( cong ( λ g → g x )( t0f=t {i} ))) ⟩
                  f x
             ∎  ))


YonedaFpreserveLimit : {c₁ c₂ ℓ : Level} (I : Category c₁ c₂ ℓ) (A : Category c₁ c₂ ℓ)
       (b : Obj A ) → LimitPreserve I A Sets (Yoneda A b) 
YonedaFpreserveLimit I A b = record {
       preserve = λ Γ lim → YonedaFpreserveLimit0 A I b Γ lim
   } 


-- K{*}↓U has preinitial full subcategory if U is representable
--     if U is representable,  K{*}↓U has initial Object ( so it has preinitial full subcategory )

open CommaHom

data * {c : Level} : Set c where
  OneObj : *

KUhasInitialObj : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ)
      (a : Obj A )
      → HasInitialObject  ( K A Sets * ↓ (Yoneda A a) ) ( record  { obj = a ; hom = λ x → id1 A a } )
KUhasInitialObj {c₁} {c₂} {ℓ} A a = record {
           initial =  λ b → initial0 b
         ; uniqueness =  λ f → unique f
     } where
         commaCat : Category  (c₂ ⊔ c₁) c₂ ℓ
         commaCat = K A Sets * ↓ Yoneda A a
         initObj  : Obj (K A Sets * ↓ Yoneda A a)
         initObj = record { obj = a ; hom = λ x → id1 A a }
         comm2 : (b : Obj commaCat) ( x : * ) → ( Sets [ FMap (Yoneda A a) (hom b OneObj) o (λ x₁ → id1 A a) ] )  x ≡ hom b x
         comm2 b OneObj = let open ≈-Reasoning A in  ≡←≈ A ( begin
                ( Sets [ FMap (Yoneda A a) (hom b OneObj) o (λ x₁ → id1 A a) ] ) OneObj
             ≈⟨⟩
                FMap (Yoneda A a) (hom b OneObj) (id1 A a)
             ≈⟨⟩
                hom b OneObj o id1 A a
             ≈⟨ idR ⟩
                hom b OneObj 
             ∎  )
         comm1 : (b : Obj commaCat) → Sets [ Sets [ FMap (Yoneda A a) (hom b OneObj) o hom initObj ] ≈ Sets [ hom b o FMap (K A Sets *) (hom b OneObj) ] ]
         comm1 b = let open ≈-Reasoning Sets in begin
                FMap (Yoneda A a) (hom b OneObj) o ( λ x → id1 A a )
             ≈⟨ extensionality A ( λ x → comm2 b x ) ⟩
                hom b 
             ≈⟨⟩
                hom b o FMap (K A Sets *) (hom b OneObj) 
             ∎ 
         initial0 : (b : Obj commaCat) →
            Hom commaCat initObj b
         initial0 b = record {
                arrow = hom b OneObj
              ; comm = comm1 b }
         -- what is comm f ?
         comm-f :  (b : Obj (K A Sets * ↓ (Yoneda A a))) (f : Hom (K A Sets * ↓ Yoneda A a) initObj b)
            → Sets [ Sets [ FMap  (Yoneda A a) (arrow f) o ( λ x → id1 A a ) ]
               ≈ Sets [ hom b  o  FMap  (K A Sets *) (arrow f) ]  ] 
         comm-f b f = comm f
         unique : {b : Obj (K A Sets * ↓ Yoneda A a)}  (f : Hom (K A Sets * ↓ Yoneda A a) initObj b)
                → (K A Sets * ↓ Yoneda A a) [ f ≈ initial0 b ]
         unique {b} f = let open ≈-Reasoning A in begin
                arrow f
             ≈↑⟨ idR ⟩
                arrow f o id1 A a
             ≈⟨⟩
                ( Sets [ FMap  (Yoneda A a) (arrow f) o id1 Sets (FObj (Yoneda A a) a)  ] ) (id1 A a)
             ≈⟨⟩
               ( Sets [ FMap  (Yoneda A a) (arrow f) o ( λ x → id1 A a ) ] ) OneObj
             ≈⟨ ≈←≡ ( cong (λ k → k OneObj ) (comm f )) ⟩
               ( Sets [ hom b  o  FMap  (K A Sets *) (arrow f) ]  ) OneObj
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
     (U : Functor A (Sets {c₂}) )
     ( i : Obj ( K A Sets * ↓ U) )
     (In : HasInitialObject ( K A Sets * ↓ U) i ) 
       → Representable A  U (obj i)
UisRepresentable A U i In = record {
        repr→ = record { TMap = tmap1 ; isNTrans = record { commute = comm1 } }
        ; repr← = record { TMap = tmap2 ; isNTrans = record { commute = comm2 } }
        ; reprId→  = iso→ 
        ; reprId←  = iso←
   } where
      comm11 : (a b : Obj A) (f : Hom A a b) (y : FObj U a ) →
         ( Sets [ FMap (Yoneda A (obj i)) f o ( λ x → arrow (initial In (ob A U a x))) ] ) y   
           ≡ (Sets [ ( λ x → arrow (initial In (ob A U b x))) o FMap U f ] ) y
      comm11 a b f y = begin
               ( Sets [ FMap (Yoneda A (obj i)) f o ( λ x → arrow (initial In (ob A U a x))) ] ) y   
             ≡⟨⟩
                 A [ f o arrow (initial In (ob A U a y)) ]
             ≡⟨⟩
                 A [ arrow ( fArrow A U f y ) o arrow (initial In (ob A U a y)) ]
             ≡⟨  ≡←≈ A ( uniqueness In {ob A U b (FMap U f y) } (( K A Sets * ↓ U) [ fArrow A U f y  o initial In (ob A U a y)] ) ) ⟩
                arrow (initial In (ob A U b (FMap U f y) ))
             ≡⟨⟩
                (Sets [ ( λ x → arrow (initial In (ob A U b x))) o FMap U f ] ) y
             ∎  where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning
      tmap1 :  (b : Obj A) → Hom Sets (FObj U b) (FObj (Yoneda A (obj i)) b)
      tmap1 b x = arrow ( initial In (ob A U b x ) ) 
      comm1 : {a b : Obj A} {f : Hom A a b} → Sets [ Sets [ FMap (Yoneda A (obj i)) f o tmap1 a ] ≈ Sets [ tmap1 b o FMap U f ] ]
      comm1 {a} {b} {f} = let open ≈-Reasoning Sets in begin
                FMap (Yoneda A (obj i)) f o tmap1 a 
             ≈⟨⟩
                FMap (Yoneda A (obj i)) f o ( λ x → arrow (initial In ( ob A U a x )))  
             ≈⟨ extensionality Sets ( λ y → comm11 a b f y ) ⟩
                ( λ x → arrow (initial In (ob A U b x))) o FMap U f 
             ≈⟨⟩
                tmap1 b o FMap U f 
             ∎ 
      comm21 : (a b : Obj A) (f : Hom A a b) ( y : Hom A (obj i) a ) → 
          (Sets [ FMap U f o (λ x → FMap U x (hom i OneObj))] ) y ≡
                (Sets [ ( λ x → (FMap U x ) (hom i OneObj)) o (λ x → A [ f o x ] ) ] )  y
      comm21 a b f y = begin
                FMap U f ( FMap U y (hom i OneObj))
             ≡⟨ ≡-cong ( λ k → k (hom i OneObj)) ( sym ( IsFunctor.distr (isFunctor U ) ) ) ⟩
                (FMap U (A [ f o y ] ) ) (hom i OneObj) 
             ∎  where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning
      tmap2 :  (b : Obj A) → Hom Sets (FObj (Yoneda A (obj i)) b) (FObj U b)
      tmap2 b x =  ( FMap U x ) ( hom i OneObj )
      comm2 : {a b : Obj A} {f : Hom A a b} → Sets [ Sets [ FMap U f o tmap2 a ] ≈
        Sets [ tmap2 b o FMap (Yoneda A (obj i)) f ] ]
      comm2 {a} {b} {f} = let open ≈-Reasoning Sets in begin
                FMap U f o tmap2 a 
             ≈⟨⟩
                FMap U f o ( λ x → ( FMap U x ) ( hom i OneObj ) )
             ≈⟨ extensionality Sets ( λ y → comm21 a b f y ) ⟩
                ( λ x → ( FMap U x ) ( hom i OneObj ) ) o ( λ x → A [ f o x  ]  )
             ≈⟨⟩
                ( λ x → ( FMap U x ) ( hom i OneObj ) ) o FMap (Yoneda A (obj i)) f 
             ≈⟨⟩
                tmap2 b o FMap (Yoneda A (obj i)) f 
             ∎
      iso0 : ( x : Obj A) ( y : Hom A (obj i ) x ) ( z : * )
         → ( Sets [ FMap U y o hom i ] ) z ≡ ( Sets [ ub A U x (FMap U y (hom i OneObj)) o FMap (K A Sets *) y ] ) z 
      iso0 x y  OneObj = refl
      iso→  : {x : Obj A} → Sets [ Sets [ tmap1 x o tmap2 x ] ≈ id1 Sets (FObj (Yoneda A (obj i)) x) ]
      iso→ {x} = let open ≈-Reasoning A in extensionality Sets ( λ ( y : Hom A (obj i ) x ) → ≡←≈ A ( begin
               ( Sets [ tmap1 x o tmap2 x ] ) y
             ≈⟨⟩
                arrow ( initial In (ob A U x (( FMap U y ) ( hom i OneObj ) ))) 
             ≈↑⟨  uniqueness In (record { arrow = y ; comm = extensionality Sets ( λ (z : * ) → iso0 x y z ) }  ) ⟩
               y
             ∎  ))
      iso←  : {x : Obj A} → Sets [ Sets [ tmap2 x o tmap1 x ] ≈ id1 Sets (FObj U x) ]
      iso← {x} = extensionality Sets ( λ (y : FObj U x ) → ( begin 
               ( Sets [ tmap2 x o tmap1 x ] ) y
             ≡⟨⟩
               ( FMap U ( arrow ( initial In (ob A U x y ) ))  ) ( hom i OneObj )
             ≡⟨ ≡-cong (λ k → k OneObj) ( comm ( initial In (ob A U x y ) )) ⟩
                 hom (ob A U x y) OneObj
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
      ≈↑⟨ ≈←≡ ( cong (λ k → arrow (solution k)) ( ≡←≈ B ugη=f )) ⟩
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

-- end

