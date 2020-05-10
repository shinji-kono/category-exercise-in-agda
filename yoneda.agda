---
--
--  A → Sets^A^op  : Yoneda Functor
--     Contravariant Functor h_a
--     Nat(h_a,F)
--                        Shinji KONO <kono@ie.u-ryukyu.ac.jp>
----

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
open import Category.Sets
module yoneda where 
-- { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } where

open import HomReasoning
open import cat-utility
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym )



-- Contravariant Functor : op A → Sets  ( Obj of Sets^{A^op} )
--   Obj and Hom of Sets^A^op

open Functor

YObj : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Set (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁))
YObj {_} {c₂} A = Functor (Category.op A) (Sets {c₂})
YHom : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  (f : YObj A ) → (g : YObj A ) →  Set  (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁))
YHom {_} {c₂} A f g = NTrans (Category.op A) (Sets {c₂}) f g

open NTrans 
Yid : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) {a : YObj A } → YHom A a a
Yid {_} {c₂} A {a} = record { TMap = λ a → λ x → x ; isNTrans = isNTrans1 {a} } where
   isNTrans1 : {a : YObj A } → IsNTrans (Category.op A) (Sets {c₂}) a a (λ a → λ x → x )
   isNTrans1 {a} = record { commute = refl  }

_+_ : { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } {a b c : YObj A} → YHom A b c → YHom A a b → YHom A a c
_+_ {_} {c₂} {_} {A} {a} {b} {c} f g  = record { TMap = λ x → Sets [ TMap f x o TMap g x ] ; isNTrans = isNTrans1  } where
   commute1 :  (a b c : YObj A ) (f : YHom A b c)  (g : YHom A a b ) 
            (a₁ b₁ : Obj (Category.op A)) (h : Hom (Category.op A) a₁ b₁) →
                        Sets [ Sets [ FMap c h o Sets [ TMap f a₁ o TMap g a₁ ] ] ≈
                        Sets [ Sets [ TMap f b₁ o TMap g b₁ ] o FMap a h ] ]
   commute1  a b c f g a₁ b₁ h =   let open ≈-Reasoning (Sets {c₂})in begin
                Sets [ FMap c h o Sets [ TMap f a₁ o TMap g a₁ ] ]
             ≈⟨ assoc {_} {_} {_} {_} {FMap c h } {TMap f a₁} {TMap g a₁} ⟩
                Sets [ Sets [ FMap c h o TMap f a₁ ] o TMap g a₁ ] 
             ≈⟨ car (nat f) ⟩
                Sets [ Sets [ TMap f b₁ o FMap b h ] o TMap g a₁ ] 
             ≈↑⟨ assoc {_} {_} {_} {_} { TMap f b₁} {FMap b h } {TMap g a₁}⟩
                Sets [ TMap f b₁ o Sets [ FMap b h  o TMap g a₁ ]  ]
             ≈⟨ cdr {_} {_} {_} {_} {_} { TMap f b₁} (nat g) ⟩
                Sets [ TMap f b₁ o Sets [ TMap g b₁  o FMap a h ]  ]
             ≈↑⟨ assoc  {_} {_} {_} {_} {TMap f b₁} {TMap g b₁} { FMap a h}  ⟩
                Sets [ Sets [ TMap f b₁ o TMap g b₁ ] o FMap a h ] 
             ∎ 
   isNTrans1 : IsNTrans (Category.op A) (Sets {c₂}) a c (λ x → Sets [ TMap f x o TMap g x ]) 
   isNTrans1 = record { commute = λ {a₁ b₁ h} → commute1 a b c f g a₁ b₁ h }

_==_  :  { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } {a b : YObj A} → YHom A a b → YHom A a b → Set (c₂ ⊔ c₁)
_==_  {_} { c₂} {_} {A} f g = ∀{x : Obj (Category.op A)} → (Sets {c₂}) [ TMap f x ≈ TMap g x ]

infix  4 _==_

isSetsAop :   { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → IsCategory (YObj A) (YHom A) _==_ _+_ ( Yid A )
isSetsAop {_} {c₂} {_} A =  
  record  { isEquivalence =  record {refl = refl ; trans = λ {i j k} → trans1 {_} {_} {i} {j} {k} ; sym = λ {i j} → sym1  {_} {_} {i} {j}}
        ; identityL = refl
        ; identityR = refl
        ; o-resp-≈ =  λ{a b c f g h i } → o-resp-≈      {a} {b} {c} {f} {g} {h} {i}
        ; associative = refl
        } where 
            open ≈-Reasoning (Sets {c₂}) 
            sym1 : {a b : YObj A } {i j : YHom A a b } → i == j → j == i
            sym1 {a} {b} {i} {j} eq {x} = sym eq 
            trans1 : {a b : YObj A } {i j k : YHom A a b} → i == j → j == k → i == k
            trans1 {a} {b} {i} {j} {k} i=j j=k {x} =  trans-hom i=j j=k
            o-resp-≈ : {A₁ B C : YObj A} {f g : YHom A A₁ B} {h i : YHom A B C} → 
                f == g → h == i → h + f == i + g
            o-resp-≈ {a} {b} {c} {f} {g} {h} {i} f=g h=i {x} = resp  f=g h=i

SetsAop :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  → Category (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁))  (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁)) (c₂ ⊔ c₁)
SetsAop {_} {c₂} {_} A  =
  record { Obj = YObj A
         ; Hom = YHom A
         ; _o_ = _+_
         ; _≈_ = _==_
         ; Id  = Yid A
         ; isCategory = isSetsAop A
         }

-- A is Locally small
postulate ≈-≡ :  { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ }  {a b : Obj A } { x y : Hom A a b } →  (x≈y : A [ x ≈ y  ]) → x ≡ y

import Relation.Binary.PropositionalEquality
-- Extensionality a b = {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g → ( λ x → f x ≡ λ x → g x )
postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Relation.Binary.PropositionalEquality.Extensionality c₂ c₂


----
--
--  Object mapping in Yoneda Functor
--
----

open import Function

y-obj :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  (a : Obj A) → Functor (Category.op A) (Sets {c₂})
y-obj {_} {c₂} {_} A a = record {
        FObj = λ b → Hom (Category.op A) a b  ;
        FMap =   λ {b c : Obj A } → λ ( f : Hom  A c b ) → λ (g : Hom  A b a ) →  (Category.op A) [ f o g ] ;
        isFunctor = record {
             identity =  λ {b} → extensionality A ( λ x → lemma-y-obj1 {b} x ) ;
             distr = λ {a} {b} {c} {f} {g} → extensionality A ( λ x → lemma-y-obj2 a b c f g x ) ;
             ≈-cong = λ eq → extensionality A ( λ x →  lemma-y-obj3 x eq ) 
        } 
    }  where
        lemma-y-obj1 : {b : Obj A } → (x : Hom A b a) →  (Category.op A) [ id1 A b o x ] ≡ x
        lemma-y-obj1 {b} x = let open ≈-Reasoning (Category.op A) in ≈-≡ {_} {_} {_} {A} idL
        lemma-y-obj2 :  (a₁ b c : Obj A) (f : Hom A b a₁) (g : Hom A c b ) → (x : Hom A a₁ a )→ 
               Category.op A [ Category.op A [ g o f ] o x ] ≡ (Sets [ _[_o_] (Category.op A) g o _[_o_] (Category.op A) f ]) x
        lemma-y-obj2 a₁ b c f g x = let open ≈-Reasoning (Category.op A) in ≈-≡ {_} {_} {_} {A} ( begin
               Category.op A [ Category.op A [ g o f ] o x ]
             ≈↑⟨ assoc ⟩
               Category.op A [ g o Category.op A [ f o x ] ]
             ≈⟨⟩
               ( λ x →  Category.op A [ g o x  ]  ) ( ( λ x → Category.op A [ f o x ] ) x )
             ∎ )
        lemma-y-obj3 :  {b c : Obj A} {f g : Hom A c b } → (x : Hom A b a ) → A [ f ≈ g ] →  Category.op A [ f o x ] ≡ Category.op A [ g o x ]
        lemma-y-obj3 {_} {_} {f} {g} x eq =  let open ≈-Reasoning (Category.op A) in ≈-≡ {_} {_} {_} {A}   ( begin
                Category.op A [ f o x ]
             ≈⟨ resp refl-hom eq ⟩
                Category.op A [ g o x ]
             ∎ )


----
--
--  Hom mapping in Yoneda Functor
--
----

y-tmap :   { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  ( a b : Obj A ) → (f : Hom A a b ) → (x : Obj (Category.op A)) → 
     FObj (y-obj A a) x → FObj (y-obj A b ) x 
y-tmap {_} {c₂} {_} A  a b f x = λ ( g : Hom A x a ) → A [ f o g ]  --  ( h : Hom A x b ) 

y-map :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a b : Obj A } → (f : Hom A a b ) → YHom A (y-obj A a) (y-obj A b) 
y-map  {_} {c₂} {_} A  {a} {b} f = record { TMap =  y-tmap A a b f ; isNTrans = isNTrans1 {a} {b} f } where
   lemma-y-obj4 : {a₁ b₁ : Obj (Category.op A)} {g : Hom (Category.op A) a₁ b₁} → {a b : Obj A } → (f : Hom A a b ) →
        Sets [ Sets [ FMap (y-obj A b) g o y-tmap A a b f a₁ ] ≈
        Sets [ y-tmap A a b f b₁ o FMap (y-obj A a) g ] ]
   lemma-y-obj4 {a₁} {b₁} {g} {a} {b} f = let open ≈-Reasoning A in extensionality A ( λ x →  ≈-≡ {_} {_} {_} {A} ( begin
                A [ A [ f o x ] o g ]
             ≈↑⟨ assoc ⟩
                A [ f o A [ x  o g ] ]
             ∎ ) )
   isNTrans1 : {a b : Obj A } →  (f : Hom A a b ) → IsNTrans (Category.op A) (Sets {c₂}) (y-obj A a) (y-obj A b) (y-tmap A a b f )
   isNTrans1 {a} {b} f = record { commute = λ{a₁ b₁ g } → lemma-y-obj4 {a₁} {b₁} {g} {a} {b} f } 

-----
--
-- Yoneda Functor itself
--
-----

YonedaFunctor :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  → Functor A (SetsAop A)
YonedaFunctor A = record {
         FObj = λ a → y-obj A a
       ; FMap = λ f → y-map A f
       ; isFunctor = record {
             identity =  identity
             ; distr = distr1
             ; ≈-cong = ≈-cong

        } 
  } where
        ≈-cong : {a b : Obj A} {f g : Hom A a b} → A [ f ≈ g ] → SetsAop A [ y-map A f ≈ y-map A g ]
        ≈-cong {a} {b} {f} {g} eq  =  let open ≈-Reasoning (A) in  -- (λ x g₁ → A [ f o g₁ ] ) ≡ (λ x g₁ → A [  g o  g₁ ] )
             extensionality A ( λ h → ≈-≡ {_} {_} {_} {A}  ( begin
                A [ f o h ]
             ≈⟨ resp refl-hom eq ⟩
                A [ g o h ]
             ∎
          ) ) 
        identity : {a : Obj A} → SetsAop A [ y-map A (id1 A a) ≈ id1 (SetsAop A) (y-obj A a )  ]
        identity  {a} =  let open ≈-Reasoning (A) in -- (λ x g → A [ id1 A a o g ] ) ≡ (λ a₁ x → x)
             extensionality A ( λ g →  ≈-≡ {_} {_} {_} {A}  ( begin
                A [ id1 A a o g ] 
             ≈⟨ idL ⟩
                g
             ∎
          ) )  
        distr1 : {a b c : Obj A} {f : Hom A a b} {g : Hom A b c} → SetsAop A [ y-map A (A [ g o f ]) ≈ SetsAop A [ y-map A g o y-map A f ] ]
        distr1 {a} {b} {c} {f} {g} = let open ≈-Reasoning (A) in -- (λ x g₁ → (A [  (A [ g o f]  o g₁ ]))) ≡ (λ x x₁ → A [  g o A [ f o x₁ ] ] )
           extensionality A ( λ h →  ≈-≡ {_} {_} {_} {A}  ( begin
                A [ A [ g o f ]  o h ]
             ≈↑⟨ assoc  ⟩
                A [  g o A [ f o h ] ]
             ∎
          ) )  


------
--
--  F : A → Sets  ∈ Obj SetsAop
--
--  F(a) → Nat(h_a,F)
--      x ∈ F(a) , (g : Hom A b a)  → ( FMap F g ) x
------

F2Natmap :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a : Obj A} → {F : Obj ( SetsAop A) } 
     → {x : FObj F a} → (b : Obj (Category.op A)) → Hom Sets (FObj (y-obj A a) b) (FObj F b)
F2Natmap  A {a} {F} {x} b = λ ( g : Hom A b a ) → ( FMap F g ) x

F2Nat :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a : Obj A} → {F : Obj (SetsAop A )} →  FObj F a  → Hom (SetsAop A) (y-obj A a) F
F2Nat {_} {c₂}  A {a} {F} x = record { TMap = F2Natmap A {a} {F} {x} ; isNTrans = isNTrans1 } where
   commute1 : {a₁ b : Obj (Category.op A)} {f : Hom (Category.op A) a₁ b} (g : Hom A  a₁ a) →
                (Sets [ FMap F f o  FMap F g ]) x ≡ FMap F (A [ g o  f ] ) x
   commute1 g =  let open ≈-Reasoning (Sets) in
            cong ( λ f → f x ) ( sym ( distr F )  )
   commute : {a₁ b : Obj (Category.op A)} {f : Hom (Category.op A) a₁ b} → 
        Sets [ Sets [ FMap F f o F2Natmap A {a} {F} {x} a₁ ] ≈ Sets [ F2Natmap A {a} {F} {x} b o FMap (y-obj A a) f ] ]
   commute {a₁} {b} {f} =  let open ≈-Reasoning (Sets) in
             begin
                Sets [ FMap F f o F2Natmap A {a} {F} {x} a₁ ]
             ≈⟨⟩
                Sets [ FMap F f o (λ ( g : Hom A a₁ a ) → ( FMap F g ) x) ]
             ≈⟨ extensionality A  ( λ (g : Hom A  a₁ a) → commute1 {a₁} {b} {f} g ) ⟩
                Sets [  (λ ( g : Hom A b a ) → ( FMap F g ) x) o FMap (y-obj A a) f ] 
             ≈⟨⟩
                Sets [ F2Natmap A {a} {F} {x} b o FMap (y-obj A a) f ] 
             ∎
   isNTrans1 : IsNTrans (Category.op A) (Sets {c₂}) (y-obj A a) F (F2Natmap A {a} {F})
   isNTrans1 = record { commute = λ {a₁ b f}  →  commute {a₁} {b} {f} } 


--  F(a) <- Nat(h_a,F)
Nat2F :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) {a : Obj A} → {F : Obj (SetsAop A) } →  Hom (SetsAop A) (y-obj A a) F  → FObj F a 
Nat2F A {a} {F} ha =  ( TMap ha a ) (id1 A a)

----
--
-- Prove  Bijection (as routine exercise ...)
--
----

F2Nat→Nat2F :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a : Obj A } → {F : Obj (SetsAop A)} → (fa : FObj F a) 
    →  Nat2F A {a} {F} (F2Nat A {a} {F} fa) ≡ fa 
F2Nat→Nat2F A {a} {F} fa = let open ≈-Reasoning (Sets) in cong ( λ f → f fa ) (
             -- FMap F (Category.Category.Id A) fa ≡ fa
             begin
               ( FMap F (id1 A _ )) 
             ≈⟨ IsFunctor.identity (isFunctor F)    ⟩
                id1 Sets (FObj F a)
             ∎ )

open  import  Relation.Binary.PropositionalEquality

≡-cong = Relation.Binary.PropositionalEquality.cong 

--     F :  op A → Sets
--     ha : NTrans (op A) Sets (y-obj {a}) F
--                FMap F  g  o TMap ha a ≈   TMap ha b  o FMap (y-obj {a}) g

Nat2F→F2Nat :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a : Obj A } → {F : Obj (SetsAop A)} → (ha : Hom (SetsAop A) (y-obj A a) F) 
     →  SetsAop A [ F2Nat A {a} {F} (Nat2F A {a} {F} ha) ≈ ha ]
Nat2F→F2Nat A {a} {F} ha {b} = let open ≡-Reasoning in
             begin
                TMap (F2Nat A {a} {F} (Nat2F A {a} {F} ha)) b
             ≡⟨⟩
                (λ g → FMap F g (TMap ha a (Category.Category.Id A)))
             ≡⟨  extensionality A  (λ g → (
                begin
                    FMap F g (TMap ha a (Category.Category.Id A)) 
                ≡⟨  ≡-cong (λ f → f (Category.Category.Id A)) (IsNTrans.commute (isNTrans ha)) ⟩
                    TMap ha b (FMap (y-obj A a) g (Category.Category.Id A))
                ≡⟨⟩
                    TMap ha b ( (A Category.o Category.Category.Id A) g )
                ≡⟨  ≡-cong ( TMap ha b ) ( ≈-≡ {_} {_} {_} {A} (IsCategory.identityL  ( Category.isCategory A ))) ⟩
                    TMap ha b g
                ∎ 
             )) ⟩
                TMap ha b
             ∎ 

-- Yoneda's Lemma
--    Yoneda Functor is full and faithfull
--    that is FMapp Yoneda is injective and surjective

--  λ b g → (A Category.o f₁) g
YondaLemma1 :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a a' : Obj A } {f : FObj (FObj (YonedaFunctor A) a) a' } 
     → SetsAop A [ F2Nat A {a'} {FObj (YonedaFunctor A) a} f ≈ FMap (YonedaFunctor A) f ]
YondaLemma1 A {a} {a'} {f} = refl

--  F2Nat is bijection so FMap YonedaFunctor also ( using functional extensionality )

--  Full embedding of Yoneda Functor requires injective on Object, 
--
-- But we cannot prove like this
--     FObj YonedaFunctor a   ≡ FObj YonedaFunctor b → a  ≡ b

open import Relation.Nullary
open import Data.Empty

--YondaLemma2 :  {c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )   →
--     (a b x : Obj A )  → (FObj (FObj (YonedaFunctor A) a) x)  ≡ (FObj (FObj (YonedaFunctor A) b ) x)  → a ≡ b 
--YondaLemma2 A a bx eq = {!!}

--       N.B     = ≡-cong gives you ! a ≡ b, so we cannot cong inv to prove a ≡ b

--record Category c₁ c₂ ℓ : Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
--  infixr 9 _o_
--  infix  4 _≈_
--  field
--    Obj : Set c₁
--    Hom : Obj → Obj → Set c₂
--YondaLemma31 :  {c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )   →
--     (a b x : Obj A )  → Hom A a x  ≡ Hom A b x  → a ≡ b 
--YondaLemma31 A a b x eq = {!!}
--
-- Instead we prove only
--     inv ( FObj YonedaFunctor a )  ≡ a

inv :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a x : Obj A} ( f : FObj (FObj (YonedaFunctor A) a) x)  →  Obj A
inv A {a} f =  Category.cod A f

YonedaLemma21 :   { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a x : Obj A} ( f : ( FObj (FObj (YonedaFunctor A ) a) x) ) →  inv A f  ≡ a
YonedaLemma21 A {a} {x} f = refl

open import  Relation.Binary.HeterogeneousEquality
a1 : { c₁ : Level} {A B : Set c₁ } {a : A } { b : B } → a ≅ b → A ≡ B 
a1 refl = refl

-- YondaLemma3 :  {c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )   →
--     (a b x : Obj A )  → Hom A a x  ≅ Hom A b x  → a ≡ b 
-- YondaLemma3 A a b x eq = {!!} -- ≡-cong (inv A) ?

a2 :  ( a b : Set ) (f : a → a ) (g : b → a ) -> f ≅ g → a ≡ b
a2 a b f g eq = {!!}

-- YonedaInjective :   { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a b : Obj A}
--          → FObj (FObj (YonedaFunctor A ) a ) a  ≅ FObj (FObj (YonedaFunctor A ) a ) b
--          → a ≡ b
-- YonedaInjective A {a} {b} eq = {!!}


