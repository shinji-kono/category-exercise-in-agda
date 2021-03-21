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
open import cat-utility
module yoneda { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) (I : Set c₁) ( small : Small A I ) where

open import HomReasoning
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym )



-- Contravariant Functor : op A → Sets  ( Obj of Sets^{A^op} )
--   Obj and Hom of Sets^A^op

open Functor
open NTrans 

SetsAop :  Category (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁))  (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁)) (c₂ ⊔ c₁)
SetsAop  = record { Obj = YObj
         ; Hom = YHom
         ; _o_ = _+_
         ; _≈_ = _==_
         ; Id  = Yid
         ; isCategory = record  {
              isEquivalence =  record {refl = refl ; trans = λ {i} {j} {k} → trans1 {_} {_} {i} {j} {k} ; sym = λ {i j} → sym1  {_} {_} {i} {j}}
            ; identityL = refl
            ; identityR = refl
            ; o-resp-≈ =  λ{a b c f g h i } → o-resp-≈      {a} {b} {c} {f} {g} {h} {i}
            ; associative = refl
        } } where 
            open ≈-Reasoning (Sets {c₂}) 
            YObj : Set (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁))
            YObj  = Functor (Category.op A) (Sets {c₂})
            YHom : ( f : YObj  ) → (g : YObj  ) →  Set  (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁))
            YHom  f g = NTrans (Category.op A) (Sets {c₂}) f g

            Yid : {a : YObj } → YHom a a
            Yid {a} = record { TMap = λ a → λ x → x ; isNTrans = isNTrans1 {a} } where
               isNTrans1 : {a : YObj } → IsNTrans (Category.op A) (Sets {c₂}) a a (λ a → λ x → x )
               isNTrans1 {a} = record { commute = refl  }

            _+_ : {a b c : YObj} → YHom b c → YHom a b → YHom a c
            _+_ {a} {b} {c} f g  =
                   record { TMap = λ x → Sets [ TMap f x o TMap g x ] ;
                   isNTrans = record { commute = λ {a₁ b₁ h} → commute1 a b c f g a₁ b₁ h }  } where
               commute1 :  (a b c : YObj ) (f : YHom b c)  (g : YHom a b ) 
                        (a₁ b₁ : Obj (Category.op A)) (h : Hom (Category.op A) a₁ b₁) →
                                    Sets [ Sets [ FMap c h o Sets [ TMap f a₁ o TMap g a₁ ] ] ≈
                                    Sets [ Sets [ TMap f b₁ o TMap g b₁ ] o FMap a h ] ]
               commute1  a b c f g a₁ b₁ h =   begin
                    Sets [ FMap c h o Sets [ TMap f a₁ o TMap g a₁ ] ] ≈⟨ assoc {_} {_} {_} {_} {FMap c h } {TMap f a₁} {TMap g a₁} ⟩
                    Sets [ Sets [ FMap c h o TMap f a₁ ] o TMap g a₁ ] ≈⟨ car (nat f) ⟩
                    Sets [ Sets [ TMap f b₁ o FMap b h ] o TMap g a₁ ] ≈↑⟨ assoc {_} {_} {_} {_} { TMap f b₁} {FMap b h } {TMap g a₁}⟩
                    Sets [ TMap f b₁ o Sets [ FMap b h  o TMap g a₁ ]  ] ≈⟨ cdr {_} {_} {_} {_} {_} { TMap f b₁} (nat g) ⟩
                    Sets [ TMap f b₁ o Sets [ TMap g b₁  o FMap a h ]  ] ≈↑⟨ assoc  {_} {_} {_} {_} {TMap f b₁} {TMap g b₁} { FMap a h}  ⟩
                    Sets [ Sets [ TMap f b₁ o TMap g b₁ ] o FMap a h ] ∎ 

            _==_  :  {a b : YObj} → YHom a b → YHom a b → Set (c₂ ⊔ c₁)
            _==_  f g = ∀{x : Obj (Category.op A)} → (Sets {c₂}) [ TMap f x ≈ TMap g x ]

            sym1 : {a b : YObj } {i j : YHom a b } → i == j → j == i
            sym1 {a} {b} {i} {j} eq {x} = sym eq 
            trans1 : {a b : YObj } {i j k : YHom a b} → i == j → j == k → i == k
            trans1 {a} {b} {i} {j} {k} i=j j=k {x} =  trans-hom i=j j=k
            o-resp-≈ : {A₁ B C : YObj} {f g : YHom A₁ B} {h i : YHom B C} → 
                f == g → h == i → (h + f) == (i + g)
            o-resp-≈ {a} {b} {c} {f} {g} {h} {i} f=g h=i {x} = resp  f=g h=i

-- A is Locally small
postulate ≈-≡ :  { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a b : Obj A } { x y : Hom A a b } →  (x≈y : A [ x ≈ y  ]) → x ≡ y

import Axiom.Extensionality.Propositional
-- Extensionality a b = {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g → ( λ x → f x ≡ λ x → g x )
postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Axiom.Extensionality.Propositional.Extensionality c₂ c₂

----
--
--  Object mapping in Yoneda Functor
--
----

open import Function

y-obj :  (a : Obj A) → Functor (Category.op A) (Sets {c₂})
y-obj a = record {
        FObj = λ b → Hom (Category.op A) a b  ;
        FMap =   λ {b c : Obj A } → λ ( f : Hom  A c b ) → λ (g : Hom  A b a ) →  (Category.op A) [ f o g ] ;
        isFunctor = record {
             identity =  λ {b} → extensionality A ( λ x → lemma-y-obj1 {b} x ) ;
             distr = λ {a} {b} {c} {f} {g} → extensionality A ( λ x → lemma-y-obj2 a b c f g x ) ;
             ≈-cong = λ eq → extensionality A ( λ x →  lemma-y-obj3 x eq ) 
        } 
    }  where
        lemma-y-obj1 : {b : Obj A } → (x : Hom A b a) →  (Category.op A) [ id1 A b o x ] ≡ x
        lemma-y-obj1 {b} x = let open ≈-Reasoning (Category.op A) in ≈-≡ A idL
        lemma-y-obj2 :  (a₁ b c : Obj A) (f : Hom A b a₁) (g : Hom A c b ) → (x : Hom A a₁ a )→ 
               Category.op A [ Category.op A [ g o f ] o x ] ≡ (Sets [ _[_o_] (Category.op A) g o _[_o_] (Category.op A) f ]) x
        lemma-y-obj2 a₁ b c f g x = let open ≈-Reasoning (Category.op A) in ≈-≡ A ( begin
               Category.op A [ Category.op A [ g o f ] o x ] ≈↑⟨ assoc ⟩
               Category.op A [ g o Category.op A [ f o x ] ] ≈⟨⟩
               ( λ x →  Category.op A [ g o x  ]  ) ( ( λ x → Category.op A [ f o x ] ) x ) ∎ )
        lemma-y-obj3 :  {b c : Obj A} {f g : Hom A c b } → (x : Hom A b a ) → A [ f ≈ g ] →  Category.op A [ f o x ] ≡ Category.op A [ g o x ]
        lemma-y-obj3 {_} {_} {f} {g} x eq =  let open ≈-Reasoning (Category.op A) in ≈-≡ A  ( begin
                Category.op A [ f o x ] ≈⟨ resp refl-hom eq ⟩
                Category.op A [ g o x ] ∎ )

----
--
--  Hom mapping in Yoneda Functor
--
----

y-tmap :   ( a b : Obj A ) → (f : Hom A a b ) → (x : Obj (Category.op A)) → 
     FObj (y-obj a) x → FObj (y-obj b ) x 
y-tmap a b f x = λ ( g : Hom A x a ) → A [ f o g ]  --  ( h : Hom A x b ) 

y-map :  {a b : Obj A } → (f : Hom A a b ) → NTrans (Category.op A) (Sets {c₂}) (y-obj a) (y-obj b) 
y-map  {a} {b} f = record { TMap =  y-tmap  a b f ; isNTrans = isNTrans1 {a} {b} f } where
   lemma-y-obj4 : {a₁ b₁ : Obj (Category.op A)} {g : Hom (Category.op A) a₁ b₁} → {a b : Obj A } → (f : Hom A a b ) →
        Sets [ Sets [ FMap (y-obj b) g o y-tmap  a b f a₁ ] ≈
        Sets [ y-tmap  a b f b₁ o FMap (y-obj a) g ] ]
   lemma-y-obj4 {a₁} {b₁} {g} {a} {b} f = let open ≈-Reasoning A in extensionality A ( λ x →  ≈-≡ A ( begin
                A [ A [ f o x ] o g ] ≈↑⟨ assoc ⟩
                A [ f o A [ x  o g ] ] ∎ ) )
   isNTrans1 : {a b : Obj A } →  (f : Hom A a b ) → IsNTrans (Category.op A) (Sets {c₂}) (y-obj a) (y-obj b) (y-tmap  a b f )
   isNTrans1 {a} {b} f = record { commute = λ{a₁ b₁ g } → lemma-y-obj4 {a₁} {b₁} {g} {a} {b} f } 

-----
--
-- Yoneda Functor itself
--
-----

YonedaFunctor :  Functor A SetsAop 
YonedaFunctor  = record {
         FObj = λ a → y-obj a
       ; FMap = λ f → y-map f
       ; isFunctor = record {
             identity =  identity
             ; distr = distr1
             ; ≈-cong = ≈-cong
        } } where
        ≈-cong : {a b : Obj A} {f g : Hom A a b} → A [ f ≈ g ] → SetsAop [ y-map  f ≈ y-map  g ]
        ≈-cong {a} {b} {f} {g} eq  =  let open ≈-Reasoning A in  -- (λ x g₁ → A [ f o g₁ ] ) ≡ (λ x g₁ → A [  g o  g₁ ] )
             extensionality A ( λ h → ≈-≡ A  ( begin
                A [ f o h ] ≈⟨ resp refl-hom eq ⟩
                A [ g o h ] ∎ ) ) 
        identity : {a : Obj A} → SetsAop [ y-map (id1 A a) ≈ id1 SetsAop (y-obj a )  ]
        identity  {a} =  let open ≈-Reasoning A in -- (λ x g → A [ id1 A a o g ] ) ≡ (λ a₁ x → x)
             extensionality A ( λ g →  ≈-≡ A  ( begin
                A [ id1 A a o g ] ≈⟨ idL ⟩
                g ∎ ) )  
        distr1 : {a b c : Obj A} {f : Hom A a b} {g : Hom A b c} → SetsAop [ y-map (A [ g o f ]) ≈ SetsAop [ y-map g o y-map f ] ]
        distr1 {a} {b} {c} {f} {g} = let open ≈-Reasoning A in -- (λ x g₁ → (A [  (A [ g o f]  o g₁ ]))) ≡ (λ x x₁ → A [  g o A [ f o x₁ ] ] )
           extensionality A ( λ h →  ≈-≡ A  ( begin
                A [ A [ g o f ]  o h ] ≈↑⟨ assoc  ⟩
                A [  g o A [ f o h ] ] ∎ ) )  

------
--
--  Hom(_ , _) : Obj (op A) → Obj A → Sets
--
--
------

-- module _ where
-- 
--   open import Category.Constructions.Product
--   open import Data.Product renaming (_×_ to _*_)
-- 
--   HomAAop : Functor ((Category.op A) × A)  (Sets {c₂})
--   HomAAop = record {
--         FObj = λ x → Hom A (proj₁ x) (proj₂ x)
-- -- f     : Hom (Category.op A × A) A₁ B
-- -- g     : Category.Category.Hom A (proj₁ A₁) (proj₂ A₁)
--       ; FMap = λ f g →  A [ A [ proj₂ f o g ] o proj₁ f  ] 
--       ; isFunctor = record { ≈-cong = λ {a} {b} {f} {g} f=g → extensionality A ( λ h → cong (λ k → A [ A [ proj₂ k o h ] o (proj₁ k) ]  ) {!!})
--          ; distr = {!!} ; identity = {!!} }
--      } where  open ≈-Reasoning A

------
--
--  Yoneda Lemma
--
--  (F : Obj SetsAop) → ( 
--       Hom SetsAop (FObj YonedaFunctor a , F ) ≅ FObj F a
--
--  F : Functor (co A) Sets  ∈ Obj SetsAop
--
--  F(a) → Nat(h_a,F)
--      x ∈ F(a) , (g : Hom A b a)  → ( FMap F g ) x
------

F2Natmap :  {a : Obj A} → {F : Obj SetsAop  } 
     → {x : FObj F a} → (b : Obj (Category.op A)) → Hom Sets (FObj (y-obj a) b) (FObj F b)
F2Natmap  {a} {F} {x} b = λ ( g : Hom A b a ) → ( FMap F g ) x

F2Nat :   {a : Obj A} → {F : Obj SetsAop } →  FObj F a  → Hom SetsAop (y-obj a) F
F2Nat  {a} {F} x = record { TMap = F2Natmap {a} {F} {x} ; isNTrans = isNTrans1 } where
   commute1 : {a₁ b : Obj (Category.op A)} {f : Hom (Category.op A) a₁ b} (g : Hom A  a₁ a) →
                (Sets [ FMap F f o  FMap F g ]) x ≡ FMap F (A [ g o  f ] ) x
   commute1 g =  let open ≈-Reasoning (Sets) in
            cong ( λ f → f x ) ( sym ( distr F )  )
   commute : {a₁ b : Obj (Category.op A)} {f : Hom (Category.op A) a₁ b} → 
        Sets [ Sets [ FMap F f o F2Natmap {a} {F} {x} a₁ ] ≈ Sets [ F2Natmap  {a} {F} {x} b o FMap (y-obj  a) f ] ]
   commute {a₁} {b} {f} =  let open ≈-Reasoning (Sets) in
             begin
                Sets [ FMap F f o F2Natmap  {a} {F} {x} a₁ ]
             ≈⟨⟩
                Sets [ FMap F f o (λ ( g : Hom A a₁ a ) → ( FMap F g ) x) ]
             ≈⟨ extensionality A  ( λ (g : Hom A  a₁ a) → commute1 {a₁} {b} {f} g ) ⟩
                Sets [  (λ ( g : Hom A b a ) → ( FMap F g ) x) o FMap (y-obj  a) f ] 
             ≈⟨⟩
                Sets [ F2Natmap  {a} {F} {x} b o FMap (y-obj  a) f ] 
             ∎
   isNTrans1 : IsNTrans (Category.op A) (Sets {c₂}) (y-obj  a) F (F2Natmap  {a} {F})
   isNTrans1 = record { commute = λ {a₁ b f}  →  commute {a₁} {b} {f} } 

--
-- Obj Part : SetAop (Y - , F) ≅  F 
--

--  F(a) <- Nat(h_a,F)
Nat2F :    {a : Obj A} → {F : Obj SetsAop  } →  Hom SetsAop  (y-obj  a) F  → FObj F a 
Nat2F  {a} {F} ha =  ( TMap ha a ) (id1 A a)

----
--
-- Prove  Bijection (as routine exercise ...)
--
----

F2Nat→Nat2F :     {a : Obj A } → {F : Obj SetsAop } → (fa : FObj F a) 
    →  Nat2F  {a} {F} (F2Nat  {a} {F} fa) ≡ fa 
F2Nat→Nat2F  {a} {F} fa = let open ≈-Reasoning (Sets) in cong ( λ f → f fa ) (
             -- FMap F (Category.Category.Id A) fa ≡ fa
             begin
               ( FMap F (id1 A _ )) 
             ≈⟨ IsFunctor.identity (isFunctor F)    ⟩
                id1 Sets (FObj F a)
             ∎ )

≡-cong = Relation.Binary.PropositionalEquality.cong 

--     ha : NTrans (op A) Sets (y-obj {a}) F
--                FMap F  g  o TMap ha a ≈   TMap ha b  o FMap (y-obj {a}) g
Nat2F→F2Nat :  {a : Obj A } → {F : Obj SetsAop } → (ha : Hom SetsAop  (y-obj  a) F) 
     →  SetsAop  [ F2Nat  {a} {F} (Nat2F  {a} {F} ha) ≈ ha ]
Nat2F→F2Nat {a} {F} ha {b} = let open ≡-Reasoning in begin
     TMap (F2Nat  {a} {F} (Nat2F {a} {F} ha)) b ≡⟨⟩
     (λ g → FMap F g (TMap ha a (id1 A _))) ≡⟨  extensionality A  (λ g → ( begin
            FMap F g (TMap ha a (id1 A _)) ≡⟨  ≡-cong (λ f → f (id1 A _)) (IsNTrans.commute (isNTrans ha)) ⟩
            TMap ha b (FMap (y-obj a) g (id1 A _)) ≡⟨⟩
            TMap ha b ( A [ id1 A _ o g ] ) ≡⟨  ≡-cong ( TMap ha b ) ( ≈-≡ A (≈-Reasoning.idL A)) ⟩
            TMap ha b g ∎ )) ⟩
        TMap ha b
     ∎ 

-- Yoneda's Lemma
--    Yoneda Functor is full and faithfull
--    that is FMapp Yoneda is injective and surjective

--  λ b g → (A Category.o f₁) g
YonedaLemma1 :  {a a' : Obj A } {f : FObj (FObj YonedaFunctor  a) a' } 
     → SetsAop [ F2Nat  {a'} {FObj YonedaFunctor  a} f ≈ FMap YonedaFunctor  f ]
YonedaLemma1 {a} {a'} {f} = refl

YonedaIso0 :  {a a' : Obj A } {f : FObj (FObj YonedaFunctor  a) a' } 
     → Nat2F ( FMap YonedaFunctor  f ) ≡ f
YonedaIso0 {a} {a'} {f} = ≈-≡ A (≈-Reasoning.idR A)

YonedaIso1 : {a a' : Obj A } →  (ha : Hom SetsAop  (y-obj  a) (y-obj a'))
     →  SetsAop  [ FMap YonedaFunctor (Nat2F  {a} ha) ≈ ha ]
YonedaIso1 {a} {a'} ha = Nat2F→F2Nat ha 

domF : (y :  Obj SetsAop) → {x : Obj (Category.op A)} → FObj y x → Obj A
domF y {x} z = x

YonedaLemma2 :  {a a' b : Obj A } (f : Hom A a  a' ) →  NTrans (Category.op A) Sets (FObj YonedaFunctor a) (FObj YonedaFunctor a')
YonedaLemma2 f =  FMap YonedaFunctor  f

YonedaLemma3 :  {a a' b : Obj A } (f : Hom A a  a' ) → (g : Hom A b a ) →  Hom A b a' -- f o g
YonedaLemma3 {a} {a'} {b} f g = TMap  (FMap YonedaFunctor  f) b g

YonedaLemma4 :  {a a' b : Obj A } (f : Hom A a  a' ) → (g : Hom A b a ) →  Hom A b a' -- f o g
YonedaLemma4 {a} {a'} {b} f = TMap  (FMap YonedaFunctor  f) b 

--
-- f ∈ FMap (FObj YonedaFunctor a') a
--

--                g       f
--             b --→ a ------→ a'      
--                   |         |
--     TMap (H f) b  |         | TMap (H id) a'
--          o g      ↓         ↓          o (f o g)
--                 H a ------→ H a'
--                      H f
--

_^ : {a a' b : Obj A } → (f : Hom A a  a' )  → Hom A b a →  Hom A b a' 
_^ {a} {a'} {b} f g = (FMap (FObj YonedaFunctor a') g) f

f-unique : {a a' b : Obj A } (f : Hom A a  a' ) →  f ^ ≡ TMap  (FMap YonedaFunctor  f) b
f-unique {a} {a'} {b} f  =  extensionality A  (λ g → begin
             (f ^ ) g ≡⟨⟩
             (FMap (FObj YonedaFunctor a') g) f ≡⟨⟩
             A [ f o g ] ≡⟨⟩
             TMap  (FMap YonedaFunctor  f) b g ∎  ) where  open ≡-Reasoning 

f-u : {a a' b : Obj A } (f : FObj (FObj YonedaFunctor a') a  ) → Sets [  f ^ ≈   TMap (FMap YonedaFunctor f ) b ]
f-u = f-unique

-- faithful (injective )
Yoneda-injective : {a b b'  : Obj A } → {x y : Obj SetsAop} → (g h : Hom A b b' )  (f : Hom A a b )
    → SetsAop [ FMap YonedaFunctor g  ≈  FMap YonedaFunctor h ]
    → A [  g ≈ h ]
Yoneda-injective {a} {b} {x} {y} g h f yg=yh = begin
             g  ≈↑⟨ idR  ⟩
             Nat2F (FMap YonedaFunctor g)  ≈⟨ ylem11 yg=yh ⟩ 
             Nat2F (FMap YonedaFunctor h)  ≈⟨ idR ⟩
             h  ∎  where
     ylem11 : SetsAop [ FMap YonedaFunctor g  ≈  FMap YonedaFunctor h ] → A [ Nat2F (FMap YonedaFunctor g) ≈ Nat2F (FMap YonedaFunctor h) ]
     ylem11 yg=yh with  yg=yh {b}
     ... | eq = ≈-Reasoning.≈←≡ A ( cong (λ k →  k (id1 A b)) eq )
     open ≈-Reasoning A

-- full (surjective)

record CatSurjective { c₁ c₂ ℓ c₁' c₂' ℓ' : Level} ( A : Category c₁ c₂ ℓ ) ( B : Category c₁' c₂' ℓ' ) (F : Functor A B)
         : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ')) where
     field 
       sur :        {a a' : Obj A} (g : Hom B (FObj F a) (FObj F a')) → Hom A a a'
       surjective : {a a' : Obj A} (g : Hom B (FObj F a) (FObj F a')) → B [ FMap F (sur g) ≈ g ]

open CatSurjective

CatEpi : {c : Level} (F : Functor (Sets {c}) (Sets {c}))
    → (s : CatSurjective Sets Sets F  )
    → {a a' : Obj Sets } {b : Obj Sets} (g h : Hom Sets (FObj F a') b)
    → Sets [ Sets [ g o FMap F ( sur s (id1 Sets _)) ] ≈  Sets [ h o FMap F ( sur s (id1 Sets _)) ] ]  → Sets [ g  ≈ h ]
CatEpi F s g h  eq = begin
     g ≈↑⟨ idR ⟩
     Sets [ g o id1  Sets _ ]  ≈↑⟨ cdr (surjective s (id1 Sets _) ) ⟩
     Sets [ g o  FMap F (sur s (id1 Sets _)) ]  ≈⟨ eq ⟩
     Sets [ h o  FMap F (sur s (id1 Sets _)) ]  ≈⟨ cdr (surjective s (id1 Sets _) ) ⟩
     Sets [ h o id1  Sets _ ]  ≈⟨ idR ⟩
     h ∎ 
  where
     open ≈-Reasoning Sets
     -- sj : B [ FMap F ( CatSurjective.sur s (FMap F (f g h))) ≈ FMap F (f g h) ]
     -- sj  = CatSurjective.surjective s (FMap F (f g h)) 

Yoneda-surjective : CatSurjective A SetsAop YonedaFunctor 
Yoneda-surjective  = record { sur = λ {a} {a'} g → f g ; surjective = λ g → 
  begin
     TMap (FMap YonedaFunctor (f g) ) _ ≈⟨ YonedaIso1 g ⟩
     TMap g _ ∎ 
 } where
     open ≈-Reasoning Sets
     f : {a a' : Obj A } → (g : Hom SetsAop (FObj YonedaFunctor a) (FObj YonedaFunctor a')) → Hom A a a'
     f g = Nat2F g

Yoneda-epi : { b : Obj A } {x y : Obj SetsAop} → (g h : Hom SetsAop (FObj YonedaFunctor b) y)
    → ( {a : Obj A } (f : Hom A a b ) → SetsAop [ SetsAop [ g o FMap YonedaFunctor f ] ≈ SetsAop [ h o FMap YonedaFunctor f ] ] )
    → SetsAop [  g ≈ h ]
Yoneda-epi {b} {x} {y} g h yg=yh = begin
         TMap g _ ≈↑⟨ idR ⟩
         Sets [ TMap g _  o id1  Sets _ ] ≈↑⟨  cdr (surjective Yoneda-surjective (id1 SetsAop _)) ⟩
         Sets [ TMap g _  o (λ z → A [ sur Yoneda-surjective (id1 SetsAop _) o z ] ) ]   ≈⟨⟩
         (λ z → TMap g _ (A [ id1 A _  o z ] ))   ≈⟨ yg=yh (id1 A b) ⟩
         Sets [ TMap h _  o (λ z → A [ sur Yoneda-surjective (id1 SetsAop _) o z ] ) ] ≈⟨  cdr (surjective Yoneda-surjective (id1 SetsAop _)) ⟩
         Sets [ TMap h _  o id1  Sets _ ] ≈⟨ idR ⟩
         TMap h _
         ∎ where
             open ≈-Reasoning Sets
             s : CatSurjective A SetsAop YonedaFunctor 
             s = Yoneda-surjective 

--- How to prove it? from smallness?

data _~_   {a b : Obj A} (f : Hom A a b)
     : ∀{x y : Obj A} → Hom A x y → Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
  refl : {g : Hom A a b} → (eqv : A [ f ≈ g ]) →  f ~ g

postulate  -- ?
     eqObj1 : {a b a' b' : Obj A } → Hom A a b ≡ Hom A a' b' → b ≡ b'

Yoneda-full-embed : {a b : Obj A } → FObj YonedaFunctor a ≡ FObj YonedaFunctor b → a ≡ b
Yoneda-full-embed {a} {b} eq = eqObj1 ylem1 where
     ylem1 : Hom A a a ≡ Hom A a b
     ylem1 = cong (λ k → FObj k a) eq

