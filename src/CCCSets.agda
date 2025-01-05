-- {-# OPTIONS --cubical-compatible --allow-unsolved-metas #-}
{-# OPTIONS  --cubical-compatible --safe #-}
-- {-# OPTIONS  --warning=noUnsupportedIndexedMatch --allow-unsolved-metas #-}
module CCCSets where

open import Level
open import Category 
open import HomReasoning
open import Definitions
open import Data.Product renaming (_×_ to _/\_  ) hiding ( <_,_> )
open import Category.Constructions.Product
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import CCC

open Functor

--   ccc-1 : Hom A a 1 ≅ {*}
--   ccc-2 : Hom A c (a × b) ≅ (Hom A c a ) × ( Hom A c b )
--   ccc-3 : Hom A a (c ^ b) ≅ Hom A (a × b) c

open import Category.Sets

-- Sets is a CCC

-- open import SetsCompleteness hiding (ki1)

import Axiom.Extensionality.Propositional

data One  {c : Level } : Set c where
  ! : One   -- () in Haskell ( or any one object set )

ccc-sets : {c : Level } 
   → CCC (Sets {c})
ccc-sets = record {
         １  = One
       ; ○ = λ _ → λ _ → !
       ; _∧_ = _∧_
       ; <_,_> = <,>
       ; π = π
       ; π' = π'
       ; _<=_ = _<=_
       ; _* = _*
       ; ε = ε
       ; isCCC = isCCC
  } where
         １ : Obj Sets 
         １ = One 
         ○ : (a : Obj Sets ) → Hom Sets a １
         ○ a = λ _ → !
         _∧_ : Obj Sets → Obj Sets → Obj Sets
         _∧_ a b =  a /\  b
         <,> : {a b c : Obj Sets } → Hom Sets c a → Hom Sets c b → Hom Sets c ( a ∧ b)
         <,> f g = λ x → ( f x , g x )
         π : {a b : Obj Sets } → Hom Sets (a ∧ b) a
         π {a} {b} =  proj₁ 
         π' : {a b : Obj Sets } → Hom Sets (a ∧ b) b
         π' {a} {b} =  proj₂ 
         _<=_ : (a b : Obj Sets ) → Obj Sets
         a <= b  = b → a
         _* : {a b c : Obj Sets } → Hom Sets (a ∧ b) c → Hom Sets a (c <= b)
         f * =  λ x → λ y → f ( x , y )
         ε : {a b : Obj Sets } → Hom Sets ((a <= b ) ∧ b) a
         ε {a} {b} =  λ x → ( proj₁ x ) ( proj₂ x )
         isCCC : CCC.IsCCC Sets １ ○ _∧_ <,> π π' _<=_ _* ε
         isCCC = record {
               e2  = e2
             ; e3a = λ {a} {b} {c} {f} {g} → e3a {a} {b} {c} {f} {g}
             ; e3b = λ {a} {b} {c} {f} {g} → e3b {a} {b} {c} {f} {g}
             ; e3c = e3c
             ; π-cong = π-cong
             ; e4a = e4a
             ; e4b = e4b
           } where
                e2 : {a : Obj Sets} {f : Hom Sets a １} → Sets [ f ≈ ○ a ]
                e2 {a} {f} x = e20 x 
                  where
                        e20 : (x : a ) → f x ≡ ○ a x
                        e20 x with f x
                        e20 x | ! = refl
                e3a : {a b c : Obj Sets} {f : Hom Sets c a} {g : Hom Sets c b} →
                    Sets [ ( Sets [  π  o ( <,> f g)  ] ) ≈ f ]
                e3a _ = refl
                e3b : {a b c : Obj Sets} {f : Hom Sets c a} {g : Hom Sets c b} →
                    Sets [ Sets [ π' o ( <,> f g ) ] ≈ g ]
                e3b _ = refl
                e3c : {a b c : Obj Sets} {h : Hom Sets c (a ∧ b)} →
                    Sets [ <,> (Sets [ π o h ]) (Sets [ π' o h ]) ≈ h ]
                e3c _ = refl
                π-cong : {a b c : Obj Sets} {f f' : Hom Sets c a} {g g' : Hom Sets c b} →
                    Sets [ f ≈ f' ] → Sets [ g ≈ g' ] → Sets [ <,> f g ≈ <,> f' g' ]
                π-cong {a} {b} {c} {f} {f'} {g} {g'} f=f g=g x = begin
                    (f x , g x)  ≡⟨ cong₂ _,_ (f=f x) (g=g x)  ⟩
                    (f' x , g' x)  ≡⟨⟩
                    <,> f' g' x ∎ where
                       open ≡-Reasoning 
                e4a : {a b c : Obj Sets} {h : Hom Sets (c ∧ b) a} →
                    Sets [ Sets [ ε o <,> (Sets [ h * o π ]) π' ] ≈ h ]
                e4a _ = refl
                e4b : {a b c : Obj Sets} {k : Hom Sets c (a <= b)} →
                    Sets [ (Sets [ ε o <,> (Sets [ k o π ]) π' ]) * ≈ k ]
                e4b _ = refl

--    →  (extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Axiom.Extensionality.Propositional.Extensionality  c₂ c₂)
--               *-cong : {a b c : Obj Sets} {f f' : Hom Sets (a ∧ b) c} →
--                   Sets [ f ≈ f' ] → Sets [ f * ≈ f' * ]
--               *-cong {a} {b} {c} {f} {f'} f=f x = begin
--                  (f  *) x  ≡⟨⟩
--                  (λ y → f  (x , y) )   ≡⟨ ext Sets (λ y → f=f (x , y)) ⟩
--                  (λ y → f' (x , y) )   ≡⟨⟩
--                  (f' *) x  ∎ where
--                      open ≡-Reasoning

open import Relation.Nullary
open import Data.Empty
open import equalizer

     
open import graph
module ccc-from-graph {c₁ c₂ : Level }  (G : Graph {c₁} {c₂})  where

   open import Relation.Binary.PropositionalEquality renaming ( cong to ≡-cong ) hiding ( [_] )
   open Graph

   V = vertex G
   E : V → V → Set c₂
   E = edge G
   
   data Objs : Set c₁ where
      atom : V → Objs 
      ⊤ : Objs 
      _∧_ : Objs  → Objs → Objs 
      _<=_ : Objs → Objs → Objs 

   data  Arrows  : (b c : Objs ) → Set (c₁  ⊔  c₂)
   data Arrow :  Objs → Objs → Set (c₁  ⊔ c₂)  where                       --- case i
      arrow : {a b : V} →  E a b → Arrow (atom a) (atom b)
      π : {a b : Objs } → Arrow ( a ∧ b ) a
      π' : {a b : Objs } → Arrow ( a ∧ b ) b
      ε : {a b : Objs } → Arrow ((a <= b) ∧ b ) a
      _* : {a b c : Objs } → Arrows (c ∧ b ) a → Arrow c ( a <= b )        --- case v

   data  Arrows where
      id : ( a : Objs ) → Arrows a a                                      --- case i
      ○ : ( a : Objs ) → Arrows a ⊤                                       --- case i
      <_,_> : {a b c : Objs } → Arrows c a → Arrows c b → Arrows c (a ∧ b)      -- case iii
      iv  : {b c d : Objs } ( f : Arrow d c ) ( g : Arrows b d ) → Arrows b c   -- cas iv

   _・_ :  {a b c : Objs } (f : Arrows b c ) → (g : Arrows a b) → Arrows a c
   id a ・ g = g
   ○ a ・ g = ○ _
   < f , g > ・ h = < f ・ h , g ・ h >
   iv f g ・ h = iv f ( g ・ h )


   identityL : {A B : Objs} {f : Arrows A B} → (id B ・ f) ≡ f
   identityL = refl

   identityR : {A B : Objs} {f : Arrows A B} → (f ・ id A) ≡ f
   identityR {a} {a} {id a} = refl
   identityR {a} {⊤} {○ a} = refl 
   identityR {a} {_} {< f , f₁ >} = cong₂ (λ j k → < j , k > ) identityR identityR
   identityR {a} {b} {iv f g} = cong (λ k → iv f k ) identityR

   assoc≡ : {a b c d : Objs} (f : Arrows c d) (g : Arrows b c) (h : Arrows a b) →
                            (f ・ (g ・ h)) ≡ ((f ・ g) ・ h)
   assoc≡ (id a) g h = refl
   assoc≡ (○ a) g h = refl 
   assoc≡ < f , f₁ > g h =  cong₂ (λ j k → < j , k > ) (assoc≡ f g h) (assoc≡ f₁ g h) 
   assoc≡ (iv f f1) g h = cong (λ k → iv f k ) ( assoc≡ f1 g h )

   -- positive intutionistic calculus
   PL :  Category  c₁ (c₁  ⊔ c₂) (c₁  ⊔ c₂)
   PL = record {
            Obj  = Objs;
            Hom = λ a b →  Arrows  a b ;
            _o_ =  λ{a} {b} {c} x y → x ・ y ;
            _≈_ =  λ x y → x ≡  y ;
            Id  =  λ{a} → id a ;
            isCategory  = record {
                    isEquivalence =  record {refl = refl ; trans = trans ; sym = sym} ;
                    identityL  = λ {a b f} → identityL {a} {b} {f} ; 
                    identityR  = λ {a b f} → identityR {a} {b} {f} ; 
                    o-resp-≈  = λ {a b c f g h i} → o-resp-≈ {a} {b} {c} {f} {g} {h} {i}  ; 
                    associative  = λ{a b c d f g h } → assoc≡  f g h
               }
           } where  
              o-resp-≈  : {A B C : Objs} {f g : Arrows A B} {h i : Arrows B C} →
                                    f ≡  g → h ≡  i → (h ・ f) ≡ (i ・ g)
              o-resp-≈ refl refl = refl

--  ccc-PL : CCC PL
--  ccc-PL = record {
--        １  =  ⊤
--      ; ○ = λ a → ○ a
--      ; _∧_ = _∧_
--      ; <_,_> = λ {a} {b} {c} f g → < f , g >
--      ; π = λ {a} {b}  → iv  π  (id _)
--      ; π' = λ {a} {b}  → iv  π'  (id _)
--      ; _<=_ = λ f g → f <= g
--      ; _* = λ {a} {b} {c} f → iv  (f *)  (id _)
--      ; ε = λ {a} {b} → iv  ε  (id _)
--      ; isCCC = isCCC
--    } where
--        isCCC : CCC.IsCCC PL ⊤ (λ a → ○ a)  _∧_ ((λ {a} {b} {c} f g → < f , g >)) (iv π (id _)) (iv π' (id _)) 
--            (λ f g → f <= g ) (λ f → iv (f *) (id _)) (iv ε (id _))
--        isCCC = record {
--              e2  = λ {a} {f} → ?
--            ; e3a = λ {a} {b} {c} {f} {g} → ?
--            ; e3b = λ {a} {b} {c} {f} {g} → ?
--            ; e3c = ?
--            ; π-cong = ?
--            ; e4a = ?
--            ; e4b = ?
--          } 
--
--------
--
-- Functor from Positive Logic to Sets
--

   C = graphtocat.Chain G

   tr : {a b : vertex G} → edge G a b → ((y : vertex G) → C y a) → (y : vertex G) → C y b
   tr f x y = graphtocat.next f (x y) 
   
   fobj :  ( a  : Objs  ) → Set (c₁  ⊔ c₂)
   fobj  (atom x) = ( y : vertex G ) → C y x
   fobj ⊤ = One
   fobj  (a ∧ b) = ( fobj  a /\ fobj  b)
   fobj  (a <= b) = fobj  b → fobj  a

   fmap :  { a b : Objs  } → Hom PL a b → fobj  a → fobj  b
   amap :  { a b : Objs  } → Arrow  a b → fobj  a → fobj  b
   amap  (arrow x) y =  tr x y -- tr x
   amap π ( x , y ) = x 
   amap π' ( x , y ) = y
   amap ε (f , x ) = f x
   amap (f *) x = λ y →  fmap f ( x , y ) 
   fmap (id a) x = x
   fmap (○ a) x = !
   fmap < f , g > x = ( fmap f x , fmap g x )
   fmap (iv x f) a = amap x ( fmap f a )

--   CS is a map from Positive logic to Sets
--    Sets is CCC, so we have a cartesian closed category generated by a graph
--       as a sub category of Sets

   CS :  Functor PL (Sets {c₁ ⊔ c₂})
   FObj CS a  = fobj  a
   FMap CS {a} {b} f = fmap  {a} {b} f
   isFunctor CS = isf where
        _+_ = Category._o_ PL
        ++idR = IsCategory.identityR ( Category.isCategory PL )
        distr : {a b c : Obj PL}  { f : Hom PL a b } { g : Hom PL b c } → (z : fobj  a ) → fmap (g + f) z ≡ fmap g (fmap f z)
        distr {a} {a₁} {a₁} {f} {id a₁} z = refl
        distr {a} {a₁} {⊤} {f} {○ a₁} z = refl
        distr {a} {b} {c ∧ d} {f} {< g , g₁ >} z = cong₂ (λ j k  →  j , k  ) (distr {a} {b} {c} {f} {g} z) (distr {a} {b} {d} {f} {g₁} z)
        distr {a} {b} {c} {f} {iv {_} {_} {d} x g} z = adistr (distr  {a} {b} {d} {f} {g} z) x where 
           adistr : fmap (g + f) z ≡ fmap g (fmap f z) →
                ( x : Arrow d c ) → fmap ( iv x (g + f) ) z  ≡ fmap ( iv x g ) (fmap f z )
           adistr eq x = cong ( λ k → amap x k ) eq
        isf : IsFunctor PL Sets fobj fmap 
        IsFunctor.identity isf x = refl 
        IsFunctor.≈-cong isf refl x = refl 
        IsFunctor.distr isf {a} {b} {c} {g} {f} x = distr {a} {b} {c} {g} {f} x 


