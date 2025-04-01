{-# OPTIONS  --cubical-compatible --safe #-}
module CCCSets where

open import Level
open import Category
open import HomReasoning
open import Definitions
open import Data.Product renaming (_×_ to _/\_  ) hiding ( <_,_> )
open import Category.Constructions.Product
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import CCC
open import Data.Unit

open Functor

--   ccc-1 : Hom A a 1 ≅ {*}
--   ccc-2 : Hom A c (a × b) ≅ (Hom A c a ) × ( Hom A c b )
--   ccc-3 : Hom A a (c ^ b) ≅ Hom A (a × b) c

open import Category.Sets

-- Sets is a CCC

-- open import SetsCompleteness hiding (ki1)

import Axiom.Extensionality.Propositional

ccc-sets : {c : Level }
   → CCC (Sets {c})
ccc-sets {c} = record {
         １  = Lift c ⊤
       ; ○ = λ _ → λ _ → lift tt
       ; _∧_ = _∧_
       ; <_,_> = <,>
       ; π = π
       ; π' = π'
       ; _<=_ = _<=_
       ; _* = _*
       ; ε = ε
       ; isCCC = isCCC
  } where
         １ : Obj (Sets  {c})
         １ = Lift c ⊤
         ○ : (a : Obj (Sets {c}) ) → Hom (Sets {c}) a １
         ○ a = λ _ → lift tt
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

ccc-sets-*-cong : {c : Level} (ext :  Axiom.Extensionality.Propositional.Extensionality  c c)
   → CCC-* (Sets {c})
ccc-sets-*-cong {c} ext = record {
         １  = Lift c ⊤
       ; ○ = λ _ → λ _ → lift tt
       ; _∧_ = _∧_
       ; <_,_> = <,>
       ; π = π
       ; π' = π'
       ; _<=_ = _<=_
       ; _* = _*
       ; ε = ε
       ; isCCC = CCC.isCCC (ccc-sets {c} )
       ; is*-CCC = record {
             *-cong = *-cong
          }
    } where
         １ : Obj (Sets  {c})
         １ = Lift c ⊤
         ○ : (a : Obj (Sets {c}) ) → Hom (Sets {c}) a １
         ○ a = λ _ → lift tt
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
         *-cong : {a b c : Obj Sets} {f f' : Hom Sets (a ∧ b) c} →
             Sets [ f ≈ f' ] → Sets [ f * ≈ f' * ]
         *-cong {a} {b} {c} {f} {f'} f=f x = begin
            (f  *) x  ≡⟨⟩
            (λ y → f  (x , y) )   ≡⟨ ext (λ y → f=f (x , y)) ⟩
            (λ y → f' (x , y) )   ≡⟨⟩
            (f' *) x  ∎ where
                open ≡-Reasoning

