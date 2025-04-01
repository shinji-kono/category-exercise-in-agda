-- {-# OPTIONS --with-K --cubical-compatible #-}
{-# OPTIONS --cubical-compatible --safe #-}
module CCCgraph where

open import Level
open import Category
open import HomReasoning
open import Definitions
open import Data.Product renaming (_×_ to _/\_  ) hiding ( <_,_> )
open import Category.Constructions.Product
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import CCC
import Axiom.Extensionality.Propositional

open Functor

--   ccc-1 : Hom A a 1 ≅ {*}
--   ccc-2 : Hom A c (a × b) ≅ (Hom A c a ) × ( Hom A c b )
--   ccc-3 : Hom A a (c ^ b) ≅ Hom A (a × b) c

open import Category.Sets
open import graph
open import Data.Unit
-- open import Polynominal

-- import Axiom.Extensionality.Propositional
-- postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Axiom.Extensionality.Propositional.Extensionality  c₂ c₂

infixr 8 _∨_
data _∨_ {c c' : Level } (a : Set c) (b : Set c') : Set (c ⊔ c') where
        case1 : a → a ∨ b
        case2 : b → a ∨ b

module ccc-from-graph {c₁ c₂ : Level }  (G : Graph {c₁} {c₂})  (ext : Axiom.Extensionality.Propositional.Extensionality (c₁ ⊔ c₂) (c₁ ⊔ c₂) ) where

   open import Relation.Binary.PropositionalEquality renaming ( cong to ≡-cong ) hiding ( [_] )
   open Graph

   V = vertex G
   E : V → V → Set c₂
   E = edge G
   
   data Objs : Set c₁ where
      atom : V → Objs 
      top : Objs 
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
      id : (a : Objs ) → Arrows a a                                      --- case i
      ○ : (a : Objs ) → Arrows a top                                       --- case i
      <_,_> : {a b c : Objs } → Arrows c a → Arrows c b → Arrows c (a ∧ b)      -- case iii
      iv  : {b c d : Objs } ( f : Arrow d c ) ( g : Arrows b d ) → Arrows b c   -- cas iv

   _∙_ :  {a b c : Objs } (f : Arrows b c ) → (g : Arrows a b) → Arrows a c
   id _ ∙ g = g
   ○ _ ∙ g = ○ _
   < f , g > ∙ h = < f ∙ h , g ∙ h >
   iv f g ∙ h = iv f ( g ∙ h )


   identityL : {A B : Objs} {f : Arrows A B} → (id B ∙ f) ≡ f
   identityL = refl

   identityR : {A B : Objs} {f : Arrows A B} → (f ∙ id A) ≡ f
   identityR {a} {b} {id _} = refl
   identityR {a} {⊤} {○ eq} = refl 
   identityR {a} {_} {< f , f₁ >} = cong₂ (λ j k → < j , k > ) identityR identityR
   identityR {a} {b} {iv f g} = cong (λ k → iv f k ) identityR

   plassoc : {a b c d : Objs} (f : Arrows c d) (g : Arrows b c) (h : Arrows a b) →
                            (f ∙ (g ∙ h)) ≡ ((f ∙ g) ∙ h)
   plassoc (id _) g h = refl
   plassoc (○ a) g h = refl 
   plassoc < f , f₁ > g h =  cong₂ (λ j k → < j , k > ) (plassoc f g h) (plassoc f₁ g h) 
   plassoc (iv f f1) g h = cong (λ k → iv f k ) ( plassoc f1 g h )
   o-resp-≈  : {A B C : Objs} {f g : Arrows A B} {h i : Arrows B C} →
                        f ≡  g → h ≡  i → (h ∙ f) ≡ (i ∙ g)
   o-resp-≈ refl refl = refl

   -- positive intutionistic calculus
   PL :  Category  c₁ (c₁  ⊔ c₂) (c₁  ⊔ c₂)
   PL = record {
            Obj  = Objs;
            Hom = λ a b →  Arrows  a b ;
            _o_ =  λ{a} {b} {c} x y → x ∙ y ;
            _≈_ =  λ x y → x ≡  y ;
            Id  =  λ{a} → id a ;
            isCategory  = record {
                    isEquivalence =  record {refl = refl ; trans = trans ; sym = sym} ;
                    identityL  = λ {a b f} → identityL {a} {b} {f} ; 
                    identityR  = λ {a b f} → identityR {a} {b} {f} ; 
                    o-resp-≈  = λ {a b c f g h i} → o-resp-≈ {a} {b} {c} {f} {g} {h} {i}  ; 
                    associative  = λ{a b c d f g h } → plassoc  f g h
               }
           } 


   open import Relation.Nullary
   open import Data.Empty

   data Bool { c : Level } : Set c where
         true : Bool
         false : Bool

   ¬f≡t  : { c : Level } → ¬ (false {c} ≡ true )
   ¬f≡t ()

   ¬x≡t∧x≡f  : { c : Level } → {x : Bool {c}} → ¬ ((x ≡ false) /\ (x ≡ true) )
   ¬x≡t∧x≡f {_} {true} p = ⊥-elim (¬f≡t (sym (proj₁ p)))
   ¬x≡t∧x≡f {_} {false} p = ⊥-elim (¬f≡t (proj₂ p))
         
--------
--
-- CCC of  Positive Logic 
--

   C = graphtocat.Chain G

   tr : {a b : vertex G} → edge G a b → ((y : vertex G) → C y a) → (y : vertex G) → C y b
   tr f x y = graphtocat.next f (x y) 
   
   fobj :  ( a  : Objs  ) → Set (c₁  ⊔ c₂)
   fobj  (atom x) = ( y : vertex G ) → C y x
   fobj top = Lift _  ⊤
   fobj  (a ∧ b) = ( fobj  a /\ fobj  b)
   fobj  (a <= b) = fobj  b → fobj  a

   fmap :  { a b : Objs  } → Hom PL a b → fobj  a → fobj  b
   amap :  { a b : Objs  } → Arrow  a b → fobj  a → fobj  b
   amap  (arrow x) y =  tr x y -- tr x
   amap π ( x , y ) = x 
   amap π' ( x , y ) = y
   amap ε (f , x ) = f x
   amap (f *) x = λ y →  fmap f ( x , y ) 
   fmap (id _) x = x
   fmap (○ _) x = lift tt  -- subst ( λ k → fobj k) (sym eq) ( lift tt  )
   fmap < f , g > x = ( fmap f x , fmap g x )
   fmap (iv x f) a = amap x ( fmap f a )

   -- to do so, we have to chose right equivalence relation
   -- 

   _≐_ : {a b : Objs} → (f g : Hom PL a b) → Set (c₁  ⊔ c₂)
   _≐_ {a} {b} fa fb = (oa : fobj a) → fmap fa oa ≡ fmap fb oa

   fmap-distr : {a b c : Obj PL}  { f : Hom PL a b } { g : Hom PL b c } → (z : fobj  a ) → fmap (g ∙ f) z ≡ fmap g (fmap f z)
   fmap-distr {a} {a₁} {b} {f} {id _} z = refl
   fmap-distr {a} {a₁} {⊤} {f} {○ _} z = refl
   fmap-distr {a} {b} {c ∧ d} {f} {< g , g₁ >} z = cong₂ (λ j k  →  j , k  ) (fmap-distr {a} {b} {c} {f} {g} z) (fmap-distr {a} {b} {d} {f} {g₁} z)
   fmap-distr {a} {b} {c} {f} {iv {_} {_} {d} x g} z = adistr (fmap-distr  {a} {b} {d} {f} {g} z) x where 
       adistr : fmap (g ∙ f) z ≡ fmap g (fmap f z) →
            ( x : Arrow d c ) → fmap ( iv x (g ∙ f) ) z  ≡ fmap ( iv x g ) (fmap f z )
       adistr eq x = cong ( λ k → amap x k ) eq

   -- no injection here, because of ¬ ( id top ≡ ○ top )
   -- ≐-iject : {a b : Objs} → (f g : Hom PL a b) → (f ≐ g) → (f ≡ g) 

   PLC :  Category  c₁ (c₁  ⊔ c₂) (c₁  ⊔ c₂)
   PLC = record {
            Obj  = Objs ;
            Hom = λ a b → Arrows a b ;
            _o_ =  λ{a} {b} {c} x y →  x ∙ y ;
            _≈_ =  λ x y → x ≐ y  ;
            Id  =  λ{a} → id a  ;
            isCategory  = record {
                    isEquivalence =  record { refl = λ _ → refl ; trans = λ f=g g=h → λ oa → trans (f=g oa) (g=h oa) ; sym = λ eq oa → sym (eq oa) } ; 
                    identityL  = λ {a b f} oa → refl ;
                    identityR  = λ {a b f} oa → cong (λ k → fmap k oa ) (identityR {a} {b} {f} ) ;
                    o-resp-≈  = λ {a b c f g h i} f=g h=i →  o-resp {a} {b} {c} f g h i f=g h=i ;
                    associative  = λ{a b c d f g h } oa →  cong (λ k → fmap k oa ) (plassoc  f g h)
               }
           }  where
              o-resp : {A B C : Objs} (f g : Hom PL A B) (h i : Hom PL B C) → f ≐ g → h ≐ i → (h ∙ f) ≐ (i ∙ g)
              o-resp {a} {b} {c} f g h i f=g h=i oa = begin
                 fmap (h ∙ f) oa ≡⟨ fmap-distr {a} {b} {c} {f} {h} oa ⟩
                 fmap h (fmap f oa) ≡⟨ cong (λ k → fmap h k) (f=g oa) ⟩
                 fmap h (fmap g oa) ≡⟨ h=i (fmap g oa) ⟩
                 fmap i (fmap g oa) ≡⟨ sym (fmap-distr {a} {b} {c} {g} {i} oa) ⟩
                 fmap (i ∙ g) oa ∎
                   where open ≡-Reasoning 


   ccc-PL : CCC PLC
   ccc-PL = record {
         １  =  top
       ; ○ = λ a → ○ a
       ; _∧_ = _∧_
       ; <_,_> = λ {a} {b} {c} f g → < f , g >
       ; π = λ {a} {b}  → iv  π  (id _)
       ; π' = λ {a} {b}  → iv  π'  (id _)
       ; _<=_ = λ f g → f <= g
       ; _* = λ {a} {b} {c} f → iv  (f *)  (id _)
       ; ε = λ {a} {b} → iv  ε  (id _)
       ; isCCC = isCCC
     } where
         isCCC : CCC.IsCCC PLC top (λ a → ○ a)  _∧_ ((λ {a} {b} {c} f g → < f , g >)) (iv π (id _)) (iv π' (id _)) 
             (λ f g → f <= g ) (λ f → iv (f *) (id _)) (iv ε (id _))
         isCCC = record {
               e2  = λ {a} {f} oa → e2lem {a} oa f 
             ; e3a = λ {a} {b} {c} {f} {g} oa → e3alem oa f g
             ; e3b = λ {a} {b} {c} {f} {g} oa → e3blem oa f g
             ; e3c = λ {a} {b} {c} {h} → e3clem {a} {b} {c} {h}
             ; π-cong = λ {a} {b} {c} {f} {f'} {g} {g'} → π-cong-lem {a} {b} {c} {f} {f'} {g} {g'}
             ; e4a = λ  {a} {b} {c} {h} → e4a-lem {a} {b} {c} {h} 
             ; e4b = λ {a} {b} {c} {k} → e4b-lem {a} {b} {c} {k}
           } where
               e2lem : {c : Objs} →  (oa : fobj c) (f : Arrows c top) → fmap f oa ≡ lift tt
               e2lem oa f = refl 
               e3alem :  {a b c : Objs} → (oa : fobj c) → (f : Arrows c a)  → (g : Arrows c b)  → fmap (iv π (id (a ∧ b)) ∙ < f , g > ) oa ≡ fmap f oa
               e3alem oa f g = refl
               e3blem :  {a b c : Objs} → (oa : fobj c) → (f : Arrows c a)  → (g : Arrows c b)  → fmap (iv π' (id (a ∧ b)) ∙ < f , g > ) oa ≡ fmap g oa
               e3blem oa f g = refl
               e3clem : {a b c : Obj PLC} {h : Hom PLC c (a ∧ b)} → PLC [ < PLC [ iv π (id (a ∧ b)) o h ] , PLC [ iv π' (id (a ∧ b)) o h ] > ≈ h ]
               e3clem {a} {b} {c} {h} oa = refl
               π-cong-lem : {a b c : Obj PLC} {f f' : Hom PLC c a} {g g' : Hom PLC c b} → PLC [ f ≈ f' ] → PLC [ g ≈ g' ] → PLC [ < f , g > ≈ < f' , g' > ]
               π-cong-lem {a} {b} {c} {f} {f'} {g} {g'} eqf eqg oa = begin
                   fmap f oa , fmap g oa ≡⟨ cong₂ _,_  (eqf oa) (eqg oa)  ⟩
                   fmap f' oa , fmap g' oa  ∎ where open ≡-Reasoning
               e4a-lem :  {a b c : Obj PLC} {h : Hom PLC (c ∧ b) a} → PLC [ PLC [ iv ε (id ((a <= b) ∧ b)) 
                   o < PLC [ iv (h *) (id c) o iv π (id (c ∧ b)) ] , iv π' (id (c ∧ b)) > ] ≈ h ]
               e4a-lem {a} {b} {c} {h} oa = refl
               e4b-lem :  {a b c : Obj PLC} {k : Hom PLC c (a <= b)} → PLC [ iv ((PLC [ iv ε (id ((a <= b) ∧ b)) 
                   o < PLC [ k o iv π (id (c ∧ b)) ] , iv π' (id (c ∧ b)) > ]) *) (id c) ≈ k ]
               e4b-lem {a} {b} {.(a <= b)} {id .(a <= b)} oa = refl
               e4b-lem {a} {b} {c} {iv f k} oa = begin
                    (λ y → amap f (fmap (k ∙ iv π (id (c ∧ b))) (oa , y)) y)  ≡⟨ ext (λ y → ( begin    -- extensionality
                       amap f (fmap (k ∙ iv π (id (c ∧ b))) (oa , y)) y ≡⟨ cong (λ h → amap f h y ) (fmap-distr {_} {_} {_} {_} {k} (oa , y)) ⟩
                       amap f (fmap k oa) y ∎ ) ) ⟩
                    (λ y → amap f (fmap k (fmap (iv π (id (c ∧ b))) (oa , y))) y)  ≡⟨ refl ⟩
                    (λ y → amap f (fmap k oa) y)  ≡⟨ refl ⟩
                   amap f (fmap k oa) ∎ where open ≡-Reasoning

   ccc*-PL : CCC-* PLC
   ccc*-PL = record {
         １  =  top
       ; ○ = λ a → ○ a
       ; _∧_ = _∧_
       ; <_,_> = λ {a} {b} {c} f g → < f , g >
       ; π = λ {a} {b}  → iv  π  (id _)
       ; π' = λ {a} {b}  → iv  π'  (id _)
       ; _<=_ = λ f g → f <= g
       ; _* = λ {a} {b} {c} f → iv  (f *)  (id _)
       ; ε = λ {a} {b} → iv  ε  (id _)
       ; isCCC = CCC.isCCC (ccc-PL)
       ; is*-CCC = record { *-cong = λ {a} {b} {c} {f} {f'} → *-cong {a} {b} {c} {f} {f'} }
     } where 
        *-cong : {a b c : Obj PLC} {f f' : Hom PLC (a ∧ b) c} → PLC [ f ≈ f' ] → PLC [ iv (f *) (id a) ≈ iv (f' *) (id a) ]
        *-cong {a} {b} {c} {f} {g} eq oa = begin
            fmap (iv (f *) (id a)) oa ≡⟨ ext (λ y → eq (oa , y) ) ⟩
            fmap (iv (g *) (id a)) oa ∎ where open ≡-Reasoning

                

--   CS is a map from Positive logic to Sets
--    Sets is CCC, so we have a cartesian closed category generated by a graph
--       as a sub category of Sets

   CS :  Functor PL (Sets {c₁ ⊔ c₂})
   FObj CS a  = fobj  a
   FMap CS {a} {b} f = fmap  {a} {b} f
   isFunctor CS = isf where
        isf : IsFunctor PL Sets fobj fmap 
        IsFunctor.identity isf x = refl 
        IsFunctor.≈-cong isf refl x = refl 
        IsFunctor.distr isf {a} {b} {c} {g} {f} x = fmap-distr {a} {b} {c} {g} {f} x 


---
---  SubCategoy SC F A is a category with Obj = FObj F, Hom = FMap
---
---     CCC ( SC (CS G)) Sets   have to be proved
---  SM can be eliminated if we have
---    sobj (a : vertex g ) → {a}              a set have only a
---    smap (a b : vertex g ) → {a} → {b}


record CCCObj {c₁ c₂ ℓ : Level}  : Set  (suc (ℓ ⊔ (c₂ ⊔ c₁))) where
   field
     cat : Category c₁ c₂ ℓ
     ≡←≈ : {a b : Obj cat } → { f g : Hom cat a b } → cat [ f ≈ g ] → f ≡ g
     ccc : CCC cat

open CCCObj

record CCCMap {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (A : CCCObj {c₁} {c₂} {ℓ} ) (B : CCCObj {c₁′} {c₂′}{ℓ′} ) : Set (suc (ℓ′ ⊔ (c₂′ ⊔ c₁′) ⊔ ℓ ⊔ (c₂ ⊔ c₁))) where
   field
     cmap : Functor (cat A ) (cat B )
     ccf :  CCC (cat A) → CCC (cat B)

open import Category.Cat

open  CCCMap
open import Relation.Binary

Cart : {c₁ c₂ ℓ : Level} →  Category  (suc (c₁ ⊔ c₂ ⊔ ℓ)) (suc (ℓ ⊔ (c₂ ⊔ c₁))) (suc (ℓ ⊔ c₁ ⊔ c₂))
Cart  {c₁} {c₂} {ℓ} = record {
    Obj = CCCObj  {c₁} {c₂} {ℓ}
  ; Hom = CCCMap
  ; _o_ = λ {A} {B} {C} f g → record { cmap = (cmap f) ○ ( cmap g ) ; ccf = λ _ → ccf f ( ccf g (ccc A )) }
  ; _≈_ = λ {a} {b} f g → cmap f ≃ cmap g
  ; Id  = λ {a} → record { cmap = identityFunctor ; ccf = λ x → x }
  ; isCategory = record {
     isEquivalence = λ {A} {B} → record {
          refl = λ {f} →  let open ≈-Reasoning (CAT) in refl-hom {cat A} {cat B} {cmap f}
        ; sym = λ {f} {g}  → let open ≈-Reasoning (CAT) in sym-hom {cat A} {cat B} {cmap f} {cmap g}
        ; trans = λ {f} {g} {h} → let open ≈-Reasoning (CAT) in trans-hom {cat A} {cat B} {cmap f} {cmap g} {cmap h}  }
     ; identityL = λ {x} {y} {f} → let open ≈-Reasoning (CAT) in idL {cat x} {cat y} {cmap f} {_} {_}
     ; identityR = λ {x} {y} {f} → let open ≈-Reasoning (CAT) in idR {cat x} {cat y} {cmap f}
     ; o-resp-≈ = λ {x} {y} {z} {f} {g} {h} {i}  → IsCategory.o-resp-≈ ( Category.isCategory CAT) {cat x}{cat y}{cat z} {cmap f} {cmap g} {cmap h} {cmap i}
     ; associative =  λ {a} {b} {c} {d} {f} {g} {h} → let open ≈-Reasoning (CAT) in assoc {cat a} {cat b} {cat c} {cat d} {cmap f} {cmap g} {cmap h}
   }}

open import graph
open Graph

record GMap {c₁ c₂ c₁' c₂' : Level}  (x : Graph {c₁} {c₂} ) (y : Graph {c₁'} {c₂'}  )  : Set (c₁ ⊔ c₂ ⊔ c₁' ⊔ c₂') where
  field
   vmap : vertex x → vertex y
   emap : {a b : vertex x} → edge x a b → edge y (vmap a) (vmap b)

open GMap

-- open import Relation.Binary.HeterogeneousEquality using (_≅_;refl ) renaming ( sym to ≅-sym ; trans to ≅-trans ; cong to ≅-cong )

data [_]_==_ {c₁ c₂ : Level} (C : Graph  {c₁} {c₂}) {A B : vertex C} (f : edge C A B)
     : ∀{X Y : vertex C} → edge C X Y → Set (c₁ ⊔ c₂ ) where
  mrefl : {g : edge C A B} → (eqv : f ≡ g ) → [ C ] f == g

eq-vertex1 : {c₁ c₂ : Level} (C : Graph  {c₁} {c₂}) {A B : vertex C} {f : edge C A B}
      {X Y : vertex C} → {g : edge C X Y } → ( [ C ] f == g ) → A ≡ X
eq-vertex1 _ (mrefl refl) = refl

eq-vertex2 : {c₁ c₂ : Level} (C : Graph  {c₁} {c₂}) {A B : vertex C} {f : edge C A B}
      {X Y : vertex C} → {g : edge C X Y } → ( [ C ] f == g ) → B ≡ Y
eq-vertex2 _ (mrefl refl) = refl

--   eq-edge : {c₁ c₂ : Level} (C : Graph  {c₁} {c₂}) {A B : vertex C} {f : edge C A B}
--         {X Y : vertex C} → {g : edge C X Y } → ( [ C ] f == g ) → f ≅ g
--   eq-edge C eq with eq-vertex1 C eq | eq-vertex2 C eq
--   eq-edge C (mrefl refl) | refl | refl = refl

_=m=_ : {c₁ c₂ c₁' c₂'  : Level} {C : Graph {c₁} {c₂} } {D : Graph {c₁'} {c₂'} }
    → (F G : GMap C D) → Set (c₁ ⊔ c₂ ⊔ c₁' ⊔ c₂')
_=m=_ {C = C} {D = D} F G = ∀{A B : vertex C} → (f : edge C A B) → [ D ] emap F f == emap G f

_&_ :  {c₁ c₂ c₁' c₂'  c₁'' c₂'' : Level} {x : Graph {c₁} {c₂}} {y : Graph {c₁'} {c₂'}} {z : Graph {c₁''} {c₂''} } ( f : GMap y z ) ( g : GMap x y ) → GMap x z
f & g = record { vmap = λ x →  vmap f ( vmap g x ) ; emap = λ x → emap f ( emap g x ) }

Grph : {c₁ c₂ : Level} →  Category (suc (c₁ ⊔ c₂)) (c₁ ⊔ c₂) (c₁ ⊔ c₂)
Grph {c₁} {c₂}  = record {
    Obj = Graph {c₁} {c₂}
  ; Hom = GMap
  ; _o_ = _&_
  ; _≈_ = _=m=_
  ; Id  = record { vmap = λ y → y ; emap = λ f → f }
  ; isCategory = record {
       isEquivalence = λ {A} {B} →  ise
     ; identityL = λ e → mrefl refl
     ; identityR =  λ e → mrefl refl
     ; o-resp-≈ = m--resp-≈
     ; associative = λ e → mrefl refl
   }}  where
       msym : {x y : Graph {c₁} {c₂} }  { f g : GMap x y } → f =m= g → g =m= f
       msym {x} {y} f=g f = lemma ( f=g f ) where
            lemma  : ∀{a b c d} {f : edge y a b} {g : edge y c d} → [ y ] f == g → [ y ] g == f
            lemma (mrefl Ff≈Gf) = mrefl  (sym  Ff≈Gf)
       mtrans :  {x y : Graph {c₁} {c₂} }  { f g h : GMap x y } → f =m= g → g =m= h → f =m= h
       mtrans {x} {y} f=g g=h f = lemma ( f=g f ) ( g=h f ) where
           lemma : ∀{a b c d e f} {p : edge y a b} {q : edge y c d} → {r : edge y e f}  → [ y ] p == q → [ y ] q == r → [ y ] p == r
           lemma (mrefl eqv) (mrefl eqv₁) = mrefl ( trans eqv  eqv₁ )
       ise : {x y : Graph {c₁} {c₂} }  → IsEquivalence {_} {c₁ ⊔ c₂} {_} ( _=m=_ {_} {_} {_} {_} {x} {y})
       ise  = record {
          refl =  λ f → mrefl refl
        ; sym = msym
        ; trans = mtrans
          }
       m--resp-≈ :  {A B C : Graph {c₁} {c₂} }
           {f g : GMap A B} {h i : GMap B C} → f =m= g → h =m= i → ( h & f ) =m= ( i & g )
       m--resp-≈  {A} {B} {C} {f} {g} {h} {i0} f=g h=i e =
          lemma (emap f e) (emap g e) (emap i0 (emap g e)) (f=g e) (h=i ( emap g e )) where
            lemma : {a b c d : vertex B } {z w : vertex C } (ϕ : edge B a b) (ψ : edge B c d) (π : edge C z w) →
                [ B ] ϕ  == ψ → [ C ] (emap h ψ) == π → [ C ] (emap h ϕ) == π
            lemma _ _ _ (mrefl refl) (mrefl refl) = mrefl refl

--- Forgetful functor

module forgetful {c₁ : Level} where

  ≃-cong : {c₁ ℓ : Level}  (B : Category c₁ c₁ ℓ ) → {a b a' b' : Obj B }
      → { f f'   : Hom B a b }
      → { g g' : Hom B a' b' }
      → [_]_~_ B f g → B [ f ≈ f' ] → B [ g ≈ g' ] → [_]_~_ B f' g'
  ≃-cong B {a} {b} {a'} {b'} {f} {f'} {g} {g'}  (refl {g2} eqv) f=f' g=g' = let open ≈-Reasoning B in refl {_} {_} {_} {B} {a'} {b'} {f'} {g'} ( begin
             f'
          ≈↑⟨ f=f' ⟩
             f
          ≈⟨ eqv  ⟩
             g
          ≈⟨ g=g' ⟩
             g'
          ∎  )

  ≃→a=a : {c₁ ℓ : Level}  (B : Category c₁ c₁ ℓ ) → {a b a' b' : Obj B }
      → ( f : Hom B a b )
      → ( g : Hom B a' b' )
      → [_]_~_ B f g → a ≡ a'
  ≃→a=a B f g (refl eqv) = refl

  ≃→b=b : {c₁ ℓ : Level}  (B : Category c₁ c₁ ℓ ) → {a b a' b' : Obj B }
      → ( f : Hom B a b )
      → ( g : Hom B a' b' )
      → [_]_~_ B f g → b ≡ b'
  ≃→b=b B f g (refl eqv) = refl

  -- Grph does not allow morph on different level graphs
  -- simply assumes c₁ and c₂ has the same

  uobj : Obj (Cart {c₁ } {c₁} {c₁}) → Obj Grph
  uobj a = record { vertex = Obj (cat a) ; edge = Hom (cat a) }
  umap :  {a b : Obj (Cart {c₁ } {c₁} {c₁} ) } → Hom (Cart ) a b → Hom (Grph {c₁} {c₁}) (( uobj a )) (( uobj b ))
  umap {a} {b} f =  record {
           vmap = λ e → FObj (cmap f) e
         ; emap = λ e → FMap (cmap f) e }

  UX :  Functor (Cart  {c₁} {c₁} {c₁}) (Grph {c₁} {c₁})
  FObj UX a = (uobj a)
  FMap UX f =  umap f
  isFunctor UX  = isf where
    isf : IsFunctor Cart Grph (λ z → (uobj z)) umap
    IsFunctor.identity isf {a} {b} {f} = begin
         umap (id1 Cart a)
       ≈⟨⟩
         umap {a} {a} (record { cmap = identityFunctor ; ccf = λ x → x })
       ≈⟨⟩
         record { vmap = λ y → y ; emap = λ f → f }
       ≈⟨⟩
         id1 Grph ((uobj a))
       ∎ where open ≈-Reasoning Grph
    IsFunctor.distr isf {a} {b} {c} {f} {g} = begin
         umap ( Cart [ g o f ] )  -- FMap (cmap g) (FMap (cmap f) x)   = FMap (cmap g) (FMap (cmap f) x)
       ≈⟨ (λ x → mrefl refl ) ⟩
         Grph [ umap g o umap f ]
       ∎ where open ≈-Reasoning Grph  --  FMap (cmap f) e emap (umap f) e =  emap (umap g) e  <-  Cart [ f ≈ g ]
    IsFunctor.≈-cong isf {a} {b} {f} {g} f=g e with
           f=g e
         | ≃→a=a (cat b) (FMap (cmap f) e) (FMap (cmap g) e) (f=g e)
         | ≃→b=b (cat b) (FMap (cmap f) e) (FMap (cmap g) e) (f=g e)
    ... | eq | eqa | eqb =  cc11 (FMap (cmap f) e) (FMap (cmap g) e) eq eqa eqb where
           cc11 : {a c a' c' : Obj (cat b) } → ( f : Hom (cat b) a c ) → ( g : Hom (cat b) a' c' )
               → [ cat b ] f ~ g → a ≡ a'  → c  ≡ c'  →  [ uobj b ] f == g
           cc11 f g (refl eqv) eq eq1 =  mrefl (≡←≈ b eqv)

--
--  UC :  Functor (CAT  {c₁} {c₁} {c₁}) (Grph {c₁} {c₁})
--  FObj UC a = record { vertex = Obj a ; edge = Hom a }
--  FMap UC {a} {b} f =   record { vmap = λ e → FObj f e ; emap = λ e → FMap f e }
--  isFunctor UC  = isf where
--    isf : IsFunctor CAT Grph (λ z → {!!}) {!!}
--    IsFunctor.identity isf {a} {b} {f} = {!!}
--    IsFunctor.distr isf {a} {b} {c} {f} {g} = {!!}
--    IsFunctor.≈-cong isf {a} {b} {f} {g} f=g e = {!!}
--
-- at-graph-univ :  {c₁ : Level} → UniversalMapping (Grph {c₁} {c₁}) (CAT {c₁ } {c₁} {c₁}) forgetful.UC
-- at-graph-univ {c₁}  = record {
--     F = F ;
--     η = {!!} ;
--     _* = {!!} ;
--     isUniversalMapping = record {
--         universalMapping = {!!} ;
--         uniquness = {!!}
--      }
--  }  where
--      F :  Obj (Grph {c₁} {c₁}) → Obj CAT
--      F g =  PL where open ccc-from-graph g
--
open ccc-from-graph.Objs
-- open ccc-from-graph.Arrow
-- open ccc-from-graph.Arrows
open graphtocat.Chain

Sets0 : {c₂ : Level } → Category (suc c₂) c₂ c₂
Sets0 {c₂} = Sets {c₂}

module fcat {c₁ c₂ : Level}  ( g : Graph {c₁} {c₂} ) where

  open ccc-from-graph g

-- FCat : Obj (Cart {c₁} {c₁ ⊔ c₂} {c₁ ⊔ c₂})
-- FCat  = record { cat = record {
--         Obj = Obj PL
--         ; Hom = λ a b → Hom PL a b
--         ; _o_ = Category._o_ PL
--         ; _≈_ = λ {a} {b} f g → FMap CS f ≡ FMap CS g
--         ; Id  = λ {a} → id1 PL a
--         ; isCategory = record {
--                   isEquivalence = {!!} ;
--                   identityL  = λ {a b f} → {!!} ;
--                   identityR  = λ {a b f} → {!!} ;
--                   o-resp-≈  = λ {a b c f g h i} → {!!} ;
--                   associative  = λ {a} {b} {c} {f} {g} {h} → {!!}
--            }
--         } ;
--        ≡←≈  = λ eq → {!!} ;
--        ccc = {!!}
--     } where
--         B = Sets {c₁ ⊔ c₂}

  -- Hom FCat is an image of Fucntor CS, but I don't know how to write it
-- postulate
--     fcat-pl : {a b : Obj (cat FCat) } → Hom (cat FCat) a b → Hom PL a b
--     fcat-eq :  {a b : Obj (cat FCat) } → (f : Hom (cat FCat) a b ) → {!!} -- FMap CS (fcat-pl f) ≡ f

--   ccc-graph-univ :  {c₁ : Level} → UniversalMapping (Grph {c₁} {c₁}) (Cart {c₁ } {c₁} {c₁}) forgetful.UX
--   ccc-graph-univ {c₁}  = record {
--    F = F ;
--    η = η ;
--    _* = solution ;
--    isUniversalMapping = record {
--        universalMapping = {!!} ;
--        uniquness = {!!}
--     }
-- } where
--      open forgetful
--      open ccc-from-graph
       --
       --
       --                                        η : Hom Grph a (FObj UX (F a))
       --                    f : edge g x y   ----------------------------------->  (record {vertex = fobj (atom x) ; edge = fmap h }) : Graph
       --  Graph g     x  ----------------------> y : vertex g                             ↑
       --                       arrow f             : Hom (PL g) (atom x) (atom y)         |
       --  PL g     atom x  ------------------> atom y : Obj (PL g)                        | UX : Functor Sets Graph
       --                          |                                                       |
       --                          | Functor (CS g)                                        |
       --                          ↓                                                       |
       --  Sets  ((z : vertx g) → C z x)  ----> ((z : vertx g) → C z y)  = h : Hom Sets (fobj (atom x)) (fobj (atom y))
       --
--      F : Obj (Grph {c₁} {c₁}) → Obj (Cart {c₁} {c₁} {c₁})
--      F g = FCat  where open fcat g
--      η : (a : Obj (Grph {c₁} {c₁}) ) → Hom Grph a (FObj UX (F a))
--      η a = record { vmap = λ y → vm y ;  emap = λ f → em f }  where
--           fo : Graph  {c₁ } {c₁}
--           fo = uobj {c₁} (F a)
--           vm : (y : vertex a ) →  vertex (FObj UX (F a))
--           vm y =  atom y
--           em :  { x y : vertex a } (f : edge a x y ) → edge (FObj UX (F a)) (vm x) (vm y)
--           em {x} {y} f = iv (arrow f) (id _)  -- fmap a (iv (arrow f) (id _))
--      cobj  :  {g : Obj (Grph {c₁} {c₁} ) } {c : Obj Cart} → Hom Grph g (FObj UX c)  → Objs g → Obj (cat c)
--      cobj {g} {c} f (atom x) = vmap f x
--      cobj {g} {c} f ⊤ = CCC.１ (ccc c)
--      cobj {g} {c} f (x ∧ y) = CCC._∧_ (ccc c) (cobj {g} {c} f x) (cobj {g} {c} f y)
--      cobj {g} {c} f (b <= a) = CCC._<=_ (ccc c) (cobj {g} {c} f b) (cobj {g} {c} f a)
--      c-map :  {g : Obj (Grph  )} {c : Obj Cart} {A B : Objs g}
--          → (f : Hom Grph g (FObj UX c) ) → (fobj g A → fobj g B) → Hom (cat c) (cobj {g} {c} f A) (cobj {g} {c} f B)
--      c-map = ?
--      c-map {g} {c} {atom x} {atom b} f y = {!!}  where
--           cmpa1 : ((y₁ : vertex g) → C g y₁ x ) → {!!}
--           cmpa1 = {!!}
--      c-map {g} {c} {⊤} {atom b} f y with y ! b
--      ... | id .b = {!!}
--      ... | next x t = (cat c) [ emap f x o c-map f {!!} ]
--      c-map {g} {c} {a ∧ a₁} {atom b} f y = {!!}
--      c-map {g} {c} {a <= a₁} {atom b} f y = {!!}
--      c-map {g} {c} {a} {⊤} f x = CCC.○ (ccc c) (cobj f a)
--      c-map {g} {c} {a} {x ∧ y} f z = CCC.<_,_> (ccc c) (c-map f (λ k → proj₁ (z k))) (c-map f (λ k → proj₂ (z k)))
--      c-map {g} {c} {d} {b <= a} f x = CCC._* (ccc c) ( c-map f (λ k → x (proj₁ k)  (proj₂ k)))
--      solution : {g : Obj Grph } {c : Obj Cart } → Hom Grph g (FObj UX c) → Hom Cart (F g) c
--      solution  {g} {c} f = record { cmap = record {
--            FObj = λ x →  cobj {g} {c} f x ;
--            FMap = λ {x} {y} h → c-map {g} {c} {x} {y} f {!!} ;
--            isFunctor = {!!} } ;
--            ccf = {!!} }
