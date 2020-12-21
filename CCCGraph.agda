module CCCgraph where

open import Level
open import Category 
open import HomReasoning
open import cat-utility
open import Data.Product renaming (_×_ to _/\_  ) hiding ( <_,_> )
open import Category.Constructions.Product
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import CCC

open Functor

--   ccc-1 : Hom A a 1 ≅ {*}
--   ccc-2 : Hom A c (a × b) ≅ (Hom A c a ) × ( Hom A c b )
--   ccc-3 : Hom A a (c ^ b) ≅ Hom A (a × b) c

open import Category.Sets

-- Sets is a CCC

import Axiom.Extensionality.Propositional
postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Axiom.Extensionality.Propositional.Extensionality  c₂ c₂

data One  {c : Level } : Set c where
  OneObj : One   -- () in Haskell ( or any one object set )

sets : {c : Level } → CCC (Sets {c})
sets  = record {
         １  = One
       ; ○ = λ _ → λ _ → OneObj
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
         ○ a = λ _ → OneObj
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
             ; *-cong = *-cong
           } where
                e2 : {a : Obj Sets} {f : Hom Sets a １} → Sets [ f ≈ ○ a ]
                e2 {a} {f} = extensionality Sets ( λ x → e20 x )
                  where
                        e20 : (x : a ) → f x ≡ ○ a x
                        e20 x with f x
                        e20 x | OneObj = refl
                e3a : {a b c : Obj Sets} {f : Hom Sets c a} {g : Hom Sets c b} →
                    Sets [ ( Sets [  π  o ( <,> f g)  ] ) ≈ f ]
                e3a = refl
                e3b : {a b c : Obj Sets} {f : Hom Sets c a} {g : Hom Sets c b} →
                    Sets [ Sets [ π' o ( <,> f g ) ] ≈ g ]
                e3b = refl
                e3c : {a b c : Obj Sets} {h : Hom Sets c (a ∧ b)} →
                    Sets [ <,> (Sets [ π o h ]) (Sets [ π' o h ]) ≈ h ]
                e3c = refl
                π-cong : {a b c : Obj Sets} {f f' : Hom Sets c a} {g g' : Hom Sets c b} →
                    Sets [ f ≈ f' ] → Sets [ g ≈ g' ] → Sets [ <,> f g ≈ <,> f' g' ]
                π-cong refl refl = refl
                e4a : {a b c : Obj Sets} {h : Hom Sets (c ∧ b) a} →
                    Sets [ Sets [ ε o <,> (Sets [ h * o π ]) π' ] ≈ h ]
                e4a = refl
                e4b : {a b c : Obj Sets} {k : Hom Sets c (a <= b)} →
                    Sets [ (Sets [ ε o <,> (Sets [ k o π ]) π' ]) * ≈ k ]
                e4b = refl
                *-cong : {a b c : Obj Sets} {f f' : Hom Sets (a ∧ b) c} →
                    Sets [ f ≈ f' ] → Sets [ f * ≈ f' * ]
                *-cong refl = refl




open import graph
module ccc-from-graph {c₁ c₂ : Level }  (G : Graph {c₁} {c₂})  where

   open import Relation.Binary.PropositionalEquality renaming ( cong to ≡-cong ) hiding ( [_] )
   open Graph

   data Objs : Set (suc c₁) where
      atom : (vertex G) → Objs 
      ⊤ : Objs 
      _∧_ : Objs  → Objs  → Objs 
      _<=_ : Objs → Objs → Objs 

   data  Arrows  : (b c : Objs ) → Set (suc c₁  ⊔  c₂)
   data Arrow :  Objs → Objs → Set (suc c₁  ⊔ c₂)  where                       --- case i
      arrow : {a b : vertex G} →  (edge G) a b → Arrow (atom a) (atom b)
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
   PL :  Category  (suc c₁) (suc c₁  ⊔ c₂) (suc c₁  ⊔ c₂)
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

--------
--
-- Functor from Positive Logic to Sets
--

   -- open import Category.Sets
   -- postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Relation.Binary.PropositionalEquality.Extensionalit y c₂ c₂

   open import Data.List

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
   fmap (○ a) x = OneObj
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
        IsFunctor.identity isf = extensionality Sets ( λ x → refl )
        IsFunctor.≈-cong isf refl = refl 
        IsFunctor.distr isf {a} {b} {c} {g} {f} = extensionality Sets ( λ z → distr {a} {b} {c} {g} {f} z ) 

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

open import Relation.Binary.HeterogeneousEquality using (_≅_;refl ) renaming ( sym to ≅-sym ; trans to ≅-trans ; cong to ≅-cong )

data [_]_==_ {c₁ c₂ : Level} (C : Graph  {c₁} {c₂}) {A B : vertex C} (f : edge C A B)
     : ∀{X Y : vertex C} → edge C X Y → Set (c₁ ⊔ c₂ ) where
  mrefl : {g : edge C A B} → (eqv : f ≡ g ) → [ C ] f == g

eq-vertex1 : {c₁ c₂ : Level} (C : Graph  {c₁} {c₂}) {A B : vertex C} {f : edge C A B}
      {X Y : vertex C} → {g : edge C X Y } → ( [ C ] f == g ) → A ≡ X
eq-vertex1 _ (mrefl refl) = refl

eq-vertex2 : {c₁ c₂ : Level} (C : Graph  {c₁} {c₂}) {A B : vertex C} {f : edge C A B}
      {X Y : vertex C} → {g : edge C X Y } → ( [ C ] f == g ) → B ≡ Y
eq-vertex2 _ (mrefl refl) = refl

eq-edge : {c₁ c₂ : Level} (C : Graph  {c₁} {c₂}) {A B : vertex C} {f : edge C A B}
      {X Y : vertex C} → {g : edge C X Y } → ( [ C ] f == g ) → f ≅ g
eq-edge C eq with eq-vertex1 C eq | eq-vertex2 C eq
eq-edge C (mrefl refl) | refl | refl = refl

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
       m--resp-≈  {A} {B} {C} {f} {g} {h} {i} f=g h=i e =
          lemma (emap f e) (emap g e) (emap i (emap g e)) (f=g e) (h=i ( emap g e )) where
            lemma : {a b c d : vertex B } {z w : vertex C } (ϕ : edge B a b) (ψ : edge B c d) (π : edge C z w) →
                [ B ] ϕ  == ψ → [ C ] (emap h ψ) == π → [ C ] (emap h ϕ) == π
            lemma _ _ _ (mrefl refl) (mrefl refl) = mrefl refl

--- Forgetful functor

module forgetful {c₁ c₂ : Level} where

  ≃-cong : {c₁ c₂ ℓ : Level}  (B : Category c₁ c₂ ℓ ) → {a b a' b' : Obj B }
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

  -- Grph does not allow morph on different level graphs
  -- simply assumes we have iso to the another level. This may means same axiom on CCCs results the same CCCs.
  postulate
     g21 : Graph {suc c₁} {c₁ ⊔ c₂} → Graph {c₁} {c₂} 
     m21 : (g : Graph {suc c₁ } {c₁ ⊔ c₂} )  → GMap  {suc c₁ } {c₁ ⊔ c₂} {c₁} {c₂} g (g21 g)
     m12 : (g : Graph {suc c₁ } {c₁ ⊔ c₂} )  → GMap  {c₁} {c₂}  {suc c₁ } {c₁ ⊔ c₂} (g21 g) g
     giso→  : { g : Graph {suc c₁ } {c₁ ⊔ c₂} }
          → {a b : vertex g } →  (m12 g & m21 g) =m= id1 Grph g
     giso←  : { g : Graph {suc c₁ } {c₁ ⊔ c₂} }
          → {a b : vertex (g21 g) } →  (m21 g & m12 g ) =m= id1 Grph (g21 g)
                -- Grph [ Grph [ m21 g o m12 g ] ≈ id1 Grph (g21 g) ]
  
  uobj : Obj (Cart {suc c₁ } {c₁ ⊔ c₂} {c₁ ⊔ c₂}) → Obj Grph
  uobj a = record { vertex = Obj (cat a) ; edge = Hom (cat a) }
  umap :  {a b : Obj (Cart {suc c₁ } {c₁ ⊔ c₂} {c₁ ⊔ c₂} ) } → Hom (Cart ) a b → Hom (Grph {c₁} {c₂}) (g21 ( uobj a )) (g21 ( uobj b ))
  umap {a} {b} f =  record {
           vmap = λ e → vmap (m21 (uobj b)) (FObj (cmap f) (vmap (m12 (uobj a)) e ))
         ; emap = λ e → emap (m21 (uobj b)) (FMap (cmap f) (emap (m12 (uobj a)) e )) } 

  UX :  Functor (Cart  {suc c₁} {c₁ ⊔ c₂} {c₁ ⊔ c₂}) (Grph {c₁} {c₂})
  FObj UX a = g21 (uobj a)
  FMap UX f =  umap f
  isFunctor UX  = isf where
    isf : IsFunctor Cart Grph (λ z → g21 (uobj z)) umap
    IsFunctor.identity isf {a} {b} {f} = begin
         umap (id1 Cart a) 
       ≈⟨⟩
         umap {a} {a} (record { cmap = identityFunctor ; ccf = λ x → x })
       ≈⟨⟩
         record { vmap = λ e → vmap (m21 (uobj a)) (vmap (m12 (uobj a)) e ) ; emap = λ e → emap (m21 (uobj a)) (emap (m12 (uobj a)) e )}
       ≈⟨ giso← {uobj a} {f} {f}  ⟩
         record { vmap = λ y → y ; emap = λ f → f }
       ≈⟨⟩
         id1 Grph (g21 (uobj a))
       ∎ where open ≈-Reasoning Grph 
    IsFunctor.distr isf {a} {b} {c} {f} {g} = begin
         umap ( Cart [ g o f ] )
       ≈⟨⟩
         ( m21 (uobj c) & ( record { vmap = λ e → FObj (cmap (( Cart [ g o f ] ))) e ; emap = λ e → FMap (cmap (( Cart [ g o f ] ))) e} &  m12 (uobj a) ) )
       ≈⟨ {!!} ⟩
--         ( m21 (uobj c) &  (record { vmap = λ e → FObj (cmap g) (FObj (cmap f) e)  ; emap = λ e → FMap (cmap g) (FMap (cmap f) e) }
--            &  m12 (uobj a)))
--       ≈⟨ cdr (cdr (car (giso← {uobj b} )))  ⟩
--         ( m21 (uobj c) &  (record { vmap = λ e → FObj (cmap g) e ; emap = λ e → FMap (cmap g) e}
--            &  ((m12 (uobj b) 
--            &  (m21 (uobj b))) &  (record { vmap = λ e → FObj (cmap f) e ; emap = λ e → FMap (cmap f) e}
--            &  (m12 (uobj a) )))))
--       ≈⟨⟩
         Grph [ umap g o umap f ]
       ∎ where open ≈-Reasoning Grph 
    IsFunctor.≈-cong isf {a} {b} {f} {g} f=g e = {!!} where -- lemma ( (extensionality Sets ( λ z → lemma4 (
          --       ≃-cong (cat b) (f=g (id1 (cat a) z)) (IsFunctor.identity (Functor.isFunctor (cmap f))) (IsFunctor.identity (Functor.isFunctor (cmap g)))
          --  )))) (f=g e) where
      lemma4 : {x y : vertex (uobj b)} →  [_]_~_ (cat b)  (id1 (cat b) x) (id1 (cat b) y) → x ≡ y
      lemma4 (refl eqv) = refl 
      -- lemma : vmap (umap f) ≡ vmap (umap g) → [ cat b ] FMap (cmap f) e ~ FMap (cmap g) e → [ g21 (uobj b)] emap (umap f) {!!} == emap (umap g) {!!}
      -- lemma = {!!} -- refl (refl eqv) = mrefl (≡←≈ b eqv)


open ccc-from-graph.Objs
open ccc-from-graph.Arrow
open ccc-from-graph.Arrows
open graphtocat.Chain

Sets0 : {c₂ : Level } → Category (suc c₂) c₂ c₂
Sets0 {c₂} = Sets {c₂}

module fcat {c₁ c₂ : Level}  ( g : Graph {c₁} {c₂} ) where

  open ccc-from-graph g

  FCat : Obj (Cart {suc c₁} {c₁ ⊔ c₂} {c₁ ⊔ c₂})
  FCat  = record { cat = record {
          Obj = Obj PL 
          ; Hom = λ a b → Hom B (FObj CS a) (FObj CS b)
          ; _o_ = Category._o_ B
          ; _≈_ = Category._≈_ B
          ; Id  = λ {a} → id1 B (FObj CS a)
          ; isCategory = record {
                    isEquivalence =  IsCategory.isEquivalence (Category.isCategory B) ;
                    identityL  = λ {a b f} → IsCategory.identityL (Category.isCategory B) ;
                    identityR  = λ {a b f} → IsCategory.identityR (Category.isCategory B) ;
                    o-resp-≈  = λ {a b c f g h i} → IsCategory.o-resp-≈ (Category.isCategory B);
                    associative  = {!!} -- IsCategory.associative (Category.isCategory B) 
             }
          } ;
         ≡←≈  = λ eq → eq ;
         ccc = {!!}
      } where
          B = Sets {c₁ ⊔ c₂}

  -- Hom FCat is an image of Fucntor CS, but I don't know how to write it
  postulate
      fcat-pl : {a b : Obj (cat FCat) } → Hom (cat FCat) a b → Hom PL a b
      fcat-eq :  {a b : Obj (cat FCat) } → (f : Hom (cat FCat) a b ) → FMap CS (fcat-pl f) ≡ f


ccc-graph-univ :  {c₁ c₂ : Level} → UniversalMapping (Grph {c₁} {c₂}) (Cart {suc c₁ } {c₁ ⊔ c₂} {c₁ ⊔ c₂}) forgetful.UX 
ccc-graph-univ {c₁} {c₂} = record {
     F = F ;
     η = η ; 
     _* = solution ;
     isUniversalMapping = record {
         universalMapping = {!!} ;
         uniquness = {!!}
      }
  } where
       open forgetful  
       open ccc-from-graph
       -- 
       -- 
       --                                        η : Hom Grph a (FObj UX (F a))
       --                    f : edge g x y   ----------------------------------->  m21 (record {vertex = fobj (atom x) ; edge = fmap h }) : Graph
       --  Graph g     x  ----------------------> y : vertex g                             ↑
       --                       arrow f             : Hom (PL g) (atom x) (atom y)         |
       --  PL g     atom x  ------------------> atom y : Obj (PL g)                        | UX : Functor Sets Graph
       --                          |                                                       | 
       --                          | Functor (CS g)                                        | 
       --                          ↓                                                       |
       --  Sets  ((z : vertx g) → C z x)  ----> ((z : vertx g) → C z y)  = h : Hom Sets (fobj (atom x)) (fobj (atom y))
       --
       F : Obj (Grph {c₁} {c₂}) → Obj (Cart {suc c₁} {c₁ ⊔ c₂} {c₁ ⊔ c₂})
       F g = FCat  where open fcat g 
       η : (a : Obj (Grph {c₁} {c₂}) ) → Hom Grph a (FObj UX (F a))
       η a = record { vmap = λ y → vm y ;  emap = λ f → em f }  where
            fo : Graph  {suc c₁ } {c₁ ⊔ c₂}
            fo = uobj {c₁} {c₂} (F a)
            vm : (y : vertex a ) →  vertex (g21 fo) 
            vm y =  vmap (m21 fo) (atom y) 
            em :  { x y : vertex a } (f : edge a x y ) → edge (FObj UX (F a)) (vm x) (vm y)
            em {x} {y} f = emap (m21 fo) (fmap a (iv (arrow f) (id _)))
       pl : {c₁ c₂ : Level}  → (g : Graph {c₁} {c₂} ) → Category _ _ _
       pl g = PL g
       cobj  :  {g : Obj (Grph {c₁} {c₂} ) } {c : Obj Cart} → Hom Grph g (FObj UX c)  → Objs g → Obj (cat c)
       cobj {g} {c} f (atom x) = vmap (m12 (uobj {c₁} {c₂} c)) (vmap f x)
       cobj {g} {c} f ⊤ = CCC.１ (ccc c)
       cobj {g} {c} f (x ∧ y) = CCC._∧_ (ccc c) (cobj {g} {c} f x) (cobj {g} {c} f y)
       cobj {g} {c} f (b <= a) = CCC._<=_ (ccc c) (cobj {g} {c} f b) (cobj {g} {c} f a) 
       c-map :  {g : Obj (Grph  )} {c : Obj Cart} {A B : Objs g} 
           → (f : Hom Grph g (FObj UX c) ) → (fobj g A → fobj g B) → Hom (cat c) (cobj {g} {c} f A) (cobj {g} {c} f B)
       c-map {g} {c} {a} {atom b} f y with fcat.fcat-pl {c₁} {c₂} g {a} {atom b} y
       c-map {g} {c} {atom b} {atom b} f y | id (atom b) = id1 (cat c) _
       c-map {g} {c} {a} {atom b} f y | iv {_} {_} {d} (arrow x) t = {!!} 
          -- (cat c) [ emap (m12 (uobj {c₁} {c₂} c)) ( emap f x)  o c-map {g} {c} {a} {d} f (fmap g t) ]
       c-map {g} {c} {a} {atom b} f y | iv {_} {_} {d} π t = {!!} --(cat c) [ CCC.π (ccc c) o c-map {g} {c} {a} {d} f (fmap g t)]
       c-map {g} {c} {a} {atom b} f y | iv {_} {_} {d} π' t = {!!} -- (cat c) [ CCC.π' (ccc c) o c-map {g} {c} {a} {d} f (fmap g t) ]
       c-map {g} {c} {a} {atom b} f y | iv {_} {_} {d} ε t = {!!} -- (cat c) [ CCC.ε (ccc c) o c-map {g} {c} {a} {d} f (fmap g t) ]
       -- with emap (m12 (uobj {c₁} {c₂} c)) ( emap f {!!} )
       c-map {g} {c} {a} {⊤} f x = CCC.○ (ccc c) (cobj f a)
       c-map {g} {c} {a} {x ∧ y} f z = CCC.<_,_> (ccc c) (c-map f (λ k → proj₁ (z k))) (c-map f (λ k → proj₂ (z k)))
       c-map {g} {c} {d} {b <= a} f x = CCC._* (ccc c) ( c-map f (λ k → x (proj₁ k)  (proj₂ k)))
       solution : {g : Obj Grph } {c : Obj Cart } → Hom Grph g (FObj UX c) → Hom Cart (F g) c
       solution  {g} {c} f = record { cmap = record {
             FObj = λ x →  cobj {g} {c} f x ;
             FMap = λ {x} {y} h → c-map {g} {c} {x} {y} f h ;
             isFunctor = {!!} } ;
             ccf = {!!} } 
