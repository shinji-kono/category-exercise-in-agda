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

   data CArrows : (a b : Objs) → Set  (c₁ ⊔ c₂) where
       ca-id : (a b : Objs) → a ≡ b → CArrows a b
       ca-term : (a b : Objs) → b ≡ top →  CArrows a b
       ca-par : (a b c d : Objs) →  d ≡ (a ∧ b) → CArrows c a → CArrows c b → CArrows c d
       ca-comp : (b c d : Objs) → (f : Arrow d c) → (g : CArrows b d ) → CArrows b c

   C←A : {a b  : Objs}  → Arrows a b → CArrows a b
   C←A {a} {.a} (id .a) = ca-id a _ refl
   C←A {a} {.top} (○ .a) = ca-term a _ refl
   C←A {a} {.(_ ∧ _)} < f , f₁ > = ca-par _ _ _ _ refl (C←A f ) (C←A f₁ )
   C←A {a} {b} (iv f f₁) = ca-comp _ _ _ f (C←A f₁)

   A←C : {a b  : Objs}  → CArrows a b → Arrows a b
   A←C {a} {.a} (ca-id .a _ refl) = id a
   A←C {a} {.top} (ca-term .a _ refl) = ○ a
   A←C (ca-par _ _  _ _ refl f  f₁ ) = < A←C f , A←C f₁ >
   A←C {a} {b} (ca-comp _ _ _ f f₁) = iv f (A←C f₁)

   iso-AC : {a b : Objs} → (f : Arrows a b) → A←C (C←A f) ≡ f
   iso-AC {a} {.a} (id .a) = refl
   iso-AC {a} {.top} (○ .a) = refl
   iso-AC {a} {.(_ ∧ _)} < f , f₁ > = cong₂ (λ j k → < j , k > ) (iso-AC f) (iso-AC f₁)
   iso-AC {a} {b} (iv f f₁) = cong (λ k → iv f k ) (iso-AC f₁)

   iso-CA : {a b : Objs} → (f : CArrows a b) → C←A (A←C f) ≡ f
   iso-CA {a} {b} (ca-id .a .b refl) = refl
   iso-CA {a} {b} (ca-term .a .b refl) = refl
   iso-CA {a} {b} (ca-par a₁ b₁ .a .b refl f f₁) = cong₂ (λ j k → ca-par _ _ _ _ refl j k ) (iso-CA f) (iso-CA f₁)
   iso-CA {a} {b} (ca-comp .a .b d f f₁) = cong (λ k → ca-comp _ _ _ f k) (iso-CA f₁)

   -- no injection here, because of ¬ ( id top ≡ ○ top )
   -- ≐-inject : {a b : Objs} → (f g : Hom PL a b) → (f ≐ g) → (f ≡ g)

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

   record PLCI : Set (c₁  ⊔ c₂) where
      field 
        a b : Objs
        parrow : Arrows a b

   -- PLC-Small : Small (c₁  ⊔ c₂)  PLC we cannot prove these
   PLC-Small = record {
         I = PLCI
       ; hom→ = λ {i} {j} f → record { a = i ; b = j ; parrow = f } 
       ; s-dom = λ p → PLCI.a p
       ; s-cod  = λ p → PLCI.b p
       ; s-dom-iso  = refl
       ; s-cod-iso  = refl
       ; hom← = λ f →  PLCI.parrow f 
       ; hom-iso = λ _ → refl
       ; hom-rev = refl
       ; hom-inject  = lem
       ; subst-eq = ?
       ; ≡←≈ = ?
     } where
         lem : {i j k l : Obj PLC} {f : Hom PLC i j} {g : Hom PLC k l} → record { a = i ; b = j ; parrow = f } ≡
            record { a = k ; b = l ; parrow = g } → i ≡ k /\ j ≡ l
         lem eq =  (cong PLCI.a eq) , (cong PLCI.b eq) 
         -- we can prove this using with-K
         lem2 : {a b c d : Obj PLC} (a=b a=b' : a ≡ b) (c=d c=d' : c ≡ d) {f : Hom PLC a c} →
            PLC [ subst₂ (Hom PLC) a=b c=d f ≈ subst₂ (Hom PLC) a=b' c=d' f ]
         lem2 {a} {b} {c} {d} a=b a=b' c=d c=d' {f} oa = ?
         lem3 : {i j : Obj PLC} {f g : Hom PLC i j} → PLC [ f ≈ g ] → f ≡ g   -- we cannot say this
         lem3 = ?


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

record CCCObj {c₁ c₂ ℓ : Level}  : Set  (suc (ℓ ⊔ (c₂ ⊔ c₁))) where
   field
     cat : Category c₁ c₂ ℓ
     small : Small c₁ cat
     -- ≡←≈ : {a b : Obj cat } → { f g : Hom cat a b } → cat [ f ≈ g ] → f ≡ g   -- we assume smallness of Category
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
             f' ≈↑⟨ f=f' ⟩
             f ≈⟨ eqv  ⟩
             g ≈⟨ g=g' ⟩ g' ∎  )

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
         umap (id1 Cart a) ≈⟨⟩
         umap {a} {a} (record { cmap = identityFunctor ; ccf = λ x → x }) ≈⟨⟩
         record { vmap = λ y → y ; emap = λ f → f } ≈⟨⟩
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
           cc11 f g (refl eqv) eq eq1 =  mrefl (Small.≡←≈ (small b) eqv)

-- open ccc-from-graph.Objs
open graphtocat.Chain

module fcat {c₁ c₂ : Level} (ext : Axiom.Extensionality.Propositional.Extensionality c₁ c₁ )
  (≡←≈ : (g : Obj (Grph {c₁} {c₁})) →  {a b : Obj (ccc-from-graph.PLC g ext)}
            {f : Hom (ccc-from-graph.PLC g ext) a b}
            {g₁ : Hom (ccc-from-graph.PLC g ext) a b} →
            ccc-from-graph.PLC g ext [ f ≈ g₁ ] → f ≡ g₁ ) where

  -- open g ext

  ccc-graph-univ : UniversalMapping (Grph {c₁} {c₁}) (Cart {c₁ } {c₁} {c₁}) forgetful.UX
  ccc-graph-univ  = record {
   F = F ;
   η = η ;
   _* = solution ;
   isUniversalMapping = record {
       universalMapping = λ {a} {b} {f} → is-solution {a} {b} {f};
       uniquness = λ {a} {b} {f} {g} → is-unique {a} {b} {f} {g}
     }
   }  where
    F : Obj (Grph {c₁} {c₁}) → Obj (Cart {c₁} {c₁} {c₁})
    F g = record { cat = ccc-from-graph.PLC g ext ; small =  ? ; ccc = ccc-from-graph.ccc-PL g ext }
    η : (a : Obj (Grph {c₁} {c₁}) ) → Hom Grph a (forgetful.uobj (F a))
    η a = record { vmap = λ v → atom v ;  emap = λ {b} {c} e → iv (arrow e) (id (atom b)) }   where
        open ccc-from-graph a ext
    solution : {g : Obj Grph} {b : Obj Cart} → Hom Grph g (forgetful.uobj b) → Hom Cart (F g) b
    solution {g} {b} f = record { cmap = record {
           FObj = fobj1
         ; FMap = λ f → fmap1 f
         ; isFunctor = record {
                identity = λ {a} → refl-hom
               ; ≈-cong = λ {a} {b} {f} {h} → sl01 {a} {b} {f} {h}
               ; distr = λ {a} {b} {c} {f} {g} → sl02 {a} {b} {c} {f} {g}
            } } ;
        ccf = λ _ → ccc b } where
            open ccc-from-graph g ext hiding ( top  ;  _∧_ ; atom ; _<=_ )
            open ≈-Reasoning (cat b) hiding ( sym )
            open ccc-from-graph.Objs

            fobj1 : Obj PLC → Obj (cat b)
            fobj1 (atom x) = vmap f x
            fobj1 top = CCC.１ (ccc b)
            fobj1 (a ∧ a₁) = CCC._∧_ (ccc b) (fobj1 a) (fobj1 a₁)
            fobj1 (a <= a₁) = CCC._<=_ (ccc b) (fobj1 a) (fobj1 a₁)

            fmap1 :  {A B : Obj PLC} → Hom PLC A B → Hom (cat b) (fobj1 A) (fobj1 B)
            fmap1 {a} {.a} (id .a) = id1 (cat b) (fobj1 a)
            fmap1 {a} {.top} (○ .a) = CCC.○ (ccc b) (fobj1 a)
            fmap1 {a} {.(_ ∧ _)} < m , m₁ > = CCC.<_,_> (ccc b) (fmap1 {a}  m) (fmap1 {a}  m₁)
            fmap1 {a} {_} (iv (arrow x) m) = (cat b) [ emap f x o fmap1 m ]
            fmap1 {a} {_} (iv π m) = (cat b) [ CCC.π (ccc b)  o fmap1 m ]
            fmap1 {a} {_} (iv π' m) = (cat b) [ CCC.π' (ccc b) o fmap1 m ]
            fmap1 {a} {_} (iv ε m) = (cat b) [ CCC.ε (ccc b) o fmap1 m ]
            fmap1 {a} {_} (iv (x *) m) = (cat b) [ CCC._* (ccc b) (fmap1 x) o fmap1 m ]


            sl00 : {A : Obj PLC} → cat b [ id1 (cat b) (fobj1 A) ≈ id1 (cat b) (fobj1 A) ]
            sl00 {a} = refl-hom
            sl01 :  {A B : Obj PLC} {f : Hom PLC A B} {h : Hom PLC A B} →
                PLC [ f ≈ h ] → cat b [ fmap1 f ≈ fmap1 h ]
            sl01 {a} {b} {f} {h} f=h = ?
            sl02 : {a : Obj PLC} {b₂ : Obj PLC} {c : Obj PLC} {f : Hom PLC a b₂} {g : Hom PLC b₂ c} →
                cat b [ fmap1 (PLC [ g o f ]) ≈ cat b [ fmap1 g o fmap1 f ] ]
            sl02 {a} {b₂} {.b₂} {f} {ccc-from-graph.id .b₂} = ?
            sl02 {a} {b₂} {.top} {f} {ccc-from-graph.○ .b₂} = ?
            sl02 {a} {b₂} {.(_ ∧ _)} {f} {ccc-from-graph.< g , g₁ >} = ?
            sl02 {a} {b₂} {c} {f} {ccc-from-graph.iv f₁ g} = ?


    is-solution :   {a : Obj Grph} {b : Obj Cart} {f : Hom Grph a (forgetful.uobj b)} → Grph [ Grph [ forgetful.umap (solution {a}{b} f) o η a ] ≈ f ]
    is-solution {a} {b1} {record { vmap = vmap ; emap = emap }} e = mrefl ? where
       lem :  GMap.emap (Grph [ forgetful.umap (solution {a} {b1} (record { vmap = vmap ; emap = emap })) o η a ]) e ≡ emap e
       lem = begin
          cat b1 [ emap e o id1 (cat b1) (vmap _ ) ]  ≡⟨ ? ⟩
          emap e ∎ where
             open ≡-Reasoning


    is-unique : {a : Obj Grph} {b : Obj Cart} {f : Hom Grph a (forgetful.uobj b)}
            {g : Hom Cart (F a) b} →
            Grph [ Grph [ forgetful.umap g o η a ] ≈ f ] →
            Cart [ solution f ≈ g ]
    is-unique {a} {b1} {f} {g} eq e = ?

