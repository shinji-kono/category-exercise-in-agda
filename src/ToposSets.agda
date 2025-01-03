-- {-# OPTIONS --with-K --cubical-compatible --allow-unsolved-metas #-}
{-# OPTIONS  --warning=noUnsupportedIndexedMatch --allow-unsolved-metas #-}
module ToposSets where

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

open import SetsCompleteness hiding (ki1)

-- import Axiom.Extensionality.Propositional
-- postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Axiom.Extensionality.Propositional.Extensionality  c₂ c₂


open import Relation.Nullary
open import Data.Empty
open import equalizer
open import CCCSets

data Bool { c : Level } : Set c where
     true : Bool
     false : Bool

¬f≡t  : { c : Level } → ¬ (false {c} ≡ true )
¬f≡t ()

¬x≡t∧x≡f  : { c : Level } → {x : Bool {c}} → ¬ ((x ≡ false) /\ (x ≡ true) )
¬x≡t∧x≡f {_} {true} p = ⊥-elim (¬f≡t (sym (proj₁ p)))
¬x≡t∧x≡f {_} {false} p = ⊥-elim (¬f≡t (proj₂ p))
     
data _∨_ {c c' : Level } (a : Set c) (b : Set c') : Set (c ⊔ c') where
    case1 : a → a ∨ b
    case2 : b → a ∨ b

---------------------------------------------
--
-- a binary Topos of Sets
--
-- m : b → a determins a subset of a as an image
-- b and m-image in a has one to one correspondence with an equalizer (x : b) → (y : a) ≡ m x.
--   so tchar m mono and ker (tchar m mono) is Iso.
--   Finding (x : b) from (y : a) is non constructive. Assuming LEM of image.
--
data image {c : Level} {a b : Set c} (m : Hom Sets b a) : a → Set c where
   isImage : (x : b ) → image m (m x) 

topos : {c : Level } → ({ c : Level} →  (b : Set c) → b ∨ (¬ b)) → Topos (Sets {c}) ccc-sets
topos {c} lem = record {
         Ω =  Bool
      ;  ⊤ = λ _ → true
      ;  Ker = tker
      ;  char = λ m mono → tchar m mono
      ;  isTopos = record {
                 char-uniqueness  = λ {a} {b} {h} →  ? -- extensionality Sets ( λ x → uniq h x )
              ;  char-iso  = iso-m
              ;  ker-m = ker-iso 
         }
    } where
--
-- In Sets, equalizers exist as
-- data sequ {c : Level} (A B : Set c) ( f g : A → B ) :  Set c where
--     elem : (x : A ) → (eq : f x ≡ g x) → sequ A B f g
-- m have to be isomorphic to ker (char m).
--
--                  b→s         ○ b
--   ker (char m)  ----→ b -----------→ 1
--       |         ←---- |              |
--       |          b←s  |m             | ⊤   char m : a → Ω = {true,false}
--       |   e           ↓    char m    ↓     if y : a ≡ m (∃ x : b) → true  ( data char )
--       +-------------→ a -----------→ Ω     else         false
--                             h
--
        tker   : {a : Obj Sets} (h : Hom Sets a Bool) → Equalizer Sets h (Sets [ (λ _ → true ) o CCC.○ sets a ])
        tker {a} h = record {
                equalizer-c =  sequ a Bool h (λ _ → true )
              ; equalizer = λ e → equ e
              ; isEqualizer = SetsIsEqualizer _ _ _ _ ? }
        tchar : {a b : Obj Sets} (m : Hom Sets b a) → (mono : Mono Sets m ) → a → Bool {c}
        tchar {a} {b} m mono y with lem (image m y )
        ... | case1 t = true
        ... | case2 f = false
        -- imequ   : {a b : Obj Sets} (m : Hom Sets b a) (mono : Mono Sets m) → IsEqualizer Sets m (tchar m mono) (Sets [ (λ _ → true ) o CCC.○ sets a ])
        -- imequ {a} {b} m mono = equalizerIso _ _ (tker (tchar m mono)) m (isol m mono)
        uniq : {a : Obj (Sets {c})}  (h : Hom Sets a Bool)   (y : a) →
               tchar (Equalizer.equalizer (tker h)) (record { isMono = λ f g → monic (tker h) }) y ≡ h y
        uniq = ?
--        uniq {a}  h y with h y  | inspect h y | lem (image (Equalizer.equalizer (tker h)) y ) | inspect (tchar (Equalizer.equalizer (tker h)) (record { isMono = λ f g → monic (tker h) })) y
--        ... | true  | record { eq = eqhy } | case1 x | record { eq = eq1 } = eq1 
--        ... | true  | record { eq = eqhy } | case2 x | record { eq = eq1 } = ⊥-elim (x (isImage (elem y eqhy)))
--        ... | false | record { eq = eqhy } | case1 (isImage (elem x eq)) | record { eq = eq1 } = ⊥-elim ( ¬x≡t∧x≡f record {fst = eqhy ; snd = eq })
--        ... | false | record { eq = eqhy } | case2 x | record { eq = eq1 } = eq1
           
        -- technical detail of equalizer-image isomorphism (isol) below
        open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
        img-cong : {a b : Obj (Sets {c}) } (m : Hom Sets b a) → (mono : Mono Sets m ) → (y y' : a) → y ≡ y' → (s : image m y ) (t : image m y') → s ≅ t
        img-cong {a} {b} m mono .(m x) .(m x₁) eq (isImage x) (isImage x₁) = ?
         --   with cong (λ k → k ! ) ? -- ( Mono.isMono mono {One} (λ _ → x) (λ _ → x₁ ) ? ) -- ( extensionality Sets ( λ _ → eq )) )
        -- ... | refl = HE.refl
        image-uniq : {a b : Obj (Sets {c})} (m : Hom Sets b a) → (mono : Mono Sets m )  (y : a) → (i0 i1 : image m y ) → i0 ≡ i1
        image-uniq {a} {b} m mono y i0 i1 = HE.≅-to-≡ (img-cong m mono y y refl i0 i1)
        tchar¬Img : {a b : Obj Sets} (m : Hom Sets b a) → (mono : Mono Sets m )  (y : a) → tchar m mono y ≡ false → ¬ image m y
        tchar¬Img  m mono y eq im with lem (image m y) 
        ... | case2 n  = n im
        b2i : {a b : Obj (Sets {c}) } (m : Hom Sets b a) → (x : b) → image m (m x)
        b2i m x = isImage x
        i2b : {a b : Obj (Sets {c}) } (m : Hom Sets b a) →  {y : a} → image m y → b
        i2b m (isImage x) = x
        img-mx=y :  {a b : Obj (Sets {c}) } (m : Hom Sets b a) →  {y : a} → (im : image m y ) → m (i2b m im) ≡ y
        img-mx=y m (isImage x) = refl
        b2i-iso : {a b : Obj (Sets {c}) } (m : Hom Sets b a) →  (x : b) → i2b m (b2i m x) ≡ x
        b2i-iso m x = refl
        b2s : {a b : Obj (Sets {c}) } (m : Hom Sets b a) → (mono : Mono Sets m ) → (x : b) →  sequ a Bool (tchar m mono)  (λ _ → true )
        b2s m mono x with tchar m mono (m x) | inspect (tchar m mono) (m x)
        ... | true | record {eq = eq1} = elem (m x) eq1
        ... | false | record { eq = eq1 } with tchar¬Img m mono (m x) eq1
        ... | t = ⊥-elim (t (isImage x)) 
        s2i  : {a b : Obj (Sets {c}) } (m : Hom Sets b a) → (mono : Mono Sets m ) → (e : sequ a Bool (tchar m mono)  (λ _ → true )) → image m (equ e)
        s2i {a} {b} m mono (elem y eq) with lem (image m y)
        ... | case1 im = im
        ker-iso :  {a b : Obj Sets} (m : Hom Sets b a) (mono : Mono Sets m) → IsEqualizer Sets m (tchar m mono) (Sets [ (λ _ → true) o CCC.○ sets a ])
        ker-iso {a} {b} m mono = equalizerIso _ _ (tker (tchar m mono)) m  isol ? where -- (extensionality Sets ( λ x → iso4 x)) where
          b→s : Hom Sets b (sequ a Bool (tchar m mono) (λ _ → true))
          b→s x = b2s m mono x
          b←s : Hom Sets (sequ a Bool (tchar m mono) (λ _ → true)) b
          b←s (elem y eq) = i2b m (s2i m mono (elem y eq))
          iso3 : (s : sequ a Bool (tchar m mono) (λ _ → true)) → m (b←s s) ≡ equ s
          iso3 (elem y eq) with lem (image m y)
          ... | case1 (isImage x) = refl
          iso1 : (x : b) → b←s ( b→s x ) ≡  x
          iso1 x with  tchar m mono (m x) | inspect (tchar m mono ) (m x)
          ... | true | record { eq = eq1 }  = begin
             b←s ( elem (m x) eq1 )  ≡⟨⟩
             i2b m (s2i m mono (elem (m x ) eq1 ))  ≡⟨ cong (λ k → i2b m k) (image-uniq m mono (m x) (s2i m mono (elem (m x ) eq1 )) (isImage x) ) ⟩
             i2b m (isImage x)  ≡⟨⟩
             x ∎ where open ≡-Reasoning
          iso1 x | false | record { eq = eq1 } = ⊥-elim ( tchar¬Img m mono (m x) eq1 (isImage x))
          iso4 : (x : b ) →  (Sets [ Equalizer.equalizer (tker (tchar m mono)) o b→s ]) x ≡ m x
          iso4 x = begin 
             equ (b2s m mono x) ≡⟨ sym (iso3 (b2s m mono x)) ⟩
             m (b←s (b2s m mono x)) ≡⟨ cong (λ k → m k ) (iso1 x) ⟩
             m x ∎ where open ≡-Reasoning
          iso2 : (x : sequ a Bool (tchar m mono) (λ _ → true) ) →  (Sets [ b→s o b←s ]) x ≡ id1 Sets (sequ a Bool (tchar m mono) (λ _ → true)) x
          iso2 (elem y eq) = begin
             b→s ( b←s (elem y eq)) ≡⟨⟩
             b2s m mono ( i2b m (s2i m mono (elem y eq)))  ≡⟨⟩
             b2s m mono x  ≡⟨ equ-inject ? _ _ (iso21 x ) ⟩
             elem (m x) eq1 ≡⟨ equ-inject ?  _ _ mx=y ⟩
             elem y eq  ∎ where
               open ≡-Reasoning
               x : b
               x = i2b m (s2i m mono (elem y eq))
               eq1 : tchar m mono (m x) ≡ true
               eq1 with lem (image m (m x))
               ... | case1 t = refl
               ... | case2 n = ⊥-elim (n (isImage x))
               mx=y : m x ≡ y
               mx=y = img-mx=y m (s2i m mono (elem y eq))
               iso21 : (x : b)  → equ (b2s m mono x ) ≡ m x
               iso21 x with  tchar m mono (m x) | inspect (tchar m mono) (m x)
               ... | true | record {eq = eq1} = refl
               ... | false | record { eq = eq1 } with tchar¬Img m mono (m x) eq1
               ... | t = ⊥-elim (t (isImage x)) 
          isol :  Iso Sets b (Equalizer.equalizer-c (tker (tchar m mono)))
          isol = record { ≅→ = b→s ; ≅← = b←s ;
                iso→  =  ? -- extensionality Sets ( λ x → iso1 x )
              ; iso←  =  ? } -- extensionality Sets ( λ x → iso2 x) } 

        iso-m :  {a a' b : Obj Sets} (p : Hom Sets a b) (q : Hom Sets a' b) (mp : Mono Sets p) (mq : Mono Sets q) →
            (i : Iso Sets a a' ) → Sets [ p ≈ Sets [ q o Iso.≅→ i ] ] → Sets [ tchar p mp ≈ tchar q mq ]
        iso-m {a} {a'} {b} p q mp mq i ei = ? -- extensionality Sets (λ y → iso-m1 y ) where
          where
           --
           --          Iso.≅← i     x      ○ a            mq : q ( f x ) ≡ q ( g x ) → f x ≡ g x 
           --       a'------------→ a -----------→ 1
           --       | ⟵------------ |              |
           --      q|  Iso.≅→ i     |p             | ⊤   char m : a → Ω = {true,false}
           --       |               ↓    char m    ↓     if y : a ≡ m (∃ x : b) → true  ( data char )
           --       +-------------→ b -----------→ Ω     else         false
           --    q ( Iso.≅→ i x ) ≡ y ≡  p x
           --
           iso-m1 : (y : b) → tchar p mp y ≡ tchar q mq y
           iso-m1 y with lem (image p y) | lem (image q y) 
           ... | case1 (isImage x) |  case1 x₁  = refl
           ... | case1 (isImage x) |  case2 not = ⊥-elim ( not iso-m2 ) where
               iso-m4 :  q ( Iso.≅→ i x ) ≡ p x
               iso-m4 = begin
                  q ( Iso.≅→ i x )  ≡⟨ sym ( cong ( λ k → k x) ei ) ⟩
                  p x ∎ where open ≡-Reasoning
               iso-m2 : image q (p x)   
               iso-m2 = subst (λ k → image q k) iso-m4 ( isImage ( Iso.≅→ i x ) ) 
           ... | case2 not |  case1 (isImage x) = ⊥-elim ( not ( subst (λ k → image p k) iso-m3 ( isImage ( Iso.≅← i x ) ) )) where
               iso-m3 :  p (Iso.≅← i x) ≡ q x
               iso-m3 = begin
                  p (Iso.≅← i x)  ≡⟨  cong ( λ k → k (Iso.≅← i x) ) ei ⟩
                  q (Iso.≅→ i (Iso.≅← i x))  ≡⟨ cong (λ k → q k) (cong (λ k1 → k1 x) (Iso.iso← i)) ⟩
                  q x ∎ where open ≡-Reasoning
           ... | case2 x |  case2 not = refl

--       open import Polynominal (Sets {c} )  (sets {c})
--       A = Sets {c}
--       Ω = Bool
--       １ = One
--       ⊤ = λ _ → true
--       ○ = λ _ → λ _ → !
--       _⊢_  : {a b : Obj A}  (p : Poly a  Ω b ) (q : Poly a  Ω b ) → Set (suc c )
--       _⊢_  {a} {b} p q = {c : Obj A} (h : Hom A c b ) → A [ A [ Poly.f p o  h ]  ≈ A [  ⊤ o ○  c  ] ]
--              → A [   Poly.f q ∙ h  ≈  A [ ⊤ o  ○  c  ]  ]
--       tl01 : {a b : Obj A}  (p : Poly a  Ω b ) (q : Poly a  Ω b )
--            → p ⊢ q → q ⊢ p →  A [ Poly.f p ≈ Poly.f q ]
--       tl01 {a} {b} p q p<q q<p = ? where  -- extensionality Sets t1011 where
--           open ≡-Reasoning
--           t1011 : (s : b ) → Poly.f p s ≡ Poly.f q s 
--           t1011 x with Poly.f p x | inspect ( Poly.f p) x
--           ... | true | record { eq = eq1 } = sym tt1 where
--                tt1 : Poly.f q _ ≡ true 
--                tt1 = cong (λ k → k !) (p<q _ ? ) -- ( extensionality Sets (λ x → eq1) ))
--           ... | false |  record { eq = eq1 } with Poly.f q x | inspect (Poly.f q) x
--           ... | true | record { eq = eq2 } = ⊥-elim ( ¬x≡t∧x≡f record { fst  = eq1 ; snd = tt1 } ) where
--                tt1 : Poly.f p _ ≡ true 
--                tt1 = cong (λ k → k !) (q<p _ ? ) -- ( extensionality Sets (λ x → eq2) ))
--           ... | false | eq2 = refl


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
        IsFunctor.identity isf = ? -- extensionality Sets ( λ x → refl )
        IsFunctor.≈-cong isf refl = refl 
        IsFunctor.distr isf {a} {b} {c} {g} {f} = ? -- extensionality Sets ( λ z → distr {a} {b} {c} {g} {f} z ) 


