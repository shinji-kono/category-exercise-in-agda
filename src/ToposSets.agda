{-# OPTIONS --safe --cubical-compatible  #-}
module ToposSets where

open import Level
open import Category 
open import HomReasoning
open import Definitions
open import Data.Product renaming (_×_ to _/\_  ) hiding ( <_,_> )
open import Category.Constructions.Product
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import CCC
open import CCCSets

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

topos : {c : Level } → ({ c : Level} →  (b : Set c) → b ∨ (¬ b)) 
   → (≡-irr : { c₂ : Level}  {d : Set c₂ }  { x y : d } ( eq eq' :  x  ≡ y ) → eq ≡ eq')
   → Topos (Sets {c}) ccc-sets
topos {c} lem ≡-irr = record {
         Ω =  Bool
      ;  ⊤ = λ _ → true
      ;  Ker = tker
      ;  char = λ m mono → tchar m mono
      ;  isTopos = record {
                 char-uniqueness  = λ {a} {b} {h} x →  uniq h x 
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
        tker   : {a : Obj Sets} (h : Hom Sets a Bool) → Equalizer Sets h (Sets [ (λ _ → true ) o CCC.○ ccc-sets a ])
        tker {a} h = record {
                equalizer-c =  sequ a Bool h (λ _ → true )
              ; equalizer = λ e → equ e
              ; isEqualizer = SetsIsEqualizer ≡-irr _ _ _ (λ _ → true ) }
        tchar : {a b : Obj Sets} (m : Hom Sets b a) → (mono : Mono Sets m ) → a → Bool {c}
        tchar {a} {b} m mono y with lem (image m y )
        ... | case1 t = true
        ... | case2 f = false
        uniq : {a : Obj (Sets {c})}  (h : Hom Sets a Bool)   (y : a) →
               tchar (Equalizer.equalizer (tker h)) (record { isMono = λ f g → monic (tker h) }) y ≡ h y
        uniq {a}  h y with h y  in eqhy | lem (image (Equalizer.equalizer (tker h)) y ) | (tchar (Equalizer.equalizer (tker h)) (record { isMono = λ f g → monic (tker h) })) y in eq1
        ... | true  | case1 x | _ = sym eq1 
        ... | true  | case2 x | _ = ⊥-elim (x (isImage (elem y eqhy)))
        ... | false | case1 (isImage (elem x eq)) | _ = ⊥-elim ( ¬x≡t∧x≡f record {fst = eqhy ; snd = eq })
        ... | false | case2 x | _ = sym eq1
        -- technical detail of equalizer-image isomorphism (isol) below
        tchar¬Img : {a b : Obj Sets} (m : Hom Sets b a) → (mono : Mono Sets m )  (y : a) → tchar m mono y ≡ false → ¬ image m y
        tchar¬Img  m mono y eq im with lem (image m y) 
        ... | case2 n  = n im
        ... | case1 n  = ⊥-elim (¬f≡t (sym eq) )
        b2i : {a b : Obj (Sets {c}) } (m : Hom Sets b a) → (x : b) → image m (m x)
        b2i m x = isImage x
        i2b : {a b : Obj (Sets {c}) } (m : Hom Sets b a) →  {y : a} → image m y → b
        i2b m (isImage x) = x
        img-mx=y :  {a b : Obj (Sets {c}) } (m : Hom Sets b a) →  {y : a} → (im : image m y ) → m (i2b m im) ≡ y
        img-mx=y m (isImage x) = refl
        b2i-iso : {a b : Obj (Sets {c}) } (m : Hom Sets b a) →  (x : b) → i2b m (b2i m x) ≡ x
        b2i-iso m x = refl
        bs2s1 : {a b : Obj (Sets {c}) } (m : Hom Sets b a) → (mono : Mono Sets m ) → (x : b) →  ( bl : Bool) 
            → bl ≡ tchar m mono (m x) →  sequ a Bool (tchar m mono)  (λ _ → true )
        bs2s1 m mono x true eq1 = elem (m x) (sym eq1)
        bs2s1 m mono x false eq1 = ⊥-elim (tchar¬Img m mono (m x) (sym eq1) (isImage x ))
        b2s : {a b : Obj (Sets {c}) } (m : Hom Sets b a) → (mono : Mono Sets m ) → (x : b) →  sequ a Bool (tchar m mono)  (λ _ → true )
        b2s {a} {b} m mono x = bs2s1 m mono x (tchar m mono (m x)) refl 
        s2i  : {a b : Obj (Sets {c}) } (m : Hom Sets b a) → (mono : Mono Sets m ) → (e : sequ a Bool (tchar m mono)  (λ _ → true )) → image m (equ e)
        s2i {a} {b} m mono (elem y eq) with lem (image m y)
        ... | case1 im = im
        ... | case2 im = ⊥-elim (¬f≡t eq)
        ker-iso :  {a b : Obj Sets} (m : Hom Sets b a) (mono : Mono Sets m) → IsEqualizer Sets m (tchar m mono) (Sets [ (λ _ → true) o CCC.○ ccc-sets a ])
        ker-iso {a} {b} m mono = equalizerIso _ _ (tker (tchar m mono)) m  isol iso4 where 
          b→s : Hom Sets b (sequ a Bool (tchar m mono) (λ _ → true))
          b→s x = b2s m mono x
          b←s : Hom Sets (sequ a Bool (tchar m mono) (λ _ → true)) b
          b←s (elem y eq) = i2b m (s2i m mono (elem y eq))
          iso3 : (s : sequ a Bool (tchar m mono) (λ _ → true)) → m (b←s s) ≡ equ s
          iso3 (elem y eq) with lem (image m y)
          ... | case1 (isImage x) = refl
          iso1 : (x : b) → b←s ( b→s x ) ≡  x
          iso1 x = lem02 _ refl  where
             -- we cannot directory do "with tchar m mono (m x) in eq1" 
             lem02 : ( bl : Bool) → (eq1 : bl ≡ tchar m mono (m x)) →  b←s (bs2s1 m mono x bl eq1) ≡ x
             lem02 true eq1 with lem (image m (m x))
             ... | case1 im = lem03 _ im refl  where
                lem03 : (a1 : a) → (im : image m a1 ) → a1 ≡ m x → i2b m im ≡ x
                lem03 _ (isImage b1) eq2 = Mono.isMono mono (λ x → b1) _ (λ y → eq2 ) b1 
             ... | case2 im = ⊥-elim (¬f≡t (sym eq1) )
             lem02 false eq1 = ⊥-elim ( tchar¬Img m mono (m x) (sym eq1) (isImage x))
          iso4 : (x : b ) →  (Sets [ Equalizer.equalizer (tker (tchar m mono)) o b→s ]) x ≡ m x
          iso4 x = begin 
             equ (b2s m mono x) ≡⟨ sym (iso3 (b2s m mono x)) ⟩
             m (b←s (b2s m mono x)) ≡⟨ cong (λ k → m k ) (iso1 x) ⟩
             m x ∎ where open ≡-Reasoning
          iso2 : (x : sequ a Bool (tchar m mono) (λ _ → true) ) →  (Sets [ b→s o b←s ]) x ≡ id1 Sets (sequ a Bool (tchar m mono) (λ _ → true)) x
          iso2 (elem y eq) = begin
             b→s ( b←s (elem y eq)) ≡⟨⟩
             b2s m mono ( i2b m (s2i m mono (elem y eq)))  ≡⟨⟩
             b2s m mono x  ≡⟨ equ-inject ≡-irr _ _ (iso21 x ) ⟩
             elem (m x) eq1 ≡⟨ equ-inject ≡-irr  _ _ mx=y ⟩
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
               iso21 x = lem02 _ refl where 
                  lem02 : ( bl : Bool ) → (eq1 : bl ≡ tchar m mono (m x) ) →  equ (bs2s1 m mono x _ eq1) ≡ m x
                  lem02 true eq1 = refl 
                  lem02 false eq1 = ⊥-elim ( tchar¬Img m mono (m x) (sym eq1) (isImage x) )
          isol :  Iso Sets b (Equalizer.equalizer-c (tker (tchar m mono)))
          isol = record { ≅→ = b→s ; ≅← = b←s ;
                iso→  =  iso1   
              ; iso←  =  iso2  } 

        iso-m :  {a a' b : Obj Sets} (p : Hom Sets a b) (q : Hom Sets a' b) (mp : Mono Sets p) (mq : Mono Sets q) →
            (i : Iso Sets a a' ) → Sets [ p ≈ Sets [ q o Iso.≅→ i ] ] → Sets [ tchar p mp ≈ tchar q mq ]
        iso-m {a} {a'} {b} p q mp mq i ei = iso-m1 
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
                  q ( Iso.≅→ i x )  ≡⟨ sym (ei x) ⟩
                  p x ∎ where open ≡-Reasoning
               iso-m2 : image q (p x)   
               iso-m2 = subst (λ k → image q k) iso-m4 ( isImage ( Iso.≅→ i x ) ) 
           ... | case2 not |  case1 (isImage x) = ⊥-elim ( not ( subst (λ k → image p k) iso-m3 ( isImage ( Iso.≅← i x ) ) )) where
               iso-m3 :  p (Iso.≅← i x) ≡ q x
               iso-m3 = begin
                  p (Iso.≅← i x)  ≡⟨ ei _ ⟩
                  q (Iso.≅→ i (Iso.≅← i x))  ≡⟨ cong q (Iso.iso← i _) ⟩
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


