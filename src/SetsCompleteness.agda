{-# OPTIONS --cubical-compatible --safe #-}

open import Category -- https://github.com/konn/category-agda
open import Level
open import Category.Sets 

module SetsCompleteness where

open import Definitions
open import Relation.Binary.Core
open import Function
import Relation.Binary.PropositionalEquality

open import Relation.Binary.PropositionalEquality hiding ( [_] )

lemma1 :  { c₂ : Level  } {a b  : Obj (Sets { c₂})} {f g : Hom Sets a b} →
   Sets [ f ≈ g ] → (x : a ) → f x  ≡ g x
lemma1 eq  x  = eq x

record Σ {a} (A : Set a) (B : Set a) : Set a where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open Σ public


SetsProduct :  {  c₂ : Level} → ( a b : Obj (Sets  {c₂})) → Product ( Sets  {  c₂} ) a b
SetsProduct { c₂ } a b = record {
         product =  Σ a b
       ; π1 = λ ab → (proj₁ ab)
       ; π2 = λ ab → (proj₂ ab)
       ; isProduct = record {
              _×_  = λ f g  x →   record { proj₁ = f  x ;  proj₂ =  g  x }     -- ( f x ,  g x )
              ; π1fxg=f = λ {c} {f} {g} x → refl
              ; π2fxg=g  = λ {c} {f} {g} x → refl
              ; uniqueness = λ {c} {h} x →  refl
              ; ×-cong   =  λ {c} {f} {f'} {g} {g'} f=f g=g →  prod-cong a b f=f g=g
          }
      } where
          prod-cong : ( a b : Obj (Sets {c₂}) ) {c : Obj (Sets {c₂}) } {f f' : Hom Sets c a } {g g' : Hom Sets c b }
              → Sets [ f ≈ f' ] → Sets [ g ≈ g' ]
              → Sets [ (λ x → f x , g x) ≈ (λ x → f' x , g' x) ]
          prod-cong a b {c} {f} {f1} {g} {g1} eq eq1 x = cong₂ (λ j k → j , k) (eq x) (eq1 x)


record iproduct {a} (I : Set a)  ( pi0 : I → Set a ) : Set a where
    field
       pi1 : ( i : I ) → pi0 i

open iproduct

open import Axiom.Extensionality.Propositional

SetsIProduct :  {  c₂ : Level} → (I : Obj Sets) (ai : I → Obj Sets )
     → Extensionality c₂ c₂     -- cannot avoid this here
     → IProduct I ( Sets  {  c₂} ) ai
SetsIProduct {c₂} I fi ext = record {
       iprod = iproduct I fi
       ; pi  = λ i prod  → pi1 prod i
       ; isIProduct = record {
              iproduct = iproduct1
            ; pif=q = λ {q} {qi} {i} → pif=q {q} {qi} {i}
            ; ip-uniqueness = ip-uniqueness
            ; ip-cong  = ip-cong
       }
   } where
       iproduct1 : {q : Obj Sets} → ((i : I) → Hom Sets q (fi i)) → Hom Sets q (iproduct I fi)
       iproduct1 {q} qi x = record { pi1 = λ i → (qi i) x  }
       pif=q : {q : Obj Sets} {qi : (i : I) → Hom Sets q (fi i)} → {i : I} → Sets [ Sets [ (λ prod → pi1 prod i) o iproduct1 qi ] ≈ qi i ]
       pif=q {q} {qi} {i} x = refl
       ip-uniqueness : {q : Obj Sets} {h : Hom Sets q (iproduct I fi)} → Sets [ iproduct1 (λ i → Sets [ (λ prod → pi1 prod i) o h ]) ≈ h ]
       ip-uniqueness {q} {h} x = refl
       ipcx : {q :  Obj Sets} {qi qi' : (i : I) → Hom Sets q (fi i)} → ((i : I) → Sets [ qi i ≈ qi' i ]) → (x : q) → iproduct1 qi x ≡ iproduct1 qi' x
       ipcx {q} {qi} {qi'} qi=qi x  =
              begin
                record { pi1 = λ i → (qi i) x  }
             ≡⟨ cong (λ k → record { pi1 = k} ) (ext (λ i → qi=qi i x) ) ⟩
                record { pi1 = λ i → (qi' i) x  }
             ∎  where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning
       ip-cong  : {q : Obj Sets} {qi qi' : (i : I) → Hom Sets q (fi i)} → ((i : I) → Sets [ qi i ≈ qi' i ]) → Sets [ iproduct1 qi ≈ iproduct1  qi' ]
       ip-cong {q} {qi} {qi'} qi=qi  = ipcx qi=qi 

data coproduct {c} (a b : Set c) :  Set c where
       k1 : ( i : a ) → coproduct a b 
       k2 : ( i : b ) → coproduct a b 

SetsCoProduct :  {  c₂ : Level} → (a b : Obj (Sets  {c₂})) → coProduct Sets a b 
SetsCoProduct a b = record {
         coproduct = coproduct a b
       ; κ1 = λ i → k1 i
       ; κ2 = λ i → k2 i
       ; isProduct = record {
          _+_ = sum
        ; κ1f+g=f = λ {c} {f} {g} x → fk1 {c} {f} {g} x
        ; κ2f+g=g = λ {c} {f} {g} x → fk2 {c} {f} {g} x
        ; uniqueness = λ {c} {h} x → uniq {c} {h} x
        ; +-cong = pccong
       }
     } where
        sum : {c : Obj Sets} → Hom Sets a c → Hom Sets b c → Hom Sets (coproduct a b ) c
        sum {c} f g (k1 i) = f i
        sum {c} f g (k2 i) = g i
        uniq :  {c : Obj Sets} {h : Hom Sets (coproduct a b) c} → (x : coproduct a b ) → sum (Sets [ h o (λ i → k1 i) ]) (Sets [ h o (λ i → k2 i) ]) x ≡ h x
        uniq {c} {h} (k1 i) = refl
        uniq {c} {h} (k2 i) = refl
        pccong :  {c : Obj Sets} {f f' : Hom Sets a c} {g g' : Hom Sets b c} → Sets [ f ≈ f' ] → Sets [ g ≈ g' ] → Sets [ sum f g ≈ sum f' g' ]
        pccong {c} {f} {f'} {g} {g'} eq eq1 (k1 i) = eq i
        pccong {c} {f} {f'} {g} {g'} eq eq1 (k2 i) = eq1 i
        fk1 :  {c : Obj Sets} {f : Hom Sets a c} {g : Hom Sets b c} → Sets [ Sets [ sum f g o (λ i → k1 i) ] ≈ f ]
        fk1 {c} {f} {g} x = refl
        fk2 : {c : Obj Sets} {f : Hom Sets a c} {g : Hom Sets b c} → Sets [ Sets [ sum f g o (λ i → k2 i) ] ≈ g ]
        fk2 {c} {f} {g} x = refl


data icoproduct {a} (I : Set a) (ki : I → Set a) :  Set a where
       ki1 : (i : I)   (x : ki i ) → icoproduct I ki

SetsICoProduct :  {  c₂ : Level} → (I : Obj (Sets {c₂})) (ci : I → Obj Sets )
     → ICoProduct I ( Sets  {  c₂} ) ci
SetsICoProduct I fi = record {
       icoprod = icoproduct I fi
       ; ki  = λ i x → ki1 i x
       ; isICoProduct = record {
              icoproduct = isum 
            ; kif=q = λ {q} {qi} {i} → kif=q {q} {qi} {i}
            ; icp-uniqueness = uniq
            ; icp-cong  = iccong
       }
   } where
        isum : {q : Obj Sets} → ((i : I) → Hom Sets (fi i) q) → Hom Sets (icoproduct I fi) q
        isum {q} fi (ki1 i x) = fi i x
        kif=q : {q : Obj Sets} {qi : (i : I) → Hom Sets (fi i) q} {i : I} → Sets [ Sets [ isum qi o (λ x → ki1 i x) ] ≈ qi i ]
        kif=q {q} {qi} {i} x =  refl 
        uniq : {q : Obj Sets} {h : Hom Sets (icoproduct I fi) q} → Sets [ isum (λ i → Sets [ h o (λ x → ki1 i x) ]) ≈ h ]
        uniq {q} {h} = u1 where 
           u1 : (x : icoproduct I fi ) → isum (λ i → Sets [ h o (λ x₁ → ki1 i x₁) ]) x ≡ h x
           u1 (ki1 i x) = refl
        iccong : {q : Obj Sets} {qi qi' : (i : I) → Hom Sets (fi i) q} → ((i : I) → Sets [ qi i ≈ qi' i ]) → Sets [ isum qi ≈ isum qi' ]
        iccong {q} {qi} {qi'} ieq = u2 where 
           u2 : (x : icoproduct I fi ) → isum qi x ≡ isum qi' x
           u2 (ki1 i x) = ieq i x

        --
        --         e             f
        --    c  -------→ a ---------→ b        f ( f'
        --    ^        .     ---------→
        --    |      .            g
        --    |k   .
        --    |  . h
        --y : d

        -- cf. https://github.com/danr/Agda-projects/blob/master/Category-Theory/Equalizer.agda

data sequ {c : Level} (A B : Set c) ( f g : A → B ) :  Set c where
    elem : (x : A ) → (eq : f x ≡ g x) → sequ A B f g

equ  :  {  c₂ : Level}  {a b : Obj (Sets {c₂}) } { f g : Hom (Sets {c₂}) a b } → ( sequ a b  f g ) →  a
equ  (elem x eq)  = x

fe=ge0  :  {  c₂ : Level}  {a b : Obj (Sets {c₂}) } { f g : Hom (Sets {c₂}) a b } →
     (x : sequ a b f g) → (Sets [ f o (λ e → equ e) ]) x ≡ (Sets [ g o (λ e → equ e) ]) x
fe=ge0 (elem x eq )  =  eq

-- we need -with-K to prove this
--- ≡-irr : { c₂ : Level}  {d : Set c₂ }  { x y : d } ( eq eq' :  x  ≡ y ) → eq ≡ eq'

equ-inject : {  c₂ : Level}  {a b : Set c₂}  
     (≡-irr : { c₂ : Level}  {d : Set c₂ }  { x y : d } ( eq eq' :  x  ≡ y ) → eq ≡ eq')
    {f g : Hom (Sets {c₂}) a b}  (x y : sequ a b f g) → equ x ≡ equ y →  x  ≡ y
equ-inject ≡-irr ( elem x eq  ) (elem .x eq' ) refl   =  cong (λ k → elem x k ) (≡-irr eq eq' )

open sequ

--           equalizer-c = sequ a b f g
--          ; equalizer = λ e → equ e

open import  Relation.Binary.PropositionalEquality

SetsIsEqualizer :  {  c₂ : Level}  
    (≡-irr : { c₂ : Level}  {d : Set c₂ }  { x y : d } ( eq eq' :  x  ≡ y ) → eq ≡ eq')
    →  (a b : Obj (Sets {c₂}) )  (f g : Hom (Sets {c₂}) a b) → IsEqualizer Sets (λ e → equ e) f g
SetsIsEqualizer {c₂} ≡-irr a b f g = record {
               fe=ge  = fe=ge
             ; k = k
             ; ek=h = λ {d} {h} {eq} → ek=h {d} {h} {eq}
             ; uniqueness  = uniqueness
       } where
           fe=ge  :  Sets [ Sets [ f o (λ e → equ e ) ] ≈ Sets [ g o (λ e → equ e ) ] ]
           fe=ge (elem x eq) = eq
           k :  {d : Obj Sets} (h : Hom Sets d a) → Sets [ Sets [ f o h ] ≈ Sets [ g o h ] ] → Hom Sets d (sequ a b f g)
           k {d} h eq x = elem  (h x) (eq x)
           ek=h : {d : Obj Sets} {h : Hom Sets d a} {eq : Sets [ Sets [ f o h ] ≈ Sets [ g o h ] ]} → Sets [ Sets [ (λ e → equ e )  o k h eq ] ≈ h ]
           ek=h {d} {h} {eq} x = refl
           injection :  { c₂ : Level  } {a b  : Obj (Sets { c₂})} (f  : Hom Sets a b) → Set c₂
           injection f =  ∀ x y  → f x ≡ f y →  x  ≡ y
           uniqueness :   {d : Obj Sets} {h : Hom Sets d a} {fh=gh : Sets [ Sets [ f o h ] ≈ Sets [ g o h ] ]} {k' : Hom Sets d (sequ a b f g)} →
                Sets [ Sets [ (λ e → equ e) o k' ] ≈ h ] → Sets [ k h fh=gh  ≈ k' ]
           uniqueness  {d} {h} {fh=gh} {k'} ek'=h x = equ-inject ≡-irr _ _ ( begin
               equ ( k h fh=gh x)  ≡⟨⟩
               h x ≡⟨ sym ( ek'=h x)  ⟩
               equ (k' x)  ∎ ) where open ≡-Reasoning

-- -- we have to make this Level c, that is {B : Set c} → (A → B) is iso to I : Set c
-- record cequ {c : Level} (A B : Set c)  :  Set (suc c) where
--   field
--     rev : {B : Set c} → (A → B) → B → A
--     surjective : {B : Set c } (x : B ) → (g : A → B)  → g (rev g x) ≡ x

-- -- λ f₁ x y → (λ x₁ → x (f₁ x₁)) ≡ (λ x₁ → y (f₁ x₁)) → x ≡ y
-- -- λ x y → (λ x₁ → x x₁ ≡ y x₁) → x ≡ y
-- -- Y / R

-- open import HomReasoning

-- SetsIsCoEqualizer :  {  c₂ : Level}  →  (a b : Obj (Sets {c₂}) )  (f g : Hom (Sets {c₂}) a b)
--   → IsCoEqualizer Sets (λ x → {!!}    ) f g
-- SetsIsCoEqualizer {c₂} a b f g = record {
--               ef=eg  = extensionality Sets (λ x → {!!} )
--             ; k = {!!} 
--             ; ke=h = λ {d} {h} {eq} → ke=h {d} {h} {eq}
--             ; uniqueness  = {!!}
--       } where
--          c : Set  c₂
--          c = {!!} --cequ a b   
--          d : cequ a b   
--          d = {!!}
--          ef=eg :  Sets [ Sets [ cequ.rev d f o f ] ≈ Sets [ cequ.rev d g o g ] ]
--          ef=eg = begin
--              Sets [ cequ.rev d f o f ]  ≈↑⟨ idL ⟩
--              Sets [ id1 Sets _ o Sets [ cequ.rev d f o f ]  ] ≈↑⟨ assoc ⟩
--              Sets [ Sets [ id1 Sets _ o  cequ.rev d f ] o f ] ≈⟨ {!!}  ⟩
--              Sets [ Sets [ id1 Sets _ o  cequ.rev d (id1 Sets _) ] o {!!} ] ≈⟨ car ( extensionality Sets (λ x →  cequ.surjective d {!!} {!!} ))  ⟩
--              Sets [ {!!} o f ] ≈⟨ {!!}  ⟩
--              Sets [ id1 Sets _ o Sets [ cequ.rev d g o g ]  ] ≈⟨ idL ⟩
--              Sets [ cequ.rev d g o g ]  ∎  where open ≈-Reasoning Sets
--          epi :  { c₂ : Level  } {a b c : Obj (Sets { c₂})} (e : Hom Sets b c ) → (f g : Hom Sets a b) → Set c₂
--          epi e f g = Sets [ Sets [ e o f ] ≈ Sets [ e o g ] ] → Sets [ f ≈ g ]
--          k : {d : Obj Sets} (h : Hom Sets b d) → Sets [ Sets [ h o f ] ≈ Sets [ h o g ] ] → Hom Sets c d
--          k {d} h hf=hg = {!!} where
--             ca : Sets [ Sets [ h o f ] ≈ Sets [ h o g ] ] → a  -- (λ x → h (f x)) ≡ (λ x → h (g x))
--             ca eq = {!!}
--             cd : ( {y : a} → f y ≡ g y → sequ a b f g ) → d
--             cd = {!!}
--          ke=h : {d : Obj Sets } {h : Hom Sets b d } → { eq : Sets [ Sets [ h o f ] ≈ Sets [ h o g ] ] }
--           →   Sets [ Sets [ k h eq o {!!} ] ≈ h ]
--          ke=h {d} {h} {eq} =  extensionality Sets  ( λ  x → begin
--             k h eq ( {!!}) ≡⟨ {!!} ⟩
--             h (f {!!})  ≡⟨ {!!}  ⟩
--             h (g {!!})  ≡⟨ {!!}  ⟩
--             h x
--             ∎ )  where
--                  open  import  Relation.Binary.PropositionalEquality
--                  open ≡-Reasoning


