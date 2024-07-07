{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --cubical-compatible --safe #-}

-- {-# OPTIONS --cubical-compatible #-}

open import CCC
open import Level
open import Category
open import Definitions
open import HomReasoning
module ToposEx   {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (c : CCC A) (t : Topos A c ) (n : ToposNat A (CCC.１ c)) where

  open Topos
  open Equalizer
  open ≈-Reasoning A
  open CCC.CCC c

--
--             ○ b
--       b -----------→ 1
--       |              |
--     m |              | ⊤
--       ↓    char m    ↓
--       a -----------→ Ω
--             h
--
--   Ker t h : Equalizer A h (A [ ⊤ o (○ a) ])

  mh=⊤ : {a d : Obj A} (h : Hom A a (Ω t))  (p1 : Hom A d a) (p2 : Hom A d １) (eq : A [ A [ h o p1 ] ≈ A [ ⊤ t o p2 ] ] )
        → A [ A [ h o p1 ] ≈ A [ A [ ⊤ t o ○ a ] o p1 ] ]
  mh=⊤ {a} {d} h p1 p2 eq = begin
            h o p1                      ≈⟨ eq ⟩
            ⊤ t o p2                    ≈⟨ cdr (IsCCC.e2 isCCC) ⟩
            ⊤ t o  (○ d)                ≈↑⟨ cdr (IsCCC.e2 isCCC) ⟩
            ⊤ t o ( ○ a o p1 )          ≈⟨ assoc ⟩
           (⊤ t o ○ a ) o p1            ∎ 

  ----
  --
  --  pull back from h
  --
  topos-pullback :  {a : Obj A}  → (h : Hom A a (Ω t)) → Pullback A h (⊤ t)
  topos-pullback {a} h = record {
      ab = equalizer-c (Ker t h)         -- b
    ; π1 = equalizer   (Ker t h)         -- m
    ; π2 = ○ ( equalizer-c (Ker t h) )   -- ○ b
    ; isPullback = record {
              commute = comm
         ;    pullback = λ {d} {p1} {p2} eq → IsEqualizer.k (isEqualizer (Ker t h)) p1 (mh=⊤ h  p1 p2 eq )
         ;    π1p=π1 = IsEqualizer.ek=h (isEqualizer (Ker t h))
         ;    π2p=π2 = λ {d} {p1'} {p2'} {eq} → lemma2 eq
         ;    uniqueness = uniq
      }
    } where
    e2 = IsCCC.e2 isCCC
    comm :  A [ A [ h o equalizer (Ker t h) ] ≈ A [ ⊤ t o ○ (equalizer-c (Ker t h)) ] ]
    comm = begin
            h o equalizer (Ker t h)      ≈⟨ IsEqualizer.fe=ge (isEqualizer (Ker t h)) ⟩
            (⊤ t o ○ a ) o equalizer (Ker t h) ≈↑⟨ assoc ⟩
            ⊤ t o (○ a  o equalizer (Ker t h)) ≈⟨ cdr e2  ⟩
            ⊤ t o ○ (equalizer-c (Ker t h))   ∎
    lemma2 : {d : Obj A}  {p1' : Hom A d a} {p2' : Hom A d １} (eq : A [ A [ h o p1' ] ≈ A [ ⊤ t o p2' ] ] )
        →   A [ A [  ○ (equalizer-c (Ker t h)) o IsEqualizer.k (isEqualizer (Ker t h)) p1'(mh=⊤ h p1' p2' eq) ] ≈ p2' ]
    lemma2 {d} {p1'} {p2'} eq = begin
             ○ (equalizer-c (Ker t h)) o IsEqualizer.k (isEqualizer (Ker t h)) p1'(mh=⊤ h p1' p2' eq)          ≈⟨ e2 ⟩
             ○ d ≈↑⟨ e2 ⟩
             p2' ∎ 
    uniq :  {d : Obj A} (p' : Hom A d (equalizer-c (Ker t h))) (π1' : Hom A d a) (π2' : Hom A d １) (eq : A [ A [ h o π1' ] ≈ A [ ⊤ t o π2' ] ])
            (π1p=π1' : A [ A [ equalizer (Ker t h) o p' ] ≈ π1' ]) (π2p=π2' : A [ A [ ○ (equalizer-c (Ker t h)) o p' ] ≈ π2' ])
             → A [ IsEqualizer.k (isEqualizer (Ker t h)) π1' (mh=⊤ h π1' π2' eq) ≈ p' ]
    uniq {d} (p') p1' p2' eq pe1 pe2 = begin
             IsEqualizer.k (isEqualizer (Ker t h)) p1' (mh=⊤ h p1' p2' eq)  ≈⟨ IsEqualizer.uniqueness  (isEqualizer (Ker t h)) pe1 ⟩
             p' ∎ 

  ----
  --
  --  pull back from m
  --
  topos-m-pullback : {a b : Obj A}  → (m : Hom A b a) → (mono : Mono A m ) → Pullback A (char t m mono )  (⊤ t)
  topos-m-pullback {a} {b} m mono  = record {
      ab = b     
    ; π1 = m    
    ; π2 = ○ b   
    ; isPullback = record {
              commute = IsTopos.char-m=⊤ (Topos.isTopos t) m mono
         ;    pullback = λ {d} {p1} {p2} eq →  k  p1 p2 eq
         ;    π1p=π1 = λ {d} {p1'} {p2'} {eq} → lemma3 p1' p2' eq
         ;    π2p=π2 = λ {d} {p1'} {p2'} {eq} → trans-hom (IsCCC.e2 isCCC) (sym (IsCCC.e2 isCCC))
         ;    uniqueness = uniq
      }
    } where
        k : {d : Obj A} (p1 : Hom A d a) → (p2 : Hom A d １) →  A [ A [ char t m mono o p1 ] ≈ A [ ⊤ t o p2 ] ] → Hom A d b
        k p1 p2 eq = IsEqualizer.k (IsTopos.ker-m (isTopos t) m mono) p1 (mh=⊤ (char t m mono) p1 p2 eq )
        lemma3 : {d : Obj A} (p1 : Hom A d a) → (p2 : Hom A d １)
            →  (eq : A [ A [ char t m mono o p1 ] ≈ A [ ⊤ t o p2 ] ] ) → m o (k p1 p2 eq ) ≈ p1 
        lemma3 {d} p1 p2 eq = begin
           m  o k p1 p2 eq ≈⟨ IsEqualizer.ek=h (IsTopos.ker-m (isTopos t) m mono)  ⟩
           p1 ∎
        uniq : {d : Obj A} (p' : Hom A d b) (π1' : Hom A d a) (π2' : Hom A d １)
            (eq : A [ A [ char t m mono o π1' ] ≈ A [ ⊤ t o π2' ] ]) →
            A [ A [ m o p' ] ≈ π1' ] → A [ A [ ○ b o p' ] ≈ π2' ] → k π1' π2' eq ≈ p' 
        uniq {d} p p1 p2 eq pe1 pe2 = begin
             k p1 p2 eq ≈⟨  IsEqualizer.uniqueness  (IsTopos.ker-m (isTopos t) m mono) pe1 ⟩
             p ∎ 

  δmono : {b : Obj A } → Mono A < id1 A b , id1 A b >
  δmono  = record {
     isMono = m1
   } where
    m1 :   {d b : Obj A} (f g : Hom A d b) → A [ A [  < id1 A b , id1 A b > o f ] ≈ A [  < id1 A b , id1 A b > o g ] ] → A [ f ≈ g ]
    m1 {d} {b} f g eq = begin
            f  ≈↑⟨ idL ⟩
            id1 A _ o f ≈↑⟨ car (IsCCC.e3a isCCC) ⟩
            (π o < id1 A b , id1 A b >)  o f  ≈↑⟨ assoc ⟩
            π o (< id1 A b , id1 A b >  o f)  ≈⟨ cdr eq ⟩
            π o (< id1 A b , id1 A b >  o g)  ≈⟨ assoc ⟩
            (π o < id1 A b , id1 A b >)  o g  ≈⟨  car (IsCCC.e3a isCCC) ⟩
            id1 A _ o g  ≈⟨ idL ⟩
            g ∎

--
--
--   Hom equality and Ω    (p.94 cl(Δ a) in Takeuchi )
--
--
--       a -----------→ +
--     f||g     ○ a     |
--      ↓↓              |
--       b -----------→ 1
--       |      ○ b     |
-- <1,1> |              | ⊤
--       ↓              ↓
--     b ∧ b ---------→ Ω
--          char <1,1>

  prop32→ :  {a b : Obj A}→ (f g : Hom A a b )
    → A [ f ≈ g ] → A [ A [ char t < id1 A b , id1 A b > δmono  o < f , g > ]  ≈ A [ ⊤ t o  ○  a  ] ]
  prop32→ {a} {b} f g f=g = begin
            char t < id1 A b , id1 A b > δmono o < f , g >  ≈⟨  cdr ( IsCCC.π-cong isCCC refl-hom (sym f=g))  ⟩
            char t < id1 A b , id1 A b > δmono o < f , f >  ≈↑⟨ cdr ( IsCCC.π-cong isCCC idL idL ) ⟩
            char t < id1 A b , id1 A b > δmono o < id1 A _ o f , id1 A _ o f >    ≈↑⟨ cdr ( IsCCC.distr-π isCCC ) ⟩
            char t < id1 A b , id1 A b > δmono o (< id1 A _ , id1 A _ > o f)   ≈⟨ assoc ⟩
           (char t < id1 A b , id1 A b > δmono o < id1 A b , id1 A b > ) o f  ≈⟨ car (IsTopos.char-m=⊤ (Topos.isTopos t) _  δmono ) ⟩
            (⊤ t o  ○  b)  o f  ≈↑⟨ assoc ⟩
            ⊤ t o  (○  b  o f)  ≈⟨ cdr (IsCCC.e2 isCCC)  ⟩
            ⊤ t o  ○  a  ∎ 

  prop23→ :  {a b : Obj A}→ (f g : Hom A a b )
    → A [ A [ char t  < id1 A b , id1 A b > δmono  o < f , g > ]  ≈ A [ ⊤ t o  ○  a  ] ] → A [ f ≈ g ]
  prop23→ {a} {b} f g eq = begin
     f   ≈⟨ IsCCC.π≈ isCCC p2 ⟩
     k   ≈↑⟨ IsCCC.π'≈ isCCC p2 ⟩
     g   ∎
     where
       δb : Hom A ( b ∧ b ) (Ω t)
       δb = char t  < id1 A b , id1 A b > δmono
       ip : Pullback A  δb  (⊤ t)
       ip = topos-m-pullback < id1 A b , id1 A b >  δmono
       k : Hom A a b
       k = IsPullback.pullback (Pullback.isPullback ip ) eq 
       p2 :  < f , g > ≈  < k , k >   
       p2 = begin
            < f , g >   ≈↑⟨ IsPullback.π1p=π1 (Pullback.isPullback ip) ⟩
            < id1 A b , id1 A b > o k  ≈⟨ IsCCC.distr-π isCCC ⟩ 
            < id1 A b o k , id1 A b o k >   ≈⟨ IsCCC.π-cong isCCC idL idL ⟩ 
            < k , k >  ∎
--
--
-- Initial Natural number diagram
--
--

  open NatD
  open ToposNat n

--            0               suc
--       1 -----------→ N ---------→ N
--       |              |            |
--       |        <f,g> |       <f,g>|
--       |              ↓            ↓
--       1 ---------→ N x A -----→ N x A
--             <0,z>     <suc o π , h >

  N : Obj A
  N = Nat iNat 
  --  if h : Hom A (N  ∧ a) a is π', A is a constant

  record prop33   {a : Obj A} (f : Hom A １ a ) ( h : Hom A (N  ∧ a) a )  : Set  ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
     field 
       g :  Hom A N  a
       g0=f : A [ A [ g o nzero iNat  ]  ≈ f ]
       gs=h : A [ A [ g o nsuc  iNat  ]  ≈ A [ h o < id1 A _ , g > ] ]
       xnat : NatD A １

  p33 : {a : Obj A} (z : Hom A １ a ) ( h : Hom A (N  ∧ a) a )  → prop33  z h
  p33  {a} z h = record {
        g = g
      ; g0=f = iii
      ; gs=h = v
      ; xnat = xnat
    } where
        xnat : NatD A １
        xnat = record { Nat = N ∧ a ; nzero = < nzero iNat , z > ; nsuc = < nsuc iNat o π , h > }
        fg : Hom A N (N ∧ a )
        fg = initialNat xnat -- < f , g >
        f : Hom A N N
        f = π o fg
        g : Hom A N a
        g = π' o fg
        i : f o nzero iNat  ≈ nzero iNat
        i = begin
            f o nzero iNat  ≈⟨⟩ 
            (π  o fg) o  nzero iNat  ≈↑⟨ assoc ⟩ 
            π  o (fg o  nzero iNat ) ≈⟨ cdr (IsToposNat.izero isToposN xnat ) ⟩ 
            π o nzero xnat ≈⟨ IsCCC.e3a isCCC ⟩ 
            nzero iNat  ∎  
        ii : f o nsuc iNat  ≈ nsuc  iNat o f
        ii = begin
            f o nsuc iNat  ≈⟨⟩ 
            (π o fg ) o nsuc iNat  ≈↑⟨ assoc ⟩ 
            π o ( fg  o nsuc iNat ) ≈⟨ cdr (IsToposNat.isuc isToposN xnat ) ⟩ 
            π o (nsuc xnat o initialNat xnat) ≈⟨ assoc ⟩ 
            (π o  < nsuc iNat o π , h > ) o initialNat xnat ≈⟨ car (IsCCC.e3a isCCC) ⟩ 
            ( nsuc iNat o π ) o initialNat xnat ≈↑⟨ assoc ⟩ 
             nsuc iNat o ( π  o initialNat xnat ) ≈⟨⟩ 
             nsuc  iNat o f  ∎  
        ig : f ≈ id1 A N 
        ig  = begin
           f   ≈⟨ nat-unique iNat i ii ⟩
           initialNat iNat   ≈↑⟨ nat-unique iNat idL (trans-hom idL (sym idR) ) ⟩
           id1 A _  ∎
        iii : g o nzero iNat ≈ z
        iii = begin
            g o nzero iNat  ≈⟨⟩ (π' o initialNat xnat ) o nzero iNat  ≈↑⟨ assoc ⟩ 
            π' o ( initialNat xnat  o nzero iNat)  ≈⟨ cdr (IsToposNat.izero isToposN xnat) ⟩ 
            π' o < nzero iNat , z >  ≈⟨ IsCCC.e3b isCCC ⟩ 
            z  ∎  
        iv : g o nsuc iNat ≈ h o < f , g >
        iv = begin 
            g o nsuc iNat  ≈⟨⟩ 
            (π' o initialNat xnat) o nsuc iNat   ≈↑⟨ assoc ⟩ 
            π' o (initialNat xnat o nsuc iNat )  ≈⟨ cdr (IsToposNat.isuc isToposN xnat) ⟩ 
            π' o  (nsuc xnat o initialNat xnat ) ≈⟨ assoc ⟩ 
            (π' o  nsuc xnat ) o initialNat xnat  ≈⟨ car (IsCCC.e3b isCCC) ⟩ 
            h o initialNat xnat  ≈↑⟨ cdr (IsCCC.e3c isCCC) ⟩ 
            h o < π o fg , π' o fg >  ≈⟨⟩ 
            h o < f , g >  ∎  
        v : A [ A [ g o nsuc iNat ] ≈ A [ h o < id1 A N , g > ] ]
        v = begin
            g o nsuc iNat   ≈⟨ iv  ⟩ 
            h o < f , g >   ≈⟨ cdr ( IsCCC.π-cong isCCC ig refl-hom) ⟩ 
            h o < id1 A N , g >  ∎  

  --               .
  --             / | \
  --            /  |  \
  --           /   ↓   \
  --         N --→ N ←-- a
  --
  cor33  :  coProduct A １ (Nat iNat ) --  N ≅ N + 1
  cor33 = record {
        coproduct = N 
      ; κ1 = nzero iNat 
      ; κ2 = nsuc iNat 
      ; isProduct = record {
              _+_ = λ {a} f g → prop33.g (p  f ( g o π ))  -- Hom A (N n ∧ a) a
           ;  κ1f+g=f = λ {a} {f} {g} → prop33.g0=f (p f (g o π ) )
           ;  κ2f+g=g = λ {a} {f} {g} → k2 {a} {f} {g}
           ;  uniqueness = uniq
           ;  +-cong = pcong 
       }
    } where
        p :  {a : Obj A} (f  : Hom A １ a) ( h : Hom A (N  ∧ a) a ) → prop33  f h
        p f h = p33  f h
        k2 : {a : Obj A} {f  : Hom A １ a} {g : Hom A (Nat iNat) a }
           → A [ A [ prop33.g (p f (g o  π)) o nsuc iNat ] ≈ g ]
        k2 {a} {f} {g} = begin
            (prop33.g (p f (g o π)) o nsuc iNat)  ≈⟨ prop33.gs=h (p f (g o π ))   ⟩
            ( g o π ) o  < id1 A N  , prop33.g (p f (g o π)) >   ≈⟨ sym assoc ⟩
            g o ( π  o   < id1 A N  , prop33.g (p f (g o π)) >)  ≈⟨ cdr (IsCCC.e3a isCCC ) ⟩
            g o id1 A N   ≈⟨ idR ⟩
            g  ∎
        pp :  {c : Obj A} {h : Hom A (Nat iNat) c} → prop33 ( h o nzero iNat ) ( (h o nsuc iNat)  o π)
        pp {c} {h} = p ( h o nzero iNat ) ( (h o nsuc iNat)  o π)
        uniq :  {c : Obj A} {h : Hom A (Nat iNat) c} → 
            prop33.g pp ≈ h 
        uniq {c} {h} = begin
            prop33.g pp  ≈⟨⟩
            π' o initialNat (prop33.xnat pp) ≈↑⟨ cdr (nat-unique (prop33.xnat pp) (
               begin
                  < id1 A _ , h > o nzero iNat ≈⟨ IsCCC.distr-π isCCC ⟩
                  < id1 A _ o nzero iNat , h o nzero iNat > ≈⟨ IsCCC.π-cong isCCC idL refl-hom  ⟩
                  < nzero iNat , h o nzero iNat > ≈⟨⟩
                  nzero (prop33.xnat pp) ∎ )
               (begin
                  < id1 A _ , h > o nsuc iNat ≈⟨  IsCCC.distr-π isCCC ⟩
                  < id1 A _ o nsuc iNat   ,  h o nsuc iNat   > ≈⟨  IsCCC.π-cong isCCC idL refl-hom ⟩
                  < nsuc iNat   ,  h o nsuc iNat   > ≈↑⟨  IsCCC.π-cong isCCC idR idR ⟩
                  < nsuc iNat o   id1 A _  ,  (h o nsuc iNat ) o  id1 A _   > ≈↑⟨  IsCCC.π-cong isCCC (cdr (IsCCC.e3a isCCC)) (cdr (IsCCC.e3a isCCC))  ⟩
                  < nsuc iNat o ( π  o  < id1 A _ , h > ) ,  (h o nsuc iNat ) o ( π   o < id1 A _ , h > ) > ≈⟨  IsCCC.π-cong isCCC assoc assoc ⟩
                  < (nsuc iNat o π ) o  < id1 A _ , h > ,  ((h o nsuc iNat ) o π  )  o < id1 A _ , h > > ≈↑⟨  IsCCC.distr-π isCCC ⟩
                  < nsuc iNat o π ,  (h o nsuc iNat ) o π  >  o < id1 A _ , h >  ≈⟨⟩
                  nsuc (prop33.xnat pp) o < id1 A _ , h > ∎  )) ⟩
            π' o < id1 A _ , h > ≈⟨ IsCCC.e3b isCCC ⟩
            h  ∎
        pcong : {a : Obj A } {f f' : Hom A １ a } {g g' : Hom A (Nat iNat) a } → (f=f' : f ≈ f' ) → ( g=g' : g ≈ g' )
            →  prop33.g (p f (g o π)) ≈ prop33.g (p f' (g' o π))
        pcong {a} {f} {f'} {g} {g'} f=f' g=g' = begin
             prop33.g (p f (g o π))   ≈⟨⟩
             π' o (initialNat (prop33.xnat (p f (g o π)))) ≈↑⟨  cdr (nat-unique (prop33.xnat (p f (g o π))) lem1 lem2 ) ⟩
             π' o (initialNat (prop33.xnat (p f' (g' o π)))) ≈⟨⟩
             prop33.g (p f' (g' o π))   ∎ where
                lem1 :  A [ A [ initialNat (prop33.xnat (p f' ((A Category.o g') π))) o nzero iNat ] ≈ nzero (prop33.xnat (p f ((A Category.o g) π))) ]
                lem1 = begin
                     initialNat (prop33.xnat (p f' (g' o π))) o nzero iNat  ≈⟨ IsToposNat.izero isToposN _ ⟩
                     nzero (prop33.xnat (p f' (g' o π)))  ≈⟨⟩
                     < nzero iNat , f' > ≈⟨  IsCCC.π-cong isCCC refl-hom (sym f=f') ⟩
                     < nzero iNat , f > ≈⟨⟩
                     nzero (prop33.xnat (p f (g o π)))   ∎
                lem2 :   A [ A [ initialNat (prop33.xnat (p f' (g' o π))) o nsuc iNat ] ≈ A [ nsuc (prop33.xnat (p f (g o π))) o initialNat (prop33.xnat (p f' (g' o π))) ] ]
                lem2 = begin
                     initialNat (prop33.xnat (p f' (g' o π))) o nsuc iNat ≈⟨  IsToposNat.isuc isToposN _ ⟩
                     nsuc (prop33.xnat (p f' (g' o π))) o initialNat (prop33.xnat (p f' (g' o π))) ≈⟨⟩
                     < (nsuc iNat) o π ,  g' o π > o initialNat (prop33.xnat (p f' (g' o π))) ≈⟨ car ( IsCCC.π-cong isCCC refl-hom (car (sym g=g')) ) ⟩
                     < (nsuc iNat) o π ,  g  o π > o initialNat (prop33.xnat (p f' (g' o π))) ≈⟨⟩
                     nsuc (prop33.xnat (p f (g o π))) o initialNat (prop33.xnat (p f' (g' o π))) ∎
 
  open Functor
  open import Category.Sets -- hiding (_o_)
  open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym)

  record Singleton (a : Obj A) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
     field
        singleton : Hom A (a ∧ a) ( CCC._<=_ c (Ω t) (a ∧ a) )
        scommute  : A [ A [ CCC.ε c o < singleton , id1 A _ > ] ≈  char t < id1 A _ , id1 A _ > δmono ]  

  tequalizer : {a b : Obj A} → (f g : Hom A a b ) → Equalizer A f g
  tequalizer {a} {b} f g = record {
      equalizer-c = equalizer-c  ker
    ; equalizer = equalizer ker
    ; isEqualizer = record {
          fe=ge = {!!}
        ; k = {!!}
        ; ek=h = {!!}
        ; uniqueness = {!!}
      }
    } where
        ker : Equalizer A ( A [  char t < id1 A _ , id1 A b > δmono o < f , g > ] ) (A [ ⊤ t o (CCC.○ c a) ])
        ker = Ker t ( A [  char t < id1 A _ , id1 A b > δmono o < f , g > ] )

  singleton→mono : {a : Obj A} (s : Singleton a ) → Mono A (Singleton.singleton s)
  singleton→mono {a} s = record { isMono = λ {b} f g eq → {!!} }

  record Partialmap  (a b : Obj A) :  Set (c₁ ⊔ c₂ ⊔ ℓ) where
      field
         p : Obj A
         d : Hom A p a
         f : Hom A p b
         dm  : Mono A d

  record PartialmapClassifier  (b : Obj A) :  Set (c₁ ⊔ c₂ ⊔ ℓ) where
      field
         b1 : Obj A
         η : Hom A b b1
         pm : Partialmap b1 b
         pmc : {a : Obj A} ( d f : Hom A a b) → Mono A d → Hom A a b1
         pb : {a : Obj A} ( d f : Hom A a b) → (dm : Mono A d ) → Pullback A (pmc d f dm) η 
         uniq : {a : Obj A} ( d f : Hom A a b) → (dm : Mono A d ) → (p : Hom A a b1) → Pullback A p η → A [ pmc d f dm ≈ p ]

  partialmapClassifier : (b : Obj A) → PartialmapClassifier b
  partialmapClassifier = {!!}

  record SubObject (a : Obj A) : Set (c₁ ⊔ c₂ ⊔ ℓ)  where
     field
        sb : Obj A
        sm : Hom A sb a 
        smono : Mono A sm

  record SubObjectClassifier  (b : Obj A) :  Set (c₁ ⊔ c₂ ⊔ ℓ) where
      field
         sm : SubObject b
         smc : {a : Obj A} ( d f : Hom A a b) → Mono A d → Hom A a b
         pb : {a : Obj A} ( d f : Hom A a b) → (dm : Mono A d ) → Pullback A (smc d f dm) (id1 A _) 
         uniq : {a : Obj A} ( d f : Hom A a b) → (dm : Mono A d ) → (p : Hom A a b) → Pullback A p (id1 A _) → A [ smc d f dm ≈ p ]

--  postulate
--    I : Set c₁
--    small : Small A I 

--   open import yoneda A I small
-- 
--   cs : CCC SetsAop
--   cs = {!!}
--   
--   toposS : Topos SetsAop cs
--   toposS = {!!}
-- 
