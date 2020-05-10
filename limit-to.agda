open import Category -- https://github.com/konn/category-agda
open import Level

module limit-to where

open import cat-utility
open import HomReasoning
open import Relation.Binary.Core
open  import  Relation.Binary.PropositionalEquality hiding ([_])


open import graph


---  Equalizer  from Limit ( 2→A IdnexFunctor Γ and  IndexNat :  K →　Γ)
---
---
---                     f
---          e       -----→
---     c -----→  a         b     A
---     ^      /     -----→
---     |k   h          g
---     |   /
---     |  /            ^
---     | /             |
---     |/              | Γ
---     d _             |
---      |\             |
---        \ K          af
---         \       -----→
---          \    t0        t1    I
---                  -----→
---                     ag
---
---

open Complete
open Limit
open IsLimit
open NTrans

-- Functor Γ : TwoCat → A

IndexFunctor :  {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) ( a b : Obj A) ( f g : Hom A a b ) →  Functor (TwoCat ) A
IndexFunctor  {c₁} {c₂} {ℓ} A a b f g = record {
         FObj = λ a → fobj a
       ; FMap = λ {a} {b} f → fmap {a} {b} f
       ; isFunctor = record {
             identity = λ{x} → identity x
             ; distr = λ {a} {b} {c} {f} {g}   → distr1 {a} {b} {c} {f} {g}
             ; ≈-cong = λ {a} {b} {c} {f}   → ≈-cong  {a} {b} {c} {f}
       }
      } where
          T = TwoCat 
          fobj :  Obj T → Obj A
          fobj t0 = a
          fobj t1 = b
          fmap :  {x y : Obj T } →  (Hom T x y  ) → Hom A (fobj x) (fobj y)
          fmap  {t0} {t0} id-t0 = id1 A a
          fmap  {t1} {t1} id-t1 = id1 A b
          fmap  {t0} {t1} arrow-f = f
          fmap  {t0} {t1} arrow-g = g
          ≈-cong :  {a : Obj T} {b : Obj T} {f g : Hom T a b}  → T [ f ≈ g ]  → A [ fmap f ≈ fmap g ]
          ≈-cong  {a} {b} {f} {_} refl = let open  ≈-Reasoning A in refl-hom
          identity : (x : Obj T ) →  A [ fmap (id1 T x) ≈  id1 A (fobj x) ]
          identity t0  = let open  ≈-Reasoning A in refl-hom
          identity t1  = let open  ≈-Reasoning A in refl-hom
          distr1 : {a : Obj T} {b : Obj T} {c : Obj T} {f : Hom T a b} {g : Hom T b c} →
               A [ fmap (T [ g o f ])  ≈  A [ fmap g o fmap f ] ]
          distr1  {t0} {t0} {t0} {id-t0 } { id-t0 } = let open  ≈-Reasoning A in sym-hom idL
          distr1  {t1} {t1} {t1} { id-t1 } { id-t1 } = let open  ≈-Reasoning A in begin
                   id b
                ≈↑⟨ idL ⟩
                   id b o id b
                ∎
          distr1  {t0} {t0} {t1} { id-t0 } { arrow-f } = let open  ≈-Reasoning A in begin
                  fmap (T [ arrow-f  o id-t0 ] )
                ≈⟨⟩
                  fmap arrow-f
                ≈↑⟨ idR ⟩
                   fmap arrow-f o id a
                ∎
          distr1  {t0} {t0} {t1}  { id-t0 } { arrow-g } = let open  ≈-Reasoning A in begin
                  fmap (T [ arrow-g  o id-t0 ] )
                ≈⟨⟩
                  fmap arrow-g
                ≈↑⟨ idR ⟩
                   fmap arrow-g o id a
                ∎
          distr1  {t0} {t1} {t1}  { arrow-f } { id-t1 } = let open  ≈-Reasoning A in begin
                  fmap (T [ id-t1  o arrow-f ] )
                ≈⟨⟩
                  fmap arrow-f
                ≈↑⟨ idL ⟩
                   id b o  fmap arrow-f
                ∎
          distr1  {t0} {t1} {t1} { arrow-g } { id-t1 } = let open  ≈-Reasoning A in begin
                  fmap (T [ id-t1  o arrow-g ] )
                ≈⟨⟩
                  fmap arrow-g
                ≈↑⟨ idL ⟩
                   id b o  fmap arrow-g
                ∎

--- Nat for Limit
--
--     Nat : K → IndexFunctor
--

open Functor

IndexNat : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ)
        →  {a b : Obj A}      (f g : Hom A  a b )
    (d : Obj A) → (h : Hom A d a ) →  A [ A [ f  o  h ] ≈ A [ g  o h ] ]   →
        NTrans TwoCat  A (K TwoCat A d) (IndexFunctor {c₁} {c₂} {ℓ} A a b f g)
IndexNat {c₁} {c₂} {ℓ} A {a} {b} f g d h fh=gh = record {
    TMap = λ x → nmap x d h ;
    isNTrans = record {
        commute = λ {x} {y} {f'} → commute1 {x} {y} {f'} d h fh=gh
    }
 } where
         I = TwoCat 
         Γ : Functor I A
         Γ = IndexFunctor {c₁} {c₂} {ℓ} A a b f g
         nmap :  (x : Obj I ) ( d : Obj (A)  ) (h : Hom A d a ) → Hom A (FObj (K I A d) x) (FObj Γ x)
         nmap t0 d h = h
         nmap t1 d h = A [ f o  h ]
         commute1 : {x y : Obj I}  {f' : Hom I x y} (d : Obj A) (h : Hom A d a ) →  A [ A [ f  o  h ] ≈ A [ g  o h ] ]
                 → A [ A [ FMap Γ f' o nmap x d h ] ≈ A [ nmap y d h o FMap (K I A d) f' ] ]
         commute1  {t0} {t1} {arrow-f}  d h fh=gh =  let open  ≈-Reasoning A in begin
                    f o h
                ≈↑⟨ idR ⟩
                    (f o h ) o id d
                ∎
         commute1  {t0} {t1} {arrow-g}  d h fh=gh =  let open  ≈-Reasoning A in begin
                    g o h
                ≈↑⟨ fh=gh ⟩
                    f o h
                ≈↑⟨ idR ⟩
                    (f o h ) o id d
                ∎
         commute1  {t0} {t0} {id-t0}  d h fh=gh =   let open  ≈-Reasoning A in begin
                    id a o h
                ≈⟨ idL ⟩
                    h
                ≈↑⟨ idR ⟩
                    h o id d
                ∎
         commute1  {t1} {t1} {id-t1}  d h fh=gh =   let open  ≈-Reasoning A in begin
                    id b o  ( f o  h  )
                ≈⟨ idL ⟩
                     f o  h
                ≈↑⟨ idR ⟩
                    ( f o  h ) o id d
                ∎


equlimit : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂  ℓ) {a b : Obj A} → (f g : Hom A a b)  (lim : Limit TwoCat A (IndexFunctor A a b f g) ) →
         Hom A (a0 lim) a
equlimit A {a} {b} f g lim = TMap (Limit.t0 lim) graph.t0

lim-to-equ :  {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ)
        →  {a b : Obj A}  (f g : Hom A  a b )
       (lim : Limit TwoCat A (IndexFunctor A a b f g) )
        → IsEqualizer A (equlimit A f g lim) f g
lim-to-equ {c₁} {c₂} {ℓ} A {a} {b} f g lim =  record {
        fe=ge =  fe=ge0
        ; k = λ {d} h fh=gh → k {d} h fh=gh
        ; ek=h = λ {d} {h} {fh=gh} → ek=h d h fh=gh
        ; uniqueness = λ {d} {h} {fh=gh} {k'} → uniquness d h fh=gh k'
     } where
         I : Category Level.zero Level.zero Level.zero   
         I = TwoCat
         Γ : Functor I A
         Γ = IndexFunctor A a b f g
         e : Hom A (a0 lim) a
         e = equlimit A f g lim
         c : Obj A
         c = a0 lim
         inat : (d : Obj A) (h : Hom A d a) → A [ A [ f o h ] ≈ A [ g o h ] ] → NTrans I A (K I A d) Γ
         inat = IndexNat A f g
         fe=ge0 : A [ A [ f o (equlimit A f g lim ) ] ≈ A [ g o (equlimit A f g lim ) ] ]
         fe=ge0 = let open  ≈-Reasoning A in  begin
                    f o (equlimit A f g lim )
                ≈⟨⟩
                    FMap  Γ arrow-f o TMap (Limit.t0 lim) graph.t0
                ≈⟨  IsNTrans.commute ( isNTrans (Limit.t0 lim)) {graph.t0} {graph.t1} {arrow-f} ⟩ 
                    TMap (Limit.t0 lim) graph.t1 o FMap (K (TwoCat   ) A (a0 lim)) id-t0
                ≈↑⟨ IsNTrans.commute ( isNTrans (Limit.t0 lim)) {graph.t0} {graph.t1} {arrow-g} ⟩ 
                    FMap  Γ arrow-g o TMap (Limit.t0 lim) graph.t0
                ≈⟨⟩
                    g o (equlimit A f g lim )
                ∎
         k : {d : Obj A}  (h : Hom A d a) → A [ A [ f  o  h ] ≈ A [ g  o h ] ] → Hom A d c
         k {d} h fh=gh  =  limit (isLimit lim) d (inat d h fh=gh )
         ek=h :  (d : Obj A ) (h : Hom A d a ) →  ( fh=gh : A [ A [ f  o  h ] ≈ A [ g  o h ] ] )  → A [ A [ e o k h fh=gh ] ≈ h ]
         ek=h d h fh=gh = let open  ≈-Reasoning A in  begin
                    e o k h fh=gh
                ≈⟨⟩
                    TMap (Limit.t0 lim) graph.t0  o k h fh=gh
                ≈⟨ t0f=t (isLimit lim) {d} {inat d h fh=gh } {graph.t0}  ⟩
                    TMap (inat d h fh=gh) graph.t0
                ≈⟨⟩
                    h
                ∎
         uniq-nat :  {i : Obj I} →  (d : Obj A )  (h : Hom A d a ) ( k' : Hom A d c )
                       ( fh=gh : A [ A [ f  o  h ] ≈ A [ g  o h ] ]) → A [ A [ e o k' ] ≈ h ] →
                       A [ A [ TMap (Limit.t0 lim) i o k' ] ≈ TMap (inat d h fh=gh) i ]
         uniq-nat {t0} d h k' fh=gh ek'=h =  let open  ≈-Reasoning A in begin
                    TMap (Limit.t0 lim) graph.t0 o k'
                ≈⟨⟩
                    e o k'
                ≈⟨ ek'=h ⟩
                    h
                ≈⟨⟩
                    TMap (inat d h fh=gh) graph.t0
                ∎
         uniq-nat {t1} d h k' fh=gh ek'=h =  let open  ≈-Reasoning A in begin
                    TMap (Limit.t0 lim) t1 o k'
                ≈↑⟨ car (idR) ⟩
                    ( TMap (Limit.t0 lim) t1  o  id c ) o k'
                ≈⟨⟩
                    ( TMap (Limit.t0 lim) t1  o  FMap (K I A c) arrow-f ) o k'
                ≈↑⟨ car ( nat1 (Limit.t0 lim) arrow-f ) ⟩
                    ( FMap Γ  arrow-f  o TMap (Limit.t0 lim) graph.t0 ) o k'
                ≈⟨⟩
                   (f o e ) o k'
                ≈↑⟨ assoc ⟩
                   f o ( e o k' )
                ≈⟨ cdr  ek'=h ⟩
                    f o h
                ≈⟨⟩
                    TMap (inat d h fh=gh) t1
                ∎
         uniquness :  (d : Obj A ) (h : Hom A d a ) →  ( fh=gh : A [ A [ f  o  h ] ≈ A [ g  o h ] ] )  →
                 ( k' : Hom A d c )
                → A [ A [ e o k' ] ≈ h ] → A [ k h  fh=gh   ≈ k' ]
         uniquness d h fh=gh k' ek'=h =  let open  ≈-Reasoning A in  begin
                    k h fh=gh
                ≈⟨ limit-uniqueness (isLimit lim) ( λ{i} → uniq-nat {i} d h k' fh=gh ek'=h ) ⟩
                    k'
                ∎


---  Product  from Limit ( given Discrete→A functor Γ and  pnat :  K →　Γ)

open  import  Relation.Binary.PropositionalEquality

open DiscreteHom

plimit : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (S : Set  c₁) 
      →  ( Γ : Functor (DiscreteCat  S ) A ) → (lim : Limit ( DiscreteCat  S ) A Γ )  → Obj A
plimit A S Γ lim = a0 lim

discrete-identity : { c₁ : Level} { S : Set c₁} { a : S } → (f : DiscreteHom a a ) →  (DiscreteCat S)  [ f  ≈  id1 (DiscreteCat S) a ]
discrete-identity  f =   refl

pnat :  {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ)  (S : Set  c₁)  
    → (Γ : Functor (DiscreteCat S) A )
    →  {q : Obj A }  ( qi : (i : Obj ( DiscreteCat  S)) → Hom A q (FObj Γ i) )
    → NTrans (DiscreteCat S )A (K (DiscreteCat S) A q) Γ
pnat  A S Γ {q} qi  = record {
        TMap = qi ; 
        isNTrans = record { commute = λ {a} {b} {f} → commute {a} {b} {f} }
    } where
        commute :  {a b : Obj (DiscreteCat  S) } {f : Hom (DiscreteCat S)  a b} →
                A [ A [ FMap Γ f o qi a ] ≈ A [ qi  b o FMap (K (DiscreteCat  S) A q) f ] ]
        commute {a} {b} {f} with discrete f
        commute {a} {.a} {f} | refl =  let open  ≈-Reasoning A in  begin
                  FMap Γ f o qi a
                ≈⟨ car ( fcong Γ (discrete-identity f )) ⟩
                  FMap Γ (id1 (DiscreteCat S) a ) o qi a
                ≈⟨ car ( IsFunctor.identity (isFunctor Γ) ) ⟩
                  id1 A (FObj Γ a)  o qi a
                ≈⟨ idL ⟩
                   qi  a 
                ≈↑⟨ idR ⟩
                   qi  a o id q
                ≈⟨⟩
                   qi  a o FMap (K (DiscreteCat S) A q) f
                ∎

lim-to-product :  {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) ( S : Set  c₁ )
        →  ( Γ : Functor (DiscreteCat S) A )     -- could be constructed from S → Obj A
        → (lim : Limit (DiscreteCat S) A Γ )
        → IProduct  (Obj (DiscreteCat S))  A (FObj Γ)
lim-to-product A S Γ lim = record {
          iprod = plimit A S Γ lim
          ; pi =  λ  i →   TMap (Limit.t0 lim) i 
          ; isIProduct =  record {
              iproduct = λ {q} qi → iproduct {q} qi ;
              pif=q =  λ {q} {qi} {i} → pif=q {q} qi {i}  ;
              ip-uniqueness  = λ  {q } { h } → ip-uniqueness {q} {h} ;
              ip-cong  =  λ {q } { qi }  { qi' } qi=qi' → ip-cong  {q} {qi} {qi'} qi=qi'
          }
   } where
        D = DiscreteCat S
        I = Obj ( DiscreteCat S )
        ai = λ i → FObj Γ i
        p = a0 lim
        pi =  λ i → TMap (Limit.t0 lim) i
        iproduct : {q : Obj A}  → ( qi : (i : I) → Hom A q (ai i) ) → Hom A q p
        iproduct {q} qi = limit (isLimit lim) q (pnat A S Γ qi )
        pif=q :   {q : Obj A}  → ( qi : (i : I) → Hom A q (ai i) ) → ∀ { i : I } → A [ A [ ( pi i )  o ( iproduct qi ) ] ≈  (qi i) ]
        pif=q {q} qi {i} = t0f=t (isLimit lim)  {q} {pnat A S Γ qi } {i}
        ipu : {i : Obj D} → (q : Obj A) (h : Hom A q p ) → A [ A [ TMap (Limit.t0 lim) i o h ] ≈ A [ pi i o h ] ]
        ipu {i} q h = let open  ≈-Reasoning A in  refl-hom
        ip-uniqueness :  {q : Obj A} { h : Hom A q p } → A [ iproduct ( λ (i : I) →  A [ (pi i)  o h ] )  ≈  h ]
        ip-uniqueness {q} {h} = limit-uniqueness (isLimit lim) {q} {pnat A S Γ (λ i → A [ pi i  o h ]  )} (ipu q h)
        ipc : {q : Obj A}   → { qi : (i : I) → Hom A q (ai i) } → { qi' : (i : I) → Hom A q (ai i) } 
             → (i : I ) →  A [ qi i ≈ qi' i ]  → 
             A [ A [ TMap (Limit.t0 lim) i o iproduct qi' ] ≈ TMap (pnat A S Γ qi) i ]
        ipc {q} {qi} {qi'} i qi=qi' = let open  ≈-Reasoning A in begin
                  TMap (Limit.t0 lim) i o iproduct qi' 
                ≈⟨⟩
                  TMap (Limit.t0 lim) i o limit (isLimit lim) q (pnat A S Γ qi' )
                ≈⟨ t0f=t (isLimit lim) {q} {pnat A S Γ qi'} {i} ⟩
                  TMap (pnat A S Γ qi') i
                ≈⟨⟩
                  qi' i
                ≈↑⟨ qi=qi' ⟩
                  qi i
                ≈⟨⟩
                  TMap (pnat A S Γ qi) i
                ∎
        ip-cong : {q : Obj A}   → { qi : (i : I) → Hom A q (ai i) } → { qi' : (i : I) → Hom A q (ai i) }
                        → ( ∀ (i : I ) →  A [ qi i ≈ qi' i ] ) → A [ iproduct qi ≈ iproduct qi' ]
        ip-cong {q} {qi} {qi'} qi=qi' =  limit-uniqueness (isLimit lim) {q} {pnat A S Γ qi}  (λ {i} → ipc {q} {qi} {qi'} i (qi=qi' i))
