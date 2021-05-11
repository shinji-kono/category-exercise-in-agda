---
--
--  Equalizer
--
--         e             f
--    c  -------→ a ---------→ b
--    ^        .     ---------→
--    |      .            g
--    |k   .
--    |  . h
--    d
--
--                        Shinji KONO <kono@ie.u-ryukyu.ac.jp>
----

open import Category -- https://github.com/konn/category-agda
open import Level
module equalizer { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } where

open import HomReasoning
open import cat-utility

--
-- Some obvious conditions for k  (fe = ge) → ( fh = gh )
--

f1=g1 : { a b c : Obj A } {f g : Hom A a b } → (eq : A [ f ≈ g ] ) → (h : Hom A c a) →  A [ A [ f o h ] ≈ A [ g o h ]  ]
f1=g1 eq h = let open ≈-Reasoning (A) in (resp refl-hom eq )

f1=f1 : { a b : Obj A } (f : Hom A a b ) →  A [ A [ f o (id1 A a)  ] ≈ A [ f o (id1 A a)  ]  ]
f1=f1  f = let open ≈-Reasoning (A) in refl-hom

f1=gh : { a b c d : Obj A } {f g : Hom A a b } → { e : Hom A c a } → { h : Hom A d c } →
       (eq : A [ A [ f  o e ] ≈ A [ g  o e ] ] ) → A [ A [ f o A [ e o h ] ] ≈ A [ g o A [ e  o h ]  ] ]
f1=gh {a} {b} {c} {d} {f} {g} {e} {h} eq = let open ≈-Reasoning (A) in
             begin
                  f o ( e  o h )
             ≈⟨ assoc  ⟩
                  (f o  e ) o h
             ≈⟨ car eq  ⟩
                  (g o  e ) o h
             ≈↑⟨ assoc  ⟩
                  g o ( e  o h )
             ∎

--
-- Burroni's Flat Equational Definition of Equalizer
--

record Burroni : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
   field
      equ : {a b : Obj A } → (f g : Hom A a b) →  Obj A
      α : {a b : Obj A } → (f g : Hom A a b) →  Hom A (equ f g)  a
      γ : {a b d : Obj A } → (f g : Hom A a b) → (h : Hom A d a ) →  Hom A (equ (A [ f o h ]) (A [ g o h ]))  (equ f g)
      δ : {a b : Obj A } → (f g : Hom A a b) → A [ f ≈ g ] → Hom A a (equ f g)
      b1 : {a b : Obj A } → (f g : Hom A a b) → A [ A [ f  o α f g ] ≈ A [ g  o α f g ] ]
   b1k :  {a b : Obj A } → (f g : Hom A a b) → {d : Obj A } {k : Hom A d (equ f g)} →  A [ A [ f o A [ α f g o k ] ] ≈ A [ g o A [ α f g o k ] ] ]
   b1k f g {d} {k} = ≈-Reasoning.trans-hom A (≈-Reasoning.assoc A) (≈-Reasoning.trans-hom A (≈-Reasoning.car A (b1 f g)) (≈-Reasoning.sym A (≈-Reasoning.assoc A)))
   field
      b2 : {a b d : Obj A} {h : Hom A d a } → (f g : Hom A a b) → A [ A [ ( α f g ) o (γ f g h) ] ≈ A [ h  o α (A [ f o h ]) (A [ g o h ]) ] ]
      b3 : {a b   : Obj A} (f g : Hom A a b) → (f=g : A [ f ≈ g ]) → A [ A [ α f g o δ f g f=g ] ≈ id1 A a ]
      b4 : {a b d : Obj A} (f g : Hom A a b) → {k : Hom A d (equ f g)} → 
           A [ A [ γ f g ( A [ α f g o k ] ) o ( δ (A [ f o A [ α f g o  k ] ] ) (A [ g o A [ α f g o  k ] ] ) (f1=gh (b1 f g) ) )] ≈ k ]
   β : { d a b : Obj A}  → (f g : Hom A a b) → (h : Hom A d a ) → A [ A [ f o h ]  ≈ A [ g o h ] ] → Hom A d (equ f g)
   β {d} {a} {b} f g h eq =  A [ γ f g h o δ (A [ f o h ]) (A [ g o h ]) eq ]

open Equalizer
open IsEqualizer
open Burroni

-------------------------------
-- 
-- Every equalizer is monic
--
--     e i = e j → i = j
--
--           e eqa f g        f
--         c ---------→ a ------→b
--        ^^
--        ||
--       i||j
--        ||
--         d

monic : { a b d : Obj A } {f g : Hom A a b } → ( eqa : Equalizer A f g) 
      →  { i j : Hom A d (equalizer-c eqa) }
      →  A [ A [ equalizer eqa o i ]  ≈  A [ equalizer eqa o j ] ] →  A [ i  ≈ j  ]
monic {a} {b} {d} {f} {g} eqa {i} {j} ei=ej = let open ≈-Reasoning (A) in begin
                 i
              ≈↑⟨ uniqueness (isEqualizer eqa) ( begin
                   equalizer eqa  o i
              ≈⟨ ei=ej ⟩
                   equalizer eqa  o j
              ∎ )⟩
                 k (isEqualizer eqa) (equalizer eqa o j) ( f1=gh (fe=ge (isEqualizer eqa) ) )
              ≈⟨ uniqueness (isEqualizer eqa) ( begin
                   equalizer eqa o j
              ≈⟨⟩
                   equalizer eqa o j
              ∎ )⟩
                 j
              ∎ 

--------------------------------
--
--
--   Isomorphic arrows from c' to c makes another equalizer
--
--           e eqa f g        f
--         c ---------→ a ------→b
--        |^
--        ||
--    h   || h-1
--        v|
--         c'

equalizer+iso : {a b c' : Obj A } {f g : Hom A a b } →
                ( eqa : Equalizer A f g ) → (iso : Iso A c' (equalizer-c eqa) )
           → IsEqualizer A (A [ equalizer eqa  o Iso.≅→ iso ] ) f g   -- h-1
equalizer+iso  {a} {b} {c'} {f} {g} eqa iso =  record {
      fe=ge = fe=ge1 ;
      k = λ j eq → A [ h o k (isEqualizer eqa) j eq ] ;
      ek=h = ek=h1 ;
      uniqueness = uniqueness1
  } where
      h-1 : Hom A c' (equalizer-c eqa)
      h-1 = Iso.≅→ iso
      h : Hom A (equalizer-c eqa) c' 
      h =  Iso.≅← iso
      e = equalizer eqa
      fe=ge1 :  A [ A [ f o  A [ e  o h-1  ]  ]  ≈ A [ g o  A [ e  o h-1  ]  ] ]
      fe=ge1 = f1=gh ( fe=ge (isEqualizer eqa) )
      ek=h1 :   {d : Obj A} {j : Hom A d a} {eq : A [ A [ f o j ] ≈ A [ g o j ] ]} →
                A [ A [  A [ e  o h-1  ]  o A [ h o k (isEqualizer eqa) j eq ] ] ≈ j ]
      ek=h1 {d} {j} {eq} =  let open ≈-Reasoning (A) in
             begin
                   ( e  o h-1 )  o ( h o k (isEqualizer eqa) j eq )
             ≈↑⟨ assoc ⟩
                    e o ( h-1  o ( h  o k (isEqualizer eqa) j eq  ) )
             ≈⟨ cdr assoc ⟩
                    e o (( h-1  o  h)  o k (isEqualizer eqa) j eq  ) 
             ≈⟨ cdr (car ( Iso.iso← iso) )  ⟩
                    e o (id1 A (equalizer-c eqa)  o k (isEqualizer eqa) j eq  ) 
             ≈⟨ cdr idL  ⟩
                    e o  k (isEqualizer eqa) j eq  
             ≈⟨ ek=h (isEqualizer eqa) ⟩
                   j
             ∎ 
      uniqueness1 : {d : Obj A} {h' : Hom A d a} {eq : A [ A [ f o h' ] ≈ A [ g o h' ] ]} {j : Hom A d c'} →
                A [ A [  A [ e  o h-1 ]  o j ] ≈ h' ] →
                A [ A [ h o k (isEqualizer eqa) h' eq ] ≈ j ]
      uniqueness1 {d} {h'} {eq} {j} ej=h  =  let open ≈-Reasoning (A) in
             begin
                   h o k (isEqualizer eqa) h' eq
             ≈⟨ cdr (uniqueness (isEqualizer eqa) ( begin
                    e o ( h-1 o j  )
                 ≈⟨ assoc ⟩
                   (e o  h-1 ) o j  
                 ≈⟨ ej=h ⟩
                    h'
             ∎ )) ⟩
                   h o  ( h-1 o j )
             ≈⟨ assoc  ⟩
                   (h o   h-1 ) o j 
             ≈⟨ car (Iso.iso→ iso)  ⟩
                   id c' o j 
             ≈⟨ idL ⟩
                   j
             ∎


equalizerIso : {a b c : Obj A} → (f g : Hom A a b ) → (equ : Equalizer A f g )
   → (m :  Hom A c a) → ( iso : Iso A c (equalizer-c equ))
   → ( mm : A [ A [ equalizer equ o Iso.≅→ iso ] ≈  m ] ) 
   → IsEqualizer A m f g
equalizerIso {a} {b} {c} f g equ m iso mm = record {
     fe=ge = fe-ge
   ; k = λ {d} h eq  → A [ Iso.≅← iso o  IsEqualizer.k (Equalizer.isEqualizer equ) h eq  ]
   ; ek=h = ek=h1
   ; uniqueness = uniqueness1 } where
     ker : Hom A ( equalizer-c equ ) a
     ker  = equalizer equ
     fe-ge : A [ A [ f o m ] ≈ A [ g o m ] ]
     fe-ge = begin
        f o m ≈↑⟨ cdr mm ⟩
        f o (equalizer equ o Iso.≅→ iso) ≈⟨ assoc ⟩
        (f o equalizer equ) o Iso.≅→ iso ≈⟨ car ( IsEqualizer.fe=ge (Equalizer.isEqualizer equ) )  ⟩
        (g o equalizer equ ) o Iso.≅→ iso ≈↑⟨ assoc ⟩
        g o (equalizer equ  o Iso.≅→ iso) ≈⟨ cdr mm  ⟩
        g o m ∎  where   open ≈-Reasoning A 
     ek=h1 : {d : Obj A} {h : Hom A d a}
           {eq : A [ A [ f o h ] ≈ A [ g o h ] ]} →
            A [ A [ m o (A Category.o Iso.≅← iso) (IsEqualizer.k (isEqualizer equ) h eq) ] ≈ h ]
     ek=h1  {d} {h} {eq} = begin
            m o (  Iso.≅← iso o IsEqualizer.k (Equalizer.isEqualizer equ) h eq ) ≈↑⟨ car mm ⟩
            (equalizer equ o Iso.≅→ iso) o (  Iso.≅← iso o IsEqualizer.k (Equalizer.isEqualizer equ) h eq ) ≈↑⟨ assoc ⟩
            _ o (Iso.≅→ iso o (  Iso.≅← iso o IsEqualizer.k (Equalizer.isEqualizer equ) h eq )) ≈⟨ cdr assoc ⟩
            equalizer equ o ((Iso.≅→ iso o   Iso.≅← iso) o IsEqualizer.k (Equalizer.isEqualizer equ) h eq ) ≈⟨ cdr (car (Iso.iso←  iso)) ⟩
            equalizer equ o (id1 A _ o IsEqualizer.k (Equalizer.isEqualizer equ) h eq ) ≈⟨ cdr idL ⟩
            equalizer equ o IsEqualizer.k (Equalizer.isEqualizer equ) h eq  ≈⟨ IsEqualizer.ek=h (isEqualizer equ) ⟩
            h ∎  where   open ≈-Reasoning A
     uniqueness1 : {d : Obj A} {h : Hom A d a}
            {eq : A [ A [ f o h ] ≈ A [ g o h ] ]}
            {k' : Hom A d c} → A [ A [ m o k' ] ≈ h ]
               → A [ (A Category.o Iso.≅← iso) (IsEqualizer.k (isEqualizer equ) h eq) ≈ k' ]
     uniqueness1  {d} {h} {eq} {k'} eqk = begin
            Iso.≅← iso  o  (IsEqualizer.k (isEqualizer equ) h eq) ≈⟨ cdr ( IsEqualizer.uniqueness (Equalizer.isEqualizer equ) (  begin
             equalizer equ o ((Iso.≅→ iso)  o k' ) ≈⟨ assoc  ⟩
             (equalizer equ o Iso.≅→ iso)  o k'  ≈⟨ car mm  ⟩
             m o k' ≈⟨ eqk  ⟩
             h ∎ ))   ⟩
            Iso.≅← iso o ( Iso.≅→ iso o k' ) ≈⟨ assoc ⟩
            (Iso.≅← iso o  Iso.≅→ iso ) o k'  ≈⟨ car (Iso.iso→  iso )⟩
            id1 A _ o k' ≈⟨  idL ⟩
            k' ∎  where   open ≈-Reasoning A
     mequ : Equalizer A f g
     mequ = record { equalizer-c = c ; equalizer =  m ; isEqualizer = record {
           fe=ge = fe-ge 
         ; k = λ {d} h fh=gh → A [ Iso.≅← iso o IsEqualizer.k (Equalizer.isEqualizer equ) h fh=gh ]
         ; ek=h = ek=h1 
         ; uniqueness = uniqueness1 
         } }

--------------------------------
--
-- If we have two equalizers on c and c', there are isomorphic pair h, h'
--
--     h : c → c'  h' : c' → c
--     e' = h   o e
--     e  = h'  o e'
--
--
--
--           e eqa f g        f
--         c ---------→a ------→b
--         ^            ^     g
--         |            |
--         |k = id c'   |
--         v            |
--         c'-----------+
--           e eqa' f g

c-iso-l : { c c' a b : Obj A } {f g : Hom A a b } →  {e : Hom A c a } { e' : Hom A c' a }
       ( eqa : IsEqualizer A e f g) → ( eqa' :  IsEqualizer A e' f g )
      → Hom A c c'         
c-iso-l  {c} {c'} {a} {b} {f} {g} {e} eqa eqa' = k eqa' e ( fe=ge eqa )

c-iso-r : { c c' a b : Obj A } {f g : Hom A a b } →  {e : Hom A c a } { e' : Hom A c' a }
       ( eqa : IsEqualizer A e f g) → ( eqa' :  IsEqualizer A e' f g )
      → Hom A c' c         
c-iso-r  {c} {c'} {a} {b} {f} {g} {e} {e'} eqa eqa' = k eqa e' ( fe=ge eqa' )

c-iso-lr : { c c' a b : Obj A } {f g : Hom A a b } →  {e : Hom A c a } { e' : Hom A c' a }
       ( eqa : IsEqualizer A e f g) → ( eqa' :  IsEqualizer A e' f g ) →
  A [ A [ c-iso-l eqa eqa' o c-iso-r eqa eqa' ]  ≈ id1 A c' ]
c-iso-lr  {c} {c'} {a} {b} {f} {g} {e} {e'} eqa eqa' =  let open ≈-Reasoning (A) in begin
                  c-iso-l eqa eqa' o c-iso-r eqa eqa'
              ≈⟨⟩
                  k eqa' e ( fe=ge eqa )  o  k eqa e' ( fe=ge eqa' )
              ≈↑⟨ uniqueness eqa' ( begin
                  e' o ( k eqa' e (fe=ge eqa) o k eqa e' (fe=ge eqa') )
              ≈⟨ assoc  ⟩
                  ( e' o  k eqa' e (fe=ge eqa) ) o k eqa e' (fe=ge eqa') 
              ≈⟨ car (ek=h eqa') ⟩
                  e o k eqa e' (fe=ge eqa') 
              ≈⟨ ek=h eqa ⟩
                  e'
              ∎ )⟩
                 k eqa' e' ( fe=ge eqa' )
              ≈⟨ uniqueness eqa' ( begin
                   e' o id c'
              ≈⟨ idR ⟩
                   e'
              ∎ )⟩
                 id c'
              ∎

-- c-iso-rl is obvious from the symmetry

equ-iso : { c c' a b : Obj A } {f g : Hom A a b } →  {e : Hom A c a } { e' : Hom A c' a }
       ( eqa : IsEqualizer A e f g) → ( eqa' :  IsEqualizer A e' f g )
      → Iso A c c'
equ-iso eqa eqa' = record {
      ≅→ = c-iso-l eqa eqa'
    ; ≅← = c-iso-r eqa eqa'
    ; iso→ = c-iso-lr eqa' eqa
    ; iso←  = c-iso-lr eqa eqa'
   }


--
-- we cannot have equalizer ≈ id. we only have Iso A (equalizer-c equ) a
--
equ-ff : {a b : Obj A} → (f : Hom A a b ) → IsEqualizer A (id1 A a) f f
equ-ff {a} {b} f = record {
      fe=ge = ≈-Reasoning.refl-hom A ;  
      k = λ {d} h eq → h ;
      ek=h = λ {d} {h} {eq} → ≈-Reasoning.idL A ;
      uniqueness  = λ {d} {h} {eq} {k'} ek=h → begin
            h
         ≈↑⟨ ek=h ⟩
            id1 A a o k'
         ≈⟨ idL ⟩
            k'
         ∎ 
   } where open  ≈-Reasoning A


--------------------------------
----
--
-- Existence of equalizer satisfies Burroni equations
--
----

lemma-equ1 : ({a b : Obj A} (f g : Hom A a b) → Equalizer A f g ) → Burroni 
lemma-equ1  eqa  = record {
      equ = λ f g → equalizer-c (eqa f g)
    ; α = λ f g   →  equalizer (eqa f g)
    ; γ = λ f g h → k (isEqualizer (eqa f g )) ( A [ h  o (equalizer ( eqa (A [ f  o  h ] ) (A [ g o h ] ))) ] )
           (lemma-equ4 f g h) 
    ; δ =   λ {a} {b} f g f=g → k (isEqualizer (eqa {a} {b} f g )) {a} (id1 A a) (f1=g1 f=g _ )
    ; b1 = λ f g → fe=ge (isEqualizer (eqa f g ))
    ; b2 = lemma-b2 
    ; b3 = λ {a } {b} f g f=g → lemma-b3 f g f=g 
    ; b4 = lemma-b4
 }  where
     ieqa : {a b : Obj A} (f g : Hom A a b) → IsEqualizer A ( equalizer (eqa f g )) f g 
     ieqa f g = isEqualizer (eqa f g) 
     lemma-b3 : {a b : Obj A} (f g : Hom A a b ) 
        → (f=g : A [ f ≈ g ] ) → A [ A [ equalizer (eqa f g ) o k (isEqualizer (eqa f g)) (id1 A a) (f1=g1 f=g _ ) ] ≈ id1 A a  ]
     lemma-b3 {a} f g f=g = let open ≈-Reasoning (A) in
             begin
                  equalizer (eqa f g) o k (isEqualizer (eqa f g)) (id a) (f1=g1 f=g _ )
             ≈⟨ ek=h (isEqualizer (eqa f g ))  ⟩
                  id a
             ∎
     lemma-equ4 :  {a b d : Obj A}  → (f : Hom A a b) → (g : Hom A a b ) → (h : Hom A d a ) →
                      A [ A [ f o A [ h o equalizer (eqa (A [ f o h ]) (A [ g o h ])) ] ] ≈ A [ g o A [ h o equalizer (eqa (A [ f o h ]) (A [ g o h ])) ] ] ]
     lemma-equ4 {a} {b} {d} f g h  = let open ≈-Reasoning (A) in
             begin
                   f o ( h o equalizer (eqa (f o h) ( g o h )))
             ≈⟨ assoc ⟩
                   (f o h) o equalizer (eqa (f o h) ( g o h ))
             ≈⟨ fe=ge (isEqualizer (eqa (A [ f o h ]) (A [ g o h ]))) ⟩
                   (g o h) o equalizer (eqa (f o h) ( g o h ))
             ≈↑⟨ assoc ⟩
                   g o ( h o equalizer (eqa (f o h) ( g o h )))
             ∎
     lemma-b2 : {a b d : Obj A} {h : Hom A d a} → (f g : Hom A a b) → A [
                      A [ equalizer (eqa f g) o k (isEqualizer (eqa f g)) (A [ h o equalizer (eqa (A [ f o h ]) (A [ g o h ])) ]) (lemma-equ4 {a} {b} f g h) ]
                    ≈ A [ h o equalizer (eqa (A [ f o h ]) (A [ g o h ])) ] ]
     lemma-b2 {a} {b} {d} {h} f g = let open ≈-Reasoning (A) in
             begin
                    equalizer (eqa f g) o k (isEqualizer (eqa f g)) (h o equalizer (eqa (f o h) (g o h))) (lemma-equ4 {a} {b} f g h)
             ≈⟨ ek=h (isEqualizer (eqa f g))  ⟩
                    h o equalizer (eqa (f o h ) ( g o h ))
             ∎
     lemma-b4 : {a b d : Obj A} (f g : Hom A a b) → {j : Hom A d (equalizer-c (eqa f g))} → A [
              A [ k (ieqa f g) (A [ A [ equalizer (eqa f g) o j ] o 
                              equalizer (eqa (A [ f o A [ equalizer (eqa f g ) o j ] ]) (A [ g o A [ equalizer (eqa f g  ) o j ] ])) ])
                     (lemma-equ4 {a} {b} {d} f g (A [ equalizer (eqa f g) o j ])) 
                 o    k (ieqa (A [ f o A [ equalizer (eqa f g) o j ] ]) (A [ g o A [ equalizer (eqa f g) o j ] ])) (id1 A _)
                     (f1=g1 (f1=gh (fe=ge (ieqa f g))) (id1 A _))] ≈ j ]
     --   h = equalizer (eqa f g) o j 
     lemma-b4 {a} {b} {d} f g  {j} = 
             begin
                 k (ieqa f g) ( h o equalizer (eqa ( f o h ) ( g o h )) ) (lemma-equ4 {a} {b} {d} f g h)
                 o    k (ieqa (f o h) ( g o h)) (id1 A _) (f1=g1 (f1=gh (fe=ge (ieqa f g))) (id1 A _))
             ≈↑⟨ uniqueness (ieqa f g) ( begin
                  equalizer (eqa f g) o ( k (ieqa f g) (( h o equalizer (eqa ( f o h ) ( g o h )) )) (lemma-equ4 {a} {b} {d} f g h)
                   o    k (ieqa (f o h) ( g o h)) (id1 A _) (f1=g1 (f1=gh (fe=ge (ieqa f g))) (id1 A _)) )
                ≈⟨ assoc ⟩
                 (equalizer (eqa f g) o ( k (ieqa f g) (( h o equalizer (eqa ( f o h ) ( g o h )) )) (lemma-equ4 {a} {b} {d} f g h)))
                   o    k (ieqa (f o h) ( g o h)) (id1 A _) (f1=g1 (f1=gh (fe=ge (ieqa f g))) (id1 A _))
                ≈⟨ car (ek=h (ieqa f g) ) ⟩
                 (( h o equalizer (eqa ( f o h ) ( g o h )) ))
                   o    k (ieqa (f o h) ( g o h)) (id1 A _) (f1=g1 (f1=gh (fe=ge (ieqa f g))) (id1 A _))
                ≈↑⟨ assoc ⟩
                 h o (equalizer (eqa ( f o h ) ( g o h )) o    k (ieqa (f o h) ( g o h)) (id1 A _) (f1=g1 (f1=gh (fe=ge (ieqa f g))) (id1 A _)))
                ≈⟨ cdr (ek=h  (ieqa (f o h) ( g o h))) ⟩
                 h o id1 A _
                ≈⟨ idR ⟩
                 h
                ∎ 
             ) ⟩
                 k (ieqa f g) h (f1=gh (fe=ge (ieqa f g)) )
             ≈⟨ uniqueness (ieqa f g) refl-hom ⟩
                 j
             ∎  where
               open ≈-Reasoning A
               h : Hom A d a
               h = equalizer (eqa f g) o j
--     cong-γ1 :  {a b c d : Obj A } → {f g : Hom A a b} {h h' : Hom A d a } →  A [ h ≈ h' ] →  
--                     A [  k (ieqa f g ) {_} ( A [ h  o (equalizer1 ( ieqa (A [ f  o  h  ] ) (A [ g o h  ] )  )) ] ) (lemma-equ4 {a} {b} {d} f g h ) 
--                       ≈  A [ k (ieqa f g ) {_} ( A [ h' o (equalizer1 ( ieqa (A [ f  o  h' ] ) (A [ g o h' ] )  )) ] ) (lemma-equ4 {a} {b} {d} f g h' ) o {!!} ] ]
--     cong-γ1 {a} {b} {c} {d} {f} {g} {h} {h'} h=h'  = let open ≈-Reasoning (A) in begin
--                 k (ieqa f g ) {_} ( A [ h  o (equalizer1 ( ieqa (A [ f  o  h  ] ) (A [ g o h  ] ))) ] ) (lemma-equ4 {a} {b} {d} f g h )
--             ≈⟨ uniqueness (ieqa f g) {!!} ⟩    
--                 {!!} -- k (ieqa f g ) {_} ( A [ h' o (equalizer1 ( ieqa (A [ f  o  h' ] ) (A [ g o h' ] ))) ] ) (lemma-equ4 {a} {b} {d} f g h' )
--             ∎
--     cong-δ1 : {a b c : Obj A} {e : Hom A c a } {f f' : Hom A a b} → A [ f ≈ f' ] →  A [ k (ieqa  f f ) (id1 A a)  (f1=f1 f)  ≈ 
--                                                                            A [ {!!} o k (ieqa  f' f' ) (id1 A a)  (f1=f1 f')  ] ]
--     cong-δ1 {a} {b} {c} {e} {f} {f'} f=f' =  let open ≈-Reasoning (A) in
--             begin
--                 k (ieqa  f  f  ) (id a)  (f1=f1 f) 
--             ≈⟨  uniqueness (ieqa f f) {!!} ⟩
--                 {!!} -- k (ieqa  f' f' ) (id a)  (f1=f1 f') 
--             ∎



--------------------------------
--
-- Bourroni equations gives an Equalizer
--

lemma-equ2 : {a b : Obj A} (f g : Hom A a b) → ( bur : Burroni ) → IsEqualizer A {equ bur f g} {a} {b} (α bur f g ) f g 
lemma-equ2 {a} {b} f g bur = record {
      fe=ge = fe=ge1 ;  
      k = k1 ;
      ek=h = λ {d} {h} {eq} → ek=h1 {d} {h} {eq} ;
      uniqueness  = λ {d} {h} {eq} {k'} ek=h → uniqueness1  {d} {h} {eq} {k'} ek=h
   } where
      c : Obj A
      c = equ bur f g
      e : Hom A c a
      e = α bur f g
      k1 :  {d : Obj A} (h : Hom A d a) → A [ A [ f o h ] ≈ A [ g o h ] ] → Hom A d c
      k1 {d} h fh=gh = β bur {d} {a} {b} f g h fh=gh
      fe=ge1 : A [ A [ f o (α bur f g ) ] ≈ A [ g o (α bur f g ) ] ]
      fe=ge1 = b1 bur f g
      ek=h1 : {d : Obj A}  → ∀ {h : Hom A d a} →  {eq : A [ A [ f  o  h ] ≈ A [ g  o h ] ] } →  A [ A [ (α bur f g )  o k1 {d} h eq ] ≈ h ]
      ek=h1 {d} {h} {eq} =  let open ≈-Reasoning (A) in
             begin
                 α bur f g  o k1 h eq 
             ≈⟨ assoc ⟩
                 (α bur f g o γ bur f g h) o δ bur (f o h) (g o h) eq
             ≈⟨ car (b2 bur f g) ⟩
                 ( h o α bur ( f o h ) ( g o h ) ) o δ bur (f o h) (g o h) eq
             ≈↑⟨ assoc ⟩
                   h o α bur (f o h) (g o h) o δ bur (f o h) (g o h) eq
             ≈⟨ cdr ( b3 bur (f o h) (g o h) eq ) ⟩
                   h o id d
             ≈⟨ idR ⟩
                 h 
             ∎

--         e             f
--    c  -------→ a ---------→ b
--    ^        .     ---------→
--    |      .            g
--    |k   .
--    |  . h
--    d

      postulate 
              uniqueness1 : {d : Obj A} →  ∀ {h : Hom A d a} →  {eq : A [ A [ f  o  h ] ≈ A [ g  o h ] ] } →  {k' : Hom A d c } →
                      A [ A [ (α bur f g ) o k' ] ≈ h ] → A [ k1 {d} h eq  ≈ k' ]
--       uniqueness1 {d} {h} {eq} {k'} ek=h =  
--              begin
--                 k1 {d} h eq
--              ≈⟨⟩
--                 γ bur f g h o δ bur (f o h) (g o h) eq
--              ≈⟨ ? ⟩  -- without locality, we cannot simply replace h with (α bur f g o k' 
--                 γ bur f g (α bur f g o k' ) o (δ bur ( f o ( α bur f g o k' )) ( g o ( α bur f g o k' )) (f1=gh (b1 bur f g )))
--              ≈⟨ b4 bur f g ⟩
--                 k'
--              ∎ 

-- end





