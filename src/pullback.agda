-- Pullback from product and equalizer
--
--
--                        Shinji KONO <kono@ie.u-ryukyu.ac.jp>
----

open import Category -- https://github.com/konn/category-agda
open import Level
module pullback { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) { c₁' c₂' ℓ' : Level} ( I : Category c₁' c₂' ℓ') ( Γ : Functor I A ) where

open import HomReasoning
open import cat-utility

--
-- Pullback from equalizer and product
--         f
--     a ------→ c
--     ^         ^
--  π1 |         |g
--     |         |
--    axb -----→ b
--     ^   π2
--     |
--     | e = equalizer (f π1) (g π1)
--     |
--     d <------------------ d'
--         k (π1' × π2' )

open Equalizer
open IsEqualizer
open IsProduct

pullback-from :  {a b c : Obj A}
      ( f : Hom A a c )    ( g : Hom A b c )
      ( eqa : {a b : Obj A} → (f g : Hom A a b)  → Equalizer A f g )
      ( prod : ( a b : Obj A ) → Product A a b ) → Pullback A f g
pullback-from  {a} {b} {c} f g eqa prod0 =  record {
         ab = d ;
         π1 = A [ π1 o e ] ;
         π2 = A [ π2 o e ] ;
         isPullback = record {
              commute = commute1 ;
              pullback = p1 ;
              π1p=π1 = λ {d} {π1'} {π2'} {eq} → π1p=π11  {d} {π1'} {π2'} {eq} ;
              π2p=π2 = λ {d} {π1'} {π2'} {eq} → π2p=π21  {d} {π1'} {π2'} {eq} ;
              uniqueness = uniqueness1
         }
      } where
      axb : Obj A
      axb =  Product.product (prod0 a b) 
      π1 : Hom A axb a
      π1 = Product.π1 (prod0 a b ) 
      π2 : Hom A axb b
      π2 = Product.π2 (prod0 a b ) 
      d : Obj A
      d = equalizer-c (eqa (A [ f o π1 ]) (A [ g o π2 ]))
      e : Hom A d axb 
      e = equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ]))
      prod = Product.isProduct (prod0 a b)
      commute1 :  A [ A [ f o A [ π1 o e ] ]
                    ≈ A [ g o A [ π2 o e ] ] ]
      commute1 = let open ≈-Reasoning (A) in
             begin
                    f o ( π1 o e )
             ≈⟨ assoc ⟩
                    ( f o  π1 ) o e 
             ≈⟨ fe=ge (isEqualizer (eqa (A [ f o π1 ]) (A [ g o π2 ]))) ⟩
                    ( g o  π2 ) o e 
             ≈↑⟨ assoc ⟩
                    g o ( π2 o e )
             ∎
      lemma1 :  {d' : Obj A} {π1' : Hom A d' a} {π2' : Hom A d' b} → A [ A [ f o π1' ] ≈ A [ g o π2' ] ] →
                      A [ A [ A [ f o π1 ] o (prod × π1') π2' ] ≈ A [ A [ g o π2 ] o (prod × π1') π2' ] ]
      lemma1  {d'} { π1' } { π2' } eq  = let open ≈-Reasoning (A) in
             begin
                    ( f o π1 ) o (prod × π1') π2'
             ≈↑⟨ assoc ⟩
                     f o ( π1  o (prod × π1') π2' )
             ≈⟨ cdr (π1fxg=f prod)  ⟩
                     f o  π1'
             ≈⟨ eq ⟩
                     g o  π2'
             ≈↑⟨ cdr (π2fxg=g prod)  ⟩
                     g o ( π2  o (prod × π1') π2'  )
             ≈⟨ assoc ⟩
                    ( g o π2 ) o (prod × π1') π2'
             ∎
      p1 :  {d' : Obj A} {π1' : Hom A d' a} {π2' : Hom A d' b} → A [ A [ f o π1' ] ≈ A [ g o π2' ] ] → Hom A d' d
      p1 {d'} { π1' } { π2' } eq  =
         let open ≈-Reasoning (A) in k (isEqualizer (eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ))) (_×_ prod  π1'  π2' ) ( lemma1 eq )
      π1p=π11 :   {d₁ : Obj A} {π1' : Hom A d₁ a} {π2' : Hom A d₁ b} {eq : A [ A [ f o π1' ] ≈ A [ g o π2' ] ]} →
            A [ A [ A [ π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ]) ) ] o p1 eq ] ≈ π1' ]
      π1p=π11 {d'} {π1'} {π2'} {eq} = let open ≈-Reasoning (A) in
             begin
                     ( π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ]) ) ) o p1 eq
             ≈⟨⟩
                     ( π1 o e) o  k (isEqualizer ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) )) (_×_ prod  π1'  π2' ) (lemma1 eq)
             ≈↑⟨ assoc ⟩
                      π1 o ( e o  k (isEqualizer ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) )) (_×_ prod  π1'  π2' ) (lemma1 eq) )
             ≈⟨ cdr ( ek=h  (isEqualizer ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] )  ))) ⟩
                      π1 o  (_×_ prod  π1'  π2' )
             ≈⟨ π1fxg=f prod ⟩
                     π1'
             ∎
      π2p=π21 : {d₁ : Obj A} {π1' : Hom A d₁ a} {π2' : Hom A d₁ b} {eq : A [ A [ f o π1' ] ≈ A [ g o π2' ] ]} →
            A [ A [ A [ π2 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ]) ) ] o p1 eq ] ≈ π2' ]
      π2p=π21  {d'} {π1'} {π2'} {eq} = let open ≈-Reasoning (A) in
             begin
                     ( π2 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ]) ) ) o p1 eq
             ≈⟨⟩
                     ( π2 o e) o  k (isEqualizer ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) )) (_×_ prod  π1'  π2' ) (lemma1 eq)
             ≈↑⟨ assoc ⟩
                      π2 o ( e o  k (isEqualizer ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) )) (_×_ prod  π1'  π2' ) (lemma1 eq) )
             ≈⟨ cdr ( ek=h  (isEqualizer ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] )  ))) ⟩
                      π2 o  (_×_ prod  π1'  π2' )
             ≈⟨ π2fxg=g prod ⟩
                     π2'
             ∎
      uniqueness1 :  {d₁ : Obj A} (p' : Hom A d₁ d) {π1' : Hom A d₁ a} {π2' : Hom A d₁ b} 
         {eq : A [ A [ f o π1' ] ≈ A [ g o π2' ] ]} →
        {eq1 : A [ A [ A [ π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) ] o p' ] ≈ π1' ]} →
        {eq2 : A [ A [ A [ π2 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) ] o p' ] ≈ π2' ]} →
        A [ p1 eq ≈ p' ]
      uniqueness1 {d'} p' {π1'} {π2'} {eq} {eq1} {eq2} = let open ≈-Reasoning (A) in
             begin
                 p1 eq
             ≈⟨⟩
                 k (isEqualizer ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) )) (_×_ prod  π1'  π2' ) (lemma1 eq)
             ≈⟨ IsEqualizer.uniqueness (isEqualizer (eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) )) ( begin
                 e o p'
             ≈⟨⟩
                  equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) o p'
             ≈↑⟨ IsProduct.uniqueness prod ⟩
                (prod × (  π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) o p') ) ( π2 o (equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) o p'))
             ≈⟨ ×-cong prod (assoc) (assoc) ⟩
                 (prod × (A [ A [ π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) ] o p' ]))
                         (A [ A [ π2 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) ] o p' ])
             ≈⟨ ×-cong prod eq1 eq2 ⟩
                ((prod × π1') π2')
             ∎ ) ⟩
                 p'
             ∎

--------------------------------
--
-- If we have two limits on c and c', there are isomorphic pair h, h'

open Limit
open IsLimit
open NTrans

iso-l :  { c₁' c₂' ℓ' : Level} ( I : Category c₁' c₂' ℓ' ) ( Γ : Functor I A )
       ( lim : Limit I A Γ ) → ( lim' :  Limit I A Γ )
      → Hom A (a0 lim )(a0 lim')
iso-l  I Γ  lim lim' = limit (isLimit lim') (a0 lim) ( t0 lim)

iso-r :  { c₁' c₂' ℓ' : Level} ( I : Category c₁' c₂' ℓ' ) ( Γ : Functor I A )
       ( lim : Limit I A Γ ) → ( lim' :  Limit I A Γ  )
      → Hom A (a0 lim') (a0 lim)
iso-r  I Γ lim lim' = limit (isLimit lim) (a0 lim') (t0 lim')


iso-lr :  { c₁' c₂' ℓ' : Level} ( I : Category c₁' c₂' ℓ' ) ( Γ : Functor I A )
       ( lim : Limit I A Γ ) → ( lim' :  Limit I A Γ  )  →
       ∀{ i : Obj I } → A [ A [ iso-l I Γ lim lim' o iso-r I Γ  lim lim'  ]  ≈ id1 A (a0 lim') ]
iso-lr  I Γ lim lim' {i} =  let open ≈-Reasoning (A) in begin
           iso-l I Γ lim lim' o iso-r I Γ lim lim'
      ≈⟨⟩
           limit (isLimit lim') (a0 lim) ( t0 lim) o  limit (isLimit lim) (a0 lim') (t0 lim')
      ≈↑⟨ limit-uniqueness (isLimit lim') ( λ {i} → ( begin
          TMap (t0 lim') i o ( limit (isLimit lim') (a0 lim) (t0 lim) o limit (isLimit lim) (a0 lim') (t0 lim') )
      ≈⟨ assoc  ⟩
          ( TMap (t0 lim') i o  limit (isLimit lim') (a0 lim) (t0 lim) ) o limit (isLimit lim) (a0 lim') (t0 lim')
      ≈⟨ car ( t0f=t (isLimit lim') ) ⟩
          TMap (t0 lim)  i o limit (isLimit lim) (a0 lim') (t0 lim')
      ≈⟨ t0f=t (isLimit lim) ⟩
          TMap (t0 lim') i
      ∎) ) ⟩
           limit (isLimit lim') (a0 lim') (t0 lim')
      ≈⟨ limit-uniqueness (isLimit lim')  idR ⟩
           id (a0 lim' )
      ∎



open import CatExponetial

open Functor

--------------------------------
--
-- Constancy Functor

KI : { c₁' c₂' ℓ' : Level} ( I : Category c₁' c₂' ℓ' ) →  Functor A ( A ^ I )
KI { c₁'} {c₂'} {ℓ'} I = record {
      FObj = λ a → K I A a ;
      FMap = λ f → record { --  NTrans I A (K I A a)  (K I A b)
            TMap = λ a → f ;
            isNTrans = record {
                 commute = λ {a b f₁} → commute1 {a} {b} {f₁} f
            }
        }  ;
        isFunctor = let  open ≈-Reasoning (A) in record {
               ≈-cong   = λ f=g {x} → f=g
             ; identity = refl-hom
             ; distr    = refl-hom
        }
  } where
     commute1 :  {a b : Obj I} {f₁ : Hom I a b} → {a' b' : Obj A} → (f : Hom A a' b' ) →
        A [ A [ FMap (K I A b') f₁ o f ] ≈ A [ f o FMap (K I A a') f₁ ] ]
     commute1 {a} {b} {f₁} {a'} {b'} f = let  open ≈-Reasoning (A) in begin
            FMap (K I A b') f₁ o f
        ≈⟨ idL ⟩
           f
        ≈↑⟨ idR ⟩
            f o FMap (K I A a') f₁
        ∎


---------
--
--   Limit    Constancy Functor F : A → A^I     has right adjoint
--
--   we are going to prove universal mapping

---------
--
-- limit gives co universal mapping ( i.e. adjunction )
--
--     F = KI I : Functor A (A ^ I)
--     U = λ b → A0 (lim b {a0 b} {t0 b}
--     ε = λ b → T0 ( lim b {a0 b} {t0 b} )
--
--     a0 : Obj A and t0 : NTrans K Γ come from the limit

limit2couniv :
     ( lim : ( Γ : Functor I A ) → Limit I A Γ )
     →  coUniversalMapping A ( A ^ I ) (KI I) 
limit2couniv lim  = record {  
       U = λ b → a0 ( lim b) ;
       ε = λ b → t0 (lim b) ;
       _*' = λ {b} {a} k → limit (isLimit (lim b )) a k ; 
       iscoUniversalMapping = record { couniversalMapping = λ{ b a f} → couniversalMapping1 {b} {a} {f} ;
           couniquness = couniquness2
       }
  } where
   couniversalMapping1 :  {b : Obj (A ^ I)} {a : Obj A} {f : Hom (A ^ I) (FObj (KI I) a) b} →
        A ^ I [ A ^ I [ t0 (lim b) o FMap (KI I) (limit (isLimit (lim b)) a f) ] ≈ f ]
   couniversalMapping1 {b} {a} {f} {i} = let  open ≈-Reasoning (A) in begin
            TMap (t0 (lim b )) i o TMap ( FMap (KI I) (limit (isLimit (lim b )) a f) ) i
        ≈⟨⟩
            TMap (t0 (lim b)) i o (limit (isLimit (lim b)) a f)
        ≈⟨ t0f=t (isLimit (lim b)) ⟩
            TMap f i  -- i comes from   ∀{i} → B [ TMap f i  ≈  TMap g i  ]
        ∎
   couniquness2 : {b : Obj (A ^ I)} {a : Obj A} {f : Hom (A ^ I) (FObj (KI I) a) b} {g : Hom A a (a0 (lim b ))} →
        ( ∀ { i : Obj I } → A [ A [ TMap (t0 (lim b )) i  o TMap ( FMap (KI I) g) i  ] ≈ TMap f i ] )
         → A [ limit (isLimit (lim b )) a f ≈ g ]
   couniquness2 {b} {a} {f} {g} lim-g=f  =  let  open ≈-Reasoning (A) in begin
            limit (isLimit (lim b )) a f
        ≈⟨ limit-uniqueness (isLimit ( lim b )) lim-g=f ⟩
            g
        ∎

univ2limit :
     ( univ :   coUniversalMapping A (A ^ I) (KI I) ) →
     ( Γ : Functor I A ) →   Limit I A Γ 
univ2limit univ Γ = record {
     a0 = (coUniversalMapping.U univ ) Γ  ;
     t0 = (coUniversalMapping.ε univ ) Γ  ;
     isLimit = record {
             limit = λ a t → limit1 a t ;
             t0f=t = λ {a t i } → t0f=t1 {a} {t} {i}  ;
             limit-uniqueness =  λ {a} {t} {f} t=f → limit-uniqueness1 {a} {t} {f} t=f
     }
 } where
     U : Obj (A ^ I) → Obj A  
     U b = coUniversalMapping.U univ b
     ε : ( b : Obj (A ^ I ) ) → NTrans I A (FObj (KI I) (U b)) b 
     ε b = coUniversalMapping.ε univ b
     limit1 :  (a : Obj A) → NTrans I A (FObj (KI I) a) Γ → Hom A a (U Γ)
     limit1 a t = coUniversalMapping._*' univ {_} {a} t
     t0f=t1 :   {a : Obj A} {t : NTrans I A (K I A a) Γ}  {i : Obj I} →
                A [ A [ TMap (ε Γ) i o limit1 a t ] ≈ TMap t i ]
     t0f=t1 {a} {t} {i} =  let  open ≈-Reasoning (A) in begin
            TMap (ε Γ) i o limit1 a t
        ≈⟨⟩
            TMap (ε Γ) i o coUniversalMapping._*' univ t
        ≈⟨ coIsUniversalMapping.couniversalMapping ( coUniversalMapping.iscoUniversalMapping univ) {Γ} {a} {t} ⟩
            TMap t i
        ∎
     limit-uniqueness1 : { a : Obj A } →  { t : NTrans I A ( K I A a ) Γ } → { f : Hom A a (U Γ)}
         → ( ∀ { i : Obj I } → A [ A [ TMap  (ε Γ) i o  f ]  ≈ TMap t i ] ) → A [ limit1 a t ≈ f ]
     limit-uniqueness1 {a} {t} {f} εf=t = let  open ≈-Reasoning (A) in begin
            coUniversalMapping._*' univ t
        ≈⟨  ( coIsUniversalMapping.couniquness ( coUniversalMapping.iscoUniversalMapping univ) ) εf=t  ⟩
            f
        ∎



-- another form of uniqueness of a product
lemma-p0 :   (a b ab : Obj A) ( π1 : Hom A ab a ) ( π2 : Hom A ab b ) ( prod : IsProduct A a b ab π1 π2 ) →
      A [ _×_ prod π1 π2 ≈  id1 A ab  ]
lemma-p0  a b ab π1 π2 prod =  let  open ≈-Reasoning (A) in begin
             _×_ prod π1 π2
         ≈↑⟨ ×-cong prod idR idR ⟩
             _×_ prod (A [ π1 o id1 A ab ]) (A [ π2 o id1 A ab ])
         ≈⟨ IsProduct.uniqueness prod ⟩
             id1 A ab 
         ∎


open IProduct
open IsIProduct
open Equalizer

--
-- limit from equalizer and product
--
--              Γu
--            → Γj → Γk ←   
--           /   ↑   ↑   \     
-- proj j   /    |   |    \ proj k
--         /   μu|   |μu   \           Equalizer have to be independent from j and k
--        |      |   |      |            so we need products of Obj I and Hom I
--        |product of Hom I |   
--        |      ↑   ↑      |                    K u = id lim                        
--        |      }   |      |                       
--        | f(id)|   |g(Γ)  |            lim = K j -----------→ K k = lim
--        |      |   |      |                   |      u        |
--         \     |   |     /   proj j o e = ε j |               | ε k = proj k o e
--         product of Obj I       μ  u o g o e  |               | μ  u o f o e
--        ↑                                     |               |
--        | e = equalizer f g                   |               |
--        |                                     ↓               ↓
--       lim ←---------------- d'              Γ j ----------→ Γ k 
--              k ( product pi )                     Γ u
--                                              Γ u o ε j = ε k 
--

-- homprod should be written by IProduct
-- If I is locally small, this is iso to a set
record homprod {c : Level } : Set (suc c₁' ⊔ suc c₂' ) where
   field
      hom-j : Obj I
      hom-k : Obj I
      hom : Hom I hom-j hom-k
open homprod

Homprod : {j k : Obj I} (u : Hom I j k) → homprod {c₁}
Homprod {j} {k} u = record {hom-j = j ; hom-k = k ; hom = u}

limit-from :
     ( prod :  {c : Level} { I : Set c } → ( ai : I → Obj A ) →  IProduct I A ai )
     ( eqa : {a b : Obj A} → (f g : Hom A a b)  → Equalizer A f g )
      → Limit I A Γ 
limit-from prod eqa = record {
     a0 = d ;
     t0 = cone-ε ; 
     isLimit = record {
             limit = λ a t → cone1 a t ;
             t0f=t = λ {a t i } → t0f=t1  {a} {t} {i} ;
             limit-uniqueness =  λ {a} {t} {f} t=f → limit-uniqueness1 {a} {t} {f} t=f
     }
    }  where
         p0 : Obj A 
         p0 = iprod (prod (FObj Γ))
         Fcod : homprod {c₁} → Obj A
         Fcod = λ  u →  FObj Γ ( hom-k u )
         f : Hom A p0 (iprod (prod Fcod))
         f =  iproduct (isIProduct (prod Fcod)) (λ u → pi (prod (FObj Γ)) (hom-k u ))
         g : Hom A p0 (iprod (prod Fcod))
         g =  iproduct (isIProduct (prod Fcod)) (λ u → A [ FMap Γ (hom u) o pi (prod (FObj Γ)) (hom-j u ) ] )
         equ-ε : Equalizer A g f
         equ-ε = eqa g f
         d :  Obj A
         d  = equalizer-c equ-ε  
         e : Hom A d p0
         e = equalizer equ-ε 
         equ = isEqualizer  equ-ε 
         -- projection of the product of Obj I
         proj : (i : Obj I) → Hom A p0 (FObj Γ i)
         proj = pi ( prod  (FObj Γ) )
         prodΓ = isIProduct ( prod (FObj Γ) ) 
         -- projection of the product of Hom I
         μ  : {j k : Obj I} → (u : Hom I j k ) → Hom A (iprod (prod Fcod)) (Fcod (Homprod u))
         μ  u = pi (prod Fcod ) (Homprod u) 
         cone-ε :  NTrans I A (K I A (equalizer-c equ-ε ) ) Γ
         cone-ε = record {
               TMap = λ i → tmap i ; 
               isNTrans = record { commute = commute1 }
           } where
               tmap : (i : Obj I) → Hom A (FObj (K I A d) i) (FObj Γ i)
               tmap i = A [ proj i o e ] 
               commute1 :  {j k : Obj I} {u : Hom I j k} →
                 A [ A [ FMap Γ u o tmap j ] ≈ A [ tmap k o FMap (K I A d) u ] ]
               commute1 {j} {k} {u} =  let  open ≈-Reasoning (A) in begin
                      FMap Γ u o tmap j 
                 ≈⟨⟩
                      FMap Γ u o ( proj j o e )
                 ≈⟨ assoc ⟩
                      ( FMap Γ u o  pi (prod (FObj Γ)) j ) o e 
                 ≈↑⟨ car ( pif=q (isIProduct (prod Fcod )) ) ⟩
                     ( μ  u o g ) o e 
                 ≈↑⟨ assoc ⟩
                       μ  u o (g  o e )
                 ≈⟨ cdr ( fe=ge (isEqualizer equ-ε )) ⟩
                       μ  u o (f  o e )
                 ≈⟨ assoc ⟩
                     (μ  u o f ) o e 
                 ≈⟨ car ( pif=q (isIProduct (prod Fcod )))   ⟩
                       pi (prod (FObj Γ)) k o e 
                 ≈⟨⟩
                      proj k o e 
                 ≈↑⟨ idR ⟩
                      (proj k o e ) o id1 A d
                 ≈⟨⟩
                      tmap k o FMap (K I A d) u
                 ∎ 
         --  an arrow to our product of Obj I ( is an equalizer because of commutativity of t )
         h : {a : Obj A} → (t : NTrans I A (K I A a) Γ ) → Hom A a p0
         h t = iproduct prodΓ (TMap t) 
         fh=gh : (a : Obj A) → (t : NTrans I A (K I A a) Γ ) →
            A [ A [ g o h t ] ≈ A [ f o h t ] ]
         fh=gh a t = let  open ≈-Reasoning (A) in begin
                  g o h t
                ≈↑⟨ ip-uniqueness (isIProduct (prod Fcod)) ⟩
                  iproduct (isIProduct (prod Fcod)) (λ u →  pi (prod Fcod) u o ( g o h t ))
                ≈⟨ ip-cong  (isIProduct (prod Fcod)) ( λ u →  begin
                            pi (prod Fcod) u o ( g o h t )
                        ≈⟨ assoc ⟩
                            ( pi (prod Fcod) u o  g ) o h t
                        ≈⟨ car (pif=q  (isIProduct (prod Fcod ))) ⟩
                            (FMap Γ (hom u) o  pi (prod (FObj Γ)) (hom-j u) )  o h t
                        ≈↑⟨ assoc ⟩
                            FMap Γ (hom u) o (pi (prod (FObj Γ)) (hom-j u)   o h t )
                        ≈⟨ cdr ( pif=q prodΓ ) ⟩
                            FMap Γ (hom u) o TMap t (hom-j u)
                        ≈⟨ IsNTrans.commute (isNTrans t) ⟩
                            TMap t (hom-k u) o id1 A a
                        ≈⟨ idR ⟩
                            TMap t (hom-k u) 
                        ≈↑⟨  pif=q prodΓ  ⟩
                           pi (prod (FObj Γ)) (hom-k u) o h t
                        ≈↑⟨ car (pif=q  (isIProduct (prod Fcod ))) ⟩
                            (pi (prod Fcod) u o  f ) o h t
                        ≈↑⟨ assoc ⟩
                            pi (prod Fcod) u o ( f o h t )
                        ∎
                 ) ⟩
                  iproduct (isIProduct (prod Fcod)) (λ u →  pi (prod Fcod) u o ( f o h t ))
                ≈⟨ ip-uniqueness (isIProduct (prod Fcod)) ⟩
                  f o h t
                ∎
         cone1 :  (a : Obj A) → NTrans I A (K I A a) Γ → Hom A a d
         cone1 a t =  k equ (h t) ( fh=gh a t )
         t0f=t1 :  {a : Obj A} {t : NTrans I A (K I A a) Γ} {i : Obj I} →
                A [ A [ TMap cone-ε  i o cone1 a t ] ≈ TMap t i ]
         t0f=t1 {a} {t} {i} = let  open ≈-Reasoning (A) in begin
                   TMap cone-ε  i o cone1 a t 
                ≈⟨⟩
                   ( ( proj i )  o e ) o  k equ (h t) (fh=gh a t)
                ≈↑⟨ assoc  ⟩
                    proj i  o ( e  o  k equ (h t) (fh=gh a t ) )
                ≈⟨ cdr ( ek=h equ) ⟩
                    proj i  o h t
                ≈⟨ pif=q prodΓ ⟩
                   TMap t i 
                ∎
         limit-uniqueness1 :  {a : Obj A} {t : NTrans I A (K I A a) Γ} {f : Hom A a d} 
                → ({i : Obj I} → A [ A [ TMap cone-ε  i o f ] ≈ TMap t i ]) →
                A [ cone1 a t ≈ f ]
         limit-uniqueness1 {a} {t} {f} lim=t = let  open ≈-Reasoning (A) in begin
                    cone1 a t
                ≈⟨⟩
                    k equ (h t) (fh=gh a t)
                ≈⟨ IsEqualizer.uniqueness  equ ( begin
                      e o f 
                ≈↑⟨ ip-uniqueness prodΓ ⟩
                      iproduct prodΓ (λ i → ( proj i o ( e  o f ) ) )
                ≈⟨ ip-cong  prodΓ ( λ i → begin
                        proj i o ( e o f )
                ≈⟨ assoc  ⟩
                        ( proj i o  e ) o f 
                ≈⟨ lim=t {i} ⟩
                        TMap t i
                ∎ ) ⟩
                      h t
                ∎ ) ⟩
                    f
                ∎


--
--
-- Adjoint functor preserves limits
--
--      

open import Category.Cat

ta1 : { c₁' c₂' ℓ' : Level}  (B : Category c₁' c₂' ℓ') ( Γ : Functor I B ) 
     ( lim : Obj B ) ( tb : NTrans I B ( K I B lim ) Γ ) → 
         ( U : Functor B A)  → NTrans I A ( K I A (FObj U lim) ) (U  ○  Γ)
ta1 B Γ lim tb U = record {
               TMap  = TMap (Functor*Nat I A U tb) ; 
               isNTrans = record { commute = λ {a} {b} {f} → let  open ≈-Reasoning (A) in begin
                     FMap (U ○ Γ) f o TMap (Functor*Nat I A U tb) a 
                 ≈⟨ nat ( Functor*Nat I A U tb ) ⟩
                     TMap (Functor*Nat I A U tb) b o FMap (U ○ K I B lim) f 
                 ≈⟨ cdr (IsFunctor.identity (isFunctor U) ) ⟩
                     TMap (Functor*Nat I A U tb) b o FMap (K I A (FObj U lim)) f
                 ∎
               } }
 
adjoint-preseve-limit :
     { c₁' c₂' ℓ' : Level}  (B : Category c₁' c₂' ℓ') ( Γ : Functor I B ) ( limitb : Limit I B Γ ) →
       ( adj : Adjunction A B ) →  Limit I A (Adjunction.U adj ○ Γ) 
adjoint-preseve-limit B Γ limitb adj = record {
     a0 = FObj U lim ;
     t0 = ta1 B Γ lim tb U ;
     isLimit = record {
             limit = λ a t → limit1 a t ;
             t0f=t = λ {a t i } → t0f=t1 {a} {t} {i}  ;
             limit-uniqueness =  λ {a} {t} {f} t=f → limit-uniqueness1 {a} {t} {f} t=f
     }
    } where
         U : Functor B A
         U = Adjunction.U adj
         F : Functor A B 
         F = Adjunction.F adj
         η : NTrans A A identityFunctor ( U ○ F ) 
         η = Adjunction.η adj
         ε : NTrans B B  ( F ○  U ) identityFunctor  
         ε = Adjunction.ε adj
         ta = ta1 B Γ (a0 limitb) (t0 limitb) U
         tb = t0 limitb
         lim = a0 limitb
         tfmap : (a : Obj A) → NTrans I A (K I A a) (U ○ Γ) → (i : Obj I) → Hom B (FObj (K I B (FObj F a)) i) (FObj Γ i)
         tfmap a t i  = B [ TMap ε (FObj Γ i) o FMap F (TMap t i) ]
         tF :  (a : Obj A) → NTrans I A (K I A a) (U ○ Γ) →  NTrans I B (K I B (FObj F a)) Γ
         tF a t = record {
             TMap = tfmap a t ; 
             isNTrans = record { commute = λ {a'} {b} {f} → let  open ≈-Reasoning (B) in begin
                  FMap Γ f o tfmap a t a' 
               ≈⟨⟩
                  FMap Γ f o ( TMap ε (FObj Γ a') o FMap F (TMap t a'))
               ≈⟨ assoc ⟩
                  (FMap Γ f o  TMap ε (FObj Γ a') ) o FMap F (TMap t a')
               ≈⟨ car (nat ε) ⟩
                  (TMap ε (FObj Γ b) o FMap (F ○ U) (FMap Γ f) ) o FMap F (TMap t a')
               ≈↑⟨ assoc ⟩
                  TMap ε (FObj Γ b) o ( FMap (F ○ U) (FMap Γ f)  o FMap F (TMap t a') )
               ≈↑⟨ cdr ( distr F ) ⟩
                  TMap ε (FObj Γ b) o ( FMap F (A [ FMap U (FMap Γ f) o TMap t a' ] ) )
               ≈⟨ cdr ( fcong F (nat t) ) ⟩
                  TMap ε (FObj Γ b) o  FMap F (A [ TMap t b o FMap (K I A a) f ])
               ≈⟨⟩
                  TMap ε (FObj Γ b) o  FMap F (A [ TMap t b o id1 A (FObj (K I A a) b) ])
               ≈⟨ cdr ( fcong F (idR1 A)) ⟩
                  TMap ε (FObj Γ b) o  FMap F (TMap t b )
               ≈↑⟨ idR ⟩
                  ( TMap ε (FObj Γ b)  o  FMap F (TMap t b))  o  id1 B (FObj F (FObj (K I A a) b))
               ≈⟨⟩
                  tfmap a t b o FMap (K I B (FObj F a)) f 
               ∎
          } }
         limit1 :  (a : Obj A) → NTrans I A (K I A a) (U ○ Γ) → Hom A a (FObj U (a0 limitb) )
         limit1 a t = A [ FMap U (limit (isLimit limitb) (FObj F a) (tF a t )) o TMap η a ]
         t0f=t1 :  {a : Obj A} {t : NTrans I A (K I A a) (U ○ Γ)} {i : Obj I} →
                A [ A [ TMap ta i o limit1 a t ] ≈ TMap t i ]
         t0f=t1 {a} {t} {i} = let  open ≈-Reasoning (A) in  begin
                 TMap ta i o limit1 a t 
               ≈⟨⟩
                  FMap U ( TMap tb i )  o ( FMap U (limit (isLimit limitb) (FObj F a) (tF a t )) o TMap η a  )
               ≈⟨ assoc ⟩
                  ( FMap U ( TMap tb i )  o  FMap U (limit (isLimit limitb) (FObj F a) (tF a t ))) o TMap η a  
               ≈↑⟨ car ( distr U ) ⟩
                  FMap U ( B [ TMap tb i  o limit (isLimit limitb) (FObj F a) (tF a t ) ] ) o TMap η a  
               ≈⟨ car ( fcong U ( t0f=t (isLimit limitb) ) ) ⟩
                  FMap U (TMap (tF a t) i) o TMap η a  
               ≈⟨⟩
                  FMap U ( B [ TMap ε (FObj Γ i) o FMap F (TMap t i) ] ) o TMap η a  
               ≈⟨ car ( distr U ) ⟩
                  ( FMap U ( TMap ε (FObj Γ i))  o FMap U ( FMap F (TMap t i) )) o TMap η a  
               ≈↑⟨ assoc ⟩
                   FMap U ( TMap ε (FObj Γ i) ) o ( FMap U ( FMap F (TMap t i) ) o TMap η a   )
               ≈⟨ cdr ( nat η ) ⟩
                    FMap U (TMap ε (FObj Γ i)) o (  TMap η (FObj U (FObj Γ i)) o FMap (identityFunctor {_} {_} {_} {A}) (TMap t i) )
               ≈⟨ assoc ⟩
                    ( FMap U (TMap ε (FObj Γ i)) o   TMap η (FObj U (FObj Γ i))) o TMap t i
               ≈⟨ car ( IsAdjunction.adjoint1 ( Adjunction.isAdjunction adj ) ) ⟩
                 id1 A (FObj (U ○ Γ) i) o TMap t i
               ≈⟨ idL ⟩
                 TMap t i
               ∎
         -- ta = TMap (Functor*Nat I A U tb) , FMap U ( TMap tb i )  o f  ≈ TMap t i
         limit-uniqueness1 :  {a : Obj A} {t : NTrans I A (K I A a) (U ○ Γ)} {f : Hom A a (FObj U lim)} 
                → ({i : Obj I} → A [ A [ TMap ta i o f ] ≈ TMap t i ]) →
                A [ limit1 a t ≈ f ]
         limit-uniqueness1 {a} {t} {f} lim=t = let  open ≈-Reasoning (A) in  begin
                 limit1 a t
               ≈⟨⟩
                 FMap U (limit (isLimit limitb) (FObj F a) (tF a t )) o TMap η a  
               ≈⟨ car ( fcong U (limit-uniqueness (isLimit limitb)  ( λ {i} →  lemma1 i) )) ⟩
                 FMap U ( B [ TMap ε lim o FMap F f ] ) o TMap η a   -- Universal mapping 
               ≈⟨ car (distr U ) ⟩
                 ( (FMap U (TMap ε lim))  o (FMap U ( FMap F f )) ) o TMap η a
               ≈⟨ sym assoc ⟩
                  (FMap U (TMap ε lim))  o ((FMap U ( FMap F f ))  o TMap η a )
               ≈⟨ cdr (nat η) ⟩
                  (FMap U (TMap ε lim))  o ((TMap η (FObj U lim )) o f )
               ≈⟨ assoc ⟩
                  ((FMap U (TMap ε lim))  o (TMap η (FObj U lim)))  o f
               ≈⟨ car ( IsAdjunction.adjoint1 ( Adjunction.isAdjunction adj))  ⟩
                  id (FObj U lim) o f
               ≈⟨  idL  ⟩
                  f
               ∎ where
                  lemma1 : (i : Obj I) → B [ B [ TMap tb i o B [ TMap ε lim  o FMap F f ] ] ≈ TMap (tF a t) i ]
                  lemma1 i =  let  open ≈-Reasoning (B) in  begin
                          TMap tb i o (TMap ε lim  o FMap F f)
                       ≈⟨ assoc ⟩
                          ( TMap tb i o TMap ε lim  ) o FMap F f
                       ≈⟨ car ( nat ε ) ⟩
                          ( TMap ε (FObj Γ i) o  FMap F ( FMap U ( TMap tb i )))  o FMap F f 
                       ≈↑⟨ assoc  ⟩
                          TMap ε (FObj Γ i) o  ( FMap F ( FMap U ( TMap tb i ))  o FMap F f )
                       ≈↑⟨ cdr ( distr F )  ⟩
                          TMap ε (FObj Γ i) o  FMap F ( A [ FMap U ( TMap tb i )  o f ] ) 
                       ≈⟨ cdr ( fcong F (lim=t {i}) ) ⟩
                          TMap ε (FObj Γ i) o FMap F (TMap t i) 
                       ≈⟨⟩
                          TMap (tF a t) i  
                       ∎ 

     

