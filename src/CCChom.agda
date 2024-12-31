{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Category 
module CCChom where

open import HomReasoning
open import Definitions
open import Data.Product renaming (_×_ to _/\_  ) hiding ( <_,_> )
open import Category.Constructions.Product
open  import  Relation.Binary.PropositionalEquality hiding ( [_] )

open Functor

--  CCC satisfies   hom natural iso
--   ccc-1 : Hom A a 1 ≅ {*}
--   ccc-2 : Hom A c (a × b) ≅ (Hom A c a ) × ( Hom A c b )
--   ccc-3 : Hom A a (c ^ b) ≅ Hom A (a × b) c

data One  : Set where
  OneObj : One   -- () in Haskell ( or any one object set )

OneCat : Category Level.zero Level.zero Level.zero
OneCat = record {
    Obj  = One ;
    Hom = λ a b →   One  ;
    _o_ =  λ{a} {b} {c} x y → OneObj ;
    _≈_ =  λ x y → x ≡ y ;
    Id  =  λ{a} → OneObj ;
    isCategory  = record {
            isEquivalence =  record {refl = refl ; trans = trans ; sym = sym } ;
            identityL  = λ{a b f} → lemma {a} {b} {f} ;
            identityR  = λ{a b f} → lemma {a} {b} {f} ;
            o-resp-≈  = λ{a b c f g h i} _ _ →  refl ;
            associative  = λ{a b c d f g h } → refl 
       }
   }  where
         lemma : {a b : One } → { f : One } →  OneObj ≡ f
         lemma {a} {b} {f} with f
         ... | OneObj = refl

record IsCCChom {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (１ : Obj A) 
          ( _*_ : Obj A → Obj A → Obj A  ) ( _^_ : Obj A → Obj A → Obj A  ) :  Set ( c₁  ⊔  c₂ ⊔ ℓ ) where
     field
       ccc-1 : {a : Obj A} {b c : Obj OneCat}   →  --   Hom A a １ ≅ {*}
                          IsoS A OneCat a １ b c
       ccc-2 : {a b c : Obj A} →  --  Hom A c ( a * b ) ≅ ( Hom A c a ) * ( Hom A c b )
                          IsoS A (A × A)  c (a * b) (c , c ) (a , b )
       ccc-3 : {a b c : Obj A} →  -- Hom A a ( c ^ b ) ≅ Hom A ( a * b ) c
                          IsoS A A  a (c ^ b) (a * b) c
       nat-2 : {a b c  : Obj A} → {f : Hom A (b * c) (b * c) } → {g : Hom A a (b * c) }
                 → (A × A) [ (A × A) [ IsoS.≅→ ccc-2 f o (g , g) ] ≈  IsoS.≅→ ccc-2 ( A [ f o g ] ) ]
       nat-3 : {a b c : Obj A} → { k : Hom A c (a ^ b ) } → A [ A [  IsoS.≅→ (ccc-3) (id1 A (a ^ b)) o
                    (IsoS.≅← (ccc-2 ) (A [ k o (proj₁ ( IsoS.≅→ ccc-2  (id1 A (c *  b)))) ] ,
                        (proj₂ ( IsoS.≅→ ccc-2  (id1 A (c *  b) ))))) ] ≈ IsoS.≅→ (ccc-3 ) k ]

open import CCC
        
record CCChom {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) :  Set ( c₁  ⊔  c₂ ⊔ ℓ ) where
     field
       one : Obj A
       _*_ : Obj A → Obj A → Obj A
       _^_ : Obj A → Obj A → Obj A  
       isCCChom : IsCCChom A one   _*_ _^_

open import HomReasoning 

CCC→hom : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) ( c : CCC A ) 
   → (CCCcong : IsCCC-*-cong A _ _ _ _ _ _ _ _ _ (CCC.isCCC c))
   → CCChom A
CCC→hom A c ccong = record {
       one = CCC.１ c
     ; _*_ = CCC._∧_ c 
     ; _^_ = CCC._<=_ c
     ; isCCChom = record {
            ccc-1 =  λ {a} {b} {c'} → record {   ≅→ =  c101  ; ≅← = c102  ; iso→  = c103 {a} {b} {c'} ; iso←  = c104 ; cong← = c105 ; cong→ = c106 }
          ; ccc-2 =  record {   ≅→ =  c201 ; ≅← = c202 ; iso→  = c203 ; iso←  = c204  ; cong← = c205; cong→ = c206 }
          ; ccc-3 =   record {   ≅→ =  c301 ; ≅← = c302 ; iso→  = c303 ; iso←  = c304 ; cong← = c305 ; cong→ = c306 }
          ; nat-2 = nat-2 ; nat-3 = nat-3
        }
   } module CCC→HOM where
      c101 : {a : Obj A} → Hom A a (CCC.１ c) → Hom OneCat OneObj OneObj
      c101 _  = OneObj
      c102 : {a : Obj A} → Hom OneCat OneObj OneObj → Hom A a (CCC.１ c)
      c102 {a} OneObj = CCC.○ c a
      c103 : {a : Obj A } {b c : Obj OneCat} {f : Hom OneCat b b } → _[_≈_] OneCat {b} {c} ( c101 {a} (c102 {a} f) ) f 
      c103 {a} {OneObj} {OneObj} {OneObj} = refl
      c104 : {a : Obj A} →  {f : Hom A a (CCC.１ c)} → A [ (c102 ( c101 f )) ≈ f ]
      c104 {a} {f} = let  open  ≈-Reasoning A in HomReasoning.≈-Reasoning.sym A (IsCCC.e2 (CCC.isCCC c)  ) 
      c201 :  { c₁ a b  : Obj A} → Hom A c₁ ((c CCC.∧ a) b) → Hom (A × A) (c₁ , c₁) (a , b)
      c201 f = ( A [ CCC.π c o f ]  , A  [ CCC.π' c o f ] )
      c202 :  { c₁ a b  : Obj A} → Hom (A × A) (c₁ , c₁) (a , b) → Hom A c₁ ((c CCC.∧ a) b)
      c202 (f , g ) = CCC.<_,_> c f g 
      c203 : { c₁ a b  : Obj A} → {f : Hom (A × A) (c₁ , c₁) (a , b)} → (A × A) [ (c201 ( c202 f )) ≈ f ]
      c203 = ( IsCCC.e3a (CCC.isCCC c) , IsCCC.e3b (CCC.isCCC c))
      c204 : { c₁ a b  : Obj A} → {f : Hom A c₁ ((c CCC.∧ a) b)} → A [ (c202 ( c201 f ))  ≈ f ]
      c204 = IsCCC.e3c (CCC.isCCC c)
      c301 :  { d a b  : Obj A} → Hom A a ((c CCC.<= d) b) → Hom A ((c CCC.∧ a) b) d  --   a -> d <= b  -> (a ∧ b ) -> d
      c301 {d} {a} {b} f = A [ CCC.ε c o  CCC.<_,_> c ( A [ f o CCC.π c ] ) ( CCC.π' c )  ]
      c302 : { d a b  : Obj A} →  Hom A ((c CCC.∧ a) b) d → Hom A a ((c CCC.<= d) b)
      c302 f = CCC._* c f
      c303 : { c₁ a b  : Obj A} →  {f : Hom A ((c CCC.∧ a) b) c₁} → A [  (c301 ( c302 f ))  ≈ f ]
      c303 = IsCCC.e4a (CCC.isCCC c)
      c304 : { c₁ a b  : Obj A} →  {f : Hom A a ((c CCC.<= c₁) b)} → A [ (c302 ( c301 f ))  ≈ f ]
      c304 = IsCCC.e4b (CCC.isCCC c)
      c105 :  {a : Obj A } {f g : Hom OneCat OneObj OneObj} → _[_≈_] OneCat {OneObj} {OneObj} f g → A [ c102 {a} f ≈ c102 {a} g ]
      c105 refl = let  open  ≈-Reasoning A in refl-hom
      c106 : { a  : Obj A }  {f g : Hom A a (CCC.１ c)} → A [ f ≈ g ] → _[_≈_] OneCat {OneObj} {OneObj}  OneObj  OneObj 
      c106 _ = refl
      c205  : { a b c₁ : Obj A } {f g : Hom (A × A) (c₁ , c₁) (a , b)} → (A × A) [ f ≈ g ] → A [ c202 f ≈ c202 g ]
      c205  f=g = IsCCC.π-cong (CCC.isCCC c ) (proj₁ f=g ) (proj₂ f=g )
      c206  : { a b c₁ : Obj A } {f g : Hom A c₁ ((c CCC.∧ a) b)} → A [ f ≈ g ] → (A × A) [ c201 f ≈ c201 g ]
      c206 {a} {b} {c₁} {f} {g}  f=g = ( begin
                      CCC.π c o f 
                  ≈⟨ cdr f=g   ⟩
                      CCC.π c o g
                  ∎ ) , ( begin
                      CCC.π' c o f 
                  ≈⟨ cdr  f=g   ⟩
                      CCC.π' c o g 
                  ∎ ) where open ≈-Reasoning A
      c305  : { a b  c₁ : Obj A } {f g : Hom A ((c CCC.∧ a) b) c₁} → A [ f ≈ g ] → A [ (c CCC.*) f ≈ (c CCC.*) g ]
      c305  f=g = IsCCC-*-cong.*-cong ccong f=g
      c306  : { a b  c₁ : Obj A } {f g : Hom A a ((c CCC.<= c₁) b)} → A [ f ≈ g ] → A [ c301 f ≈ c301 g ]
      c306  {a} {b} {c₁} {f} {g} f=g =  begin
                       CCC.ε c o  CCC.<_,_> c (  f o CCC.π c ) ( CCC.π' c ) 
                  ≈⟨ cdr ( IsCCC.π-cong (CCC.isCCC c ) (car f=g )  refl-hom)  ⟩
                       CCC.ε c o  CCC.<_,_> c (  g o CCC.π c ) ( CCC.π' c ) 
                  ∎  where open ≈-Reasoning A
      nat-2 :  {a b : Obj A} {c = c₁ : Obj A} {f : Hom A ((c CCC.∧ b) c₁) ((c CCC.∧ b) c₁)}
            {g : Hom A a ((c CCC.∧ b) c₁)} → (A × A) [ (A × A) [ c201 f o g , g ] ≈ c201 (A [ f o g ]) ]
      nat-2 {a} {b} {c₁} {f} {g} =   ( begin
                 ( CCC.π c  o f) o g    
             ≈↑⟨ assoc ⟩
                 ( CCC.π c ) o (f o g)  
             ∎ ) , (sym-hom assoc) where open ≈-Reasoning A
      nat-3 : {a b : Obj A} {c = c₁ : Obj A} {k : Hom A c₁ ((c CCC.<= a) b)} →
            A [ A [ c301 (id1 A ((c CCC.<= a) b)) o c202 (A [ k o proj₁ (c201 (id1 A ((c CCC.∧ c₁) b))) ] , proj₂ (c201 (id1 A ((c CCC.∧ c₁) b)))) ]
            ≈ c301 k ]
      nat-3 {a} {b} { c₁} {k} =  begin
                 c301 (id1 A ((c CCC.<= a) b)) o c202 ( k o proj₁ (c201 (id1 A ((c CCC.∧ c₁) b)))  , proj₂ (c201 (id1 A ((c CCC.∧ c₁) b)))) 
             ≈⟨⟩
                  ( CCC.ε c o CCC.<_,_> c ((id1 A (CCC._<=_ c a b )) o CCC.π c) (CCC.π' c))
                     o (CCC.<_,_> c (k o ( CCC.π c o (id1 A (CCC._∧_ c c₁ b )))) ( CCC.π' c o (id1 A (CCC._∧_ c c₁ b))))
             ≈↑⟨ assoc ⟩
                 (CCC.ε c) o ((  CCC.<_,_> c ((id1 A (CCC._<=_ c a b )) o CCC.π c) (CCC.π' c))
                     o (CCC.<_,_> c (k o ( CCC.π c o (id1 A (CCC._∧_ c c₁ b )))) ( CCC.π' c o (id1 A (CCC._∧_ c c₁ b)))))
             ≈⟨ cdr (car (IsCCC.π-cong (CCC.isCCC c ) idL refl-hom ) )   ⟩
                 (CCC.ε c) o (  CCC.<_,_> c (CCC.π c) (CCC.π' c)
                     o (CCC.<_,_> c (k o ( CCC.π c o (id1 A (CCC._∧_ c c₁ b )))) ( CCC.π' c o (id1 A (CCC._∧_ c c₁ b)))))
             ≈⟨ cdr (car (IsCCC.π-id (CCC.isCCC c)))   ⟩
                 (CCC.ε c) o ( id1 A (CCC._∧_ c ((c CCC.<= a) b) b )
                     o (CCC.<_,_> c (k o ( CCC.π c o (id1 A (CCC._∧_ c c₁ b )))) ( CCC.π' c o (id1 A (CCC._∧_ c c₁ b)))))
             ≈⟨ cdr ( cdr ( IsCCC.π-cong (CCC.isCCC c) (cdr idR) idR )) ⟩
                 (CCC.ε c) o ( id1 A (CCC._∧_ c ((c CCC.<= a) b) b ) o (CCC.<_,_> c (k o ( CCC.π c )) ( CCC.π' c )))
             ≈⟨ cdr idL  ⟩
                 (CCC.ε c) o (CCC.<_,_> c  ( k o  (CCC.π c) ) (CCC.π' c))
             ≈⟨⟩
                 c301 k
             ∎ where open ≈-Reasoning A

U_b : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) → ( ccc : CCC A ) → (b : Obj A)  
   → (CCCcong : IsCCC-*-cong A _ _ _ _ _ _ _ _ _ (CCC.isCCC ccc))
   → Functor A A
FObj (U_b A ccc b ccong) = λ a → (CCC._<=_ ccc  a b )
FMap (U_b A ccc b ccong) = λ f → CCC._* ccc ( A [ f o  CCC.ε ccc ] ) 
isFunctor (U_b A ccc b ccong) = isF where
   open CCC.CCC ccc
   isc = isCCC 
   open IsCCC isCCC 
   *-cong = IsCCC-*-cong.*-cong ccong 

   isF : IsFunctor A A ( λ a → (a <=  b)) (  λ f → CCC._* ccc ( A [ f o  ε ] ) )
   IsFunctor.≈-cong isF f≈g = *-cong ( car f≈g ) where open ≈-Reasoning A
   --    e4b : {a b c : Obj A} → { k : Hom A c (a <= b ) } →  A [ ( A [ ε o < A [ k o  π ]  ,  π' > ] ) * ≈ k ]
   IsFunctor.identity isF {a} = begin
                 (id1 A a o ε ) * 
            ≈⟨ *-cong  ( begin
                 id1 A a o CCC.ε ccc
            ≈⟨  idL  ⟩
                 ε 
            ≈↑⟨  idR  ⟩
                 ε o id1 A ( ( a <= b ) ∧ b )
            ≈↑⟨  cdr ( IsCCC.π-id isc) ⟩
                  ε o ( < π , π'  > )
            ≈↑⟨  cdr ( π-cong  idL refl-hom)  ⟩
                  ε o ( < id1 A (a <= b)  o π , π' > )
            ∎ ) ⟩
                  (  ε o ( < id1 A ( a <= b)  o π ,  π'  > ) ) *
             ≈⟨ IsCCC.e4b (CCC.isCCC ccc) ⟩
                 id1 A (a <= b)
             ∎ where open ≈-Reasoning A
   IsFunctor.distr isF {x} {y} {z} {f} {g} = begin
                 ( ( g o f ) o ε ) *
             ≈↑⟨ *-cong assoc ⟩
                 (  g o (f o ε ) ) *
             ≈↑⟨ *-cong ( cdr (IsCCC.e4a isc) ) ⟩
                  ( g o ( ε  o ( < ( ( f o ε ) * ) o π , π' > ) )) *
             ≈⟨ *-cong assoc ⟩
                  ( ( g o ε ) o ( < ( ( f o ε ) * ) o π , π' > ) ) *
             ≈↑⟨ IsCCC-*-cong.distr-* ccong ⟩
                  ( g o ε ) *  o  ( f o ε ) *  
             ∎ where open ≈-Reasoning A

F_b : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) → ( ccc : CCC A ) → (b : Obj A)  → Functor A A
FObj (F_b A ccc b) = λ a → ( CCC._∧_ ccc a  b )
FMap (F_b A ccc b) = λ f → ( CCC.<_,_>  ccc (A [ f o CCC.π ccc ] ) ( CCC.π'  ccc) )
isFunctor (F_b A ccc b) = isF where
   open CCC.CCC ccc
   isc = isCCC 
   open IsCCC isCCC 

   isF : IsFunctor A A ( λ a → (a ∧  b)) (  λ f → < ( A [ f o π ] ) , π' >  )
   IsFunctor.≈-cong isF f≈g = π-cong ( car f≈g ) refl-hom  where open ≈-Reasoning A
   IsFunctor.identity isF {a} = trans-hom (π-cong idL refl-hom ) (IsCCC.π-id isc)  where open ≈-Reasoning A
   IsFunctor.distr isF {x} {y} {z} {f} {g} = begin
                 < ( g o f ) o π  , π' >
             ≈↑⟨ π-cong assoc refl-hom ⟩
                 <  g o ( f o π ) , π' >
             ≈↑⟨  π-cong (cdr (IsCCC.e3a isc )) refl-hom ⟩
                 <  g o ( π  o < ( f o π ) , π' > ) , π' >
             ≈⟨  π-cong  assoc ( sym-hom (IsCCC.e3b isc ))  ⟩
                 < ( g o π )  o < ( f o π ) , π' > , π'  o < ( f o π ) , π' > >
             ≈↑⟨ IsCCC.distr-π isc ⟩
                 < ( g o π ) , π' > o < ( f o π ) , π' > 
             ∎ where open ≈-Reasoning A

-------
--- U_b and F_b is an adjunction Functor
-------

CCCtoAdj : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (  ccc : CCC A ) 
    → (CCCcong : IsCCC-*-cong A _ _ _ _ _ _ _ _ _ (CCC.isCCC ccc))
    → (b : Obj A ) → coUniversalMapping A A (F_b A ccc b)
CCCtoAdj  A ccc ccong b = record {
        U  = λ a → a <= b 
   ;    ε  = ε'
   ;    _*  = solution
   ;    iscoUniversalMapping = record {
           couniversalMapping = couniversalMapping
         ; uniquness = uniquness
     }
  } where
   open CCC.CCC ccc
   isc = isCCC 
   open IsCCC isCCC 
   ε' :  (a : Obj A) → Hom A (FObj (F_b A ccc b) (a <= b)) a
   ε' a = ε
   *-cong = IsCCC-*-cong.*-cong ccong 
   solution :  { b' : Obj A} {a : Obj A} → Hom A (FObj (F_b A ccc b) a) b' → Hom A a (b' <= b)
   solution f = f *
   couniversalMapping : {b = b₁ : Obj A} {a : Obj A}
            {f : Hom A (FObj (F_b A ccc b) a) b₁} →
            A [ A [ ε' b₁ o FMap (F_b A ccc b) (solution f) ] ≈ f ]
   couniversalMapping {c} {a} {f} = IsCCC.e4a isc
   uniquness :  {b = b₁ : Obj A} {a : Obj A}
            {f : Hom A (FObj (F_b A ccc b) a) b₁} {g : Hom A a (b₁ <= b)} →
            A [ A [ ε' b₁ o FMap (F_b A ccc b) g ] ≈ f ] → A [ solution f ≈ g ]
   uniquness {c} {a} {f} {g} eq = begin
                 f *
             ≈↑⟨ *-cong eq ⟩
                  ( ε o FMap (F_b A ccc b) g ) *
             ≈⟨⟩
                  ( ε o < ( g o π ) , π' > ) *
             ≈⟨ IsCCC.e4b isc  ⟩
                  g 
             ∎ where open ≈-Reasoning A


----------
--- Hom A １ ( c ^ b ) ≅ Hom A b c
---     p54 (3.3)
----------

c^b=b<=c : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) ( ccc : CCC A ) 
    → (CCCcong : IsCCC-*-cong A _ _ _ _ _ _ _ _ _ (CCC.isCCC ccc))
    → {a b c : Obj A} →  IsoS A A  (CCC.１ ccc ) (CCC._<=_ ccc  c b) b c
c^b=b<=c A ccc ccong {a} {b} {c} = record {
           ≅→ = λ f → A [ CCC.ε ccc o  CCC.<_,_> ccc ( A [ f o CCC.○ ccc b ] ) ( id1 A b )  ] ---   g ’   (g : 1 → b ^ a) of
       ;   ≅← =  λ f → CCC._* ccc ( A [ f o  CCC.π' ccc  ] )                                  --- ┌ f ┐   name of (f : b ^a → 1 )
       ;   iso→  = iso→
       ;   iso←  = iso←
       ;   cong→ = cong*
       ;   cong← = cong2
   } where
       cc = IsCCChom.ccc-3 ( CCChom.isCCChom (CCC→hom  A ccc ccong ) )  
       *-cong = IsCCC-*-cong.*-cong ccong 
       -- e4a : {a b c : Obj A} → { k : Hom A (c /\ b) a } →  A [ A [ ε o ( <,> ( A [ (k *) o π ] )   π')  ] ≈ k ]
       iso→ : {f : Hom A b c} → A [
            (A Category.o CCC.ε ccc) (CCC.< ccc , (A Category.o (ccc CCC.*) ((A Category.o f) (CCC.π' ccc))) (CCC.○ ccc b) > (Category.Category.Id A)) ≈ f ]
       iso→ {f} = begin
               CCC.ε ccc o (CCC.<_,_> ccc  (CCC._* ccc ( f o (CCC.π' ccc)) o (CCC.○ ccc b)) (id1 A b )  )
             ≈↑⟨ cdr ( IsCCC.π-cong ( CCC.isCCC ccc ) refl-hom (IsCCC.e3b (CCC.isCCC ccc) ) ) ⟩
                 CCC.ε ccc   o ( CCC.<_,_> ccc (CCC._* ccc (f o CCC.π' ccc) o CCC.○ ccc b) ((CCC.π' ccc) o CCC.<_,_> ccc (CCC.○ ccc b) (id1 A b) )  )
             ≈↑⟨ cdr ( IsCCC.π-cong ( CCC.isCCC ccc ) (cdr (IsCCC.e3a (CCC.isCCC ccc))) refl-hom )  ⟩
                 CCC.ε ccc   o ( CCC.<_,_> ccc (CCC._* ccc (f o CCC.π' ccc) o ( CCC.π ccc  o CCC.<_,_> ccc (CCC.○ ccc b) (id1 A b) ) ) ((CCC.π' ccc) o CCC.<_,_> ccc (CCC.○ ccc b) (id1 A b) )  )
             ≈⟨ cdr ( IsCCC.π-cong ( CCC.isCCC ccc ) assoc refl-hom ) ⟩
                 CCC.ε ccc   o ( CCC.<_,_> ccc ((CCC._* ccc (f o CCC.π' ccc) o CCC.π ccc ) o CCC.<_,_> ccc (CCC.○ ccc b) (id1 A b)  ) ((CCC.π' ccc) o CCC.<_,_> ccc (CCC.○ ccc b) (id1 A b) )  )
             ≈↑⟨ cdr ( IsCCC.distr-π ( CCC.isCCC ccc ) ) ⟩
                 CCC.ε ccc   o ( CCC.<_,_> ccc (CCC._* ccc (f o CCC.π' ccc) o CCC.π ccc ) (CCC.π' ccc)   o CCC.<_,_> ccc (CCC.○ ccc b) (id1 A b) )
             ≈⟨ assoc ⟩
                ( CCC.ε ccc   o  CCC.<_,_> ccc (CCC._* ccc (f o CCC.π' ccc) o CCC.π ccc ) (CCC.π' ccc) )  o CCC.<_,_> ccc (CCC.○ ccc b) (id1 A b)
             ≈⟨ car ( IsCCC.e4a (CCC.isCCC ccc) )  ⟩
               ( f o  CCC.π' ccc ) o  CCC.<_,_> ccc (CCC.○ ccc b) (id1 A b) 
             ≈↑⟨ assoc ⟩
               f o ( CCC.π' ccc  o  CCC.<_,_> ccc (CCC.○ ccc b) (id1 A b) ) 
             ≈⟨ cdr (IsCCC.e3b (CCC.isCCC ccc)) ⟩
               f o id1 A b 
             ≈⟨ idR ⟩
               f
             ∎ where open ≈-Reasoning A
       lemma : {f : Hom A (CCC.１ ccc) ((ccc CCC.<= c) b)} → A [ A [ A [ f o (CCC.○ ccc b) ] o  (CCC.π' ccc) ]  ≈ A [  f o (CCC.π ccc) ] ]
       lemma {f} = begin
                   ( f o (CCC.○ ccc b) ) o  (CCC.π' ccc)
               ≈↑⟨ assoc  ⟩
                   f o ( (CCC.○ ccc b) o  (CCC.π' ccc) )
               ≈⟨ cdr ( IsCCC.e2 (CCC.isCCC ccc) )  ⟩
                   f o (CCC.○ ccc ( CCC._∧_ ccc (CCC.１ ccc) b ) )
               ≈↑⟨ cdr ( IsCCC.e2 (CCC.isCCC ccc) )  ⟩
                   f o ( (CCC.○ ccc) (CCC.１ ccc) o (CCC.π ccc) )
               ≈↑⟨ cdr ( car ( IsCCC.e2 (CCC.isCCC ccc) ))  ⟩
                   f o ( id1 A (CCC.１ ccc) o (CCC.π ccc) )
               ≈⟨ cdr (idL) ⟩
                   f o (CCC.π ccc)
               ∎ where open ≈-Reasoning A
       --     e4b : {a b c : Obj A} → { k : Hom A c (a <= b ) } →  A [ ( A [ ε o ( <,> ( A [ k o  π ]  )  π' ) ] ) * ≈ k ]
       iso← : {f : Hom A (CCC.１ ccc) ((ccc CCC.<= c) b)} → A [  (ccc CCC.*) ((A Category.o (A Category.o CCC.ε ccc) (CCC.< ccc , (A Category.o f) (CCC.○ ccc b) >
                          (Category.Category.Id A))) (CCC.π' ccc)) ≈ f ]
       iso← {f} = begin
                CCC._* ccc (( CCC.ε ccc o ( CCC.<_,_> ccc ( f o (CCC.○ ccc b) ) (id1 A b ))) o (CCC.π' ccc))
             ≈↑⟨ *-cong  assoc ⟩
                CCC._* ccc ( CCC.ε ccc o (( CCC.<_,_> ccc ( f o (CCC.○ ccc b) ) (id1 A b )) o (CCC.π' ccc)))
             ≈⟨ *-cong  (cdr ( IsCCC.distr-π ( CCC.isCCC ccc ) ) ) ⟩
                CCC._* ccc ( CCC.ε ccc o CCC.<_,_> ccc ( (f o (CCC.○ ccc b)) o  CCC.π' ccc ) (id1 A b o CCC.π' ccc) )
             ≈⟨ *-cong  (cdr ( IsCCC.π-cong ( CCC.isCCC ccc ) lemma idL )) ⟩
                CCC._* ccc ( CCC.ε ccc o CCC.<_,_> ccc ( f o CCC.π ccc ) (CCC.π' ccc) )
             ≈⟨  IsCCC.e4b (CCC.isCCC ccc)  ⟩
               f
             ∎ where open ≈-Reasoning A
       cong* :  {f g : Hom A (CCC.１ ccc) ((ccc CCC.<= c) b)} →
            A [ f ≈ g ] → A [ (A Category.o CCC.ε ccc) (CCC.< ccc , (A Category.o f) (CCC.○ ccc b) > (Category.Category.Id A))
            ≈ (A Category.o CCC.ε ccc) (CCC.< ccc , (A Category.o g) (CCC.○ ccc b) > (Category.Category.Id A)) ]
       cong* {f} {g} f≈g = begin
                CCC.ε ccc o (  CCC.<_,_> ccc ( f o ( CCC.○ ccc b )) (id1 A b ))
             ≈⟨ cdr (IsCCC.π-cong ( CCC.isCCC ccc ) (car f≈g) refl-hom  )  ⟩
                CCC.ε ccc o (  CCC.<_,_> ccc ( g o ( CCC.○ ccc b )) (id1 A b ))
             ∎ where open ≈-Reasoning A
       cong2 : {f g : Hom A b c} → A [ f ≈ g ] →
            A [ (ccc CCC.*) ((A Category.o f) (CCC.π' ccc)) ≈ (ccc CCC.*) ((A Category.o g) (CCC.π' ccc)) ]
       cong2 {f} {g} f≈g = begin
                CCC._* ccc ( f o (CCC.π' ccc) )
             ≈⟨ *-cong  (car f≈g ) ⟩
                CCC._* ccc ( g o (CCC.π' ccc) )
             ∎ where open ≈-Reasoning A


open CCChom
open IsCCChom
open IsoS

hom→CCC : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) ( h : CCChom A ) → CCC A
hom→CCC A h = record {
         １  = １
       ; ○ = ○
       ; _∧_ = _∧_
       ; <_,_> = <,>
       ; π = π
       ; π' = π'
       ; _<=_ = _<=_
       ; _* = _*
       ; ε = ε
       ; isCCC = isCCC
  } where
         １ : Obj A 
         １ = one h
         ○ : (a : Obj A ) → Hom A a １ 
         ○ a = ≅← ( ccc-1 (isCCChom h ) {_} {OneObj} {OneObj} ) OneObj
         _∧_ : Obj A → Obj A → Obj A   
         _∧_ a b = _*_ h a b
         <,> : {a b c : Obj A } → Hom A c a → Hom A c b → Hom A c ( a ∧ b)  
         <,> f g = ≅← ( ccc-2 (isCCChom h ) ) ( f , g )
         π : {a b : Obj A } → Hom A (a ∧ b) a 
         π {a} {b} =  proj₁ ( ≅→ ( ccc-2 (isCCChom h ) ) (id1 A (_*_ h a b) ))
         π' : {a b : Obj A } → Hom A (a ∧ b) b  
         π' {a} {b} =  proj₂ ( ≅→ ( ccc-2 (isCCChom h ) ) (id1 A (_*_ h a b) ))
         _<=_ : (a b : Obj A ) → Obj A 
         _<=_ = _^_ h
         _* : {a b c : Obj A } → Hom A (a ∧ b) c → Hom A a (c <= b) 
         _* =  ≅← ( ccc-3 (isCCChom h ) )
         ε : {a b : Obj A } → Hom A ((a <= b ) ∧ b) a 
         ε {a} {b} =  ≅→ ( ccc-3 (isCCChom h ) {_^_ h a b} {b} ) (id1 A ( _^_ h a b )) 
         isCCC : CCC.IsCCC A １ ○ _∧_ <,> π π' _<=_ _* ε 
         isCCC = record {
               e2  = e2
             ; e3a = e3a
             ; e3b = e3b
             ; e3c = e3c
             ; π-cong = π-cong
             ; e4a = e4a
             ; e4b = e4b
             -- ; *-cong = *-cong
           } where
               e20 : ∀ ( f : Hom OneCat OneObj OneObj ) →  _[_≈_] OneCat {OneObj} {OneObj} f OneObj 
               e20 OneObj = refl
               e2  : {a : Obj A} → ∀ { f : Hom A a １ } →  A [ f ≈ ○ a ]
               e2 {a} {f} = begin
                     f
                  ≈↑⟨  iso← ( ccc-1 (isCCChom h )) ⟩
                    ≅← ( ccc-1 (isCCChom h )  {a} {OneObj} {OneObj}) (  ≅→ ( ccc-1 (isCCChom h ) {a} {OneObj} {OneObj} ) f ) 
                  ≈⟨  ≡-cong OneCat {OneObj} {OneObj}  (
                         λ y → ≅← ( ccc-1 (isCCChom h ) {a} {OneObj} {OneObj} ) y ) (e20 ( ≅→ ( ccc-1 (isCCChom h ) {a} {OneObj} {OneObj} ) f) )  ⟩
                    ≅← ( ccc-1 (isCCChom h ) {a} {OneObj} {OneObj} ) OneObj
                  ≈⟨⟩
                     ○ a
                  ∎ where open ≈-Reasoning A
               --
               --             g                 id
               --     a -------------> b * c ------>  b * c
               --
               --     a -------------> b * c ------>  b
               --     a -------------> b * c ------>  c
               --
               cong-proj₁ : {a b c d  : Obj A} → { f g : Hom (A × A) ( a , b ) ( c , d ) } → (A × A) [ f ≈ g ] → A [ proj₁ f  ≈ proj₁ g ]
               cong-proj₁ eq =  proj₁ eq
               cong-proj₂ : {a b c d  : Obj A} → { f g : Hom (A × A) ( a , b ) ( c , d ) } → (A × A) [ f ≈ g ] → A [ proj₂ f  ≈ proj₂ g ]
               cong-proj₂ eq =  proj₂ eq
               e3a : {a b c : Obj A} → { f : Hom A c a }{ g : Hom A c b } →  A [ A [ π o <,> f g  ] ≈ f ]
               e3a {a} {b} {c} {f} {g} =  begin
                    π o <,> f g
                  ≈⟨⟩
                     proj₁ (≅→ (ccc-2 (isCCChom h)) (id1 A (_*_ h a b) )) o  (≅← (ccc-2 (isCCChom h)) (f , g))
                  ≈⟨ cong-proj₁ (nat-2 (isCCChom h))  ⟩
                     proj₁ (≅→ (ccc-2 (isCCChom h)) (( id1 A ( _*_ h a  b )) o ( ≅← (ccc-2 (isCCChom h)) (f , g) ) ))
                  ≈⟨ cong-proj₁  ( cong→ (ccc-2 (isCCChom h)) idL ) ⟩
                     proj₁ (≅→ (ccc-2 (isCCChom h)) ( ≅← (ccc-2 (isCCChom h)) (f , g) ))
                  ≈⟨ cong-proj₁ ( iso→ (ccc-2 (isCCChom h))) ⟩
                     proj₁ ( f , g )
                  ≈⟨⟩
                    f 
                  ∎ where open ≈-Reasoning A
               e3b : {a b c : Obj A} → { f : Hom A c a }{ g : Hom A c b } →  A [ A [ π' o <,> f g  ] ≈ g ]
               e3b {a} {b} {c} {f} {g} =  begin
                    π' o <,> f g
                  ≈⟨⟩
                     proj₂ (≅→ (ccc-2 (isCCChom h)) (id1 A (_*_ h a b) )) o  (≅← (ccc-2 (isCCChom h)) (f , g))
                  ≈⟨ cong-proj₂ (nat-2 (isCCChom h))  ⟩
                     proj₂ (≅→ (ccc-2 (isCCChom h)) (( id1 A ( _*_ h a  b )) o ( ≅← (ccc-2 (isCCChom h)) (f , g) ) ))
                  ≈⟨ cong-proj₂  ( cong→ (ccc-2 (isCCChom h)) idL ) ⟩
                     proj₂ (≅→ (ccc-2 (isCCChom h)) ( ≅← (ccc-2 (isCCChom h)) (f , g) ))
                  ≈⟨ cong-proj₂ ( iso→ (ccc-2 (isCCChom h))) ⟩
                     proj₂ ( f , g )
                  ≈⟨⟩
                    g 
                  ∎ where open ≈-Reasoning A
               e3c : {a b c : Obj A} → { h : Hom A c (a ∧ b) } →  A [ <,> ( A [ π o h ] ) ( A [ π' o h  ] )  ≈ h ]
               e3c {a} {b} {c} {f} = begin
                   <,> (  π o f  ) (  π' o f   )
                  ≈⟨⟩
                    ≅← (ccc-2 (isCCChom h)) ( ( proj₁ (≅→ (ccc-2 (isCCChom h)) (id1 A (_*_ h a b) ))) o f
                           , ( proj₂ (≅→ (ccc-2 (isCCChom h)) (id1 A (_*_ h a b)))) o f )
                  ≈⟨⟩
                    ≅← (ccc-2 (isCCChom h)) (_[_o_] (A × A) (≅→ (ccc-2 (isCCChom h)) (id1 A (_*_ h a b) )) (f , f ) )
                  ≈⟨ cong← (ccc-2 (isCCChom h)) (nat-2 (isCCChom h))   ⟩
                    ≅← (ccc-2 (isCCChom h)) (≅→ (ccc-2 (isCCChom h)) (id1 A (_*_ h a b) o f  ))
                  ≈⟨ cong← (ccc-2 (isCCChom h)) (cong→ (ccc-2 (isCCChom h)) idL ) ⟩
                    ≅← (ccc-2 (isCCChom h)) (≅→ (ccc-2 (isCCChom h)) f )
                  ≈⟨ iso← (ccc-2 (isCCChom h))  ⟩
                    f
                  ∎ where open ≈-Reasoning A
               π-cong :  {a b c : Obj A} → { f f' : Hom A c a }{ g g' : Hom A c b } → A [ f ≈ f' ] → A [ g ≈ g' ]  →  A [ <,> f  g   ≈ <,> f'  g'  ] 
               π-cong {a} {b} {c} {f} {f'} {g} {g'} eq1 eq2 = begin
                      <,> f  g 
                  ≈⟨⟩
                       ≅← (ccc-2 (isCCChom h)) (f , g)
                  ≈⟨ cong← (ccc-2 (isCCChom h)) ( eq1 , eq2 )  ⟩
                       ≅← (ccc-2 (isCCChom h)) (f' , g')
                  ≈⟨⟩
                      <,> f'  g' 
                  ∎ where open ≈-Reasoning A
               e4a : {a b c : Obj A} → { k : Hom A (c ∧ b) a } →  A [ A [ ε o ( <,> ( A [ (k *) o π ] )   π')  ] ≈ k ]
               e4a {a} {b} {c} {k} =  begin
                      ε o ( <,> ((k *)  o π  ) π' )
                  ≈⟨⟩
                      ≅→ (ccc-3 (isCCChom h)) (id1 A (_^_ h a b)) o (≅← (ccc-2 (isCCChom h)) ((( ≅← (ccc-3 (isCCChom h)) k) o π ) , π'))
                  ≈⟨ nat-3 (isCCChom h) ⟩
                      ≅→ (ccc-3 (isCCChom h)) (≅← (ccc-3 (isCCChom h)) k) 
                  ≈⟨ iso→  (ccc-3 (isCCChom h))  ⟩
                      k
                  ∎ where open ≈-Reasoning A
               e4b : {a b c : Obj A} → { k : Hom A c (a <= b ) } →  A [ ( A [ ε o ( <,> ( A [ k o  π ]  )  π' ) ] ) * ≈ k ]
               e4b {a} {b} {c} {k} =  begin
                      ( ε o ( <,> (  k o  π  )  π' ) ) *
                  ≈⟨⟩
                     ≅← (ccc-3 (isCCChom h)) ( ≅→ ( ccc-3 (isCCChom h ) {_^_ h a b} {b} ) (id1 A ( _^_ h a b )) o (≅← (ccc-2 (isCCChom h)) ( k o  π , π'))) 
                  ≈⟨ cong← (ccc-3 (isCCChom h)) (nat-3 (isCCChom h)) ⟩
                     ≅← (ccc-3 (isCCChom h)) (≅→ (ccc-3 (isCCChom h)) k)
                  ≈⟨ iso←  (ccc-3 (isCCChom h))  ⟩
                      k
                  ∎ where open ≈-Reasoning A
               *-cong  : {a b c : Obj A} {f f' : Hom A (a ∧ b) c} → A [ f ≈ f' ] → A [ f * ≈ f' * ]
               *-cong eq = cong← ( ccc-3 (isCCChom h )) eq

