{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS --cubical-compatible --safe #-}

open import CCC
open import Level
open import Category
open import Definitions
open import HomReasoning
open import Data.List hiding ( [_] )
module ToposIL   {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (c : CCC A)  (n : ToposNat A (CCC.１ c))  where

  open Topos
  open Equalizer
  -- open ≈-Reasoning A hiding (_∙_)
  open CCC.CCC c

  open Functor
  open import Category.Sets hiding (_==_)
  open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym)
  open import Polynominal A c

  record IsLogic (Ω : Obj A) (⊤ : Hom A １ Ω) (P  : Obj A → Obj A)
         (_==_ : {a : Obj A} (x y : Hom A １ a ) → Hom A １ Ω)
         (_∈_ : {a : Obj A} (x :  Hom A １ a ) (α : Hom A １ (P a) ) → Hom A １ Ω)
         (select : {a : Obj A} → ( φ :  Poly a Ω １ ) → Hom A １ (P a))
         (apply : {a  : Obj A}  (p : Poly a  Ω １ )  → ( x : Hom A １ a ) →  Poly a  Ω １ )
             :   Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
     field
         isSelect : {a : Obj A} → ( φ :  Poly a Ω １ ) → {c : Obj A} (h : Hom A c １ )
            → A [ ( ( Poly.x φ ∈ select φ ) == Poly.f φ )  ∙ h  ≈  ⊤ ∙  ○  c ]
         uniqueSelect : {a : Obj A} → ( φ :  Poly a Ω １ ) → (α : Hom A １ (P a) )
            → {c : Obj A} (h : Hom A c １ )
            → A [ ( Poly.f φ == ( Poly.x φ ∈ α ) )  ∙ h  ≈  ⊤ ∙  ○  c ]
            → A [ ( select φ == α )  ∙ h  ≈  ⊤ ∙  ○  c ]
         isApply : {a : Obj A}  (x y : Hom A １ a ) → (q p : Poly a  Ω １ ) 
            → {c : Obj A} (h : Hom A c １ )  → A [ ( x == y )  ∙ h  ≈  ⊤ ∙  ○  c ] 
            → A [ Poly.f q ∙ h  ≈  ⊤ ∙  ○  c ]
            → A [ Poly.f (apply p x ) ∙ h  ≈  ⊤ ∙  ○  c ] 
            → A [ Poly.f (apply p y ) ∙ h  ≈  ⊤ ∙  ○  c ]  
         applyCong : {a : Obj A}  (x : Hom A １ a ) → (q p : Poly a  Ω １ ) 
            → {c : Obj A} (h : Hom A c １ )  
            → ( A [ Poly.f q ∙ h  ≈  ⊤ ∙  ○  c ] → A [ Poly.f p ∙ h  ≈  ⊤ ∙  ○  c ] )
            → ( A [ Poly.f (apply q x ) ∙ h  ≈  ⊤ ∙  ○  c ] → A [ Poly.f (apply p x ) ∙ h  ≈  ⊤ ∙  ○  c ] )

  record InternalLanguage (Ω : Obj A) (⊤ : Hom A １ Ω) (P  : Obj A → Obj A)
          :   Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
     field
         _==_ : {a : Obj A} (x y : Hom A １ a ) → Hom A １ Ω
         _∈_ : {a : Obj A} (x :  Hom A １ a ) (α : Hom A １ (P a) ) → Hom A １ Ω
         -- { x ∈ a | φ x } : P a
         select : {a : Obj A} → ( φ :  Poly a Ω １ ) → Hom A １ (P a)
         apply : {a  : Obj A}  (p : Poly a  Ω １ )  → ( x : Hom A １ a ) →  Poly a  Ω １ 
         isIL : IsLogic Ω ⊤ P _==_ _∈_  select apply
     _⊢_  : {a b : Obj A}  (p : Poly a  Ω b ) (q : Poly a  Ω b ) → Set  ( c₁  ⊔  c₂ ⊔ ℓ ) 
     _⊢_  {a} {b} p q = {c : Obj A} (h : Hom A c b ) → A [ Poly.f p ∙  h  ≈  ⊤ ∙  ○  c  ]
         → A [   Poly.f q ∙ h  ≈  ⊤ ∙  ○  c  ] 
     _,_⊢_  : {a b : Obj A}  (p : Poly a  Ω b ) (p1 : Poly a  Ω b ) (q : Poly a  Ω b ) → Set  ( c₁  ⊔  c₂ ⊔ ℓ ) 
     _,_⊢_  {a} {b} p p1 q = {c : Obj A} (h : Hom A c b ) → A [ Poly.f p ∙  h  ≈  ⊤ ∙  ○  c  ]
         → A [   Poly.f p1 ∙ h  ≈  ⊤ ∙  ○  c  ] 
         → A [   Poly.f q  ∙ h  ≈  ⊤ ∙  ○  c  ] 
     -- expr : {a b c  : Obj A}  (p : Hom A １ Ω  )  → ( x : Hom A １ a ) →  Poly a  Ω １ 
     -- expr p x = record { x = x ;  f = p ; phi = i ; idx = {!!} }
     ⊨_ :   (p : Hom A １ Ω  ) →  Set  ( c₁  ⊔  c₂ ⊔ ℓ )
     ⊨  p = {c : Obj A} (h : Hom A c １ )  → A [ p  ∙ h  ≈  ⊤ ∙  ○  c ] 

--             ○ b
--       b -----------→ 1
--       |              |
--     m |              | ⊤
--       ↓    char m    ↓
--       a -----------→ Ω

  -- (n : ToposNat A １)
  -- open NatD
  -- open ToposNat n

  -- N : Obj A
  -- N = Nat iNat 

  open import ToposEx A c using ( δmono  )

  -- f ≡ λ (x ∈ a) → φ x , ∃ (f : b <= a) →  f ∙ x ≈  φ x  


  -- functional completeness
  FC0 : Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ )
  FC0 = {a b : Obj A}  (t : Topos A c) ( φ : Poly a (Ω t) b) → Functional-completeness φ

  FC1 : Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ )
  FC1 = {a : Obj A}  (t : Topos A c) ( φ : Poly a (Ω t) １) → Fc φ

  topos→logic : (t : Topos A c ) → ToposNat A １ → FC0 →  FC1  → InternalLanguage (Topos.Ω t) (Topos.⊤ t) (λ a → (Topos.Ω t) <= a)
  topos→logic t n fc0 fc = record {
         _==_ = λ {b} f g →   A [ char t < id1 A b , id1 A b > (δmono t n ) o < f , g > ]
      ;  _∈_ = λ {a} x α →  A [ ε o < α , x > ]
      -- { x ∈ a | φ x } : P a
      ;  select = λ {a} φ →  Fc.g ( fc t φ )
      ;  apply = λ {a}  φ x → record { x = x ; f = Functional-completeness.fun (fc0 t φ ) ∙ < x ∙  ○ _ , id1 A _ >  ; phi = i _ }
      ;  isIL = record {
           isSelect = {!!}
         ; uniqueSelect = {!!}
         ; isApply = {!!}
         ; applyCong = {!!}
        }
    } where
     open ≈-Reasoning A -- hiding (_∙_)
     _⊢_  : {a b : Obj A}  (p : Poly a  (Topos.Ω t) b ) (q : Poly a  (Topos.Ω t) b ) → Set  ( c₁  ⊔  c₂ ⊔ ℓ ) 
     _⊢_  {a} {b}  p q = {c : Obj A} (h : Hom A c b ) → A [ Poly.f p ∙  h  ≈  (Topos.⊤ t) ∙  ○  c  ]
         → A [   Poly.f q ∙ h  ≈  (Topos.⊤ t) ∙  ○  c  ] 
--
--     iso          ○ c
--  e ⇐====⇒  c -----------→ 1     
--  |         |              |
--  |       h |              | ⊤
--  |         ↓    char h    ↓    
--  + ------→ b -----------→ Ω    
--     ker h       fp / fq
--
     tl01 : {a b : Obj A}  (p q : Poly a  (Topos.Ω t) b ) 
        → p ⊢ q → q ⊢ p →  A [ Poly.f p ≈ Poly.f q ]
     tl01 {a} {b} p q p<q q<p = begin
          Poly.f p ≈↑⟨ tt p  ⟩
          char t (equalizer (kp p) ) (eMonic A (kp p)) ≈⟨ IsTopos.char-iso (Topos.isTopos t) (equalizer (kp p) ) (equalizer (kp q) ) (eMonic A (kp p)) (eMonic A (kp q)) pqiso ei ⟩
          char t (equalizer (kp q) ) (eMonic A (kp q)) ≈⟨ tt q ⟩
          Poly.f q ∎   where
        open import equalizer using ( monic )
        open IsEqualizer renaming ( k to ek )
        kp : (p : Poly a  (Topos.Ω t) b ) →  Equalizer A _ _
        kp p = Ker t ( Poly.f p )
        ee :  (p q : Poly a  (Topos.Ω t) b ) →  q ⊢ p
            →  A [ A [ Poly.f p o equalizer (Ker t ( Poly.f q )) ] ≈ A [ A [ ⊤ t o ○ b ] o equalizer (Ker t ( Poly.f q ))] ]
        ee p q q<p = begin
           Poly.f p o equalizer (Ker t ( Poly.f q )) ≈⟨ q<p _ ( begin
            Poly.f q ∙ equalizer (Ker t ( Poly.f q )) ≈⟨ fe=ge (isEqualizer (Ker t ( Poly.f q))) ⟩
            ( ⊤ t ∙ ○ b ) ∙ equalizer (Ker t ( Poly.f q )) ≈↑⟨ assoc ⟩
            ⊤ t ∙ ( ○ b  ∙ equalizer (Ker t ( Poly.f q ))) ≈⟨ cdr e2 ⟩
            ⊤ t ∙ ○ (equalizer-c (Ker t ( Poly.f q )))  ∎ ) ⟩
           ⊤ t ∙ ○ (equalizer-c (Ker t ( Poly.f q ))) ≈↑⟨ cdr e2 ⟩
           ⊤ t ∙ ( ○ b ∙  equalizer (Ker t (Poly.f q) ))  ≈⟨ assoc ⟩
           (⊤ t ∙ ○ b) ∙  equalizer (Ker t (Poly.f q) )  ∎  
        qtop : (p q : Poly a  (Topos.Ω t) b ) →  q ⊢ p →  Hom A (equalizer-c (Ker t ( Poly.f q ))) (equalizer-c (Ker t ( Poly.f p )))
        qtop p q q<p = ek (isEqualizer (Ker t ( Poly.f p))) (equalizer (Ker t ( Poly.f q))) (ee p q q<p)
        qq=1 : (p q : Poly a  (Topos.Ω t) b ) →  (q<p : q ⊢ p ) → (p<q : p ⊢ q) → A [ A [ qtop p q q<p o qtop q p p<q ] ≈ id1 A (equalizer-c (Ker t ( Poly.f p ))) ]
        qq=1 p q q<p p<q = begin
           qtop  p q q<p o qtop q p p<q  ≈↑⟨ uniqueness (isEqualizer (Ker t ( Poly.f p ))) (begin
             equalizer (kp p) ∙ (qtop  p q q<p ∙ qtop q p p<q  ) ≈⟨ assoc ⟩
             (equalizer (kp p) ∙ qtop  p q q<p ) ∙ qtop q p p<q   ≈⟨ car (ek=h (isEqualizer (kp p))) ⟩
             equalizer (kp q) ∙ qtop q p p<q    ≈⟨ ek=h (isEqualizer (kp q)) ⟩
             equalizer (kp p) ∎ ) ⟩
           ek (isEqualizer (kp p)) (equalizer (kp p)) (fe=ge (isEqualizer (kp p))) ≈⟨ uniqueness (isEqualizer (kp p)) idR ⟩
           id1 A _ ∎  
        pqiso : Iso A (equalizer-c (kp p)) (equalizer-c (kp q))
        pqiso = record { ≅← = qtop  p q q<p ; ≅→ =  qtop q p p<q ; iso→  = qq=1 p q q<p p<q  ; iso← = qq=1 q p p<q q<p  } 
        ei :  A [ equalizer (Ker t (Poly.f p)) ≈ A [ equalizer (Ker t (Poly.f q)) o Iso.≅→ pqiso ] ]
        ei = sym (ek=h (isEqualizer (kp q)) )
        tt :  (q : Poly a  (Topos.Ω t) b ) → A [ char t (equalizer (Ker t (Poly.f q))) (eMonic A (Ker t (Poly.f q)))  ≈  Poly.f q ]
        tt q = IsTopos.char-uniqueness (Topos.isTopos t) {b} {a} 

  module IL1 (Ω : Obj A) (⊤ : Hom A １ Ω) (P  : Obj A → Obj A) (il : InternalLanguage  Ω ⊤ P)  where
     open InternalLanguage il
     il00 : {a : Obj A}  (p : Poly a  Ω １ )  → p  ⊢ p
     il00 {a}  p h eq = eq

     ---  Poly.f p ∙  h  ≈  ⊤ ∙  ○  c 
     ---  Poly.f q ∙  h  ≈  ⊤ ∙  ○  c 

     il011 : {a b : Obj A}  (p q q1 : Poly a  Ω b ) 
        → q ⊢ p → q , q1 ⊢ p 
     il011 {a} p q q1 p<q h tq tq1 = p<q h tq

     il012 : {a b : Obj A}  (p q r : Poly a  Ω b ) 
        → q ⊢ p → q , p  ⊢ r → q ⊢ r 
     il012 {a} p q r p<q pq<r h  qt = pq<r h qt (p<q h qt) 
     

     il02 : {a : Obj A} (x : Hom A １ a ) → ⊨ (x == x) 
     il02 = {!!}

     --- (b : Hom A １ a) → φ y  ⊢ φ' y  → φ b  ⊢ φ' b
     il03 : {a : Obj A}  (b : Hom A １ a ) → (q p : Poly a  Ω １ ) 
        → q ⊢ p → apply q b  ⊢ apply p b
     il03 {a} b q p q<p h = IsLogic.applyCong (InternalLanguage.isIL il ) b q p h (q<p h)

     --- a == b → φ a  ⊢ φ b
     il04 : {a : Obj A}  (x y : Hom A １ a ) → (q p : Poly a  Ω １ ) 
        → ⊨ (x == y) 
        → q ⊢ apply p x → q ⊢ apply p y
     il04 {a} x y q p eq q<px h qt = IsLogic.isApply (InternalLanguage.isIL il ) x y q p h (eq h) qt (q<px h qt )
  
     --- ⊨ x ∈ select φ == φ x
     il05 : {a : Obj A}  → (q : Poly a  Ω １ ) 
        → ⊨ ( ( Poly.x q ∈ select q ) == Poly.f q  )
     il05 {a} = IsLogic.isSelect (InternalLanguage.isIL il )
  
     ---    q ⊢  φ x == x ∈ α 
     ---   ----------------------- 
     ---    q ⊢ select φ == α
     ---
     il06 : {a : Obj A}  → (q : Poly a  Ω １ )  → (α : Hom A １ (P a) )
        → ⊨ ( Poly.f q  == ( Poly.x q ∈ α ) ) 
        → ⊨ ( select q == α )
     il06 {a} q p eq h = IsLogic.uniqueSelect (InternalLanguage.isIL il ) q p h (eq h)
  
