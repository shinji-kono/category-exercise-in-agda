open import CCC
open import Level
open import Category
open import cat-utility
open import HomReasoning
open import Data.List hiding ( [_] )
module ToposIL   {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (c : CCC A)   where

  open Topos
  open Equalizer
  open ≈-Reasoning A
  open CCC.CCC c

  open Functor
  open import Category.Sets hiding (_o_)
  open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym)
  open import Polynominal A c

  -- record IsLogic    (c : CCC A) 
  --        (Ω : Obj A)
  --        (⊤ : Hom A １ Ω)
  --        (P  : Obj A → Obj A)
  --        (_==_ : {a : Obj A} (x y : Hom A １ a ) → Hom A ( a ∧ a ) Ω)
  --        (_∈_ : {a : Obj A} (x : Hom A １ a ) → Hom A ( a ∧ P a ) Ω)
  --        (_|-_  : {a : Obj A} (x : List ( Hom A １ a ) ) → Hom A {!!} Ω)
  --           :   Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
  --    field
  --        a : {!!}

  record InternalLanguage (Ω : Obj A) (⊤ : Hom A １ Ω) (P  : Obj A → Obj A)
          :   Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
     field
         _==_ : {a : Obj A} (x y : Hom A １ a ) → Hom A １ Ω
         _∈_ : {a : Obj A} (x :  Hom A １ a ) (α : Hom A １ (P a) ) → Hom A １ Ω
         -- { x ∈ a | φ x } : P a
         select : {a : Obj A} → ( φ :  Poly a Ω １ ) → Hom A １ (P a)
         -- isTL : IsLogic c Ω ⊤ P _==_ _∈_  _|-_
     -- _|-_  :  (List (Hom A １ Ω)) → (p : Hom A １ Ω ) → Set ℓ
     -- [] |-  p = A [ p ≈  ⊤ ] 
     -- (h ∷ t) |-  p = {!!}
  
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
  FC1 : Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ )
  FC1 = {a : Obj A}  (t : Topos A c) ( φ : Poly a (Ω t)１) → Fc φ

  topos→logic : (t : Topos A c ) → ToposNat A １ → FC1  → InternalLanguage (Topos.Ω t) (Topos.⊤ t) (λ a → (Topos.Ω t) <= a)
  topos→logic t n fc = record {
         _==_ = λ {b} f g →   A [ char t < id1 A b , id1 A b > (δmono t n ) o < f , g > ]
      ;  _∈_ = λ {a} x α →  A [ ε o < α , x > ]
      -- { x ∈ a | φ x } : P a
      ;  select = λ {a} φ →  Fc.g ( fc t φ )
      -- ;  isTL = {!!}
    } 
