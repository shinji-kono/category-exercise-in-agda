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

  -- record IsLogic    (c : CCC A) 
  --        (Ω : Obj A)
  --        (⊤ : Hom A (CCC.１ c) Ω)
  --        (P  : Obj A → Obj A)
  --        (_==_ : {a : Obj A} (x y : Hom A  (CCC.１ c) a ) → Hom A ( a ∧ a ) Ω)
  --        (_∈_ : {a : Obj A} (x : Hom A (CCC.１ c) a ) → Hom A ( a ∧ P a ) Ω)
  --        (_|-_  : {a : Obj A} (x : List ( Hom A (CCC.１ c) a ) ) → Hom A {!!} Ω)
  --           :   Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
  --    field
  --        a : {!!}

  record InternalLanguage (Ω : Obj A) (⊤ : Hom A (CCC.１ c) Ω) (P  : Obj A → Obj A)
          :   Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
     field
         _==_ : {a : Obj A} (x y : Hom A  (CCC.１ c) a ) → Hom A (CCC.１ c) Ω
         _∈_ : {a : Obj A} (x :  Hom A  (CCC.１ c) a ) (α : Hom A (CCC.１ c) (P a) ) → Hom A (CCC.１ c) Ω
         -- { x ∈ a | φ x } : P a
         select : {a b : Obj A}  (α : Hom A (CCC.１ c) (P a) ) → ( (x :  Hom A  (CCC.１ c) a ) →  Hom A (CCC.１ c) Ω ) → Hom A (CCC.１ c) (P a)
         -- isTL : IsLogic c Ω ⊤ P _==_ _∈_  _|-_
     |-_  : {a : Obj A} (p : Hom A (CCC.１ c) Ω ) → Set ℓ
     |-_  {a} p = A [ p ≈  ⊤ ] 
  
--             ○ b
--       b -----------→ 1
--       |              |
--     m |              | ⊤
--       ↓    char m    ↓
--       a -----------→ Ω

  -- (n : ToposNat A (CCC.１ c))
  -- open NatD
  -- open ToposNat n

  -- N : Obj A
  -- N = Nat iNat 

  open import ToposEx A c using ( δmono  )

  -- λ (x ∈ a) → φ x
  record Select  {a b : Obj A} (Ω : Obj A) (α : Hom A (CCC.１ c) (Ω <= a) ) ( φ : (x :  Hom A  (CCC.１ c) a ) → Hom A (CCC.１ c) b )
         :  Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
    field
      sl :  Hom A (CCC.１ c) (b <= a) 
      isSelect : (x : Hom A  (CCC.１ c) a  ) → A [  A [ CCC.ε c o < sl , x > ]  ≈  φ x ]

  -- functional completeness
  FC : Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ )
  FC = {a b : Obj A}  (α : Hom A (CCC.１ c) (b <= a) ) ( φ : (x :  Hom A  (CCC.１ c) a ) → Hom A (CCC.１ c) b ) → Select b α φ

  topos→logic : (t : Topos A c ) → ToposNat A (CCC.１ c)  → FC  → InternalLanguage (Topos.Ω t) (Topos.⊤ t) (λ a → (Topos.Ω t) <= a)
  topos→logic t n fc = record {
         _==_ = λ {b} f g →   A [ char t < id1 A b , id1 A b > (δmono t n ) o < f , g > ]
      ;  _∈_ = λ {a} x α →  A [ CCC.ε c o < α , x > ]
      -- { x ∈ a | φ x } : P a
      ;  select = λ {a} α φ →  Select.sl ( fc α φ )
      -- ;  isTL = {!!}
    } 
