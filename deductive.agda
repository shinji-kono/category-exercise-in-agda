open import Level
open import Category
module deductive {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) where

-- Deduction Theorem

-- positive logic 

record PositiveLogic {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) :  Set ( c₁  ⊔  c₂ ⊔ ℓ ) where
     field
         ⊤ : Obj A 
         ○ : (a : Obj A ) → Hom A a ⊤ 
         _∧_ : Obj A → Obj A → Obj A   
         <_,_> : {a b c : Obj A } → Hom A c a → Hom A c b → Hom A c (a ∧ b)  
         π : {a b : Obj A } → Hom A (a ∧ b) a 
         π' : {a b : Obj A } → Hom A (a ∧ b) b  
         _<=_ : (a b : Obj A ) → Obj A 
         _* : {a b c : Obj A } → Hom A (a ∧ b) c → Hom A a (c <= b) 
         ε : {a b : Obj A } → Hom A ((a <= b ) ∧ b) a 


module deduction-theorem (  L :  PositiveLogic A ) where

  open PositiveLogic L
  _・_ = _[_o_] A
  
  -- every proof b →  c with assumption a has following forms
  
  data  φ  {a : Obj A } ( x : Hom A ⊤ a ) : {b c : Obj A } → Hom A b c → Set ( c₁  ⊔  c₂ ) where
     i   : {b c : Obj A} {k : Hom A b c } → φ x k
     ii  : φ x {⊤} {a} x
     iii : {b c' c'' : Obj A } { f : Hom A b c' } { g : Hom A b c'' } (ψ : φ x f ) (χ : φ x g ) → φ x {b} {c'  ∧ c''} < f , g > 
     iv  : {b c d : Obj A } { f : Hom A d c } { g : Hom A b d } (ψ : φ x f ) (χ : φ x g ) → φ x ( f ・ g )
     v   : {b c' c'' : Obj A } { f : Hom A (b ∧ c') c'' }  (ψ : φ x f )  → φ x {b} {c'' <= c'} ( f * )
  
  α : {a b c : Obj A } → Hom A (( a ∧ b ) ∧ c ) ( a ∧ ( b ∧ c ) )
  α = < π  ・ π   , < π'  ・ π  , π'  > >
  
  -- genetate (a ∧ b) → c proof from  proof b →  c with assumption a
  
  k : {a b c : Obj A } → ( x∈a : Hom A ⊤ a ) → {z : Hom A b c } → ( y  : φ {a} x∈a z ) → Hom A (a ∧ b) c
  k x∈a {k} i = k ・ π'
  k x∈a ii = π
  k x∈a (iii ψ χ ) = < k x∈a ψ  , k x∈a χ  >
  k x∈a (iv ψ χ ) = k x∈a ψ  ・ < π , k x∈a χ  >
  k x∈a (v ψ ) = ( k x∈a ψ  ・ α ) *

--  toφ : {a b c : Obj A } → ( x∈a : Hom A ⊤ a ) → (z : Hom A b c ) → φ {a} x∈a z  
--  toφ {a} {b} {c} x∈a z = {!!}
