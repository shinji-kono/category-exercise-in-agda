{-# OPTIONS --cubical-compatible --safe #-}

module bi-ccc where

open import Category
open import CCC
open import Level
open import HomReasoning
open import Definitions

record IsBICCC {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) 
      ( ⊥ : Obj A)  -- ０
      ( □ : (a : Obj A ) → Hom A ⊥ a )
      ( _∨_ :  Obj A → Obj A → Obj A  )
      ( [_,_] : {a b c : Obj A } → Hom A a c → Hom A b c → Hom A (a ∨ b) c  )
      ( κ : {a b : Obj A }  → Hom A a (a ∨ b)  )
      ( κ' : {a b : Obj A } → Hom A b (a ∨ b)  )
             :  Set ( c₁  ⊔  c₂ ⊔ ℓ ) where
   field
       e5 : {a : Obj A} → { f : Hom A ⊥ a } →  A [ f ≈ □ a ]
       e6a : {a b c : Obj A} → { f : Hom A a c }{ g : Hom A b c } →  A [ A [ [ f , g ] o κ  ] ≈ f ]
       e6b : {a b c : Obj A} → { f : Hom A a c }{ g : Hom A b c } →  A [ A [ [ f , g ] o κ'  ] ≈ g ]
       e6c : {a b c : Obj A} → { h : Hom A (a ∨ b ) c } →  A [ [ A [ h o κ ] , A [ h o κ' ] ] ≈ h ]
       κ-cong :  {a b c : Obj A} → { f f' : Hom A a c }{ g g' : Hom A b c } → A [ f ≈ f' ]  → A [ g ≈ g' ]  →  A [ [ f , g ]  ≈ [ f' , g' ] ] 

record BICCC {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) :  Set ( c₁  ⊔  c₂ ⊔ ℓ ) where
   field
      ⊥ : Obj A
      □ : (a : Obj A ) → Hom A ⊥ a 
      _∨_ :  Obj A → Obj A → Obj A  
      [_,_] : {a b c : Obj A } → Hom A a c → Hom A b c → Hom A (a ∨ b) c  
      κ : {a b : Obj A }  → Hom A a (a ∨ b)  
      κ' : {a b : Obj A } → Hom A b (a ∨ b)  
      isBICCC : IsBICCC A ⊥ □ _∨_  [_,_] κ κ'

bi-ccc-⊥ : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) → (C : CCC A ) → (B : BICCC A ) → {a : Obj A} → Hom A a (BICCC.⊥ B) → Iso A a (BICCC.⊥ B)
bi-ccc-⊥ A C B {a} f = record {
      ≅→ = f
    ; ≅← = □ a
    ; iso→  = bi-ccc-1
    ; iso←  = bi-ccc-2 } where
       open ≈-Reasoning A
       open CCC.CCC C
       open BICCC B
       bi-hom← : {a c : Obj A } → Hom A (a ∧ ⊥) c → Hom A ⊥ (c <= a )
       bi-hom← f = (f o < π' , π > ) *
       bi-hom→ : {a c : Obj A } →  Hom A ⊥ (c <= a ) → Hom A (a ∧ ⊥) c
       bi-hom→ f =  ε o ( < π' , π > o < π , f o π' > )
       bi-hom-iso : {a : Obj A } → {f : Hom A  (a ∧ ⊥) (a ∧ ⊥)}  →  A [ bi-hom→ (bi-hom← f )  ≈ f ] 
       bi-hom-iso {a} {f} = begin
            bi-hom→ (bi-hom← f )
          ≈⟨⟩
            ε o ( < π' , π > o < π , ((f o < π' , π > ) *) o π' > )
          ≈⟨ cdr (IsCCC.π-exchg isCCC)  ⟩
            ε o ( < ((f o < π' , π > ) *) o π' , π > )
          ≈⟨ cdr ( IsCCC.π-cong isCCC refl-hom (sym idL)) ⟩
            ε o ( < ((f o < π' , π > ) *) o π' , id1 A _ o π > )
          ≈↑⟨ cdr (IsCCC.exchg-π isCCC) ⟩
            ε o (( < ((f o < π' , π > ) *) o π , id1 A _ o π' > ) o < π' , π > )
          ≈⟨ cdr (car ( IsCCC.π-cong isCCC refl-hom idL)) ⟩
            ε o (( < ((f o < π' , π > ) *) o π , π' > ) o < π' , π > )
          ≈⟨ assoc ⟩
            (ε o ( < ((f o < π' , π > ) *) o π , π' > )) o < π' , π > 
          ≈⟨ car (IsCCC.e4a isCCC) ⟩
            (f o < π' , π >) o < π' , π >
          ≈⟨ sym assoc ⟩
            f o (< π' , π > o < π' , π >)
          ≈⟨ cdr (IsCCC.π'π isCCC) ⟩
            f o id1 A _
          ≈⟨ idR ⟩
            f  
          ∎ 
       bi-hom-cong : {a c : Obj A } → {f g : Hom A ⊥ (c <= a )} → A [ f ≈ g ]  →  A [ bi-hom→ f   ≈ bi-hom→ g ]
       bi-hom-cong f=g = cdr ( cdr (IsCCC.π-cong isCCC refl-hom (car f=g) ))
       bi-ccc-0 :  A [ A [ □ ( a ∧ ⊥ ) o π' ] ≈ id1 A ( a ∧ ⊥ ) ]
       bi-ccc-0 = begin
             □ ( a ∧ ⊥ ) o π'
          ≈↑⟨ bi-hom-iso ⟩
             bi-hom→ (bi-hom← ( □ ( a ∧ ⊥ ) o π' ))
          ≈⟨ bi-hom-cong  (IsBICCC.e5 isBICCC ) ⟩
             bi-hom→ ( □ ( ( a ∧ ⊥ ) <=  a) )
          ≈↑⟨ bi-hom-cong  (IsBICCC.e5 isBICCC ) ⟩
             bi-hom→ (bi-hom← (id1 A ( a ∧ ⊥ )))
          ≈⟨ bi-hom-iso ⟩
             id1 A ( a ∧ ⊥ )
          ∎ 
       bi-ccc-1 :  A [ A [ □ a o f ] ≈ id1 A a ]
       bi-ccc-1 = begin
             □ a o f
          ≈⟨ resp (sym (IsCCC.e3b isCCC) ) (sym ( IsBICCC.e5 isBICCC)) ⟩
             (π  o  □ ( a ∧ ⊥ )) o (π' o < id1 A a , f > )
          ≈⟨ sym assoc ⟩
             π  o  ( □ ( a ∧ ⊥ ) o (π' o < id1 A a , f > ))
          ≈⟨ cdr (assoc) ⟩
             π  o  ( □ ( a ∧ ⊥ ) o π' ) o < id1 A a , f > 
          ≈⟨ cdr (car bi-ccc-0) ⟩
             π  o  id1 A _ o < id1 A a , f > 
          ≈⟨ cdr idL ⟩
             π  o  < id1 A a , f > 
          ≈⟨ IsCCC.e3a isCCC  ⟩
             id1 A a 
          ∎ 
       bi-ccc-2 :  A [ A [ f o □ a ] ≈ id1 A ⊥  ]
       bi-ccc-2 = begin
             f o □  a 
          ≈⟨ IsBICCC.e5 isBICCC  ⟩
             □  _ 
          ≈↑⟨ IsBICCC.e5 isBICCC  ⟩
             id1 A ⊥ 
          ∎ 

-- define boolean category ( bi-cartesian closed category wth ⊤ and ⊥ object )
-- Any bi-cartesian closed category is isomorpphic to the boolean category
