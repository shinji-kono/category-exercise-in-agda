{-# OPTIONS --cubical-compatible --safe #-}

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level

module freyd where

open import Definitions
open import HomReasoning
open import Relation.Binary.Core
open Functor

-- C is small full subcategory of A ( C is image of F )
--    but we don't use smallness in this proof
--
-- pre-initial

record PreInitial {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) 
       (P : Obj A → Set ℓ)  : Set  (suc ℓ ⊔ (suc c₁ ⊔ suc c₂)) where
   field
      preinitialObj : Obj A 
      Pp : P preinitialObj
      preinitialArrow : ∀{a : Obj A } →  Hom A ( FObj (InclusiveFunctor A P )  record { s = preinitialObj; p = Pp } ) a 

-- initial object
--   now in Definitions
-- record HasInitialObject {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (i : Obj A) : Set  (suc ℓ ⊔ (suc c₁ ⊔ suc c₂)) where
--    field
--       initial :  ∀( a : Obj A ) →  Hom A i a
--       uniqueness  : { a : Obj A } →  ( f : Hom A i a ) → A [ f ≈  initial a ]

-- A complete catagory has initial object if it has PreInitial-FullSubcategory

open NTrans
open Limit
open IsLimit
open PreInitial
open Complete
open Equalizer
open IsEqualizer

initialFromPreInitialFullSubcategory : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ)
      (comp : Complete A)
      (P : Obj A → Set ℓ ) → 
      (PI : PreInitial A  P) → HasInitialObject A (limit-c comp (InclusiveFunctor A P))
initialFromPreInitialFullSubcategory A comp P PI = record {
      initial = initialArrow ; 
      uniqueness  = λ {a} f → lemma1 a f
    } where
      S = FullSubCategory A P
      F : Functor S A 
      F = InclusiveFunctor A P 
      pri : SObj A P
      pri = record { s = preinitialObj PI ; p = Pp PI }  
      a00 : Obj A
      a00 = limit-c comp F
      lim : ( Γ : Functor S A ) → Limit S A Γ 
      lim Γ =  climit comp Γ 
      u : NTrans S A (K S A a00) F
      u = t0 ( lim F )
      equ : {a b : Obj A} → (f g : Hom A a b)  → IsEqualizer A (equalizer-e comp f g ) f g
      equ f g = isEqualizer ( Complete.cequalizer comp f g  )
      ep : {a b : Obj A} → {f g : Hom A a b}  → Obj A 
      ep {a} {b} {f} {g} = equalizer-p comp f g
      ee :  {a b : Obj A} → {f g : Hom A a b}  → Hom A (ep {a} {b} {f} {g} ) a 
      ee {a} {b} {f} {g} = equalizer-e comp f g  
      f : Hom A  a00 (FObj F pri ) 
      f = TMap u pri 
      initialArrow :  ∀( a : Obj A )  →  Hom A a00 a
      initialArrow a  = A [ preinitialArrow PI {a}  o f ]
      equ-fi : { a : Obj A} → {f' : Hom A a00 a} → 
          IsEqualizer A ee ( A [ preinitialArrow PI {a} o  f ] ) f'
      equ-fi  {a} {f'} = equ ( A [ preinitialArrow PI {a} o  f ] ) f'
      e=id : {e : Hom A a00 a00} → ( {c : Obj S} → A [ A [ TMap u  c o  e ]  ≈  TMap u c ] ) → A [ e  ≈ id1 A a00 ]
      e=id  {e} uce=uc =  let open ≈-Reasoning (A) in
            begin
              e
            ≈↑⟨ limit-uniqueness  (isLimit (lim F)) ( λ {i} → uce=uc ) ⟩
              limit (isLimit (lim F)) a00 u 
            ≈⟨ limit-uniqueness (isLimit (lim F))  ( λ {i} → idR ) ⟩
              id1 A a00
            ∎
      kfuc=uc : {c : Obj S} {k1 : Obj A} →  {p : Hom A k1 a00} → A [ A [ TMap u  c  o  
              A [ p o A [ preinitialArrow PI {k1} o TMap u pri ] ] ]  
                      ≈ TMap u c ]
      kfuc=uc {c} {k1} {p} =  let open ≈-Reasoning (A) in
            begin
                 TMap u  c  o ( p o ( preinitialArrow PI {k1} o TMap u pri  ))
            ≈⟨ cdr assoc  ⟩
                 TMap u c o ((p o preinitialArrow PI) o TMap u pri)
            ≈⟨ assoc ⟩
                 (TMap u  c  o ( p o ( preinitialArrow PI {k1} ))) o TMap u pri  
            ≈⟨ nat u  ⟩
                  TMap u c o id1 A a00
            ≈⟨ idR ⟩
                 TMap u  c  
            ∎
      kfuc=1 : {k1 : Obj A} →  {p : Hom A k1 a00} → A [ A [ p o A [ preinitialArrow PI {k1} o TMap u pri ] ] ≈ id1 A a00 ]
      kfuc=1 {k1} {p} = e=id ( kfuc=uc )
      -- if equalizer has right inverse, f = g
      lemma2 :  (a b : Obj A) {c : Obj A} ( f g : Hom A a b ) 
            {e : Hom A c a } {e' : Hom A a c } ( equ : IsEqualizer A e f g ) (inv-e : A [ A [ e o e' ] ≈ id1 A a ] )
           → A [ f ≈ g ]
      lemma2 a b {c} f g {e} {e'} equ inv-e = let open ≈-Reasoning (A) in
            let open Equalizer in
            begin
                f
               ≈↑⟨ idR ⟩
                 f o  id1 A a 
               ≈↑⟨ cdr inv-e ⟩
                 f o  (  e o e'  ) 
               ≈⟨ assoc  ⟩
                 ( f o  e ) o e'  
               ≈⟨ car ( fe=ge equ ) ⟩ ( g o  e ) o e'  
               ≈↑⟨ assoc  ⟩
                 g o  (  e o e'  ) 
               ≈⟨ cdr inv-e   ⟩
                 g o  id1 A a
               ≈⟨ idR ⟩
                g
            ∎
      lemma1 : (a : Obj A) (f' : Hom A a00 a) → A [ f' ≈ initialArrow a ]
      lemma1 a f' = let open ≈-Reasoning (A) in 
             sym (
             begin
                 initialArrow a
             ≈⟨⟩
                 preinitialArrow PI {a} o  f
             ≈⟨ lemma2 a00 a (A [ preinitialArrow PI {a} o  f ]) f' {ee {a00} {a} {A [ preinitialArrow PI {a} o  f ]} {f'} } (equ-fi )
                      (kfuc=1 {ep} {ee} ) ⟩
                 f'
             ∎  )
 


