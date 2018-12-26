open import Category -- https://github.com/konn/category-agda
open import Level
--open import Category.HomReasoning
open import HomReasoning
open import cat-utility
open import Category.Cat

module code-data { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } where

-- DataObj is a set of code segment with reverse computation
record DataObj : Set (c₁ ⊔ c₂ ⊔ ℓ)  where
   field
      dom : Obj A
      codom : Obj A
      code : Hom A dom codom
      rev-code : Hom A codom dom
      id-left   :  A [ A [ code  o rev-code ]  ≈  id1 A codom ]
      id-right  :  A [ A [ rev-code  o code ]  ≈  id1 A dom ]

open DataObj

-- DataHom is a set of data segment with computational continuation 
record isDataHom (a : DataObj ) (b : DataObj ) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
   field
      continuation : Hom A (codom a) (dom b)
   data-dom = a
   data-codom = b

open isDataHom

DataHom : (a : DataObj ) (b : DataObj ) → Set (c₁ ⊔ c₂ ⊔ ℓ)
DataHom = λ a b →  isDataHom a b

DataId : { a : DataObj } → DataHom a a
DataId {a} = record {
      continuation = rev-code a
   }

_∙_ :  {a b c : DataObj } → DataHom b c → DataHom a b → DataHom a c
_∙_ {a} {b} {c} g f = record { continuation = A [ continuation g o A [ code b o continuation f ] ] }

_≗_ : {a : DataObj } {b : DataObj } (f g : DataHom a b ) → Set ℓ 
_≗_ {a} {b} f g = A [  continuation f ≈  continuation g ]

open import Relation.Binary.Core

isDataCategory : IsCategory DataObj DataHom _≗_ _∙_  DataId 
isDataCategory  = record  { isEquivalence =  isEquivalence 
                    ; identityL =   \{a} {b} {f} -> identityL a b f
                    ; identityR =   \{a} {b} {f} -> identityR a b f
                    ; o-resp-≈ =    \{a} {b} {c} {f} {g} {h} {i} -> o-resp {a} {b} {c} {f} {g} {h} {i}
                    ; associative = \{a} {b} {c} {d} {f} {g} {h} -> associative a b c d f g h
                    }
     where
         open ≈-Reasoning (A) 
         o-resp :  {A B C : DataObj} {f g : DataHom A B} {h i : DataHom B C} → f ≗ g → h ≗ i → (h ∙ f) ≗ (i ∙ g)
         o-resp {a} {b} {c} {f} {g} {h} {i} f≗g h≗i =  begin
                continuation (h ∙ f) 
           ≈⟨⟩
                continuation h o code b o continuation f
           ≈⟨  cdr ( cdr ( f≗g ))  ⟩
                continuation h o code b o continuation g
           ≈⟨ car h≗i ⟩
                continuation i  o code b o continuation g
           ≈⟨⟩
                continuation (i ∙ g)
           ∎ 
         associative : (a b c d : DataObj)  (f : DataHom c d) (g : DataHom b c) (h : DataHom a b) → (f ∙ (g ∙ h)) ≗ ((f ∙ g) ∙ h)
         associative a b c d f g h  = begin
               continuation (f ∙ (g ∙ h))
           ≈⟨⟩
               continuation f o code c o  continuation g  o code b o continuation h  
           ≈⟨ cdr assoc  ⟩
               continuation f o (code c o  continuation g)  o code b o continuation h  
           ≈⟨ assoc ⟩
               (continuation f o code c o continuation g) o code b o continuation h
           ≈⟨⟩
               continuation ((f ∙ g) ∙ h) 
           ∎
         identityL : (a : DataObj) (b : DataObj) (f : DataHom a b) → (DataId ∙ f) ≗ f
         identityL a b f  = begin
              continuation (DataId ∙ f) 
           ≈⟨⟩
              rev-code b o code b o continuation f 
           ≈⟨ assoc ⟩
               (rev-code b  o  code b ) o continuation f 
           ≈⟨ car ( id-right b) ⟩
               id1 A (dom b) o continuation f 
           ≈⟨ idL ⟩
              continuation f
           ∎
         identityR : (a : DataObj) (b : DataObj) (f : DataHom a b) → (f ∙ DataId  ) ≗ f
         identityR a b f  = begin
               continuation (f ∙ DataId) 
           ≈⟨⟩
               ( continuation f  o ( code a   o rev-code a ) )
           ≈⟨ cdr (id-left a) ⟩
               ( continuation f  o id1 A (codom a) )
           ≈⟨ idR ⟩
               continuation f
           ∎
         isEquivalence : {a : DataObj } {b : DataObj } →
               IsEquivalence {_} {_} {DataHom a b } _≗_
         isEquivalence {C} {D} =      -- this is the same function as A's equivalence but has different types
           record { refl  = refl-hom
             ; sym   = sym
             ; trans = trans-hom
           } 
DataCategory : Category (c₁ ⊔ c₂ ⊔ ℓ) (c₁ ⊔ c₂ ⊔ ℓ) ℓ
DataCategory =
  record { Obj = DataObj
         ; Hom = DataHom
         ; _o_ = _∙_ 
         ; _≈_ = _≗_
         ; Id  =  DataId 
         ; isCategory = isDataCategory
          }



open Functor
open NTrans

F : Obj A -> Obj DataCategory  
F d  = record {
      dom  = d
      ; codom = d
      ; code  = id1 A d
      ; rev-code  = id1 A d
      ; id-left = idL
      ; id-right = idR
   }  where open ≈-Reasoning (A)  

U : Functor  DataCategory A
U = record {
      FObj = \d -> codom  d
    ; FMap = \f -> A [ code ( data-codom f ) o continuation f ] 
    ; isFunctor = record {
             ≈-cong   =  \{a} {b} {f} {g} -> ≈-cong-1 {a} {b} {f} {g}
             ; identity = \{a} -> identity-1 {a}
             ; distr    = \{a b c f g} -> distr-1 {a} {b} {c} {f} {g}
      }
 } where
    open ≈-Reasoning (A) 
    ≈-cong-1 :  {a : Obj DataCategory} {b : Obj DataCategory} {f g : Hom DataCategory a b} → DataCategory [ f ≈ g ] → 
         A [ A [ code (data-codom f) o continuation f ] ≈ A [ code (data-codom g) o continuation g ] ]
    ≈-cong-1 {a} {b} {f} {g}  f≈g =  begin
              code (data-codom f) o continuation f 
           ≈⟨⟩
              code b o continuation f 
           ≈⟨ cdr f≈g ⟩
              code b o continuation g 
           ≈⟨⟩
              code (data-codom g) o continuation g 
           ∎
    identity-1 :  {a : Obj DataCategory} → A [ A [ code (data-codom (DataId {a})) o continuation (DataId {a}) ] ≈ id1 A (codom a) ]
    identity-1 {a} =   begin
              code (data-codom (DataId {a} )) o continuation (DataId  {a} )
           ≈⟨⟩
               code a o  rev-code a
           ≈⟨ id-left a ⟩
              id1 A (codom a)
           ∎
    distr-1 :  {a b c : Obj DataCategory} {f : Hom DataCategory a b} {g : Hom DataCategory b c} → 
             A [ A [ code (data-codom ( g ∙ f )) o continuation ( g ∙ f ) ] ≈
                A [ A [ code (data-codom g) o continuation g ] o A [ code (data-codom f) o continuation f ] ] ]
    distr-1 {a} {b} {c} {f} {g} =  begin
               code (data-codom (g ∙ f )) o continuation ( g ∙ f ) 
           ≈⟨⟩
                code c o continuation g o  code b o continuation f
           ≈⟨ assoc ⟩
                (code c o continuation g ) o  code b o continuation f
           ≈⟨⟩
               ( code (data-codom g) o continuation g ) o ( code (data-codom f) o continuation f )
           ∎

eta-map :   (a : Obj A) → Hom A a ( FObj U (F a) )
eta-map a = id1 A a


Lemma1 :  UniversalMapping A DataCategory U 
Lemma1 = record {
         F = F ;
         η = eta-map ;
         _* =  solution ;
         isUniversalMapping = record {
                    universalMapping  = \{a} {b} {f} -> universalMapping {a} {b} {f} ;
                    uniquness = \{a} {b} {f} {g} -> uniqueness {a} {b} {f} {g}
              }
  } where
    open ≈-Reasoning (A) 
    solution :  {a : Obj A} {b : Obj DataCategory} → Hom A a (FObj U b) → Hom DataCategory (F a) b
    solution {a} {b} f = record { continuation = A [ rev-code b o f ]  }
    universalMapping :  {a : Obj A} {b : Obj DataCategory} {f : Hom A a (FObj U b)} → A [ A [ FMap U (solution {a} {b} f) o eta-map a ] ≈ f ]
    universalMapping {a} {b} {f} = begin
                FMap U (solution {a} {b} f) o eta-map a 
           ≈⟨⟩
               (code b o ( rev-code b  o f))  o id1 A a
           ≈⟨ idR  ⟩
               code b o ( rev-code b  o f)
           ≈⟨ assoc  ⟩
               (code b o  rev-code b  ) o f
           ≈⟨ car (id-left b) ⟩
               id1 A (codom b) o f
           ≈⟨ idL ⟩
                f
           ∎
    uniqueness :  {a : Obj A} {b : Obj DataCategory} {f : Hom A a (FObj U b)}
        {g : Hom DataCategory (F a) b} →
        A [ A [ FMap U g o eta-map a ] ≈ f ] →
        DataCategory [ solution f ≈ g ]
    uniqueness {a} {b} {f} {g} Uη≈f  =  begin
               continuation (solution {a} {b} f)
           ≈⟨⟩
               rev-code b o f
           ≈⟨ sym (  cdr  Uη≈f   ) ⟩
               rev-code b o ( code b o continuation g ) o id1 A (codom (F a))
           ≈⟨  sym ( cdr assoc) ⟩
               rev-code b o code b o continuation g o id1 A (codom (F a))
           ≈⟨  assoc ⟩
               (rev-code b o  code b ) o continuation g  o id1 A (codom (F a))
           ≈⟨  car ( id-right b ) ⟩
               id (dom b) o continuation g o id1 A (codom (F a))
           ≈⟨ idL ⟩
               ( continuation g ) o id1 A (codom (F a))
           ≈⟨ idR ⟩
               continuation g
           ∎




