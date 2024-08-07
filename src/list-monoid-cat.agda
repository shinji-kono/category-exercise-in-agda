{-# OPTIONS --cubical-compatible --safe #-}

open import Category -- https://github.com/konn/category-agda
open import Level
open import HomReasoning
open import Definitions
open import Relation.Binary


module list-monoid-cat (c : Level ) where

infixr 40 _::_
data  List  (A : Set ) : Set  where
   [] : List A
   _::_ : A → List A → List A


infixl 30 _++_
_++_ :   {A : Set } → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data ListObj : Set where
  * : ListObj

open  import  Relation.Binary.Core
open  import  Relation.Binary.PropositionalEquality

≡-cong = Relation.Binary.PropositionalEquality.cong 

isListCategory : (A : Set) → IsCategory ListObj (λ a b → List A) _≡_  _++_  []
isListCategory  A = record  { isEquivalence =  isEquivalence1 {A}
                    ; identityL =   list-id-l
                    ; identityR =   list-id-r
                    ; o-resp-≈ =    o-resp-≈ {A}
                    ; associative = λ {a} {b} {c} {d} {x} {y} {z} → list-assoc {A} {x} {y} {z}
                    }
     where
        list-id-l : { A : Set } → { x : List A } →  [] ++ x ≡ x
        list-id-l {_} {_} = refl
        list-id-r : { A : Set } → { x : List A } →  x ++ [] ≡ x
        list-id-r {_} {[]} =   refl
        list-id-r {A} {x :: xs} =  ≡-cong ( λ y → x :: y ) ( list-id-r {A} {xs} ) 
        list-assoc : {A : Set} → { xs ys zs : List A } →
              ( xs ++ ( ys ++ zs ) ) ≡ ( ( xs ++ ys ) ++ zs )
        list-assoc  {_} {[]} {_} {_} = refl
        list-assoc  {A} {x :: xs}  {ys} {zs} = ≡-cong  ( λ y  → x :: y ) 
                 ( list-assoc {A} {xs} {ys} {zs} )
        o-resp-≈ :  {A : Set} →  {f g : List A } → {h i : List A } → 
                          f ≡  g → h ≡  i → (h ++ f) ≡  (i ++ g)
        o-resp-≈  {A} refl refl = refl
        isEquivalence1 : {A : Set} → IsEquivalence {_} {_} {List A }  _≡_ 
        isEquivalence1 {A} =      -- this is the same function as A's equivalence but has different types
           record { refl  = refl
             ; sym   = sym
             ; trans = trans
             } 
ListCategory : (A : Set) → Category _ _ _
ListCategory A =
  record { Obj = ListObj
         ; Hom = λ a b → List  A
         ; _o_ = _++_ 
         ; _≈_ = _≡_
         ; Id  =  []
         ; isCategory = ( isListCategory A )
          }

open import Algebra.Structures
-- open import Algebra.FunctionProperties using (Op₁; Op₂)

data MonoidObj : Set c where
  ! : MonoidObj

record ≡-Monoid c : Set (suc c) where
  infixl 7 _∙_
  field
    Carrier  : Set c
    _∙_      : Carrier → Carrier → Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≡_ _∙_ ε

open ≡-Monoid 
open import Data.Product

isMonoidCategory : (M :  ≡-Monoid c) → IsCategory MonoidObj (λ a b → Carrier M ) _≡_  (_∙_  M) (ε M)
isMonoidCategory  M = record  { isEquivalence =  isEquivalence1 {M}
                    ; identityL =   λ {_} {_} {x} → (( proj₁ ( IsMonoid.identity ( isMonoid M )) ) x )
                    ; identityR =   λ {_} {_} {x} → (( proj₂ ( IsMonoid.identity ( isMonoid M )) ) x )
                    ; associative = λ {a} {b} {c} {d} {x} {y} {z} → sym ( (IsMonoid.assoc ( isMonoid M )) x y z )
                    ; o-resp-≈ =    o-resp-≈ {M}
                    }
     where
        o-resp-≈ :  {M :  ≡-Monoid c} →  {f g : Carrier M } → {h i : Carrier M } → 
                          f ≡  g → h ≡  i → (_∙_ M  h f) ≡  (_∙_ M i g)
        o-resp-≈  {A} refl refl = refl
        isEquivalence1 : {M :  ≡-Monoid c} → IsEquivalence {_} {_} {Carrier M }  _≡_ 
        isEquivalence1 {A} =      -- this is the same function as A's equivalence but has different types
           record { refl  = refl
             ; sym   = sym
             ; trans = trans
             } 
MonoidCategory : (M : ≡-Monoid c) → Category _ _ _
MonoidCategory M =
  record { Obj = MonoidObj
         ; Hom = λ a b → Carrier M 
         ; _o_ = _∙_  M
         ; _≈_ = _≡_
         ; Id  =  ε M
         ; isCategory = ( isMonoidCategory M )
          }

