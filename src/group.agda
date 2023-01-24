-- Free Group and it's Universal Mapping 
---- using Sets and forgetful functor

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
module group { c c₁ c₂ ℓ : Level }   where

open import Category.Sets
open import Category.Cat
open import HomReasoning
open import cat-utility
open import Relation.Binary.Structures
open import universal-mapping 
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

-- from https://github.com/danr/Agda-projects/blob/master/Category-Theory/FreeGroup.agda

open import Algebra
open import Algebra.Definitions -- using (Op₁; Op₂)
open import Algebra.Core
open import Algebra.Structures
open import Data.Product

record ≡-Group : Set (suc c) where
  infixr 9 _∙_
  field
    Carrier  : Set c
    _∙_      : Op₂ Carrier
    ε        : Carrier
    _⁻¹      : Carrier → Carrier
    isGroup : IsGroup _≡_ _∙_ ε _⁻¹

_<_∙_> :  (m : ≡-Group)  →    ≡-Group.Carrier m →  ≡-Group.Carrier m →  ≡-Group.Carrier m
m < x ∙ y > =  ≡-Group._∙_ m x y

infixr 9 _<_∙_>

record Homomorph ( a b : ≡-Group )  : Set c where
  field
      morph :  ≡-Group.Carrier a →  ≡-Group.Carrier b  
      identity     :  morph (≡-Group.ε a)   ≡  ≡-Group.ε b
      inverse      :  ∀{x} → morph ( ≡-Group._⁻¹ a x)  ≡   ≡-Group._⁻¹ b (morph  x) 
      homo :  ∀{x y} → morph ( a < x ∙ y > ) ≡ b < morph  x  ∙ morph  y >

open Homomorph

_*_ : { a b c : ≡-Group } → Homomorph b c → Homomorph a b → Homomorph a c
_*_ {a} {b} {c} f g =  record {
      morph = λ x →  morph  f ( morph g x ) ;
      identity  = identity1 ;
      inverse  = inverse1 ;
      homo  = homo1 
   } where
      open  ≡-Group 
      identity1 : morph f ( morph g (ε a) )  ≡  ε c
      identity1 = let open ≡-Reasoning in begin
         morph f (morph g (ε a)) ≡⟨  cong (morph f ) ( identity g )  ⟩
         morph f (ε b) ≡⟨  identity f  ⟩
         ε c ∎ 
      homo1 :  ∀{x y} → morph f ( morph g ( a < x ∙  y > )) ≡ ( c <   (morph f (morph  g x )) ∙(morph f (morph  g y) ) > )
      homo1 {x} {y} = let open ≡-Reasoning in begin
         morph f (morph g (a < x ∙ y >)) ≡⟨  cong (morph f ) ( homo g) ⟩
         morph f (b < morph g x ∙ morph g y >) ≡⟨  homo f ⟩
         c < morph f (morph g x) ∙ morph f (morph g y) > ∎ 
      inverse1 : {x : Carrier a} → morph f (morph g ((a ⁻¹) x)) ≡ (c ⁻¹) (morph f (morph g x))
      inverse1 {x} = begin 
         morph f (morph g (_⁻¹ a x))  ≡⟨  cong (morph f) (inverse g) ⟩
         morph f (_⁻¹ b (morph g x))   ≡⟨ inverse f ⟩
         _⁻¹ c (morph f (morph g x)) ∎ where  open ≡-Reasoning 


M-id : { a : ≡-Group } → Homomorph a a 
M-id = record { morph = λ x → x  ; identity = refl ; homo = refl ; inverse = refl }

_==_ : { a b : ≡-Group } → Homomorph a b → Homomorph a b → Set c 
_==_  f g =  morph f ≡ morph g

-- Functional Extensionality Axiom (We cannot prove this in Agda / Coq, just assumming )
-- postulate extensionality : { a b : Obj A } {f g : Hom A a b } → (∀ {x} → (f x ≡ g x))  → ( f ≡ g ) 
-- postulate extensionality : Relation.Binary.PropositionalEquality.Extensionality c c 

isGroups : IsCategory ≡-Group Homomorph _==_  _*_  (M-id)
isGroups  = record  { isEquivalence =  isEquivalence1 
                    ; identityL =  refl
                    ; identityR =  refl
                    ; associative = refl
                    ; o-resp-≈ =    λ {a} {b} {c} {f} {g} {h} {i} → o-resp-≈ {a} {b} {c} {f} {g} {h} {i}
                    }
     where
        isEquivalence1 : { a b : ≡-Group } → IsEquivalence {_} {_} {Homomorph a b}  _==_ 
        isEquivalence1  =      -- this is the same function as A's equivalence but has different types
           record { refl  = refl
             ; sym   = sym
             ; trans = trans
             } 
        o-resp-≈ :  {a b c :  ≡-Group } {f g : Homomorph a b } → {h i : Homomorph b c }  → 
                          f ==  g → h ==  i → (h * f) ==  (i * g)
        o-resp-≈ {a} {b} {c} {f} {g} {h} {i} f==g h==i =  let open ≡-Reasoning in begin
             morph ( h * f )
         ≡⟨ cong ( λ  g → ( ( λ (x : ≡-Group.Carrier a ) →  g x ) )) (extensionality (Sets ) {≡-Group.Carrier a} lemma11) ⟩
             morph ( i * g )
         ∎  where
            lemma11 : (x : ≡-Group.Carrier a) → morph (h * f) x ≡ morph (i * g) x
            lemma11 x =   let open ≡-Reasoning in begin
                  morph ( h * f ) x ≡⟨⟩
                  morph h ( ( morph f ) x ) ≡⟨   cong ( λ y -> morph h ( y x ) )  f==g ⟩
                  morph h ( morph g x ) ≡⟨   cong ( λ y -> y ( morph g  x ) )  h==i ⟩
                  morph i ( morph g x ) ≡⟨⟩
                  morph ( i * g ) x ∎

Groups : Category _ _ _
Groups  =
  record { Obj =  ≡-Group 
         ; Hom = Homomorph
         ; _o_ = _*_  
         ; _≈_ = _==_
         ; Id  =  M-id
         ; isCategory = isGroups 
           }

record NormalGroup (A : Obj Groups )  : Set (suc c) where
   field 
       normal :  Hom Groups A A 
       comm : {a b :  ≡-Group.Carrier A} → A < b ∙ morph normal a > ≡ A < morph normal a ∙ b >

-- Set of a ∙ ∃ n ∈ N
--
record aN {A : Obj Groups }  (N : NormalGroup A ) (x : ≡-Group.Carrier A  ) : Set c where 
    field 
        a n : ≡-Group.Carrier A 
        x=aN : A < a ∙ morph (NormalGroup.normal N) n > ≡ x

open import Tactic.MonoidSolver using (solve; solve-macro)

qadd : (A : Obj Groups ) (N  : NormalGroup A ) → (f g : (x : ≡-Group.Carrier A  )  → aN N x ) → (x : ≡-Group.Carrier A  )  → aN N x
qadd A N f g x = qadd1 where
       open ≡-Group A
       open aN
       open NormalGroup 
       qadd1 : aN N x
       qadd1 = record { a = x ⁻¹ ∙ a (f x) ∙ a (g x) ; n = n (f x) ∙ n (g x) ; x=aN = q00 } where
          m = morph (normal N)
          q00 : ( x ⁻¹ ∙  a (f x) ∙ a (g x)  ) ∙ m (n (f x) ∙ n (g x))  ≡ x
          q00 = begin
             (x ⁻¹ ∙ (a (f x) ∙ a (g x))) ∙ m (n (f x) ∙ n (g x))  ≡⟨ ? ⟩ 
             (a (f x) ∙ a (g x) ) ∙ m (n (f x) ∙ n (g x)) ∙ x ⁻¹ ≡⟨ cong ? (homo (normal N))  ⟩
             (a (f x) ∙ a (g x) ) ∙ (m (n (f x)) ∙ m (n (g x))) ∙ x ⁻¹  ≡⟨ solve mono  ⟩
             (a (f x) ∙ ((a (g x)  ∙ m (n (f x))) ∙ m (n (g x)))) ∙ x ⁻¹ ≡⟨ cong (λ k → ? ) (comm N) ⟩
             (a (f x) ∙ ((m (n (f x))  ∙ a (g x)) ∙ m (n (g x)))) ∙ x ⁻¹ ≡⟨ solve mono ⟩
             (a (f x) ∙ m (n (f x)) ) ∙ ((a (g x) ∙ m (n (g x))) ∙ x ⁻¹)  ≡⟨ cong (λ k → ? ) ?   ⟩
             (a (f x) ∙ m (n (f x)) ) ∙ (x ∙ x ⁻¹)  ≡⟨ ?  ⟩
             (a (f x) ∙ m (n (f x)) ) ∙ ε  ≡⟨ ?  ⟩
             (a (f x) ∙ m (n (f x)) )  ≡⟨ x=aN (f x)  ⟩
             x ∎ where 
                open ≡-Reasoning
                open IsGroup isGroup
                mono : Monoid _ _
                mono = record {isMonoid = isMonoid }

_/_ : (A : Obj Groups ) (N  : NormalGroup A ) → ≡-Group 
_/_ A N  = record {
    Carrier  = (x : ≡-Group.Carrier A  ) → aN N x
    ; _∙_      = qadd A N 
    ; ε        = λ x → record { a = x  ; n = ε  ; x=aN = ?  }
    ; _⁻¹      = λ f x → record { a = x ∙ (morph (normal N) (n (f x))) ⁻¹  ; n = n (f x)  ; x=aN = ?  }
    ; isGroup = record { isMonoid  = record { isSemigroup = record { isMagma = record {
       isEquivalence = record {refl = refl ; trans = trans ; sym = sym }
       ; ∙-cong = ? }
       ; assoc = ? }
       ; identity = ( (λ q → ? ) , (λ q → ? ))  }
       ; inverse   = ( (λ x → ? ) , (λ x → ? ))  
       ; ⁻¹-cong   = λ i=j → ?
      }
   } where
       open ≡-Group A
       open aN
       open NormalGroup 

φ : (G : Obj Groups ) (K  : NormalGroup G ) → Homomorph G (G / K )
φ = ?

GC : (G : Obj Groups ) → Category c c (suc c)
GC G = ?

U : (G H : Obj Groups ) → (f : Homomorph G H ) →  Functor (GC G) (GC H)
U = ?


fundamentalTheorem : (G H : Obj Groups ) → (K : NormalGroup G) → (f : Homomorph G H ) → UniversalMapping (GC G) (GC (G / K)) (U G H f )
fundamentalTheorem G H K f = record { F = morph (φ G K)  ; η = eta ; _* = ? ; isUniversalMapping 
       = record { universalMapping = λ {a} {b} {g} → is-solution a b g ; uniquness = ? }}  where
     eta :  (a : Obj (GC G)) → Hom (GC G) a (Functor.FObj (U G H f) ( (morph (φ G K) a)) )
     eta = ?
     solution : {a : Obj (GC G)} {b : Obj (GC (G / K))} → Hom (GC G) a (Functor.FObj (U G H f) b) → Hom (GC (G / K)) (morph (φ G K) a) b
     solution = ?
     is-solution :  (a : Obj (GC G)) (b : Obj (GC (G / K)))
            (g : Hom (GC G) a (Functor.FObj (U G H f) b)) →
            (GC G) [ (GC G) [ Functor.FMap (U G H f) (solution {a} {b} g) o eta a ] ≈ g ]
     is-solution = ?
   


