{-# OPTIONS --cubical-compatible --safe #-}

-- Free Group and it's Universal Mapping 
---- using Sets and forgetful functor

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

import Axiom.Extensionality.Propositional

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
module group { c c₁ c₂ ℓ : Level }  (f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m ) where

open import Category.Sets
open import Category.Cat
open import HomReasoning
open import Definitions
open import Relation.Binary.Structures
open import universal-mapping 
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

-- from https://github.com/danr/Agda-projects/blob/master/Category-Theory/FreeGroup.agda

-- fundamental homomorphism theorem
--

open import Algebra
open import Algebra.Structures
open import Algebra.Definitions
open import Algebra.Core
open import Algebra.Bundles

open import Data.Product
import Function.Definitions as FunctionDefinitions

import Algebra.Morphism.Definitions as MorphismDefinitions
open import Algebra.Morphism.Structures 

open import Tactic.MonoidSolver using (solve; solve-macro)

--
-- Given two groups G and H and a group homomorphism f : G → H,
-- let K be a normal subgroup in G and φ the natural surjective homomorphism G → G/K
-- (where G/K is the quotient group of G by K).
-- If K is a subset of ker(f) then there exists a unique homomorphism h: G/K → H such that f = h∘φ.
--     https://en.wikipedia.org/wiki/Fundamental_theorem_on_homomorphisms
--
--       f
--    G --→ H
--    |   /
--  φ |  / h
--    ↓ /
--    G/K
--

import Relation.Binary.Reasoning.Setoid as EqReasoning

_<_∙_> :  (m : Group c c )  →    Group.Carrier m →  Group.Carrier m →  Group.Carrier m
m < x ∙ y > =  Group._∙_ m x y

infixr 9 _<_∙_>

--
--  Coset : N : NormalSubGroup →  { a ∙ n | G ∋ a , N ∋ n }
--


open GroupMorphisms


GR : {c l : Level } → Group c l → RawGroup c l
GR G = record {
     Carrier        = Carrier G
     ; _≈_          = _≈_ G
     ; _∙_          = _∙_ G
     ; ε            = ε G
     ; _⁻¹          = _⁻¹ G
  } where open Group

grefl : {c l : Level } → (G : Group c l ) → {x : Group.Carrier G} → Group._≈_ G x x
grefl G = IsGroup.refl ( Group.isGroup G )

gsym : {c l : Level } → (G : Group c l ) → {x y : Group.Carrier G} → Group._≈_ G x y → Group._≈_ G y x
gsym G = IsGroup.sym ( Group.isGroup G )

gtrans : {c l : Level } → (G : Group c l ) → {x y z : Group.Carrier G} → Group._≈_ G x y → Group._≈_ G y z → Group._≈_ G x z
gtrans G = IsGroup.trans ( Group.isGroup G )

record NormalSubGroup (A : Group c c )  : Set c  where
   open Group A
   field  
       ⟦_⟧ : Group.Carrier A → Group.Carrier A 
       normal :  IsGroupHomomorphism (GR A) (GR A)  ⟦_⟧
       comm : {a b :  Carrier } → b ∙ ⟦ a ⟧  ≈ ⟦ a ⟧  ∙ b 

-- Set of a ∙ ∃ n ∈ N
--
record aN {A : Group c c }  (N : NormalSubGroup A ) (x : Group.Carrier A  ) : Set c where 
    open Group A
    open NormalSubGroup N
    field 
        a n : Group.Carrier A 
        aN=x :  a ∙ ⟦ n ⟧ ≈ x

open import Tactic.MonoidSolver using (solve; solve-macro)


_/_ : (A : Group c c ) (N  : NormalSubGroup A ) → Group c c
_/_ A N  = record {
    Carrier  = (x : Group.Carrier A  ) → aN N x
    ; _≈_      = _=n=_
    ; _∙_      = qadd 
    ; ε        = qid
    ; _⁻¹      = λ f x → record { a = x ∙ ⟦ n (f x) ⟧  ⁻¹  ; n = n (f x)  ; aN=x = ?  }
    ; isGroup = record { isMonoid  = record { isSemigroup = record { isMagma = record {
       isEquivalence = record {refl = grefl A  ; trans = ? ; sym = ? }
       ; ∙-cong = ? }
       ; assoc = ? }
       ; identity =  idL , (λ q → ? )  }
       ; inverse   = ( (λ x → ? ) , (λ x → ? ))  
       ; ⁻¹-cong   = λ i=j → ?
      }
   } where
       open Group A
       open aN
       open NormalSubGroup N
       open IsGroupHomomorphism normal 
       open EqReasoning (Algebra.Group.setoid A)
       _=n=_ : (f g : (x : Group.Carrier A  )  → aN N x ) →  Set c
       f =n= g = {x : Group.Carrier A  } → ⟦ n (f x) ⟧  ≈ ⟦ n (g x) ⟧  
       qadd : (f g : (x : Group.Carrier A  )  → aN N x ) → (x : Group.Carrier A  )  → aN N x
       qadd f g x = record { a = x ⁻¹ ∙ a (f x) ∙ a (g x) ; n = n (f x) ∙ n (g x) ; aN=x = q00 } where
           q00 : ( x ⁻¹ ∙  a (f x) ∙ a (g x)  ) ∙ ⟦ n (f x) ∙ n (g x) ⟧  ≈ x
           q00 = begin 
              ( x ⁻¹ ∙ a (f x) ∙ a (g x) ) ∙ ⟦ n (f x) ∙ n (g x) ⟧  ≈⟨ ∙-cong (assoc _ _ _) (homo _ _ ) ⟩
              x ⁻¹ ∙ (a (f x) ∙ a (g x) ) ∙ ( ⟦ n (f x) ⟧  ∙ ⟦ n (g x) ⟧ ) ≈⟨ solve monoid ⟩
              x ⁻¹ ∙ (a (f x) ∙ ((a (g x)  ∙ ⟦ n (f x) ⟧ ) ∙ ⟦ n (g x) ⟧ )) ≈⟨ ∙-cong (grefl A) (∙-cong (grefl A) (∙-cong comm (grefl A) ))  ⟩
              x ⁻¹ ∙ (a (f x) ∙ ((⟦ n (f x) ⟧  ∙ a (g x)) ∙ ⟦ n (g x) ⟧ ))  ≈⟨ solve monoid ⟩
              x ⁻¹ ∙ (a (f x) ∙ ⟦ n (f x) ⟧ ) ∙ (a (g x) ∙ ⟦ n (g x) ⟧ )  ≈⟨ ∙-cong (grefl A) (aN=x (g x)  ) ⟩
              x ⁻¹ ∙ (a (f x) ∙ ⟦ n (f x) ⟧ ) ∙ x   ≈⟨ ∙-cong (∙-cong (grefl A) (aN=x (f x))) (grefl A)  ⟩
              (x ⁻¹ ∙ x ) ∙ x   ≈⟨ ∙-cong (proj₁ inverse _ ) (grefl A)  ⟩
              ε ∙ x  ≈⟨ solve monoid  ⟩
              x ∎ 
       qid : ( x : Carrier ) → aN N x
       qid x = record { a = x  ; n = ε  ; aN=x = qid1 } where
           qid1 : x ∙ ⟦ ε ⟧ ≈ x
           qid1 = begin
              x ∙ ⟦ ε ⟧ ≈⟨ ∙-cong (grefl A) ε-homo ⟩
              x ∙ ε  ≈⟨ solve monoid ⟩
              x ∎ 
       qinv : (( x : Carrier ) → aN N x) → ( x : Carrier ) → aN N x
       qinv f x = record { a = x ∙ ⟦ n (f x) ⟧  ⁻¹  ; n = n (f x)  ; aN=x = qinv1  } where
             qinv1 : x ∙ ⟦ n (f x) ⟧ ⁻¹ ∙ ⟦ n (f x) ⟧ ≈ x
             qinv1 = begin
              x ∙ ⟦ n (f x) ⟧ ⁻¹ ∙ ⟦ n (f x) ⟧ ≈⟨ ? ⟩
              x ∙ ⟦ (n (f x)) ⁻¹ ⟧  ∙ ⟦ n (f x) ⟧ ≈⟨ ? ⟩
              x ∙ ⟦ ((n (f x)) ⁻¹ )  ∙ n (f x) ⟧ ≈⟨ ? ⟩
              x ∙ ⟦ ε ⟧ ≈⟨ ∙-cong (grefl A) ε-homo ⟩
              x ∙ ε  ≈⟨ solve monoid ⟩
              x ∎ 
       idL : (f : (x  : Carrier )→  aN N x) → (qadd qid f ) =n= f 
       idL f = ?

-- K ⊂ ker(f)
K⊆ker : (G H : Group c c)  (K : NormalSubGroup G) (f : Group.Carrier G → Group.Carrier H ) → Set c
K⊆ker G H K f = (x : Group.Carrier G ) → f ( ⟦ x ⟧ ) ≈ ε   where
  open Group H
  open NormalSubGroup K

open import Function.Surjection
open import Function.Equality

module _ (G : Group c c) (K : NormalSubGroup G) where
    open Group G
    open aN
    open NormalSubGroup K
    open IsGroupHomomorphism normal 

    φ : Group.Carrier G → Group.Carrier (G / K )
    φ g x = record { a = x ; n = ε ; aN=x = gtrans G ( ∙-cong (grefl G) ε-homo) (solve monoid) } where

    φ-homo : IsGroupHomomorphism (GR G) (GR (G / K)) φ 
    φ-homo = ?

    φe : (Algebra.Group.setoid G)  Function.Equality.⟶ (Algebra.Group.setoid (G / K))
    φe = record { _⟨$⟩_ = φ ; cong = φ-cong  }  where
           φ-cong : {f g : Carrier } → f ≈ g  → {x : Carrier } →  ⟦ n (φ f x ) ⟧ ≈ ⟦ n (φ g x ) ⟧ 
           φ-cong = ?

    inv-φ : Group.Carrier (G / K ) → Group.Carrier G
    inv-φ f = ⟦ n (f ε) ⟧ 

    φ-surjective : Surjective φe 
    φ-surjective = record { from = record { _⟨$⟩_ = inv-φ ; cong = λ {f} {g} → cong-i {f} {g} }  ; right-inverse-of = is-inverse } where
           cong-i : {f g : Group.Carrier (G / K ) } → ({x : Carrier } →  ⟦ n (f x) ⟧ ≈ ⟦ n (g x) ⟧ ) → inv-φ f ≈ inv-φ g
           cong-i = ?
           is-inverse : (f : (x : Carrier) → aN K x ) →  {y : Carrier} → ⟦ n (φ (inv-φ f) y) ⟧ ≈ ⟦ n (f y) ⟧
           is-inverse = ?
 
record FundamentalHomomorphism (G H : Group c c )
    (f : Group.Carrier G → Group.Carrier H ) 
    (homo : IsGroupHomomorphism (GR G) (GR H) f ) 
    (K : NormalSubGroup G ) (kf : K⊆ker G H K f) :  Set c where
  open Group H
  field
    h : Group.Carrier (G / K ) → Group.Carrier H
    h-homo :  IsGroupHomomorphism (GR (G / K) ) (GR H) h
    is-solution : (x : Group.Carrier G)  →  f x ≈ h ( φ G K x )
    unique : (h1 : Group.Carrier (G / K ) → Group.Carrier H)  → 
       ( (x : Group.Carrier G)  →  f x ≈ h1 ( φ G K x ) ) → ( ( x : Group.Carrier (G / K)) → h x ≈ h1 x )

postulate 
  FundamentalHomomorphismTheorm : (G H : Group c c)
    (f : Group.Carrier G → Group.Carrier H )
    (homo : IsGroupHomomorphism (GR G) (GR H) f )
    (K : NormalSubGroup G ) → (kf : K⊆ker G H K f)   → FundamentalHomomorphism G H f homo K kf

Homomorph : ?
Homomorph = ?

-- _==_ : ?
-- _==_ = ?

_*_ : ?
_*_ = ?

morph : ?
morph = ?

isGroups : IsCategory (Group c c) ? ? ? ?
isGroups  = record  { isEquivalence =  isEquivalence1 
                    ; identityL =  refl
                    ; identityR =  refl
                    ; associative = refl
                    ; o-resp-≈ =    λ {a} {b} {c} {f} {g} {h} {i} → ? -- o-resp-≈ {a} {b} {c} {f} {g} {h} {i}
                    }
     where
        isEquivalence1 : { a b : (Group c c) } → ?
        isEquivalence1  =      -- this is the same function as A's equivalence but has different types
           record { refl  = refl
             ; sym   = sym
             ; trans = trans
             } 
        o-resp-≈ :  {a b c' :  Group c c } {f g : ? } → {h i : ? }  → 
                          f ==  g → h ==  i → (h * f) ==  (i * g)
        o-resp-≈ {a} {b} {c} {f} {g} {h} {i} f==g h==i =  let open EqReasoning (Algebra.Group.setoid ?) in begin
             morph ( h * f )
         ≈⟨ ? ⟩
             morph ( i * g )
         ∎  where
            open Group c
            lemma11 : (x : Group.Carrier a) → morph (h * f) x ≈ morph (i * g) x
            lemma11 x =   let open EqReasoning (Algebra.Group.setoid c) in begin
                  morph ( h * f ) x ≈⟨ grefl c   ⟩
                  morph h ( ( morph f ) x ) ≈⟨ ?  ⟩
                  morph h ( morph g x ) ≈⟨ ?  ⟩
                  morph i ( morph g x ) ≈⟨ grefl c ⟩
                  morph ( i * g ) x ∎

Groups : Category _ _ _
Groups  =
  record { Obj =  Group c c
         ; Hom = ?
         ; _o_ = _*_  
         ; _≈_ = _==_
         ; Id  =  ?
         ; isCategory = ? -- isGroups 
           }

open import Data.Unit

GC : (G : Obj Groups ) → Category c c (suc c)
GC G = record { Obj = Lift c ⊤ ; Hom = λ _ _ → Group.Carrier G ; _o_ = Group._∙_ G }

F : (G H : Obj Groups ) → (f : Homomorph G H ) → (K : NormalSubGroup G)  →  Functor (GC H) (GC (G / K))
F G H f K = record { FObj = λ _ → lift  tt ; FMap = λ x y → record { a = ? ; n = ? ; x=aN = ?  } ; isFunctor = ?  }

--       f                f   ε
--    G --→ H          G --→  H (a)
--    |   /            |    /
--  φ |  / h         φ |   /h ↑
--    ↓ /              ↓  /
--    G/K              G/K

fundamentalTheorem : (G H : Obj Groups ) → (K : NormalSubGroup G) → (f : Homomorph G H ) 
     → ( kerf⊆K : (x : Group.Carrier G) → aN K x  → morph f x ≡ Group.ε H  )
     → coUniversalMapping (GC H) (GC (G / K)) (F G H f K )
fundamentalTheorem G H K f kerf⊆K = record { U = λ _ → lift tt ; ε = λ _ g → record { a = ? ; n = ? ; x=aN = ? }  
   ; _* = λ {b} {a} g → solution {b} {a} g ; iscoUniversalMapping 
       = record { couniversalMapping = ?  ; uniquness = ? }}  where
     m : Homomorph G G
     m = NormalSubGroup.normal K 
     φ⁻¹ : Group.Carrier (G / K) → Group.Carrier G
     φ⁻¹ = ?
     solution : {b : Obj (GC (G / K))} {a : Obj (GC H)} { f0 : Hom (GC (G / K)) (lift tt) b} →
            GC (G / K) [ GC (G / K) [ (λ g → record { a = ? ; n = ? ; x=aN = ? }) o
                (λ y → record { a = ? ; n = ? ; x=aN = ? }) ] ≈ f0 ]
     solution = ?
     is-solution :  ?
     is-solution a b g = ?
   

