{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS --cubical-compatible --safe #-}

open import CCC
open import Level
open import Category
open import Definitions
open import HomReasoning
module ToposSub   {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (c : CCC A) (t : Topos A c ) (n : ToposNat A (CCC.１ c)) where

  open Topos
  open Equalizer
  open ≈-Reasoning A
  open CCC.CCC c

  open Functor
  open import Category.Sets hiding (_o_)
  open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym)

--             ○ b
--       b -----------→ 1
--       |              |
--     m |              | ⊤
--       ↓    char m    ↓
--       a -----------→ Ω

  record SubObject (a : Obj A) : Set (c₁ ⊔ c₂ ⊔ ℓ)  where
     field
        sb : Obj A
        sm : Hom A sb a 
        smono : Mono A sm

  postulate
    I : Set c₁
    small : Small A I 

  open import yoneda A I small


  module SubObjectFunctor
     (S : (a : Set (c₁ ⊔ c₂ ⊔ ℓ))  → Set c₂)
     (solv← : {x : Obj A} → S (SubObject x) → SubObject x)
     (solv→ : {x : Obj A} → SubObject x → S (SubObject x))
     (soiso← : {a : Obj A} → (x : SubObject a) → solv← (solv→ x) ≡ x)
     (soiso→ : {a : Obj A} → (x : S (SubObject a) ) → solv→ (solv← x) ≡ x)
     (≡←≈ :   {a b : Obj A } { x y : Hom A a b } →  (x≈y : A [ x ≈ y  ]) → x ≡ y) where

    open SubObject 

    Smap : {x y : Obj A} → Hom A y x → Hom Sets (S (SubObject x)) (S (SubObject y))
    Smap {x} {y} h s = solv→ record { sb = y ; sm = id1 A y ; smono = record { isMono = λ f g eq → sm1 f g eq } } where
         sm1 : {a : Obj A } → ( f g : Hom A a y ) → A [ A [ id1 A y o f ]  ≈ A [ id1 A y o g ] ] → A [ f  ≈ g ]
         sm1 f g eq = begin
              f ≈↑⟨ idL ⟩ 
              id1 A y o f ≈⟨ eq ⟩ 
              id1 A y o g ≈⟨ idL  ⟩ 
              g ∎  

    SubObjectFuntor  : Functor  (Category.op A)  (Sets {c₂})
    SubObjectFuntor  = record {
         FObj = λ x → S (SubObject x)
       ; FMap = Smap
       ; isFunctor  = record {
              identity = {!!}
            ; distr  = {!!}
            ; ≈-cong  = {!!}
          }
       } 

    open NTrans 
    sub→topos : (Ω : Obj A) → Representable A ≡←≈ SubObjectFuntor Ω → Topos A c
    sub→topos Ω R = record {
          Ω =  Ω
       ;  ⊤ = TMap (Representable.repr→ R) １ (solv→ record { sb = {!!} ; sm = {!!} ; smono = {!!} })
       ;  Ker = λ {a} h → record { equalizer-c = sb {!!}
          ; equalizer = sm {!!}
          ; isEqualizer = {!!}
          }
       ;  char = λ m mono → {!!} 
       ;  isTopos = record {
          char-uniqueness  = {!!}
       ;  ker-m = {!!}
          } }
 
    topos→rep : (t : Topos A c ) → Representable A ≡←≈ SubObjectFuntor (Topos.Ω t)
    topos→rep t = record {
        repr→ = record { TMap = λ a Sa → Topos.char t (sm (solv← Sa)) (smono (solv← Sa)) ; isNTrans = record { commute = {!!} } } -- Hom A a Ω
      ; repr← = record { TMap = λ a h →  solv→ record {sb = equalizer-c (Ker t h) ; sm = equalizer (Ker t h) ; smono =
         {!!} } ; isNTrans = {!!} }  -- FObj (Sub S) a
      ; reprId→  = {!!}
      ; reprId←  = {!!}
     }
 
 




