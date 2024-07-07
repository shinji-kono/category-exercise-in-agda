{-# OPTIONS --cubical-compatible --safe #-}

module Category.Sets where
open import Category
open import Relation.Binary.Core
open import Relation.Binary
open import Level
open import Function
open import Relation.Binary.PropositionalEquality

_==_  : ∀{ℓ} {a b : Set ℓ} → (f g : a → b)  → Set ℓ
_==_ {_} {a} {b} f g = (x : a) →  f x ≡ g x

Sets : ∀{ℓ} → Category _ _ ℓ
Sets {ℓ} = record { Obj = Set ℓ
                  ; Hom = λ a b → a → b
                  ; _o_ = λ f g → f ∘ g
                  ; _≈_ = _==_ 
                  ; isCategory = isCategory
                  }
  where
    isCategory : IsCategory (Set ℓ) (λ a b → a → b)  _==_ (λ f g → f ∘ g) (λ x → x)
    isCategory = record { isEquivalence = record {refl = λ x → refl 
       ; trans = λ i=j j=k x → trans (i=j x) (j=k x) ; sym = λ eq x → sym (eq x)}
                        ; identityL     = λ x → refl
                        ; identityR     = λ x → refl
                        ; o-resp-≈      = λ {c} {b} {a} {f} {g} {h} {i} f=g h=i x → trans (h=i (f x)) (cong i (f=g x))
                        ; associative   = λ x → refl
                        }
