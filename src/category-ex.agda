{-# OPTIONS --cubical-compatible --safe #-}

module category-ex where

open import Level
open import Category

module _ {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (a b c : Obj A) (g : Hom A a b) (f : Hom A b c) where

    open Category.Category

    h = _o_  A f g

    i = A [ f o g ]


