open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level

module maybeCat where

open import cat-utility
open import HomReasoning
open import Relation.Binary 
open import Relation.Binary.Core
open import Data.Maybe

open Functor


record MaybeHom { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  (a : Obj A ) (b : Obj A ) : Set  (ℓ ⊔ c₂)   where
   field
      hom : Maybe ( Hom A a b )

open MaybeHom

_+_ :  { c₁ c₂ ℓ : Level} → { A : Category c₁ c₂ ℓ } →  {a b c : Obj A } → MaybeHom A b c  →  MaybeHom A a b  →  MaybeHom A  a c 
_+_  {x} {y} {z} {A} {a} {b} {c} f g with hom f | hom g
_+_  {_} {_} {_} {A} {a} {b} {c} f g | nothing  | _  = record { hom =  nothing }
_+_  {_} {_} {_} {A} {a} {b} {c} f g | _ | nothing   = record { hom =  nothing }
_+_  {_} {_} {_} {A} {a} {b} {c} _ _ | (just f) |  (just g)  = record { hom =  just ( A [ f o  g ]  ) }

MaybeHomId  : { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } (a  : Obj A ) → MaybeHom A a a
MaybeHomId   {_} {_} {_} {A} a  = record { hom = just ( id1 A a)  }

_[_≡≡_] : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {a b : Obj A } →  Rel (Maybe (Hom A a b)) (c₂ ⊔ ℓ) 
_[_≡≡_]  A =  Eq ( Category._≈_ A ) 


module ≡≡-Reasoning { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  where

        infixr  2 _∎
        infixr 2 _≡≡⟨_⟩_ _≡≡⟨⟩_
        infix  1 begin_

        ≡≡-refl :   {a b : Obj A } → {x : Maybe ( Hom A a b ) } → A [ x ≡≡ x ]
        ≡≡-refl  {_} {_} {just x}  = just refl-hom where  open ≈-Reasoning (A)
        ≡≡-refl  {_} {_} {nothing} = nothing

        ≡≡-sym :  {a b : Obj A } → {x y : Maybe ( Hom A a b ) }  → A [ x ≡≡ y ] → A [ y ≡≡ x ]
        ≡≡-sym (just x≈y) = just (sym x≈y)  where  open ≈-Reasoning (A)
        ≡≡-sym nothing    = nothing

        ≡≡-trans :  {a b : Obj A } → {x y z : Maybe ( Hom A a b ) }  → A [ x ≡≡ y ] → A [ y ≡≡ z ] → A [ x ≡≡ z ]
        ≡≡-trans (just x≈y) (just y≈z) = just (trans-hom x≈y y≈z)  where  open ≈-Reasoning (A)
        ≡≡-trans nothing    nothing    = nothing

        ≡≡-cong :  ∀{ a b c d }   → ∀ {x y :  Maybe (Hom A a b )} →
                (f : Maybe (Hom A a b ) → Maybe (Hom A c d ) )  →  x  ≡  y  →  A [ f x ≡≡ f y ]
        ≡≡-cong  {a} {b } {c} {d} {nothing} {nothing} f refl  = ≡≡-refl
        ≡≡-cong  {a} {b } {c} {d} {just x} {just .x} f refl  = ≡≡-refl

        data _IsRelatedTo_  {a b : Obj A}  (x y : (Maybe (Hom A a b ))) :
                             Set  (ℓ ⊔ c₂)  where
            relTo : (x≈y : A [ x  ≡≡ y  ] ) → x IsRelatedTo y

        begin_ :  {a b : Obj A}  {x : Maybe (Hom A a b ) } {y : Maybe (Hom A a b )} →
                   x IsRelatedTo y →  A [ x ≡≡  y ]
        begin relTo x≈y = x≈y

        _≡≡⟨_⟩_ :  {a b : Obj A}  (x :  Maybe  (Hom A a b )) {y z :  Maybe (Hom A a b ) } →
                    A [ x ≡≡ y ]  → y IsRelatedTo z → x IsRelatedTo z
        _ ≡≡⟨ x≈y ⟩ relTo y≈z = relTo (≡≡-trans x≈y y≈z)

        _≡≡⟨⟩_ :  {a b : Obj A}  (x : Maybe  (Hom A a b )) {y : Maybe (Hom A a b )}
                    → x IsRelatedTo y → x IsRelatedTo y
        _ ≡≡⟨⟩ x≈y = x≈y

        _∎ :   {a b : Obj A}  (x :  Maybe (Hom A a b )) → x IsRelatedTo x
        _∎ _ = relTo ≡≡-refl




MaybeCat : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Category   c₁ (ℓ ⊔ c₂)  (ℓ ⊔ c₂)
MaybeCat { c₁} {c₂} {ℓ} ( A ) =   record {
    Obj  = Obj A  ;
    Hom = λ a b →   MaybeHom A  a b   ; 
    _o_ =  _+_   ;
    _≈_ = λ a b →    _[_≡≡_] { c₁} {c₂} {ℓ} A  (hom a) (hom b)  ;
    Id  =  λ {a} → MaybeHomId a ;
    isCategory  = record {
            isEquivalence = let open ≡≡-Reasoning (A) in record {refl = ≡≡-refl ; trans = ≡≡-trans ; sym = ≡≡-sym  } ;
            identityL  = λ {a b f} → identityL {a} {b} {f} ;
            identityR  = λ {a b f} → identityR {a} {b} {f};
            o-resp-≈  = λ {a b c f g h i} →  o-resp-≈ {a} {b} {c} {f} {g} {h} {i} ;
            associative  = λ {a b c d f g h } → associative {a } { b } { c } { d } { f } { g } { h }
       } 
   } where
        identityL : { a b : Obj A } { f : MaybeHom A a b } →  A [ hom (MaybeHomId b + f) ≡≡ hom f ]
        identityL {a} {b} {f}  with hom f
        identityL {a} {b} {_} | nothing  = nothing
        identityL {a} {b} {_} | just f = just ( IsCategory.identityL ( Category.isCategory A )  {a} {b} {f}  )

        identityR : { a b : Obj A } { f : MaybeHom A a b } →  A [ hom (f + MaybeHomId a  ) ≡≡ hom f ]
        identityR {a} {b} {f}  with hom f
        identityR {a} {b} {_} | nothing  = nothing
        identityR {a} {b} {_} | just f = just ( IsCategory.identityR ( Category.isCategory A )  {a} {b} {f}  )

        o-resp-≈  :  {a b c : Obj A} → {f g : MaybeHom A a b } → {h i : MaybeHom A  b c } → 
                A [ hom f ≡≡ hom g ] → A [ hom h ≡≡ hom i ] → A [ hom (h + f) ≡≡ hom (i + g) ]
        o-resp-≈  {a} {b} {c} {f} {g} {h} {i} eq-fg eq-hi with hom f | hom g  | hom h | hom i
        o-resp-≈  {a} {b} {c} {_} {_} {_} {_}  (just eq-fg)  (just eq-hi) | just f | just g | just h | just i =  
             just ( IsCategory.o-resp-≈ ( Category.isCategory A )  {a} {b} {c} {f} {g} {h} {i} eq-fg eq-hi )
        o-resp-≈  {a} {b} {c} {f} {g} {h} {i} (just _)  nothing | just _ | just _ | nothing | nothing = nothing
        o-resp-≈  {a} {b} {c} {f} {g} {h} {i} nothing  (just _) | nothing | nothing | just _ | just _ = nothing
        o-resp-≈  {a} {b} {c} {f} {g} {h} {i} nothing nothing | nothing | nothing | nothing | nothing = nothing


        associative  :  {a b c d : Obj A} → {f : MaybeHom A c d } → {g : MaybeHom A b c } → {h : MaybeHom A a b } → 
           A [ hom (f + (g + h)) ≡≡ hom ((f + g) + h) ]
        associative  {_} {_} {_} {_} {f} {g} {h}  with hom f | hom g | hom h 
        associative  {_} {_} {_} {_} {f} {g} {h}  | nothing | _ | _ = nothing
        associative  {_} {_} {_} {_} {f} {g} {h}  | just _ | nothing | _ = nothing
        associative  {_} {_} {_} {_} {f} {g} {h}  | just _ | just _ | nothing = nothing
        associative  {a} {b} {c} {d} {_} {_} {_}  | just f | just g | just h = 
             just ( IsCategory.associative ( Category.isCategory A )  {a} {b} {c} {d} {f} {g} {h}  )

≈-to-== : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) →  { a b :  Obj A }
    { f g : Hom A a b } →
    A [ f ≈ g ] → (MaybeCat A) [  record { hom = just f } ≈  record { hom = just g } ]
≈-to-==  A {a} {b} {f} {g} f≈g =  just f≈g
