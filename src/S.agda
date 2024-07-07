
--I'd like to write the Limit in Sets Category using Agda. Assuming local smallness, a functor is a pair of map on Set OC and I, like this.
--
--     sobj :  OC →  Set  c₂
--     smap : { i j :  OC  }  → (f : I ) →  sobj i → sobj j
--
--A cone for the functor is a record with two fields. Using the record, commutativity of the cone and the propertiesy of the Limit
--are easity shown, except uniquness. The uniquness of the Limit turned out that congruence of the record with two fields.
--
--In the following agda code, I'd like to prove snat-cong lemma.

    -- {-# OPTIONS --cubical-compatible --safe #-}
    open import Level
    module S where

    open import Relation.Binary.Core
    open import Function
    open import Relation.Binary.PropositionalEquality
    open import Relation.Binary.HeterogeneousEquality using (_≅_;refl)

    record snat   { c₂ }  { I OC :  Set  c₂ } ( sobj :  OC →  Set  c₂ )
         ( smap : { i j :  OC  }  → (f : I ) →  sobj i → sobj j ) : Set  c₂ where
       field
           snmap : ( i : OC ) → sobj i
           sncommute : ( i j : OC ) → ( f :  I ) →  smap f ( snmap i )  ≡ snmap j
       smap0 :  { i j :  OC  }  → (f : I ) →  sobj i → sobj j
       smap0 {i} {j} f x =  smap f x

    open snat

    -- snat-cong' :  { c : Level }  { I OC :  Set  c }  { SObj :  OC →  Set  c  } { SMap : { i j :  OC  }  → (f : I )→  SObj i → SObj j }
    --          ( s t :  snat SObj SMap   )
    --      → ( ( λ i  → snmap s i )  ≡  ( λ i →  snmap t i ) )
    --      → ( ( λ i j f →  smap0 s f ( snmap s i )  ≡ snmap s j   ) ≡ (  ( λ  i j f → smap0 t f ( snmap t i )  ≡ snmap t j ) ) )
    --      → s ≡ t
    -- snat-cong' s t refl refl = {!!}

    snat-cong : {c : Level}
                {I OC : Set c}
                {sobj : OC → Set c}
                {smap : {i j : OC}  → (f : I) → sobj i → sobj j}
              → (s t : snat sobj smap)
              → (snmap-≡ : snmap s ≡ snmap t)
              → (sncommute-≅ : sncommute s ≅ sncommute t)
              → s ≡ t
    snat-cong _ _ refl refl = refl

--This is quite simlar to the answer of 
--
--    Equality on dependent record types
--    https://stackoverflow.com/questions/37488098/equality-on-dependent-record-types
--
--So it should work something like
--
--    snat-cong s t refl refl = refl
--
--but it gives an error like this.
--
--    .sncommute i j f != sncommute t i j f of type
--    .SMap f (snmap t i) ≡ snmap t j
--
--Is there any help?
