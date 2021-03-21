open import Category
open import Level
open import HomReasoning 
open import cat-utility


module coKleisli { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } { S : Functor A A } (SM : coMonad A S)  where

    open coMonad 

    open Functor
    open NTrans

--
--  Hom in Kleisli Category
--

    record SHom (a : Obj A)  (b : Obj A)
      : Set c₂ where
      field
        SMap :  Hom A ( FObj S a ) b

    open SHom 

    S-id :  (a : Obj A) → SHom a a
    S-id a = record { SMap =  TMap (ε SM) a }

    open import Relation.Binary

    _⋍_ : { a : Obj A } { b : Obj A } (f g  : SHom a b ) → Set ℓ 
    _⋍_ {a} {b} f g = A [ SMap f ≈ SMap g ]

    _*_ : { a b c : Obj A } → ( SHom b c) → (  SHom a b) → SHom a c 
    _*_ {a} {b} {c} g f = record { SMap = coJoin SM {a} {b} {c} (SMap g) (SMap f) }

    isSCat : IsCategory ( Obj A ) SHom _⋍_ _*_ (λ {a} → S-id a)
    isSCat  = record  { isEquivalence =  isEquivalence 
                    ; identityL =   SidL
                    ; identityR =   SidR
                    ; o-resp-≈ =    So-resp
                    ; associative = Sassoc
                    }
     where
         open ≈-Reasoning A 
         isEquivalence :  { a b : Obj A } → IsEquivalence {_} {_} {SHom a b} _⋍_
         isEquivalence {C} {D} = record { refl  = refl-hom ; sym   = sym ; trans = trans-hom } 
         SidL : {a b : Obj A} → {f : SHom a b} → (S-id _ * f) ⋍ f
         SidL {a} {b} {f} =  begin
             SMap (S-id _ * f)  ≈⟨⟩
             (TMap (ε SM) b o (FMap S (SMap f))) o TMap (δ SM) a ≈↑⟨ car (nat (ε SM)) ⟩
             (SMap f o TMap (ε SM) (FObj S a)) o TMap (δ SM) a ≈↑⟨ assoc ⟩
              SMap f o TMap (ε SM) (FObj S a) o TMap (δ SM) a  ≈⟨ cdr (IsCoMonad.unity1 (isCoMonad SM)) ⟩
              SMap f o id1 A _  ≈⟨ idR ⟩
              SMap f ∎ 
         SidR : {C D : Obj A} → {f : SHom C D} → (f * S-id _ ) ⋍ f
         SidR {a} {b} {f} =  begin
               SMap (f * S-id a) ≈⟨⟩
               (SMap f o FMap S (TMap (ε SM) a)) o TMap (δ SM) a ≈↑⟨ assoc ⟩
               SMap f o (FMap S (TMap (ε SM) a) o TMap (δ SM) a) ≈⟨ cdr (IsCoMonad.unity2 (isCoMonad SM)) ⟩
               SMap f o id1 A _ ≈⟨ idR ⟩
              SMap f ∎ 
         So-resp :  {a b c : Obj A} → {f g : SHom a b } → {h i : SHom  b c } → 
                          f ⋍ g → h ⋍ i → (h * f) ⋍ (i * g)
         So-resp {a} {b} {c} {f} {g} {h} {i} eq-fg eq-hi = resp refl-hom (resp (fcong S eq-fg ) eq-hi )
         Sassoc :   {a b c d : Obj A} → {f : SHom c d } → {g : SHom b c } → {h : SHom a b } →
                          (f * (g * h)) ⋍ ((f * g) * h)
         Sassoc {a} {b} {c} {d} {f} {g} {h} =  begin
               SMap  (f * (g * h)) ≈⟨ car (cdr (distr S))  ⟩
                (SMap f o ( FMap S (SMap g o FMap S (SMap h)) o FMap S (TMap (δ SM) a) )) o TMap (δ SM) a ≈⟨ car assoc ⟩
                ((SMap f o  FMap S (SMap g o FMap S (SMap h))) o FMap S (TMap (δ SM) a) ) o TMap (δ SM) a ≈↑⟨ assoc ⟩
                (SMap f o  FMap S (SMap g o FMap S (SMap h))) o (FMap S (TMap (δ SM) a)  o TMap (δ SM) a ) ≈↑⟨ cdr (IsCoMonad.assoc (isCoMonad SM)) ⟩
                  (SMap f o (FMap S (SMap g o FMap S (SMap h)))) o ( TMap (δ SM) (FObj S a) o TMap (δ SM) a ) ≈⟨ assoc ⟩
                  ((SMap f o (FMap S (SMap g o FMap S (SMap h)))) o  TMap (δ SM) (FObj S a) ) o TMap (δ SM) a  ≈⟨ car (car (cdr (distr S))) ⟩
                  ((SMap f o (FMap S (SMap g) o FMap S (FMap S (SMap h)))) o  TMap (δ SM) (FObj S a) ) o TMap (δ SM) a  ≈↑⟨ car assoc ⟩
                  (SMap f o ((FMap S (SMap g) o FMap S (FMap S (SMap h))) o  TMap (δ SM) (FObj S a) )) o TMap (δ SM) a  ≈↑⟨ assoc ⟩
                  SMap f o (((FMap S (SMap g) o FMap S (FMap S (SMap h))) o  TMap (δ SM) (FObj S a) ) o TMap (δ SM) a)  ≈↑⟨ cdr (car assoc ) ⟩
                  SMap f o ((FMap S (SMap g) o (FMap S (FMap S (SMap h)) o  TMap (δ SM) (FObj S a) )) o TMap (δ SM) a)  ≈⟨ cdr (car (cdr (nat (δ SM)))) ⟩
                  SMap f o ((FMap S (SMap g) o ( TMap (δ SM) b o FMap S (SMap h))) o TMap (δ SM) a)  ≈⟨ assoc ⟩
                  (SMap f o (FMap S (SMap g) o ( TMap (δ SM) b o FMap S (SMap h)))) o TMap (δ SM) a  ≈⟨ car (cdr assoc) ⟩
                  (SMap f o ((FMap S (SMap g) o  TMap (δ SM) b ) o FMap S (SMap h))) o TMap (δ SM) a  ≈⟨ car assoc ⟩
                  ((SMap f o (FMap S (SMap g) o  TMap (δ SM) b )) o FMap S (SMap h)) o TMap (δ SM) a  ≈⟨ car (car assoc) ⟩
                  (((SMap f o FMap S (SMap g)) o  TMap (δ SM) b ) o FMap S (SMap h)) o TMap (δ SM) a  ≈⟨⟩
               SMap  ((f * g) * h) ∎ 

    SCat : Category c₁ c₂ ℓ
    SCat = record { Obj = Obj A ; Hom = SHom ; _o_ = _*_ ; _≈_ = _⋍_ ; Id  = λ {a} → S-id a ; isCategory = isSCat }

