open import Category
open import CCC
open import Level
open import HomReasoning
open import cat-utility

module Polynominal { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) ( C : CCC A )   where

  module coKleisli { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } { S : Functor A A } (SM : coMonad A S) where

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

  open CCC.CCC C
  open coMonad 
  open Functor
  open NTrans
  open import Category.Cat
  
  SA : (a : Obj A) → Functor A A
  SA a = record {
       FObj = λ x → a ∧ x
     ; FMap = λ f →  < π ,  A [ f o π' ]   >
     ; isFunctor = record {
          identity = sa-id
        ; ≈-cong = λ eq → IsCCC.π-cong isCCC refl-hom (resp refl-hom eq )
        ; distr = sa-distr
       }
    } where
        open ≈-Reasoning A
        sa-id :  {b : Obj A} →  < π , ( id1 A b o π'  ) > ≈ id1 A (a ∧ b ) 
        sa-id {b} = begin
           < π , ( id1 A b o π'  ) > ≈⟨ IsCCC.π-cong isCCC (sym idR) (trans-hom idL (sym idR) ) ⟩
           < ( π o id1 A _ ) , ( π' o id1 A _ )  > ≈⟨ IsCCC.e3c isCCC  ⟩
          id1 A (a ∧ b ) ∎
        sa-distr :  {x b c : Obj A} {f : Hom A x b} {g : Hom A b c} →
            < π , (( g o f ) o π') > ≈ < π , ( g o π' ) > o < π , (f o π') > 
        sa-distr {x} {b} {c} {f} {g} = begin
            < π , (( g o f ) o π') > ≈↑⟨ IsCCC.π-cong isCCC (IsCCC.e3a isCCC) ( begin 
               ( g o π' ) o < π , (f o π') >  ≈↑⟨ assoc ⟩ 
                g o ( π'  o < π , (f o π') > )  ≈⟨ cdr (IsCCC.e3b isCCC)  ⟩ 
                g o ( f o π')   ≈⟨ assoc  ⟩ 
               ( g o f ) o π'  ∎ ) ⟩
            < (π o < π , (f o π') >) ,  ( ( g o π' ) o < π , (f o π') >) > ≈↑⟨ IsCCC.distr-π isCCC  ⟩
            < π , ( g o π' ) > o < π , (f o π') > ∎

  SM : (a : Obj A) → coMonad A (SA a)
  SM a = record {
        δ = record { TMap = λ x → < π , id1 A _ > ;  isNTrans = record { commute = δ-comm} }
      ; ε = record { TMap = λ x → π' ; isNTrans =  record { commute = ε-comm } }
      ; isCoMonad = record {
           unity1 = IsCCC.e3b isCCC
         ; unity2 = unity2
         ; assoc = assoc2
        }
     } where
        open ≈-Reasoning A
        δ-comm :  {a₁ : Obj A} {b : Obj A} {f : Hom A a₁ b} →
             FMap (_○_ (SA a)  (SA a)) f o < π , id1 A _ > ≈ < π , id1 A _ > o FMap (SA a) f 
        δ-comm {x} {b} {f} = begin
           FMap (_○_ (SA a)  (SA a)) f o < π , id1 A _ > ≈⟨  IsCCC.distr-π isCCC ⟩
           < π o < π , id1 A _ > ,  (FMap (SA a) f o π' ) o < π , id1 A _ > >  ≈⟨ IsCCC.π-cong isCCC (IsCCC.e3a isCCC) (sym assoc) ⟩
           < π ,  FMap (SA a) f o ( π'  o < π , id1 A _ >) >  ≈⟨ IsCCC.π-cong isCCC refl-hom (cdr (IsCCC.e3b isCCC)) ⟩
           < π ,  FMap (SA a) f o id1 A _  >                  ≈⟨  IsCCC.π-cong isCCC refl-hom idR ⟩
           < π ,  FMap (SA a) f  >                            ≈↑⟨   IsCCC.π-cong isCCC  (IsCCC.e3a isCCC) idL ⟩
           < π o  FMap (SA a) f ,  id1 A _ o FMap (SA a) f >  ≈↑⟨  IsCCC.distr-π isCCC   ⟩
           < π , id1 A _ > o FMap (SA a) f  ∎
        ε-comm :  {a₁ : Obj A} {b : Obj A} {f : Hom A a₁ b} → 
             FMap (identityFunctor {_} {_} {_} {A}) f o π'  ≈  π' o FMap (SA a) f 
        ε-comm {_} {_} {f} = sym  (IsCCC.e3b isCCC)
        unity2 :  {a₁ : Obj A} →  FMap (SA a) π' o < π , id1 A _ >  ≈ id1 A (a ∧ a₁)
        unity2 {x} = begin
           FMap (SA a) π' o < π , id1 A _ >                         ≈⟨  IsCCC.distr-π isCCC   ⟩
            < π o < π , id1 A _ > , ( π' o π' ) o < π , id1 A _ > > ≈⟨  IsCCC.π-cong isCCC (IsCCC.e3a isCCC) (sym assoc) ⟩
            < π  ,  π' o ( π'  o < π , id1 A _ > ) >                ≈⟨  IsCCC.π-cong isCCC  refl-hom (cdr (IsCCC.e3b isCCC)) ⟩
            < π  ,  π' o  id1 A _ >                                 ≈⟨  IsCCC.π-cong isCCC  refl-hom  idR ⟩
            < π  ,  π' >                                            ≈⟨  IsCCC.π-id isCCC ⟩
           id1 A (a ∧ x)  ∎
        assoc2 :   {a₁ : Obj A} →  < π , id1 A _ > o < π , id1  A _ > ≈  FMap (SA a) < π , id1 A (a ∧ a₁) > o < π , id1 A _ > 
        assoc2 {x} = begin
            < π , id1 A _ > o < π , id1  A _ >                      ≈⟨  IsCCC.distr-π isCCC ⟩
            < π o < π , id1  A _ > , id1 A _ o < π , id1  A _ > >   ≈⟨  IsCCC.π-cong isCCC  (IsCCC.e3a isCCC) idL  ⟩
            < π  , < π , id1 A _ > >                                ≈↑⟨ IsCCC.π-cong isCCC refl-hom idR ⟩
            < π  , < π , id1 A _ > o  id1 A _ >                     ≈↑⟨ IsCCC.π-cong isCCC refl-hom  (cdr (IsCCC.e3b isCCC)) ⟩
            < π  , < π , id1 A _ > o  ( π'  o < π , id1 A _ > ) >   ≈↑⟨ IsCCC.π-cong isCCC  (IsCCC.e3a isCCC) (sym assoc) ⟩
            < π o < π , id1 A _ > , (< π , id1 A _ > o  π' ) o < π , id1 A _ > > ≈↑⟨  IsCCC.distr-π isCCC  ⟩
           FMap (SA a) < π , id1 A (a ∧ x) > o < π , id1 A _ > ∎



  -- functional-completeness : (C : CCC A ) → {a : Obj A} → ( x : Hom A (CCC.１ C) a ) → {!!}
  -- functional-completeness = {!!}

-- end
