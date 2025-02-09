-- {-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --cubical-compatible --safe #-}

open import Category
open import CCC
open import Level
open import HomReasoning
open import Definitions
open import Relation.Nullary
open import Data.Empty
open import Data.Product renaming ( <_,_> to ⟪_,_⟫ )

module Polynominal { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) ( C : CCC-* A )   where

  open import Category.Cat
  open CCC.CCC-* C
  -- open ≈-Reasoning A -- hiding (_∙_)

  _∙_ = _[_o_] A

  --
  --   Polynominal (p.57) in Introduction to Higher order categorical logic
  --
  --   Given object a₀ and a of a caterisian closed category A, how does one adjoin an interminate arraow x : a₀ → a to A?
  --   A[x] based on the `assumption' x, as was done in Section 2 (data φ). The formulas of A[x] are the objects of A and the
  --   proofs of A[x] are formed from the arrows of A and the new arrow x :  a₀ → a by the appropriate ules of inference.
  --
  -- Here, A is actualy A[x]. It contains x and all the arrow generated from x.
  -- If we can put constraints on rule i (sub : Hom A b c → Set), then A is strictly smaller than A[x],
  -- that is, a subscategory of A[x].
  --
  --   i   : {b c : Obj A} {k : Hom A b c } → sub k  → φ x k
  --         sub k is ¬ ( k ≈ x ), we cannot write this because b≡⊤ c≡a is forced
  --
  -- this makes a few changes, but we don't care.
  -- from page. 51
  --

  open Functor
  -- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )
  open import Relation.Binary.PropositionalEquality hiding ( [_] ; resp ) renaming ( sym to ≡sym )

  -- data _H≈_ {a b c d : Obj A } ( x : Hom A a b ) (y : Hom A c d ) : Set ( c₁  ⊔  c₂ ⊔ ℓ) where
  --   feq : a ≡ c → b ≡ d → (z : Hom A a b) → z ≅ y → A [ x ≈ z ] → x H≈ y

  data  φ  {a ⊤ : Obj A } ( x : Hom A ⊤ a ) : {b c : Obj A } → Hom A b c → Set ( c₁  ⊔  c₂ ⊔ ℓ) where
     i   : {b c : Obj A} (k : Hom A b c ) →  φ x k
     ii  : φ x {⊤} {a} x
     iii : {b c' c'' : Obj A } { f : Hom A b c' } { g : Hom A b c'' } (ψ : φ x f ) (χ : φ x g ) → φ x {b} {c'  ∧ c''} < f , g >
     iv  : {b c d : Obj A } { f : Hom A d c } { g : Hom A b d } (ψ : φ x f ) (χ : φ x g ) → φ x ( f ∙ g )
     v   : {b c' c'' : Obj A } { f : Hom A (b ∧ c') c'' }  (ψ : φ x f )  → φ x {b} {c'' <= c'} ( f * )

  α : {a b c : Obj A } → Hom A (( a ∧ b ) ∧ c ) ( a ∧ ( b ∧ c ) )
  α = < π  ∙ π   , < π'  ∙ π  , π'  > >

  -- genetate (a ∧ b) → c proof from  proof b →  c with assumption a
  -- from page. 51

  k : {a ⊤ b c : Obj A } → ( x∈a : Hom A ⊤ a ) → {z : Hom A b c } → ( y  : φ {a} x∈a z ) → Hom A (a ∧ b) c
  k x∈a {k} (i _) = k ∙ π'
  k x∈a ii = π
  k x∈a (iii ψ χ ) = < k x∈a ψ  , k x∈a χ  >
  k x∈a (iv ψ χ ) = k x∈a ψ  ∙ < π , k x∈a χ  >
  k x∈a (v ψ ) = ( k x∈a ψ  ∙ α ) *

  α' : {a b c : Obj A } → Hom A ( a ∧ ( b ∧ c ) ) (( a ∧ b ) ∧ c ) 
  α' = <  < π , π ∙ π' >  , π' ∙ π' >

  -- we should open IsCCC isCCC
  π-cong = IsCCC.π-cong isCCC
  *-cong = IsCCC-*-cong.*-cong is*-CCC
  distr-* = IsCCC-*-cong.distr-* is*-CCC
  e2 = IsCCC.e2 isCCC

  α-iso : {a b c : Obj A} → A [ α ∙ α' ≈ id1 A (a ∧ (b ∧ c))]
  α-iso = begin
     < π  ∙ π   , < π'  ∙ π  , π'  > > ∙  <  < π , π ∙ π' >  , π' ∙ π' >  ≈⟨ IsCCC.distr-π isCCC ⟩
     < (π  ∙ π)  ∙  <  < π , π ∙ π' >  , π' ∙ π' > , < π'  ∙ π  , π'  >  ∙  <  < π , π ∙ π' >  , π' ∙ π' > >  ≈⟨ π-cong (sym assoc) (IsCCC.distr-π isCCC) ⟩
     < π  ∙ (π  ∙  <  < π , π ∙ π' >  , π' ∙ π' >) , < (π'  ∙ π) ∙   <  < π , π ∙ π' >  , π' ∙ π' >  , π'   ∙  <  < π , π ∙ π' >  , π' ∙ π' > > >  
        ≈⟨ π-cong (cdr (IsCCC.e3a isCCC)) (π-cong (sym assoc) (IsCCC.e3b isCCC) )  ⟩
     < π  ∙ < π , π ∙ π' >  , < π'  ∙ ( π ∙   <  < π , π ∙ π' >  , π' ∙ π' > ) ,  π' ∙ π' > >  
         ≈⟨ π-cong (IsCCC.e3a isCCC) (π-cong (cdr (IsCCC.e3a isCCC)) refl-hom ) ⟩
     <  π   , < π'  ∙ < π , π ∙ π' > ,  π' ∙ π' > >  ≈⟨ π-cong refl-hom (π-cong (IsCCC.e3b isCCC) refl-hom ) ⟩
     <  π   , < π ∙ π'  ,  π' ∙ π' > >  ≈⟨ π-cong refl-hom (sym (IsCCC.distr-π isCCC)) ⟩
     <  π   , < π ,  π' > ∙ π' >  ≈⟨ π-cong refl-hom (car (IsCCC.π-id isCCC)) ⟩
     <  π   , id1 A _  ∙ π' >  ≈⟨ π-cong refl-hom idL ⟩
     <  π   ,  π' >  ≈⟨ IsCCC.π-id isCCC ⟩
     id1 A _  ∎ where open  ≈-Reasoning A

  α'-iso : {a b c : Obj A} → A [ α' ∙ α ≈ id1 A ((a ∧ b) ∧ c)]
  α'-iso = begin
      < < π , π ∙ π' >  , π' ∙ π' > ∙  < π  ∙ π   , < π'  ∙ π  , π'  > > ≈⟨ IsCCC.distr-π isCCC ⟩ 
      < < π , π ∙ π' > ∙ < π  ∙ π   , < π'  ∙ π  , π'  > > ,  ( π' ∙ π') ∙ < π  ∙ π   , < π'  ∙ π  , π'  > > > ≈⟨ π-cong (IsCCC.distr-π isCCC) (sym assoc)  ⟩
      < < π ∙ < π  ∙ π   , < π'  ∙ π  , π'  > > , ( π ∙ π') ∙ < π  ∙ π   , < π'  ∙ π  , π'  > > > ,   π' ∙ (π' ∙ < π  ∙ π   , < π'  ∙ π  , π'  > >) > 
          ≈⟨ π-cong (π-cong (IsCCC.e3a isCCC) (sym assoc) ) (cdr (IsCCC.e3b isCCC) )  ⟩
      < <  π  ∙ π   , π ∙ (π' ∙ < π  ∙ π   , < π'  ∙ π  , π'  > >) > ,   π' ∙ < π'  ∙ π  , π'  > > 
         ≈⟨ π-cong (π-cong refl-hom (cdr (IsCCC.e3b isCCC) )) (IsCCC.e3b isCCC) ⟩
      < <  π  ∙ π   , π ∙ < π'  ∙ π  , π'  > > ,   π'  > ≈⟨ π-cong (π-cong refl-hom (IsCCC.e3a isCCC) ) refl-hom ⟩
      < <  π  ∙ π   ,  π' ∙ π  > ,   π'  > ≈⟨ π-cong (sym (IsCCC.distr-π isCCC)) refl-hom  ⟩
      < <  π  ,  π'  >  ∙ π ,   π'  > ≈⟨ π-cong (car (IsCCC.π-id isCCC)) refl-hom ⟩
      < id1 A _  ∙ π ,   π'  > ≈⟨ π-cong idL refl-hom ⟩
      < π ,   π'  > ≈⟨ IsCCC.π-id isCCC ⟩
     id1 A _ ∎ where open  ≈-Reasoning A

  -- toφ : {a ⊤ b c : Obj A } → ( x∈a : Hom A ⊤ a ) → (z : Hom A b c ) → φ {a} x∈a z
  -- toφ {a} {⊤} {b} {c} x∈a z = i z


  PolyS : (a : Obj A) → Functor A A
  PolyS a = record { FObj = λ x → a ∧ x ; FMap = λ {b c} f → < π , A [ f o π' ]  > ; isFunctor = record { 
          ≈-cong = λ {a} {b} {f} {g} f=g → begin
              < π , A [ f o π' ]  > ≈⟨ π-cong refl-hom (resp refl-hom f=g ) ⟩
              < π , A [ g o π' ]  > ∎
        ; identity = λ {a} → begin
              < π , id1 A _ o π' > ≈⟨ π-cong refl-hom idL  ⟩
              < π , π' > ≈⟨ IsCCC.π-id isCCC ⟩
              id1 A _  ∎
        ; distr = λ {a} {b} {c} {f} {g} → begin
              < π , (g o f) o π' >  ≈⟨ π-cong (sym (IsCCC.e3a isCCC)) ( begin
                 (g o f ) o π' ≈⟨ sym assoc ⟩
                 g o ( f o π') ≈⟨ cdr (sym (IsCCC.e3b isCCC)) ⟩
                 g o ( π' o < π , f o π' > ) ≈⟨ assoc ⟩
                 (g o π') o < π , f o π' > ∎ ) ⟩
              < π o < π , f o π' > , (g o π') o < π , f o π' >  >   ≈↑⟨ IsCCC.distr-π isCCC ⟩
              < π , g o π' > o < π , f  o π' > ∎
       }
     } where open ≈-Reasoning A

  eta : {a : Obj A} (x : Hom A １ a) → NTrans A A (PolyS a) identityFunctor
  eta {a} x = record { TMap = λ b → π' ; isNTrans = record  {
          commute = λ {b} {b} {f} → begin
              f o π'   ≈⟨ sym ( IsCCC.e3b isCCC) ⟩
              π' ∙ < π , f ∙  π' > ∎
       }
    }
      where open ≈-Reasoning A

  mu : {a : Obj A} (x : Hom A １ a) → NTrans A A (PolyS a) (_○_ (PolyS a ) (PolyS a))
  mu {a} x = record { TMap = λ b → < π , id1 A _ > ; isNTrans = record  {
          commute = λ {b} {b} {f} → begin
            < π , < π , f o π' > o π' > o < π , id1 A _ >  ≈⟨ IsCCC.distr-π isCCC ⟩
            < π o < π , id1 A _ > , (< π , f o π' > o π') o < π , id1 A _ > >  ≈⟨ π-cong (IsCCC.e3a isCCC) ( begin
               (< π , f o π' > o π') o < π , id1 A _ > ≈⟨ sym assoc ⟩
               < π , f o π' > o ( π' o < π , id1 A _ >) ≈⟨ cdr ( IsCCC.e3b isCCC) ⟩
               < π , f o π' > o id1 A _ ≈⟨ idR ⟩
               < π , f o π' > ∎ ) ⟩
            < π  , < π , f o π' > >  ≈⟨ π-cong (sym (IsCCC.e3a isCCC)) (sym idL) ⟩
            < π o < π , ( f o π')> , id1 A _ o < π , (f o π' ) > > ≈⟨ sym ( IsCCC.distr-π isCCC)  ⟩
            < π , id1 A _ > o < π , ( f o π') > ∎
    } }
      where open ≈-Reasoning A

  poly-comonad : {a : Obj A} (x : Hom A １ a) → IsCoMonad A (PolyS a) (eta x) (mu x)
  poly-comonad {a} x = record {
        assoc = λ {b} → assocm b
      ; unity1 = unity1
      ; unity2 = unity2
    } where
        open ≈-Reasoning A
        assocm : (b : Obj A) →
            A [ A [ < π , id1 A (a ∧ (a ∧ b)) > o < π , id1 A (a ∧ b) > ] ≈ A [ < π , A [ < π , id1 A (a ∧ b) > o π' ] > o < π , id1 A (a ∧ b) > ] ]
        assocm b = begin
            < π , id1 A _ > o < π , id1 A _ > ≈⟨ IsCCC.distr-π isCCC ⟩
            < π  o < π , id1 A _ > , id1 A _ o < π , id1 A _ > >  ≈⟨ π-cong refl-hom ( begin
               id1 A _ o < π , id1 A _ > ≈⟨ idL  ⟩
               < π , id1 A (a ∧ b) >  ≈⟨ sym idR ⟩
               < π , id1 A (a ∧ b) > o id1 A (a ∧ b)  ≈⟨  cdr (sym (IsCCC.e3b isCCC))  ⟩
               < π , id1 A (a ∧ b) > o (π' o < π , id1 A (a ∧ b) >) ≈⟨ assoc ⟩
               ( < π , id1 A (a ∧ b) > o π') o < π , id1 A (a ∧ b) > ∎ ) ⟩
            < π o  < π , id1 A (a ∧ b) > , ( < π , id1 A (a ∧ b) > o π') o < π , id1 A (a ∧ b) > >  ≈⟨ sym ( IsCCC.distr-π isCCC) ⟩ 
            < π , < π , id1 A (a ∧ b) > o π' > o < π , id1 A (a ∧ b) >  ∎
        unity1 :  {b : Obj A} →
            A [ A [ π' o < π , id1 A (a ∧ b) > ] ≈ id1 A (a ∧ b) ]
        unity1 {b} = begin
            π' ∙ < π , id1 A _ > ≈⟨ IsCCC.e3b isCCC ⟩
            id1 A (a ∧ b) ∎
        unity2 :  {b : Obj A} →
            A [ A [ < π , A [ π' o π' ] > o < π , id1 A (a ∧ b) > ] ≈ id1 A (a ∧ b) ]
        unity2 {b} = begin
            < π ,  π' ∙ π' > ∙ < π , id1 A _ >  ≈⟨ IsCCC.distr-π isCCC ⟩
            <  π o < π , id1 A _ > ,  (π' o π')  o < π , id1 A (a ∧ b) > >  ≈⟨ π-cong (IsCCC.e3a isCCC) ( begin
                (π' o π')  o < π , id1 A (a ∧ b) > ≈⟨ sym assoc ⟩ 
                π' o ( π'  o < π , id1 A (a ∧ b) > ) ≈⟨ cdr ( IsCCC.e3b isCCC) ⟩ 
                π' o id1 A _ ≈⟨ idR ⟩ 
                π' ∎ ) ⟩
            <  π , π' >  ≈⟨  IsCCC.π-id isCCC ⟩
            id1 A (a ∧ b)  ∎ 

  PolyComonad : {a : Obj A} (x : Hom A １ a) → coMonad A (PolyS a) 
  PolyComonad x = record {
        ε = eta x
      ; δ = mu x
      ; isCoMonad = poly-comonad x
    }

  Poly : {a : Obj A} (x : Hom A １ a) → Category c₁ c₂ ℓ
  Poly x = SCat where
     open import coKleisli (PolyComonad x)

  -- we have to show CCC of Poly x and Universal property of Poly x

  PolyCCC : {a : Obj A} (x : Hom A １ a) → CCC-* (Poly x)
  PolyCCC {a} x = record {
        １ = １
      ; ○ = λ b →  ○ ( a ∧ b ) 
      ; _∧_ = λ f g → f ∧ g
      ; <_,_> = <_,_>
      ; π =  π   ∙ π' 
      ; π' = π'  ∙ π' 
      ; _<=_ = λ b c → b <= c
      ;  _* = λ f → ( f ∙ α ) *
      ; ε = ε ∙ π'
      ; isCCC = record {
               e2  = IsCCC.e2 isCCC
            ;  e3a = λ {_} {_} {_} {f} {g}  → begin
                ( (π ∙ π' ) ∙ < π , < f , g > ∙ π' >) ∙ < π , id1 A _ >  ≈↑⟨ car assoc ⟩
                ( π ∙ ( π'  ∙ < π , < f , g > ∙ π' >)) ∙ < π , id1 A _ >  ≈⟨ car (cdr (IsCCC.e3b isCCC)) ⟩
                ( π ∙ ( < f , g > ∙ π' )) ∙ < π , id1 A _ >  ≈⟨ car assoc ⟩
                ( (π ∙  < f , g >) ∙ π' ) ∙ < π , id1 A _ >  ≈⟨ car (car (IsCCC.e3a isCCC)) ⟩
                (f ∙ π') ∙ < π , id1 A _ >  ≈⟨ sym assoc ⟩
                f ∙ (π' ∙ < π , id1 A _ >)  ≈⟨ cdr (IsCCC.e3b isCCC) ⟩
                f ∙ id1 A _  ≈⟨ idR ⟩
                f ∎ 
            ;  e3b = λ {_} {_} {_} {f} {g}  → begin
                ( (π' ∙ π' ) ∙ < π , < f , g > ∙ π' >) ∙ < π , id1 A _ >  ≈↑⟨ car assoc ⟩
                ( π' ∙ ( π'  ∙ < π , < f , g > ∙ π' >)) ∙ < π , id1 A _ >  ≈⟨ car (cdr (IsCCC.e3b isCCC)) ⟩
                ( π' ∙ ( < f , g > ∙ π' )) ∙ < π , id1 A _ >  ≈⟨ car assoc ⟩
                ( (π' ∙  < f , g >) ∙ π' ) ∙ < π , id1 A _ >  ≈⟨ car (car (IsCCC.e3b isCCC)) ⟩
                (g ∙ π') ∙ < π , id1 A _ >  ≈⟨ sym assoc ⟩
                g ∙ (π' ∙ < π , id1 A _ >)  ≈⟨ cdr (IsCCC.e3b isCCC) ⟩
                g ∙ id1 A _  ≈⟨ idR ⟩
                g ∎ 
            ;  e3c = λ {_} {_} {_} {h}  → begin
                < ( (π ∙ π' ) ∙ < π , ( h ∙ π') >) ∙ < π , id1 A _ >   , ((π' ∙ π' ) ∙ < π , ( h ∙ π') > ) ∙ < π , id1 A _ > >  
                    ≈↑⟨ π-cong (car assoc) (car assoc)  ⟩
                <  (π ∙ (π'  ∙ < π , ( h ∙ π') > ))  ∙ < π , id1 A _ >   , (π' ∙ (π'  ∙ < π , ( h ∙ π') > )) ∙ < π , id1 A _ > >  
                    ≈⟨ π-cong (car (cdr (IsCCC.e3b isCCC)))  (car (cdr (IsCCC.e3b isCCC)))  ⟩
                <  (π ∙ (h ∙ π')) ∙ < π , id1 A _ >   , (π' ∙ (h ∙ π')) ∙ < π , id1 A _ > >  ≈⟨ π-cong (car assoc) (car assoc)  ⟩
                <  ((π ∙ h) ∙ π') ∙ < π , id1 A _ >   , ((π' ∙ h) ∙ π') ∙ < π , id1 A _ > >  ≈↑⟨ π-cong assoc assoc  ⟩
                <  (π ∙ h) ∙ (π' ∙ < π , id1 A _ > )  , (π' ∙ h) ∙ (π' ∙ < π , id1 A _ > )>  ≈⟨ π-cong (cdr (IsCCC.e3b isCCC)) (cdr (IsCCC.e3b isCCC))  ⟩
                <  (π ∙ h) ∙ id1 A _  , (π' ∙ h) ∙ id1 A _ >  ≈⟨ π-cong idR idR ⟩
                <  π ∙ h , π' ∙ h >  ≈⟨ IsCCC.e3c isCCC ⟩
                h ∎
            ;  π-cong = π-cong 
            ;  e4a = λ {a₁} {b} {c} {k} → begin 
                (( ε ∙ π' ) ∙ < π , < (((k ∙ α) *) ∙ < π , (π ∙ π') ∙ π'  > ) ∙ < π , id1 A _ > , π' ∙ π' > ∙ π'  > ) ∙ < π , id1 A _ > ≈⟨ car (sym assoc) ⟩ 
                ( ε ∙ (π'  ∙ < π , < (((k ∙ α) *) ∙ < π , (π ∙ π') ∙ π'  > ) ∙ < π , id1 A _ > , π' ∙ π' > ∙ π'  > )) ∙ < π , id1 A _ > ≈⟨ car (cdr (IsCCC.e3b isCCC)) ⟩ 
                ( ε ∙ (< (((k ∙ α) *) ∙ < π , (π ∙ π') ∙ π'  > ) ∙ < π , id1 A _ > , π' ∙ π' > ∙ π' )  ) ∙ < π , id1 A _ > ≈⟨ sym assoc ⟩ 
                 ε ∙ ((< (((k ∙ α) *) ∙ < π , (π ∙ π') ∙ π'  > ) ∙ < π , id1 A _ > , π' ∙ π' > ∙ π' ) ∙ < π , id1 A _ >) ≈⟨ cdr (sym assoc) ⟩ 
                 ε ∙ ((< (((k ∙ α) *) ∙ < π , (π ∙ π') ∙ π'  > ) ∙ < π , id1 A _ > , π' ∙ π' >) ∙ (π'  ∙ < π , id1 A _ >)) ≈⟨ cdr (cdr (IsCCC.e3b isCCC)) ⟩ 
                 ε ∙ ((< (((k ∙ α) *) ∙ < π , (π ∙ π') ∙ π'  > ) ∙ < π , id1 A _ > , π' ∙ π' >) ∙ id1 A _ ) ≈⟨ cdr idR ⟩ 
                 ε ∙  (< (((k ∙ α) *) ∙ < π , (π ∙ π') ∙ π'  > ) ∙ < π , id1 A _ > , π' ∙ π' >)  ≈⟨ cdr (π-cong (sym assoc) refl-hom ) ⟩ 
                 ε ∙  (< ((k ∙ α) *) ∙ (< π , (π ∙ π') ∙ π'  >  ∙ < π , id1 A _ >) , π' ∙ π' >)  ≈⟨ cdr (π-cong (cdr (IsCCC.distr-π isCCC)) refl-hom) ⟩ 
                 ε ∙  (< ((k ∙ α) *) ∙ (< π ∙ < π , id1 A _ > , ((π ∙ π') ∙ π') ∙ < π , id1 A _ > >)  , π' ∙ π' >)  
                    ≈⟨ cdr (π-cong (cdr (π-cong (IsCCC.e3a isCCC) (sym assoc)) ) refl-hom ) ⟩ 
                 ε ∙  (< ((k ∙ α) *) ∙ <  π  , (π ∙ π') ∙ (π' ∙ < π , id1 A _ >) >  , π' ∙ π' >)  ≈⟨ cdr (π-cong (cdr (π-cong refl-hom (cdr (IsCCC.e3b isCCC)))) refl-hom) ⟩ 
                 ε ∙  (< ((k ∙ α) *) ∙ <  π  , (π ∙ π') ∙ id1 A _ >  , π' ∙ π' >)  ≈⟨ cdr (π-cong (cdr (π-cong refl-hom idR )) refl-hom) ⟩ 
                 ε ∙  (< ((k ∙ α) *) ∙ <  π  , π ∙ π' >  , π' ∙ π' >)  ≈⟨ cdr (sym idR) ⟩ 
                 ε ∙  ((< ((k ∙ α) *) ∙ <  π  , π ∙ π' >  , π' ∙ π' >) ∙ id1 A _)  ≈⟨ cdr (cdr (sym α-iso)) ⟩ 
                 ε ∙  ((< ((k ∙ α) *) ∙ <  π  , π ∙ π' >  , π' ∙ π' >) ∙ (α ∙ α'))  ≈⟨ cdr assoc ⟩ 
                 ε ∙  ((< ((k ∙ α) *) ∙ <  π  , π ∙ π' >  , π' ∙ π' > ∙ α ) ∙ α')  ≈⟨ cdr (car (IsCCC.distr-π isCCC) ) ⟩ 
                 ε ∙  ((< (((k ∙ α) *) ∙ <  π  , π ∙ π' >) ∙ α   , (π' ∙ π') ∙ α >) ∙ α')  ≈⟨ cdr (car (π-cong (sym assoc) (sym assoc) )) ⟩ 
                 ε ∙  ((< ((k ∙ α) *) ∙ (<  π  , π ∙ π' > ∙ α )  , π' ∙ (π' ∙ α) >) ∙ α')  
                    ≈⟨ cdr (car (π-cong (cdr (IsCCC.distr-π isCCC)) (cdr (IsCCC.e3b isCCC)) )) ⟩ 
                 ε ∙  ((< ((k ∙ α) *) ∙ (<  π  ∙ α , (π ∙ π') ∙ α > )  , π' ∙ < π' ∙ π , π' > >) ∙ α')  
                    ≈⟨ cdr (car (π-cong (cdr (π-cong (IsCCC.e3a isCCC) (sym assoc) ) ) (IsCCC.e3b isCCC) )) ⟩ 
                 ε ∙  ((< ((k ∙ α) *) ∙ (<  π  ∙ π , π ∙ (π' ∙ α) > )  , π' > ) ∙ α')  
                    ≈⟨ cdr (car (π-cong (cdr (π-cong refl-hom (cdr (IsCCC.e3b isCCC)))) refl-hom)) ⟩ 
                 ε ∙  ((< ((k ∙ α) *) ∙ (<  π  ∙ π , π ∙ < π' ∙ π , π' > > )  , π' > ) ∙ α')  
                    ≈⟨ cdr (car (π-cong (cdr (π-cong refl-hom (IsCCC.e3a isCCC) )) refl-hom )) ⟩ 
                 ε ∙  ((< ((k ∙ α) *) ∙ (<  π  ∙ π , π' ∙ π > )  , π' > ) ∙ α')  ≈⟨ cdr (car (π-cong (cdr (sym (IsCCC.distr-π isCCC))) refl-hom)) ⟩ 
                 ε ∙  ((< ((k ∙ α) *) ∙ (<  π , π' > ∙ π )  , π' > ) ∙ α')  ≈⟨ cdr (car (π-cong (cdr (car (IsCCC.π-id isCCC))) refl-hom)) ⟩ 
                 ε ∙  (< ((k ∙ α) *) ∙ (id1 A _ ∙ π )  , π' >  ∙ α')  ≈⟨ cdr (car (π-cong (cdr idL ) refl-hom)) ⟩ 
                 ε ∙ ( < ((k ∙ α) *) ∙  π ,  π' > ∙ α' ) ≈⟨ assoc ⟩ 
                (ε ∙ < ((k ∙ α) *) ∙  π ,  π' >) ∙ α' ≈⟨ car (IsCCC.e4a isCCC) ⟩ 
                (k ∙ α) ∙ α' ≈⟨ sym assoc ⟩ 
                k ∙ (α ∙ α') ≈⟨ cdr α-iso ⟩ 
                k ∙ id1 A _ ≈⟨ idR ⟩ 
                k ∎
            ;  e4b = λ {a₁} {b} {c} {k} → begin 
                (( ( ( ε ∙ π') ∙ < π , < (k ∙ < π , (π ∙ π') ∙ π' > ) ∙ < π , id1 A _ >  , π' ∙ π' > ∙ π' > )  ∙ < π , id1 A _ > ) ∙ α ) * 
                   ≈⟨ IsCCC-*-cong.*-cong is*-CCC ( begin  
                ( ( ( ε ∙ π') ∙ < π , < (k ∙ < π , (π ∙ π') ∙ π' > ) ∙ < π , id1 A _ >  , π' ∙ π' > ∙ π' > )  ∙ < π , id1 A _ > ) ∙ α  ≈⟨ car (sym assoc) ⟩ 
                (  ( ε ∙ π') ∙ ( < π , < (k ∙ < π , (π ∙ π') ∙ π' > ) ∙ < π , id1 A _ >  , π' ∙ π' > ∙ π' >   ∙ < π , id1 A _ > )) ∙ α  
                     ≈⟨ car (cdr (IsCCC.distr-π isCCC)) ⟩ 
                (  ( ε ∙ π') ∙  < π ∙ < π , id1 A _ > , (< (k ∙ < π , (π ∙ π') ∙ π' > ) ∙ < π , id1 A _ >  , π' ∙ π' > ∙ π' ) ∙ < π , id1 A _ > > ) ∙ α  
                     ≈⟨ car (cdr (π-cong (IsCCC.e3a isCCC) (sym assoc) ) ) ⟩ 
                (  ( ε ∙ π') ∙  < π  , (< (k ∙ < π , (π ∙ π') ∙ π' > ) ∙ < π , id1 A _ >  , π' ∙ π' >) ∙ ( π'  ∙ < π , id1 A _ >) > ) ∙ α  
                     ≈⟨ car (cdr (π-cong refl-hom (resp (IsCCC.e3b isCCC) (π-cong (sym assoc) refl-hom ) ) )) ⟩ 
                (  ( ε ∙ π') ∙  < π  , (< k ∙ ( < π , (π ∙ π') ∙ π' > ∙ < π , id1 A _ >)  , π' ∙ π' >) ∙  id1 A _  > ) ∙ α  
                     ≈⟨ car (cdr (π-cong refl-hom idR )) ⟩ 
                (  ( ε ∙ π') ∙  < π  , (< k ∙ ( < π , (π ∙ π') ∙ π' > ∙ < π , id1 A _ >)  , π' ∙ π' >) > ) ∙ α  
                     ≈⟨ car (cdr (π-cong refl-hom (π-cong (cdr (IsCCC.distr-π isCCC)) refl-hom) )) ⟩ 
                (  ( ε ∙ π') ∙  < π  , (< k ∙ ( < π ∙ < π , id1 A _ > , ((π ∙ π') ∙ π' ) ∙ < π , id1 A _ > > )  , π' ∙ π' >) > ) ∙ α  
                     ≈⟨ car (cdr (π-cong refl-hom (π-cong (cdr (π-cong (IsCCC.e3a isCCC)  (sym assoc)) ) refl-hom ))) ⟩ 
                (  ( ε ∙ π') ∙  < π  , (< k ∙ ( < π  , (π ∙ π') ∙ (π'  ∙ < π , id1 A _ >) > )  , π' ∙ π' >) > ) ∙ α  
                     ≈⟨ car (cdr (π-cong refl-hom (π-cong (cdr (π-cong refl-hom (cdr (IsCCC.e3b isCCC) )) ) refl-hom ))) ⟩ 
                (  ( ε ∙ π') ∙  < π  , (< k ∙ ( < π  , (π ∙ π') ∙ id1 A _ > )  , π' ∙ π' >) > ) ∙ α  
                     ≈⟨ car (cdr (π-cong refl-hom (π-cong (cdr (π-cong refl-hom idR ) ) refl-hom ))) ⟩ 
                (  ( ε ∙ π') ∙  < π  , (< k ∙ ( < π  , (π ∙ π') > )  , π' ∙ π' >) > ) ∙ α  ≈⟨ car (sym assoc) ⟩ 
                  ( ε ∙ ( π' ∙  < π  , (< k ∙ ( < π  , (π ∙ π') > )  , π' ∙ π' >) > )) ∙ α  ≈⟨ car (cdr (IsCCC.e3b isCCC)) ⟩ 
                  ( ε ∙ < k ∙ ( < π  , (π ∙ π') > )  , π' ∙ π' >) ∙ α  ≈⟨ sym assoc ⟩ 
                   ε ∙ ( < k ∙ ( < π  , (π ∙ π') > )  , π' ∙ π' > ∙ α )  ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩ 
                   ε ∙  < (k ∙ ( < π  , (π ∙ π') > )) ∙ α   , (π' ∙ π' ) ∙ α >  ≈⟨ cdr (π-cong (sym assoc) (sym assoc) ) ⟩ 
                   ε ∙  < k ∙ ( < π  , (π ∙ π') >  ∙ α) , π' ∙ ( π'  ∙ α) >  ≈⟨ cdr (π-cong (cdr (IsCCC.distr-π isCCC)) (cdr (IsCCC.e3b isCCC) )) ⟩ 
                   ε ∙  < k ∙  < π ∙ α , (π ∙ π') ∙ α > , π' ∙ <  π' ∙ π , π' > >  ≈⟨ cdr (π-cong (cdr (π-cong refl-hom (sym assoc))) (IsCCC.e3b isCCC)) ⟩ 
                   ε ∙  < k ∙  < π ∙ α , π ∙ ( π' ∙ α ) >  , π'  >  ≈⟨ cdr (π-cong (cdr (π-cong refl-hom (cdr (IsCCC.e3b isCCC))  )) refl-hom ) ⟩ 
                   ε ∙  < k ∙  < π ∙ α , π ∙ < π' ∙ π , π' > >  , π'  >  ≈⟨ cdr (π-cong (cdr (π-cong (IsCCC.e3a isCCC) (IsCCC.e3a isCCC) ))  refl-hom ) ⟩ 
                   ε ∙  < k ∙  < π ∙ π ,  π' ∙ π >  , π'  >  ≈⟨ cdr (π-cong (cdr (sym (IsCCC.distr-π isCCC))) refl-hom) ⟩ 
                   ε ∙  < k ∙  ( < π ,  π' > ∙ π )  , π'  >  ≈⟨ cdr (π-cong (cdr (car (IsCCC.π-id isCCC))) refl-hom) ⟩ 
                   ε ∙  < k ∙  ( id1 A _  ∙ π )  , π'  >  ≈⟨ cdr (π-cong (cdr idL) refl-hom) ⟩ 
                   ε ∙  < k ∙  π   , π'  > ∎ ) ⟩ 
                ( ε ∙ <  k ∙ π ,  π'  > ) * ≈⟨ IsCCC.e4b isCCC ⟩
                k ∎
        }
        ; is*-CCC = record {
             *-cong = λ {a'} {b} {c} {f} {f'} f=f' → *-cong (resp refl-hom f=f' ) 
          }
     } where open ≈-Reasoning A


  open NTrans

  H : {a : Obj A} (x : Hom A １ a) → Functor A (Poly x) 
  H {a} x = record {
          FObj = λ b → b
        ; FMap = λ {b} {c} f → f ∙ π' 
        ; isFunctor = record {
              ≈-cong = λ {b} {c} {f} {g} f≈g → begin
                  f ∙ π'  ≈⟨ car f≈g ⟩
                  g ∙ π'  ∎ 
          ;  identity = λ {b} → begin
              id1 A b ∙ π'  ≈⟨ idL ⟩
              π'  ≈⟨⟩
              id1 (Poly x) _   ∎
           ; distr = λ {b} {c} {d} {f} {g} → begin
              (g ∙ f) ∙ π'  ≈↑⟨ assoc ⟩
              g ∙ (f ∙ π') ≈↑⟨ cdr idR ⟩
              g ∙ ((f ∙ π') ∙ id1 A _)   ≈↑⟨ cdr (cdr (IsCCC.e3b isCCC)) ⟩
              g ∙ ((f ∙ π') ∙ (π'  ∙ < π , id1 A _ >))   ≈⟨ cdr assoc ⟩
              g ∙ (((f ∙ π') ∙ π' ) ∙ < π , id1 A _ >)   ≈⟨ assoc ⟩
              (g ∙ ((f ∙ π') ∙ π' )) ∙ < π , id1 A _ >   ≈↑⟨ car (cdr (IsCCC.e3b isCCC)) ⟩
              (g ∙ (π' ∙ < π , (f ∙ π') ∙ π'  > )) ∙ < π , id1 A _ >   ≈⟨ car assoc ⟩
              ((g ∙ π') ∙ < π , (f ∙ π') ∙ π'  > ) ∙ < π , id1 A _ >   ≈⟨⟩
              (Poly x) [ (g ∙ π') o (f  ∙ π') ]  ∎
         }
      } where open ≈-Reasoning A

  -- The Polynominal arrow  -- λ term in A
  --
  -- arrow in A[x], equality in A[x] should be a modulo x, that is  k x phi ≈ k x phi'
  -- the smallest equivalence relation
  --
  -- if we use equality on f as in A, Poly is ovioously Hom c b of a Category.
  -- it is better to define A[x] as an extension of A as described before

  record Polym {a : Obj A} (x : Hom A １ a) (b c : Obj A )  : Set (c₁ ⊔ c₂ ⊔ ℓ)  where
     field
        f :  Hom A b c
        phi  : φ x {b} {c} f

  --
  --   this is justified equality f ≈ g in A[x] is used in f ∙ < x , id1 A _> ≈  f ∙ < x , id1 A _>
  --   ( x ∙ π' ) ∙ < x , id1 A _ > ≈ π ∙ < x , id1 A _ >

  -- f  ≈ g → k x {f} _ ≡  k x {g} _   Lambek p.60

  ki : {a b c : Obj A} → (x : Hom A １ a) → (f : Hom A b c ) → (fp  :  φ x {b} {c} f )
     →  A [ k x (i f) ≈ k x fp ]
  ki x f (i _) = refl-hom where
      open ≈-Reasoning A
  ki {a} {b} {c} x .x ii = lem2 where -- this will not happen because x may not be in A
       lem : Hom A (a ∧ b) a
       lem = x ∙ π'
       lem1 : Hom A (a ∧ b) a
       lem1 = π
       lem3 : A [ x ∙ π' ≈ π ]
       lem3 = ?
       lem2 : A [ k x (i x) ≈ k x ii ] 
       lem2 = lem3
  ki x _ (iii {_} {_} {_} {f₁}{ f₂} fp₁ fp₂ ) = begin
               < f₁ ,  f₂  > ∙ π'  ≈⟨ IsCCC.distr-π isCCC ⟩
               < f₁ ∙ π'  ,  f₂   ∙ π' >  ≈⟨ π-cong (ki x f₁ fp₁  ) (ki x f₂ fp₂  ) ⟩
                k x (iii  fp₁ fp₂ )  ∎ where
      open ≈-Reasoning A
  ki x _ (iv {_} {_} {_} {f₁} {f₂} fp fp₁) = begin
               (f₁ ∙ f₂  ) ∙ π'  ≈↑⟨ assoc ⟩
               f₁  ∙ ( f₂ ∙ π')  ≈↑⟨ cdr (IsCCC.e3b isCCC) ⟩
               f₁  ∙ ( π'  ∙ < π , (f₂ ∙ π' )  >)  ≈⟨ assoc ⟩
               (f₁  ∙ π' ) ∙ < π , (f₂ ∙ π' )  >  ≈⟨ resp (π-cong refl-hom (ki x _ fp₁  )) (ki x _ fp  ) ⟩
               k x fp ∙ < π , k x fp₁ >  ≈⟨⟩
               k x (iv fp fp₁ )  ∎ where
      open ≈-Reasoning A
  ki x _ (v {_} {_} {_} {f} fp) = begin
               (f *) ∙ π' ≈⟨ distr-*  ⟩
               ( f ∙ < π' ∙ π , π'  > ) * ≈↑⟨ *-cong (cdr (IsCCC.e3b isCCC)) ⟩
               ( f ∙ ( π'  ∙  < π ∙ π , < π' ∙  π , π' > > ) ) *  ≈⟨ *-cong assoc  ⟩
               ( (f ∙ π')  ∙  < π ∙ π , < π' ∙  π , π' > > ) *  ≈⟨ *-cong ( car ( ki x _ fp )) ⟩
               ( k x fp ∙  < π ∙ π , < π' ∙  π , π' > > ) *  ≈⟨⟩
               k x (v fp )  ∎ where
      open ≈-Reasoning A

-- k-cong : {a b c : Obj A}  (x : Hom A １ a ) → (f g :  Polym x c b )
--       → A [ Polym.f f ≈ Polym.f g ] → A [ k x (Polym.phi f)   ≈ k x (Polym.phi g) ]
-- k-cong {a} {b} {c} x f g f=f = begin
--         k x (Polym.phi f) ≈↑⟨ ?  ⟩
--         Polym.f f ∙ π' ≈⟨ car f=f  ⟩
--         Polym.f g ∙ π'  ≈⟨ ? ⟩
--         k x (Polym.phi g) ∎ where
--     open ≈-Reasoning A


  -- since we have A[x] now, we can proceed the proof on p.64 in some possible future

  --
  --  Proposition 6.1
  --
  --  For every polynominal ψ(x) : b → c in an indeterminate x : 1 → a over a cartesian or cartesian closed
  --  category A there is a unique arrow f : a ∧ b → c in A such that f ∙ < x ∙ ○ b , id1 A b > ≈ ψ(x).

  record Functional-completeness {a b c : Obj A} (x : Hom A １ a)(  p : Polym x b c ) : Set  (c₁ ⊔ c₂ ⊔ ℓ) where
    field
      fun  : Hom A (a ∧ b) c
      fp   : A [  fun ∙ <  x ∙ ○ b   , id1 A b  >  ≈ Polym.f p  ]
      uniq : ( f : Hom A (a ∧ b) c) → A [ f ∙ < x ∙ ○ b , id1 A b > ≈ Polym.f p ] → A [ f ≈ fun  ]

  record Functional-completenessF {a b c : Obj A} (x : Hom A １ a)(  p : Hom (Poly x) b c ) : Set  (c₁ ⊔ c₂ ⊔ ℓ) where
    field
      fun  : Hom A (a ∧ b) c
      fp   : A [  fun ∙ <  x ∙ ○ b   , id1 A b  >  ≈ p ∙ <  x ∙ ○ b   , id1 A b  > ]
      uniq : ( f : Hom A (a ∧ b) c) → A [ f ∙ < x ∙ ○ b , id1 A b > ≈ p ∙ <  x ∙ ○ b   , id1 A b  > ] → A [ f ≈ fun  ]

  -- ε form
  -- f ≡ λ (x ∈ a) → φ x , ∃ (f : b <= a) →  f ∙ x ≈  φ x
  record FcF {a b : Obj A } (x : Hom A １ a) ( φ :  Hom (Poly x) １ b )
         :  Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
    field
      sl :  Hom A a b
    g :  Hom A １ (b <= a)
    g  = ( sl ∙ π'  ) *
    field
      isSelect : A [   ε ∙ < g  , x >   ≈  sl ∙ x  ]
      isUnique : (f : Hom A １ (b <= a) )  → A [   ε ∙ < f , x  >   ≈  sl ∙ x  ]
        →  A [ g ≈ f ]

  record Fc {a b : Obj A } (x : Hom A １ a) ( φ :  Polym x １ b )
         :  Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
    field
      sl :  Hom A a b
    g :  Hom A １ (b <= a)
    g  = ( sl ∙ π'  ) *
    field
      isSelect : A [   ε ∙ < g  , x >   ≈  Polym.f φ  ]
      isUnique : (f : Hom A １ (b <= a) )  → A [   ε ∙ < f , x  >   ≈  Polym.f φ ]
        →  A [ g ≈ f ]

  functional-completenessF : {a b c : Obj A} (x : Hom A １ a) ( p : Hom (Poly x) c b ) → Functional-completenessF x p
  functional-completenessF {a} {b} {c} x p = record {
         fun = p
       ; fp = refl-hom
       ; uniq = λ f eq → begin 
            f ≈⟨ sym idR ⟩
            f ∙ id1 A _ ≈⟨ cdr (sym (lem-eq c)) ⟩
            f ∙ (< x ∙ ○ c , id1 A c > ∙ π' ) ≈⟨ assoc ⟩
            (f ∙ < x ∙ ○ c , id1 A c >) ∙ π'  ≈⟨ car eq ⟩
            (p ∙ < x ∙ ○ c , id1 A c >) ∙ π'  ≈⟨ sym assoc ⟩
            p ∙ (< x ∙ ○ c , id1 A c > ∙ π')  ≈⟨ cdr (lem-eq c) ⟩
            p ∙ id1 A _  ≈⟨ idR ⟩
            p  ∎
     }  where
        open ≈-Reasoning A
        lem : Hom A b ( a ∧ b )
        lem = <  x ∙ ○ b   , id1 A b  >
        inv : Hom A ( a ∧ b ) b
        inv = π'
        lem3 : (b : Obj A ) → A [ x ∙ (○ (a ∧ b)) ≈ π ] 
        lem3 b = begin
            x ∙ (○ (a ∧ b))  ≈⟨ cdr (sym (IsCCC.e2 isCCC)) ⟩
            x ∙ (○ _ ∙ π')  ≈⟨ ? ⟩
            π ∎ 
        lem-eq : (b : Obj A) → A [ <  x ∙ ○ b   , id1 A b  > ∙ π' ≈ id1 A ( a ∧ b ) ]
        lem-eq b = begin
              <  x ∙ ○ b   , id1 A b  > ∙ π'  ≈⟨ IsCCC.distr-π isCCC ⟩
              < (x ∙  ○ b) ∙ π' , id1 A b ∙ π' >    ≈⟨ π-cong (sym assoc) idL ⟩
              < x ∙  (○ b ∙ π') , π' >    ≈⟨ π-cong (cdr (IsCCC.e2 isCCC)) refl-hom ⟩
              < x ∙  ○ (a ∧ b) , π' >    ≈⟨ π-cong (lem3 b) refl-hom  ⟩
              < π , π' >    ≈⟨ IsCCC.π-id isCCC ⟩
              id1 A ( a ∧ b )  ∎

  -- proof in p.59 Lambek
  --
  --  (ψ : Poly a c b) is basically λ x.ψ(x). To use x from outside as a ψ(x), apply x ψ will work.
  --  Instead of replacing x in Polym.phi ψ, we can use simple application with this fuctional completeness
  --  in the internal language of Topos.
  --

  functional-completeness : {a b c : Obj A} (x : Hom A １ a) ( p : Polym x c b ) → Functional-completeness x p
  functional-completeness {a} {b} {c} x p = record {
         fun = k x (Polym.phi p)
       ; fp = fc0 x (Polym.f p) (Polym.phi p)
       ; uniq = λ f eq  → uniq p f eq
     } where
        open ≈-Reasoning A
        fc0 : {a b c : Obj A}  → (x :  Hom A １ a) (f :  Hom A b c) (phi  :  φ x {b} {c} f )
           → A [  k x phi ∙ <  x ∙ ○ b  , id1 A b >  ≈ f ]
        fc0 {a} {b} {c} x f' phi with phi
        ... | i {_} {_} s = begin
             (s ∙ π') ∙ < ( x ∙ ○ b ) , id1 A b > ≈↑⟨ assoc ⟩
             s ∙ (π' ∙ < ( x ∙ ○ b ) , id1 A b >) ≈⟨ cdr (IsCCC.e3b isCCC ) ⟩
             s ∙ id1 A b ≈⟨ idR ⟩
             s ∎
        ... | ii = begin
             π ∙ < ( x ∙ ○ b ) , id1 A b > ≈⟨ IsCCC.e3a isCCC ⟩
             x ∙ ○ b  ≈↑⟨ cdr (e2 ) ⟩
             x ∙ id1 A b  ≈⟨ idR ⟩
             x ∎
        ... | iii {_} {_} {_} {f} {g} y z  = begin
             < k x y , k x z > ∙ < (x ∙ ○ b ) , id1 A b > ≈⟨ IsCCC.distr-π isCCC  ⟩
             < k x y ∙ < (x ∙ ○ b ) , id1 A b > , k x z ∙ < (x ∙ ○ b ) , id1 A b > >
                 ≈⟨ π-cong (fc0 x  f y ) (fc0 x g z ) ⟩
             < f , g > ≈⟨⟩
             f'  ∎
        ... | iv {_} {_} {d} {f} {g} y z  = begin
             (k x y ∙ < π , k x z >) ∙ < ( x ∙ ○ b ) , id1 A b > ≈↑⟨ assoc ⟩
             k x y ∙ ( < π , k x z > ∙ < ( x ∙ ○ b ) , id1 A b > ) ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩
             k x y ∙ ( < π  ∙ < ( x ∙ ○ b ) , id1 A b > ,  k x z  ∙ < ( x ∙ ○ b ) , id1 A b > > )
                 ≈⟨ cdr (π-cong (IsCCC.e3a isCCC) (fc0 x g z ) ) ⟩
             k x y ∙ ( < x ∙ ○ b  ,  g > ) ≈↑⟨ cdr (π-cong (cdr (e2)) refl-hom ) ⟩
             k x y ∙ ( < x ∙ ( ○ d ∙ g ) ,  g > ) ≈⟨  cdr (π-cong assoc (sym idL)) ⟩
             k x y ∙ ( < (x ∙ ○ d) ∙ g  , id1 A d ∙ g > ) ≈↑⟨ cdr (IsCCC.distr-π isCCC) ⟩
             k x y ∙ ( < x ∙ ○ d ,  id1 A d > ∙ g ) ≈⟨ assoc ⟩
             (k x y ∙  < x ∙ ○ d ,  id1 A d > ) ∙ g  ≈⟨ car (fc0 x f y ) ⟩
             f ∙ g  ∎
        ... | v {_} {_} {_} {f} y = begin
            ( (k x y ∙ < π ∙ π , <  π' ∙  π , π' > >) *) ∙ < x ∙ (○ b) , id1 A b > ≈⟨ distr-* ⟩
            ( (k x y ∙ < π ∙ π , <  π' ∙  π , π' > >) ∙ < < x ∙ ○ b , id1 A _ > ∙ π , π' > ) * ≈⟨  *-cong ( begin
             ( k x y ∙ < π ∙ π , <  π' ∙  π , π' > >) ∙ < < x ∙ ○ b , id1 A _ > ∙ π , π' >   ≈↑⟨ assoc ⟩
              k x y ∙ ( < π ∙ π , <  π' ∙  π , π' > > ∙ < < x ∙ ○ b , id1 A _ > ∙ π , π' > )   ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩
              k x y ∙ < (π ∙ π) ∙ < < x ∙ ○ b , id1 A _ > ∙ π , π' >  , <  π' ∙  π , π' > ∙ < < x ∙ ○ b , id1 A _ > ∙ π , π' >  >
                  ≈⟨ cdr (π-cong (sym assoc) (IsCCC.distr-π isCCC )) ⟩
              k x y ∙ < π ∙ (π ∙ < < x ∙ ○ b , id1 A _ > ∙ π , π' > ) ,
                <  (π' ∙  π) ∙ < < x ∙ ○ b , id1 A _ > ∙ π , π' > , π'  ∙ < < x ∙ ○ b , id1 A _ > ∙ π , π' > > >
                    ≈⟨ cdr ( π-cong (cdr (IsCCC.e3a isCCC))( π-cong (sym assoc) (IsCCC.e3b isCCC) )) ⟩
              k x y ∙ < π ∙ ( < x ∙ ○ b , id1 A _ > ∙ π  ) , <  π' ∙  (π ∙ < < x ∙ ○ b , id1 A _ > ∙ π , π' >) ,  π'  > >
                ≈⟨  cdr ( π-cong refl-hom (  π-cong (cdr (IsCCC.e3a isCCC)) refl-hom )) ⟩
              k x y ∙ < (π ∙ ( < x ∙ ○ b , id1 A _ > ∙ π ) ) , <  π' ∙  (< x ∙ ○ b , id1 A _ > ∙ π ) , π' > >
                ≈⟨ cdr ( π-cong  assoc (π-cong  assoc refl-hom )) ⟩
              k x y ∙ < (π ∙  < x ∙ ○ b , id1 A _ > ) ∙ π   , <  (π' ∙  < x ∙ ○ b , id1 A _ > ) ∙ π  , π' > >
                  ≈⟨ cdr (π-cong (car (IsCCC.e3a isCCC)) (π-cong (car (IsCCC.e3b isCCC)) refl-hom ))  ⟩
              k x y ∙ < ( (x ∙ ○ b ) ∙ π )  , <   id1 A _  ∙ π  , π' > >    ≈⟨ cdr (π-cong (sym assoc)  (π-cong idL refl-hom ))  ⟩
              k x y ∙ <  x ∙ (○ b  ∙ π )  , <    π  , π' > >    ≈⟨   cdr (π-cong (cdr (e2)) (IsCCC.π-id isCCC) ) ⟩
              k x y ∙  < x ∙ ○ _ , id1 A _  >    ≈⟨ fc0 x f y  ⟩
             f  ∎ )  ⟩
             f * ∎
        --
        --   f ∙ <  x ∙ ○ b  , id1 A b >  ≈ f →  f ≈ k x (phi p)
        --     p.61
        uniq : {b c : Obj A}  →  (p : Polym x b c ) (f' : Hom A (a ∧ b) c)
            → A [  f' ∙ <  x ∙ ○ b  , id1 A b >  ≈ Polym.f p ] → A [ f' ≈ k x (Polym.phi p) ]
        uniq {b} {c} p f' fx=p  = sym (begin
               k x phi ≈↑⟨ ki x _ phi ⟩
               k x {f} (i _) ≈↑⟨ car fx=p ⟩
               k x {f' ∙ < x ∙ ○ b , id1 A b >} (i _)  ≈⟨ trans-hom (sym assoc)  (cdr (IsCCC.distr-π isCCC) ) ⟩ -- ( f' ∙ < x ∙ ○ b , id1 A b> ) ∙ π'
               f' ∙ k x {< x ∙ ○ b , id1 A b >} (iii (i _)  (i _)  ) ≈⟨⟩                         -- ( f' ∙ < (x ∙ ○ b) ∙ π'  , id1 A b ∙ π' > )
               f' ∙ < k x (i (x ∙ ○ b)) ,  k x {id1 A b} (i _) >  ≈⟨ cdr ( π-cong u3 refl-hom ) ⟩ 
               f' ∙ < k x (iv ii (i _)) ,  k x {id1 A b} (i _) >  ≈⟨⟩ -- ( f' ∙ < (x ∙ ○ b) ∙ π' , id1 A b ∙ π' > )
               f' ∙ < k x {x} ii ∙ < π , k x {○ b} (i _)  >  , k x {id1 A b} (i _)  >   -- ( f' ∙ < π ∙ < π , (x ∙ ○ b) ∙ π' >  , id1 A b ∙ π' > )
                    ≈⟨ cdr (π-cong (cdr (π-cong refl-hom (car e2))) idL ) ⟩
               f' ∙  <  π ∙ < π , (○ b ∙ π' ) >  , π' >   ≈⟨ cdr (π-cong (IsCCC.e3a isCCC)  refl-hom) ⟩
               f' ∙  < π , π' >  ≈⟨ cdr (IsCCC.π-id isCCC) ⟩
               f' ∙  id1 A _ ≈⟨ idR ⟩
               f' ∎  )  where
                   u3 : k x (i (x o ○ b )) ≈ k x (iv ii (i (○ b)) )  
                   u3 = ki x (x ∙ ○ b) (iv ii (i _))
                   phi = Polym.phi p
                   f = Polym.f p
  
  
  -- functional completeness ε form
  --
  --  g : Hom A １ (b <= a)       fun : Hom A (a ∧ １) c
  --       fun *                       ε ∙ < g ∙ π , π' >
  --  a -> d <= b  <-> (a ∧ b ) -> d
  --
  --   fun ∙ <  x ∙ ○ b   , id1 A b  >  ≈ Polym.f p
  --   (ε ∙ < g ∙ π , π' >) ∙ <  x ∙ ○ b   , id1 A b  >  ≈ Polym.f p
  --      could be simpler
  FC : {a b : Obj A} (x : Hom A １ a) → (φ  : Polym x １ b )  → Fc {a} {b} x φ
  FC {a} {b} x φ = record {
     sl =  k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >
     ; isSelect = isSelect
     ; isUnique = uniq
    }  where
        open ≈-Reasoning A
        π-exchg = IsCCC.π-exchg isCCC
        fc0 :  {b c : Obj A} (p : Polym x １ c) → A [  k x (Polym.phi p) ∙ <  x  ∙  ○ １  , id1 A １ >  ≈ Polym.f p ]
        fc0 p =  Functional-completeness.fp (functional-completeness x p)
        gg : A [ (  k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ x ≈ Polym.f φ ]
        gg  = begin
          ( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ x   ≈⟨ trans-hom (sym assoc) (cdr (IsCCC.distr-π isCCC ) ) ⟩
          k x (Polym.phi φ) ∙ <  id1 A _ ∙  x  ,  ○ a ∙ x >  ≈⟨ cdr (π-cong idL e2 ) ⟩
          k x (Polym.phi φ) ∙ <   x  ,  ○ １ >  ≈⟨ cdr (π-cong (trans-hom (sym idR) (cdr e2) )  (sym e2) ) ⟩
          k x (Polym.phi φ) ∙ <  x  ∙  ○ １  , id1 A １ >  ≈⟨ fc0 {a} {b} φ  ⟩
          Polym.f φ ∎
        isSelect :  A [ ε ∙ < ( ( k x (  Polym.phi φ) ∙ < id1 A _ , ○ a > ) ∙ π' ) * , x >  ≈ Polym.f φ ]
        isSelect =      begin
          ε ∙ <  ((k (x) (Polym.phi φ)∙ < id1 A _ ,  ○ a > ) ∙ π')  * ,  x  > ≈↑⟨ cdr (π-cong idR refl-hom ) ⟩
          ε ∙ (< ((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙   id1 A _   ,  x > )  ≈⟨ cdr (π-cong (cdr e2) refl-hom ) ⟩
          ε ∙ (< ((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙   ○ １ ,  x > )  ≈↑⟨ cdr (π-cong (cdr e2) refl-hom ) ⟩
          ε ∙ (< ((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙   (○ a  ∙ x)  ,  x > )  ≈↑⟨ cdr (π-cong (sym assoc) idL ) ⟩
          ε ∙ (< (((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙   ○ a ) ∙ x  ,  id1 A _ ∙ x > )
              ≈↑⟨ cdr (IsCCC.distr-π isCCC)  ⟩
          ε ∙ ((< (((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙   ○ a ) ,  id1 A _ > )  ∙ x )
              ≈↑⟨ cdr (car (π-cong (cdr (IsCCC.e3a isCCC) ) refl-hom))  ⟩
          ε ∙ ((< (((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙  (π  ∙ <  ○ a , id1 A _ > )) ,  id1 A _ > )  ∙ x )
              ≈⟨ cdr (car (π-cong assoc (sym (IsCCC.e3b isCCC)) )) ⟩
          ε ∙ ((< ((((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙  π ) ∙ <  ○ a , id1 A _ > ) , (π' ∙  <  ○ a , id1 A _ > ) > )  ∙ x )
              ≈↑⟨ cdr (car (IsCCC.distr-π isCCC)) ⟩
            ε ∙ ((< ((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙  π , π' >  ∙ <  ○ a , id1 A _ > )  ∙ x )  ≈⟨ assoc ⟩
            (ε ∙ (< ((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙  π , π' >  ∙ <  ○ a , id1 A _ > ) ) ∙ x   ≈⟨ car assoc ⟩
          ((ε ∙ < ((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙  π , π' > ) ∙ <  ○ a , id1 A _ >  ) ∙ x
              ≈⟨ car (car (IsCCC.e4a isCCC))  ⟩
          ((( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) ∙ <  ○ a , id1 A _ >  ) ∙ x   ≈↑⟨ car assoc ⟩
          (( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ (π' ∙ <  ○ a , id1 A _ > ) ) ∙ x   ≈⟨ car (cdr (IsCCC.e3b isCCC)) ⟩
          (( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ id1 A _ ) ∙ x   ≈⟨ car idR ⟩
          ( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ x   ≈⟨ gg  ⟩
          Polym.f φ ∎
        uniq  :  (f : Hom A １ (b <= a)) → A [  ε ∙ < f , x >  ≈ Polym.f φ ] →
            A [ (( k (x) (Polym.phi φ) ∙  < id1 A _  , ○ a > )∙ π' ) * ≈ f ]
        uniq f eq = begin
           (( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ π' ) *   ≈⟨ *-cong ( begin
              (k (x) (Polym.phi φ) ∙ < id1 A _ , ○ a >) ∙ π' ≈↑⟨ assoc ⟩
              k (x) (Polym.phi φ) ∙ (< id1 A _ , ○ a > ∙ π') ≈⟨ car ( sym (Functional-completeness.uniq (functional-completeness x φ) _ ( begin
                ((ε ∙ < f ∙ π , π' >) ∙ < π' , π >) ∙ < x ∙ ○ １ , id1 A １ > ≈↑⟨ assoc ⟩
                (ε ∙ < f ∙ π , π' >) ∙ ( < π' , π > ∙ < x ∙ ○ １ , id1 A １ > ) ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩
                (ε ∙ < f ∙ π , π' >) ∙  < π' ∙ < x ∙ ○ １ , id1 A １ > , π ∙  < x ∙ ○ １ , id1 A １ > >
                     ≈⟨ cdr (π-cong (IsCCC.e3b isCCC) (IsCCC.e3a isCCC)) ⟩
                (ε ∙ < f ∙ π , π' >) ∙  < id1 A １  ,  x ∙ ○ １ > ≈↑⟨ assoc ⟩
                ε ∙ ( < f ∙ π , π' > ∙  < id1 A １  ,  x ∙ ○ １ > ) ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩
                ε ∙ ( < (f ∙ π ) ∙  < id1 A １  ,  x ∙ ○ １ > , π'  ∙  < id1 A １  ,  x ∙ ○ １ > > ) ≈⟨ cdr (π-cong (sym assoc) (IsCCC.e3b isCCC)) ⟩
                ε ∙ ( < f ∙ (π  ∙  < id1 A １  ,  x ∙ ○ １ > ) ,  x ∙ ○ １  > ) ≈⟨ cdr (π-cong (cdr (IsCCC.e3a isCCC)) (cdr (trans-hom e2 (sym e2)))) ⟩
                ε ∙ ( < f ∙ id1 A １ ,  x ∙ id1 A １  > ) ≈⟨ cdr (π-cong idR idR ) ⟩
                 ε ∙ < f , x > ≈⟨ eq ⟩
                Polym.f φ ∎ ))) ⟩
              ((ε ∙ < f ∙ π , π' > ) ∙ < π' , π > ) ∙  ( < id1 A _ ,  ○ a > ∙ π' ) ≈↑⟨ assoc ⟩
              (ε ∙ < f ∙ π , π' > ) ∙ (< π' , π > ∙ ( < id1 A _ ,  ○ a > ∙ π' ) )  ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩
              (ε ∙ < f ∙ π , π' > ) ∙ (< π'  ∙ ( < id1 A _ ,  ○ a > ∙ π' ) , π ∙ ( < id1 A _ ,  ○ a > ∙ π' ) > )  ≈⟨ cdr (π-cong assoc assoc ) ⟩
              (ε ∙ < f ∙ π , π' > ) ∙ (< (π'  ∙  < id1 A _ ,  ○ a > ) ∙ π'  , (π ∙ < id1 A _ ,  ○ a > ) ∙ π'   > )
                 ≈⟨ cdr (π-cong (car (IsCCC.e3b isCCC)) (car (IsCCC.e3a isCCC) ))  ⟩
              (ε ∙ < f ∙ π , π' > ) ∙ < ○ a  ∙ π'  ,  id1 A _ ∙ π'   >   ≈⟨ cdr (π-cong (trans-hom e2 (sym e2) ) idL ) ⟩
              (ε ∙ < f ∙ π , π' > ) ∙ <  π  ,   π'   >   ≈⟨ cdr (IsCCC.π-id isCCC) ⟩
              (ε ∙ < f ∙ π , π' > ) ∙ id1 A  (１ ∧ a) ≈⟨ idR ⟩
              ε ∙ < f ∙ π , π' > ∎ ) ⟩
           ( ε ∙ < A [ f o π ] , π' > ) *   ≈⟨ IsCCC.e4b isCCC  ⟩
           f ∎
  
