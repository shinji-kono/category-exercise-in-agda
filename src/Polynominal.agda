{-# OPTIONS --allow-unsolved-metas #-}

open import Category
open import CCC
open import Level
open import HomReasoning 
open import cat-utility

module Polynominal { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) ( C : CCC A )   where

  open CCC.CCC C
  open ≈-Reasoning A hiding (_∙_)

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
  --
  -- this makes a few changes, but we don't care.
  -- from page. 51
  --
  data  φ  {a ⊤ : Obj A } ( x : Hom A ⊤ a ) : {b c : Obj A } → Hom A b c → Set ( c₁  ⊔  c₂ ⊔ ℓ) where
     i   : {b c : Obj A} {k : Hom A b c } → φ x k   
     ii  : φ x {⊤} {a} x
     iii : {b c' c'' : Obj A } { f : Hom A b c' } { g : Hom A b c'' } (ψ : φ x f ) (χ : φ x g ) → φ x {b} {c'  ∧ c''} < f , g > 
     iv  : {b c d : Obj A } { f : Hom A d c } { g : Hom A b d } (ψ : φ x f ) (χ : φ x g ) → φ x ( f ∙ g )
     v   : {b c' c'' : Obj A } { f : Hom A (b ∧ c') c'' }  (ψ : φ x f )  → φ x {b} {c'' <= c'} ( f * )
     φ-cong   : {b c : Obj A} {k k' : Hom A b c } → A [ k ≈ k' ] → φ x k  → φ x k'
  
  α : {a b c : Obj A } → Hom A (( a ∧ b ) ∧ c ) ( a ∧ ( b ∧ c ) )
  α = < π  ∙ π   , < π'  ∙ π  , π'  > >
  
  -- genetate (a ∧ b) → c proof from  proof b →  c with assumption a
  -- from page. 51
  
  k : {a ⊤ b c : Obj A } → ( x∈a : Hom A ⊤ a ) → {z : Hom A b c } → ( y  : φ {a} x∈a z ) → Hom A (a ∧ b) c
  k x∈a {k} i = k ∙ π'
  k x∈a ii = π
  k x∈a (iii ψ χ ) = < k x∈a ψ  , k x∈a χ  >
  k x∈a (iv ψ χ ) = k x∈a ψ  ∙ < π , k x∈a χ  >
  k x∈a (v ψ ) = ( k x∈a ψ  ∙ α ) *
  k x∈a (φ-cong  eq ψ) = k x∈a  ψ

  toφ : {a ⊤ b c : Obj A } → ( x∈a : Hom A ⊤ a ) → (z : Hom A b c ) → φ {a} x∈a z  
  toφ {a} {⊤} {b} {c} x∈a z = i

  record Poly (a b ⊤ : Obj A )  : Set (c₁ ⊔ c₂ ⊔ ℓ)  where
    field
       x :  Hom A ⊤ a
       f :  Hom A ⊤ b
       phi  :  φ x {⊤} {b} f 

  record PHom {a ⊤ : Obj A } { x : Hom A ⊤ a } (b c : Obj A) : Set (c₁ ⊔ c₂ ⊔ ℓ)  where
    field
       hom : Hom A b c 
       phi : φ x {b} {c} hom

  open PHom

  --
  --  Proposition 6.1
  --
  --  For every polynominal ψ(x) : b → c in an indeterminate x : 1 → a over a cartesian or cartesian closed
  --  category A there is a unique arrow f : a ∧ b → c in A such that f ∙ < x ∙ ○ b , id1 A b > ≈ ψ(x).
  --

  record Functional-completeness {a : Obj A} ( x : Hom A １ a ) : Set  (c₁ ⊔ c₂ ⊔ ℓ) where
    field 
      fun  : {b c : Obj A} →  PHom {a} {１} {x} b c  → Hom A (a ∧ b) c
      fp   : {b c : Obj A} →  (p : PHom b c)  → A [  fun p ∙ <  x ∙ ○ b   , id1 A b  >  ≈ hom p ] 
      uniq : {b c : Obj A} →  (p : PHom b c)  → (f : Hom A (a ∧ b) c) → A [ f ∙ < x ∙ ○ b   , id1 A b  >  ≈ hom p ] 
         → A [ f  ≈ fun p ]

  -- f ≡ λ (x ∈ a) → φ x , ∃ (f : b <= a) →  f ∙ x ≈  φ x  
  record Fc {a b : Obj A } ( φ :  Poly a b １ ) 
         :  Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
    field
      sl :  Hom A a b 
    g :  Hom A １ (b <= a) 
    g  = (A [ A [ A [ sl o  π ] o < id1 A _ ,  ○ a > ] o π' ]  ) *
    field
      isSelect : A [  A [ ε  o < g  , Poly.x φ  > ]  ≈  Poly.f φ  ]
      isUnique : (f : Hom A １ (b <= a) )  → A [  A [ ε o < f , Poly.x φ  > ]  ≈  Poly.f φ  ]
        →  A [ g   ≈ f ]

  π-cong = IsCCC.π-cong isCCC
  *-cong = IsCCC.*-cong isCCC
  e2 = IsCCC.e2 isCCC

  -- functional completeness
  FC : {a b : Obj A}  → (φ  : Poly a b １ )  → Fc {a} {b} φ 
  FC {a} {b} φ = record {
     sl = A [ k (Poly.x φ ) (Poly.phi φ) o < id1 A _ ,  ○ a  > ] 
     ; isSelect = begin
        ε ∙ <  (( ((k (Poly.x φ) (Poly.phi φ)∙ < id1 A _ ,  ○ a > ) ∙ π ) ∙ < id1 A a , ○ a > ) ∙ π')  * ,  Poly.x φ  > ≈↑⟨ cdr (π-cong (*-cong (car assoc))  refl-hom) ⟩
        ε ∙ < (((k (Poly.x φ) (Poly.phi φ) ∙ < id1  A _ , ○ a >) ∙ (π ∙ (< id1  A _ , ○ a >))) ∙ π' ) * , Poly.x φ > ≈⟨ {!!} ⟩
        ε ∙ <  ( (k (Poly.x φ) (Poly.phi φ)∙ < id1 A _ ,  ○ a > ) ∙ (id1 A _ ∙ π' ) )  * ,  Poly.x φ  > ≈⟨ {!!} ⟩
        ε ∙ ( < ((k (Poly.x φ ) (Poly.phi φ) * ) ∙ π ) , π' >   ∙ <  Poly.x φ  ∙  ○ １  , id1 A １ > ) ≈⟨ assoc ⟩ 
        (ε ∙ < ((k (Poly.x φ ) (Poly.phi φ) * ) ∙ π ) , π' >  ) ∙ <  Poly.x φ  ∙  ○ １  , id1 A １ > ≈⟨ car ( IsCCC.e4a isCCC ) ⟩ 
        k (Poly.x φ ) (Poly.phi φ) ∙ <  Poly.x φ  ∙  ○ １  , id1 A １ >  ≈⟨ fc0 φ  ⟩
        Poly.f φ ∎
     ; isUnique = {!!} 
    }  where
        fc0 :  {b c : Obj A} (p : Poly b c １) → A [  k (Poly.x p ) (Poly.phi p) ∙ <  Poly.x p  ∙  ○ １  , id1 A １ >  ≈ Poly.f p ]
        fc0 = {!!}

  -- {-# TERMINATING #-}
  functional-completeness : {a : Obj A} ( x : Hom A １ a ) → Functional-completeness  x 
  functional-completeness {a} x = record {
         fun = λ y → k x (phi y)
       ; fp = fc0
       ; uniq = uniq
     } where 
        open φ
        fc0 :  {b c : Obj A} (p : PHom b c) → A [  k x (phi p) ∙ <  x ∙ ○ b  , id1 A b >  ≈ hom p ]
        fc0 {b} {c} p with phi p
        ... | i {_} {_} {s} = begin
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
                 ≈⟨ π-cong (fc0 record { hom = f ; phi = y } ) (fc0 record { hom = g ; phi = z } ) ⟩
             < f , g > ≈⟨⟩
             hom p ∎
        ... | iv {_} {_} {d} {f} {g} y z  = begin
             (k x y ∙ < π , k x z >) ∙ < ( x ∙ ○ b ) , id1 A b > ≈↑⟨ assoc ⟩
             k x y ∙ ( < π , k x z > ∙ < ( x ∙ ○ b ) , id1 A b > ) ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩
             k x y ∙ ( < π  ∙ < ( x ∙ ○ b ) , id1 A b > ,  k x z  ∙ < ( x ∙ ○ b ) , id1 A b > > )
                 ≈⟨ cdr (π-cong (IsCCC.e3a isCCC) (fc0 record { hom = g ; phi = z} ) ) ⟩
             k x y ∙ ( < x ∙ ○ b  ,  g > ) ≈↑⟨ cdr (π-cong (cdr (e2)) refl-hom ) ⟩
             k x y ∙ ( < x ∙ ( ○ d ∙ g ) ,  g > ) ≈⟨  cdr (π-cong assoc (sym idL)) ⟩
             k x y ∙ ( < (x ∙ ○ d) ∙ g  , id1 A d ∙ g > ) ≈↑⟨ cdr (IsCCC.distr-π isCCC) ⟩
             k x y ∙ ( < x ∙ ○ d ,  id1 A d > ∙ g ) ≈⟨ assoc ⟩
             (k x y ∙  < x ∙ ○ d ,  id1 A d > ) ∙ g  ≈⟨ car (fc0 record { hom = f ; phi = y }) ⟩
             f ∙ g  ∎
        ... | v {_} {_} {_} {f} y = begin
            ( (k x y ∙ < π ∙ π , <  π' ∙  π , π' > >) *) ∙ < x ∙ (○ b) , id1 A b > ≈⟨ IsCCC.distr-* isCCC ⟩
            ( (k x y ∙ < π ∙ π , <  π' ∙  π , π' > >) ∙ < < x ∙ ○ b , id1 A _ > ∙ π , π' > ) * ≈⟨  IsCCC.*-cong isCCC ( begin
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
              k x y ∙  < x ∙ ○ _ , id1 A _  >    ≈⟨ fc0 record { hom = f ; phi = y} ⟩
             f  ∎ )  ⟩
             f * ∎ 
        ... | φ-cong {_} {_} {f} {f'} f=f' y = trans-hom (fc0 record { hom = f ; phi = y}) f=f'
        --
        --   f ∙ <  x ∙ ○ b  , id1 A b >  ≈ hom p →  f ≈ k x (phi p)
        -- 
        uniq :  {b c : Obj A} (p : PHom b c) (f : Hom A (a ∧ b) c) →
            A [  f ∙ <  x ∙ ○ b  , id1 A b >  ≈ hom p ] → A [ f ≈ k x (phi p) ]
        uniq {b} {c} p f fx=p = sym (begin 
              k x (phi p) ≈⟨ fc1 p ⟩
              k x {hom p} i ≈⟨⟩
              hom p ∙ π'  ≈↑⟨ car fx=p ⟩
              (f ∙ <  x ∙ ○ b  , id1 A b > ) ∙ π' ≈↑⟨ assoc ⟩
              f ∙ (<  x ∙ ○ b  , id1 A b >  ∙ π') ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩
              f ∙ <  (x ∙ ○ b) ∙ π'   , id1 A b ∙ π' >   ≈⟨⟩
              f ∙ <  k x {x ∙ ○ b} i  , id1 A b ∙ π' >   ≈⟨ cdr (π-cong (sym (fc1 record { hom =  x ∙ ○ b  ; phi = iv ii i } )) refl-hom) ⟩
              f ∙ <  k x (phi record { hom = x ∙ ○ b ; phi = iv ii i })  , id1 A b ∙ π' >   ≈⟨ cdr (π-cong refl-hom idL) ⟩
              f ∙  <  π ∙ < π , (○ b ∙ π' ) >  , π' >   ≈⟨ cdr (π-cong (IsCCC.e3a isCCC)  refl-hom) ⟩
              f ∙  < π , π' >  ≈⟨ cdr (IsCCC.π-id isCCC) ⟩
              f ∙  id1 A _ ≈⟨ idR ⟩
              f ∎  ) where
          fc1 : {b c : Obj A} (p : PHom b c) → A [ k x (phi p)  ≈ k x {hom p} i ]    -- it looks like (*) in page 60
          fc1 {b} {c} p = {!!}
        

-- end
