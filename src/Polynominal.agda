{-# OPTIONS --allow-unsolved-metas #-}

open import Category
open import CCC
open import Level
open import HomReasoning 
open import cat-utility
open import Relation.Nullary
open import Data.Empty
open import Data.Product renaming ( <_,_> to ⟪_,_⟫ )

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
  --         sub k is ¬ ( k ≈ x ), we cannot write this because b≡⊤ c≡a is forced
  --
  -- this makes a few changes, but we don't care.
  -- from page. 51
  --

  open Functor
  open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
  open import Relation.Binary.PropositionalEquality hiding ( [_] ; resp ) renaming ( sym to ≡sym )

  data _H≈_ {a b c d : Obj A } ( x : Hom A a b ) (y : Hom A c d ) : Set ( c₁  ⊔  c₂ ⊔ ℓ) where
     feq : a ≡ c → b ≡ d → (z : Hom A a b) → z ≅ y → A [ x ≈ z ] → x H≈ y

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

  toφ : {a ⊤ b c : Obj A } → ( x∈a : Hom A ⊤ a ) → (z : Hom A b c ) → φ {a} x∈a z  
  toφ {a} {⊤} {b} {c} x∈a z = i z

  -- The Polynominal arrow  -- λ term in A
  --
  -- arrow in A[x], equality in A[x] should be a modulo x, that is  k x phi ≈ k x phi'
  -- the smallest equivalence relation
  --
  -- if we use equality on f as in A, Poly is ovioously Hom c b of a Category.
  -- it is better to define A[x] as an extension of A as described before

  record Poly (a c b : Obj A )  : Set (c₁ ⊔ c₂ ⊔ ℓ)  where
    field
       x :  Hom A １ a 
       f :  Hom A b c
       phi  : φ x {b} {c} f

  -- an assuption needed in k x phi ≈ k x phi'
  --   k x (i x) ≈ k x ii  
  postulate 
       xf :  {a b c : Obj A } → ( x : Hom A １ a ) → {f : Hom A b c } → ( fp  : φ {a} x f ) →  A [ k x (i f) ≈ k x fp ]
       -- ( x ∙ π' ) ≈ π 
  --   
  --   this is justified equality f ≈ g in A[x] is used in f ∙ < x , id1 A _> ≈  f ∙ < x , id1 A _>
  --   ( x ∙ π' ) ∙ < x , id1 A _ > ≈ π ∙ < x , id1 A _ >


  --
  -- Subcategory of A without x
  --
  -- Since A is CCC, ∀ f : Hom A b c ,  φ x {b} {c} (FMap F f) is an arrow of CCC A.
  --

  --
  -- If no x in SA (Subcategory of CCC A), we may have xf.
  --
  record SA  {a ⊤ : Obj A } ( x : Hom A ⊤ a ) : Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ) where
     field
       F : Functor A A
       CF : CCCFunctor A A C C F
       FObj-iso : (x : Obj A) → FObj F x ≡ x
       without-x : {b c : Obj A} → (f : Hom A b c) → ¬ ( FMap F f H≈ x  )

  xf-in-SA : {a ⊤ : Obj A } ( x : Hom A ⊤ a ) → (sa : SA x) → 
       {b c : Obj A } → {f : Hom A b c } → ( fp  : φ {a} x (FMap (SA.F sa) f) ) →  Set ℓ
  xf-in-SA {a} {⊤} x sa {b} {c} {f} fp = A [ k x (i (FMap (SA.F sa) f)) ≈ k x fp ]

  -- since we have A[x] now, we can proceed the proof on p.64 in some possible future

  --
  --  Proposition 6.1
  --
  --  For every polynominal ψ(x) : b → c in an indeterminate x : 1 → a over a cartesian or cartesian closed
  --  category A there is a unique arrow f : a ∧ b → c in A such that f ∙ < x ∙ ○ b , id1 A b > ≈ ψ(x).

  record Functional-completeness {a b c : Obj A} ( p : Poly a c b ) : Set  (c₁ ⊔ c₂ ⊔ ℓ) where
    x = Poly.x p
    field 
      fun  : Hom A (a ∧ b) c
      fp   : A [  fun ∙ <  x ∙ ○ b   , id1 A b  >  ≈ Poly.f p  ]
      uniq : ( f : Hom A (a ∧ b) c) → A [ f ∙ < x ∙ ○ b , id1 A b > ≈ Poly.f p ] 
         → A [ f ≈ fun  ]

  -- ε form
  -- f ≡ λ (x ∈ a) → φ x , ∃ (f : b <= a) →  f ∙ x ≈  φ x  
  record Fc {a b : Obj A } ( φ :  Poly a b １ ) 
         :  Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
    field
      sl :  Hom A a b 
    g :  Hom A １ (b <= a) 
    g  = ( sl ∙ π'  ) *
    field
      isSelect : A [   ε ∙ < g  , Poly.x φ  >   ≈  Poly.f φ  ]
      isUnique : (f : Hom A １ (b <= a) )  → A [   ε ∙ < f , Poly.x φ  >   ≈  Poly.f φ  ]
        →  A [ g ≈ f ]

  -- we should open IsCCC isCCC
  π-cong = IsCCC.π-cong isCCC
  *-cong = IsCCC.*-cong isCCC
  distr-* = IsCCC.distr-* isCCC
  e2 = IsCCC.e2 isCCC

  -- f  ≈ g → k x {f} _ ≡  k x {g} _   Lambek p.60
  --   if A is locally small, it is ≡-cong.
  --   case i i is π ∙ f ≈ π ∙ g
  --   we have (x y :  Hom A １ a) → x ≈ y (minimul equivalende assumption) in record Poly. this makes all k x ii case valid
  --   all other cases, arguments are reduced to f ∙ π' .

  ki : {a b c : Obj A} → (x : Hom A １ a) → (f : Hom A b c ) → (fp  :  φ x {b} {c} f )
     →  A [ k x (i f) ≈ k x fp ]
  ki x f (i _) = refl-hom
  ki {a} x .x ii = xf x ii -- we may think this is not happen in A or this is the nature of equality in A[x]
  ki x _ (iii {_} {_} {_} {f₁}{ f₂} fp₁ fp₂ ) = begin
               < f₁ ,  f₂  > ∙ π'  ≈⟨ IsCCC.distr-π isCCC ⟩
               < f₁ ∙ π'  ,  f₂   ∙ π' >  ≈⟨ π-cong (ki x f₁ fp₁  ) (ki x f₂ fp₂  ) ⟩
                k x (iii  fp₁ fp₂ )  ∎ 
  ki x _ (iv {_} {_} {_} {f₁} {f₂} fp fp₁) = begin
               (f₁ ∙ f₂  ) ∙ π'  ≈↑⟨ assoc ⟩
               f₁  ∙ ( f₂ ∙ π')  ≈↑⟨ cdr (IsCCC.e3b isCCC) ⟩
               f₁  ∙ ( π'  ∙ < π , (f₂ ∙ π' )  >)  ≈⟨ assoc ⟩
               (f₁  ∙ π' ) ∙ < π , (f₂ ∙ π' )  >  ≈⟨ resp (π-cong refl-hom (ki x _ fp₁  )) (ki x _ fp  ) ⟩
               k x fp ∙ < π , k x fp₁ >  ≈⟨⟩
               k x (iv fp fp₁ )  ∎  
  ki x _ (v {_} {_} {_} {f} fp) = begin
               (f *) ∙ π' ≈⟨ distr-*  ⟩
               ( f ∙ < π' ∙ π , π'  > ) * ≈↑⟨ *-cong (cdr (IsCCC.e3b isCCC)) ⟩
               ( f ∙ ( π'  ∙  < π ∙ π , < π' ∙  π , π' > > ) ) *  ≈⟨ *-cong assoc  ⟩
               ( (f ∙ π')  ∙  < π ∙ π , < π' ∙  π , π' > > ) *  ≈⟨ *-cong ( car ( ki x _ fp )) ⟩
               ( k x fp ∙  < π ∙ π , < π' ∙  π , π' > > ) *  ≈⟨⟩
               k x (v fp )  ∎  

  k-cong : {a b c : Obj A}  → (f g :  Poly a c b )
        → A [ Poly.f f ≈ Poly.f g ] → A [ k (Poly.x f) (Poly.phi f)   ≈ k (Poly.x g) (Poly.phi g) ]
  k-cong {a} {b} {c} f g f=f = begin
          k (Poly.x f) (Poly.phi f) ≈↑⟨ ki  (Poly.x f) (Poly.f f)  (Poly.phi f)  ⟩
          Poly.f f ∙ π' ≈⟨ car f=f  ⟩
          Poly.f g ∙ π'  ≈⟨ ki  (Poly.x g) (Poly.f g)  (Poly.phi g) ⟩
          k (Poly.x g) (Poly.phi g) ∎   

  -- proof in p.59 Lambek
  --
  --  (ψ : Poly a c b) is basically λ x.ψ(x). To use x from outside as a ψ(x), apply x ψ will work.
  --  Instead of replacing x in Poly.phi ψ, we can use simple application with this fuctional completeness
  --  in the internal language of Topos.
  --  
  functional-completeness : {a b c : Obj A} ( p : Poly a c b ) → Functional-completeness p 
  functional-completeness {a} {b} {c} p = record {
         fun = k (Poly.x p) (Poly.phi p)
       ; fp = fc0 (Poly.x p) (Poly.f p) (Poly.phi p)
       ; uniq = λ f eq  → uniq (Poly.x p) (Poly.f p) (Poly.phi p)  f eq
     } where 
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
              k x y ∙  < x ∙ ○ _ , id1 A _  >    ≈⟨ fc0 x f y  ⟩
             f  ∎ )  ⟩
             f * ∎  
        --
        --   f ∙ <  x ∙ ○ b  , id1 A b >  ≈ f →  f ≈ k x (phi p)
        -- 
        uniq : {a b c : Obj A}  → (x :  Hom A １ a) (f :  Hom A b c) (phi  :  φ x {b} {c} f ) (f' : Hom A (a ∧ b) c)
            → A [  f' ∙ <  x ∙ ○ b  , id1 A b >  ≈ f ] → A [ f' ≈ k x phi ]
        uniq {a} {b} {c} x f phi f' fx=p  = sym (begin
               k x phi ≈↑⟨ ki x f phi ⟩
               k x {f} (i _) ≈↑⟨ car fx=p ⟩
               k x {f' ∙ < x ∙ ○ b , id1 A b >} (i _)  ≈⟨ trans-hom (sym assoc)  (cdr (IsCCC.distr-π isCCC) ) ⟩ -- ( f' ∙ < x ∙ ○ b , id1 A b> ) ∙ π'
               f' ∙ k x {< x ∙ ○ b , id1 A b >} (iii (i _)  (i _)  ) ≈⟨⟩                         -- ( f' ∙ < (x ∙ ○ b) ∙ π'  , id1 A b ∙ π' > ) 
               f' ∙ <  k x (i (x ∙ ○ b)) ,  k x {id1 A b} (i _) >  ≈⟨ cdr (π-cong u2 refl-hom) ⟩ -- ( f' ∙ < (x ∙ ○ b) ∙ π' , id1 A b ∙ π' > ) 
               f' ∙ < k x {x} ii ∙ < π , k x {○ b} (i _)  >  , k x {id1 A b} (i _)  >   -- ( f' ∙ < π ∙ < π , (x ∙ ○ b) ∙ π' >  , id1 A b ∙ π' > ) 
                   ≈⟨ cdr (π-cong (cdr (π-cong refl-hom (car e2))) idL ) ⟩ 
               f' ∙  <  π ∙ < π , (○ b ∙ π' ) >  , π' >   ≈⟨ cdr (π-cong (IsCCC.e3a isCCC)  refl-hom) ⟩
               f' ∙  < π , π' >  ≈⟨ cdr (IsCCC.π-id isCCC) ⟩
               f' ∙  id1 A _ ≈⟨ idR ⟩
               f' ∎  )  where
                   -- x ∙ ○ b is clearly Polynominal or assumption xf
                   u2 : k x {x ∙ ○ b} (i _) ≈ k x {x} ii ∙ < π , k x {○ b} (i _) >  --  (x ∙ (○ b)) ∙ π' ≈ π ∙ < π , (○ b) ∙ π' >
                   u2 = ki x (x ∙ ○ b) (iv ii (i _)) 

  -- functional completeness ε form
  --
  --  g : Hom A １ (b <= a)       fun : Hom A (a ∧ １) c
  --       fun *                       ε ∙ < g ∙ π , π' >
  --  a -> d <= b  <-> (a ∧ b ) -> d
  --            
  --   fun ∙ <  x ∙ ○ b   , id1 A b  >  ≈ Poly.f p
  --   (ε ∙ < g ∙ π , π' >) ∙ <  x ∙ ○ b   , id1 A b  >  ≈ Poly.f p
  --      could be simpler
  FC : {a b : Obj A}  → (φ  : Poly a b １ )  → Fc {a} {b} φ 
  FC {a} {b} φ = record {
     sl =  k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  > 
     ; isSelect = isSelect
     ; isUnique = uniq 
    }  where
        π-exchg = IsCCC.π-exchg isCCC
        fc0 :  {b c : Obj A} (p : Poly b c １) → A [  k (Poly.x p ) (Poly.phi p) ∙ <  Poly.x p  ∙  ○ １  , id1 A １ >  ≈ Poly.f p ]
        fc0 p =  Functional-completeness.fp (functional-completeness p)
        gg : A [ (  k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ Poly.x φ ≈ Poly.f φ ]
        gg  = begin
          ( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ Poly.x φ   ≈⟨ trans-hom (sym assoc) (cdr (IsCCC.distr-π isCCC ) ) ⟩
          k (Poly.x φ ) (Poly.phi φ) ∙ <  id1 A _ ∙  Poly.x φ  ,  ○ a ∙ Poly.x φ >  ≈⟨ cdr (π-cong idL e2 ) ⟩
          k (Poly.x φ ) (Poly.phi φ) ∙ <   Poly.x φ  ,  ○ １ >  ≈⟨ cdr (π-cong (trans-hom (sym idR) (cdr e2) )  (sym e2) ) ⟩
          k (Poly.x φ ) (Poly.phi φ) ∙ <  Poly.x φ  ∙  ○ １  , id1 A １ >  ≈⟨ fc0 φ  ⟩
          Poly.f φ ∎
        isSelect :  A [ ε ∙ < ( ( k (Poly.x φ ) (  Poly.phi φ) ∙ < id1 A _ , ○ a > ) ∙ π' ) * , Poly.x φ >  ≈ Poly.f φ ]
        isSelect =      begin
          ε ∙ <  ((k (Poly.x φ) (Poly.phi φ)∙ < id1 A _ ,  ○ a > ) ∙ π')  * ,  Poly.x φ  > ≈↑⟨ cdr (π-cong idR refl-hom ) ⟩
          ε ∙ (< ((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙   id1 A _   ,  Poly.x φ > )  ≈⟨ cdr (π-cong (cdr e2) refl-hom ) ⟩
          ε ∙ (< ((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙   ○ １ ,  Poly.x φ > )  ≈↑⟨ cdr (π-cong (cdr e2) refl-hom ) ⟩
          ε ∙ (< ((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙   (○ a  ∙ Poly.x φ)  ,  Poly.x φ > )  ≈↑⟨ cdr (π-cong (sym assoc) idL ) ⟩
          ε ∙ (< (((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙   ○ a ) ∙ Poly.x φ  ,  id1 A _ ∙ Poly.x φ > )
              ≈↑⟨ cdr (IsCCC.distr-π isCCC)  ⟩
          ε ∙ ((< (((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙   ○ a ) ,  id1 A _ > )  ∙ Poly.x φ )
              ≈↑⟨ cdr (car (π-cong (cdr (IsCCC.e3a isCCC) ) refl-hom))  ⟩
          ε ∙ ((< (((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙  (π  ∙ <  ○ a , id1 A _ > )) ,  id1 A _ > )  ∙ Poly.x φ )
              ≈⟨ cdr (car (π-cong assoc (sym (IsCCC.e3b isCCC)) )) ⟩
          ε ∙ ((< ((((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙  π ) ∙ <  ○ a , id1 A _ > ) , (π' ∙  <  ○ a , id1 A _ > ) > )  ∙ Poly.x φ )
              ≈↑⟨ cdr (car (IsCCC.distr-π isCCC)) ⟩
            ε ∙ ((< ((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙  π , π' >  ∙ <  ○ a , id1 A _ > )  ∙ Poly.x φ )  ≈⟨ assoc ⟩
            (ε ∙ (< ((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙  π , π' >  ∙ <  ○ a , id1 A _ > ) ) ∙ Poly.x φ   ≈⟨ car assoc ⟩
          ((ε ∙ < ((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) * )  ∙  π , π' > ) ∙ <  ○ a , id1 A _ >  ) ∙ Poly.x φ
              ≈⟨ car (car (IsCCC.e4a isCCC))  ⟩
          ((( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  >)  ∙ π' ) ∙ <  ○ a , id1 A _ >  ) ∙ Poly.x φ   ≈↑⟨ car assoc ⟩
          (( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ (π' ∙ <  ○ a , id1 A _ > ) ) ∙ Poly.x φ   ≈⟨ car (cdr (IsCCC.e3b isCCC)) ⟩
          (( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ id1 A _ ) ∙ Poly.x φ   ≈⟨ car idR ⟩
          ( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ Poly.x φ   ≈⟨ gg  ⟩
          Poly.f φ ∎
        uniq  :  (f : Hom A １ (b <= a)) → A [  ε ∙ < f , Poly.x φ >  ≈ Poly.f φ ] →
            A [ (( k (Poly.x φ) (Poly.phi φ) ∙  < id1 A _  , ○ a > )∙ π' ) * ≈ f ]
        uniq f eq = begin
           (( k (Poly.x φ ) (Poly.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ π' ) *   ≈⟨ IsCCC.*-cong isCCC ( begin
              (k (Poly.x φ) (Poly.phi φ) ∙ < id1 A _ , ○ a >) ∙ π' ≈↑⟨ assoc ⟩
              k (Poly.x φ) (Poly.phi φ) ∙ (< id1 A _ , ○ a > ∙ π') ≈⟨ car ( sym (Functional-completeness.uniq (functional-completeness φ) _ ( begin
                ((ε ∙ < f ∙ π , π' >) ∙ < π' , π >) ∙ < Poly.x φ ∙ ○ １ , id1 A １ > ≈↑⟨ assoc ⟩
                (ε ∙ < f ∙ π , π' >) ∙ ( < π' , π > ∙ < Poly.x φ ∙ ○ １ , id1 A １ > ) ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩
                (ε ∙ < f ∙ π , π' >) ∙  < π' ∙ < Poly.x φ ∙ ○ １ , id1 A １ > , π ∙  < Poly.x φ ∙ ○ １ , id1 A １ > >
                     ≈⟨ cdr (π-cong (IsCCC.e3b isCCC) (IsCCC.e3a isCCC)) ⟩
                (ε ∙ < f ∙ π , π' >) ∙  < id1 A １  ,  Poly.x φ ∙ ○ １ > ≈↑⟨ assoc ⟩
                ε ∙ ( < f ∙ π , π' > ∙  < id1 A １  ,  Poly.x φ ∙ ○ １ > ) ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩
                ε ∙ ( < (f ∙ π ) ∙  < id1 A １  ,  Poly.x φ ∙ ○ １ > , π'  ∙  < id1 A １  ,  Poly.x φ ∙ ○ １ > > ) ≈⟨ cdr (π-cong (sym assoc) (IsCCC.e3b isCCC)) ⟩
                ε ∙ ( < f ∙ (π  ∙  < id1 A １  ,  Poly.x φ ∙ ○ １ > ) ,  Poly.x φ ∙ ○ １  > ) ≈⟨ cdr (π-cong (cdr (IsCCC.e3a isCCC)) (cdr (trans-hom e2 (sym e2)))) ⟩
                ε ∙ ( < f ∙ id1 A １ ,  Poly.x φ ∙ id1 A １  > ) ≈⟨ cdr (π-cong idR idR ) ⟩
                 ε ∙ < f , Poly.x φ > ≈⟨ eq ⟩
                Poly.f φ ∎ ))) ⟩
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



-- end
