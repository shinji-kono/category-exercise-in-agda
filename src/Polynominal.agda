{-# OPTIONS --cubical-compatible --allow-unsolved-metas  #-}
-- {-# OPTIONS --cubical-compatible --safe --warning=noUnsupportedIndexedMatch #-}


open import Category
open import CCC
open import Level
open import HomReasoning
open import Definitions
open import Relation.Nullary
open import Data.Empty
open import Data.Product renaming ( <_,_> to ⟪_,_⟫ )

module Polynominal { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) ( C : CCC A )   where

  open CCC.CCC C
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

  toφ : {a ⊤ b c : Obj A } → ( x∈a : Hom A ⊤ a ) → (z : Hom A b c ) → φ {a} x∈a z
  toφ {a} {⊤} {b} {c} x∈a z = i z

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
       xf :  A [ k x (i f) ≈ k x phi ]

  pid : {a : Obj A} (x : Hom A １ a) → (c : Obj A)  → Polym x c c
  pid {a} x c = record { f = id1 A c ; phi = i (id1 A c) ; xf = ≈-Reasoning.refl-hom A }

  pf : {a : Obj A} (x : Hom A １ a) → {b c : Obj A}  → (f : Hom A b c)  → Polym x b c
  pf {a} x f = record { f = f ; phi = i f ; xf = ≈-Reasoning.refl-hom A }

  pcomp : {a : Obj A} (x : Hom A １ a) { b c d : Obj A } ( f : Polym x c d ) → (g : Polym x b c) → Polym x b d
  pcomp {a} x {b} {c} {d} f g = record { f = Polym.f f ∙ Polym.f g  ; phi = iv (i (Polym.f f)) (i (Polym.f g))
     ; xf = lemma }  where
        lemma : A [ (Polym.f f ∙ Polym.f g) ∙ π' ≈ (Polym.f f ∙ π') ∙ < π , Polym.f g ∙ π' > ]
        lemma = begin
           (Polym.f f ∙ Polym.f g) ∙ π' ≈↑⟨ assoc ⟩
           Polym.f f ∙ (Polym.f g ∙ π' ) ≈↑⟨ cdr ( IsCCC.e3b isCCC ) ⟩
           Polym.f f ∙ (π' ∙ < π , Polym.f g ∙ π' >) ≈⟨ assoc ⟩
           (Polym.f f ∙ π') ∙ < π , Polym.f g ∙ π' >  ∎ where
             open ≈-Reasoning A


  data P≈ {a : Obj A} (x : Hom A １ a) : { b c : Obj A } ( f g : Polym x b c ) → Set ( c₁  ⊔  c₂ ⊔ ℓ) where
     p-refl : { b c  : Obj A}  {f g : Polym x b c } → A [ Polym.f f ≈ Polym.f g ]  → P≈ x f g
     p-sym : { b c  : Obj A}  {f g : Polym x b c } → P≈ x f g → P≈ x g f
     p-trans : { b c : Obj A} {χ ψ φ  : Polym x b c} → P≈ x χ ψ → P≈ x ψ φ → P≈ x χ φ
     p-comp : { b c d : Obj A} {g : Polym x c d } {f : Polym x b c } {h : Polym x b d}
        → A [ Polym.f g ∙ Polym.f f ≈ Polym.f h ] → P≈ x (pcomp x g f) h
     p-resp : { b c d : Obj A} {ψ  ψ' : Polym x c d } {χ χ' : Polym x b c}
        → P≈ x χ χ' → P≈ x ψ ψ'
        → P≈ x (pcomp x ψ χ) (pcomp x ψ' χ')
     p-idr : { c d : Obj A} {ψ  : Polym x c d } → P≈ x  (pcomp x ψ (pid x _)) ψ
     p-idl : { c d : Obj A} {ψ  : Polym x c d } → P≈ x  (pcomp x (pid x _) ψ) ψ
     p-assoc : { b c d e : Obj A} (χ  : Polym x d e) (ψ  : Polym x c d ) (φ  : Polym x b c )
         → P≈ x (pcomp x χ (pcomp x ψ φ ) ) (pcomp x (pcomp x χ ψ) φ )
     p-<> : { c d e : Obj A} {f : Polym x c d } {g : Polym x c e} {h : Polym x c (d ∧ e)} →
         A [ < Polym.f f , Polym.f g > ≈ Polym.f h ] → P≈ x (pf x ( < Polym.f f , Polym.f g > )) h
     p-π-cong : { a b c  : Obj A} {f f' : Polym x a b } {g g' : Polym x a c}
         → P≈ x f f' → P≈ x g g'
         → P≈ x (pf x ( < Polym.f f , Polym.f g > )) (pf x ( < Polym.f f' , Polym.f g' > ))
     p-*-cong : { a b c : Obj A} {f g : Polym x (a ∧ c) b }
         → P≈ x f g
         → P≈ x (pf x ( Polym.f f * )) (pf x ( Polym.f g * ))

  PolyC : {a : Obj A} (x : Hom A １ a) → Category c₁ (c₁ ⊔ c₂ ⊔ ℓ) (c₁ ⊔ c₂ ⊔ ℓ)
  PolyC {a} x = record {
     Obj  = Obj A ;
     Hom = λ b c →  Polym x b c ;
     _o_ =  λ {b} {c} {d} f g → pcomp x f g ;
     _≈_ =  λ f g → P≈ x f g ;
     Id  =  λ{b} → pid x b ;
     isCategory  = record {
        isEquivalence =  record {refl = p-refl refl-hom  ; trans = p-trans ; sym = p-sym  } ;
        identityL  = p-idl ;
        identityR  = p-idr ;
        o-resp-≈  = p-resp  ;
        associative  = λ {b c d e f g h} → p-assoc f g h
     }
   }  where
      open ≈-Reasoning A

  PolyCCC : {a : Obj A} (x : Hom A １ a) → CCC (PolyC x)
  PolyCCC {a} x = record {
     １ = １ ;
     ○ = λ b → pf x (○ b)  ;
     _∧_ = _∧_ ;
     <_,_> = λ f g → pf x ( < Polym.f f , Polym.f g > ) ;
     π = pf x π ;
     π' = pf x π' ;
     _<=_ = _<=_ ;
     _* = λ f → pf x ( (Polym.f f) *  ) ;
     ε = pf x ε ;
     isCCC  = record {
       e2 = p-refl (IsCCC.e2 isCCC ) ;
       e3a = λ {a} {b} {c} {f} {g} → e3a {a} {b} {c} {f} {g};
       e3b = λ {a} {b} {c} {f} {g} → e3b {a} {b} {c} {f} {g};
       e3c = λ {a} {b} {c} {h} → e3c {a} {b} {c} {h};
       π-cong = π-cong ;
       -- closed
       e4a = e4a ;
       e4b = e4b ;
       *-cong = *-cong
      }
    } where
       e3a : {a1 : Obj (PolyC x)} {b c : Obj (PolyC x)} {f : Hom (PolyC x) c a1} {g : Hom (PolyC x) c b}
           → PolyC x [ PolyC x [ pf x π o pf x < Polym.f f , Polym.f g > ] ≈ f ]
       e3a {a1} {b} {c} {f} {g} = p-comp {a} {x} {c} {a1 ∧ b} {a1} {pf x _} {pf x _} (IsCCC.e3a isCCC {a1} {b} {c} {Polym.f f} {Polym.f g})
       e3b : {a₁ : Obj (PolyC x)} {b c : Obj (PolyC x)} {f : Hom (PolyC x) c a₁} {g : Hom (PolyC x) c b} →
            PolyC x [ PolyC x [ pf x π' o pf x < Polym.f f , Polym.f g > ] ≈ g ]
       e3b {a1} {b} {c} {f} {g} = p-comp {a} {x} {c} {a1 ∧ b} {b} {pf x _} {pf x _} (IsCCC.e3b isCCC {a1} {b} {c} {Polym.f f} {Polym.f g})
       e3c :  {a₁ : Obj (PolyC x)} {b c : Obj (PolyC x)} {h : Hom (PolyC x) c (a₁ ∧ b)} →
            PolyC x [ pf x < Polym.f (PolyC x [ pf x π o h ]) , Polym.f (PolyC x [ pf x π' o h ]) > ≈ h ]
       e3c {a1} {b} {c} {h} = p-<> {_} {_} {c} {_} {_} {pf x (A [ π o Polym.f h ])} {pf x (A [ π' o Polym.f h ])} (IsCCC.e3c isCCC {a1} {b} {c} {Polym.f h})
       π-cong : {a₁ : Obj (PolyC x)} {b c : Obj (PolyC x)}
            {f f' : Hom (PolyC x) c a₁} {g g' : Hom (PolyC x) c b} →
            PolyC x [ f ≈ f' ] → PolyC x [ g ≈ g' ] → PolyC x [ pf x < Polym.f f , Polym.f g > ≈ pf x < Polym.f f' , Polym.f g' > ]
       π-cong {a₁} {b} {c} {f} {f'} {g} {g'} f=f' g=g' = p-π-cong f=f' g=g'
       e4a : {a₁ : Obj (PolyC x)} {b c : Obj (PolyC x)} {h : Hom (PolyC x) (c ∧ b) a₁} →
            PolyC x [ PolyC x [ pf x ε o pf x < Polym.f (PolyC x [ pf x (Polym.f h *) o pf x π ]) , π' > ] ≈ h ]
       e4a {a1} {b} {c} {h} = p-comp {_} {_} {_} {_} {_} {pf x ε } {pf x _} {_} (IsCCC.e4a isCCC {_} {_} {_} {_})
       e4b :  {a₁ : Obj (PolyC x)} {b c : Obj (PolyC x)} {k₁ : Hom (PolyC x) c (a₁ <= b)} →
            PolyC x [ pf x (Polym.f (PolyC x [ pf x ε o pf x < Polym.f (PolyC x [ k₁ o pf x π ]) , π' > ]) *) ≈ k₁ ]
       e4b {a1} {b} {c} {k1} = p-refl (IsCCC.e4b isCCC {a1} {b} )
       *-cong : {a₁ : Obj (PolyC x)} {b c : Obj (PolyC x)} {f f' : Hom (PolyC x) (a₁ ∧ b) c} → PolyC x [ f ≈ f' ] →
            PolyC x [ pf x (Polym.f f *) ≈ pf x (Polym.f f' *) ]
       *-cong eq = p-*-cong eq



  -- an assuption needed in k x phi ≈ k x phi'
  --   k x (i x) ≈ k x ii
  -- xf :  {a b c : Obj A } → ( x : Hom A １ a ) → {f : Hom A b c } → ( fp  : φ {a} x f ) →  A [ k x (i f) ≈ k x fp ]
  -- xf x fp = ?
       -- ( x ∙ π' ) ≈ π
  --
  --   this is justified equality f ≈ g in A[x] is used in f ∙ < x , id1 A _> ≈  f ∙ < x , id1 A _>
  --   ( x ∙ π' ) ∙ < x , id1 A _ > ≈ π ∙ < x , id1 A _ >


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
      uniq : ( f : Hom A (a ∧ b) c) → A [ f ∙ < x ∙ ○ b , id1 A b > ≈ Polym.f p ]
         → A [ f ≈ fun  ]

  record P-Functional-completeness {a : Obj A} (x : Hom A １ a) {b c : Obj A} ( p : Polym x b c ) : Set  (c₁ ⊔ c₂ ⊔ ℓ) where
    field
      fun  : Hom A (a ∧ b) c
      fp   : P≈ x (pf x ( fun ∙ <  x ∙ ○ b   , id1 A b  >))  p
      uniq : ( f : Hom A (a ∧ b) c) → P≈ x (pf x ( f ∙ < x ∙ ○ b , id1 A b >)) p
         → A [ f ≈ fun  ]

  -- ε form
  -- f ≡ λ (x ∈ a) → φ x , ∃ (f : b <= a) →  f ∙ x ≈  φ x
  record Fc {a b : Obj A } (x : Hom A １ a) ( φ :  Polym x １ b )
         :  Set ( suc c₁  ⊔  suc c₂ ⊔ suc ℓ ) where
    field
      sl :  Hom A a b
    g :  Hom A １ (b <= a)
    g  = ( sl ∙ π'  ) *
    field
      isSelect : A [   ε ∙ < g  , x >   ≈  Polym.f φ  ]
      isUnique : (f : Hom A １ (b <= a) )  → A [   ε ∙ < f , x  >   ≈  Polym.f φ  ]
        →  A [ g ≈ f ]

  -- we should open IsCCC isCCC
  π-cong = IsCCC.π-cong isCCC
  *-cong = IsCCC.*-cong isCCC
  distr-* = IsCCC.distr-* isCCC
  e2 = IsCCC.e2 isCCC

  -- f  ≈ g → k x {f} _ ≡  k x {g} _   Lambek p.60
  --   if A is locally small, it is ≡-cong.
  --   case i i is π ∙ f ≈ π ∙ g
  --   we have (x y :  Hom A １ a) → x ≈ y (minimul equivalende assumption) in record Polym. this makes all k x ii case valid
  --   all other cases, arguments are reduced to f ∙ π' .

  ki : {a b c : Obj A} → (x : Hom A １ a) → (f : Hom A b c ) → (fp  :  φ x {b} {c} f )
     →  A [ k x (i f) ≈ k x fp ]
  ki x f (i _) = refl-hom where
      open ≈-Reasoning A
  ki {a} x .x ii = ? -- xf x ii -- we may think this is not happen in A or this is the nature of equality in A[x]
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

  k-cong : {a b c : Obj A}  (x : Hom A １ a ) → (f g :  Polym x c b )
        → A [ Polym.f f ≈ Polym.f g ] → A [ k x (Polym.phi f)   ≈ k x (Polym.phi g) ]
  k-cong {a} {b} {c} x f g f=f = begin
          k x (Polym.phi f) ≈↑⟨ Polym.xf f  ⟩
          Polym.f f ∙ π' ≈⟨ car f=f  ⟩
          Polym.f g ∙ π'  ≈⟨ Polym.xf g ⟩
          k x (Polym.phi g) ∎ where
      open ≈-Reasoning A

  P≈→eq  : {a b c : Obj A} → (x : Hom A １ a ) → {ψ φ : Polym x b c } → ( eq : P≈ x ψ φ ) → A [ Polym.f ψ ≈ Polym.f φ ]
  P≈→eq  x eq = kc03 x eq where
      open ≈-Reasoning A
      kc03 : {a b c : Obj A} →(x : Hom A １ a ) → {ψ φ : Polym x b c } → ( eq : P≈ x ψ φ ) → A [ Polym.f ψ ≈ Polym.f φ ]
      kc03 x (p-refl eq) = eq
      kc03 x (p-sym {_} {_} {f1} {g1} eq) = sym (kc03 x {f1} {g1} eq)
      kc03 x (p-trans eq eq₁) = trans-hom (kc03 x eq) (kc03 x eq₁)
      kc03 x (p-comp {h} eq) = eq
      kc03 x (p-resp eq eq₁) = resp (kc03 x eq) (kc03 x eq₁)
      kc03 x p-idr  = idR
      kc03 x p-idl = idL
      kc03 x (p-assoc χ ψ φ₁) = assoc
      kc03 x (p-<> eq) = eq
      kc03 x (p-π-cong eq eq₁) = π-cong (kc03 x eq) (kc03 x eq₁)
      kc03 x (p-*-cong eq) = *-cong (kc03 x eq)

  k-cong-p : {a b c : Obj A}  →  (x : Hom A １ a)  →   (f g :  Polym x b c )
        → P≈ x f g  → A [ k x (Polym.phi f)   ≈ k x (Polym.phi g) ]
  k-cong-p x ψ φ eq = kc02 eq where
     open ≈-Reasoning A
     kc02 : ( eq : P≈ x ψ φ ) → A [ k x (Polym.phi ψ) ≈ k x (Polym.phi φ)]
     kc02 eq = begin
          k x (Polym.phi ψ) ≈↑⟨ Polym.xf ψ  ⟩
          Polym.f ψ ∙ π' ≈⟨ car (P≈→eq x {ψ} {φ} eq)  ⟩
          Polym.f φ ∙ π'  ≈⟨ Polym.xf φ ⟩
          k x (Polym.phi φ) ∎

  -- proof in p.59 Lambek
  --
  --  (ψ : Poly a c b) is basically λ x.ψ(x). To use x from outside as a ψ(x), apply x ψ will work.
  --  Instead of replacing x in Polym.phi ψ, we can use simple application with this fuctional completeness
  --  in the internal language of Topos.
  --

  p-functional-completeness : {a : Obj A} (x : Hom A １ a) { b c : Obj A} ( p : Polym x b c ) → P-Functional-completeness x p
  p-functional-completeness {a} x {b} {c} p = record {
         fun = k x (Polym.phi p)
       ; fp = fc0 p
       ; uniq = uniq p
     } where
        fc0 : {b c : Obj A} → (p : Polym x b c ) → P≈ x (pf x (k x (Polym.phi p) ∙ < x ∙ ○ b , id1 A b >)) p
        fc0 {b} {c} p with Polym.phi p
        ... | i s = p-refl ( begin
             (s ∙ π') ∙ < ( x ∙ ○ b ) , id1 A b > ≈↑⟨ assoc ⟩
             s ∙ (π' ∙ < ( x ∙ ○ b ) , id1 A b >) ≈⟨ cdr (IsCCC.e3b isCCC ) ⟩
             s ∙ id1 A b ≈⟨ idR ⟩
             s ∎ ) where
           open ≈-Reasoning A
        ... | ii = p-refl ( begin
             π ∙ < ( x ∙ ○ b ) , id1 A b > ≈⟨ IsCCC.e3a isCCC ⟩
             x ∙ ○ b  ≈↑⟨ cdr (e2 ) ⟩
             x ∙ id1 A b  ≈⟨ idR ⟩
             x ∎ ) where
           open ≈-Reasoning A
        ... | iii {_} {_} {_} {f} {g} y z  = begin
             pf x (A [ < k x y  , k x z > o < A [ x o (○ b) ] , id1 A b > ]) ≈⟨ p-refl ( IsCCC.distr-π isCCC) ⟩
             pf x < A  [ k x y  o  < ( A [ x o (○ b) ] ) , id1 A _ >  ] , A [ k x z o < A [ x o (○ b) ] , id1 A _ > ]  >
                ≈⟨ p-π-cong (fc0 record { f = f ; phi = y ; xf = ? }) (fc0 record { f = g ; phi = z ; xf = ? })  ⟩
             pf x < f , g > ≈⟨ p-refl (π-cong (≈-Reasoning.refl-hom A) (≈-Reasoning.refl-hom A) )  ⟩
             p   ∎ where
                fc01 : A [ < f , g > ∙ π' ≈ k x (iii y z) ]
                fc01 = ?
                fc02 : A [ A [ < k x y  , k x z > o < A [ x o (○ b) ] , id1 A b > ] ≈ Polym.f p ]
                fc02 = begin
                    < k x y , k x z > ∙ < (x ∙ ○ b ) , id1 A b > ≈⟨ IsCCC.distr-π isCCC  ⟩
                    < k x y ∙ < (x ∙ ○ b ) , id1 A b > , k x z ∙ < (x ∙ ○ b ) , id1 A b > >
                    ≈⟨ π-cong ? ? ⟩
                    < f , g > ≈⟨⟩
                    Polym.f p  ∎ where
                       open ≈-Reasoning A
                open ≈-Reasoning (PolyC x)
        ... | iv {_} {_} {d} {f} {g} y z  = p-refl ( begin
             (k x y ∙ < π , k x z >) ∙ < ( x ∙ ○ b ) , id1 A b > ≈↑⟨ assoc ⟩
             k x y ∙ ( < π , k x z > ∙ < ( x ∙ ○ b ) , id1 A b > ) ≈⟨ cdr (IsCCC.distr-π isCCC) ⟩
             k x y ∙ ( < π  ∙ < ( x ∙ ○ b ) , id1 A b > ,  k x z  ∙ < ( x ∙ ○ b ) , id1 A b > > )
                 ≈⟨ cdr (π-cong (IsCCC.e3a isCCC) ? ) ⟩
             k x y ∙ ( < x ∙ ○ b  ,  g > ) ≈↑⟨ cdr (π-cong (cdr (e2)) refl-hom ) ⟩
             k x y ∙ ( < x ∙ ( ○ d ∙ g ) ,  g > ) ≈⟨  cdr (π-cong assoc (sym idL)) ⟩
             k x y ∙ ( < (x ∙ ○ d) ∙ g  , id1 A d ∙ g > ) ≈↑⟨ cdr (IsCCC.distr-π isCCC) ⟩
             k x y ∙ ( < x ∙ ○ d ,  id1 A d > ∙ g ) ≈⟨ assoc ⟩
             (k x y ∙  < x ∙ ○ d ,  id1 A d > ) ∙ g  ≈⟨ car ? ⟩
             f ∙ g  ∎ ) where
           open ≈-Reasoning A
        ... | v {_} {_} {_} {f} y = p-trans ( p-refl ( begin
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
              k x y ∙  < x ∙ ○ _ , id1 A _  > ∎ ) ⟩ _  ∎ )) ?
             -- f  ∎ )  ⟩
             -- f * ∎ ) where
           where open ≈-Reasoning A
        uniq : ( p : Polym x b c) (f : Hom A (a ∧ b) c)  → P≈ x (pf x (f ∙ < x ∙ ○ b , id1 A b >)) p → A [ f ≈ k x (Polym.phi p) ]
        uniq p f eq = sym (begin
               k x (Polym.phi p) ≈⟨ k-cong-p x p (pf x (f ∙ < x ∙ ○ b , id1 A b >)) (p-sym eq)  ⟩
               k x {f ∙ < x ∙ ○ b , id1 A b >} (i _)  ≈⟨ trans-hom (sym assoc)  (cdr (IsCCC.distr-π isCCC) ) ⟩
               f ∙ k x {< x ∙ ○ b , id1 A b >} (iii (i _)  (i _)  ) ≈⟨⟩
               f ∙ <  k x (i (x ∙ ○ b)) ,  k x {id1 A b} (i _) >  ≈⟨ cdr (π-cong u3 idL) ⟩
               -- f ∙ < k x {x} ii ∙ < π , k x {○ b} (i _)  >  , k x {id1 A b} (i _)  >
               --     ≈⟨ cdr (π-cong (cdr (π-cong refl-hom (car e2))) idL ) ⟩
               f ∙  <  π ∙ < π , (○ b ∙ π' ) >  , π' >   ≈⟨ cdr (π-cong (IsCCC.e3a isCCC)  refl-hom) ⟩
               f ∙  < π , π' >  ≈⟨ cdr (IsCCC.π-id isCCC) ⟩
               f ∙  id1 A _ ≈⟨ idR ⟩
               f  ∎  )  where
                   open ≈-Reasoning A
                   -- x ∙ ○ b is clearly Polynominal or assumption xf
                   u3 : A [  k x (i (x ∙ ○ b)) ≈ π ∙ < π , ○ b ∙ π' > ]
                   u3 = begin
                       k x (i (x ∙ ○ b)) ≈⟨ k-cong x (pf x (x ∙ ○ b)) (pcomp x (pf x x) (pf x (○ b))) refl-hom ⟩
                       k x (iv (i x) (i (○ b))) ≈⟨⟩
                       k x (i x) ∙ < π , k x (i (○ b )) > ≈⟨ resp refl-hom ?  ⟩
                       k x ii ∙ < π , k x (i (○ b )) > ≈⟨⟩             
                       π ∙ < π , ○ b ∙ π' >                           
                       ∎



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
        uniq : {b c : Obj A}  →  (p : Polym x b c ) (f' : Hom A (a ∧ b) c)
            → A [  f' ∙ <  x ∙ ○ b  , id1 A b >  ≈ Polym.f p ] → A [ f' ≈ k x (Polym.phi p) ]
        uniq {b} {c} p f' fx=p  = sym (begin
               k x phi ≈↑⟨ Polym.xf p  ⟩
               k x {f} (i _) ≈↑⟨ car fx=p ⟩
               k x {f' ∙ < x ∙ ○ b , id1 A b >} (i _)  ≈⟨ trans-hom (sym assoc)  (cdr (IsCCC.distr-π isCCC) ) ⟩ -- ( f' ∙ < x ∙ ○ b , id1 A b> ) ∙ π'
               f' ∙ k x {< x ∙ ○ b , id1 A b >} (iii (i _)  (i _)  ) ≈⟨⟩                         -- ( f' ∙ < (x ∙ ○ b) ∙ π'  , id1 A b ∙ π' > )
               f' ∙ <  k x (i (x ∙ ○ b)) ,  k x {id1 A b} (i _) >  ≈⟨ cdr (π-cong u3 idL ) ⟩ -- ( f' ∙ < (x ∙ ○ b) ∙ π' , id1 A b ∙ π' > )
               -- f' ∙ < k x {x} ii ∙ < π , k x {○ b} (i _)  >  , k x {id1 A b} (i _)  >   -- ( f' ∙ < π ∙ < π , (x ∙ ○ b) ∙ π' >  , id1 A b ∙ π' > )
               --     ≈⟨ cdr (π-cong (cdr (π-cong refl-hom (car e2))) idL ) ⟩
               f' ∙  <  π ∙ < π , (○ b ∙ π' ) >  , π' >   ≈⟨ cdr (π-cong (IsCCC.e3a isCCC)  refl-hom) ⟩
               f' ∙  < π , π' >  ≈⟨ cdr (IsCCC.π-id isCCC) ⟩
               f' ∙  id1 A _ ≈⟨ idR ⟩
               f' ∎  )  where
                   -- x ∙ ○ b is clearly Polynominal or assumption xf
                   u2 : k x {x ∙ ○ b} (i _) ≈ k x {x} ii ∙ < π , k x {○ b} (i _) >  --  (x ∙ (○ b)) ∙ π' ≈ π ∙ < π , (○ b) ∙ π' >
                   u2 = (≈-Reasoning.trans-hom A) (Polym.xf (pcomp x ? ? )) ?
                   phi = Polym.phi p
                   f = Polym.f p
                   u5 : k x (i x ) ≈ k x ii
                   u5 = ?
                   u4 :  A [ k x (i x) ≈ k x (ii {_} {_} {x}) ]
                   u4 = begin
                      k x (i x) ≈⟨⟩
                      x ∙ π'  ≈⟨ ? ⟩
                      (x ∙ π') ∙ id1 A (a ∧ １)  ≈⟨ ? ⟩
                      (x ∙ π') ∙ < π  , π' >  ≈⟨ ? ⟩
                      ?  ≈⟨ ? ⟩
                      π  ∎
                   u6 : Polym x １ a
                   u6 = record { f = x ; phi = i x ; xf = refl-hom }
                   u7 : Polym x １ a
                   u7 = record { f = x ; phi = ii ; xf = u4 }
                   u3 : A [  k x (i (x ∙ ○ b)) ≈ π ∙ < π , ○ b ∙ π' > ]
                   u3 = begin
                       k x (i (x ∙ ○ b)) ≈⟨ k-cong x (pf x (x ∙ ○ b)) (pcomp x (pf x x) (pf x (○ b))) refl-hom ⟩
                       k x (iv (i x) (i (○ b))) ≈⟨⟩
                       k x (i x) ∙ < π , k x (i (○ b )) > ≈⟨ resp refl-hom u4 ⟩
                       k x ii ∙ < π , k x (i (○ b )) > ≈⟨⟩
                       π ∙ < π , ○ b ∙ π' >
                       ∎ 



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
          k x (Polym.phi φ) ∙ <  x  ∙  ○ １  , id1 A １ >  ≈⟨ fc0 φ  ⟩
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
           (( k x (Polym.phi φ) ∙ < id1 A _ ,  ○ a  > ) ∙ π' ) *   ≈⟨ IsCCC.*-cong isCCC ( begin
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

  data  FourObject   : Set where
       ta : FourObject
       tb : FourObject
       tc : FourObject
       td : FourObject

  data FourHom  : FourObject → FourObject → Set  where
   id-ta :    FourHom ta ta
   id-tb :    FourHom tb tb
   id-tc :    FourHom tc tc
   id-td :    FourHom td td
   arrow-ca :  FourHom tc ta
   arrow-ab :  FourHom ta tb
   arrow-bd :  FourHom tb td
   arrow-cb :  FourHom tc tb
   arrow-ad :  FourHom ta td
   arrow-cd :  FourHom tc td

--
--       epi and monic but does not have inverted arrow
--
--       +--------------------------+
--       |                          |
--       c-----------------+        |
--       |                 ↓        ↓
--       + ----→  a ----→  b ----→  d 
--                |                 ↑
--                +-----------------+
--

  open import graph -- hiding -- (_・_)
                                                                                    
  FourCat : Category  Level.zero Level.zero Level.zero                                                                                  
  FourCat  = GraphtoCat ( record { vertex = FourObject ; edge = FourHom } )                                                             
     where open graphtocat


-- end
