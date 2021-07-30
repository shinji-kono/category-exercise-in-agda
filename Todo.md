Todo
====

CCCGraph.agda            
---
CCC generated from Graph (iconmplete) p.55

   cat-graph-univ :  {c₁ : Level} → UniversalMapping (Grph {c₁} {c₁}) (CAT {c₁ } {c₁} {c₁}) forgetful.UC 
   ccc-graph-univ :  {c₁ : Level} → UniversalMapping (Grph {c₁} {c₁}) (Cart {c₁ } {c₁} {c₁}) forgetful.UX 

Polynominal.agda         
---
Polynominal Category and functional completeness

  -- an assuption needed in k x phi ≈ k x phi'
  --   k x (i x) ≈ k x ii  
  postulate 
       xf :  {a b c : Obj A } → ( x : Hom A １ a ) → {z : Hom A b c } → ( y  : φ {a} x z ) → ( x ∙ π' ) ≈ π 

  define Polynominal Category as a graph generated one
  define Polynominal Category as a coMonad

Topos
---

   ToposEx.agda             Topos Exercise (incomplete)                p.141
   ToposIL.agda             Topos Internal Language (incomplete)       p.143
   ToposSub.agda            Topos Subobject classifier (incomplete)

equalizer.agda           
---
Equalizer example p.21

Bourroni equations gives an Equalizer

   postulate 
     uniqueness1 : {d : Obj A} →  ∀ {h : Hom A d a} →  {eq : A [ A [ f  o  h ] ≈ A [ g  o h ] ] } →  {k' : Hom A d c } →
        A [ A [ (α bur f g ) o k' ] ≈ h ] → A [ k1 {d} h eq  ≈ k' ]

system-f.agda
---

   very incomplete, because this is a meta circular interpreter of Agda

yoneda.agda              
---
Yoneda Functor p.11

     ylem0 : {a b : Obj A } → Hom A a a ≡ Hom A a b → a ≡ b

