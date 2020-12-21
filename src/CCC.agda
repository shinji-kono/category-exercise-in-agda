open import Level
open import Category 
module CCC where

open import HomReasoning
open import cat-utility
open  import  Relation.Binary.PropositionalEquality


open import HomReasoning 

record IsCCC {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) 
         ( １ : Obj A )
         ( ○ : (a : Obj A ) → Hom A a １ )
          ( _∧_ : Obj A → Obj A → Obj A  ) 
          ( <_,_> : {a b c : Obj A } → Hom A c a → Hom A c b → Hom A c (a ∧ b)  ) 
          ( π : {a b : Obj A } → Hom A (a ∧ b) a ) 
          ( π' : {a b : Obj A } → Hom A (a ∧ b) b ) 
          ( _<=_ : (a b : Obj A ) → Obj A ) 
          ( _* : {a b c : Obj A } → Hom A (a ∧ b) c → Hom A a (c <= b) ) 
          ( ε : {a b : Obj A } → Hom A ((a <= b ) ∧ b) a )
             :  Set ( c₁  ⊔  c₂ ⊔ ℓ ) where
     field
       -- cartesian
       e2  : {a : Obj A} → ∀ { f : Hom A a １ } →  A [ f ≈ ○ a ]
       e3a : {a b c : Obj A} → { f : Hom A c a }{ g : Hom A c b } →  A [ A [ π o < f , g > ] ≈ f ]
       e3b : {a b c : Obj A} → { f : Hom A c a }{ g : Hom A c b } →  A [ A [ π' o < f , g > ] ≈ g ]
       e3c : {a b c : Obj A} → { h : Hom A c (a ∧ b) } →  A [ < A [ π o h ] , A [ π' o h  ] >  ≈ h ]
       π-cong :  {a b c : Obj A} → { f f' : Hom A c a }{ g g' : Hom A c b } → A [ f ≈ f' ]  → A [ g ≈ g' ]  →  A [ < f , g >  ≈ < f' , g' > ] 
       -- closed
       e4a : {a b c : Obj A} → { h : Hom A (c ∧ b) a } →  A [ A [ ε o < A [ (h *) o π ]  ,  π' > ] ≈ h ]
       e4b : {a b c : Obj A} → { k : Hom A c (a <= b ) } →  A [ ( A [ ε o < A [ k o  π ]  ,  π' > ] ) * ≈ k ]
       *-cong :  {a b c : Obj A} → { f f' : Hom A (a ∧ b) c } → A [ f ≈ f' ]  → A [  f *  ≈  f' * ] 

     e'2 : A [ ○ １ ≈ id1 A １ ]
     e'2 = let open  ≈-Reasoning A in begin
            ○ １
        ≈↑⟨ e2  ⟩
           id1 A １
        ∎
     e''2 : {a b : Obj A} {f : Hom A a b } → A [ A [  ○ b o f ] ≈ ○ a ]
     e''2 {a} {b} {f} = let open  ≈-Reasoning A in begin
           ○ b o f
        ≈⟨ e2  ⟩
           ○ a
        ∎
     π-id : {a b : Obj A} → A [ < π ,  π' >  ≈ id1 A (a ∧ b ) ]
     π-id {a} {b} = let open  ≈-Reasoning A in begin
           < π ,  π' > 
        ≈↑⟨ π-cong idR idR  ⟩
          < π o id1 A (a ∧ b)  ,  π'  o id1 A (a ∧ b) >
        ≈⟨ e3c ⟩
          id1 A (a ∧ b )
        ∎
     distr-π : {a b c d : Obj A} {f : Hom A c a }{g : Hom A c b } {h : Hom A d c } → A [ A [ < f , g > o h ]  ≈  < A [ f o h ] , A [ g o h ] > ]
     distr-π {a} {b} {c} {d} {f} {g} {h} = let open  ≈-Reasoning A in begin
            < f , g > o h
        ≈↑⟨ e3c ⟩
            < π o  < f , g > o h  , π' o  < f , g > o h  >
        ≈⟨ π-cong assoc assoc ⟩
            < ( π o  < f , g > ) o h  , (π' o  < f , g > ) o h  >
        ≈⟨ π-cong (car e3a ) (car e3b) ⟩
            < f o h ,  g o h  >
        ∎
     _×_ :  {  a b c d  : Obj A } ( f : Hom A a c ) (g : Hom A b d )  → Hom A (a ∧ b) ( c ∧ d )
     f × g  = < (A [ f o  π ] ) , (A [ g o π' ])  >
     distr-* : {a b c d : Obj A } { h : Hom A (a ∧ b) c } { k : Hom A d a } → A [ A [ h * o k ]  ≈ ( A [ h o < A [ k o π ] , π' > ] ) * ]
     distr-* {a} {b} {c} {d} {h} {k} = begin
             h * o k
        ≈↑⟨ e4b  ⟩
             (  ε o < (h * o k ) o π  , π' > ) *
        ≈⟨ *-cong ( begin
              ε o < (h * o k ) o π  , π' > 
        ≈↑⟨ cdr ( π-cong assoc refl-hom ) ⟩
              ε o ( < h * o ( k o π ) , π' > ) 
        ≈↑⟨ cdr ( π-cong (cdr e3a) e3b ) ⟩
               ε o ( < h * o ( π o < k o π , π' > ) , π' o < k o π , π' > > ) 
        ≈⟨ cdr ( π-cong assoc refl-hom) ⟩
               ε o ( < (h * o π) o < k o π , π' > , π' o < k o π , π' > > ) 
        ≈↑⟨ cdr ( distr-π ) ⟩
               ε o ( < h * o π , π' >  o < k o π , π' > )
        ≈⟨ assoc ⟩
              ( ε o < h * o π , π' > ) o < k o π , π' > 
        ≈⟨ car e4a  ⟩
               h o < k o π , π' > 
        ∎ ) ⟩
            ( h o  <  k o π  , π' > ) *
        ∎ where open  ≈-Reasoning A
     α : {a b c : Obj A } → Hom A (( a ∧ b ) ∧ c ) ( a ∧ ( b ∧ c ) )
     α = < A [ π  o π  ]  , < A [ π'  o π ]  , π'  > >
     α' : {a b c : Obj A } → Hom A  ( a ∧ ( b ∧ c ) ) (( a ∧ b ) ∧ c )
     α' = < < π , A [ π o π' ] > ,  A [ π'  o π' ]  >
     β : {a b c d : Obj A } { f : Hom A a b} { g : Hom A a c } { h : Hom A a d } → A [ A [ α o < < f , g > , h > ] ≈  < f , < g , h > > ]
     β {a} {b} {c} {d} {f} {g} {h} = begin
             α o < < f , g > , h >
        ≈⟨⟩
            ( < ( π o π ) , < ( π' o π ) , π' > > ) o  < < f , g > , h >
        ≈⟨ distr-π ⟩
             < ( ( π o π ) o  < < f , g > , h > ) , ( < ( π' o π ) , π' >   o  < < f , g > , h > )  >  
        ≈⟨ π-cong refl-hom distr-π ⟩
             < ( ( π o π ) o  < < f , g > , h > ) , ( < ( ( π' o π ) o  < < f , g > , h > ) , ( π'  o  < < f , g > , h > ) > )  >  
        ≈↑⟨ π-cong assoc ( π-cong assoc refl-hom )  ⟩
             < (  π o (π  o  < < f , g > , h >) ) , ( < (  π' o ( π  o  < < f , g > , h > ) ) , ( π'  o  < < f , g > , h > ) > )  >  
        ≈⟨ π-cong (cdr e3a ) ( π-cong (cdr e3a ) e3b )  ⟩
             < (  π o < f , g >  ) ,  < (  π' o < f , g >  ) , h >   >  
        ≈⟨ π-cong e3a ( π-cong e3b refl-hom )  ⟩
            < f , < g , h > >
         ∎ where open  ≈-Reasoning A


record CCC {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) :  Set ( c₁  ⊔  c₂ ⊔ ℓ ) where
     field
         １ : Obj A 
         ○ : (a : Obj A ) → Hom A a １ 
         _∧_ : Obj A → Obj A → Obj A   
         <_,_> : {a b c : Obj A } → Hom A c a → Hom A c b → Hom A c (a ∧ b)  
         π : {a b : Obj A } → Hom A (a ∧ b) a 
         π' : {a b : Obj A } → Hom A (a ∧ b) b  
         _<=_ : (a b : Obj A ) → Obj A 
         _* : {a b c : Obj A } → Hom A (a ∧ b) c → Hom A a (c <= b) 
         ε : {a b : Obj A } → Hom A ((a <= b ) ∧ b) a 
         isCCC : IsCCC A １ ○ _∧_ <_,_> π π' _<=_ _* ε 





