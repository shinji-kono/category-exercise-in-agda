{-# OPTIONS --cubical-compatible --safe #-}

-- -- -- -- -- -- -- -- 
--  Monad to Kelisli Category
--  defines U_T and F_T as a resolution of Monad
--  checks Adjointness
-- 
--   Shinji KONO <kono@ie.u-ryukyu.ac.jp>
-- -- -- -- -- -- -- -- 

-- Monad
-- Category A
-- A = Category
-- Functor T : A → A
--T(a) = t(a)
--T(f) = tf(f)

open import Category -- https://github.com/konn/category-agda
open import Level
--open import Category.HomReasoning
open import HomReasoning
open import Definitions
open import Category.Cat

module kleisli { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ }
                 { T : Functor A A }
                 { η : NTrans A A identityFunctor T }
                 { μ : NTrans A A (T ○ T) T }
                 { M : IsMonad A T η μ }  where

--T(g f) = T(g) T(f)

open Functor
Lemma1 : {c₁ c₂ l : Level} {A : Category c₁ c₂ l} (T : Functor A A) →  {a b c : Obj A} {g : Hom A b c} { f : Hom A a b }
     → A [ ( FMap T (A [ g o f ] ))  ≈ (A [ FMap T g o FMap T f ]) ]
Lemma1 = λ t → IsFunctor.distr ( isFunctor t )


open NTrans
Lemma2 : {c₁ c₂ l : Level} {A : Category c₁ c₂ l} {F G : Functor A A} 
      → (μ : NTrans A A F G) → {a b : Obj A} { f : Hom A a b }
      → A [ A [  FMap G f o TMap μ a ]  ≈ A [ TMap μ b o  FMap F f ] ]
Lemma2 = λ n → IsNTrans.commute ( isNTrans  n  )

-- Laws of Monad
--
-- η :   1_A → T
-- μ :   TT → T
-- μ(a)η(T(a)) = a                 -- unity law 1
-- μ(a)T(η(a)) = a                 -- unity law 2
-- μ(a)(μ(T(a))) = μ(a)T(μ(a))     -- association law


Lemma3 : {c₁ c₂ ℓ : Level} {A : Category c₁ c₂ ℓ}
                 { T : Functor A A }
                 { η : NTrans A A identityFunctor T }
                 { μ : NTrans A A (T ○ T) T }
                 { a : Obj A } →
                 ( M : IsMonad A T η μ )
    → A [ A [  TMap μ a o TMap μ ( FObj T a ) ] ≈  A [  TMap μ a o FMap T (TMap μ a) ] ]
Lemma3 = λ m → IsMonad.assoc m


Lemma4 : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) {a b : Obj A } { f : Hom A a b}
    → A [ A [ Id {_} {_} {_} {A} b o f ] ≈ f ]
Lemma4 = λ a → IsCategory.identityL ( Category.isCategory a )

Lemma5 : {c₁ c₂ ℓ : Level} {A : Category c₁ c₂ ℓ}
                 { T : Functor A A }
                 { η : NTrans A A identityFunctor T }
                 { μ : NTrans A A (T ○ T) T }
                 { a : Obj A } →
                 ( M : IsMonad A T η μ )
    →  A [ A [ TMap μ a o TMap η ( FObj T a )  ] ≈ Id {_} {_} {_} {A} (FObj T a) ]
Lemma5 = λ m → IsMonad.unity1 m

Lemma6 : {c₁ c₂ ℓ : Level} {A : Category c₁ c₂ ℓ}
                 { T : Functor A A }
                 { η : NTrans A A identityFunctor T }
                 { μ : NTrans A A (T ○ T) T }
                 { a : Obj A } →
                 ( M : IsMonad A T η μ )
    →  A [ A [ TMap μ a o (FMap T (TMap η a )) ] ≈ Id {_} {_} {_} {A} (FObj T a) ]
Lemma6 = λ m → IsMonad.unity2 m

-- Laws of Kleisli Category
--
-- nat of η
-- g ○ f = μ(c) T(g) f        -- join definition
-- η(b) ○ f = f               -- left id  (Lemma7)
-- f ○ η(a) = f               -- right id  (Lemma8)
-- h ○ (g ○ f) = (h ○ g) ○ f  -- assocation law (Lemma9)

-- η(b) ○ f = f

join : (m : IsMonad A T η μ ) → { a b : Obj A } → { c : Obj A } →
                              ( Hom A b ( FObj T c )) → (  Hom A a ( FObj T b)) → Hom A a ( FObj T c )
join _ {_} {_} {c} g f = A [ TMap μ c  o A [ FMap T g o f ] ]

Lemma7 : { a : Obj A } { b : Obj A } ( f : Hom A a ( FObj T b) )
                      → A  [ join M (TMap η b) f  ≈ f ]
Lemma7 {_} {b} f = 
  let open ≈-Reasoning (A) in 
     begin  
         join M (TMap η b) f 
     ≈⟨ refl-hom ⟩
         A [ TMap μ b  o A [ FMap T ((TMap η b)) o f ] ]  
     ≈⟨ IsCategory.associative (Category.isCategory A) ⟩
        A [ A [ TMap μ b  o  FMap T ((TMap η b)) ] o f ]
     ≈⟨ car ( IsMonad.unity2 M )  ⟩
        A [  id (FObj T b)   o f ]
     ≈⟨ IsCategory.identityL (Category.isCategory A) ⟩
        f
     ∎

-- f ○ η(a) = f
Lemma8 : { a  : Obj A }  { b : Obj A }
                 ( f : Hom A a ( FObj T b) )
                      → A  [ join M f (TMap η a)  ≈ f ]
Lemma8 {a} {b} f = 
  begin
     join M f (TMap η a) 
  ≈⟨ refl-hom ⟩
     A [ TMap μ b  o A [  FMap T f o (TMap η a) ] ]  
  ≈⟨ cdr  ( nat η ) ⟩
     A [ TMap μ b  o A [ (TMap η ( FObj T b)) o f ] ] 
  ≈⟨ IsCategory.associative (Category.isCategory A) ⟩
     A [ A [ TMap μ b  o (TMap η ( FObj T b)) ] o f ] 
  ≈⟨ car ( IsMonad.unity1 M ) ⟩
     A [ id (FObj T b)  o f ]
  ≈⟨  IsCategory.identityL (Category.isCategory A)  ⟩
     f
  ∎  where 
      open ≈-Reasoning (A) 

-- h ○ (g ○ f) = (h ○ g) ○ f
Lemma9 : { a b c d : Obj A }
                 ( h : Hom A c ( FObj T d) )
                 ( g : Hom A b ( FObj T c) ) 
                 ( f : Hom A a ( FObj T b) )
                      → A  [ join M h (join M g f)  ≈ join M ( join M h g) f ]
Lemma9 {a} {b} {c} {d} h g f = 
  begin 
     join M h (join M g f)  
   ≈⟨⟩
     join M h (                  ( TMap μ c o ( FMap T g o f ) ) )
   ≈⟨ refl-hom ⟩
     ( TMap μ d  o ( FMap T h  o  ( TMap μ c o ( FMap T g  o f ) ) ) )
   ≈⟨ cdr ( cdr ( assoc )) ⟩
     ( TMap μ d  o ( FMap T h o ( ( TMap μ c o  FMap T g )  o f ) ) )
   ≈⟨ assoc  ⟩    ---   ( f  o  ( g  o  h ) ) = ( ( f  o  g )  o  h )
     (     ( TMap μ d o  FMap T h ) o  ( (TMap μ c   o  FMap T g )    o f ) )
   ≈⟨ assoc  ⟩
     ( ( ( TMap μ d o      FMap T h ) o  (TMap μ c   o  FMap T g ) )  o f )
   ≈↑⟨ car assoc ⟩
     ( ( TMap μ d o  ( FMap T h     o   ( TMap μ c   o  FMap T g ) ) ) o f )
   ≈⟨ car ( cdr (assoc) ) ⟩
     ( ( TMap μ d o  ( ( FMap T h o       TMap μ c ) o  FMap T g )   ) o f )
   ≈⟨ car assoc ⟩
     ( ( ( TMap μ d o  ( FMap T h   o   TMap μ c ) ) o  FMap T g ) o f )
   ≈⟨ car (car ( cdr ( begin 
           ( FMap T h o TMap μ c )
       ≈⟨ nat μ ⟩
           ( TMap μ (FObj T d) o FMap T (FMap T h) )
        ∎ 
   )))  ⟩
      ( ( ( TMap μ d  o  ( TMap μ ( FObj T d)  o FMap T (  FMap T h ) ) )  o FMap T g )  o f )
   ≈↑⟨ car assoc ⟩
     ( ( TMap μ d  o  ( ( TMap μ ( FObj T d)   o FMap T (  FMap T h ) )   o FMap T g ) )   o f )
   ≈↑⟨ car ( cdr assoc ) ⟩
     ( ( TMap μ d  o  ( TMap μ ( FObj T d)   o ( FMap T (  FMap T h ) o FMap T g ) ) )   o f )
   ≈↑⟨ car ( cdr (cdr (distr T ))) ⟩
     ( ( TMap μ d  o  ( TMap μ ( FObj T d)     o FMap T ( ( FMap T h  o g ) ) ) )   o f )
   ≈⟨ car assoc ⟩
     ( ( ( TMap μ d  o  TMap μ ( FObj T d)  )  o FMap T ( ( FMap T h  o g ) ) )    o f )
   ≈⟨ car ( car (
      begin
         ( TMap μ d o TMap μ (FObj T d) )
      ≈⟨ IsMonad.assoc M ⟩
         ( TMap μ d o FMap T (TMap μ d) )
      ∎
   )) ⟩
     ( ( ( TMap μ d  o    FMap T ( TMap μ d) ) o FMap T ( ( FMap T h  o g ) ) )    o f )
   ≈↑⟨ car assoc ⟩
     ( ( TMap μ d  o  ( FMap T ( TMap μ d )    o FMap T ( ( FMap T h  o g ) ) ) )  o f )
   ≈↑⟨ assoc ⟩
     ( TMap μ d  o  ( ( FMap T ( TMap μ d )    o FMap T ( ( FMap T h  o g ) ) )  o f ) )
   ≈↑⟨ cdr ( car (  distr T ))   ⟩
     ( TMap μ d  o ( FMap T ( ( ( TMap μ d )   o ( FMap T h  o g ) ) ) o f ) )
   ≈⟨ refl-hom ⟩
     join M ( ( TMap μ d  o ( FMap T h  o g ) ) ) f
   ≈⟨ refl-hom ⟩
     join M ( join M h g) f 
  ∎ where open ≈-Reasoning (A) 

--
--  o-resp in Kleisli Category ( for Functor definitions )
--
Lemma10 :  {a b c : Obj A} → (f g : Hom A a (FObj T b) ) → (h i : Hom A b (FObj T c) ) → 
                          A [ f ≈ g ] → A [ h ≈ i ] → A [ (join M h f) ≈ (join M i g) ]
Lemma10 {a} {b} {c} f g h i f≈g h≈i = let open ≈-Reasoning (A) in
   begin 
       join M h f
   ≈⟨⟩
       TMap μ c  o ( FMap T h  o f )
   ≈⟨ cdr ( car ( fcong T h≈i )) ⟩
       TMap μ c  o ( FMap T i  o f )
   ≈⟨ cdr ( cdr f≈g ) ⟩
       TMap μ c  o ( FMap T i  o g )
   ≈⟨⟩
       join M i g
   ∎

--
--  Hom in Kleisli Category
--

K-id :  {a : Obj A} → Hom A a (FObj T a)
K-id {a = a} = TMap η a 

open import Relation.Binary

_⋍_ : { a : Obj A } { b : Obj A } (f g  : Hom A a (FObj T b) ) → Set ℓ 
_⋍_ {a} {b} f g = A [ f ≈ g ]

_*_ : { a b c : Obj A } → ( Hom A b (FObj T c)) → Hom A a (FObj T b) → Hom A a (FObj T c )
_*_ {a} {b} {c} g f = join M {a} {b} {c} g f

isKleisliCategory : IsCategory ( Obj A ) (λ a b → Hom A a (FObj T b))_⋍_ _*_ K-id 
isKleisliCategory  = record  { isEquivalence =  isEquivalence 
                    ; identityL =   λ {a} {b} {f} → Lemma7 f
                    ; identityR =   λ {a} {b} {f} → Lemma8 f
                    ; o-resp-≈ =    λ {a} {b} {c} {f} {g} {h} {i} → Lemma10 f g h i
                    ; associative = λ {a} {b} {c} {d} {f} {g} {h} →  Lemma9 f g h
                    }
     where
         open ≈-Reasoning (A) 
         isEquivalence :  { a b : Obj A } →
               IsEquivalence {_} {_} {Hom A a (FObj T b)} _⋍_
         isEquivalence {C} {D} =      -- this is the same function as A's equivalence but has different types
           record { refl  = refl-hom
             ; sym   = sym
             ; trans = trans-hom
             } 

KleisliCategory : Category c₁ c₂ ℓ
KleisliCategory =
  record { Obj = Obj A
         ; Hom = λ a b → Hom A a (FObj T b)
         ; _o_ = _*_
         ; _≈_ = _⋍_
         ; Id  = K-id
         ; isCategory = isKleisliCategory
         }

--
-- Resolution
--    T = U_T U_F
--      nat-ε
--      nat-η
--

ufmap : {a b : Obj A} (f : Hom A a (FObj T b) ) → Hom A (FObj T a) (FObj T b)
ufmap {a} {b} f =  A [ TMap μ (b)  o FMap T (f) ]

U_T : Functor KleisliCategory A
U_T = record {
        FObj = FObj T
          ; FMap = ufmap
        ; isFunctor = record
        {      ≈-cong   = ≈-cong
             ; identity = identity
             ; distr    = distr1
        }
     } where
        identity : {a : Obj A} →  A [ ufmap (K-id {a}) ≈ id1 A (FObj T a) ]
        identity {a} = let open ≈-Reasoning (A) in
          begin
              TMap μ (a)  o FMap T (TMap η a)
          ≈⟨ IsMonad.unity2 M ⟩
             id (FObj T a)
          ∎
        ≈-cong : {a b : Obj A} {f g : Hom A a (FObj T b)} → A [ f ≈ g ] → A [ ufmap f ≈ ufmap g ]
        ≈-cong {a} {b} {f} {g} f≈g = let open ≈-Reasoning (A) in
          begin
             TMap μ (b)  o FMap T (f)
          ≈⟨ cdr (fcong T f≈g) ⟩
             TMap μ (b)  o FMap T (g)
          ∎
        distr1 :  {a b c : Obj A} {f : Hom A a (FObj T b)} {g : Hom A b (FObj T c)} → A [ ufmap (g * f) ≈ (A [ ufmap g o ufmap f ] )]
        distr1 {a} {b} {c} {f} {g} = let open ≈-Reasoning (A) in
          begin
             ufmap (g * f)
          ≈⟨⟩
             ufmap {a} {c} ( TMap μ (c) o (FMap T (g)  o (f))  )
          ≈⟨⟩
             TMap μ (c)  o  FMap T ( TMap μ (c) o (FMap T (g)  o (f)))
          ≈⟨ cdr ( distr T) ⟩
             TMap μ (c)  o (( FMap T ( TMap μ (c)) o FMap T  (FMap T (g)  o (f))))
          ≈⟨ assoc ⟩
             (TMap μ (c)  o ( FMap T ( TMap μ (c)))) o FMap T  (FMap T (g)  o (f))
          ≈⟨ car (sym (IsMonad.assoc M)) ⟩
             (TMap μ (c)  o ( TMap μ (FObj T c))) o FMap T  (FMap T (g)  o (f))
          ≈⟨ sym assoc ⟩
             TMap μ (c)  o (( TMap μ (FObj T c)) o FMap T  (FMap T (g)  o (f)))
          ≈⟨ cdr (cdr (distr T)) ⟩
             TMap μ (c)  o (( TMap μ (FObj T c)) o (FMap T  (FMap T (g))  o FMap T (f)))
          ≈⟨ cdr (assoc) ⟩
             TMap μ (c)  o ((( TMap μ (FObj T c)) o (FMap T  (FMap T (g))))  o FMap T (f))
          ≈⟨ sym (cdr (car (nat μ ))) ⟩
             TMap μ (c)  o ((FMap T (g )  o  TMap μ (b))  o FMap T (f ))
          ≈⟨ cdr (sym assoc) ⟩
             TMap μ (c)  o (FMap T (g )  o  ( TMap μ (b)  o FMap T (f )))
          ≈⟨ assoc ⟩
             ( TMap μ (c)  o FMap T (g ) )  o  ( TMap μ (b)  o FMap T (f ) )
          ≈⟨⟩
             ufmap g o ufmap f
          ∎


ffmap :  {a b : Obj A} (f : Hom A a b) → Hom A a (FObj T b)
ffmap {a} {b} f = A [ TMap η b o f ] 

F_T : Functor A KleisliCategory
F_T = record {
        FObj = λ a → a
        ; FMap = ffmap
        ; isFunctor = record
        { ≈-cong   = ≈-cong
             ; identity = identity
             ; distr    = distr1
        }
     } where
        identity : {a : Obj A} →  A [ A [ TMap η a o id1 A a ] ≈ TMap η a  ]
        identity {a} = IsCategory.identityR ( Category.isCategory A)
        --  Category.cod A f and Category.cod A g are actualy the same b, so we don't need cong-≈, just refl
        lemma1 : {b : Obj A} → A [ TMap η b  ≈  TMap η b ]
        lemma1 = IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory A ))
        ≈-cong : {a b : Obj A} {f g : Hom A a b} → A [ f ≈ g ] → A [ A [ TMap η b o f ] ≈ A [ TMap η b o g ] ]
        ≈-cong f≈g =  (IsCategory.o-resp-≈ (Category.isCategory A)) f≈g lemma1 
        distr1 :  {a b c : Obj A} {f : Hom A a b} {g : Hom A b c} → 
                 ( ffmap (A [ g o f ]) ⋍  ( ffmap g * ffmap f ) )
        distr1 {a} {b} {c} {f} {g} =  let open ≈-Reasoning (A) in
          begin
             (ffmap (A [ g o f ]))
          ≈⟨⟩
             TMap η (c) o (g o f)
          ≈⟨ assoc ⟩
             (TMap η (c) o g) o f
          ≈⟨ car (sym (nat η)) ⟩
             (FMap T g  o TMap η (b)) o f
          ≈⟨ sym idL ⟩
             id (FObj T c)  o ((FMap T g  o TMap η (b)) o f)
          ≈⟨ sym (car (IsMonad.unity2 M))  ⟩
             (TMap μ c  o FMap T (TMap η c)) o ((FMap T g  o TMap η (b)) o f)
          ≈⟨ sym assoc  ⟩
             TMap μ c  o  ( FMap T (TMap η c) o ((FMap T g  o TMap η (b)) o f) )
          ≈⟨ cdr (cdr (sym  assoc))  ⟩
             TMap μ c  o  ( FMap T (TMap η c) o (FMap T g  o (TMap η (b) o f)))
          ≈⟨ cdr assoc  ⟩
             TMap μ c  o ( ( FMap T (TMap η c) o FMap T g ) o (TMap η (b) o f) )
          ≈⟨ sym (cdr ( car ( distr T ))) ⟩
             TMap μ c  o ( ( FMap T (TMap η c o g))  o (TMap η (b) o f))
          ≈⟨ assoc ⟩
             (TMap μ c  o  ( FMap T (TMap η c o g)))  o (TMap η (b) o f)
          ≈⟨ assoc ⟩
             ((TMap μ c  o  (FMap T  (TMap η c o g)))  o  TMap η b) o f
          ≈⟨ sym assoc ⟩
             (TMap μ c  o  (FMap T  (TMap η c o g)))  o  (TMap η b o f) 
          ≈⟨ sym assoc ⟩
             TMap μ c  o ( (FMap T  (TMap η c o g))  o  (TMap η b o f) )
          ≈⟨⟩
             join M (TMap η c o g)  (TMap η b o f) 
          ≈⟨⟩
              ( ffmap g * ffmap f )
          ∎

--
-- T = (U_T ○ F_T) 
--

Lemma11-1 :  ∀{a b : Obj A} → (f : Hom A a b ) → A [ FMap T f  ≈ FMap (U_T ○ F_T) f ]
Lemma11-1 {a} {b} f = let open ≈-Reasoning (A) in
     sym ( begin
          FMap (U_T ○ F_T) f
     ≈⟨⟩
          FMap U_T ( FMap F_T f )
     ≈⟨⟩  
           TMap μ (b)  o FMap T (( ffmap f ) )
     ≈⟨⟩  
           TMap μ (b)  o FMap T (TMap η (b) o f)
     ≈⟨ cdr (distr T ) ⟩  
           TMap μ (b)  o ( FMap T (TMap η (b)) o FMap T f)
     ≈⟨ assoc  ⟩
           (TMap μ (b)  o  FMap T (TMap η (b))) o FMap T f
     ≈⟨ car (IsMonad.unity2 M) ⟩
           id (FObj T b) o FMap T f
     ≈⟨ idL ⟩
           FMap T f 
     ∎ )

-- construct ≃

Lemma11 :  T ≃  (U_T ○ F_T)
Lemma11 f = Category.Cat.refl (Lemma11-1 f)

--
-- natural transformations
--

nat-η : NTrans A A identityFunctor ( U_T ○ F_T ) 
nat-η = record { TMap = λ x → TMap η x ; isNTrans =  record { commute = commute } } where
       commute :  {a b : Obj A} {f : Hom A a b}
            → A [ A [ (  FMap ( U_T ○ F_T ) f ) o  ( TMap η a ) ]  ≈ A [ (TMap η b ) o  f  ] ]
       commute {a} {b} {f} =  let open ≈-Reasoning (A) in
          begin
              ( FMap ( U_T ○ F_T ) f ) o  ( TMap η a )
          ≈⟨ sym (resp refl-hom (Lemma11-1 f)) ⟩
              FMap T f o TMap η a 
          ≈⟨ nat η ⟩
              TMap η b o f
          ∎ 

tmap-ε : (a : Obj A) → Hom A (FObj T a) (FObj T a)
tmap-ε a = id1 A (FObj T a) 

nat-ε : NTrans KleisliCategory KleisliCategory  ( F_T ○ U_T ) identityFunctor
nat-ε = record { TMap = λ a → tmap-ε a; isNTrans = isNTrans1 } where
       commute1 : {a b : Obj A} {f : Hom A a (FObj T b)}
            →  (f * ( tmap-ε a ) ) ⋍   (( tmap-ε b ) * (  FMap (F_T ○ U_T) f ) )
       commute1 {a} {b} {f} =  let open ≈-Reasoning (A) in
          sym ( begin
              (( tmap-ε b ) * (  FMap (F_T ○ U_T) f ))
          ≈⟨⟩
              TMap μ b  o ( FMap T ( id (FObj T b) )  o (  (FMap (F_T ○ U_T) f ) ))
          ≈⟨ cdr ( cdr (
               begin
                  (FMap (F_T ○ U_T) f ) 
               ≈⟨⟩
                  (FMap F_T (FMap U_T f))
               ≈⟨⟩
                 TMap η (FObj T b) o (TMap μ (b)  o FMap T (f))
               ∎  
          ))  ⟩
              TMap μ b  o ( FMap T ( id (FObj T b) )  o (TMap η (FObj T b) o (TMap μ (b)  o FMap T (f))))
          ≈⟨ cdr (car (IsFunctor.identity (isFunctor T))) ⟩
              TMap μ b  o ( id (FObj T (FObj T b) )  o (TMap η (FObj T b) o (TMap μ (b)  o FMap T (f))))
          ≈⟨ cdr idL ⟩
              TMap μ b  o  (TMap η (FObj T b) o (TMap μ (b)  o FMap T (f)))
          ≈⟨ assoc ⟩
              (TMap μ b  o  (TMap η (FObj T b))) o (TMap μ (b)  o FMap T (f))
          ≈⟨ (car (IsMonad.unity1 M)) ⟩
              id (FObj T b) o (TMap μ (b)  o FMap T (f))
          ≈⟨ idL ⟩
              TMap μ b  o FMap T (f) 
          ≈⟨ cdr (sym idR) ⟩
              TMap μ b  o ( FMap T (f)  o id (FObj T a) )
          ≈⟨⟩
              (f * ( tmap-ε a ))
          ∎ )
       isNTrans1 : IsNTrans  KleisliCategory KleisliCategory ( F_T ○ U_T ) identityFunctor (λ a → tmap-ε a )
       isNTrans1 = record { commute = commute1 } 

--
-- μ = U_T ε U_F
--
tmap-μ :  (a : Obj A) → Hom A (FObj ( U_T ○ F_T ) (FObj ( U_T ○ F_T ) a)) (FObj ( U_T ○ F_T ) a)
tmap-μ a = FMap U_T ( TMap nat-ε ( FObj F_T a ))

nat-μ : NTrans A A (( U_T ○ F_T ) ○ ( U_T ○ F_T )) ( U_T ○ F_T )
nat-μ = record { TMap = tmap-μ ; isNTrans = isNTrans1 } where
        commute1 : {a b : Obj A} {f : Hom A a b}
             →  A [ A [ (FMap (U_T ○ F_T) f) o  ( tmap-μ a) ]  ≈ A [ ( tmap-μ b ) o  FMap (U_T ○ F_T) ( FMap (U_T ○ F_T) f)  ] ]
        commute1 {a} {b} {f} =  let open ≈-Reasoning (A) in
          sym ( begin
             ( tmap-μ b ) o  FMap (U_T ○ F_T) ( FMap (U_T ○ F_T) f)  
          ≈⟨⟩
             (  FMap U_T ( TMap nat-ε ( FObj F_T b )) ) o  FMap (U_T ○ F_T) ( FMap (U_T ○ F_T) f)  
          ≈⟨ sym ( distr U_T) ⟩
             FMap U_T ( KleisliCategory [ TMap nat-ε ( FObj F_T b )  o  FMap F_T ( FMap (U_T ○ F_T) f) ] )  
          ≈⟨ fcong U_T (sym (nat nat-ε)) ⟩
             FMap U_T ( KleisliCategory [ (FMap  F_T f) o TMap nat-ε ( FObj F_T a ) ] ) 
          ≈⟨ distr U_T ⟩
             (FMap U_T (FMap  F_T f)) o   FMap U_T ( TMap nat-ε ( FObj F_T a )) 
          ≈⟨⟩
             (FMap (U_T ○ F_T) f) o  ( tmap-μ a) 
          ∎ )
        isNTrans1 : IsNTrans A A (( U_T ○ F_T ) ○ ( U_T ○ F_T )) ( U_T ○ F_T ) tmap-μ
        isNTrans1 = record { commute = commute1 } 

Lemma12 : {x : Obj A } → A [ TMap nat-μ x ≈ FMap U_T ( TMap nat-ε ( FObj F_T x ) ) ]
Lemma12 {x} = let open ≈-Reasoning (A) in
          sym ( begin
              FMap U_T ( TMap nat-ε ( FObj F_T x ) )
          ≈⟨⟩
              tmap-μ x
          ≈⟨⟩
              TMap nat-μ x
          ∎ )

Lemma13 : {x : Obj A } → A [ TMap μ x ≈ FMap U_T ( TMap nat-ε ( FObj F_T x ) ) ]
Lemma13 {x} = let open ≈-Reasoning (A) in
          sym ( begin
              FMap U_T ( TMap nat-ε ( FObj F_T x ) )
          ≈⟨⟩
              TMap μ x  o FMap T (id (FObj T x) )
          ≈⟨  cdr (IsFunctor.identity (isFunctor T)) ⟩
              TMap μ x  o id (FObj T (FObj T x) )
          ≈⟨ idR ⟩
              TMap μ x
          ∎ )

Adj_T : Adjunction A KleisliCategory 
Adj_T = record {
           U = U_T ;
           F = F_T ;
           η = nat-η ;
           ε = nat-ε  ;
           isAdjunction = record {
               adjoint1 = adjoint1 ; 
               adjoint2 = adjoint2
           } 
       } where
           adjoint1 :   { b : Obj KleisliCategory } →
                     A [ A [ ( FMap U_T ( TMap nat-ε b))  o ( TMap nat-η ( FObj U_T b )) ]  ≈ id1 A (FObj U_T b) ]
           adjoint1 {b} =  let open ≈-Reasoning (A) in
               begin
                  ( FMap U_T ( TMap nat-ε b))  o ( TMap nat-η ( FObj U_T b ))
               ≈⟨⟩
                  (TMap μ (b)  o FMap T (id (FObj T b )))  o ( TMap η ( FObj T b ))
               ≈⟨ car ( cdr (IsFunctor.identity (isFunctor T))) ⟩
                  (TMap μ (b)  o (id (FObj T (FObj T b ))))  o ( TMap η ( FObj T b ))
               ≈⟨ car idR ⟩
                  TMap μ (b) o ( TMap η ( FObj T b ))
               ≈⟨ IsMonad.unity1 M ⟩
                  id (FObj U_T b)
               ∎ 
           adjoint2 :   {a : Obj A} →
                     KleisliCategory [ KleisliCategory [ ( TMap nat-ε ( FObj F_T a ))  o ( FMap F_T ( TMap nat-η a )) ]  
                                     ≈ id1 KleisliCategory (FObj F_T a) ]
           adjoint2 {a} =  let open ≈-Reasoning (A) in
               begin
                  (( TMap nat-ε ( FObj F_T a )) * ( FMap F_T ( TMap nat-η a )) )
               ≈⟨⟩
                  TMap μ a o (FMap T (id (FObj T a) ) o ((TMap η (FObj T a)) o (TMap η a)))
               ≈⟨ cdr ( car ( IsFunctor.identity (isFunctor T))) ⟩
                  TMap μ a o ((id (FObj T (FObj T a) )) o ((TMap η (FObj T a)) o (TMap η a)))
               ≈⟨ cdr ( idL ) ⟩
                  TMap μ a o ((TMap η (FObj T a)) o (TMap η a))
               ≈⟨ assoc  ⟩
                  (TMap μ a o (TMap η (FObj T a))) o (TMap η a)
               ≈⟨ car (IsMonad.unity1 M) ⟩
                  id (FObj T a) o (TMap η a)
               ≈⟨ idL ⟩
                  TMap η a
               ≈⟨⟩
                  TMap η (FObj F_T a)
               ≈⟨⟩
                  (id1 KleisliCategory (FObj F_T a))
               ∎

open MResolution

Resolution_T : MResolution A KleisliCategory ( record { T = T ; η = η ; μ = μ; isMonad = M } )
Resolution_T = record {
      UR = U_T ;
      FR = F_T ;
      ηR = nat-η ;
      εR = nat-ε ;
      μR = nat-μ ;
      Adj = Adjunction.isAdjunction Adj_T  ;
      T=UF   = Lemma11;
      μ=UεF  = Lemma12 
  }

-- end
