{-# OPTIONS --cubical-compatible --safe #-}

open import Level
open import Category
open import Definitions
open Functor

module monad→monoidal (
    FT : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (C : Category c₁ c₂ ℓ) (D : Category c₁' c₂' ℓ') {a b c : Obj C } → FreeTheorem C D  {a} {b} {c} )
 where

open import Data.Product renaming (_×_ to _*_) hiding (_<*>_)
open import Category.Constructions.Product
open import HomReasoning
open import Relation.Binary.Core
open import Relation.Binary

open NTrans

open import monoidal 
open import applicative  FT
open import Category.Cat
open import Category.Sets
open import Relation.Binary.PropositionalEquality  hiding ( [_] )

-----
--
--  Monad on Sets implies Applicative and Haskell Monidal Functor
--
--

open import  Relation.Binary.PropositionalEquality as EqR
open ≡-Reasoning

left : {n : Level} { a b : Set n} → { x y : a → b } { h : a }  → ( x ≡ y ) → x h ≡ y h
left {_} {_} {_} {_} {_} {h} eq = ≡-cong ( λ k → k h ) eq 

right : {n : Level} { a b : Set n} → { x y : a } { h : a → b }  → ( x ≡ y ) → h x  ≡ h y 
right {_} {_} {_} {_} {_} {h} eq = ≡-cong ( λ k → h k ) eq 

Monad→HaskellMonoidalFunctor : {l : Level } (m : Monad (Sets {l} ) ) → HaskellMonoidalFunctor ( Monad.T m )
Monad→HaskellMonoidalFunctor {l} monad = record {
         unit = unit
       ; φ = φ
       ; isHaskellMonoidalFunctor = record {
          natφ = natφ 
        ; assocφ = assocφ  
        ; idrφ =  idrφ  
        ; idlφ = idlφ  
       }
   } where
          open Monad monad
          isM = Monoidal.isMonoidal MonoidalSets 
          unit  : FObj T One
          unit  = TMap η One OneObj 
          φ    : {a b : Obj Sets} → Hom Sets ((FObj T a) *  (FObj T b )) ( FObj T ( a * b ) )
          φ {a} {b} (x , y)  =  TMap μ (a * b) (FMap T ( λ f → FMap T ( λ g → ( f , g )) y ) x )
          open IsMonoidal
          id : { a : Obj (Sets {l}) } → a → a
          id x = x
          fdistr : {a b c : Obj (Sets {l})} → {f : Hom (Sets {l}) b c } {g : Hom (Sets {l} ) a b } → (x : FObj T a) 
             →  FMap T (λ z → f (g z)) x ≡ FMap T f ( FMap T g x )  
          fdistr x = IsFunctor.distr (isFunctor T) x 
          fcong : {b c : Obj (Sets {l})} → {f g : Hom (Sets {l}) b c }  → (x : FObj T b) 
             →  ((x : b) → f x ≡ g x) →  FMap T f x ≡ FMap T g x
          fcong x eq = IsFunctor.≈-cong (isFunctor T) eq x
          natφ : { a b c d : Obj Sets } { x : FObj T a} { y : FObj T b} { f : a → c } { g : b → d  }
             → FMap T (map f g) (φ (x , y)) ≡ φ (FMap T f x , FMap T g y)
          natφ {a} {b} {c} {d} {x} {y} {f} {g} = begin 
             FMap T (map f g) (φ (x , y)) ≡⟨  nat μ (FMap T (λ a → FMap T (λ b → (a , b))  y )  x)  ⟩ 
             TMap μ (c * d) (FMap T (FMap T (map f g)) (FMap T (λ f₁ → FMap T (λ g₁ → f₁ , g₁) y) x)) ≡⟨ cong (λ k → TMap μ (c * d) k) (
                begin
                FMap T (FMap T (map f g)) (FMap T (λ f₁ → FMap T (λ g₁ → f₁ , g₁) y) x) ≡⟨ sym (fdistr x) ⟩ 
                FMap T (λ f₁ → FMap T (map f g) (FMap T (λ g₁ → f₁ , g₁) y)) x ≡⟨ fcong x ( λ x → begin
                   FMap T (map f g) (FMap T (λ g₁ → x , g₁) y) ≡⟨ sym (IsFunctor.distr (isFunctor T) y) ⟩
                   FMap T (λ x₂ → map f g (x , x₂)) y ≡⟨ fdistr y ⟩  -- to use Sets assoc in F
                   FMap T (λ g₁ → f x , g₁) (FMap T g y) ∎ )  ⟩
                FMap T (λ x₁ → FMap T (λ g₁ → f x₁ , g₁) (FMap T g y)) x ≡⟨ fdistr x  ⟩
                FMap T (λ f → FMap T (λ g → f , g) (FMap T g y)) (FMap T f x) ∎ ) ⟩
             φ (FMap T f x , FMap T g y) ∎ 
          assocφ : { x y z : Obj Sets } { a : FObj T x } { b : FObj T y }{ c : FObj T z }
             → φ (a , φ (b , c)) ≡ FMap T (Iso.≅→ (mα-iso isM)) (φ (φ (a , b) , c))
          assocφ {x} {y} {z} {a} {b} {c} =  begin
               φ (a , φ (b , c)) ≡⟨ cong ( TMap μ (x * (y * z)) ) (fcong a (λ f → begin
                  FMap T (λ g → f , g) (φ (b , c)) ≡⟨ refl ⟩
                  FMap T (λ g → f , g)  (TMap μ (Σ y (λ v → z)) (FMap T (λ f → FMap T (λ g → f , g) c) b)) 
                       ≡⟨ nat μ (FMap T (λ f → FMap T (λ g → (f , g)) c) b) ⟩
                  TMap μ (x * y * z) (FMap T (FMap T (λ g → f , g)) (FMap T (λ f → FMap T (λ g → f , g) c) b)) 
                     ≡⟨ sym (cong (λ k → TMap μ (x * y * z) k) (fdistr b )) ⟩
                  TMap μ (x * y * z) (FMap T ((λ f₁ → (FMap T (λ g → f , g)  (FMap T (λ g → f₁ , g) c )))) b)  
                     ≡⟨ sym (cong (λ k → TMap μ (x * y * z) k ) (fcong b (λ x → fdistr c )  ))  ⟩
                  TMap μ (x * y * z) (( FMap T (λ g → (FMap T (λ h → f , (g , h))) c)) b )  ∎ )  ) ⟩
               TMap μ (x * y * z) (FMap T (λ z₁ → TMap μ (x * y * z) (FMap T (λ g → FMap T (λ h → z₁ , g , h) c) b)) a) 
                   ≡⟨ cong (λ k → TMap μ (x * y * z) k ) (fdistr a ) ⟩
               TMap μ (x * y * z) (FMap T (TMap μ (x * y * z)) (FMap T (λ f → ( FMap T (λ g → (FMap T (λ h → f , (g , h))) c)) b ) a ))   
                   ≡⟨ sym (IsMonad.assoc isMonad _ ) ⟩
               TMap μ (x * y * z) (TMap μ (FObj T (x * y * z)) (FMap T (λ f → FMap T (λ g → FMap T (λ h → f , g , h) c) b) a))  
                   ≡⟨ cong ( λ k → TMap μ (x * (y * z)) (TMap μ _ k) ) (begin
                     FMap T (λ f → FMap T (λ g → FMap T (λ h → f , g , h) c) b) a  ≡⟨ fcong a (λ w → fdistr b) ⟩ 
                     FMap T (λ z₁ → FMap T (λ z₂ → FMap T (λ z₃ → Iso.≅→ (mα-iso isM) (z₂ , z₃)) c) (FMap T (λ g → z₁ , g) b)) a
                          ≡⟨ fcong a (λ w → (fcong _ (λ z → fdistr c)) ) ⟩ 
                     FMap T (λ z₁ → FMap T (λ x₁ → FMap T (Iso.≅→ (mα-iso isM)) (FMap T (λ g → x₁ , g) c)) (FMap T (λ g → z₁ , g) b)) a  ∎ ) ⟩
               TMap μ (x * y * z) (TMap μ (FObj T (x * y * z)) (FMap T (λ z₁ → FMap T (λ x₁ → FMap T (Iso.≅→ (mα-iso isM)) (FMap T (λ g → x₁ , g) c)) (FMap T (λ g → z₁ , g) b)) a))
                   ≡⟨ cong ( λ k → TMap μ (x * (y * z)) (TMap μ _ k) ) (fdistr a) ⟩
               TMap μ (x * y * z) (TMap μ (FObj T (x * y * z)) 
                  (FMap T (FMap T (λ x₁ → FMap T (Iso.≅→ (mα-iso isM)) (FMap T (λ g → x₁ , g) c))) (FMap T (λ f → FMap T (λ g → f , g) b) a))) 
                      ≡⟨ cong (λ k → TMap μ (x * (y * z)) k ) (sym ( nat μ _ )) ⟩
               TMap μ (x * y * z) (FMap T (λ x₁ → FMap T (Iso.≅→ (mα-iso isM)) (FMap T (λ g → x₁ , g) c)) (φ (a , b))) 
                   ≡⟨ cong (λ k → TMap μ (x * (y * z)) k ) (fdistr _)  ⟩
               TMap μ (x * y * z) (FMap T (FMap T (Iso.≅→ (mα-iso isM))) (FMap T (λ f → FMap T (λ g → f , g) c) (φ (a , b)))) ≡⟨ sym ( nat μ _ ) ⟩
               FMap T (Iso.≅→ (mα-iso isM)) (φ (φ (a , b) , c)) ∎
          proj1 :  {a : Obj Sets} → _*_ {l} {l} a One → a
          proj1 =  proj₁
          proj2 :  {a : Obj Sets} → _*_ {l} {l} One a → a
          proj2 =  proj₂
          import HomReasoning
          -- open ≈-Reasoning  (Sets {l}) as HR
          idrφ : {a : Obj Sets } { x : FObj T a } → FMap T (Iso.≅→ (mρ-iso isM)) (φ (x , unit)) ≡ x
          idrφ {a} {x} =  begin
             FMap T (Iso.≅→ (mρ-iso isM)) (φ (x , unit)) ≡⟨ cong (λ f → FMap T (Iso.≅→ (mρ-iso isM)) (TMap μ _ f)) ( begin
               FMap T (λ f → FMap T (λ g → f , g) unit) x ≡⟨ fcong x (λ g → nat η _ )  ⟩
               FMap T (λ z → TMap η (Σ a (λ v → One)) (z  , OneObj)) x ≡⟨ fdistr x  ⟩
               FMap T ( TMap η(a * One  )) (FMap T ( λ f → ( f , OneObj  )) x ) ∎ ) ⟩
             FMap T proj1 (  TMap μ (a * One ) (FMap T ( TMap η(a * One  )) (FMap T ( λ f → ( f , OneObj  )) x )))  
                 ≡⟨ cong (λ f →  FMap T proj₁ f) (IsMonad.unity2 isMonad _ ) ⟩
             FMap T proj₁ (id1 Sets (FObj T (a * One)) (FMap T (λ f → f , OneObj) x)) ≡⟨ fcong _ (λ f →  ≈-Reasoning.idL Sets x ) ⟩
             FMap T proj₁ (FMap T (λ f → f , OneObj) x) ≡⟨ sym (fdistr x) ⟩
             FMap T ( id1 Sets a) x ≡⟨ IsFunctor.identity (isFunctor T) x ⟩
             id1 Sets (FObj T a) x ≡⟨ refl ⟩
             x ∎
          idlφ : {a : Obj Sets } { x : FObj T a } → FMap T (Iso.≅→ (mλ-iso isM)) (φ (unit , x)) ≡ x
          idlφ {a} {x} = begin
             FMap T (Iso.≅→ (mλ-iso isM)) (φ (unit , x)) ≡⟨ cong (λ f → FMap T (Iso.≅→ (mλ-iso isM)) (TMap μ _ f)) ( begin
               FMap T (λ f → FMap T (λ g → f , g) x) unit ≡⟨ nat η _  ⟩
               TMap η (FObj T (Σ One (λ _ → a))) (FMap T (λ f → OneObj , f) x)  ∎ ) ⟩
             FMap T proj₂ (TMap μ (One * a) (TMap η (FObj T (Σ One (λ _ → a))) (FMap T (λ f → OneObj , f) x))) 
                 ≡⟨ cong (λ f →  FMap T proj₂ f) (IsMonad.unity1 isMonad _ )  ⟩
             FMap T proj₂ (id1 Sets (FObj T (One * a)) (FMap T (λ f → OneObj , f) x)) ≡⟨ fcong _ (λ f →  ≈-Reasoning.idR Sets x ) ⟩
             FMap T proj₂ (FMap T (λ f → OneObj , f) x) ≡⟨ sym (fdistr x) ⟩
             FMap T ( id1 Sets a) x ≡⟨ IsFunctor.identity (isFunctor T) x ⟩
             id1 Sets (FObj T a) x ≡⟨ refl ⟩
             x ∎

-- Someday...
--
-- Monad→Applicative : {l : Level } (m : Monad (Sets {l} ) ) → Applicative ( Monad.T m )
-- Monad→Applicative {l} monad = record {
--         pure = pure
--       ; <*> = _<*>_
--       ; isApplicative = record {
--            identity = identity 
--         ;  composition = composition 
--         ;  homomorphism  = homomorphism 
--         ;  interchange  = interchange 
--      }
--  } where
--          open Monad monad
--          isM = Monoidal.isMonoidal (MonoidalSets  {l} )
--          unit  : FObj T One
--          unit  = TMap η One OneObj 
--          φ    : {a b : Obj Sets} → Hom Sets ((FObj T a) *  (FObj T b )) ( FObj T ( a * b ) )
--          φ {a} {b} (x , y)  =  TMap μ (a * b) (FMap T ( λ f → FMap T ( λ g → ( f , g )) y ) x )
--          open IsMonoidal
--          id : { a : Obj (Sets {l}) } → a → a
--          id x = x
--          fdistr : {a b c : Obj (Sets {l})} → {f : Hom (Sets {l}) b c } {g : Hom (Sets {l} ) a b } → (x : FObj T a) 
--             →  FMap T (λ z → f (g z)) x ≡ FMap T f ( FMap T g x )  
--          fdistr x = IsFunctor.distr (isFunctor T) x 
--          fcong : {b c : Obj (Sets {l})} → {f g : Hom (Sets {l}) b c }  → (x : FObj T b) 
--             →  ((x : b) → f x ≡ g x) →  FMap T f x ≡ FMap T g x
--          fcong x eq = IsFunctor.≈-cong (isFunctor T) eq x
-- 
--          pure  : {a : Obj Sets} → Hom Sets a ( FObj T a )
--          pure {a}  = TMap η a
--          _<*>_   : {a b : Obj Sets} → FObj T ( a → b ) → FObj T a → FObj T b
--          _<*>_ {a} {b} f x = ( NTrans.TMap (Monad.μ monad ) b ) ( (FMap T (λ k → FMap T k x )) f )
--          identity : { a : Obj Sets } { u : FObj T a } → pure ( id1 Sets a )  <*> u ≡ u
--          identity {a} {u} =  ?
--          composition : { a b c : Obj Sets } { u : FObj T ( b → c ) } { v : FObj T (a → b ) } { w : FObj T a }
--              → (( pure _・_ <*> u ) <*> v ) <*> w  ≡ u  <*> (v  <*> w)
--          composition {a} {b} {c} {u} {v} {w} = ?
--          homomorphism : { a b : Obj Sets } { f : Hom Sets a b } { x : a }  → pure f <*> pure x ≡ pure (f x)
--          homomorphism {a} {b} {f} {x} = ?
--          interchange : { a b : Obj Sets } { u : FObj T ( a → b ) } { x : a } → u <*> pure x ≡ pure (λ f → f x) <*> u
--          interchange {a} {b} {u} {x} =  ?
-- 
-- an easy one ( we already have HaskellMonoidal→Applicative )

Monad→Applicative' : {l : Level } (m : Monad (Sets {l} ) ) → Applicative ( Monad.T m )
Monad→Applicative' {l} m =  HaskellMonoidal→Applicative ( Monad.T m ) (  Monad→HaskellMonoidalFunctor m )

-- end
