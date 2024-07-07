{-# OPTIONS --cubical-compatible --safe #-}

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Algebra
open import Level
open import Category.Sets
module monoid-monad {c : Level} where

open import Algebra.Structures
open import HomReasoning 
open import Definitions
open import Category.Cat
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary

-- open Monoid
-- open import Algebra.FunctionProperties using (Op₁; Op₂)

open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym )


record ≡-Monoid c : Set (suc c) where
  infixl 7 _*_
  field
    Carrier  : Set c
    _*_      : Op₂ Carrier
    ε        : Carrier   -- id in Monoid
    isMonoid : IsMonoid _≡_ _*_ ε

module _ (M : ≡-Monoid c) where

    open ≡-Monoid

    infixl 7 _∙_

    _∙_   : ( m m' : Carrier M ) → Carrier M
    _∙_ m m' = _*_ M m m'

    A = Sets {c}

    -- T : A → (M x A)

    T : Functor A A
    T = record {
            FObj = λ a → (Carrier M) × a
            ; FMap = λ f p → (proj₁ p , f (proj₂ p )) 
            ; isFunctor = record {
                 identity = IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory Sets ))
                 ; distr = (IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory Sets )))
                 ; ≈-cong = λ f≈g x → cong (λ k → proj₁ x , k ) (f≈g (proj₂ x))
            } 
        } 

    open Functor

    Lemma-MM1 :  {a b : Obj A} {f : Hom A a b} →
            A [ A [ FMap T f o (λ x → ε M , x) ] ≈
            A [ (λ x → ε M , x) o f ] ]
    Lemma-MM1 {a} {b} {f} = let open ≈-Reasoning A in 
            begin
                 FMap T f o (λ x → ε M , x)
            ≈⟨⟩
                 (λ x → ε M , x) o f
            ∎

    -- η : a → (ε,a)
    η : NTrans  A A identityFunctor T
    η = record {
           TMap = λ a → λ(x : a) → ( ε M , x ) ;
           isNTrans = record {
                commute = Lemma-MM1
           }
      }

    -- μ : (m,(m',a)) → (m*m,a)

    muMap : (a : Obj A  ) → FObj T ( FObj T a ) → Σ (Carrier M) (λ x → a )
    muMap a ( m , ( m' , x ) ) = ( m ∙ m' ,  x )

    Lemma-MM2 :  {a b : Obj A} {f : Hom A a b} →
            A [ A [ FMap T f o (λ x → muMap a x) ] ≈
            A [ (λ x → muMap b x) o FMap (T ○ T) f ] ]
    Lemma-MM2 {a} {b} {f} =  let open ≈-Reasoning A in
            begin
                 FMap T f o (λ x → muMap a x)
            ≈⟨⟩
                 (λ x → muMap b x) o FMap (T ○ T) f
            ∎

    μ : NTrans  A A ( T ○ T ) T
    μ = record {
           TMap = λ a → λ x  → muMap a x ; 
           isNTrans = record {
                commute = λ{a} {b} {f} → Lemma-MM2 {a} {b} {f}
           }
      }

    open NTrans

    Lemma-MM33 : {a : Level} {b : Level} {A : Set a} {B : A → Set b}  {x :  Σ A B } →  (((proj₁ x) , proj₂ x ) ≡ x )
    Lemma-MM33 =  _≡_.refl

    Lemma-MM34 : ∀( x : Carrier M  ) → ε M ∙ x ≡ x  
    Lemma-MM34  x = (( proj₁ ( IsMonoid.identity ( isMonoid M )) ) x )

    Lemma-MM35 : ∀( x : Carrier M  ) → x ∙ ε M ≡ x
    Lemma-MM35  x = ( proj₂  ( IsMonoid.identity ( isMonoid M )) ) x

    Lemma-MM36 : ∀( x y z : Carrier M ) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z ) 
    Lemma-MM36  x y z = ( IsMonoid.assoc ( isMonoid M ))  x y z

    import Relation.Binary.PropositionalEquality


    MonoidMonad : Monad A 
    MonoidMonad = record {
           T = T 
         ; η = η 
         ; μ = μ 
         ; isMonad = record {
               unity1 = λ {a} x → Lemma-MM3 x ;
               unity2 = Lemma-MM4 ;
               assoc  = Lemma-MM5 
           }  
       } where
           Lemma-MM3 : {a : Obj A} → A [ A [ TMap μ a o TMap η ( FObj T a ) ] ≈ Id {_} {_} {_} {A} (FObj T a) ]
           Lemma-MM3 {a} x = let open ≡-Reasoning in
                    begin
                        (Sets [ TMap μ a o TMap η ( FObj T a ) ]) x
                    ≡⟨⟩
                        ε M ∙ (proj₁ x) , proj₂ x 
                    ≡⟨ cong (λ k → (k , proj₂ x)) ( Lemma-MM34 (proj₁ x) ) ⟩
                        ( (proj₁ x) , proj₂ x )
                    ≡⟨⟩
                        x 
                    ≡⟨⟩
                       Id {_} {_} {_} {A} (FObj T a) x
                    ∎
           Lemma-MM4 : {a : Obj A} → A [ A [ TMap μ a o (FMap T (TMap η a ))] ≈ Id {_} {_} {_} {A} (FObj T a) ]
           Lemma-MM4 {a} x = let open ≡-Reasoning in
                    begin
                        (Sets [ TMap μ a o (FMap T (TMap η a ))] ) x
                    ≡⟨⟩
                        proj₁ x ∙ (ε M) , proj₂ x
                    ≡⟨  cong (λ k → (k , proj₂ x)) ( Lemma-MM35 (proj₁ x) ) ⟩
                        ((proj₁ x) , proj₂ x )
                    ≡⟨⟩
                        x
                    ≡⟨⟩
                        Id {_} {_} {_} {A} (FObj T a) x
                    ∎
           Lemma-MM5 : {a : Obj A} → A [ A [ TMap μ a o TMap μ ( FObj T a ) ] ≈  A [  TMap μ a o FMap T (TMap μ a) ] ]
           Lemma-MM5 {a} x = let open ≡-Reasoning  in
                    begin
                        (Sets [ TMap μ a o TMap μ ( FObj T a ) ])  x
                    ≡⟨⟩
                       (muMap a ( muMap (Carrier M × a) x )) 
                    ≡⟨ cong₂ (λ j k → ( j , k )) (Lemma-MM36 _ _ _ ) refl ⟩
                        muMap a (proj₁ x , muMap a (proj₂ x))
                    ≡⟨⟩
                        (Sets [ TMap μ a o FMap T (TMap μ a)]) x
                    ∎


    F  : (m : Carrier M) → { a b : Obj A } → ( f : a → b ) → Hom A a ( FObj T b )
    F m {a} {b} f =  λ (x : a ) → ( m , ( f x) )

    -- postulate m m' : Carrier M
    -- postulate a b c' : Obj A 
    -- postulate f :  b → c'
    -- postulate g :  a → b

    -- Lemma-MM12 =  Monad.join MonoidMonad (F m f) (F m' g)

    open import kleisli {_} {_} {_} {A} {T} {η} {μ} {Monad.isMonad MonoidMonad}

    -- nat-ε   TMap = λ a₁ → record { KMap = λ x → x }
    -- nat-η   TMap = λ a₁ → _,_ (ε,  M)
    -- U_T     Functor Kleisli A
    -- U_T     FObj = λ B → Σ (Carrier M) (λ x → B)     FMap = λ {a₁} {b₁} f₁ x → ( proj₁ x ∙ (proj₁ (KMap f₁ (proj₂ x)))  , proj₂ (KMap f₁ (proj₂ x))
    -- F_T     Functor A Kleisli 
    -- F_T     FObj = λ a₁ → a₁                         FMap = λ {a₁} {b₁} f₁ → record { KMap = λ x → ε M , f₁ x }

