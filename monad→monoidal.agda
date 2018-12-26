open import Level
open import Category
module monad→monoidal where

open import Data.Product renaming (_×_ to _*_)
open import Category.Constructions.Product
open import HomReasoning
open import cat-utility
open import Relation.Binary.Core
open import Relation.Binary

open Functor
open NTrans

open import monoidal 
open import applicative 
open import Category.Cat
open import Category.Sets
import Relation.Binary.PropositionalEquality

-----
--
--  Monad on Sets implies Applicative and Haskell Monidal Functor
--
--

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
          F = Monad.T monad
          isM = Monoidal.isMonoidal MonoidalSets 
          μ = NTrans.TMap (Monad.μ monad) 
          η = NTrans.TMap (Monad.η monad) 
          unit  : FObj F One
          unit  = η One OneObj 
          φ    : {a b : Obj Sets} → Hom Sets ((FObj F a) *  (FObj F b )) ( FObj F ( a * b ) )
          φ {a} {b} (x , y)  =  ( NTrans.TMap (Monad.μ monad ) (a * b) ) (FMap F ( λ f → FMap F ( λ g → ( f , g )) y ) x )
          open IsMonoidal
          id : { a : Obj (Sets {l}) } → a → a
          id x = x
          natφ' : { a b c d : Obj Sets } { x : FObj F a} { y : FObj F b} { f : a → c } { g : b → d  }
             → FMap F (map f g) (φ (x , y)) ≡ φ (FMap F f x , FMap F g y)
          natφ' {a} {b} {c} {d} {x} {y} {f} {g} = monoidal.≡-cong ( λ h → h x ) ( begin
                ( λ x → (FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) ・ (μ (Σ a (λ k → b))))  ( FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y) x ))
             ≈⟨⟩
                (FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy))  o (μ (Σ a (λ k → b)))) o  FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y)  
             ≈⟨ car {_} {_} {_} {_} {_} {FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y)} ( nat (Monad.μ monad) ) ⟩
                ( μ ( c * d)  o FMap F (FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)))) o  FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y)  
             ≈↑⟨ cdr {_} {_} {_} {_} {_} {μ ( c * d)} ( distr F ) ⟩
                 μ ( c * d)  o FMap F (FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) o  (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y) )
             ≈⟨ cdr {_} {_} {_} {_} {_} {μ ( c * d)} (  begin
                  FMap F (FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) o  (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y) )
                ≈⟨⟩
                  FMap F (λ x₁ → (FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) o (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y)) x₁)
                ≈⟨ fcong F ( extensionality Sets ( λ x₁ →  monoidal.≡-cong ( λ h → h x₁ ) ( begin
                       FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) o (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y )
                    ≈⟨⟩
                        ( λ x₁ → FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) (FMap F (λ g₁ → x₁ , g₁) y) )
                    ≈⟨⟩
                        ( λ x₁ → ( FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy))  o FMap F (λ g₁ → x₁ , g₁) ) y )
                    ≈↑⟨  monoidal.≡-cong ( λ h → λ x₁ →  h x₁ y ) (  extensionality Sets ( λ x₁ →  distr F )) ⟩
                        ( λ x₁ → FMap F (λ g₁ → ( λ xy → f (proj₁ xy) , g (proj₂ xy)) (x₁ , g₁)) y )
                    ≈⟨⟩
                        ( λ x₁ →  FMap F (λ g₁ → f x₁ , g g₁) y )
                    ≈⟨  monoidal.≡-cong ( λ h → λ x₁ →  h x₁ y ) (  extensionality Sets ( λ x₁ →  distr F )) ⟩
                        ( λ x₁ →  ( FMap F (λ g₁ → f x₁ , g₁) o FMap F g ) y )
                    ≈⟨⟩
                        ( λ x₁ →  FMap F (λ g₁ → f x₁ , g₁)    (FMap F g y) )
                    ∎ 
                    ) ) )  ⟩
                  FMap F (λ x₁ → FMap F (λ g₁ → f x₁ , g₁) (FMap F g y))
                ≈⟨⟩
                  FMap F ( (λ f₁ → FMap F (λ g₁ → f₁ , g₁) (FMap F g y)) o f )
                ≈⟨ distr F  ⟩
                  FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) (FMap F g y)) o (FMap F f )
                ∎ 
                ) ⟩
                 μ ( c * d)  o (FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) (FMap F g y)) o (FMap F f ))
             ≈⟨⟩
                ( λ x →  μ  (Σ c (λ x₁ → d)) (FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) (FMap F g y)) (FMap F f x)))
             ∎ ) where
                  open ≈-Reasoning Sets hiding ( _o_ )
          natφ : { a b c d : Obj Sets } { x : FObj F a} { y : FObj F b} { f : a → c } { g : b → d  }
             → FMap F (map f g) (φ (x , y)) ≡ φ (FMap F f x , FMap F g y)
          natφ {a} {b} {c} {d} {x} {y} {f} {g} = begin
                  FMap F (map f g) (φ (x , y))
             ≡⟨⟩ 
                  FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) (μ (Σ a (λ k → b))  (FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y) x))
             ≡⟨⟩ 
                  (FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) ・ (μ (Σ a (λ k → b))))  (FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y) x)
             ≡⟨ ≡-cong ( λ h → h  (FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y) x)  ) (IsNTrans.commute (NTrans.isNTrans  (Monad.μ monad) ))   ⟩ 
               ( μ  (Σ c (λ v → d)) ・ (( FMap F ( FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)))) ・ (FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y)))) x
             ≡⟨  sym (≡-cong ( λ h →   ( μ  (Σ c (λ v → d)) ・  h ) x )   (IsFunctor.distr (Functor.isFunctor F )) )  ⟩ 
                  (μ (Σ c (λ v → d)) ・ FMap F (( FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) ・ (λ f₁ → FMap F (λ g₁ → f₁ , g₁) y) ))) x
             ≡⟨⟩ 
                  μ (Σ c (λ v → d)) (FMap F (λ x₁ → FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) (FMap F (λ g₁ → x₁ , g₁) y)) x)
             ≡⟨⟩ 
                  (μ (Σ c (λ v → d)) ・ (FMap F (λ x₁ → FMap F (λ xy → f (proj₁ xy) , g (proj₂ xy)) (FMap F (λ g₁ → x₁ , g₁) y)))) x
             ≡⟨ sym (  ≡-cong ( λ h → (μ (Σ c (λ v → d)) ・ (FMap F (λ x₁ → ( h x₁ y )))) x ) ( extensionality Sets ( λ x → IsFunctor.distr ( Functor.isFunctor F )   )))  ⟩ 
                  (μ (Σ c (λ v → d)) ・ (FMap F (λ x₁ → FMap F ((λ xy → f (proj₁ xy) , g (proj₂ xy)) ・  (λ g₁ → x₁ , g₁) ) y))) x
             ≡⟨⟩ 
                 μ  (Σ c (λ v → d)) (FMap F (λ x₁ → FMap F (λ x₂ → f x₁ , g x₂) y) x)
             ≡⟨⟩ 
               ( μ  (Σ c (λ v → d)) ・ (FMap F (λ x₁ → FMap F (λ k → f x₁ , g k) y))) x
             ≡⟨⟩ 
                μ  (Σ c (λ x₁ → d)) (FMap F (λ x₁ → FMap F (λ k → f x₁ , g k) y) x)
             ≡⟨⟩ 
                μ  (Σ c (λ x₁ → d)) (FMap F ((λ f₁ → FMap F (λ k → f₁ , g k) y) ・ f) x)
             ≡⟨  ≡-cong ( λ h → μ  (Σ c (λ x₁ → d)) (h x)) ( IsFunctor.distr ( Functor.isFunctor F ))  ⟩ 
                μ  (Σ c (λ x₁ → d)) (((FMap F (λ f₁ → FMap F (λ k → f₁ , g k) y)) ・ (FMap F f)) x)
             ≡⟨⟩ 
                μ  (Σ c (λ x₁ → d)) (FMap F (λ f₁ → FMap F (λ k → f₁ , g k) y) (FMap F f x))
             ≡⟨⟩ 
                  μ  (Σ c (λ x₁ → d)) (FMap F (λ f₁ → FMap F (λ k → ((λ g₁ → f₁ , g₁) (g k))) y) (FMap F f x))
             ≡⟨  ≡-cong ( λ h →  μ  (Σ c (λ x₁ → d)) (FMap F (λ f₁ → h f₁ y ) (FMap F f x ))) ( extensionality Sets ( λ x →  (IsFunctor.distr ( Functor.isFunctor F )  ) )) ⟩ 
                  μ  (Σ c (λ x₁ → d)) (FMap F (λ f₁ → FMap F (λ g₁ → f₁ , g₁) (FMap F g y)) (FMap F f x))
             ≡⟨⟩
                  φ (FMap F f x , FMap F g y)
             ∎ where
                  open Relation.Binary.PropositionalEquality
                  open Relation.Binary.PropositionalEquality.≡-Reasoning
          ≡←≈ :  {a b : Obj (Sets {l}) } { x y : Hom (Sets {l}) a b } →  (x≈y : Sets [ x ≈ y  ]) → x ≡ y
          ≡←≈ refl = refl
          -- fcongλ :  { a b c : Obj (Sets {l} ) } { x y : a → Hom (Sets {l}) a b  }  → Sets [ x ≈ y  ]  → ( g : ? )
          --    →  Sets [ FMap F  ( λ (f : a)  → ( x f ))  ≈  FMap F ( λ (f : a )  → ( y f )) ]
          -- fcongλ {a} {b} {c} {x} {y} g  eq =  let open ≈-Reasoning (Sets {l}) hiding ( _o_ ) in  fcong F ( extensionality Sets (λ f →  monoidal.≡-cong ( λ h → g h f ) eq
          assocφ : { x y z : Obj Sets } { a : FObj F x } { b : FObj F y }{ c : FObj F z }
             → φ (a , φ (b , c)) ≡ FMap F (Iso.≅→ (mα-iso isM)) (φ (φ (a , b) , c))
          assocφ {x} {y} {z} {a} {b} {c} =  monoidal.≡-cong ( λ h → h a ) ( begin
                 ( λ a  →  φ (a , φ (b , c)) )
             ≈⟨⟩
                 ( λ a → μ ( x * ( y * z ) ) (FMap F (λ f → FMap F (λ g → f , g) (μ (y * z ) (FMap F (λ f₁ → FMap F (λ g → f₁ , g) c) b))) a))
             ≈⟨⟩
                  μ ( x * ( y * z ) )  o (FMap F (λ f → ( FMap F (λ g → f , g) o ( μ (y * z ) o  FMap F (λ f₁ → FMap F (λ g → f₁ , g) c ) )) b ))
             ≈⟨⟩ -- assoc
                  μ ( x * ( y * z ) )  o (FMap F (λ f → ( (FMap F (λ g → f , g) o ( μ (y * z ))) o  FMap F (λ f₁ → FMap F (λ g → f₁ , g) c ) ) b ))
             ≈⟨ cdr {_} {_} {_} {_} {_} { μ ( x * ( y * z ) ) } (fcong F (extensionality Sets (λ f →  monoidal.≡-cong ( λ h → h b )
                     ( car {_} {_} {_} {_} {_} { FMap F (λ f₁ → FMap F (λ g → f₁ , g) c )} (nat (Monad.μ monad ))) ) )) ⟩
                  μ ( x * ( y * z ) )  o (FMap F (λ f → ( ( μ ( x * ( y * z ) ) o FMap F (FMap F (λ g → f , g))  ) o  FMap F (λ f₁ → FMap F (λ g → f₁ , g) c ) ) b )) ≈⟨⟩ -- assoc
                  μ ( x * ( y * z ) )  o (FMap F (λ f → (  μ ( x * ( y * z ) ) o ( FMap F (FMap F (λ g → f , g))  o  FMap F (λ f₁ → FMap F (λ g → f₁ , g) c )) ) b ))
             ≈↑⟨ cdr {_} {_} {_} {_} {_} { μ ( x * ( y * z ) ) } (fcong F (extensionality Sets (λ f →  monoidal.≡-cong ( λ h → h b )
                     ( cdr {_} {_} {_} {_} {_} { μ ( x * ( y * z ) )} (distr F)) ) )) ⟩
                  μ ( x * ( y * z ) )  o (FMap F (λ f → (  μ ( x * ( y * z ) ) o ( FMap F (FMap F (λ g → f , g) o (λ f₁ → FMap F (λ g → f₁ , g) c)))) b ))
             ≈⟨⟩
                  μ ( x * ( y * z ) )  o (FMap F (λ f → (  μ ( x * ( y * z ) ) o ( FMap F ((λ f₁ → (FMap F (λ g → f , g) o FMap F (λ g → f₁ , g)) c)))) b ))
             ≈⟨ cdr {_} {_} {_} {_} {_} { μ ( x * ( y * z ) ) } (fcong F (extensionality Sets (λ f →  monoidal.≡-cong ( λ h → h b )  ( begin
                     μ (x * y * z) o FMap F (λ f₁ → (FMap F (λ g → f , g) o FMap F (λ g → f₁ , g)) c)
                  ≈↑⟨ cdr {_} {_} {_} {_} {_} {μ (x * y * z)} ( fcong F ( extensionality Sets (λ f →  monoidal.≡-cong ( λ h → h c ) ( distr F)  ))) ⟩
                     μ (x * y * z) o FMap F (λ f₁ → FMap F ((λ g → f , g) o (λ g → f₁ , g)) c)
                  ∎  
                ) ))) ⟩
                  μ ( x * ( y * z ) )  o (FMap F (λ f → (  μ ( x * ( y * z ) ) o ( FMap F (λ f₁ → (FMap F ((λ g → f , g) o (λ g → f₁ , g))) c))) b ))
             ≈⟨⟩
                  μ ( x * ( y * z ) )  o (FMap F (λ f → (  μ ( x * ( y * z ) ) o ( FMap F (λ g → (FMap F (λ h → f , (g , h))) c))) b ))
             ≈⟨⟩
                  μ ( x * ( y * z ) )  o (FMap F (  μ ( x * ( y * z ) ) o (λ f → ( FMap F (λ g → (FMap F (λ h → f , (g , h))) c)) b )))
             ≈⟨ cdr {_} {_} {_} {_} {_} {μ ( x * ( y * z ) )} ( distr F ) ⟩ -- distr F
                  μ ( x * ( y * z ) )  o (FMap F (  μ ( x * ( y * z ) )) o FMap F (λ f → ( FMap F (λ g → (FMap F (λ h → f , (g , h))) c)) b ))
             ≈⟨⟩ -- assoc
                  ( μ ( x * ( y * z ) )  o FMap F (  μ ( x * ( y * z ) ))) o (FMap F (λ f → ( FMap F (λ g → (FMap F (λ h → f , (g , h))) c)) b ))
             ≈↑⟨ car ( IsMonad.assoc ( Monad.isMonad monad )) ⟩  --- monad assoc
                  ( μ ( x * ( y * z ) )  o  μ ( FObj F (x * ( y * z ) ))) o (FMap F (λ f → ( FMap F (λ g → (FMap F (λ h → f , (g , h))) c)) b ))
             ≈⟨ cdr {_} {_} {_} {_} {_} { μ ( x * ( y * z ) )} ( cdr {_} {_} {_} {_} {_} { μ ( FObj F (x * ( y * z ) ))} ( begin
                     FMap F (λ f → ( FMap F (λ g → (FMap F (λ h → f , (g , h))) c)) b ) 
                  ≈⟨⟩
                     FMap F ( λ h →  ( FMap F (( λ f → ( FMap F (λ x₂ → proj₁ f , proj₂ f , x₂)) c)  o (λ g → h , g))) b  )
                  ≈⟨ fcong F ( extensionality Sets (λ f →  monoidal.≡-cong ( λ h → h b ) (distr F) )) ⟩
                     FMap F ( λ h →  ( FMap F ( λ f → ( FMap F (λ x₂ → proj₁ f , proj₂ f , x₂)) c)  o (FMap F (λ g → h , g))) b  )
                  ≈⟨⟩
                     FMap F ( FMap F ( λ f → ( FMap F (λ x₂ → proj₁ f , proj₂ f , x₂)) c)  o (λ h → FMap F (λ g → h , g) b)  )
                  ≈⟨⟩
                     FMap F ( FMap F ( λ f → ( FMap F ((λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o (λ g → f , g))) c)  o (λ f → FMap F (λ g → f , g) b))
                  ≈⟨ fcong F ( car ( fcong F ( extensionality Sets (λ f →  monoidal.≡-cong ( λ h → h c ) ( distr F ) )))) ⟩
                     FMap F ( FMap F ( λ f → ( FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o FMap F (λ g → f , g)) c)  o (λ f → FMap F (λ g → f , g) b)  )
                  ≈⟨⟩
                     FMap F ( FMap F (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o (λ f → FMap F (λ g → f , g) c))  o (λ f → FMap F (λ g → f , g) b)  )
                  ≈⟨ distr F ⟩
                     FMap F ( FMap F (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o (λ f → FMap F (λ g → f , g) c)) ) o (FMap F (λ f → FMap F (λ g → f , g) b)  )
                  ∎  
               ))  ⟩
                  ( μ ( x * ( y * z ))   o μ ( FObj F (x * ( y * z ))))
                            o ( FMap F ( FMap F (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o (λ f → FMap F (λ g → f , g) c)) ) o (FMap F (λ f → FMap F (λ g → f , g) b) ) )
             ≈⟨⟩ -- assoc
                  μ ( x * ( y * z ))   o ( μ ( FObj F (x * ( y * z )))
                            o ( FMap F ( FMap F (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o (λ f → FMap F (λ g → f , g) c)) ) o (FMap F (λ f → FMap F (λ g → f , g) b) ) ))
             ≈⟨⟩ -- assoc 
                  μ ( x * ( y * z ))   o (( μ ( FObj F (x * ( y * z )))  o FMap F (FMap F (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o
                      (λ f → FMap F (λ g → f , g) c)) ) ) o (FMap F (λ f → FMap F (λ g → f , g) b) ))
             ≈↑⟨ cdr {_} {_} {_} {_} {_} {μ ( x * ( y * z ))} (car ( nat (Monad.μ monad ))) ⟩
                  μ ( x * ( y * z ))   o (( FMap F (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o 
                      (λ f → FMap F (λ g → f , g) c))  o μ (x * y ) ) o (FMap F (λ f → FMap F (λ g → f , g) b) ))
             ≈⟨⟩ --- assoc
                  μ ( x * ( y * z ))   o ( FMap F (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o 
                      (λ f → FMap F (λ g → f , g) c))  o (μ (x * y )  o (FMap F (λ f → FMap F (λ g → f , g) b) )))
             ≈⟨ cdr {_} {_} {_} {_} {_} {μ ( x * ( y * z ))} ( car ( distr F )) ⟩ 
                  μ ( x * ( y * z ))   o (( FMap F (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc) ) o 
                      FMap F (λ f → FMap F (λ g → f , g) c))  o (μ (x * y )  o (FMap F (λ f → FMap F (λ g → f , g) b) )))
             ≈⟨⟩ -- assoc
                  μ ( x * ( y * z ))   o (( FMap F (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc) )) o 
                      (FMap F (λ f → FMap F (λ g → f , g) c)  o (μ (x * y )  o (FMap F (λ f → FMap F (λ g → f , g) b) ))))
             ≈⟨⟩ -- assoc
                 ( μ ( x * ( y * z ))   o (FMap F (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc) ))) o 
                      (FMap F (λ f → FMap F (λ g → f , g) c)  o (μ (x * y )  o (FMap F (λ f → FMap F (λ g → f , g) b) )))
             ≈↑⟨ car ( nat ( Monad.μ monad ) ) ⟩  
                 (FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o μ ( ( x * y ) * z ))  o
                      (FMap F (λ f → FMap F (λ g → f , g) c)  o (μ (x * y )  o (FMap F (λ f → FMap F (λ g → f , g) b) )))
             ≈⟨⟩ 
                 FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)  o
                    (μ ( ( x * y ) * z )  o  (FMap F (λ f → FMap F (λ g → f , g) c)  o (μ (x * y )  o (FMap F (λ f → FMap F (λ g → f , g) b) ))))
             ≈⟨⟩
                 ( λ a → FMap F (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)
                    (μ ( ( x * y ) * z ) (FMap F (λ f → FMap F (λ g → f , g) c) (μ (x * y ) (FMap F (λ f → FMap F (λ g → f , g) b) a)))))
             ≈⟨⟩
                 ( λ a  → FMap F (Iso.≅→ (mα-iso isM)) (φ (φ (a , b) , c)) )
             ∎ ) where
                  open ≈-Reasoning Sets hiding ( _o_ )
          proj1 :  {a : Obj Sets} → _*_ {l} {l} a One → a
          proj1 =  proj₁
          proj2 :  {a : Obj Sets} → _*_ {l} {l} One a → a
          proj2 =  proj₂
          idrφ : {a : Obj Sets } { x : FObj F a } → FMap F (Iso.≅→ (mρ-iso isM)) (φ (x , unit)) ≡ x
          idrφ {a} {x} =  monoidal.≡-cong ( λ h → h x ) ( begin
                  ( λ x → FMap F (Iso.≅→ (mρ-iso isM)) (φ (x , unit)) )
             ≈⟨⟩
                  ( λ x → FMap F proj₁ (μ (a * One) (FMap F (λ f → FMap F (λ g → f , g) (η  One OneObj)) x)) )
             ≈⟨⟩
                  FMap F proj₁ o  (μ (a * One ) o FMap F (λ f → ( FMap F (λ g → f , g) ((η One) OneObj))))
             ≈⟨⟩
                  FMap F proj₁ o  (μ (a * One ) o FMap F (λ f → ( FMap F (λ g → f , g) o η One ) OneObj ))
             ≈⟨ cdr {_} {_} {_} {_} {_} {FMap F  proj₁} ( cdr {_} {_} {_} {_} {_} {μ (a * One ) } ( fcong F  ( begin
                   (λ f → ( FMap F (λ g → f , g) o η One ) OneObj )
                 ≈⟨  monoidal.≡-cong ( λ h →  λ f → (h f) OneObj ) (extensionality Sets (λ f → (
                      begin
                         FMap F (λ g → f , g) o η One 
                      ≈⟨ nat ( Monad.η monad ) ⟩
                          η  ( a * One) o FMap (identityFunctor {_} {_} {_} {Sets {l}} )(λ g → f , g) 
                      ≈⟨⟩
                         η (a * One) o ( λ g → ( f , g ) )
                      ∎   
                    ))) ⟩
                   (λ f → ( η (a * One) o ( λ g → ( f , g ) ) ) OneObj )
                 ≈⟨⟩
                     η (a * One  ) o ( λ f → ( f , OneObj  ) )
                 ∎
                ))) ⟩
                  FMap F proj₁ o  (μ (a * One ) o FMap F ( η (a * One  ) o ( λ f → ( f , OneObj  ))))
             ≈⟨ cdr {_} {_} {_} {_} {_} {FMap F proj₁} ( cdr {_} {_} {_} {_} {_} {μ (a * One )} ( distr F )) ⟩
                  FMap F proj1 o  (μ (a * One ) o ( FMap F ( η (a * One  )) o FMap F ( λ f → ( f , OneObj  ))))
             ≈⟨⟩
                  FMap F proj1 o  ( ( μ (a * One ) o  FMap F ( η (a * One  ))) o FMap F ( λ f → ( f , OneObj  )))
             ≈⟨ cdr {_} {_} {_} {_} {_} {FMap F proj₁} ( car ( IsMonad.unity2 (Monad.isMonad monad )))   ⟩
                  FMap F proj₁ o  ( id1 Sets (FObj F (a * One)) o FMap F ( λ f → ( f , OneObj  )))
             ≈⟨ cdr {_} {_} {_} {_} {_} {FMap F proj₁} idL ⟩
                  FMap F proj₁ o   FMap F ( λ f → ( f , OneObj  ))
             ≈↑⟨ distr F  ⟩
                  FMap F (proj1 o   ( λ f → ( f , OneObj  )))
             ≈⟨⟩
                  FMap F (id1 Sets a )
             ≈⟨ IsFunctor.identity ( Functor.isFunctor F ) ⟩
                 id1 Sets (FObj F a)
             ∎ ) where
                  open ≈-Reasoning Sets hiding ( _o_ )
          idlφ : {a : Obj Sets } { x : FObj F a } → FMap F (Iso.≅→ (mλ-iso isM)) (φ (unit , x)) ≡ x
          idlφ {a} {x} =  monoidal.≡-cong ( λ h → h x ) ( begin
                 ( λ x → FMap F (Iso.≅→ (mλ-iso isM)) (φ (unit , x)) )
             ≈⟨⟩
                 ( λ x → FMap F proj₂ (μ (One * a ) (FMap F (λ f → FMap F (λ g → f , g) x) (η  One OneObj))))
             ≈⟨⟩
                 ( λ x → ( FMap F proj₂ o (μ (One * a ) o  (FMap F (λ f → FMap F (λ g → f , g) x) o  η  One) )) OneObj )
             ≈⟨ monoidal.≡-cong ( λ h →  λ x → ( FMap F proj₂ o (μ (One * a ) o h x )) OneObj ) ( extensionality (Sets {l}) ( λ x →  nat (Monad.η monad  )  ))   ⟩
                  (λ x → (FMap F proj2 o (μ (One * a) o (η (FObj F (One * a)) o FMap (identityFunctor {_} {_} {_} {Sets {l}} ) (λ f → FMap F (λ g → f , g) x) ))) OneObj)
             ≈⟨⟩
                 FMap F proj2 o (μ (One * a ) o  (η (FObj F (One * a)) o ( FMap F (λ g → (OneObj , g )) )))
             ≈⟨ cdr {_} {_} {_} {_} {_} {FMap F proj2} ( assoc {_} {_} {_} {_} {μ (One * a )} {η (FObj F (One * a))} { FMap F (λ g → (OneObj , g )) } ) ⟩
                 FMap F proj₂ o (( μ (One * a ) o  η (FObj F (One * a))) o  FMap F (λ g → (OneObj , g )) )
             ≈⟨ cdr {_} {_} {_} {_} {_} {FMap F proj2} ( car {_} {_} {_} {_} {_} { FMap F (λ g → (OneObj , g ))} (  IsMonad.unity1 (Monad.isMonad monad )) )   ⟩
                 FMap F proj₂ o (id1 Sets (FObj F (One * a)) o  FMap F (λ g → (OneObj , g )) )
             ≈⟨ cdr {_} {_} {_} {_} {_} {FMap F proj2} ( idL ) ⟩
                 FMap F proj₂ o  FMap F (λ g → (OneObj , g ) )
             ≈↑⟨ distr F ⟩
                 FMap F ( proj2 o  (λ g → (OneObj , g ) ))
             ≈⟨⟩
                  FMap F (id1 Sets a )
             ≈⟨ IsFunctor.identity ( Functor.isFunctor F ) ⟩
                 id1 Sets (FObj F a)
             ∎ ) where
                  open ≈-Reasoning Sets hiding ( _o_ )

Monad→Applicative : {l : Level } (m : Monad (Sets {l} ) ) → Applicative ( Monad.T m )
Monad→Applicative {l} monad = record {
         pure = pure
       ; <*> = _<*>_
       ; isApplicative = record {
            identity = identity 
         ;  composition = composition 
         ;  homomorphism  = homomorphism 
         ;  interchange  = interchange 
      }
  } where
          F = Monad.T monad
          isM = Monoidal.isMonoidal ( MonoidalSets {l} )
          η = NTrans.TMap (Monad.η monad ) 
          μ = NTrans.TMap (Monad.μ monad) 
          pure  : {a : Obj Sets} → Hom Sets a ( FObj F a )
          pure {a}  = η a
          _<*>_   : {a b : Obj Sets} → FObj F ( a → b ) → FObj F a → FObj F b
          _<*>_ {a} {b} f x = ( NTrans.TMap (Monad.μ monad ) b ) ( (FMap F (λ k → FMap F k x )) f )
          open IsMonoidal
          id : { a : Obj (Sets {l}) } → a → a
          id x = x
          left : {n : Level} { a b : Set n} → { x y : a → b } { h : a }  → ( x ≡ y ) → x h ≡ y h
          left {_} {_} {_} {_} {_} {h} eq = ≡-cong ( λ k → k h ) eq 
          ≡cong = Relation.Binary.PropositionalEquality.cong
          identity : { a : Obj Sets } { u : FObj F a } → pure ( id1 Sets a )  <*> u ≡ u
          identity {a} {u} =  ≡cong ( λ h → h u ) ( begin
                 (  λ u →  pure ( id1 Sets a )  <*> u )
             ≈⟨⟩
                 ( λ u → μ  a (FMap F (λ k → FMap F k u) (η (a → a) (λ x → x)))) 
             ≈⟨⟩
                 (λ u → μ a ((FMap F (λ k → FMap F k u) o η (a → a)) (id1 Sets a ))) 
             ≈⟨ ≡cong ( λ h → λ u → μ a (h u (id1 Sets a) ) ) ( extensionality Sets ( λ x → (IsNTrans.commute (NTrans.isNTrans  (Monad.η monad ) )))) ⟩
                 (λ u → μ a ( (η (FObj F a) o FMap F (  (id1 Sets a )) ) u )  ) 
             ≈⟨⟩
                 μ a o (η (FObj F a) o FMap F (id1 Sets a))  
             ≈⟨ ≡cong ( λ h →  (λ u → μ a ( ( η (FObj F a) o  h)  u ))) (IsFunctor.identity (Functor.isFunctor F ))   ⟩ -- cdr cdr
                 μ a o (η (FObj F a) o id1 Sets (FObj F a))  
             ≈⟨ ≡cong ( λ h →  (λ u → μ a ( h  u ))) idR ⟩  -- cdr idR
                 μ  a o η  (FObj F a) 
             ≈⟨ IsMonad.unity1 (Monad.isMonad monad )   ⟩
                 id1 Sets (FObj F a) 
             ≈⟨⟩
                 ( λ u →  u )
             ∎ ) 
             where
                  open ≈-Reasoning Sets hiding ( _o_ )
          composition : { a b c : Obj Sets } { u : FObj F ( b → c ) } { v : FObj F (a → b ) } { w : FObj F a }
              → (( pure _・_ <*> u ) <*> v ) <*> w  ≡ u  <*> (v  <*> w)
          composition {a} {b} {c} {u} {v} {w} = ≡cong ( λ h → h w ) ( begin 
                 ( λ w →  (( pure _・_ <*> u ) <*> v ) <*> w  )
             ≈⟨⟩ 
                 ( λ w → μ c (FMap F (λ k → FMap F k w) (μ (a → c) (FMap F (λ k → FMap F k v)
                   (μ ((a → b) → a → c) (FMap F (λ k → FMap F k u) (η ((b → c) → (a → b) → a → c) (λ f g x → f (g x)))))))))
             ≈⟨⟩ 
                 ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o ( FMap F (λ k → FMap F k v)  o (
                        μ ((a → b) → a → c)  o  (FMap F (λ k → FMap F k u)  o η ((b → c) → (a → b) → a → c))
                     ) ) ) ) ) (λ f g x → f (g x))  )
             ≈⟨  ≡cong ( λ h → ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o ( FMap F (λ k → FMap F k v)  o ( μ ((a → b) → a → c)  o  h ) ) ) ) ) (λ f g x → f (g x))  )) (nat ( Monad.η monad))  ⟩ 
                 ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o ( FMap F (λ k → FMap F k v)  o (
                        μ ((a → b) → a → c)  o  (η (FObj F ((a → b) → a → c)) o (λ k → FMap F k u)   )
                     ) ) ) ) ) (λ f g x → f (g x))  )
             ≈⟨⟩ -- assoc
                 ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o ( FMap F (λ k → FMap F k v)  o (
                        ( μ ((a → b) → a → c)  o  η (FObj F ((a → b) → a → c)) ) o (λ k → FMap F k u)   
                     ) ) ) ) ) (λ f g x → f (g x))  )
             ≈⟨   ≡cong ( λ h → ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o ( FMap F (λ k → FMap F k v)  o ( h   o (λ k → FMap F k u) ) ) ) ) ) (λ f g x → f (g x))  ) ) ( IsMonad.unity1 ( Monad.isMonad monad  ))  ⟩ 
                 ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o ( FMap F (λ k → FMap F k v)  o (
                        id1 Sets (FObj (Monad.T monad) ((a → b) → a → c))  o (λ k → FMap F k u)   
                     ) ) ) ) ) (λ f g x → f (g x))  )
             ≈⟨  ≡cong ( λ h →  ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o ( FMap F (λ k → FMap F k v)  o  h  ) ) ) ) (λ f g x → f (g x))  )) (idL {_} {_} {λ k → FMap F k u} )  ⟩ 
                 ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o ( FMap F (λ k → FMap F k v)  o (
                         λ k → FMap F k u   
                     ) ) ) ) ) (λ f g x → f (g x))  )
             ≈⟨⟩ 
                 ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o (  λ j → ( FMap F (λ k → FMap F k v)  o  FMap F j ) u ))))  (λ f g x → f (g x))  )
             ≈↑⟨    ≡cong ( λ h →  ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o (  λ j → h u ))))  (λ (f : (b → c) ) (g : (a → b))  (x : a ) → f (g x)) )) (distr F )  ⟩
                 ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o (  λ j → ( FMap F (( λ k → FMap F k v)  o   j ) u )))))  (λ f g x → f (g x))  )
             ≈⟨⟩
                 ( λ w → ( μ c o (FMap F (λ k → FMap F k w) o ( μ (a → c) o ( FMap F ((λ k → FMap F k v) o (λ f g x → f (g x)) ))   ))) u )
             ≈⟨⟩
                 ( λ w → ( μ c o ((FMap F (λ k → FMap F k w) o  μ (a → c) ) o ( FMap F ((λ k → FMap F k v) o (λ f g x → f (g x)) ))))  u )
             ≈⟨ extensionality Sets (λ w →  ( ≡cong ( λ h →  h u ) (cdr {_} {_} {_} {_} {_} {μ c} ( car {_} {_} {_} {_} {_} { FMap F ((λ k → FMap F k v) o (λ f g x → f (g x)))}  (nat (Monad.μ monad)) )))) ⟩  
                 ( λ w → ( μ c o ((μ (FObj F c)  o FMap F (FMap F (λ k → FMap F k w) ) ) o ( FMap F ((λ k → FMap F k v) o (λ f g x → f (g x)) ))))  u )
             ≈⟨⟩ -- assoc 
                 ( λ w → ( μ c o (μ (FObj F c)  o ( FMap F (FMap F (λ k → FMap F k w) )  o ( FMap F ((λ k → FMap F k v) o (λ f g x → f (g x)) )))))  u )
             ≈↑⟨   extensionality Sets (λ w →  ( ≡cong ( λ h →  h u ) (cdr {_} {_} {_} {_} {_} { μ c} (cdr {_} {_} {_} {_} {_} {μ (FObj F c)} ( distr F ))))) ⟩
                 ( λ w → ( μ c o (μ (FObj F c)  o ( FMap F (FMap F (λ k → FMap F k w)  o ((λ k → FMap F k v) o (λ f g x → f (g x)) )))))  u )
             ≈⟨⟩
                 ( λ w → (( μ c o μ (FObj F c) ) o ( FMap F (FMap F (λ k → FMap F k w)  o ((λ k → FMap F k v) o (λ f g x → f (g x)) ))    ))  u )
             ≈⟨   extensionality Sets (λ w →  ( ≡cong ( λ h →  h u ) (car {_} {_} {_} {_} {_} {( FMap F (FMap F (λ k → FMap F k w)  o ((λ k → FMap F k v) o (λ f g x → f (g x)) )) )}  (IsMonad.assoc (Monad.isMonad monad ))  )   )) ⟩
                 ( λ w → (( μ c o (FMap F ( μ c )) ) o ( FMap F (FMap F (λ k → FMap F k w)  o ((λ k → FMap F k v) o (λ f g x → f (g x)) ))    ))  u )
             ≈⟨⟩
                 ( λ w → ( μ c o (FMap F ( μ c ) o ( FMap F (FMap F (λ k → FMap F k w)  o ((λ k → FMap F k v) o (λ f g x → f (g x)) )) )))    u )
             ≈↑⟨ extensionality Sets (λ w →  ( ≡cong ( λ h → ( μ c o h) u ) (distr F) ))  ⟩
                 ( λ w → ( μ c o (FMap F ( μ c  o (FMap F (λ k → FMap F k w)  o ((λ k → FMap F k v) o (λ f g x → f (g x)) )) )))   u )
             ≈⟨⟩
                 ( λ w → ( μ c o (FMap F (λ x →  ( μ c  o (FMap F (λ k → FMap F k w)  o (FMap F (λ g x₁ → x (g x₁))))) v ))) u )
             ≈⟨  extensionality Sets (λ w → ( ≡cong ( λ h →  ( μ c o h ) u ) (fcong F (  extensionality Sets (λ k →  ≡cong ( λ h → h v ) ( begin
                      μ c  o (FMap F (λ x → FMap F x w)  o (FMap F (λ g x₁ → k (g x₁))))
                  ≈↑⟨ cdr {_} {_} {_} {_} {_} {μ c} ( distr F ) ⟩
                      μ c  o (FMap F ((λ x → FMap F x w)  o (λ g x₁ → k (g x₁))))
                  ≈⟨⟩ 
                      μ c  o (FMap F ((λ x → (FMap F ( k o  x ) w))))
                  ≈⟨ cdr {_} {_} {_} {_} {_} {μ c}  ( fcong F ( extensionality Sets ( λ x →  ≡cong ( λ h → h w ) (distr F ) )))  ⟩ 
                      μ c  o (FMap F ((λ x → (FMap F k  o  FMap F x ) w)))
                  ≈⟨⟩ 
                      μ c  o (FMap F (FMap F k  o (λ h → FMap F h w))) 
                  ≈⟨ cdr {_} {_} {_} {_} {_} {μ c} ( distr F ) ⟩ 
                       μ c o ( FMap F (FMap F k ) o FMap F  (λ h → FMap F h w))
                  ≈⟨⟩ 
                       ( μ c o FMap F (FMap F k )) o FMap F  (λ h → FMap F h w)
                  ≈↑⟨ car {_} {_} {_} {_} {_} {FMap F  (λ h → FMap F h w)} (nat ( Monad.μ monad ))  ⟩
                      ((( FMap F k o  μ b ) o FMap F  (λ h → FMap F h w))          )
                  ∎ ) 
                )))))  ⟩ 
                 ( λ w → ( μ c o (FMap F (λ k →  ( FMap F k o ( μ b  o FMap F  (λ h → FMap F h w))            ) v ))) u ) 
             ≈⟨⟩ 
                 ( λ w → μ c (FMap F (λ k → FMap F k (μ b (FMap F (λ h → FMap F h w) v))) u) )
             ≈⟨⟩ 
                 ( λ w →  u <*> (v <*> w) )
             ∎ ) 
             where
                  open ≈-Reasoning Sets hiding ( _o_ )
          homomorphism : { a b : Obj Sets } { f : Hom Sets a b } { x : a }  → pure f <*> pure x ≡ pure (f x)
          homomorphism {a} {b} {f} {x} = ≡cong ( λ h → h x ) ( begin
                 ( λ x →  pure f <*> pure x )
             ≈⟨⟩
                 ( λ x → μ  b (FMap F (λ k → FMap F k (η  a x)) ((η  (a → b) f)) ))
             ≈⟨⟩
                 μ b o ( λ x → (FMap F ( λ k → FMap F k (η  a x)  ) o η (a → b) ) f )
             ≈⟨  cdr {_} {_} {_} {_} {_} {μ b} ( extensionality Sets ( λ x →  ≡cong ( λ h → h f ) ( nat ( Monad.η monad ) ))) ⟩
                 μ b o ( λ x → (η (FObj F b) o (λ k → FMap F k (η  a x)) ) f )
             ≈⟨⟩
                 μ b o (η (FObj F b) o (FMap F f o η  a ))
             ≈⟨⟩
                (μ b o η (FObj F b)) o (FMap F f o η  a )
             ≈⟨  car ( IsMonad.unity1 ( Monad.isMonad monad ))  ⟩
                id1 Sets (FObj F b ) o (FMap F f o η  a )
             ≈⟨  idL ⟩
                FMap F f o η a 
             ≈⟨  nat ( Monad.η monad )   ⟩
                η b o  f 
             ≈⟨⟩
                 ( λ x → η  b (f x) )
             ≈⟨⟩
                 ( λ x →  pure (f x ))
             ∎ )
             where
                  open ≈-Reasoning Sets hiding ( _o_ )
          interchange : { a b : Obj Sets } { u : FObj F ( a → b ) } { x : a } → u <*> pure x ≡ pure (λ f → f x) <*> u
          interchange {a} {b} {u} {x} =  ≡cong ( λ h → h x ) ( begin
                 ( λ x →  u <*> pure x )
             ≈⟨⟩
                 ( λ x → μ  b (FMap F (λ k → FMap F k (η  a x)) u)) 
             ≈⟨⟩
                 ( λ x → (μ b o (FMap F (λ k → (FMap F k o η  a) x))) u )
             ≈⟨  extensionality Sets ( λ x → ≡cong ( λ h → ( μ b o h) u ) (fcong F (  extensionality Sets ( λ k →  ≡cong ( λ h → h x ) ( nat ( Monad.η monad ))))))  ⟩
                 ( λ x → (μ b o FMap F (λ k → (η b o k ) x)) u )
             ≈⟨⟩
                  (λ x → (μ b o FMap F ( η b o (λ f → f x) )) u) 
             ≈↑⟨  extensionality Sets ( λ x → ≡cong ( λ h → ( μ b o h) u ) ( fcong F (nat ( Monad.η monad ) )))  ⟩
                  (λ x → (μ b o FMap F ( FMap F (λ f → f x) o η (a → b) )) u) 
             ≈⟨  extensionality Sets ( λ x → ≡cong ( λ h → ( μ b o h) u ) ( distr F ) ) ⟩
                 ( λ x → (μ b o ( FMap F ( FMap F   (λ f → f x) )   o FMap F ( η (a → b) ))) u )
             ≈⟨⟩
                 ( λ x → ( (μ b o (FMap F ( FMap F   (λ f → f x) )) )  o FMap F ( η (a → b) )) u )
             ≈↑⟨ extensionality Sets ( λ x → ≡cong ( λ h → ( h  o FMap F ( η (a → b) )) u ) ( nat ( Monad.μ monad )))  ⟩
                 ( λ x → ((FMap F  (λ f → f x) o (μ (a → b) o FMap F ( η (a → b) )))) u )
             ≈⟨ extensionality Sets ( λ x → ≡cong ( λ h → (FMap F  (λ f → f x) o h ) u ) ( IsMonad.unity2 ( Monad.isMonad monad ) ))  ⟩
                 ( λ x → ((FMap F (λ f → f x) o id1 Sets (FObj F (a → b)))) u )
             ≈⟨ extensionality Sets ( λ x → ≡cong ( λ h → h u ) ( idR {_} {_} {FMap F (λ f → f x)} ))  ⟩
                 ( λ x → ( FMap F (λ f → f x) ) u )
             ≈↑⟨ extensionality Sets ( λ x → ≡cong ( λ h → h u ) ( idL {_} {_} { FMap F (λ f → f x) }) )  ⟩
                 ( λ x → (id1 Sets (FObj F b ) o  FMap F (λ f → f x) ) u )
             ≈↑⟨ extensionality Sets ( λ x → ≡cong ( λ h → (h  o  FMap F (λ f → f x)  ) u ) ( IsMonad.unity1 ( Monad.isMonad monad ) ))  ⟩
                 ( λ x → (( μ b o  η (FObj F b )) o  FMap F (λ f → f x) ) u )
             ≈⟨⟩
                 ( λ x → ( μ b o ( η (FObj F b ) o  FMap F (λ f → f x)))  u )
             ≈⟨⟩
                 ( λ x → ( μ b o ( η (FObj F b ) o  (λ k → FMap F k u)   )) (λ f → f x) )
             ≈↑⟨ extensionality Sets ( λ x → ≡cong ( λ h → ( μ b o h ) (λ f → f x) ) ( nat ( Monad.η monad )))  ⟩
                 ( λ x → ( μ b o ((FMap F (λ k → FMap F k u) ) o η ((f : a → b) → b))) (λ f → f x) )
             ≈⟨⟩
                 ( λ x → (( μ b o (FMap F (λ k → FMap F k u) )) o η ((f : a → b) → b)) (λ f → f x) )
             ≈⟨⟩
                 ( λ x → μ  b (FMap F (λ k → FMap F k u) (η  ((f : a → b) → b) (λ f → f x))) )
             ≈⟨⟩
                 ( λ x →   pure (λ f → f x) <*> u )
             ∎ )
             where
                  open ≈-Reasoning Sets hiding ( _o_ )

-- an easy one ( we already have HaskellMonoidal→Applicative )

Monad→Applicative' : {l : Level } (m : Monad (Sets {l} ) ) → Applicative ( Monad.T m )
Monad→Applicative' {l} m =  HaskellMonoidal→Applicative ( Monad.T m ) (  Monad→HaskellMonoidalFunctor m )

-- end
