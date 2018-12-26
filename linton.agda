open import Level
open import Category
open import cat-utility
open import HomReasoning
open import Category.Cat

module linton {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) 
                 { T : Functor A A }
                 { η : NTrans A A identityFunctor T }
                 { μ : NTrans A A (T ○ T) T }
                 { M' : Monad A T η μ }
      {c₁' c₂' ℓ' : Level} ( B : Category c₁' c₂' ℓ' ) 
      { U_K : Functor B A } { F_K : Functor A B }
      { η_K : NTrans A A identityFunctor ( U_K ○ F_K ) }
      { ε_K : NTrans B B ( F_K ○ U_K ) identityFunctor } 
      { μ_K' : NTrans A A (( U_K ○ F_K ) ○ ( U_K ○ F_K )) ( U_K ○ F_K ) }
      ( AdjK : Adjunction A B U_K F_K η_K ε_K )
      ( R_K : MResolution A B T U_K F_K {η_K} {ε_K} {μ_K'} AdjK )
      { U^K : Functor B A } { F^K : Functor A B }
      { η^K : NTrans A A identityFunctor ( U^K ○ F^K ) }
      { ε^K : NTrans B B ( F^K ○ U^K ) identityFunctor } 
      { μ^K : NTrans A A (( U^K ○ F^K ) ○ ( U^K ○ F^K )) ( U^K ○ F^K ) }
      ( Adj^K : Adjunction A B U^K F^K η^K ε^K )
      ( R^K : MResolution A B T U^K F^K {η^K} {ε^K} {μ^K} Adj^K )
   where

--------
--
-- A^T --------> Sets^A_T^op
--  |                |
--  |                |
--  |U^T             |Sets^L^op
--  |                |
--  v                v
-- A ----------> Sets^A^op
--
--   Eliengberg Moore from Klisli as a pullback
--
--------


open import yoneda
open import comparison-functor {c₁}{ c₂}{ ℓ } { A } { T } { η } { μ } { M'} {c₁'}{ c₂'}{ ℓ' } ( B ) { U_K } { F_K } { η_K } { ε_K } { μ_K' } ( AdjK ) ( R_K )

open import comparison-em { c₁ }{ c₂ }{ ℓ } { A } { T } { η } { μ } { M'} {c₁' }{ c₂' }{ ℓ' } ( B ) { U^K } { F^K } { η^K } { ε^K } { μ^K } ( Adj^K ) ( R^K )



