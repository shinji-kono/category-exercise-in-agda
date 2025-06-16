{-# OPTIONS --warning=noUnsupportedIndexedMatch --with-K #-}

-- we cannot run this proof in curical compatible and with out warning


open import Category -- https://github.com/konn/category-agda
open import Level
open import Category.Sets 

module SetsCompleteness1 where

open import Definitions
open import Relation.Binary.Core
open import Function
import Relation.Binary.PropositionalEquality

open import Relation.Binary.PropositionalEquality hiding ( [_] )

open Small

open import Axiom.Extensionality.Propositional

open Functor


ΓObj :  {  c₁ c₂ ℓ : Level} { C : Category c₁ c₂ ℓ }  ( s : Small c₁ C  ) ( Γ : Functor C ( Sets { c₁} ))
   (i : Obj C ) →　 Set (c₁)
ΓObj s  Γ i = FObj Γ i

ΓMap :  {  c₁ c₂ ℓ : Level} { C : Category c₁ c₂ ℓ }  ( s : Small c₁ C  ) ( Γ : Functor C ( Sets { c₁} ))
    {i j : Obj C } →　 ( f : Small.I s ) →  ΓObj s Γ i → ΓObj  s Γ j
ΓMap  s Γ {i} {j} f = ? -- FMap Γ ( hom← s f )

record snat   { c₁ c₂ }  { I : Set c₂} { OC :  Set  c₁ } ( sobj :  OC →  Set  c₂ )
     ( smap : { i j :  OC  }  → (f : I ) →  sobj i → sobj j ) : Set   (c₁ ⊔ c₂) where
   field
       snmap : ( i : OC ) → sobj i
       sncommute : ( i j : OC ) → ( f :  I ) →  smap f ( snmap i )  ≡ snmap j

open snat

open import Relation.Binary.HeterogeneousEquality as HE renaming ( cong to cong' ; sym to sym' ; subst₂ to subst₂' )
    using (_≅_;refl; ≡-to-≅)

open import Axiom.Extensionality.Heterogeneous renaming ( Extensionality to HExtensionality )

snat-cong : {c₁ c₂ : Level}
                {I : Set c₁}
                {OC : Set c₁}
                {sobj : OC → Set c₁}
                {smap : {i j : OC}  → (f : I) → sobj i → sobj j}
              → (s t : snat sobj smap)
              → (snmap-≡ : snmap s ≡ snmap t)
              → (sncommute-≅ : sncommute s ≅ sncommute t)
              → s ≡ t
snat-cong _ _ refl refl = refl

open import HomReasoning
open NTrans

Cone : {  c₁ c₂ ℓ : Level} ( C : Category c₁ c₂ ℓ )  ( s : Small c₁ C  )  
    → ( Γ : Functor C (Sets  {c₁} ) )
    → NTrans C Sets (K C Sets (snat  (ΓObj s Γ) (ΓMap s Γ) ) ) Γ
Cone C s Γ  =  record {
               TMap = λ i →  λ sn → snmap sn i
             ; isNTrans = record { commute = comm1 }
      } where
    comm1 :  {a b : Obj C} {f : Hom C a b} →
        Sets [ Sets [ FMap Γ f o (λ sn → snmap sn a) ] ≈
        Sets [ (λ sn →  (snmap sn b)) o FMap (K C Sets (snat (ΓObj s Γ) (ΓMap s Γ))) f ] ]
    comm1 {a} {b} {f} sn = begin
                FMap Γ f  (snmap sn  a )
            ≡⟨ cong ( λ f → ( FMap Γ f (snmap sn  a ))) (sym ( ≡←≈ s ( hom-iso s ))) ⟩
                FMap Γ ( hom← s ( hom→ s f))  ? -- (snmap sn  a )
            ≡⟨ ? ⟩
                ΓMap s Γ (hom→ s f) (snmap sn a )
            ≡⟨ sncommute sn a b  (hom→ s  f) ⟩
                snmap sn b
            ∎  where
                 open  import  Relation.Binary.PropositionalEquality
                 open ≡-Reasoning


SetsLimit : {  c₁ c₂ ℓ : Level}  ( C : Category c₁ c₂ ℓ )  ( small : Small c₁ C  ) ( Γ : Functor C (Sets  {c₁} ) )
    → ( (a b : Level) → HExtensionality a b )
    → ( (a b : Level) → Extensionality a b )
    → Limit C Sets Γ
SetsLimit {c₁}  C s Γ hext ext = record {
           a0 =  snat  (ΓObj s Γ) (ΓMap s Γ)
         ; t0 = Cone C s Γ
         ; isLimit = record {
               limit  = limit1
             ; t0f=t = λ {a t i } → t0f=t {a} {t} {i}
             ; limit-uniqueness  =  λ {a t i }  → limit-uniqueness   {a} {t} {i}
          }
       }  where
          comm2 : { a : Obj Sets } {x : a } {i j : Obj C} (t : NTrans C Sets (K C Sets a) Γ) (f : Small.I s)
             → ΓMap s Γ f (TMap t i x) ≡ TMap t j x
          comm2 {a} {x} t f =  IsNTrans.commute ( isNTrans t ) x 
          limit1 : (a : Obj Sets) → NTrans C Sets (K C Sets a) Γ → Hom Sets a (snat (ΓObj s Γ) (ΓMap s Γ))
          limit1 a t = λ x →  record { snmap = λ i →  ( TMap t i ) x ;
              sncommute = λ i j f → comm2 t f }
          t0f=t : {a : Obj Sets} {t : NTrans C Sets (K C Sets a) Γ} {i : Obj C} → Sets [ Sets [ TMap (Cone C s Γ) i o limit1 a t ] ≈ TMap t i ]
          t0f=t {a} {t} {i} x = begin
                ( Sets [ TMap (Cone C  s Γ) i o limit1 a t ]) x
            ≡⟨⟩
                TMap t i x
            ∎   where
                 open ≡-Reasoning
          limit-uniqueness : {a : Obj Sets} {t : NTrans C Sets (K C Sets a) Γ} {f : Hom Sets a (snat (ΓObj s Γ) (ΓMap s Γ))} →
                ({i : Obj C} → Sets [ Sets [ TMap (Cone C  s Γ) i o f ] ≈ TMap t i ]) → Sets [ limit1 a t ≈ f ]
          limit-uniqueness {a} {t} {f} cif=t x = begin
                  limit1 a t x
             ≡⟨⟩
                  record { snmap = λ i →  ( TMap t i ) x ; sncommute = λ i j f → comm2 t f }
             ≡⟨ snat-cong (limit1 a t x) (f x ) eq10 (eq5 x ) ⟩
                  record { snmap = λ i →  snmap  (f x ) i  ; sncommute = λ i j g → sncommute (f x ) i j g  }
             ≡⟨⟩
                  f x
             ∎   where
                  open ≡-Reasoning
                  eq1 : (x : a ) (i : Obj C) → TMap t i x ≡ snmap (f x) i
                  eq1 x i = sym ( cif=t x )
                  eq10 : snmap (limit1 a t x) ≡ snmap (f x)
                  eq10 = ext _ _ ( λ i → eq1 x i )
                  eq2 : (x : a ) (i j : Obj C) (k : Small.I s) → ΓMap s Γ k (TMap t i x) ≡ TMap t j x 
                  eq2 x i j  y =  IsNTrans.commute ( isNTrans t )  x
                  eq3 :  (x : a ) (i j : Obj C) (k : Small.I s) → ΓMap s Γ k (snmap (f x) i) ≡ snmap (f x) j
                  eq3 x i j k =  sncommute (f x ) i j k
                  irr≅ : { c₂ : Level}  {d e : Set c₂ }  { x1 y1 : d } { x2 y2 : e }
                      ( ee :  x1 ≅ x2 ) ( ee' :  y1  ≅ y2 )  ( eq :  x1  ≡ y1 ) ( eq' :  x2  ≡ y2 ) → eq ≅ eq'
                  irr≅ refl refl refl refl = refl
                  eq4 :  ( x : a)  ( i j : Obj C ) ( g : Small.I s )
                    → ( IsNTrans.commute ( isNTrans t ) {i} {j} {hom← s g } x ) ≅  sncommute (f x) i j g
                  eq4 x i j g = irr≅ (≡-to-≅ (cong ( λ h → ΓMap s Γ g h ) (eq1 x i))) (≡-to-≅ (eq1 x j )) (eq2 x i j g ) (eq3 x i j g )
                  eq5 :  ( x : a) 
                      →  ( λ i j g → IsNTrans.commute ( isNTrans t ) {i} {j} {hom← s g } x )
                       ≅ ( λ i j g →  sncommute (f x) i j g )
                  eq5 x = hext _ _ ? ( λ i →
                          hext _ _ ? ( λ j →
                          hext _ _ ? ( λ g → eq4 x i j g ) ) )

open Limit
open IsLimit
open IProduct

open import SetsCompleteness

SetsCompleteness : {  c₁ c₂ ℓ : Level} ( C : Category c₁ c₂ ℓ ) ( I :  Set  c₁ ) ( small : Small c₁ C  ) → Complete  {c₁} {c₂} {ℓ} (Sets {c₁}) 
SetsCompleteness {c₁} {c₂} C I s  =  record {
         climit = λ Γ → ? -- SetsLimit {c₁} I C s ? ? ?
      ;  cequalizer = λ {a} {b} f g → record {  equalizer-c = sequ a b f g ;
                equalizer = ( λ e → equ e ) ;
                isEqualizer =  SetsIsEqualizer ? a b f g }
      ;  cproduct = λ J fi → SetsIProduct J fi ?
   } 
