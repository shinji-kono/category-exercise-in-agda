open import Category -- https://github.com/konn/category-agda
open import Level
open import Category.Sets renaming ( _o_ to _*_ )

module SetsCompleteness where

open import cat-utility
open import Relation.Binary.Core
open import Function
import Relation.Binary.PropositionalEquality
-- Extensionality a b = {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → ( λ x → f x ≡ λ x → g x )
postulate extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → Relation.Binary.PropositionalEquality.Extensionality c₂ c₂

≡cong = Relation.Binary.PropositionalEquality.cong

open import Relation.Binary.PropositionalEquality hiding ( [_] )

lemma1 :  { c₂ : Level  } {a b  : Obj (Sets { c₂})} {f g : Hom Sets a b} →
   Sets [ f ≈ g ] → (x : a ) → f x  ≡ g x
lemma1 refl  x  = refl

record Σ {a} (A : Set a) (B : Set a) : Set a where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open Σ public


SetsProduct :  {  c₂ : Level} → ( a b : Obj (Sets  {c₂})) → Product ( Sets  {  c₂} ) a b
SetsProduct { c₂ } a b = record {
         product =  Σ a b
       ; π1 = λ ab → (proj₁ ab)
       ; π2 = λ ab → (proj₂ ab)
       ; isProduct = record {
              _×_  = λ f g  x →   record { proj₁ = f  x ;  proj₂ =  g  x }     -- ( f x ,  g x )
              ; π1fxg=f = refl
              ; π2fxg=g  = refl
              ; uniqueness = refl
              ; ×-cong   =  λ {c} {f} {f'} {g} {g'} f=f g=g →  prod-cong a b f=f g=g
          }
      } where
          prod-cong : ( a b : Obj (Sets {c₂}) ) {c : Obj (Sets {c₂}) } {f f' : Hom Sets c a } {g g' : Hom Sets c b }
              → Sets [ f ≈ f' ] → Sets [ g ≈ g' ]
              → Sets [ (λ x → f x , g x) ≈ (λ x → f' x , g' x) ]
          prod-cong a b {c} {f} {.f} {g} {.g} refl refl = refl


record iproduct {a} (I : Set a)  ( pi0 : I → Set a ) : Set a where
    field
       pi1 : ( i : I ) → pi0 i

open iproduct

SetsIProduct :  {  c₂ : Level} → (I : Obj Sets) (ai : I → Obj Sets )
     → IProduct I ( Sets  {  c₂} ) ai
SetsIProduct I fi = record {
       iprod = iproduct I fi
       ; pi  = λ i prod  → pi1 prod i
       ; isIProduct = record {
              iproduct = iproduct1
            ; pif=q = λ {q} {qi} {i} → pif=q {q} {qi} {i}
            ; ip-uniqueness = ip-uniqueness
            ; ip-cong  = ip-cong
       }
   } where
       iproduct1 : {q : Obj Sets} → ((i : I) → Hom Sets q (fi i)) → Hom Sets q (iproduct I fi)
       iproduct1 {q} qi x = record { pi1 = λ i → (qi i) x  }
       pif=q : {q : Obj Sets} {qi : (i : I) → Hom Sets q (fi i)} → {i : I} → Sets [ Sets [ (λ prod → pi1 prod i) o iproduct1 qi ] ≈ qi i ]
       pif=q {q} {qi} {i} = refl
       ip-uniqueness : {q : Obj Sets} {h : Hom Sets q (iproduct I fi)} → Sets [ iproduct1 (λ i → Sets [ (λ prod → pi1 prod i) o h ]) ≈ h ]
       ip-uniqueness = refl
       ipcx : {q :  Obj Sets} {qi qi' : (i : I) → Hom Sets q (fi i)} → ((i : I) → Sets [ qi i ≈ qi' i ]) → (x : q) → iproduct1 qi x ≡ iproduct1 qi' x
       ipcx {q} {qi} {qi'} qi=qi x  =
              begin
                record { pi1 = λ i → (qi i) x  }
             ≡⟨ ≡cong ( λ QIX → record { pi1 = QIX } ) ( extensionality Sets (λ i → ≡cong ( λ f → f x )  (qi=qi i)  )) ⟩
                record { pi1 = λ i → (qi' i) x  }
             ∎  where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning
       ip-cong  : {q : Obj Sets} {qi qi' : (i : I) → Hom Sets q (fi i)} → ((i : I) → Sets [ qi i ≈ qi' i ]) → Sets [ iproduct1 qi ≈ iproduct1  qi' ]
       ip-cong {q} {qi} {qi'} qi=qi  = extensionality Sets ( ipcx qi=qi )


        --
        --         e             f
        --    c  -------→ a ---------→ b        f ( f'
        --    ^        .     ---------→
        --    |      .            g
        --    |k   .
        --    |  . h
        --y : d

        -- cf. https://github.com/danr/Agda-projects/blob/master/Category-Theory/Equalizer.agda

data sequ {c : Level} (A B : Set c) ( f g : A → B ) :  Set c where
    elem : (x : A ) → (eq : f x ≡ g x) → sequ A B f g

equ  :  {  c₂ : Level}  {a b : Obj (Sets {c₂}) } { f g : Hom (Sets {c₂}) a b } → ( sequ a b  f g ) →  a
equ  (elem x eq)  = x

fe=ge0  :  {  c₂ : Level}  {a b : Obj (Sets {c₂}) } { f g : Hom (Sets {c₂}) a b } →
     (x : sequ a b f g) → (Sets [ f o (λ e → equ e) ]) x ≡ (Sets [ g o (λ e → equ e) ]) x
fe=ge0 (elem x eq )  =  eq

irr : { c₂ : Level}  {d : Set c₂ }  { x y : d } ( eq eq' :  x  ≡ y ) → eq ≡ eq'
irr refl refl = refl

open sequ

--           equalizer-c = sequ a b f g
--          ; equalizer = λ e → equ e

SetsIsEqualizer :  {  c₂ : Level}  →  (a b : Obj (Sets {c₂}) )  (f g : Hom (Sets {c₂}) a b) → IsEqualizer Sets (λ e → equ e) f g
SetsIsEqualizer {c₂} a b f g = record {
               fe=ge  = fe=ge
             ; k = k
             ; ek=h = λ {d} {h} {eq} → ek=h {d} {h} {eq}
             ; uniqueness  = uniqueness
       } where
           fe=ge  :  Sets [ Sets [ f o (λ e → equ e ) ] ≈ Sets [ g o (λ e → equ e ) ] ]
           fe=ge  =  extensionality Sets (fe=ge0 )
           k :  {d : Obj Sets} (h : Hom Sets d a) → Sets [ Sets [ f o h ] ≈ Sets [ g o h ] ] → Hom Sets d (sequ a b f g)
           k {d} h eq = λ x → elem  (h x) ( ≡cong ( λ y → y x ) eq )
           ek=h : {d : Obj Sets} {h : Hom Sets d a} {eq : Sets [ Sets [ f o h ] ≈ Sets [ g o h ] ]} → Sets [ Sets [ (λ e → equ e )  o k h eq ] ≈ h ]
           ek=h {d} {h} {eq} = refl
           injection :  { c₂ : Level  } {a b  : Obj (Sets { c₂})} (f  : Hom Sets a b) → Set c₂
           injection f =  ∀ x y  → f x ≡ f y →  x  ≡ y
           elm-cong :   (x y : sequ a b f g) → equ x ≡ equ y →  x  ≡ y
           elm-cong ( elem x eq  ) (elem .x eq' ) refl   =  ≡cong ( λ ee → elem x ee ) ( irr eq eq' )
           lemma5 :   {d : Obj Sets} {h : Hom Sets d a} {fh=gh : Sets [ Sets [ f o h ] ≈ Sets [ g o h ] ]} {k' : Hom Sets d (sequ a b f g)} →
                Sets [ Sets [ (λ e → equ e) o k' ] ≈ h ] → (x : d ) → equ (k h fh=gh x) ≡ equ (k' x)
           lemma5 refl  x  = refl   -- somehow this is not equal to lemma1
           uniqueness :   {d : Obj Sets} {h : Hom Sets d a} {fh=gh : Sets [ Sets [ f o h ] ≈ Sets [ g o h ] ]} {k' : Hom Sets d (sequ a b f g)} →
                Sets [ Sets [ (λ e → equ e) o k' ] ≈ h ] → Sets [ k h fh=gh  ≈ k' ]
           uniqueness  {d} {h} {fh=gh} {k'} ek'=h =  extensionality Sets  ( λ ( x : d ) →  begin
                k h fh=gh x
             ≡⟨ elm-cong ( k h fh=gh x) (  k' x ) (lemma5 {d} {h} {fh=gh} {k'} ek'=h x )  ⟩
                k' x
             ∎  ) where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning


open Functor

----
-- C is locally small i.e. Hom C i j is a set c₁
--
record Small  {  c₁ c₂ ℓ : Level} ( C : Category c₁ c₂ ℓ ) ( I :  Set  c₁ )
                : Set (suc (c₁ ⊔ c₂ ⊔ ℓ )) where
   field
     hom→ : {i j : Obj C } →    Hom C i j →  I
     hom← : {i j : Obj C } →  ( f : I ) →  Hom C i j
     hom-iso : {i j : Obj C } →  { f : Hom C i j } →   C [ hom← ( hom→ f )  ≈ f ]
     hom-rev : {i j : Obj C } →  { f : I } →   hom→ ( hom← {i} {j} f )  ≡ f
     ≡←≈ : {i j : Obj C } →  { f g : Hom C i j } →  C [ f ≈ g ] →   f ≡ g

open Small

ΓObj :  {  c₁ c₂ ℓ : Level} { C : Category c₁ c₂ ℓ } { I :  Set  c₁ } ( s : Small C I ) ( Γ : Functor C ( Sets { c₁} ))
   (i : Obj C ) →　 Set c₁
ΓObj s  Γ i = FObj Γ i

ΓMap :  {  c₁ c₂ ℓ : Level} { C : Category c₁ c₂ ℓ } { I :  Set  c₁ } ( s : Small C I ) ( Γ : Functor C ( Sets { c₁} ))
    {i j : Obj C } →　 ( f : I ) →  ΓObj s Γ i → ΓObj  s Γ j
ΓMap  s Γ {i} {j} f = FMap Γ ( hom← s f )

record snat   { c₂ }  { I OC :  Set  c₂ } ( sobj :  OC →  Set  c₂ )
     ( smap : { i j :  OC  }  → (f : I ) →  sobj i → sobj j ) : Set  c₂ where
   field
       snmap : ( i : OC ) → sobj i
       sncommute : ( i j : OC ) → ( f :  I ) →  smap f ( snmap i )  ≡ snmap j

open snat

open import Relation.Binary.HeterogeneousEquality as HE renaming ( cong to cong' ; sym to sym' ; subst₂ to subst₂' ; Extensionality to Extensionality' )
    using (_≅_;refl; ≡-to-≅)
-- why we cannot use Extensionality' ?
postulate ≅extensionality : { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) → 
                  {a : Level } {A : Set a} {B B' : A → Set a}
                               {f : (y : A) → B y} {g : (y : A) → B' y} → (∀ y → f y ≅ g y) → ( ( λ y → f y ) ≅ ( λ y → g y ))

snat-cong : {c : Level}
                {I OC : Set c}
                {sobj : OC → Set c}
                {smap : {i j : OC}  → (f : I) → sobj i → sobj j}
              → (s t : snat sobj smap)
              → (snmap-≡ : snmap s ≡ snmap t)
              → (sncommute-≅ : sncommute s ≅ sncommute t)
              → s ≡ t
snat-cong _ _ refl refl = refl

open import HomReasoning
open NTrans

Cone : {  c₁ c₂ ℓ : Level} ( C : Category c₁ c₂ ℓ ) ( I :  Set  c₁ ) ( s : Small C I )  ( Γ : Functor C (Sets  {c₁} ) )
    → NTrans C Sets (K C Sets (snat  (ΓObj s Γ) (ΓMap s Γ) ) ) Γ
Cone C I s  Γ  =  record {
               TMap = λ i →  λ sn →  snmap sn i
             ; isNTrans = record { commute = comm1 }
      } where
    comm1 :  {a b : Obj C} {f : Hom C a b} →
        Sets [ Sets [ FMap Γ f o (λ sn → snmap sn a) ] ≈
        Sets [ (λ sn →  (snmap sn b)) o FMap (K C Sets (snat (ΓObj s Γ) (ΓMap s Γ))) f ] ]
    comm1 {a} {b} {f} = extensionality Sets  ( λ  sn  →  begin
                 FMap Γ f  (snmap sn  a )
             ≡⟨ ≡cong ( λ f → ( FMap Γ f (snmap sn  a ))) (sym ( ≡←≈ s ( hom-iso s ))) ⟩
                 FMap Γ ( hom← s ( hom→ s f))  (snmap sn  a )
             ≡⟨⟩
                 ΓMap s Γ (hom→ s f) (snmap sn a )
             ≡⟨ sncommute sn a b  (hom→ s  f) ⟩
                 snmap sn b
             ∎  ) where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning


SetsLimit : {  c₁ c₂ ℓ : Level} ( I :  Set  c₁ ) ( C : Category c₁ c₂ ℓ )  ( small : Small C I ) ( Γ : Functor C (Sets  {c₁} ) )
    → Limit C Sets Γ
SetsLimit {c₁} I C s Γ = record {
           a0 =  snat  (ΓObj s Γ) (ΓMap s Γ)
         ; t0 = Cone C I s Γ
         ; isLimit = record {
               limit  = limit1
             ; t0f=t = λ {a t i } → t0f=t {a} {t} {i}
             ; limit-uniqueness  =  λ {a t i }  → limit-uniqueness   {a} {t} {i}
          }
       }  where
          comm2 : { a : Obj Sets } {x : a } {i j : Obj C} (t : NTrans C Sets (K C Sets a) Γ) (f : I)
             → ΓMap s Γ f (TMap t i x) ≡ TMap t j x
          comm2 {a} {x} t f =  ≡cong ( λ h → h x ) ( IsNTrans.commute ( isNTrans t ) )
          limit1 : (a : Obj Sets) → NTrans C Sets (K C Sets a) Γ → Hom Sets a (snat (ΓObj s Γ) (ΓMap s Γ))
          limit1 a t = λ x →  record { snmap = λ i →  ( TMap t i ) x ;
              sncommute = λ i j f → comm2 t f }
          t0f=t : {a : Obj Sets} {t : NTrans C Sets (K C Sets a) Γ} {i : Obj C} → Sets [ Sets [ TMap (Cone C I s Γ) i o limit1 a t ] ≈ TMap t i ]
          t0f=t {a} {t} {i} =  extensionality Sets  ( λ  x  →  begin
                 ( Sets [ TMap (Cone C I s Γ) i o limit1 a t ]) x
             ≡⟨⟩
                 TMap t i x
             ∎  ) where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning
          limit-uniqueness : {a : Obj Sets} {t : NTrans C Sets (K C Sets a) Γ} {f : Hom Sets a (snat (ΓObj s Γ) (ΓMap s Γ))} →
                ({i : Obj C} → Sets [ Sets [ TMap (Cone C I s Γ) i o f ] ≈ TMap t i ]) → Sets [ limit1 a t ≈ f ]
          limit-uniqueness {a} {t} {f} cif=t = extensionality Sets  ( λ  x  →  begin
                  limit1 a t x
             ≡⟨⟩
                  record { snmap = λ i →  ( TMap t i ) x ; sncommute = λ i j f → comm2 t f }
             ≡⟨ snat-cong (limit1 a t x) (f x ) ( extensionality Sets  ( λ  i  →  eq1 x i )) (eq5 x ) ⟩
                  record { snmap = λ i →  snmap  (f x ) i  ; sncommute = λ i j g → sncommute (f x ) i j g  }
             ≡⟨⟩
                  f x
             ∎  ) where
                  open  import  Relation.Binary.PropositionalEquality
                  open ≡-Reasoning
                  eq1 : (x : a ) (i : Obj C) → TMap t i x ≡ snmap (f x) i
                  eq1 x i = sym ( ≡cong ( λ f → f x ) cif=t  )
                  eq2 : (x : a ) (i j : Obj C) (k : I) → ΓMap s Γ k (TMap t i x) ≡ TMap t j x 
                  eq2 x i j f =  ≡cong ( λ f → f x ) ( IsNTrans.commute ( isNTrans t ) )
                  eq3 :  (x : a ) (i j : Obj C) (k : I) → ΓMap s Γ k (snmap (f x) i) ≡ snmap (f x) j
                  eq3 x i j k =  sncommute (f x ) i j k
                  irr≅ : { c₂ : Level}  {d e : Set c₂ }  { x1 y1 : d } { x2 y2 : e }
                      ( ee :  x1 ≅ x2 ) ( ee' :  y1  ≅ y2 )  ( eq :  x1  ≡ y1 ) ( eq' :  x2  ≡ y2 ) → eq ≅ eq'
                  irr≅ refl refl refl refl = refl
                  eq4 :  ( x : a)  ( i j : Obj C ) ( g : I )
                     → ≡cong ( λ h → h x ) ( IsNTrans.commute ( isNTrans t ) {i} {j} {hom← s g }  ) ≅  sncommute (f x) i j g
                  eq4 x i j g = irr≅ (≡-to-≅ (≡cong ( λ h → ΓMap s Γ g h ) (eq1 x i))) (≡-to-≅ (eq1 x j )) (eq2 x i j g ) (eq3 x i j g )
                  eq5 :  ( x : a) 
                      →  ( λ i j g → ≡cong ( λ h → h x ) ( IsNTrans.commute ( isNTrans t ) {i} {j} {hom← s g } ))
                       ≅ ( λ i j g →  sncommute (f x) i j g )
                  eq5 x = ≅extensionality (Sets {c₁} ) ( λ i →
                          ≅extensionality (Sets {c₁} ) ( λ j →
                          ≅extensionality (Sets {c₁} ) ( λ g → eq4 x i j g ) ) )

open Limit
open IsLimit
open IProduct

SetsCompleteness : {  c₁ c₂ ℓ : Level} ( C : Category c₁ c₂ ℓ ) ( I :  Set  c₁ ) ( small : Small C I ) → Complete (Sets {c₁}) C
SetsCompleteness {c₁} {c₂} C I s  =  record {
         climit = λ Γ → SetsLimit {c₁} I C s Γ
      ;  cequalizer = λ {a} {b} f g → record {  equalizer-c = sequ a b f g ;
                equalizer = ( λ e → equ e ) ;
                isEqualizer =  SetsIsEqualizer a b f g }
      ;  cproduct = λ J fi → SetsIProduct J fi 
   } where
