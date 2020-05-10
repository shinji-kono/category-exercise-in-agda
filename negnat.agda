module negnat where


open import Data.Nat
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Data.Fin renaming ( suc to fsuc ; zero to fzero ; _+_ to _++_ )
open import Relation.Binary.Core
open import  Relation.Binary.PropositionalEquality


--  http://stackoverflow.com/questions/22580842/non-trivial-negation-in-agda


ℕ-elim : ∀ {p} (P : ℕ → Set p)
  (s : ∀ {n} → P n → P (suc n))
  (z : P 0) → ∀ n → P n
ℕ-elim P s z zero    = z
ℕ-elim P s z (suc n) = s (ℕ-elim P s z n)

-- data ⊥ : Set where

-- record ⊤ : Set where
--  constructor tt

-- peano : ∀ n → suc n ≡ zero → ⊥

Nope : (m n : ℕ) → Set
Nope (suc _) zero = ⊥
Nope _    _       = ⊤

nope : ∀ m n → m ≡ n → Nope m n
nope zero    ._ refl = _
nope (suc m) ._ refl = _

peano : ∀ n → suc n ≡ zero → ⊥
peano _ p = nope _ _ p


J : ∀ {a p} {A : Set a} (P : ∀ (x : A) y → x ≡ y → Set p)
  (f : ∀ x → P x x refl) → ∀ x y → (p : x ≡ y) → P x y p
J P f x .x refl = f x

Fin-elim : ∀ {p} (P : ∀ n → Fin n → Set p)
  (s : ∀ {n} {fn : Fin n} → P n fn → P (suc n) (fsuc fn))
  (z : ∀ {n} → P (suc n) fzero) →
  ∀ {n} (fn : Fin n) → P n fn
Fin-elim P s z fzero    = z
Fin-elim P s z (fsuc x) = s (Fin-elim P s z x)

Nope1  :  ℕ  -> Set 
Nope1 zero    = ⊥
Nope1 (suc _) = ⊤

Nope0 : ℕ → Set
Nope0 = ℕ-elim (λ _ → Set) (λ _ → ⊤) ⊥

bad : Fin 0 → ⊥
bad = Fin-elim (λ n _ → Nope0 n) (λ _ → _) _


--  http://stackoverflow.com/questions/18347542/agda-how-does-one-obtain-a-value-of-a-dependent-type
even : ℕ -> Set
even zero = ⊤
even (suc zero) =  ⊥
even (suc (suc n)) = even n

div : (n :  ℕ) -> even n ->  ℕ
div zero p = zero
div (suc (suc n)) p = suc (div n p)
div (suc zero) () 

proof : 2 + 3 ≡ suc (suc (suc (suc (suc zero)))) 
proof = refl

--
-- ¬_ : Set → Set
-- ¬ A = A → ⊥
--
-- data Dec (P : Set) : Set where
--   yes :   P → Dec P
--   no  : ¬ P → Dec P

EvenDecidable : Set
EvenDecidable = ∀ n → Dec (even n)

isEven : EvenDecidable
isEven zero          = yes _
isEven (suc zero)    = no (λ ())
isEven (suc (suc n)) = isEven n

data Bool : Set where
  true false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then t else _ = t
if false then _ else f = f

⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

bad1 : ∀ n → even n → even (suc n) → ⊥
bad1 zero          p q = q
bad1 (suc zero)    p q = p
bad1 (suc (suc n)) p q = bad1 n p q

odd : ∀ n → ¬ even n → even (suc n)
odd zero          p = p _
odd (suc zero)    p = _
odd (suc (suc n)) p = odd n p

g : ℕ → ℕ
g n with isEven n
... | yes e = div n e
... | no  o = div (suc n) (odd n o)

-- g-bad : ℕ → ℕ
-- g-bad n = if  ⌊ isEven n  ⌋
--   then (div n {!!})
--   else (div (suc n) (odd n {!!}))


if-dec_then_else_ : {P A : Set} → Dec P → (P → A) → (¬ P → A) → A
if-dec yes p then t else _ = t  p
if-dec no ¬p then _ else f = f ¬p

g' : ℕ → ℕ
g' n = if-dec isEven n
  then (λ e → div n e)
  else (λ o → div (suc n) (odd n o))

if-syntax = if-dec_then_else_

syntax if-syntax dec (λ yup → yupCase) (λ nope → nopeCase)
  = if-dec dec then[ yup ] yupCase else[ nope ] nopeCase

g'' : ℕ → ℕ
g'' n = if-dec isEven n
  then[ e ] div n e
  else[ o ] div (suc n) (odd n o)


mod :  ℕ  ->  ℕ 
mod zero = zero
mod (suc zero) = suc zero
mod (suc (suc N)) = mod N

proof1 : (n :  ℕ ) -> ( if ⌊ isEven n ⌋  then zero else (suc zero)  )  ≡ ( mod n )
proof1 zero =  refl
proof1 (suc zero) = refl
proof1 (suc (suc n)) =   let open ≡-Reasoning in 
   begin 
        if ⌊ isEven (suc (suc n)) ⌋ then zero else suc zero
   ≡⟨ cong ( \x -> (if ⌊ x ⌋ then zero else suc zero)) (lemma2 {n} )⟩
        if ⌊ isEven  n ⌋ then zero else suc zero
   ≡⟨ proof1 n ⟩
       mod n
   ≡⟨ sym (lemma1 {n}) ⟩
       mod (suc (suc n))
   ∎ where
        lemma1 : { n :  ℕ } -> mod (suc (suc n ))  ≡  mod n
        lemma1 = refl
        lemma2 : { n :  ℕ } -> isEven (suc (suc n ))  ≡  isEven n
        lemma2 = refl

data One : Set where
   * : One

lemma1 :  ( x y : One  ) → x ≡ y
lemma1 * * = refl

lemma2 :  {A : Set} ( x : A) → x ≡ x
lemma2 x  = refl


open import Data.Empty
open import Relation.Nullary
open import Level

lemma4 : Set (Level.suc Level.zero)
lemma4 =  {A : Set} ( x y : A) → ¬ ( ¬ x ≡ y )

data  A   : Set  where
   x y z : A

data _==_ : ( a b : A ) → Set where
   x=y : x == y

lemma3 : ( a b : A ) → a == b → ¬ a ≡ b
lemma3 _ _ x=y = λ ()

