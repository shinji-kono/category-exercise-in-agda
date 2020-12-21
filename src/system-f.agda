{-# OPTIONS --universe-polymorphism #-}

open import Level
open import Relation.Binary.PropositionalEquality

module system-f  where

Bool : {l : Level} → Set l → Set l
Bool {l} = λ(X : Set l) → X → X → X

T : {l : Level} (X : Set l) → Bool X
T X = λ(x y : X) → x

F : {l : Level} (X : Set l) → Bool X


F X = λ(x y : X) → y

D : {l : Level} → {U : Set l} → U → U → Bool U → U
D u v t = t u v

lemma04 : {l : Level} { U : Set l} {u v : U} → D {_} {U} u v (T U ) ≡  u
lemma04 = refl

lemma05 : {l : Level} { U : Set l} {u v : U} → D {_} {U} u v (F U ) ≡  v
lemma05 = refl

_×_ : {l : Level} → Set l → Set l →  Set (suc l)
_×_ {l} U V =  {X : Set l} → (U → V → X)  → X 
 
<_,_> : {l : Level} {U V : Set l} → U → V → (U ×  V) 
<_,_> {l} {U} {V} u v = λ x → x u v 

π1 : {l : Level} {U V : Set l} → (U ×  V) → U
π1 {l} {U} {V}  t = t {U} (λ(x : U) → λ(y : V) → x)

π2 : {l : Level} {U V : Set l} → (U ×  V) → V
π2 {l} {U} {V}  t = t {V} (λ(x : U) → λ(y : V) → y)

lemma06 : {l : Level} {U V : Set l } → {u : U } → {v : V} → π1 ( < u , v > ) ≡  u
lemma06 = refl

lemma07 : {l : Level} {U V : Set l } → {u : U } → {v : V} → π2 ( < u , v > ) ≡  v
lemma07 = refl

hoge : {l : Level} {U V : Set l} → U → V  → (U ×  V)
hoge u v = < u , v >

--lemma08 :  {l : Level} {X U V : Set l } → {x : X } → {u : U } →  (t : U ×  V)  → < π1 t  , π2 t > x ≡ t x
--lemma08 t = refl

-- Emp definision is still wrong...

--record Emp {l : Level } : Set (suc l) where
--   field 
--      ε : (U : Set l ) → U
--      e1 :  {U V : Set l} → (u : U) → (ε (U → V) ) u ≡ ε V
--
--open Emp

--lemma103 : {l : Level} {U V : Set l} → (u : U) → (t : Emp ) → (ε t (U → V) ) u ≡ ε t V 
--lemma103 u t = e1 t u

Emp  : {l : Level } → Set (suc l)
Emp {l} = {X : Set l} → X 

ε :  {l : Level} {U : Set l} → Emp {l} → U
ε {l} {U} t =  t {U}

-- lemma103 : {l : Level} {U V : Set l} → (u : U) → (t : Emp {l} ) → (ε {l} {U → V} t) u ≡ ε {l} {V} t
-- lemma103 u t = refl

-- lemma09 : {l : Level} {U : Set l}  → (t : Emp ) → ε {l} {U} (ε {_} {Emp} t) ≡ ε {_} {U} t
-- lemma09 t = refl

-- lemma10 :  {l : Level} {U V X : Set l} →  (t : Emp ) → U ×  V
-- lemma10  {l} {U} {V} t = ε {suc l} {U ×  V} t

-- lemma100 : {l : Level} {U V X : Set l} →  (t : Emp ) → Emp 
-- lemma100 {l} {U} {V} t = ε {_} {U} t

-- lemma101 : {l : Level} {U V : Set l} →  (t : Emp ) → π1 (ε {suc l} {U ×  V} t) ≡ ε {l} {U} t
-- lemma101 t = refl

-- lemma102 : {l : Level} {U V : Set l} →  (t : Emp ) → π2 (ε {_} {U ×  V} t) ≡ ε {_} {V} t
-- lemma102 t = refl


_+_  : {l : Level} → Set l → Set l → Set (suc l)
_+_ {l} U V = {X : Set l} → ( U → X ) → (V → X) → X

ι1 : {l : Level } {U V : Set l} →  U →  U + V
ι1 {l} {U} {V} u = λ x y → x u -- λ{X} → λ(x : U → X) → λ(y : V → X ) → x u

ι2 : {l : Level } {U V : Set l} →  V →  U + V
ι2 {l} {U} {V} v = λ x y → y v --λ{X} → λ(x : U → X) → λ(y : V → X ) → y v

δ : {l : Level} { U V R S : Set l } → (R → U) → (S → U) → ( R + S ) → U
δ {l} {U} {V} {R} {S} u v t = t {U} (λ(x : R) → u x) ( λ(y : S) → v y)

lemma11 : {l : Level} { U V R S : Set _ } → (u : R → U ) (v : S → U ) → (r : R) → δ {l} {U} {V} {R} {S} u v ( ι1 r )  ≡ u r
lemma11 u v r =  refl

lemma12 : {l : Level} { U V R S : Set _ } → (u : R → U ) (v : S → U ) → (s : S) → δ {l} {U} {V} {R} {S} u v ( ι2 s )  ≡ v s
lemma12 u v s =  refl


_××_ : {l : Level} → Set (suc l) → Set l →  Set (suc l)
_××_ {l} U V =  {X : Set l} → (U → V → X)  → X 

<<_,_>> : {l : Level} {U : Set (suc l) } {V : Set l} → U → V → (U  ××   V) 
<<_,_>> {l} {U} {V} u v = λ x → x u v -- λ{X} → λ(x : U → V → X) → x u v


Int : {l : Level } ( X : Set l ) → Set l
Int X = X → ( X → X ) → X

Zero : {l : Level } → { X : Set l } → Int X
Zero {l} {X} = λ(x : X ) → λ(y : X → X ) → x

S : {l : Level } → { X : Set l } → Int X → Int X
S {l} {X} t = λ(x : X) → λ(y : X → X ) → y ( t x y )

n0 : {l : Level} {X : Set l} → Int X
n0 = Zero 

n1 : {l : Level } → { X : Set l } → Int X
n1 {_} {X} = λ(x : X ) → λ(y : X → X ) → y x

n2 : {l : Level } → { X : Set l } → Int X
n2 {_} {X} = λ(x : X ) → λ(y : X → X ) → y (y x)

n3 : {l : Level } → { X : Set l } → Int X
n3 {_} {X} = λ(x : X ) → λ(y : X → X ) → y (y (y x))

n4 : {l : Level } → { X : Set l } → Int X
n4 {_} {X} = λ(x : X ) → λ(y : X → X ) → y (y (y (y x)))

lemma13 : {l : Level } → { X : Set l } → S (S (Zero {_} {X}))  ≡ n2 
lemma13 = refl

It : {l : Level} {U : Set l} → U → ( U → U ) → Int U → U
It u f t = t u f

ItInt : {l : Level} {X : Set l} → Int X → (X → Int X ) → ( Int X → Int X ) → Int X → Int X
ItInt {l} {X} u g f t = λ z s → t (u z s) ( λ (w : X) → (f (g w)) z s )

copy_int : {l l' : Level } { X X' : Set l } → Int (X → (X → X) → X) → Int X
copy_int {_} {_} {X} {X'} x = It Zero S x

R : {l : Level} { U X : Set l}   → U → ( U → Int X →  U ) → Int _ → U 
R {l} {U} {X} u v t =  π1 ( It {suc l} {U ×  Int X} (< u , Zero >) (λ (x : U × Int X) →  < v (π1 x) (π2 x) , S (π2 x) > ) t ) 

-- bad adder which modifies input type
add' : {l : Level} {X : Set l} → Int (Int X) → Int X → Int X
add' x y = It y S x

add : {l : Level} {X : Set l} → Int X → Int X → Int X
add x y = λ z s → x (y z s) s

add'' : {l : Level} {X : Set l} → Int X → Int X → Int X
add'' x y = ItInt y (\w z s -> w )S x

lemma22 : {l : Level} {X : Set l} ( x y : Int X ) → add x y  ≡ add'' x y
lemma22 x y = refl

lemma21 : {l : Level} {X : Set l} ( x y : Int X ) → add x Zero  ≡ x
lemma21 x y = refl

postulate extensionality : {l : Level } → Relation.Binary.PropositionalEquality.Extensionality l l

--lemma23 : {l : Level} {X : Set l} ( x y : Int X ) → add x (S y)  ≡ S ( add x y )
--lemma23 x y = extensionality ( λ z → {!!} )
--   where
--       lemma24 : {!!}
--       lemma24 = {!!}

-- lemma23 : {l : Level} {X : Set l} ( x y : Int X ) → add x y  ≡ add y x
-- lemma23 x y = {!!}

-- bad adder which modifies input type
mul' : {l : Level } {X : Set l} → Int X → Int (Int X) → Int X
mul' {l} {X} x y = It Zero (add x) y

mul : {l : Level } {X : Set l} → Int X → Int X → Int X
mul {l} {X} x y = λ z s → x z ( λ w → y w s )

mul'' : {l : Level } {X : Set l} → Int X → Int X → Int X
mul'' {l} {X} x y = ItInt Zero (\w z s -> w) (add'' x) y

fact : {l : Level} {X : Set l} → Int _ → Int X
fact  {l} {X} n = R (S Zero) (λ z → λ w → mul z (S w)) n

lemma13' : {l : Level} {X : Set l} → fact {l} {X} n4 ≡ mul n4 ( mul n2 n3)
lemma13' = refl

-- lemma23 : {l : Level} {X : Set l} ( x y : Int X ) → mul x y  ≡ mul'' x y
-- lemma23 x y = {!!}

lemma24 :  {l : Level } {X : Set l} → mul {l} {X} n4 n3  ≡ mul'' {l} {X} n3 n4
lemma24 = refl


-- lemma14 : {l : Level} {X : Set l} → (x y : Int X) → mul x y  ≡ mul y x
-- lemma14 x y = {!!} -- It {!!} {!!} {!!}

lemma15 : {l : Level} {X : Set l} (x y : Int X) → mul {l} {X} n2 n3  ≡ mul {l} {X} n3 n2
lemma15 x y = refl

lemma15' : {l : Level} {X : Set l} (x y : Int X) → mul'' {l} {X} n2 n3  ≡ mul'' {l} {X} n3 n2
lemma15' x y = refl

lemma16 : {l : Level} {X U : Set l} → (u : U ) → (v : U → Int X →  U ) → R u v Zero ≡ u
lemma16 u v = refl

-- lemma17 : {l : Level} {X U : Set l} → (u : U ) → (v : U → Int →  U ) → (t : Int ) → R u v (S t) ≡ v ( R u v t ) t
-- lemma17 u v t = refl

-- postulate lemma17 : {l : Level} {X U : Set l} → (u : U ) → (v : U → Int X →  U ) → (t : Int X ) → R u v (S t) ≡ v ( R u v t ) t

List : {l : Level} (U X : Set l) → Set l
List {l} = λ( U X : Set l)  → X → ( U → X → X ) → X 

Nil : {l : Level} {U : Set l} {X : Set l} → List U X
Nil {l} {U} {X} = λ(x : X) → λ(y : U → X → X) → x

Cons : {l : Level} {U : Set l} {X : Set l} → U → List U X → List U X
Cons {l} {U} {X} u t = λ(x : X) → λ(y : U → X → X) → y u (t x y )

l0 : {l : Level} {X X' : Set l} → List (Int X) (X')
l0 = Nil

l1 : {l : Level} {X X' : Set l} → List (Int X) (X')
l1 = Cons n1 Nil

l2 : {l : Level} {X X' : Set l} → List (Int X) (X')
l2 = Cons n2 l1

l3 : {l : Level} {X X' : Set l} → List (Int X) (X')
l3 = Cons n3 l2

--    λ x x₁ y → y x (y x (y x x₁))
l4 : {l : Level} {X X' : Set l} → Int X → List (Int X) (X')
l4 x = Cons x (Cons x (Cons x Nil))

ListIt : {l : Level} {U X : Set l} → X → ( U → X → X ) → List U X → X
ListIt w f t = t w f

LListIt : {l : Level} {U X : Set l} → List U X  → (X → List U X) → ( U → List U X → List U X ) → List U X → List U X
LListIt {l} {U} {X} w g f t = λ x y → t (w x y) (λ (x' : U) (y' : X)  → (f x' (g y')) x y )

-- Cdr : {l : Level} {U : Set l} {X : Set l} → List U X →  List U X
-- Cdr w = λ x → λ y →  w x (λ x y   →  y) 

-- lemma181 :{l : Level} {U : Set l} {X : Set l} → Car Zero l2 ≡ n2
-- lemma181 = refl

-- lemma182 :{l : Level} {U : Set l} {X : Set l} → Cdr l2 ≡ l1
-- lemma182 = refl

Nullp : {l : Level} {U : Set (suc l)} { X : Set (suc l)} → List U (Bool X) → Bool X
Nullp {_} {_} {X} list = ListIt (T X) (λ u w → (F X)) list

-- bad append
Append' : {l : Level} {U X : Set l} → List U (List U X) → List U X → List U X
Append' {_} {_} {X} x y = ListIt y Cons x    

Append : {l : Level} {U : Set l} {X : Set l} → List U X → List U X → List U X
Append x y = λ n c → x (y n c) c

Append'' : {l : Level} {U X : Set l} → List U X → List U X → List U X
Append'' {_} {_} {X} x y = LListIt y (\e n c -> e) Cons x   

lemma18 :{l : Level} {U : Set l} {X : Set l} → Append {_} {Int U} {X} l1 l2 ≡ Cons n1 (Cons n2 (Cons n1 Nil))
lemma18 = refl

lemma18' :{l : Level} {U : Set l} {X : Set l} → Append'' {_} {Int U} {X} l1 l2 ≡ Cons n1 (Cons n2 (Cons n1 Nil))
lemma18' = refl

lemma18'' :{l : Level} {U : Set l} {X : Set l} → Append'' {_} {Int U} {X}  ≡ Append 
lemma18'' = refl

Reverse : {l : Level} {U : Set l} {X : Set l} → List U (List U X) → List U X
Reverse {l} {U} {X} x = ListIt Nil ( λ u w → Append w (Cons u Nil) ) x
-- λ x → x (λ x₁ y → x₁) (λ u w s t → w (t u s) t)

lemma19 :{l : Level} {U : Set l} {X : Set l} → Reverse {_} {Int U} {X} l3 ≡ Cons n1 (Cons n2 (Cons n3 Nil))
lemma19 = refl

Reverse' : {l : Level} {U : Set l} {X : Set l} → List U X → List U X
Reverse' {l} {U} {X} x = LListIt Nil (\e n c -> e) ( λ u w → Append w (Cons u Nil) ) x
-- λ x x₁ y → x x₁ (λ x' y' → y')

-- lemma19' :{l : Level} {U : Set l} {X : Set l} → Reverse' {_} {Int U} {X} l3 ≡ Cons n1 (Cons n2 (Cons n3 Nil))
-- lemma19' = refl

Tree : {l : Level} → Set l → Set l → Set l
Tree {l} = λ( U X : Set l)  → X → ( (U → X) →  X ) → X

NilTree : {l : Level} {U : Set l} {X : Set l} → Tree U X
NilTree {l} {U} {X} = λ(x : X) → λ(y : (U → X) → X) → x

Collect : {l : Level} {U : Set l} {X : Set l} → (U → Tree U X ) → Tree U X
Collect {l} {U} {X} f = λ(x : X) → λ(y : (U → X) → X) → y (λ(z : U) → f z x y )

TreeIt : {l : Level} {U X X : Set l} → X → ( (U → X) → X ) → Tree U X → X
TreeIt w h t = t w h

t0 :  {l : Level} {X X' : Set l} → Tree (Bool X) X'
t0 {l} {X} {X'} =  NilTree 

t1 :  {l : Level} {X X' : Set l} → Tree (Bool X) X'
t1 {l} {X} {X'} =  NilTree -- Collect (λ b → D b NilTree (λ c → Collect NilTree NilTree ))
