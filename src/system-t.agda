{-# OPTIONS --cubical-compatible --safe #-}

module system-t (U : Set) (V : Set) (v : V) (u : U) where

open  import  Relation.Binary.PropositionalEquality

record _×_ ( U : Set ) ( V : Set )   :  Set where
    field
       π1 : U
       π2 : V

<_,_> : {U V : Set} → U → V → U × V
< u , v >  = record {π1 = u ; π2 = v }

open _×_


f : U → V
f = λ u → v


UV : Set
UV = U × V

uv : U × V
uv  = < u , v >

lemma01 : π1  < u , v >   ≡ u
lemma01 = refl

lemma02 : π2  < u , v >   ≡ v
lemma02 = refl

lemma03 : (uv : U × V ) → < π1  uv , π2 uv >   ≡ uv
lemma03 uv = refl

lemma04 : (λ x →  f x ) u ≡  f u
lemma04 = refl

lemma05 : (λ  x → f x ) ≡  f
lemma05 = refl

nn = λ (x : U ) →  u
n1 = λ ( x : U ) →  f x

data Bool : Set where
  T : Bool 
  F : Bool

D : { U : Set } → U → U → Bool → U 
D u v T = u 
D u v F = v

data Int : Set where 
    zero : Int
    S : Int →  Int

pred : Int → Int
pred zero = zero
pred (S t) = t

R : { U : Set } → U → ( U → Int → U ) → Int → U
R u v zero = u 
R u v ( S t ) = v (R u v t) t

null : Int → Bool
null zero = T
null (S _)  = F

It : { T : Set } → T → (T → T) → Int → T
It u v zero = u
It u v ( S t ) = v (It u v t )

R' : { T : Set } → T → ( T → Int → T ) → Int → T
R' u v t = π1 ( It ( < u , zero > ) (λ x →  < v (π1 x) (π2 x) , S (π2 x) > ) t )

sum : Int → Int → Int
sum x y = R y ( λ z → λ w → S z ) x

sum2 : Int → Int → Int
sum2 zero x = x
sum2 (S x) y = S ( sum2 x y )

cong1 : { x y :  Int } -> ( f : Int -> Int ) ->  x ≡ y -> f x ≡ f y 
cong1 {x} {.x} f refl = refl

lemma1 : ( x y : Int ) → sum x y  ≡ sum2 x y
lemma1 zero y  = refl
lemma1 (S x) y = cong1 ( λ z -> S z ) ( lemma1 x y )

mul : Int → Int → Int
mul x y = R zero ( λ z → λ w → sum y z ) x 

sum' : Int → Int → Int
sum' x y = R' y ( λ z → λ w → S z ) x

mul' : Int → Int → Int
mul' x y = R' zero ( λ z → λ w → sum y z ) x

fact : Int → Int
fact  n = R  (S zero) (λ z → λ w → mul (S w) z ) n

fact' : Int → Int
fact' n = R' (S zero) (λ z → λ w → mul (S w) z ) n

f3 = fact (S (S (S zero)))
f3' = fact' (S (S (S zero)))

lemma21 : f3 ≡ f3'
lemma21 = refl

lemma07 : { U : Set } → ( u : U ) → ( v : U → Int → U ) →( t :  Int ) → 
        (π2 (It < u , zero > (λ x → < v (π1 x) (π2 x) , S (π2 x) >) t )) ≡  t
lemma07 u v zero   =  refl
lemma07 u v (S t)  =  cong ( λ x → S x ) ( lemma07 u v t )

lemma06 : { U : Set } → ( u : U ) → ( v : U → Int → U ) →( t :  Int ) → ( (R u v t) ≡  (R' u v t ))
lemma06 u v zero = refl 
lemma06 u v (S t) =  trans  ( cong ( λ x →  v x t )  ( lemma06 u v t ) ) 
                            ( cong ( λ y →  v (R' u v t) y ) (sym ( lemma07 u v t ) ) )

lemma08 : ( n m : Int ) → ( sum' n m ≡ sum n m )
lemma08 zero _ = refl 
lemma08 (S t) y =  cong ( λ x → S x ) ( lemma08 t y ) 

lemma09 : ( n m : Int ) → ( mul' n m ≡ mul n m )
lemma09 zero _ = refl 
lemma09 (S t) y =  cong ( λ x → sum y x) ( lemma09 t y ) 

lemma10 : ( n : Int ) → ( fact n  ≡ fact n )
lemma10 zero = refl 
lemma10 (S t) =  cong ( λ x → mul (S t) x ) ( lemma10 t ) 

lemma11 : ( n : Int ) → ( fact n  ≡ fact' n )
lemma11 n = lemma06 (S zero) (λ z → λ w → mul (S w) z ) n

lemma06' : { U : Set } → ( u : U ) → ( v : U → Int → U ) →( t :  Int ) → ( (R u v t) ≡  (R' u v t ))
lemma06' u v zero = refl
lemma06' u v (S t) = let open ≡-Reasoning in 
   begin 
       R u v (S t)
   ≡⟨⟩
       v (R u v t) t
   ≡⟨ cong (λ x → v x t ) ( lemma06' u v t )  ⟩
       v (R' u v t) t
   ≡⟨ cong (λ x → v (R' u v t) x ) ( sym ( lemma07 u v t )) ⟩
       v (R' u v t) (π2 (It < u , zero > (λ x → < v (π1 x) (π2 x) , S (π2 x) >) t))
   ≡⟨⟩
       R' u v (S t)
   ∎


sum1 : (x y : Int) → sum x (S y)  ≡ S (sum x y )
sum1 zero y = refl
sum1 (S x) y = cong (λ x → S x ) (sum1  x y )

sum-sym : (x y : Int) → sum x y  ≡ sum y x
sum-sym zero zero = refl
sum-sym zero (S t) = cong (λ x → S x )( sum-sym zero t)
sum-sym (S t) zero = cong (λ x → S x ) ( sum-sym t zero )
sum-sym (S t) (S t') =  let open ≡-Reasoning in 
   begin 
       sum (S t) (S t')
   ≡⟨⟩
       S (sum t (S t')) 
   ≡⟨ cong ( λ x → S x ) ( sum1 t t') ⟩
       S ( S (sum t t')) 
   ≡⟨ cong ( λ x → S (S x ) ) ( sum-sym t t') ⟩
       S ( S (sum t' t)) 
   ≡⟨ sym ( cong ( λ x → S x ) ( sum1 t' t)) ⟩
       S (sum t' (S t)) 
   ≡⟨⟩
       R (S t) ( λ z → λ w → S z ) (S t')
   ≡⟨⟩
       sum (S t') (S t)
   ∎

sum-assoc : (x y z : Int) → sum x (sum y z ) ≡ sum (sum x y)  z 
sum-assoc zero y z  = refl
sum-assoc (S x) y z =  let open ≡-Reasoning in
   begin
     sum (S x) ( sum y z )
   ≡⟨⟩
     S ( sum x ( sum y z ) )
   ≡⟨ cong (λ x → S x ) ( sum-assoc x y z) ⟩
     S ( sum (sum x y) z )
   ≡⟨⟩
     sum (S ( sum x y)) z
   ≡⟨⟩
     sum (sum (S x) y) z
   ∎

mul-distr1 : (x y : Int) → mul x (S y) ≡ sum x ( mul x y )
mul-distr1 zero y = refl
mul-distr1 (S x) y =   let open ≡-Reasoning in
   begin
     mul (S x) (S y)
   ≡⟨⟩
     sum (S y) (mul x (S y))
   ≡⟨⟩
     S (sum y (mul x (S y)  ))
   ≡⟨ cong (λ t → S ( sum y t )) (mul-distr1 x y ) ⟩
     S (sum y (sum x (mul x y)))
   ≡⟨ cong (λ x → S x ) (
   begin
     sum y (sum x (mul x y))
   ≡⟨ sum-assoc y x (mul x y) ⟩
     sum (sum y x) (mul x y)
   ≡⟨ cong (λ t → sum t (mul x y)) (sum-sym y x ) ⟩
     sum (sum x y) (mul x y)
   ≡⟨ sym ( sum-assoc x y (mul x y)) ⟩
     sum x (sum y (mul x y))
   ∎
   ) ⟩
     S (sum x (sum y (mul x y) ))
   ≡⟨⟩
     S (sum x (mul (S x) y ) )
   ≡⟨⟩
     sum (S x) (mul (S x) y)
   ∎

mul-sym0 : (x : Int) → mul zero x  ≡ mul x zero 
mul-sym0 zero = refl
mul-sym0 (S x) =  mul-sym0 x

mul-sym : (x y : Int) → mul x y  ≡ mul y x
mul-sym zero x =  mul-sym0 x
mul-sym (S x) y =  let open ≡-Reasoning in
   begin
      mul (S x) y
   ≡⟨⟩
     sum y (mul x y )
   ≡⟨ cong ( λ x → sum y x ) (mul-sym x y ) ⟩
     sum y (mul y x)
   ≡⟨ sym ( mul-distr1 y x ) ⟩
     mul y (S x) 
   ∎


mul-ditr : (y z w : Int) → sum (mul y z) ( mul w z ) ≡ mul (sum y w)  z
mul-ditr y zero w =  let open ≡-Reasoning in
   begin
      sum (mul y zero) ( mul w zero ) 
   ≡⟨ cong ( λ t → sum (mul y zero ) t ) (mul-sym w zero ) ⟩
      sum (mul y zero ) ( mul zero w ) 
   ≡⟨ cong ( λ t → sum t zero ) (mul-sym y zero ) ⟩
      sum zero zero 
   ≡⟨⟩
      mul zero (sum y w) 
   ≡⟨  mul-sym0 (sum y w)  ⟩
      mul (sum y w)  zero
   ∎
mul-ditr y (S z) w =  let open ≡-Reasoning in
   begin
      sum (mul y (S z)) ( mul w (S z) )
   ≡⟨ cong ( λ t → sum t ( mul w (S z ))) (mul-distr1 y z) ⟩
      sum (  sum y ( mul y z)) ( mul w (S z) )
   ≡⟨ cong ( λ t → sum (  sum y ( mul y z)) t ) (mul-distr1 w z) ⟩
      sum (  sum y ( mul y z)) ( sum w ( mul w z) )
   ≡⟨ sym ( sum-assoc y (mul y z ) ( sum w ( mul w z) ) ) ⟩
      sum  y ( sum ( mul y z) ( sum w ( mul w z) ))
   ≡⟨ cong ( λ t → sum  y t) (sum-sym ( mul y z)  ( sum w ( mul w z) )) ⟩
      sum  y ( sum  ( sum w ( mul w z) )( mul y z))
   ≡⟨  sym ( cong ( λ t → sum  y t) (sum-assoc w (mul w z) (mul y z )) ) ⟩
      sum  y ( sum  w  (sum ( mul w z) ( mul y z)) )
   ≡⟨  cong ( λ t → sum  y (sum w t) ) ( sum-sym (mul w z) (mul y z ))  ⟩
      sum  y ( sum  w  (sum ( mul y z) ( mul w z)) )
   ≡⟨  cong ( λ t → sum  y (sum w t) ) ( mul-ditr y z w )  ⟩
      sum  y ( sum  w  (mul (sum y w)  z) )
   ≡⟨ sum-assoc y w (mul (sum y w)  z) ⟩
      sum (sum y w) ( mul (sum y w)  z )
   ≡⟨ sym ( mul-distr1 (sum y w) z ) ⟩
      mul (sum y w) (S z) 
   ∎


mul-assoc : (x y z : Int) → mul x (mul y z ) ≡ mul (mul x y)  z 
mul-assoc zero y z = refl
mul-assoc (S x) y z =  let open ≡-Reasoning in
   begin
      mul (S x) (mul y z )
   ≡⟨⟩
      sum (mul y z) ( mul x ( mul y z ) )
   ≡⟨ cong (λ t → sum (mul y z) t ) (mul-assoc x y z ) ⟩
      sum (mul y z) ( mul ( mul x y) z ) 
   ≡⟨ mul-ditr y z (mul x y) ⟩
      mul (sum y (mul x y))  z
   ≡⟨⟩
      mul (mul (S x) y)  z
   ∎




