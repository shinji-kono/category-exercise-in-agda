module tmp1 where

data  TwoObject   : Set  where
       t0 : TwoObject
       t1 : TwoObject

data TwoArrow  : TwoObject → TwoObject → Set  where
       f0 :  TwoArrow t0 t1
       f1 :  TwoArrow t0 t1

data ⊥ : Set where
⊥-elim : {A : Set } -> ⊥ -> A
⊥-elim ()

¬_ : Set → Set
¬ A = A → ⊥

l1 : TwoArrow t0 t1
l1 = f0

ln : ¬ ( TwoArrow t0 t0 )
ln ()
