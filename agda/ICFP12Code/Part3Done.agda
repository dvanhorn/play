module Part3Done where

{- Here be numbers -}

data Nat : Set where
  zero  :               Nat
  suc   : (n : Nat) ->  Nat

_+_ : Nat -> Nat -> Nat
zero   + m = m
suc n  + m = suc (n + m)

infixr 5 _+_
{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

one = 1
two = 2

data Bool : Set where tt ff : Bool

if_then_else_ : {T : Set} -> Bool -> T -> T -> T
if tt then t else f = t
if ff then t else f = f

data Expr : Set where
  val   : Nat ->             Expr
  boo   : Bool -> Expr
  _+'_  : (e1 e2 : Expr) ->  Expr
  if'_then_else_ : (e0 e1 e2 : Expr) -> Expr

data Val : Set where
  VN : Nat -> Val
  VB : Bool -> Val

eval_ : Expr -> Val
eval (val y)      = VN y
eval (boo b)      = VB b
eval (e1 +' e2) with eval e1 | eval e2
eval (e1 +' e2) | VN y | VN y' = VN (y + y')
eval (e1 +' e2) | VN y | VB y' = {!!}
eval (e1 +' e2) | VB y | v2 = {!!}
eval (if' e0 then e1 else e2) = {!!} -- if eval e0 then eval e1 else e2

{-
{- Plan: index by initial and final stack configuration -}

Rel : Set -> Set1
Rel I = I -> I -> Set

data List {I : Set}(X : Rel I) : Rel I where
  [] : {i : I} -> List X i i
  _,_ : {i j k : I} -> X i j -> List X j k -> List X i k
infixr 4 _,_

_++_ : forall {I}{X : Rel I}{i j k : I} ->
       List X i j -> List X j k -> List X i k
[]        ++ ys  = ys
(x , xs)  ++ ys  = x , (xs ++ ys)
infixr 4 _++_

data Inst : Rel Nat where
  PUSH  : (v : Nat) ->  {n : Nat} -> Inst n       (1 + n)
  ADD   :               {n : Nat} -> Inst (2 + n) (1 + n)

compile : Expr -> {n : Nat} -> List Inst n (1 + n)
compile (val y)     = PUSH y , []
compile (e1 +' e2)  = compile e1 ++ compile e2 ++ ADD , []

data V (X : Set) : Rel Nat where
  E : X -> {n : Nat} -> V X (1 + n) n

run : forall {i j} -> List Inst i j -> List (V Nat) i 0 -> List (V Nat) j 0
run []              vs              = vs
run (PUSH v  , is)  vs              = run is (E v , vs)
run (ADD     , is)  (E v2 , E v1 , vs)  = run is (E (v1 + v2) , vs)

-}