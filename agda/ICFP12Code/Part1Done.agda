










                         {- Agda-curious? -}

                         {- Conor McBride -}

          {- Mathematically Structured Programming Group -}
        {- Department of Computer and Information Sciences -}
                   {- University of Strathclyde -}












module Part1Done where

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

data Expr : Set where
  val   : Nat ->             Expr
  _+'_  : (e1 e2 : Expr) ->  Expr

eval_ : Expr -> Nat
eval (val y)      = y
eval (e1 +' e2)  = eval e1 + eval e2

data List (X : Set) : Set where
  [] : List X
  _,_ : X -> List X -> List X
infixr 4 _,_

_++_ : forall {X} -> List X -> List X -> List X
[]        ++ ys  = ys
(x , xs)  ++ ys  = x , (xs ++ ys)
infixr 4 _++_

data Inst : Set where
  PUSH  : (v : Nat) ->  Inst
  ADD   :               Inst

compile : Expr -> List Inst
compile (val y)     = PUSH y , []
compile (e1 +' e2)  = compile e1 ++ compile e2 ++ ADD , []

run : List Inst -> List Nat -> List Nat
run []              vs              = vs
run (PUSH v  , is)  vs              = run is (v , vs)
run (ADD     , is)  []              = {!!}
run (ADD     , is)  (v  , [])       = {!!}
run (ADD     , is)  (v2 , v1 , vs)  = run is (v1 + v2 , vs)

