module Part4Done where

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

data Ty : Set where bool nat : Ty

El : Ty -> Set
El bool = Bool
El nat = Nat

data Expr : Ty -> Set where
  val   : {t : Ty} -> El t -> Expr t
  _+'_  : (e1 e2 : Expr nat) ->  Expr nat
  if'_then_else  : {t : Ty}(e0 : Expr bool)(e1 e2 : Expr t) ->  Expr t

if_then_else_ : {T : Set} -> Bool -> T -> T -> T
if tt then t else f = t
if ff then t else f = f

eval_ : {t : Ty} -> Expr t -> El t
eval (val n)     = n
eval (e1 +' e2)  = eval e1 + eval e2
eval (if' e0  then e1 else e2) = if eval e0 then eval e1 else eval e2

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

record One : Set where
  constructor <>

SC : Set
SC = List {One} (\ i j -> Ty) <> <>

data Inst : Rel SC where
  PUSH  : {t : Ty} (v : El t) ->  {ts : SC} -> Inst ts       (t , ts)
  ADD   :                         {ts : SC} -> Inst (nat , nat , ts) (nat , ts)
  IFPOP : forall {ts ts'} ->
          List Inst ts ts' -> List Inst ts ts' -> Inst (bool , ts) ts'

compile : {t : Ty} -> Expr t -> {ts : SC} -> List Inst ts (t , ts)
compile (val y)     = PUSH y , []
compile (e1 +' e2)  = compile e1 ++ compile e2 ++ ADD , []
compile (if' e0 then e1 else e2) =
  compile e0 ++ IFPOP (compile e1) (compile e2) , []

data Elt : Rel SC where
  E : forall {t ts} -> El t -> Elt (t , ts) ts

run : forall {ts ts'} -> List Inst ts ts' -> List Elt ts [] -> List Elt ts' []
run []              vs              = vs
run (PUSH v  , is)  vs              = run is (E v , vs)
run (ADD     , is)  (E v2 , E v1 , vs)  = run is (E 0 , vs)
run (IFPOP is1 is2 , is) (E tt , vs) = run is (run is2 vs)
run (IFPOP is1 is2 , is) (E ff , vs) = run is (run is1 vs)
