module Part5Done where

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

data Elt : Rel SC where
  E : forall {t ts} -> El t -> Elt (t , ts) ts

Stk : SC -> Set
Stk i = List Elt i []

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _&_
  field
    fst : S
    snd : T fst

data Inst : Rel (Sg SC Stk) where
  PUSH  : {t : Ty} (v : El t) -> forall {ts vs} ->
            Inst (ts & vs) ((t , ts) & (E v , vs))
  ADD   : {x y : Nat}{ts : SC}{vs : Stk ts} ->
            Inst ((nat , nat , ts) & (E y , E x , vs))
                  ((nat , ts) & (E (x + y) , vs))
  IFPOP : forall {ts vs ts' vst vsf b} ->
          List Inst (ts & vs) (ts' & vst)  -> List Inst (ts & vs) (ts' & vsf)
          -> Inst ((bool  , ts) & (E b , vs)) (ts' & if b then vst else vsf)

postulate
  Level : Set
  zl : Level
  sl : Level -> Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zl #-}
{-# BUILTIN LEVELSUC sl #-}

data _==_ {l : Level}{X : Set l}(x : X) : X -> Set l where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}


fact : forall {T S} -> (b : Bool)(t f : El T)(s : Stk S) ->
         (E (if b then t else f) , s) ==
         (if b then (E t , s) else (E f , s))
fact tt t f s = refl
fact ff t f s = refl

compile : {t : Ty} -> (e : Expr t) -> forall {ts vs} ->
   List Inst (ts & vs) ((t , ts) & (E (eval e) , vs))
compile (val y)     = PUSH y , []
compile (e1 +' e2)  = compile e1 ++ compile e2 ++ ADD , []
compile (if' e0 then e1 else e2) {vs = vs}
  rewrite fact (eval e0) (eval e1) (eval e2) vs
  = compile e0 ++ IFPOP (compile e1) (compile e2) , []

{-
run : forall {i j} -> List Inst i j -> List V i [] -> List V j []
run []              vs              = vs
run (PUSH v  , is)  vs              = run is (E v , vs)
run (ADD     , is)  (E v2 , E v1 , vs)  = run is (E (v1 + v2) , vs)
run (IFPOP is1 is2 , is) (E tt , vs) = run is (run is1 vs)
run (IFPOP is1 is2 , is) (E ff , vs) = run is (run is2 vs)
-}