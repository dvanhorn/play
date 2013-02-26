module Hole where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

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

data List (X : Set) : Set where
  [] : List X
  _::_ : X -> List X -> List X

data Pair (X Y : Set) : Set where
  pair : X -> Y -> Pair X Y

{- START -}

data _∈_ {A : Set}(x : A) : List A -> Set where
  hd : forall {xs} -> x ∈ (x :: xs)
  tl : forall {y xs} -> x ∈ xs -> x ∈ (y :: xs)

length : forall {A} -> (List A) -> Nat
length [] = 0
length (x :: xs) = suc (length xs)

index : forall {A}{x : A}{xs} -> x ∈ xs -> Nat
index hd = zero
index (tl p) = suc (index p)

_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

data Lookup {A : Set}(xs : List A) : Nat -> Set where
  inside  : (x : A) -> (p : x ∈ xs) -> Lookup xs (index p)
  outside : (m : Nat) -> Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : Nat) -> Lookup xs n
[] ! n = outside n
(x :: xs) ! zero = inside x hd
(x :: xs) ! suc n with xs ! n
(x :: xs) ! suc .(index p) | inside y p = inside y (tl p)
(x :: xs) ! suc .(length xs + n) | outside n = outside n

data Type : Set where
  nat : Type
  _=>_ : Type -> Type -> Type

data Equal? : Type -> Type -> Set where
  yes : forall {τ} -> Equal? τ τ
  no : forall {σ τ} -> Equal? σ τ

_=?=_ : (σ τ : Type) -> Equal? σ τ
nat =?= nat      = yes
(_ => _) =?= nat = no
nat =?= (_ => _) = no
(a => b) =?= (c => d) with a =?= c | b =?= d
(a => b) =?= (.a => .b)  | yes     | yes = yes
(a => b) =?= (c => d)    | _       | _   = no

Ctx = List Type

data Expr : Set where
  ● : Type -> Expr
  nat : Nat -> Expr
  var : Nat -> Expr
  app : Expr -> Expr -> Expr
  lam : Type -> Expr -> Expr
  if : Expr -> Expr -> Expr -> Expr

data Term (Γ : Ctx) : Type -> Set where
  ● : (τ : Type) -> Term Γ τ
  nat : (n : Nat) -> Term Γ nat
  var : {τ : Type} -> τ ∈ Γ -> Term Γ τ
  app : {τ σ : Type} -> Term Γ (σ => τ) -> Term Γ σ -> Term Γ τ
  lam : (σ : Type) -> {τ : Type} -> Term (σ :: Γ) τ -> Term Γ (σ => τ)
  if : {σ τ : Type} -> Term Γ σ -> Term Γ τ -> Term Γ τ -> Term Γ τ

data Refine (Γ : Ctx) : Type -> Set where
  refl : {τ : Type} -> Term Γ τ -> Refine Γ τ
  -- trans : (e : Refine Γ τ) -> (f : Refine Γ τ)
  hole : {τ : Type} -> Refine Γ τ

p : Term (nat :: []) nat
p = var hd
-- test = var hd

erase : {Γ : Ctx} -> {τ : Type} -> Term Γ τ -> Expr
erase (● τ)  = ● τ
erase (nat n) = nat n
erase (var x) = var (index x)
erase (app t u) = app (erase t) (erase u)
erase (lam σ t) = lam σ (erase t)
erase (if t1 t2 t3) = if (erase t1) (erase t2) (erase t3)

data Infer (Γ : Ctx) : Expr -> Set where
  ok : (τ : Type) -> (t : Term Γ τ) -> Infer Γ (erase t)
  bad : {e : Expr} -> Infer Γ e

infer : (Γ : Ctx) (e : Expr) -> Infer Γ e
infer Γ (● τ)   = ok τ (● τ)
infer Γ (nat n) = ok nat (nat n)
infer Γ (var x)
  with Γ ! x
infer Γ (var .(length Γ + n)) | outside n = bad
infer Γ (var .(index x))      | inside σ x = ok σ (var x)
infer Γ (app e1 e2)
  with infer Γ e1
infer Γ (app e1 e2)          | bad = bad
infer Γ (app .(erase t1) e2) | ok nat t1 = bad
infer Γ (app .(erase t1) e2) | ok (σ => τ) t1
  with infer Γ e2
infer Γ (app .(erase t1) e2) | ok (σ => τ) t1 | bad = bad
infer Γ (app .(erase t1) .(erase t2)) | ok (σ => τ) t1 | ok σ' t2
  with σ =?= σ'
infer Γ (app .(erase t1) .(erase t2))
  | ok (σ => τ) t1 | ok .σ t2 | yes = ok τ (app t1 t2)
infer Γ (app .(erase t1) .(erase t2))
  | ok (σ => τ) t1 | ok σ' t2 | no = bad
infer Γ (lam σ e)
  with infer (σ :: Γ) e
infer Γ (lam σ .(erase t)) | ok τ t = ok (σ => τ) (lam σ t)
infer Γ (lam σ e)          | bad    = bad
infer Γ (if e1 e2 e3)
  with infer Γ e1
infer Γ (if e1 e2 e3) | bad = bad
infer Γ (if .(erase t1) e2 e3) | ok σ t1
  with infer Γ e2
infer Γ (if .(erase t1) e2 e3) | ok σ t1 | bad = bad
infer Γ (if .(erase t1) .(erase t2) e3) | ok σ t1 | ok τ t2
  with infer Γ e3
infer Γ (if .(erase t1) .(erase t2) e3) | ok σ t1 | ok τ t2 | bad = bad
infer Γ (if .(erase t1) .(erase t2) .(erase t3)) | ok σ t1 | ok τ t2 | ok τ' t3
  with τ =?= τ'
infer Γ (if .(erase t1) .(erase t2) .(erase t3))
  | ok σ t1 | ok τ t2 | ok .τ t3 | yes = ok τ (if t1 t2 t3)
infer Γ (if .(erase t1) .(erase t2) .(erase t3))
  | ok σ t1 | ok τ t2 | ok τ' t3 | no = bad

test0 = (infer [] (● nat)) == ok nat (● nat)
test1 = (infer [] (nat 7)) == ok nat (nat 7)
test2 = (infer [] (lam nat (var 0))) == ok (nat => nat) (lam nat (var hd))
test3 = (infer (nat :: []) (var 0)) == ok nat (var hd)
test4 = (infer [] (app (nat 7) (nat 7))) == bad
