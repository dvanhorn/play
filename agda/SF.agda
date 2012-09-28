-- Software Foundations in Agda
module SF where

-- Prove yourself
-- Prove yourself
-- Prove yourself
--
-- Y?

-- Ch. Basics
data Nat : Set where
  zero : Nat
  suc : (n : Nat) -> Nat

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


_+N_ : Nat -> Nat -> Nat
zero  +N y = y
suc n +N y = suc (n +N y)

-- Fixpoint minus (n m:nat) : nat :=
--   match n, m with
--   | O , _ => O
--   | S _ , O => n
--   | S n', S m' => minus n' m'
--   end.
_*N_ : Nat -> Nat -> Nat
zero  *N m = zero
suc n *N m = m +N (n *N m)


-- Fixpoint minus (n m:nat) : nat :=
--   match n, m with
--   | O , _ => O
--   | S _ , O => n
--   | S n', S m' => minus n' m'
--   end.
_-N_ : Nat -> Nat -> Nat
zero  -N m = zero
n     -N zero = n
suc n -N suc m = n -N m


-- Inductive bool : Type :=
--   | true : bool
--   | false : bool.
data Bool : Set where
  false : Bool
  true  : Bool

-- Definition negb (b:bool) : bool :=
--   match b with
--   | true => false
--   | false => true
--   end.
¬ : Bool -> Bool
¬ true  = false
¬ false = true

-- Definition andb (b1:bool) (b2:bool) : bool :=
--   match b1 with
--   | true => b2
--   | false => false
--   end.
_∧_ : Bool -> Bool -> Bool
true  ∧ b = b
false ∧ b = false

-- Definition orb (b1:bool) (b2:bool) : bool :=
--   match b1 with
--   | true => true
--   | false => b2
--   end.
_∨_ : Bool -> Bool -> Bool
true  ∨ b = true
false ∨ b = b

-- Fixpoint beq_nat (n m : nat) : bool :=
--   match n with
--   | O => match m with
--          | O => true
--          | S m' => false
--          end
--   | S n' => match m with
--             | O => false
--             | S m' => beq_nat n' m'
--             end
--   end.
_=N_ : (m n : Nat) → Bool
zero  =N zero  = true
zero  =N suc y = false
suc m =N zero  = false
suc m =N suc n = m =N n

-- Fixpoint ble_nat (n m : nat) : bool :=
--   match n with
--   | O => true
--   | S n' =>
--       match m with
--       | O => false
--       | S m' => ble_nat n' m'
--       end
--   end.
_<=_ : (n m : Nat) → Bool
zero  <= zero  = true
zero  <= suc n = true
suc n <= zero  = false
suc n <= suc m = n <= m

-- Example test_ble_nat1: (ble_nat 2 2) = true.
-- Proof. simpl. reflexivity. Qed.
-- Example test_ble_nat2: (ble_nat 2 4) = true.
-- Proof. simpl. reflexivity. Qed.
-- Example test_ble_nat3: (ble_nat 4 2) = false.
-- Proof. simpl. reflexivity. Qed.
test-<=-0 : (2 <= 2) == true
test-<=-0 = refl
test-<=-1 : (2 <= 4) == true
test-<=-1 = refl
test-<=-2 : (4 <= 2) == false
test-<=-2 = refl

-- Theorem plus_O_n' : ∀n:nat, 0 + n = n.
-- Proof.
--   reflexivity. Qed.
plus_Z_n : (n : Nat) -> (0 +N n) == n
plus_Z_n n = refl

-- Theorem plus_1_l : ∀n:nat, 1 + n = S n.
-- Proof.
--   intros n. reflexivity. Qed.
plus-S-n : (n : Nat) -> (1 +N n) == (suc n)
plus-S-n n = refl

-- Theorem plus_O_n' : ∀n:nat, 0 + n = n.
-- Proof.
--   reflexivity. Qed.
mult-Z-n : (n : Nat) -> (0 *N n) == 0
mult-Z-n = (\ n -> refl)

-- Theorem plus_id_example : ∀n m:nat,
--   n = m →
--   n + n = m + m.
-- Proof.
--   intros n m. (* move both quantifiers into the context *)
--   intros H. (* move the hypothesis into the context *)
--   rewrite → H. (* Rewrite the goal using the hypothesis *)
--   reflexivity. Qed.
plus_id : (n m : Nat) → (m == n) → (n +N n) == (m +N m)
plus_id m .m refl = refl

-- Theorem plus_id_exercise : ∀n m o : nat,
--  n = m → m = o → n + m = m + o.
plus_id_exercise : (n m o : Nat) ->
  (n == m) -> (m == o) -> (n +N m) == (m +N o)
plus_id_exercise .o .o o refl refl = refl

-- Theorem mult_0_plus : ∀n m : nat,
--   (0 + n) * m = n * m.
-- Proof.
--   intros n m.
--   rewrite → plus_O_n.
--   reflexivity. Qed.
mult_Z_plus : (n m : Nat) -> ((0 +N n) *N m) == (n *N m)
mult_Z_plus n m = refl

-- Theorem mult_1_plus : ∀n m : nat,
--   (1 + n) * m = m + (n * m).
mult_S_plus : (n m : Nat) -> ((1 +N n) *N m) == (m +N (n *N m))
mult_S_plus n m = refl

-- Theorem plus_1_neq_0_firsttry : ∀n : nat,
--   beq_nat (n + 1) 0 = false.
plus_S_neq_Z : (n : Nat) -> ((n +N 1) =N 0) == false
plus_S_neq_Z zero = refl
plus_S_neq_Z (suc n) = refl

-- Theorem zero_nbeq_plus_1 : ∀n : nat,
--   beq_nat 0 (n + 1) = false.
Z_!=_S : (n : Nat) -> (0 =N (n +N 1)) == false
Z_!=_S zero = refl
Z_!=_S (suc n) = refl

-- Theorem plus_0_r_firsttry : ∀n:nat,
--   n + 0 = n.
plus-n-Z : (n : Nat) -> (n +N 0) == n
plus-n-Z zero = refl
plus-n-Z (suc n) rewrite plus-n-Z n = refl

-- Theorem minus_diag : ∀n,
--   minus n n = 0.
-- Proof.
--   (* WORKED IN CLASS *)
--   intros n. induction n as [| n'].
--   Case "n = 0".
--     simpl. reflexivity.
--   Case "n = S n'".
--     simpl. rewrite → IHn'. reflexivity. Qed.
minus-diag : (n : Nat) -> (n -N n) == 0
minus-diag zero = refl
minus-diag (suc n) rewrite minus-diag n = refl

-- Theorem mult_0_r : ∀n:nat,
--   n * 0 = 0.
mult-n-Z : (n : Nat) -> (n *N 0) == 0
mult-n-Z zero = refl
mult-n-Z (suc n) rewrite mult-n-Z n = refl

-- Theorem plus_n_Sm : ∀n m : nat,
--   S (n + m) = n + (S m).
S-plus-n-m : (n m : Nat) -> (suc (n +N m)) == (n +N (suc m))
S-plus-n-m zero m = refl
S-plus-n-m (suc n) m rewrite S-plus-n-m n m = refl

-- Theorem plus_comm : ∀n m : nat,
--   n + m = m + n.
comm : {X : Set}{x y : X} -> (x == y) -> (y == x)
comm refl = refl

plus-comm : (n m : Nat) -> (n +N m) == (m +N n)
plus-comm n zero = plus-n-Z n
plus-comm n (suc m) rewrite comm (S-plus-n-m n m)
                            | plus-comm n m
                            = refl

-- Fixpoint double (n:nat) :=
--   match n with
--   | O => O
--   | S n' => S (S (double n'))
--   end.
double : Nat -> Nat
double zero = zero
double (suc n) = suc (suc (double n))

-- Lemma double_plus : ∀n, double n = n + n .
double-plus : (n : Nat) -> (double n) == (n +N n)
double-plus zero = refl
double-plus (suc n) rewrite comm (S-plus-n-m n n)
                    | double-plus n
                    = refl

-- Theorem plus_assoc' : ∀n m p : nat,
--   n + (m + p) = (n + m) + p.
-- Proof. intros n m p. induction n as [| n']. reflexivity.
--   simpl. rewrite → IHn'. reflexivity. Qed.
plus-assoc : (n m p : Nat) -> (n +N (m +N p)) == ((n +N m) +N p)
plus-assoc zero m p = refl
plus-assoc (suc n) m p rewrite plus-assoc n m p = refl

-- Theorem beq_nat_refl : ∀n : nat,
--   true = beq_nat n n.
=N-refl : (n : Nat) -> (true == (n =N n))
=N-refl zero = refl
=N-refl (suc n) rewrite =N-refl n = refl

-- Theorem mult_0_plus' : ∀n m : nat,
--   (0 + n) * m = n * m.
-- Proof.
--   intros n m.
--   assert (H: 0 + n = n).
--     Case "Proof of assertion". reflexivity.
--   rewrite → H.
--   reflexivity. Qed.
mult-Z-plus : (n m : Nat) -> ((0 +N n) *N m) == (n *N m)
mult-Z-plus zero m = refl
mult-Z-plus (suc n) m = refl

-- Theorem plus_rearrange : ∀n m p q : nat,
--   (n + m) + (p + q) = (m + n) + (p + q).
-- Proof.
--   intros n m p q.
--   assert (H: n + m = m + n).
--     Case "Proof of assertion".
--     rewrite → plus_comm. reflexivity.
--   rewrite → H. reflexivity. Qed.
plus-rearrange : (n m p q : Nat) ->
  ((n +N m) +N (p +N q)) == ((m +N n) +N (p +N q))
plus-rearrange n m p q rewrite plus-comm n m = refl

-- Theorem plus_swap : ∀n m p : nat,
--   n + (m + p) = m + (n + p).
plus-swap : (n m p : Nat) -> (n +N (m +N p)) == (m +N (n +N p))
plus-swap n m p rewrite plus-assoc n m p
  | plus-assoc m n p
  | plus-comm m n
  = refl

-- Theorem mult_comm : ∀m n : nat,
--  m * n = n * m.
push : (n m : Nat) -> (n *N (suc m)) == (n +N (n *N m))
push zero m = refl
push (suc n) m rewrite push n m
                    | plus-assoc n m (n *N m)
                    | plus-comm n m
                    | plus-assoc m n (n *N m)
                    = refl

mult-comm : (n m : Nat) -> (n *N m) == (m *N n)
mult-comm n zero = mult-n-Z n
mult-comm n (suc m) rewrite (push n m)
                    | mult-comm m n
                    = refl

-- Theorem ble_nat_refl : ∀n:nat,
--   true = ble_nat n n.
n<=n : (n : Nat) -> true == (n <= n)
n<=n zero = refl
n<=n (suc n) rewrite n<=n n = refl

-- Theorem zero_nbeq_S : ∀n:nat,
--   beq_nat 0 (S n) = false.
0=Sn-false : (n : Nat) -> (0 =N (suc n)) == false
0=Sn-false n = refl

-- Theorem andb_false_r : ∀b : bool,
--   andb b false = false.
b∧false-false : (b : Bool) -> (b ∧ false) == false
b∧false-false false = refl
b∧false-false true = refl

-- Theorem plus_ble_compat_l : ∀n m p : nat,
--   ble_nat n m = true → ble_nat (p + n) (p + m) = true.
weak-<= : (n m : Nat) -> (n <= (n +N m)) == true
weak-<= n zero rewrite plus-comm n 0
                       | n<=n n = refl
weak-<= zero (suc m) = refl
weak-<= (suc n) m rewrite weak-<= n m = refl

plus-<=-compat : (n m p : Nat) ->
  (n <= m) == true -> ((p +N n) <= (p +N m)) == true
plus-<=-compat zero zero p q rewrite n<=n (p +N 0) = q
plus-<=-compat (suc n) zero p ()
plus-<=-compat zero (suc m) p q rewrite plus-comm p 0
                                | weak-<= p (suc m) = refl
plus-<=-compat (suc n) (suc m) p q rewrite plus-comm p (suc n)
                                   | plus-comm p (suc m)
                                   | plus-comm n p
                                   | plus-comm m p
                                   | plus-<=-compat n m p q
                                   = refl

-- Theorem S_nbeq_0 : ∀n:nat,
--   beq_nat (S n) 0 = false.
Sn=0-false : (n : Nat) -> ((suc n) =N 0) == false
Sn=0-false n = refl

-- Theorem mult_1_l : ∀n:nat, 1 * n = n.
1*n=n : (n : Nat) -> (1 *N n) == n
1*n=n n rewrite plus-comm n 0 = refl

-- Theorem all3_spec : ∀b c : bool,
--     orb
--       (andb b c)
--       (orb (negb b)
--                (negb c))
--   = true.
all3-spec : (b c : Bool) -> ((b ∧ c) ∨ ((¬ b) ∨  (¬ c))) == true
all3-spec false false = refl
all3-spec false true = refl
all3-spec true false = refl
all3-spec true true = refl

-- Theorem mult_plus_distr_r : ∀n m p : nat,
--   (n + m) * p = (n * p) + (m * p).
mult-plus-distr : (n m p : Nat) ->
  ((n +N m) *N p) == ((n *N p) +N (m *N p))
mult-plus-distr zero m p = refl
mult-plus-distr (suc n) m p rewrite mult-plus-distr n m p
                            | plus-assoc p (n *N p) (m *N p)
                            = refl

-- Theorem mult_assoc : ∀n m p : nat,
--   n * (m * p) = (n * m) * p.
mult-assoc : (n m p : Nat) -> (n *N (m *N p)) == ((n *N m) *N p)
mult-assoc zero m p = refl
mult-assoc (suc n) m p rewrite mult-assoc n m p
                       | mult-plus-distr m (n *N m) p
                       = refl

-- Theorem bool_fn_applied_thrice :
--   ∀(f : bool → bool) (b : bool),
--   f (f (f b)) = f b.
bool-fn-thrice : (f : Bool -> Bool) -> (b : Bool) -> f (f (f b)) == f b
bool-fn-thrice f b = {!!}

data Fin : Nat -> Set where
  zero : {n : Nat} → Fin (suc n)
  suc : {n : Nat} -> (i : Fin n) -> Fin (suc n)

fog : {n : Nat} -> Fin n -> Nat
fog zero = zero
fog (suc i) = suc (fog i)

-- "bit strings of base n"
data Bits (n : Nat) : Set where
  [] : Bits n
  _::_ : (b : Fin n) -> (bs : Bits n) -> Bits n


carry : Bits 2 -> Bits 2
carry [] = suc zero :: []
carry (zero :: bs)         = suc zero :: bs
carry (suc zero :: bs)     = zero :: carry bs
carry (suc (suc ()) :: bs)

bsuc : Bits 2 -> Bits 2
bsuc [] = zero :: []
bsuc (zero :: bs)          = suc zero :: bs
bsuc (suc zero :: bs)      = zero :: carry bs
bsuc ((suc (suc ())) :: bs)

#0 : Fin 2
#0 = zero

#1 : Fin 2
#1 = suc zero

expt : {n : Nat} -> Nat -> Nat
expt zero = (suc zero)
expt {n} (suc p) = n *N (expt {n} p)

test-expt0 : expt {0} 0 == 1
test-expt0 = refl

test-expt1 : expt {1} 0 == 1
test-expt1 = refl

test-expt2 : expt {1} 1 == 1
test-expt2 = refl

test-expt3 : expt {2} 8 == 256
test-expt3 = refl

-- Don't try this at home
-- test-expt4 : expt {2} 32 == 4294967296
-- test-expt4 = refl

loop : {n : Nat} -> (Bits n) -> Nat -> Nat
loop {n} []        l = 0
loop {n} (b :: bs) l = ((fog b) *N (expt {n} l)) +N (loop {n} bs (suc l))

bits->nat : {n : Nat} -> Bits n -> Nat
bits->nat [] = 0
bits->nat bs = suc (loop bs 0)

loop-inv : {n : Nat} -> (b : Fin n) -> (bs : Bits n) -> (l : Nat) ->
  (loop (b :: bs) l) == (((fog b) *N (expt {n} l)) +N (loop bs (suc l)))
loop-inv b bs l = refl

plus-rid : (n : Nat) -> (n +N 0) == n
plus-rid zero = refl
plus-rid (suc n) rewrite plus-rid n = refl

loop-inv' : (bs : Bits 2) -> (l : Nat) ->
  (loop (carry bs) l) == ((expt {2} l) +N (loop bs l))
loop-inv' [] l rewrite plus-rid (expt {2} l)
               | plus-rid (expt {2} l)
               = refl
loop-inv' (zero :: bs) l rewrite plus-rid (expt {2} l) = refl
loop-inv' (suc zero :: bs) l rewrite plus-rid (expt {2} l) = {!!}
loop-inv' (suc (suc ()) :: bs) l

-- carry-lem : (b : Fin 2) -> (bs : Bits 2) ->
--   (suc (loop (carry (b :: bs)) 1)) == (suc (suc (suc (loop (b :: bs) 1))))
-- carry-lem bs = {!!}

test-b2n0 : ∀ (n : Nat) -> (bits->nat {n} [] == 0)
test-b2n0 n = refl

test-b2n1 : (bits->nat {2} (#0 :: [])) == 1
test-b2n1 = refl

test-b2n2 : (bits->nat {2} (#1 :: [])) == 2
test-b2n2 = refl

test-b2n3 : (bits->nat {2} (#0 :: (#1 :: []))) == 3
test-b2n3 = refl

test-b2n4 : (bits->nat {2} (#1 :: (#1 :: []))) == 4
test-b2n4 = refl

test-b2n5 : (bits->nat {2} (#0 :: (#0 :: (#1 :: [])))) == 5
test-b2n5 = refl

nat->bits : Nat -> Bits 2
nat->bits zero = []
nat->bits (suc n) = bsuc (nat->bits n)

nat-suc-round : (bs : Bits 2) ->
  bits->nat (bsuc bs) == suc (bits->nat {2} bs)
nat-suc-round [] = refl
nat-suc-round (zero :: bs) = {!!}
nat-suc-round (suc zero :: bs) = {!!}
nat-suc-round (suc (suc ()) :: bs)

nat-round : (n : Nat) -> n == (bits->nat {2} (nat->bits n))
nat-round zero = refl
nat-round (suc n) = {!!}

normalize : Bits 2 -> Bits 2
normalize bs = {!!}
