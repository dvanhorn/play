module DTP where

module Ch1 where

-- My (DVH) solutions the Vectors and Finite Sets chapter of
-- Dependently Typed Programming: an Agda introduction, Feb 21, 2011
-- edition, by Conor McBride.

-- I'm sure there are plenty of improvements to be made, so comments
-- are very welcome.  Please send to dvanhorn at ccs dot neu dot edu.

-- Thanks,
-- David

-- § 1.0

data List (X : Set) : Set where
  nil : List X
  cons : X -> List X -> List X

zap : {X Y : Set} -> List (X -> Y) -> List X -> List Y
zap nil nil = nil
zap (cons f fs) (cons x xs) = cons (f x) (zap fs xs)
zap _ _ = nil -- dummy

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

length : {X : Set} -> List X -> Nat
length nil = zero
length (cons x xs) = suc (length xs)

_+N_ : Nat -> Nat -> Nat
zero  +N y = y
suc n +N y = suc (n +N y)

_+L+_ : {X : Set} -> (List X) -> (List X) -> (List X)
nil +L+ ys = ys
cons x xs +L+ ys = cons x (xs +L+ ys)

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

-- proof of "informal" claim about append and length.
lemAppend : {X : Set} -> (xs ys : List X) ->
  length (xs +L+ ys) == (length xs +N length ys)
lemAppend nil ys = refl
lemAppend (cons x xs) ys rewrite lemAppend xs ys = refl

sucLem : (x y : Nat) -> (x +N suc y) == suc (x +N y)
sucLem zero y = refl
sucLem (suc x) y rewrite sucLem x y = refl

-- Ex 1.1
_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc y *N m = m +N (y *N m)

-- Maybe there's a more idiomatic way to write unit tests, but this is
-- pretty cute and saved my ass a number of times.
test*N0 : (4 *N 3) == 12
test*N0 = refl

-- Some proofs from SF:

-- Inductive bool : Type :=
--   | true : bool
--   | false : bool.
data Bool : Set where
  false : Bool
  true  : Bool

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
zero =N zero = true
zero =N suc y = false
suc m =N zero = false
suc m =N suc n = m =N n

-- Theorem plus_O_n' : ∀n:nat, 0 + n = n.
-- Proof.
--   reflexivity. Qed.
Theorem:plus_Z_n : (n : Nat) -> (0 +N n) == n
Theorem:plus_Z_n n = refl

-- Theorem plus_1_l : ∀n:nat, 1 + n = S n.
-- Proof.
--   intros n. reflexivity. Qed.
Theorem:plus_S_n : (n : Nat) -> (1 +N n) == (suc n)
Theorem:plus_S_n n = refl

-- Theorem plus_O_n' : ∀n:nat, 0 + n = n.
-- Proof.
--   reflexivity. Qed.
Theorem:mult_Z_n : (n : Nat) -> (0 *N n) == 0
Theorem:mult_Z_n n = refl

-- Theorem plus_id_example : ∀n m:nat,
--   n = m →
--   n + n = m + m.
-- Proof.
--   intros n m. (* move both quantifiers into the context *)
--   intros H. (* move the hypothesis into the context *)
--   rewrite → H. (* Rewrite the goal using the hypothesis *)
--   reflexivity. Qed.
Theorem:plus_id : (n m : Nat) → (m == n) → (n +N n) == (m +N m)
Theorem:plus_id m .m refl = refl

-- Theorem plus_id_exercise : ∀n m o : nat,
--  n = m → m = o → n + m = m + o.
Theorem:plus_id_exercise : (n m o : Nat) →
  (n == m) → (m == o) → (n +N m) == (m +N o)
Theorem:plus_id_exercise .o .o o refl refl = refl

-- Theorem mult_0_plus : ∀n m : nat,
--   (0 + n) * m = n * m.
-- Proof.
--   intros n m.
--   rewrite → plus_O_n.
--   reflexivity. Qed.
Theorem:mult_Z_plus : (n m : Nat) → ((0 +N n) *N m) == (n *N m)
Theorem:mult_Z_plus n m = refl

-- Theorem mult_1_plus : ∀n m : nat,
--   (1 + n) * m = m + (n * m).
Theorem:mult_S_plus : (n m : Nat) -> ((1 +N n) *N m) == (m +N (n *N m))
Theorem:mult_S_plus n m = refl

-- Theorem plus_1_neq_0_firsttry : ∀n : nat,
--   beq_nat (n + 1) 0 = false.
Theorem:plus_S_neq_Z : (n : Nat) → ((n +N 1) =N 0) == false
Theorem:plus_S_neq_Z zero = refl
Theorem:plus_S_neq_Z (suc n) = refl

-- Theorem zero_nbeq_plus_1 : ∀n : nat,
--   beq_nat 0 (n + 1) = false.
Theorem:Z_!=_S : (n : Nat) -> (0 =N (n +N 1)) == false
Theorem:Z_!=_S zero = refl
Theorem:Z_!=_S (suc n) = refl

-- Theorem plus_0_r_firsttry : ∀n:nat,
--   n + 0 = n.
Theorem:plus_n_Z : (n : Nat) -> (n +N 0) == n
Theorem:plus_n_Z zero = refl
Theorem:plus_n_Z (suc n) rewrite Theorem:plus_n_Z n = refl

-- Ex 1.2
_-N_ : Nat -> Nat -> Nat
zero -N m = zero
suc n -N zero = suc n
suc n -N suc m = n -N m

-- Ex 1.3
_/N_ : Nat -> Nat -> Nat
x /N zero = zero -- dummy
x /N (suc d) = help x (suc d) where
  help : Nat -> Nat -> Nat
  help zero zero = suc zero
  help zero (suc e) = zero
  help (suc x) zero = suc (help x d)
  help (suc x) (suc e) = help x e

test-/N0 : (1 /N 1) == 1
test-/N0 = refl

test-/N1 : (2 /N 2) == 1
test-/N1 = refl

test-/N2 : (1 /N 2) == 0
test-/N2 = refl

test-/N3 : (13 /N 3) == 4
test-/N3 = refl

test-/N4 : (15 /N 3) == 5
test-/N4 = refl

test-/N5 : (1 /N 0) == 0
test-/N5 = refl

-- § 1.1

data Vec (X : Set) : Nat -> Set where
  nil : Vec X zero
  cons : {n : Nat} -> (x : X) -> (xs : Vec X n) -> Vec X (suc n)

vap : {n : Nat}{X Y : Set} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
vap nil nil = nil
vap (cons f fs) (cons x xs) = cons (f x) (vap fs xs)

vec : {n : Nat}{X : Set} -> X -> Vec X n
vec {zero} x = nil
vec {suc n} x = cons x (vec x)

_+V+_ : {n m : Nat}{X : Set} -> Vec X n -> Vec X m -> Vec X (n +N m)
nil +V+ ys = ys
cons x xs +V+ ys = cons x (xs +V+ ys)

-- stinker
-- how do you make this not stink?
{-
vrevapp : {m n : Nat}{X : Set} -> Vec X n -> Vec X m -> Vec X (n +N m)
vrevapp nil ys = ys
vrevapp (cons x xs) ys = {!vrevapp xs (cons x ys)!}
-}

vtraverse : {F : Set -> Set} ->
  ({X : Set} -> X -> F X) ->
  ({S T : Set} -> F (S -> T) -> F S -> F T) ->
  {n : Nat}{X Y : Set} ->
  (X -> F Y) -> Vec X n -> F (Vec Y n)
vtraverse pure over f nil = pure nil
vtraverse pure over f (cons x xs) = over (over (pure cons) (f x)) (vtraverse pure over f xs)

i : {X : Set} -> X -> X
i x = x

k : {X Y : Set} -> X -> Y -> X
k x y = x

vsum : {n : Nat} -> Vec Nat n -> Nat
vsum = vtraverse (k zero) _+N_ { Y = Nat } i

test-vsum0 : vsum nil == 0
test-vsum0 = refl

test-vsum1 : vsum (cons 5 nil) == 5
test-vsum1 = refl

test-vsum2 : vsum (cons 3 (cons 7 nil)) == 10
test-vsum2 = refl

vfoldr : {X Y : Set}{n : Nat} -> (X -> Y -> Y) -> Y -> Vec X n -> Y
vfoldr f b nil = b
vfoldr f b (cons x xs) = f x (vfoldr f b xs)

vfoldl : {X Y : Set}{n : Nat} -> (X -> Y -> Y) -> Y -> Vec X n -> Y
vfoldl f a nil = a
vfoldl f a (cons x xs) = vfoldl f (f x a) xs

vsum' : {n : Nat} -> Vec Nat n -> Nat
vsum' = vfoldr _+N_ zero

test-vsum'0 : vsum' nil == 0
test-vsum'0 = refl

test-vsum'1 : vsum' (cons 5 nil) == 5
test-vsum'1 = refl

test-vsum'2 : vsum' (cons 3 (cons 7 nil)) == 10
test-vsum'2 = refl

vsum'' : {n : Nat} -> Vec Nat n -> Nat
vsum'' = vfoldr _+N_ zero

test-vsum''0 : vsum'' nil == 0
test-vsum''0 = refl

test-vsum''1 : vsum'' (cons 5 nil) == 5
test-vsum''1 = refl

test-vsum''2 : vsum' (cons 3 (cons 7 nil)) == 10
test-vsum''2 = refl

-- Can't figure this out - even at less general type.
-- vfoldr' : {X : Set}{n : Nat} -> (X -> X -> X) -> X -> Vec X n -> X
-- vfoldr' f b xs = vtraverse (k b) f i xs

vid : {X : Set}{n : Nat} -> Vec X n -> Vec X n
vid = vtraverse i (\ f x -> f x) i

Matrix : Nat -> Nat -> Set -> Set
Matrix m n X = Vec (Vec X n) m

-- Ex 1.4
vvec : {m n : Nat}{X : Set} -> X -> Matrix m n X
vvec {m}{n} x = vec {m} (vec {n} x)

-- CMB: Now, can you express vvap non-recursively with vec and vap?
vvap : {m n : Nat}{X Y : Set} ->
  Matrix m n (X -> Y) -> Matrix m n X -> Matrix m n Y
vvap fss = vap (vap (vec vap) fss)

-- Ex 1.5
_+M_ : {m n : Nat} -> Matrix m n Nat -> Matrix m n Nat -> Matrix m n Nat
_+M_ xss = vvap (vvap (vvec _+N_) xss)

-- Ex 1.6
-- CMB: Can you make transpose with vtraverse?
transpose : {m n : Nat}{X : Set} -> Matrix m n X -> Matrix n m X
transpose = vtraverse vec vap i

test-transpose0 : transpose (vec {5} (vec {4} 0)) == (vec {4} (vec {5} 0))
test-transpose0 = refl

-- Ex 1.7
idrow : (w : Nat) -> (d : Nat) -> Vec Nat w
idrow zero d = nil
idrow (suc w) zero = cons 1 (vec 0)
idrow (suc w) (suc d) = cons 0 (idrow w d)

idMatrix : {n : Nat} -> Matrix n n Nat
idMatrix {n} = help n 0 where
  help : (m : Nat) -> (i : Nat) -> Vec (Vec Nat n) m
  help zero i = nil
  help (suc m) i = cons (idrow n i) (help m (suc i))

-- Neat that the size of the identity matrix is inferred in this test.
test11 : idMatrix == cons (cons 1 (cons 0 nil)) (cons (cons 0 (cons 1 nil)) nil)
test11 = refl

test-trans-trans-id : transpose (transpose (idMatrix {5})) == idMatrix
test-trans-trans-id = refl

test-trans-sq : transpose (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 nil)) nil))
  == cons (cons 1 (cons 3 nil)) (cons (cons 2 (cons 4 nil)) nil)
test-trans-sq = refl

-- Ex 1.8
_*V_ : {n : Nat} -> Vec Nat n -> Vec Nat n -> Vec Nat n
xs *V ys = vap (vap (vec _*N_) xs) ys

test-*V0 : ((cons 1 (cons 3 nil)) *V (cons 1 (cons 2 nil))) == (cons 1 (cons 6 nil))
test-*V0 = refl

dot : {n : Nat} -> Vec Nat n -> Vec Nat n -> Nat
dot xs ys = vsum (xs *V ys)

test-dot0 : dot (cons 1 (cons 3 nil)) (cons 1 (cons 2 nil)) == 7
test-dot0 = refl

-- computes A*(B⊤)
_*M⊤_ : {n m p : Nat} -> Matrix n m Nat -> Matrix p m Nat -> Matrix n p Nat
nil *M⊤ yss = nil
cons xs xss *M⊤ yss = cons (vap (vec (\ ys -> dot xs ys)) yss) (xss *M⊤ yss)

_*M_ : {n m p : Nat} -> Matrix n m Nat -> Matrix m p Nat -> Matrix n p Nat
xss *M yss = xss *M⊤ (transpose yss)

mA : Matrix 2 2 Nat
mA = (cons (cons 1 (cons 2 nil))
     (cons (cons 3 (cons 4 nil))
       nil))

mA^2 : Matrix 2 2 Nat
mA^2 = (cons (cons 7 (cons 10 nil))
       (cons (cons 15 (cons 22 nil))
         nil))

test-M*0 : (mA *M mA) == mA^2
test-M*0 = refl

-- § 1.2

data Fin : Nat -> Set where
  zero : {n : Nat} → Fin (suc n)
  suc : {n : Nat} -> (i : Fin n) -> Fin (suc n)

foo : {X : Set}{n : Nat} -> Fin zero -> X
foo ()

fog : {n : Nat} -> Fin n -> Nat
fog zero = zero
fog (suc i) = suc (fog i)

vproj : {n : Nat}{X : Set} -> Vec X n -> Fin n -> X
vproj nil ()
vproj (cons x xs) zero = x
vproj (cons x xs) (suc i) = vproj xs i


weaken : {m n : Nat} -> (Fin m -> Fin n) -> Fin (suc m) -> Fin (suc n)
weaken f zero = zero
weaken f (suc i) = suc (f i)

thin : {n : Nat} -> Fin (suc n) -> Fin n -> Fin (suc n)
thin zero = suc
thin {zero} (suc ())
thin {suc n} (suc i) = weaken (thin i)

test-thin0 : thin (zero {1}) (zero {0}) == (suc {1} zero)
test-thin0 = refl

test-thin1 : thin (suc {1} zero) (zero {0}) == (zero {1})
test-thin1 = refl

test-thin2 : thin (suc {5} zero) (zero {4}) == (zero {5})
test-thin2 = refl

test-thin3 : thin (suc {5} zero) (suc {4} zero) == (suc {5} (suc zero))
test-thin3 = refl

-- Ex 1.9
vtab : {n : Nat}{X : Set} -> (Fin n -> X) -> Vec X n
vtab {zero} f = nil
vtab {suc y} f = cons (f zero) (vtab (\ i -> f (suc i)))

test-vtab0 : vtab fog == cons 0 (cons 1 (cons 2 nil))
test-vtab0 = refl

-- Ex 1.10
vplan : {n : Nat} -> Vec (Fin n) n
vplan = vtab i

test-vplan0 : vplan == cons zero (cons (suc zero) nil)
test-vplan0 = refl

-- Ex 1.11
max : {n : Nat} -> Fin (suc n)
max {zero} = zero
max {suc y} = suc (max {y})

test-max0 : max {3} == suc (suc (suc zero))
test-max0 = refl

-- Ex 1.12
emb : {n : Nat} -> Fin n -> Fin (suc n)
emb zero = zero
emb (suc i) = suc (emb i)

test_emb0 : fog (emb (zero {5})) == zero
test_emb0 = refl

test_emb1 : fog (emb (suc {5} zero)) == suc zero
test_emb1 = refl

-- Ex 1.13
data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  :      Maybe X

maybeap : {S T : Set} -> (S -> T) -> Maybe S -> Maybe T
maybeap f (yes x) = yes (f x)
maybeap f no = no

thick : {n : Nat} -> Fin (suc n) -> Fin (suc n) -> Maybe (Fin n)
thick {zero}  i       j       = no
thick {suc n} zero    zero    = no
thick {suc n} zero    (suc i) = yes i
thick {suc n} (suc i) zero    = yes i
thick {suc n} (suc i) (suc j) = maybeap suc (thick i j)

test-thick0 : thick {5} zero zero == no
test-thick0 = refl

test-thick1 : thick {5} zero (suc zero) == yes zero
test-thick1 = refl

-- Ex 1.14
-- ??
