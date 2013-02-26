module AgdaBasics where

data Bool : Set where
  true : Bool
  false : Bool

t : {A : Set} -> A -> A -> A
t x y = x

f : {A : Set} -> A -> A -> A
f x y = y

not : ({A : Set} -> A -> A -> A) -> ({A : Set} -> A -> A -> A)
not b = \x y -> b y x

--and : ({A : Set} -> A -> A -> A) -> ({A : Set} -> A -> A -> A) -> ({A : Set} -> A -> A -> A)
--and b b' = \x y -> {!!}

f' : {A : Set} -> A -> A -> A
f' = not t

id : (A : Set) -> A -> A
id A x = x

blah : (A : Set) -> A -> A
blah A = id (A -> A) (id A)

id' : {A : Set} -> A -> A
id' x = x

blah' : {A : Set} -> A -> A
blah' = id' id'

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

data List (A : Set) : Set where
  []   :                List A
  _::_ : A -> List A -> List A

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (succ n)

head : {A : Set}{n : Nat} -> Vec A (succ n) -> A
head (x :: xs) = x

data Vec' (A : Set) : Nat -> Set where
  nil : Vec' A zero
  cons : (n : Nat) -> A -> Vec' A n -> Vec' A (succ n)

head' : (A : Set)(n : Nat) -> Vec' A (succ n) -> A
head' A n (cons .n x xs) = x

vmap : {A B : Set}(n : Nat) -> (A -> B) -> Vec' A n -> Vec' B n
vmap .zero f nil = nil
vmap .(succ n) f (cons n x xs) = cons n (f x) (vmap n f xs)


data Image_∋_ {A B : Set}(f : A -> B) : B -> Set where
  im : (x : A) -> Image f ∋ f x

inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
inv f .(f x) (im x) = x

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (succ n)
  fsucc : {n : Nat} -> Fin n -> Fin (succ n)

_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
[] ! ()
(x :: xs) ! fzero = x
(x :: xs) ! (fsucc i) = xs ! i

vid : (A : Set)(n : Nat) -> (Vec' A n) -> (Vec' A n)
vid A zero nil = nil
vid A (succ n) (cons .n x xs) = (cons n x xs)

_∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
      (f : {x : A}(y : B x) -> C x y) (g : (x : A) -> B x)
      (x : A) -> C x (g x)
(f ∘ g) x = f (g x)

plus-two = succ ∘ succ

tabulate : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
tabulate {zero} f = []
tabulate {succ n} f = f fzero :: tabulate (f ∘ fsucc)

data False : Set where
record True : Set where

trivial : True
trivial = _

isTrue : Bool -> Set
isTrue true = True
isTrue false = False

_<_ : Nat -> Nat -> Bool
_      < zero   = false
zero   < succ n = true
succ m < succ n = m < n

length : {A : Set} -> List A -> Nat
length [] = zero
length (x :: xs) = succ (length xs)

lookup : {A : Set}(xs : List A)(n : Nat) ->
  isTrue (n < length xs) -> A
lookup [] n ()
lookup (x :: xs) zero     p = x
lookup (x :: xs) (succ n) p = lookup xs n p

ls : List Nat
ls = succ zero :: (zero :: [])

o : Nat
o = lookup ls (succ zero) _

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x


data _≤_ : Nat -> Nat -> Set where
  leq-zero : {n : Nat} -> zero ≤ n
  leq-succ : {m n : Nat} -> m ≤ n -> succ m ≤ succ n

{-

-}
