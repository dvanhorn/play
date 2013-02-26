module SEWPR where

-- Bits of Chapter 1 of Semantics Engineering by Felleisen, Findler
-- and Flatt.

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

data _≡_ {l : Level}{X : Set l}(x : X) : X -> Set l where
  ≡-refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL ≡-refl #-}

{- START -}

data BEXP : Set where
  #t : BEXP
  #f : BEXP
  _●_ : BEXP -> BEXP -> BEXP

Rel : Set -> Set -> Set1
Rel A B = A -> B -> Set

data Id {A : Set} : Rel A A where
  refl : ∀ {x} -> Id x x

data _r_ : BEXP -> BEXP -> Set where
  r#f : {b : BEXP} -> (#f ● b) r b
  r#t : {b : BEXP} -> (#t ● b) r #t

tra : (#f ● #f) r #f
tra = r#f

data _≍r_ : BEXP -> BEXP -> Set where
  ra : {b : BEXP} -> (#f ● b) ≍r b
  rb : {b : BEXP} -> (#t ● b) ≍r #t
  rc : {b : BEXP} -> b ≍r b

data _≍r'_ : BEXP -> BEXP -> Set where
  rab : {b1 b2 : BEXP} -> (b1 r b2) -> b1 ≍r' b2
  rc : {b : BEXP} -> b ≍r' b

≍r=>≍r' : {b1 b2 : BEXP} -> (b1 ≍r b2) -> b1 ≍r' b2
≍r=>≍r' ra = rab r#f
≍r=>≍r' rb = rab r#t
≍r=>≍r' rc = rc

≍r'=>≍r : {b1 b2 : BEXP} -> (b1 ≍r' b2) -> b1 ≍r b2
≍r'=>≍r (rab r#f) = ra
≍r'=>≍r (rab r#t) = rb
≍r'=>≍r rc = rc

data _≈r_ : BEXP -> BEXP -> Set where
  rab : {b1 b2 : BEXP} -> (b1 r b2) -> b1 ≈r b2
  rc : {b : BEXP} -> b ≈r b
  rd : {b1 b2 : BEXP} -> (b1 ≈r b2) -> b2 ≈r b1
  re : {b1 b2 b3 : BEXP} -> (b1 ≈r b2) -> (b2 ≈r b3) -> b1 ≈r b3

data _~>r_ : BEXP -> BEXP -> Set where
  ra : {b : BEXP} -> b ~>r b
  rb : {b1 b2 : BEXP} -> (b1 r b2) -> b1 ~>r b2
  rc : {b1 b2 b3 : BEXP} -> (b1 ~>r b2) -> (b2 ~>r b3) -> (b1 ~>r b3)

eg0 : (#f ● (#f ● (#t ● #f))) ~>r #t
eg0 = rc (rc (rb r#f) (rb r#f)) (rb r#t)

-- Ex 1.2
eg1 : (#f ● (#f ● (#f ● #f))) ~>r #f
eg1 = rc (rc (rb r#f) (rb r#f)) (rb r#f)

data _->r_ : BEXP -> BEXP -> Set where
  ra : {b1 b2 : BEXP} -> (b1 r b2) -> b1 ->r b2
  rb : {b1 b1' : BEXP} -> (b1 ->r b1') -> {b2 : BEXP} -> (b1 ● b2) ->r (b1' ● b2)
  rc : {b2 b2' : BEXP} -> (b2 ->r b2') -> {b1 : BEXP} -> (b1 ● b2) ->r (b1 ● b2')

data _->>r_ : BEXP -> BEXP -> Set where
  refl : {b : BEXP} -> b ->>r b
  trans : {b1 b2 b3 : BEXP} -> b1 ->>r b2 -> b2 ->>r b3 -> b1 ->>r b3
  step : {b1 b2 : BEXP} -> b1 ->r b2 -> b1 ->>r b2

eg2 : ((#f ● #t) ● #f) ->r (#t ● #f)
eg2 = rb (ra r#f)

-- Ex 1.4
eg3 : (#f ● ((#t ● #f) ● #f)) ->>r #t
eg3 = trans (step (ra r#f)) (trans (step (rb (ra r#t))) (step (ra r#t)))

data RES : Set where
  #t : RES
  #f : RES

erase : RES -> BEXP
erase #t = #t
erase #f = #f

data _eval->>r_ : BEXP -> RES -> Set where
  ev : {r : RES} -> {b : BEXP} -> (b ->>r (erase r)) -> b eval->>r r

data _=r_ : BEXP -> BEXP -> Set where
  reduce : {b1 b2 : BEXP} -> b1 ->>r b2 -> b1 =r b2
  symm : {b1 b2 : BEXP} -> b1 =r b2 -> b2 =r b1
  trans : {b1 b2 b3 : BEXP} -> b1 =r b2 -> b2 =r b3 -> b1 =r b3

refl=r : {b : BEXP} -> b =r b
refl=r = reduce refl


data _eval=r_ : BEXP -> RES -> Set where
  ev : {r : RES} -> {b : BEXP} -> (b =r (erase r)) -> b eval=r r

-- Ex 1.6
eg4 : ((#f ● #t) ● #t) eval=r #t
eg4 = ev (reduce (trans (step (rb (ra r#f))) (step (ra r#t))))
eg5 : ((#f ● #t) ● #f) eval->>r #t
eg5 = ev (trans (step (rb (ra r#f))) (step (ra r#t)))


claim : {b : BEXP} -> {r0 r1 : RES} -> b eval=r r0 -> b eval=r r1 -> (erase r0) =r (erase r1)
claim (ev p) (ev q) = trans (symm p) q

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) -> B a -> Σ A B

∃ : {A : Set} (P : A -> Set) -> Set
∃ {A} = Σ A

_×_ : (A B : Set) -> Set
A × B = Σ A (\ _ -> B)

data _⋁_ (A B : Set) : Set where
  inj1 : A -> A ⋁ B
  inj2 : B -> A ⋁ B

proj1 : {A : Set} {B : A → Set} → Σ A B → A
proj1 (a , b) = a
proj2 : {A : Set} {B : A → Set} → (σ : Σ A B) → B (proj1 σ)
proj2 (a , b) = b


church-rosser : {L M N : BEXP} -> L ->>r M -> L ->>r N -> (∃ (\ (L' : BEXP) -> (M ->>r L') × (N ->>r L')))
church-rosser p q = {!!}

data _!=_ : BEXP -> BEXP -> Set where
  t!=f : #t != #f
  ●!=t : {b0 b1 : BEXP} -> (b0 ● b1) != #t
  ●!=f : {b0 b1 : BEXP} -> (b0 ● b1) != #t
  left : {b0 b0' : BEXP} -> (b0 != b0') -> {b1 : BEXP} -> (b0 ● b1) != (b0' ● b1)
  right : {b0 b0' : BEXP} -> (b0 != b0') -> {b1 : BEXP} -> (b0 ● b1) != (b0' ● b1)
  symm : {b0 b1 : BEXP} -> (b0 != b1) -> b1 != b0

data True : Set where
  tt : True

data False : Set where

falseElim : {A : Set} -> False -> A
falseElim ()

Not : Set -> Set
Not A = A -> False

sane : {L M N : BEXP} -> L r M -> L r N -> M ≡ N
sane r#f r#f = ≡-refl
sane r#t r#t = ≡-refl

irr-true : {B : BEXP} -> Not (#t ->r B)
irr-true (ra ())

irr-false : {B : BEXP} -> Not (#f ->r B)
irr-false (ra ())

ren->r : {L M : BEXP} -> L ≡ M -> {N : BEXP} -> (L ->r N) -> (M ->r N)
ren->r ≡-refl r = r

invr : {b1 b2 b3 : BEXP} -> (b1 ● b2) r b3 ->
  ((b1 ≡ #t) × (b3 ≡ #t)) ⋁
  ((b1 ≡ #f) × (b3 ≡ b2))
invr r#f = inj2 (≡-refl , ≡-refl)
invr r#t = inj1 (≡-refl , ≡-refl)

lem1 : {B N : BEXP} -> ((#f ● B) ->r N) -> (Not (B ≡ N)) ->
  (∃ (\ (B' : BEXP) -> (N ≡ (#f ● B')) × (B ->r B')))
lem1 (ra p) b!=n = falseElim (b!=n (sane r#f p))
lem1 (rb p) b!=n = falseElim (irr-false p)
lem1 (rc {_}{b'} p) b!=n = (b' , (≡-refl , p))

lem2 : {B N : BEXP} -> ((#t ● B) ->r N) -> (Not (#t ≡ N)) ->
  (∃ (\ (B' : BEXP) -> (N ≡ (#t ● B')) × (B ->r B')))
lem2 (ra p) b!=n = falseElim (b!=n (sane r#t p))
lem2 (rb p) b!=n = falseElim (irr-true p)
lem2 (rc {_}{b'} p) b!=n = (b' , (≡-refl , p))

diamond-like : {L M N : BEXP} -> (L ->r M) -> (L ->r N) ->
  (Not (M ≡ N)) ->
  ((M ->r N) ⋁
  ((N ->r M) ⋁
  (∃ (\ (L' : BEXP) -> (M ->r L') × (N ->r L')))))
diamond-like (ra r#f) q m!=n with lem1 q m!=n
diamond-like (ra r#f) q m!=n | (b , p) = {!!}
diamond-like (ra r#t) q m!=n with lem2 q m!=n
diamond-like (ra r#t) q m!=n | (b , p) = {!!}
diamond-like (rb y) q m!=n = {!!}
diamond-like (rc y) q m!=n = {!!}
-- diamond-like (ra p) (ra q) m!=n with sane p q
-- diamond-like (ra p) (ra q) m!=n | s = falseElim (m!=n s)
-- diamond-like (ra p) (rb q) m!=n with invr p
-- diamond-like (ra p) (rb q) m!=n | inj2 (a , _) = falseElim (irr-false (ren->r a q))
-- diamond-like (ra p) (rb q) m!=n | inj1 (a , _) = falseElim (irr-true (ren->r a q))
-- diamond-like (ra p) (rc q) m!=n with invr p
-- diamond-like (ra p) (rc q) m!=n | inj2 (a , _) = {!!}
-- diamond-like (ra p) (rc q) m!=n | inj1 (a , _) = {!!}
-- diamond-like (rb p) q m!=n = {!!}
-- diamond-like (rc p) q m!=n = {!!}

consistency : {b1 b2 : BEXP} -> b1 =r b2 -> ∃ (\ (b3 : BEXP) -> (b1 ->>r b3) × (b2 ->>r b3))
consistency (reduce p) = _ , (p , refl)
consistency (symm p) with consistency p
consistency (symm p) | (b , (q , q')) = b , (q' , q)
consistency (trans p q) with consistency p | consistency q
consistency (trans p q) | (l1 , (q1 , q1')) | (l2 , (q2 , q2')) = {!!}
