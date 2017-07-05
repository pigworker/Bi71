module Basics where


data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

sym : forall {l}{X : Set l}{x y : X} -> x == y -> y == x
sym refl = refl

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
        (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a)(a : A) -> C a (g a)
(f - g) x = f (g x)

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data Fin : Nat -> Set where
  ze : forall {n} -> Fin (su n)
  su : forall {n} -> Fin n -> Fin (su n)

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T

record One : Set where
  constructor <>

data Zero : Set where
