module Lib.Eq where

open import Agda.Primitive

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

subst : forall {k l}{X : Set k}{x y : X} -> x == y ->
        (P : X -> Set l) -> P x -> P y
subst refl P p = p

_$=_ : forall {k l}{S : Set k}{T : Set l} ->
       (f : S -> T){x y : S} -> x == y -> f x == f y
f $= refl = refl

_=$=_ : forall {k l}{S : Set k}{T : Set l} ->
       {f g : S -> T}{x y : S} -> f == g -> x == y -> f x == g y
refl =$= refl = refl

infixl 3 _$=_ _=$=_

sym : forall {l}{X : Set l}{x y : X} -> x == y -> y == x
sym refl = refl

trans : forall {l}{X : Set l}{x y z : X} -> x == y -> y == z -> x == z
trans refl q = q

_=^=_ : forall {k l}{S : Set k}{T : S -> Set l}
        (f g : (x : S) -> T x) -> Set (k ⊔ l)
f =^= g = (x : _) -> f x == g x

postulate
  ext : forall {k l}{S : Set k}{T : S -> Set l}
        {f g : (x : S) -> T x} ->
        f =^= g -> f == g

_=[_>=_ : forall {l}{X : Set l}(x : X){y z} ->
        x == y -> y == z -> x == z
x =[ refl >= q = q

_=<_]=_ : forall {l}{X : Set l}(x : X){y z} ->
        y == x -> y == z -> x == z
x =< refl ]= q = q

_=[] : forall {l}{X : Set l}(x : X) -> x == x
x =[] = refl

infixr 2 _=[_>=_ _=<_]=_ _=[]
