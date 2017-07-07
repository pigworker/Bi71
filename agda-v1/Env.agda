module Env where

open import Basics
open import OPE

data Env (X : Set) : Nat -> Set where
  []   : Env X ze
  _-,_ : forall {n} -> Env X n -> X -> Env X (su n)

env : forall {n X Y} -> (X -> Y) -> Env X n -> Env Y n
env f []        = []
env f (xz -, x) = env f xz -, f x

_!_ : forall {X n} -> Env X n -> Fin n -> X
(xz -, x) ! ze = x
(xz -, x) ! su i = xz ! i

env!Q : forall {n X Y}(f : X -> Y)(xz : Env X n)(i : Fin n) ->
  (env f xz ! i) == f (xz ! i)
env!Q f (xz -, x) ze = refl
env!Q f (xz -, x) (su i) = env!Q f xz i

envIdQ : forall {n X}(f : X -> X)(q : (x : X) -> f x == x) ->
         (xz : Env X n) -> env f xz == xz
envIdQ f q [] = refl
envIdQ f q (xz -, x) rewrite envIdQ f q xz | q x = refl

_/_ : forall {n m X} -> Env X m -> n <= m -> Env X n
[] / oz = []
(xz -, x) / os th = (xz / th) -, x
(xz -, _) / o' th = xz / th

/!Q : forall {n m X}(xz : Env X m)(th : n <= m)(i : Fin n) ->
        (xz ! thin th i) == ((xz / th) ! i)
/!Q [] oz ()
/!Q (xz -, x) (os th) ze = refl
/!Q (xz -, x) (os th) (su i) rewrite /!Q xz th i = refl
/!Q (xz -, x) (o' th) i = /!Q xz th i

_/oiQ : forall {n X}(xz : Env X n) -> (xz / oi) == xz
[] /oiQ = refl
(xz -, x) /oiQ rewrite xz /oiQ = refl

env/Q : forall {n m X Y}(f : X -> Y)(xz : Env X m)(th : n <= m) ->
  (env f xz / th) == env f (xz / th)
env/Q f [] oz = refl
env/Q f (xz -, x) (os th) rewrite env/Q f xz th = refl
env/Q f (xz -, x) (o' th) = env/Q f xz th


envenvQ : forall {n X Y Z}(g : Y -> Z)(f : X -> Y)(xz : Env X n) ->
  env g (env f xz) == env (g - f) xz
envenvQ g f [] = refl
envenvQ g f (xz -, x) rewrite envenvQ g f xz = refl

envextQ : forall {n X Y}{f g : X -> Y} -> ((x : X) -> f x == g x) ->
          (xz : Env X n) -> env f xz == env g xz
envextQ q [] = refl
envextQ q (xz -, x) rewrite envextQ q xz | q x = refl
