module Lib.Comb where

id : forall {l}{X : Set l} -> X -> X
id x = x

_-_ : forall {j k l}{A : Set j}{B : A -> Set k}{C : (a : A)(b : B a) -> Set l}
         (f : {a : A}(b : B a) -> C a b)
         (g : (a : A) -> B a)
         (a : A) -> C a (g a)
(f - g) a = f (g a)

_&_ : forall {j k l}{A : Set j}{B : A -> Set k}{C : (a : A)(b : B a) -> Set l}
         (g : (a : A) -> B a)
         (f : {a : A}(b : B a) -> C a b)
         (a : A) -> C a (g a)
(f & g) a = g (f a)
