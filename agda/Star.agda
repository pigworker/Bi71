module Star where

open import Basics

data Star {X}(R : X -> X -> Set)(x : X) : X -> Set where
  [] : Star R x x
  _,-_ : forall {y z} -> R x y -> Star R y z -> Star R x z

infixr 4 _,-_

List : Set -> Set
List X = Star {One} (\ _ _ -> X) _ _

All : forall {X} -> (X -> Set) -> List X -> Set
All P [] = One
All P (x ,- xs) = P x * All P xs

all : forall {X}{P Q : X -> Set} ->
      (forall {x} -> P x -> Q x) -> forall {xs} -> All P xs -> All Q xs
all f {[]} <> = <>
all f {x ,- xs} (p , ps) = f p , all f ps

_++_ : forall {X}{R : X -> X -> Set}{x y z} ->
       Star R x y -> Star R y z -> Star R x z
[] ++ ss = ss
(r ,- rs) ++ ss = r ,- (rs ++ ss)

starm : forall {X Y}(f : X -> Y){R : X -> X -> Set}{R' : Y -> Y -> Set} ->
  ({x x' : X} -> R x x' -> R' (f x) (f x')) ->
  {x x' : X} -> Star R x x' -> Star R' (f x) (f x')
starm f g [] = []
starm f g (r ,- rz) = g r ,- starm f g rz

Parallelogram : forall {X}(R S : X -> X -> Set) -> Set
Parallelogram {X} R S = forall {x y z} ->
  R x y -> S x z -> Sg X \ w -> S y w * R z w

Diamond : forall {X}(R : X -> X -> Set) -> Set
Diamond R = Parallelogram R R

stripLemma : forall {X}{R : X -> X -> Set} ->
             Diamond R -> Parallelogram R (Star R)
stripLemma d s [] = _ , [] , s
stripLemma d s (r ,- rs) with d s r
... | _ , t , u with stripLemma d u rs
... | _ , ts , v = _ , ((t ,- ts)) , v

diamondLemma : forall {X}{R : X -> X -> Set} ->
             Diamond R -> Diamond (Star R)
diamondLemma d [] ss = _ , ss , []
diamondLemma d (r ,- rs) ss with stripLemma d r ss
... | _ , ts , u with diamondLemma d rs ts
... | _ , vs , us = _ , vs , (u ,- us)
