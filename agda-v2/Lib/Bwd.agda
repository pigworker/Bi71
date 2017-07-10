module Lib.Bwd where

open import Lib.Comb
open import Lib.Eq
open import Lib.One
open import Lib.Sg
open import Lib.Ix

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

infixl 4 _-,_

data _<-_ {X}(x : X) : Bwd X -> Set where
  ze : forall {xz}   ->  x <- (xz -, x)
  su : forall {xz y} ->  x <- xz  ->  x <- (xz -, y)

{-
data <Bwd> {X : Set}(P : X -> Set) : Bwd X -> Set where
  ze : forall {xz x} -> P x        -> <Bwd> P (xz -, x)
  su : forall {xz x} -> <Bwd> P xz -> <Bwd> P (xz -, x)
-}

[Bwd] : forall {X} -> (X -> Set) -> Bwd X -> Set
[Bwd] P [] = One
[Bwd] P (xz -, x) = [Bwd] P xz * P x

bwd : forall {X Y} -> (X -> Y) -> Bwd X -> Bwd Y
bwd f [] = []
bwd f (xz -, x) = bwd f xz -, f x

[bwd] : forall {X}{P Q : X -> Set} ->
        (^ P -:> Q) -> ^ [Bwd] P -:> [Bwd] Q
[bwd] f {[]} pz = <>
[bwd] f {xz -, x} (pz , p) = [bwd] f pz , f p

[bwd]Id : forall {X}{P : X -> Set}
          (f : ^ P -:> P)(q : forall {x}(p : P x) -> f p == p) ->
          {xz : Bwd X} ->
          (pz : [Bwd] P xz) -> [bwd] f pz == pz
[bwd]Id f q {[]} <> = refl
[bwd]Id f q {xz -, x} (pz , p) = _,_ $= [bwd]Id f q {xz} pz =$= q p

[bwd]Comp : forall {X}{P Q R : X -> Set}(g : ^ Q -:> R)(f : ^ P -:> Q)(h : ^ P -:> R)
            (q : forall {x}(p : P x) -> g (f p) == h p) ->
          {xz : Bwd X} -> (pz : [Bwd] P xz) -> [bwd] g ([bwd] f pz) == [bwd] h pz
[bwd]Comp g f h q {[]} <> = refl
[bwd]Comp g f h q {xz -, x} (pz , p) = _,_ $= [bwd]Comp g f h q {xz} pz =$= q p

bProj : forall {X}{P : X -> Set}{x xz} ->
        [Bwd] P xz -> x <- xz -> P x
bProj (_ , p)   ze    = p
bProj (pz , _) (su i) = bProj pz i

bProjNatural : forall {X}{P Q : X -> Set}{x xz} ->
    (f : ^ P -:> Q)(ps : [Bwd] P xz)(i : x <- xz) ->
    bProj ([bwd] f ps) i == f (bProj ps i)
bProjNatural f (_  , p)  ze    = refl
bProjNatural f (ps , _) (su i) = bProjNatural f ps i
                 

{-
bProj : forall {X}{P Q : X -> Set}{xz : Bwd X} ->
        <Bwd> P xz -> [Bwd] Q xz -> % P :* Q
bProj (ze p)  (qz , q) = %[ p , q ]
bProj (su ip) (qz , q) = bProj ip qz

bProjNatural : forall {X}{P Q R : X -> Set}{xz : Bwd X} ->
  (i : <Bwd> P xz)(qz : [Bwd] Q xz)(f : (^ Q -:> R)) ->
  bProj i ([bwd] f qz) == %map (\ { (p , q) -> p , f q }) (bProj i qz)
bProjNatural (ze p) (qz , q) f = refl
bProjNatural (su i) (qz , q) f = bProjNatural i qz f

bwdPointwise : forall {X}{P : X -> Set} xz (pz pz' : [Bwd] P xz) ->
                ({x : X}(i : <Bwd> (_==_ x) xz) -> bProj i pz == bProj i pz') ->
                pz == pz'
bwdPointwise [] <> <> q = refl
bwdPointwise (xz -, x) (pz , p) (pz' , p') q with q (ze refl)
bwdPointwise (xz -, x) (pz , p) (pz' , .p) q | refl
  = _,_ $= bwdPointwise xz pz pz' (q - su) =$= refl
-}
