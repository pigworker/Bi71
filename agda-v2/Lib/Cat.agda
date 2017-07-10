module Lib.Cat where

open import Agda.Primitive
open import Lib.Comb
open import Lib.Eq

module CATSTUFF {k l}{I : Set k}(R : I -> I -> Set l) where

  record Hom (i j : I) : Set l where
    constructor <_]
    field
      hom : R i j

  record Cat : Set (k ⊔ l) where
    field
      idC     : {i : I} -> Hom i i
      _<<_    : {i j k : I} -> Hom j k -> Hom i j -> Hom i k

  module CATLAWS (Q : forall {i j} -> Hom i j -> Hom i j -> Set l)
                 (C : Cat) where
    open Cat C
    record CatLaws : Set (k ⊔ l) where
      field
        id-co : forall {i j}(h : Hom i j) -> Q (idC << h) h
        co-id : forall {i j}(h : Hom i j) -> Q (h << idC) h
        assoc : forall {i j k l}(f : Hom k l)(g : Hom j k)(h : Hom i j) ->
                  Q ((f << g) << h) (f << (g << h))

open CATSTUFF public
open Hom public
HQ : forall {k l}{I : Set k}{R : I -> I -> Set l} ->
     (forall {i j} -> R i j -> R i j -> Set l) ->
     forall {i j} -> Hom R i j -> Hom R i j -> Set l
HQ Q < f ] < g ] = Q f g

open module CATLAWS' {k}{l}{I}{R} = CATLAWS {k}{l}{I} R public

SET-L : forall l -> Cat {l = l} \ S T -> S -> T
SET-L l = record
  { idC = < id ]
  ; _<<_ = \ { < f ] < g ] -> < f - g ] }
  }

SET = SET-L lzero

_<Cat-_ : forall {j k l}{I : Set k}{J : Set j}{R : I -> I -> Set l} ->
          Cat R -> (f : J -> I) -> Cat \ j0 j1 -> R (f j0) (f j1)
C <Cat- f = record
  { idC = < hom idC ]  -- bizarre
  ; _<<_ = \ f g -> < hom (< hom f ] << < hom g ]) ]  -- bizarrer
  } where open Cat C

module FUNCTORSTUFF
  {k l}{I : Set k}{R : I -> I -> Set l}
  {k' l'}{I' : Set k'}{R' : I' -> I' -> Set l'}
  (SC : Cat R)(TC : Cat R')
  where
  record Functor : Set (k ⊔ l ⊔ k' ⊔ l') where
    field
      objF : I -> I'
      homF : forall {i j} -> Hom R i j -> Hom R' (objF i) (objF j)

  module FUNCTORLAWS
    (Q  : forall {i j} -> Hom R i j -> Hom R i j -> Set l)
    (Q' : forall {i j} -> Hom R' i j -> Hom R' i j -> Set l')
    (F : Functor)
    where
    open Cat
    open Functor F
    record FunctorLaws : Set (k ⊔ l ⊔ l') where
      field
        funId : forall {i}(f : Hom R i i) -> Q f (idC SC) ->
                  Q' (homF f) (idC TC)
        funCo : forall {i j k}
                  (h : Hom R i k)(f : Hom R j k)(g : Hom R i j) ->
                  Q h (_<<_ SC f g) ->
                  Q' (homF h) (_<<_ TC (homF f) (homF g))
                  
open FUNCTORSTUFF public
open FUNCTORLAWS public
