module Lib.Ix where

open import Lib.Sg
open import Lib.Cat
open import Lib.Eq

module INDEX {I : Set} where

  ^_ : forall (T : I -> Set) -> Set
  ^ T = forall {i} -> T i
  infix 0 ^_

  _-:>_ : (S T : I -> Set) -> I -> Set
  (S -:> T) i = S i -> T i
  infixr 2 _-:>_

  _:*_ : (S T : I -> Set) -> I -> Set
  (S :* T) i = S i * T i
  infixr 4 _:*_

  _:*map_ : forall {S T S' T'} -> (^ S -:> T) -> (^ S' -:> T') ->
              ^ (S :* S') -:> (T :* T')
  (f :*map f') (s , s') = f s , f' s'

  %map : forall {S T} -> (^ S -:> T) -> % S -> % T
  %map f %[ s ] = %[ f s ]

  uncurry:* : forall {S T U} ->
               (^ S -:> T -:> U)
            -> ^ S :* T -:> U
  uncurry:* p (s , t) = p s t

  ford : forall {j}{T} -> T j ->
         ^ _==_ j -:> T
  ford t refl = t

  module MODAL {R : I -> I -> Set}(C : Cat R) where

    open Cat C

    BOX : (I -> Set) -> I -> Set
    BOX T i = ^ (Hom R i -:> T)

    box : forall {T i j} -> Hom R i j -> BOX T i -> BOX T j
    box ij t jk = t (jk << ij)

    DIA : (I -> Set) -> I -> Set
    DIA T i = % (Hom R i :* T)

open INDEX public
