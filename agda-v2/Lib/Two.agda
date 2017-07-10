module Lib.Two where

open import Lib.Zero
open import Lib.One
open import Lib.Comb

data Two : Set where tt ff : Two

_<?>_ : forall {l}{P : Two -> Set l} -> P tt -> P ff -> (b : Two) -> P b
(t <?> f) tt = t
(t <?> f) ff = f

So : Two -> Set
So tt = One
So ff = Zero

ifSo_then_else_ : forall {l}{X : Set l} -> (b : Two) ->
  (So b -> X) -> ((So b -> Zero) -> X) -> X
ifSo tt then t else f = t <>
ifSo ff then t else f = f id
