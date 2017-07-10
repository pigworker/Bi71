module Lib.Sg where

open import Agda.Primitive
open import Lib.Two
open import Lib.Comb

record Sg {k l}(S : Set k)(T : S -> Set l) : Set (k ⊔ l) where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public

_*_ : forall {k l} -> Set k -> Set l -> Set (k ⊔ l)
S * T = Sg S \ _ -> T

infixr 5 _,_ _*_

sg : forall {k k' l l'}{S : Set k}{S' : Set k'}
                 {T : S -> Set l}{T' : S' -> Set l'}
       (f : S -> S')(g : forall {s} -> T s -> T' (f s)) ->
       Sg S T -> Sg S' T'
sg f g (s , t) = f s , g t

_+_ : forall {l} -> Set l -> Set l -> Set l
S + T = Sg Two (S <?> T)

infixr 4 _+_

pattern inl s = tt , s
pattern inr t = ff , t

_<+>_ : forall {k l}{S T : Set k}{S' T' : Set l} ->
        (S -> S') -> (T -> T') -> (S + T) -> (S' + T')
(f <+> g) = sg id \ { {tt} -> f ; {ff} -> g }

record %_ {I : Set}(T : I -> Set) : Set where
  constructor %[_]
  field
    {wit} : I
    see : T wit
open %_ public

infixl 0 %_
