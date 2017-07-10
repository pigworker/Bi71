module Lib.Datoid where

open import Lib.Sg
open import Lib.Dec

record Datoid : Set1 where
  field
    Data : Set
    decD : Dec Data

open Datoid public

