module Lib.Dec where

open import Lib.Zero
open import Lib.Sg

Dec : forall {l} -> Set l -> Set l
Dec X = X + (X -> Zero)
