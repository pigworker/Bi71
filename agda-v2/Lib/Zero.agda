module Lib.Zero where

data Zero : Set where

naughty : forall {l}{X : Set l} -> Zero -> X
naughty ()

Not : forall {l} -> Set l -> Set l
Not X = X -> Zero
