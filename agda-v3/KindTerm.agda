module KindTerm where

open import ScoThin

data Zero : Set where
record One : Set where
  constructor <>
data Two : Set where tt ff : Two
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
_+_ : Set -> Set -> Set
S + T = Sg Two \ { tt -> S ; ff -> T }

Dec : Set -> Set
Dec X = (x y : X) -> (x == y) + ((x == y) -> Zero)

record Datoid : Set1 where
  field
    Data : Set
    decD : Dec Data

open Datoid public

module KINDTERM (I : Set) where

  record Kind : Set where
    inductive
    constructor _!-_
    field
      scope : Bwd Kind
      sort  : I
  open Kind public

  data Desc : Set1 where
    rec' : Kind -> Desc
    sg'  : (A : Datoid)(D : Data A -> Desc) -> Desc
    _*'_ : Desc -> Desc -> Desc
    one' : Desc

  Node : Desc -> (Kind -> Set) -> Set
  Node (rec' k) T = T k
  Node (sg' A D) T = Sg (Data A) \ a -> Node (D a) T
  Node (D *' E) T = Node D T * Node E T
  Node one' T = One

  module SYN (F : I -> Desc) where

    data Tm (ga : Bwd Kind)(i : I) : Set
    data Sp (ga : Bwd Kind) : Bwd Kind -> Set
    TmK : (ga : Bwd Kind)(k : Kind) -> Set
    TmK ga (de !- i) = Tm (ga +B de) i

    data Tm ga i where
      _$_ : forall {de} -> (de !- i) <- ga -> Sp ga de -> Tm ga i
      <_> : Node (F i) (TmK ga) -> Tm ga i
    data Sp ga where
      [] : Sp ga []
      _-,_ : forall {de k} -> Sp ga de -> TmK ga k -> Sp ga (de -, k)

    record Action (ga0 ga1 ga de : Bwd Kind) : Set where
      field
        subIm   : Bwd Kind
        thinSrc : ga0 <= ga
        thinTrg : ga0 <= de
        subSrc  : ga1 <= ga
        subTrg  : subIm <= de
        thinSub : Complement thinSrc subSrc
        subSp   : Sp subIm ga1
    open Action public

    _+Action_ : forall {ga0 ga1 ga de}(sg : Action ga0 ga1 ga de) de' ->
            Action (ga0 +B de') ga1 (ga +B de') (de +B de')
    sg +Action [] = sg
    sg +Action (de' -, k) with sg +Action de'
    sg +Action (de' -, k)
      | record
      { subIm = subIm
      ; thinSrc = thinSrc
      ; thinTrg = thinTrg
      ; subSrc = subSrc
      ; subTrg = subTrg
      ; thinSub = thinSub
      ; subSp = subSp
      } = record
      { subIm = subIm
      ; thinSrc = thinSrc -, k
      ; thinTrg = thinTrg -, k
      ; subSrc = subSrc -^ k
      ; subTrg = subTrg -^ k
      ; thinSub = thinSub -, k
      ; subSp = subSp
      }

    vaAct : forall {ga1 de0 de1 de i}
              -> ((de0 !- i) <- ga1)
              -> Sp de1 ga1 -> de1 <= de
              -> Sp de de0 -> Tm de i
    tmAct : forall {ga0 ga1 ga de i} -> Tm ga i  -> Action ga0 ga1 ga de -> Tm de i
    spAct : forall {ga0 ga1 ga de de'} ->
              Sp ga de' -> Action ga0 ga1 ga de -> Sp de de'
    noAct : forall {ga0 ga1 ga de} D -> Node D (TmK ga)
              -> Action ga0 ga1 ga de -> Node D (TmK de)
    vaAct {de0 = de0}{de1 = de1}(x -, .(_ !- _)) (ss1 -, t) th ss0 with share de1 de0
    ... | ph0 , ph1 , c
      = tmAct t (record
                   { subIm = _
                   ; thinSrc = ph0
                   ; thinTrg = th
                   ; subSrc = ph1
                   ; subTrg = id<= _
                   ; thinSub = c
                   ; subSp = ss0
                   })
    vaAct (x -^ j) (ss1 -, _) th ss0 = vaAct x ss1 th ss0
    tmAct (x $ ss) sg with cover _ _ (thinSub sg) x
    tmAct (.(y =<= thinSrc sg) $ ss) sg | inl y
      = (y =<= thinTrg sg) $ spAct ss sg
    tmAct (.(z =<= subSrc sg) $ ss) sg  | inr z
      = vaAct z (subSp sg) (subTrg sg) (spAct ss sg)
    tmAct < ts > sg = < noAct (F _) ts sg >
    spAct [] sg = []
    spAct {de' = de' -, k} (ss -, s) sg = spAct ss sg -, tmAct s (sg +Action scope k)
    noAct (rec' k) t sg = tmAct t (sg +Action scope k)
    noAct (sg' A D) (a , ts) sg = a , noAct (D a) ts sg
    noAct (D *' D') (ts , ts') sg = noAct D ts sg , noAct D' ts' sg
    noAct one' <> sg = <>
