module KindTerm where

open import ScoThin

data Zero : Set where
record One : Set where
  constructor <>

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

    data Act : Bwd Kind -> Bwd Kind -> Bwd Kind -> Set where
      []   : Act [] [] []
      _-,_ : forall {ga' ga de} -> Act ga' ga de ->
               forall k -> Act ga' (ga -, k) (de -, k)
      _-^_ : forall {ga' ga de} -> Act ga' ga de ->
               forall k -> Act ga'  ga       (de -, k)
      _-$_ : forall {ga' ga de de' k} ->
               Act ga' ga de ->
                 Tm (de' +B scope k) (sort k) * (de' <= de) ->
                 Act (ga' -, k) (ga -, k) de

    _+Act_ : forall {ga' ga de}(sg : Act ga' ga de) ze ->
            Act ga' (ga +B ze) (de +B ze)
    sg +Act [] = sg
    sg +Act (ze -, k) = (sg +Act ze) -, k

    thAct : forall {ga de} -> ga <= de -> Act [] ga de
    thAct []        = []
    thAct (th -, k) = thAct th -, k
    thAct (th -^ j) = thAct th -^ j

    jig : forall {ga de ze} ->
          Sp de ze -> ga <= de -> Act ze (ga +B ze) de
    jig [] th = thAct th
    jig (ss -, s) th = jig ss th -$ (s , id<= _)

    vaAct : forall {ga' ga de ze k}
              -> (k <- ga)
              -> Act ga' ga de
              -> de <= ze
              -> Sp ze (scope k) -> Tm ze (sort k)
    tmAct : forall {ga' ga de i} ->
            Tm ga i -> Act ga' ga de -> Tm de i
    spAct : forall {ga' ga de ze} ->
            Sp ga ze -> Act ga' ga de -> Sp de ze
    noAct : forall {ga' ga de} D -> Node D (TmK ga)
              -> Act ga' ga de -> Node D (TmK de)
    vaAct () [] ph ss
    vaAct (x -, .k) (sg -, k) ph ss = ((in<= _ -, k) =<= ph) $ ss
    vaAct (x -^ .k) (sg -, k) ph ss = vaAct x sg (peel ph) ss
    vaAct x (sg -^ k) ph ss = vaAct x sg (peel ph) ss
    vaAct (x -, k) (sg -$ (t , th)) ph ss = tmAct t (jig ss (th =<= ph))
    vaAct (x -^ j) (sg -$ s) ph ss = vaAct x sg ph ss
    tmAct (x $ ss) sg = vaAct x sg (id<= _) (spAct ss sg)
    tmAct < ts > sg = < noAct (F _) ts sg >
    spAct [] sg = []
    spAct {ze = ze -, k} (ss -, s) sg = spAct ss sg -, tmAct s (sg +Act scope k)
    noAct (rec' k) t sg = tmAct t (sg +Act scope k)
    noAct (sg' A D) (a , ts) sg = a , noAct (D a) ts sg
    noAct (D *' D') (ts , ts') sg = noAct D ts sg , noAct D' ts' sg
    noAct one' <> sg = <>

    reAct : forall {ga de' de ze} ->
            ga <= de -> Act de' de ze -> Sg _ \ ga' -> Act ga' ga ze
    reAct th (sg -^ k) with reAct th sg
    ... | ga' , ta = ga' , (ta -^ k)
    reAct [] [] = [] , []
    reAct (th -, k) (sg -, .k) with reAct th sg
    ... | ga' , ta = ga' , (ta -, k)
    reAct (th -, k) (sg -$ s) with reAct th sg
    ... | ga' , ta = (ga' -, k) , (ta -$ s)
    reAct (th -^ j) (sg -, .j) with reAct th sg
    ... | ga' , ta = ga' , (ta -^ j)
    reAct (th -^ j) (sg -$ x) = reAct th sg

    ACT : Bwd Kind -> Bwd Kind -> Set
    ACT ga de = Sg _ \ ga' -> Act ga' ga de

    vaACT : forall {ga de ze k}
              -> (k <- ga)
              -> ACT ga de
              -> de <= ze
              -> Sp ze (scope k) -> Tm ze (sort k)
    tmACT : forall {ga de i} ->
            Tm ga i -> ACT ga de -> Tm de i
    spACT : forall {ga de ze} ->
            Sp ga ze -> ACT ga de -> Sp de ze
    noACT : forall {ga de} D -> Node D (TmK ga)
              -> ACT ga de -> Node D (TmK de)
    vaACT x (_ , sg) = vaAct x sg
    tmACT t (_ , sg) = tmAct t sg
    spACT ss (_ , sg) = spAct ss sg
    noACT D ts (_ , sg) = noAct D ts sg

    coAct : forall {ga' ga de de' ze} -> Act ga' ga de -> Act de' de ze ->
              ACT ga ze
    coAct sg (ta -^ k) with coAct sg ta
    ... | ga'' , up = ga'' , (up -^ k)
    coAct [] ta = _ , ta
    coAct (sg -, .k) (ta -, k) with coAct sg ta
    ... | ga'' , up = ga'' , (up -, k)
    coAct (sg -^ .k) (ta -, k) with coAct sg ta
    ... | ga'' , up = ga'' , (up -^ k)
    coAct {ga' = _ -, k} (sg -$ (t , th)) ta with coAct sg ta | reAct th ta
    ... | ga'' , up | _ , ta'
        = (ga'' -, _) , (up -$ (tmAct t (ta' +Act scope k) , id<= _))
    coAct (sg -, k) (ta -$ t) with coAct sg ta
    ... | ga'' , up = (ga'' -, k) , (up -$ t)
    coAct (sg -^ k) (ta -$ t) = coAct sg ta

    coACT : forall {ga de ze} -> ACT ga de -> ACT de ze -> ACT ga ze
    coACT (_ , sg) (_ , ta) = coAct sg ta

    _+ACT_ : forall {ga de} -> ACT ga de -> forall ze -> ACT (ga +B ze) (de +B ze)
    (ga' , sg) +ACT ze = ga' , (sg +Act ze)

    coACTLemma : forall {ga de  ze}
              (sg : ACT ga de)(ta : ACT de ze) -> forall ze' ->
              coACT (sg +ACT ze') (ta +ACT ze') ==
              (coACT sg ta +ACT ze')
    coACTLemma sg ta [] = refl
    coACTLemma sg ta (ze' -, x) rewrite coACTLemma sg ta ze' = refl
              
    idAct : forall ga -> Act [] ga ga
    idAct ga = thAct (id<= ga)

    idActLemma : forall ga de -> (idAct ga +Act de) == idAct (ga +B de)
    idActLemma ga [] = refl
    idActLemma ga (de -, k) rewrite idActLemma ga de = refl

    thActLemma : forall {ga de ze k}
                 (x : k <- ga)(th : ga <= de)(ph : de <= ze)(ss : Sp ze (scope k)) ->
                 vaAct x (thAct th) ph ss == ((x =<= (th =<= ph)) $ ss)
    thActLemma () [] ph ss
    thActLemma (x -, .k) (th -, k) ph ss with initial x
    thActLemma (.(in<= _) -, .k) (th -, k) ph ss | init
      rewrite sym (=<=<=Q (in<= _ -, k) (th -, k) ph)
            | in<=inQ th
            = refl
    thActLemma (x -^ .k) (th -, k) ph ss
      rewrite thActLemma x th (peel ph) ss
            | sym (=<=<=Q (x -^ k) (th -, k) ph)
            | sym (=<=<=Q x th (peel ph))
            | peelQ (x =<= th) ph
            = refl
    thActLemma x (th -^ j) ph ss
      rewrite thActLemma x th (peel ph) ss
            | peelQ th ph
            = refl

    tmActId : forall {ga i}(t : Tm ga i) -> tmAct t (idAct ga) == t
    spActId : forall {ga de}(ss : Sp ga de) -> spAct ss (idAct ga) == ss
    noActId : forall {ga} D (ts : Node D (TmK ga)) -> noAct D ts (idAct ga) == ts
    tmActId {ga} (x $ ss)
      rewrite spActId ss
            | thActLemma x (id<= ga) (id<= ga) ss
            | id<=Q (id<= ga)
            | Qid<= x
            = refl
    tmActId < ts > rewrite noActId (F _) ts = refl
    spActId [] = refl
    spActId {ga = ga}{de = de -, k} (ss -, s)
      rewrite spActId ss
            | idActLemma ga (scope k)
            | tmActId s
            = refl
    noActId {ga} (rec' k) t rewrite idActLemma ga (scope k) = tmActId t
    noActId (sg' A D) (a , ts) rewrite noActId (D a) ts = refl
    noActId (D *' D') (ts , ts')
      rewrite noActId D ts | noActId D' ts'
            = refl
    noActId one' <> = refl

    tmACTCo : forall {ga de ze i}(t : Tm ga i)(sg : ACT ga de)(ta : ACT de ze) ->
      tmACT (tmACT t sg) ta == tmACT t (coACT sg ta)
    tmACTCo (x $ ss) sg ta = {!!}
    tmACTCo < x > sg ta = {!!}
      
