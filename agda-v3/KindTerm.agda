module KindTerm where

open import ScoThin

trans : forall {l}{X : Set l}{x y z : X} -> x == y -> y == z -> x == z
trans refl q = q

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
      _-,_ : forall {gas ga de} -> Act gas ga de ->
               forall k -> Act gas (ga -, k) (de -, k)
      _-^_ : forall {gas ga de} -> Act gas ga de ->
               forall k -> Act gas ga       (de -, k)
      _-$_ : forall {gas ga de k} ->
               Act gas ga de ->
                 Tm (de +B scope k) (sort k) ->
                 Act (gas -, k) (ga -, k) de

    data ActX (de : Bwd Kind) : Bwd Kind -> Bwd Kind -> Bwd Kind -> Set where
      [] : ActX de [] [] []
      _-,_ : forall {ze' ga' de'} -> ActX de ze' ga' de' -> forall k ->
              ActX de ze' (ga' -, k) (de' -, k)
      _-^_ : forall {ze' ga' de'} -> ActX de ze' ga' de' -> forall k ->
              ActX de ze' ga' (de' -, k)
      _-$_ : forall {ze' ga' de'} -> ActX de ze' ga' de' -> forall {k} ->
               Tm ((de +B de') +B scope k) (sort k) -> ActX de (ze' -, k) (ga' -, k) de'

    _+X_ : forall {ze ga de ze' ga' de'} -> Act ze ga de -> ActX de ze' ga' de' ->
             Act (ze +B ze') (ga +B ga') (de +B de')
    sg +X [] = sg
    sg +X (ta -, k) = (sg +X ta) -, k
    sg +X (ta -^ k) = (sg +X ta) -^ k
    sg +X (ta -$ t) = (sg +X ta) -$ t

    data Tca (gas ga de : Bwd Kind) : Bwd Kind -> Bwd Kind -> Bwd Kind -> Set where
      []   : Tca gas ga de gas ga de
      _,-_ : forall {gas' ga' de'} k
               -> Tca gas (ga -, k) (de -, k) gas' ga' de'
               -> Tca gas ga de gas' ga' de'
      _^-_ : forall {gas' ga' de'} k
               -> Tca  gas ga       (de -, k) gas' ga' de'
               -> Tca gas ga de gas' ga' de'
      _$-_ : forall {gas' ga' de' k} -> Tm (de +B scope k) (sort k)
               -> Tca (gas -, k) (ga -, k) de gas' ga' de'
               -> Tca gas ga de gas' ga' de'

    _<><_ : forall {gas ga de gas' ga' de'} ->
              Act gas ga de -> Tca gas ga de gas' ga' de' -> Act gas' ga' de'
    sg <>< [] = sg
    sg <>< (k ,- ta) = (sg -, k) <>< ta
    sg <>< (k ^- ta) = (sg -^ k) <>< ta
    sg <>< (t $- ta) = (sg -$ t) <>< ta

    _+ThTca_ : forall {de0 gas ga de gas' ga' de'} ->
              de0 <= de -> Tca gas ga de gas' ga' de' -> de0 <= de'
    th +ThTca []        = th
    th +ThTca (k ,- ta) = (th -^ k) +ThTca ta
    th +ThTca (k ^- ta) = (th -^ k) +ThTca ta
    th +ThTca (_ $- ta) = th +ThTca ta

    tcaTh : forall {gas ga de gas' ga' de'} ->
              Tca gas ga de gas' ga' de' -> de <= de'
    tcaTh []        = id<= _
    tcaTh (k ,- ta) = (id<= _ -^ k) =<= tcaTh ta
    tcaTh (k ^- ta) = (id<= _ -^ k) =<= tcaTh ta
    tcaTh (_ $- ta) = tcaTh ta

    tcaFact : forall {de0 gas ga de gas' ga' de'} ->
              (th : de0 <= de)(ta : Tca gas ga de gas' ga' de') ->
              (th +ThTca ta) == (th =<= tcaTh ta)
    tcaFact th [] rewrite Qid<= th = refl
    tcaFact th (k ,- ta)
      rewrite sym (=<=<=Q th (id<= _ -^ k) (tcaTh ta))
            | Qid<= th
            = tcaFact (th -^ k) ta
    tcaFact th (k ^- ta)
      rewrite sym (=<=<=Q th (id<= _ -^ k) (tcaTh ta))
            | Qid<= th
      = tcaFact (th -^ k) ta
    tcaFact th (x $- ta) = tcaFact th ta

    tcaLemma : forall {gas ga de gas' ga' de'} ->
              (ta : Tca gas ga de gas' ga' de') ->
              (id<= _ +ThTca ta) == tcaTh ta
    tcaLemma ta
      rewrite tcaFact (id<= _) ta
            | id<=Q (tcaTh ta)
            = refl

    _+Act_ : forall {gas ga de}(sg : Act gas ga de) ze ->
            Act gas (ga +B ze) (de +B ze)
    sg +Act [] = sg
    sg +Act (ze -, k) = (sg +Act ze) -, k

    thAct : forall {ga de} -> ga <= de -> Act [] ga de
    thAct []        = []
    thAct (th -, k) = thAct th -, k
    thAct (th -^ j) = thAct th -^ j

    _+ThSp_ : forall {ga de ze} ->
          ga <= de -> Sp de ze -> Act ze (ga +B ze) de
    th +ThSp []        = thAct th
    th +ThSp (ss -, s) = (th +ThSp ss) -$ s

    vaAct : forall {gas ga de de' k}
              -> (k <- ga)
              -> Act gas ga de
              -> de <= de'
              -> Sp de' (scope k) -> Tm de' (sort k)
    tmAct : forall {gas ga de i} ->
            Tm ga i -> Act gas ga de -> Tm de i
    spAct : forall {gas ga de ze} ->
            Sp ga ze -> Act gas ga de -> Sp de ze
    noAct : forall {gas ga de} D -> Node D (TmK ga)
              -> Act gas ga de -> Node D (TmK de)
    vaAct () [] ph ss
    vaAct x (sg -^ k) ph ss = vaAct x sg ((id<= _ -^ k) =<= ph) ss
    vaAct (x -, .k) (sg -, k) ph ss
      = ((in<= _ -, k) =<= ph) $ ss
    vaAct (x -^ .k) (sg -, k) ph ss = vaAct x sg ((id<= _ -^ k) =<= ph) ss
    vaAct (x -, k) (sg -$ t) ph ss = tmAct t (ph +ThSp ss)
    vaAct (x -^ j) (sg -$ t) ph ss = vaAct x sg ph ss

    tmAct (x $ ss) sg = vaAct x sg (id<= _) (spAct ss sg)
    tmAct < ts > sg = < noAct (F _) ts sg >
    spAct [] sg = []
    spAct {ze = ze -, k} (ss -, s) sg = spAct ss sg -, tmAct s (sg +Act scope k)
    noAct (rec' k) t sg = tmAct t (sg +Act scope k)
    noAct (sg' A D) (a , ts) sg = a , noAct (D a) ts sg
    noAct (D *' D') (ts , ts') sg = noAct D ts sg , noAct D' ts' sg
    noAct one' <> sg = <>

    ActIm : Bwd Kind -> Kind -> Set
    ActIm de k = (k <- de) + Sg _ \ dei -> TmK dei k * (dei <= de)

    actImTh : forall {de k ze} -> ActIm de k -> de <= ze -> ActIm ze k
    actImTh (tt , y) ph = tt , (y =<= ph)
    actImTh (ff , dei , t , th) ph = ff , dei , t , (th =<= ph)

    actImThId : forall {de k}(w : ActIm de k) ->
      actImTh w (id<= _) == w
    actImThId (tt , y) rewrite Qid<= y = refl
    actImThId (ff , dei , t , th) rewrite Qid<= th = refl

    actImThCo : forall {ga k de ze}(w : ActIm ga k)(th : ga <= de)(ph : de <= ze)
      -> actImTh (actImTh w th) ph == actImTh w (th =<= ph)
    actImThCo (tt , y) th ph rewrite =<=<=Q y th ph = refl
    actImThCo (ff , dei , t , ps) th ph rewrite =<=<=Q ps th ph = refl

    ACT : Bwd Kind -> Bwd Kind -> Set
    ACT ga de = Sg _ \ ga' -> Act ga' ga de

    tmACT : forall {ga de i} ->
            Tm ga i -> ACT ga de -> Tm de i
    spACT : forall {ga de ze} ->
            Sp ga ze -> ACT ga de -> Sp de ze
    noACT : forall {ga de} D -> Node D (TmK ga)
              -> ACT ga de -> Node D (TmK de)
    tmACT t (_ , sg) = tmAct t sg
    spACT ss (_ , sg) = spAct ss sg
    noACT D ts (_ , sg) = noAct D ts sg

    _!-^_ : forall {ga de} -> ACT ga de -> forall k -> ACT ga (de -, k)
    (_ , sg) !-^ k = _ , (sg -^ k)

    coAct : forall {ga' ga de de' ze} -> Act ga' ga de -> Act de' de ze ->
              ACT ga ze
    coAct [] ta = _ , ta
    coAct {ga' = _ -, k} (sg -$ s) ta with coAct sg ta
    ... | ga'' , up
        = (ga'' -, _) , (up -$ tmAct s (ta +Act scope k))
    coAct sg (ta -^ k) with coAct sg ta
    ... | ga'' , up = ga'' , (up -^ k)
    coAct (sg -, .k) (ta -, k) with coAct sg ta
    ... | ga'' , up = ga'' , (up -, k)
    coAct (sg -^ .k) (ta -, k) with coAct sg ta
    ... | ga'' , up = ga'' , (up -^ k)
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

    wk : (ga de : Bwd Kind) -> ga <= (ga +B de)
    wk ga [] = id<= ga
    wk ga (de -, k) = wk ga de -^ k

    coActLig : forall {gas ga de gas' ga' de'}
                (sg : Act gas ga de)
                (ta : ActX de gas' ga' de') ->
                coAct (thAct (wk ga ga')) (sg +X ta)
                  ==
                coAct sg (thAct (wk de de'))
    coActLig sg [] = {!!}
    coActLig sg@[]       (ta -, k) rewrite coActLig sg ta = refl
    coActLig sg@(_ -, _) (ta -, k) rewrite coActLig sg ta = refl
    coActLig sg@(_ -^ _) (ta -, k) rewrite coActLig sg ta = refl
    coActLig sg@(_ -$ _) (ta -, k) rewrite coActLig sg ta = {!!} -- rewrite coActLig sg ta = {!!}
    coActLig sg      (ta -^ k) = {!refl!}
    coActLig sg (ta -$ x) rewrite coActLig sg ta = refl

    coActHig : forall {ga de}(th : ga <= de)
                {des' xi' des xi}
                (sg : Act des' ga xi')(ta : Tca des' ga xi' des de xi) ->
                coAct (thAct th) (sg <>< ta)
                  ==
                coAct sg (thAct (tcaTh ta))
    coActHig th sg [] = {!!}
    coActHig th sg (k ,- ta)
      --  rewrite coActHig th (sg -, k) ta
      = {!!}
    coActHig th sg (k ^- ta) = {!!}
    coActHig th sg (x $- ta) = {!!}

    coActJig : forall {ga de ze}(th : ga <= de)(ss : Sp de ze)
                {des' xi' des xi}
                (sg : Act des' ga xi')(ta : Tca des' ga xi' des de xi) ->
      coAct (th +ThSp ss) {- Act ze (ga +B ze) de -}
            (sg <>< ta) {- Act des de xi -} ==
      coAct (sg +Act ze) ((tcaTh ta) +ThSp spAct ss (sg <>< ta) {- Sp xi ze -})
          {- Act des' (de' +B ze) (xi' +B ze) -}
              {- Act ze (xi' +B ze)   xi -}
    coActJig th [] sg ta = coActHig th sg ta
    coActJig th (ss -, s) sg ta rewrite coActJig th ss sg ta = refl

    idAct : forall ga -> Act [] ga ga
    idAct ga = thAct (id<= ga)

    idActLemma : forall ga de -> (idAct ga +Act de) == idAct (ga +B de)
    idActLemma ga [] = refl
    idActLemma ga (de -, k) rewrite idActLemma ga de = refl

    vaActId : forall {ga ga' k}
               (x : k <- ga)(ta : Tca [] ga ga [] ga' ga')
               (ss : Sp ga' (scope k))
               (q : (idAct ga <>< ta) == idAct ga')
              -> vaAct x (idAct ga) (tcaTh ta) ss == ((x +ThTca ta) $ ss)
    tmActId : forall {ga i}(t : Tm ga i) -> tmAct t (idAct ga) == t
    spActId : forall {ga de}(ss : Sp ga de) -> spAct ss (idAct ga) == ss
    noActId : forall {ga} D (ts : Node D (TmK ga)) -> noAct D ts (idAct ga) == ts
    vaActId (x -, k) ta ss q with initial x
    vaActId (.(in<= _) -, k) ta ss q | init
      rewrite tcaFact (in<= _ -, k) ta
            = refl
    vaActId (x -^ j) ta ss q = vaActId x (j ,- ta) ss q

    tmActId {ga} (x $ ss)
      rewrite spActId ss
            | vaActId x [] ss refl
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

    coAcId : forall {gas ga de}(sg : Act gas ga de) ->
           coAct sg (idAct de) == (gas , sg)
    coAcId [] = refl
    coAcId (sg -, k) rewrite coAcId sg = refl
    coAcId (sg -^ k) rewrite coAcId sg = refl
    coAcId {de = de} (_-$_ {k = k} sg t)
      rewrite coAcId sg
            | idActLemma de (scope k)
            | tmActId t
            = refl

    coIdAc : forall {gas ga de}(sg : Act gas ga de) ->
           coAct (idAct ga) sg == (gas , sg)
    coIdAc [] = refl
    coIdAc (sg -, k) rewrite coIdAc sg = refl
    coIdAc {ga = []} (sg -^ k) = refl
    coIdAc {ga = ga -, j} (sg -^ k) rewrite coIdAc sg = refl
    coIdAc (sg -$ t) rewrite coIdAc sg = refl

    tmActCo : forall {gas ga des de ze i}
      (t : Tm ga i)(sg : Act gas ga de)(ta : Act des de ze) ->
      tmAct (tmAct t sg) ta == tmACT t (coACT (gas , sg) (des , ta))
    spActCo : forall {gas ga des de ze xi}
      (ss : Sp ga xi)(sg : Act gas ga de)(ta : Act des de ze) ->
      spAct (spAct ss sg) ta == spACT ss (coACT (gas , sg) (des , ta))
    vaActCo : forall {gas ga de k}  (x : k <- ga)(sg : Act gas ga de)
                     {gas1 ga1 de1} (ta : Tca gas ga de gas1 ga1 de1)
                                    (ss : Sp de1 (scope k))
                     {des ze}       (sg1 : Act des de ze)
                     {des1 ze1}     (ta1 : Tca des de ze des1 de1 ze1) ->
                     ((x : k <- de) ->
                       vaAct (x +ThTca ta) (sg1 <>< ta1) (id<= _)
                          (spAct ss (sg1 <>< ta1))
                       ==
                       vaAct x sg1 (tcaTh ta1)
                          (spAct ss (sg1 <>< ta1)))
                       ->
        tmAct (vaAct x sg (tcaTh ta) ss) (sg1 <>< ta1) ==
          vaAct x (snd (coAct sg sg1)) (tcaTh ta1) (spAct ss (sg1 <>< ta1))

    vaActCo () [] ta ss sg1 ta1 q1
    vaActCo (x -^ j) (sg -$ t) ta ss sg1 ta1 q1
      = vaActCo x sg (t $- ta) ss sg1 ta1 q1
    vaActCo (x -, k) (sg -$ t) ta ss sg1 ta1 q1
      rewrite tmActCo t (tcaTh ta +ThSp ss) (sg1 <>< ta1)
            | tmActCo t (sg1 +Act scope k) (tcaTh ta1 +ThSp spAct ss (sg1 <>< ta1))
         --   | coActJig (tcaTh ta) ss sg1 ta1
      = {!!}
    vaActCo x sg@(_ -, _) ta ss (sg1 -^ k) ta1 q1
      = vaActCo x sg ta ss sg1 (k ^- ta1) q1
    vaActCo x sg@(_ -^ _) ta ss (sg1 -^ k) ta1 q1
      = vaActCo x sg ta ss sg1 (k ^- ta1) q1
    vaActCo (x -, .k) (sg -, k) ta ss (sg1 -, .k) ta1 q1
      rewrite sym (tcaFact (in<= _ -, k) ta)
      = q1 (in<= _ -, k)
    vaActCo (x -^ .k) (sg -, k) ta ss (sg1 -, .k) ta1 q1
      = vaActCo x sg (k ,- ta) ss sg1 (k ,- ta1) (q1 - (_-^ k))
    vaActCo (x -, .k) (sg -, k) ta ss (sg1 -$ t) ta1 q1
      rewrite sym (tcaFact (in<= _ -, k) ta)
      = q1 (in<= _ -, k) 
    vaActCo (x -^ .k) (sg -, k) ta ss (sg1 -$ t) ta1 q1
      = vaActCo x sg (k ,- ta) ss sg1 (t $- ta1) (q1 - (_-^ k))
    vaActCo x (sg -^ k) ta ss (sg1 -, .k) ta1 q1
      = vaActCo x sg (k ^- ta) ss sg1 (k ,- ta1) (q1 - (_-^ k))
    vaActCo x (sg -^ k) ta ss (sg1 -$ t) ta1 q1
      = vaActCo x sg (k ^- ta) ss sg1 (t $- ta1) (q1 - (_-^ k))

    tmActCo (x $ ss) sg ta
      rewrite vaActCo x sg [] (spAct ss sg) ta [] (\ _ -> refl)
            | spActCo ss sg ta
      = refl
    tmActCo < x > sg ta = {!!}
    spActCo ss sg ta = {!!}
