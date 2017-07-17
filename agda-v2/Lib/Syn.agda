module Lib.Syn where

open import Lib.Comb
open import Lib.One
open import Lib.Two
open import Lib.Sg
open import Lib.Datoid
open import Lib.Bwd
open import Lib.OPE
open import Lib.Eq

module SYNTAX {I : Set} where

  data Kind : Set where
    ok   : I -> Kind
    _!-_ : Kind -> Kind -> Kind

  data Desc : Set1 where
    #    : (k : Kind) -> Desc
    Sg'  : (S : Datoid)(T : Data S -> Desc) -> Desc
    _*'_ : (S T : Desc) -> Desc
    One' : Desc

  module NODE (Rec : Kind -> Set) where

    Node : Desc -> Set
    Node (# k)     = Rec k
    Node (Sg' S T) = Sg (Data S) \ s -> Node (T s)
    Node (S *' T)  = Node S * Node T
    Node One'      = One

  open NODE

  module FRAMEWORK (F : I -> Desc)
    where

    data Nm (Ga : Bwd Kind) : Kind -> Set
    data Sp (Ga : Bwd Kind)(j : Kind) : Kind -> Set

    data Nm Ga where
      _$_ : forall {k i} -> k <- Ga -> Sp Ga k (ok i) -> Nm Ga (ok i)
      <_> : forall {i} -> Node (Nm Ga) (F i) -> Nm Ga (ok i)
      \\_ : forall {j k} -> Nm (Ga -, j) k -> Nm Ga (j !- k)

    data Sp Ga j where
      []   : Sp Ga j j
      _-,_ : forall {k l} -> Sp Ga j (k !- l) -> Nm Ga k -> Sp Ga j l

    data Ps (Ga : Bwd Kind) : Kind -> Kind -> Set where
      []   : forall {k} -> Ps Ga k k
      _,-_ : forall {j k l} -> Nm Ga j -> Ps Ga k l -> Ps Ga (j !- k) l

    _<><_ : forall {Ga j k l} -> Sp Ga j k -> Ps Ga k l -> Sp Ga j l
    sz <>< []        = sz
    sz <>< (s ,- ss) = (sz -, s) <>< ss

    _<>>_ : forall {Ga j k l} -> Sp Ga j k -> Ps Ga k l -> Ps Ga j l
    [] <>> ss = ss
    (sz -, s) <>> ss = sz <>> (s ,- ss)

    fishFact : forall {Ga j k l}(sz : Sp Ga j k)(ss : Ps Ga k l) -> ((sz <>< ss) <>> []) == (sz <>> ss)
    fishFact sz [] = refl
    fishFact sz (s ,- ss) = fishFact (sz -, s) ss

    infixr 2 \\_
    infixr 3 _$_

    record ACTION (M : Bwd Kind -> Bwd Kind -> Set) : Set where
      field
        actW : forall {k Ga De} -> M Ga De -> M (Ga -, k) (De -, k)
        actV : forall {Ga De k i} -> M Ga De -> k <- Ga -> Sp De k (ok i) -> Nm De (ok i)
      actNm   : forall {Ga De k} -> M Ga De -> Nm Ga k -> Nm De k
      actNo   : forall {Ga De} D -> M Ga De -> Node (Nm Ga) D -> Node (Nm De) D
      actSp  : forall {Ga De j k} -> M Ga De -> Sp Ga j k -> Sp De j k
      actNm ga (x $ sz) = actV ga x (actSp ga sz)
      actNm ga < ts > = < actNo (F _) ga ts >
      actNm ga (\\ t) = \\ actNm (actW ga) t
      actNo (# k) ga t = actNm ga t
      actNo (Sg' A T) ga (a , ts) = a , actNo (T a) ga ts
      actNo (D *' D') ga (ts , ts') = actNo D ga ts , actNo D' ga ts'
      actNo One' ga <> = <>
      actSp ga [] = []
      actSp ga (sz -, s) = actSp ga sz -, actNm ga s

    open ACTION public

    Thn : ACTION _<=_
    Thn = record { actW = os ; actV = \ th x sz -> thin th x $ sz }

    record ACTIONIDENTITY {M}(A : ACTION M) : Set where
      field
        actId : forall {Ga} -> M Ga Ga
        actIdW : forall k {Ga} -> actW A actId == actId {Ga -, k}
        actIdV : forall {Ga k i}(x : k <- Ga)(sz : Sp Ga k (ok i)) ->
          actV A actId x sz == (x $ sz)
      actNmId : forall {Ga k}(t : Nm Ga k) -> actNm A actId t == t
      actNoId : forall {Ga} D (ts : Node (Nm Ga) D) ->
                  actNo A D actId ts == ts
      actSpId : forall {Ga j k}(sz : Sp Ga j k) -> actSp A actId sz == sz
      actNmId (x $ sz) rewrite actSpId sz = actIdV x sz
      actNmId < ts > rewrite actNoId (F _) ts = refl
      actNmId {Ga}{j !- k} (\\ t) rewrite actIdW j {Ga} | actNmId t = refl
      actNoId (# k) t = actNmId t
      actNoId (Sg' S T) (s , ts) rewrite actNoId (T s) ts = refl
      actNoId (D *' D') (ts , ts') rewrite actNoId D ts | actNoId D' ts' = refl
      actNoId One' <> = refl
      actSpId [] = refl
      actSpId (sz -, s) rewrite actSpId sz | actNmId s = refl

    ThnId : ACTIONIDENTITY Thn
    ThnId = record { actId = oi ; actIdW = \ _ -> refl ; actIdV = \ x sz -> (_$ sz) $= oiQ x } where

    record ACTIONCOMPOSITION {Mb Mf Mc}(Ab : ACTION Mb)(Af : ACTION Mf)(Ac : ACTION Mc) : Set where
      field
        actCo : forall {Ga De Th} -> Mb De Th -> Mf Ga De -> Mc Ga Th
        actCoW : forall k {Ga De Th}(mb : Mb De Th)(mf : Mf Ga De) ->
                   actCo (actW Ab {k} mb) (actW Af mf) == actW Ac (actCo mb mf)
        actCoV : forall {Ga De Th k i}(mb : Mb De Th)(mf : Mf Ga De)
                   (x : k <- Ga)(sz : Sp De k (ok i)) ->
                   actNm Ab mb (actV Af mf x sz) == actV Ac (actCo mb mf) x (actSp Ab mb sz)
      actNmCo : forall {Ga De Th}(mb : Mb De Th)(mf : Mf Ga De) ->
                forall {k}(t : Nm Ga k) ->
                actNm Ab mb (actNm Af mf t) == actNm Ac (actCo mb mf) t
      actNoCo : forall {Ga De Th}(mb : Mb De Th)(mf : Mf Ga De) ->
                forall D (ts : Node (Nm Ga) D) ->
                actNo Ab D mb (actNo Af D mf ts) == actNo Ac D (actCo mb mf) ts
      actSpCo : forall {Ga De Th j k}(mb : Mb De Th)(mf : Mf Ga De)(sz : Sp Ga j k) ->
                actSp Ab mb (actSp Af mf sz) == actSp Ac (actCo mb mf) sz
      actNmCo mb mf (x $ sz)
        rewrite actCoV mb mf x (actSp Af mf sz)
              | actSpCo mb mf sz
        = refl
      actNmCo mb mf < ts > rewrite actNoCo mb mf (F _) ts = refl
      actNmCo mb mf {j !- k} (\\ t)
        rewrite actNmCo (actW Ab mb) (actW Af mf) t
              | actCoW j mb mf
              = refl
      actNoCo mb mf (# k) t = actNmCo mb mf t
      actNoCo mb mf (Sg' S T) (s , ts) rewrite actNoCo mb mf (T s) ts = refl
      actNoCo mb mf (D *' D') (ts , ts')
        rewrite actNoCo mb mf D ts | actNoCo mb mf D' ts' = refl
      actNoCo mb mf One' <> = refl
      actSpCo mb mf [] = refl
      actSpCo mb mf (sz -, s)
        rewrite actSpCo mb mf sz | actNmCo mb mf s
        = refl

    open ACTIONCOMPOSITION

    ThnThnThn : ACTIONCOMPOSITION Thn Thn Thn
    ThnThnThn = record
      { actCo = _-<-_
      ; actCoW = \ _ _ _ -> refl
      ; actCoV = \ mb mf x sz -> (_$ actSp Thn mb sz) $= sym (thinCo mb mf x)
      }
    
    data Sel (k : Kind) : Bwd Kind -> Bwd Kind -> Set where
      ze : forall {Ga} -> Sel k (Ga -, k) Ga
      su : forall {j Ga De} -> Sel k Ga De -> Sel k (Ga -, j) (De -, j)

    sel? : forall {Ga De j k}(x : Sel k Ga De)(y : j <- Ga) ->
             (k == j) + (j <- De)
    sel? ze ze = inl refl
    sel? ze (su y) = inr y
    sel? (su x) ze = inr ze
    sel? (su x) (su y) with sel? x y
    sel? (su x) (su y) | inl refl = inl refl
    sel? (su x) (su y) | inr z = inr (su z)

    Sb1 : (k : Kind) -> ACTION (\ Ga De -> Sel k Ga De * Nm De k)
    hitV : forall (k : Kind){Ga De j i} -> Sel k Ga De * Nm De k ->
              j <- Ga -> Sp De j (ok i) -> Nm De (ok i)
    inst : (k : Kind) -> forall {De l} -> Nm De k -> Ps De k l -> Nm De l
    Sb1 k = record
      { actW = \ { (x , s) -> su x , actNm Thn (o' oi) s }
      ; actV = hitV k
      }
    hitV k (x , s) y sz with sel? x y
    hitV k (x , s) y sz | inl refl = inst k s (sz <>> [])
    hitV k (x , s) y sz | inr z    = z $ sz
    inst k t [] = t
    inst (j !- k) (\\ t) (s ,- ss) = inst k (actNm (Sb1 j) (ze , s) t) ss

    selThin : forall {k Ga De} -> Sel k Ga De -> De <= Ga
    selThin ze = o' oi
    selThin (su x) = os (selThin x)

    selVar : forall {k Ga De} -> Sel k Ga De -> k <- Ga
    selVar ze = ze
    selVar (su x) = su (selVar x)

    Swap : forall {Ga De De' Th j k}
                  (y : Sel k De Th)(x : Sel j Ga De)
                  (x' : Sel j De' Th)(y' : Sel k Ga De') -> Set
    Swap y x x' y' =
                  (thin (selThin x) (selVar y) == selVar y') *
                  (thin (selThin y') (selVar x') == selVar x)

    swap : forall {Ga De Th j k}(y : Sel k De Th)(x : Sel j Ga De) ->
            Sg (Bwd Kind) \ De' -> Sg (Sel j De' Th) \ x' -> Sg (Sel k Ga De') \ y' ->
            Swap y x x' y'
    swap y ze = _ , ze , su y , (su $= oiQ _) , refl
    swap ze (su x) = _ , x , ze , refl , (su $= oiQ _)
    swap (su y) (su x) with swap y x
    ... | _ , x' , y' , qy' , qx = _ , su x' , su y' , (su $= qy') , (su $= qx) 

    ExchangeNm : forall {Ga De Th j k l}
                  (y : Sel k De Th)(t : Nm Th k)
                  (x : Sel j Ga De)(s : Nm De j)
                  (u : Nm Ga l) -> Set
    ExchangeNm {Ga}{De}{Th}{j}{k}{l} y t x s u with swap y x
    ... | _ , x' , y' , qy' , qx =
      actNm (Sb1 k) (y , t) (actNm (Sb1 j) (x , s) u) ==
      actNm (Sb1 j) (x' , actNm (Sb1 k) (y , t) s) (actNm (Sb1 k) (y' , actNm Thn (selThin x') t) u)

    exchangeNm : forall {Ga De Th j k l}
                  (y : Sel k De Th)(t : Nm Th k)
                  (x : Sel j Ga De)(s : Nm De j)
                  (u : Nm Ga l) -> ExchangeNm y t x s u
    exchangeNm y t x s (z $ uz) = {!!}
    exchangeNm y t x s < us > = {!!}
    exchangeNm y t x s (\\ u) with exchangeNm (su y) (actNm Thn (o' oi) t) (su x) (actNm Thn (o' oi) s) u
    ... | q with swap y x
    ... | De' , x' , y' , qy' , qx = \\_ $= {!q!}

-- exchangeNm (su y) (actNm Thn (o' oi) t) (su x) (actNm Thn (o' oi) s) u









    Env : Bwd Kind -> Bwd Kind -> Set
    Env Ga De = [Bwd] (Nm De) Ga

    expand : forall k {Ga j} -> j <- Ga -> Sp Ga j k -> Nm Ga k
    expand (ok i)   x sz = x $ sz
    expand (j !- k) x sz = \\ expand k (thin (o' oi) x) (actSp Thn (o' oi) sz -, expand j ze [])

    expandThin : forall {Ga De}(th : Ga <= De) ->
                 forall k {j}(x : j <- Ga)(sz : Sp Ga j k) ->
                 actNm Thn th (expand k x sz) == expand k (thin th x) (actSp Thn th sz)
    expandThin th (ok i)   x sz = refl
    expandThin th (k !- l) x sz
      rewrite oiQ x
            | expandThin (os th) l (su x) (actSp Thn (o' oi) sz -, expand k ze [])
            | expandThin (os th) k ze []
            | actSpCo ThnThnThn (os{_}{k} th) (o' oi) sz | th -<-oiQ
            | actSpCo ThnThnThn (o'{_}{k} oi) th sz | oiQ (thin th x) | oi-<-Q th
            = refl

    SbS : ACTION Env
    SbS = record
      { actW = \ ga -> [bwd] (actNm Thn (o' oi)) ga , expand _ ze []
      ; actV = \ ga x sz -> inst _ (bProj ga x) (sz <>> []) 
      }

    envi : forall {Ga} -> Env Ga Ga
    envi {[]} = <>
    envi {Ga -, k} = actW SbS envi

    enviProj : forall {Ga k}(x : k <- Ga) -> bProj envi x == expand k x []
    enviProj ze     = refl
    enviProj {Ga -, j}(su x)
      rewrite bProjNatural (actNm Thn (o'{_}{j} oi)) envi x
            | enviProj x
            | expandThin (o'{_}{j} oi) _ x []
            | oiQ x
            = refl

    thinPs : forall {Ga De}(th : Ga <= De) -> forall {k l} -> Ps Ga k l -> Ps De k l
    thinPs th [] = []
    thinPs th (s ,- ss) = actNm Thn th s ,- thinPs th ss
{-
    instSb1 : forall {Ga De j k i}(x : Sel j Ga De)(s : Nm De j)(t : Nm Ga k)(ss : Ps De k (ok i)) ->
      inst k (actNm (Sb1 j) (x , s) t) ss == actNm (Sb1 j) (x , s) (inst k t (thinPs (selThin x) ss))
    instSb1 x s t [] = refl
    instSb1 {j = j} x s (\\ t) (a ,- as)
      rewrite instSb1 ze a ((actNm (Sb1 j) (actW (Sb1 j) (x , s)) t)) as
            | instSb1 (su x) (actNm Thn (o' oi) s) t (thinPs (o' oi) as)
      = {!!}

    instExpand : forall {Ga j k i}(x : j <- Ga)(sz : Sp Ga j k)(ss : Ps Ga k (ok i)) ->
                   inst k (expand k x sz) ss == (x $ (sz <>< ss))
    instExpand x sz [] = refl
    instExpand x sz (s ,- ss) rewrite oiQ x = {!!}

    SbSId : ACTIONIDENTITY SbS
    SbSId = record
      { actId  = envi
      ; actIdW = \ _ -> refl
      ; actIdV = hoid
      } where
      hoid : forall {Ga k i}(x : k <- Ga) (sz : Sp Ga k (ok i)) ->
        inst k (bProj envi x) (sz <>> []) == (x $ sz)
      hoid x sz rewrite enviProj x = {!!}
-}
