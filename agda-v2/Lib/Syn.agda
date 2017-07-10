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
    data Ne (Ga : Bwd Kind)(k : Kind) : Set

    data Nm Ga where
      `   : forall {i} -> Ne Ga (ok i) -> Nm Ga (ok i)
      <_> : forall {i} -> Node (Nm Ga) (F i) -> Nm Ga (ok i)
      \\_ : forall {j k} -> Nm (Ga -, j) k -> Nm Ga (j !- k)

    data Ne Ga k where
      #    : k <- Ga -> Ne Ga k
      _!$_ : forall {j} -> Ne Ga (j !- k) -> Nm Ga j -> Ne Ga k
      
    infixr 3 \\_
    infixl 4 _!$_

    data Spine (Ga : Bwd Kind) : Kind -> Kind -> Set where
      [] : forall {l} -> Spine Ga l l
      _::_ : forall {j k l} -> Nm Ga j -> Spine Ga k l -> Spine Ga (j !- k) l

    neSpine : forall {Ga k i} -> Ne Ga k -> Spine Ga k (ok i) -> Nm Ga (ok i)
    neSpine f [] = ` f
    neSpine f (s :: ss) = neSpine (f !$ s) ss

    record ACTION (M : Bwd Kind -> Bwd Kind -> Set) : Set where
      field
        actW : forall {k Ga De} -> M Ga De -> M (Ga -, k) (De -, k)
        actV : forall {Ga De k i} -> M Ga De -> k <- Ga -> Spine De k (ok i) -> Nm De (ok i)
      actNm   : forall {Ga De k} -> M Ga De -> Nm Ga k -> Nm De k
      actNe   : forall {Ga De k i} -> M Ga De -> Ne Ga k -> Spine De k (ok i) -> Nm De (ok i)
      actNo   : forall {Ga De} D -> M Ga De -> Node (Nm Ga) D -> Node (Nm De) D
      actNm ga (` e) = actNe ga e []
      actNm ga < ts > = < actNo (F _) ga ts >
      actNm ga (\\ t) = \\ actNm (actW ga) t
      actNo (# k) ga t = actNm ga t
      actNo (Sg' A T) ga (a , ts) = a , actNo (T a) ga ts
      actNo (D *' D') ga (ts , ts') = actNo D ga ts , actNo D' ga ts'
      actNo One' ga <> = <>
      actNe ga (# i) ss = actV ga i ss
      actNe ga (f !$ s') ss = actNe ga f (actNm ga s' :: ss)

    open ACTION public

    Th : ACTION _<=_
    Th = record { actW = os ; actV = \ th x ss -> neSpine (# (thin th x)) ss }

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

    Sb1 : (k : Kind) -> ACTION \ Ga De -> Sel k Ga De * Nm De k
    hitV : forall (k : Kind){Ga De j i} -> Sel k Ga De * Nm De k ->
              j <- Ga -> Spine De j (ok i) -> Nm De (ok i)
    inst : (k : Kind) -> forall {De i} -> Nm De k -> Spine De k (ok i) -> Nm De (ok i)
    Sb1 k = record
      { actW = \ { (x , s) -> su x , actNm Th (o' oi) s }
      ; actV = hitV k
      }
    hitV k (x , s) y ss with sel? x y
    hitV k (x , s) y ss | inl refl = inst k s ss
    hitV k (x , s) y ss | inr z    = neSpine (# z) ss
    inst (ok _) t [] = t
    inst (j !- k) (\\ t) (s :: ss) = inst k (actNm (Sb1 j) (ze , s) t) ss

    Env : Bwd Kind -> Bwd Kind -> Set
    Env Ga De = [Bwd] (Nm De) Ga
    thinNe : forall {Ga De k} -> Ga <= De -> Ne Ga k -> Ne De k
    thinNe th (# x) = # (thin th x)
    thinNe th (e !$ s) = thinNe th e !$ actNm Th th s
    expand : forall k {Ga} -> Ne Ga k -> Nm Ga k
    expand (ok i) e = ` e
    expand (j !- k) e = \\ expand k (thinNe (o' oi) e !$ expand j (# ze))
    expandThin : forall {Ga De}(th : Ga <= De) -> forall k (e : Ne Ga k) ->
      actNm Th th (expand k e) == expand k (thinNe th e)
    expandThin th (ok i) e = {!!}
    expandThin th (j !- k) e
      rewrite expandThin (os th) k (thinNe (o' oi) e !$ expand j (# ze))
            | expandThin (os th) j (# ze)
       = {!!}
    SbS : ACTION Env
    SbS = record
      { actW = \ ga -> [bwd] (actNm Th (o' oi)) ga , expand _ (# ze)
      ; actV = \ ga i ss -> inst _ (bProj ga i) ss
      }

    record ACTIONIDENTITY {M}(A : ACTION M) : Set where
      field
        actId : forall {Ga} -> M Ga Ga
        actIdW : forall k {Ga} -> actW A actId == actId {Ga -, k}
        actIdV : forall {Ga k i}(x : k <- Ga)(ss : Spine Ga k (ok i)) ->
          actV A actId x ss == neSpine (# x) ss
      actNmId : forall {Ga k}(t : Nm Ga k) -> actNm A actId t == t
      actNeId : forall {Ga k i}(e : Ne Ga k)(ss : Spine Ga k (ok i)) ->
                  actNe A actId e ss == neSpine e ss
      actNoId : forall {Ga} D (ts : Node (Nm Ga) D) ->
                  actNo A D actId ts == ts
      actNmId (` e) = actNeId e []
      actNmId < ts > rewrite actNoId (F _) ts = refl
      actNmId {Ga}{j !- k} (\\ t) rewrite actIdW j {Ga} | actNmId t = refl
      actNeId (# x) ss = actIdV x ss
      actNeId (e !$ s) ss rewrite actNmId s = actNeId e (s :: ss)
      actNoId (# k) t = actNmId t
      actNoId (Sg' S T) (s , ts) rewrite actNoId (T s) ts = refl
      actNoId (D *' D') (ts , ts') rewrite actNoId D ts | actNoId D' ts' = refl
      actNoId One' <> = refl

    ThId : ACTIONIDENTITY Th
    ThId = record { actId = oi ; actIdW = \ _ -> refl ; actIdV = help } where
      help : forall {Ga : Bwd Kind} {k : Kind} {i : I}
               (x : k <- Ga) (ss : Spine Ga k (ok i)) ->
               neSpine (# (thin oi x)) ss == neSpine (# x) ss
      help x ss rewrite oiQ x = refl

    envi : forall {Ga} -> Env Ga Ga
    envi {[]} = <>
    envi {Ga -, k} = actW SbS (envi {Ga})

    enviProj : forall {k Ga}(x : k <- Ga) -> bProj envi x == expand k (# x)
    enviProj ze = refl
    enviProj (su {_}{k} x)
      rewrite bProjNatural (actNm Th (o'{_}{k} oi)) envi x
            | enviProj x
            | expandThin (o' {_}{k} oi) _ (# x)
            | oiQ x
            = refl
    SbSId : ACTIONIDENTITY SbS
    SbSId = record
      { actId = envi
      ; actIdW = \ _ -> refl
      ; actIdV = {!!}
      }
