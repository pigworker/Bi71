module Par where

open import Basics
open import OPE
open import Tm
open import Env
open import Subst

data _~>>_ {n} : {d : Dir} -> Tm n d -> Tm n d -> Set where
  star : star ~>> star
  pi   : forall {S S' T T'} -> S ~>> S' -> T ~>> T' -> pi S T ~>> pi S' T'
  lam  : forall {t t'} -> t ~>> t' -> lam t ~>> lam t'
  [_]  : forall {e e'} -> e ~>> e' -> [ e ] ~>> [ e' ]
  var  : (i : Fin n) -> var i ~>> var i
  _$_  : forall {f f' s s'} -> f ~>> f' -> s ~>> s' -> (f $ s) ~>> (f' $ s')
  _::_ : forall {t t' T T'} -> t ~>> t' -> T ~>> T' -> (t :: T) ~>> (t' :: T')
  beta : forall {t t' S S' T T' s s'} ->
           t ~>> t' -> S ~>> S' -> T ~>> T' -> s ~>> s' ->
           ((lam t :: pi S T) $ s) ~>> Sb.act (si -, (s' :: S')) (t' :: T')
  upsi : forall {t t' T} -> t ~>> t' -> [ t :: T ] ~>> t'

parRefl : forall {d n}(t : Tm n d) -> t ~>> t
parRefl star = star
parRefl (pi S T) = pi (parRefl S) (parRefl T)
parRefl (lam t) = lam (parRefl t)
parRefl [ e ] = [ parRefl e ]
parRefl (var i) = var i
parRefl (f $ s) = parRefl f $ parRefl s
parRefl (t :: T) = parRefl t :: parRefl T

_~~>>_ : forall {n m} -> Env (Tm m syn) n -> Env (Tm m syn) n -> Set
[] ~~>> [] = One
(sz -, s) ~~>> (tz -, t) = (sz ~~>> tz) * (s ~>> t)

parzRefl : forall {n m}(sz : Env (Tm m syn) n) -> sz ~~>> sz
parzRefl [] = <>
parzRefl (sz -, s) = parzRefl sz , parRefl s

parThin : forall {d n m}{s t : Tm n d}(th : n <= m) ->
           s ~>> t -> Th.act th s ~>> Th.act th t
parThin th star = star
parThin th (pi rS rT) = pi (parThin th rS) (parThin (os th) rT)
parThin th (lam rt) = lam (parThin (os th) rt)
parThin th [ re ] = [ parThin th re ]
parThin th (var i) = var (thin th i)
parThin th (rf $ rs) = parThin th rf $ parThin th rs
parThin th (rt :: rT) = parThin th rt :: parThin th rT
parThin th (beta {t}{t'}{S}{S'}{T}{T'}{s}{s'} rt rS rT rs)
  with beta (parThin (os th) rt) (parThin th rS)
            (parThin (os th) rT) (parThin th rs)
... | z
    rewrite ActCo.actCo THINSUBSTSUBST th (si -, (s' :: S')) t'
          | ActCo.actCo THINSUBSTSUBST th (si -, (s' :: S')) T'
          | ActCo.actCo SUBSTTHINSUBST (si -, Th.act th (s' :: S')) (os th) t'
          | ActCo.actCo SUBSTTHINSUBST (si -, Th.act th (s' :: S')) (os th) T'
          | thin/idQ th
          = z
parThin th (upsi rt) = upsi (parThin th rt)

parThinz : forall {n m m'}(sz tz : Env (Tm m syn) n)(th : m <= m') ->
  sz ~~>> tz -> env (Th.act th) sz ~~>> env (Th.act th) tz
parThinz []        []        th <> = <>
parThinz (sz -, s) (tz -, t) th (rz , r) = parThinz sz tz th rz , parThin th r

parWeak : forall {n m}{sz tz : Env (Tm m syn) n} ->
          sz ~~>> tz -> Sb.actW sz ~~>> Sb.actW tz
parWeak rz = parThinz _ _ (o' oi) rz , var ze

parStab : forall {d n m}{sz tz : Env (Tm m syn) n}{s t : Tm n d} ->
          sz ~~>> tz -> s ~>> t -> Sb.act sz s ~>> Sb.act tz t
parStab rz star = star
parStab rz (pi rS rT) = pi (parStab rz rS) (parStab (parThinz _ _ (o' oi) rz , var _) rT)
parStab rz (lam rt) = lam (parStab (parThinz _ _ (o' oi) rz , var _) rt)
parStab rz [ re ] = [ parStab rz re ]
parStab rz (var i) = go _ _ rz i where
  go : forall {n m} (sz tz : Env (Tm m syn) n) ->
     sz ~~>> tz -> (i : Fin n) -> (sz ! i) ~>> (tz ! i)
  go (sz -, s) (tz -, t) (rz , r) ze = r
  go (sz -, s) (tz -, t) (rz , r) (su i) = go sz tz rz i
parStab rz (rf $ rs) = parStab rz rf $ parStab rz rs
parStab rz (rt :: rT) = parStab rz rt :: parStab rz rT
parStab {sz = sz}{tz = tz} rz (beta {t}{t'}{S}{S'}{T}{T'}{s}{s'} rt rS rT rs)
    with beta (parStab (parThinz _ _ (o' oi) rz , var ze) rt)
              (parStab rz rS)
              (parStab (parThinz _ _ (o' oi) rz , var ze) rT)
              (parStab rz rs)
... | z
  rewrite ActCo.actCo SUBSTSUBSTSUBST tz (si -, (s' :: S')) t'
        | ActCo.actCo SUBSTSUBSTSUBST tz (si -, (s' :: S')) T'
        | ActCo.actCo SUBSTSUBSTSUBST (si -, Sb.act tz (s' :: S')) (Sb.actW tz) t'
        | ActCo.actCo SUBSTSUBSTSUBST (si -, Sb.act tz (s' :: S')) (Sb.actW tz) T'
        | envenvQ (Sb.act (si -, Sb.act tz (s' :: S'))) (Th.act (o' oi)) tz
        | envextQ (lemma2 si (Sb.act tz (s' :: S'))) tz
        | envIdQ (Sb.act si) (ActId.actId SUBSTID) tz
        | subsiQ tz
  = z
parStab rz (upsi rt) = upsi (parStab rz rt)
