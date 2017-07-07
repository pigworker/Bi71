module Subst where

open import Basics
open import OPE
open import Tm
open import Env

SUBST : Act \ n m -> Env (Tm m syn) n
SUBST = record { actV = _!_ ; actW = \ tz -> env (Th.act (o' oi)) tz -, var ze }

module Sb = Act SUBST

si : forall {n} -> Env (Tm n syn) n
si {ze} = []
si {su n} = env (Th.act (o' oi)) si -, var ze

siQ : forall {n}(i : Fin n) -> (si ! i) == var i
siQ ze = refl
siQ (su i) rewrite env!Q (Th.act (o' oi)) si i | siQ i | oiQ i = refl

thin/idQ : forall {n m}(th : n <= m) -> env (Th.act th) si == (si / th)
thin/idQ oz = refl
thin/idQ {su n}{su m} (os th)
  rewrite envenvQ (Th.act (os th)) (Th.act (o' oi)) si
        | envextQ (lemma th) si
        | thin/idQ (o' th)
        = refl
 where
thin/idQ (o' th)
  rewrite env/Q (Th.act (o' oi)) si th
        | sym (thin/idQ th)
        | envenvQ (Th.act (o' oi)) (Th.act th) si
        | envextQ (lemma' th) si
        = refl

SUBSTID : ActId SUBST si
SUBSTID = record { actVId = siQ ; actWId = \ _ -> refl }

SUBSTTHINSUBST : ActCo SUBST THIN SUBST _/_
SUBSTTHINSUBST = record { actVCo = /!Q ; actWCo = helpW } where
  helpW : {n m l : Nat} (a : Env (Tm l syn) m) (b : n <= m) ->
      ((env (Th.act (o' oi)) a / b) -, var ze) == Sb.actW (a / b)
  helpW a b rewrite env/Q (Th.act (o' oi)) a b = refl

coS : forall {A : Nat -> Nat -> Set} -> Act A ->
        forall {n m l} -> A m l -> Env (Tm m syn) n -> Env (Tm l syn) n
coS AA a = env (Act.act AA a)

THINSUBSTSUBST : ActCo THIN SUBST SUBST (coS THIN)
THINSUBSTSUBST = record { actVCo = helpV ; actWCo = helpW } where
  helpV : {n m l : Nat} (a : m <= l) (b : Env (Tm m syn) n)
      (i : Fin n) -> Th.act a (Sb.actV b i) == Sb.actV (coS THIN a b) i
  helpV a b i rewrite env!Q (Th.act a) b i = refl
  helpC : forall {m l}(a : m <= l)(t : Tm m syn) ->
            Th.act (os a) (Th.act (o' oi) t) == Th.act (o' oi) (Th.act a t)
  helpC a t
    rewrite ActCo.actCo THINTHINTHIN (os a) (o' oi) t
          | ActCo.actCo THINTHINTHIN (o' oi) a t
          | a -<-oiQ
          | oi-<-Q a
    = refl
  helpW : {n m l : Nat} (a : m <= l) (b : Env (Tm m syn) n) ->
          coS THIN (Th.actW a) (Sb.actW b) == Sb.actW (coS THIN a b)
  helpW a b
    rewrite envenvQ (Th.act (Th.actW a)) (Th.act (o' oi)) b
          | envenvQ (Th.act (o' oi)) (Th.act a) b
          | envextQ (helpC a) b
          = refl

SUBSTSUBSTSUBST : ActCo SUBST SUBST SUBST (coS SUBST)
SUBSTSUBSTSUBST = record { actVCo = helpV ; actWCo = helpW } where

  helpV : {n m l : Nat} (a : Env (Tm l syn) m) (b : Env (Tm m syn) n)
          (i : Fin n) -> Sb.act a (Sb.actV b i) == Sb.actV (coS SUBST a b) i
  helpV a b i rewrite env!Q (Sb.act a) b i = refl

  helpC : forall {m l}(a : Env (Tm l syn) m)(t : Tm m syn) ->
           Sb.act (Sb.actW a) (Th.act (o' oi) t) ==
           Th.act (o' oi) (Sb.act a t)
  helpC a t
    rewrite ActCo.actCo SUBSTTHINSUBST (Sb.actW a) (o' oi) t
          | ActCo.actCo THINSUBSTSUBST (o' oi) a t
          | env (Th.act (o' oi)) a /oiQ
    = refl
  helpW : {n m l : Nat} (a : Env (Tm l syn) m) (b : Env (Tm m syn) n) ->
      coS SUBST (Sb.actW a) (Sb.actW b) == Sb.actW (coS SUBST a b)
  helpW a b
    rewrite envenvQ (Sb.act (Sb.actW a)) (Th.act (o' oi)) b
          | envenvQ (Th.act (o' oi)) (Sb.act a) b
          | envextQ (helpC a) b
    = refl

lemma2 : forall {n m}(tz : Env (Tm m syn) n)(t : Tm m syn) ->
         (x : Tm n syn) -> Sb.act (tz -, t) (Th.act (o' oi) x) == Sb.act tz x
lemma2 tz t x
  rewrite ActCo.actCo SUBSTTHINSUBST (tz -, t) (o' oi) x
        | tz /oiQ
  = refl

subsiQ : forall {n m}(tz : Env (Tm m syn) n) -> env (Sb.act tz) si == tz
subsiQ [] = refl
subsiQ (tz -, t)
  rewrite envenvQ (Sb.act (tz -, t)) (Th.act (o' oi)) si
        | envextQ (lemma2 tz t) si
        | subsiQ tz
  = refl

