module Tm where

open import Basics
open import OPE
open import Env

data Dir : Set where chk syn : Dir

data Tm (n : Nat) : Dir -> Set where

  star : Tm n chk
  pi   : Tm n chk -> Tm (su n) chk -> Tm n chk
  lam  : Tm (su n) chk -> Tm n chk
  [_]  : Tm n syn -> Tm n chk

  var  : Fin n -> Tm n syn
  _$_  : Tm n syn -> Tm n chk -> Tm n syn
  _::_ : Tm n chk -> Tm n chk -> Tm n syn

record Act (A : Nat -> Nat -> Set) : Set where
  field
    actV : forall {n m} -> A n m -> Fin n -> Tm m syn
    actW : forall {n m} -> A n m -> A (su n) (su m)

  act : forall {n m d} -> A n m -> Tm n d -> Tm m d
  act a star = star
  act a (pi S T) = pi (act a S) (act (actW a) T)
  act a (lam t) = lam (act (actW a) t)
  act a [ e ] = [ act a e ]
  act a (var i) = actV a i
  act a (f $ s) = act a f $ act a s
  act a (t :: T) = act a t :: act a T

THIN : Act _<=_
THIN = record { actV = \ th x -> var (thin th x) ; actW = os }

module Th = Act THIN

record ActId {A : Nat -> Nat -> Set}(AA : Act A)(ai : forall {n} -> A n n) : Set where
  field
    actVId : forall {n}(i : Fin n) -> Act.actV AA ai i == var i
    actWId : forall n -> Act.actW AA (ai {n}) == ai {su n}

  actId : forall {d n}(t : Tm n d) -> Act.act AA ai t == t
  actId star = refl
  actId {n = n} (pi S T) rewrite actId S | actWId n | actId T = refl
  actId {n = n} (lam t) rewrite actWId n | actId t = refl
  actId [ e ] rewrite actId e = refl
  actId (var i) = actVId i
  actId (f $ s) rewrite actId f | actId s = refl
  actId (t :: T) rewrite actId t | actId T = refl

THINID : ActId THIN oi
THINID = record { actVId = help ; actWId = \ n -> refl } where
  help : forall {n} (i : Fin n) -> var (thin oi i) == var i
  help i rewrite oiQ i = refl

record ActCo {A B C : Nat -> Nat -> Set}
             (AA : Act A)(AB : Act B)(AC : Act C)
             (abc : forall {n m l} -> A m l -> B n m -> C n l) : Set where
  field
    actVCo : forall {n m l}(a : A m l)(b : B n m)(i : Fin n) ->
               Act.act AA a (Act.actV AB b i) == Act.actV AC (abc a b) i
    actWCo : forall {n m l}(a : A m l)(b : B n m) ->
               abc (Act.actW AA a) (Act.actW AB b) == Act.actW AC (abc a b)
  actCo : forall {d n m l}(a : A m l)(b : B n m)(t : Tm n d) ->
          Act.act AA a (Act.act AB b t) == Act.act AC (abc a b) t
  actCo a b star = refl
  actCo a b (pi S T)
    rewrite actCo a b S
          | actCo (Act.actW AA a) (Act.actW AB b) T
          | actWCo a b
          = refl
  actCo a b (lam t)
    rewrite actCo (Act.actW AA a) (Act.actW AB b) t
          | actWCo a b
          = refl
  actCo a b [ e ] rewrite actCo a b e = refl
  actCo a b (var i) = actVCo a b i
  actCo a b (f $ s) rewrite actCo a b f | actCo a b s = refl
  actCo a b (t :: T) rewrite actCo a b t | actCo a b T = refl

THINTHINTHIN : ActCo THIN THIN THIN _-<-_
THINTHINTHIN = record { actVCo = help ; actWCo = \ _ _ -> refl } where
  help : forall {n m l} (a : m <= l) (b : n <= m) (i : Fin n) ->
          var (thin a (thin b i)) == var (thin (a -<- b) i)
  help th ph i rewrite thinCo th ph i = refl

lemma : forall {n m}(th : n <= m)(t : Tm n syn) ->
            Th.act (os th) (Th.act (o' oi) t) ==
            Th.act (o' th) t
lemma th t
  rewrite ActCo.actCo THINTHINTHIN (os th) (o' oi) t
        | th -<-oiQ
        = refl

lemma' : forall {n m}(th : n <= m)(t : Tm n syn) ->
            Th.act (o' oi) (Th.act th t) ==
            Th.act (o' th) t
lemma' th t
  rewrite ActCo.actCo THINTHINTHIN (o' oi) th t
        | oi-<-Q th
        = refl
