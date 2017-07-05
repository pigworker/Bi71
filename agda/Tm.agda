module Tm where

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

sym : forall {l}{X : Set l}{x y : X} -> x == y -> y == x
sym refl = refl

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
        (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a)(a : A) -> C a (g a)
(f - g) x = f (g x)

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data Dir : Set where chk syn : Dir

data Fin : Nat -> Set where
  ze : forall {n} -> Fin (su n)
  su : forall {n} -> Fin n -> Fin (su n)

data Tm (n : Nat) : Dir -> Set where

  star : Tm n chk
  pi   : Tm n chk -> Tm (su n) chk -> Tm n chk
  lam  : Tm (su n) chk -> Tm n chk
  [_]  : Tm n syn -> Tm n chk

  var  : Fin n -> Tm n syn
  _$_  : Tm n syn -> Tm n chk -> Tm n syn
  _::_ : Tm n chk -> Tm n chk -> Tm n syn

data _<=_ : Nat -> Nat -> Set where
  oz : ze <= ze
  os : forall {n m} -> n <= m -> su n <= su m
  o' : forall {n m} -> n <= m ->    n <= su m

thin : forall {n m} -> n <= m -> Fin n -> Fin m
thin oz ()
thin (o' th)  i = su (thin th i)
thin (os th) ze = ze
thin (os th) (su i) = su (thin th i)

oi : forall {n} -> n <= n
oi {ze} = oz
oi {su x} = os oi

oiQ : forall {n}(i : Fin n) -> thin oi i == i
oiQ ze = refl
oiQ (su i) rewrite oiQ i = refl

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

data Env (X : Set) : Nat -> Set where
  []   : Env X ze
  _-,_ : forall {n} -> Env X n -> X -> Env X (su n)

env : forall {n X Y} -> (X -> Y) -> Env X n -> Env Y n
env f []        = []
env f (xz -, x) = env f xz -, f x

_!_ : forall {X n} -> Env X n -> Fin n -> X
(xz -, x) ! ze = x
(xz -, x) ! su i = xz ! i

env!Q : forall {n X Y}(f : X -> Y)(xz : Env X n)(i : Fin n) ->
  (env f xz ! i) == f (xz ! i)
env!Q f (xz -, x) ze = refl
env!Q f (xz -, x) (su i) = env!Q f xz i

envIdQ : forall {n X}(f : X -> X)(q : (x : X) -> f x == x) ->
         (xz : Env X n) -> env f xz == xz
envIdQ f q [] = refl
envIdQ f q (xz -, x) rewrite envIdQ f q xz | q x = refl

SUBST : Act \ n m -> Env (Tm m syn) n
SUBST = record { actV = _!_ ; actW = \ tz -> env (Th.act (o' oi)) tz -, var ze }

module Sb = Act SUBST

si : forall {n} -> Env (Tm n syn) n
si {ze} = []
si {su n} = env (Th.act (o' oi)) si -, var ze

siQ : forall {n}(i : Fin n) -> (si ! i) == var i
siQ ze = refl
siQ (su i) rewrite env!Q (Th.act (o' oi)) si i | siQ i | oiQ i = refl

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

SUBSTID : ActId SUBST si
SUBSTID = record { actVId = siQ ; actWId = \ _ -> refl }

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

_-<-_ : forall {n m l} -> m <= l -> n <= m -> n <= l
oz -<- oz = oz
os th -<- os ph = os (th -<- ph)
os th -<- o' ph = o' (th -<- ph)
o' th -<- ph = o' (th -<- ph)

_-<-oiQ : forall {n m}(th : n <= m) -> (th -<- oi) == th
oz -<-oiQ = refl
os th -<-oiQ rewrite th -<-oiQ = refl
o' th -<-oiQ rewrite th -<-oiQ = refl

oi-<-Q : forall {n m}(th : n <= m) -> (oi -<- th) == th
oi-<-Q oz = refl
oi-<-Q (os th) rewrite oi-<-Q th = refl
oi-<-Q (o' th) rewrite oi-<-Q th = refl

thinCo : forall {n m l}(th : m <= l)(ph : n <= m)(i : Fin n) ->
           thin th (thin ph i) == thin (th -<- ph) i
thinCo oz oz ()
thinCo (os th) (os ph) ze = refl
thinCo (os th) (os ph) (su i) rewrite thinCo th ph i = refl
thinCo (os th) (o' ph) i rewrite thinCo th ph i = refl
thinCo (o' th) ph i rewrite thinCo th ph i = refl

THINTHINTHIN : ActCo THIN THIN THIN _-<-_
THINTHINTHIN = record { actVCo = help ; actWCo = \ _ _ -> refl } where
  help : forall {n m l} (a : m <= l) (b : n <= m) (i : Fin n) ->
          var (thin a (thin b i)) == var (thin (a -<- b) i)
  help th ph i rewrite thinCo th ph i = refl

_/_ : forall {n m X} -> Env X m -> n <= m -> Env X n
[] / oz = []
(xz -, x) / os th = (xz / th) -, x
(xz -, _) / o' th = xz / th

/!Q : forall {n m X}(xz : Env X m)(th : n <= m)(i : Fin n) ->
        (xz ! thin th i) == ((xz / th) ! i)
/!Q [] oz ()
/!Q (xz -, x) (os th) ze = refl
/!Q (xz -, x) (os th) (su i) rewrite /!Q xz th i = refl
/!Q (xz -, x) (o' th) i = /!Q xz th i

_/oiQ : forall {n X}(xz : Env X n) -> (xz / oi) == xz
[] /oiQ = refl
(xz -, x) /oiQ rewrite xz /oiQ = refl

env/Q : forall {n m X Y}(f : X -> Y)(xz : Env X m)(th : n <= m) ->
  (env f xz / th) == env f (xz / th)
env/Q f [] oz = refl
env/Q f (xz -, x) (os th) rewrite env/Q f xz th = refl
env/Q f (xz -, x) (o' th) = env/Q f xz th


envenvQ : forall {n X Y Z}(g : Y -> Z)(f : X -> Y)(xz : Env X n) ->
  env g (env f xz) == env (g - f) xz
envenvQ g f [] = refl
envenvQ g f (xz -, x) rewrite envenvQ g f xz = refl

envextQ : forall {n X Y}{f g : X -> Y} -> ((x : X) -> f x == g x) ->
          (xz : Env X n) -> env f xz == env g xz
envextQ q [] = refl
envextQ q (xz -, x) rewrite envextQ q xz | q x = refl

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

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T

record One : Set where
  constructor <>

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

data Zero : Set where

NoRadFun : forall {n} -> Tm n syn -> Set
NoRadFun (lam _ :: pi _ _) = Zero
NoRadFun _ = One

NoRad : forall {n} -> Tm n syn -> Set
NoRad (_ :: _) = Zero
NoRad _ = One

data RedView {n} : forall {d} -> Tm n d -> Set where
  star : RedView star
  pi   : forall {S T} -> RedView (pi S T)
  lam  : forall {t} -> RedView (lam t)
  emb  : forall {e} -> NoRad e -> RedView [ e ]
  var  : forall {i} -> RedView (var i)
  app  : forall {f s} -> NoRadFun f -> RedView (f $ s)
  typ  : forall {t T} -> RedView (t :: T)
  beta : forall {t S T s} -> RedView ((lam t :: pi S T) $ s)
  upsi : forall {t T}     -> RedView [ t :: T ]

redView : forall {n d}(t : Tm n d) -> RedView t
redView star = star
redView (pi S T) = pi
redView (lam t) = lam
redView [ var x ] = emb <>
redView [ e $ e₁ ] = emb <>
redView [ t :: T ] = upsi
redView (var i) = var
redView (var _ $ s) = app <>
redView ((_ $ _) $ s) = app <>
redView ((star :: T) $ s) = app <>
redView ((pi _ _ :: T) $ s) = app <>
redView ((lam _ :: star) $ s) = app <>
redView ((lam t :: pi S T) $ s) = beta
redView ((lam _ :: lam _) $ s) = app <>
redView ((lam _ :: [ _ ]) $ s) = app <>
redView (([ _ ] :: T) $ s) = app <>
redView (t :: T) = typ

dev : forall {d n} -> Tm n d -> Tm n d
dev t with redView t
dev star | star = star
dev (pi S T) | pi = pi (dev S) (dev T)
dev (lam t) | lam = lam (dev t)
dev [ e ] | emb x = [ dev e ]
dev (var i) | var = var i
dev (f $ s) | app x = dev f $ dev s
dev (t :: T) | typ = dev t :: dev T
dev ((lam t :: pi S T) $ s) | beta = Sb.act (si -, (dev s :: dev S)) (dev t :: dev T)
dev [ t :: T ] | upsi = dev t

dev1 : forall {d n}(t : Tm n d) -> t ~>> dev t
dev1 t with redView t
dev1 star | star = star
dev1 (pi S T) | pi = pi (dev1 S) (dev1 T)
dev1 (lam t) | lam = lam (dev1 t)
dev1 [ e ] | emb x = [ dev1 e ]
dev1 (var i) | var = var i
dev1 (f $ s) | app x = dev1 f $ dev1 s
dev1 (t :: T) | typ = dev1 t :: dev1 T
dev1 ((lam t :: pi S T) $ s) | beta = beta (dev1 t) (dev1 S) (dev1 T) (dev1 s)
dev1 [ t :: T ] | upsi = upsi (dev1 t)

dev2 : forall {d n}(t t' : Tm n d) -> t ~>> t' -> t' ~>> dev t
dev2 t t' r with redView t
dev2 .star .star star | star = star
dev2 .(pi _ _) .(pi _ _) (pi r r') | pi = pi (dev2 _ _ r) (dev2 _ _ r')
dev2 .(lam _) .(lam _) (lam r) | lam = lam (dev2 _ _ r)
dev2 .([ _ ]) .([ _ ]) [ r ] | emb x = [ dev2 _ _ r ]
dev2 .([ _ :: _ ]) t' (upsi r) | emb ()
dev2 .(var i) .(var i) (var i) | var = var i
dev2 .(_ $ _) .(_ $ _) (r $ r') | app x = dev2 _ _ r $ dev2 _ _ r'
dev2 .((lam _ :: pi _ _) $ _) ._ (beta _ _ _ _ ) | app ()
dev2 .(_ :: _) .(_ :: _) (r :: r') | typ = dev2 _ _ r :: dev2 _ _ r'
dev2 .((lam _ :: pi _ _) $ _) .((lam _ :: pi _ _) $ _) ((lam rt :: pi rS rT) $ rs) | beta
  = beta (dev2 _ _ rt) (dev2 _ _ rS) (dev2 _ _ rT) (dev2 _ _ rs)
dev2 .((lam _ :: pi _ _) $ _) ._ (beta rt rS rT rs) | beta
  = parStab (parzRefl si , (dev2 _ _ rs :: dev2 _ _ rS)) (dev2 _ _ rt :: dev2 _ _ rT)
dev2 .([ _ :: _ ]) .([ _ :: _ ]) [ r :: r' ] | upsi = upsi (dev2 _ _ r)
dev2 .([ _ :: _ ]) t' (upsi r) | upsi = dev2 _ _ r
