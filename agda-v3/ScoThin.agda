module ScoThin where

id : forall {l}{X : Set l} -> X -> X
id x = x

_-_ : forall {j k l}{A : Set j}{B : A -> Set k}{C : (a : A)(b : B a) -> Set l}
         (f : {a : A}(b : B a) -> C a b)
         (g : (a : A) -> B a)
         (a : A) -> C a (g a)
(f - g) a = f (g a)

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

sym : forall {l}{X : Set l}{x y : X} -> x == y -> y == x
sym refl = refl

data Bwd (K : Set) : Set where
  []   : Bwd K
  _-,_ : Bwd K -> K -> Bwd K

data _<=_ {K : Set} : Bwd K -> Bwd K -> Set where
  []   : [] <= []
  _-,_ : forall {ga de}(th : ga <= de)(k : K) -> (ga -, k) <= (de -, k)
  _-^_ : forall {ga de}(th : ga <= de)(j : K) -> ga <= (de -, j)

id<= : forall {K}(ga : Bwd K) -> ga <= ga
id<= []        = []
id<= (ga -, k) = id<= ga -, k

_=<=_ : forall {K}{ga0 ga1 ga2 : Bwd K} -> ga0 <= ga1 -> ga1 <= ga2 -> ga0 <= ga2
th         =<= (ph -^ j) = (th =<= ph) -^ j
(th -, .k) =<= (ph -, k) = (th =<= ph) -, k
(th -^ .k) =<= (ph -, k) = (th =<= ph) -^ k
[]         =<= []        = []

op : forall {K}{ga de : Bwd K} -> ga <= de -> Bwd K
op []        = []
op (th -, k) = op th
op (th -^ j) = op th -, j

co : forall {K}{ga de : Bwd K}(th : ga <= de) -> op th <= de
co []        = []
co (th -, k) = co th -^ k
co (th -^ j) = co th -, j

in<= : forall {K}(ga : Bwd K) -> [] <= ga
in<= []        = []
in<= (ga -, k) = in<= ga -^ k

coin<= : forall {K}{ga : Bwd K}(th : [] <= ga) -> op th == ga
coin<= [] = refl
coin<= (th -^ j) rewrite coin<= th = refl

_<-_ : forall {K} -> K -> Bwd K -> Set
k <- ga = ([] -, k) <= ga

peel : forall {X}{ga de : Bwd X}{k} -> (ga -, k) <= de -> ga <= de
peel (th -, k) = th -^ k
peel (th -^ j) = peel th -^ j

bad : forall {X}{de : Bwd X}{k} -> (de -, k) <= de -> forall {X : Set} -> X
bad (th -, k) = bad th
bad (th -^ j) = bad (peel th)

antisym : forall {X}{ga de : Bwd X} -> ga <= de -> de <= ga -> ga == de
antisym [] [] = refl
antisym (th -, k) (ph -, .k) with antisym th ph
antisym (th -, k) (ph -, .k) | refl = refl
antisym (th -, k) (ph -^ .k) with antisym th (peel ph)
antisym (th -, k) (ph -^ .k) | refl = refl
antisym (th -^ j) (ph -, .j) with antisym (peel th) ph
antisym (th -^ j) (ph -, .j) | refl = refl
antisym (th -^ j) (ph -^ j₁) with antisym (peel th) (peel ph)
antisym (th -^ j) (ph -^ j₁) | refl = bad ph

data Initial {K}{ga : Bwd K} : [] <= ga -> Set where
  init : Initial (in<= ga)

initial : forall {K}{ga : Bwd K}(x : [] <= ga) -> Initial x
initial [] = init
initial (x -^ j) with initial x
initial (.(in<= _) -^ j) | init = init

data Identity {K}{ga : Bwd K} : ga <= ga -> Set where
  iden : Identity(id<= ga)
identity : forall {K}{ga : Bwd K}(x : ga <= ga) -> Identity x
identity [] = iden
identity (x -, k) with identity x
identity (.(id<= _) -, k) | iden = iden
identity (x -^ j) = bad x

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
infixr 4 _,_
data Two : Set where tt ff : Two
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
_+_ : Set -> Set -> Set
S + T = Sg Two \ { tt -> S ; ff -> T }

in<=inQ : forall {X}{ga de : Bwd X}(th : ga <= de) ->
          ((in<= ga) =<= th) == in<= de
in<=inQ [] = refl
in<=inQ (th -, k) rewrite in<=inQ th = refl
in<=inQ (th -^ j) rewrite in<=inQ th = refl

id<=Q : forall {X}{ga de : Bwd X}(th : ga <= de) ->
          ((id<= ga) =<= th) == th
id<=Q [] = refl
id<=Q (th -, k) rewrite id<=Q th = refl
id<=Q (th -^ j) rewrite id<=Q th = refl

Qid<= : forall {X}{ga de : Bwd X}(th : ga <= de) ->
          (th =<= (id<= de)) == th
Qid<= [] = refl
Qid<= (th -, k) rewrite Qid<= th = refl
Qid<= (th -^ j) rewrite Qid<= th = refl

=<=<=Q : forall {X}{ga0 ga1 ga2 ga3 : Bwd X}
         (th01 : ga0 <= ga1)(th12 : ga1 <= ga2)(th23 : ga2 <= ga3) ->
         ((th01 =<= th12) =<= th23) == (th01 =<= (th12 =<= th23)) 
=<=<=Q th01 th12 (th23 -^ j) rewrite =<=<=Q th01 th12 th23 = refl
=<=<=Q th01 (th12 -^ .k) (th23 -, k) rewrite =<=<=Q th01 th12 th23 = refl
=<=<=Q (th01 -^ .k) (th12 -, .k) (th23 -, k) rewrite =<=<=Q th01 th12 th23 = refl
=<=<=Q (th01 -, .k) (th12 -, .k) (th23 -, k) rewrite =<=<=Q th01 th12 th23 = refl
=<=<=Q [] [] [] = refl

peelQ : forall {X}{ga de ze}{k : X}(th : ga <= de)(ph : (de -, k) <= ze) ->
         (th =<= peel ph) == ((th -^ k) =<= ph)
peelQ th (ph -, k) = refl
peelQ th (ph -^ j) rewrite peelQ th ph = refl

prod : forall {X}{ga0 ga1 de : Bwd X} -> ga0 <= de -> ga1 <= de -> Bwd X
prod [] [] = []
prod (th0 -, k) (th1 -, .k) = prod th0 th1 -, k
prod (th0 -, k) (th1 -^ .k) = prod th0 th1
prod (th0 -^ j) (th1 -, .j) = prod th0 th1
prod (th0 -^ j) (th1 -^ .j) = prod th0 th1

prod<= : forall {X}{ga0 ga1 de : Bwd X}(th0 : ga0 <= de)(th1 : ga1 <= de) ->
         (prod th0 th1 <= ga0) * (prod th0 th1 <= ga1)
prod<= [] [] = [] , []
prod<= (th0 -, k) (th1 -, .k) with prod<= th0 th1
... | ph0 , ph1 = (ph0 -, k) , (ph1 -, k)
prod<= (th0 -, k) (th1 -^ .k) with prod<= th0 th1
... | ph0 , ph1 = (ph0 -^ k) , ph1
prod<= (th0 -^ j) (th1 -, .j) with prod<= th0 th1
... | ph0 , ph1 = ph0 , (ph1 -^ j)
prod<= (th0 -^ j) (th1 -^ .j) with prod<= th0 th1
... | ph0 , ph1 = ph0 , ph1

-- universal property?

data Complement {X} : forall {ga0 ga1 de : Bwd X}
                      (th0 : ga0 <= de)(th1 : ga1 <= de) -> Set
 where
  [] : Complement [] []
  _-,_ : forall {ga0 ga1 de}{th : ga0 <= de}{ph : ga1 <= de} ->
        Complement th ph -> forall k -> Complement (th -, k) (ph -^ k)
  _-^_ : forall {ga0 ga1 de}{th : ga0 <= de}{ph : ga1 <= de} ->
        Complement th ph -> forall k -> Complement (th -^ k) (ph -, k)

complement : forall {X}{ga0 de : Bwd X}(th : ga0 <= de) ->
             Complement th (co th)
complement [] = []
complement (th -, k) = complement th -, k
complement (th -^ j) = complement th -^ j

selComp : forall {X}{ga0 ga1 de ze : Bwd X}
             {th0 : ga0 <= ze}{th1 : ga1 <= ze}(ph : de <= ze) ->
             Complement th0 th1 ->
             Sg _ \ ga0' -> Sg _ \ ga1' ->
             Sg (ga0' <= de) \ ph0 -> Sg (ga1' <= de) \ ph1 ->
             Complement ph0 ph1 * ((ga0' <= ga0) * (ga1' <= ga1))
selComp [] [] = [] , [] , [] , [] , [] , [] , []
selComp (ph -, k) (c -, .k) with selComp ph c
... | ga0' , ga1' , ph0 , ph1 , c' , ps0 , ps1
    = (ga0' -, k) , ga1' , (ph0 -, k) , (ph1 -^ k) , (c' -, k) , (ps0 -, k) , ps1
selComp (ph -, k) (c -^ .k) with selComp ph c
... | ga0' , ga1' , ph0 , ph1 , c' , ps0 , ps1
    = ga0' , (ga1' -, k) , (ph0 -^ k) , (ph1 -, k) , (c' -^ k) , ps0 , (ps1 -, k)
selComp (ph -^ j) (c -, .j) with selComp ph c
... | ga0' , ga1' , ph0 , ph1 , c' , ps0 , ps1
    = ga0' , ga1' , ph0 , ph1 , c' , (ps0 -^ j) , ps1
selComp (ph -^ j) (c -^ .j) with selComp ph c
... | ga0' , ga1' , ph0 , ph1 , c' , ps0 , ps1
    = ga0' , ga1' , ph0 , ph1 , c' , ps0 , (ps1 -^ j)

data Cover {X}{ga0 ga1 de : Bwd X}(th0 : ga0 <= de)(th1 : ga1 <= de){k} :
    (k <- de) -> Set where
  inl : (th : k <- ga0) -> Cover th0 th1 (th =<= th0)
  inr : (th : k <- ga1) -> Cover th0 th1 (th =<= th1)

cover : forall {X}{ga0 ga1 de : Bwd X}(th0 : ga0 <= de)(th1 : ga1 <= de) ->
        Complement th0 th1 -> forall {k}(x : k <- de) -> Cover th0 th1 x
cover .[] .[] [] ()
cover {ga0 = ga0 -, .k} (th -, .k) .(_ -^ k) (cmpl -, k) (x -, .k) with initial x
cover {ga0 = ga0 -, .k} (th -, .k) .(_ -^ k) (cmpl -, k) (.(in<= _) -, .k) | init
  rewrite sym (in<=inQ th) = inl (in<= ga0 -, k)
cover (th -, .k) (ph -^ .k) (cmpl -, k) (x -^ .k) with cover _ _ cmpl x
cover (th -, .k) (ph -^ .k) (cmpl -, k) (.(y =<= th) -^ .k) | inl y = inl (y -^ k)
cover (th -, .k) (ph -^ .k) (cmpl -, k) (.(z =<= ph) -^ .k) | inr z = inr z
cover {ga1 = ga1 -, .k} (th -^ .k) (ph -, .k) (cmpl -^ k) (x -, .k) with initial x
cover {ga1 = ga1 -, .k} (th -^ .k) (ph -, .k) (cmpl -^ k) (.(in<= _) -, .k) | init
  rewrite sym (in<=inQ ph) = inr (in<= ga1 -, k)
cover (th -^ .k) (ph -, .k) (cmpl -^ k) (x -^ .k) with cover _ _ cmpl x
cover (th -^ .k) (ph -, .k) (cmpl -^ k) (.(y =<= th) -^ .k) | inl y = inl y
cover (th -^ .k) (ph -, .k) (cmpl -^ k) (.(z =<= ph) -^ .k) | inr z = inr (z -^ k)

_+B_ : forall {X} -> Bwd X -> Bwd X -> Bwd X
kz +B [] = kz
kz +B (jz -, j) = (kz +B jz) -, j

allLeft : forall {X}(kz : Bwd X) -> Complement (id<= kz) (in<= kz)
allLeft [] = []
allLeft (kz -, k) = allLeft kz -, k

share : forall {X}(kz jz : Bwd X) ->
        Sg (kz <= (kz +B jz)) \ th ->
        Sg (jz <= (kz +B jz)) \ ph ->
        Complement th ph
share kz [] = id<= _ , in<= _ , allLeft kz
share kz (jz -, x) with share kz jz
share kz (jz -, x) | th , ph , c = (th -^ x) , (ph -, x) , (c -^ x)

_+Th_ : forall {X}{ga ga' : Bwd X}(th : ga <= ga') de -> (ga +B de) <= (ga' +B de)
th +Th [] = th
th +Th (de -, k) = (th +Th de) -, k

id+ThQ : forall {X}(ga de : Bwd X) -> (id<= ga +Th de) == id<= (ga +B de)
id+ThQ ga [] = refl
id+ThQ ga (de -, k) rewrite id+ThQ ga de = refl

_+^_ : forall {X}{ga ga' : Bwd X}(th : ga <= ga') de -> ga <= (ga' +B de)
th +^ [] = th
th +^ (de -, k) = (th +^ de) -^ k

in+^Q : forall {X}(ga de : Bwd X) -> (in<= ga +^ de) == in<= (ga +B de)
in+^Q ga [] = refl
in+^Q ga (de -, k) rewrite in+^Q ga de = refl

moreLeft : forall {X}{ga0 ga1 de : Bwd X}
             {th0 : ga0 <= de}{th1 : ga1 <= de}
             (c : Complement th0 th1) ze -> Complement (th0 +Th ze) (th1 +^ ze)
moreLeft c [] = c
moreLeft c (ze -, k) = moreLeft c ze -, k

data JM {l}{X : Set l}(x : X) : {Y : Set l} -> Y -> Set l where
  refl : JM x x
jmQ : forall {l}{X : Set l}{x y : X} -> JM x y -> x == y
jmQ refl = refl

moreAllLeftQ : forall {X} (ga de : Bwd X) ->
               JM (moreLeft (allLeft ga) de) (allLeft (ga +B de))
moreAllLeftQ ga [] = refl
moreAllLeftQ ga (de -, x) with moreLeft (allLeft ga) de | moreAllLeftQ ga de
... | c | j rewrite id+ThQ ga de | in+^Q ga de | jmQ j = refl
