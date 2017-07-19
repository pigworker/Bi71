module ScoThin where

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
open Sg
infixr 4 _,_

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

data Complement {X} : forall {ga0 ga1 de : Bwd X}
                      (ga0 : ga0 <= de)(ga1 : ga1 <= de) -> Set
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

