module OPE where

open import Basics

data _<=_ : Nat -> Nat -> Set where
  oz : ze <= ze
  os : forall {n m} -> n <= m -> su n <= su m
  o' : forall {n m} -> n <= m ->    n <= su m

oi : forall {n} -> n <= n
oi {ze} = oz
oi {su x} = os oi

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

thin : forall {n m} -> n <= m -> Fin n -> Fin m
thin oz ()
thin (o' th)  i = su (thin th i)
thin (os th) ze = ze
thin (os th) (su i) = su (thin th i)

oiQ : forall {n}(i : Fin n) -> thin oi i == i
oiQ ze = refl
oiQ (su i) rewrite oiQ i = refl

thinCo : forall {n m l}(th : m <= l)(ph : n <= m)(i : Fin n) ->
           thin th (thin ph i) == thin (th -<- ph) i
thinCo oz oz ()
thinCo (os th) (os ph) ze = refl
thinCo (os th) (os ph) (su i) rewrite thinCo th ph i = refl
thinCo (os th) (o' ph) i rewrite thinCo th ph i = refl
thinCo (o' th) ph i rewrite thinCo th ph i = refl
