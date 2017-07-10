module Lib.OPE {X} where

open import Lib.Comb
open import Lib.Eq
open import Lib.Bwd
open import Lib.Cat

data _<=_ : Bwd X -> Bwd X -> Set where
  oz : [] <= []
  os : forall {w xz yz} -> xz <= yz -> (xz -, w) <= (yz -, w)
  o' : forall {w xz yz} -> xz <= yz ->  xz       <= (yz -, w)

oi : forall {xz} -> xz <= xz
oi {[]}     = oz
oi {_ -, _} = os oi

on : forall {xz} -> [] <= xz
on {[]}     = oz
on {_ -, _} = o' on

_-<-_ : forall {xz yz zz} -> yz <= zz -> xz <= yz -> xz <= zz
oz    -<- oz    = oz
os th -<- os ph = os (th -<- ph)
os th -<- o' ph = o' (th -<- ph)
o' th -<- ph    = o' (th -<- ph)

OPECAT : Cat _<=_
OPECAT = record { idC = < oi ] ; _<<_ = \ f g -> < hom f -<- hom g ] }


oi-<-Q : forall {n m}(th : n <= m) -> (oi -<- th) == th
oi-<-Q oz = refl
oi-<-Q (os th) rewrite oi-<-Q th = refl
oi-<-Q (o' th) rewrite oi-<-Q th = refl

_-<-oiQ : forall {n m}(th : n <= m) -> (th -<- oi) == th
oz -<-oiQ = refl
os th -<-oiQ rewrite th -<-oiQ = refl
o' th -<-oiQ rewrite th -<-oiQ = refl

-<-<-<-Q : forall {q p n m}(th : n <= m)(ph : p <= n)(ps : q <= p) ->
        ((th -<- ph) -<- ps) == (th -<- (ph -<- ps))
-<-<-<-Q  oz      oz      oz     = refl
-<-<-<-Q (os th) (os ph) (os ps) = os $= -<-<-<-Q th ph ps
-<-<-<-Q (os th) (os ph) (o' ps) = o' $= -<-<-<-Q th ph ps
-<-<-<-Q (os th) (o' ph)     ps  = o' $= -<-<-<-Q th ph ps
-<-<-<-Q (o' th)     ph      ps  = o' $= -<-<-<-Q th ph ps

OPECATLAWS : CatLaws _==_ OPECAT
OPECATLAWS = record
  { id-co = \ h -> <_] $= oi-<-Q (hom h)
  ; co-id = \ h -> <_] $= ((hom h) -<-oiQ)
  ; assoc = \ f g h -> <_] $= -<-<-<-Q (hom f) (hom g) (hom h)
  } where


thin : forall {x xz yz} -> xz <= yz -> x <- xz -> x <- yz
thin  oz      ()
thin (o' th)     i  = su (thin th i)
thin (os th)  ze    = ze
thin (os th) (su i) = su (thin th i)

ThinVar : {x : X} -> Functor OPECAT (SET <Cat- (x <-_))
ThinVar {x} = record
  { objF = id
  ; homF = \ {< th ] -> < thin th ]}
  }

oiQ : forall {x}{xz}(i : x <- xz) -> thin oi i == i
oiQ ze = refl
oiQ (su i) rewrite oiQ i = refl

thinCo : forall {x}{n m l}(th : m <= l)(ph : n <= m) ->
           thin {x} (th -<- ph) =^= (thin th - thin ph)
thinCo oz oz ()
thinCo (os th) (os ph) ze = refl
thinCo (os th) (os ph) (su i) rewrite thinCo th ph i = refl
thinCo (os th) (o' ph) i rewrite thinCo th ph i = refl
thinCo (o' th) ph i rewrite thinCo th ph i = refl


ThinVarLaws : {x : X} ->
              FunctorLaws OPECAT (SET <Cat- _<-_ x)
                          _==_   (HQ _=^=_)
                          (ThinVar {x})
ThinVarLaws {x} = record
  { funId = \ { .(< oi ]) refl -> oiQ }
  ; funCo = \ { .(< th -<- ph ]) < th ] < ph ] refl -> thinCo th ph }
  }


