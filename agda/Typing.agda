module Typing where

open import Basics
open import OPE
open import Tm
open import Env
open import Subst
open import Par

data Cx : Nat -> Set where
  [] : Cx ze
  _-,_ : forall {n} -> Cx n -> Tm n chk -> Cx (su n)

cxTy : forall {n} -> Cx n -> Fin n -> Tm n chk
cxTy (Ga -, S) ze     = Th.act (o' oi) S
cxTy (Ga -, _) (su i) = Th.act (o' oi) (cxTy Ga i)

data CHK {n}(Ga : Cx n) : Tm n chk -> Tm n chk -> Set
data SYN {n}(Ga : Cx n) : Tm n syn -> Tm n chk -> Set

data CHK {n} Ga where

  pre  : forall {T T' t} ->
         T ~>> T' -> CHK Ga T' t ->
         CHK Ga T t

  star : CHK Ga star star

  pi   : forall {S T} ->
         CHK Ga star S -> CHK (Ga -, S) star T ->
         CHK Ga star (pi S T)

  lam  : forall {S T t} ->
         CHK (Ga -, S) T t ->
         CHK Ga (pi S T) (lam t)

  [_]  : forall {e S T} ->
         SYN Ga e S -> S == T ->
         CHK Ga T [ e ]

data SYN {n} Ga where

  post : forall {e S S'} ->
         SYN Ga e S -> S ~>> S' ->
         SYN Ga e S'

  var  : forall i ->
         SYN Ga (var i) (cxTy Ga i)

  _$_  : forall {f s S T} ->
         SYN Ga f (pi S T) -> CHK Ga S s ->
         SYN Ga (f $ s) (Sb.act (si -, (s :: S)) T)

  _:~:_ : forall {t T} ->
         CHK Ga star T -> CHK Ga T t ->
         SYN Ga (t :: T) T

ThinC : forall {n m} -> n <= m -> Cx n -> Cx m -> Set
ThinC oz [] [] = One
ThinC (os th) (Ga -, S) (De -, S') = ThinC th Ga De * (Th.act th S == S')
ThinC (o' th) Ga (De -, _) = ThinC th Ga De

idThinC : forall {n}(Ga : Cx n) -> ThinC oi Ga Ga
idThinC [] = <>
idThinC (Ga -, S) = idThinC Ga , ActId.actId THINID S

cxTyThin : forall {n m}(th : n <= m)(Ga : Cx n)(De : Cx m) ->
           ThinC th Ga De -> (i : Fin n) ->
           Th.act th (cxTy Ga i) == cxTy De (thin th i)
cxTyThin oz Ga De thGaDe ()
cxTyThin (os th) (Ga -, S) (De -, S') (thGaDe , thSS') ze
  rewrite sym thSS'
        | ActCo.actCo THINTHINTHIN (o' oi) th S
        | ActCo.actCo THINTHINTHIN (os th) (o' oi) S
        | oi-<-Q th
        | th -<-oiQ
        = refl
cxTyThin (os th) (Ga -, S) (De -, S') (thGaDe , thSS') (su i)
  with cxTyThin th Ga De thGaDe i
... | q rewrite sym q
        | ActCo.actCo THINTHINTHIN (o' oi) th (cxTy Ga i)
        | ActCo.actCo THINTHINTHIN (os th) (o' oi) (cxTy Ga i)
        | oi-<-Q th
        | th -<-oiQ
        = refl
cxTyThin (o' th) Ga (De -, _) thGaDe i with cxTyThin th Ga De thGaDe i
... | q rewrite sym q
              | ActCo.actCo THINTHINTHIN (o' oi) th (cxTy Ga i)
              | oi-<-Q th
              = refl

thinCHK : forall {n m}(th : n <= m)
          {Ga : Cx n}{De : Cx m} -> ThinC th Ga De ->
          forall {T t} -> CHK Ga T t ->
             CHK De (Th.act th T) (Th.act th t)
thinSYN : forall {n m}(th : n <= m)
          {Ga : Cx n}{De : Cx m} -> ThinC th Ga De ->
          forall {e S} -> SYN Ga e S ->
             SYN De (Th.act th e) (Th.act th S)
thinCHK th thC (pre TT' Tt) = pre (parThin th TT') (thinCHK th thC Tt)
thinCHK th thC star = star
thinCHK th thC (pi S T) =
  pi (thinCHK th thC S) (thinCHK (os th) (thC , refl) T)
thinCHK th thC (lam Tt) = lam (thinCHK (os th) (thC , refl) Tt)
thinCHK th thC ([ eS ] refl) = [ thinSYN th thC eS ] refl
thinSYN th thC (post eS SS') = post (thinSYN th thC eS) (parThin th SS')
thinSYN th thC (var i) rewrite cxTyThin th _ _ thC i = var (thin th i)
thinSYN th thC (_$_ {f}{s}{S}{T} fST Ss)
  with the (SYN _ _ _) (thinSYN th thC fST $ thinCHK th thC Ss)
... | h
    rewrite ActCo.actCo SUBSTTHINSUBST (si -, Th.act th (s :: S)) (os th) T
          | ActCo.actCo THINSUBSTSUBST th (si -, (s :: S)) T
          | thin/idQ th
    = h
thinSYN th thC (T :~: t) = thinCHK th thC T :~: thinCHK th thC t

CxMor : {n m : Nat} -> Cx m -> Cx n -> Env (Tm m syn) n -> Set
CxMor De [] [] = One
CxMor De (Ga -, S) (ez -, e) = CxMor De Ga ez * SYN De e (Sb.act ez S)

thinCxMor : {n m l : Nat}(th : m <= l) ->
            {De : Cx m}{Th : Cx l} -> ThinC th De Th ->
            {Ga : Cx n}(ez : Env (Tm m syn) n) ->
            CxMor De Ga ez ->
            CxMor Th Ga (env (Th.act th) ez)
thinCxMor th thC {[]} [] <> = <>
thinCxMor th thC {Ga -, S} (ez -, e) (ezok , eS)
  with thinSYN th thC eS
... | eS'
  rewrite ActCo.actCo THINSUBSTSUBST th ez S
  = (thinCxMor th thC {Ga} ez ezok) , eS'

CxMorW : {n m : Nat}{De : Cx m}{Ga : Cx n}(ez : Env (Tm m syn) n) ->
          CxMor De Ga ez ->
          (S : Tm n chk) ->
          CxMor (De -, Sb.act ez S) (Ga -, S) (Sb.actW ez)
CxMorW {De = De} ez ezok S
  with the (SYN (De -, Sb.act ez S) (var ze) (Th.act (o' oi) (Sb.act ez S)))
           (var ze)
... | h
  rewrite ActCo.actCo THINSUBSTSUBST (o' oi) ez S
  = thinCxMor (o' oi) (idThinC De) ez ezok , h

yelp : forall {n m}(ez : Env (Tm m syn) n) s S ->
       env (Sb.act (si -, Sb.act ez (s :: S))) (env (Th.act (o' oi)) ez)
       == ez
yelp {n}{m} ez s S
  rewrite envenvQ (Sb.act (si -, Sb.act ez (s :: S))) (Th.act (o' oi)) ez
  = envIdQ _ zelp ez
  where
    zelp : (x : Tm m syn) ->
            Sb.act (si -, Sb.act ez (s :: S)) (Th.act (o' oi) x) == x
    zelp x
      rewrite ActCo.actCo SUBSTTHINSUBST (si -, Sb.act ez (s :: S)) (o' oi) x
            | si{m} /oiQ
      = ActId.actId SUBSTID x

substVar : forall {n m}{Ga : Cx n}{De : Cx m}
           (ez : Env (Tm m syn) n) -> CxMor De Ga ez ->
           (i : Fin n) ->
           SYN De (ez ! i) (Sb.act ez (cxTy Ga i))
substVar {Ga = Ga -, S} (ez -, e) (ezok , eS) ze
  rewrite ActCo.actCo SUBSTTHINSUBST (ez -, e) (o' oi) S
        | ez /oiQ
  = eS
substVar {Ga = Ga -, S} (ez -, e) (ezok , _) (su i) with substVar ez ezok i
... | eS 
  rewrite ActCo.actCo SUBSTTHINSUBST (ez -, e) (o' oi) (cxTy Ga i)
        | ez /oiQ
  = eS

substCHK : forall {n m}{Ga : Cx n}{De : Cx m}
           (ez : Env (Tm m syn) n) -> CxMor De Ga ez ->
           forall {T t} ->
           CHK Ga T t -> CHK De (Sb.act ez T) (Sb.act ez t)
substSYN : forall {n m}{Ga : Cx n}{De : Cx m}
           (ez : Env (Tm m syn) n) -> CxMor De Ga ez ->
           forall {e S} ->
           SYN Ga e S -> SYN De (Sb.act ez e) (Sb.act ez S)

substCHK ez ezok (pre TT' Tt) =
  pre (parStab (parzRefl ez) TT') (substCHK ez ezok Tt)
substCHK ez ezok star = star
substCHK ez ezok (pi {S} *S *T) =
  pi (substCHK ez ezok *S) (substCHK (Sb.actW ez) (CxMorW ez ezok S) *T)
substCHK ez ezok (lam {S} Tt) =
  lam (substCHK (Sb.actW ez) (CxMorW ez ezok S) Tt)
substCHK ez ezok ([ eS ] refl) =
  [ substSYN ez ezok eS ] refl
substSYN ez ezok (post eS SS') =
  post (substSYN ez ezok eS) (parStab (parzRefl ez) SS')
substSYN ez ezok (var i) = substVar ez ezok i
substSYN ez ezok (_$_ {f}{s}{S}{T} fST Ss)
  with the (SYN _ _ _)
           (substSYN ez ezok fST $ substCHK ez ezok Ss)
... | h
  rewrite ActCo.actCo SUBSTSUBSTSUBST (si -, Sb.act ez (s :: S)) (Sb.actW ez) T
        | yelp ez s S
        | ActCo.actCo SUBSTSUBSTSUBST ez (si -, (s :: S)) T
        | subsiQ ez
  = h
substSYN ez ezok (*T :~: Tt) = substCHK ez ezok *T :~: substCHK ez ezok Tt
