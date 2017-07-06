module Preservation where

open import Basics
open import OPE
open import Tm
open import Env
open import Subst
open import Par
open import Star
open import Dev
open import Typing

_~~>>*_ : forall {n m} -> Env (Tm m syn) n -> Env (Tm m syn) n -> Set
_~~>>*_ = Star _~~>>_

parsStab : forall {d n m}{sz tz : Env (Tm m syn) n}{s t : Tm n d} ->
           sz ~~>>* tz -> s ~>>* t -> Sb.act sz s ~>>* Sb.act tz t
parsStab {sz = sz} {.sz} [] [] = []
parsStab {sz = sz} {.sz} [] (r ,- rs)
  = parStab (parzRefl sz) r ,- parsStab [] rs
parsStab {sz = sz} {tz} {s = s} (rz ,- rzs) rs
  = parStab rz (parRefl s) ,- parsStab rzs rs

_!~>>*_ : forall {n} -> Cx n -> Cx n -> Set
[] !~>>* [] = One
(Ga -, S) !~>>* (De -, T) = (Ga !~>>* De) * (S ~>>* T)

pre* : forall {n}{Ga : Cx n}{T T' t} ->
         T ~>>* T' -> CHK Ga T' t ->
         CHK Ga T t
pre* [] Tt = Tt
pre* (rT ,- rTs) T't = pre rT (pre* rTs T't)

post* : forall {n}{Ga : Cx n}{e S S'} ->
        SYN Ga e S -> S ~>>* S' -> SYN Ga e S'
post* eS [] = eS
post* eS (r ,- rs) = post* (post eS r) rs

starInvRed : forall {n}{U : Tm n chk} -> star ~>>* U -> U == star
starInvRed [] = refl
starInvRed (star ,- rs) = starInvRed rs

annInv : forall {n}{Ga}{t T T' : Tm n chk} ->
         SYN Ga (t :: T) T' ->
         CHK Ga star T * CHK Ga T t * (T ~>>* T')
annInv (post tT r) with annInv tT
... | T , t , rs = T , t , (rs ++ (r ,- []))
annInv (T :~: t)   = T , t , []

piInvRed : forall {n}{S U : Tm n chk}{T : Tm (su n) chk} ->
  pi S T ~>>* U ->
  Sg (Tm n chk) \ S' -> Sg (Tm (su n) chk) \ T' ->
  (U == pi S' T') * (S ~>>* S') * (T ~>>* T')
piInvRed [] = _ , _ , refl , [] , []
piInvRed (pi S T ,- rs) with piInvRed rs
... | _ , _ , refl , SS' , TT' = _ , _ , refl , (S ,- SS') , (T ,- TT')

lamInv : forall {n}{Ga}{S : Tm n chk}{T t} ->
         CHK Ga (pi S T) (lam t) ->
         Sg (Tm n chk) \ S' -> Sg (Tm (su n) chk) \ T' ->
         (S ~>>* S') * (T ~>>* T') *
         CHK (Ga -, S') T' t
lamInv (pre (pi rS rT) d) with lamInv d
... | _ , _ , rsS , rsT , d' = _ , _ , (rS ,- rsS) , (rT ,- rsT) , d'
lamInv (lam d) = _ , _ , [] , [] , d

piInv : forall {n}{Ga}{S : Tm n chk}{T} ->
        CHK Ga star (pi S T) ->
        CHK Ga star S * CHK (Ga -, S) star T
piInv (pre star *piST) = piInv *piST
piInv (pi *S *T) = *S , *T

zeMor : forall {n}{Ga : Cx n}{s S S'} ->
        CHK Ga star S -> CHK Ga S s -> S ~>>* S' ->
        CxMor Ga (Ga -, S') (si -, (s :: S))
zeMor {n}{Ga}{s}{S}{S'} *S Ss SS'
  rewrite ActId.actId SUBSTID S'
        = idCxMor Ga , post* (*S :~: Ss) SS'

presCHK : forall {n}{Ga Ga' : Cx n}{T T' : Tm n chk}{t t' : Tm n chk} ->
  Ga !~>>* Ga' -> T ~>>* T' -> t ~>> t' ->
  CHK Ga T t -> CHK Ga' T' t'

presSYN : forall {n}{Ga Ga' : Cx n}{e e' : Tm n syn}{S : Tm n chk} ->
  Ga !~>>* Ga' -> e ~>> e' ->
  SYN Ga e S -> Sg (Tm n chk) \ S' -> (S ~>>* S') * SYN Ga' e' S'

presCxTy : forall {n}{Ga Ga' : Cx n} ->
  Ga !~>>* Ga' -> (i : Fin n) -> cxTy Ga i ~>>* cxTy Ga' i
presCxTy {Ga = Ga -, S} {Ga' -, S'} (rGa , SS') ze
  = starm (Th.act (o' oi)) (parThin (o' oi)) SS'
presCxTy {Ga = Ga -, S} {Ga' -, S'} (rGa , SS') (su i)
  = starm (Th.act (o' oi)) (parThin (o' oi)) (presCxTy rGa i)

presCHK rGa rT0 rt (pre rT1 Tt) with confluence rT0 (rT1 ,- [])
... | _ , rT2 , rT3 = pre* rT2 (presCHK rGa rT3 rt Tt)
presCHK rGa rT star star with starInvRed rT
presCHK rGa rT star star | refl = star
presCHK rGa rT (pi SS' TT') (pi S T) with starInvRed rT
presCHK rGa rT (pi SS' TT') (pi S T) | refl
  = pi (presCHK rGa [] SS' S) (presCHK (rGa , (SS' ,- [])) [] TT' T)
presCHK rGa rT (lam rt) (lam Tt) with piInvRed rT
presCHK rGa rT (lam rt) (lam Tt) | S , T , refl , SS' , TT'
  = lam (presCHK (rGa , SS') TT' rt Tt)
presCHK rGa rT [ re ] ([ e ] refl) with presSYN rGa re e
... | S' , SS' , e'S' with confluence rT SS'
... | Sw , T'Sw , S'Sw = pre* T'Sw ([ post* e'S' S'Sw ] refl)
presCHK {n} rGa rT (upsi rt) ([ e ] refl) = help rGa rT rt e where
  help : forall {t t' T U V : Tm n chk}{Ga Ga'} ->
           Ga !~>>* Ga' -> U ~>>* V -> t ~>> t' -> SYN Ga (t :: T) U ->
           CHK Ga' V t'
  help rGa UV tt' (post tTS SU) = help rGa (SU ,- UV) tt' tTS
  help rGa UV tt' (T :~: t) = presCHK rGa UV tt' t 

presSYN rGa re (post eS S0S') with presSYN rGa re eS
... | _ , S0S1 , eS1 with confluence S0S1 (S0S' ,- [])
... | _ , S1Sw , S'Sw = _ , S'Sw , post* eS1 S1Sw
presSYN rGa (var .i) (var i) = _ , presCxTy rGa i , var i
presSYN rGa (rf $ rs) (fST $ Ss) with presSYN rGa rf fST
... | _ , STS'T' , f'S'T' with piInvRed STS'T'
presSYN rGa (_$_ {f}{f'}{s}{s'} rf rs) (_$_ {.f}{.s}{S}{T} fST Ss)
  | .(pi S' T') , STS'T' , f'S'T'
  | (S' , T' , refl , SS' , TT')
  with presCHK rGa SS' rs Ss
... | S's'
    = let  arg : (s :: S) ~>>* (s' :: S')
           arg = (rs :: parRefl S) ,- starm (_::_ s') (_::_ (parRefl s')) SS'
      in   _ , parsStab (starm (si -,_) (parzRefl si ,_) arg) TT'
             , (f'S'T' $ S's')
presSYN {Ga = Ga} rGa (beta {t}{t'}{S}{S'}{T}{T'}{s}{s'} tt' SS' TT' ss')
  (_$_ {_}{_}{Si}{Ti} fST Sis)
  with annInv fST
... | *piST , piSTlamt , piSTpiSiTi
  with piInv *piST | lamInv piSTlamt | piInvRed piSTpiSiTi
... | *S , *T | Sc , Tc , SSc , TTc , Tct | .Si , .Ti , refl , SSi , TTi
  with consensus S (S' ,- Si ,- Sc ,- []) ((SS' ,- []) , SSi , SSc , <>)
     | consensus T (T' ,- Ti ,- Tc ,- []) ((TT' ,- []) , TTi , TTc , <>)
...  | Sw , SSw , S'Sw , SiSw , ScSw , <>
     | Tw , TTw , T'Tw , TiTw , TcTw , <>
  with presCHK rGa [] SS' *S          | presCHK rGa SiSw ss' Sis
     | presCHK (rGa , SSw) [] TT' *T  | presCHK (rGa , ScSw) TcTw tt' Tct
...  | hS | hs | hT | ht
    = let yada : forall {Sa} -> Sa ~>>* Sw ->
                   (si -, (s' :: Sa)) ~~>>* (si -, (s' :: Sw))
          yada SaSw = starm (si -,_) (parzRefl si ,_)
                        (starm (s' ::_) (parRefl s' ::_) SaSw)
          zada = zeMor hS (pre* S'Sw hs) S'Sw
      in  Sb.act (si -, (s' :: Sw)) Tw
          , parsStab ((parzRefl si , (ss' :: parRefl Si)) ,- yada SiSw)
            TiTw
          , post* (substCHK (si -, (s' :: S')) zada hT
                   :~:
                   substCHK (si -, (s' :: S')) zada (pre* T'Tw ht))
              (parsStab (yada S'Sw) T'Tw)
presSYN rGa (rt :: rT) (T :~: t) =
  _ , (rT ,- []) , (presCHK rGa [] rT T :~: presCHK rGa (rT ,- []) rt t)
