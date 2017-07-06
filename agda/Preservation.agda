module Preservation where

open import Basics
open import OPE
open import Star
open import Env
open import Tm
open import Subst
open import Par
open import Dev
open import Typing

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
