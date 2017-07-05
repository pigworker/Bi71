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

_~~>>*_ : forall {n} -> Cx n -> Cx n -> Set
[] ~~>>* [] = One
(Ga -, S) ~~>>* (De -, T) = (Ga ~~>>* De) * (S ~>>* T)

pre* : forall {n}{Ga : Cx n}{T T' t} ->
         T ~>>* T' -> CHK Ga T' t ->
         CHK Ga T t
pre* [] Tt = Tt
pre* (rT ,- rTs) T't = pre rT (pre* rTs T't)

post* : forall {n}{Ga : Cx n}{e S S'} ->
        SYN Ga e S -> S ~>>* S' -> SYN Ga e S'
post* eS [] = eS
post* eS (r ,- rs) = post* (post eS r) rs

starInv : forall {n}{U : Tm n chk} -> star ~>>* U -> U == star
starInv [] = refl
starInv (star ,- rs) = starInv rs

piInv : forall {n}{S U : Tm n chk}{T : Tm (su n) chk} ->
  pi S T ~>>* U ->
  Sg (Tm n chk) \ S' -> Sg (Tm (su n) chk) \ T' ->
  (U == pi S' T') * (S ~>>* S') * (T ~>>* T')
piInv [] = _ , _ , refl , [] , []
piInv (pi S T ,- rs) with piInv rs
... | _ , _ , refl , SS' , TT' = _ , _ , refl , (S ,- SS') , (T ,- TT')

presCHK : forall {n}{Ga Ga' : Cx n}{T T' : Tm n chk}{t t' : Tm n chk} ->
  Ga ~~>>* Ga' -> T ~>>* T' -> t ~>> t' ->
  CHK Ga T t -> CHK Ga' T' t'

presSYN : forall {n}{Ga Ga' : Cx n}{e e' : Tm n syn}{S : Tm n chk} ->
  Ga ~~>>* Ga' -> e ~>> e' ->
  SYN Ga e S -> Sg (Tm n chk) \ S' -> (S ~>>* S') * SYN Ga' e' S'

presCHK rGa rT0 rt (pre rT1 Tt) with confluence rT0 (rT1 ,- [])
... | _ , rT2 , rT3 = pre* rT2 (presCHK rGa rT3 rt Tt)
presCHK rGa rT star star with starInv rT
presCHK rGa rT star star | refl = star
presCHK rGa rT (pi SS' TT') (pi S T) with starInv rT
presCHK rGa rT (pi SS' TT') (pi S T) | refl
  = pi (presCHK rGa [] SS' S) (presCHK (rGa , (SS' ,- [])) [] TT' T)
presCHK rGa rT (lam rt) (lam Tt) with piInv rT
presCHK rGa rT (lam rt) (lam Tt) | S , T , refl , SS' , TT'
  = lam (presCHK (rGa , SS') TT' rt Tt)
presCHK rGa rT [ re ] ([ e ] refl) with presSYN rGa re e
... | S' , SS' , e'S' with confluence rT SS'
... | Sw , T'Sw , S'Sw = pre* T'Sw ([ post* e'S' S'Sw ] refl)
presCHK {n} rGa rT (upsi rt) ([ e ] refl) = help rGa rT rt e where
  help : forall {t t' T U V : Tm n chk}{Ga Ga'} ->
           Ga ~~>>* Ga' -> U ~>>* V -> t ~>> t' -> SYN Ga (t :: T) U ->
           CHK Ga' V t'
  help rGa UV tt' (post tTS SU) = help rGa (SU ,- UV) tt' tTS
  help rGa UV tt' (T :: t) = presCHK rGa UV tt' t 

presSYN rGa re eS = {!!}
