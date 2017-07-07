module Progress where

open import Basics
open import Star
open import Tm
open import RedNorm
open import Par
open import Typing

data Progressive {n} : Tm n chk -> Set where
  nm : (t : Nm n chk) -> Progressive (fog t)
  go : {t t' : Tm n chk} -> t ~> t' -> Progressive t

data Operative {n} : Tm n syn -> Set where
  ne   : (e : Nm n syn) -> Operative (fog e)
  _::_ : (t T : Nm n chk) -> Operative (fog t :: fog T)
  go   : {e e' : Tm n syn} -> e ~> e' -> Operative e

findPi : forall {n}{V S' T'}(U : Nm n chk) ->
         V ~>>* pi S' T' -> V == fog U ->
         Sg (Nm n chk) \ S -> Sg (Nm (su n) chk) \ T ->
         (U == pi S T) * (S' == fog S) * (T' == fog T)
findPi U VpiST q with starb parReds VpiST
findPi star VpiST () | []
findPi (pi S T) VpiST refl | [] = S , T , refl , refl , refl
findPi (lam U) VpiST () | []
findPi [ U ] VpiST () | []
findPi U VpiST refl | r ,- rs = naughty (nmNoRed U r refl)

progCHK : forall {n Ga}{T t : Tm n chk} ->
          CHK Ga T t -> Progressive t
operSYN : forall {n Ga}{e : Tm n syn}{S} ->
          SYN Ga e S -> Operative e
progCHK (pre TT' T't) = progCHK T't
progCHK star = nm star
progCHK (pi *S *T) with progCHK *S
progCHK (pi *S *T) | nm S with progCHK *T
progCHK (pi *S *T) | nm S | (nm T) = nm (pi S T)
progCHK (pi *S *T) | nm S | (go TT') = go (piR _ TT')
progCHK (pi *S *T) | go SS' = go (piL SS' _)
progCHK (lam Tt) with progCHK Tt
progCHK (lam Tt) | nm t = nm (lam t)
progCHK (lam Tt) | go tt' = go (lam tt')
progCHK ([ eS ] refl) with operSYN eS
progCHK ([ eS ] refl) | ne e   = nm [ e ]
progCHK ([ eS ] refl) | t :: T = go upsi
progCHK ([ eS ] refl) | go ee' = go [ ee' ]
operSYN (post eS SS') = operSYN eS
operSYN (var i)       = ne (var i)
operSYN (fpiST $ Ss) with operSYN fpiST
operSYN (fpiST $ Ss) | ne e with progCHK Ss
operSYN (fpiST $ Ss) | ne e | nm s = ne (e $ s)
operSYN (fpiST $ Ss) | ne e | go s = go (_ $R s)
operSYN (fpiST $ Ss) | t :: T with progCHK Ss
operSYN {n}{Ga} (fpiST $ Ss) | t :: U | nm s with annInv fpiST
... | *F , Ff , FpiST with findPi U FpiST refl
operSYN (fpiST $ Ss) | star :: .(pi S T) | (nm s) | (*F , Ff , FpiST)
  | (S , T , refl , refl , refl) = naughty (killPi* Ff)
operSYN (fpiST $ Ss) | pi t t₁ :: .(pi S T) | (nm s) | (*F , Ff , FpiST)
  | (S , T , refl , refl , refl) = naughty (killPiPi Ff)
operSYN (fpiST $ Ss) | lam t :: .(pi S T) | (nm s) | (*F , Ff , FpiST)
  | (S , T , refl , refl , refl)
  = go beta
operSYN (fpiST $ Ss) | [ e ] :: .(pi S T) | (nm s) | (*F , Ff , FpiST)
  | (S , T , refl , refl , refl)
  = ne ([ e ]::Pi S > T :$ s)
operSYN (fpiST $ Ss) | t :: T | go s = go (_ $R s)
operSYN (fpiST $ Ss) | go ff' = go (ff' $L _)
operSYN (*T :~: Tt) with progCHK Tt
operSYN (*T :~: Tt) | nm t with progCHK *T
operSYN (*T :~: Tt) | nm t | nm T    = t :: T
operSYN (*T :~: Tt) | nm t | go TT'  = go (_ ::R TT')
operSYN (*T :~: Tt) | go tt'         = go (tt' ::L _)
