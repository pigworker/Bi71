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

  _::_ : forall {t T} ->
         CHK Ga star T -> CHK Ga T t ->
         SYN Ga (t :: T) T
