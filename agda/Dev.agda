module Dev where

open import Basics
open import OPE
open import Tm
open import Env
open import Subst
open import Par

NoRadFun : forall {n} -> Tm n syn -> Set
NoRadFun (lam _ :: pi _ _) = Zero
NoRadFun _ = One

NoRad : forall {n} -> Tm n syn -> Set
NoRad (_ :: _) = Zero
NoRad _ = One

data RedView {n} : forall {d} -> Tm n d -> Set where
  star : RedView star
  pi   : forall {S T} -> RedView (pi S T)
  lam  : forall {t} -> RedView (lam t)
  emb  : forall {e} -> NoRad e -> RedView [ e ]
  var  : forall {i} -> RedView (var i)
  app  : forall {f s} -> NoRadFun f -> RedView (f $ s)
  typ  : forall {t T} -> RedView (t :: T)
  beta : forall {t S T s} -> RedView ((lam t :: pi S T) $ s)
  upsi : forall {t T}     -> RedView [ t :: T ]

redView : forall {n d}(t : Tm n d) -> RedView t
redView star = star
redView (pi S T) = pi
redView (lam t) = lam
redView [ var x ] = emb <>
redView [ e $ e₁ ] = emb <>
redView [ t :: T ] = upsi
redView (var i) = var
redView (var _ $ s) = app <>
redView ((_ $ _) $ s) = app <>
redView ((star :: T) $ s) = app <>
redView ((pi _ _ :: T) $ s) = app <>
redView ((lam _ :: star) $ s) = app <>
redView ((lam t :: pi S T) $ s) = beta
redView ((lam _ :: lam _) $ s) = app <>
redView ((lam _ :: [ _ ]) $ s) = app <>
redView (([ _ ] :: T) $ s) = app <>
redView (t :: T) = typ

dev : forall {d n} -> Tm n d -> Tm n d
dev t with redView t
dev star | star = star
dev (pi S T) | pi = pi (dev S) (dev T)
dev (lam t) | lam = lam (dev t)
dev [ e ] | emb x = [ dev e ]
dev (var i) | var = var i
dev (f $ s) | app x = dev f $ dev s
dev (t :: T) | typ = dev t :: dev T
dev ((lam t :: pi S T) $ s) | beta = Sb.act (si -, (dev s :: dev S)) (dev t :: dev T)
dev [ t :: T ] | upsi = dev t

dev1 : forall {d n}(t : Tm n d) -> t ~>> dev t
dev1 t with redView t
dev1 star | star = star
dev1 (pi S T) | pi = pi (dev1 S) (dev1 T)
dev1 (lam t) | lam = lam (dev1 t)
dev1 [ e ] | emb x = [ dev1 e ]
dev1 (var i) | var = var i
dev1 (f $ s) | app x = dev1 f $ dev1 s
dev1 (t :: T) | typ = dev1 t :: dev1 T
dev1 ((lam t :: pi S T) $ s) | beta = beta (dev1 t) (dev1 S) (dev1 T) (dev1 s)
dev1 [ t :: T ] | upsi = upsi (dev1 t)

dev2 : forall {d n}(t t' : Tm n d) -> t ~>> t' -> t' ~>> dev t
dev2 t t' r with redView t
dev2 .star .star star | star = star
dev2 .(pi _ _) .(pi _ _) (pi r r') | pi = pi (dev2 _ _ r) (dev2 _ _ r')
dev2 .(lam _) .(lam _) (lam r) | lam = lam (dev2 _ _ r)
dev2 .([ _ ]) .([ _ ]) [ r ] | emb x = [ dev2 _ _ r ]
dev2 .([ _ :: _ ]) t' (upsi r) | emb ()
dev2 .(var i) .(var i) (var i) | var = var i
dev2 .(_ $ _) .(_ $ _) (r $ r') | app x = dev2 _ _ r $ dev2 _ _ r'
dev2 .((lam _ :: pi _ _) $ _) ._ (beta _ _ _ _ ) | app ()
dev2 .(_ :: _) .(_ :: _) (r :: r') | typ = dev2 _ _ r :: dev2 _ _ r'
dev2 .((lam _ :: pi _ _) $ _) .((lam _ :: pi _ _) $ _) ((lam rt :: pi rS rT) $ rs) | beta
  = beta (dev2 _ _ rt) (dev2 _ _ rS) (dev2 _ _ rT) (dev2 _ _ rs)
dev2 .((lam _ :: pi _ _) $ _) ._ (beta rt rS rT rs) | beta
  = parStab (parzRefl si , (dev2 _ _ rs :: dev2 _ _ rS)) (dev2 _ _ rt :: dev2 _ _ rT)
dev2 .([ _ :: _ ]) .([ _ :: _ ]) [ r :: r' ] | upsi = upsi (dev2 _ _ r)
dev2 .([ _ :: _ ]) t' (upsi r) | upsi = dev2 _ _ r
