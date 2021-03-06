
%if False
\begin{code}
module TypesNi where

id : forall {l}{X : Set l} -> X -> X
id x = x

_-_ : forall {k l f}{A : Set k}{B : A -> Set l}{C : (a : A) -> B a -> Set f}
      (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a) ->
      (a : A) -> C a (g a)
(f - g) a = f (g a)

_-:>_ : forall {I : Set}(S T : I -> Set) -> I -> Set
(S -:> T) i = S i -> T i
[_] : forall {I : Set}(P : I -> Set) -> Set
[ P ] = forall {i} -> P i

\end{code}
%endif

\documentclass[natbib]{article}
\usepackage{a4wide}
\usepackage{upgreek}
\usepackage{stmaryrd}
\usepackage{latexsym}
\usepackage{pig}
\ColourEpigram

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

%subst numeral a = "\C{" a "}"
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"

%format forall = "\blue{\forall}"

\newcommand{\type}{\blue{\ast}}
\newcommand{\hb}{\!:\!}
\newcommand{\PI}[2]{\blue{(\black{#1}\hb \black{#2})\to\;}}
\newcommand{\LT}[2]{\red{\uplambda\black{#1}\hb \black{#2}.\;}}
\newcommand{\LA}[1]{\red{\uplambda\black{#1}.\;}}
\newcommand{\conv}{\cong}
\newcommand{\EC}{\mathcal{E}}
\newcommand{\VALID}[1]{#1 \vdash \textsc{ok}}
\newcommand{\MLSYN}[3]{#1 \vdash #2 \,:\, #3}

\newcommand{\U}[1]{\black{\mathsf{#1}}}
\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}

\newcommand{\agdanote}[1]{[\textbf{Agda.}~ #1]}

\begin{document}
\title{The Types Who Say `$\backslash$ni'}
\author{Conor McBride}
\maketitle

\section{Introduction}

This paper documents a formalization of the basic metatheory for a
bidirectional presentation of Martin-L\"of's small and beautiful, but
notoriously inconsistent dependent type theory from
1971~\cite{martinloef:atheoryoftypes}. Perhaps more significantly, it
introduces a methodology for constructing and validating bidirectional
type systems, illustrated with a nontrivial running
example. Crucially, the fact that the system is not strongly
normalizing is exploited to demonstrate concretely that the
methodology relies in no way on strong normalization, which is perhaps
peculiar given that bidirectional type systems are often (but not
here) given only for terms in $\beta$-normal
form~\cite{DBLP:journals/toplas/PierceT00}.


\section{The 1971 Rules}

Let us first see the system which we are about to reorganise.

\textbf{Really? Actually, I'm just guessing.}

\[\begin{array}{rrl@@{\qquad}l}
f,s,t,S,T & ::= & \type & \mbox{the type of all types} \\
          &   || & \PI xS T[x] & \mbox{dependent function spaces} \\
          &   || & \LT xS t[x] & \mbox{typed abstraction} \\
          &   || & f\:s        & \mbox{application} \\
          &   || & x           & \mbox{variable} \medskip\\
\Gamma,\Delta & ::= & \EC & \mbox{empty context} \\
              &   || & \Gamma,x\hb S & \mbox{context extension, with freshly chosen $x$}
\end{array}\]

It is my habit to be explicit (with square brackets) when introducing schematic variables in the scope of a binder: here, $T[x]$ and $t[x]$ may depend on the $x$ bound just before, whereas the domain type $S$ may not. It is, moreover, my habit to substitute such bound variables just by writing terms in the square brackets. For example, the $\beta$-contraction scheme is given thus:
\[
(\LT xS t[x])\:s \leadsto t[s]
\]
The left-hand side is a \emph{pattern}, which establishes schematic variables and makes clear their scope;
the right-hand side is an \emph{expression}, which must explain how the bound variable is instantiated.

Terms are identified up to $\alpha$-conversion and substitution is capture-avoiding: the formalization uses a scope-safe de Bruijn index representation~\cite{deBruijn:dummies}.

Let us define $\conv$, `$\beta$-convertibility', to be the equivalence and contextual closure of $\leadsto$. The typing rules will identify types up to $\conv$.

We have two judgment forms
\begin{description}
\item[context validity] \framebox{$\VALID\Gamma$} ~ asserts that $\Gamma$ is an assignment of types to distinct variables, where each type may depend on the variables given before;
\item[type synthesis] \framebox{$\MLSYN\Gamma tT$} ~ asserts that the type $T$ can be \emph{synthesized} for the term $t$.
\end{description}

\[\begin{array}{l@@{\qquad}c}
\framebox{$\VALID\Gamma$}&
  \Axiom{\VALID\EC}\qquad
  \Rule{\VALID\Gamma\quad \MLSYN\Gamma S\type}
       {\VALID{\Gamma,x\hb S}}
\bigskip\\
\framebox{$\MLSYN\Gamma tT$}&
  \Rule{\VALID{\Gamma,x\hb S,\Delta}}
       {\MLSYN{\Gamma,x\hb S,\Delta}xS} \qquad
  \Rule{\VALID\Gamma}{\MLSYN\Gamma\type\type}
\\ &
  \Rule{\MLSYN\Gamma S\type\quad \MLSYN{\Gamma,x\hb S}{T[x]}\type}
       {\MLSYN\Gamma{\PI xS T[x]}\type} \qquad
  \Rule{\MLSYN\Gamma S\type\quad \MLSYN{\Gamma,x\hb S}{t[x]}{T[x]}}
       {\MLSYN\Gamma{\LT xS t[x]}{\PI xS T[x]}}\\
& \Rule{\MLSYN\Gamma f {\PI xS T[x]} \quad \MLSYN\Gamma sS}
       {\MLSYN\Gamma{f\:s}{T[s]}} \\
&  \Rule{\MLSYN\Gamma tS \quad \MLSYN\Gamma T\type\quad S\conv T}
       {\MLSYN\Gamma tT} \\
\end{array}\]

I do not write explicit variable freshness requirements. Rather, I think of the turnstile as equipped with a supply of fresh names for free variables, while bound names are arbitrary. So, for example, in the rule for typing an abstraction, it is not that we hope for a coincidence of bound names but that we impose a standard choice of a free name when we extend the context.

The system has one rule for each syntactic construct and one rule (the `conversion' rule) to impose the identification of types up to convertibility. If you look carefully at the rules for the syntax, you will
see that the data left of the colon in the conclusion determine the data left of the colon in the premises;
moreover, the data right of the colon in the premises determine the data right of the colon in the conclusion.
That is to say that these five rules can be read as instructions for type synthesis. Only the conversion rule
comes with no clear syntactic guidance: the essence of writing a type synthesis \emph{algorithm} is to fix a
particular strategy for deploying the conversion rule, then proving that strategy complete.

It is worth noting that the application rule has \emph{two} occurrences of $S$ right of the colon: implicitly, such a rule demands that two synthesized types agree precisely, but the conversion rule allows them to be brought into precise agreement by computation. Meanwhile, the conversion rule allows a type, once synthesized, to be modified by any amount of forward \emph{or backward} computation. Backward creates an opportunity to introduce
any old nonsense, as
\[
  (\LT X\type \type)\:(\type\:\type\:\type\:\type) \leadsto \type
\]
To prevent infection with such nonsense, the conversion rule insists that we check we end up with a valid type.
Now, as it happens, our reduction system is confluent and moreover, forward computation preserves type. As a result, if we know that $S \conv T$ are valid types, then they have a common reduct $R$: we can compute $S$ to $R$ and $T$ to $R$ without stepping outside the valid types at any point. Hence, the conversion rule's check
that $T$ is a type is both necessary and sufficient.

A further point of note is that the type synthesis rules have no axioms. The \emph{only} axiom is that the empty context is uncontroversially valid. The two `base cases' of typing, for $\type$ and for variables, have premises ensuring context validity. The following `sanity clauses' are admissible:
\[
\Rule{\MLSYN\Gamma tT}{\VALID\Gamma}
\qquad
\Rule{\MLSYN\Gamma tT}{\MLSYN\Gamma T\type}
\]
You can see that both of the rules which extend the context directly check the validity condition for so doing: the type synthesis rule for abstraction makes crucial use of the type annotation in $\LT xS t[x]$, without which it would be necessary to guess the type of $x$ from its uses. The type of the abstraction body, being generic
in the argument, allows us to form the correct function type unproblematically.
Meanwhile, to see why synthesized types are well formed (for application in particular), we need stability of typing under substitution, which is as much as to say that we can substitute a (suitably weakened) typing derivation for some $s:S$ in place of all uses of the variable rule which witness $x:S$. Stability of typing
under substitution relies, of course, on stability of computation under substitution. However, our computation
rule never makes any requirements about the presence of free variables, matching only syntactic constructs which are preserved by substitution, so it would be quite a surprise if stability under substitution were to fail.


The rule for $\type$, often called `Type-in-Type', opens the door to paradox. Famously, Girard had shown that the Burali-Forti paradox could be embedded in System U, which has two impredicative layers. Martin-L\"of's system offered arbitrary impredicativity, making it easy to embed System U. However, despite being inconsistent and non-normalizing, this theory does enjoy the basic type preservation and progress properties we expect of functional programming languages, and many of the type theories we have today are effectively refinements with sufficient paranoia to prevent loops.

\textbf{Stick in the Hurkens construction?}


\section{The Bidirectional Syntax}

\newcommand{\CHK}[3]{#1 \vdash #2 \ni #3}
\newcommand{\SYN}[3]{#1 \vdash #2 \in #3}
\newcommand{\el}[1]{\green{\underline{\black{#1}}}}

The idea behind bidirectional type systems is to make use of the way we sometimes know type information in advance. If we start from a type, there may be fewer choices to determine an inhabiting term. The type represents a \emph{requirement}, rather than a \emph{measurement}. We work a little more precisely at managing the flow of type information, and we gain some convenience and cleanliness. I like to start by separating the syntactic categories into checkable \emph{constructions} and synthesizable \emph{eliminations}.
\[\begin{array}{rrl@@{\qquad}l}
s,t,S,T & ::= & \type & \mbox{the type of all types} \\
        &   || & \PI xS T[x] & \mbox{dependent function spaces} \\
        &   || & \LA x t[x] & \mbox{untyped abstraction} \\
        &   || & \el e & \mbox{embedded elimination} \medskip \\
e,f     & ::= & x     & \mbox{variable} \\
        &   || & f\:s  & \mbox{application} \\
        &   \vdots &  & \mbox{to be continued\ldots}
\end{array}\]
I have omitted one elimination form by way of generating a little suspense: let us see how we get along without it. Type formation and value introduction syntax sits on the \emph{construction} side; variable usage and application sit on the \emph{elimination} side. Eliminations embed into constructions, with a relatively unobtrusive but nontrivial underline: in a real implementation, there is no need to spend characters on this feature, but when studying metatheory, it helps to see where it is used. The reverse embedding is \emph{not} available, and we shall see why when we study the rules.

At this stage, however, it is worth noting the following:
\begin{itemize}
\item the syntax forbids the expression of $\beta$-redexes;
\item every elimination has a variable at its head, with a spine of arguments;
\item it is syntactically invalid to substitute a construction for a variable.
\end{itemize}

%format Set = "\U{Set}"
%format Sort = "\D{Sort}"
%format chk = "\C{chk}"
%format syn = "\C{syn}"
Let us formalize this syntax in Agda. We may enumerate the choice of syntactic
category, or |Sort| (in its universal algebra sense, rather than its `type of
types' sense) for short.

\begin{code}
data Sort : Set where chk syn : Sort
\end{code}

%format Nat = "\D{Nat}"
%format ze = "\C{ze}"
%format su = "\C{su}"
The constructor names highlight the distinction between checking and synthesis.
Variables must be in \emph{scope}. In more complex syntaxes, a scope is a list
of variable |Sort|s, but here we have variables only of sort |syn|, so a
|Nat|ural number suffices to represent a valid scope.
\agdanote{The BUILTIN pragma instructs Agda to allow us decimal numerals for numbers.}

\begin{code}
data Nat : Set where  ze : Nat ;  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}
\end{code}

%format <= = "\F{\le}"
%format _<=_ = _ <= _
%format <=_ = <= _
%format oz = "\C{oz}"
%format os = "\C{os}"
\newcommand{\apo}{\mbox{\red{'}}}
%format o' = "\C{o\apo}"
%format Var = "\F{Var}"
%format Mor = "\D{Mor}"
%format Zero = "\D{Zero}"
%format ox = "\C{ox}"
A syntactically valid term has a scope and a sort.
\newsavebox{\opebox}
\savebox{\opebox}{\parbox{4in}{
\begin{code}
data Mor (X : Nat -> Set) : Nat -> Nat -> Set where
  oz  :                                      Mor X    ze        ze
  os  : forall {n m} -> Mor X n m ->         Mor X (  su  n) (  su  m)
  o'  : forall {n m} -> Mor X n m ->         Mor X        n  (  su  m)
  ox  : forall {n m} -> Mor X n m -> X m ->  Mor X (  su  n)        m

data Zero : Set where

_<=_ : Nat -> Nat -> Set
_<=_ = Mor (\ _ -> Zero)

Var : Nat -> Set
Var = (1 <=_)
\end{code}
}}

%format Tm = "\D{Tm}"
%format Ty = "\C{\ast}"
%format Pi = "\C{\Uppi}"
%format la = "\C{\uplambda}"
%format em = "\C{\upepsilon}"
%format va = "\C{\#}"
%format $ = "\C{\raisebox{0.05in}{$\scriptscriptstyle{\$}$}}"
%format _$_ = _ $ _
%format :: = "\C{:\!:}"
%format _::_ = _ :: _
\begin{code}
data Tm (n : Nat) : Sort -> Set where                       -- informally\ldots

  Ty   :                                          Tm n chk  -- $\type$
  Pi   : (S : Tm n chk)  (T : Tm (su n) chk)  ->  Tm n chk  -- $\PI xS T[x]$
  la   :                 (t : Tm (su n) chk)  ->  Tm n chk  -- $\LA x t[x]$
  em   : (e : Tm n syn)                       ->  Tm n chk  -- $\el e$

  va   : (i : Var n)                          ->  Tm n syn  -- $x$
  _$_  : (f : Tm n syn)(s : Tm n chk)         ->  Tm n syn  -- $f\:s$
\end{code}
\newsavebox{\radbox}\savebox{\radbox}{\parbox{4in}{
\begin{code}
  _::_ : Tm n chk -> Tm n chk -> Tm n syn
\end{code}
}}
%format == = "\D{\simeq}"
%format _==_ = _ == _
%format refl = "\C{refl}"
\agdanote{In the declaration of |Tm|, we see |(n : Nat)| abstracted left of |:|,
scoping over the whole declaration. Some young people might incorrectly refer to
$n$ as a `parameter' of |Tm|, but it is not a parameter in Dybjer's definitive
sense~\cite{dybjer:families}: |Tm|'s first argument varies in
recursive positions, so we are taking a least fixpoint on |Nat -> Sort -> Set|,
not a number of fixpoints on |Sort -> Set|. The |n| is thus an \emph{index},
but one in which the constructor return types are \emph{uniform}. Hancock calls
such indices `protestant' to distinguish them from the `catholic' indices (such
as our |Sort|) which may be individually instantiated in constructor return
types, as paradigmatically done in the inductively defined equality type,
enabling
the miracle of transubstantiation.}

It has always struck me as an intensely frustrating business, defining
an inductive datatype to represent some syntax of terms, and then
showing that it really works like a syntax by defining operations such
as substitution and proving that they exhibit the appropriate
structure. When appropriately viewed, these types are syntactic by
construction. Sadly, the appropriate view is not the machine's view:
the business of teaching the machine to see syntax is for another time.

Back to our datatype, note that the types of |Pi| and |la| expose
their variable binding power by incrementing the scope count for the
range of function types and the body of an abstraction. The |Var n|
type represents a choice of one variable from the |n| available. I
shall resolve the mystery of its definition directly.


\section{Variables as a Line in Pascal's Triangle}

Choosing \emph{one} variable from those in scope is the unitary case
of choosing \emph{some} variables from those in scope.  Choosing
\emph{some} variables amounts to constructing an
\emph{order-preserving embedding} (or a `thinning', for short) from
the chosen variables into all the variables.  Such a choice is
possible only if we have enough variables, so we acquire a
proof-relevant version, |<=|, of the `less or equal' relation,
preserved by the constructors of numbers (as shown by |oz| and |os|),
but allowing us to omit a `target' variable (with |o'|) whenever we
choose, or rather, whenever we choose-not.

With an eye to the future, I introduce a more general notion of
\emph{scope morphism}, which allows us to embed variables from source
to target scope, but also to map them to some other sort of image, |X|.
We acquire |<=| as the special case where |X| is empty.

\usebox{\opebox}

Our |Var| is then given as an operator section, fixing the number of variables
to choose as |1|.

We may tabulate these |<=| types as a version of Pascal's Triangle,
replacing the \emph{number} of paths to a given position by the
\emph{type} of the embeddings they generate:
\[\begin{array}{c@@{}c@@{}c@@{}c@@{}c@@{}c@@{}c} &&& |oz : 0 <= 0| &&&
\\ &&\;\;|o'|\swarrow && \searrow|os|\;\;&& \\ &&|0 <= 1| && |1 <=
1|&& \\ &|o'|\swarrow && |os|\searrow\;\;\swarrow|o'| &&
\searrow|os|&\\ &|0 <= 2| && |1 <= 2| && |2 <= 2|& \\ |o'|\swarrow &&
|os|\searrow\;\;\swarrow|o'| && |os|\searrow\;\;\swarrow|o'| &&
\searrow|os|\\ |0 <= 3| && |1 <= 3| && |2 <= 3| && |3 <= 3| \\ \vdots
&& \vdots &\vdots& \vdots && \vdots \end{array}\]

The left spine of the triangle (usually all 1s) gives the unique
embedding from the empty scope to any scope. Meanwhile, the right
spine gives the identity embedding. In fact, we can and should
construct these operations for scope morphisms in general.

%format oe = "\F{oe}"
%format oi = "\F{oi}"

\parbox{3in}{
\begin{code}
oe : forall {n X} -> Mor X ze n
oe {ze}    = oz
oe {su n}  = o' (oe {n})
\end{code}}
\parbox{1.5in}{
\begin{code}
oi : forall {n X} -> Mor X n n
oi {ze}    = oz
oi {su n}  = os (oi {n})
\end{code}}

\agdanote{Curly braces in function types mark arguments to be suppressed by default.
Curly braces in applications and abstractions override default suppression, as is
necessary here for purposes of pattern matching. That is, in a most unmilnerian
manner, arguments usually delivered by ``type inference'' have relevance in execution.
We could perfectly well have written |o' oe| and |os oi| on the right of the above
step cases, suppressing the |{n}|s. I give them explicitly only to make legible the
structural justification for the recursion.}

|Var| is the next south-westerly diagonal down from the left spine, |1
<= n|, where each type has size |n| and may be taken to represent the
choice of one variable from |n| in scope. The $i$th de Bruijn index
(counting from 0) is given as $|o'|^i\:|(os oe)|$.  I use |(1 <=_)|
rather than the more traditional `Fin' family to emphasize that
variable sets arise from |<=|, the category of thinnings. We have the identity
thinning, but you will have to wait for the composition. Why? Because we shall
define compositions for |Mor| in general, not just for |<=|, and that will
demand additional equipment.


\section{Action and Composition of Scope Morphisms}

In any case, we must consider how to make our morphisms act on \emph{terms}.

%format - = "\F{\circ}"
%format + = "\D{+}"
%format _+_ = _ + _
%format +e = "\F{+}_{\F{e}}"
%format _+e_ = _ +e _
%format +m = "\F{+}"
%format _+m_ = _ +m _
%format inl = "\C{inl}"
%format inr = "\C{inr}"
\newsavebox{\plusbox}\savebox{\plusbox}{\parbox{4in}{
\begin{code}
data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

_+e_ : {S T U : Set} -> (S -> U) -> (T -> U) -> (S + T) -> U
(f +e g) (inl s) = f s
(f +e g) (inr t) = g t

_+m_ : {S S' T T' : Set} -> (S -> S') -> (T -> T') -> (S + T) -> (S' + T')
f +m g = (inl - f) +e (inr - g)
\end{code}}}

%format ACT = "\mathrm{ACT}"
%format fetch = "\F{fetch}"
%format fetched = "\F{fetched}"
%format / = "\F{\slash}"
%format _/_ = _ / _
%format sg = "\V{\sigma}"
\begin{code}
module ACT (X : Nat -> Set)
           -- operations on |X| will appear as we discover what we need
\end{code}

\vspace*{ -0.28in}

\newsavebox{\tmXbox}\savebox{\tmXbox}{\parbox{4in}{
\begin{code}
           (tmX : forall {n} -> X n -> Tm n syn)
\end{code}}}
\newsavebox{\wkXbox}\savebox{\wkXbox}{\parbox{4in}{
\begin{code}
           (wkX : forall {n} -> X n -> X (su n))
\end{code}}}
\begin{code}
  where
\end{code}
\newsavebox{\fetchTybox}\savebox{\fetchTybox}{\parbox{5in}{
\begin{code}
    fetch : forall {n m} -> Var n -> Mor X n m -> Var m + X m
\end{code}}}
\newsavebox{\fetchbox}\savebox{\fetchbox}{\parbox{5in}{
\begin{code}
    fetch  i          (o' sg)    = (o' +m wkX) (fetch i sg)
    fetch  (ox i ())  sg
    fetch  (os i)     (os sg)    = inl (os oe)
    fetch  (o' i)     (os sg)    = (o' +m wkX) (fetch i sg)
    fetch  (os i)     (ox sg x)  = inr x
    fetch  (o' i)     (ox sg x)  = fetch i sg
\end{code}}}
\newsavebox{\fetchedbox}\savebox{\fetchedbox}{\parbox{5in}{
\begin{code}
    fetched : forall {m} -> Var m + X m -> Tm m syn
    fetched = va +e tmX
\end{code}}}

\vspace*{ -0.35in}

\begin{code}
    _/_ : forall {n m sort} -> Tm n sort -> Mor X n m -> Tm m sort
\end{code}

\vspace*{ -0.2in}

\newsavebox{\vabox}\savebox{\vabox}{\parbox{3in}{
\begin{code}
    va i      / sg  = fetched (fetch i sg)
\end{code}}}
\begin{spec}
    va i      / sg                = ?
\end{spec}

\vspace*{ -0.2in}

\begin{code}
    Ty        / sg                = Ty
    Pi S T    / sg                = Pi (S / sg) (T / os sg)
    la t      / sg                = la (t / os sg)
    em e      / sg                = em (e / sg)
    (f $ s)   / sg                = (f / sg) $ (s / sg)
\end{code}
\newsavebox{\radactbox}\savebox{\radactbox}{\parbox{4in}{
\begin{code}
    (t :: T)  / sg                = (t / sg) :: (T / sg)
\end{code}}}

We can implement the (functorial, as we shall see) action of a
morphism for everything but variables, using the (functorial, as we
shall see) |os| constructor.

Let us think about what the morphism |sg| might do to some source variable |i|.
It will either be sent to some target variable by |os| or mapped to some |X| by an
|ox|. Correspondingly, we should be able to implement some operation \\
\usebox{\fetchTybox} \\
where |+| is the usual sum type, |+e| its case analysis operator, and
|+m| its functorial action.

\usebox{\plusbox}

We can then complete our action, provided we know how to turn an |X| into an
elimination. If we add a parameter to the |ACT| module, \\
\usebox{\tmXbox} \\
then we can make some progress. \\
\usebox{\fetchedbox} \\
\usebox{\vabox}

However, to finish the job we must define |fetch|. This will clearly require us
to be shift |X|s under binders. |ACT| needs a further module parameter\\
\usebox{\wkXbox}\\
so that we may complete the construction:\\
\usebox{\fetchbox}

We immediately acquire the action of thinnings: as |X| is empty, |tmX| and |wkX| are
vacuous.
%format /t = / "_{\!\F{t}}"
%format _/t = _ /t
%format _/t_ = _ /t _
%format ACT._/_ = ACT "." _/_
\begin{code}
_/t_ : forall {n m sort} -> Tm n sort -> n <= m -> Tm m sort
_/t_ = ACT._/_ (\ _ -> Zero) (\ ()) (\ ())
\end{code}

\agdanote{Unlike in Haskell, where |()| means the boring value in the unit type,
Agda uses |()| for the \emph{impossible} pattern in an empty type. Moreover, when
you point out that an input is impossible, you are absolved of the responsibility
to explain what to do with it. Correspondingly |\ ()| is just the function we need
to map non-existent |X|s into anything.}

Now that we can thin, \emph{substitution} is easy, too. We may now permit morphisms
which turn variables into eliminations.
%format Elim = "\F{Elim}"
%format >> = "\F{\Rightarrow}"
%format _>>_ = _ >> _
%format /s = / "_{\!\F{s}}"
%format _/s = _ /s
%format _/s_ = _ /s _
\begin{code}
Elim : Nat -> Set
Elim n = Tm n syn
\end{code}
To give the action of a substitution, we need to embed |Elim| into itself, which is
the identity, and to weaken |Elim|, which we do with the thinning |o' oi|, `missing'
the top variable.
\begin{code}
_>>_ : Nat -> Nat -> Set
_>>_ = Mor Elim

_/s_ : forall {n m sort} -> Tm n sort -> n >> m -> Tm m sort
_/s_ = ACT._/_ Elim id (_/t o' oi)
\end{code}

We can play the same sort of game when defining composition.
%format COMP = "\mathrm{COMP}"
%format /, = "\F{\fatsemi}"
%format _/,_ = _ /, _
%format ta = "\V{\tau}"
\begin{code}
module COMP  (S T U  : Nat -> Set)
             (front  : forall {n m} -> S n ->  Mor T n m ->  U m)
             (back   : forall {m} ->           T m ->        U m)
  where
    _/,_ : forall {p n m} -> Mor S p n -> Mor T n m -> Mor U p m
    sg       /, o' ta    = o' (sg /, ta)
    ox sg s  /, ta       = ox (sg /, ta) (front s ta)
    os sg    /, ox ta t  = ox (sg /, ta) (back t)
    o' sg    /, ox ta t  = sg /, ta
    os sg    /, os ta    = os (sg /, ta)
    o' sg    /, os ta    = o' (sg /, ta)
    oz       /, oz       = oz
\end{code}

\agdanote{I have been careful to order the lines of this definition
so that it is lazy in its front argument whenever its back is |o' ta|.
Agda's translation from pattern matching to case analysis trees is
quite na\"\i{}ve: the fact that the first line does not split |sg| but
does match the back argument is what ensures this laziness.
The first line takes priority over the second: they do overlap.
Shifting the first two lines later in the definition while retaining their
order would retain the extensional properties of the function, but
change the intensional properties.}

As we try to implement composition, we discover that we need the
means to transport |S| and |T| values (packed by |ox|) across to
|U|. For thinning, of course, these are vacuous requirements.
%format /,t = /, "_{\F{t}}"
%format _/,t_ = _ /,t _
%format ph = "\V{\phi}"
%format th = "\V{\theta}"
%format COMP._/,_ = COMP "." _/,_
\begin{code}
_/,t_ : forall {p n m} -> p <= n -> n <= m -> p <= m
_/,t_ =  COMP._/,_ (\ _ -> Zero) (\ _ -> Zero) (\ _ -> Zero)
         (\ ()) (\ ())
\end{code}
For substitutions, we need merely know how they act.
%format /,s = /, "_{\F{s}}"
%format _/,s_ = _ /,s _
\begin{code}
_/,s_ : forall {p n m} -> p >> n -> n >> m -> p >> m
_/,s_ =  COMP._/,_ Elim Elim Elim _/s_ (\ t -> t)
\end{code}

%format rewrite = "\mathkw{rewrite}"
Now, let us at least state some laws in terms of the equality type:
\begin{code}
data _==_ {l}{X : Set l}(x : X) : X -> Set l where refl : x == x
\end{code}
%if False
\begin{code}
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}
\end{code}
%endif

%format th0 = "\V{\theta_0}"
%format th1 = "\V{\theta_1}"
%format th2 = "\V{\theta_2}"
%format sg0 = "\V{\sigma_0}"
%format sg1 = "\V{\sigma_1}"
%format sg2 = "\V{\sigma_2}"
I omit the unedifying proofs that show thinnings and substitutions
both form categories acting functorially on terms.
\[\begin{array}{c@@{\qquad}c@@{\qquad}c}
& |(t /t oi) == t| & |((t /t th0) /t th1) == (t /t (th0 /, th1))| \\
|(oi /,t th) == th| & |(th /,t oi) == th|
  & |((th0 /,t th1) /,t th2) == (th0 /,t (th1 /,t th2))| \\
& |(t /s oi) == t| & |((t /t sg0) /t sg1) == (t /s (sg0 /, sg1))| \\
|(oi /,s sg) == sg| & |(sg /,s oi) == sg|
  & |((sg0 /,s sg1) /,s sg2) == (sg0 /,s (sg1 /,s sg2))| \\
\end{array}\]
The proofs are implemented in the same style as the programs: generic results
are proved with conditions, then instantiated trivially for thinnings to obtain
the lemmas needed to show that the conditions hold for substitutions.

It is worth noting that construction of |/t| and |/s|, together with the
proofs of the laws they satisfy, is entirely generic for syntaxes with binding.
Really, we should present all the syntaxes as a \emph{universe} and do the
construction once.

With our basic syntactic machinery now in place, let us
return to designing the type system.

%if False
\begin{code}
self : {X : Set}(x : X) -> x == x
self x = refl
_=$=_ : {S T : Set}{f g : S -> T}{x y : S} -> f == g -> x == y -> f x == g y
refl =$= refl = refl
infixl 2 _=$=_


sym : {X : Set}{x y : X} -> x == y -> y == x
sym refl = refl
trans : {X : Set}{x y z : X} -> x == y -> y == z -> x == z
trans refl = id

_-[_>_ : forall {X : Set} (x : X) {y z} -> x == y -> y == z -> x == z
x -[ refl > q = q

oeUnique : forall {n}(i : ze <= n) -> oe == i
oeUnique oz     = refl
oeUnique (o' i) = self o' =$= oeUnique i

mor : forall {S T : Nat -> Set} -> (forall {n} -> S n -> T n) ->
       forall {n m} -> Mor S n m -> Mor T n m
mor f oz = oz
mor f (os sg) = os (mor f sg)
mor f (o' sg) = o' (mor f sg)
mor f (ox sg s) = ox (mor f sg) (f s)

morId : forall {S : Nat -> Set}
          (f : forall {n} -> S n -> S n)(fq : forall {n}(s : S n) -> f s == s)
          {n m}(sg : Mor S n m) ->
          mor f sg == sg
morId f fq oz = self oz
morId f fq (os sg) = self os =$= morId f fq sg
morId f fq (o' sg) = self o' =$= morId f fq sg
morId f fq (ox sg s) = self ox =$= morId f fq sg =$= fq s

module ACTID (X : Nat -> Set)
             (tmX : forall {n} -> X n -> Tm n syn)
             (wkX : forall {n} -> X n -> X (su n))
  where
    open ACT X tmX wkX

    fetchId : forall {n}(i : Var n) -> fetch i oi == inl i
    fetchId (os i) = self inl =$= (self os =$= oeUnique i)
    fetchId (o' i) rewrite fetchId i = refl
    fetchId (ox i ())

    actId : forall {n sort}(t : Tm n sort) -> (t / oi) == t
    actId (va i) with fetch i oi | fetchId i
    actId (va i) | .(inl i) | refl = refl
    actId Ty = self Ty
    actId (Pi S T) = self Pi =$= actId S =$= actId T
    actId (la t) = self la =$= actId t
    actId (em e) = self em =$= actId e
    actId (f $ s) = self _$_ =$= actId f =$= actId s
    actId (t :: T) = self _::_ =$= actId t =$= actId T

module COMPCAT (S T U : Nat -> Set)
               (front : forall {n m}(s : S n)(ta : Mor T n m) -> U m)
               (back  : forall {n} -> T n -> U n)
  where
    open COMP S T U front back
    
    idComp : forall {n m}(ta : Mor T n m) -> (oi /, ta) == mor back ta
    idComp oz = self oz
    idComp (os ta) = self os =$= idComp ta
    idComp (o' ta) = self o' =$= idComp ta
    idComp (ox ta t) = self ox =$= idComp ta =$= self (back t)

    compId : forall {n m}(sg : Mor S n m) -> (sg /, oi) == mor (\ s -> front s oi) sg
    compId oz = self oz
    compId (os sg) = self os =$= compId sg
    compId (o' sg) = self o' =$= compId sg
    compId {m = ze}   (ox sg s) = self ox =$= compId sg =$= self (front s oz)
    compId {m = su m} (ox sg s) = self ox =$= compId sg =$= self (front s (os oi))

    data CompG : forall {p n m} -> Mor S p n -> Mor T n m -> Mor U p m -> Set where
      cg-' : forall {p n m}{sg : Mor S p n}{ta : Mor T n m}{up : Mor U p m} ->
              CompG sg ta up -> CompG sg (o' ta) (o' up)
      cgx- : forall {p n m}{sg : Mor S p n}{ta : Mor T n m}{up : Mor U p m}(s : S n) ->
              CompG sg ta up -> CompG (ox sg s) ta (ox up (front s ta))
      cgsx : forall {p n m}{sg : Mor S p n}{ta : Mor T n m}{up : Mor U p m}(t : T m) ->
              CompG sg ta up -> CompG (os sg) (ox ta t) (ox up (back t))
      cg'x : forall {p n m}{sg : Mor S p n}{ta : Mor T n m}{up : Mor U p m}(t : T m) ->
              CompG sg ta up -> CompG (o' sg) (ox ta t) up
      cgss : forall {p n m}{sg : Mor S p n}{ta : Mor T n m}{up : Mor U p m} ->
              CompG sg ta up -> CompG (os sg) (os ta) (os up)
      cg's : forall {p n m}{sg : Mor S p n}{ta : Mor T n m}{up : Mor U p m} ->
              CompG sg ta up -> CompG (o' sg) (os ta) (o' up)
      cgzz : CompG oz oz oz

    compG : forall {p n m}(sg : Mor S p n)(ta : Mor T n m) -> CompG sg ta (sg /, ta)
    compG sg (o' ta) = cg-' (compG sg ta)
    compG oz oz = cgzz
    compG (ox sg s) oz = cgx- s (compG sg oz)
    compG (os sg) (os ta) = cgss (compG sg ta)
    compG (o' sg) (os ta) = cg's (compG sg ta)
    compG (ox sg s) (os ta) = cgx- s (compG sg (os ta))
    compG (os sg) (ox ta t) = cgsx t (compG sg ta)
    compG (o' sg) (ox ta t) = cg'x t (compG sg ta)
    compG (ox sg s) (ox ta t) = cgx- s (compG sg (ox ta t))

    module COMPACT
      (wkS : [ S -:> (S - su) ])
      (tmS : [ S -:> Elim ])
      (wkT : [ T -:> (T - su) ])
      (tmT : [ T -:> Elim ])
      (wkU : [ U -:> (U - su) ])
      (tmU : [ U -:> Elim ])
      (tmUtmT : forall {n}(t : T n) -> tmT t == tmU (back t))
      (wkUwkT : forall {n}(t : T n) -> wkU (back t) == back (wkT t))
      (tmUsTu : forall {n m}(s : S n)(ta : Mor T n m) ->
                 ACT._/_ T tmT wkT (tmS s) ta == tmU (front s ta))
      (wkUo'  : forall {n m}(s : S n)(ta : Mor T n m) ->
                wkU (front s ta) == front s (o' ta))
      (wkSox  : forall {n m}(s : S n)(ta : Mor T n m)(t : T m) ->
                front s ta == front (wkS s) (ox ta t))
      (wkSos  : forall {n m}(s : S n)(ta : Mor T n m) ->
                wkU (front s ta) == front (wkS s) (os ta))
      where
        module SA = ACT S tmS wkS
        module TA = ACT T tmT wkT
        module UA = ACT U tmU wkU

        compFetch : forall {p n m}(i : Var p)
                    {sg : Mor S p n}{ta : Mor T n m}{up : Mor U p m} ->
                    CompG sg ta up ->
                    UA.fetch i up == ((\ j -> (id +m back) (TA.fetch j ta))
                                     +e (inr - (\ s -> front s ta))) (SA.fetch i sg) 
        compFetch (ox i ()) _
        compFetch i (cg-' {sg = sg} stu) with SA.fetch i sg | compFetch i stu
        compFetch i (cg-' {ta = ta} stu) | inl j | q with TA.fetch j ta
        compFetch i (cg-' stu) | inl j | q | (inl k) rewrite q = refl
        compFetch i (cg-' stu) | inl j | q | (inr t) rewrite q | wkUwkT t = refl
        compFetch i (cg-' {ta = ta} stu) | inr s | q rewrite q | wkUo' s ta = refl
        compFetch (os i) (cgx- s stu) = refl
        compFetch (o' i) (cgx- {sg = sg} s stu) = compFetch i stu
        compFetch (os i) (cgsx t stu) = refl
        compFetch (o' i) (cgsx {sg = sg} t stu) with SA.fetch i sg | compFetch i stu
        compFetch (o' i) (cgsx {ta = ta} t stu) | inl j | q = q
        compFetch (o' i) (cgsx {ta = ta} t stu) | inr s | q rewrite q | wkSox s ta t = refl
        compFetch i (cg'x {sg = sg} t stu) with SA.fetch i sg | compFetch i stu
        compFetch i (cg'x t stu) | inl j | q = q
        compFetch i (cg'x {ta = ta} t stu) | inr s | q rewrite q | wkSox s ta t = refl
        compFetch (os i) (cgss stu) = refl
        compFetch (o' i) (cgss {sg = sg} stu) with SA.fetch i sg | compFetch i stu
        compFetch (o' i) (cgss {ta = ta} stu) | inl j | q with TA.fetch j ta
        compFetch (o' i) (cgss stu) | inl j | q | inl k rewrite q = refl
        compFetch (o' i) (cgss stu) | inl j | q | inr t rewrite q | wkUwkT t = refl
        compFetch (o' i) (cgss {ta = ta} stu) | inr s | q rewrite q | wkSos s ta = refl
        compFetch i (cg's {sg = sg} stu) with SA.fetch i sg | compFetch i stu
        compFetch i (cg's {ta = ta} stu) | inl j | q with TA.fetch j ta
        compFetch i (cg's stu) | inl j | q | (inl k) rewrite q = refl
        compFetch i (cg's stu) | inl j | q | (inr t) rewrite q | wkUwkT t = refl
        compFetch i (cg's {ta = ta} stu) | inr s | q rewrite q | wkSos s ta = refl

        compAct : forall {p n m}{sort}(t : Tm p sort)
                  (sg : Mor S p n)(ta : Mor T n m)
                   ->
                  ((t SA./ sg) TA./ ta) == (t UA./ (sg /, ta))
        compAct (va i) sg ta
          with UA.fetch i (sg /, ta) | SA.fetch i sg
               | compFetch i (compG sg ta)
        compAct (va i) sg ta | inl k | inl j | q with TA.fetch j ta
        compAct (va i) sg ta | inl k | inl j | refl | inl .k = refl
        compAct (va i) sg ta | inl k | inl j | ()   | inr t
        compAct (va i) sg ta | inl k | inr s | ()
        compAct (va i) sg ta | inr u | inl j | q with TA.fetch j ta
        compAct (va i) sg ta | inr u | inl j | () | (inl k)
        compAct (va i) sg ta | inr _ | (inl j) | refl | (inr t) = tmUtmT t
        compAct (va i) sg ta | inr _ | (inr s) | refl = tmUsTu s ta
        compAct Ty sg ta = self Ty
        compAct (Pi S T) sg ta = self Pi =$= compAct S sg ta =$= compAct T (os sg) (os ta)
        compAct (la t) sg ta =  self la =$= compAct t (os sg) (os ta)
        compAct (em e) sg ta = self em =$= compAct e sg ta
        compAct (f $ s) sg ta = self _$_ =$= compAct f sg ta =$= compAct s sg ta
        compAct (t :: T) sg ta = self _::_ =$= compAct t sg ta =$= compAct T sg ta


module THINXX (X : Nat -> Set) = COMP (\ _ -> Zero) X X (\ ()) id
module THINXXCOMP (X : Nat -> Set) = COMPCAT (\ _ -> Zero) X X (\ ()) id
module THINTHINTHIN = THINXXCOMP.COMPACT (\ _ -> Zero)
   (\ ()) (\ ()) (\ ()) (\ ()) (\ ()) (\ ())
   (\ ()) (\ ()) (\ ()) (\ ()) (\ ()) (\ ())

module THINCAT where
  module C = THINXX (\ _ -> Zero)
  module C' = THINXXCOMP (\ _ -> Zero)
  
  compId : forall {n m}(th : n <= m) -> (th C./, oi) == th
  compId th = trans (C'.compId th) (morId (\ ()) (\ ()) th)
  idComp : forall {n m}(th : n <= m) -> (oi C./, th) == th
  idComp th = trans (C'.idComp th) (morId id (\ _ -> refl) th)

module THINSBSTSBSTCOMP = THINXXCOMP Elim
module THINSBSTSBST = THINSBSTSBSTCOMP.COMPACT
  (\ ()) (\ ()) (_/t o' oi) id (_/t o' oi) id
  (\ _ -> refl) (\ _ -> refl) (\ ()) (\ ()) (\ ()) (\ ())

module SBSTXSBST (X : Nat -> Set)
           (tmX : [ X -:> Elim ])
           (wkX : [ X -:> (X - su) ])
  = COMP Elim X Elim (ACT._/_ X tmX wkX) tmX
module SBSTXSBSTCOMP  (X : Nat -> Set)
           (tmX : [ X -:> Elim ])
           (wkX : [ X -:> (X - su) ])
  = COMPCAT Elim X Elim (ACT._/_ X tmX wkX) tmX


sbstId : forall {n m}(sg : n >> m) ->
          (sg /,s oi) == sg
sbstId sg = trans (SBSTXSBSTCOMP.compId Elim id (_/t o' oi) sg)
                  (morId (_/s oi) (ACTID.actId Elim id (_/t o' oi)) sg)
idSbst : forall {n m}(sg : n >> m) ->
          (oi /,s sg) == sg
idSbst sg = trans (SBSTXSBSTCOMP.idComp Elim id (_/t o' oi) sg)
              (morId id (\ _ -> refl) sg)

module SBSTTHINSBST = SBSTXSBSTCOMP.COMPACT (\ _ -> Zero) (\ ()) (\ ())
  (_/t o' oi) id (\ ()) (\ ()) (_/t o' oi) id
  (\ ()) (\ ())
  (\ s t -> refl)
  (\ s ta -> trans (THINTHINTHIN.compAct s ta (o' oi))
             (self (s /t_) =$= (self o' =$= THINCAT.compId ta)))
  (\ _ _ ())
  (\ s ta -> trans (THINTHINTHIN.compAct s ta (o' oi))
              (trans (self (s /t_) =$= (self o' =$=
                    trans (THINCAT.compId ta) (sym (THINCAT.idComp ta))))
                (sym (THINTHINTHIN.compAct s (o' oi) (os ta)))))


oiSbst : forall {n m sort}(t : Tm n sort)(sg : n >> m) ->
             (t /s o' sg) == ((t /s sg) /t o' oi)
oiSbst t sg = sym (trans (SBSTTHINSBST.compAct t sg (o' oi))
                (self (t /s_) =$= (self o' =$=
                 trans (SBSTXSBSTCOMP.compId (\ _ -> Zero) (\ ()) (\ ()) sg)
                  (morId (_/t oi) (ACTID.actId (\ _ -> Zero) (\ ()) (\ ())) sg))))

module SBSTSBSTSBST = SBSTXSBSTCOMP.COMPACT Elim id (_/t o' oi)
  (_/t o' oi) id (_/t o' oi) id (_/t o' oi) id
  (\ _ -> refl) (\ _ -> refl) (\ _ _ -> refl)
  (\ s ta -> trans (SBSTTHINSBST.compAct s ta (o' oi))
                (self (s /s_) =$= (self o' =$=
                 trans (SBSTXSBSTCOMP.compId (\ _ -> Zero) (\ ()) (\ ()) ta)
                       (morId (_/t oi) (ACTID.actId (\ _ -> Zero) (\ ()) (\ ())) ta)))
   )
  (\ s ta t -> sym
    (trans (THINSBSTSBST.compAct s (o' oi) (ox ta t))
                          (self (s /s_) =$=
                            trans (THINXXCOMP.idComp Elim ta) (morId id (\ _ -> refl) ta)))
   )
  (\ s ta -> trans (SBSTTHINSBST.compAct s ta (o' oi))
              (trans (self (s /s_) =$= (self o' =$=
                 trans (trans (SBSTXSBSTCOMP.compId (\ _ -> Zero) (\ ()) (\ ()) ta)
                                (morId (_/t oi) (ACTID.actId (\ _ -> Zero) (\ ()) (\ ())) ta))
                       (sym (trans (THINXXCOMP.idComp Elim ta) (morId id (\ _ -> refl) ta)))))
               (sym (THINSBSTSBST.compAct s (o' oi) (os ta)))))

oxSbst : forall {p n m sort}(r : Tm (su p) sort)(sg : p >> n)(s : Elim n)(ta : n >> m) ->
           (r /s (ox sg s /,s ta)) == (r /s (ox (sg /,s ta) (s /s ta)))
oxSbst r sg s (o' ta) =
  (r /s (o' (ox sg s /,s ta))) -[ oiSbst r (ox sg s /,s ta) >
  (((r /s (ox sg s /,s ta)) /t o' oi) -[ self (_/t o' oi) =$= oxSbst r sg s ta >
  (((r /s ox (sg /,s ta) (s /s ta)) /t o' oi)
    -[ {!!} >
  {!!}))
oxSbst r sg s oz = refl
oxSbst r sg s (os ta) = refl
oxSbst r sg s (ox ta x) = refl

module COMPASS (S : Nat -> Set)
               (_//_ : forall {n m}(s : S n)(ta : Mor S n m) -> S m)
               (fact : forall {p n m}(s : S p)(sg : Mor S p n)(ta : Mor S n m) ->
                  ((s // sg) // ta) == (s // (COMP._/,_ S S S _//_ id sg ta)))
  where
  open COMP S S S _//_ id
  open COMPCAT S S S _//_ id
  compAss : forall {q p n m}(rh : Mor S q p)(sg : Mor S p n)(ta : Mor S n m) ->
              ((rh /, sg) /, ta) == (rh /, (sg /, ta))
  compAss rh sg (o' ta) = self o' =$= compAss rh sg ta
  compAss oz oz oz = refl
  compAss (ox rh r) oz oz = self ox =$= compAss rh oz oz =$= fact r oz oz
  compAss (os rh) (ox sg s) oz = self ox =$= compAss rh sg oz =$= refl
  compAss (o' rh) (ox sg s) oz = compAss rh sg oz
  compAss (ox rh r) (ox sg s) oz = self ox =$= compAss rh (ox sg s) oz =$= fact r (ox sg s) oz
  compAss (os rh) (os sg) (os ta) = self os =$= compAss rh sg ta
  compAss (o' rh) (os sg) (os ta) = self o' =$= compAss rh sg ta
  compAss (ox rh r) (os sg) (os ta) = self ox =$= compAss rh (os sg) (os ta) =$= fact r _ _
  compAss rh (o' sg) (os ta) = self o' =$= compAss rh sg ta
  compAss (os rh) (ox sg s) (os ta) = self ox =$= compAss rh sg (os ta) =$= refl
  compAss (o' rh) (ox sg s) (os ta) = compAss rh sg (os ta)
  compAss (ox rh r) (ox sg s) (os ta) = self ox =$= compAss rh (ox sg s) (os ta) =$= fact r _ _
  compAss (os rh) (os sg) (ox ta t) = self ox =$= compAss rh sg ta =$= refl
  compAss (o' rh) (os sg) (ox ta t) = compAss rh sg ta
  compAss (ox rh r) (os sg) (ox ta t) = self ox =$= compAss rh (os sg) (ox ta t) =$= fact r _ _
  compAss rh (o' sg) (ox ta t) = compAss rh sg ta
  compAss (os rh) (ox sg s) (ox ta t) = self ox =$= compAss rh sg (ox ta t) =$= refl
  compAss (o' rh) (ox sg s) (ox ta t) = compAss rh sg (ox ta t)
  compAss (ox rh r) (ox sg s) (ox ta t) =
    self ox =$= compAss rh (ox sg s) (ox ta t) =$= fact r _ _

module THINASSOC = COMPASS (\ _ -> Zero) (\ ()) (\ ())
module SBSTASSOC = COMPASS Elim _/s_ SBSTSBSTSBST.compAct
\end{code}
%endif


\section{Type-\emph{has}-Type}

We have two syntactic categories, so we need at least two judgment forms:
\begin{description}
\item[type checking] $\CHK\Gamma Tt$ ~ constructions are checked with respect to a given type;
\item[type synthesis] $\SYN\Gamma eS$ ~ eliminations have their types synthesized, from the type of their head variable, which is given in the context.
\end{description}
The `forward' $\in$ of type synthesis is pronounced ``in'', with \LaTeX{} macro {\tt $\backslash$in}, or perhaps ``is a(n)'' or ``inhabits''; its reverse, used for checking, may be pronounced ``ni'', for its \LaTeX{} macro is {\tt $\backslash$ni}, but
might be more intelligibly pronounced ``has'' or ``accepts''.

Many other authors keep terms to the left of types and use arrows (directions vary) to make the checking/synthesis distinction. I insist on retaining the left-to-right flow of \emph{time} through the
syntax of judgments, which means that when checking, the type must come before the term.

In fact, I classify the schematic positions in judgment forms as having one of three \emph{modes}:
\begin{description}
\item[inputs] are given in advance and \emph{required} to be valid (in some sense which should be specified);
\item[subjects] are the things under scrutiny, whose validity is the question;
\item[outputs] are data synthesized in the validation process and \emph{guaranteed} to be valid
  (in some sense which should be clearly specified).
\end{description}

For the above judgment forms, we shall have
\[\begin{array}{ccccc@@{\qquad\qquad}ccccc}
\CHK{\Gamma&}{&T&}{&t} & \SYN{\Gamma&}{&e&}{&S}\\
\mbox{input} && \mbox{input} && \mbox{subject} &
\mbox{input} && \mbox{subject} && \mbox{output}
\end{array}\]

In order to specify the requirements and guarantees (but not to give the rules themselves), we shall also
need a context validity judgment, $\VALID\Gamma$, for which $\Gamma$ is considered the subject.
We should expect every judgment input to have a requirement for which it is the subject and every judgment output to have a guarantee for which it is the subject. Here,
\[\begin{array}{lrl}
\CHK\Gamma Tt & \mbox{requires} & \VALID\Gamma \\
              & \mbox{requires} & \CHK\Gamma \type T \medskip \\
\SYN\Gamma eS & \mbox{requires} & \VALID\Gamma \\
              & \mbox{guarantees} & \CHK\Gamma \type S
\end{array}\]
and we are correspondingly not free to write down any old rubbish by way of typing rules. Each rule gives
rise to proof obligations which we must check. However, in the rule to establish a particular judgment,
the requirements even to propose the judgment are \emph{presumed}, not revalidated: as it were, ``We would not be asking this question if we did not already know so-and-so.''.

There is more to say about the impact of \emph{mode} on valid notions of typing rule.
\begin{enumerate}
\item The inputs of conclusions and the outputs of premises must be
\emph{patterns}, which may match against any construct of the calculus
\emph{except free variables} and are the binding sites for the
schematic variables of the rules.
\item The outputs of conclusions and the inputs of premises must
be \emph{expressions}, making use of the schematic variables in scope
and instantiating any bound variables they may have. Scope flows
clockwise round the rules, starting from the inputs of the conclusion,
accumulating left-to-right through the premises, finishing with the
outputs of the conclusion.
\item Only the schematic variables in the conclusion's \emph{subjects} are
in scope for the subjects of the premises, and they must all occur in exactly one premise.
\item A schematic subject variable becomes in scope for \emph{expressions} only after it has been the subject of a premise (and thus achieved some measure of trust).
\end{enumerate}
These four conditions form the basis of a kind of `religion' of typing
rules: let us obey them for now and consider breaking them when we are
older and more aware of the consequences of our actions.

The type checking and context validity rules are as follows:
\[\begin{array}{l@@{\qquad}c}
\framebox{$\CHK\Gamma Tt$} & \Axiom{\CHK\Gamma\type\type} \qquad
  \Rule{\CHK\Gamma\type S \quad \CHK{\Gamma,x\hb S}\type T[x]}
       {\CHK\Gamma\type \PI xS T[x]} \qquad
  \Rule{\CHK{\Gamma,x\hb S}{T[x]}{t[x]}}
       {\CHK\Gamma{\PI xS T[x]}{\LA x t[x]}} \\
  & \Rule{\SYN\Gamma e S \quad S\equiv T}
         {\CHK\Gamma T{\el e}} \bigskip \\
\framebox{$\VALID\Gamma$}&
  \Axiom{\VALID\EC}\qquad
  \Rule{\VALID\Gamma\quad \CHK\Gamma \type S}
       {\VALID{\Gamma,x\hb S}}
\end{array}\]
More rules will follow. For now, we start with `Type-has-Type', without revalidating the context (for we \emph{presume} its validity, given that the context is an input to the conclusion). Note that it is not
only the case that our entitlements \emph{allow} us to omit a $\VALID\Gamma$ premise, but also the case
that our religion \emph{forbids} such a premise, for it would have $\Gamma$ as its subject, and $\Gamma$
is an \emph{input} variable, not in scope for the subjects of premises. In time, this will save our bacon.

Meanwhile, to check a function type, we check its components: once the domain has been checked, we may extend the context (maintaining its validity) and check the range. To check an abstraction, we presume that the function type is indeed a type, and hence by inversion that its domain and range are types in the relevant contexts: we may thus proceed directly to checking that the range type accepts the body of the untyped abstraction, using the input domain as the type of the bound variable. Finally, to \emph{check} an embedded elimination, we first \emph{synthesize} the type of the elimination, and then insist that the two candidate types match \emph{exactly} (i.e., that they are $\alpha$-equivalent, which is just syntactic identity for a de Bruijn representation), rather than up to some (so far unspecified, in any case) notion of conversion.

Now, some of you may wonder why we do not synthesize the types for $\type$ and $\PI xS T[x]$, given that they clearly inhabit $\type$ if they inhabit anything at all. While that works for this system with one universe, it is unstable with respect to overloading: type checking allows us to overload introduction forms for distinct types, including the overloading of type formation constructs within different universes. Such overloading rules out type synthesis but has no impact on type checking. The fix to restore normalization exactly requires us to introduce multiple universes and overload the function type constructor, so let us stick with type checking for these things.

Meanwhile, the heart of type synthesis is the variable rule, extracting the type of the head of an elimination from the context.
\[
\Axiom{\SYN{\Gamma,x\hb S,\Delta}{x}{S}}
\]
The synthesized type comes directly from the input context which is presumed valid, and must thus confirm that $S$ is indeed a type, which is what we must guarantee.

For application, we \emph{synthesize} the type of the function (which is being eliminated), then \emph{check} that it is being eliminated in a manner consistent with its type.
We can get most of the way round before we run into trouble:
\[
\Rule{\SYN\Gamma f {\PI xS T[x]} \quad \CHK\Gamma Ss}
     {\SYN\Gamma{f\:s}{?}}
\]
Synthesizing the type (and we are guaranteed that it is a type) of the function, we may extract the (by inversion also a type) domain and use it to check the argument. However, when we come to give the output type of the whole application, the wheel comes off. We may be sure that $\CHK{\Gamma,x\hb S}\type{T[x]}$, and we surely want to give a type by choosing a suitable replacement for that $x$, but we may not give $T[s]$, as $s$ is not in the same syntactic category as $x$. Indeed, substituting such an $s$ for $x$ might create $\beta$-redexes which we have thus far excluded.

One possibility is to seek a derived notion of \emph{hereditary}
substitution~\cite{DBLP:conf/types/WatkinsCPW03} which computes out
any such $\beta$-redexes on the fly, restoring syntactic
legitimacy. However, we know that any such operation will not be well
defined: it can be persuaded to require the normalization of
anything, and this language is surely non-normalizing. We might deal
with the partiality of hereditary substitution by defining it
\emph{relationally}, but that is only to postpone the problem: in a
non-normalizing calculus, hereditary substitution is not stable under
hereditary substitution, as we can substitute an inert variable with
just the term required to kick off an infinite
computation. Correspondingly, the key stability property that drives
the proof of type preservation will fail.

We had better think it out again.


\section{Radicals Recover Small-Step Behaviour}

When we come to instantiate $T[x]$ with $s$, we do at least know $S$, the type of $s$. We can reacquire the ability to substitute if we extend the language of \emph{eliminations} with type-annotated terms, which I call \emph{radicals} by analogy with the chemical notion.
\[
e,f ::= \ldots \;||\; t\hb T
\]

We should also add radicals to the declaration of |Tm| and extend |/| accordingly.\\
\usebox{\radbox}\vspace*{ -0.2in}\\
\usebox{\radactbox}\\

The associated typing rule allows us to change direction in the other direction from embedding, at the cost of making the intermediate type explicit: the type we synthesize is exactly the type we supply.
\[\Rule{\CHK\Gamma\type T\quad \CHK\Gamma Tt}
       {\SYN\Gamma{t\hb T}T}
\]

We may now complete the application rule:
\[
\Rule{\SYN\Gamma f {\PI xS T[x]} \quad \CHK\Gamma Ss}
     {\SYN\Gamma{f\:s}{T[s\hb S]}}
\]

However, we have opened a further door at the same time. A radical can stand at the head of an elimination, taking its type not from the context but from its own explicit annotation. In particular, we can form something which looks a touch like a $\beta$-redex:
\[
(\LA xt[x] : \PI xS T[x])\:s
\]
Inversion tells us that for this to be well typed in some context $\Gamma$, we must know the following:
\[
\CHK\Gamma\type S \qquad
\CHK{\Gamma,x\hb S}\type{T[x]} \qquad
\CHK{\Gamma,x\hb S}{T[x]}{t[x]} \qquad
\CHK\Gamma Ss
\]
and have synthesized the type $T[s\hb S]$ for the whole application
We can thus give this would-be $\beta$-redex a computational behaviour:
\[
(\LA xt[x] : \PI xS T[x])\:s \;\leadsto_\beta\; t[s\hb S]:T[s\hb S]
\]
Note that, on the one hand, the type annotation on the contractum is essential (for the redex is an elimination, hence so must be its contractum), but on the other hand, the type annotation is helpful: a radical at a function type has `reacted' to release radicals at both domain and range types (which might be function types, causing further computation). It is easy to check (once we have established stability under substitution), that
\[
\CHK\Gamma\type{T[s\hb S]} \qquad
\CHK\Gamma{T[s\hb S]}{t[s\hb S]}
\]
and hence the reduct gives us the same type as the contractum.

However, as soon as a radical is being embedded rather than eliminated, its computational role is finished, so the type annotation is no longer required. We acquire the $\upsilon$-reduction scheme
\[
\el{t\hb T} \;\leadsto_\upsilon\; t
\]
That is, an introduction form is activated by annotation with its type, allowing its elimination form to compute, then eventually (we hope) deactivated once all the eliminations in its spine have been completed. In a \emph{predicative} system, the types get visibly smaller (in some suitably ramified sense) at each step. In our impredicative, indeed inconsistent system, we have no such guarantee. However, we must have checked (in the relevant context $\Gamma$) that $\CHK\Gamma\type T$ $\CHK\Gamma Tt$, allowing us to check both
\[
\CHK\Gamma T{\el{t\hb T}} \qquad \CHK\Gamma Tt
\]
again suggesting we have some chance of achieving type preservation.

But there's a but. Now that we have introduced a small-step computation system, we must ensure that typing respects it. Let us write an unlabelled $\leadsto$ for small-step reduction---the closure of either contraction scheme under all contexts---and add the \emph{pre-} and \emph{post-computation} rules, respectively,
\[
\Rule{T\leadsto T'\quad \CHK\Gamma{T'}t}
     {\CHK\Gamma Tt}
\qquad
\Rule{\SYN\Gamma eS \quad S\leadsto S'}
     {\SYN\Gamma e{S'}}
\]
These rules obey the requirements of our mode-religion if we consider reduction to be moded
\[
\mbox{input}\leadsto\mbox{output}
\]
even though reduction is not deterministic. There is often a choice as to which redex to contract.

I have chosen the orientation of these rules carefully. We may precompute a type before checking it, e.g., ensuring that a type has the form of a function type before checking an abstraction; we may post-compute the type of a function being applied, so that it reduces to the form of a function type, allowing us to check the argument.

If you are paying attention, you will have spotted a catch or two. These two rules, governing the interaction of computation and types, are not syntax-directed, just as the conversion rule was not in the 1971 system. They can be invoked anytime, which also seems to derail or at least complicate the informal appeals to inversion in the arguments above. We shall need to work a little to make sure we have not introduced a problem as we try to establish type preservation. \textbf{Can we show systematically that it is enough to establish type preservation for the contraction schemes in the absence pre and post, by making use of confluence and modes? I suspect so.}

The other catch is that we acquire some type annotation flotsam in our normal forms. The annotation in
\[
  (\el y : \PI xS T[x])\:s
\]
will not compute away either by $\beta$ or by $\upsilon$. We might consider simplifying $\el e : T$ to $e$,
but that would give us nasty critical pairs; we might insist that such an $e$ have a free variable at its head, but that property is not stable under substitution. We shall do neither of these things and yet come to no harm.
However, we might find it frustrating if such flotsam makes types incompatible, so let us return to this question later.

One positive, however, is that there is no longer any \emph{backward} computation in our calculus. The anarchic 1971 conversion rule has become the rather more controlled observation that the following is now admissible (by recursion on reduction sequences):
\[\Rule{\SYN\Gamma eS \quad S\leadsto^\ast R \quad T\leadsto^\ast R}
       {\CHK\Gamma T{\el e}}
\]
A synthesized type is good for a checked type if they have a common reduct, which is just as good as convertibility in a confluent system.

The bidirectional system offers us fewer opportunities to deploy
convertibility as opposed to reduction. Here, we rely on a crucial
property brought to prominence by Geuvers~\cite{geuvers:dunnoyet}. If
a term is \emph{convertible} with a canonical form (with a given head
constructor and whatever substructures), then it \emph{reduces} to a
canonical form (with that constructor and convertible corresponding
substructures). That is, reduction is good for conversion when seeking
to establish that a type is $\type$, or that it is $\PI xS T[x]$, as
happens both when checking types for introductions and when
synthesizing types for eliminations.


\section{Formalizing Reduction}

To formalize the typing rules, we must first formalize reduction. We may give
an inductive family capturing exactly \emph{one-step} reduction, with a base
constructor for each contraction scheme and step constructors for each possible
contextual closure.

%format ~> = "\D{\leadsto}"
%format _~>_ = _ ~> _
%format beta = "\C{\upbeta}"
%format upsilon = "\C{\upupsilon}"
%format PiL = Pi "_{\C{L}}"
%format PiR = Pi "_{\C{R}}"
%format apL = "\C{ap}_{\C{L}}"
%format apR = "\C{ap}_{\C{R}}"
%format raL = "\C{ra}_{\C{L}}"
%format raR = "\C{ra}_{\C{R}}"
\begin{code}
data _~>_ {n : Nat} : forall {sort} -> Tm n sort -> Tm n sort -> Set where

  beta     :  forall {t T s S} ->
              ((la t :: Pi S T) $ s) ~> ((t :: T) /s (ox oi (s :: S)))

  upsilon  :  forall {t T} ->
              em (t :: T) ~> t

  PiL      :  forall {S S' T} ->  S ~> S'  -> Pi S T ~> Pi S' T
  PiR      :  forall {S T T'} ->  T ~> T'  -> Pi S T ~> Pi S T'
  la       :  forall {t t'} ->    t ~> t'  -> la t ~> la t'
  em       :  forall {e e'} ->    e ~> e'  -> em e ~> em e'
  apL      :  forall {f f' s} ->  f ~> f'  -> (f $ s) ~> (f' $ s)
  apR      :  forall {f s s'} ->  s ~> s'  -> (f $ s) ~> (f $ s')
  raL      :  forall {t t' T} ->  t ~> t'  -> (t :: T) ~> (t' :: T)
  raR      :  forall {t T T'} ->  T ~> T'  -> (t :: T) ~> (t :: T')
\end{code}

Note that even though the definition is nondeterministic, it is
consistent with the mode assignment \emph{input} |~>| \emph{output},
with \emph{patterns} for the inputs of conclusions and the outputs of
premises, and \emph{expressions} (where we may use substitution) for
the outputs of conclusiosn and the inputs of premises.
As a consequence, it is straightforwardly stable under substitution.

\begin{code}
_/~>_ : forall {n m sort}{t t' : Tm n sort} -> t ~> t' -> (sg : n >> m) ->
         (t /s sg) ~> (t' /s sg)
beta {t = t}{T = T}{s = s}{S = S} /~> sg
  with beta {t = t /s os sg}{T = T /s os sg}{s = s /s sg}{S = S /s sg}
... | b rewrite SBSTSBSTSBST.compAct (t :: T) (ox oi (s :: S)) sg
              | SBSTSBSTSBST.compAct (t :: T) (os sg) (ox oi ((s :: S) /s sg))
              | oxSbst (t :: T) oi (s :: S) sg
              | sbstId sg
              | idSbst sg
              = b
upsilon /~> sg = upsilon
PiL tt' /~> sg = PiL (tt' /~> sg)
PiR tt' /~> sg = PiR (tt' /~> os sg)
la tt' /~> sg = la (tt' /~> os sg)
em tt' /~> sg = em (tt' /~> sg)
apL tt' /~> sg = apL (tt' /~> sg)
apR tt' /~> sg = apR (tt' /~> sg)
raL tt' /~> sg = raL (tt' /~> sg)
raR tt' /~> sg = raR (tt' /~> sg)
\end{code}

\newpage
\appendix


\section{Syntax, Formally}

\newcommand{\cns}{\mathsf{cn}}
\newcommand{\elm}{\mathsf{el}}
\newcommand{\bnd}[1]{\purple{[\black{#1}]}}
\newcommand{\bv}[1]{\V{#1}.\,}
\newcommand{\pic}{\blue{\Uppi}}
\newcommand{\lac}{\red{\uplambda}}
\newcommand{\elc}{\green{\upupsilon}}
\newcommand{\apc}{\green{\upalpha}}
\newcommand{\tyc}{\green{\upepsilon}}

\textbf{There's an inevitable dilemma about whether to do this explicitly in Agda.}

When we model a syntax, an `object language', its terms can be classified into object \emph{sorts}, $\iota$. (Sometimes, we may even identify the notion of `sort' with the object language's notion of `type', but that is far from crucial.) The object sorts for our language are constructions and eliminations.
\[
  \iota \quad::=\quad \cns \quad||\quad \elm
\]
To account for variable binding, we construct a \emph{meta}-level notion of \emph{kind}, $\kappa$, by closing sorts under what might look to the casual observer like a function space, but is most emphatically weaker than that.
\[
  \kappa \quad::=\quad \iota \quad||\quad \bnd\kappa \kappa'
\]
The kind $\bnd\kappa \kappa'$ means `terms in $\kappa$ which bind a variable of kind $\kappa$', not `functions from terms of kind $\kappa$ to terms of kind $\kappa'$'. The only functions thus represented are those which
\emph{substitute} the bound variable: functions which do the common functional thing of inspecting their input are absolutely ruled out.

\newcommand{\Sg}{\Upsigma}
For each \emph{sort}, $\iota$, we must give the \emph{signature}, $\Sg(\iota)$, of its constructs, specifying the \emph{kind} of each subterm. Here, we may give this translation of our earlier grammar, omitting variables (which are not a notion specific to this theory), and giving explicit prefix forms for the remainder.
\[\begin{array}{rrl}
\Sg(\cns) & ::= & \type \\
          &   || & \pic\; \cns\; \bnd\elm\cns \\
          &   || & \lac\; \bnd\elm\cns \\
          &   || & \elc\;\elm \medskip \\
\Sg(\elm) & ::= & \apc\;\elm\;\cns \\
          &   || & \tyc\;\cns\;\cns
\end{array}\]
\newcommand{\Sgc}[2]{\Sg^{\mathsf{c}}(#1,#2)}
For any kind-indexed family of sets $T(\kappa)$ (for `term'), we may give the set of constructions, $\Sgc T\iota$
\[
  \Sgc T\iota = \{c\;\vec{t} \;||\; c\:\vec{\kappa}\in \Sg(\iota), \forall i.\,t_i\in T(\kappa_i)\}
\]
These are prefix-Polish terms with $T$s as subterms. Our construction of terms will instantiate $T$ recursively,
`tying the knot'. We should note that $\Sgc-\iota$ is a functor from the category of kind-indexed sets with kind-preserving
functions to the category of sets, acting structurally on the subterms.

Now let us define scoped and kinded syntax.

\subsection{The Category of Scopes and Thinnings}

A \emph{scope} is a list of kinds, growing on the right:
\[
\gamma, \delta, \zeta \quad::=\quad \EC \quad||\quad \gamma,\kappa
\]
It will often be convenient to give kinds in \emph{spine} form, $\bnd\delta\iota$, loading all the bound variable kinds into a scope, leaving an object sort. These scopes form the objects of a category.

The morphisms of this category are the \emph{thinnings} ($\theta, \phi$) between scopes, $\gamma\le\delta$:
\[
\Axiom{\EC \in \EC\le\EC}
\qquad
\Rule{\theta \in \gamma\le\delta}
     {\theta,\kappa \in (\gamma,\kappa)\le(\delta,\kappa)}
\qquad
\Rule{\theta \in \gamma\le\delta}
     {\theta\dag_\kappa \in \gamma\le(\delta,\kappa)}
\]

By careful choice of notation, we have identity thinnings.
\[
\gamma in \gamma\le\gamma
\]

Composition of thinnings (which I write diagramatically) is definable:
\[
\Rule{\theta\in \gamma_0\le\gamma_1 \quad \phi\in\gamma_1\le\gamma_2}
     {\theta;\phi \in \gamma_0\le\gamma_2}
\qquad
\begin{array}[t]{rcl}
\EC;\EC & = & \EC \\
(\theta,\kappa);(\phi,\kappa) & = & (\theta;\phi),\kappa \\
(\theta\dag);(\phi,\kappa)    & = & (\theta;\phi)\dag \\
\theta;(\phi\dag)             & = & (\theta;\phi)\dag \\
\end{array}
\]
It is easy to check that the categorical laws hold: if $\theta\in\gamma\le\delta$, then
\[
\gamma;\theta \;=\; \theta \;=\; \theta;\delta
\]
and
\[
(\theta_0;\theta_1);\theta_2 \;=\; \theta_0;(\theta_1;\theta_2)
\]
Moreover, our definitions have ensured that $-,\kappa$, acting as it does both on scopes and on thinnings between those scopes, is a \emph{functor}.

\newcommand{\tcs}{\overline}
\newcommand{\tct}{\widehat}
Every thinning $\theta\in\gamma\le\delta$ induces a complementary scope $\tcs\theta$ and a complementary
thinning $\tct\theta\in\tcs\theta\le\delta$ inverting the selection of scope items included by $\theta$:
\[\begin{array}{rcl@@{\qquad}rcl}
\tcs\EC & = & \EC & \tct\EC & = & \EC \\
\tcs{\gamma,\kappa} & = & \tcs\gamma & \tct{\gamma,\kappa} & = & \tct\gamma\dag_\kappa \\
\tcs{\gamma\dag_\kappa} & = & \tcs\gamma,\kappa & \tct{\gamma\dag_\kappa} & = & \tct\gamma,\kappa
\end{array}\]
Note that $\tct\gamma\in\EC\le\gamma$ makes $\EC$ the initial object in the category.

\newcommand{\fae}{\leftarrow}
Let us write $\kappa\fae\gamma$ for the set of \emph{singleton} thinnings $(\EC,\kappa)\le\gamma$. These
look like
\[
\EC\dag\ldots\dag,\kappa\dag\ldots\dag
\]
selecting exactly one from however many, so they make a good representation of de Bruijn variables. Let us refer to such things by Roman letters ($x$, $y$).

Of course, as variables are thinnings, for any such $x\in\kappa\fae\gamma$, we may construct $\tct x \in \tcs x\le\gamma$ and observe that every variable in $\kappa'\fae\gamma$ is either $x$ (in which case $\kappa=\kappa'$) or some $y;\tct x$, where $y\in \kappa'\fae\tcs x$. Let us consider ourselves entitled to treat $x$ and
$y;\tct x$ as a valid covering of patterns for $\kappa'\fae\gamma$.


\subsection{Terms with Schematic Variables}
\newcommand{\Sgt}[2]{\Sg^{\mathsf{t}}(#1,#2)} 
\newcommand{\Sgs}[2]{\Sg^{\mathsf{s}}(#1,#2)}
\newcommand{\sss}{\mathit{s\!s}} 
The \emph{terms} $\Sgt\gamma\kappa$ of kind $\kappa$ in scope $\gamma$, and the \emph{spines}
$\Sgs\gamma\delta$ for scope $\delta$ in scope $\gamma$, are given thus:
\[\begin{array}{rrl}
\Sgt\gamma{\bnd\kappa\kappa'} & = & \Sgt{(\gamma,\kappa)}{\kappa'} \\
\Sgt\gamma{\iota} & = & \Sgc{\Sgt\gamma-}\iota \\
                  & \cup & \{x[\sss] \;||\; x\in\bnd\delta\iota\fae\gamma,\; \sss\in\Sgs\gamma\delta\} \medskip \\
\Sgs\gamma\EC & = & \{\EC\} \\
\Sgs\gamma{(\delta,\kappa)} & = & \{\sss,t \;||\; \sss\in \Sgs\gamma\delta,\; t\in \Sgt\gamma\kappa\}
\end{array}\]
When a variable has object sort, $x\in\iota\fae\Gamma$, its argument spine is empty, and we may abbreviate the term $x[\EC]$ to plain old $x$. The idea is that to construct a term of a given kind, we bring all of its bound variables into scope, then give either a construction allowed by the signature or a variable suitably instantiated.

This definition is designed to ensure that $\Sgt-\kappa$ and $\Sgs-\delta$ are functors from the category of scopes and thinnings to the category of sets and functions. As you can see, the scope $\gamma$ occurs only to the right of $\le$ in the definition, allowing thinning to act by composition. Meanwhile, the only time the scope changes is to bind a variable with $-,\kappa$ which acts functorially on thinnings. Let us write $t\theta$ and $\sss\theta$ for the actions of thinning $\theta$ on term $t$ and spine $\sss$, respectively.

For human readability, let us continue to mark the growing of the scope in example terms by binding \emph{names}, $\bnd x\mathit{term}$. When we use a variable $\V t$ of kind $\bnd\delta\iota$, we must
instantiate it as $\V t[\sss]$ with a spine $\sss$ for the scope $\delta$ given by its kind. We may write $\V t$ for $\V t[]$ when $\V t$'s kind
makes it of object sort without further instantiation. The $\beta$-contraction scheme looks like this:
\[
\apc\;(\tyc\;(\lac\;\bv xt[\V x])\;(\pic\:\V S\:\bv x\V T[\V x]))\;\V s \;\leadsto_\beta\;
\tyc\;\V t[\tyc\;\V s\;\V S]\;\V T[\tyc\;\V s\;\V S]
\]
The point is that the \emph{schematic} variables in the presentation of the contractions are now directly represented as variables in our
syntax. Some of them have kinds which are not just object sorts, indicating that they bind variables and must be instantiated in the construction of object terms.


\subsection{Parallel Action, Hereditary Substitution}

We shall need to do more to terms than mere thinning. In particular, we shall need to instantiate variables with terms of appropriate kind. For example, when we instantiate $\beta$-contraction, we shall need to replace $\V t$ with some actual term that binds a variable, putting
$\tyc\;\V s\;\V S$ in the place of that bound variable. Substitution begets substitution: will it ever end? We know from Watkins et al.~\cite{DBLP:conf/types/WatkinsCPW03} that hereditary substitution for the logical framework amounts to $\beta\eta$-long-normalization for simply typed $\lambda$-calculus, and thus terminates satisfactorily. Andreas Abel~\cite{DBLP:conf/mpc/000106} used Agda's \emph{sized types}
to implement \emph{simultaneous} (replacing all variables in scope) hereditary substitution for simply typed $\lambda$-calculus. I edited the volume in which that paper appears, so it should not be a surprise that an anonymous reviewer offered an implementation of \emph{single} (replacing just one variable in scope) hereditary substitution without sized types, using only \emph{structural recursion} (on the type of the substituted variable). The grapevine being what it is, that program was the seed for C. Keller and Altenkirch's normalization formalization, with full soundness and completeness proofs~\cite{DBLP:conf/icfp/KellerA10}.

The usual approach is to make sure thinning works (which is clear from our construction) and then use thinning to manage the de Bruijn shifting required for substitution (when a term is used in a larger scope than the scope that it came from): it has long been observed~\cite{Goguen97candidatesfor,DBLP:phd/ethos/McBride00} that thinning (or renaming, more generally) and substitution can be implemented by instantiating the parameters of \emph{one} structural recursion on terms in \emph{two} different ways (accounting for how to act on a variable and how to go under a binder).

Here, then, is how to implement \emph{simultaneous} (no need to focus on one variable!) hereditary substitution (or rather, something slightly more general) for our simply kinded calculus by structural recursion on \emph{scopes} (no sized types!) in one pass (no need for a prior implementation of thinning!).
\newcommand{\act}[3]{#1 \left[#2\right> #3}

The key is to define a notion of \emph{parallel action}, explaining how to either thin or substitute each variable. Read $\act\gamma\zeta\delta$ as an action mapping $\gamma$-terms to $\delta$-terms by substituting some subscope $\zeta\le\gamma$ and thinning the rest.
\[
\Axiom{\EC \in \act\EC\EC\EC}
\qquad
\Rule{\sigma \in \act\gamma\zeta\delta}
     {\sigma,\kappa \in \act{(\gamma,\kappa)}\zeta{(\delta,\kappa)}}
\qquad
\Rule{\sigma \in \act\gamma\zeta\delta}
     {\sigma\dag_\kappa \in \act\gamma\zeta{(\delta,\kappa)}}
\qquad
\Rule{\sigma \in \act\gamma\zeta\delta\quad s\in\Sgt\delta\kappa}
     {\sigma/s \in \act{(\gamma,\kappa)}{\zeta,\kappa}\delta}
\]
The first three rules tell us that every thinning is an action; the fourth tells us that actions can also substitute.
Crucially, given some $\theta\in\delta_0\le\delta$ and some $\sss\in\Sgs\delta\zeta$, we may construct
$\theta+\sss\in\act{\delta_0,\zeta}\zeta\delta$, just by copying $\theta$ to get an action in $\act{\delta_0}\EC\delta$,
then adding the terms from the spine, extending the source scope to $\delta_0,\zeta$ and the substitutive subscope to $\zeta$,
keeping the target at $\delta$ (which is the scope of the terms in the spine).

Now let us define
\newcommand{\vact}{\mathsf{vact}}
\[\begin{array}{c}
\Rule{t\in\Sgt\gamma\kappa\quad \sigma\in\act\gamma\zeta\delta}
     {t\{\kappa || \zeta\}\sigma\in\Sgt\delta\kappa}
\qquad
\Rule{\sss\in\Sgs\gamma{\delta'}\quad \sigma\in\act\gamma\zeta\delta}
     {\sss\{\delta' || \zeta\}\sigma\in\Sgs\delta{\delta'}}
\\
\Rule{x\in \bnd{\zeta_x}\iota\fae\gamma \quad \sigma\in\act\gamma\zeta{\delta_0} \quad \theta\in\delta_0\le\delta \quad
      \sss\in\Sgs\delta{\zeta_x}}
     {\vact\{\zeta\}\:x\:\sigma\:\theta\:\sss \in \Sgt\delta\iota}
\end{array}\]
In casual usage, I shall omit the details given in $\{\ldots\}$, but for purposes of definition, it is crucial to observe them,
as they justify the recursion.
\[\begin{array}{r@@{}c@@{}lcl@@{\qquad}l}
t&\{ \zeta || \bnd\kappa\kappa'\}&\sigma & = & t\{\zeta || \kappa'\}(\sigma,\kappa) \\
c\:\vec{t}&\{\zeta || \iota\}&\sigma & = & c\:\vec{t}\{\zeta || -\}\sigma & \mbox{functoriality of $\Sgc-\iota$}\\
x[\sss]&\{\zeta || \iota\}&\sigma & = & \vact\{\zeta\}\:x\:\sigma\:\delta\:(\sss\{\zeta||\zeta_x\}\sigma)
  & \mbox{where}\;\sss\in \Sgs\gamma{\zeta_x} \medskip \\
\vact\{\zeta\}\;&x\:&(\sigma\dag_\kappa)\:\theta\;\sss & = &
  \vact\{\zeta\}\:x\:&\sigma\:(\dag_\kappa;\theta)\;\sss \\
\vact\{\zeta\}\:&(x\dag_\kappa)\:&(\sigma\dag,\kappa)\:\theta\;\sss & =
   &\vact\{\zeta\}\:x\:\sigma\:(\dag_\kappa;\theta)\;\sss \\
\vact\{\zeta,\kappa\}\:&(x\dag_\kappa)\:&(\sigma/t)\:\theta\;\sss & =
   &\vact\{\zeta\}\:x\:\sigma\:\theta\;\sss \\
\vact\{\zeta\}\:&(x,\kappa)\:&(\sigma\dag,\kappa)\:\theta\;\sss & =
   &((\tct{\,},\kappa);\theta)[\sss] & \mbox{act by thinning}\\
\vact\{\zeta,\bnd{\zeta_x}\iota\}\:&(x,\bnd{\zeta_x}\iota)\:&(\sigma\dag/t)\:\theta\;\sss & =
   & t\{\zeta_x||\iota\}(\theta+\sss) & \mbox{act by substituting}\medskip\\
\EC & \{\zeta || \EC\} & \sigma & = & \EC\\
(\sss,s) & \{\zeta || \delta',\kappa\} & \sigma & = & \sss \{\zeta || \delta'\}\sigma, s\{\zeta || \kappa\}\sigma \\
\end{array}\]
The recursion is lexicographic, first on $\zeta$, then on terms. Thinning an action to go under a binder does not alter $\zeta$. As soon as we hit $x[\sss]$, we substitute the spine immediately, then we search the action, $\sigma$ to find the fate of $x$. The $\vact$ operation tears down $\sigma$ and $x$, building up a thinning, $\theta$. As soon as the variable we are looking for is found on top, we must either thin it and reattach the spine, or substitute it, acting hereditarily on its image with an action constructed from the spine. As $\vact$ searches, $\zeta$ is torn down, and in the hereditary substitution case, the substituted scope for the new substitution sits within the kind of the substituted variable.


\bibliographystyle{plainnat}
\bibliography{TypesNi}

\end{document}
