# Bi71
being a bidirectional reformulation of Martin-Löf's 1971 type theory

The `agda-v1` directory contains the formalisation, using Agda 2.5.2.

`Basics` has the definitions of numbers, pairs, equality, etc (fixing notation)

`OPE` (importing `Basics`) has the definitions of order-preserving embeddings (aka "thinnings"), being the "renamings" which matter

`Star` (importing `Basics`) develops the basic theory of reflexive-transitive closure, including functorial and monadic operations, but also the diamond lemma

`Env` (importing `Basics`, `OPE`) has the definition of environments (aka "snoc-vectors"), and their interaction with thinnings

`Tm` (importing `Basics`, `OPE`) has the syntax of terms and the notion of term "actions", identity and composition, with thinnings being a case in point

`Subst` (importing `Basics`, `OPE`, `Env`, `Tm`) makes gives environments a substitution action and establishes identity and all relevant compositions (with thinnings before or after, with other substitutions)

`RedNorm` (importing `Basics`, `OPE`, `Star`, `Env`, `Tm`, `Subst`) defines ordinary one-step reduction and what it is to be in normal form (excluding some configurations which should be impossible, e.g., badly labelled lambdas)

`Par` (importing `Basics`, `OPE`, `Star`, `Env`, `Tm`, `Subst`, `RedNorm`) defines parallel reduction and establishes that it is stable with respect to thinning and substitution; there are also two handy inversion lemmas about reducing from a canonical type

`Dev` (importing `Basics`, `OPE`, `Star`, `Env`, `Tm`, `Subst`, `Par`) equips terms with their notion of "development" (maximal parallel reduction) and proves (1) that development computes a parallel reduct, (2) that any parallel reduct parallel-reduces to the development; hence confluence (by the diamond lemma)

`Typing` (importing `Basics`, `OPE`, `Star`, `Env`, `Tm`, `Subst`, `Par`) gives the typing rules and proves they are stable under thinning, then under substitution

`Preservation` (importing `Basics`, `OPE`, `Star`, `Env`, `Tm`, `Subst`, `Par`, `Dev`, `Typing`) gives the proof of type preservation

`Progress` (importing `Basics`, `Star`, `Tm`, `RedNorm`, `Par`, `Typing`) gives the proof that a well typed term is either normal or takes a step
