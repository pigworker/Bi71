# Bi71
being a bidirectional reformulation of Martin-Löf's 1971 type theory

`Basics` has the definitions of numbers, pairs, equality, etc (fixing notation)

`OPE` (importing `Basics`) has the definitions of order-preserving embeddings (aka "thinnings"), being the "renamings" which matter

`Env` (importing `Basics`, `OPE`) has the definition of environments (aka "snoc-vectors"), and their interaction with thinnings

`Tm` (importing `Basics`, `OPE`) has the syntax of terms and the notion of term "actions", identity and composition, with thinnings being a case in point

`Subst` (importing `Basics`, `OPE`, `Env`, `Tm`) makes gives environments a substitution action and establishes identity and all relevant compositions (with thinnings before or after, with other substitutions)

`Par` (importing `Basics`, `OPE`, `Env`, `Tm`, `Subst`) defines parallel reduction and establishes that it is stable with respect to thinning and substitution

`Star` (importing `Basics`) develops the basic theory of reflexive-transitive closure, including the diamond lemma

`Dev` (importing `Basics`, `OPE`, `Env`, `Tm`, `Subst`, `Par`, `Star`) equips terms with their notion of "development" (maximal parallel reduction) and proves (1) that development computes a parallel reduct, (2) that any parallel reduct parallel-reduces to the development; hence confluence

`Typing` (importing `Basics`, `OPE`, `Env`, `Tm`, `Subst`, `Par`) gives the typing rules

`Preservation` (importing `Basics`, `OPE`, `Env`, `Tm`, `Subst`, `Par`, `Dev`) gives the (currently incomplete) proof of type preservation
