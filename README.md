Riesz Logic
===========

Implementation of the hypersequent calculus HR introduced in the article "Proof Theory of Riesz Spaces and Modal Riesz Spaces" (https://arxiv.org/abs/2004.11185).

### Terms
* *term.v* : Definitions  ad notations regarding terms of Riesz spaces (with positive real scalars as weights). The type corresponding to those terms is **term**.
* *Rterm.v* : Definitions and notations regarding terms of Riesz spaces (with any real scalars as weights). The type corresponding to those terms is **Rterm**.


### Semantics
* *semantic.v* : Definition of equational reasoning over the terms defined in *term.v*. The type corresponding to the equality between two **terms** is **eqMALG** and we note **A === B** for **eqMALG A B**. The equalities and properties regarding Riesz spaces are in these files (ex Lemma 2.14 in subsection 2.1 of the article).
* *Rsemantic.v* : The equivalent version of *semantic.v* corresponding to *Rterm.v*. **eqMALG** is here **R_eqMALG** and we note **A =R= B** for **R_eqMALG A B**.
* *semantic_Rsemantic_eq.v* : Definition of **NNF** (a function translating **Rterm** to **term**) and **toRterm** (a function translating a **term** into a **Rterm**). Properties regarding **NNF* and **toRterm** as well as proof of the equivalence between **===** and **=R=**.
* *interpretation.v* : Translation of a hypersequent into a **term** as well as properties regarding this translation.

### HR
* *hseq.v* : Implementation of the HR system as well as proofs of the lemmas of subsection 3.3 of the article.
* *soundness.v* : Proof of soundness (subsection 3.4).
* *completeness.v* : Proof of completeness (subsection 3.5).

### Aux
* *Rpos.v* : Definition of a positive real number and the operations on positive real numbers (addition, ...). Some properties over positive real numbers.
* *tactics.v* : Some tactics used in the other files, for instance a tactic that apply every possible logical rules to get an atomic hypersequent.