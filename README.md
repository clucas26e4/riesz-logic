Riesz Logic
===========

Implementation of the hypersequent calculus HR introduced in the article "Proof Theory of Riesz Spaces and Modal Riesz Spaces" (https://arxiv.org/abs/2004.11185).

## How to compile
There are four ways to compile the files in the depository:

* make : compile all files.
* make doc : compile all files and generate the documentation.
* make hr : compile only the files in Utilities and hr.
* make hmr : compile only the files in Utilities and hmr.

## Notations used in the Coq files.

* **===** or **=R=**
* **<==** or **<R=**
* **/\S** or **/\R**
* **\/S** or **\/R**
* **\*S** or **\*R**
* **+S** or **+R**
* **-S** or **-R**

## The structure of the depository
There are three folders in the depository:

* Utilities:
* hr:
* hmr:

### H(M)R
The files in hr and hmr are quite similar (because the structure of Section 3 and Section 4 of the article are also very similar), here are the files that are in both of those folders.

#### Terms
* *term.v* : Definitions  ad notations regarding terms of Riesz spaces (with positive real scalars as weights). The type corresponding to those terms is **term**.
* *Rterm.v* : Definitions and notations regarding terms of Riesz spaces (with any real scalars as weights). The type corresponding to those terms is **Rterm**.


#### Semantics
* *semantic.v* : Definition of equational reasoning over the terms defined in *term.v*. The type corresponding to the equality between two **terms** is **eqMALG** and we note **A === B** for **eqMALG A B**. The equalities and properties regarding Riesz spaces are in these files (ex Lemma 2.14 in subsection 2.1 of the article).
* *Rsemantic.v* : The equivalent version of *semantic.v* corresponding to *Rterm.v*. **eqMALG** is here **R_eqMALG** and we note **A =R= B** for **R_eqMALG A B**.
* *semantic_Rsemantic_eq.v* : Definition of **NNF** (a function translating **Rterm** to **term**) and **toRterm** (a function translating a **term** into a **Rterm**). Properties regarding **NNF* and **toRterm** as well as proof of the equivalence between **===** and **=R=**.
* *interpretation.v* : Translation of a hypersequent into a **term** as well as properties regarding this translation.

#### Proof system
* *hseq.v* : Definitions of sequents and hypersequents and some properties (like atomicity and complexity), as well as technical lemmas required to manipulate them in Coq.
* *h(m)r.v* : Definitions of the H(M)R system and some basic lemmas.
* *tech_lemmas.v* : Implementation of the lemmas in Section 3.3/4.2.
* *soundness.v* : Proof of soundness (Section 3.4/4.3)).
* *completeness.v* : Proof of completeness (Section 3.5/4.4).
* *invertibility.v* : Proof of the CAN-free invertibility of the logical rules (Section 3.6/4.5)
* *M_elim.v* : Proof of the M elimination (Section 3.7/4.6)
* *can_elim.v* : Proof of the CAN elimination (Section 3.8/4.7)
* *preproof.v* (for HMR only):

#### Aux
* *tactics.v* : Some tactics used in the other files, for instance a tactic that apply every possible logical rules to get an atomic hypersequent.
* *h(m)r_perm_lemmas.v* : Technical construction and lemmas used to help manipulate lists of lists (instead of multisets of multisets like in the article). For instance, they help deal with the exchange rule cases in the proofs by induction.
* *lambda_prop_tools.v* : some tools to make the proofs of Lemma ???????? easier to implement.

### Utilities
* *Rpos.v* : definition of positive real numbers and some lemmas used to manipulate them.
* *riesz\_logic\_List\_more.v* : additionnal lemmas for lists.
* *FOL_R.v* : definition of First Order Logic over real numbers.
* *lt_nat2.v* : definition of a well-founded order on Nat².
