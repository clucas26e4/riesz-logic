
COQ = coqc -R $(OLLIBSDIR) '' -R $(UTILDIR) ''
COQDOC = coqdoc -g

VFILES = $(wildcard *.v)

%.vo: %.v
	$(COQ) $<

%.glob: %.vo
	@true

%.html: %.v %.vo
	$(COQDOC) $<


doc: $(VFILES:.v=.glob)
	$(COQDOC) -toc $(VFILES)

clean:
	rm -f $(VFILES:.v=.vo)
	rm -f .*.aux
	rm -f *.crashcoqide
	rm -f *.glob
	rm -f *.html
	rm -f coqdoc.css
	rm -f lia.cache
	rm -f .lia.cache

.PHONY: clean
.PRECIOUS: %.vo %.glob


OLLIBSDIR = ../../ollibs
UTILDIR = ../Utilities

.DEFAULT_GOAL := all

all: ollibs utilities $(VFILES:.v=.vo)

ollibs:
	cd $(OLLIBSDIR) && $(MAKE)

utilities:
	cd $(UTILDIR) && $(MAKE)

include $(OLLIBSDIR)/ollibs.mk

term.vo : term.v $(UTILDIR)/Rpos.vo
semantic.vo : semantic.v $(UTILDIR)/Rpos.vo term.vo
hseq.vo : hseq.v $(UTILDIR)/Rpos.vo term.vo semantic.vo
interpretation.vo : interpretation.v hseq.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo

hmr.vo : hmr.v hseq.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo hmr_perm_lemmas.vo
tech_lemmas.vo : tech_lemmas.v hmr.vo hseq.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo hmr_perm_lemmas.vo
soundness.vo : soundness.v $(UTILDIR)/Rpos.vo term.vo hseq.vo hmr.vo semantic.vo interpretation.vo
completeness.vo : completeness.v $(UTILDIR)/Rpos.vo term.vo hseq.vo hmr.vo semantic.vo interpretation.vo tactics.vo lambda_prop_tools.vo tech_lemmas.vo $(UTILDIR)/riesz_logic_List_more.vo soundness.vo
invertibility.vo : invertibility.v $(UTILDIR)/Rpos.vo term.vo semantic.vo hseq.vo hmr.vo hmr_perm_lemmas.vo tech_lemmas.vo
M_elim.vo : M_elim.v $(UTILDIR)/Rpos.vo term.vo semantic.vo hseq.vo hmr.vo preproof.vo tech_lemmas.vo
can_elim.vo : can_elim.v invertibility.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo hseq.vo hmr.vo M_elim.vo hmr_perm_lemmas.vo
preproof.vo : preproof.v hmr.vo hseq.vo $(UTILDIR)/Rpos.vo term.vo
lambda_prop_tools.vo : lambda_prop_tools.v hmr.vo hseq.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo $(UTILDIR)/riesz_logic_List_more.vo

Rterm.vo : Rterm.v
Rsemantic.vo : Rsemantic.v Rterm.vo
semantic_Rsemantic_eq.vo : semantic_Rsemantic_eq.v Rsemantic.vo semantic.vo Rterm.vo term.vo $(UTILDIR)/Rpos.vo

p_hseq.vo : p_hseq.v $(UTILDIR)/Rpos.vo term.vo semantic.vo $(UTILDIR)/lt_nat2.vo $(UTILDIR)/FOL_R.vo hseq.vo
decidability.vo : decidability.v $(UTILDIR)/FOL_R.vo lambda_prop_tools.vo hmr.vo hseq.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo $(UTILDIR)/riesz_logic_List_more.vo can_elim.vo M_elim.vo invertibility.vo p_hseq.vo

tactics.vo : tactics.v hseq.vo $(UTILDIR)/Rpos.vo term.vo hmr.vo 
hmr_perm_lemmas.vo : hmr_perm_lemmas.v $(UTILDIR)/Rpos.vo term.vo hseq.vo
