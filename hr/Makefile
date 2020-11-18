
COQ = coqc -R .. "RL"
COQDOC = coqdoc -g -R .. "RL"

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

UTILDIR = ../Utilities

.DEFAULT_GOAL := all

all: utilities $(VFILES:.v=.vo)

utilities:
	cd $(UTILDIR) && $(MAKE)

term.vo : term.v $(UTILDIR)/Rpos.vo
semantic.vo : semantic.v $(UTILDIR)/Rpos.vo term.vo
hseq.vo : hseq.v $(UTILDIR)/Rpos.vo term.vo semantic.vo $(UTILDIR)/lt_nat_tuples.vo
interpretation.vo : interpretation.v hseq.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo

hr.vo : hr.v hseq.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo 
tech_lemmas.vo : tech_lemmas.v hr.vo hseq.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo 
soundness.vo : soundness.v $(UTILDIR)/Rpos.vo term.vo hseq.vo hr.vo semantic.vo interpretation.vo
completeness.vo : completeness.v $(UTILDIR)/Rpos.vo term.vo hseq.vo hr.vo semantic.vo interpretation.vo tactics.vo lambda_prop_tools.vo tech_lemmas.vo $(UTILDIR)/riesz_logic_List_more.vo soundness.vo
invertibility.vo : invertibility.v $(UTILDIR)/Rpos.vo term.vo semantic.vo hseq.vo hr.vo tech_lemmas.vo hr_perm_lemmas.vo
M_elim.vo : M_elim.v $(UTILDIR)/Rpos.vo term.vo semantic.vo hseq.vo hr.vo tech_lemmas.vo
can_elim.vo : can_elim.v invertibility.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo hseq.vo hr.vo M_elim.vo hr_perm_lemmas.vo

p_hseq.vo : p_hseq.v $(UTILDIR)/Rpos.vo term.vo semantic.vo $(UTILDIR)/lt_nat_tuples.vo $(UTILDIR)/FOL_R.vo hseq.vo
decidability.vo : decidability.v $(UTILDIR)/FOL_R.vo lambda_prop_tools.vo hr.vo hseq.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo $(UTILDIR)/riesz_logic_List_more.vo can_elim.vo M_elim.vo invertibility.vo p_hseq.vo

Rterm.vo : Rterm.v
Rsemantic.vo : Rsemantic.v Rterm.vo
semantic_Rsemantic_eq.vo : semantic_Rsemantic_eq.v Rsemantic.vo semantic.vo Rterm.vo term.vo $(UTILDIR)/Rpos.vo

tactics.vo : tactics.v hseq.vo $(UTILDIR)/Rpos.vo term.vo hr.vo
hr_perm_lemmas.vo : hr_perm_lemmas.v $(UTILDIR)/Rpos.vo term.vo hseq.vo
lambda_prop_tools.vo : lambda_prop_tools.v hr.vo hseq.vo $(UTILDIR)/Rpos.vo term.vo semantic.vo $(UTILDIR)/riesz_logic_List_more.vo
