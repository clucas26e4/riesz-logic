
COQ = coqc -R $(OLLIBSDIR) ''
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


OLLIBSDIR = ../ollibs

.DEFAULT_GOAL := all

all: cutelim

ollibs:
	cd $(OLLIBSDIR) && $(MAKE)

cutelim: ollibs $(VFILES:.v=.vo)

include $(OLLIBSDIR)/ollibs.mk

Rpos.vo : Rpos.v

term.vo : term.v Rpos.vo
semantic.vo : semantic.v Rpos.vo term.vo
hseq.vo : hseq.v Rpos.vo term.vo semantic.vo
interpretation.vo : interpretation.v hseq.vo Rpos.vo term.vo semantic.vo

hr.vo : hr.v hseq.vo Rpos.vo term.vo semantic.vo 
soundness.vo : soundness.v Rpos.vo term.vo hseq.vo hr.vo semantic.vo interpretation.vo
completeness.vo : completeness.v Rpos.vo term.vo hseq.vo hr.vo semantic.vo interpretation.vo tactics.vo
invertibility.vo : invertibility.v Rpos.vo term.vo semantic.vo hseq.vo hr.vo
M_elim.vo : M_elim.v invertibility.v Rpos.vo term.vo semantic.vo hseq.vo hr.vo 
can_elim.vo : can_elim.v invertibility.vo Rpos.vo term.vo semantic.vo hseq.vo hr.vo M_elim.vo

Rterm.vo : Rterm.v
Rsemantic.vo : Rsemantic.v Rterm.vo
semantic_Rsemantic_eq.vo : semantic_Rsemantic_eq.v Rsemantic.vo semantic.vo Rterm.vo term.vo Rpos.vo
main_results.vo : main_results.v semantic_Rsemantic_eq.vo Rsemantic.vo semantic.vo hseq.vo hr.vo completeness.vo soundness.vo Rterm.vo term.vo Rpos.vo interpretation.vo invertibility.vo M_elim.vo can_elim.vo

tactics.vo : tactics.v hseq.vo Rpos.vo term.vo hr.vo 
