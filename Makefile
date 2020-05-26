
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

term.vo : term.v Rpos.vo $(OLLIBSDIR)/List_more.vo
semantic.vo : semantic.v Rpos.vo term.vo
hseq.vo : hseq.v Rpos.vo term.vo

interpretation.vo : interpretation.v hseq.vo Rpos.vo term.vo semantic.vo
soundness.vo : soundness.v Rpos.vo term.vo hseq.vo semantic.vo interpretation.vo
