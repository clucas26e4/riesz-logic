
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

.DEFAULT_GOAL := all

all:  $(VFILES:.v=.vo)

Rpos.vo : Rpos.v
FOL_R.vo : FOL_R.v Rpos.vo riesz_logic_List_more.vo
tactics.vo : tactics.v hseq.vo Rpos.vo term.vo hr.vo
riesz_logic_List_more.vo : riesz_logic_List_more.v
lt_nat_tuples.vo : lt_nat_tuples.v
