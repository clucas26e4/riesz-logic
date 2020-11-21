
COQ = coqc -R . "RL"
COQDOC = coqdoc -g -R . "RL"

VFILES_HR = hr_main_results.v hr_example.v
VFILES_HMR = hmr_main_results.v hmr_example.v
VFILES_DOC = $(wildcard */*.v)

%.glob: %.vo
	@true

%.html: %.v %.vo
	$(COQDOC) $<


doc: util_doc pre_hr_doc pre_hmr_doc

clean:
	rm -f *.vo* */*.vo*
	rm -f .*.aux */.*.aux
	rm -f *.crashcoqide */*.crashcoqide
	rm -f *.glob */*.glob
	rm -f *.html */*.html
	rm -f coqdoc.css */coqdoc.css
	rm -f lia.cache */lia.cache
	rm -f .lia.cache */.lia.cache

.PHONY: clean
.PRECIOUS: %.vo %.glob


HRDIR = hr
HMRDIR = hmr
UTILDIR = Utilities

.DEFAULT_GOAL := all

all: hr hmr

pre_hr:
	cd $(HRDIR) && $(MAKE)

pre_hmr:
	cd $(HMRDIR) && $(MAKE)

pre_hr_doc:
	cd $(HRDIR) && $(MAKE) doc

pre_hmr_doc:
	cd $(HMRDIR) && $(MAKE) doc

util_doc : 
	cd $(UTILDIR) && $(MAKE) doc

hr: pre_hr $(VFILES_HR:.v=.vo)
hmr: pre_hmr $(VFILES_HMR:.v=.vo)

hr_main_results.vo : hr_main_results.v
	$(COQ) hr_main_results.v
hmr_main_results.vo : hmr_main_results.v
	$(COQ) hmr_main_results.v

hr_example.vo : hr_example.v
	$(COQ) hr_example.v
hmr_example.vo : hmr_example.v
	$(COQ) hmr_example.v
