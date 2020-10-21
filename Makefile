
COQ_HR = coqc -R $(OLLIBSDIR) '' -R $(HRDIR) '' -R $(UTILDIR) ''
COQ_HMR = coqc -R $(OLLIBSDIR) '' -R $(HMRDIR) ''  -R $(UTILDIR) ''
COQDOC = coqdoc -g

VFILES_HR = hr_main_results.v
VFILES_HMR = hmr_main_results.v
VFILES_DOC = $(wildcard */*.v)

%.glob: %.vo
	@true

%.html: %.v %.vo
	$(COQDOC) $<


doc: $(VFILES:.v=.glob)
	$(COQDOC) -toc $(VFILES_HR) $(VFILES_HMR)
	cd $(HRDIR) && $(MAKE) doc
	cd $(HMRDIR) && $(MAKE) doc

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
OLLIBSDIR = ../ollibs

.DEFAULT_GOAL := all

all: hr hmr

pre_hr:
	cd $(HRDIR) && $(MAKE)

pre_hmr:
	cd $(HMRDIR) && $(MAKE)

hr: pre_hr $(VFILES_HR:.v=.vo)
hmr: pre_hmr $(VFILES_HMR:.v=.vo)

hr_main_results.vo : hr_main_results.v
	$(COQ_HR) hr_main_results.v
hmr_main_results.vo : hmr_main_results.v
	$(COQ_HMR) hmr_main_results.v
