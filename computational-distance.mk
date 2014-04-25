ROOT=~/Development/CrystalHS/
TARGETDIR=$(ROOT)/test/shootout
HERE=$(shell pwd)

TARGETS=$(notdir $(wildcard $(TARGETDIR)/*.chicken))
SUMMARIES=$(TARGETS:.chicken=.sum)

all: $(SUMMARIES)

%.predicted: $(TARGETDIR)/%.chicken
	$(ROOT)/run.sh -@ $^ > $@

%.sum: %.predicted
	cd $(TARGETDIR); racket -t $(ROOT)/eval/eval.rkt -m < $(HERE)/$^ 2>&1 > /dev/null | \
	perl $(ROOT)/process-summary.pl \
	> $(HERE)/$@

.PHONY: all
