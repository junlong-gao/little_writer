monitor = Monitor.tla
singleSem = MonitorWithSem
batonQueue = MonitorWithBatonQueue

NPROCS:=$(shell grep -c ^processor /proc/cpuinfo)

#TLC2 Version 2.13 of 18 July 2018
#The model checker (TLC) provides the functionalities of model checking or
#simulation of TLA+ specifications.
specParser = java tla2sany.SANY
modelChecker = java tlc2.TLC -deadlock -workers $(NPROCS)
tex = java tla2tex.TLA -number -latexCommand pdflatex -shade

# Note in model checking if some property is violated, the model checker
# still returns 0, but outputs the violation message with a counter example.
all: parse small large counter_example wrong_large_no_liveness pdf

pdf: *.tla
	$(tex) $(monitor)
	$(tex) $(singleSem)
	$(tex) $(batonQueue)

parse: *.tla
	$(specParser) *.tla

small: $(batonQueue).tla $(batonQueue)Small.cfg
	$(modelChecker) $(batonQueue).tla \
	   -config $(batonQueue)Small.cfg

large: $(batonQueue).tla $(batonQueue)Large.cfg
	$(modelChecker) $(batonQueue).tla \
	   -config $(batonQueue)Large.cfg

counter_example: $(singleSem).tla $(singleSem)Small.cfg
	$(modelChecker) $(singleSem).tla \
	   -config $(singleSem)Small.cfg

wrong_large_no_liveness: $(singleSem).tla $(singleSem)Large.cfg
	$(modelChecker) $(singleSem).tla \
	   -config $(singleSem)Large.cfg

.PHONY: clean
clean:
	rm -rf *.tex *.pdf *.dvi *.log *.aux states
