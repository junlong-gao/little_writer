include ../Makefile.include
monitor = Monitor
singleSem = MonitorWithSem
batonQueue = MonitorWithBatonQueue

# Note in model checking if some property is violated, the model checker
# still returns 0, but outputs the violation message with a counter example.
all: parse small large counter_example wrong_large_no_liveness pdf

pdf: *.tla
	$(tex) $(monitor).tla
	$(tex) $(singleSem).tla
	$(tex) $(batonQueue).tla

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
