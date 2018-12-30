include ../Makefile.include

fsrename = Rename

# Note in model checking if some property is violated, the model checker
# still returns 0, but outputs the violation message with a counter example.
all: parse counter_example pdf

pdf: *.tla
	$(tex) $(fsrename)

parse: *.tla
	$(specParser) *.tla

# Note how the model is offloaded to a separate tla spec and the cfg
# does not contain tla constructs
counter_example: $(fsrename).tla $(fsrename)Small.cfg
	$(modelChecker) \
	   $(fsrename)Small.tla \
	   -config $(fsrename)Small.cfg
