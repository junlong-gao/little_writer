fsrename = rename

pwd:=$(shell pwd)
Docker:=docker run -w $(pwd) -v $(pwd):$(pwd) -it docker.io/jerry1394/tla_plus
NPROCS:=$(shell docker run docker.io/jerry1394/tla_plus grep -c ^processor /proc/cpuinfo)

#TLC2 Version 2.13 of 18 July 2018
#The model checker (TLC) provides the functionalities of model checking or
#simulation of TLA+ specifications.
specParser = $(Docker) java tla2sany.SANY
modelChecker = $(Docker) java tlc2.TLC -deadlock -workers $(NPROCS)
tex = $(Docker) java tla2tex.TLA -number -latexCommand pdflatex -shade

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

.PHONY: clean
clean:
	rm -rf *.tex *.pdf *.dvi *.log *.aux states
