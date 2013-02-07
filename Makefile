GHC := ghc
GHCFLAGS := -O2
RTSOPTSF := +RTS $(RTSOPTS) -RTS

GCPARSER_PATH := ../gcparser
SATSOLVER_BIN := ../lingeling/lingeling

ifneq ($(strip $(PROFILE)),)
  GHCFLAGS_FULL := -prof -auto-all -hisufp_hi -osufp_o -outputdirbin $(GHCFLAGS)
  OSUFF := p_o
else
  GHCFLAGS_FULL := -outputdirbin $(GHCFLAGS)
  OSUFF := o
endif

REGRDIR := Test
testfilter = $(filter $(REGRDIR)/%.hs, $(filter-out $(REGRDIR)/%-old.hs, $(1)))
TESTFILES := $(call testfilter, $(wildcard $(REGRDIR)/*.hs))
REGRTESTS := $(patsubst $(REGRDIR)/%.hs, %, $(TESTFILES))
# REGRTESTS naming convention suffixes: -old Dimacs Gcil Native
TESTLOGS   := $(patsubst %,tmp/%.log,$(REGRTESTS))
GCILLOGS   := $(filter %Gcil.log,$(TESTLOGS))
DIMACSLOGS := $(filter %Dimacs.log,$(TESTLOGS))
NATIVELOGS := $(filter %Native.log,$(TESTLOGS))

# These run only on 'make test'
LONG_TESTLOGS := $(patsubst %,tmp/%-long.log,$(REGRTESTS))
LONG_GCILLOGS := $(filter %Gcil-long.log,$(LONG_TESTLOGS))
LONG_DIMACSLOGS := $(filter %Dimacs-long.log,$(LONG_TESTLOGS))
LONG_NATIVELOGS := $(filter %Native-long.log,$(LONG_TESTLOGS))

# These run only when explicitly requested by name, 
#   e.g. 'make bin/WideAngleGcil-bench.log'
# Same naming convention suffixes as REGRTESTS
BENCHMARKS     := $(filter-out Benchmark/%-old.hs,$(wildcard Benchmark/*.hs))
BENCHLOGS      := $(patsubst Benchmark/%.hs,tmp/%-bench.log,$(BENCHMARKS))
GCIL_BENCHES   := $(filter %Gcil-bench.log,$(BENCHLOGS))
DIMACS_BENCHES := $(filter %Dimacs-bench.log,$(BENCHLOGS))
NATIVE_BENCHES := $(filter %Native-bench.log,$(BENCHLOGS))

.PHONY: all testbins test clean

# TODO test longtests failures

# REMOVE $* is stem
# TODO remove dimacsOut gcilouts folders, build and SorterTests.hs
#   also remove -old files
# TODO Benchmarks, StackDimacs should have a regr version
all: testbins $(TESTLOGS) ;

test: $(TESTLOGS) $(LONG_TESTLOGS) ;

# If you change the name of this folder, change it in a LOT of other places
# as well. Like makeutils/*, Circuit/NetList/*.hs etc.
tmp: ; mkdir -p tmp

clean:
	rm -rf bin tmp
	rm -f FindOptimal FormatDimacs SorterTests TestCircuits

# I want it to run even if TestCircuits (binary) exist, since ghc already 
#   does all the usual make magic for building
testbins: TestCircuits.hs
	$(GHC) --make TestCircuits $(GHCFLAGS_FULL)

# XXX why didn't I add % in list of targets? And add that in GCIL_BENCHES rule?
# It just so happens that ghc --make updates *.o files
$(patsubst %.hs,bin/%.$(OSUFF),$(BENCHMARKS)): bin/Benchmark/%.$(OSUFF): \
  Benchmark/%.hs
	$(GHC) $(GHCFLAGS_FULL) --make $< -o $*

# Probably the "most standalone" source file I have here
FormatDimacs: FormatDimacs.hs
	$(GHC) --make $@ $(GHCFLAGS_FULL)

bin/%.o bin/%.p_o: testbins ;

# This target is not really used anymore, but are here just in case
FindOptimal: FindOptimal.hs Circuit/Sorter.hs Util.hs
	$(GHC) --make $@ $(GHCFLAGS_FULL)

TestCircuits.hs: makeutils/TestGen $(TESTFILES)
	makeutils/TestGen $(REGRTESTS) > $@

# Q: Why do we want an autogenerated TestCircuits.hs
# A: Because I had time to kill
#    I wanted regression tests to be automatically included in TestCircuits
#    without me having to add it. Now, I could have just used the makefile
#    to generate separate test binaries for each test like a sane person would.
#    But I wanted to load GHC only once for all the binaries (apparently loading
#    up GHC is expensive(?)). So I instead have a single TestCircuits binary 
#    that executes any test I want.
$(GCILLOGS): tmp/%.log: tmp bin/$(REGRDIR)/%.$(OSUFF)
	@echo "------- TestCircuits -------" > $@
	@date >> $@
	./TestCircuits $* $(RTSOPTSF) >> $@
	makeutils/GcilTest $(GCPARSER_PATH) $@

$(LONG_GCILLOGS): tmp/%-long.log: tmp bin/$(REGRDIR)/%.$(OSUFF)
	@echo "------- TestCircuits -------" > $@
	@date >> $@
	./TestCircuits $*-long $(RTSOPTSF) >> $@
	makeutils/GcilTest $(GCPARSER_PATH) $@

$(GCIL_BENCHES): tmp/%-bench.log: tmp Benchmark/%.hs bin/Benchmark/%.$(OSUFF)
	./$* $(RTSOPTSF) > $@
	rm $*
	makeutils/GcilTest $(GCPARSER_PATH) $@

$(DIMACSLOGS): tmp/%.log: tmp bin/$(REGRDIR)/%.$(OSUFF)
	@echo "------- TestCircuits -------" > $@
	@date >> $@
	./TestCircuits $* $(RTSOPTSF) >> $@
	makeutils/DimacsTest $(SATSOLVER_BIN) $@

$(LONG_DIMACSLOGS): tmp/%-long.log: tmp bin/$(REGRDIR)/%.$(OSUFF)
	@echo "------- TestCircuits -------" > $@
	@date >> $@
	./TestCircuits $*-long $(RTSOPTSF) >> $@
	makeutils/DimacsTest $(SATSOLVER_BIN) $@

$(DIMACS_BENCHES): tmp/%-bench.log: tmp Benchmark/%.hs ; # TODO

$(NATIVELOGS): tmp/%.log: tmp bin/$(REGRDIR)/%.$(OSUFF)
	@date > $@
	./TestCircuits $* $(RTSOPTSF) >> $@
	@grep -q "Tests passed" $@ || echo "    Test failed"

$(LONG_NATIVELOGS): tmp/%-long.log: tmp bin/$(REGRDIR)/%.$(OSUFF)
	@date > $@
	./TestCircuits $*-long $(RTSOPTSF) >> $@
	@grep -q "Tests passed" $@ || echo "    Test failed"

$(NATIVE_BENCHES): tmp/%-bench.log: tmp Benchmark/%.hs bin/Benchmark/%.$(OSUFF)
	@date > $@
	./$* >> $@
	rm $*
