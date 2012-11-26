GHC = ghc
GHCFLAGS = -O2

REGRDIR=Test
testfilter = $(filter $(REGRDIR)/%.hs, $(filter-out $(REGRDIR)/%-old.hs, $(1)))
REGRTESTS = $(patsubst $(REGRDIR)/%.hs, %, \
              $(call testfilter, $(wildcard $(REGRDIR)/*.hs)))
# REGRTEST naming convention suffixes: -old Dimacs Gcil Native
TESTLOGS = $(patsubst %,tmp/%.log,$(REGRTESTS))

ifneq ($(strip $(PROFILE)),)
GHCFLAGS_FULL = -prof -auto-all -hisufp_hi -osufp_o -outputdirbin $(GHCFLAGS)
else
GHCFLAGS_FULL = -outputdirbin $(GHCFLAGS)
endif

.PHONY: all testbins test clean

# Make sure binaries are up to date before running tests
all:
	$(MAKE) testbins 
	mkdir -p tmp
	$(MAKE) test

clean:
	rm -rf bin tmp
	rm -f FindOptimal FormatDimacs SorterTests TestCircuits

# I want it to run even if TestCircuits exist, since ghc already 
#   does all the usual make magic for building
testbins:
	$(GHC) --make TestCircuits $(GHCFLAGS_FULL)

# Probably the "most standalone" file I have here
FormatDimacs: FormatDimacs.hs
	$(GHC) --make FormatDimacs $(GHCFLAGS_FULL)

# This target is not really used anymore, but are here just in case
FindOptimal: FindOptimal.hs Circuit/Sorter.hs Util.hs
	$(GHC) --make FindOptimal $(GHCFLAGS_FULL)


# REMOVE $* is stem
# TODO remove dimacsOut gcilouts folders, build and SorterTests.hs
#   also remove -old files
# TODO Benchmarks
test:
	@echo $(TESTLOGS)
