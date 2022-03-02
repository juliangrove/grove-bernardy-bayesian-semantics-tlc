# disable default rules:
.SUFFIXES:

EXE=dist-newstyle/build/x86_64-linux/ghc-8.10.7/grove-bernardy-bayesian-semantics-tlc-0.1.0.0/x/plots/build/plots/plots

D2SVGS := \
cookies-continuous-1.0-l0.2d.svg \
cookies-continuous-1.0-s1.2d.svg \
cookies-continuous-1.0-l1.2d.svg \
cookies-continuous-4.0-l1.2d.svg \
cookies-continuous-10.0-l1.2d.svg \
goodlass-std-l0.2d.svg \
goodlass-std-s1.2d.svg \
goodlass-std-l1.2d.svg \
goodlass-l0.2d.svg \
goodlass-s1.2d.svg \
goodlass-l1.2d.svg

D2DAT := $(D2SVGS:%.svg=%.dat)

# goodlass-l0x.1d.svg \
# goodlass-l0y.1d.svg \
# goodlass-l1x.1d.svg \
# goodlass-l1y.1d.svg \

DATS := $(D2DAT) \
 goodlass-height-prior.1d.dat \
 goodlass-svg-l1y.1d.dat \
 goodlass-avg-l1y.1d.dat

default: $(D2SVGS) goodlass-avg.svg goodlass-std.svg goodlass.svg

goodlass.svg: goodlass.gpl goodlass-height-prior.1d.dat
	gnuplot -c $<

goodlass-avg.svg: goodlass-avg.gpl goodlass-avg-l1y.1d.dat
	gnuplot -c $<

goodlass-std.svg: goodlass-std.gpl goodlass-height-prior.1d.dat
	gnuplot -c $<

%.2d.svg: %.2d.dat 2d.gpl
	gnuplot -c 2d.gpl $< $@

$(DATS): $(EXE)
	$(EXE)

$(EXE): $(shell find test -name '*.hs') $(shell find src -name '*.hs') $(shell find gasp -name '*.hs') $(shell find missing-math -name '*.hs')
	cabal v2-build

