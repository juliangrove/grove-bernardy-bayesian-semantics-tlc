
EXE=dist-newstyle/build/x86_64-linux/ghc-8.10.7/grove-bernardy-bayesian-semantics-tlc-0.1.0.0/x/plots/build/plots/plots

SVGFILES= \
goodlass-std.svg \
goodlass.svg \
cookies-continuous-1.0-l0.2d.svg \
cookies-continuous-1.0-s1.2d.svg \
cookies-continuous-1.0-l1.2d.svg \
cookies-continuous-4.0-l1.2d.svg \
cookies-continuous-10.0-l1.2d.svg \
goodlass-l0.2d.svg \
goodlass-s1.2d.svg \
goodlass-l1.2d.svg

# goodlass-l0x.1d.svg \
# goodlass-l0y.1d.svg \
# goodlass-l1x.1d.svg \
# goodlass-l1y.1d.svg \

default: $(SVGFILES)

goodlass.svg: goodlass.gpl goodlass-height-prior.1d.dat
	gnuplot -c $<

goodlass-std.svg: goodlass-std.gpl goodlass-height-prior.1d.dat
	gnuplot -c $<

%.2d.svg: %.2d.dat 2d.gpl
	gnuplot -c 2d.gpl $< $@

%.2d.dat %.1d.dat: $(EXE)
	$(EXE)

$(EXE): $(shell find test -name '*.hs') $(shell find src -name '*.hs') $(shell find gasp -name '*.hs') $(shell find missing-math -name '*.hs')
	cabal v2-build

