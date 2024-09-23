TARGETS=ContataCmdLine.exe

GENERATE_DATA := python3 generate-data.py
GENERATE_GRAPHS := python3 transform-data.py
CREATE_DEFAULT_ANSWERS := python3 create-default-answers.py

.PHONY: all build clean %.exe

all: build link

build:
	dune build app/ContataCmdLine.exe --profile release # ignores warnings as errors

link: $(TARGETS)

%.exe:
	if [ ! -f $@ ]; then ln -s _build/default/app/$@ . ; fi

install:
	jbuilder install

clean:
	rm -rf _build *.install *.pdf $(TARGETS)

clean-data:
	rm -rf generated-data
	rm -rf generated-graphs

clean-outs:
ifneq (,$(wildcard ./benchmarks/logical/*.out))
	rm benchmarks/logical/*.out
endif
ifneq (,$(wildcard ./benchmarks/io/*.out))
	rm benchmarks/io/*.out
endif

documentation:
	jbuilder build @docs

generate-data: all
	$(GENERATE_DATA) ./ContataCmdLine.exe benchmarks

regenerate-data: all
	rm -rf generated-data
	$(GENERATE_DATA) ./ContataCmdLine.exe benchmarks
