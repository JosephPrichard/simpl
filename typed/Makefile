TESTS = $(wildcard test/*.sim)

.PHONY: test build clean

all: test build

test: $(TESTS)

$(TESTS): build
	@echo "Running test $@"
	@./simpl.exe $@ 10

build:
	ocamlc -c simpltypes.ml
	ocamlyacc simplparser.mly
	ocamlc -c simplparser.mli
	ocamlc -c simplparser.ml
	ocamllex simpllexer.mll
	ocamlc -c simpllexer.ml
	ocamlc -c simpl.ml
	ocamlc -o simpl.exe simpltypes.cmo simpllexer.cmo simplparser.cmo simpl.cmo

clean:
	rm -f simpl.exe simpllexer.ml simplparser.ml simplparser.mli *.cmo *.cmi