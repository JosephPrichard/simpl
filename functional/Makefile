all:
	ocamlc -c simpltypes.ml
	ocamlyacc simplparser.mly
	ocamlc -c simplparser.mli
	ocamlc -c simplparser.ml
	ocamllex simpllexer.mll
	ocamlc -c simpllexer.ml
	ocamlc -c simpl.ml
	ocamlc -o simpl.exe simpltypes.cmo simpllexer.cmo simplparser.cmo simpl.cmo
clean:
	rm -rf *.exe
	rm -rf *.cmo
	rm -rf *.cmi
	rm simpllexer.ml
	rm simplparser.ml