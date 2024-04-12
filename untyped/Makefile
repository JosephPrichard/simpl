build: deriver interpreter

deriver:
	ocamlc -c simpltypes.ml
	ocamlyacc simplparser.mly
	ocamlc -c simplparser.mli
	ocamlc -c simplparser.ml
	ocamllex simpllexer.mll
	ocamlc -c simpllexer.ml
	ocamlc -c simplstore.ml
	ocamlc -c simplderive.ml
	ocamlc -o simplderive.exe simpltypes.cmo simplstore.cmo simpllexer.cmo simplparser.cmo simplderive.cmo

interpreter:
	ocamlc -c simpltypes.ml
	ocamlyacc simplparser.mly
	ocamlc -c simplparser.mli
	ocamlc -c simplparser.ml
	ocamllex simpllexer.mll
	ocamlc -c simpllexer.ml
	ocamlc -c simplstore.ml
	ocamlc -c simpl.ml
	ocamlc -o simpl.exe simpltypes.cmo simplstore.cmo simpllexer.cmo simplparser.cmo simpl.cmo

