.PHONY: default
default: kiddoo

kiddoo: kiddoo.ml semant.cmx translate.cmx
	ocamlopt -c kiddoo.ml
	ocamlopt ast.cmx parser.cmx scanner.cmx datatypes.cmx semant.cmx runtime.cmx translate.cmx kiddoo.cmx -o kiddoo

translate.cmx: translate.ml runtime.cmx datatypes.cmx semant.cmx ast.cmx
	ocamlopt -c translate.ml

runtime.cmx: datatypes.cmx runtime.ml
	ocamlopt -c runtime.ml

semant.cmx: semant.ml datatypes.cmx ast.cmx parser.cmx scanner.cmx
	ocamlopt -c semant.ml

datatypes.cmx: datatypes.ml
	ocamlopt -c datatypes.ml

scanner.cmx: scanner.mll parser.cmx
	ocamllex scanner.mll
	ocamlopt -c scanner.ml

parser.cmx: parser.mly ast.cmx
	ocamlyacc parser.mly
	ocamlopt parser.mli
	ocamlopt -c parser.ml

ast.cmx: ast.ml
	ocamlopt -c ast.ml

.PHONY: clean
clean:
	rm -f *.cmx *.cmi *.mli *.o test/*.g parser.ml scanner.ml kiddoo

test: test.c
	gcc -Wall test.c -o test
