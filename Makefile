
# order is important: a module must be given before what depends on it.
dillc: types.cmo ast.cmo lexer.cmo parser.cmo dillc.cmo
	ocamlc -o dillc $^

dillc.cmo: dillc.ml lexer.cmi parser.cmi ast.cmi types.cmi
	ocamlc -c $<

parser.ml parser.mli: parser.mly ast.cmi types.cmi
	menhir $<

lexer.ml: lexer.mll
	ocamllex $<

# want a general rule that says .cmi and .cmo/x both depend on the .ml.

# separately-compiled modules only depend on interfaces.
lexer.cmo lexer.cmi: lexer.ml parser.cmi
	ocamlc -c $<

# I didn't know that if there's a .mli the module depends on the .cmi.
parser.cmo: parser.ml parser.cmi ast.cmi
	ocamlc -c $<

parser.cmi: parser.mli ast.cmi
	ocamlc -c $<

ast.cmo ast.cmi: ast.ml types.cmi
	ocamlc -c $<

types.cmo types.cmi: types.ml
	ocamlc -c $<

.PHONY: clean

clean:
	rm -f lexer.ml parser.ml parser.mli *.cmo *.cmx *.cmi

cleanobj:
	rm -f *.o
