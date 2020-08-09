
testparse: testparse.cmo types.cmo ast.cmo parser.cmo lexer.cmo
	ocamlc -o testparse $^

testparse.cmo: testparse.ml lexer.cmi parser.cmi ast.cmi types.cmi
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
