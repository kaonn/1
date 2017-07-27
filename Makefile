all :
	ocamlbuild -use-ocamlfind -pkg core,compiler-libs -cflag -thread -lflag -thread -lib ocamlcommon dynamics.native
