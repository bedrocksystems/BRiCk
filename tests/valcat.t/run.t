  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  $ ls *.v | wc -l
  21

Compiling the generated Coq files.
  $ dune build
