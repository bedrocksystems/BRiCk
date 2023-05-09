  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  $ ls *.v | wc -l
  23

Compiling the generated Coq files.
  $ dune build
