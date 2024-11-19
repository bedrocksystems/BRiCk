  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  $ ls *.v | wc -l
  3

Compiling the generated Coq files.
  $ dune build
       = true
       : check.M
