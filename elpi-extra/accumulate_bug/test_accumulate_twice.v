Require Import accumulate_bug.accumulate1.
Require Import accumulate_bug.accumulate2.
Fail Elpi Typecheck program.
(*
Error:
File "ROOT/_build/default/fmdeps/cpp2v/elpi-extra/accumulate_bug/library.elpi", line 5, column 2, character 59:duplicate type abbreviation for cpp.bs. Previous declaration: File "ROOT/_build/default/fmdeps/cpp2v/elpi-extra/accumulate_bug/library.elpi", line 5, column 2, character 59:
*)
