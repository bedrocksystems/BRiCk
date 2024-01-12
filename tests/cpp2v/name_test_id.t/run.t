  $ . ../../setup-name-test.sh
  $ name_test test.cpp
  # cpp2v --name-test=test_17_name_test.v test.cpp -- -std=c++17
  # scrub test_17_name_test.v
  Require Import bedrock.auto.cpp.templates.mparser2.
  
  #[local] Open Scope bs_scope.
  
  Definition module_names : list Mname :=
    (
      (Nscoped
        (Nglobal (Nid "ns")) (Nid "inhabit")) ::
  
      (Nglobal (Nid "c")) ::
  
      (Nglobal (Nid "s")) ::
  
      (Nglobal (Nid "u")) ::
  
      (Nglobal (Nid "e1")) ::
  
      (Nglobal (Nid "e2")) ::
  
      (Nglobal (Nid "t1")) ::
  
      (Nglobal (Nid "t2")) ::
  
      (Nglobal (Nid "v")) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
