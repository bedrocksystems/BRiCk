  $ . ../../setup-name-test.sh
  $ name_test test.cpp
  # cpp2v --name-test=test_17_name_test.v test.cpp -- -std=c++17
  # scrub test_17_name_test.v
  Require Import bedrock.auto.cpp.templates.mparser2.
  
  #[local] Open Scope bs_scope.
  
  Definition module_names : list Mname :=
    (
      (Nglobal (Nfunction (nil) (Nf "fid") nil)) ::
  
      (Nscoped
        (Nglobal (Nid "fname")) (Nfunction (nil) Nctor nil)) ::
  
      (Nscoped
        (Nglobal (Nid "fname")) (Nfunction (nil) Ndtor nil)) ::
  
      (Nscoped
        (Nglobal (Nid "fname")) (Nfunction (nil) (Nop OOPlusPlus) nil)) ::
  
      (Nscoped
        (Nglobal (Nid "fname")) (Nfunction (nil) (Nop_conv Tint) nil)) ::
  
      (Nglobal (Nfunction (nil) (Nop_lit "_lit" ) (Tulonglong :: nil))) ::
  
      (Nscoped
        (Nglobal (Nid "extra")) (Nfunction (nil) Ndtor nil)) ::
  
      (Nscoped
        (Nglobal (Nid "extra")) (Nfunction (nil) (Nf "args") nil)) ::
  
      (Nscoped
        (Nglobal (Nid "extra")) (Nfunction (nil) (Nf "args") (Tint :: Tbool :: nil))) ::
  
      (Nscoped
        (Nglobal (Nid "extra")) (Nfunction (Nlvalue :: nil) (Nf "l") nil)) ::
  
      (Nscoped
        (Nglobal (Nid "extra")) (Nfunction (Nrvalue :: nil) (Nf "r") nil)) ::
  
      (Nscoped
        (Nglobal (Nid "extra")) (Nfunction (Nconst :: nil) (Nf "c") nil)) ::
  
      (Nscoped
        (Nglobal (Nid "extra")) (Nfunction (Nvolatile :: nil) (Nf "v") nil)) ::
  
      (Nscoped
        (Nglobal (Nid "extra")) (Nfunction (Nconst :: Nvolatile :: Nlvalue :: nil) (Nf "cvl") nil)) ::
  
      (Nglobal (Nid "fname")) ::
  
      (Nglobal (Nid "extra")) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
