  $ . ../../setup-name-test.sh
  $ name_test test.cpp
  # cpp2v --name-test=test_17_name_test.v test.cpp -- -std=c++17
  # scrub test_17_name_test.v
  Require Import bedrock.auto.cpp.templates.mparser2.
  
  #[local] Open Scope bs_scope.
  
  Definition module_names : list Mname :=
    (
      (Nscoped
        (Nglobal (Nanon 0)) (Nid "inhabit_ns")) ::
  
      (Nscoped
        (Nglobal (Nid "container")) (Nfunction (nil) Nctor nil)) ::
  
      (Nscoped
        (Nglobal (Nid "container")) (Nfunction (nil) Ndtor nil)) ::
  
      (Nglobal (Nid "container")) ::
  
      (Nscoped
        (Nglobal (Nid "container")) (Nanon 0)) ::
  
      (Nscoped
        (Nscoped
          (Nglobal (Nid "container")) (Nanon 0)) (Nfunction (nil) Nctor nil)) ::
  
      (Nscoped
        (Nscoped
          (Nglobal (Nid "container")) (Nanon 0)) (Nfunction (nil) Nctor ((Tref (Qconst (Tnamed
                  (Nscoped
                    (Nglobal (Nid "container")) (Nanon 0))))) :: nil))) ::
  
      (Nscoped
        (Nscoped
          (Nglobal (Nid "container")) (Nanon 0)) (Nfunction (nil) (Nop OOEqual) ((Tref (Qconst (Tnamed
                  (Nscoped
                    (Nglobal (Nid "container")) (Nanon 0))))) :: nil))) ::
  
      (Nscoped
        (Nscoped
          (Nglobal (Nid "container")) (Nanon 0)) (Nfunction (nil) Nctor ((Trv_ref (Tnamed
                (Nscoped
                  (Nglobal (Nid "container")) (Nanon 0)))) :: nil))) ::
  
      (Nscoped
        (Nscoped
          (Nglobal (Nid "container")) (Nanon 0)) (Nfunction (nil) (Nop OOEqual) ((Trv_ref (Tnamed
                (Nscoped
                  (Nglobal (Nid "container")) (Nanon 0)))) :: nil))) ::
  
      (Nscoped
        (Nscoped
          (Nglobal (Nid "container")) (Nanon 0)) (Nfunction (nil) Ndtor nil)) ::
  
      (Nscoped
        (Nglobal (Nid "container")) (Nanon 1)) ::
  
      (Nscoped
        (Nscoped
          (Nglobal (Nid "container")) (Nanon 1)) (Nfunction (nil) Nctor ((Tref (Qconst (Tnamed
                  (Nscoped
                    (Nglobal (Nid "container")) (Nanon 1))))) :: nil))) ::
  
      (Nscoped
        (Nscoped
          (Nglobal (Nid "container")) (Nanon 1)) (Nfunction (nil) Nctor ((Trv_ref (Tnamed
                (Nscoped
                  (Nglobal (Nid "container")) (Nanon 1)))) :: nil))) ::
  
      (Nscoped
        (Nscoped
          (Nglobal (Nid "container")) (Nanon 1)) (Nfunction (nil) Ndtor nil)) ::
  
      (Nglobal (Nanon 1)) ::
  
      (Nglobal (Nid "inhabit_e")) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
