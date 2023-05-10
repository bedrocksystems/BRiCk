  $ . ../setup-project.sh
  $ dune build test.vo
  mpred_sep :
  ∀ {thread_info : biIndex} {Σ : cpp_logic thread_info}, mpred → mpred → mpredI
  
  mpred_sep is not universe polymorphic
  Arguments mpred_sep {thread_info Σ} (P Q)%bi_scope
  mpred_sep is transparent
  Expands to: Constant test.test.mpred_sep
  rep_sep :
  ∀ {thread_info : biIndex} {Σ : cpp_logic thread_info}, Rep → Rep → RepI
  
  rep_sep is not universe polymorphic
  Arguments rep_sep {thread_info Σ} (P Q)%bi_scope
  rep_sep is transparent
  Expands to: Constant test.test.rep_sep
