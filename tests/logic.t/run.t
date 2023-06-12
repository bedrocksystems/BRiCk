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
  _at
       : ptrA → Rep → AT_Result ptrA
  p |-> R
       : AT_Result ptrA
  _offsetR
       : offsetA → Rep → AT_Result offsetA
  o |-> R
       : AT_Result offsetA
  1 goal
    
    σ : genv
    thread_info : biIndex
    Σ : cpp_logic thread_info
    R : Rep
    f, g : field
    o : offset
    p : ptr
    v : val
    ============================
    o ,, o_field σ f = o ,, o_field σ f
  1 goal
    
    σ : genv
    thread_info : biIndex
    Σ : cpp_logic thread_info
    R : Rep
    f, g : field
    o : offset
    p : ptr
    v : val
    ============================
    p |-> R = p |-> R
  1 goal
    
    σ : genv
    thread_info : biIndex
    Σ : cpp_logic thread_info
    R : Rep
    f, g : field
    o : offset
    p : ptr
    v : val
    ============================
    o |-> R = o |-> R
  _2 = p |-> o_field σ f |-> R
       : AT_Result ptrA
  
  _2 uses section variables σ thread_info Σ R f p.
  _3 = p .[ Ti32 ! 0 ] |-> R
       : AT_Result ptrA
  
  _3 uses section variables σ thread_info Σ R p.
  _4 = p |-> o_field σ f .[ Ti32 ! 0 ] |-> R
       : AT_Result ptrA
  
  _4 uses section variables σ thread_info Σ R f p.
  _4a = p ,, o_field σ f |-> R
       : AT_Result ptrA
  
  _4a uses section variables σ thread_info Σ R f p.
  1 goal
    
    σ : genv
    thread_info : biIndex
    Σ : cpp_logic thread_info
    R : Rep
    f, g : field
    o : offset
    p : ptr
    v : val
    ============================
    p ,, o_field σ f .[ Ti32 ! 0 ] = p ,, o_field σ f .[ Ti32 ! 0 ]
  _5 = p .[ Ti32 ! 0 ] .[ Ti32 ! 3 ] |-> R
       : AT_Result ptrA
  
  _5 uses section variables σ thread_info Σ R p.
  _6 = p ,, o_field σ f .[ Ti32 ! 0 ] ,, o_field σ g |-> R
       : AT_Result ptrA
  
  _6 uses section variables σ thread_info Σ R f g p.
  _7 =
  p ,, o_field σ g ,, o_field σ f .[ Ti32 ! 1 ] .[ Ti32 ! 0 ] ,, 
  o_field σ f |-> o_field σ f |-> R
       : AT_Result ptrA
  
  _7 uses section variables σ thread_info Σ R f g p.
  _8 =
  p ,, o_field σ g ,, o_field σ f .[ Ti32 ! 1 ] .[ Ti32 ! 0 ] ,, 
  o_field σ f |-> .[ Ti32 ! 1 ] |-> R
       : AT_Result ptrA
  
  _8 uses section variables σ thread_info Σ R f g p.
  _9 =
  o ,, o_field σ g ,, o_field σ f .[ Ti32 ! 1 ] .[ Ti32 ! 0 ] ,, 
  o_field σ f |-> R
       : AT_Result offsetA
  
  _9 uses section variables σ thread_info Σ R f g o.
  _11 = o .[ Ti32 ! 1 ] |-> R
       : AT_Result offsetA
  
  _11 uses section variables σ thread_info Σ R o.
  _14 = .[ Ti32 ! 1 ] |-> R
       : AT_Result offsetA
  
  _14 uses section variables σ thread_info Σ R.
  _16 = p .[ Ti32 ! 1 ] |-> o_field σ f |-> R
       : AT_Result ptrA
  
  _16 uses section variables σ thread_info Σ R f p.
  b0 = p |-> R
       : AT_Result ptrA
  
  b0 uses section variables thread_info Σ R p.
  b1 = o_field σ f |-> R
       : AT_Result offsetA
  
  b1 uses section variables σ thread_info Σ R f.
  b2 = p .[ Ti32 ! 1 ] |-> R
       : AT_Result ptrA
  
  b2 uses section variables σ thread_info Σ R p.
  b3 = p .[ Ti32 ! 1 ] |-> o_field σ f |-> R
       : AT_Result ptrA
  
  b3 uses section variables σ thread_info Σ R f p.
