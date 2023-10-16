  $ . ../setup-project.sh
  $ dune build demo.vo
  _foo : Foo -l> nat
  
  _foo is not universe polymorphic
  _foo is transparent
  Expands to: Constant test.demo._foo
  _bar : Foo -l> bool
  
  _bar is not universe polymorphic
  _bar is transparent
  Expands to: Constant test.demo._bar
  1 goal
    
    r : Foo
    Hpr : @eq nat (foo r) O
    ============================
    @eq nat (foo r) (foo r)
  1 goal
    
    r : Foo
    Hpr : @eq nat (foo r) O
    ============================
    @eq nat (foo r) O
  $ dune build test.vo 2>&1 | grep -v 'Derivation.*took'
  Derivation lens on indt «State»
  Module
  no_prim_projs
  := Struct
       Record State : Set := MkState { value : N }.
       Definition value : State → N.
       Definition _value : Lens.Lens State State N N.
     End
  
  Derivation lens on indt «State»
  Module
  prim_projs
  := Struct
       Record State : Set := MkState { value : N }.
       Definition value : State → N.
       Definition _value : Lens.Lens State State N N.
     End
  
  Starting module State
  Declaring inductive 
  record State (sort (typ «Set»)) MkState 
   (field [coercion off, canonical tt] value (global (indt «N»)) c0 \
     end-record)
  Deriving
  Derivation lens on indt «State»
  Done
  Module
  bar
  := Struct
       Module State
       Record State2 : Set := MkState2 { value : N }.
       Definition value : State2 → N.
     End
  
  Module
  State
  := Struct
       Record State : Set := MkState { value : N }.
       Definition value : bar.State → N.
       Definition _value : Lens.Lens bar.State bar.State N N.
     End
  
  State.value =
  λ record : State, let (value) := record in value
       : State → N
  
  Arguments State.value record
  Module
  State
  := Struct
       Record State : Set := MkState { value : N }.
       Definition value : bar.State → N.
       Definition _value : Lens.Lens bar.State bar.State N N.
     End
  
  Module
  State
  := Struct
       Record State : Set := MkState { value : N }.
       Definition value : bar.State → N.
       Definition _value : Lens.Lens bar.State bar.State N N.
     End
  
  State.value =
  λ record : bar.State, let (value) := record in value
       : bar.State → N
  
  Arguments State.value record
