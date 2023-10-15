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
    Hpr : foo r = 0
    ============================
    foo r = foo r
  1 goal
    
    r : Foo
    Hpr : foo r = 0
    ============================
    0 = 0
