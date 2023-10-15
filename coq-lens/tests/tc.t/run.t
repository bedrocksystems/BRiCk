  $ . ../setup-project.sh
  $ dune build demo.vo
  _foo : Lens Foo Foo nat nat
  
  _foo is not universe polymorphic
  _foo is transparent
  Expands to: Constant test.demo._foo
  _bar : Lens Foo Foo bool bool
  
  _bar is not universe polymorphic
  _bar is transparent
  Expands to: Constant test.demo._bar
