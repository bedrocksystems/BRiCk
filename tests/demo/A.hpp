namespace A {
  // foo_spec
  int foo(int);
  // bar_spec
  int bar(int x) {
    return foo(x) + 1;
  }
}

