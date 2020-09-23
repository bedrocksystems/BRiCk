struct S {
  int x;
  int y;
};

void test() {
  S s;
  s = S();
  S y;
  s = y;
}
