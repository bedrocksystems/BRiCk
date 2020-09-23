struct C {
  int mem;
  static int sta;
  static int get() { return 0; }
  int gett() { return 0; }
};

void test() {
  C c;
  (void)c.mem;
  (void)c.sta;
  c.get();
  c.gett();
}
