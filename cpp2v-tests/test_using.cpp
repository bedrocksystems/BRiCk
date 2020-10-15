
class B {
public:
  int get0() { return 0; }
};

class X : protected B {
public:
  using B::get0;
};

int test() {
  X x;
  return x.get0();
}
