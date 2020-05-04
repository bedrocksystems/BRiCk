struct X {
    int y;
    int f() { return 0; }
};

template<int (X::*FUN)()>
int g() {
  X x;
  x.f();
  return (x.*FUN)(); //<-- SIGSEGV
};

int main() {
  return g<&X::f>();
}