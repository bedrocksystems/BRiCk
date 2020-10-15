class X {
  friend int get(X&x) {
    return x.x;
  }
  friend int blab(X&);
  friend int blab2(X&);
  int x;
};

int blab(X& x) { return x.x; }
int test() {
  X x;
  return blab2(x);
}
