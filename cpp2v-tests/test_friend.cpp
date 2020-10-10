class X {
  friend int get(X&x) {
    return x.x;
  }
  int x;
};
