union BitUnion {
  unsigned bits : 1;
};

struct Base {};
struct WithBase : Base {
  unsigned bits : 1;
};

struct WithVirtual {
  unsigned bits : 1;
  virtual void method();
};

struct WithVirtualBase : virtual Base {
  unsigned bits : 1;
};

struct __attribute__((packed)) PackedBits {
  unsigned bits : 1;
  int unaligned;
};

struct __attribute__((packed)) PackedPlain {
  char byte;
  int unaligned;
};

template <unsigned Width> struct DependentBits {
  unsigned bits : Width;
};

template <class T> struct DependentType {
  T bits : 1;
};
