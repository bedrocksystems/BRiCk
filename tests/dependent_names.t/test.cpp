template<typename T>
struct remove_reference_ {
  using type = T;
};

template<typename T>
struct remove_reference_<T&> {
  using type = T;
};
template<typename T>
struct remove_reference_<T&&> {
  using type = T;
};

template<typename T>
using remove_reference = typename remove_reference_<T>::type;

template<typename T>
remove_reference<T>&& move(remove_reference<T>& v) {
  return static_cast<remove_reference<T>&&>(v);
}

struct C{};

void test() {
  int x = 0;
  (void) move<int>(x);
  C c;
  (void) move<C>(c);
}
