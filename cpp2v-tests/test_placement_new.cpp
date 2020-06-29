#include <new>
struct C {
    int x;
    C():x{0} {}
    C(int y):x(y) {}
};


C* test(C* p) {
    auto z = new int();  // None (Some (Eimplicit_init ..)) None
    auto y = new int{};  // None (Some (Einit_list ..)) None
    auto zz = new int[15]; // (Some 15) None None
    auto zzz = new int[15](); // (Some 15) (Some (Eimplicit_init ..)) None
    auto zzzz = new int[15]{1,2,3}; // (Some 15) (Some (Einitlist ..)) None
    auto zzzzz = new C[2] {C(1), C(2)};
    delete z;
    delete[] zz;
    p = new (p) C(3); // None (Some ctor) (Some ctor)
    C* x = new C[10]; // None (Some ctor) (Some ctor)
    delete[] x;
    delete p;
    return new C(5);  // None (Some ctor) (Some ctor)
}
