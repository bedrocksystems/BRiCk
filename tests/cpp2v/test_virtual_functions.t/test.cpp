/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
struct A {
    virtual int foo() const = 0;
    int bar() const { return foo(); }
    virtual ~A() {}
};

struct B : public A {
//    virtual int foo() const { return 1; }
    virtual ~B() {}
};

struct C : public B {
    C() { }
    virtual int foo() const { return 2; }
    virtual ~C() {}
};

int main() {
    C* c = new C();
    B* b = static_cast<C*>(c);
    A* a = static_cast<C*>(a);

    c->B::foo();
    b->foo();
    a->foo();

    return 0;
}


#if 0
struct A {
    int x{100};
    A() { std::cout << "A default\n"; }
    A(int y):x(y) { f(); /* -- undefined behavior */ }
    virtual int f() const { std::cout << "A::f " << x << "\n"; return x; }
    virtual ~A() {}
};

struct B : public A {
    B():A(f()) { f(); /* static call to B::f, returns 17 */ }
    B(int x):A(f()) { bar(); }
    virtual int f() const { std::cout<< "xxx\n"; return x; }
    void bar() { std::cout << "bar " << f() << "\n"; }
};

struct C : public B {
    C():B(f()) { f(); }
    // virtual int f() const { return 1; }
    virtual ~C() {}
};

struct D : public C {
    virtual int f() const { return 2; }
    virtual ~D() {}
};

int call_a(const A* a) {
    return a->f();
}

int call_b(const B* a) {
    return a->f();
}

int call_c(const C* a) {
    return a->f();
}

int main() {
    D b;
    A* a = &b;
    std::cout << "a " << a->f() << "\n";

/*
    C *z = new (reinterpret_cast<void*>(&b)) C();
    std::cout << "z " << z->f() << "\n";
*/
}
#endif
