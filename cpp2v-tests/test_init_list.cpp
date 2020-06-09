struct A {
    A() {}
    A(int) {}
    virtual int foo() { return 0; }
};
struct B : public A {
    B(int) {}
    B() {}
    //virtual int foo() { return 3; }
};

struct C : public B {
    int y;
    int x;
    C():x(0),y(7) {}
    virtual int foo() { return 1; }
};

int test(C* c) {
    B* b = static_cast<B*>(c);
    return b->foo() + b->A::foo();
}
