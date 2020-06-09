struct A {
    virtual int f() const = 0;
};

struct B : public A {
    virtual int f() const { return 0; }
};


int call(const A* a) {
    return a->f();
}
