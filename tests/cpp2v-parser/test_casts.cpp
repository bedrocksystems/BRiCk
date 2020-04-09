struct A {
    void a() {}
};
struct B : public A {
    void b() {}
};
struct C : public B {
    void c() { }
};
struct D {
    void d() {}
};
struct E : public D , public C {
    void e() {}
};

void test() {
    E x;
    x.e();
    x.a();

    E* p = &x;
    p->e();
    p->a();
}
