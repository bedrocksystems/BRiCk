struct Foo {
    int b;
    struct {
        int x;
    };
    struct {
        int y;
    };

    struct {
        int z;
    } z;

    union {
        struct { int p; };
        struct { char q; };
    };
};

int foo(Foo f) {
    return f.b + f.x + f.y + f.z.z + f.p;
}
