struct Top {
     int p;
};

struct Other {
    int x;
};

struct Foo : public Top {
    int z;
};

struct Bar : public Foo , public Other {
    int y;
};


int get_x(Bar& b) {
    return b.p + b.y;
}
