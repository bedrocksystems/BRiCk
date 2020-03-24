void test() {
    enum X { A , B };
    struct Y { int x; X tg; };

    X a;
    Y b;

    b.x++;
    a = B;
}
