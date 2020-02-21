struct P {
    int x;
};

int test() {
    auto t = &P::x;
    P x;
    return x.*t;
}
