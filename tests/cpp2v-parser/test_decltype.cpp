int test() {
    int x = 0;
    decltype(x) y = 3;
    decltype((x)) z = x;
    return x;
}
