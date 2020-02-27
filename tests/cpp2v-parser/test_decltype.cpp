int test() {
    int x = 0;
    decltype(x) y = 3;
    decltype((x)) z = x;
    typeof(x) p = 9;
    return x;
}
