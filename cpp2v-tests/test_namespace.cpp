namespace things { int x; }

int test() {
    using namespace things;
    return x;
}
