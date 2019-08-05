void test(void* p) {
    int* si = static_cast<int*>(p);
    int* ri = reinterpret_cast<int*>(p);
}
