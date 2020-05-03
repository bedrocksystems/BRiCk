void test() {
    int x = 0;
    __atomic_fetch_or(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_fetch_and(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_fetch_xor(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_fetch_add(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_fetch_sub(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_or_fetch(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_and_fetch(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_xor_fetch(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_add_fetch(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_sub_fetch(&x, 0, __ATOMIC_SEQ_CST);
}
