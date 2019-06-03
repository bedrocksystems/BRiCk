void foo() {
    int x = 0;
    __asm__ volatile ("syscall" : "+D"(x) :: "rcx", "r11", "memory");
}
