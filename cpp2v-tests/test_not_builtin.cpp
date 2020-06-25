
extern "C" {
unsigned long strlen(const char *msg) {
    unsigned result = 0;
    while (*msg) {
        result++;
        msg++;
    }
    return result;
}
}

unsigned test() {
    return strlen("100");
}
