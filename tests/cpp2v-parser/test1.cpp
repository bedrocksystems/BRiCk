int foo(int x) { return x; }
int foo(int x, int y) { return x + y; }

int main() {
    return foo(0) + foo(1,1);
}
