template<typename T, int res>
int g(T x) {
    return res;
}

int main() {
    g<int, 8>(1);
}
