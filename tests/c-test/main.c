extern void putstr(const char*);

int main(int argc, char* argv[])
{
    for (int i = 0; i < argc; i++) {
        putstr(argv[i]);
    }
    return 0;
}
