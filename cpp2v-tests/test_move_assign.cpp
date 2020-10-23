#if 0
struct V { };

struct XX : public virtual V {
  int x;
};

#endif 
struct YY /* : public XX, virtual V */ {
  union { int a; char b[10]; } x;
  int buf[100];
};

void test() {
  YY y;

}
