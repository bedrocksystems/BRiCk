#include <utility>

void test() {
  std::pair<int,int> x{0,0};
  auto [a,b] = x;
  auto [aa,bb] = std::pair<int,std::pair<int,int> >{0,x};
}
