template<typename T>
void destroy(T* ptr) {
  ptr->T::~T();
}

template void destroy<int>(int*);
