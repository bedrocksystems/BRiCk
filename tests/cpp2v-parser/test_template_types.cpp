template<typename T>
class P {
};

template<typename T, typename U, int n>
class Q {
};

template class P<unsigned int>;
template class Q<unsigned char, unsigned long long, 32>;
