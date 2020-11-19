template<typename Data>
class Map {
  class iterator {
    template<typename Key>
    friend class ::Map;
  };
};

template class Map<int>;
