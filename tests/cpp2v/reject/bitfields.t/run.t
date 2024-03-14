  $ . ../../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -names test_cpp_names.v -o test_cpp.v test.cpp -- -std=c++17
  $TESTCASE_ROOT/test.cpp:8:5 (Field S::some_bit): error: bit fields are not supported
  coqc -w -notation-overridden test_cpp_names.v
  Error: Can't find file ./test_cpp_names.v
  coqc -w -notation-overridden test_cpp.v
