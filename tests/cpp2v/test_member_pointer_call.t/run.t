  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -names test_cpp_names.v -o test_cpp.v test.cpp -- -std=c++17
  member pointers are currently not supported in the logic. (at <$TESTCASE_ROOT/test.cpp:16:11, col:14>)
  coqc -w -notation-overridden test_cpp_names.v
  coqc -w -notation-overridden test_cpp.v
