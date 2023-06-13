  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -names test_cpp_names.v -o test_cpp.v test.cpp -- -std=c++17
  member pointers are currently not supported in the logic. (at <$TESTCASE_ROOT/test.cpp:26:4, col:7>)
  member pointers are currently not supported in the logic. (at <$TESTCASE_ROOT/test.cpp:31:11, col:14>)
  member pointers are currently not supported in the logic. (at <$TESTCASE_ROOT/test.cpp:31:23, col:26>)
  coqc -w -notation-overridden test_cpp_names.v
  coqc -w -notation-overridden test_cpp.v
