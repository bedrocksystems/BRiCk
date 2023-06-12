  $ . ../../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -names test_cpp_names.v -o test_cpp.v test.cpp -- -std=c++17
  $TESTCASE_ROOT/test.cpp:9:9: error: initializing multiple members of union
      int y {1};
          ^
  $TESTCASE_ROOT/test.cpp:8:9: note: previous initialization is here
      int x {3};
          ^
  1 error generated.
  Error while processing $TESTCASE_ROOT/test.cpp.
  coqc -w -notation-overridden test_cpp_names.v
  coqc -w -notation-overridden test_cpp.v
