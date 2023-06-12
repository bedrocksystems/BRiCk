  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -names test_cpp_names.v -o test_cpp.v test.cpp -- -std=c++17
  $TESTCASE_ROOT/test.cpp:7:3: warning: expression result unused [-Wunused-value]
    A; // A here has type `E`
    ^
  1 warning generated.
  coqc -w -notation-overridden test_cpp_names.v
  coqc -w -notation-overridden test_cpp.v
