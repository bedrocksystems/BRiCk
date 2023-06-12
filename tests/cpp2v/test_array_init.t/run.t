  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -names test_cpp_names.v -o test_cpp.v test.cpp -- -std=c++17
  $TESTCASE_ROOT/test.cpp:19:35: warning: array designators are a C99 extension [-Wc99-designator]
      int z[2][2] = { { 1 , 2 } , { [1] = 4 } };
                                    ^~~
  $TESTCASE_ROOT/test.cpp:20:19: warning: array designators are a C99 extension [-Wc99-designator]
      int a[10] = { [9] = 1 };
                    ^~~
  2 warnings generated.
  coqc -w -notation-overridden test_cpp_names.v
  coqc -w -notation-overridden test_cpp.v
