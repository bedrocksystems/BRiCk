  $ . ../../setup-cpp2v.sh
  $ check_cpp2v_versions test.cpp 20
  cpp2v -v -names test_20_cpp_names.v -o test_20_cpp.v test.cpp -- -std=c++20
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_20_cpp_names.v
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_20_cpp.v
