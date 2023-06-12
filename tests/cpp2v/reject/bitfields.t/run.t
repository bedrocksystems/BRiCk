  $ . ../../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -names test_cpp_names.v -o test_cpp.v test.cpp -- -std=c++17
  Error: bit fields are not supported <$TESTCASE_ROOT/test.cpp:8:5, col:25>
  coqc -w -notation-overridden test_cpp_names.v
  Error: Can't find file ./test_cpp_names.v
  coqc -w -notation-overridden test_cpp.v
  File "./test_cpp.v", line 92, characters 121-122:
  Error:
  Syntax error: '##ₚ.)' or '==.)' or '≢ₚ.)' or '≡ₚ.)' or '::.)' or '⊔.)' or '⊓.)' or '⊑.)' or '!!!.)' or '!!.)' or '≫=.)' or '##.)' or '∉.)' or '∈.)' or '*:.)' or '⊎.)' or '⊄.)' or '⊂.)' or '⊈.)' or '⊆.)' or '∖.)' or '∩.)' or '∪.)' or ',.)' or '∘.)' or '→.)' or '↔.)' or '∨.)' or '∧.)' or '≢.)' or '≡.)' or '≠.)' or '=.)' or '++.)' or '|' or '+++.)' or ':::.)' or 'as' or 'in' or ',' or ')' expected after [term level 200] (in [term]).
  
  [1]
