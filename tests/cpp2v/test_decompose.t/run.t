  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -names test_17_cpp_names.v -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp_names.v
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  File "./test_17_cpp.v", line 13609, characters 61-72:
  Error: Unable to unify "[]" with
   "["std::__make_signed<unsigned long>::~__make_signed()"%cpp_field;
     "std::__make_signed<unsigned long>::operator=(std::__make_signed<unsigned long>&&)"%cpp_field;
     "std::__make_signed<unsigned long>::__make_signed(std::__make_signed<unsigned long>&&)"%cpp_field;
     "std::__make_signed<unsigned long>::operator=(const std::__make_signed<unsigned long>&)"%cpp_field;
     "std::__make_signed<unsigned long>::__make_signed(const std::__make_signed<unsigned long>&)"%cpp_field;
     "std::__make_signed<unsigned long>::__make_signed()"%cpp_field;
     "std::__make_signed<unsigned long>"%cpp_name;
     "std::__make_unsigned<long>::~__make_unsigned()"%cpp_field;
     "std::__make_unsigned<long>::operator=(std::__make_unsigned<long>&&)"%cpp_field;
     "std::__make_unsigned<long>::__make_unsigned(std::__make_unsigned<long>&&)"%cpp_field;
     "std::__make_unsigned<long>::operator=(const std::__make_unsigned<long>&)"%cpp_field;
     "std::__make_unsigned<long>::__make_unsigned(const std::__make_unsigned<long>&)"%cpp_field;
     "std::__make_unsigned<long>::__make_unsigned()"%cpp_field;
     "std::__make_unsigned<long>"%cpp_name;
     "std::__is_integral_helper<unsigned long>::~__is_integral_helper()"%cpp_field;
     "std::__is_integral_helper<unsigned long>::operator=(std::__is_integral_helper<unsigned long>&&)"%cpp_field;
     "std::__is_integral_helper<unsigned long>::__is_integral_helper(std::__is_integral_helper<unsigned long>&&)"%cpp_field;
     "std::__is_integral_helper<unsigned long>::operator=(const std::__is_integral_helper<unsigned long>&)"%cpp_field;
     "std::__is_integral_helper<unsigned long>::__is_integral_helper(const std::__is_integral_helper<unsigned long>&)"%cpp_field;
     "std::__is_integral_helper<unsigned long>::__is_integral_helper()"%cpp_field;
     "std::__is_integral_helper<unsigned long>"%cpp_name;
     "std::__is_integral_helper<long>::~__is_integral_helper()"%cpp_field;
     "std::__is_integral_helper<long>::operator=(std::__is_integral_helper<long>&&)"%cpp_field;
     "std::__is_integral_helper<long>::__is_integral_helper(std::__is_integral_helper<long>&&)"%cpp_field;
     "std::__is_integral_helper<long>::operator=(const std::__is_integral_helper<long>&)"%cpp_field;
     "std::__is_integral_helper<long>::__is_integral_helper(const std::__is_integral_helper<long>&)"%cpp_field;
     "std::__is_integral_helper<long>::__is_integral_helper()"%cpp_field;
     "std::__is_integral_helper<long>"%cpp_name]".
  
  
  [1]
