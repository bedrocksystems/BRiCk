Clang rejects every sized use of [void] in C++, so neither [wp_operand_sizeof]
nor pointer arithmetic can observe [size_of Tvoid] (see the comment on
[size_of] in [skylabs.lang.cpp.semantics.types]).

Positive control: ordinary [void*] uses (conversions, comparisons, passing)
are accepted.

  $ check_cpp2v ok.cpp
  cpp2v -v -check-types -o ok_17_cpp.v ok.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix ok_17_cpp.v

Each sized use of [void] is an error: [sizeof], [alignof] (also GNU's
[__alignof__]), [void*] arithmetic
([+], [-], [++], [--], [+=], [-=]), [void*] difference, dereference,
subscript, and arrays of [void].

  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/test.cpp:7:31: error: invalid application of 'sizeof' to an incomplete type 'void'
  unsigned long size() { return sizeof(void); }
                                ^     ~~~~~~
  $TESTCASE_ROOT/test.cpp:8:32: error: invalid application of 'alignof' to an incomplete type 'void'
  unsigned long align() { return alignof(void); }
                                 ^      ~~~~~~
  $TESTCASE_ROOT/test.cpp:9:36: error: invalid application of '__alignof' to an incomplete type 'void'
  unsigned long gnu_align() { return __alignof__(void); }
                                     ^          ~~~~~~
  $TESTCASE_ROOT/test.cpp:11:31: error: arithmetic on a pointer to void
  void *add(void *p) { return p + 1; }
                              ~ ^
  $TESTCASE_ROOT/test.cpp:12:31: error: arithmetic on a pointer to void
  void *sub(void *p) { return p - 1; }
                              ~ ^
  $TESTCASE_ROOT/test.cpp:13:24: error: arithmetic on a pointer to void
  void preinc(void *p) { ++p; }
                         ^ ~
  $TESTCASE_ROOT/test.cpp:14:26: error: arithmetic on a pointer to void
  void postinc(void *p) { p++; }
                          ~^
  $TESTCASE_ROOT/test.cpp:15:24: error: arithmetic on a pointer to void
  void predec(void *p) { --p; }
                         ^ ~
  $TESTCASE_ROOT/test.cpp:16:26: error: arithmetic on a pointer to void
  void postdec(void *p) { p--; }
                          ~^
  $TESTCASE_ROOT/test.cpp:17:30: error: arithmetic on a pointer to void
  void add_assign(void *p) { p += 1; }
                             ~ ^
  $TESTCASE_ROOT/test.cpp:18:30: error: arithmetic on a pointer to void
  void sub_assign(void *p) { p -= 1; }
                             ~ ^
  $TESTCASE_ROOT/test.cpp:19:40: error: arithmetic on pointers to void
  long diff(void *p, void *q) { return p - q; }
                                       ~ ^ ~
  $TESTCASE_ROOT/test.cpp:21:29: error: indirection not permitted on operand of type 'void *'
  void deref(void *p) { (void)*p; }
                              ^~
  $TESTCASE_ROOT/test.cpp:22:34: error: subscript of pointer to incomplete type 'void'
  void subscript(void *p) { (void)p[0]; }
                                  ~^
  $TESTCASE_ROOT/test.cpp:24:9: error: array has incomplete element type 'void'
  void arr[2];
          ^
  15 errors generated.
  Error while processing $TESTCASE_ROOT/test.cpp.
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  Error: Can't find file ./test_17_cpp.v
  [1]

GNU dialects do not change this: unlike GNU C, where [sizeof(void)] is 1 and
[void*] arithmetic has a one-byte stride, clang rejects the same uses under
[-std=gnu++17] and [-std=gnu++23] ([CRAM_CXXFLAGS] comes after the default
[-std=c++N], so it takes precedence).

  $ CRAM_CXXFLAGS=-std=gnu++17 check_cpp2v test.cpp 2>&1 | grep -E -- '-std=|error:|errors generated'
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 -std=gnu++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/test.cpp:7:31: error: invalid application of 'sizeof' to an incomplete type 'void'
  $TESTCASE_ROOT/test.cpp:8:32: error: invalid application of 'alignof' to an incomplete type 'void'
  $TESTCASE_ROOT/test.cpp:9:36: error: invalid application of '__alignof' to an incomplete type 'void'
  $TESTCASE_ROOT/test.cpp:11:31: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:12:31: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:13:24: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:14:26: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:15:24: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:16:26: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:17:30: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:18:30: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:19:40: error: arithmetic on pointers to void
  $TESTCASE_ROOT/test.cpp:21:29: error: indirection not permitted on operand of type 'void *'
  $TESTCASE_ROOT/test.cpp:22:34: error: subscript of pointer to incomplete type 'void'
  $TESTCASE_ROOT/test.cpp:24:9: error: array has incomplete element type 'void'
  15 errors generated.
  [1]

  $ CRAM_CXXFLAGS=-std=gnu++23 check_cpp2v_versions test.cpp 23 2>&1 | grep -E -- '-std=|error:|errors generated'
  cpp2v -v -check-types -o test_23_cpp.v test.cpp -- -std=c++23 -std=gnu++23 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/test.cpp:7:31: error: invalid application of 'sizeof' to an incomplete type 'void'
  $TESTCASE_ROOT/test.cpp:8:32: error: invalid application of 'alignof' to an incomplete type 'void'
  $TESTCASE_ROOT/test.cpp:9:36: error: invalid application of '__alignof' to an incomplete type 'void'
  $TESTCASE_ROOT/test.cpp:11:31: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:12:31: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:13:24: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:14:26: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:15:24: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:16:26: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:17:30: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:18:30: error: arithmetic on a pointer to void
  $TESTCASE_ROOT/test.cpp:19:40: error: arithmetic on pointers to void
  $TESTCASE_ROOT/test.cpp:21:29: error: indirection not permitted on operand of type 'void *'
  $TESTCASE_ROOT/test.cpp:22:34: error: subscript of pointer to incomplete type 'void'
  $TESTCASE_ROOT/test.cpp:24:9: error: array has incomplete element type 'void'
  15 errors generated.
  [1]
