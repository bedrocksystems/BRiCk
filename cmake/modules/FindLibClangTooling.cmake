find_package(LLVM REQUIRED)
find_package(Clang REQUIRED)

message(STATUS "Found LLVM ${LLVM_VERSION_MAJOR}")

# assume clang and llvm have the same major version
# (CLANG_VERSION_MAJOR doesn't appear to be defined)
set(CLANG_VERSION_MAJOR ${LLVM_VERSION_MAJOR})

# clang version >= 9 exposes all shared libraries in the single libclang-cpp.so.
# some distributions have switched to providing just libclang-cpp.so as of clang 10,
# hence the gating on CLANG_VERSION_MAJOR.
if (${CLANG_VERSION_MAJOR} GREATER_EQUAL 9)
  set(CLANG_LIBS clang-cpp)
else()
  set(CLANG_LIBS clangTooling clangFrontend clangSerialization clangDriver clangParse clangSema clangAnalysis clangEdit clangAST clangLex clangBasic)
endif()

foreach (lib ${CLANG_LIBS})
  find_library(LibClangTooling_${lib}_LIBRARY NAMES ${lib} PATHS ${LLVM_LIB_DIR})
  mark_as_advanced(LibClangTooling_${lib}_LIBRARY)
  list(APPEND LibClangTooling_LIBRARIES ${LibClangTooling_${lib}_LIBRARY})
endforeach()
list(APPEND LibClangTooling_LIBRARIES ${LLVM_LIBRARIES})

set(LibClangTooling_INCLUDE_DIRS ${LLVM_INCLUDE_DIRS})
set(LibClangTooling_DEFINITIONS ${LLVM_DEFINITIONS})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LibClangTooling DEFAULT_MSG LibClangTooling_LIBRARIES LibClangTooling_INCLUDE_DIRS)
