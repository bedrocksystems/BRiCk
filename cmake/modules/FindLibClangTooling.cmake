find_package(LLVM REQUIRED)
find_package(Clang REQUIRED)

message(STATUS "Found LLVM_VERSION_MAJOR ${LLVM_VERSION_MAJOR}")

# assume clang and llvm have the same major version
# (CLANG_VERSION_MAJOR doesn't appear to be defined)
set(CLANG_VERSION_MAJOR ${LLVM_VERSION_MAJOR})

# clang version >= 9 exposes all shared libraries in the single libclang-cpp.so.
# some linux distributions (e.g., arch) have switched to providing just libclang-cpp.so as
# of clang 10 so we first try to find clang-cpp, and fall back otherwise to the
# individual libs.
find_library(LibClangTooling_clang-cpp_LIBRARY NAMES clang-cpp PATHS ${LLVM_LIB_DIR})
if (LibClangTooling_clang-cpp_LIBRARY)
  mark_as_advanced(LibClangTooling_clang-cpp_LIBRARY)
  list(APPEND LibClangTooling_LIBRARIES ${LibClangTooling_clang-cpp_LIBRARY})
else()
  message(STATUS "clang-cpp not available")
  foreach (lib clangTooling clangFrontend clangSerialization clangDriver clangParse clangSema clangAnalysis clangEdit clangAST clangLex clangBasic)
    find_library(LibClangTooling_${lib}_LIBRARY NAMES ${lib} PATHS ${LLVM_LIB_DIR})
    mark_as_advanced(LibClangTooling_${lib}_LIBRARY)
    list(APPEND LibClangTooling_LIBRARIES ${LibClangTooling_${lib}_LIBRARY})
  endforeach()
endif()
message(STATUS "Found LibClangTooling_LIBRARIES ${LibClangTooling_LIBRARIES}")
list(APPEND LibClangTooling_LIBRARIES ${LLVM_LIBRARIES})

set(LibClangTooling_INCLUDE_DIRS ${LLVM_INCLUDE_DIRS})
set(LibClangTooling_DEFINITIONS ${LLVM_DEFINITIONS})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LibClangTooling DEFAULT_MSG LibClangTooling_LIBRARIES LibClangTooling_INCLUDE_DIRS)
