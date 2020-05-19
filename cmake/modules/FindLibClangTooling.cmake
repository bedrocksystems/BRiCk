find_package(LLVM REQUIRED)
find_package(Clang REQUIRED)

message(STATUS "Found LLVM_VERSION_MAJOR ${LLVM_VERSION_MAJOR}")

# assume clang and llvm have the same major version
# (CLANG_VERSION_MAJOR doesn't appear to be defined)
set(CLANG_VERSION_MAJOR ${LLVM_VERSION_MAJOR})

# --------------------------------------------------------------
# Find Clang Tooling Libraries
#
# On Linux:
# (1) First try to find libclang-cpp.so (some distributions, like
#     Arch, make only this library available as of Clang10)
# (2) If libclang-cpp.so doesn't exist, try to find the individual
#     tooling libraries.
#
# On MacOS:
# (X) Do (2) directly (method 1 links to a library,
#     /usr/local/Cellar/llvm/10.0.0_3/lib/libclang-cpp.dylib, that
#     causes runtime errors related to command-line parsing)
# --------------------------------------------------------------

# Fail unless host system is Linux or MacOS
message(STATUS "Found CMAKE_HOST_SYSTEM_NAME ${CMAKE_HOST_SYSTEM_NAME}")
if (NOT("${CMAKE_HOST_SYSTEM_NAME}" STREQUAL "Linux" OR
        "${CMAKE_HOST_SYSTEM_NAME}" STREQUAL "Darwin"))
  message(FATAL_ERROR "Unsupported platform ${CMAKE_HOST_SYSTEM_NAME}")
endif()

# Method (1): libclang-cpp.so
find_library(LibClangTooling_clang-cpp_LIBRARY NAMES clang-cpp PATHS ${LLVM_LIB_DIR})
if (LibClangTooling_clang-cpp_LIBRARY AND NOT("${CMAKE_HOST_SYSTEM_NAME}" STREQUAL "Darwin"))
  mark_as_advanced(LibClangTooling_clang-cpp_LIBRARY)
  list(APPEND LibClangTooling_LIBRARIES ${LibClangTooling_clang-cpp_LIBRARY})

# Method (2): individual libraries
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
