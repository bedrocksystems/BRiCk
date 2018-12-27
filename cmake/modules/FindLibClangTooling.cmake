find_package(LLVM REQUIRED)

foreach (lib clangTooling clangFrontend clangSerialization clangDriver clangParse clangSema clangAnalysis clangEdit clangAST clangLex clangBasic)
  find_library(LibClangTooling_${lib}_LIBRARY NAMES ${lib} PATHS ${LLVM_LIB_DIR})
  mark_as_advanced(LibClangTooling_${lib}_LIBRARY)
  list(APPEND LibClangTooling_LIBRARIES ${LibClangTooling_${lib}_LIBRARY})
endforeach()
list(APPEND LibClangTooling_LIBRARIES ${LLVM_LIBRARIES})

set(LibClangTooling_INCLUDE_DIRS ${LLVM_INCLUDE_DIRS})
set(LibClangTooling_DEFINITIONS ${LLVM_DEFINITIONS})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LibClangTooling DEFAULT_MSG LibClangTooling_LIBRARIES LibClangTooling_INCLUDE_DIRS)
