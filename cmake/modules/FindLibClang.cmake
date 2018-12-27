find_package(LLVM REQUIRED)

find_library(LibClang_LIBRARY NAMES clang PATHS ${LLVM_LIB_DIR})
mark_as_advanced(LibClang_LIBRARY)

set(LibClang_LIBRARIES ${LibClang_LIBRARY} ${LLVM_LIBRARIES})
set(LibClang_INCLUDE_DIRS ${LLVM_INCLUDE_DIRS})
set(LibClang_DEFINITIONS ${LLVM_DEFINITIONS})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LibClang DEFAULT_MSG LibClang_LIBRARIES LibClang_INCLUDE_DIRS)
