find_package(LLVM REQUIRED)

find_library(LibClang_LIBRARY NAMES clang PATHS ${LLVM_LIB_DIR})
mark_as_advanced(LibClang_LIBRARY)

set(LibClang_LIBRARIES ${LibClang_LIBRARY} ${LLVM_LIBRARIES})
set(LibClang_INCLUDE_DIRS "$ENV{CLANG_DIR}/include;${LLVM_INCLUDE_DIRS}")
set(LibClang_DEFINITIONS ${LLVM_DEFINITIONS})
set(CLANG_INCLUDE_DIR $ENV{CLANG_DIR}/include)
set(CLANG_LIB_DIR $ENV{CLANG_DIR}/lib)

message(NOTICE CLANG_LIB_DIR " " ${CLANG_LIB_DIR})
message(NOTICE CLANG_INCLUDE_DIR " " ${CLANG_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LibClang DEFAULT_MSG LibClang_LIBRARIES LibClang_INCLUDE_DIRS)
