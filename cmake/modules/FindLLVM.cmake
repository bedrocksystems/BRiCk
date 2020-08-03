find_program (LLVM_CONFIG
  llvm-config
  NAMES llvm-config-10 llvm-config-9 llvm-config
  DOC "llvm-config program. if this fails, check that you have the -dev dependencies installed")

execute_process(
  COMMAND ${LLVM_CONFIG} --cxxflags
  OUTPUT_VARIABLE LLVM_DEFINITIONS)

execute_process(
  COMMAND ${LLVM_CONFIG} --includedir
  OUTPUT_VARIABLE LLVM_INCLUDE_DIR
  OUTPUT_STRIP_TRAILING_WHITESPACE)

execute_process(
  COMMAND ${LLVM_CONFIG} --libdir
  OUTPUT_VARIABLE LLVM_LIB_DIR
  OUTPUT_STRIP_TRAILING_WHITESPACE)

execute_process(
  COMMAND ${LLVM_CONFIG} --version
  OUTPUT_VARIABLE LLVM_VERSION
  OUTPUT_STRIP_TRAILING_WHITESPACE)

execute_process(
  COMMAND ${LLVM_CONFIG} --system-libs
  OUTPUT_VARIABLE LLVM_SYSTEM_LIBS
  OUTPUT_STRIP_TRAILING_WHITESPACE)

execute_process(
  COMMAND ${LLVM_CONFIG} --libs
  OUTPUT_VARIABLE LLVM_LIBS
  OUTPUT_STRIP_TRAILING_WHITESPACE)

set(LLVM_LIBRARIES ${LLVM_LIBS} ${LLVM_SYSTEM_LIBS})
set(LLVM_INCLUDE_DIRS ${LLVM_INCLUDE_DIR})
set(LLVM_DEFINITIONS ${LLVM_DEFINITIONS} "-fno-rtti")

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LLVM DEFAULT_MSG LLVM_LIBRARIES LLVM_INCLUDE_DIRS)
