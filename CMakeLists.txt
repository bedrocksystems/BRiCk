##
## Copyright (c) 2020 BedRock Systems, Inc.
## This software is distributed under the terms of the BedRock Open-Source License.
## See the LICENSE-BedRock file in the repository root for details.
##
cmake_minimum_required(VERSION 3.10.2)
project(cpp2v)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14")

# Picks the newest version of clang, see https://github.com/CastXML/CastXML/issues/148
set(CMAKE_FIND_PACKAGE_SORT_ORDER NATURAL)
set(CMAKE_FIND_PACKAGE_SORT_DIRECTION DEC)

find_package(Clang REQUIRED CONFIG)
message(STATUS "Found LLVM: ${LLVM_INSTALL_PREFIX} (version ${LLVM_PACKAGE_VERSION})")
message(STATUS "Using ClangConfig.cmake in: ${CLANG_CMAKE_DIR}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

set(CMAKE_MODULE_PATH
  ${CMAKE_MODULE_PATH}
  "${LLVM_CMAKE_DIR}"
  "${CLANG_CMAKE_DIR}"
)

include(AddLLVM)

include_directories(
  ${LLVM_INCLUDE_DIRS}
  include
  llvm-include
)
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

IF(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/.git)
  FIND_PACKAGE(Git)
  IF(GIT_FOUND)
    EXECUTE_PROCESS(
      COMMAND ${GIT_EXECUTABLE} describe --tags --always
      WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
      OUTPUT_VARIABLE "GIT_VERSION"
      ERROR_QUIET
      OUTPUT_STRIP_TRAILING_WHITESPACE)
    MESSAGE( STATUS "Git version: ${GIT_VERSION}" )
  ELSE(GIT_FOUND)
    SET(GIT_VERSION no-version)
  ENDIF(GIT_FOUND)
ENDIF(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/.git)

add_definitions( -DGIT_VERSION="${GIT_VERSION}")

add_llvm_library(tocoq
  STATIC
  src/Version.cpp
  src/PrintExpr.cpp
  src/PrintStmt.cpp
  src/PrintType.cpp
  src/PrintDecl.cpp
  src/PrintLocalDecl.cpp
  src/ModuleBuilder.cpp
  src/CommentScanner.cpp
  src/SpecWriter.cpp
  src/NotationWriter.cpp
  src/Formatter.cpp
  src/Logging.cpp
  src/ClangPrinter.cpp
  src/ToCoq.cpp
)

set_property(TARGET tocoq PROPERTY POSITION_INDEPENDENT_CODE ON)
add_compile_options(-fno-rtti)

add_llvm_executable(cpp2v
  src/cpp2v.cpp
)


# Link against LLVM/Clang and tocoq libraries
target_link_libraries(cpp2v PUBLIC clang-cpp tocoq)


