##
## Copyright (c) 2020 BedRock Systems, Inc.
## This software is distributed under the terms of the BedRock Open-Source License.
## See the LICENSE-BedRock file in the repository root for details.
##
cmake_minimum_required(VERSION 2.8...3.19)
project(cpp2v)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14")

set(CMAKE_MODULE_PATH
  ${CMAKE_MODULE_PATH}
  "${CMAKE_SOURCE_DIR}/cmake/modules"
)

# Picks the newest version of clang, see https://github.com/CastXML/CastXML/issues/148
set(CMAKE_FIND_PACKAGE_SORT_ORDER NATURAL)
set(CMAKE_FIND_PACKAGE_SORT_DIRECTION DEC)

find_package(LibClangTooling REQUIRED)

add_definitions(${LibClangTooling_DEFINITIONS})

include_directories(
  ${LibClangTooling_INCLUDE_DIRS}
  include
  llvm-include
)

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

add_library(tocoq
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
IF (APPLE)
   message(STATUS "Apple environment detected")
   set(CMAKE_MACOSX_RPATH ON)

   IF (DEFINED "CLANG_DIR")
      message(STATUS "Building under Nix")
      return ()
   ENDIF ()

   # LLVM_LIB_DIR defined in cmake/modules/FindLLVM.cmake
   set(CMAKE_EXE_LINKER_FLAGS "-L${LLVM_LIB_DIR}")
ENDIF (APPLE)

add_executable(cpp2v
  src/cpp2v.cpp
)

target_link_libraries(cpp2v
  ${LibClangTooling_LIBRARIES}
  tocoq
)
