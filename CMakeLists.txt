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

set(CPP2V_LLVM_COMPONENTS support core bitreader)

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

IF (${LLVM_VERSION} VERSION_LESS 11.0.0)
  MESSAGE(STATUS "LLVM version " ${LLVM_VERSION} " less than 11, partial sources not permitted")

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
    src/StringPrettyPrinter.cpp
    src/ToCoq.cpp
    src/FromClang.cpp
  )

  add_llvm_executable(cpp2v
    src/cpp2v.cpp
  )
ELSE(${LLVM_VERSION} VERSION_LESS 11.0.0)
  add_llvm_library(tocoq
    STATIC
    PARTIAL_SOURCES_INTENDED
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
    src/StringPrettyPrinter.cpp
    src/ToCoq.cpp
    src/FromClang.cpp
  )

  add_llvm_executable(cpp2v
    PARTIAL_SOURCES_INTENDED
    src/cpp2v.cpp
    )
ENDIF(${LLVM_VERSION} VERSION_LESS 11.0.0)

set_property(TARGET tocoq PROPERTY POSITION_INDEPENDENT_CODE ON)
add_compile_options(-fno-rtti)

# TODO(franta) Older versions of LLVM are affected with the following
# bug in LLVM:
#
# https://bugs.llvm.org/show_bug.cgi?id=35245
#
# eventually, the bellow monolithic/component mapping should be replaced
# with simple
#
# set(CPP2V_LLVM_COMPONENTS support core bitreader)
# llvm_config(cpp2v USE_SHARED ${CPP2V_LLVM_COMPONENTS})
#
find_library(LLVM_MONO_LIB LLVM ${LLVM_LIBRARY_DIR})
if(NOT LLVM_MONO_LIB)
  message(STATUS "Monolithic LLVM library not found, gathering component libraries...")

  llvm_map_components_to_libnames(llvm_libs ${CPP2V_LLVM_COMPONENTS})
  foreach(lib_name ${llvm_libs})
    find_library(${lib_name}_found ${lib_name} ${LLVM_LIBRARY_DIR})
    if(NOT ${lib_name}_found)
        message(FATAL_ERROR "Library (LLVM component) not found: ${lib_name}")
    endif(NOT ${lib_name}_found)

    message(STATUS "Linking against LLVM component: ${lib_name} (${${lib_name}_found})")
  endforeach(lib_name ${llvm_libs})
else(NOT LLVM_MONO_LIB)
  set(llvm_libs)
  message(STATUS "Linking against monolithic libLLVM (${LLVM_MONO_LIB})")
endif(NOT LLVM_MONO_LIB)
#
# END TODO(franta)
#

# Link against LLVM/Clang and tocoq libraries
target_link_libraries(cpp2v PUBLIC ${llvm_libs} clang-cpp tocoq)


target_compile_options(tocoq PUBLIC -Wall -Wimplicit-fallthrough)
# This PUBLIC setting gets inherited by clients. That's good enough without
# external clients; otherwise, we'd enable warnings for cpp2v as well.
# target_compile_options(cpp2v PRIVATE -Wall -Wimplicit-fallthrough)
