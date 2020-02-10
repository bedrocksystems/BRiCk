cmake_minimum_required(VERSION 2.8)
project(cpp2v)

set(CMAKE_MODULE_PATH
  ${CMAKE_MODULE_PATH}
  "${CMAKE_SOURCE_DIR}/cmake/modules"
)

find_package(LibClangTooling REQUIRED)
find_package(ClangPlugin REQUIRED)

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
  src/PrintParam.cpp
  src/PrintDecl.cpp
  src/PrintLocalDecl.cpp
  src/ModuleBuilder.cpp
  src/CommentScanner.cpp
  src/SpecWriter.cpp
  src/Formatter.cpp
  src/Logging.cpp
  src/ClangPrinter.cpp
  src/ToCoq.cpp
)
set_property(TARGET tocoq PROPERTY POSITION_INDEPENDENT_CODE ON)

add_executable(cpp2v
  src/cpp2v.cpp
)

add_clang_plugin(cpp2v_plugin
  src/cpp2v_plugin.cpp
)

target_link_libraries(cpp2v
  ${LibClangTooling_LIBRARIES}
  tocoq
)

target_link_libraries(cpp2v_plugin
  tocoq
)
