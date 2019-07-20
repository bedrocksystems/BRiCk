cmake_minimum_required(VERSION 2.8)

set(CMAKE_MODULE_PATH
  ${CMAKE_MODULE_PATH}
  "${CMAKE_SOURCE_DIR}/cmake/modules"
)

find_package(LibClangTooling REQUIRED)

add_definitions(${LibClangTooling_DEFINITIONS})

include_directories(
  ${LibClangTooling_INCLUDE_DIRS}
  include
  llvm-include
)

add_executable(cpp2v
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
  src/ToCoq.cpp
  src/cpp2v.cpp
  src/ClangPrinter.cpp
)

target_link_libraries(cpp2v
  ${LibClangTooling_LIBRARIES}
)
