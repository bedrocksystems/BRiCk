cmake_minimum_required(VERSION 2.8)

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
  src/Logging.cpp
  src/ClangPrinter.cpp
  src/ToCoq.cpp
  src/cpp2v.cpp
)

add_clang_plugin(cpp2v_plugin
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
  src/cpp2v_plugin.cpp
)

target_link_libraries(cpp2v
  ${LibClangTooling_LIBRARIES}
)
