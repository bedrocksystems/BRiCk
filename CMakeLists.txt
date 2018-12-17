set( LLVM_LINK_COMPONENTS
  ${LLVM_TARGETS_TO_BUILD}
  Option
  Support
  )

add_clang_executable(cpp2v
  cpp2v.cpp
  )

target_link_libraries(cpp2v
  PRIVATE
  clangAST
  clangBasic
  clangDriver
  clangFrontend
  clangRewriteFrontend
  clangStaticAnalyzerFrontend
  clangTooling
  )

install(TARGETS cpp2v
  RUNTIME DESTINATION bin)
