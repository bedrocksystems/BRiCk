set( LLVM_LINK_COMPONENTS
  ${LLVM_TARGETS_TO_BUILD}
  Option
  Support
  )

include_directories(include)

add_clang_executable(cpp2v
  src/ToCoq.cpp
  cpp2v.cpp
  )

target_link_libraries(cpp2v
  PRIVATE
  clangAST
  clangBasic
  clangDriver
  clangFrontend
  clangTooling
  )

install(TARGETS cpp2v
  RUNTIME DESTINATION bin)
