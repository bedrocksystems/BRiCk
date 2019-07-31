macro(add_clang_plugin name)
  set (srcs ${ARGN})

  include_directories( "${LLVM_SRC_DIR}/include"
    "${CLANG_SRC_DIR}/include"
    "${LLVM_BUILD_DIR}/include"
    "${CLANG_BUILD_DIR}/include" )
  link_directories( "${LLVM_BUILD_DIR}/lib" )

  add_library( ${name} SHARED ${srcs} )

  if (SYMBOL_FILE)
    set_target_properties( ${name} PROPERTIES LINK_FlAGS
      "-exported_symbols_list ${SYMBOL_FILE}")
  endif()

  foreach (clang_lib ${CLANG_LIBS})
    target_link_libraries( ${name} ${clang_lib} )
  endforeach()

  foreach (llvm_lib ${LLVM_LIBS})
    target_link_libraries( ${name} ${llvm_lib} )
  endforeach()

  foreach (user_lib ${USER_LIBS})
    target_link_libraries( ${name} ${user_lib} )
  endforeach()

endmacro(add_clang_plugin)
