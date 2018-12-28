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
)

add_executable(cpp2v
  src/Formatter.cpp
  src/ToCoq.cpp
  src/cpp2v.cpp
)

target_link_libraries(cpp2v
  ${LibClangTooling_LIBRARIES}
)
