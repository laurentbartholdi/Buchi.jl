cmake_minimum_required(VERSION 3.5)

project(SpotBuchi)

set(CMAKE_MACOSX_RPATH 1)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib")

include_directories("${Spot_DIR}/include")
link_directories("${Spot_DIR}/lib")

message(STATUS "Found Spot at ${Spot_DIR}")

find_package(JlCxx)
get_target_property(JlCxx_location JlCxx::cxxwrap_julia LOCATION)
get_filename_component(JlCxx_location ${JlCxx_location} DIRECTORY)
set(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib;${JlCxx_location}")

message(STATUS "Found JlCxx at ${JlCxx_location}")

add_library(spot_buchi SHARED spot_buchi.cpp)

target_link_libraries(spot_buchi JlCxx::cxxwrap_julia JlCxx::cxxwrap_julia_stl spot bddx)

install(TARGETS
  spot_buchi
LIBRARY DESTINATION lib
ARCHIVE DESTINATION lib
RUNTIME DESTINATION lib)
