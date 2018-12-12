cmake_minimum_required(VERSION 3.13)

# Parse version information
file(STRINGS "${CMAKE_CURRENT_SOURCE_DIR}/lib/lz4.h" LZ4_VERSION_MAJOR REGEX "^#define LZ4_VERSION_MAJOR +([0-9]+) +.*$")
string(REGEX REPLACE "^#define LZ4_VERSION_MAJOR +([0-9]+) +.*$" "\\1" LZ4_VERSION_MAJOR "${LZ4_VERSION_MAJOR}")
file(STRINGS "${CMAKE_CURRENT_SOURCE_DIR}/lib/lz4.h" LZ4_VERSION_MINOR REGEX "^#define LZ4_VERSION_MINOR +([0-9]+) +.*$")
string(REGEX REPLACE "^#define LZ4_VERSION_MINOR +([0-9]+) +.*$" "\\1" LZ4_VERSION_MINOR "${LZ4_VERSION_MINOR}")
file(STRINGS "${CMAKE_CURRENT_SOURCE_DIR}/lib/lz4.h" LZ4_VERSION_RELEASE REGEX "^#define LZ4_VERSION_RELEASE +([0-9]+) +.*$")
string(REGEX REPLACE "^#define LZ4_VERSION_RELEASE +([0-9]+) +.*$" "\\1" LZ4_VERSION_RELEASE "${LZ4_VERSION_RELEASE}")
set(LZ4_VERSION_STRING "${LZ4_VERSION_MAJOR}.${LZ4_VERSION_MINOR}.${LZ4_VERSION_RELEASE}")
mark_as_advanced(LZ4_VERSION_STRING LZ4_VERSION_MAJOR LZ4_VERSION_MINOR LZ4_VERSION_RELEASE)

project(lz4
    VERSION ${LZ4_VERSION_STRING}
    LANGUAGES C)

set(sources 
    lib/lz4.h 
    lib/lz4hc.h 
    lib/lz4opt.h
    lib/lz4.c 
    lib/lz4hc.c
)

add_library(lz4
    STATIC ${sources}
)
target_include_directories(lz4 
    PUBLIC include-fwd
)

if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
endif()
