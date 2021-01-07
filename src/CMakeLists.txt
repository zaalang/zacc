#
# zacc
#

set(CMAKE_CXX_STANDARD 17)

if(UNIX OR MINGW)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wfloat-conversion -Wno-unused-parameter -Wno-missing-field-initializers -Wno-uninitialized")
endif(UNIX OR MINGW)

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-missing-braces -Wno-char-subscripts")
endif()

if(MSVC)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /wd4244 /wd4800 /wd4267 /wd4146 /wd4814")
endif(MSVC)

if(WIN32)
  add_definitions(-DWIN32_LEAN_AND_MEAN -DNOMINMAX -D_CRT_SECURE_NO_WARNINGS -D_WINSOCK_DEPRECATED_NO_WARNINGS)
endif(WIN32)

include_directories(${PROJECT_SOURCE_DIR}/include)
include_directories(${LLVM_INCLUDE_DIRS})

add_definitions(${LLVM_DEFINITIONS})

set(SRCS ${SRCS} main.cpp)
set(SRCS ${SRCS} util.h)
set(SRCS ${SRCS} lexer.h lexer.cpp)
set(SRCS ${SRCS} ast.h ast.cpp)
set(SRCS ${SRCS} decl.h decl.cpp)
set(SRCS ${SRCS} expr.h expr.cpp)
set(SRCS ${SRCS} stmt.h stmt.cpp)
set(SRCS ${SRCS} type.h type.cpp)
set(SRCS ${SRCS} sema.h sema.cpp)
set(SRCS ${SRCS} mangle.h mangle.cpp)
set(SRCS ${SRCS} numeric.h numeric.cpp)
set(SRCS ${SRCS} builtins.h builtins.cpp)
set(SRCS ${SRCS} diag.h diag.cpp)
set(SRCS ${SRCS} parser.h parser.cpp)
set(SRCS ${SRCS} semantic.h semantic.cpp)
set(SRCS ${SRCS} mir.h mir.cpp)
set(SRCS ${SRCS} query.h query.cpp)
set(SRCS ${SRCS} typer.h typer.cpp)
set(SRCS ${SRCS} lower.h lower.cpp)
set(SRCS ${SRCS} interp.h interp.cpp)
set(SRCS ${SRCS} codegen.h codegen.cpp)
set(SRCS ${SRCS} toolchain.h toolchain.cpp)

add_executable(zacc ${SRCS})

llvm_map_components_to_libnames(llvm_libs support core analysis target mc ipo native vectorize passes)

target_link_libraries(zacc ${llvm_libs})

if(MINGW)
  target_link_libraries(zacc mingw32)
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static -static-libgcc -static-libstdc++")
endif(MINGW)

#
# install
#

INSTALL(TARGETS zacc DESTINATION bin)
