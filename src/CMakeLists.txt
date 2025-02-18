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
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /wd4244 /wd4800 /wd4267 /wd4146 /wd4814 /Zc:__cplusplus")
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
set(SRCS ${SRCS} ident.h ident.cpp)
set(SRCS ${SRCS} mangle.h mangle.cpp)
set(SRCS ${SRCS} numeric.h numeric.cpp)
set(SRCS ${SRCS} builtins.h builtins.cpp)
set(SRCS ${SRCS} diag.h diag.cpp)
set(SRCS ${SRCS} parser.h parser.cpp)
set(SRCS ${SRCS} semantic.h semantic.cpp)
set(SRCS ${SRCS} mir.h mir.cpp)
set(SRCS ${SRCS} visitor.h)
set(SRCS ${SRCS} query.h query.cpp)
set(SRCS ${SRCS} typer.h typer.cpp)
set(SRCS ${SRCS} lower.h lower.cpp)
set(SRCS ${SRCS} interp.h interp.cpp)
set(SRCS ${SRCS} copier.h copier.cpp)
set(SRCS ${SRCS} codegen.h codegen.cpp)
set(SRCS ${SRCS} lifetime.h lifetime.cpp)
set(SRCS ${SRCS} toolchain.h toolchain.cpp)
set(SRCS ${SRCS} depgen.h depgen.cpp)

add_executable(zacc ${SRCS}
  depgen.h
  depgen.cpp)

if(LLVM_LINK_LLVM_DYLIB)
  llvm_config(zacc USE_SHARED support core analysis target mc ipo native vectorize passes)
else(LLVM_LINK_LLVM_DYLIB) 
  llvm_config(zacc support core analysis target mc ipo native vectorize passes)
endif(LLVM_LINK_LLVM_DYLIB)

if(MINGW)
  target_link_libraries(zacc PRIVATE mingw32)
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static -static-libgcc -static-libstdc++")
endif(MINGW)

#
# install
#

INSTALL(TARGETS zacc DESTINATION bin)
