# zaalang
> Peter Niekamp, 2021

A fledgling new programming language in the vein of c++

### Hello World
```
  import std.stdio;
  
  fn main() -> void
  {
    std::print("Hello World!");
  }
```

## Language Overview
see [overview.md](https://github.com/zaalang/zacc/blob/master/overview.md)
see [overview.md](overview.md)

## Getting Started
The compiler, the runtime and the standard library are all needed to get a basic toolchain up and running...
```
$ mkdir zaalang
$ pushd zaalang
$ git clone https://github.com/zaalang/zacc
$ git clone https://github.com/zaalang/zrt
$ git clone https://github.com/zaalang/std
```

Further, requires LLVM 10.x/11.x. This can be installed from the os repositories or compiled from source. See https://llvm.org/docs/GettingStarted.html

#### Building with GCC, MinGW64 or Clang.
```
$ mkdir zacc/build
$ pushd zacc/build
$ cmake -D CMAKE_BUILD_TYPE=RelWithDebInfo ..
$ cmake --build . --target install
$ popd
```
```
$ mkdir zrt/build
$ pushd zrt/build
$ cmake -D CMAKE_BUILD_TYPE=RelWithDebInfo ..
$ cmake --build . --target install
$ popd
```

#### Building with MSVC.
```
> mkdir zacc\build
> pushd zacc\build
> cmake -G "Visual Studio 16 2019" -A x64 -DLLVM_DIR=llvm\lib\cmake\llvm ..
> cmake --build . --target install --config RelWithDebInfo
> popd
```
```
> mkdir zrt\build
> pushd zrt\build
> cmake -G "Visual Studio 16 2019" -A x64 ..
> cmake --build . --target install --config RelWithDebInfo
> popd
```

### Compiling a program
The compiler needs to be provided with any include paths (-I), paths to library folders (-L) and libraries to link (-l)

Create a test.zaa file containing the hello world text listed above. Then the compile command is :

#### Linux
```
$ zacc/bin/zacc -I ./std -L ./zrt/lib test.zaa -lzrt
```

#### Windows
```
> zacc\bin\zacc.exe -I .\std -L .\zrt\lib test.zaa -lzrt -lkernel32
```
