# zacc
> Peter Niekamp, 2016 - 2020

A fledgling new programming language in the vein of c++

### Hello World
```
  import std.stdio;
  
  fn main() -> void
  {
    std::print("Hello World!");
  }
```

### Building
GCC, MinGW64 or Clang. Requires LLVM 10.x

```
$ mkdir build
$ pushd build
$ cmake -D CMAKE_BUILD_TYPE=Debug ..
$ cmake --build .
$ popd
```
