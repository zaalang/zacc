# zaalang
> Peter Niekamp, 2022

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
see [https://zaalang.readthedocs.io](https://zaalang.readthedocs.io/en/latest/overview.html)

## Getting Started
The compiler, the runtime and the standard library are all needed to get a basic toolchain up and running...
```
$ mkdir zaalang
$ pushd zaalang
$ git clone https://github.com/zaalang/zacc
$ git clone https://github.com/zaalang/zrt
$ git clone https://github.com/zaalang/std
```

Further, requires LLVM 12.x. This can be installed from the os repositories or compiled from source. See https://llvm.org/docs/GettingStarted.html

#### Building with GCC, MinGW64 or Clang.
```
$ mkdir zacc/build
$ pushd zacc/build
$ cmake -DCMAKE_BUILD_TYPE=RelWithDebInfo ..
$ cmake --build . --target install
$ popd
```
```
$ mkdir zrt/build
$ pushd zrt/build
$ cmake -DCMAKE_BUILD_TYPE=RelWithDebInfo ..
$ cmake --build . --target install
$ popd
```

#### Building with MSVC.
```
> mkdir zacc\build
> pushd zacc\build
> cmake -Thost=x64 -DLLVM_DIR=llvm\lib\cmake\llvm ..
> cmake --build . --target install --config RelWithDebInfo
> popd
```
```
> mkdir zrt\build
> pushd zrt\build
> cmake -Thost=x64 ..
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

## Another Example

```
  import std.stdio;
  
  struct as_tuple_t<T>
  {
    #{                                    // compile time block in declaritive context
      var tuple = $typename ();           // type reflection of empty tuple
  
      #for(const k : std::meta::fields_of($T))
        tuple = std::meta::tuple_append(tuple, $T::#k);  // append reflection of field
  
      -> { using type = $(tuple); }       // injection of type alias into struct scope
    }
  }
  
  using as_tuple<T> = as_tuple_t<T>::type;
  
  fn main
  {
    struct X
    {
      i32 i;
      f64 j;
      bool k;
    }
  
    std::assert(std::is_same<as_tuple<X>, (i32, f64, bool)>);
  }
```
