# zaalang

ZaaLang is basically at heart similar to c++. Most behaviour starts as in c++ with only syntax changes, then diverge as subtleties are changed.

### Basic Types
The primitive types are
 - void
 - bool
 - char (32-bit type)
 - i8, i16, i32, i64
 - u8, u16, u32, u64
 - f32, f64
 - isize, usize (i64 and u64 respectivly, distinct types)
 - int, float (i32 and f64 respectivly, aliased types)
 
Type composition includes the usual pointer (*), array ([]), reference (&) and tuple (()).
Pointers and References are const by default, use "mut" for mutability (eg int mut *)

### Functions
Functions are declared with the "fn" keyword and use trailing return type. Parameters specified type first then name.

``` 
  fn foo(int i, int j) -> bool
  {
    return i == j;
  }
```

Parameters are pass-by-value or reference parameters (&) much like c++. The return type is optional, and will be deduced if unspecified.

### Constants
Constants are declared with the "const" keyword;

``` 
  const PI = 3.14;
```

### Variables
Local variables may be declared with the "var" keyword, the type is always inferred.

``` 
  {
    var x = 1.3;
    var y = f32(9.9);
  }
```

The alternate keyword "let" may be used to designate the variable as non-mutable.

### Statements
Statements include if, for, while, return, etc.

``` 
  fn is_zero(usize width, usize height, u8 *data)
  {   
    var y = 0;

    while (y < height)
    {
      for(var x = 0; x < width; ++x)
      {
        if (*(data + y*width + x) != 0)
          return false;
      }
      
      y += 1;
    }
    
    return true;
  }
```
