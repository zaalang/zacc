## zaalang static analysis, May 2024

To acheive, not memory safety in any rigouous manner, but compiler assistance in highlighting code that is likely to produce invalid results, zaalang employs a static analysis phase combining annotations with dependancy tracking. The aim here is to specifically catch the categories of errors occuring from use after free, pointer/iterator invalidation and use of consumed/dropped objects.

1) Dangling

    The primary technique used is to track the relation upon which an object may depend.
  
    ```
        fn main
        {
          var x = 99;  // (1) 
          var y = &x;  // (2) 
          var z = y;   // (3) 
        }
    ```

    The compiler tracks dependancies within a function body. For example, (1) declares a local variable `x` which has no dependancies. (2) variable `y` is a pointer, marked as depending upon variable `x`. (3) is a pointer initialised with `y`, hence clones the dependancies of `y`, that is, will depend upon variable `x`.
    
    When referenced, a variables dependancies are checked. If any have gone out of scope, a potentially dangling error is reported.
    
    Tracking dependancies through a function call is acheived either via the use of annotations on the function signature, or through the use of the previously analysed function body.
    
    ```
        fn foo(int *i)
        {
          return i;
        }

        fn main
        {
          var x = 99;      // (1)
          var y = foo(&x); // (2)
        }
    ```

    Here the compiler processes function `foo`, notes that the return value has dependancies that are a clone of parameter `i`. When processing (2), that clone will be applied, resulting in `y` depending on variable `x`.
    
    Alternatly, an annotation on foo can be used, eg. `#[lifetime(depends(*i))]` to give the same effect.
    
    Function return values and output parameters are tracked.

    Example:
    
    ```
        fn foo(int *i, int *j)
        {
          return [i, j];
        }

        fn main() -> int
        {
          var x = 99;
          var y = 11;

          var vec = foo(&x, &y);  // (1) vec depends on x and y

          {
            var z = 42;
            vec = foo(&y, &z);    // (2) vec depends on y and z
          }

          return *vec[0];         // (3) access vec, but z out of scope
        }
        
        test.zaa:in function 'fn main() -> i32'
        test.zaa:19:14: error: potentially dangling variable access
          return *vec[0];
                     ^
    ```
    
2) Poisoned

    Pointers and iterators may be invalidated due to internal relocation of memory, typically on container like objects such as string and vector.
    
    In these cases, an annotation `poison(arg)` can be used to indicate a function may invalidate anything that depends upon that parameter.
    
    The dependancies tracked above are used to mark variables as poisoned and any subsequent use will trigger an error.
    
    ```
        import std.string;

        #[lifetime(poison(str))]
        fn foo(std::string mut &str)
        {
          // modify the string ...
        }

        fn main() -> int
        {
          var str = std::string("Hello");
          var front = &str[0];

          foo(&mut str);

          std::print(*front);

          return 0;
        }

        test.zaa:in function 'fn main() -> i32'
        test.zaa:17:14: error: potentially poisoned variable access
        std::print(*front);
                  ^
    ```

    Poisoning is usually a viral operation (like const) in that any function that poisons its parameters should also be annotated with poison. However, this is not currently enforced by the compiler.
    
3) Consumed

    An annotation `consume(arg)` can be used to indicate that a function consumes a parameter and hence any further use should result in an error. Indended use is to prevent moved from objects being reused.
    
    An additional annotation `launder(arg)` can be used to restore access to the moved from object, such as for a reassignment or clear operations.

    Consuming is also a viral operation (like poison). However, this is not currently enforced by the compiler.

## Examples

Example 1: vector of pointers, pointee goes out of scope

```
    import std.stdio;
    import std.vector;

    fn main() -> int
    {
      var vec = std::vector<int *>();

      var i = 99;
      vec.push_back(&i);

      {
        var j = 99;
        vec.push_back(&j);
      }

      std::print(vec);

      return 0;
    }
    
    test.zaa:in function 'fn main() -> i32'
    test.zaa:17:3: error: potentially dangling variable access
        std::print(vec);
        ^
```

Example 2: invalidated vector iterator within loop

```
    import std.stdio;
    import std.vector;

    fn main() -> int
    {
      var vec = std::vector<int>::from([1, 2, 3, 4]);

      for (var i : vec)
      {
        vec.push_back(2*i);  // push_back poisons the vector
      }

      std::print(vec);

      return 0;
    }
    
    test.zaa:in function 'fn main() -> i32'
    test.zaa:9:3: error: potentially poisoned variable access
        for (var i : vec)
        ^
```

Example 3: out of scope string_view within vector across function call parameter
```
    import std.stdio;
    import std.vector;

    fn split(std::vector<std::string_view> mut &vec, std::string &str) -> void
    {
      for (var word : str.words)
        vec.push_back(word);
    }

    fn main() -> int
    {
      var vec = std::vector<std::string_view>();

      {
        var str = std::string("Hello World");

        split(&mut vec, str);
      }

      std::print(vec);

      return 0;
    }

    test.zaa:in function 'fn main() -> i32'
    test.zaa:21:3: error: potentially dangling variable access
        std::print(vec);
        ^
```
