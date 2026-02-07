# The jank Book - Structure Reference

**Source:** book.jank-lang.org

## Welcome / Foreword

- jank is **alpha quality** -- expect bugs, missing features, and breaking changes.
- A passion project binding **C++** and **Clojure** together.
- The first dynamic language with **seamless C++ interop** combined with **AOT native compilation**.
- Performance is **not yet a priority** -- correctness and compatibility come first.

## Getting Started

### Installation

| Platform | Command |
|----------|---------|
| macOS (Homebrew) | `brew install jank-lang/jank/jank` |
| Ubuntu (apt) | `sudo apt install jank` (via PPA) |
| Arch (AUR) | AUR package available |
| Nix | Nix flake with binary cache |

### Hello World

```clojure
(println "Hello, world!")
```

### Leiningen Projects

jank uses Leiningen as its build tool with `project.clj`:

```clojure
(defproject my-app "0.1.0"
  :dependencies []
  :main my-app.core)
```

- `lein run` -- Run the project via the jank interpreter/JIT.
- `lein compile` -- AOT compile to a native executable.

## C++ Interop

### The `cpp` Namespace

- Contains **special forms** for C++ interop (`cpp/raw`, `cpp/cast`, `cpp/new`, etc.).
- **Disambiguates** jank vs. C++ symbols when names collide.
- **Resolution order:** jank resolves Clojure-style names first, then falls back to C++ lookup.

### Embedding Raw C++ (`cpp/raw`)

```clojure
(cpp/raw "#include <vector>")
(cpp/raw "void my_helper() { /* ... */ }")
```

- Used for `#include` directives and injecting C++ definitions.
- Always operates at **global scope**.
- Always evaluates to **`nil`**.
- **Workaround pattern:** When jank has a bug or limitation, `cpp/raw` can inject the needed C++ directly.

### Native Libraries

#### Compiler Flags

| Flag | Purpose |
|------|---------|
| `-I` | Include paths (header search directories) |
| `-D` | Preprocessor defines |
| `-L` | Library search paths |
| `-l` | Libraries to link |

#### Leiningen Configuration

```clojure
(defproject my-app "0.1.0"
  :jank {:include-dirs ["vendor/include"]
         :library-dirs ["vendor/lib"]
         :linked-libraries ["z" "ssl"]})
```

#### Example: zlib Compression

The book includes a full tutorial on using zlib from jank:

1. Include zlib headers via `cpp/raw`.
2. Call `compress` and `uncompress` functions directly.
3. Use `cpp/new` to allocate buffers and `cpp/aget` for array access.
4. Convert between jank strings and C `char*` via traits.

### Native Values

#### `#cpp` Literals

Tagged literals for efficient C++ values without boxing:

```clojure
#cpp/int 42          ;; C++ int
#cpp/float 3.14      ;; C++ float
#cpp/str "hello"     ;; C++ std::string (or const char*)
```

#### Member Access (`.-foo`)

```clojure
(cpp/.-x my-point)       ;; read member 'x'
(cpp/.-name my-struct)    ;; read member 'name'
```

#### Trait Conversions

- **Implicit** for intrinsic types: `int`, `float`, `double`, `bool`, `std::string`.
- **Custom** via `jank::runtime::convert<T>` specialization:

```cpp
template <>
struct jank::runtime::convert<MyType> {
  static MyType from(object_ptr o) { /* ... */ }
  static object_ptr to(MyType const &v) { /* ... */ }
};
```

#### Opaque Boxes

For types without convert traits:

```clojure
(def b (cpp/box some-cpp-value))     ;; wrap in opaque container
(def v (cpp/unbox b "MyType"))       ;; extract with type check
```

Type safety is enforced at compile time -- unboxing with the wrong type is an error.

#### `cpp/value`

For complex C++ expressions that cannot be expressed as literals:

```clojure
(cpp/value "std::numeric_limits<int>::max()")
```

### Native Types

- C++ `::` namespace separator is replaced with `.` in jank: `std.vector`, `std.string`.
- `cpp/type` for template types: `(cpp/type "std::vector<int>")`.
- **No user-defined types** can be declared in jank syntax yet -- define them via `cpp/raw`.

### Native Functions

#### Global / Static Functions

```clojure
(cpp/raw "#include <cmath>")
(std/sqrt #cpp/float 2.0)
```

#### Overload Resolution

Resolved at **compile time** based on argument types. `#cpp` tagged literals help the compiler pick the right overload by providing exact C++ types.

#### Member Functions

Called using `.foo` syntax on C++ objects:

```clojure
(cpp/raw "#include <string>")
(let [s (cpp/value "std::string" "hello")]
  (.size s)         ;; call member function
  (.substr s 1 3))  ;; with arguments
```

#### Function Pointers

C++ function pointers can be obtained and called.

#### Call Operator

Objects with `operator()` (functors/lambdas) can be called directly.

#### C++ Operators

Operators are called using their C++ syntax within jank's interop forms. Covers arithmetic, comparison, logical, bitwise, assignment, subscript, dereference, and more (45 total).

### Casting

#### `cpp/cast` (Safe)

Equivalent to C++ `static_cast` plus jank's convert traits:

```clojure
(cpp/cast "double" #cpp/int 42)   ;; static_cast<double>(42)
```

#### `cpp/unsafe-cast` (Unsafe)

Equivalent to C-style cast / `reinterpret_cast`:

```clojure
(cpp/unsafe-cast "char*" some-ptr)  ;; reinterpret_cast
```

Use with caution -- no type safety guarantees.

## Differences from Clojure

| Feature | Clojure | jank |
|---------|---------|------|
| Nested `require` | Supported | Not supported |
| `import` | For Java classes | Not available (use `cpp/raw` for includes) |
| Records / Protocols | `defrecord`, `defprotocol` | Not yet implemented |
| Module resolution | Classpath (JVM) | Module path (filesystem-based) |
| `aget` | Regular function | **Special form** (for C++ array interop) |
| `hash-map` | Returns array-map for small maps | Always returns hash-map |
