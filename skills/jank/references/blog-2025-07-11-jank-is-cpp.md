# jank is C++

**Date:** July 11, 2025
**Source:** jank blog

## Overview

This post demonstrates that jank is not merely interoperating with C++ -- it *is* C++. The interop is deep enough to use real-world C++ libraries directly from jank with no wrappers or bindings.

## Memory Management

### `cpp/new` and `cpp/delete`
jank provides explicit C++ memory management:

```clojure
(let [p (cpp/new SomeType args...)]
  ;; use p
  (cpp/delete p))
```

### Boehm GC (bdwgc)
jank uses the Boehm-Demers-Weiser conservative garbage collector. `cpp/new` allocates through bdwgc by default, meaning C++ objects allocated from jank are garbage-collected. `cpp/delete` is available for explicit cleanup when needed (e.g., RAII resources).

## C++ Booleans

`cpp/true` and `cpp/false` provide native C++ boolean values, distinct from jank's `true`/`false`. These are necessary when calling C++ APIs that expect actual `bool` types rather than jank's boxed booleans.

## Complex Type Strings with `cpp/type`

`cpp/type` constructs C++ type expressions for templates and complex types:

```clojure
(cpp/type "std::vector<int>")
(cpp/type "std::map<std::string, int>")
```

This is needed because jank's reader syntax cannot directly represent C++ template angle brackets and namespaces.

## Opaque Boxes

### `cpp/box` and `cpp/unbox`
When a C++ value cannot be directly converted to a jank type, it is stored in an opaque box:

```clojure
(def boxed (cpp/box some-cpp-value))
(def unboxed (cpp/unbox boxed expected-type))
```

- `cpp/box` wraps a C++ value in a jank-managed opaque container.
- `cpp/unbox` extracts the value with a compile-time type check.
- Type safety is enforced -- unboxing with the wrong type is a compile-time error.

## Pre-Compiled Headers

jank uses pre-compiled headers (PCH) to speed up compilation. Standard C++ headers and commonly used library headers are pre-compiled, significantly reducing interop compilation times.

## Practical Examples

### iostream Hello World

```clojure
(cpp/raw "#include <iostream>")

(defn -main []
  (cpp/. (cpp/value "std::cout") << "Hello from jank!" << (cpp/value "std::endl")))
```

### nlohmann/json Pretty Printer

jank can directly use the nlohmann/json header-only library to parse and pretty-print JSON:

```clojure
(cpp/raw "#include <nlohmann/json.hpp>")

(defn pretty-print [json-str]
  (let [j (cpp/value "nlohmann::json::parse" json-str)]
    (cpp/. j dump #cpp/int 2)))
```

### FTXUI Terminal Flexbox with Hiccup Interface

The most ambitious example: using the FTXUI library for terminal UI with a Clojure hiccup-style interface. jank calls FTXUI's C++ flexbox layout engine directly:

- Creates FTXUI elements (text, border, hbox, vbox, flex).
- Composes them using hiccup-like jank data structures.
- Renders to terminal via FTXUI's screen abstraction.

This demonstrates that jank can drive complex, stateful C++ libraries without any binding layer.

## Key Principle

All interop is **statically typed** -- there is no runtime reflection. The jank compiler understands C++ types at compile time and emits direct calls. This means:

- Zero overhead compared to hand-written C++.
- Compile-time error messages for type mismatches.
- Full IDE support potential (type information is available statically).
