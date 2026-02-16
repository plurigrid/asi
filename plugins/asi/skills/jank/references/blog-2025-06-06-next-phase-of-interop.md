# The next phase of jank's C++ interop

**Date:** June 6, 2025
**Source:** jank blog

## Overview

This update covers ~60 new interop tests and significant expansion of C++ interop capabilities across free functions, member functions, member access, and operators.

## Free Functions

### Overloading
jank resolves C++ function overloads at compile time based on argument types and count. When multiple overloads match, the compiler applies C++ overload resolution rules.

### Implicit Conversions
Arguments are implicitly converted from jank types to C++ types using the convert trait system. For example, a jank integer seamlessly becomes a C++ `int`, `long`, or `double` as needed.

### Void Return
C++ functions returning `void` are handled correctly -- jank treats the return value as `nil`.

### Variadic Functions
C-style variadic functions (e.g., `printf`) are supported. jank passes arguments with appropriate type conversions.

### Template Functions
Template functions can be called when the compiler can deduce template arguments from the call-site types. Explicit template arguments are also supported via type annotation syntax.

## Member Functions

### `this` Pointer
Member functions are called on C++ objects with correct `this` pointer semantics. The compiler adjusts for pointer vs. reference receivers.

### Constness
The compiler respects `const` qualifiers on member functions, selecting the correct overload based on the constness of the object.

### Ref-Qualifier
Member functions with lvalue (`&`) and rvalue (`&&`) ref-qualifiers are distinguished during overload resolution.

### Visibility
Only `public` member functions are accessible from jank. Attempting to call `private` or `protected` members produces a compile-time error.

## Member Access

### Syntax: `cpp/.-foo`

Member variables are accessed using the `cpp/.-foo` pattern (similar to Clojure's Java field access but prefixed with `cpp/`):

```clojure
(cpp/.-x my-point)    ;; access member 'x' of a C++ object
```

### References
Member access correctly handles reference semantics -- accessing a member that is a reference returns the referenced value, not a copy of the reference.

## Operators

### Scope
45 C++ operators are supported, covering:

- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`
- Logical: `&&`, `||`, `!`
- Bitwise: `&`, `|`, `^`, `~`, `<<`, `>>`
- Assignment: `=`, `+=`, `-=`, `*=`, `/=`, etc.
- Increment/decrement: `++`, `--` (prefix and postfix)
- Subscript: `[]`
- Dereference: `*`, `->`
- Address-of: `&`

### Pointer Arithmetic
Pointer arithmetic works naturally -- adding an integer to a pointer advances it by the appropriate stride.

### User-Defined Overloads
Custom operator overloads defined on C++ types are resolved and called correctly. jank treats them as any other overloaded function.

## Mentorship Program

Four mentees joined the jank project:

| Mentee | Focus Area |
|--------|------------|
| **Saket** | C++ interop internals |
| **Monty** | Compiler and runtime |
| **Jianling** | Standard library and compatibility |
| **Shantanu** | Tooling and distribution |

The mentorship program is expanding the contributor base and accelerating development across all areas of the project.
