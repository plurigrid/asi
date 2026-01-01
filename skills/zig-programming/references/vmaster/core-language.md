# Core Language Features

*Basic Zig syntax, types, literals, variables, and operators*


---

### Introduction

[Zig](https://ziglang.org) is a general-purpose programming language and toolchain for maintaining
**robust**, **optimal**, and **reusable** software.

**Robust**
: Behavior is correct even for edge cases such as out of memory.

**Optimal**
: Write programs the best way they can behave and perform.

**Reusable**
: The same code works in many environments which have different
          constraints.

**Maintainable**
: Precisely communicate intent to the compiler and
          other programmers. The language imposes a low overhead to reading code and is
          resilient to changing requirements and environments.

Often the most efficient way to learn something new is to see examples, so
this documentation shows how to use each of Zig's features. It is
all on one page so you can search with your browser's search tool.

The code samples in this document are compiled and tested as part of the main test suite of Zig.

This HTML document depends on no external files, so you can use it offline.


---

### Hello World

**`hello.zig`:**

```zig
const std = @import("std");

pub fn main() !void {
    try std.fs.File.stdout().writeAll("Hello, World!\n");
}

```

**Shell:**

```shell
$ zig build-exe hello.zig
$ ./hello
Hello, World!

```

Most of the time, it is more appropriate to write to stderr rather than stdout, and
whether or not the message is successfully written to the stream is irrelevant.
Also, formatted printing often comes in handy. For this common case,
there is a simpler API:

**`hello_again.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    std.debug.print("Hello, {s}!\n", .{"World"});
}

```

**Shell:**

```shell
$ zig build-exe hello_again.zig
$ ./hello_again
Hello, World!

```

In this case, the `!` may be omitted from the return
type of `main` because no errors are returned from the function.

See also:

- [Values](05-values.md#Values)
- [Tuples](#Tuples)
- [@import](#import)
- [Errors](28-errors.md#Errors)
- [Entry Point](#Entry-Point)
- [Source Encoding](49-source-encoding.md#Source-Encoding)
- [try](#try)


---

### Comments

Zig supports 3 types of comments. Normal comments are ignored, but doc comments
and top-level doc comments are used by the compiler to generate the package documentation.

The generated documentation is still experimental, and can be produced with:

**Shell:**

```shell
zig test -femit-docs main.zig

```

**`comments.zig`:**

```zig
const print = @import("std").debug.print;

pub fn main() void {
    // Comments in Zig start with "//" and end at the next LF byte (end of line).
    // The line below is a comment and won't be executed.

    //print("Hello?", .{});

    print("Hello, world!\n", .{}); // another comment
}

```

**Shell:**

```shell
$ zig build-exe comments.zig
$ ./comments
Hello, world!

```

There are no multiline comments in Zig (e.g. like `/* */`
comments in C). This allows Zig to have the property that each line
of code can be tokenized out of context.

#### Doc Comments

A doc comment is one that begins with exactly three slashes (i.e.
`///` but not `////`);
multiple doc comments in a row are merged together to form a multiline
doc comment. The doc comment documents whatever immediately follows it.

**`doc_comments.zig`:**

```zig
/// A structure for storing a timestamp, with nanosecond precision (this is a
/// multiline doc comment).
const Timestamp = struct {
    /// The number of seconds since the epoch (this is also a doc comment).
    seconds: i64, // signed so we can represent pre-1970 (not a doc comment)
    /// The number of nanoseconds past the second (doc comment again).
    nanos: u32,

    /// Returns a `Timestamp` struct representing the Unix epoch; that is, the
    /// moment of 1970 Jan 1 00:00:00 UTC (this is a doc comment too).
    pub fn unixEpoch() Timestamp {
        return Timestamp{
            .seconds = 0,
            .nanos = 0,
        };
    }
};

```

Doc comments are only allowed in certain places; it is a compile error to
have a doc comment in an unexpected place, such as in the middle of an expression,
or just before a non-doc comment.

**`invalid_doc-comment.zig`:**

```zig
/// doc-comment
//! top-level doc-comment
const std = @import("std");

```

**Shell:**

```shell
$ zig build-obj invalid_doc-comment.zig
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/invalid_doc-comment.zig:1:16: error: expected type expression, found 'a document comment'
/// doc-comment
               ^


```

**`unattached_doc-comment.zig`:**

```zig
pub fn main() void {}

/// End of file

```

**Shell:**

```shell
$ zig build-obj unattached_doc-comment.zig
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/unattached_doc-comment.zig:3:1: error: unattached documentation comment
/// End of file
^~~~~~~~~~~~~~~


```

Doc comments can be interleaved with normal comments. Currently, when producing
the package documentation, normal comments are merged with doc comments.

#### Top-Level Doc Comments

A top-level doc comment is one that begins with two slashes and an exclamation
point: `//!`; it documents the current module.

It is a compile error if a top-level doc comment is not placed at the start
of a [container](45-c.md#Containers), before any expressions.

**`tldoc_comments.zig`:**

```zig
//! This module provides functions for retrieving the current date and
//! time with varying degrees of precision and accuracy. It does not
//! depend on libc, but will use functions from it if available.

const S = struct {
    //! Top level comments are allowed inside a container other than a module,
    //! but it is not very useful.  Currently, when producing the package
    //! documentation, these comments are ignored.
};

```


---

### Values

**`values.zig`:**

```zig
// Top-level declarations are order-independent:
const print = std.debug.print;
const std = @import("std");
const os = std.os;
const assert = std.debug.assert;

pub fn main() void {
    // integers
    const one_plus_one: i32 = 1 + 1;
    print("1 + 1 = {}\n", .{one_plus_one});

    // floats
    const seven_div_three: f32 = 7.0 / 3.0;
    print("7.0 / 3.0 = {}\n", .{seven_div_three});

    // boolean
    print("{}\n{}\n{}\n", .{
        true and false,
        true or false,
        !true,
    });

    // optional
    var optional_value: ?[]const u8 = null;
    assert(optional_value == null);

    print("\noptional 1\ntype: {}\nvalue: {?s}\n", .{
        @TypeOf(optional_value), optional_value,
    });

    optional_value = "hi";
    assert(optional_value != null);

    print("\noptional 2\ntype: {}\nvalue: {?s}\n", .{
        @TypeOf(optional_value), optional_value,
    });

    // error union
    var number_or_error: anyerror!i32 = error.ArgNotFound;

    print("\nerror union 1\ntype: {}\nvalue: {!}\n", .{
        @TypeOf(number_or_error),
        number_or_error,
    });

    number_or_error = 1234;

    print("\nerror union 2\ntype: {}\nvalue: {!}\n", .{
        @TypeOf(number_or_error), number_or_error,
    });
}

```

**Shell:**

```shell
$ zig build-exe values.zig
$ ./values
1 + 1 = 2
7.0 / 3.0 = 2.3333333
false
true
false

optional 1
type: ?[]const u8
value: null

optional 2
type: ?[]const u8
value: hi

error union 1
type: anyerror!i32
value: error.ArgNotFound

error union 2
type: anyerror!i32
value: 1234

```

#### Primitive Types

| Type | C Equivalent | Description |
| --- | --- | --- |
| `i8` | `int8_t` | signed 8-bit integer |
| `u8` | `uint8_t` | unsigned 8-bit integer |
| `i16` | `int16_t` | signed 16-bit integer |
| `u16` | `uint16_t` | unsigned 16-bit integer |
| `i32` | `int32_t` | signed 32-bit integer |
| `u32` | `uint32_t` | unsigned 32-bit integer |
| `i64` | `int64_t` | signed 64-bit integer |
| `u64` | `uint64_t` | unsigned 64-bit integer |
| `i128` | `__int128` | signed 128-bit integer |
| `u128` | `unsigned __int128` | unsigned 128-bit integer |
| `isize` | `intptr_t` | signed pointer sized integer |
| `usize` | `uintptr_t`, `size_t` | unsigned pointer sized integer. Also see [#5185](https://github.com/ziglang/zig/issues/5185) |
| `c_char` | `char` | for ABI compatibility with C |
| `c_short` | `short` | for ABI compatibility with C |
| `c_ushort` | `unsigned short` | for ABI compatibility with C |
| `c_int` | `int` | for ABI compatibility with C |
| `c_uint` | `unsigned int` | for ABI compatibility with C |
| `c_long` | `long` | for ABI compatibility with C |
| `c_ulong` | `unsigned long` | for ABI compatibility with C |
| `c_longlong` | `long long` | for ABI compatibility with C |
| `c_ulonglong` | `unsigned long long` | for ABI compatibility with C |
| `c_longdouble` | `long double` | for ABI compatibility with C |
| `f16` | `_Float16` | 16-bit floating point (10-bit mantissa) IEEE-754-2008 binary16 |
| `f32` | `float` | 32-bit floating point (23-bit mantissa) IEEE-754-2008 binary32 |
| `f64` | `double` | 64-bit floating point (52-bit mantissa) IEEE-754-2008 binary64 |
| `f80` | `long double` | 80-bit floating point (64-bit mantissa) IEEE-754-2008 80-bit extended precision |
| `f128` | `_Float128` | 128-bit floating point (112-bit mantissa) IEEE-754-2008 binary128 |
| `bool` | `bool` | `true` or `false` |
| `anyopaque` | `void` | Used for type-erased pointers. |
| `void` | (none) | Always the value `void{}` |
| `noreturn` | (none) | the type of `break`, `continue`, `return`, `unreachable`, and `while (true) {}` |
| `type` | (none) | the type of types |
| `anyerror` | (none) | an error code |
| `comptime_int` | (none) | Only allowed for [comptime](33-comptime.md#comptime)-known values. The type of integer literals. |
| `comptime_float` | (none) | Only allowed for [comptime](33-comptime.md#comptime)-known values. The type of float literals. |

In addition to the integer types above, arbitrary bit-width integers can be referenced by using
an identifier of `i` or `u` followed by digits. For example, the identifier
`i7` refers to a signed 7-bit integer. The maximum allowed bit-width of an
integer type is `65535`.

See also:

- [Integers](08-integers.md#Integers)
- [Floats](09-floats.md#Floats)
- [void](#void)
- [Errors](28-errors.md#Errors)
- [@Type](#Type)

#### Primitive Values

| Name | Description |
| --- | --- |
| `true` and `false` | `bool` values |
| `null` | used to set an optional type to `null` |
| `undefined` | used to leave a value unspecified |

See also:

- [Optionals](29-optionals.md#Optionals)
- [undefined](#undefined)

#### String Literals and Unicode Code Point Literals

String literals are constant single-item [Pointers](13-pointers.md#Pointers) to null-terminated byte arrays.
The type of string literals encodes both the length, and the fact that they are null-terminated,
and thus they can be [coerced](#Type-Coercion) to both [Slices](14-slices.md#Slices) and
[Null-Terminated Pointers](#Sentinel-Terminated-Pointers).
Dereferencing string literals converts them to [Arrays](11-arrays.md#Arrays).

Because Zig source code is [UTF-8 encoded](49-source-encoding.md#Source-Encoding), any
non-ASCII bytes appearing within a string literal in source code carry
their UTF-8 meaning into the content of the string in the Zig program;
the bytes are not modified by the compiler. It is possible to embed
non-UTF-8 bytes into a string literal using `\xNN` notation.

Indexing into a string containing non-ASCII bytes returns individual
bytes, whether valid UTF-8 or not.

Unicode code point literals have type `comptime_int`, the same as
[Integer Literals](#Integer-Literals). All [Escape Sequences](#Escape-Sequences) are valid in both string literals
and Unicode code point literals.

**`string_literals.zig`:**

```zig
const print = @import("std").debug.print;
const mem = @import("std").mem; // will be used to compare bytes

pub fn main() void {
    const bytes = "hello";
    print("{}\n", .{@TypeOf(bytes)}); // *const [5:0]u8
    print("{d}\n", .{bytes.len}); // 5
    print("{c}\n", .{bytes[1]}); // 'e'
    print("{d}\n", .{bytes[5]}); // 0
    print("{}\n", .{'e' == '\x65'}); // true
    print("{d}\n", .{'\u{1f4a9}'}); // 128169
    print("{d}\n", .{'ð¯'}); // 128175
    print("{u}\n", .{'â¡'});
    print("{}\n", .{mem.eql(u8, "hello", "h\x65llo")}); // true
    print("{}\n", .{mem.eql(u8, "ð¯", "\xf0\x9f\x92\xaf")}); // also true
    const invalid_utf8 = "\xff\xfe"; // non-UTF-8 strings are possible with \xNN notation.
    print("0x{x}\n", .{invalid_utf8[1]}); // indexing them returns individual bytes...
    print("0x{x}\n", .{"ð¯"[1]}); // ...as does indexing part-way through non-ASCII characters
}

```

**Shell:**

```shell
$ zig build-exe string_literals.zig
$ ./string_literals
*const [5:0]u8
5
e
0
true
128169
128175
â¡
true
true
0xfe
0x9f

```

See also:

- [Arrays](11-arrays.md#Arrays)
- [Source Encoding](49-source-encoding.md#Source-Encoding)

##### Escape Sequences

| Escape Sequence | Name |
| --- | --- |
| `\n` | Newline |
| `\r` | Carriage Return |
| `\t` | Tab |
| `\\` | Backslash |
| `\'` | Single Quote |
| `\"` | Double Quote |
| `\xNN` | hexadecimal 8-bit byte value (2 digits) |
| `\u{NNNNNN}` | hexadecimal Unicode scalar value UTF-8 encoded (1 or more digits) |

Note that the maximum valid Unicode scalar value is `0x10ffff`.

##### Multiline String Literals

Multiline string literals have no escapes and can span across multiple lines.
To start a multiline string literal, use the `\\` token. Just like a comment,
the string literal goes until the end of the line. The end of the line is
not included in the string literal.
However, if the next line begins with `\\` then a newline is appended and
the string literal continues.

**`multiline_string_literals.zig`:**

```zig
const hello_world_in_c =
    \\#include <stdio.h>
    \\
    \\int main(int argc, char **argv) {
    \\    printf("hello world\n");
    \\    return 0;
    \\}
;

```

See also:

- [@embedFile](#embedFile)

#### Assignment

Use the `const` keyword to assign a value to an identifier:

**`constant_identifier_cannot_change.zig`:**

```zig
const x = 1234;

fn foo() void {
    // It works at file scope as well as inside functions.
    const y = 5678;

    // Once assigned, an identifier cannot be changed.
    y += 1;
}

pub fn main() void {
    foo();
}

```

**Shell:**

```shell
$ zig build-exe constant_identifier_cannot_change.zig
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/constant_identifier_cannot_change.zig:8:5: error: cannot assign to constant
    y += 1;
    ^
referenced by:
    main: /home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/constant_identifier_cannot_change.zig:12:8
    callMain [inlined]: /home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:695:22
    callMainWithArgs [inlined]: /home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:664:20
    posixCallMainAndExit: /home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:620:36
    2 reference(s) hidden; use '-freference-trace=6' to see all references


```

`const` applies to all of the bytes that the identifier immediately addresses. [Pointers](13-pointers.md#Pointers) have their own const-ness.

If you need a variable that you can modify, use the `var` keyword:

**`mutable_var.zig`:**

```zig
const print = @import("std").debug.print;

pub fn main() void {
    var y: i32 = 5678;

    y += 1;

    print("{d}", .{y});
}

```

**Shell:**

```shell
$ zig build-exe mutable_var.zig
$ ./mutable_var
5679

```

Variables must be initialized:

**`var_must_be_initialized.zig`:**

```zig
pub fn main() void {
    var x: i32;

    x = 1;
}

```

**Shell:**

```shell
$ zig build-exe var_must_be_initialized.zig
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/var_must_be_initialized.zig:2:15: error: expected '=', found ';'
    var x: i32;
              ^


```

##### undefined

Use `undefined` to leave variables uninitialized:

**`assign_undefined.zig`:**

```zig
const print = @import("std").debug.print;

pub fn main() void {
    var x: i32 = undefined;
    x = 1;
    print("{d}", .{x});
}

```

**Shell:**

```shell
$ zig build-exe assign_undefined.zig
$ ./assign_undefined
1

```

`undefined` can be [coerced](#Type-Coercion) to any type.
Once this happens, it is no longer possible to detect that the value is `undefined`.
`undefined` means the value could be anything, even something that is nonsense
according to the type. Translated into English, `undefined` means "Not a meaningful
value. Using this value would be a bug. The value will be unused, or overwritten before being used."

In [Debug](#Debug) and [ReleaseSafe](#ReleaseSafe) mode, Zig writes `0xaa` bytes to undefined memory. This is to catch
bugs early, and to help detect use of undefined memory in a debugger. However, this behavior is only an
implementation feature, not a language semantic, so it is not guaranteed to be observable to code.

##### Destructuring

A destructuring assignment can separate elements of indexable aggregate types
([Tuples](#Tuples), [Arrays](11-arrays.md#Arrays), [Vectors](12-vectors.md#Vectors)):

**`destructuring_to_existing.zig`:**

```zig
const print = @import("std").debug.print;

pub fn main() void {
    var x: u32 = undefined;
    var y: u32 = undefined;
    var z: u32 = undefined;

    const tuple = .{ 1, 2, 3 };

    x, y, z = tuple;

    print("tuple: x = {}, y = {}, z = {}\n", .{x, y, z});

    const array = [_]u32{ 4, 5, 6 };

    x, y, z = array;

    print("array: x = {}, y = {}, z = {}\n", .{x, y, z});

    const vector: @Vector(3, u32) = .{ 7, 8, 9 };

    x, y, z = vector;

    print("vector: x = {}, y = {}, z = {}\n", .{x, y, z});
}

```

**Shell:**

```shell
$ zig build-exe destructuring_to_existing.zig
$ ./destructuring_to_existing
tuple: x = 1, y = 2, z = 3
array: x = 4, y = 5, z = 6
vector: x = 7, y = 8, z = 9

```

A destructuring expression may only appear within a block (i.e. not at container scope).
The left hand side of the assignment must consist of a comma separated list,
each element of which may be either an lvalue (for instance, an existing `var`) or a variable declaration:

**`destructuring_mixed.zig`:**

```zig
const print = @import("std").debug.print;

pub fn main() void {
    var x: u32 = undefined;

    const tuple = .{ 1, 2, 3 };

    x, var y : u32, const z = tuple;

    print("x = {}, y = {}, z = {}\n", .{x, y, z});

    // y is mutable
    y = 100;

    // You can use _ to throw away unwanted values.
    _, x, _ = tuple;

    print("x = {}", .{x});
}

```

**Shell:**

```shell
$ zig build-exe destructuring_mixed.zig
$ ./destructuring_mixed
x = 1, y = 2, z = 3
x = 2

```

A destructure may be prefixed with the `comptime` keyword, in which case the entire
destructure expression is evaluated at [comptime](33-comptime.md#comptime). All `var`s declared would
be `comptime var`s and all expressions (both result locations and the assignee
expression) are evaluated at [comptime](33-comptime.md#comptime).

See also:

- [Destructuring Tuples](#Destructuring-Tuples)
- [Destructuring Arrays](#Destructuring-Arrays)
- [Destructuring Vectors](#Destructuring-Vectors)


---

### Variables

A variable is a unit of [Memory](41-memory.md#Memory) storage.

It is generally preferable to use `const` rather than
`var` when declaring a variable. This causes less work for both
humans and computers to do when reading code, and creates more optimization opportunities.

The `extern` keyword or [@extern](#extern) builtin function can be used to link against a variable that is exported
from another object. The `export` keyword or [@export](#export) builtin function
can be used to make a variable available to other objects at link time. In both cases,
the type of the variable must be C ABI compatible.

See also:

- [Exporting a C Library](#Exporting-a-C-Library)

#### Identifiers

Variable identifiers are never allowed to shadow identifiers from an outer scope.

Identifiers must start with an alphabetic character or underscore and may be followed
by any number of alphanumeric characters or underscores.
They must not overlap with any keywords. See [Keyword Reference](50-keyword-reference.md#Keyword-Reference).

If a name that does not fit these requirements is needed, such as for linking with external libraries, the `@""` syntax may be used.

**`identifiers.zig`:**

```zig
const @"identifier with spaces in it" = 0xff;
const @"1SmallStep4Man" = 112358;

const c = @import("std").c;
pub extern "c" fn @"error"() void;
pub extern "c" fn @"fstat$INODE64"(fd: c.fd_t, buf: *c.Stat) c_int;

const Color = enum {
    red,
    @"really red",
};
const color: Color = .@"really red";

```

#### Container Level Variables

[Container](45-c.md#Containers) level variables have static lifetime and are order-independent and lazily analyzed.
The initialization value of container level variables is implicitly
[comptime](33-comptime.md#comptime). If a container level variable is `const` then its value is
`comptime`-known, otherwise it is runtime-known.

**`test_container_level_variables.zig`:**

```zig
var y: i32 = add(10, x);
const x: i32 = add(12, 34);

test "container level variables" {
    try expect(x == 46);
    try expect(y == 56);
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

const std = @import("std");
const expect = std.testing.expect;

```

**Shell:**

```shell
$ zig test test_container_level_variables.zig
1/1 test_container_level_variables.test.container level variables...OK
All 1 tests passed.

```

Container level variables may be declared inside a [struct](15-struct.md#struct), [union](17-union.md#union), [enum](16-enum.md#enum), or [opaque](18-opaque.md#opaque):

**`test_namespaced_container_level_variable.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "namespaced container level variable" {
    try expect(foo() == 1235);
    try expect(foo() == 1236);
}

const S = struct {
    var x: i32 = 1234;
};

fn foo() i32 {
    S.x += 1;
    return S.x;
}

```

**Shell:**

```shell
$ zig test test_namespaced_container_level_variable.zig
1/1 test_namespaced_container_level_variable.test.namespaced container level variable...OK
All 1 tests passed.

```

#### Static Local Variables

It is also possible to have local variables with static lifetime by using containers inside functions.

**`test_static_local_variable.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "static local variable" {
    try expect(foo() == 1235);
    try expect(foo() == 1236);
}

fn foo() i32 {
    const S = struct {
        var x: i32 = 1234;
    };
    S.x += 1;
    return S.x;
}

```

**Shell:**

```shell
$ zig test test_static_local_variable.zig
1/1 test_static_local_variable.test.static local variable...OK
All 1 tests passed.

```

#### Thread Local Variables

A variable may be specified to be a thread-local variable using the
`threadlocal` keyword,
which makes each thread work with a separate instance of the variable:

**`test_thread_local_variables.zig`:**

```zig
const std = @import("std");
const assert = std.debug.assert;

threadlocal var x: i32 = 1234;

test "thread local storage" {
    const thread1 = try std.Thread.spawn(.{}, testTls, .{});
    const thread2 = try std.Thread.spawn(.{}, testTls, .{});
    testTls();
    thread1.join();
    thread2.join();
}

fn testTls() void {
    assert(x == 1234);
    x += 1;
    assert(x == 1235);
}

```

**Shell:**

```shell
$ zig test test_thread_local_variables.zig
1/1 test_thread_local_variables.test.thread local storage...OK
All 1 tests passed.

```

For [Single Threaded Builds](39-single-threaded-builds.md#Single-Threaded-Builds), all thread local variables are treated as regular [Container Level Variables](45-c.md#Container-Level-Variables).

Thread local variables may not be `const`.

#### Local Variables

Local variables occur inside [Functions](27-functions.md#Functions), [comptime](33-comptime.md#comptime) blocks, and [@cImport](#cImport) blocks.

When a local variable is `const`, it means that after initialization, the variable's
value will not change. If the initialization value of a `const` variable is
[comptime](33-comptime.md#comptime)-known, then the variable is also `comptime`-known.

A local variable may be qualified with the `comptime` keyword. This causes
the variable's value to be `comptime`-known, and all loads and stores of the
variable to happen during semantic analysis of the program, rather than at runtime.
All variables declared in a `comptime` expression are implicitly
`comptime` variables.

**`test_comptime_variables.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "comptime vars" {
    var x: i32 = 1;
    comptime var y: i32 = 1;

    x += 1;
    y += 1;

    try expect(x == 2);
    try expect(y == 2);

    if (y != 2) {
        // This compile error never triggers because y is a comptime variable,
        // and so `y != 2` is a comptime value, and this if is statically evaluated.
        @compileError("wrong y value");
    }
}

```

**Shell:**

```shell
$ zig test test_comptime_variables.zig
1/1 test_comptime_variables.test.comptime vars...OK
All 1 tests passed.

```


---

### Integers

#### Integer Literals

**`integer_literals.zig`:**

```zig
const decimal_int = 98222;
const hex_int = 0xff;
const another_hex_int = 0xFF;
const octal_int = 0o755;
const binary_int = 0b11110000;

// underscores may be placed between two digits as a visual separator
const one_billion = 1_000_000_000;
const binary_mask = 0b1_1111_1111;
const permissions = 0o7_5_5;
const big_address = 0xFF80_0000_0000_0000;

```

#### Runtime Integer Values

Integer literals have no size limitation, and if any Illegal Behavior occurs,
the compiler catches it.

However, once an integer value is no longer known at compile-time, it must have a
known size, and is vulnerable to safety-checked [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior).

**`runtime_vs_comptime.zig`:**

```zig
fn divide(a: i32, b: i32) i32 {
    return a / b;
}

```

In this function, values `a` and `b` are known only at runtime,
and thus this division operation is vulnerable to both [Integer Overflow](#Integer-Overflow) and
[Division by Zero](#Division-by-Zero).

Operators such as `+` and `-` cause [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior) on
integer overflow. Alternative operators are provided for wrapping and saturating arithmetic on all targets.
`+%` and `-%` perform wrapping arithmetic
while `+|` and `-|` perform saturating arithmetic.

Zig supports arbitrary bit-width integers, referenced by using
an identifier of `i` or `u` followed by digits. For example, the identifier
`i7` refers to a signed 7-bit integer. The maximum allowed bit-width of an
integer type is `65535`. For signed integer types, Zig uses a
[two's complement](https://en.wikipedia.org/wiki/Two's_complement) representation.

See also:

- [Wrapping Operations](#Wrapping-Operations)


---

### Floats

Zig has the following floating point types:

- `f16` - IEEE-754-2008 binary16
- `f32` - IEEE-754-2008 binary32
- `f64` - IEEE-754-2008 binary64
- `f80` - IEEE-754-2008 80-bit extended precision
- `f128` - IEEE-754-2008 binary128
- `c_longdouble` - matches `long double` for the target C ABI

#### Float Literals

Float literals have type `comptime_float` which is guaranteed to have
the same precision and operations of the largest other floating point type, which is
`f128`.

Float literals [coerce](#Type-Coercion) to any floating point type,
and to any [integer](08-integers.md#Integers) type when there is no fractional component.

**`float_literals.zig`:**

```zig
const floating_point = 123.0E+77;
const another_float = 123.0;
const yet_another = 123.0e+77;

const hex_floating_point = 0x103.70p-5;
const another_hex_float = 0x103.70;
const yet_another_hex_float = 0x103.70P-5;

// underscores may be placed between two digits as a visual separator
const lightspeed = 299_792_458.000_000;
const nanosecond = 0.000_000_001;
const more_hex = 0x1234_5678.9ABC_CDEFp-10;

```

There is no syntax for NaN, infinity, or negative infinity. For these special values,
one must use the standard library:

**`float_special_values.zig`:**

```zig
const std = @import("std");

const inf = std.math.inf(f32);
const negative_inf = -std.math.inf(f64);
const nan = std.math.nan(f128);

```

#### Floating Point Operations

By default floating point operations use `Strict` mode,
but you can switch to `Optimized` mode on a per-block basis:

**`float_mode_obj.zig`:**

```zig
const std = @import("std");
const big = @as(f64, 1 << 40);

export fn foo_strict(x: f64) f64 {
    return x + big - big;
}

export fn foo_optimized(x: f64) f64 {
    @setFloatMode(.optimized);
    return x + big - big;
}

```

**Shell:**

```shell
$ zig build-obj float_mode_obj.zig -O ReleaseFast

```

For this test we have to separate code into two object files -
otherwise the optimizer figures out all the values at compile-time,
which operates in strict mode.

**`float_mode_exe.zig`:**

```zig
const print = @import("std").debug.print;

extern fn foo_strict(x: f64) f64;
extern fn foo_optimized(x: f64) f64;

pub fn main() void {
    const x = 0.001;
    print("optimized = {}\n", .{foo_optimized(x)});
    print("strict = {}\n", .{foo_strict(x)});
}

```

See also:

- [@setFloatMode](#setFloatMode)
- [Division by Zero](#Division-by-Zero)


---

### Operators

There is no operator overloading. When you see an operator in Zig, you know that
it is doing something from this table, and nothing else.

#### Table of Operators

| Name | Syntax | Types | Remarks | Example |
| --- | --- | --- | --- | --- |
| Addition | `a + b a += b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) | - Can cause [overflow](#Default-Operations) for integers. - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. - See also [@addWithOverflow](#addWithOverflow). | `2 + 5 == 7` |
| Wrapping Addition | `a +% b a +%= b` | - [Integers](08-integers.md#Integers) | - Twos-complement wrapping behavior. - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. - See also [@addWithOverflow](#addWithOverflow). | `@as(u32, 0xffffffff) +% 1 == 0` |
| Saturating Addition | `a +| b a +|= b` | - [Integers](08-integers.md#Integers) | - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `@as(u8, 255) +| 1 == @as(u8, 255)` |
| Subtraction | `a - b a -= b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) | - Can cause [overflow](#Default-Operations) for integers. - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. - See also [@subWithOverflow](#subWithOverflow). | `2 - 5 == -3` |
| Wrapping Subtraction | `a -% b a -%= b` | - [Integers](08-integers.md#Integers) | - Twos-complement wrapping behavior. - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. - See also [@subWithOverflow](#subWithOverflow). | `@as(u8, 0) -% 1 == 255` |
| Saturating Subtraction | `a -| b a -|= b` | - [Integers](08-integers.md#Integers) | - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `@as(u32, 0) -| 1 == 0` |
| Negation | `-a` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) | - Can cause [overflow](#Default-Operations) for integers. | `-1 == 0 - 1` |
| Wrapping Negation | `-%a` | - [Integers](08-integers.md#Integers) | - Twos-complement wrapping behavior. | `-%@as(i8, -128) == -128` |
| Multiplication | `a * b a *= b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) | - Can cause [overflow](#Default-Operations) for integers. - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. - See also [@mulWithOverflow](#mulWithOverflow). | `2 * 5 == 10` |
| Wrapping Multiplication | `a *% b a *%= b` | - [Integers](08-integers.md#Integers) | - Twos-complement wrapping behavior. - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. - See also [@mulWithOverflow](#mulWithOverflow). | `@as(u8, 200) *% 2 == 144` |
| Saturating Multiplication | `a *| b a *|= b` | - [Integers](08-integers.md#Integers) | - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `@as(u8, 200) *| 2 == 255` |
| Division | `a / b a /= b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) | - Can cause [overflow](#Default-Operations) for integers. - Can cause [Division by Zero](#Division-by-Zero) for integers. - Can cause [Division by Zero](#Division-by-Zero) for floats in [FloatMode.Optimized Mode](#Floating-Point-Operations). - Signed integer operands must be comptime-known and positive. In other cases, use   [@divTrunc](#divTrunc),   [@divFloor](#divFloor), or   [@divExact](#divExact) instead. - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `10 / 5 == 2` |
| Remainder Division | `a % b a %= b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) | - Can cause [Division by Zero](#Division-by-Zero) for integers. - Can cause [Division by Zero](#Division-by-Zero) for floats in [FloatMode.Optimized Mode](#Floating-Point-Operations). - Signed or floating-point operands must be comptime-known and positive. In other cases, use   [@rem](#rem) or   [@mod](#mod) instead. - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `10 % 3 == 1` |
| Bit Shift Left | `a << b a <<= b` | - [Integers](08-integers.md#Integers) | - Moves all bits to the left, inserting new zeroes at the   least-significant bit. - `b` must be   [comptime-known](33-comptime.md#comptime) or have a type with log2 number   of bits as `a`. - See also [@shlExact](#shlExact). - See also [@shlWithOverflow](#shlWithOverflow). | `0b1 << 8 == 0b100000000` |
| Saturating Bit Shift Left | `a <<| b a <<|= b` | - [Integers](08-integers.md#Integers) | - See also [@shlExact](#shlExact). - See also [@shlWithOverflow](#shlWithOverflow). | `@as(u8, 1) <<| 8 == 255` |
| Bit Shift Right | `a >> b a >>= b` | - [Integers](08-integers.md#Integers) | - Moves all bits to the right, inserting zeroes at the most-significant bit. - `b` must be   [comptime-known](33-comptime.md#comptime) or have a type with log2 number   of bits as `a`. - See also [@shrExact](#shrExact). | `0b1010 >> 1 == 0b101` |
| Bitwise And | `a & b a &= b` | - [Integers](08-integers.md#Integers) | - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `0b011 & 0b101 == 0b001` |
| Bitwise Or | `a | b a |= b` | - [Integers](08-integers.md#Integers) | - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `0b010 | 0b100 == 0b110` |
| Bitwise Xor | `a ^ b a ^= b` | - [Integers](08-integers.md#Integers) | - Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `0b011 ^ 0b101 == 0b110` |
| Bitwise Not | `~a` | - [Integers](08-integers.md#Integers) |  | `~@as(u8, 0b10101111) == 0b01010000` |
| Defaulting Optional Unwrap | `a orelse b` | - [Optionals](29-optionals.md#Optionals) | If `a` is `null`, returns `b` ("default value"), otherwise returns the unwrapped value of `a`. Note that `b` may be a value of type [noreturn](26-noreturn.md#noreturn). | `const value: ?u32 = null; const unwrapped = value orelse 1234; unwrapped == 1234` |
| Optional Unwrap | `a.?` | - [Optionals](29-optionals.md#Optionals) | Equivalent to:`a orelse unreachable` | `const value: ?u32 = 5678; value.? == 5678` |
| Defaulting Error Unwrap | `a catch b a catch |err| b` | - [Error Unions](28-errors.md#Errors) | If `a` is an `error`, returns `b` ("default value"), otherwise returns the unwrapped value of `a`. Note that `b` may be a value of type [noreturn](26-noreturn.md#noreturn). `err` is the `error` and is in scope of the expression `b`. | `const value: anyerror!u32 = error.Broken; const unwrapped = value catch 1234; unwrapped == 1234` |
| Logical And | `a and b` | - [bool](#Primitive-Types) | If `a` is `false`, returns `false` without evaluating `b`. Otherwise, returns `b`. | `(false and true) == false` |
| Logical Or | `a or b` | - [bool](#Primitive-Types) | If `a` is `true`, returns `true` without evaluating `b`. Otherwise, returns `b`. | `(false or true) == true` |
| Boolean Not | `!a` | - [bool](#Primitive-Types) |  | `!false == true` |
| Equality | `a == b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) - [bool](#Primitive-Types) - [type](#Primitive-Types) - [packed struct](#packed-struct) | Returns `true` if a and b are equal, otherwise returns `false`. Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `(1 == 1) == true` |
| Null Check | `a == null` | - [Optionals](29-optionals.md#Optionals) | Returns `true` if a is `null`, otherwise returns `false`. | `const value: ?u32 = null; (value == null) == true` |
| Inequality | `a != b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) - [bool](#Primitive-Types) - [type](#Primitive-Types) | Returns `false` if a and b are equal, otherwise returns `true`. Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `(1 != 1) == false` |
| Non-Null Check | `a != null` | - [Optionals](29-optionals.md#Optionals) | Returns `false` if a is `null`, otherwise returns `true`. | `const value: ?u32 = null; (value != null) == false` |
| Greater Than | `a > b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) | Returns `true` if a is greater than b, otherwise returns `false`. Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `(2 > 1) == true` |
| Greater or Equal | `a >= b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) | Returns `true` if a is greater than or equal to b, otherwise returns `false`. Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `(2 >= 1) == true` |
| Less Than | `a < b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) | Returns `true` if a is less than b, otherwise returns `false`. Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `(1 < 2) == true` |
| Lesser or Equal | `a <= b` | - [Integers](08-integers.md#Integers) - [Floats](09-floats.md#Floats) | Returns `true` if a is less than or equal to b, otherwise returns `false`. Invokes [Peer Type Resolution](#Peer-Type-Resolution) for the operands. | `(1 <= 2) == true` |
| Array Concatenation | `a ++ b` | - [Arrays](11-arrays.md#Arrays) | - Only available when the lengths of both `a` and `b` are [compile-time known](33-comptime.md#comptime). | `const mem = @import("std").mem; const array1 = [_]u32{1,2}; const array2 = [_]u32{3,4}; const together = array1 ++ array2; mem.eql(u32, &together, &[_]u32{1,2,3,4})` |
| Array Multiplication | `a ** b` | - [Arrays](11-arrays.md#Arrays) | - Only available when the length of `a` and `b` are [compile-time known](33-comptime.md#comptime). | `const mem = @import("std").mem; const pattern = "ab" ** 3; mem.eql(u8, pattern, "ababab")` |
| Pointer Dereference | `a.*` | - [Pointers](13-pointers.md#Pointers) | Pointer dereference. | `const x: u32 = 1234; const ptr = &x; ptr.* == 1234` |
| Address Of | `&a` | All types |  | `const x: u32 = 1234; const ptr = &x; ptr.* == 1234` |
| Error Set Merge | `a || b` | - [Error Set Type](#Error-Set-Type) | [Merging Error Sets](#Merging-Error-Sets) | `const A = error{One}; const B = error{Two}; (A || B) == error{One, Two}` |

#### Precedence

```

x() x[] x.y x.* x.?
a!b
x{}
!x -x -%x ~x &x ?x
* / % ** *% *| ||
+ - ++ +% -% +| -|
<< >> <<|
& ^ | orelse catch
== != < > <= >=
and
or
= *= *%= *|= /= %= += +%= +|= -= -%= -|= <<= <<|= >>= &= ^= |=

```


---
