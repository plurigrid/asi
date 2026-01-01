# Memory Management

*Memory allocation, ownership, and optimization*


---

### Zero Bit Types

For some types, [@sizeOf](#sizeOf) is 0:

- [void](#void)
- The [Integers](08-integers.md#Integers) `u0` and `i0`.
- [Arrays](11-arrays.md#Arrays) and [Vectors](12-vectors.md#Vectors) with len 0, or with an element type that is a zero bit type.
- An [enum](16-enum.md#enum) with only 1 tag.
- A [struct](15-struct.md#struct) with all fields being zero bit types.
- A [union](17-union.md#union) with only 1 field which is a zero bit type.

These types can only ever have one possible value, and thus
require 0 bits to represent. Code that makes use of these types is
not included in the final generated code:

**`zero_bit_types.zig`:**

```zig
export fn entry() void {
    var x: void = {};
    var y: void = {};
    x = y;
    y = x;
}

```

When this turns into machine code, there is no code generated in the
body of `entry`, even in [Debug](#Debug) mode. For example, on x86_64:

```

0000000000000010 <entry>:
  10:	55                   	push   %rbp
  11:	48 89 e5             	mov    %rsp,%rbp
  14:	5d                   	pop    %rbp
  15:	c3                   	retq   

```

These assembly instructions do not have any code associated with the void values -
they only perform the function call prologue and epilogue.

#### void

`void` can be useful for instantiating generic types. For example, given a
`Map(Key, Value)`, one can pass `void` for the `Value`
type to make it into a `Set`:

**`test_void_in_hashmap.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "turn HashMap into a set with void" {
    var map = std.AutoHashMap(i32, void).init(std.testing.allocator);
    defer map.deinit();

    try map.put(1, {});
    try map.put(2, {});

    try expect(map.contains(2));
    try expect(!map.contains(3));

    _ = map.remove(2);
    try expect(!map.contains(2));
}

```

**Shell:**

```shell
$ zig test test_void_in_hashmap.zig
1/1 test_void_in_hashmap.test.turn HashMap into a set with void...OK
All 1 tests passed.

```

Note that this is different from using a dummy value for the hash map value.
By using `void` as the type of the value, the hash map entry type has no value field, and
thus the hash map takes up less space. Further, all the code that deals with storing and loading the
value is deleted, as seen above.

`void` is distinct from `anyopaque`.
`void` has a known size of 0 bytes, and `anyopaque` has an unknown, but non-zero, size.

Expressions of type `void` are the only ones whose value can be ignored. For example, ignoring
a non-`void` expression is a compile error:

**`test_expression_ignored.zig`:**

```zig
test "ignoring expression value" {
    foo();
}

fn foo() i32 {
    return 1234;
}

```

**Shell:**

```shell
$ zig test test_expression_ignored.zig
/home/andy/dev/zig/doc/langref/test_expression_ignored.zig:2:8: error: value of type 'i32' ignored
    foo();
    ~~~^~
/home/andy/dev/zig/doc/langref/test_expression_ignored.zig:2:8: note: all non-void values must be used
/home/andy/dev/zig/doc/langref/test_expression_ignored.zig:2:8: note: to discard the value, assign it to '_'


```

However, if the expression has type `void`, there will be no error. Expression results can be explicitly ignored by assigning them to `_`.

**`test_void_ignored.zig`:**

```zig
test "void is ignored" {
    returnsVoid();
}

test "explicitly ignoring expression value" {
    _ = foo();
}

fn returnsVoid() void {}

fn foo() i32 {
    return 1234;
}

```

**Shell:**

```shell
$ zig test test_void_ignored.zig
1/2 test_void_ignored.test.void is ignored...OK
2/2 test_void_ignored.test.explicitly ignoring expression value...OK
All 2 tests passed.

```


---

### Result Location Semantics

During compilation, every Zig expression and sub-expression is assigned optional result location
information. This information dictates what type the expression should have (its result type), and
where the resulting value should be placed in memory (its result location). The information is
optional in the sense that not every expression has this information: assignment to
`_`, for instance, does not provide any information about the type of an
expression, nor does it provide a concrete memory location to place it in.

As a motivating example, consider the statement `const x: u32 = 42;`. The type
annotation here provides a result type of `u32` to the initialization expression
`42`, instructing the compiler to coerce this integer (initially of type
`comptime_int`) to this type. We will see more examples shortly.

This is not an implementation detail: the logic outlined above is codified into the Zig language
specification, and is the primary mechanism of type inference in the language. This system is
collectively referred to as "Result Location Semantics".

#### Result Types

Result types are propagated recursively through expressions where possible. For instance, if the
expression `&e` has result type `*u32`, then
`e` is given a result type of `u32`, allowing the
language to perform this coercion before taking a reference.

The result type mechanism is utilized by casting builtins such as `@intCast`.
Rather than taking as an argument the type to cast to, these builtins use their result type to
determine this information. The result type is often known from context; where it is not, the
`@as` builtin can be used to explicitly provide a result type.

We can break down the result types for each component of a simple expression as follows:

**`result_type_propagation.zig`:**

```zig
const expectEqual = @import("std").testing.expectEqual;
test "result type propagates through struct initializer" {
    const S = struct { x: u32 };
    const val: u64 = 123;
    const s: S = .{ .x = @intCast(val) };
    // .{ .x = @intCast(val) }   has result type `S` due to the type annotation
    //         @intCast(val)     has result type `u32` due to the type of the field `S.x`
    //                  val      has no result type, as it is permitted to be any integer type
    try expectEqual(@as(u32, 123), s.x);
}

```

**Shell:**

```shell
$ zig test result_type_propagation.zig
1/1 result_type_propagation.test.result type propagates through struct initializer...OK
All 1 tests passed.

```

This result type information is useful for the aforementioned cast builtins, as well as to avoid
the construction of pre-coercion values, and to avoid the need for explicit type coercions in some
cases. The following table details how some common expressions propagate result types, where
`x` and `y` are arbitrary sub-expressions.

| Expression | Parent Result Type | Sub-expression Result Type |
| --- | --- | --- |
| `const val: T = x` | - | `x` is a `T` |
| `var val: T = x` | - | `x` is a `T` |
| `val = x` | - | `x` is a `@TypeOf(val)` |
| `@as(T, x)` | - | `x` is a `T` |
| `&x` | `*T` | `x` is a `T` |
| `&x` | `[]T` | `x` is some array of `T` |
| `f(x)` | - | `x` has the type of the first parameter of `f` |
| `.{x}` | `T` | `x` is a `@FieldType(T, "0")` |
| `.{ .a = x }` | `T` | `x` is a `@FieldType(T, "a")` |
| `T{x}` | - | `x` is a `@FieldType(T, "0")` |
| `T{ .a = x }` | - | `x` is a `@FieldType(T, "a")` |
| `@Type(x)` | - | `x` is a `std.builtin.Type` |
| `@typeInfo(x)` | - | `x` is a `type` |
| `x << y` | - | `y` is a `std.math.Log2IntCeil(@TypeOf(x))` |

#### Result Locations

In addition to result type information, every expression may be optionally assigned a result
location: a pointer to which the value must be directly written. This system can be used to prevent
intermediate copies when initializing data structures, which can be important for types which must
have a fixed memory address ("pinned" types).

When compiling the simple assignment expression `x = e`, many languages would
create the temporary value `e` on the stack, and then assign it to
`x`, potentially performing a type coercion in the process. Zig approaches this
differently. The expression `e` is given a result type matching the type of
`x`, and a result location of `&x`. For many syntactic
forms of `e`, this has no practical impact. However, it can have important
semantic effects when working with more complex syntax forms.

For instance, if the expression `.{ .a = x, .b = y }` has a result location of
`ptr`, then `x` is given a result location of
`&ptr.a`, and `y` a result location of `&ptr.b`.
Without this system, this expression would construct a temporary struct value entirely on the stack, and
only then copy it to the destination address. In essence, Zig desugars the assignment
`foo = .{ .a = x, .b = y }` to the two statements `foo.a = x; foo.b = y;`.

This can sometimes be important when assigning an aggregate value where the initialization
expression depends on the previous value of the aggregate. The easiest way to demonstrate this is by
attempting to swap fields of a struct or array - the following logic looks sound, but in fact is not:

**`result_location_interfering_with_swap.zig`:**

```zig
const expect = @import("std").testing.expect;
test "attempt to swap array elements with array initializer" {
    var arr: [2]u32 = .{ 1, 2 };
    arr = .{ arr[1], arr[0] };
    // The previous line is equivalent to the following two lines:
    //   arr[0] = arr[1];
    //   arr[1] = arr[0];
    // So this fails!
    try expect(arr[0] == 2); // succeeds
    try expect(arr[1] == 1); // fails
}

```

**Shell:**

```shell
$ zig test result_location_interfering_with_swap.zig
1/1 result_location_interfering_with_swap.test.attempt to swap array elements with array initializer...FAIL (TestUnexpectedResult)
/home/andy/dev/zig/lib/std/testing.zig:607:14: 0x102f019 in expect (std.zig)
    if (!ok) return error.TestUnexpectedResult;
             ^
/home/andy/dev/zig/doc/langref/result_location_interfering_with_swap.zig:10:5: 0x102f144 in test.attempt to swap array elements with array initializer (result_location_interfering_with_swap.zig)
    try expect(arr[1] == 1); // fails
    ^
0 passed; 0 skipped; 1 failed.
error: the following test command failed with exit code 1:
/home/andy/dev/zig/.zig-cache/o/d439bc8d3e0f685e13e3c778e438793a/test --seed=0x9b2332d1

```

The following table details how some common expressions propagate result locations, where
`x` and `y` are arbitrary sub-expressions. Note that
some expressions cannot provide meaningful result locations to sub-expressions, even if they
themselves have a result location.

| Expression | Result Location | Sub-expression Result Locations |
| --- | --- | --- |
| `const val: T = x` | - | `x` has result location `&val` |
| `var val: T = x` | - | `x` has result location `&val` |
| `val = x` | - | `x` has result location `&val` |
| `@as(T, x)` | `ptr` | `x` has no result location |
| `&x` | `ptr` | `x` has no result location |
| `f(x)` | `ptr` | `x` has no result location |
| `.{x}` | `ptr` | `x` has result location `&ptr[0]` |
| `.{ .a = x }` | `ptr` | `x` has result location `&ptr.a` |
| `T{x}` | `ptr` | `x` has no result location (typed initializers do not propagate result locations) |
| `T{ .a = x }` | `ptr` | `x` has no result location (typed initializers do not propagate result locations) |
| `@Type(x)` | `ptr` | `x` has no result location |
| `@typeInfo(x)` | `ptr` | `x` has no result location |
| `x << y` | `ptr` | `x` and `y` do not have result locations |


---

### Memory

The Zig language performs no memory management on behalf of the programmer. This is
why Zig has no runtime, and why Zig code works seamlessly in so many environments,
including real-time software, operating system kernels, embedded devices, and
low latency servers. As a consequence, Zig programmers must always be able to answer
the question:

[Where are the bytes?](#Where-are-the-bytes)

Like Zig, the C programming language has manual memory management. However, unlike Zig,
C has a default allocator - `malloc`, `realloc`, and `free`.
When linking against libc, Zig exposes this allocator with `std.heap.c_allocator`.
However, by convention, there is no default allocator in Zig. Instead, functions which need to
allocate accept an `Allocator` parameter. Likewise, some data structures
accept an `Allocator` parameter in their initialization functions:

**`test_allocator.zig`:**

```zig
const std = @import("std");
const Allocator = std.mem.Allocator;
const expect = std.testing.expect;

test "using an allocator" {
    var buffer: [100]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();
    const result = try concat(allocator, "foo", "bar");
    try expect(std.mem.eql(u8, "foobar", result));
}

fn concat(allocator: Allocator, a: []const u8, b: []const u8) ![]u8 {
    const result = try allocator.alloc(u8, a.len + b.len);
    @memcpy(result[0..a.len], a);
    @memcpy(result[a.len..], b);
    return result;
}

```

**Shell:**

```shell
$ zig test test_allocator.zig
1/1 test_allocator.test.using an allocator...OK
All 1 tests passed.

```

In the above example, 100 bytes of stack memory are used to initialize a
`FixedBufferAllocator`, which is then passed to a function.
As a convenience there is a global `FixedBufferAllocator`
available for quick tests at `std.testing.allocator`,
which will also perform basic leak detection.

Zig has a general purpose allocator available to be imported
with `std.heap.GeneralPurposeAllocator`. However, it is still recommended to
follow the [Choosing an Allocator](45-c.md#Choosing-an-Allocator) guide.

#### Choosing an Allocator

What allocator to use depends on a number of factors. Here is a flow chart to help you decide:

1. Are you making a library? In this case, best to accept an `Allocator`
   as a parameter and allow your library's users to decide what allocator to use.
2. Are you linking libc? In this case, `std.heap.c_allocator` is likely
   the right choice, at least for your main allocator.
3. Is the maximum number of bytes that you will need bounded by a number known at
   [comptime](33-comptime.md#comptime)? In this case, use `std.heap.FixedBufferAllocator`.
4. Is your program a command line application which runs from start to end without any fundamental
   cyclical pattern (such as a video game main loop, or a web server request handler),
   such that it would make sense to free everything at once at the end?
   In this case, it is recommended to follow this pattern:
   **`cli_allocation.zig`:**
   ```zig
   const std = @import("std");

   pub fn main() !void {
       var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
       defer arena.deinit();

       const allocator = arena.allocator();

       const ptr = try allocator.create(i32);
       std.debug.print("ptr={*}\n", .{ptr});
   }
   ```

   **Shell:**
   ```shell
   $ zig build-exe cli_allocation.zig
   $ ./cli_allocation
   ptr=i32@7f1a3ed8e010

   ```

   When using this kind of allocator, there is no need to free anything manually. Everything
   gets freed at once with the call to `arena.deinit()`.
5. Are the allocations part of a cyclical pattern such as a video game main loop, or a web
   server request handler? If the allocations can all be freed at once, at the end of the cycle,
   for example once the video game frame has been fully rendered, or the web server request has
   been served, then `std.heap.ArenaAllocator` is a great candidate. As
   demonstrated in the previous bullet point, this allows you to free entire arenas at once.
   Note also that if an upper bound of memory can be established, then
   `std.heap.FixedBufferAllocator` can be used as a further optimization.
6. Are you writing a test, and you want to make sure `error.OutOfMemory`
   is handled correctly? In this case, use `std.testing.FailingAllocator`.
7. Are you writing a test? In this case, use `std.testing.allocator`.
8. Finally, if none of the above apply, you need a general purpose allocator.
   If you are in Debug mode, `std.heap.DebugAllocator` is available as a
   function that takes a [comptime](33-comptime.md#comptime) [struct](15-struct.md#struct) of configuration options and returns a type.
   Generally, you will set up exactly one in your main function, and
   then pass it or sub-allocators around to various parts of your
   application.
9. If you are compiling in ReleaseFast mode, `std.heap.smp_allocator` is
   a solid choice for a general purpose allocator.
10. You can also consider implementing an allocator.

#### Where are the bytes?

String literals such as `"hello"` are in the global constant data section.
This is why it is an error to pass a string literal to a mutable slice, like this:

**`test_string_literal_to_slice.zig`:**

```zig
fn foo(s: []u8) void {
    _ = s;
}

test "string literal to mutable slice" {
    foo("hello");
}

```

**Shell:**

```shell
$ zig test test_string_literal_to_slice.zig
/home/andy/dev/zig/doc/langref/test_string_literal_to_slice.zig:6:9: error: expected type '[]u8', found '*const [5:0]u8'
    foo("hello");
        ^~~~~~~
/home/andy/dev/zig/doc/langref/test_string_literal_to_slice.zig:6:9: note: cast discards const qualifier
/home/andy/dev/zig/doc/langref/test_string_literal_to_slice.zig:1:11: note: parameter type declared here
fn foo(s: []u8) void {
          ^~~~


```

However if you make the slice constant, then it works:

**`test_string_literal_to_const_slice.zig`:**

```zig
fn foo(s: []const u8) void {
    _ = s;
}

test "string literal to constant slice" {
    foo("hello");
}

```

**Shell:**

```shell
$ zig test test_string_literal_to_const_slice.zig
1/1 test_string_literal_to_const_slice.test.string literal to constant slice...OK
All 1 tests passed.

```

Just like string literals, `const` declarations, when the value is known at [comptime](33-comptime.md#comptime),
are stored in the global constant data section. Also [Compile Time Variables](45-c.md#Compile-Time-Variables) are stored
in the global constant data section.

`var` declarations inside functions are stored in the function's stack frame. Once a function returns,
any [Pointers](13-pointers.md#Pointers) to variables in the function's stack frame become invalid references, and
dereferencing them becomes unchecked [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior).

`var` declarations at the top level or in [struct](15-struct.md#struct) declarations are stored in the global
data section.

The location of memory allocated with `allocator.alloc` or
`allocator.create` is determined by the allocator's implementation.

TODO: thread local variables

#### Heap Allocation Failure

Many programming languages choose to handle the possibility of heap allocation failure by
unconditionally crashing. By convention, Zig programmers do not consider this to be a
satisfactory solution. Instead, `error.OutOfMemory` represents
heap allocation failure, and Zig libraries return this error code whenever heap allocation
failure prevented an operation from completing successfully.

Some have argued that because some operating systems such as Linux have memory overcommit enabled by
default, it is pointless to handle heap allocation failure. There are many problems with this reasoning:

- Only some operating systems have an overcommit feature.
  - Linux has it enabled by default, but it is configurable.
  - Windows does not overcommit.
  - Embedded systems do not have overcommit.
  - Hobby operating systems may or may not have overcommit.
- For real-time systems, not only is there no overcommit, but typically the maximum amount
  of memory per application is determined ahead of time.
- When writing a library, one of the main goals is code reuse. By making code handle
  allocation failure correctly, a library becomes eligible to be reused in
  more contexts.
- Although some software has grown to depend on overcommit being enabled, its existence
  is the source of countless user experience disasters. When a system with overcommit enabled,
  such as Linux on default settings, comes close to memory exhaustion, the system locks up
  and becomes unusable. At this point, the OOM Killer selects an application to kill
  based on heuristics. This non-deterministic decision often results in an important process
  being killed, and often fails to return the system back to working order.

#### Recursion

Recursion is a fundamental tool in modeling software. However it has an often-overlooked problem:
unbounded memory allocation.

Recursion is an area of active experimentation in Zig and so the documentation here is not final.
You can read a
[summary of recursion status in the 0.3.0 release notes](https://ziglang.org/download/0.3.0/release-notes.html#recursion).

The short summary is that currently recursion works normally as you would expect. Although Zig code
is not yet protected from stack overflow, it is planned that a future version of Zig will provide
such protection, with some degree of cooperation from Zig code required.

#### Lifetime and Ownership

It is the Zig programmer's responsibility to ensure that a [pointer](13-pointers.md#Pointers) is not
accessed when the memory pointed to is no longer available. Note that a [slice](14-slices.md#Slices)
is a form of pointer, in that it references other memory.

In order to prevent bugs, there are some helpful conventions to follow when dealing with pointers.
In general, when a function returns a pointer, the documentation for the function should explain
who "owns" the pointer. This concept helps the programmer decide when it is appropriate, if ever,
to free the pointer.

For example, the function's documentation may say "caller owns the returned memory", in which case
the code that calls the function must have a plan for when to free that memory. Probably in this situation,
the function will accept an `Allocator` parameter.

Sometimes the lifetime of a pointer may be more complicated. For example, the
`std.ArrayList(T).items` slice has a lifetime that remains
valid until the next time the list is resized, such as by appending new elements.

The API documentation for functions and data structures should take great care to explain
the ownership and lifetime semantics of pointers. Ownership determines whose responsibility it
is to free the memory referenced by the pointer, and lifetime determines the point at which
the memory becomes inaccessible (lest [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior) occur).


---
