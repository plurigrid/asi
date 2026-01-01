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
/home/andy/dev/zig/lib/std/testing.zig:580:14: 0x10488ef in expect (test)
    if (!ok) return error.TestUnexpectedResult;
             ^
/home/andy/dev/zig/doc/langref/result_location_interfering_with_swap.zig:10:5: 0x10489d5 in test.attempt to swap array elements with array initializer (test)
    try expect(arr[1] == 1); // fails
    ^
0 passed; 0 skipped; 1 failed.
error: the following test command failed with exit code 1:
/home/andy/dev/zig/.zig-cache/o/ad052551079782d9997770925a86a745/test --seed=0x7bedf42

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
