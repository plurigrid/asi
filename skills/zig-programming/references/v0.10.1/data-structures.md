# Data Structures

*How to organize and structure data in Zig*


---

### Arrays

**`arrays.zig`:**

```zig
const expect = @import("std").testing.expect;
const assert = @import("std").debug.assert;
const mem = @import("std").mem;

// array literal
const message = [_]u8{ 'h', 'e', 'l', 'l', 'o' };

// get the size of an array
comptime {
    assert(message.len == 5);
}

// A string literal is a single-item pointer to an array literal.
const same_message = "hello";

comptime {
    assert(mem.eql(u8, &message, same_message));
}

test "iterate over an array" {
    var sum: usize = 0;
    for (message) |byte| {
        sum += byte;
    }
    try expect(sum == 'h' + 'e' + 'l' * 2 + 'o');
}

// modifiable array
var some_integers: [100]i32 = undefined;

test "modify an array" {
    for (some_integers) |*item, i| {
        item.* = @intCast(i32, i);
    }
    try expect(some_integers[10] == 10);
    try expect(some_integers[99] == 99);
}

// array concatenation works if the values are known
// at compile time
const part_one = [_]i32{ 1, 2, 3, 4 };
const part_two = [_]i32{ 5, 6, 7, 8 };
const all_of_it = part_one ++ part_two;
comptime {
    assert(mem.eql(i32, &all_of_it, &[_]i32{ 1, 2, 3, 4, 5, 6, 7, 8 }));
}

// remember that string literals are arrays
const hello = "hello";
const world = "world";
const hello_world = hello ++ " " ++ world;
comptime {
    assert(mem.eql(u8, hello_world, "hello world"));
}

// ** does repeating patterns
const pattern = "ab" ** 3;
comptime {
    assert(mem.eql(u8, pattern, "ababab"));
}

// initialize an array to zero
const all_zero = [_]u16{0} ** 10;

comptime {
    assert(all_zero.len == 10);
    assert(all_zero[5] == 0);
}

// use compile-time code to initialize an array
var fancy_array = init: {
    var initial_value: [10]Point = undefined;
    for (initial_value) |*pt, i| {
        pt.* = Point{
            .x = @intCast(i32, i),
            .y = @intCast(i32, i) * 2,
        };
    }
    break :init initial_value;
};
const Point = struct {
    x: i32,
    y: i32,
};

test "compile-time array initialization" {
    try expect(fancy_array[4].x == 4);
    try expect(fancy_array[4].y == 8);
}

// call a function to initialize an array
var more_points = [_]Point{makePoint(3)} ** 10;
fn makePoint(x: i32) Point {
    return Point{
        .x = x,
        .y = x * 2,
    };
}
test "array initialization with function calls" {
    try expect(more_points[4].x == 3);
    try expect(more_points[4].y == 6);
    try expect(more_points.len == 10);
}

```

**Shell:**

```shell
$ zig test arrays.zig
1/4 test.iterate over an array... OK
2/4 test.modify an array... OK
3/4 test.compile-time array initialization... OK
4/4 test.array initialization with function calls... OK
All 4 tests passed.

```

See also:

- [for](22-for.md#for)
- [Slices](14-slices.md#Slices)

#### Anonymous List Literals

Similar to [Enum Literals](#Enum-Literals) and [Anonymous Struct Literals](#Anonymous-Struct-Literals)
the type can be omitted from array literals:

**`anon_list.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "anonymous list literal syntax" {
    var array: [4]u8 = .{11, 22, 33, 44};
    try expect(array[0] == 11);
    try expect(array[1] == 22);
    try expect(array[2] == 33);
    try expect(array[3] == 44);
}

```

**Shell:**

```shell
$ zig test anon_list.zig
1/1 test.anonymous list literal syntax... OK
All 1 tests passed.

```

If there is no type in the result location then an anonymous list literal actually
turns into a [struct](15-struct.md#struct) with numbered field names:

**`infer_list_literal.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "fully anonymous list literal" {
    try dump(.{ @as(u32, 1234), @as(f64, 12.34), true, "hi"});
}

fn dump(args: anytype) !void {
    try expect(args.@"0" == 1234);
    try expect(args.@"1" == 12.34);
    try expect(args.@"2");
    try expect(args.@"3"[0] == 'h');
    try expect(args.@"3"[1] == 'i');
}

```

**Shell:**

```shell
$ zig test infer_list_literal.zig
1/1 test.fully anonymous list literal... OK
All 1 tests passed.

```

#### Multidimensional Arrays

Multidimensional arrays can be created by nesting arrays:

**`multidimensional.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const mat4x4 = [4][4]f32{
    [_]f32{ 1.0, 0.0, 0.0, 0.0 },
    [_]f32{ 0.0, 1.0, 0.0, 1.0 },
    [_]f32{ 0.0, 0.0, 1.0, 0.0 },
    [_]f32{ 0.0, 0.0, 0.0, 1.0 },
};
test "multidimensional arrays" {
    // Access the 2D array by indexing the outer array, and then the inner array.
    try expect(mat4x4[1][1] == 1.0);

    // Here we iterate with for loops.
    for (mat4x4) |row, row_index| {
        for (row) |cell, column_index| {
            if (row_index == column_index) {
                try expect(cell == 1.0);
            }
        }
    }
}

```

**Shell:**

```shell
$ zig test multidimensional.zig
1/1 test.multidimensional arrays... OK
All 1 tests passed.

```

#### Sentinel-Terminated Arrays

The syntax `[N:x]T` describes an array which has a sentinel element of value `x` at the
index corresponding to `len`.

**`null_terminated_array.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "null terminated array" {
    const array = [_:0]u8 {1, 2, 3, 4};

    try expect(@TypeOf(array) == [4:0]u8);
    try expect(array.len == 4);
    try expect(array[4] == 0);
}

```

**Shell:**

```shell
$ zig test null_terminated_array.zig
1/1 test.null terminated array... OK
All 1 tests passed.

```

See also:

- [Sentinel-Terminated Pointers](#Sentinel-Terminated-Pointers)
- [Sentinel-Terminated Slices](#Sentinel-Terminated-Slices)


---

### Vectors

A vector is a group of booleans, [Integers](08-integers.md#Integers), [Floats](09-floats.md#Floats), or
[Pointers](13-pointers.md#Pointers) which are operated on in parallel, using SIMD instructions if possible.
Vector types are created with the builtin function [@Vector](#Vector).

Vectors support the same builtin operators as their underlying base types.
These operations are performed element-wise, and return a vector of the same length
as the input vectors. This includes:

- Arithmetic (`+`, `-`, `/`, `*`,
  `@divFloor`, `@sqrt`, `@ceil`,
  `@log`, etc.)
- Bitwise operators (`>>`, `<<`, `&`,
  `|`, `~`, etc.)
- Comparison operators (`<`, `>`, `==`, etc.)

It is prohibited to use a math operator on a mixture of scalars (individual numbers)
and vectors. Zig provides the [@splat](#splat) builtin to easily convert from scalars
to vectors, and it supports [@reduce](#reduce) and array indexing syntax to convert
from vectors to scalars. Vectors also support assignment to and from fixed-length
arrays with comptime known length.

For rearranging elements within and between vectors, Zig provides the [@shuffle](#shuffle) and [@select](#select) functions.

Operations on vectors shorter than the target machine's native SIMD size will typically compile to single SIMD
instructions, while vectors longer than the target machine's native SIMD size will compile to multiple SIMD
instructions. If a given operation doesn't have SIMD support on the target architecture, the compiler will default
to operating on each vector element one at a time. Zig supports any comptime-known vector length up to 2^32-1,
although small powers of two (2-64) are most typical. Note that excessively long vector lengths (e.g. 2^20) may
result in compiler crashes on current versions of Zig.

**`vector_example.zig`:**

```zig
const std = @import("std");
const expectEqual = std.testing.expectEqual;

test "Basic vector usage" {
    // Vectors have a compile-time known length and base type.
    const a = @Vector(4, i32){ 1, 2, 3, 4 };
    const b = @Vector(4, i32){ 5, 6, 7, 8 };

    // Math operations take place element-wise.
    const c = a + b;

    // Individual vector elements can be accessed using array indexing syntax.
    try expectEqual(6, c[0]);
    try expectEqual(8, c[1]);
    try expectEqual(10, c[2]);
    try expectEqual(12, c[3]);
}

test "Conversion between vectors, arrays, and slices" {
    // Vectors and fixed-length arrays can be automatically assigned back and forth
    var arr1: [4]f32 = [_]f32{ 1.1, 3.2, 4.5, 5.6 };
    var vec: @Vector(4, f32) = arr1;
    var arr2: [4]f32 = vec;
    try expectEqual(arr1, arr2);

    // You can also assign from a slice with comptime-known length to a vector using .*
    const vec2: @Vector(2, f32) = arr1[1..3].*;

    var slice: []const f32 = &arr1;
    var offset: u32 = 1;
    // To extract a comptime-known length from a runtime-known offset,
    // first extract a new slice from the starting offset, then an array of
    // comptime known length
    const vec3: @Vector(2, f32) = slice[offset..][0..2].*;
    try expectEqual(slice[offset], vec2[0]);
    try expectEqual(slice[offset + 1], vec2[1]);
    try expectEqual(vec2, vec3);
}

```

**Shell:**

```shell
$ zig test vector_example.zig
1/2 test.Basic vector usage... OK
2/2 test.Conversion between vectors, arrays, and slices... OK
All 2 tests passed.

```

TODO talk about C ABI interop  
TODO consider suggesting std.MultiArrayList

See also:

- [@splat](#splat)
- [@shuffle](#shuffle)
- [@select](#select)
- [@reduce](#reduce)


---

### Pointers

Zig has two kinds of pointers: single-item and many-item.

- `*T` - single-item pointer to exactly one item.
  - Supports deref syntax: `ptr.*`
- `[*]T` - many-item pointer to unknown number of items.
  - Supports index syntax: `ptr[i]`
  - Supports slice syntax: `ptr[start..end]`
  - Supports pointer arithmetic: `ptr + x`, `ptr - x`
  - `T` must have a known size, which means that it cannot be
    `anyopaque` or any other [opaque type](18-opaque.md#opaque).

These types are closely related to [Arrays](11-arrays.md#Arrays) and [Slices](14-slices.md#Slices):

- `*[N]T` - pointer to N items, same as single-item pointer to an array.
  - Supports index syntax: `array_ptr[i]`
  - Supports slice syntax: `array_ptr[start..end]`
  - Supports len property: `array_ptr.len`

- `[]T` - is a slice (a fat pointer, which contains a pointer of type `[*]T` and a length).
  - Supports index syntax: `slice[i]`
  - Supports slice syntax: `slice[start..end]`
  - Supports len property: `slice.len`

Use `&x` to obtain a single-item pointer:

**`single_item_pointer_test.zig`:**

```zig
const expect = @import("std").testing.expect;

test "address of syntax" {
    // Get the address of a variable:
    const x: i32 = 1234;
    const x_ptr = &x;

    // Dereference a pointer:
    try expect(x_ptr.* == 1234);

    // When you get the address of a const variable, you get a const single-item pointer.
    try expect(@TypeOf(x_ptr) == *const i32);

    // If you want to mutate the value, you'd need an address of a mutable variable:
    var y: i32 = 5678;
    const y_ptr = &y;
    try expect(@TypeOf(y_ptr) == *i32);
    y_ptr.* += 1;
    try expect(y_ptr.* == 5679);
}

test "pointer array access" {
    // Taking an address of an individual element gives a
    // single-item pointer. This kind of pointer
    // does not support pointer arithmetic.
    var array = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    const ptr = &array[2];
    try expect(@TypeOf(ptr) == *u8);

    try expect(array[2] == 3);
    ptr.* += 1;
    try expect(array[2] == 4);
}

```

**Shell:**

```shell
$ zig test single_item_pointer_test.zig
1/2 test.address of syntax... OK
2/2 test.pointer array access... OK
All 2 tests passed.

```

Zig supports pointer arithmetic. It's better to assign the pointer to `[*]T` and increment that variable. For example, directly incrementing the pointer from a slice will corrupt it.

**`pointer_arthemtic.zig`:**

```zig
const expect = @import("std").testing.expect;

test "pointer arithmetic with many-item pointer" {
    const array = [_]i32{ 1, 2, 3, 4 };
    var ptr: [*]const i32 = &array;

    try expect(ptr[0] == 1);
    ptr += 1;
    try expect(ptr[0] == 2);
}

test "pointer arithmetic with slices" {
    var array = [_]i32{ 1, 2, 3, 4 };
    var length: usize = 0;
    var slice = array[length..array.len];

    try expect(slice[0] == 1);
    try expect(slice.len == 4);

    slice.ptr += 1;
    // now the slice is in an bad state since len has not been updated

    try expect(slice[0] == 2);
    try expect(slice.len == 4);
}

```

**Shell:**

```shell
$ zig test pointer_arthemtic.zig
1/2 test.pointer arithmetic with many-item pointer... OK
2/2 test.pointer arithmetic with slices... OK
All 2 tests passed.

```

In Zig, we generally prefer [Slices](14-slices.md#Slices) rather than [Sentinel-Terminated Pointers](#Sentinel-Terminated-Pointers).
You can turn an array or pointer into a slice using slice syntax.

Slices have bounds checking and are therefore protected
against this kind of undefined behavior. This is one reason
we prefer slices to pointers.

**`slice_bounds.zig`:**

```zig
const expect = @import("std").testing.expect;

test "pointer slicing" {
    var array = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    const slice = array[2..4];
    try expect(slice.len == 2);

    try expect(array[3] == 4);
    slice[1] += 1;
    try expect(array[3] == 5);
}

```

**Shell:**

```shell
$ zig test slice_bounds.zig
1/1 test.pointer slicing... OK
All 1 tests passed.

```

Pointers work at compile-time too, as long as the code does not depend on
an undefined memory layout:

**`comptime_pointers.zig`:**

```zig
const expect = @import("std").testing.expect;

test "comptime pointers" {
    comptime {
        var x: i32 = 1;
        const ptr = &x;
        ptr.* += 1;
        x += 1;
        try expect(ptr.* == 3);
    }
}

```

**Shell:**

```shell
$ zig test comptime_pointers.zig
1/1 test.comptime pointers... OK
All 1 tests passed.

```

To convert an integer address into a pointer, use `@intToPtr`.
To convert a pointer to an integer, use `@ptrToInt`:

**`integer_pointer_conversion.zig`:**

```zig
const expect = @import("std").testing.expect;

test "@ptrToInt and @intToPtr" {
    const ptr = @intToPtr(*i32, 0xdeadbee0);
    const addr = @ptrToInt(ptr);
    try expect(@TypeOf(addr) == usize);
    try expect(addr == 0xdeadbee0);
}

```

**Shell:**

```shell
$ zig test integer_pointer_conversion.zig
1/1 test.@ptrToInt and @intToPtr... OK
All 1 tests passed.

```

Zig is able to preserve memory addresses in comptime code, as long as
the pointer is never dereferenced:

**`comptime_pointer_conversion.zig`:**

```zig
const expect = @import("std").testing.expect;

test "comptime @intToPtr" {
    comptime {
        // Zig is able to do this at compile-time, as long as
        // ptr is never dereferenced.
        const ptr = @intToPtr(*i32, 0xdeadbee0);
        const addr = @ptrToInt(ptr);
        try expect(@TypeOf(addr) == usize);
        try expect(addr == 0xdeadbee0);
    }
}

```

**Shell:**

```shell
$ zig test comptime_pointer_conversion.zig
1/1 test.comptime @intToPtr... OK
All 1 tests passed.

```

See also:

- [Optional Pointers](#Optional-Pointers)
- [@intToPtr](#intToPtr)
- [@ptrToInt](#ptrToInt)
- [C Pointers](46-c.md#C-Pointers)

#### volatile

Loads and stores are assumed to not have side effects. If a given load or store
should have side effects, such as Memory Mapped Input/Output (MMIO), use `volatile`.
In the following code, loads and stores with `mmio_ptr` are guaranteed to all happen
and in the same order as in source code:

**`volatile.zig`:**

```zig
const expect = @import("std").testing.expect;

test "volatile" {
    const mmio_ptr = @intToPtr(*volatile u8, 0x12345678);
    try expect(@TypeOf(mmio_ptr) == *volatile u8);
}

```

**Shell:**

```shell
$ zig test volatile.zig
1/1 test.volatile... OK
All 1 tests passed.

```

Note that `volatile` is unrelated to concurrency and [Atomics](36-atomics.md#Atomics).
If you see code that is using `volatile` for something other than Memory Mapped
Input/Output, it is probably a bug.

To convert one pointer type to another, use [@ptrCast](#ptrCast). This is an unsafe
operation that Zig cannot protect you against. Use `@ptrCast` only when other
conversions are not possible.

**`pointer_casting.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "pointer casting" {
    const bytes align(@alignOf(u32)) = [_]u8{ 0x12, 0x12, 0x12, 0x12 };
    const u32_ptr = @ptrCast(*const u32, &bytes);
    try expect(u32_ptr.* == 0x12121212);

    // Even this example is contrived - there are better ways to do the above than
    // pointer casting. For example, using a slice narrowing cast:
    const u32_value = std.mem.bytesAsSlice(u32, bytes[0..])[0];
    try expect(u32_value == 0x12121212);

    // And even another way, the most straightforward way to do it:
    try expect(@bitCast(u32, bytes) == 0x12121212);
}

test "pointer child type" {
    // pointer types have a `child` field which tells you the type they point to.
    try expect(@typeInfo(*u32).Pointer.child == u32);
}

```

**Shell:**

```shell
$ zig test pointer_casting.zig
1/2 test.pointer casting... OK
2/2 test.pointer child type... OK
All 2 tests passed.

```

#### Alignment

Each type has an **alignment** - a number of bytes such that,
when a value of the type is loaded from or stored to memory,
the memory address must be evenly divisible by this number. You can use
[@alignOf](#alignOf) to find out this value for any type.

Alignment depends on the CPU architecture, but is always a power of two, and
less than `1 << 29`.

In Zig, a pointer type has an alignment value. If the value is equal to the
alignment of the underlying type, it can be omitted from the type:

**`variable_alignment.zig`:**

```zig
const std = @import("std");
const builtin = @import("builtin");
const expect = std.testing.expect;

test "variable alignment" {
    var x: i32 = 1234;
    const align_of_i32 = @alignOf(@TypeOf(x));
    try expect(@TypeOf(&x) == *i32);
    try expect(*i32 == *align(align_of_i32) i32);
    if (builtin.target.cpu.arch == .x86_64) {
        try expect(@typeInfo(*i32).Pointer.alignment == 4);
    }
}

```

**Shell:**

```shell
$ zig test variable_alignment.zig
1/1 test.variable alignment... OK
All 1 tests passed.

```

In the same way that a `*i32` can be [coerced](#Type-Coercion) to a
`*const i32`, a pointer with a larger alignment can be implicitly
cast to a pointer with a smaller alignment, but not vice versa.

You can specify alignment on variables and functions. If you do this, then
pointers to them get the specified alignment:

**`variable_func_alignment.zig`:**

```zig
const expect = @import("std").testing.expect;

var foo: u8 align(4) = 100;

test "global variable alignment" {
    try expect(@typeInfo(@TypeOf(&foo)).Pointer.alignment == 4);
    try expect(@TypeOf(&foo) == *align(4) u8);
    const as_pointer_to_array: *align(4) [1]u8 = &foo;
    const as_slice: []align(4) u8 = as_pointer_to_array;
    const as_unaligned_slice: []u8 = as_slice;
    try expect(as_unaligned_slice[0] == 100);
}

fn derp() align(@sizeOf(usize) * 2) i32 {
    return 1234;
}
fn noop1() align(1) void {}
fn noop4() align(4) void {}

test "function alignment" {
    try expect(derp() == 1234);
    try expect(@TypeOf(noop1) == fn () align(1) void);
    try expect(@TypeOf(noop4) == fn () align(4) void);
    noop1();
    noop4();
}

```

**Shell:**

```shell
$ zig test variable_func_alignment.zig
1/2 test.global variable alignment... OK
2/2 test.function alignment... OK
All 2 tests passed.

```

If you have a pointer or a slice that has a small alignment, but you know that it actually
has a bigger alignment, use [@alignCast](#alignCast) to change the
pointer into a more aligned pointer. This is a no-op at runtime, but inserts a
[safety check](#Incorrect-Pointer-Alignment):

**`test.zig`:**

```zig
const std = @import("std");

test "pointer alignment safety" {
    var array align(4) = [_]u32{ 0x11111111, 0x11111111 };
    const bytes = std.mem.sliceAsBytes(array[0..]);
    try std.testing.expect(foo(bytes) == 0x11111111);
}
fn foo(bytes: []u8) u32 {
    const slice4 = bytes[1..5];
    const int_slice = std.mem.bytesAsSlice(u32, @alignCast(4, slice4));
    return int_slice[0];
}

```

**Shell:**

```shell
$ zig test test.zig
1/1 test.pointer alignment safety... thread 3566936 panic: incorrect alignment
docgen_tmp/test.zig:10:43: 0x2117ab in foo (test)
    const int_slice = std.mem.bytesAsSlice(u32, @alignCast(4, slice4));
                                          ^
docgen_tmp/test.zig:6:31: 0x2116cf in test.pointer alignment safety (test)
    try std.testing.expect(foo(bytes) == 0x11111111);
                              ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/test_runner.zig:63:28: 0x212f93 in main (test)
        } else test_fn.func();
                           ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/std/start.zig:604:22: 0x2120fc in posixCallMainAndExit (test)
            root.main();
                     ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/std/start.zig:376:5: 0x211c01 in _start (test)
    @call(.{ .modifier = .never_inline }, posixCallMainAndExit, .{});
    ^
error: the following test command crashed:
/home/ci/release-0.10.1/out/zig-local-cache/o/886dbde2c2a21074c6c6d3ff9b83336b/test

```

#### allowzero

This pointer attribute allows a pointer to have address zero. This is only ever needed on the
freestanding OS target, where the address zero is mappable. If you want to represent null pointers, use
[Optional Pointers](#Optional-Pointers) instead. [Optional Pointers](#Optional-Pointers) with `allowzero`
are not the same size as pointers. In this code example, if the pointer
did not have the `allowzero` attribute, this would be a
[Pointer Cast Invalid Null](#Pointer-Cast-Invalid-Null) panic:

**`allowzero.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "allowzero" {
    var zero: usize = 0;
    var ptr = @intToPtr(*allowzero i32, zero);
    try expect(@ptrToInt(ptr) == 0);
}

```

**Shell:**

```shell
$ zig test allowzero.zig
1/1 test.allowzero... OK
All 1 tests passed.

```

#### Sentinel-Terminated Pointers

The syntax `[*:x]T` describes a pointer that
has a length determined by a sentinel value. This provides protection
against buffer overflow and overreads.

**`test.zig`:**

```zig
const std = @import("std");

// This is also available as `std.c.printf`.
pub extern "c" fn printf(format: [*:0]const u8, ...) c_int;

pub fn main() anyerror!void {
    _ = printf("Hello, world!\n"); // OK

    const msg = "Hello, world!\n";
    const non_null_terminated_msg: [msg.len]u8 = msg.*;
    _ = printf(&non_null_terminated_msg);
}

```

**Shell:**

```shell
$ zig build-exe test.zig -lc
docgen_tmp/test.zig:11:16: error: expected type '[*:0]const u8', found '*const [14]u8'
    _ = printf(&non_null_terminated_msg);
               ^~~~~~~~~~~~~~~~~~~~~~~~
docgen_tmp/test.zig:11:16: note: destination pointer requires '0' sentinel
docgen_tmp/test.zig:4:35: note: parameter type declared here
pub extern "c" fn printf(format: [*:0]const u8, ...) c_int;
                                 ~^~~~~~~~~~~~
referenced by:
    comptime_0: /home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/std/start.zig:59:50
    remaining reference traces hidden; use '-freference-trace' to see all reference traces


```

See also:

- [Sentinel-Terminated Slices](#Sentinel-Terminated-Slices)
- [Sentinel-Terminated Arrays](#Sentinel-Terminated-Arrays)


---

### Slices

**`test.zig`:**

```zig
const expect = @import("std").testing.expect;

test "basic slices" {
    var array = [_]i32{ 1, 2, 3, 4 };
    // A slice is a pointer and a length. The difference between an array and
    // a slice is that the array's length is part of the type and known at
    // compile-time, whereas the slice's length is known at runtime.
    // Both can be accessed with the `len` field.
    var known_at_runtime_zero: usize = 0;
    const slice = array[known_at_runtime_zero..array.len];
    try expect(@TypeOf(slice) == []i32);
    try expect(&slice[0] == &array[0]);
    try expect(slice.len == array.len);

    // If you slice with comptime-known start and end positions, the result is
    // a pointer to an array, rather than a slice.
    const array_ptr = array[0..array.len];
    try expect(@TypeOf(array_ptr) == *[array.len]i32);

    // Using the address-of operator on a slice gives a single-item pointer,
    // while using the `ptr` field gives a many-item pointer.
    try expect(@TypeOf(slice.ptr) == [*]i32);
    try expect(@TypeOf(&slice[0]) == *i32);
    try expect(@ptrToInt(slice.ptr) == @ptrToInt(&slice[0]));

    // Slices have array bounds checking. If you try to access something out
    // of bounds, you'll get a safety check failure:
    slice[10] += 1;

    // Note that `slice.ptr` does not invoke safety checking, while `&slice[0]`
    // asserts that the slice has len >= 1.
}

```

**Shell:**

```shell
$ zig test test.zig
1/1 test.basic slices... thread 3567298 panic: index out of bounds: index 10, len 4
docgen_tmp/test.zig:28:10: 0x2119c6 in test.basic slices (test)
    slice[10] += 1;
         ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/test_runner.zig:63:28: 0x2131b3 in main (test)
        } else test_fn.func();
                           ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/std/start.zig:604:22: 0x21233c in posixCallMainAndExit (test)
            root.main();
                     ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/std/start.zig:376:5: 0x211e41 in _start (test)
    @call(.{ .modifier = .never_inline }, posixCallMainAndExit, .{});
    ^
error: the following test command crashed:
/home/ci/release-0.10.1/out/zig-local-cache/o/886dbde2c2a21074c6c6d3ff9b83336b/test

```

This is one reason we prefer slices to pointers.

**`slices.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;
const mem = std.mem;
const fmt = std.fmt;

test "using slices for strings" {
    // Zig has no concept of strings. String literals are const pointers
    // to null-terminated arrays of u8, and by convention parameters
    // that are "strings" are expected to be UTF-8 encoded slices of u8.
    // Here we coerce *const [5:0]u8 and *const [6:0]u8 to []const u8
    const hello: []const u8 = "hello";
    const world: []const u8 = "ä¸ç";

    var all_together: [100]u8 = undefined;
    // You can use slice syntax on an array to convert an array into a slice.
    const all_together_slice = all_together[0..];
    // String concatenation example.
    const hello_world = try fmt.bufPrint(all_together_slice, "{s} {s}", .{ hello, world });

    // Generally, you can use UTF-8 and not worry about whether something is a
    // string. If you don't need to deal with individual characters, no need
    // to decode.
    try expect(mem.eql(u8, hello_world, "hello ä¸ç"));
}

test "slice pointer" {
    var a: []u8 = undefined;
    try expect(@TypeOf(a) == []u8);
    var array: [10]u8 = undefined;
    const ptr = &array;
    try expect(@TypeOf(ptr) == *[10]u8);

    // A pointer to an array can be sliced just like an array:
    var start: usize = 0;
    var end: usize = 5;
    const slice = ptr[start..end];
    slice[2] = 3;
    try expect(slice[2] == 3);
    // The slice is mutable because we sliced a mutable pointer.
    try expect(@TypeOf(slice) == []u8);

    // Again, slicing with constant indexes will produce another pointer to an array:
    const ptr2 = slice[2..3];
    try expect(ptr2.len == 1);
    try expect(ptr2[0] == 3);
    try expect(@TypeOf(ptr2) == *[1]u8);
}

```

**Shell:**

```shell
$ zig test slices.zig
1/2 test.using slices for strings... OK
2/2 test.slice pointer... OK
All 2 tests passed.

```

See also:

- [Pointers](13-pointers.md#Pointers)
- [for](22-for.md#for)
- [Arrays](11-arrays.md#Arrays)

#### Sentinel-Terminated Slices

The syntax `[:x]T` is a slice which has a runtime known length
and also guarantees a sentinel value at the element indexed by the length. The type does not
guarantee that there are no sentinel elements before that. Sentinel-terminated slices allow element
access to the `len` index.

**`null_terminated_slice.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "null terminated slice" {
    const slice: [:0]const u8 = "hello";

    try expect(slice.len == 5);
    try expect(slice[5] == 0);
}

```

**Shell:**

```shell
$ zig test null_terminated_slice.zig
1/1 test.null terminated slice... OK
All 1 tests passed.

```

Sentinel-terminated slices can also be created using a variation of the slice syntax
`data[start..end :x]`, where `data` is a many-item pointer,
array or slice and `x` is the sentinel value.

**`null_terminated_slicing.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "null terminated slicing" {
    var array = [_]u8{ 3, 2, 1, 0, 3, 2, 1, 0 };
    var runtime_length: usize = 3;
    const slice = array[0..runtime_length :0];

    try expect(@TypeOf(slice) == [:0]u8);
    try expect(slice.len == 3);
}

```

**Shell:**

```shell
$ zig test null_terminated_slicing.zig
1/1 test.null terminated slicing... OK
All 1 tests passed.

```

Sentinel-terminated slicing asserts that the element in the sentinel position of the backing data is
actually the sentinel value. If this is not the case, safety-protected [Undefined Behavior](41-undefined-behavior.md#Undefined-Behavior) results.

**`test.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "sentinel mismatch" {
    var array = [_]u8{ 3, 2, 1, 0 };

    // Creating a sentinel-terminated slice from the array with a length of 2
    // will result in the value `1` occupying the sentinel element position.
    // This does not match the indicated sentinel value of `0` and will lead
    // to a runtime panic.
    var runtime_length: usize = 2;
    const slice = array[0..runtime_length :0];

    _ = slice;
}

```

**Shell:**

```shell
$ zig test test.zig
1/1 test.sentinel mismatch... thread 3567804 panic: sentinel mismatch: expected 0, found 1
docgen_tmp/test.zig:12:24: 0x211604 in test.sentinel mismatch (test)
    const slice = array[0..runtime_length :0];
                       ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/test_runner.zig:63:28: 0x212fc3 in main (test)
        } else test_fn.func();
                           ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/std/start.zig:604:22: 0x211f6c in posixCallMainAndExit (test)
            root.main();
                     ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/std/start.zig:376:5: 0x211a71 in _start (test)
    @call(.{ .modifier = .never_inline }, posixCallMainAndExit, .{});
    ^
error: the following test command crashed:
/home/ci/release-0.10.1/out/zig-local-cache/o/886dbde2c2a21074c6c6d3ff9b83336b/test

```

See also:

- [Sentinel-Terminated Pointers](#Sentinel-Terminated-Pointers)
- [Sentinel-Terminated Arrays](#Sentinel-Terminated-Arrays)


---

### struct

**`structs.zig`:**

```zig
// Declare a struct.
// Zig gives no guarantees about the order of fields and the size of
// the struct but the fields are guaranteed to be ABI-aligned.
const Point = struct {
    x: f32,
    y: f32,
};

// Maybe we want to pass it to OpenGL so we want to be particular about
// how the bytes are arranged.
const Point2 = packed struct {
    x: f32,
    y: f32,
};


// Declare an instance of a struct.
const p = Point {
    .x = 0.12,
    .y = 0.34,
};

// Maybe we're not ready to fill out some of the fields.
var p2 = Point {
    .x = 0.12,
    .y = undefined,
};

// Structs can have methods
// Struct methods are not special, they are only namespaced
// functions that you can call with dot syntax.
const Vec3 = struct {
    x: f32,
    y: f32,
    z: f32,

    pub fn init(x: f32, y: f32, z: f32) Vec3 {
        return Vec3 {
            .x = x,
            .y = y,
            .z = z,
        };
    }

    pub fn dot(self: Vec3, other: Vec3) f32 {
        return self.x * other.x + self.y * other.y + self.z * other.z;
    }
};

const expect = @import("std").testing.expect;
test "dot product" {
    const v1 = Vec3.init(1.0, 0.0, 0.0);
    const v2 = Vec3.init(0.0, 1.0, 0.0);
    try expect(v1.dot(v2) == 0.0);

    // Other than being available to call with dot syntax, struct methods are
    // not special. You can reference them as any other declaration inside
    // the struct:
    try expect(Vec3.dot(v1, v2) == 0.0);
}

// Structs can have declarations.
// Structs can have 0 fields.
const Empty = struct {
    pub const PI = 3.14;
};
test "struct namespaced variable" {
    try expect(Empty.PI == 3.14);
    try expect(@sizeOf(Empty) == 0);

    // you can still instantiate an empty struct
    const does_nothing = Empty {};

    _ = does_nothing;
}

// struct field order is determined by the compiler for optimal performance.
// however, you can still calculate a struct base pointer given a field pointer:
fn setYBasedOnX(x: *f32, y: f32) void {
    const point = @fieldParentPtr(Point, "x", x);
    point.y = y;
}
test "field parent pointer" {
    var point = Point {
        .x = 0.1234,
        .y = 0.5678,
    };
    setYBasedOnX(&point.x, 0.9);
    try expect(point.y == 0.9);
}

// You can return a struct from a function. This is how we do generics
// in Zig:
fn LinkedList(comptime T: type) type {
    return struct {
        pub const Node = struct {
            prev: ?*Node,
            next: ?*Node,
            data: T,
        };

        first: ?*Node,
        last:  ?*Node,
        len:   usize,
    };
}

test "linked list" {
    // Functions called at compile-time are memoized. This means you can
    // do this:
    try expect(LinkedList(i32) == LinkedList(i32));

    var list = LinkedList(i32) {
        .first = null,
        .last = null,
        .len = 0,
    };
    try expect(list.len == 0);

    // Since types are first class values you can instantiate the type
    // by assigning it to a variable:
    const ListOfInts = LinkedList(i32);
    try expect(ListOfInts == LinkedList(i32));

    var node = ListOfInts.Node {
        .prev = null,
        .next = null,
        .data = 1234,
    };
    var list2 = LinkedList(i32) {
        .first = &node,
        .last = &node,
        .len = 1,
    };

    // When using a pointer to a struct, fields can be accessed directly,
    // without explicitly dereferencing the pointer.
    // So you can do
    try expect(list2.first.?.data == 1234);
    // instead of try expect(list2.first.?.*.data == 1234);
}

```

**Shell:**

```shell
$ zig test structs.zig
1/4 test.dot product... OK
2/4 test.struct namespaced variable... OK
3/4 test.field parent pointer... OK
4/4 test.linked list... OK
All 4 tests passed.

```

#### Default Field Values

Each struct field may have an expression indicating the default field value. Such expressions
are executed at [comptime](34-comptime.md#comptime), and allow the field to be omitted in a struct literal expression:

**`default_field_values.zig`:**

```zig
const Foo = struct {
    a: i32 = 1234,
    b: i32,
};

test "default struct initialization fields" {
    const x = Foo{
        .b = 5,
    };
    if (x.a + x.b != 1239) {
        @compileError("it's even comptime known!");
    }
}

```

**Shell:**

```shell
$ zig test default_field_values.zig
1/1 test.default struct initialization fields... OK
All 1 tests passed.

```

#### extern struct

An `extern struct` has in-memory layout guaranteed to match the
C ABI for the target.

This kind of struct should only be used for compatibility with the C ABI. Every other
use case should be solved with [packed struct](#packed-struct) or normal [struct](#struct).

See also:

- [extern union](#extern-union)
- [extern enum](#extern-enum)

#### packed struct

Unlike normal structs, `packed` structs have guaranteed in-memory layout:

- Fields remain in the order declared, least to most significant.
- There is no padding between fields.
- Zig supports arbitrary width [Integers](08-integers.md#Integers) and although normally, integers with fewer
  than 8 bits will still use 1 byte of memory, in packed structs, they use
  exactly their bit width.
- `bool` fields use exactly 1 bit.
- An [enum](16-enum.md#enum) field uses exactly the bit width of its integer tag type.
- A [packed union](#packed-union) field uses exactly the bit width of the union field with
  the largest bit width.
- Non-ABI-aligned fields are packed into the smallest possible
  ABI-aligned integers in accordance with the target endianness.

This means that a `packed struct` can participate
in a [@bitCast](#bitCast) or a [@ptrCast](#ptrCast) to reinterpret memory.
This even works at [comptime](34-comptime.md#comptime):

**`packed_structs.zig`:**

```zig
const std = @import("std");
const native_endian = @import("builtin").target.cpu.arch.endian();
const expect = std.testing.expect;

const Full = packed struct {
    number: u16,
};
const Divided = packed struct {
    half1: u8,
    quarter3: u4,
    quarter4: u4,
};

test "@bitCast between packed structs" {
    try doTheTest();
    comptime try doTheTest();
}

fn doTheTest() !void {
    try expect(@sizeOf(Full) == 2);
    try expect(@sizeOf(Divided) == 2);
    var full = Full{ .number = 0x1234 };
    var divided = @bitCast(Divided, full);
    try expect(divided.half1 == 0x34);
    try expect(divided.quarter3 == 0x2);
    try expect(divided.quarter4 == 0x1);

    var ordered = @bitCast([2]u8, full);
    switch (native_endian) {
        .Big => {
            try expect(ordered[0] == 0x12);
            try expect(ordered[1] == 0x34);
        },
        .Little => {
            try expect(ordered[0] == 0x34);
            try expect(ordered[1] == 0x12);
        },
    }
}

```

**Shell:**

```shell
$ zig test packed_structs.zig
1/1 test.@bitCast between packed structs... OK
All 1 tests passed.

```

Zig allows the address to be taken of a non-byte-aligned field:

**`pointer_to_non-byte_aligned_field.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const BitField = packed struct {
    a: u3,
    b: u3,
    c: u2,
};

var foo = BitField{
    .a = 1,
    .b = 2,
    .c = 3,
};

test "pointer to non-byte-aligned field" {
    const ptr = &foo.b;
    try expect(ptr.* == 2);
}

```

**Shell:**

```shell
$ zig test pointer_to_non-byte_aligned_field.zig
1/1 test.pointer to non-byte-aligned field... OK
All 1 tests passed.

```

However, the pointer to a non-byte-aligned field has special properties and cannot
be passed when a normal pointer is expected:

**`test.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const BitField = packed struct {
    a: u3,
    b: u3,
    c: u2,
};

var bit_field = BitField{
    .a = 1,
    .b = 2,
    .c = 3,
};

test "pointer to non-bit-aligned field" {
    try expect(bar(&bit_field.b) == 2);
}

fn bar(x: *const u3) u3 {
    return x.*;
}

```

**Shell:**

```shell
$ zig test test.zig
docgen_tmp/test.zig:17:20: error: expected type '*const u3', found '*align(0:3:1) u3'
    try expect(bar(&bit_field.b) == 2);
                   ^~~~~~~~~~~~
docgen_tmp/test.zig:17:20: note: pointer host size '1' cannot cast into pointer host size '0'
docgen_tmp/test.zig:17:20: note: pointer bit offset '3' cannot cast into pointer bit offset '0'
docgen_tmp/test.zig:20:11: note: parameter type declared here
fn bar(x: *const u3) u3 {
          ^~~~~~~~~


```

In this case, the function `bar` cannot be called because the pointer
to the non-ABI-aligned field mentions the bit offset, but the function expects an ABI-aligned pointer.

Pointers to non-ABI-aligned fields share the same address as the other fields within their host integer:

**`packed_struct_field_addrs.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const BitField = packed struct {
    a: u3,
    b: u3,
    c: u2,
};

var bit_field = BitField{
    .a = 1,
    .b = 2,
    .c = 3,
};

test "pointers of sub-byte-aligned fields share addresses" {
    try expect(@ptrToInt(&bit_field.a) == @ptrToInt(&bit_field.b));
    try expect(@ptrToInt(&bit_field.a) == @ptrToInt(&bit_field.c));
}

```

**Shell:**

```shell
$ zig test packed_struct_field_addrs.zig
1/1 test.pointers of sub-byte-aligned fields share addresses... OK
All 1 tests passed.

```

This can be observed with [@bitOffsetOf](#bitOffsetOf) and [offsetOf](#offsetOf):

**`test_bitOffsetOf_offsetOf.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const BitField = packed struct {
    a: u3,
    b: u3,
    c: u2,
};

test "pointer to non-bit-aligned field" {
    comptime {
        try expect(@bitOffsetOf(BitField, "a") == 0);
        try expect(@bitOffsetOf(BitField, "b") == 3);
        try expect(@bitOffsetOf(BitField, "c") == 6);

        try expect(@offsetOf(BitField, "a") == 0);
        try expect(@offsetOf(BitField, "b") == 0);
        try expect(@offsetOf(BitField, "c") == 0);
    }
}

```

**Shell:**

```shell
$ zig test test_bitOffsetOf_offsetOf.zig
1/1 test.pointer to non-bit-aligned field... OK
All 1 tests passed.

```

Packed structs have the same alignment as their backing integer, however, overaligned
pointers to packed structs can override this:

**`overaligned_packed_struct.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const S = packed struct {
    a: u32,
    b: u32,
};
test "overaligned pointer to packed struct" {
    var foo: S align(4) = .{ .a = 1, .b = 2 };
    const ptr: *align(4) S = &foo;
    const ptr_to_b: *u32 = &ptr.b;
    try expect(ptr_to_b.* == 2);
}

```

**Shell:**

```shell
$ zig test overaligned_packed_struct.zig
1/1 test.overaligned pointer to packed struct... OK
All 1 tests passed.

```

It's also possible to set alignment of struct fields:

**`test_aligned_struct_fields.zig`:**

```zig
const std = @import("std");
const expectEqual = std.testing.expectEqual;

test "aligned struct fields" {
    const S = struct {
        a: u32 align(2),
        b: u32 align(64),
    };
    var foo = S{ .a = 1, .b = 2 };

    try expectEqual(64, @alignOf(S));
    try expectEqual(*align(2) u32, @TypeOf(&foo.a));
    try expectEqual(*align(64) u32, @TypeOf(&foo.b));
}

```

**Shell:**

```shell
$ zig test test_aligned_struct_fields.zig
1/1 test.aligned struct fields... OK
All 1 tests passed.

```

Using packed structs with [volatile](#volatile) is problematic, and may be a compile error in the future.
For details on this subscribe to
[this issue](https://github.com/ziglang/zig/issues/1761).
TODO update these docs with a recommendation on how to use packed structs with MMIO
(the use case for volatile packed structs) once this issue is resolved.
Don't worry, there will be a good solution for this use case in zig.

#### Struct Naming

Since all structs are anonymous, Zig infers the type name based on a few rules.

- If the struct is in the initialization expression of a variable, it gets named after
  that variable.
- If the struct is in the `return` expression, it gets named after
  the function it is returning from, with the parameter values serialized.
- Otherwise, the struct gets a name such as `(anonymous struct at file.zig:7:38)`.
- If the struct is declared inside another struct, it gets named after both the parent
  struct and the name inferred by the previous rules, separated by a dot.

**`struct_name.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    const Foo = struct {};
    std.debug.print("variable: {s}\n", .{@typeName(Foo)});
    std.debug.print("anonymous: {s}\n", .{@typeName(struct {})});
    std.debug.print("function: {s}\n", .{@typeName(List(i32))});
}

fn List(comptime T: type) type {
    return struct {
        x: T,
    };
}

```

**Shell:**

```shell
$ zig build-exe struct_name.zig

$ ./struct_name
variable: struct_name.main.Foo
anonymous: struct_name.main__struct_3896
function: struct_name.List(i32)

```

#### Anonymous Struct Literals

Zig allows omitting the struct type of a literal. When the result is [coerced](#Type-Coercion),
the struct literal will directly instantiate the result location, with no copy:

**`struct_result.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Point = struct {x: i32, y: i32};

test "anonymous struct literal" {
    var pt: Point = .{
        .x = 13,
        .y = 67,
    };
    try expect(pt.x == 13);
    try expect(pt.y == 67);
}

```

**Shell:**

```shell
$ zig test struct_result.zig
1/1 test.anonymous struct literal... OK
All 1 tests passed.

```

The struct type can be inferred. Here the result location does not include a type, and
so Zig infers the type:

**`struct_anon.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "fully anonymous struct" {
    try dump(.{
        .int = @as(u32, 1234),
        .float = @as(f64, 12.34),
        .b = true,
        .s = "hi",
    });
}

fn dump(args: anytype) !void {
    try expect(args.int == 1234);
    try expect(args.float == 12.34);
    try expect(args.b);
    try expect(args.s[0] == 'h');
    try expect(args.s[1] == 'i');
}

```

**Shell:**

```shell
$ zig test struct_anon.zig
1/1 test.fully anonymous struct... OK
All 1 tests passed.

```

Anonymous structs can be created without specifying field names, and are referred to as "tuples".

The fields are implicitly named using numbers starting from 0. Because their names are integers,
the `@"0"` syntax must be used to access them. Names inside `@""` are always recognised as [identifiers](#Identifiers).

Like arrays, tuples have a .len field, can be indexed and work with the ++ and ** operators. They can also be iterated over with [inline for](#inline-for).

**`tuple.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "tuple" {
    const values = .{
        @as(u32, 1234),
        @as(f64, 12.34),
        true,
        "hi",
    } ++ .{false} ** 2;
    try expect(values[0] == 1234);
    try expect(values[4] == false);
    inline for (values) |v, i| {
        if (i != 2) continue;
        try expect(v);
    }
    try expect(values.len == 6);
    try expect(values.@"3"[0] == 'h');
}

```

**Shell:**

```shell
$ zig test tuple.zig
1/1 test.tuple... OK
All 1 tests passed.

```

See also:

- [comptime](34-comptime.md#comptime)
- [@fieldParentPtr](#fieldParentPtr)


---

### enum

**`enums.zig`:**

```zig
const expect = @import("std").testing.expect;
const mem = @import("std").mem;

// Declare an enum.
const Type = enum {
    ok,
    not_ok,
};

// Declare a specific instance of the enum variant.
const c = Type.ok;

// If you want access to the ordinal value of an enum, you
// can specify the tag type.
const Value = enum(u2) {
    zero,
    one,
    two,
};

// Now you can cast between u2 and Value.
// The ordinal value starts from 0, counting up for each member.
test "enum ordinal value" {
    try expect(@enumToInt(Value.zero) == 0);
    try expect(@enumToInt(Value.one) == 1);
    try expect(@enumToInt(Value.two) == 2);
}

// You can override the ordinal value for an enum.
const Value2 = enum(u32) {
    hundred = 100,
    thousand = 1000,
    million = 1000000,
};
test "set enum ordinal value" {
    try expect(@enumToInt(Value2.hundred) == 100);
    try expect(@enumToInt(Value2.thousand) == 1000);
    try expect(@enumToInt(Value2.million) == 1000000);
}

// Enums can have methods, the same as structs and unions.
// Enum methods are not special, they are only namespaced
// functions that you can call with dot syntax.
const Suit = enum {
    clubs,
    spades,
    diamonds,
    hearts,

    pub fn isClubs(self: Suit) bool {
        return self == Suit.clubs;
    }
};
test "enum method" {
    const p = Suit.spades;
    try expect(!p.isClubs());
}

// An enum variant of different types can be switched upon.
const Foo = enum {
    string,
    number,
    none,
};
test "enum variant switch" {
    const p = Foo.number;
    const what_is_it = switch (p) {
        Foo.string => "this is a string",
        Foo.number => "this is a number",
        Foo.none => "this is a none",
    };
    try expect(mem.eql(u8, what_is_it, "this is a number"));
}

// @typeInfo can be used to access the integer tag type of an enum.
const Small = enum {
    one,
    two,
    three,
    four,
};
test "std.meta.Tag" {
    try expect(@typeInfo(Small).Enum.tag_type == u2);
}

// @typeInfo tells us the field count and the fields names:
test "@typeInfo" {
    try expect(@typeInfo(Small).Enum.fields.len == 4);
    try expect(mem.eql(u8, @typeInfo(Small).Enum.fields[1].name, "two"));
}

// @tagName gives a [:0]const u8 representation of an enum value:
test "@tagName" {
    try expect(mem.eql(u8, @tagName(Small.three), "three"));
}

```

**Shell:**

```shell
$ zig test enums.zig
1/7 test.enum ordinal value... OK
2/7 test.set enum ordinal value... OK
3/7 test.enum method... OK
4/7 test.enum variant switch... OK
5/7 test.std.meta.Tag... OK
6/7 test.@typeInfo... OK
7/7 test.@tagName... OK
All 7 tests passed.

```

See also:

- [@typeInfo](#typeInfo)
- [@tagName](#tagName)
- [@sizeOf](#sizeOf)

#### extern enum

By default, enums are not guaranteed to be compatible with the C ABI:

**`test.zig`:**

```zig
const Foo = enum { a, b, c };
export fn entry(foo: Foo) void { _ = foo; }

```

**Shell:**

```shell
$ zig build-obj test.zig
docgen_tmp/test.zig:2:17: error: parameter of type 'test.Foo' not allowed in function with calling convention 'C'
export fn entry(foo: Foo) void { _ = foo; }
                ^~~~~~~~
docgen_tmp/test.zig:2:17: note: enum tag type 'u2' is not extern compatible
docgen_tmp/test.zig:2:17: note: only integers with power of two bits are extern compatible
docgen_tmp/test.zig:1:13: note: enum declared here
const Foo = enum { a, b, c };
            ^~~~~~~~~~~~~~~~


```

For a C-ABI-compatible enum, provide an explicit tag type to
the enum:

**`test.zig`:**

```zig
const Foo = enum(c_int) { a, b, c };
export fn entry(foo: Foo) void { _ = foo; }

```

**Shell:**

```shell
$ zig build-obj test.zig

```

#### Enum Literals

Enum literals allow specifying the name of an enum field without specifying the enum type:

**`test_enum_literals.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Color = enum {
    auto,
    off,
    on,
};

test "enum literals" {
    const color1: Color = .auto;
    const color2 = Color.auto;
    try expect(color1 == color2);
}

test "switch using enum literals" {
    const color = Color.on;
    const result = switch (color) {
        .auto => false,
        .on => true,
        .off => false,
    };
    try expect(result);
}

```

**Shell:**

```shell
$ zig test test_enum_literals.zig
1/2 test.enum literals... OK
2/2 test.switch using enum literals... OK
All 2 tests passed.

```

#### Non-exhaustive enum

A Non-exhaustive enum can be created by adding a trailing '_' field.
It must specify a tag type and cannot consume every enumeration value.

[@intToEnum](#intToEnum) on a non-exhaustive enum involves the safety semantics
of [@intCast](#intCast) to the integer tag type, but beyond that always results in
a well-defined enum value.

A switch on a non-exhaustive enum can include a '_' prong as an alternative to an `else` prong
with the difference being that it makes it a compile error if all the known tag names are not handled by the switch.

**`test_switch_non-exhaustive.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Number = enum(u8) {
    one,
    two,
    three,
    _,
};

test "switch on non-exhaustive enum" {
    const number = Number.one;
    const result = switch (number) {
        .one => true,
        .two,
        .three => false,
        _ => false,
    };
    try expect(result);
    const is_one = switch (number) {
        .one => true,
        else => false,
    };
    try expect(is_one);
}

```

**Shell:**

```shell
$ zig test test_switch_non-exhaustive.zig
1/1 test.switch on non-exhaustive enum... OK
All 1 tests passed.

```


---

### union

A bare `union` defines a set of possible types that a value
can be as a list of fields. Only one field can be active at a time.
The in-memory representation of bare unions is not guaranteed.
Bare unions cannot be used to reinterpret memory. For that, use [@ptrCast](#ptrCast),
or use an [extern union](#extern-union) or a [packed union](#packed-union) which have
guaranteed in-memory layout.
[Accessing the non-active field](#Wrong-Union-Field-Access) is
safety-checked [Undefined Behavior](41-undefined-behavior.md#Undefined-Behavior):

**`test.zig`:**

```zig
const Payload = union {
    int: i64,
    float: f64,
    boolean: bool,
};
test "simple union" {
    var payload = Payload{ .int = 1234 };
    payload.float = 12.34;
}

```

**Shell:**

```shell
$ zig test test.zig
1/1 test.simple union... thread 3569067 panic: access of inactive union field
docgen_tmp/test.zig:8:12: 0x2115a1 in test.simple union (test)
    payload.float = 12.34;
           ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/test_runner.zig:63:28: 0x212d43 in main (test)
        } else test_fn.func();
                           ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/std/start.zig:604:22: 0x211ecc in posixCallMainAndExit (test)
            root.main();
                     ^
/home/ci/release-0.10.1/out/zig-x86_64-linux-musl-baseline/lib/zig/std/start.zig:376:5: 0x2119d1 in _start (test)
    @call(.{ .modifier = .never_inline }, posixCallMainAndExit, .{});
    ^
error: the following test command crashed:
/home/ci/release-0.10.1/out/zig-local-cache/o/886dbde2c2a21074c6c6d3ff9b83336b/test

```

You can activate another field by assigning the entire union:

**`test_simple_union.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Payload = union {
    int: i64,
    float: f64,
    boolean: bool,
};
test "simple union" {
    var payload = Payload{ .int = 1234 };
    try expect(payload.int == 1234);
    payload = Payload{ .float = 12.34 };
    try expect(payload.float == 12.34);
}

```

**Shell:**

```shell
$ zig test test_simple_union.zig
1/1 test.simple union... OK
All 1 tests passed.

```

In order to use [switch](20-switch.md#switch) with a union, it must be a [Tagged union](#Tagged-union).

To initialize a union when the tag is a [comptime](34-comptime.md#comptime)-known name, see [@unionInit](#unionInit).

#### Tagged union

Unions can be declared with an enum tag type.
This turns the union into a *tagged* union, which makes it eligible
to use with [switch](20-switch.md#switch) expressions.
Tagged unions coerce to their tag type: [Type Coercion: unions and enums](#Type-Coercion-unions-and-enums).

**`test_switch_tagged_union.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const ComplexTypeTag = enum {
    ok,
    not_ok,
};
const ComplexType = union(ComplexTypeTag) {
    ok: u8,
    not_ok: void,
};

test "switch on tagged union" {
    const c = ComplexType{ .ok = 42 };
    try expect(@as(ComplexTypeTag, c) == ComplexTypeTag.ok);

    switch (c) {
        ComplexTypeTag.ok => |value| try expect(value == 42),
        ComplexTypeTag.not_ok => unreachable,
    }
}

test "get tag type" {
    try expect(std.meta.Tag(ComplexType) == ComplexTypeTag);
}

test "coerce to enum" {
    const c1 = ComplexType{ .ok = 42 };
    const c2 = ComplexType.not_ok;

    try expect(c1 == .ok);
    try expect(c2 == .not_ok);
}

```

**Shell:**

```shell
$ zig test test_switch_tagged_union.zig
1/3 test.switch on tagged union... OK
2/3 test.get tag type... OK
3/3 test.coerce to enum... OK
All 3 tests passed.

```

In order to modify the payload of a tagged union in a switch expression,
place a `*` before the variable name to make it a pointer:

**`test_switch_modify_tagged_union.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const ComplexTypeTag = enum {
    ok,
    not_ok,
};
const ComplexType = union(ComplexTypeTag) {
    ok: u8,
    not_ok: void,
};

test "modify tagged union in switch" {
    var c = ComplexType{ .ok = 42 };
    try expect(@as(ComplexTypeTag, c) == ComplexTypeTag.ok);

    switch (c) {
        ComplexTypeTag.ok => |*value| value.* += 1,
        ComplexTypeTag.not_ok => unreachable,
    }

    try expect(c.ok == 43);
}

```

**Shell:**

```shell
$ zig test test_switch_modify_tagged_union.zig
1/1 test.modify tagged union in switch... OK
All 1 tests passed.

```

Unions can be made to infer the enum tag type.
Further, unions can have methods just like structs and enums.

**`test_union_method.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Variant = union(enum) {
    int: i32,
    boolean: bool,

    // void can be omitted when inferring enum tag type.
    none,

    fn truthy(self: Variant) bool {
        return switch (self) {
            Variant.int => |x_int| x_int != 0,
            Variant.boolean => |x_bool| x_bool,
            Variant.none => false,
        };
    }
};

test "union method" {
    var v1 = Variant{ .int = 1 };
    var v2 = Variant{ .boolean = false };

    try expect(v1.truthy());
    try expect(!v2.truthy());
}

```

**Shell:**

```shell
$ zig test test_union_method.zig
1/1 test.union method... OK
All 1 tests passed.

```

[@tagName](#tagName) can be used to return a [comptime](34-comptime.md#comptime)
`[:0]const u8` value representing the field name:

**`test_tagName.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Small2 = union(enum) {
    a: i32,
    b: bool,
    c: u8,
};
test "@tagName" {
    try expect(std.mem.eql(u8, @tagName(Small2.a), "a"));
}

```

**Shell:**

```shell
$ zig test test_tagName.zig
1/1 test.@tagName... OK
All 1 tests passed.

```

#### extern union

An `extern union` has memory layout guaranteed to be compatible with
the target C ABI.

See also:

- [extern struct](#extern-struct)

#### packed union

A `packed union` has well-defined in-memory layout and is eligible
to be in a [packed struct](#packed-struct).

#### Anonymous Union Literals

[Anonymous Struct Literals](#Anonymous-Struct-Literals) syntax can be used to initialize unions without specifying
the type:

**`anon_union.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Number = union {
    int: i32,
    float: f64,
};

test "anonymous union literal syntax" {
    var i: Number = .{.int = 42};
    var f = makeNumber();
    try expect(i.int == 42);
    try expect(f.float == 12.34);
}

fn makeNumber() Number {
    return .{.float = 12.34};
}

```

**Shell:**

```shell
$ zig test anon_union.zig
1/1 test.anonymous union literal syntax... OK
All 1 tests passed.

```


---

### opaque

`opaque {}` declares a new type with an unknown (but non-zero) size and alignment.
It can contain declarations the same as [structs](15-struct.md#struct), [unions](17-union.md#union),
and [enums](16-enum.md#enum).

This is typically used for type safety when interacting with C code that does not expose struct details.
Example:

**`test.zig`:**

```zig
const Derp = opaque {};
const Wat = opaque {};

extern fn bar(d: *Derp) void;
fn foo(w: *Wat) callconv(.C) void {
    bar(w);
}

test "call foo" {
    foo(undefined);
}

```

**Shell:**

```shell
$ zig test test.zig
docgen_tmp/test.zig:6:9: error: expected type '*test.Derp', found '*test.Wat'
    bar(w);
        ^
docgen_tmp/test.zig:6:9: note: pointer type child 'test.Wat' cannot cast into pointer type child 'test.Derp'
docgen_tmp/test.zig:2:13: note: opaque declared here
const Wat = opaque {};
            ^~~~~~~~~
docgen_tmp/test.zig:1:14: note: opaque declared here
const Derp = opaque {};
             ^~~~~~~~~
docgen_tmp/test.zig:4:18: note: parameter type declared here
extern fn bar(d: *Derp) void;
                 ^~~~~
referenced by:
    test.call foo: docgen_tmp/test.zig:10:5
    remaining reference traces hidden; use '-freference-trace' to see all reference traces


```


---
