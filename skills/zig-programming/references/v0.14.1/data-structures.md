# Data Structures

*How to organize and structure data in Zig*


---

### Arrays

**`test_arrays.zig`:**

```zig
const expect = @import("std").testing.expect;
const assert = @import("std").debug.assert;
const mem = @import("std").mem;

// array literal
const message = [_]u8{ 'h', 'e', 'l', 'l', 'o' };

// alternative initialization using result location
const alt_message: [5]u8 = .{ 'h', 'e', 'l', 'l', 'o' };

comptime {
    assert(mem.eql(u8, &message, &alt_message));
}

// get the size of an array
comptime {
    assert(message.len == 5);
}

// A string literal is a single-item pointer to an array.
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
    for (&some_integers, 0..) |*item, i| {
        item.* = @intCast(i);
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
    for (&initial_value, 0..) |*pt, i| {
        pt.* = Point{
            .x = @intCast(i),
            .y = @intCast(i * 2),
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
$ zig test test_arrays.zig
1/4 test_arrays.test.iterate over an array...OK
2/4 test_arrays.test.modify an array...OK
3/4 test_arrays.test.compile-time array initialization...OK
4/4 test_arrays.test.array initialization with function calls...OK
All 4 tests passed.

```

See also:

- [for](22-for.md#for)
- [Slices](14-slices.md#Slices)

#### Multidimensional Arrays

Multidimensional arrays can be created by nesting arrays:

**`test_multidimensional_arrays.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

const mat4x5 = [4][5]f32{
    [_]f32{ 1.0, 0.0, 0.0, 0.0, 0.0 },
    [_]f32{ 0.0, 1.0, 0.0, 1.0, 0.0 },
    [_]f32{ 0.0, 0.0, 1.0, 0.0, 0.0 },
    [_]f32{ 0.0, 0.0, 0.0, 1.0, 9.9 },
};
test "multidimensional arrays" {
    // mat4x5 itself is a one-dimensional array of arrays.
    try expectEqual(mat4x5[1], [_]f32{ 0.0, 1.0, 0.0, 1.0, 0.0 });

    // Access the 2D array by indexing the outer array, and then the inner array.
    try expect(mat4x5[3][4] == 9.9);

    // Here we iterate with for loops.
    for (mat4x5, 0..) |row, row_index| {
        for (row, 0..) |cell, column_index| {
            if (row_index == column_index) {
                try expect(cell == 1.0);
            }
        }
    }

    // Initialize a multidimensional array to zeros.
    const all_zero: [4][5]f32 = .{.{0} ** 5} ** 4;
    try expect(all_zero[0][0] == 0);
}

```

**Shell:**

```shell
$ zig test test_multidimensional_arrays.zig
1/1 test_multidimensional_arrays.test.multidimensional arrays...OK
All 1 tests passed.

```

#### Sentinel-Terminated Arrays

The syntax `[N:x]T` describes an array which has a sentinel element of value `x` at the
index corresponding to the length `N`.

**`test_null_terminated_array.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "0-terminated sentinel array" {
    const array = [_:0]u8{ 1, 2, 3, 4 };

    try expect(@TypeOf(array) == [4:0]u8);
    try expect(array.len == 4);
    try expect(array[4] == 0);
}

test "extra 0s in 0-terminated sentinel array" {
    // The sentinel value may appear earlier, but does not influence the compile-time 'len'.
    const array = [_:0]u8{ 1, 0, 0, 4 };

    try expect(@TypeOf(array) == [4:0]u8);
    try expect(array.len == 4);
    try expect(array[4] == 0);
}

```

**Shell:**

```shell
$ zig test test_null_terminated_array.zig
1/2 test_null_terminated_array.test.0-terminated sentinel array...OK
2/2 test_null_terminated_array.test.extra 0s in 0-terminated sentinel array...OK
All 2 tests passed.

```

See also:

- [Sentinel-Terminated Pointers](#Sentinel-Terminated-Pointers)
- [Sentinel-Terminated Slices](#Sentinel-Terminated-Slices)

#### Destructuring Arrays

Arrays can be destructured:

**`destructuring_arrays.zig`:**

```zig
const print = @import("std").debug.print;

fn swizzleRgbaToBgra(rgba: [4]u8) [4]u8 {
    // readable swizzling by destructuring
    const r, const g, const b, const a = rgba;
    return .{ b, g, r, a };
}

pub fn main() void {
    const pos = [_]i32{ 1, 2 };
    const x, const y = pos;
    print("x = {}, y = {}\n", .{x, y});

    const orange: [4]u8 = .{ 255, 165, 0, 255 };
    print("{any}\n", .{swizzleRgbaToBgra(orange)});
}

```

**Shell:**

```shell
$ zig build-exe destructuring_arrays.zig
$ ./destructuring_arrays
x = 1, y = 2
{ 0, 165, 255, 255 }

```

See also:

- [Destructuring](#Destructuring)
- [Destructuring Tuples](#Destructuring-Tuples)
- [Destructuring Vectors](#Destructuring-Vectors)


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
arrays with comptime-known length.

For rearranging elements within and between vectors, Zig provides the [@shuffle](#shuffle) and [@select](#select) functions.

Operations on vectors shorter than the target machine's native SIMD size will typically compile to single SIMD
instructions, while vectors longer than the target machine's native SIMD size will compile to multiple SIMD
instructions. If a given operation doesn't have SIMD support on the target architecture, the compiler will default
to operating on each vector element one at a time. Zig supports any comptime-known vector length up to 2^32-1,
although small powers of two (2-64) are most typical. Note that excessively long vector lengths (e.g. 2^20) may
result in compiler crashes on current versions of Zig.

**`test_vector.zig`:**

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
    const arr1: [4]f32 = [_]f32{ 1.1, 3.2, 4.5, 5.6 };
    const vec: @Vector(4, f32) = arr1;
    const arr2: [4]f32 = vec;
    try expectEqual(arr1, arr2);

    // You can also assign from a slice with comptime-known length to a vector using .*
    const vec2: @Vector(2, f32) = arr1[1..3].*;

    const slice: []const f32 = &arr1;
    var offset: u32 = 1; // var to make it runtime-known
    _ = &offset; // suppress 'var is never mutated' error
    // To extract a comptime-known length from a runtime-known offset,
    // first extract a new slice from the starting offset, then an array of
    // comptime-known length
    const vec3: @Vector(2, f32) = slice[offset..][0..2].*;
    try expectEqual(slice[offset], vec2[0]);
    try expectEqual(slice[offset + 1], vec2[1]);
    try expectEqual(vec2, vec3);
}

```

**Shell:**

```shell
$ zig test test_vector.zig
1/2 test_vector.test.Basic vector usage...OK
2/2 test_vector.test.Conversion between vectors, arrays, and slices...OK
All 2 tests passed.

```

TODO talk about C ABI interop  
TODO consider suggesting std.MultiArrayList

See also:

- [@splat](#splat)
- [@shuffle](#shuffle)
- [@select](#select)
- [@reduce](#reduce)

#### Destructuring Vectors

Vectors can be destructured:

**`destructuring_vectors.zig`:**

```zig
const print = @import("std").debug.print;

// emulate punpckldq
pub fn unpack(x: @Vector(4, f32), y: @Vector(4, f32)) @Vector(4, f32) {
    const a, const c, _, _ = x;
    const b, const d, _, _ = y;
    return .{ a, b, c, d };
}

pub fn main() void {
    const x: @Vector(4, f32) = .{ 1.0, 2.0, 3.0, 4.0 };
    const y: @Vector(4, f32) = .{ 5.0, 6.0, 7.0, 8.0 };
    print("{}", .{unpack(x, y)});
}

```

**Shell:**

```shell
$ zig build-exe destructuring_vectors.zig
$ ./destructuring_vectors
{ 1e0, 5e0, 2e0, 6e0 }

```

See also:

- [Destructuring](#Destructuring)
- [Destructuring Tuples](#Destructuring-Tuples)
- [Destructuring Arrays](#Destructuring-Arrays)


---

### Pointers

Zig has two kinds of pointers: single-item and many-item.

- `*T` - single-item pointer to exactly one item.
  - Supports deref syntax: `ptr.*`
  - Supports slice syntax: `ptr[0..1]`
  - Supports pointer subtraction: `ptr - ptr`
- `[*]T` - many-item pointer to unknown number of items.
  - Supports index syntax: `ptr[i]`
  - Supports slice syntax: `ptr[start..end]` and `ptr[start..]`
  - Supports pointer-integer arithmetic: `ptr + int`, `ptr - int`
  - Supports pointer subtraction: `ptr - ptr``T` must have a known size, which means that it cannot be
  `anyopaque` or any other [opaque type](18-opaque.md#opaque).

These types are closely related to [Arrays](11-arrays.md#Arrays) and [Slices](14-slices.md#Slices):

- `*[N]T` - pointer to N items, same as single-item pointer to an array.
  - Supports index syntax: `array_ptr[i]`
  - Supports slice syntax: `array_ptr[start..end]`
  - Supports len property: `array_ptr.len`
  - Supports pointer subtraction: `array_ptr - array_ptr`

- `[]T` - is a slice (a fat pointer, which contains a pointer of type `[*]T` and a length).
  - Supports index syntax: `slice[i]`
  - Supports slice syntax: `slice[start..end]`
  - Supports len property: `slice.len`

Use `&x` to obtain a single-item pointer:

**`test_single_item_pointer.zig`:**

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

test "slice syntax" {
    // Get a pointer to a variable:
    var x: i32 = 1234;
    const x_ptr = &x;

    // Convert to array pointer using slice syntax:
    const x_array_ptr = x_ptr[0..1];
    try expect(@TypeOf(x_array_ptr) == *[1]i32);

    // Coerce to many-item pointer:
    const x_many_ptr: [*]i32 = x_array_ptr;
    try expect(x_many_ptr[0] == 1234);
}

```

**Shell:**

```shell
$ zig test test_single_item_pointer.zig
1/3 test_single_item_pointer.test.address of syntax...OK
2/3 test_single_item_pointer.test.pointer array access...OK
3/3 test_single_item_pointer.test.slice syntax...OK
All 3 tests passed.

```

Zig supports pointer arithmetic. It's better to assign the pointer to `[*]T` and increment that variable. For example, directly incrementing the pointer from a slice will corrupt it.

**`test_pointer_arithmetic.zig`:**

```zig
const expect = @import("std").testing.expect;

test "pointer arithmetic with many-item pointer" {
    const array = [_]i32{ 1, 2, 3, 4 };
    var ptr: [*]const i32 = &array;

    try expect(ptr[0] == 1);
    ptr += 1;
    try expect(ptr[0] == 2);

    // slicing a many-item pointer without an end is equivalent to
    // pointer arithmetic: `ptr[start..] == ptr + start`
    try expect(ptr[1..] == ptr + 1);

    // subtraction between any two pointers except slices based on element size is supported
    try expect(&ptr[1] - &ptr[0] == 1);
}

test "pointer arithmetic with slices" {
    var array = [_]i32{ 1, 2, 3, 4 };
    var length: usize = 0; // var to make it runtime-known
    _ = &length; // suppress 'var is never mutated' error
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
$ zig test test_pointer_arithmetic.zig
1/2 test_pointer_arithmetic.test.pointer arithmetic with many-item pointer...OK
2/2 test_pointer_arithmetic.test.pointer arithmetic with slices...OK
All 2 tests passed.

```

In Zig, we generally prefer [Slices](14-slices.md#Slices) rather than [Sentinel-Terminated Pointers](#Sentinel-Terminated-Pointers).
You can turn an array or pointer into a slice using slice syntax.

Slices have bounds checking and are therefore protected
against this kind of Illegal Behavior. This is one reason
we prefer slices to pointers.

**`test_slice_bounds.zig`:**

```zig
const expect = @import("std").testing.expect;

test "pointer slicing" {
    var array = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    var start: usize = 2; // var to make it runtime-known
    _ = &start; // suppress 'var is never mutated' error
    const slice = array[start..4];
    try expect(slice.len == 2);

    try expect(array[3] == 4);
    slice[1] += 1;
    try expect(array[3] == 5);
}

```

**Shell:**

```shell
$ zig test test_slice_bounds.zig
1/1 test_slice_bounds.test.pointer slicing...OK
All 1 tests passed.

```

Pointers work at compile-time too, as long as the code does not depend on
an undefined memory layout:

**`test_comptime_pointers.zig`:**

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
$ zig test test_comptime_pointers.zig
1/1 test_comptime_pointers.test.comptime pointers...OK
All 1 tests passed.

```

To convert an integer address into a pointer, use `@ptrFromInt`.
To convert a pointer to an integer, use `@intFromPtr`:

**`test_integer_pointer_conversion.zig`:**

```zig
const expect = @import("std").testing.expect;

test "@intFromPtr and @ptrFromInt" {
    const ptr: *i32 = @ptrFromInt(0xdeadbee0);
    const addr = @intFromPtr(ptr);
    try expect(@TypeOf(addr) == usize);
    try expect(addr == 0xdeadbee0);
}

```

**Shell:**

```shell
$ zig test test_integer_pointer_conversion.zig
1/1 test_integer_pointer_conversion.test.@intFromPtr and @ptrFromInt...OK
All 1 tests passed.

```

Zig is able to preserve memory addresses in comptime code, as long as
the pointer is never dereferenced:

**`test_comptime_pointer_conversion.zig`:**

```zig
const expect = @import("std").testing.expect;

test "comptime @ptrFromInt" {
    comptime {
        // Zig is able to do this at compile-time, as long as
        // ptr is never dereferenced.
        const ptr: *i32 = @ptrFromInt(0xdeadbee0);
        const addr = @intFromPtr(ptr);
        try expect(@TypeOf(addr) == usize);
        try expect(addr == 0xdeadbee0);
    }
}

```

**Shell:**

```shell
$ zig test test_comptime_pointer_conversion.zig
1/1 test_comptime_pointer_conversion.test.comptime @ptrFromInt...OK
All 1 tests passed.

```

[@ptrCast](#ptrCast) converts a pointer's element type to another. This
creates a new pointer that can cause undetectable Illegal Behavior
depending on the loads and stores that pass through it. Generally, other
kinds of type conversions are preferable to
`@ptrCast` if possible.

**`test_pointer_casting.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "pointer casting" {
    const bytes align(@alignOf(u32)) = [_]u8{ 0x12, 0x12, 0x12, 0x12 };
    const u32_ptr: *const u32 = @ptrCast(&bytes);
    try expect(u32_ptr.* == 0x12121212);

    // Even this example is contrived - there are better ways to do the above than
    // pointer casting. For example, using a slice narrowing cast:
    const u32_value = std.mem.bytesAsSlice(u32, bytes[0..])[0];
    try expect(u32_value == 0x12121212);

    // And even another way, the most straightforward way to do it:
    try expect(@as(u32, @bitCast(bytes)) == 0x12121212);
}

test "pointer child type" {
    // pointer types have a `child` field which tells you the type they point to.
    try expect(@typeInfo(*u32).pointer.child == u32);
}

```

**Shell:**

```shell
$ zig test test_pointer_casting.zig
1/2 test_pointer_casting.test.pointer casting...OK
2/2 test_pointer_casting.test.pointer child type...OK
All 2 tests passed.

```

See also:

- [Optional Pointers](#Optional-Pointers)
- [@ptrFromInt](#ptrFromInt)
- [@intFromPtr](#intFromPtr)
- [C Pointers](46-c.md#C-Pointers)

#### volatile

Loads and stores are assumed to not have side effects. If a given load or store
should have side effects, such as Memory Mapped Input/Output (MMIO), use `volatile`.
In the following code, loads and stores with `mmio_ptr` are guaranteed to all happen
and in the same order as in source code:

**`test_volatile.zig`:**

```zig
const expect = @import("std").testing.expect;

test "volatile" {
    const mmio_ptr: *volatile u8 = @ptrFromInt(0x12345678);
    try expect(@TypeOf(mmio_ptr) == *volatile u8);
}

```

**Shell:**

```shell
$ zig test test_volatile.zig
1/1 test_volatile.test.volatile...OK
All 1 tests passed.

```

Note that `volatile` is unrelated to concurrency and [Atomics](36-atomics.md#Atomics).
If you see code that is using `volatile` for something other than Memory Mapped
Input/Output, it is probably a bug.

#### Alignment

Each type has an **alignment** - a number of bytes such that,
when a value of the type is loaded from or stored to memory,
the memory address must be evenly divisible by this number. You can use
[@alignOf](#alignOf) to find out this value for any type.

Alignment depends on the CPU architecture, but is always a power of two, and
less than `1 << 29`.

In Zig, a pointer type has an alignment value. If the value is equal to the
alignment of the underlying type, it can be omitted from the type:

**`test_variable_alignment.zig`:**

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
        try expect(@typeInfo(*i32).pointer.alignment == 4);
    }
}

```

**Shell:**

```shell
$ zig test test_variable_alignment.zig
1/1 test_variable_alignment.test.variable alignment...OK
All 1 tests passed.

```

In the same way that a `*i32` can be [coerced](#Type-Coercion) to a
`*const i32`, a pointer with a larger alignment can be implicitly
cast to a pointer with a smaller alignment, but not vice versa.

You can specify alignment on variables and functions. If you do this, then
pointers to them get the specified alignment:

**`test_variable_func_alignment.zig`:**

```zig
const expect = @import("std").testing.expect;

var foo: u8 align(4) = 100;

test "global variable alignment" {
    try expect(@typeInfo(@TypeOf(&foo)).pointer.alignment == 4);
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
    try expect(@TypeOf(derp) == fn () i32);
    try expect(@TypeOf(&derp) == *align(@sizeOf(usize) * 2) const fn () i32);

    noop1();
    try expect(@TypeOf(noop1) == fn () void);
    try expect(@TypeOf(&noop1) == *align(1) const fn () void);

    noop4();
    try expect(@TypeOf(noop4) == fn () void);
    try expect(@TypeOf(&noop4) == *align(4) const fn () void);
}

```

**Shell:**

```shell
$ zig test test_variable_func_alignment.zig
1/2 test_variable_func_alignment.test.global variable alignment...OK
2/2 test_variable_func_alignment.test.function alignment...OK
All 2 tests passed.

```

If you have a pointer or a slice that has a small alignment, but you know that it actually
has a bigger alignment, use [@alignCast](#alignCast) to change the
pointer into a more aligned pointer. This is a no-op at runtime, but inserts a
[safety check](#Incorrect-Pointer-Alignment):

**`test_incorrect_pointer_alignment.zig`:**

```zig
const std = @import("std");

test "pointer alignment safety" {
    var array align(4) = [_]u32{ 0x11111111, 0x11111111 };
    const bytes = std.mem.sliceAsBytes(array[0..]);
    try std.testing.expect(foo(bytes) == 0x11111111);
}
fn foo(bytes: []u8) u32 {
    const slice4 = bytes[1..5];
    const int_slice = std.mem.bytesAsSlice(u32, @as([]align(4) u8, @alignCast(slice4)));
    return int_slice[0];
}

```

**Shell:**

```shell
$ zig test test_incorrect_pointer_alignment.zig
1/1 test_incorrect_pointer_alignment.test.pointer alignment safety...thread 198705 panic: incorrect alignment
/home/andy/dev/zig/doc/langref/test_incorrect_pointer_alignment.zig:10:68: 0x1048b82 in foo (test)
    const int_slice = std.mem.bytesAsSlice(u32, @as([]align(4) u8, @alignCast(slice4)));
                                                                   ^
/home/andy/dev/zig/doc/langref/test_incorrect_pointer_alignment.zig:6:31: 0x1048a2f in test.pointer alignment safety (test)
    try std.testing.expect(foo(bytes) == 0x11111111);
                              ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:214:25: 0x10ef475 in mainTerminal (test)
        if (test_fn.func()) |_| {
                        ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:62:28: 0x10e785d in main (test)
        return mainTerminal();
                           ^
/home/andy/dev/zig/lib/std/start.zig:651:22: 0x10e6cd2 in posixCallMainAndExit (test)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:271:5: 0x10e68ad in _start (test)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
error: the following test command crashed:
/home/andy/dev/zig/.zig-cache/o/c74c6fc05a4afb04990e9fe5ae00c4c0/test --seed=0x77765cb4

```

#### allowzero

This pointer attribute allows a pointer to have address zero. This is only ever needed on the
freestanding OS target, where the address zero is mappable. If you want to represent null pointers, use
[Optional Pointers](#Optional-Pointers) instead. [Optional Pointers](#Optional-Pointers) with `allowzero`
are not the same size as pointers. In this code example, if the pointer
did not have the `allowzero` attribute, this would be a
[Pointer Cast Invalid Null](#Pointer-Cast-Invalid-Null) panic:

**`test_allowzero.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "allowzero" {
    var zero: usize = 0; // var to make to runtime-known
    _ = &zero; // suppress 'var is never mutated' error
    const ptr: *allowzero i32 = @ptrFromInt(zero);
    try expect(@intFromPtr(ptr) == 0);
}

```

**Shell:**

```shell
$ zig test test_allowzero.zig
1/1 test_allowzero.test.allowzero...OK
All 1 tests passed.

```

#### Sentinel-Terminated Pointers

The syntax `[*:x]T` describes a pointer that
has a length determined by a sentinel value. This provides protection
against buffer overflow and overreads.

**`sentinel-terminated_pointer.zig`:**

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
$ zig build-exe sentinel-terminated_pointer.zig -lc
/home/andy/dev/zig/doc/langref/sentinel-terminated_pointer.zig:11:16: error: expected type '[*:0]const u8', found '*const [14]u8'
    _ = printf(&non_null_terminated_msg);
               ^~~~~~~~~~~~~~~~~~~~~~~~
/home/andy/dev/zig/doc/langref/sentinel-terminated_pointer.zig:11:16: note: destination pointer requires '0' sentinel
/home/andy/dev/zig/doc/langref/sentinel-terminated_pointer.zig:4:34: note: parameter type declared here
pub extern "c" fn printf(format: [*:0]const u8, ...) c_int;
                                 ^~~~~~~~~~~~~
referenced by:
    main: /home/andy/dev/zig/lib/std/start.zig:660:37
    comptime: /home/andy/dev/zig/lib/std/start.zig:58:30
    2 reference(s) hidden; use '-freference-trace=4' to see all references


```

See also:

- [Sentinel-Terminated Slices](#Sentinel-Terminated-Slices)
- [Sentinel-Terminated Arrays](#Sentinel-Terminated-Arrays)


---

### Slices

A slice is a pointer and a length. The difference between an array and
a slice is that the array's length is part of the type and known at
compile-time, whereas the slice's length is known at runtime.
Both can be accessed with the `len` field.

**`test_basic_slices.zig`:**

```zig
const expect = @import("std").testing.expect;
const expectEqualSlices = @import("std").testing.expectEqualSlices;

test "basic slices" {
    var array = [_]i32{ 1, 2, 3, 4 };
    var known_at_runtime_zero: usize = 0;
    _ = &known_at_runtime_zero;
    const slice = array[known_at_runtime_zero..array.len];

    // alternative initialization using result location
    const alt_slice: []const i32 = &.{ 1, 2, 3, 4 };

    try expectEqualSlices(i32, slice, alt_slice);

    try expect(@TypeOf(slice) == []i32);
    try expect(&slice[0] == &array[0]);
    try expect(slice.len == array.len);

    // If you slice with comptime-known start and end positions, the result is
    // a pointer to an array, rather than a slice.
    const array_ptr = array[0..array.len];
    try expect(@TypeOf(array_ptr) == *[array.len]i32);

    // You can perform a slice-by-length by slicing twice. This allows the compiler
    // to perform some optimisations like recognising a comptime-known length when
    // the start position is only known at runtime.
    var runtime_start: usize = 1;
    _ = &runtime_start;
    const length = 2;
    const array_ptr_len = array[runtime_start..][0..length];
    try expect(@TypeOf(array_ptr_len) == *[length]i32);

    // Using the address-of operator on a slice gives a single-item pointer.
    try expect(@TypeOf(&slice[0]) == *i32);
    // Using the `ptr` field gives a many-item pointer.
    try expect(@TypeOf(slice.ptr) == [*]i32);
    try expect(@intFromPtr(slice.ptr) == @intFromPtr(&slice[0]));

    // Slices have array bounds checking. If you try to access something out
    // of bounds, you'll get a safety check failure:
    slice[10] += 1;

    // Note that `slice.ptr` does not invoke safety checking, while `&slice[0]`
    // asserts that the slice has len > 0.

    // Empty slices can be created like this:
    const empty1 = &[0]u8{};
    // If the type is known you can use this short hand:
    const empty2: []u8 = &.{};
    try expect(empty1.len == 0);
    try expect(empty2.len == 0);

    // A zero-length initialization can always be used to create an empty slice, even if the slice is mutable.
    // This is because the pointed-to data is zero bits long, so its immutability is irrelevant.
}

```

**Shell:**

```shell
$ zig test test_basic_slices.zig
1/1 test_basic_slices.test.basic slices...thread 200412 panic: index out of bounds: index 10, len 4
/home/andy/dev/zig/doc/langref/test_basic_slices.zig:41:10: 0x104b511 in test.basic slices (test)
    slice[10] += 1;
         ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:214:25: 0x10f2925 in mainTerminal (test)
        if (test_fn.func()) |_| {
                        ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:62:28: 0x10ead0d in main (test)
        return mainTerminal();
                           ^
/home/andy/dev/zig/lib/std/start.zig:651:22: 0x10ea182 in posixCallMainAndExit (test)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:271:5: 0x10e9d5d in _start (test)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
error: the following test command crashed:
/home/andy/dev/zig/.zig-cache/o/59dc8382d8140cff64d1ea721c83a213/test --seed=0x2837bf4f

```

This is one reason we prefer slices to pointers.

**`test_slices.zig`:**

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
    // You can use slice syntax with at least one runtime-known index on an
    // array to convert an array into a slice.
    var start: usize = 0;
    _ = &start;
    const all_together_slice = all_together[start..];
    // String concatenation example.
    const hello_world = try fmt.bufPrint(all_together_slice, "{s} {s}", .{ hello, world });

    // Generally, you can use UTF-8 and not worry about whether something is a
    // string. If you don't need to deal with individual characters, no need
    // to decode.
    try expect(mem.eql(u8, hello_world, "hello ä¸ç"));
}

test "slice pointer" {
    var array: [10]u8 = undefined;
    const ptr = &array;
    try expect(@TypeOf(ptr) == *[10]u8);

    // A pointer to an array can be sliced just like an array:
    var start: usize = 0;
    var end: usize = 5;
    _ = .{ &start, &end };
    const slice = ptr[start..end];
    // The slice is mutable because we sliced a mutable pointer.
    try expect(@TypeOf(slice) == []u8);
    slice[2] = 3;
    try expect(array[2] == 3);

    // Again, slicing with comptime-known indexes will produce another pointer
    // to an array:
    const ptr2 = slice[2..3];
    try expect(ptr2.len == 1);
    try expect(ptr2[0] == 3);
    try expect(@TypeOf(ptr2) == *[1]u8);
}

```

**Shell:**

```shell
$ zig test test_slices.zig
1/2 test_slices.test.using slices for strings...OK
2/2 test_slices.test.slice pointer...OK
All 2 tests passed.

```

See also:

- [Pointers](13-pointers.md#Pointers)
- [for](22-for.md#for)
- [Arrays](11-arrays.md#Arrays)

#### Sentinel-Terminated Slices

The syntax `[:x]T` is a slice which has a runtime-known length
and also guarantees a sentinel value at the element indexed by the length. The type does not
guarantee that there are no sentinel elements before that. Sentinel-terminated slices allow element
access to the `len` index.

**`test_null_terminated_slice.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "0-terminated slice" {
    const slice: [:0]const u8 = "hello";

    try expect(slice.len == 5);
    try expect(slice[5] == 0);
}

```

**Shell:**

```shell
$ zig test test_null_terminated_slice.zig
1/1 test_null_terminated_slice.test.0-terminated slice...OK
All 1 tests passed.

```

Sentinel-terminated slices can also be created using a variation of the slice syntax
`data[start..end :x]`, where `data` is a many-item pointer,
array or slice and `x` is the sentinel value.

**`test_null_terminated_slicing.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "0-terminated slicing" {
    var array = [_]u8{ 3, 2, 1, 0, 3, 2, 1, 0 };
    var runtime_length: usize = 3;
    _ = &runtime_length;
    const slice = array[0..runtime_length :0];

    try expect(@TypeOf(slice) == [:0]u8);
    try expect(slice.len == 3);
}

```

**Shell:**

```shell
$ zig test test_null_terminated_slicing.zig
1/1 test_null_terminated_slicing.test.0-terminated slicing...OK
All 1 tests passed.

```

Sentinel-terminated slicing asserts that the element in the sentinel position of the backing data is
actually the sentinel value. If this is not the case, safety-checked [Illegal Behavior](41-illegal-behavior.md#Illegal-Behavior) results.

**`test_sentinel_mismatch.zig`:**

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
    _ = &runtime_length;
    const slice = array[0..runtime_length :0];

    _ = slice;
}

```

**Shell:**

```shell
$ zig test test_sentinel_mismatch.zig
1/1 test_sentinel_mismatch.test.sentinel mismatch...thread 201174 panic: sentinel mismatch: expected 0, found 1
/home/andy/dev/zig/doc/langref/test_sentinel_mismatch.zig:13:24: 0x1048a71 in test.sentinel mismatch (test)
    const slice = array[0..runtime_length :0];
                       ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:214:25: 0x10ef1d5 in mainTerminal (test)
        if (test_fn.func()) |_| {
                        ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:62:28: 0x10e75bd in main (test)
        return mainTerminal();
                           ^
/home/andy/dev/zig/lib/std/start.zig:651:22: 0x10e6a32 in posixCallMainAndExit (test)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:271:5: 0x10e660d in _start (test)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
error: the following test command crashed:
/home/andy/dev/zig/.zig-cache/o/3ae1c7f3e7c9fd9d03520f85869dba54/test --seed=0xcab5d72d

```

See also:

- [Sentinel-Terminated Pointers](#Sentinel-Terminated-Pointers)
- [Sentinel-Terminated Arrays](#Sentinel-Terminated-Arrays)


---

### struct

**`test_structs.zig`:**

```zig
// Declare a struct.
// Zig gives no guarantees about the order of fields and the size of
// the struct but the fields are guaranteed to be ABI-aligned.
const Point = struct {
    x: f32,
    y: f32,
};

// Declare an instance of a struct.
const p: Point = .{
    .x = 0.12,
    .y = 0.34,
};

// Functions in the struct's namespace can be called with dot syntax.
const Vec3 = struct {
    x: f32,
    y: f32,
    z: f32,

    pub fn init(x: f32, y: f32, z: f32) Vec3 {
        return Vec3{
            .x = x,
            .y = y,
            .z = z,
        };
    }

    pub fn dot(self: Vec3, other: Vec3) f32 {
        return self.x * other.x + self.y * other.y + self.z * other.z;
    }
};

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

    // Empty structs can be instantiated the same as usual.
    const does_nothing: Empty = .{};

    _ = does_nothing;
}

// Struct field order is determined by the compiler, however, a base pointer
// can be computed from a field pointer:
fn setYBasedOnX(x: *f32, y: f32) void {
    const point: *Point = @fieldParentPtr("x", x);
    point.y = y;
}
test "field parent pointer" {
    var point = Point{
        .x = 0.1234,
        .y = 0.5678,
    };
    setYBasedOnX(&point.x, 0.9);
    try expect(point.y == 0.9);
}

// Structs can be returned from functions.
fn LinkedList(comptime T: type) type {
    return struct {
        pub const Node = struct {
            prev: ?*Node,
            next: ?*Node,
            data: T,
        };

        first: ?*Node,
        last: ?*Node,
        len: usize,
    };
}

test "linked list" {
    // Functions called at compile-time are memoized.
    try expect(LinkedList(i32) == LinkedList(i32));

    const list = LinkedList(i32){
        .first = null,
        .last = null,
        .len = 0,
    };
    try expect(list.len == 0);

    // Since types are first class values you can instantiate the type
    // by assigning it to a variable:
    const ListOfInts = LinkedList(i32);
    try expect(ListOfInts == LinkedList(i32));

    var node = ListOfInts.Node{
        .prev = null,
        .next = null,
        .data = 1234,
    };
    const list2 = LinkedList(i32){
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

const expect = @import("std").testing.expect;

```

**Shell:**

```shell
$ zig test test_structs.zig
1/4 test_structs.test.dot product...OK
2/4 test_structs.test.struct namespaced variable...OK
3/4 test_structs.test.field parent pointer...OK
4/4 test_structs.test.linked list...OK
All 4 tests passed.

```

#### Default Field Values

Each struct field may have an expression indicating the default field
value. Such expressions are executed at [comptime](34-comptime.md#comptime), and allow the
field to be omitted in a struct literal expression:

**`struct_default_field_values.zig`:**

```zig
const Foo = struct {
    a: i32 = 1234,
    b: i32,
};

test "default struct initialization fields" {
    const x: Foo = .{
        .b = 5,
    };
    if (x.a + x.b != 1239) {
        comptime unreachable;
    }
}

```

**Shell:**

```shell
$ zig test struct_default_field_values.zig
1/1 struct_default_field_values.test.default struct initialization fields...OK
All 1 tests passed.

```

##### Faulty Default Field Values

Default field values are only appropriate when the data invariants of a struct
cannot be violated by omitting that field from an initialization.

For example, here is an inappropriate use of default struct field initialization:

**`bad_default_value.zig`:**

```zig
const Threshold = struct {
    minimum: f32 = 0.25,
    maximum: f32 = 0.75,

    const Category = enum { low, medium, high };

    fn categorize(t: Threshold, value: f32) Category {
        assert(t.maximum >= t.minimum);
        if (value < t.minimum) return .low;
        if (value > t.maximum) return .high;
        return .medium;
    }
};

pub fn main() !void {
    var threshold: Threshold = .{
        .maximum = 0.20,
    };
    const category = threshold.categorize(0.90);
    try std.io.getStdOut().writeAll(@tagName(category));
}

const std = @import("std");
const assert = std.debug.assert;

```

**Shell:**

```shell
$ zig build-exe bad_default_value.zig
$ ./bad_default_value
thread 206555 panic: reached unreachable code
/home/andy/dev/zig/lib/std/debug.zig:550:14: 0x1048dbd in assert (bad_default_value)
    if (!ok) unreachable; // assertion failure
             ^
/home/andy/dev/zig/doc/langref/bad_default_value.zig:8:15: 0x10de7d9 in categorize (bad_default_value)
        assert(t.maximum >= t.minimum);
              ^
/home/andy/dev/zig/doc/langref/bad_default_value.zig:19:42: 0x10de71a in main (bad_default_value)
    const category = threshold.categorize(0.90);
                                         ^
/home/andy/dev/zig/lib/std/start.zig:660:37: 0x10de62a in posixCallMainAndExit (bad_default_value)
            const result = root.main() catch |err| {
                                    ^
/home/andy/dev/zig/lib/std/start.zig:271:5: 0x10de1dd in _start (bad_default_value)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

Above you can see the danger of ignoring this principle. The default
field values caused the data invariant to be violated, causing illegal
behavior.

To fix this, remove the default values from all the struct fields, and provide
a named default value:

**`struct_default_value.zig`:**

```zig
const Threshold = struct {
    minimum: f32,
    maximum: f32,

    const default: Threshold = .{
        .minimum = 0.25,
        .maximum = 0.75,
    };
};

```

If a struct value requires a runtime-known value in order to be initialized
without violating data invariants, then use an initialization method that accepts
those runtime values, and populates the remaining fields.

#### extern struct

An `extern struct` has in-memory layout matching
the C ABI for the target.

If well-defined in-memory layout is not required, [struct](#struct) is a better choice
because it places fewer restrictions on the compiler.

See [packed struct](#packed-struct) for a struct that has the ABI of its backing integer,
which can be useful for modeling flags.

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
- Packed structs support equality operators.

This means that a `packed struct` can participate
in a [@bitCast](#bitCast) or a [@ptrCast](#ptrCast) to reinterpret memory.
This even works at [comptime](34-comptime.md#comptime):

**`test_packed_structs.zig`:**

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
    try comptime doTheTest();
}

fn doTheTest() !void {
    try expect(@sizeOf(Full) == 2);
    try expect(@sizeOf(Divided) == 2);
    const full = Full{ .number = 0x1234 };
    const divided: Divided = @bitCast(full);
    try expect(divided.half1 == 0x34);
    try expect(divided.quarter3 == 0x2);
    try expect(divided.quarter4 == 0x1);

    const ordered: [2]u8 = @bitCast(full);
    switch (native_endian) {
        .big => {
            try expect(ordered[0] == 0x12);
            try expect(ordered[1] == 0x34);
        },
        .little => {
            try expect(ordered[0] == 0x34);
            try expect(ordered[1] == 0x12);
        },
    }
}

```

**Shell:**

```shell
$ zig test test_packed_structs.zig
1/1 test_packed_structs.test.@bitCast between packed structs...OK
All 1 tests passed.

```

The backing integer is inferred from the fields' total bit width.
Optionally, it can be explicitly provided and enforced at compile time:

**`test_missized_packed_struct.zig`:**

```zig
test "missized packed struct" {
    const S = packed struct(u32) { a: u16, b: u8 };
    _ = S{ .a = 4, .b = 2 };
}

```

**Shell:**

```shell
$ zig test test_missized_packed_struct.zig
/home/andy/dev/zig/doc/langref/test_missized_packed_struct.zig:2:29: error: backing integer type 'u32' has bit size 32 but the struct fields have a total bit size of 24
    const S = packed struct(u32) { a: u16, b: u8 };
                            ^~~
referenced by:
    test.missized packed struct: /home/andy/dev/zig/doc/langref/test_missized_packed_struct.zig:2:22


```

Zig allows the address to be taken of a non-byte-aligned field:

**`test_pointer_to_non-byte_aligned_field.zig`:**

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
$ zig test test_pointer_to_non-byte_aligned_field.zig
1/1 test_pointer_to_non-byte_aligned_field.test.pointer to non-byte-aligned field...OK
All 1 tests passed.

```

However, the pointer to a non-byte-aligned field has special properties and cannot
be passed when a normal pointer is expected:

**`test_misaligned_pointer.zig`:**

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

test "pointer to non-byte-aligned field" {
    try expect(bar(&bit_field.b) == 2);
}

fn bar(x: *const u3) u3 {
    return x.*;
}

```

**Shell:**

```shell
$ zig test test_misaligned_pointer.zig
/home/andy/dev/zig/doc/langref/test_misaligned_pointer.zig:17:20: error: expected type '*const u3', found '*align(1:3:1) u3'
    try expect(bar(&bit_field.b) == 2);
                   ^~~~~~~~~~~~
/home/andy/dev/zig/doc/langref/test_misaligned_pointer.zig:17:20: note: pointer host size '1' cannot cast into pointer host size '0'
/home/andy/dev/zig/doc/langref/test_misaligned_pointer.zig:17:20: note: pointer bit offset '3' cannot cast into pointer bit offset '0'
/home/andy/dev/zig/doc/langref/test_misaligned_pointer.zig:20:11: note: parameter type declared here
fn bar(x: *const u3) u3 {
          ^~~~~~~~~


```

In this case, the function `bar` cannot be called because the pointer
to the non-ABI-aligned field mentions the bit offset, but the function expects an ABI-aligned pointer.

Pointers to non-ABI-aligned fields share the same address as the other fields within their host integer:

**`test_packed_struct_field_address.zig`:**

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
    try expect(@intFromPtr(&bit_field.a) == @intFromPtr(&bit_field.b));
    try expect(@intFromPtr(&bit_field.a) == @intFromPtr(&bit_field.c));
}

```

**Shell:**

```shell
$ zig test test_packed_struct_field_address.zig
1/1 test_packed_struct_field_address.test.pointers of sub-byte-aligned fields share addresses...OK
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

test "offsets of non-byte-aligned fields" {
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
1/1 test_bitOffsetOf_offsetOf.test.offsets of non-byte-aligned fields...OK
All 1 tests passed.

```

Packed structs have the same alignment as their backing integer, however, overaligned
pointers to packed structs can override this:

**`test_overaligned_packed_struct.zig`:**

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
$ zig test test_overaligned_packed_struct.zig
1/1 test_overaligned_packed_struct.test.overaligned pointer to packed struct...OK
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
1/1 test_aligned_struct_fields.test.aligned struct fields...OK
All 1 tests passed.

```

Equating packed structs results in a comparison of the backing integer,
and only works for the `==` and `!=` operators.

**`test_packed_struct_equality.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "packed struct equality" {
    const S = packed struct {
        a: u4,
        b: u4,
    };
    const x: S = .{ .a = 1, .b = 2 };
    const y: S = .{ .b = 2, .a = 1 };
    try expect(x == y);
}

```

**Shell:**

```shell
$ zig test test_packed_struct_equality.zig
1/1 test_packed_struct_equality.test.packed struct equality...OK
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
- Otherwise, the struct gets a name such as `(filename.funcname__struct_ID)`.
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
anonymous: struct_name.main__struct_24147
function: struct_name.List(i32)

```

#### Anonymous Struct Literals

Zig allows omitting the struct type of a literal. When the result is [coerced](#Type-Coercion),
the struct literal will directly instantiate the [result location](32-result-location-semantics.md#Result-Location-Semantics),
with no copy:

**`test_struct_result.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Point = struct { x: i32, y: i32 };

test "anonymous struct literal" {
    const pt: Point = .{
        .x = 13,
        .y = 67,
    };
    try expect(pt.x == 13);
    try expect(pt.y == 67);
}

```

**Shell:**

```shell
$ zig test test_struct_result.zig
1/1 test_struct_result.test.anonymous struct literal...OK
All 1 tests passed.

```

The struct type can be inferred. Here the [result location](32-result-location-semantics.md#Result-Location-Semantics)
does not include a type, and so Zig infers the type:

**`test_anonymous_struct.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "fully anonymous struct" {
    try check(.{
        .int = @as(u32, 1234),
        .float = @as(f64, 12.34),
        .b = true,
        .s = "hi",
    });
}

fn check(args: anytype) !void {
    try expect(args.int == 1234);
    try expect(args.float == 12.34);
    try expect(args.b);
    try expect(args.s[0] == 'h');
    try expect(args.s[1] == 'i');
}

```

**Shell:**

```shell
$ zig test test_anonymous_struct.zig
1/1 test_anonymous_struct.test.fully anonymous struct...OK
All 1 tests passed.

```

#### Tuples

Anonymous structs can be created without specifying field names, and are referred to as "tuples". An empty tuple looks like `.{}` and can be seen in one of the [Hello World examples](03-hello-world.md#Hello-World).

The fields are implicitly named using numbers starting from 0. Because their names are integers,
they cannot be accessed with `.` syntax without also wrapping them in
`@""`. Names inside `@""` are always recognised as
[identifiers](#Identifiers).

Like arrays, tuples have a .len field, can be indexed (provided the index is comptime-known)
and work with the ++ and ** operators. They can also be iterated over with [inline for](#inline-for).

**`test_tuples.zig`:**

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
    inline for (values, 0..) |v, i| {
        if (i != 2) continue;
        try expect(v);
    }
    try expect(values.len == 6);
    try expect(values.@"3"[0] == 'h');
}

```

**Shell:**

```shell
$ zig test test_tuples.zig
1/1 test_tuples.test.tuple...OK
All 1 tests passed.

```

##### Destructuring Tuples

Tuples can be [destructured](#Destructuring).

Tuple destructuring is helpful for returning multiple values from a block:

**`destructuring_block.zig`:**

```zig
const print = @import("std").debug.print;

pub fn main() void {
    const digits = [_]i8 { 3, 8, 9, 0, 7, 4, 1 };

    const min, const max = blk: {
        var min: i8 = 127;
        var max: i8 = -128;

        for (digits) |digit| {
            if (digit < min) min = digit;
            if (digit > max) max = digit;
        }

        break :blk .{ min, max };
    };

    print("min = {}", .{ min });
    print("max = {}", .{ max });
}

```

**Shell:**

```shell
$ zig build-exe destructuring_block.zig
$ ./destructuring_block
min = 0max = 9

```

Tuple destructuring is helpful for dealing with functions and built-ins that return multiple values
as a tuple:

**`destructuring_return_value.zig`:**

```zig
const print = @import("std").debug.print;

fn divmod(numerator: u32, denominator: u32) struct { u32, u32 } {
    return .{ numerator / denominator, numerator % denominator };
}

pub fn main() void {
    const div, const mod = divmod(10, 3);

    print("10 / 3 = {}\n", .{div});
    print("10 % 3 = {}\n", .{mod});
}

```

**Shell:**

```shell
$ zig build-exe destructuring_return_value.zig
$ ./destructuring_return_value
10 / 3 = 3
10 % 3 = 1

```

See also:

- [Destructuring](#Destructuring)
- [Destructuring Arrays](#Destructuring-Arrays)
- [Destructuring Vectors](#Destructuring-Vectors)

See also:

- [comptime](34-comptime.md#comptime)
- [@fieldParentPtr](#fieldParentPtr)


---

### enum

**`test_enums.zig`:**

```zig
const expect = @import("std").testing.expect;
const mem = @import("std").mem;

// Declare an enum.
const Type = enum {
    ok,
    not_ok,
};

// Declare a specific enum field.
const c = Type.ok;

// If you want access to the ordinal value of an enum, you
// can specify the tag type.
const Value = enum(u2) {
    zero,
    one,
    two,
};
// Now you can cast between u2 and Value.
// The ordinal value starts from 0, counting up by 1 from the previous member.
test "enum ordinal value" {
    try expect(@intFromEnum(Value.zero) == 0);
    try expect(@intFromEnum(Value.one) == 1);
    try expect(@intFromEnum(Value.two) == 2);
}

// You can override the ordinal value for an enum.
const Value2 = enum(u32) {
    hundred = 100,
    thousand = 1000,
    million = 1000000,
};
test "set enum ordinal value" {
    try expect(@intFromEnum(Value2.hundred) == 100);
    try expect(@intFromEnum(Value2.thousand) == 1000);
    try expect(@intFromEnum(Value2.million) == 1000000);
}

// You can also override only some values.
const Value3 = enum(u4) {
    a,
    b = 8,
    c,
    d = 4,
    e,
};
test "enum implicit ordinal values and overridden values" {
    try expect(@intFromEnum(Value3.a) == 0);
    try expect(@intFromEnum(Value3.b) == 8);
    try expect(@intFromEnum(Value3.c) == 9);
    try expect(@intFromEnum(Value3.d) == 4);
    try expect(@intFromEnum(Value3.e) == 5);
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

// An enum can be switched upon.
const Foo = enum {
    string,
    number,
    none,
};
test "enum switch" {
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
    try expect(@typeInfo(Small).@"enum".tag_type == u2);
}

// @typeInfo tells us the field count and the fields names:
test "@typeInfo" {
    try expect(@typeInfo(Small).@"enum".fields.len == 4);
    try expect(mem.eql(u8, @typeInfo(Small).@"enum".fields[1].name, "two"));
}

// @tagName gives a [:0]const u8 representation of an enum value:
test "@tagName" {
    try expect(mem.eql(u8, @tagName(Small.three), "three"));
}

```

**Shell:**

```shell
$ zig test test_enums.zig
1/8 test_enums.test.enum ordinal value...OK
2/8 test_enums.test.set enum ordinal value...OK
3/8 test_enums.test.enum implicit ordinal values and overridden values...OK
4/8 test_enums.test.enum method...OK
5/8 test_enums.test.enum switch...OK
6/8 test_enums.test.std.meta.Tag...OK
7/8 test_enums.test.@typeInfo...OK
8/8 test_enums.test.@tagName...OK
All 8 tests passed.

```

See also:

- [@typeInfo](#typeInfo)
- [@tagName](#tagName)
- [@sizeOf](#sizeOf)

#### extern enum

By default, enums are not guaranteed to be compatible with the C ABI:

**`enum_export_error.zig`:**

```zig
const Foo = enum { a, b, c };
export fn entry(foo: Foo) void {
    _ = foo;
}

```

**Shell:**

```shell
$ zig build-obj enum_export_error.zig -target x86_64-linux
/home/andy/dev/zig/doc/langref/enum_export_error.zig:2:17: error: parameter of type 'enum_export_error.Foo' not allowed in function with calling convention 'x86_64_sysv'
export fn entry(foo: Foo) void {
                ^~~~~~~~
/home/andy/dev/zig/doc/langref/enum_export_error.zig:2:17: note: enum tag type 'u2' is not extern compatible
/home/andy/dev/zig/doc/langref/enum_export_error.zig:2:17: note: only integers with 0, 8, 16, 32, 64 and 128 bits are extern compatible
/home/andy/dev/zig/doc/langref/enum_export_error.zig:1:13: note: enum declared here
const Foo = enum { a, b, c };
            ^~~~~~~~~~~~~~~~
referenced by:
    root: /home/andy/dev/zig/lib/std/start.zig:3:22
    comptime: /home/andy/dev/zig/lib/std/start.zig:27:9
    2 reference(s) hidden; use '-freference-trace=4' to see all references


```

For a C-ABI-compatible enum, provide an explicit tag type to
the enum:

**`enum_export.zig`:**

```zig
const Foo = enum(c_int) { a, b, c };
export fn entry(foo: Foo) void {
    _ = foo;
}

```

**Shell:**

```shell
$ zig build-obj enum_export.zig

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
1/2 test_enum_literals.test.enum literals...OK
2/2 test_enum_literals.test.switch using enum literals...OK
All 2 tests passed.

```

#### Non-exhaustive enum

A non-exhaustive enum can be created by adding a trailing `_` field.
The enum must specify a tag type and cannot consume every enumeration value.

[@enumFromInt](#enumFromInt) on a non-exhaustive enum involves the safety semantics
of [@intCast](#intCast) to the integer tag type, but beyond that always results in
a well-defined enum value.

A switch on a non-exhaustive enum can include a `_` prong as an alternative to an `else` prong.
With a `_` prong the compiler errors if all the known tag names are not handled by the switch.

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
        .two, .three => false,
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
1/1 test_switch_non-exhaustive.test.switch on non-exhaustive enum...OK
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
safety-checked [Illegal Behavior](41-illegal-behavior.md#Illegal-Behavior):

**`test_wrong_union_access.zig`:**

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
$ zig test test_wrong_union_access.zig
1/1 test_wrong_union_access.test.simple union...thread 210915 panic: access of union field 'float' while field 'int' is active
/home/andy/dev/zig/doc/langref/test_wrong_union_access.zig:8:12: 0x1048a5f in test.simple union (test)
    payload.float = 12.34;
           ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:214:25: 0x10ef2e5 in mainTerminal (test)
        if (test_fn.func()) |_| {
                        ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:62:28: 0x10e76cd in main (test)
        return mainTerminal();
                           ^
/home/andy/dev/zig/lib/std/start.zig:651:22: 0x10e6b42 in posixCallMainAndExit (test)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:271:5: 0x10e671d in _start (test)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
error: the following test command crashed:
/home/andy/dev/zig/.zig-cache/o/0e2ad1837ee3fe26786cd418343cba9e/test --seed=0xdea5f103

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
1/1 test_simple_union.test.simple union...OK
All 1 tests passed.

```

In order to use [switch](20-switch.md#switch) with a union, it must be a [Tagged union](#Tagged-union).

To initialize a union when the tag is a [comptime](34-comptime.md#comptime)-known name, see [@unionInit](#unionInit).

#### Tagged union

Unions can be declared with an enum tag type.
This turns the union into a *tagged* union, which makes it eligible
to use with [switch](20-switch.md#switch) expressions.
Tagged unions coerce to their tag type: [Type Coercion: Unions and Enums](#Type-Coercion-Unions-and-Enums).

**`test_tagged_union.zig`:**

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
        .ok => |value| try expect(value == 42),
        .not_ok => unreachable,
    }
}

test "get tag type" {
    try expect(std.meta.Tag(ComplexType) == ComplexTypeTag);
}

```

**Shell:**

```shell
$ zig test test_tagged_union.zig
1/2 test_tagged_union.test.switch on tagged union...OK
2/2 test_tagged_union.test.get tag type...OK
All 2 tests passed.

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
1/1 test_switch_modify_tagged_union.test.modify tagged union in switch...OK
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
    var v1: Variant = .{ .int = 1 };
    var v2: Variant = .{ .boolean = false };
    var v3: Variant = .none;

    try expect(v1.truthy());
    try expect(!v2.truthy());
    try expect(!v3.truthy());
}

```

**Shell:**

```shell
$ zig test test_union_method.zig
1/1 test_union_method.test.union method...OK
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
1/1 test_tagName.test.@tagName...OK
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

**`test_anonymous_union.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Number = union {
    int: i32,
    float: f64,
};

test "anonymous union literal syntax" {
    const i: Number = .{ .int = 42 };
    const f = makeNumber();
    try expect(i.int == 42);
    try expect(f.float == 12.34);
}

fn makeNumber() Number {
    return .{ .float = 12.34 };
}

```

**Shell:**

```shell
$ zig test test_anonymous_union.zig
1/1 test_anonymous_union.test.anonymous union literal syntax...OK
All 1 tests passed.

```


---

### opaque

`opaque {}` declares a new type with an unknown (but non-zero) size and alignment.
It can contain declarations the same as [structs](15-struct.md#struct), [unions](17-union.md#union),
and [enums](16-enum.md#enum).

This is typically used for type safety when interacting with C code that does not expose struct details.
Example:

**`test_opaque.zig`:**

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
$ zig test test_opaque.zig
/home/andy/dev/zig/doc/langref/test_opaque.zig:6:9: error: expected type '*test_opaque.Derp', found '*test_opaque.Wat'
    bar(w);
        ^
/home/andy/dev/zig/doc/langref/test_opaque.zig:6:9: note: pointer type child 'test_opaque.Wat' cannot cast into pointer type child 'test_opaque.Derp'
/home/andy/dev/zig/doc/langref/test_opaque.zig:2:13: note: opaque declared here
const Wat = opaque {};
            ^~~~~~~~~
/home/andy/dev/zig/doc/langref/test_opaque.zig:1:14: note: opaque declared here
const Derp = opaque {};
             ^~~~~~~~~
/home/andy/dev/zig/doc/langref/test_opaque.zig:4:18: note: parameter type declared here
extern fn bar(d: *Derp) void;
                 ^~~~~
referenced by:
    test.call foo: /home/andy/dev/zig/doc/langref/test_opaque.zig:10:8


```


---
