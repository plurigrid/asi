# Arrays, Vectors, and Slices

*Working with sequential data structures in Zig*


---

### Vectors

A vector is a group of booleans, [Integers](08-integers.md#Integers), [Floats](09-floats.md#Floats), or
[Pointers](13-pointers.md#Pointers) which are operated on in parallel, using SIMD instructions if possible.
Vector types are created with the builtin function [@Vector](#Vector).

Vectors generally support the same builtin operators as their underlying base types.
The only exception to this is the keywords `and` and `or` on vectors of bools, since
these operators affect control flow, which is not allowed for vectors.
All other operations are performed element-wise, and return a vector of the same length
as the input vectors. This includes:

- Arithmetic (`+`, `-`, `/`, `*`,
  `@divFloor`, `@sqrt`, `@ceil`,
  `@log`, etc.)
- Bitwise operators (`>>`, `<<`, `&`,
  `|`, `~`, etc.)
- Comparison operators (`<`, `>`, `==`, etc.)
- Boolean not (`!`)

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
    // Vectors can be coerced to arrays, and vice versa.
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

#### Relationship with Arrays

Vectors and [Arrays](11-arrays.md#Arrays) each have a well-defined **bit layout**
and therefore support [@bitCast](#bitCast) between each other. [Type Coercion](#Type-Coercion) implicitly peforms
`@bitCast`.

Arrays have well-defined byte layout, but vectors do not, making [@ptrCast](#ptrCast) between
them [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior).

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
{ 1, 5, 2, 6 }

```

See also:

- [Destructuring](#Destructuring)
- [Destructuring Tuples](#Destructuring-Tuples)
- [Destructuring Arrays](#Destructuring-Arrays)


---


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
1/1 test_basic_slices.test.basic slices...thread 1784244 panic: index out of bounds: index 10, len 4
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_basic_slices.zig:41:10: 0x1034f44 in test.basic slices (test_basic_slices.zig)
    slice[10] += 1;
         ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/compiler/test_runner.zig:248:25: 0x117a829 in mainTerminal (test_runner.zig)
        if (test_fn.func()) |_| {
                        ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/compiler/test_runner.zig:71:28: 0x117441a in main (test_runner.zig)
        return mainTerminal();
                           ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:687:22: 0x116f9d7 in callMain (std.zig)
            root.main();
                     ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:237:5: 0x116f4b1 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
error: the following test command crashed:
/home/ci/actions-runner/_work/zig-bootstrap/out/zig-local-cache/o/1249843f81c17f2cdc5314d37a2223df/test --seed=0xc0b74928

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
actually the sentinel value. If this is not the case, safety-checked [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior) results.

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
1/1 test_sentinel_mismatch.test.sentinel mismatch...thread 1784151 panic: sentinel mismatch: expected 0, found 1
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_sentinel_mismatch.zig:13:24: 0x10320f4 in test.sentinel mismatch (test_sentinel_mismatch.zig)
    const slice = array[0..runtime_length :0];
                       ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/compiler/test_runner.zig:248:25: 0x1175c29 in mainTerminal (test_runner.zig)
        if (test_fn.func()) |_| {
                        ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/compiler/test_runner.zig:71:28: 0x116f81a in main (test_runner.zig)
        return mainTerminal();
                           ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:687:22: 0x116add7 in callMain (std.zig)
            root.main();
                     ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:237:5: 0x116a8b1 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
error: the following test command crashed:
/home/ci/actions-runner/_work/zig-bootstrap/out/zig-local-cache/o/a3318f9050b707e49157fb3893f9828b/test --seed=0xd1036997

```

See also:

- [Sentinel-Terminated Pointers](#Sentinel-Terminated-Pointers)
- [Sentinel-Terminated Arrays](#Sentinel-Terminated-Arrays)


---


---
