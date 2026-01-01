# Structs and Methods

*Defining structs and implementing methods in Zig*


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
value. Such expressions are executed at [comptime](33-comptime.md#comptime), and allow the
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
    try std.fs.File.stdout().writeAll(@tagName(category));
}

const std = @import("std");
const assert = std.debug.assert;

```

**Shell:**

```shell
$ zig build-exe bad_default_value.zig
$ ./bad_default_value
thread 1782213 panic: reached unreachable code
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/debug.zig:416:14: 0x102c5c9 in assert (std.zig)
    if (!ok) unreachable; // assertion failure
             ^
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/bad_default_value.zig:8:15: 0x11568aa in categorize (bad_default_value.zig)
        assert(t.maximum >= t.minimum);
              ^
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/bad_default_value.zig:19:42: 0x11557fe in main (bad_default_value.zig)
    const category = threshold.categorize(0.90);
                                         ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:696:37: 0x1155e03 in callMain (std.zig)
            const result = root.main() catch |err| {
                                    ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:237:5: 0x1155751 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
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

`packed` structs, like `enum`, are based on the concept
of interpreting integers differently. All packed structs have a **backing integer**,
which is implicitly determined by the total bit count of fields, or explicitly specified.
Packed structs have well-defined memory layout - exactly the same ABI as their backing integer.

Each field of a packed struct is interpreted as a logical sequence of bits, arranged from
least to most significant. Allowed field types:

- An [integer](08-integers.md#Integers) field uses exactly as many bits as its
  bit width. For example, a `u5` will use 5 bits of
  the backing integer.
- A [bool](#Primitive-Types) field uses exactly 1 bit.
- An [enum](16-enum.md#enum) field uses exactly the bit width of its integer tag type.
- A [packed union](#packed-union) field uses exactly the bit width of the union field with
  the largest bit width.
- A `packed struct` field uses the bits of its backing integer.

This means that a `packed struct` can participate
in a [@bitCast](#bitCast) or a [@ptrCast](#ptrCast) to reinterpret memory.
This even works at [comptime](33-comptime.md#comptime):

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

The backing integer can be inferred or explicitly provided. When
inferred, it will be unsigned. When explicitly provided, its bit width
will be enforced at compile time to exactly match the total bit width of
the fields:

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
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_missized_packed_struct.zig:2:29: error: backing integer type 'u32' has bit size 32 but the struct fields have a total bit size of 24
    const S = packed struct(u32) { a: u16, b: u8 };
                            ^~~
referenced by:
    test.missized packed struct: /home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_missized_packed_struct.zig:2:22


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
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_misaligned_pointer.zig:17:20: error: expected type '*const u3', found '*align(1:3:1) u3'
    try expect(bar(&bit_field.b) == 2);
                   ^~~~~~~~~~~~
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_misaligned_pointer.zig:17:20: note: pointer host size '1' cannot cast into pointer host size '0'
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_misaligned_pointer.zig:17:20: note: pointer bit offset '3' cannot cast into pointer bit offset '0'
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_misaligned_pointer.zig:20:11: note: parameter type declared here
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
    const ptr_to_b = &ptr.b;
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
and only works for the `==` and `!=` [Operators](10-operators.md#Operators).

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

Field access and assignment can be understood as shorthand for bitshifts
on the backing integer. These operations are not [atomic](35-atomics.md#Atomics),
so beware using field access syntax when combined with memory-mapped
input-output (MMIO). Instead of field access on [volatile](#volatile) [Pointers](13-pointers.md#Pointers),
construct a fully-formed new value first, then write that value to the volatile pointer.

**`packed_struct_mmio.zig`:**

```zig
pub const GpioRegister = packed struct(u8) {
    GPIO0: bool,
    GPIO1: bool,
    GPIO2: bool,
    GPIO3: bool,
    reserved: u4 = 0,
};

const gpio: *volatile GpioRegister = @ptrFromInt(0x0123);

pub fn writeToGpio(new_states: GpioRegister) void {
    // Example of what not to do:
    // BAD! gpio.GPIO0 = true; BAD!

    // Instead, do this:
    gpio.* = new_states;
}

```

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
anonymous: struct_name.main__struct_26936
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

    print("min = {}\n", .{ min });
    print("max = {}\n", .{ max });
}

```

**Shell:**

```shell
$ zig build-exe destructuring_block.zig
$ ./destructuring_block
min = 0
max = 9

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

- [comptime](33-comptime.md#comptime)
- [@fieldParentPtr](#fieldParentPtr)


---


---
