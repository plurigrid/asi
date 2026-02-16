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
- [Pointers to Zero Bit Types](13-pointers.md#Pointers-to-Zero-Bit-Types) are themselves zero bit types.

These types can only ever have one possible value, and thus
require 0 bits to represent. Code that makes use of these types is
not included in the final generated code:

**`test.zig`:**

```zig
export fn entry() void {
    var x: void = {};
    var y: void = {};
    x = y;
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
they only perform the function call prologue and epilog.

#### void

`void` can be useful for instantiating generic types. For example, given a
`Map(Key, Value)`, one can pass `void` for the `Value`
type to make it into a `Set`:

**`void_in_hashmap.zig`:**

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
$ zig test void_in_hashmap.zig
1/1 test "turn HashMap into a set with void"... OK
All 1 tests passed.

```

Note that this is different from using a dummy value for the hash map value.
By using `void` as the type of the value, the hash map entry type has no value field, and
thus the hash map takes up less space. Further, all the code that deals with storing and loading the
value is deleted, as seen above.

`void` is distinct from `anyopaque`.
`void` has a known size of 0 bytes, and `anyopaque` has an unknown, but non-zero, size.

Expressions of type `void` are the only ones whose value can be ignored. For example:

**`test.zig`:**

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
$ zig test test.zig
./docgen_tmp/test.zig:2:8: error: expression value is ignored
    foo();
       ^

```

However, if the expression has type `void`, there will be no error. Function return values can also be explicitly ignored by assigning them to `_`.

**`void_ignored.zig`:**

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
$ zig test void_ignored.zig
1/2 test "void is ignored"... OK
2/2 test "explicitly ignoring expression value"... OK
All 2 tests passed.

```

#### Pointers to Zero Bit Types

Pointers to zero bit types also have zero bits. They always compare equal to each other:

**`pointers_to_zero_bits.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "pointer to empty struct" {
    const Empty = struct {};
    var a = Empty{};
    var b = Empty{};
    var ptr_a = &a;
    var ptr_b = &b;
    comptime try expect(ptr_a == ptr_b);
}

```

**Shell:**

```shell
$ zig test pointers_to_zero_bits.zig
1/1 test "pointer to empty struct"... OK
All 1 tests passed.

```

The type being pointed to can only ever be one value; therefore loads and stores are
never generated. [ptrToInt](#ptrToInt) and [intToPtr](#intToPtr) are not allowed:

**`test.zig`:**

```zig
const Empty = struct {};

test "@ptrToInt for pointer to zero bit type" {
    var a = Empty{};
    _ = @ptrToInt(&a);
}

test "@intToPtr for pointer to zero bit type" {
    _ = @intToPtr(*Empty, 0x1);
}

```

**Shell:**

```shell
$ zig test test.zig
./docgen_tmp/test.zig:4:5: error: pointer to size 0 type has no address
    var a = Empty{};
    ^
./docgen_tmp/test.zig:9:19: error: type '*Empty' has 0 bits and cannot store information
    _ = @intToPtr(*Empty, 0x1);
                  ^

```


---

### Result Location Semantics

[TODO add documentation for this](https://github.com/ziglang/zig/issues/2809)


---
