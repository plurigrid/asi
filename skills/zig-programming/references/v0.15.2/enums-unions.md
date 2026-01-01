# Enums and Unions

*Tagged unions, enums, and variant types in Zig*


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
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/enum_export_error.zig:2:17: error: parameter of type 'enum_export_error.Foo' not allowed in function with calling convention 'x86_64_sysv'
export fn entry(foo: Foo) void {
                ^~~~~~~~
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/enum_export_error.zig:2:17: note: enum tag type 'u2' is not extern compatible
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/enum_export_error.zig:2:17: note: only integers with 0, 8, 16, 32, 64 and 128 bits are extern compatible
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/enum_export_error.zig:1:13: note: enum declared here
const Foo = enum { a, b, c };
            ^~~~~~~~~~~~~~~~
referenced by:
    root: /home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:3:22
    comptime: /home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:31:9
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


---

### union

A bare `union` defines a set of possible types that a value
can be as a list of fields. Only one field can be active at a time.
The in-memory representation of bare unions is not guaranteed.
Bare unions cannot be used to reinterpret memory. For that, use [@ptrCast](#ptrCast),
or use an [extern union](#extern-union) or a [packed union](#packed-union) which have
guaranteed in-memory layout.
[Accessing the non-active field](#Wrong-Union-Field-Access) is
safety-checked [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior):

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
1/1 test_wrong_union_access.test.simple union...thread 1783514 panic: access of union field 'float' while field 'int' is active
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_wrong_union_access.zig:8:12: 0x1032042 in test.simple union (test_wrong_union_access.zig)
    payload.float = 12.34;
           ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/compiler/test_runner.zig:248:25: 0x1175cb9 in mainTerminal (test_runner.zig)
        if (test_fn.func()) |_| {
                        ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/compiler/test_runner.zig:71:28: 0x116f8aa in main (test_runner.zig)
        return mainTerminal();
                           ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:687:22: 0x116ae67 in callMain (std.zig)
            root.main();
                     ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:237:5: 0x116a941 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
error: the following test command crashed:
/home/ci/actions-runner/_work/zig-bootstrap/out/zig-local-cache/o/17f0a7af60a8362172795bb02bbf580e/test --seed=0xb30b714f

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

To initialize a union when the tag is a [comptime](33-comptime.md#comptime)-known name, see [@unionInit](#unionInit).

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

Unions with inferred enum tag types can also assign ordinal values to their inferred tag.
This requires the tag to specify an explicit integer type.
[@intFromEnum](#intFromEnum) can be used to access the ordinal value corresponding to the active field.

**`test_tagged_union_with_tag_values.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Tagged = union(enum(u32)) {
    int: i64 = 123,
    boolean: bool = 67,
};

test "tag values" {
    const int: Tagged = .{ .int = -40 };
    try expect(@intFromEnum(int) == 123);

    const boolean: Tagged = .{ .boolean = false };
    try expect(@intFromEnum(boolean) == 67);
}

```

**Shell:**

```shell
$ zig test test_tagged_union_with_tag_values.zig
1/1 test_tagged_union_with_tag_values.test.tag values...OK
All 1 tests passed.

```

[@tagName](#tagName) can be used to return a [comptime](33-comptime.md#comptime)
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

All fields in a packed union must have the same [@bitSizeOf](#bitSizeOf).

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
fn foo(w: *Wat) callconv(.c) void {
    bar(w);
}

test "call foo" {
    foo(undefined);
}

```

**Shell:**

```shell
$ zig test test_opaque.zig
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_opaque.zig:6:9: error: expected type '*test_opaque.Derp', found '*test_opaque.Wat'
    bar(w);
        ^
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_opaque.zig:6:9: note: pointer type child 'test_opaque.Wat' cannot cast into pointer type child 'test_opaque.Derp'
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_opaque.zig:2:13: note: opaque declared here
const Wat = opaque {};
            ^~~~~~~~~
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_opaque.zig:1:14: note: opaque declared here
const Derp = opaque {};
             ^~~~~~~~~
/home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_opaque.zig:4:18: note: parameter type declared here
extern fn bar(d: *Derp) void;
                 ^~~~~
referenced by:
    test.call foo: /home/ci/actions-runner/_work/zig-bootstrap/zig/doc/langref/test_opaque.zig:10:8


```


---


---
