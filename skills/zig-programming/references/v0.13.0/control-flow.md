# Control Flow

*Program flow control structures and patterns*


---

### Blocks

Blocks are used to limit the scope of variable declarations:

**`test_blocks.zig`:**

```zig
test "access variable after block scope" {
    {
        var x: i32 = 1;
        _ = &x;
    }
    x += 1;
}

```

**Shell:**

```shell
$ zig test test_blocks.zig
doc/langref/test_blocks.zig:6:5: error: use of undeclared identifier 'x'
    x += 1;
    ^


```

Blocks are expressions. When labeled, `break` can be used
to return a value from the block:

**`test_labeled_break.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "labeled break from labeled block expression" {
    var y: i32 = 123;

    const x = blk: {
        y += 1;
        break :blk y;
    };
    try expect(x == 124);
    try expect(y == 124);
}

```

**Shell:**

```shell
$ zig test test_labeled_break.zig
1/1 test_labeled_break.test.labeled break from labeled block expression...OK
All 1 tests passed.

```

Here, `blk` can be any name.

See also:

- [Labeled while](#Labeled-while)
- [Labeled for](#Labeled-for)

#### Shadowing

[Identifiers](#Identifiers) are never allowed to "hide" other identifiers by using the same name:

**`test_shadowing.zig`:**

```zig
const pi = 3.14;

test "inside test block" {
    // Let's even go inside another block
    {
        var pi: i32 = 1234;
    }
}

```

**Shell:**

```shell
$ zig test test_shadowing.zig
doc/langref/test_shadowing.zig:6:13: error: local variable shadows declaration of 'pi'
        var pi: i32 = 1234;
            ^~
doc/langref/test_shadowing.zig:1:1: note: declared here
const pi = 3.14;
^~~~~~~~~~~~~~~


```

Because of this, when you read Zig code you can always rely on an identifier to consistently mean
the same thing within the scope it is defined. Note that you can, however, use the same name if
the scopes are separate:

**`test_scopes.zig`:**

```zig
test "separate scopes" {
    {
        const pi = 3.14;
        _ = pi;
    }
    {
        var pi: bool = true;
        _ = π
    }
}

```

**Shell:**

```shell
$ zig test test_scopes.zig
1/1 test_scopes.test.separate scopes...OK
All 1 tests passed.

```

#### Empty Blocks

An empty block is equivalent to `void{}`:

**`test_empty_block.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test {
    const a = {};
    const b = void{};
    try expect(@TypeOf(a) == void);
    try expect(@TypeOf(b) == void);
    try expect(a == b);
}

```

**Shell:**

```shell
$ zig test test_empty_block.zig
1/1 test_empty_block.test_0...OK
All 1 tests passed.

```


---

### switch

**`test_switch.zig`:**

```zig
const std = @import("std");
const builtin = @import("builtin");
const expect = std.testing.expect;

test "switch simple" {
    const a: u64 = 10;
    const zz: u64 = 103;

    // All branches of a switch expression must be able to be coerced to a
    // common type.
    //
    // Branches cannot fallthrough. If fallthrough behavior is desired, combine
    // the cases and use an if.
    const b = switch (a) {
        // Multiple cases can be combined via a ','
        1, 2, 3 => 0,

        // Ranges can be specified using the ... syntax. These are inclusive
        // of both ends.
        5...100 => 1,

        // Branches can be arbitrarily complex.
        101 => blk: {
            const c: u64 = 5;
            break :blk c * 2 + 1;
        },

        // Switching on arbitrary expressions is allowed as long as the
        // expression is known at compile-time.
        zz => zz,
        blk: {
            const d: u32 = 5;
            const e: u32 = 100;
            break :blk d + e;
        } => 107,

        // The else branch catches everything not already captured.
        // Else branches are mandatory unless the entire range of values
        // is handled.
        else => 9,
    };

    try expect(b == 1);
}

// Switch expressions can be used outside a function:
const os_msg = switch (builtin.target.os.tag) {
    .linux => "we found a linux user",
    else => "not a linux user",
};

// Inside a function, switch statements implicitly are compile-time
// evaluated if the target expression is compile-time known.
test "switch inside function" {
    switch (builtin.target.os.tag) {
        .fuchsia => {
            // On an OS other than fuchsia, block is not even analyzed,
            // so this compile error is not triggered.
            // On fuchsia this compile error would be triggered.
            @compileError("fuchsia not supported");
        },
        else => {},
    }
}

```

**Shell:**

```shell
$ zig test test_switch.zig
1/2 test_switch.test.switch simple...OK
2/2 test_switch.test.switch inside function...OK
All 2 tests passed.

```

`switch` can be used to capture the field values
of a [Tagged union](#Tagged-union). Modifications to the field values can be
done by placing a `*` before the capture variable name,
turning it into a pointer.

**`test_switch_tagged_union.zig`:**

```zig
const expect = @import("std").testing.expect;

test "switch on tagged union" {
    const Point = struct {
        x: u8,
        y: u8,
    };
    const Item = union(enum) {
        a: u32,
        c: Point,
        d,
        e: u32,
    };

    var a = Item{ .c = Point{ .x = 1, .y = 2 } };

    // Switching on more complex enums is allowed.
    const b = switch (a) {
        // A capture group is allowed on a match, and will return the enum
        // value matched. If the payload types of both cases are the same
        // they can be put into the same switch prong.
        Item.a, Item.e => |item| item,

        // A reference to the matched value can be obtained using `*` syntax.
        Item.c => |*item| blk: {
            item.*.x += 1;
            break :blk 6;
        },

        // No else is required if the types cases was exhaustively handled
        Item.d => 8,
    };

    try expect(b == 6);
    try expect(a.c.x == 2);
}

```

**Shell:**

```shell
$ zig test test_switch_tagged_union.zig
1/1 test_switch_tagged_union.test.switch on tagged union...OK
All 1 tests passed.

```

See also:

- [comptime](34-comptime.md#comptime)
- [enum](16-enum.md#enum)
- [@compileError](#compileError)
- [Compile Variables](43-compile-variables.md#Compile-Variables)

#### Exhaustive Switching

When a `switch` expression does not have an `else` clause,
it must exhaustively list all the possible values. Failure to do so is a compile error:

**`test_unhandled_enumeration_value.zig`:**

```zig
const Color = enum {
    auto,
    off,
    on,
};

test "exhaustive switching" {
    const color = Color.off;
    switch (color) {
        Color.auto => {},
        Color.on => {},
    }
}

```

**Shell:**

```shell
$ zig test test_unhandled_enumeration_value.zig
doc/langref/test_unhandled_enumeration_value.zig:9:5: error: switch must handle all possibilities
    switch (color) {
    ^~~~~~
doc/langref/test_unhandled_enumeration_value.zig:3:5: note: unhandled enumeration value: 'off'
    off,
    ^~~
doc/langref/test_unhandled_enumeration_value.zig:1:15: note: enum 'test_unhandled_enumeration_value.Color' declared here
const Color = enum {
              ^~~~


```

#### Switching with Enum Literals

[Enum Literals](#Enum-Literals) can be useful to use with `switch` to avoid
repetitively specifying [enum](16-enum.md#enum) or [union](17-union.md#union) types:

**`test_exhaustive_switch.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Color = enum {
    auto,
    off,
    on,
};

test "enum literals with switch" {
    const color = Color.off;
    const result = switch (color) {
        .auto => false,
        .on => false,
        .off => true,
    };
    try expect(result);
}

```

**Shell:**

```shell
$ zig test test_exhaustive_switch.zig
1/1 test_exhaustive_switch.test.enum literals with switch...OK
All 1 tests passed.

```

#### Inline Switch Prongs

Switch prongs can be marked as `inline` to generate
the prong's body for each possible value it could have, making the
captured value [comptime](34-comptime.md#comptime).

**`test_inline_switch.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;
const expectError = std.testing.expectError;

fn isFieldOptional(comptime T: type, field_index: usize) !bool {
    const fields = @typeInfo(T).Struct.fields;
    return switch (field_index) {
        // This prong is analyzed twice with `idx` being a
        // comptime-known value each time.
        inline 0, 1 => |idx| @typeInfo(fields[idx].type) == .Optional,
        else => return error.IndexOutOfBounds,
    };
}

const Struct1 = struct { a: u32, b: ?u32 };

test "using @typeInfo with runtime values" {
    var index: usize = 0;
    try expect(!try isFieldOptional(Struct1, index));
    index += 1;
    try expect(try isFieldOptional(Struct1, index));
    index += 1;
    try expectError(error.IndexOutOfBounds, isFieldOptional(Struct1, index));
}

// Calls to `isFieldOptional` on `Struct1` get unrolled to an equivalent
// of this function:
fn isFieldOptionalUnrolled(field_index: usize) !bool {
    return switch (field_index) {
        0 => false,
        1 => true,
        else => return error.IndexOutOfBounds,
    };
}

```

**Shell:**

```shell
$ zig test test_inline_switch.zig
1/1 test_inline_switch.test.using @typeInfo with runtime values...OK
All 1 tests passed.

```

The `inline` keyword may also be combined with ranges:

**`inline_prong_range.zig`:**

```zig
fn isFieldOptional(comptime T: type, field_index: usize) !bool {
    const fields = @typeInfo(T).Struct.fields;
    return switch (field_index) {
        inline 0...fields.len - 1 => |idx| @typeInfo(fields[idx].type) == .Optional,
        else => return error.IndexOutOfBounds,
    };
}

```

`inline else` prongs can be used as a type safe
alternative to `inline for` loops:

**`test_inline_else.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const SliceTypeA = extern struct {
    len: usize,
    ptr: [*]u32,
};
const SliceTypeB = extern struct {
    ptr: [*]SliceTypeA,
    len: usize,
};
const AnySlice = union(enum) {
    a: SliceTypeA,
    b: SliceTypeB,
    c: []const u8,
    d: []AnySlice,
};

fn withFor(any: AnySlice) usize {
    const Tag = @typeInfo(AnySlice).Union.tag_type.?;
    inline for (@typeInfo(Tag).Enum.fields) |field| {
        // With `inline for` the function gets generated as
        // a series of `if` statements relying on the optimizer
        // to convert it to a switch.
        if (field.value == @intFromEnum(any)) {
            return @field(any, field.name).len;
        }
    }
    // When using `inline for` the compiler doesn't know that every
    // possible case has been handled requiring an explicit `unreachable`.
    unreachable;
}

fn withSwitch(any: AnySlice) usize {
    return switch (any) {
        // With `inline else` the function is explicitly generated
        // as the desired switch and the compiler can check that
        // every possible case is handled.
        inline else => |slice| slice.len,
    };
}

test "inline for and inline else similarity" {
    const any = AnySlice{ .c = "hello" };
    try expect(withFor(any) == 5);
    try expect(withSwitch(any) == 5);
}

```

**Shell:**

```shell
$ zig test test_inline_else.zig
1/1 test_inline_else.test.inline for and inline else similarity...OK
All 1 tests passed.

```

When using an inline prong switching on an union an additional
capture can be used to obtain the union's enum tag value.

**`test_inline_switch_union_tag.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const U = union(enum) {
    a: u32,
    b: f32,
};

fn getNum(u: U) u32 {
    switch (u) {
        // Here `num` is a runtime-known value that is either
        // `u.a` or `u.b` and `tag` is `u`'s comptime-known tag value.
        inline else => |num, tag| {
            if (tag == .b) {
                return @intFromFloat(num);
            }
            return num;
        },
    }
}

test "test" {
    const u = U{ .b = 42 };
    try expect(getNum(u) == 42);
}

```

**Shell:**

```shell
$ zig test test_inline_switch_union_tag.zig
1/1 test_inline_switch_union_tag.test.test...OK
All 1 tests passed.

```

See also:

- [inline while](#inline-while)
- [inline for](#inline-for)


---

### while

A while loop is used to repeatedly execute an expression until
some condition is no longer true.

**`test_while.zig`:**

```zig
const expect = @import("std").testing.expect;

test "while basic" {
    var i: usize = 0;
    while (i < 10) {
        i += 1;
    }
    try expect(i == 10);
}

```

**Shell:**

```shell
$ zig test test_while.zig
1/1 test_while.test.while basic...OK
All 1 tests passed.

```

Use `break` to exit a while loop early.

**`test_while_break.zig`:**

```zig
const expect = @import("std").testing.expect;

test "while break" {
    var i: usize = 0;
    while (true) {
        if (i == 10)
            break;
        i += 1;
    }
    try expect(i == 10);
}

```

**Shell:**

```shell
$ zig test test_while_break.zig
1/1 test_while_break.test.while break...OK
All 1 tests passed.

```

Use `continue` to jump back to the beginning of the loop.

**`test_while_continue.zig`:**

```zig
const expect = @import("std").testing.expect;

test "while continue" {
    var i: usize = 0;
    while (true) {
        i += 1;
        if (i < 10)
            continue;
        break;
    }
    try expect(i == 10);
}

```

**Shell:**

```shell
$ zig test test_while_continue.zig
1/1 test_while_continue.test.while continue...OK
All 1 tests passed.

```

While loops support a continue expression which is executed when the loop
is continued. The `continue` keyword respects this expression.

**`test_while_continue_expression.zig`:**

```zig
const expect = @import("std").testing.expect;

test "while loop continue expression" {
    var i: usize = 0;
    while (i < 10) : (i += 1) {}
    try expect(i == 10);
}

test "while loop continue expression, more complicated" {
    var i: usize = 1;
    var j: usize = 1;
    while (i * j < 2000) : ({
        i *= 2;
        j *= 3;
    }) {
        const my_ij = i * j;
        try expect(my_ij < 2000);
    }
}

```

**Shell:**

```shell
$ zig test test_while_continue_expression.zig
1/2 test_while_continue_expression.test.while loop continue expression...OK
2/2 test_while_continue_expression.test.while loop continue expression, more complicated...OK
All 2 tests passed.

```

While loops are expressions. The result of the expression is the
result of the `else` clause of a while loop, which is executed when
the condition of the while loop is tested as false.

`break`, like `return`, accepts a value
parameter. This is the result of the `while` expression.
When you `break` from a while loop, the `else` branch is not
evaluated.

**`test_while_else.zig`:**

```zig
const expect = @import("std").testing.expect;

test "while else" {
    try expect(rangeHasNumber(0, 10, 5));
    try expect(!rangeHasNumber(0, 10, 15));
}

fn rangeHasNumber(begin: usize, end: usize, number: usize) bool {
    var i = begin;
    return while (i < end) : (i += 1) {
        if (i == number) {
            break true;
        }
    } else false;
}

```

**Shell:**

```shell
$ zig test test_while_else.zig
1/1 test_while_else.test.while else...OK
All 1 tests passed.

```

#### Labeled while

When a `while` loop is labeled, it can be referenced from a `break`
or `continue` from within a nested loop:

**`test_while_nested_break.zig`:**

```zig
test "nested break" {
    outer: while (true) {
        while (true) {
            break :outer;
        }
    }
}

test "nested continue" {
    var i: usize = 0;
    outer: while (i < 10) : (i += 1) {
        while (true) {
            continue :outer;
        }
    }
}

```

**Shell:**

```shell
$ zig test test_while_nested_break.zig
1/2 test_while_nested_break.test.nested break...OK
2/2 test_while_nested_break.test.nested continue...OK
All 2 tests passed.

```

#### while with Optionals

Just like [if](23-if.md#if) expressions, while loops can take an optional as the
condition and capture the payload. When [null](#null) is encountered the loop
exits.

When the `|x|` syntax is present on a `while` expression,
the while condition must have an [Optional Type](#Optional-Type).

The `else` branch is allowed on optional iteration. In this case, it will
be executed on the first null value encountered.

**`test_while_null_capture.zig`:**

```zig
const expect = @import("std").testing.expect;

test "while null capture" {
    var sum1: u32 = 0;
    numbers_left = 3;
    while (eventuallyNullSequence()) |value| {
        sum1 += value;
    }
    try expect(sum1 == 3);

    // null capture with an else block
    var sum2: u32 = 0;
    numbers_left = 3;
    while (eventuallyNullSequence()) |value| {
        sum2 += value;
    } else {
        try expect(sum2 == 3);
    }

    // null capture with a continue expression
    var i: u32 = 0;
    var sum3: u32 = 0;
    numbers_left = 3;
    while (eventuallyNullSequence()) |value| : (i += 1) {
        sum3 += value;
    }
    try expect(i == 3);
}

var numbers_left: u32 = undefined;
fn eventuallyNullSequence() ?u32 {
    return if (numbers_left == 0) null else blk: {
        numbers_left -= 1;
        break :blk numbers_left;
    };
}

```

**Shell:**

```shell
$ zig test test_while_null_capture.zig
1/1 test_while_null_capture.test.while null capture...OK
All 1 tests passed.

```

#### while with Error Unions

Just like [if](23-if.md#if) expressions, while loops can take an error union as
the condition and capture the payload or the error code. When the
condition results in an error code the else branch is evaluated and
the loop is finished.

When the `else |x|` syntax is present on a `while` expression,
the while condition must have an [Error Union Type](#Error-Union-Type).

**`test_while_error_capture.zig`:**

```zig
const expect = @import("std").testing.expect;

test "while error union capture" {
    var sum1: u32 = 0;
    numbers_left = 3;
    while (eventuallyErrorSequence()) |value| {
        sum1 += value;
    } else |err| {
        try expect(err == error.ReachedZero);
    }
}

var numbers_left: u32 = undefined;

fn eventuallyErrorSequence() anyerror!u32 {
    return if (numbers_left == 0) error.ReachedZero else blk: {
        numbers_left -= 1;
        break :blk numbers_left;
    };
}

```

**Shell:**

```shell
$ zig test test_while_error_capture.zig
1/1 test_while_error_capture.test.while error union capture...OK
All 1 tests passed.

```

#### inline while

While loops can be inlined. This causes the loop to be unrolled, which
allows the code to do some things which only work at compile time,
such as use types as first class values.

**`test_inline_while.zig`:**

```zig
const expect = @import("std").testing.expect;

test "inline while loop" {
    comptime var i = 0;
    var sum: usize = 0;
    inline while (i < 3) : (i += 1) {
        const T = switch (i) {
            0 => f32,
            1 => i8,
            2 => bool,
            else => unreachable,
        };
        sum += typeNameLength(T);
    }
    try expect(sum == 9);
}

fn typeNameLength(comptime T: type) usize {
    return @typeName(T).len;
}

```

**Shell:**

```shell
$ zig test test_inline_while.zig
1/1 test_inline_while.test.inline while loop...OK
All 1 tests passed.

```

It is recommended to use `inline` loops only for one of these reasons:

- You need the loop to execute at [comptime](34-comptime.md#comptime) for the semantics to work.
- You have a benchmark to prove that forcibly unrolling the loop in this way is measurably faster.

See also:

- [if](23-if.md#if)
- [Optionals](29-optionals.md#Optionals)
- [Errors](28-errors.md#Errors)
- [comptime](34-comptime.md#comptime)
- [unreachable](25-unreachable.md#unreachable)


---

### for

**`test_for.zig`:**

```zig
const expect = @import("std").testing.expect;

test "for basics" {
    const items = [_]i32{ 4, 5, 3, 4, 0 };
    var sum: i32 = 0;

    // For loops iterate over slices and arrays.
    for (items) |value| {
        // Break and continue are supported.
        if (value == 0) {
            continue;
        }
        sum += value;
    }
    try expect(sum == 16);

    // To iterate over a portion of a slice, reslice.
    for (items[0..1]) |value| {
        sum += value;
    }
    try expect(sum == 20);

    // To access the index of iteration, specify a second condition as well
    // as a second capture value.
    var sum2: i32 = 0;
    for (items, 0..) |_, i| {
        try expect(@TypeOf(i) == usize);
        sum2 += @as(i32, @intCast(i));
    }
    try expect(sum2 == 10);

    // To iterate over consecutive integers, use the range syntax.
    // Unbounded range is always a compile error.
    var sum3: usize = 0;
    for (0..5) |i| {
        sum3 += i;
    }
    try expect(sum3 == 10);
}

test "multi object for" {
    const items = [_]usize{ 1, 2, 3 };
    const items2 = [_]usize{ 4, 5, 6 };
    var count: usize = 0;

    // Iterate over multiple objects.
    // All lengths must be equal at the start of the loop, otherwise detectable
    // illegal behavior occurs.
    for (items, items2) |i, j| {
        count += i + j;
    }

    try expect(count == 21);
}

test "for reference" {
    var items = [_]i32{ 3, 4, 2 };

    // Iterate over the slice by reference by
    // specifying that the capture value is a pointer.
    for (&items) |*value| {
        value.* += 1;
    }

    try expect(items[0] == 4);
    try expect(items[1] == 5);
    try expect(items[2] == 3);
}

test "for else" {
    // For allows an else attached to it, the same as a while loop.
    const items = [_]?i32{ 3, 4, null, 5 };

    // For loops can also be used as expressions.
    // Similar to while loops, when you break from a for loop, the else branch is not evaluated.
    var sum: i32 = 0;
    const result = for (items) |value| {
        if (value != null) {
            sum += value.?;
        }
    } else blk: {
        try expect(sum == 12);
        break :blk sum;
    };
    try expect(result == 12);
}

```

**Shell:**

```shell
$ zig test test_for.zig
1/4 test_for.test.for basics...OK
2/4 test_for.test.multi object for...OK
3/4 test_for.test.for reference...OK
4/4 test_for.test.for else...OK
All 4 tests passed.

```

#### Labeled for

When a `for` loop is labeled, it can be referenced from a `break`
or `continue` from within a nested loop:

**`test_for_nested_break.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "nested break" {
    var count: usize = 0;
    outer: for (1..6) |_| {
        for (1..6) |_| {
            count += 1;
            break :outer;
        }
    }
    try expect(count == 1);
}

test "nested continue" {
    var count: usize = 0;
    outer: for (1..9) |_| {
        for (1..6) |_| {
            count += 1;
            continue :outer;
        }
    }

    try expect(count == 8);
}

```

**Shell:**

```shell
$ zig test test_for_nested_break.zig
1/2 test_for_nested_break.test.nested break...OK
2/2 test_for_nested_break.test.nested continue...OK
All 2 tests passed.

```

#### inline for

For loops can be inlined. This causes the loop to be unrolled, which
allows the code to do some things which only work at compile time,
such as use types as first class values.
The capture value and iterator value of inlined for loops are
compile-time known.

**`test_inline_for.zig`:**

```zig
const expect = @import("std").testing.expect;

test "inline for loop" {
    const nums = [_]i32{ 2, 4, 6 };
    var sum: usize = 0;
    inline for (nums) |i| {
        const T = switch (i) {
            2 => f32,
            4 => i8,
            6 => bool,
            else => unreachable,
        };
        sum += typeNameLength(T);
    }
    try expect(sum == 9);
}

fn typeNameLength(comptime T: type) usize {
    return @typeName(T).len;
}

```

**Shell:**

```shell
$ zig test test_inline_for.zig
1/1 test_inline_for.test.inline for loop...OK
All 1 tests passed.

```

It is recommended to use `inline` loops only for one of these reasons:

- You need the loop to execute at [comptime](34-comptime.md#comptime) for the semantics to work.
- You have a benchmark to prove that forcibly unrolling the loop in this way is measurably faster.

See also:

- [while](21-while.md#while)
- [comptime](34-comptime.md#comptime)
- [Arrays](11-arrays.md#Arrays)
- [Slices](14-slices.md#Slices)


---

### if

**`test_if.zig`:**

```zig
// If expressions have three uses, corresponding to the three types:
// * bool
// * ?T
// * anyerror!T

const expect = @import("std").testing.expect;

test "if expression" {
    // If expressions are used instead of a ternary expression.
    const a: u32 = 5;
    const b: u32 = 4;
    const result = if (a != b) 47 else 3089;
    try expect(result == 47);
}

test "if boolean" {
    // If expressions test boolean conditions.
    const a: u32 = 5;
    const b: u32 = 4;
    if (a != b) {
        try expect(true);
    } else if (a == 9) {
        unreachable;
    } else {
        unreachable;
    }
}

test "if error union" {
    // If expressions test for errors.
    // Note the |err| capture on the else.

    const a: anyerror!u32 = 0;
    if (a) |value| {
        try expect(value == 0);
    } else |err| {
        _ = err;
        unreachable;
    }

    const b: anyerror!u32 = error.BadValue;
    if (b) |value| {
        _ = value;
        unreachable;
    } else |err| {
        try expect(err == error.BadValue);
    }

    // The else and |err| capture is strictly required.
    if (a) |value| {
        try expect(value == 0);
    } else |_| {}

    // To check only the error value, use an empty block expression.
    if (b) |_| {} else |err| {
        try expect(err == error.BadValue);
    }

    // Access the value by reference using a pointer capture.
    var c: anyerror!u32 = 3;
    if (c) |*value| {
        value.* = 9;
    } else |_| {
        unreachable;
    }

    if (c) |value| {
        try expect(value == 9);
    } else |_| {
        unreachable;
    }
}

```

**Shell:**

```shell
$ zig test test_if.zig
1/3 test_if.test.if expression...OK
2/3 test_if.test.if boolean...OK
3/3 test_if.test.if error union...OK
All 3 tests passed.

```

#### if with Optionals

**`test_if_optionals.zig`:**

```zig
const expect = @import("std").testing.expect;

test "if optional" {
    // If expressions test for null.

    const a: ?u32 = 0;
    if (a) |value| {
        try expect(value == 0);
    } else {
        unreachable;
    }

    const b: ?u32 = null;
    if (b) |_| {
        unreachable;
    } else {
        try expect(true);
    }

    // The else is not required.
    if (a) |value| {
        try expect(value == 0);
    }

    // To test against null only, use the binary equality operator.
    if (b == null) {
        try expect(true);
    }

    // Access the value by reference using a pointer capture.
    var c: ?u32 = 3;
    if (c) |*value| {
        value.* = 2;
    }

    if (c) |value| {
        try expect(value == 2);
    } else {
        unreachable;
    }
}

test "if error union with optional" {
    // If expressions test for errors before unwrapping optionals.
    // The |optional_value| capture's type is ?u32.

    const a: anyerror!?u32 = 0;
    if (a) |optional_value| {
        try expect(optional_value.? == 0);
    } else |err| {
        _ = err;
        unreachable;
    }

    const b: anyerror!?u32 = null;
    if (b) |optional_value| {
        try expect(optional_value == null);
    } else |_| {
        unreachable;
    }

    const c: anyerror!?u32 = error.BadValue;
    if (c) |optional_value| {
        _ = optional_value;
        unreachable;
    } else |err| {
        try expect(err == error.BadValue);
    }

    // Access the value by reference by using a pointer capture each time.
    var d: anyerror!?u32 = 3;
    if (d) |*optional_value| {
        if (optional_value.*) |*value| {
            value.* = 9;
        }
    } else |_| {
        unreachable;
    }

    if (d) |optional_value| {
        try expect(optional_value.? == 9);
    } else |_| {
        unreachable;
    }
}

```

**Shell:**

```shell
$ zig test test_if_optionals.zig
1/2 test_if_optionals.test.if optional...OK
2/2 test_if_optionals.test.if error union with optional...OK
All 2 tests passed.

```

See also:

- [Optionals](29-optionals.md#Optionals)
- [Errors](28-errors.md#Errors)


---

### defer

Executes an expression unconditionally at scope exit.

**`test_defer.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;
const print = std.debug.print;

fn deferExample() !usize {
    var a: usize = 1;

    {
        defer a = 2;
        a = 1;
    }
    try expect(a == 2);

    a = 5;
    return a;
}

test "defer basics" {
    try expect((try deferExample()) == 5);
}

```

**Shell:**

```shell
$ zig test test_defer.zig
1/1 test_defer.test.defer basics...OK
All 1 tests passed.

```

Defer expressions are evaluated in reverse order.

**`defer_unwind.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;
const print = std.debug.print;

test "defer unwinding" {
    print("\n", .{});

    defer {
        print("1 ", .{});
    }
    defer {
        print("2 ", .{});
    }
    if (false) {
        // defers are not run if they are never executed.
        defer {
            print("3 ", .{});
        }
    }
}

```

**Shell:**

```shell
$ zig test defer_unwind.zig
1/1 defer_unwind.test.defer unwinding...
2 1 OK
All 1 tests passed.

```

Inside a defer expression the return statement is not allowed.

**`test_invalid_defer.zig`:**

```zig
fn deferInvalidExample() !void {
    defer {
        return error.DeferError;
    }

    return error.DeferError;
}

```

**Shell:**

```shell
$ zig test test_invalid_defer.zig
doc/langref/test_invalid_defer.zig:3:9: error: cannot return from defer expression
        return error.DeferError;
        ^~~~~~~~~~~~~~~~~~~~~~~
doc/langref/test_invalid_defer.zig:2:5: note: defer expression here
    defer {
    ^~~~~


```

See also:

- [Errors](28-errors.md#Errors)


---
