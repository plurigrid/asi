# Functions and Error Handling

*Function design, error handling patterns, and type conversions*


---

### unreachable

In [Debug](#Debug) and [ReleaseSafe](#ReleaseSafe) mode
`unreachable` emits a call to `panic` with the message `reached unreachable code`.

In [ReleaseFast](#ReleaseFast) and [ReleaseSmall](#ReleaseSmall) mode, the optimizer uses the assumption that `unreachable` code
will never be hit to perform optimizations.

#### Basics

**`test_unreachable.zig`:**

```zig
// unreachable is used to assert that control flow will never reach a
// particular location:
test "basic math" {
    const x = 1;
    const y = 2;
    if (x + y != 3) {
        unreachable;
    }
}

```

**Shell:**

```shell
$ zig test test_unreachable.zig
1/1 test_unreachable.test.basic math...OK
All 1 tests passed.

```

In fact, this is how `std.debug.assert` is implemented:

**`test_assertion_failure.zig`:**

```zig
// This is how std.debug.assert is implemented
fn assert(ok: bool) void {
    if (!ok) unreachable; // assertion failure
}

// This test will fail because we hit unreachable.
test "this will fail" {
    assert(false);
}

```

**Shell:**

```shell
$ zig test test_assertion_failure.zig
1/1 test_assertion_failure.test.this will fail...thread 209597 panic: reached unreachable code
/home/andy/dev/zig/doc/langref/test_assertion_failure.zig:3:14: 0x104892d in assert (test)
    if (!ok) unreachable; // assertion failure
             ^
/home/andy/dev/zig/doc/langref/test_assertion_failure.zig:8:11: 0x10488fa in test.this will fail (test)
    assert(false);
          ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:214:25: 0x10ef0c5 in mainTerminal (test)
        if (test_fn.func()) |_| {
                        ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:62:28: 0x10e74ad in main (test)
        return mainTerminal();
                           ^
/home/andy/dev/zig/lib/std/start.zig:651:22: 0x10e6922 in posixCallMainAndExit (test)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:271:5: 0x10e64fd in _start (test)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
error: the following test command crashed:
/home/andy/dev/zig/.zig-cache/o/0594f73810636b148c5e4293efd1faf6/test --seed=0x2a37766c

```

#### At Compile-Time

**`test_comptime_unreachable.zig`:**

```zig
const assert = @import("std").debug.assert;

test "type of unreachable" {
    comptime {
        // The type of unreachable is noreturn.

        // However this assertion will still fail to compile because
        // unreachable expressions are compile errors.

        assert(@TypeOf(unreachable) == noreturn);
    }
}

```

**Shell:**

```shell
$ zig test test_comptime_unreachable.zig
/home/andy/dev/zig/doc/langref/test_comptime_unreachable.zig:10:16: error: unreachable code
        assert(@TypeOf(unreachable) == noreturn);
               ^~~~~~~~~~~~~~~~~~~~
/home/andy/dev/zig/doc/langref/test_comptime_unreachable.zig:10:24: note: control flow is diverted here
        assert(@TypeOf(unreachable) == noreturn);
                       ^~~~~~~~~~~


```

See also:

- [Zig Test](06-zig-test.md#Zig-Test)
- [Build Mode](39-build-mode.md#Build-Mode)
- [comptime](34-comptime.md#comptime)


---

### noreturn

`noreturn` is the type of:

- `break`
- `continue`
- `return`
- `unreachable`
- `while (true) {}`

When resolving types together, such as `if` clauses or `switch` prongs,
the `noreturn` type is compatible with every other type. Consider:

**`test_noreturn.zig`:**

```zig
fn foo(condition: bool, b: u32) void {
    const a = if (condition) b else return;
    _ = a;
    @panic("do something with a");
}
test "noreturn" {
    foo(false, 1);
}

```

**Shell:**

```shell
$ zig test test_noreturn.zig
1/1 test_noreturn.test.noreturn...OK
All 1 tests passed.

```

Another use case for `noreturn` is the `exit` function:

**`test_noreturn_from_exit.zig`:**

```zig
const std = @import("std");
const builtin = @import("builtin");
const native_arch = builtin.cpu.arch;
const expect = std.testing.expect;

const WINAPI: std.builtin.CallingConvention = if (native_arch == .x86) .Stdcall else .C;
extern "kernel32" fn ExitProcess(exit_code: c_uint) callconv(WINAPI) noreturn;

test "foo" {
    const value = bar() catch ExitProcess(1);
    try expect(value == 1234);
}

fn bar() anyerror!u32 {
    return 1234;
}

```

**Shell:**

```shell
$ zig test test_noreturn_from_exit.zig -target x86_64-windows --test-no-exec

```


---

### Functions

**`test_functions.zig`:**

```zig
const std = @import("std");
const builtin = @import("builtin");
const native_arch = builtin.cpu.arch;
const expect = std.testing.expect;

// Functions are declared like this
fn add(a: i8, b: i8) i8 {
    if (a == 0) {
        return b;
    }

    return a + b;
}

// The export specifier makes a function externally visible in the generated
// object file, and makes it use the C ABI.
export fn sub(a: i8, b: i8) i8 {
    return a - b;
}

// The extern specifier is used to declare a function that will be resolved
// at link time, when linking statically, or at runtime, when linking
// dynamically. The quoted identifier after the extern keyword specifies
// the library that has the function. (e.g. "c" -> libc.so)
// The callconv specifier changes the calling convention of the function.
const WINAPI: std.builtin.CallingConvention = if (native_arch == .x86) .Stdcall else .C;
extern "kernel32" fn ExitProcess(exit_code: u32) callconv(WINAPI) noreturn;
extern "c" fn atan2(a: f64, b: f64) f64;

// The @branchHint builtin can be used to tell the optimizer that a function is rarely called ("cold").
fn abort() noreturn {
    @branchHint(.cold);
    while (true) {}
}

// The naked calling convention makes a function not have any function prologue or epilogue.
// This can be useful when integrating with assembly.
fn _start() callconv(.Naked) noreturn {
    abort();
}

// The inline calling convention forces a function to be inlined at all call sites.
// If the function cannot be inlined, it is a compile-time error.
inline fn shiftLeftOne(a: u32) u32 {
    return a << 1;
}

// The pub specifier allows the function to be visible when importing.
// Another file can use @import and call sub2
pub fn sub2(a: i8, b: i8) i8 {
    return a - b;
}

// Function pointers are prefixed with `*const `.
const Call2Op = *const fn (a: i8, b: i8) i8;
fn doOp(fnCall: Call2Op, op1: i8, op2: i8) i8 {
    return fnCall(op1, op2);
}

test "function" {
    try expect(doOp(add, 5, 6) == 11);
    try expect(doOp(sub2, 5, 6) == -1);
}

```

**Shell:**

```shell
$ zig test test_functions.zig
1/1 test_functions.test.function...OK
All 1 tests passed.

```

There is a difference between a function *body* and a function *pointer*.
Function bodies are [comptime](34-comptime.md#comptime)-only types while function [Pointers](13-pointers.md#Pointers) may be
runtime-known.

#### Pass-by-value Parameters

Primitive types such as [Integers](08-integers.md#Integers) and [Floats](09-floats.md#Floats) passed as parameters
are copied, and then the copy is available in the function body. This is called "passing by value".
Copying a primitive type is essentially free and typically involves nothing more than
setting a register.

Structs, unions, and arrays can sometimes be more efficiently passed as a reference, since a copy
could be arbitrarily expensive depending on the size. When these types are passed
as parameters, Zig may choose to copy and pass by value, or pass by reference, whichever way
Zig decides will be faster. This is made possible, in part, by the fact that parameters are immutable.

**`test_pass_by_reference_or_value.zig`:**

```zig
const Point = struct {
    x: i32,
    y: i32,
};

fn foo(point: Point) i32 {
    // Here, `point` could be a reference, or a copy. The function body
    // can ignore the difference and treat it as a value. Be very careful
    // taking the address of the parameter - it should be treated as if
    // the address will become invalid when the function returns.
    return point.x + point.y;
}

const expect = @import("std").testing.expect;

test "pass struct to function" {
    try expect(foo(Point{ .x = 1, .y = 2 }) == 3);
}

```

**Shell:**

```shell
$ zig test test_pass_by_reference_or_value.zig
1/1 test_pass_by_reference_or_value.test.pass struct to function...OK
All 1 tests passed.

```

For extern functions, Zig follows the C ABI for passing structs and unions by value.

#### Function Parameter Type Inference

Function parameters can be declared with `anytype` in place of the type.
In this case the parameter types will be inferred when the function is called.
Use [@TypeOf](#TypeOf) and [@typeInfo](#typeInfo) to get information about the inferred type.

**`test_fn_type_inference.zig`:**

```zig
const expect = @import("std").testing.expect;

fn addFortyTwo(x: anytype) @TypeOf(x) {
    return x + 42;
}

test "fn type inference" {
    try expect(addFortyTwo(1) == 43);
    try expect(@TypeOf(addFortyTwo(1)) == comptime_int);
    const y: i64 = 2;
    try expect(addFortyTwo(y) == 44);
    try expect(@TypeOf(addFortyTwo(y)) == i64);
}

```

**Shell:**

```shell
$ zig test test_fn_type_inference.zig
1/1 test_fn_type_inference.test.fn type inference...OK
All 1 tests passed.

```

#### inline fn

Adding the `inline` keyword to a function definition makes that
function become *semantically inlined* at the callsite. This is
not a hint to be possibly observed by optimization passes, but has
implications on the types and values involved in the function call.

Unlike normal function calls, arguments at an inline function callsite which are
compile-time known are treated as [Compile Time Parameters](46-c.md#Compile-Time-Parameters). This can potentially
propagate all the way to the return value:

**`inline_call.zig`:**

```zig
test "inline function call" {
    if (foo(1200, 34) != 1234) {
        @compileError("bad");
    }
}

inline fn foo(a: i32, b: i32) i32 {
    return a + b;
}

```

**Shell:**

```shell
$ zig test inline_call.zig
1/1 inline_call.test.inline function call...OK
All 1 tests passed.

```

If `inline` is removed, the test fails with the compile error
instead of passing.

It is generally better to let the compiler decide when to inline a
function, except for these scenarios:

- To change how many stack frames are in the call stack, for debugging purposes.
- To force comptime-ness of the arguments to propagate to the return value of the function, as in the above example.
- Real world performance measurements demand it.

Note that `inline` actually *restricts*
what the compiler is allowed to do. This can harm binary size,
compilation speed, and even runtime performance.

#### Function Reflection

**`test_fn_reflection.zig`:**

```zig
const std = @import("std");
const math = std.math;
const testing = std.testing;

test "fn reflection" {
    try testing.expect(@typeInfo(@TypeOf(testing.expect)).@"fn".params[0].type.? == bool);
    try testing.expect(@typeInfo(@TypeOf(testing.tmpDir)).@"fn".return_type.? == testing.TmpDir);

    try testing.expect(@typeInfo(@TypeOf(math.Log2Int)).@"fn".is_generic);
}

```

**Shell:**

```shell
$ zig test test_fn_reflection.zig
1/1 test_fn_reflection.test.fn reflection...OK
All 1 tests passed.

```


---

### Errors

#### Error Set Type

An error set is like an [enum](16-enum.md#enum).
However, each error name across the entire compilation gets assigned an unsigned integer
greater than 0. You are allowed to declare the same error name more than once, and if you do, it
gets assigned the same integer value.

The error set type defaults to a `u16`, though if the maximum number of distinct
error values is provided via the `--error-limit [num]` command line parameter an integer type
with the minimum number of bits required to represent all of the error values will be used.

You can [coerce](#Type-Coercion) an error from a subset to a superset:

**`test_coerce_error_subset_to_superset.zig`:**

```zig
const std = @import("std");

const FileOpenError = error{
    AccessDenied,
    OutOfMemory,
    FileNotFound,
};

const AllocationError = error{
    OutOfMemory,
};

test "coerce subset to superset" {
    const err = foo(AllocationError.OutOfMemory);
    try std.testing.expect(err == FileOpenError.OutOfMemory);
}

fn foo(err: AllocationError) FileOpenError {
    return err;
}

```

**Shell:**

```shell
$ zig test test_coerce_error_subset_to_superset.zig
1/1 test_coerce_error_subset_to_superset.test.coerce subset to superset...OK
All 1 tests passed.

```

But you cannot [coerce](#Type-Coercion) an error from a superset to a subset:

**`test_coerce_error_superset_to_subset.zig`:**

```zig
const FileOpenError = error{
    AccessDenied,
    OutOfMemory,
    FileNotFound,
};

const AllocationError = error{
    OutOfMemory,
};

test "coerce superset to subset" {
    foo(FileOpenError.OutOfMemory) catch {};
}

fn foo(err: FileOpenError) AllocationError {
    return err;
}

```

**Shell:**

```shell
$ zig test test_coerce_error_superset_to_subset.zig
/home/andy/dev/zig/doc/langref/test_coerce_error_superset_to_subset.zig:16:12: error: expected type 'error{OutOfMemory}', found 'error{AccessDenied,OutOfMemory,FileNotFound}'
    return err;
           ^~~
/home/andy/dev/zig/doc/langref/test_coerce_error_superset_to_subset.zig:16:12: note: 'error.AccessDenied' not a member of destination error set
/home/andy/dev/zig/doc/langref/test_coerce_error_superset_to_subset.zig:16:12: note: 'error.FileNotFound' not a member of destination error set
/home/andy/dev/zig/doc/langref/test_coerce_error_superset_to_subset.zig:15:28: note: function return type declared here
fn foo(err: FileOpenError) AllocationError {
                           ^~~~~~~~~~~~~~~
referenced by:
    test.coerce superset to subset: /home/andy/dev/zig/doc/langref/test_coerce_error_superset_to_subset.zig:12:8


```

There is a shortcut for declaring an error set with only 1 value, and then getting that value:

**`single_value_error_set_shortcut.zig`:**

```zig
const err = error.FileNotFound;

```

This is equivalent to:

**`single_value_error_set.zig`:**

```zig
const err = (error{FileNotFound}).FileNotFound;

```

This becomes useful when using [Inferred Error Sets](#Inferred-Error-Sets).

##### The Global Error Set

`anyerror` refers to the global error set.
This is the error set that contains all errors in the entire compilation unit, i.e. it is the union of all other error sets.

You can [coerce](#Type-Coercion) any error set to the global one, and you can explicitly
cast an error of the global error set to a non-global one. This inserts a language-level
assert to make sure the error value is in fact in the destination error set.

The global error set should generally be avoided because it prevents the
compiler from knowing what errors are possible at compile-time. Knowing
the error set at compile-time is better for generated documentation and
helpful error messages, such as forgetting a possible error value in a [switch](20-switch.md#switch).

#### Error Union Type

An error set type and normal type can be combined with the `!`
binary operator to form an error union type. You are likely to use an
error union type more often than an error set type by itself.

Here is a function to parse a string into a 64-bit integer:

**`error_union_parsing_u64.zig`:**

```zig
const std = @import("std");
const maxInt = std.math.maxInt;

pub fn parseU64(buf: []const u8, radix: u8) !u64 {
    var x: u64 = 0;

    for (buf) |c| {
        const digit = charToDigit(c);

        if (digit >= radix) {
            return error.InvalidChar;
        }

        // x *= radix
        var ov = @mulWithOverflow(x, radix);
        if (ov[1] != 0) return error.OverFlow;

        // x += digit
        ov = @addWithOverflow(ov[0], digit);
        if (ov[1] != 0) return error.OverFlow;
        x = ov[0];
    }

    return x;
}

fn charToDigit(c: u8) u8 {
    return switch (c) {
        '0'...'9' => c - '0',
        'A'...'Z' => c - 'A' + 10,
        'a'...'z' => c - 'a' + 10,
        else => maxInt(u8),
    };
}

test "parse u64" {
    const result = try parseU64("1234", 10);
    try std.testing.expect(result == 1234);
}

```

**Shell:**

```shell
$ zig test error_union_parsing_u64.zig
1/1 error_union_parsing_u64.test.parse u64...OK
All 1 tests passed.

```

Notice the return type is `!u64`. This means that the function
either returns an unsigned 64 bit integer, or an error. We left off the error set
to the left of the `!`, so the error set is inferred.

Within the function definition, you can see some return statements that return
an error, and at the bottom a return statement that returns a `u64`.
Both types [coerce](#Type-Coercion) to `anyerror!u64`.

What it looks like to use this function varies depending on what you're
trying to do. One of the following:

- You want to provide a default value if it returned an error.
- If it returned an error then you want to return the same error.
- You know with complete certainty it will not return an error, so want to unconditionally unwrap it.
- You want to take a different action for each possible error.

##### catch

If you want to provide a default value, you can use the `catch` binary operator:

**`catch.zig`:**

```zig
const parseU64 = @import("error_union_parsing_u64.zig").parseU64;

fn doAThing(str: []u8) void {
    const number = parseU64(str, 10) catch 13;
    _ = number; // ...
}

```

In this code, `number` will be equal to the successfully parsed string, or
a default value of 13. The type of the right hand side of the binary `catch` operator must
match the unwrapped error union type, or be of type `noreturn`.

If you want to provide a default value with
`catch` after performing some logic, you
can combine `catch` with named [Blocks](19-blocks.md#Blocks):

**`handle_error_with_catch_block.zig.zig`:**

```zig
const parseU64 = @import("error_union_parsing_u64.zig").parseU64;

fn doAThing(str: []u8) void {
    const number = parseU64(str, 10) catch blk: {
        // do things
        break :blk 13;
    };
    _ = number; // number is now initialized
}

```

##### try

Let's say you wanted to return the error if you got one, otherwise continue with the
function logic:

**`catch_err_return.zig`:**

```zig
const parseU64 = @import("error_union_parsing_u64.zig").parseU64;

fn doAThing(str: []u8) !void {
    const number = parseU64(str, 10) catch |err| return err;
    _ = number; // ...
}

```

There is a shortcut for this. The `try` expression:

**`try.zig`:**

```zig
const parseU64 = @import("error_union_parsing_u64.zig").parseU64;

fn doAThing(str: []u8) !void {
    const number = try parseU64(str, 10);
    _ = number; // ...
}

```

`try` evaluates an error union expression. If it is an error, it returns
from the current function with the same error. Otherwise, the expression results in
the unwrapped value.

Maybe you know with complete certainty that an expression will never be an error.
In this case you can do this:

`const number = parseU64("1234", 10) catch unreachable;`

Here we know for sure that "1234" will parse successfully. So we put the
`unreachable` value on the right hand side.
`unreachable` invokes safety-checked [Illegal Behavior](41-illegal-behavior.md#Illegal-Behavior), so
in [Debug](#Debug) and [ReleaseSafe](#ReleaseSafe), triggers a safety panic by default. So, while
we're debugging the application, if there *was* a surprise error here, the application
would crash appropriately.

You may want to take a different action for every situation. For that, we combine
the [if](23-if.md#if) and [switch](20-switch.md#switch) expression:

**`handle_all_error_scenarios.zig`:**

```zig
fn doAThing(str: []u8) void {
    if (parseU64(str, 10)) |number| {
        doSomethingWithNumber(number);
    } else |err| switch (err) {
        error.Overflow => {
            // handle overflow...
        },
        // we promise that InvalidChar won't happen (or crash in debug mode if it does)
        error.InvalidChar => unreachable,
    }
}

```

Finally, you may want to handle only some errors. For that, you can capture the unhandled
errors in the `else` case, which now contains a narrower error set:

**`handle_some_error_scenarios.zig`:**

```zig
fn doAnotherThing(str: []u8) error{InvalidChar}!void {
    if (parseU64(str, 10)) |number| {
        doSomethingWithNumber(number);
    } else |err| switch (err) {
        error.Overflow => {
            // handle overflow...
        },
        else => |leftover_err| return leftover_err,
    }
}

```

You must use the variable capture syntax. If you don't need the
variable, you can capture with `_` and avoid the
`switch`.

**`handle_no_error_scenarios.zig`:**

```zig
fn doADifferentThing(str: []u8) void {
    if (parseU64(str, 10)) |number| {
        doSomethingWithNumber(number);
    } else |_| {
        // do as you'd like
    }
}

```

##### errdefer

The other component to error handling is defer statements.
In addition to an unconditional [defer](24-defer.md#defer), Zig has `errdefer`,
which evaluates the deferred expression on block exit path if and only if
the function returned with an error from the block.

Example:

**`errdefer_example.zig`:**

```zig
fn createFoo(param: i32) !Foo {
    const foo = try tryToAllocateFoo();
    // now we have allocated foo. we need to free it if the function fails.
    // but we want to return it if the function succeeds.
    errdefer deallocateFoo(foo);

    const tmp_buf = allocateTmpBuffer() orelse return error.OutOfMemory;
    // tmp_buf is truly a temporary resource, and we for sure want to clean it up
    // before this block leaves scope
    defer deallocateTmpBuffer(tmp_buf);

    if (param > 1337) return error.InvalidParam;

    // here the errdefer will not run since we're returning success from the function.
    // but the defer will run!
    return foo;
}

```

The neat thing about this is that you get robust error handling without
the verbosity and cognitive overhead of trying to make sure every exit path
is covered. The deallocation code is always directly following the allocation code.

The `errdefer` statement can optionally capture the error:

**`test_errdefer_capture.zig`:**

```zig
const std = @import("std");

fn captureError(captured: *?anyerror) !void {
    errdefer |err| {
        captured.* = err;
    }
    return error.GeneralFailure;
}

test "errdefer capture" {
    var captured: ?anyerror = null;

    if (captureError(&captured)) unreachable else |err| {
        try std.testing.expectEqual(error.GeneralFailure, captured.?);
        try std.testing.expectEqual(error.GeneralFailure, err);
    }
}

```

**Shell:**

```shell
$ zig test test_errdefer_capture.zig
1/1 test_errdefer_capture.test.errdefer capture...OK
All 1 tests passed.

```

A couple of other tidbits about error handling:

- These primitives give enough expressiveness that it's completely practical
  to have failing to check for an error be a compile error. If you really want
  to ignore the error, you can add `catch unreachable` and
  get the added benefit of crashing in Debug and ReleaseSafe modes if your assumption was wrong.
- Since Zig understands error types, it can pre-weight branches in favor of
  errors not occurring. Just a small optimization benefit that is not available
  in other languages.

See also:

- [defer](24-defer.md#defer)
- [if](23-if.md#if)
- [switch](20-switch.md#switch)

An error union is created with the `!` binary operator.
You can use compile-time reflection to access the child type of an error union:

**`test_error_union.zig`:**

```zig
const expect = @import("std").testing.expect;

test "error union" {
    var foo: anyerror!i32 = undefined;

    // Coerce from child type of an error union:
    foo = 1234;

    // Coerce from an error set:
    foo = error.SomeError;

    // Use compile-time reflection to access the payload type of an error union:
    try comptime expect(@typeInfo(@TypeOf(foo)).error_union.payload == i32);

    // Use compile-time reflection to access the error set type of an error union:
    try comptime expect(@typeInfo(@TypeOf(foo)).error_union.error_set == anyerror);
}

```

**Shell:**

```shell
$ zig test test_error_union.zig
1/1 test_error_union.test.error union...OK
All 1 tests passed.

```

##### Merging Error Sets

Use the `||` operator to merge two error sets together. The resulting
error set contains the errors of both error sets. Doc comments from the left-hand
side override doc comments from the right-hand side. In this example, the doc
comments for `C.PathNotFound` is `A doc comment`.

This is especially useful for functions which return different error sets depending
on [comptime](34-comptime.md#comptime) branches. For example, the Zig standard library uses
`LinuxFileOpenError || WindowsFileOpenError` for the error set of opening
files.

**`test_merging_error_sets.zig`:**

```zig
const A = error{
    NotDir,

    /// A doc comment
    PathNotFound,
};
const B = error{
    OutOfMemory,

    /// B doc comment
    PathNotFound,
};

const C = A || B;

fn foo() C!void {
    return error.NotDir;
}

test "merge error sets" {
    if (foo()) {
        @panic("unexpected");
    } else |err| switch (err) {
        error.OutOfMemory => @panic("unexpected"),
        error.PathNotFound => @panic("unexpected"),
        error.NotDir => {},
    }
}

```

**Shell:**

```shell
$ zig test test_merging_error_sets.zig
1/1 test_merging_error_sets.test.merge error sets...OK
All 1 tests passed.

```

##### Inferred Error Sets

Because many functions in Zig return a possible error, Zig supports inferring the error set.
To infer the error set for a function, prepend the `!` operator to the functionâs return type, like `!T`:

**`test_inferred_error_sets.zig`:**

```zig
// With an inferred error set
pub fn add_inferred(comptime T: type, a: T, b: T) !T {
    const ov = @addWithOverflow(a, b);
    if (ov[1] != 0) return error.Overflow;
    return ov[0];
}

// With an explicit error set
pub fn add_explicit(comptime T: type, a: T, b: T) Error!T {
    const ov = @addWithOverflow(a, b);
    if (ov[1] != 0) return error.Overflow;
    return ov[0];
}

const Error = error{
    Overflow,
};

const std = @import("std");

test "inferred error set" {
    if (add_inferred(u8, 255, 1)) |_| unreachable else |err| switch (err) {
        error.Overflow => {}, // ok
    }
}

```

**Shell:**

```shell
$ zig test test_inferred_error_sets.zig
1/1 test_inferred_error_sets.test.inferred error set...OK
All 1 tests passed.

```

When a function has an inferred error set, that function becomes generic and thus it becomes
trickier to do certain things with it, such as obtain a function pointer, or have an error
set that is consistent across different build targets. Additionally, inferred error sets
are incompatible with recursion.

In these situations, it is recommended to use an explicit error set. You can generally start
with an empty error set and let compile errors guide you toward completing the set.

These limitations may be overcome in a future version of Zig.

#### Error Return Traces

Error Return Traces show all the points in the code that an error was returned to the calling function. This makes it practical to use [try](#try) everywhere and then still be able to know what happened if an error ends up bubbling all the way out of your application.

**`error_return_trace.zig`:**

```zig
pub fn main() !void {
    try foo(12);
}

fn foo(x: i32) !void {
    if (x >= 5) {
        try bar();
    } else {
        try bang2();
    }
}

fn bar() !void {
    if (baz()) {
        try quux();
    } else |err| switch (err) {
        error.FileNotFound => try hello(),
    }
}

fn baz() !void {
    try bang1();
}

fn quux() !void {
    try bang2();
}

fn hello() !void {
    try bang2();
}

fn bang1() !void {
    return error.FileNotFound;
}

fn bang2() !void {
    return error.PermissionDenied;
}

```

**Shell:**

```shell
$ zig build-exe error_return_trace.zig
$ ./error_return_trace
error: PermissionDenied
/home/andy/dev/zig/doc/langref/error_return_trace.zig:34:5: 0x10de708 in bang1 (error_return_trace)
    return error.FileNotFound;
    ^
/home/andy/dev/zig/doc/langref/error_return_trace.zig:22:5: 0x10de733 in baz (error_return_trace)
    try bang1();
    ^
/home/andy/dev/zig/doc/langref/error_return_trace.zig:38:5: 0x10de758 in bang2 (error_return_trace)
    return error.PermissionDenied;
    ^
/home/andy/dev/zig/doc/langref/error_return_trace.zig:30:5: 0x10de7c3 in hello (error_return_trace)
    try bang2();
    ^
/home/andy/dev/zig/doc/langref/error_return_trace.zig:17:31: 0x10de868 in bar (error_return_trace)
        error.FileNotFound => try hello(),
                              ^
/home/andy/dev/zig/doc/langref/error_return_trace.zig:7:9: 0x10de8d0 in foo (error_return_trace)
        try bar();
        ^
/home/andy/dev/zig/doc/langref/error_return_trace.zig:2:5: 0x10de928 in main (error_return_trace)
    try foo(12);
    ^

```

Look closely at this example. This is no stack trace.

You can see that the final error bubbled up was `PermissionDenied`,
but the original error that started this whole thing was `FileNotFound`. In the `bar` function, the code handles the original error code,
and then returns another one, from the switch statement. Error Return Traces make this clear, whereas a stack trace would look like this:

**`stack_trace.zig`:**

```zig
pub fn main() void {
    foo(12);
}

fn foo(x: i32) void {
    if (x >= 5) {
        bar();
    } else {
        bang2();
    }
}

fn bar() void {
    if (baz()) {
        quux();
    } else {
        hello();
    }
}

fn baz() bool {
    return bang1();
}

fn quux() void {
    bang2();
}

fn hello() void {
    bang2();
}

fn bang1() bool {
    return false;
}

fn bang2() void {
    @panic("PermissionDenied");
}

```

**Shell:**

```shell
$ zig build-exe stack_trace.zig
$ ./stack_trace
thread 207080 panic: PermissionDenied
/home/andy/dev/zig/doc/langref/stack_trace.zig:38:5: 0x10df3dc in bang2 (stack_trace)
    @panic("PermissionDenied");
    ^
/home/andy/dev/zig/doc/langref/stack_trace.zig:30:10: 0x10dfca8 in hello (stack_trace)
    bang2();
         ^
/home/andy/dev/zig/doc/langref/stack_trace.zig:17:14: 0x10df3b0 in bar (stack_trace)
        hello();
             ^
/home/andy/dev/zig/doc/langref/stack_trace.zig:7:12: 0x10df1d4 in foo (stack_trace)
        bar();
           ^
/home/andy/dev/zig/doc/langref/stack_trace.zig:2:8: 0x10de96d in main (stack_trace)
    foo(12);
       ^
/home/andy/dev/zig/lib/std/start.zig:651:22: 0x10de362 in posixCallMainAndExit (stack_trace)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:271:5: 0x10ddf3d in _start (stack_trace)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

Here, the stack trace does not explain how the control
flow in `bar` got to the `hello()` call.
One would have to open a debugger or further instrument the application
in order to find out. The error return trace, on the other hand,
shows exactly how the error bubbled up.

This debugging feature makes it easier to iterate quickly on code that
robustly handles all error conditions. This means that Zig developers
will naturally find themselves writing correct, robust code in order
to increase their development pace.

Error Return Traces are enabled by default in [Debug](#Debug) and [ReleaseSafe](#ReleaseSafe) builds and disabled by default in [ReleaseFast](#ReleaseFast) and [ReleaseSmall](#ReleaseSmall) builds.

There are a few ways to activate this error return tracing feature:

- Return an error from main
- An error makes its way to `catch unreachable` and you have not overridden the default panic handler
- Use [errorReturnTrace](#errorReturnTrace) to access the current return trace. You can use `std.debug.dumpStackTrace` to print it. This function returns comptime-known [null](#null) when building without error return tracing support.

##### Implementation Details

To analyze performance cost, there are two cases:

- when no errors are returned
- when returning errors

For the case when no errors are returned, the cost is a single memory write operation, only in the first non-failable function in the call graph that calls a failable function, i.e. when a function returning `void` calls a function returning `error`.
This is to initialize this struct in the stack memory:

**`stack_trace_struct.zig`:**

```zig
pub const StackTrace = struct {
    index: usize,
    instruction_addresses: [N]usize,
};

```

Here, N is the maximum function call depth as determined by call graph analysis. Recursion is ignored and counts for 2.

A pointer to `StackTrace` is passed as a secret parameter to every function that can return an error, but it's always the first parameter, so it can likely sit in a register and stay there.

That's it for the path when no errors occur. It's practically free in terms of performance.

When generating the code for a function that returns an error, just before the `return` statement (only for the `return` statements that return errors), Zig generates a call to this function:

**`zig_return_error_fn.zig`:**

```zig
// marked as "no-inline" in LLVM IR
fn __zig_return_error(stack_trace: *StackTrace) void {
    stack_trace.instruction_addresses[stack_trace.index] = @returnAddress();
    stack_trace.index = (stack_trace.index + 1) % N;
}

```

The cost is 2 math operations plus some memory reads and writes. The memory accessed is constrained and should remain cached for the duration of the error return bubbling.

As for code size cost, 1 function call before a return statement is no big deal. Even so,
I have [a plan](https://github.com/ziglang/zig/issues/690) to make the call to
`__zig_return_error` a tail call, which brings the code size cost down to actually zero. What is a return statement in code without error return tracing can become a jump instruction in code with error return tracing.


---

### Optionals

One area that Zig provides safety without compromising efficiency or
readability is with the optional type.

The question mark symbolizes the optional type. You can convert a type to an optional
type by putting a question mark in front of it, like this:

**`optional_integer.zig`:**

```zig
// normal integer
const normal_int: i32 = 1234;

// optional integer
const optional_int: ?i32 = 5678;

```

Now the variable `optional_int` could be an `i32`, or `null`.

Instead of integers, let's talk about pointers. Null references are the source of many runtime
exceptions, and even stand accused of being
[the worst mistake of computer science](https://www.lucidchart.com/techblog/2015/08/31/the-worst-mistake-of-computer-science/).

Zig does not have them.

Instead, you can use an optional pointer. This secretly compiles down to a normal pointer,
since we know we can use 0 as the null value for the optional type. But the compiler
can check your work and make sure you don't assign null to something that can't be null.

Typically the downside of not having null is that it makes the code more verbose to
write. But, let's compare some equivalent C code and Zig code.

Task: call malloc, if the result is null, return null.

C code

**call_malloc_in_c.c:**

```c
// malloc prototype included for reference
void *malloc(size_t size);

struct Foo *do_a_thing(void) {
    char *ptr = malloc(1234);
    if (!ptr) return NULL;
    // ...
}

```

Zig code

**`call_malloc_from_zig.zig`:**

```zig
// malloc prototype included for reference
extern fn malloc(size: usize) ?[*]u8;

fn doAThing() ?*Foo {
    const ptr = malloc(1234) orelse return null;
    _ = ptr; // ...
}

```

Here, Zig is at least as convenient, if not more, than C. And, the type of "ptr"
is `[*]u8` *not* `?[*]u8`. The `orelse` keyword
unwrapped the optional type and therefore `ptr` is guaranteed to be non-null everywhere
it is used in the function.

The other form of checking against NULL you might see looks like this:

**checking_null_in_c.c:**

```c
void do_a_thing(struct Foo *foo) {
    // do some stuff

    if (foo) {
        do_something_with_foo(foo);
    }

    // do some stuff
}

```

In Zig you can accomplish the same thing:

**`checking_null_in_zig.zig`:**

```zig
const Foo = struct {};
fn doSomethingWithFoo(foo: *Foo) void {
    _ = foo;
}

fn doAThing(optional_foo: ?*Foo) void {
    // do some stuff

    if (optional_foo) |foo| {
        doSomethingWithFoo(foo);
    }

    // do some stuff
}

```

Once again, the notable thing here is that inside the if block,
`foo` is no longer an optional pointer, it is a pointer, which
cannot be null.

One benefit to this is that functions which take pointers as arguments can
be annotated with the "nonnull" attribute - `__attribute__((nonnull))` in
[GCC](https://gcc.gnu.org/onlinedocs/gcc-4.0.0/gcc/Function-Attributes.html).
The optimizer can sometimes make better decisions knowing that pointer arguments
cannot be null.

#### Optional Type

An optional is created by putting `?` in front of a type. You can use compile-time
reflection to access the child type of an optional:

**`test_optional_type.zig`:**

```zig
const expect = @import("std").testing.expect;

test "optional type" {
    // Declare an optional and coerce from null:
    var foo: ?i32 = null;

    // Coerce from child type of an optional
    foo = 1234;

    // Use compile-time reflection to access the child type of the optional:
    try comptime expect(@typeInfo(@TypeOf(foo)).optional.child == i32);
}

```

**Shell:**

```shell
$ zig test test_optional_type.zig
1/1 test_optional_type.test.optional type...OK
All 1 tests passed.

```

#### null

Just like [undefined](#undefined), `null` has its own type, and the only way to use it is to
cast it to a different type:

**`null.zig`:**

```zig
const optional_value: ?i32 = null;

```

#### Optional Pointers

An optional pointer is guaranteed to be the same size as a pointer. The `null` of
the optional is guaranteed to be address 0.

**`test_optional_pointer.zig`:**

```zig
const expect = @import("std").testing.expect;

test "optional pointers" {
    // Pointers cannot be null. If you want a null pointer, use the optional
    // prefix `?` to make the pointer type optional.
    var ptr: ?*i32 = null;

    var x: i32 = 1;
    ptr = &x;

    try expect(ptr.?.* == 1);

    // Optional pointers are the same size as normal pointers, because pointer
    // value 0 is used as the null value.
    try expect(@sizeOf(?*i32) == @sizeOf(*i32));
}

```

**Shell:**

```shell
$ zig test test_optional_pointer.zig
1/1 test_optional_pointer.test.optional pointers...OK
All 1 tests passed.

```

See also:

- [while with Optionals](21-while.md#while-with-Optionals)
- [if with Optionals](23-if.md#if-with-Optionals)


---

### Casting

A **type cast** converts a value of one type to another.
Zig has [Type Coercion](#Type-Coercion) for conversions that are known to be completely safe and unambiguous,
and [Explicit Casts](#Explicit-Casts) for conversions that one would not want to happen on accident.
There is also a third kind of type conversion called [Peer Type Resolution](#Peer-Type-Resolution) for
the case when a result type must be decided given multiple operand types.

#### Type Coercion

Type coercion occurs when one type is expected, but different type is provided:

**`test_type_coercion.zig`:**

```zig
test "type coercion - variable declaration" {
    const a: u8 = 1;
    const b: u16 = a;
    _ = b;
}

test "type coercion - function call" {
    const a: u8 = 1;
    foo(a);
}

fn foo(b: u16) void {
    _ = b;
}

test "type coercion - @as builtin" {
    const a: u8 = 1;
    const b = @as(u16, a);
    _ = b;
}

```

**Shell:**

```shell
$ zig test test_type_coercion.zig
1/3 test_type_coercion.test.type coercion - variable declaration...OK
2/3 test_type_coercion.test.type coercion - function call...OK
3/3 test_type_coercion.test.type coercion - @as builtin...OK
All 3 tests passed.

```

Type coercions are only allowed when it is completely unambiguous how to get from one type to another,
and the transformation is guaranteed to be safe. There is one exception, which is [C Pointers](46-c.md#C-Pointers).

##### Type Coercion: Stricter Qualification

Values which have the same representation at runtime can be cast to increase the strictness
of the qualifiers, no matter how nested the qualifiers are:

- `const` - non-const to const is allowed
- `volatile` - non-volatile to volatile is allowed
- `align` - bigger to smaller alignment is allowed
- [error sets](#Error-Set-Type) to supersets is allowed

These casts are no-ops at runtime since the value representation does not change.

**`test_no_op_casts.zig`:**

```zig
test "type coercion - const qualification" {
    var a: i32 = 1;
    const b: *i32 = &a;
    foo(b);
}

fn foo(_: *const i32) void {}

```

**Shell:**

```shell
$ zig test test_no_op_casts.zig
1/1 test_no_op_casts.test.type coercion - const qualification...OK
All 1 tests passed.

```

In addition, pointers coerce to const optional pointers:

**`test_pointer_coerce_const_optional.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;
const mem = std.mem;

test "cast *[1][*:0]const u8 to []const ?[*:0]const u8" {
    const window_name = [1][*:0]const u8{"window name"};
    const x: []const ?[*:0]const u8 = &window_name;
    try expect(mem.eql(u8, mem.span(x[0].?), "window name"));
}

```

**Shell:**

```shell
$ zig test test_pointer_coerce_const_optional.zig
1/1 test_pointer_coerce_const_optional.test.cast *[1][*:0]const u8 to []const ?[*:0]const u8...OK
All 1 tests passed.

```

##### Type Coercion: Integer and Float Widening

[Integers](08-integers.md#Integers) coerce to integer types which can represent every value of the old type, and likewise
[Floats](09-floats.md#Floats) coerce to float types which can represent every value of the old type.

**`test_integer_widening.zig`:**

```zig
const std = @import("std");
const builtin = @import("builtin");
const expect = std.testing.expect;
const mem = std.mem;

test "integer widening" {
    const a: u8 = 250;
    const b: u16 = a;
    const c: u32 = b;
    const d: u64 = c;
    const e: u64 = d;
    const f: u128 = e;
    try expect(f == a);
}

test "implicit unsigned integer to signed integer" {
    const a: u8 = 250;
    const b: i16 = a;
    try expect(b == 250);
}

test "float widening" {
    const a: f16 = 12.34;
    const b: f32 = a;
    const c: f64 = b;
    const d: f128 = c;
    try expect(d == a);
}

```

**Shell:**

```shell
$ zig test test_integer_widening.zig
1/3 test_integer_widening.test.integer widening...OK
2/3 test_integer_widening.test.implicit unsigned integer to signed integer...OK
3/3 test_integer_widening.test.float widening...OK
All 3 tests passed.

```

##### Type Coercion: Float to Int

A compiler error is appropriate because this ambiguous expression leaves the compiler
two choices about the coercion.

- Cast `54.0` to `comptime_int` resulting in `@as(comptime_int, 10)`, which is casted to `@as(f32, 10)`
- Cast `5` to `comptime_float` resulting in `@as(comptime_float, 10.8)`, which is casted to `@as(f32, 10.8)`

**`test_ambiguous_coercion.zig`:**

```zig
// Compile time coercion of float to int
test "implicit cast to comptime_int" {
    const f: f32 = 54.0 / 5;
    _ = f;
}

```

**Shell:**

```shell
$ zig test test_ambiguous_coercion.zig
/home/andy/dev/zig/doc/langref/test_ambiguous_coercion.zig:3:25: error: ambiguous coercion of division operands 'comptime_float' and 'comptime_int'; non-zero remainder '4'
    const f: f32 = 54.0 / 5;
                   ~~~~~^~~


```

##### Type Coercion: Slices, Arrays and Pointers

**`test_coerce_slices_arrays_and_pointers.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

// You can assign constant pointers to arrays to a slice with
// const modifier on the element type. Useful in particular for
// String literals.
test "*const [N]T to []const T" {
    const x1: []const u8 = "hello";
    const x2: []const u8 = &[5]u8{ 'h', 'e', 'l', 'l', 111 };
    try expect(std.mem.eql(u8, x1, x2));

    const y: []const f32 = &[2]f32{ 1.2, 3.4 };
    try expect(y[0] == 1.2);
}

// Likewise, it works when the destination type is an error union.
test "*const [N]T to E![]const T" {
    const x1: anyerror![]const u8 = "hello";
    const x2: anyerror![]const u8 = &[5]u8{ 'h', 'e', 'l', 'l', 111 };
    try expect(std.mem.eql(u8, try x1, try x2));

    const y: anyerror![]const f32 = &[2]f32{ 1.2, 3.4 };
    try expect((try y)[0] == 1.2);
}

// Likewise, it works when the destination type is an optional.
test "*const [N]T to ?[]const T" {
    const x1: ?[]const u8 = "hello";
    const x2: ?[]const u8 = &[5]u8{ 'h', 'e', 'l', 'l', 111 };
    try expect(std.mem.eql(u8, x1.?, x2.?));

    const y: ?[]const f32 = &[2]f32{ 1.2, 3.4 };
    try expect(y.?[0] == 1.2);
}

// In this cast, the array length becomes the slice length.
test "*[N]T to []T" {
    var buf: [5]u8 = "hello".*;
    const x: []u8 = &buf;
    try expect(std.mem.eql(u8, x, "hello"));

    const buf2 = [2]f32{ 1.2, 3.4 };
    const x2: []const f32 = &buf2;
    try expect(std.mem.eql(f32, x2, &[2]f32{ 1.2, 3.4 }));
}

// Single-item pointers to arrays can be coerced to many-item pointers.
test "*[N]T to [*]T" {
    var buf: [5]u8 = "hello".*;
    const x: [*]u8 = &buf;
    try expect(x[4] == 'o');
    // x[5] would be an uncaught out of bounds pointer dereference!
}

// Likewise, it works when the destination type is an optional.
test "*[N]T to ?[*]T" {
    var buf: [5]u8 = "hello".*;
    const x: ?[*]u8 = &buf;
    try expect(x.?[4] == 'o');
}

// Single-item pointers can be cast to len-1 single-item arrays.
test "*T to *[1]T" {
    var x: i32 = 1234;
    const y: *[1]i32 = &x;
    const z: [*]i32 = y;
    try expect(z[0] == 1234);
}

```

**Shell:**

```shell
$ zig test test_coerce_slices_arrays_and_pointers.zig
1/7 test_coerce_slices_arrays_and_pointers.test.*const [N]T to []const T...OK
2/7 test_coerce_slices_arrays_and_pointers.test.*const [N]T to E![]const T...OK
3/7 test_coerce_slices_arrays_and_pointers.test.*const [N]T to ?[]const T...OK
4/7 test_coerce_slices_arrays_and_pointers.test.*[N]T to []T...OK
5/7 test_coerce_slices_arrays_and_pointers.test.*[N]T to [*]T...OK
6/7 test_coerce_slices_arrays_and_pointers.test.*[N]T to ?[*]T...OK
7/7 test_coerce_slices_arrays_and_pointers.test.*T to *[1]T...OK
All 7 tests passed.

```

See also:

- [C Pointers](46-c.md#C-Pointers)

##### Type Coercion: Optionals

The payload type of [Optionals](29-optionals.md#Optionals), as well as [null](#null), coerce to the optional type.

**`test_coerce_optionals.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "coerce to optionals" {
    const x: ?i32 = 1234;
    const y: ?i32 = null;

    try expect(x.? == 1234);
    try expect(y == null);
}

```

**Shell:**

```shell
$ zig test test_coerce_optionals.zig
1/1 test_coerce_optionals.test.coerce to optionals...OK
All 1 tests passed.

```

Optionals work nested inside the [Error Union Type](#Error-Union-Type), too:

**`test_coerce_optional_wrapped_error_union.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "coerce to optionals wrapped in error union" {
    const x: anyerror!?i32 = 1234;
    const y: anyerror!?i32 = null;

    try expect((try x).? == 1234);
    try expect((try y) == null);
}

```

**Shell:**

```shell
$ zig test test_coerce_optional_wrapped_error_union.zig
1/1 test_coerce_optional_wrapped_error_union.test.coerce to optionals wrapped in error union...OK
All 1 tests passed.

```

##### Type Coercion: Error Unions

The payload type of an [Error Union Type](#Error-Union-Type) as well as the [Error Set Type](#Error-Set-Type)
coerce to the error union type:

**`test_coerce_to_error_union.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "coercion to error unions" {
    const x: anyerror!i32 = 1234;
    const y: anyerror!i32 = error.Failure;

    try expect((try x) == 1234);
    try std.testing.expectError(error.Failure, y);
}

```

**Shell:**

```shell
$ zig test test_coerce_to_error_union.zig
1/1 test_coerce_to_error_union.test.coercion to error unions...OK
All 1 tests passed.

```

##### Type Coercion: Compile-Time Known Numbers

When a number is [comptime](34-comptime.md#comptime)-known to be representable in the destination type,
it may be coerced:

**`test_coerce_large_to_small.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "coercing large integer type to smaller one when value is comptime-known to fit" {
    const x: u64 = 255;
    const y: u8 = x;
    try expect(y == 255);
}

```

**Shell:**

```shell
$ zig test test_coerce_large_to_small.zig
1/1 test_coerce_large_to_small.test.coercing large integer type to smaller one when value is comptime-known to fit...OK
All 1 tests passed.

```

##### Type Coercion: Unions and Enums

Tagged unions can be coerced to enums, and enums can be coerced to tagged unions
when they are [comptime](34-comptime.md#comptime)-known to be a field of the union that has only one possible value, such as
[void](#void):

**`test_coerce_unions_enums.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const E = enum {
    one,
    two,
    three,
};

const U = union(E) {
    one: i32,
    two: f32,
    three,
};

const U2 = union(enum) {
    a: void,
    b: f32,

    fn tag(self: U2) usize {
        switch (self) {
            .a => return 1,
            .b => return 2,
        }
    }
};

test "coercion between unions and enums" {
    const u = U{ .two = 12.34 };
    const e: E = u; // coerce union to enum
    try expect(e == E.two);

    const three = E.three;
    const u_2: U = three; // coerce enum to union
    try expect(u_2 == E.three);

    const u_3: U = .three; // coerce enum literal to union
    try expect(u_3 == E.three);

    const u_4: U2 = .a; // coerce enum literal to union with inferred enum tag type.
    try expect(u_4.tag() == 1);

    // The following example is invalid.
    // error: coercion from enum '@TypeOf(.enum_literal)' to union 'test_coerce_unions_enum.U2' must initialize 'f32' field 'b'
    //var u_5: U2 = .b;
    //try expect(u_5.tag() == 2);
}

```

**Shell:**

```shell
$ zig test test_coerce_unions_enums.zig
1/1 test_coerce_unions_enums.test.coercion between unions and enums...OK
All 1 tests passed.

```

See also:

- [union](17-union.md#union)
- [enum](16-enum.md#enum)

##### Type Coercion: undefined

[undefined](#undefined) can be coerced to any type.

##### Type Coercion: Tuples to Arrays

[Tuples](#Tuples) can be coerced to arrays, if all of the fields have the same type.

**`test_coerce_tuples_arrays.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

const Tuple = struct { u8, u8 };
test "coercion from homogeneous tuple to array" {
    const tuple: Tuple = .{ 5, 6 };
    const array: [2]u8 = tuple;
    _ = array;
}

```

**Shell:**

```shell
$ zig test test_coerce_tuples_arrays.zig
1/1 test_coerce_tuples_arrays.test.coercion from homogeneous tuple to array...OK
All 1 tests passed.

```

#### Explicit Casts

Explicit casts are performed via [Builtin Functions](38-builtin-functions.md#Builtin-Functions).
Some explicit casts are safe; some are not.
Some explicit casts perform language-level assertions; some do not.
Some explicit casts are no-ops at runtime; some are not.

- [@bitCast](#bitCast) - change type but maintain bit representation
- [@alignCast](#alignCast) - make a pointer have more alignment
- [@enumFromInt](16-enum.md#enumFromInt) - obtain an enum value based on its integer tag value
- [@errorFromInt](#errorFromInt) - obtain an error code based on its integer value
- [@errorCast](#errorCast) - convert to a smaller error set
- [@floatCast](#floatCast) - convert a larger float to a smaller float
- [@floatFromInt](#floatFromInt) - convert an integer to a float value
- [@intCast](#intCast) - convert between integer types
- [@intFromBool](#intFromBool) - convert true to 1 and false to 0
- [@intFromEnum](#intFromEnum) - obtain the integer tag value of an enum or tagged union
- [@intFromError](#intFromError) - obtain the integer value of an error code
- [@intFromFloat](#intFromFloat) - obtain the integer part of a float value
- [@intFromPtr](#intFromPtr) - obtain the address of a pointer
- [@ptrFromInt](#ptrFromInt) - convert an address to a pointer
- [@ptrCast](#ptrCast) - convert between pointer types
- [@truncate](#truncate) - convert between integer types, chopping off bits

#### Peer Type Resolution

Peer Type Resolution occurs in these places:

- [switch](20-switch.md#switch) expressions
- [if](23-if.md#if) expressions
- [while](21-while.md#while) expressions
- [for](22-for.md#for) expressions
- Multiple break statements in a block
- Some [binary operations](#Table-of-Operators)

This kind of type resolution chooses a type that all peer types can coerce into. Here are
some examples:

**`test_peer_type_resolution.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;
const mem = std.mem;

test "peer resolve int widening" {
    const a: i8 = 12;
    const b: i16 = 34;
    const c = a + b;
    try expect(c == 46);
    try expect(@TypeOf(c) == i16);
}

test "peer resolve arrays of different size to const slice" {
    try expect(mem.eql(u8, boolToStr(true), "true"));
    try expect(mem.eql(u8, boolToStr(false), "false"));
    try comptime expect(mem.eql(u8, boolToStr(true), "true"));
    try comptime expect(mem.eql(u8, boolToStr(false), "false"));
}
fn boolToStr(b: bool) []const u8 {
    return if (b) "true" else "false";
}

test "peer resolve array and const slice" {
    try testPeerResolveArrayConstSlice(true);
    try comptime testPeerResolveArrayConstSlice(true);
}
fn testPeerResolveArrayConstSlice(b: bool) !void {
    const value1 = if (b) "aoeu" else @as([]const u8, "zz");
    const value2 = if (b) @as([]const u8, "zz") else "aoeu";
    try expect(mem.eql(u8, value1, "aoeu"));
    try expect(mem.eql(u8, value2, "zz"));
}

test "peer type resolution: ?T and T" {
    try expect(peerTypeTAndOptionalT(true, false).? == 0);
    try expect(peerTypeTAndOptionalT(false, false).? == 3);
    comptime {
        try expect(peerTypeTAndOptionalT(true, false).? == 0);
        try expect(peerTypeTAndOptionalT(false, false).? == 3);
    }
}
fn peerTypeTAndOptionalT(c: bool, b: bool) ?usize {
    if (c) {
        return if (b) null else @as(usize, 0);
    }

    return @as(usize, 3);
}

test "peer type resolution: *[0]u8 and []const u8" {
    try expect(peerTypeEmptyArrayAndSlice(true, "hi").len == 0);
    try expect(peerTypeEmptyArrayAndSlice(false, "hi").len == 1);
    comptime {
        try expect(peerTypeEmptyArrayAndSlice(true, "hi").len == 0);
        try expect(peerTypeEmptyArrayAndSlice(false, "hi").len == 1);
    }
}
fn peerTypeEmptyArrayAndSlice(a: bool, slice: []const u8) []const u8 {
    if (a) {
        return &[_]u8{};
    }

    return slice[0..1];
}
test "peer type resolution: *[0]u8, []const u8, and anyerror![]u8" {
    {
        var data = "hi".*;
        const slice = data[0..];
        try expect((try peerTypeEmptyArrayAndSliceAndError(true, slice)).len == 0);
        try expect((try peerTypeEmptyArrayAndSliceAndError(false, slice)).len == 1);
    }
    comptime {
        var data = "hi".*;
        const slice = data[0..];
        try expect((try peerTypeEmptyArrayAndSliceAndError(true, slice)).len == 0);
        try expect((try peerTypeEmptyArrayAndSliceAndError(false, slice)).len == 1);
    }
}
fn peerTypeEmptyArrayAndSliceAndError(a: bool, slice: []u8) anyerror![]u8 {
    if (a) {
        return &[_]u8{};
    }

    return slice[0..1];
}

test "peer type resolution: *const T and ?*T" {
    const a: *const usize = @ptrFromInt(0x123456780);
    const b: ?*usize = @ptrFromInt(0x123456780);
    try expect(a == b);
    try expect(b == a);
}

test "peer type resolution: error union switch" {
    // The non-error and error cases are only peers if the error case is just a switch expression;
    // the pattern `if (x) {...} else |err| blk: { switch (err) {...} }` does not consider the
    // non-error and error case to be peers.
    var a: error{ A, B, C }!u32 = 0;
    _ = &a;
    const b = if (a) |x|
        x + 3
    else |err| switch (err) {
        error.A => 0,
        error.B => 1,
        error.C => null,
    };
    try expect(@TypeOf(b) == ?u32);

    // The non-error and error cases are only peers if the error case is just a switch expression;
    // the pattern `x catch |err| blk: { switch (err) {...} }` does not consider the unwrapped `x`
    // and error case to be peers.
    const c = a catch |err| switch (err) {
        error.A => 0,
        error.B => 1,
        error.C => null,
    };
    try expect(@TypeOf(c) == ?u32);
}

```

**Shell:**

```shell
$ zig test test_peer_type_resolution.zig
1/8 test_peer_type_resolution.test.peer resolve int widening...OK
2/8 test_peer_type_resolution.test.peer resolve arrays of different size to const slice...OK
3/8 test_peer_type_resolution.test.peer resolve array and const slice...OK
4/8 test_peer_type_resolution.test.peer type resolution: ?T and T...OK
5/8 test_peer_type_resolution.test.peer type resolution: *[0]u8 and []const u8...OK
6/8 test_peer_type_resolution.test.peer type resolution: *[0]u8, []const u8, and anyerror![]u8...OK
7/8 test_peer_type_resolution.test.peer type resolution: *const T and ?*T...OK
8/8 test_peer_type_resolution.test.peer type resolution: error union switch...OK
All 8 tests passed.

```


---
