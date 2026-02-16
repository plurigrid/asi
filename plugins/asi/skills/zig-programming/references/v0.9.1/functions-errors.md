# Functions and Error Handling

*Function design, error handling patterns, and type conversions*


---

### unreachable

In `Debug` and `ReleaseSafe` mode, and when using `zig test`,
`unreachable` emits a call to `panic` with the message `reached unreachable code`.

In `ReleaseFast` mode, the optimizer uses the assumption that `unreachable` code
will never be hit to perform optimizations. However, `zig test` even in `ReleaseFast` mode
still emits `unreachable` as calls to `panic`.

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
1/1 test "basic math"... OK
All 1 tests passed.

```

In fact, this is how `std.debug.assert` is implemented:

**`test.zig`:**

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
$ zig test test.zig
1/1 test "this will fail"... thread 1431741 panic: reached unreachable code
/home/andy/tmp/zig/docgen_tmp/test.zig:3:14: 0x207dbb in assert (test)
    if (!ok) unreachable; // assertion failure
             ^
/home/andy/tmp/zig/docgen_tmp/test.zig:8:11: 0x20784e in test "this will fail" (test)
    assert(false);
          ^
/home/andy/tmp/zig/lib/std/special/test_runner.zig:80:28: 0x22f103 in std.special.main (test)
        } else test_fn.func();
                           ^
/home/andy/tmp/zig/lib/std/start.zig:551:22: 0x22847c in std.start.callMain (test)
            root.main();
                     ^
/home/andy/tmp/zig/lib/std/start.zig:495:12: 0x2090be in std.start.callMainWithArgs (test)
    return @call(.{ .modifier = .always_inline }, callMain, .{});
           ^
/home/andy/tmp/zig/lib/std/start.zig:409:17: 0x208156 in std.start.posixCallMainAndExit (test)
    std.os.exit(@call(.{ .modifier = .always_inline }, callMainWithArgs, .{ argc, argv, envp }));
                ^
/home/andy/tmp/zig/lib/std/start.zig:322:5: 0x207f62 in std.start._start (test)
    @call(.{ .modifier = .never_inline }, posixCallMainAndExit, .{});
    ^
error: the following test command crashed:
docgen_tmp/zig-cache/o/e62d5b643d08f1acbb1386db92eb0f23/test /home/andy/tmp/zig/build-release/zig

```

#### At Compile-Time

**`test.zig`:**

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
$ zig test test.zig
docgen_tmp/test.zig:10:16: error: unreachable code
        assert(@TypeOf(unreachable) == noreturn);
               ^
docgen_tmp/test.zig:10:24: note: control flow is diverted here
        assert(@TypeOf(unreachable) == noreturn);
                       ^


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
1/1 test "noreturn"... OK
All 1 tests passed.

```

Another use case for `noreturn` is the `exit` function:

**`noreturn_from_exit.zig`:**

```zig
const std = @import("std");
const builtin = @import("builtin");
const native_arch = builtin.cpu.arch;
const expect = std.testing.expect;

const WINAPI: std.builtin.CallingConvention = if (native_arch == .i386) .Stdcall else .C;
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
$ zig test noreturn_from_exit.zig -target x86_64-windows --test-no-exec

```


---

### Functions

**`functions.zig`:**

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
export fn sub(a: i8, b: i8) i8 { return a - b; }

// The extern specifier is used to declare a function that will be resolved
// at link time, when linking statically, or at runtime, when linking
// dynamically.
// The callconv specifier changes the calling convention of the function.
const WINAPI: std.builtin.CallingConvention = if (native_arch == .i386) .Stdcall else .C;
extern "kernel32" fn ExitProcess(exit_code: u32) callconv(WINAPI) noreturn;
extern "c" fn atan2(a: f64, b: f64) f64;

// The @setCold builtin tells the optimizer that a function is rarely called.
fn abort() noreturn {
    @setCold(true);
    while (true) {}
}

// The naked calling convention makes a function not have any function prologue or epilogue.
// This can be useful when integrating with assembly.
fn _start() callconv(.Naked) noreturn {
    abort();
}

// The inline calling convention forces a function to be inlined at all call sites.
// If the function cannot be inlined, it is a compile-time error.
fn shiftLeftOne(a: u32) callconv(.Inline) u32 {
    return a << 1;
}

// The pub specifier allows the function to be visible when importing.
// Another file can use @import and call sub2
pub fn sub2(a: i8, b: i8) i8 { return a - b; }

// Functions can be used as values and are equivalent to pointers.
const call2_op = fn (a: i8, b: i8) i8;
fn do_op(fn_call: call2_op, op1: i8, op2: i8) i8 {
    return fn_call(op1, op2);
}

test "function" {
    try expect(do_op(add, 5, 6) == 11);
    try expect(do_op(sub2, 5, 6) == -1);
}

```

**Shell:**

```shell
$ zig test functions.zig
1/1 test "function"... OK
All 1 tests passed.

```

Function values are like pointers:

**`test.zig`:**

```zig
const assert = @import("std").debug.assert;

comptime {
    assert(@TypeOf(foo) == fn()void);
    assert(@sizeOf(fn()void) == @sizeOf(?fn()void));
}

fn foo() void { }

```

**Shell:**

```shell
$ zig build-obj test.zig

```

#### Pass-by-value Parameters

Primitive types such as [Integers](08-integers.md#Integers) and [Floats](09-floats.md#Floats) passed as parameters
are copied, and then the copy is available in the function body. This is called "passing by value".
Copying a primitive type is essentially free and typically involves nothing more than
setting a register.

Structs, unions, and arrays can sometimes be more efficiently passed as a reference, since a copy
could be arbitrarily expensive depending on the size. When these types are passed
as parameters, Zig may choose to copy and pass by value, or pass by reference, whichever way
Zig decides will be faster. This is made possible, in part, by the fact that parameters are immutable.

**`pass_by_reference_or_value.zig`:**

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
$ zig test pass_by_reference_or_value.zig
1/1 test "pass struct to function"... OK
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
    var y: i64 = 2;
    try expect(addFortyTwo(y) == 44);
    try expect(@TypeOf(addFortyTwo(y)) == i64);
}

```

**Shell:**

```shell
$ zig test test_fn_type_inference.zig
1/1 test "fn type inference"... OK
All 1 tests passed.

```

#### Function Reflection

**`test_fn_reflection.zig`:**

```zig
const expect = @import("std").testing.expect;

test "fn reflection" {
    try expect(@typeInfo(@TypeOf(expect)).Fn.args[0].arg_type.? == bool);
    try expect(@typeInfo(@TypeOf(expect)).Fn.is_var_args == false);
}

```

**Shell:**

```shell
$ zig test test_fn_reflection.zig
1/1 test "fn reflection"... OK
All 1 tests passed.

```


---

### Errors

#### Error Set Type

An error set is like an [enum](16-enum.md#enum).
However, each error name across the entire compilation gets assigned an unsigned integer
greater than 0. You are allowed to declare the same error name more than once, and if you do, it
gets assigned the same integer value.

The number of unique error values across the entire compilation should determine the size of the error set type.
However right now it is hard coded to be a `u16`. See [#768](https://github.com/ziglang/zig/issues/786).

You can [coerce](#Type-Coercion) an error from a subset to a superset:

**`coercing_subset_to_superset.zig`:**

```zig
const std = @import("std");

const FileOpenError = error {
    AccessDenied,
    OutOfMemory,
    FileNotFound,
};

const AllocationError = error {
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
$ zig test coercing_subset_to_superset.zig
1/1 test "coerce subset to superset"... OK
All 1 tests passed.

```

But you cannot [coerce](#Type-Coercion) an error from a superset to a subset:

**`test.zig`:**

```zig
const FileOpenError = error {
    AccessDenied,
    OutOfMemory,
    FileNotFound,
};

const AllocationError = error {
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
$ zig test test.zig
./docgen_tmp/test.zig:16:12: error: expected type 'AllocationError', found 'FileOpenError'
    return err;
           ^
./docgen_tmp/test.zig:2:5: note: 'error.AccessDenied' not a member of destination error set
    AccessDenied,
    ^
./docgen_tmp/test.zig:4:5: note: 'error.FileNotFound' not a member of destination error set
    FileNotFound,
    ^

```

There is a shortcut for declaring an error set with only 1 value, and then getting that value:

**`test.zig`:**

```zig
const err = error.FileNotFound;

```

This is equivalent to:

**`test.zig`:**

```zig
const err = (error {FileNotFound}).FileNotFound;

```

This becomes useful when using [Inferred Error Sets](#Inferred-Error-Sets).

##### The Global Error Set

`anyerror` refers to the global error set.
This is the error set that contains all errors in the entire compilation unit.
It is a superset of all other error sets and a subset of none of them.

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
        if (@mulWithOverflow(u64, x, radix, &x)) {
            return error.Overflow;
        }

        // x += digit
        if (@addWithOverflow(u64, x, digit, &x)) {
            return error.Overflow;
        }
    }

    return x;
}

fn charToDigit(c: u8) u8 {
    return switch (c) {
        '0' ... '9' => c - '0',
        'A' ... 'Z' => c - 'A' + 10,
        'a' ... 'z' => c - 'a' + 10,
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
1/1 test "parse u64"... OK
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

**`test.zig`:**

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

##### try

Let's say you wanted to return the error if you got one, otherwise continue with the
function logic:

**`test.zig`:**

```zig
const parseU64 = @import("error_union_parsing_u64.zig").parseU64;

fn doAThing(str: []u8) !void {
    const number = parseU64(str, 10) catch |err| return err;
    _ = number; // ...
}

```

There is a shortcut for this. The `try` expression:

**`test.zig`:**

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
`unreachable` value on the right hand side. `unreachable` generates
a panic in Debug and ReleaseSafe modes and undefined behavior in ReleaseFast mode. So, while we're debugging the
application, if there *was* a surprise error here, the application would crash
appropriately.

Finally, you may want to take a different action for every situation. For that, we combine
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
    comptime try expect(@typeInfo(@TypeOf(foo)).ErrorUnion.payload == i32);

    // Use compile-time reflection to access the error set type of an error union:
    comptime try expect(@typeInfo(@TypeOf(foo)).ErrorUnion.error_set == anyerror);
}

```

**Shell:**

```shell
$ zig test test_error_union.zig
1/1 test "error union"... OK
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
1/1 test "merge error sets"... OK
All 1 tests passed.

```

##### Inferred Error Sets

Because many functions in Zig return a possible error, Zig supports inferring the error set.
To infer the error set for a function, prepend the `!` operator to the functionâs return type, like `!T`:

**`inferred_error_sets.zig`:**

```zig
// With an inferred error set
pub fn add_inferred(comptime T: type, a: T, b: T) !T {
    var answer: T = undefined;
    return if (@addWithOverflow(T, a, b, &answer)) error.Overflow else answer;
}

// With an explicit error set
pub fn add_explicit(comptime T: type, a: T, b: T) Error!T {
    var answer: T = undefined;
    return if (@addWithOverflow(T, a, b, &answer)) error.Overflow else answer;
}

const Error = error {
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
$ zig test inferred_error_sets.zig
1/1 test "inferred error set"... OK
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

**`test.zig`:**

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
        else => try another(),
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

fn another() !void {
    try bang1();
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
$ zig build-exe test.zig

$ ./test
error: PermissionDenied
/home/andy/tmp/zig/docgen_tmp/test.zig:39:5: 0x234472 in bang1 (test)
    return error.FileNotFound;
    ^
/home/andy/tmp/zig/docgen_tmp/test.zig:23:5: 0x23434f in baz (test)
    try bang1();
    ^
/home/andy/tmp/zig/docgen_tmp/test.zig:43:5: 0x234312 in bang2 (test)
    return error.PermissionDenied;
    ^
/home/andy/tmp/zig/docgen_tmp/test.zig:31:5: 0x23443f in hello (test)
    try bang2();
    ^
/home/andy/tmp/zig/docgen_tmp/test.zig:17:31: 0x2342de in bar (test)
        error.FileNotFound => try hello(),
                              ^
/home/andy/tmp/zig/docgen_tmp/test.zig:7:9: 0x2341cc in foo (test)
        try bar();
        ^
/home/andy/tmp/zig/docgen_tmp/test.zig:2:5: 0x22ceb4 in main (test)
    try foo(12);
    ^

```

Look closely at this example. This is no stack trace.

You can see that the final error bubbled up was `PermissionDenied`,
but the original error that started this whole thing was `FileNotFound`. In the `bar` function, the code handles the original error code,
and then returns another one, from the switch statement. Error Return Traces make this clear, whereas a stack trace would look like this:

**`test.zig`:**

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
$ zig build-exe test.zig

$ ./test
thread 1434232 panic: PermissionDenied
/home/andy/tmp/zig/docgen_tmp/test.zig:38:5: 0x234f66 in bang2 (test)
    @panic("PermissionDenied");
    ^
/home/andy/tmp/zig/docgen_tmp/test.zig:30:10: 0x2352e8 in hello (test)
    bang2();
         ^
/home/andy/tmp/zig/docgen_tmp/test.zig:17:14: 0x234f4a in bar (test)
        hello();
             ^
/home/andy/tmp/zig/docgen_tmp/test.zig:7:12: 0x233f75 in foo (test)
        bar();
           ^
/home/andy/tmp/zig/docgen_tmp/test.zig:2:8: 0x22cccd in main (test)
    foo(12);
       ^
/home/andy/tmp/zig/lib/std/start.zig:551:22: 0x2263dc in std.start.callMain (test)
            root.main();
                     ^
/home/andy/tmp/zig/lib/std/start.zig:495:12: 0x206ffe in std.start.callMainWithArgs (test)
    return @call(.{ .modifier = .always_inline }, callMain, .{});
           ^
/home/andy/tmp/zig/lib/std/start.zig:409:17: 0x206096 in std.start.posixCallMainAndExit (test)
    std.os.exit(@call(.{ .modifier = .always_inline }, callMainWithArgs, .{ argc, argv, envp }));
                ^
/home/andy/tmp/zig/lib/std/start.zig:322:5: 0x205ea2 in std.start._start (test)
    @call(.{ .modifier = .never_inline }, posixCallMainAndExit, .{});
    ^
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

**`test.zig`:**

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
extern fn malloc(size: size_t) ?*u8;

fn doAThing() ?*Foo {
    const ptr = malloc(1234) orelse return null;
    _ = ptr; // ...
}

```

Here, Zig is at least as convenient, if not more, than C. And, the type of "ptr"
is `*u8` *not* `?*u8`. The `orelse` keyword
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
const Foo = struct{};
fn doSomethingWithFoo(foo: *Foo) void { _ = foo; }

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
    comptime try expect(@typeInfo(@TypeOf(foo)).Optional.child == i32);
}

```

**Shell:**

```shell
$ zig test test_optional_type.zig
1/1 test "optional type"... OK
All 1 tests passed.

```

#### null

Just like [undefined](#undefined), `null` has its own type, and the only way to use it is to
cast it to a different type:

**`test.zig`:**

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
1/1 test "optional pointers"... OK
All 1 tests passed.

```


---

### Casting

A **type cast** converts a value of one type to another.
Zig has [Type Coercion](#Type-Coercion) for conversions that are known to be completely safe and unambiguous,
and [Explicit Casts](#Explicit-Casts) for conversions that one would not want to happen on accident.
There is also a third kind of type conversion called [Peer Type Resolution](#Peer-Type-Resolution) for
the case when a result type must be decided given multiple operand types.

#### Type Coercion

Type coercion occurs when one type is expected, but different type is provided:

**`type_coercion.zig`:**

```zig
test "type coercion - variable declaration" {
    var a: u8 = 1;
    var b: u16 = a;
    _ = b;
}

test "type coercion - function call" {
    var a: u8 = 1;
    foo(a);
}

fn foo(b: u16) void {
    _ = b;
}

test "type coercion - @as builtin" {
    var a: u8 = 1;
    var b = @as(u16, a);
    _ = b;
}

```

**Shell:**

```shell
$ zig test type_coercion.zig
1/3 test "type coercion - variable declaration"... OK
2/3 test "type coercion - function call"... OK
3/3 test "type coercion - @as builtin"... OK
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

**`no_op_casts.zig`:**

```zig
test "type coercion - const qualification" {
    var a: i32 = 1;
    var b: *i32 = &a;
    foo(b);
}

fn foo(_: *const i32) void {}

```

**Shell:**

```shell
$ zig test no_op_casts.zig
1/1 test "type coercion - const qualification"... OK
All 1 tests passed.

```

In addition, pointers coerce to const optional pointers:

**`pointer_coerce_const_optional.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;
const mem = std.mem;

test "cast *[1][*]const u8 to [*]const ?[*]const u8" {
    const window_name = [1][*]const u8{"window name"};
    const x: [*]const ?[*]const u8 = &window_name;
    try expect(mem.eql(u8, std.mem.sliceTo(@ptrCast([*:0]const u8, x[0].?), 0), "window name"));
}

```

**Shell:**

```shell
$ zig test pointer_coerce_const_optional.zig
1/1 test "cast *[1][*]const u8 to [*]const ?[*]const u8"... OK
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
    var a: u8 = 250;
    var b: u16 = a;
    var c: u32 = b;
    var d: u64 = c;
    var e: u64 = d;
    var f: u128 = e;
    try expect(f == a);
}

test "implicit unsigned integer to signed integer" {
    var a: u8 = 250;
    var b: i16 = a;
    try expect(b == 250);
}

test "float widening" {
    // Note: there is an open issue preventing this from working on aarch64:
    // https://github.com/ziglang/zig/issues/3282
    if (builtin.target.cpu.arch == .aarch64) return error.SkipZigTest;

    var a: f16 = 12.34;
    var b: f32 = a;
    var c: f64 = b;
    var d: f128 = c;
    try expect(d == a);
}

```

**Shell:**

```shell
$ zig test test_integer_widening.zig
1/3 test "integer widening"... OK
2/3 test "implicit unsigned integer to signed integer"... OK
3/3 test "float widening"... OK
All 3 tests passed.

```

##### Type Coercion: Coercion Float to Int

A compiler error is appropriate because this ambiguous expression leaves the compiler
two choices about the coercion.

- Cast `54.0` to `comptime_int` resulting in `@as(comptime_int, 10)`, which is casted to `@as(f32, 10)`
- Cast `5` to `comptime_float` resulting in `@as(comptime_float, 10.8)`, which is casted to `@as(f32, 10.8)`

**`test.zig`:**

```zig
// Compile time coercion of float to int
test "implicit cast to comptime_int" {
    var f: f32 = 54.0 / 5;
    _ = f;
}

```

**Shell:**

```shell
$ zig test test.zig
./docgen_tmp/test.zig:3:18: error: float value 54.000000 cannot be coerced to type 'comptime_int'
    var f: f32 = 54.0 / 5;
                 ^

```

##### Type Coercion: Slices, Arrays and Pointers

**`coerce__slices_arrays_and_ptrs.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

// You can assign constant pointers to arrays to a slice with
// const modifier on the element type. Useful in particular for
// String literals.
test "*const [N]T to []const T" {
    var x1: []const u8 = "hello";
    var x2: []const u8 = &[5]u8{ 'h', 'e', 'l', 'l', 111 };
    try expect(std.mem.eql(u8, x1, x2));

    var y: []const f32 = &[2]f32{ 1.2, 3.4 };
    try expect(y[0] == 1.2);
}

// Likewise, it works when the destination type is an error union.
test "*const [N]T to E![]const T" {
    var x1: anyerror![]const u8 = "hello";
    var x2: anyerror![]const u8 = &[5]u8{ 'h', 'e', 'l', 'l', 111 };
    try expect(std.mem.eql(u8, try x1, try x2));

    var y: anyerror![]const f32 = &[2]f32{ 1.2, 3.4 };
    try expect((try y)[0] == 1.2);
}

// Likewise, it works when the destination type is an optional.
test "*const [N]T to ?[]const T" {
    var x1: ?[]const u8 = "hello";
    var x2: ?[]const u8 = &[5]u8{ 'h', 'e', 'l', 'l', 111 };
    try expect(std.mem.eql(u8, x1.?, x2.?));

    var y: ?[]const f32 = &[2]f32{ 1.2, 3.4 };
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
$ zig test coerce__slices_arrays_and_ptrs.zig
1/7 test "*const [N]T to []const T"... OK
2/7 test "*const [N]T to E![]const T"... OK
3/7 test "*const [N]T to ?[]const T"... OK
4/7 test "*[N]T to []T"... OK
5/7 test "*[N]T to [*]T"... OK
6/7 test "*[N]T to ?[*]T"... OK
7/7 test "*T to *[1]T"... OK
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
1/1 test "coerce to optionals"... OK
All 1 tests passed.

```

It works nested inside the [Error Union Type](#Error-Union-Type), too:

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
1/1 test "coerce to optionals wrapped in error union"... OK
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
1/1 test "coercion to error unions"... OK
All 1 tests passed.

```

##### Type Coercion: Compile-Time Known Numbers

When a number is [comptime](34-comptime.md#comptime)-known to be representable in the destination type,
it may be coerced:

**`test_coerce_large_to_small.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

test "coercing large integer type to smaller one when value is comptime known to fit" {
    const x: u64 = 255;
    const y: u8 = x;
    try expect(y == 255);
}

```

**Shell:**

```shell
$ zig test test_coerce_large_to_small.zig
1/1 test "coercing large integer type to smaller one when value is comptime known to fit"... OK
All 1 tests passed.

```

##### Type Coercion: unions and enums

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

test "coercion between unions and enums" {
    var u = U{ .two = 12.34 };
    var e: E = u;
    try expect(e == E.two);

    const three = E.three;
    var another_u: U = three;
    try expect(another_u == E.three);
}

```

**Shell:**

```shell
$ zig test test_coerce_unions_enums.zig
1/1 test "coercion between unions and enums"... OK
All 1 tests passed.

```

See also:

- [union](17-union.md#union)
- [enum](16-enum.md#enum)

##### Type Coercion: Zero Bit Types

[Zero Bit Types](31-zero-bit-types.md#Zero-Bit-Types) may be coerced to single-item [Pointers](13-pointers.md#Pointers),
regardless of const.

TODO document the reasoning for this

TODO document whether vice versa should work and why

**`coerce_zero_bit_types.zig`:**

```zig
test "coercion of zero bit types" {
    var x: void = {};
    var y: *void = x;
    _ = y;
}

```

**Shell:**

```shell
$ zig test coerce_zero_bit_types.zig
1/1 test "coercion of zero bit types"... OK
All 1 tests passed.

```

##### Type Coercion: undefined

[undefined](#undefined) can be cast to any type.

#### Explicit Casts

Explicit casts are performed via [Builtin Functions](38-builtin-functions.md#Builtin-Functions).
Some explicit casts are safe; some are not.
Some explicit casts perform language-level assertions; some do not.
Some explicit casts are no-ops at runtime; some are not.

- [@bitCast](#bitCast) - change type but maintain bit representation
- [@alignCast](#alignCast) - make a pointer have more alignment
- [@boolToInt](#boolToInt) - convert true to 1 and false to 0
- [@enumToInt](16-enum.md#enumToInt) - obtain the integer tag value of an enum or tagged union
- [@errSetCast](#errSetCast) - convert to a smaller error set
- [@errorToInt](#errorToInt) - obtain the integer value of an error code
- [@floatCast](#floatCast) - convert a larger float to a smaller float
- [@floatToInt](#floatToInt) - obtain the integer part of a float value
- [@intCast](#intCast) - convert between integer types
- [@intToEnum](#intToEnum) - obtain an enum value based on its integer tag value
- [@intToError](#intToError) - obtain an error code based on its integer value
- [@intToFloat](#intToFloat) - convert an integer to a float value
- [@intToPtr](#intToPtr) - convert an address to a pointer
- [@ptrCast](#ptrCast) - convert between pointer types
- [@ptrToInt](#ptrToInt) - obtain the address of a pointer
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

**`peer_type_resolution.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;
const mem = std.mem;

test "peer resolve int widening" {
    var a: i8 = 12;
    var b: i16 = 34;
    var c = a + b;
    try expect(c == 46);
    try expect(@TypeOf(c) == i16);
}

test "peer resolve arrays of different size to const slice" {
    try expect(mem.eql(u8, boolToStr(true), "true"));
    try expect(mem.eql(u8, boolToStr(false), "false"));
    comptime try expect(mem.eql(u8, boolToStr(true), "true"));
    comptime try expect(mem.eql(u8, boolToStr(false), "false"));
}
fn boolToStr(b: bool) []const u8 {
    return if (b) "true" else "false";
}

test "peer resolve array and const slice" {
    try testPeerResolveArrayConstSlice(true);
    comptime try testPeerResolveArrayConstSlice(true);
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
    const a = @intToPtr(*const usize, 0x123456780);
    const b = @intToPtr(?*usize, 0x123456780);
    try expect(a == b);
    try expect(b == a);
}

```

**Shell:**

```shell
$ zig test peer_type_resolution.zig
1/7 test "peer resolve int widening"... OK
2/7 test "peer resolve arrays of different size to const slice"... OK
3/7 test "peer resolve array and const slice"... OK
4/7 test "peer type resolution: ?T and T"... OK
5/7 test "peer type resolution: *[0]u8 and []const u8"... OK
6/7 test "peer type resolution: *[0]u8, []const u8, and anyerror![]u8"... OK
7/7 test "peer type resolution: *const T and ?*T"... OK
All 7 tests passed.

```


---
