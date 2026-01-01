# Testing and Code Quality

*Testing framework, undefined behavior, and best practices*


---

### Zig Test

Code written within one or more `test` declarations can be used to ensure behavior meets expectations:

**`testing_introduction.zig`:**

```zig
const std = @import("std");

test "expect addOne adds one to 41" {

    // The Standard Library contains useful functions to help create tests.
    // `expect` is a function that verifies its argument is true.
    // It will return an error if its argument is false to indicate a failure.
    // `try` is used to return an error to the test runner to notify it that the test failed.
    try std.testing.expect(addOne(41) == 42);
}

test addOne {
    // A test name can also be written using an identifier.
    // This is a doctest, and serves as documentation for `addOne`.
    try std.testing.expect(addOne(41) == 42);
}

/// The function `addOne` adds one to the number given as its argument.
fn addOne(number: i32) i32 {
    return number + 1;
}

```

**Shell:**

```shell
$ zig test testing_introduction.zig
1/2 testing_introduction.test.expect addOne adds one to 41...OK
2/2 testing_introduction.decltest.addOne...OK
All 2 tests passed.

```

The `testing_introduction.zig` code sample tests the [function](27-functions.md#Functions)
`addOne` to ensure that it returns `42` given the input
`41`. From this test's perspective, the `addOne` function is
said to be *code under test*.

`zig test` is a tool that creates and runs a test build. By default, it builds and runs an
executable program using the *default test runner* provided by the [Zig Standard Library](02-zig-standard-library.md#Zig-Standard-Library)
as its main entry point. During the build, `test` declarations found while
[resolving](#File-and-Declaration-Discovery) the given Zig source file are included for the default test runner
to run and report on.

> **Note:** 
This documentation discusses the features of the default test runner as provided by the Zig Standard Library.
Its source code is located in `lib/compiler/test_runner.zig`.

The shell output shown above displays two lines after the `zig test` command. These lines are
printed to standard error by the default test runner:

**1/2 testing_introduction.test.expect addOne adds one to 41...**
: Lines like this indicate which test, out of the total number of tests, is being run.
          In this case, 1/2 indicates that the first test, out of a total of two tests,
          is being run. Note that, when the test runner program's standard error is output
          to the terminal, these lines are cleared when a test succeeds.

**2/2 testing_introduction.decltest.addOne...**
: When the test name is an identifier, the default test runner uses the text
          decltest instead of test.

**All 2 tests passed.**
: This line indicates the total number of tests that have passed.

#### Test Declarations

Test declarations contain the [keyword](50-keyword-reference.md#Keyword-Reference) `test`, followed by an
optional name written as a [string literal](#String-Literals-and-Unicode-Code-Point-Literals) or an
[identifier](#Identifiers), followed by a [block](19-blocks.md#Blocks) containing any valid Zig code that
is allowed in a [function](27-functions.md#Functions).

Non-named test blocks always run during test builds and are exempt from
[Skip Tests](#Skip-Tests).

Test declarations are similar to [Functions](27-functions.md#Functions): they have a return type and a block of code. The implicit
return type of `test` is the [Error Union Type](#Error-Union-Type) `anyerror!void`,
and it cannot be changed. When a Zig source file is not built using the `zig test` tool, the test
declarations are omitted from the build.

Test declarations can be written in the same file, where code under test is written, or in a separate Zig source file.
Since test declarations are top-level declarations, they are order-independent and can
be written before or after the code under test.

See also:

- [The Global Error Set](#The-Global-Error-Set)
- [Grammar](#Grammar)

##### Doctests

Test declarations named using an identifier are *doctests*. The identifier must refer to another declaration in
scope. A doctest, like a [doc comment](#Doc-Comments), serves as documentation for the associated declaration, and
will appear in the generated documentation for the declaration.

An effective doctest should be self-contained and focused on the declaration being tested, answering questions a new
user might have about its interface or intended usage, while avoiding unnecessary or confusing details. A doctest is not
a substitute for a doc comment, but rather a supplement and companion providing a testable, code-driven example, verified
by `zig test`.

#### Test Failure

The default test runner checks for an [error](28-errors.md#Errors) returned from a test.
When a test returns an error, the test is considered a failure and its [error return trace](#Error-Return-Traces)
is output to standard error. The total number of failures will be reported after all tests have run.

**`testing_failure.zig`:**

```zig
const std = @import("std");

test "expect this to fail" {
    try std.testing.expect(false);
}

test "expect this to succeed" {
    try std.testing.expect(true);
}

```

**Shell:**

```shell
$ zig test testing_failure.zig
1/2 testing_failure.test.expect this to fail...FAIL (TestUnexpectedResult)
/home/andy/dev/zig/lib/std/testing.zig:607:14: 0x102f019 in expect (std.zig)
    if (!ok) return error.TestUnexpectedResult;
             ^
/home/andy/dev/zig/doc/langref/testing_failure.zig:4:5: 0x102f078 in test.expect this to fail (testing_failure.zig)
    try std.testing.expect(false);
    ^
2/2 testing_failure.test.expect this to succeed...OK
1 passed; 0 skipped; 1 failed.
error: the following test command failed with exit code 1:
/home/andy/dev/zig/.zig-cache/o/bac0cff07a7d3f5b652a5a9cf02e6de1/test --seed=0x7a2fdb1

```

#### Skip Tests

One way to skip tests is to filter them out by using the `zig test` command line parameter
`--test-filter [text]`. This makes the test build only include tests whose name contains the
supplied filter text. Note that non-named tests are run even when using the `--test-filter [text]`
command line parameter.

To programmatically skip a test, make a `test` return the error
`error.SkipZigTest` and the default test runner will consider the test as being skipped.
The total number of skipped tests will be reported after all tests have run.

**`testing_skip.zig`:**

```zig
test "this will be skipped" {
    return error.SkipZigTest;
}

```

**Shell:**

```shell
$ zig test testing_skip.zig
1/1 testing_skip.test.this will be skipped...SKIP
0 passed; 1 skipped; 0 failed.

```

#### Report Memory Leaks

When code allocates [Memory](41-memory.md#Memory) using the [Zig Standard Library](02-zig-standard-library.md#Zig-Standard-Library)'s testing allocator,
`std.testing.allocator`, the default test runner will report any leaks that are
found from using the testing allocator:

**`testing_detect_leak.zig`:**

```zig
const std = @import("std");

test "detect leak" {
    var list = std.array_list.Managed(u21).init(std.testing.allocator);
    // missing `defer list.deinit();`
    try list.append('â');

    try std.testing.expect(list.items.len == 1);
}

```

**Shell:**

```shell
$ zig test testing_detect_leak.zig
1/1 testing_detect_leak.test.detect leak...OK
[gpa] (err): memory address 0x7f74a8aa0000 leaked:
/home/andy/dev/zig/lib/std/array_list.zig:468:67: 0x10aa8fe in ensureTotalCapacityPrecise (std.zig)
                const new_memory = try self.allocator.alignedAlloc(T, alignment, new_capacity);
                                                                  ^
/home/andy/dev/zig/lib/std/array_list.zig:444:51: 0x107c9e4 in ensureTotalCapacity (std.zig)
            return self.ensureTotalCapacityPrecise(better_capacity);
                                                  ^
/home/andy/dev/zig/lib/std/array_list.zig:494:41: 0x105590d in addOne (std.zig)
            try self.ensureTotalCapacity(newlen);
                                        ^
/home/andy/dev/zig/lib/std/array_list.zig:252:49: 0x1038771 in append (std.zig)
            const new_item_ptr = try self.addOne();
                                                ^
/home/andy/dev/zig/doc/langref/testing_detect_leak.zig:6:20: 0x10350a9 in test.detect leak (testing_detect_leak.zig)
    try list.append('â');
                   ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:218:25: 0x1174760 in mainTerminal (test_runner.zig)
        if (test_fn.func()) |_| {
                        ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:66:28: 0x1170d81 in main (test_runner.zig)
        return mainTerminal();
                           ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x116ab1d in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x116a3b1 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^

All 1 tests passed.
1 errors were logged.
1 tests leaked memory.
error: the following test command failed with exit code 1:
/home/andy/dev/zig/.zig-cache/o/4df377b3969e36bf7e0b2704790b75be/test --seed=0xabc34e97

```

See also:

- [defer](24-defer.md#defer)
- [Memory](41-memory.md#Memory)

#### Detecting Test Build

Use the [compile variable](42-compile-variables.md#Compile-Variables) `@import("builtin").is_test`
to detect a test build:

**`testing_detect_test.zig`:**

```zig
const std = @import("std");
const builtin = @import("builtin");
const expect = std.testing.expect;

test "builtin.is_test" {
    try expect(isATest());
}

fn isATest() bool {
    return builtin.is_test;
}

```

**Shell:**

```shell
$ zig test testing_detect_test.zig
1/1 testing_detect_test.test.builtin.is_test...OK
All 1 tests passed.

```

#### Test Output and Logging

The default test runner and the Zig Standard Library's testing namespace output messages to standard error.

#### The Testing Namespace

The Zig Standard Library's `testing` namespace contains useful functions to help
you create tests. In addition to the `expect` function, this document uses a couple of more functions
as exemplified here:

**`testing_namespace.zig`:**

```zig
const std = @import("std");

test "expectEqual demo" {
    const expected: i32 = 42;
    const actual = 42;

    // The first argument to `expectEqual` is the known, expected, result.
    // The second argument is the result of some expression.
    // The actual's type is casted to the type of expected.
    try std.testing.expectEqual(expected, actual);
}

test "expectError demo" {
    const expected_error = error.DemoError;
    const actual_error_union: anyerror!void = error.DemoError;

    // `expectError` will fail when the actual error is different than
    // the expected error.
    try std.testing.expectError(expected_error, actual_error_union);
}

```

**Shell:**

```shell
$ zig test testing_namespace.zig
1/2 testing_namespace.test.expectEqual demo...OK
2/2 testing_namespace.test.expectError demo...OK
All 2 tests passed.

```

The Zig Standard Library also contains functions to compare [Slices](14-slices.md#Slices), strings, and more. See the rest of the
`std.testing` namespace in the [Zig Standard Library](02-zig-standard-library.md#Zig-Standard-Library) for more available functions.

#### Test Tool Documentation

`zig test` has a few command line parameters which affect the compilation.
See `zig test --help` for a full list.


---

### Illegal Behavior

Many operations in Zig trigger what is known as "Illegal Behavior" (IB). If Illegal Behavior is detected at
compile-time, Zig emits a compile error and refuses to continue. Otherwise, when Illegal Behavior is not caught
at compile-time, it falls into one of two categories.

Some Illegal Behavior is *safety-checked*: this means that the compiler will insert "safety checks"
anywhere that the Illegal Behavior may occur at runtime, to determine whether it is about to happen. If it
is, the safety check "fails", which triggers a panic.

All other Illegal Behavior is *unchecked*, meaning the compiler is unable to insert safety checks for
it. If Unchecked Illegal Behavior is invoked at runtime, anything can happen: usually that will be some kind of
crash, but the optimizer is free to make Unchecked Illegal Behavior do anything, such as calling arbitrary functions
or clobbering arbitrary data. This is similar to the concept of "undefined behavior" in some other languages. Note that
Unchecked Illegal Behavior still always results in a compile error if evaluated at [comptime](33-comptime.md#comptime), because the Zig
compiler is able to perform more sophisticated checks at compile-time than at runtime.

Most Illegal Behavior is safety-checked. However, to facilitate optimizations, safety checks are disabled by default
in the [ReleaseFast](#ReleaseFast) and [ReleaseSmall](#ReleaseSmall) optimization modes. Safety checks can also be enabled or disabled
on a per-block basis, overriding the default for the current optimization mode, using [@setRuntimeSafety](#setRuntimeSafety). When
safety checks are disabled, Safety-Checked Illegal Behavior behaves like Unchecked Illegal Behavior; that is, any behavior
may result from invoking it.

When a safety check fails, Zig's default panic handler crashes with a stack trace, like this:

**`test_illegal_behavior.zig`:**

```zig
test "safety check" {
    unreachable;
}

```

**Shell:**

```shell
$ zig test test_illegal_behavior.zig
1/1 test_illegal_behavior.test.safety check...thread 2892891 panic: reached unreachable code
/home/andy/dev/zig/doc/langref/test_illegal_behavior.zig:2:5: 0x102c00c in test.safety check (test_illegal_behavior.zig)
    unreachable;
    ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:218:25: 0x115cb20 in mainTerminal (test_runner.zig)
        if (test_fn.func()) |_| {
                        ^
/home/andy/dev/zig/lib/compiler/test_runner.zig:66:28: 0x1155d41 in main (test_runner.zig)
        return mainTerminal();
                           ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x114fadd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x114f371 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
error: the following test command crashed:
/home/andy/dev/zig/.zig-cache/o/e72b27fd3a681a218f2215fb6e7fd433/test --seed=0xeebe2201

```

#### Reaching Unreachable Code

At compile-time:

**`test_comptime_reaching_unreachable.zig`:**

```zig
comptime {
    assert(false);
}
fn assert(ok: bool) void {
    if (!ok) unreachable; // assertion failure
}

```

**Shell:**

```shell
$ zig test test_comptime_reaching_unreachable.zig
/home/andy/dev/zig/doc/langref/test_comptime_reaching_unreachable.zig:5:14: error: reached unreachable code
    if (!ok) unreachable; // assertion failure
             ^~~~~~~~~~~
/home/andy/dev/zig/doc/langref/test_comptime_reaching_unreachable.zig:2:11: note: called at comptime here
    assert(false);
    ~~~~~~^~~~~~~


```

At runtime:

**`runtime_reaching_unreachable.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    std.debug.assert(false);
}

```

**Shell:**

```shell
$ zig build-exe runtime_reaching_unreachable.zig
$ ./runtime_reaching_unreachable
thread 2897013 panic: reached unreachable code
/home/andy/dev/zig/lib/std/debug.zig:559:14: 0x1044179 in assert (std.zig)
    if (!ok) unreachable; // assertion failure
             ^
/home/andy/dev/zig/doc/langref/runtime_reaching_unreachable.zig:4:21: 0x113e86e in main (runtime_reaching_unreachable.zig)
    std.debug.assert(false);
                    ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Index out of Bounds

At compile-time:

**`test_comptime_index_out_of_bounds.zig`:**

```zig
comptime {
    const array: [5]u8 = "hello".*;
    const garbage = array[5];
    _ = garbage;
}

```

**Shell:**

```shell
$ zig test test_comptime_index_out_of_bounds.zig
/home/andy/dev/zig/doc/langref/test_comptime_index_out_of_bounds.zig:3:27: error: index 5 outside array of length 5
    const garbage = array[5];
                          ^


```

At runtime:

**`runtime_index_out_of_bounds.zig`:**

```zig
pub fn main() void {
    const x = foo("hello");
    _ = x;
}

fn foo(x: []const u8) u8 {
    return x[5];
}

```

**Shell:**

```shell
$ zig build-exe runtime_index_out_of_bounds.zig
$ ./runtime_index_out_of_bounds
thread 2893998 panic: index out of bounds: index 5, len 5
/home/andy/dev/zig/doc/langref/runtime_index_out_of_bounds.zig:7:13: 0x113fae6 in foo (runtime_index_out_of_bounds.zig)
    return x[5];
            ^
/home/andy/dev/zig/doc/langref/runtime_index_out_of_bounds.zig:2:18: 0x113e87a in main (runtime_index_out_of_bounds.zig)
    const x = foo("hello");
                 ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Cast Negative Number to Unsigned Integer

At compile-time:

**`test_comptime_invalid_cast.zig`:**

```zig
comptime {
    const value: i32 = -1;
    const unsigned: u32 = @intCast(value);
    _ = unsigned;
}

```

**Shell:**

```shell
$ zig test test_comptime_invalid_cast.zig
/home/andy/dev/zig/doc/langref/test_comptime_invalid_cast.zig:3:36: error: type 'u32' cannot represent integer value '-1'
    const unsigned: u32 = @intCast(value);
                                   ^~~~~


```

At runtime:

**`runtime_invalid_cast.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    var value: i32 = -1; // runtime-known
    _ = &value;
    const unsigned: u32 = @intCast(value);
    std.debug.print("value: {}\n", .{unsigned});
}

```

**Shell:**

```shell
$ zig build-exe runtime_invalid_cast.zig
$ ./runtime_invalid_cast
thread 2899906 panic: integer does not fit in destination type
/home/andy/dev/zig/doc/langref/runtime_invalid_cast.zig:6:27: 0x113e87f in main (runtime_invalid_cast.zig)
    const unsigned: u32 = @intCast(value);
                          ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

To obtain the maximum value of an unsigned integer, use `std.math.maxInt`.

#### Cast Truncates Data

At compile-time:

**`test_comptime_invalid_cast_truncate.zig`:**

```zig
comptime {
    const spartan_count: u16 = 300;
    const byte: u8 = @intCast(spartan_count);
    _ = byte;
}

```

**Shell:**

```shell
$ zig test test_comptime_invalid_cast_truncate.zig
/home/andy/dev/zig/doc/langref/test_comptime_invalid_cast_truncate.zig:3:31: error: type 'u8' cannot represent integer value '300'
    const byte: u8 = @intCast(spartan_count);
                              ^~~~~~~~~~~~~


```

At runtime:

**`runtime_invalid_cast_truncate.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    var spartan_count: u16 = 300; // runtime-known
    _ = &spartan_count;
    const byte: u8 = @intCast(spartan_count);
    std.debug.print("value: {}\n", .{byte});
}

```

**Shell:**

```shell
$ zig build-exe runtime_invalid_cast_truncate.zig
$ ./runtime_invalid_cast_truncate
thread 2899317 panic: integer does not fit in destination type
/home/andy/dev/zig/doc/langref/runtime_invalid_cast_truncate.zig:6:22: 0x113e880 in main (runtime_invalid_cast_truncate.zig)
    const byte: u8 = @intCast(spartan_count);
                     ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

To truncate bits, use [@truncate](#truncate).

#### Integer Overflow

##### Default Operations

The following operators can cause integer overflow:

- `+` (addition)
- `-` (subtraction)
- `-` (negation)
- `*` (multiplication)
- `/` (division)
- [@divTrunc](#divTrunc) (division)
- [@divFloor](#divFloor) (division)
- [@divExact](#divExact) (division)

Example with addition at compile-time:

**`test_comptime_overflow.zig`:**

```zig
comptime {
    var byte: u8 = 255;
    byte += 1;
}

```

**Shell:**

```shell
$ zig test test_comptime_overflow.zig
/home/andy/dev/zig/doc/langref/test_comptime_overflow.zig:3:10: error: overflow of integer type 'u8' with value '256'
    byte += 1;
    ~~~~~^~~~


```

At runtime:

**`runtime_overflow.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    var byte: u8 = 255;
    byte += 1;
    std.debug.print("value: {}\n", .{byte});
}

```

**Shell:**

```shell
$ zig build-exe runtime_overflow.zig
$ ./runtime_overflow
thread 2892886 panic: integer overflow
/home/andy/dev/zig/doc/langref/runtime_overflow.zig:5:10: 0x113e895 in main (runtime_overflow.zig)
    byte += 1;
         ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

##### Standard Library Math Functions

These functions provided by the standard library return possible errors.

- `@import("std").math.add`
- `@import("std").math.sub`
- `@import("std").math.mul`
- `@import("std").math.divTrunc`
- `@import("std").math.divFloor`
- `@import("std").math.divExact`
- `@import("std").math.shl`

Example of catching an overflow for addition:

**`math_add.zig`:**

```zig
const math = @import("std").math;
const print = @import("std").debug.print;
pub fn main() !void {
    var byte: u8 = 255;

    byte = if (math.add(u8, byte, 1)) |result| result else |err| {
        print("unable to add one: {s}\n", .{@errorName(err)});
        return err;
    };

    print("result: {}\n", .{byte});
}

```

**Shell:**

```shell
$ zig build-exe math_add.zig
$ ./math_add
unable to add one: Overflow
error: Overflow
/home/andy/dev/zig/lib/std/math.zig:570:21: 0x113ebae in add__anon_22552 (std.zig)
    if (ov[1] != 0) return error.Overflow;
                    ^
/home/andy/dev/zig/doc/langref/math_add.zig:8:9: 0x113d422 in main (math_add.zig)
        return err;
        ^

```

##### Builtin Overflow Functions

These builtins return a tuple containing whether there was an overflow
(as a `u1`) and the possibly overflowed bits of the operation:

- [@addWithOverflow](#addWithOverflow)
- [@subWithOverflow](#subWithOverflow)
- [@mulWithOverflow](#mulWithOverflow)
- [@shlWithOverflow](#shlWithOverflow)

Example of [@addWithOverflow](#addWithOverflow):

**`addWithOverflow_builtin.zig`:**

```zig
const print = @import("std").debug.print;
pub fn main() void {
    const byte: u8 = 255;

    const ov = @addWithOverflow(byte, 10);
    if (ov[1] != 0) {
        print("overflowed result: {}\n", .{ov[0]});
    } else {
        print("result: {}\n", .{ov[0]});
    }
}

```

**Shell:**

```shell
$ zig build-exe addWithOverflow_builtin.zig
$ ./addWithOverflow_builtin
overflowed result: 9

```

##### Wrapping Operations

These operations have guaranteed wraparound semantics.

- `+%` (wraparound addition)
- `-%` (wraparound subtraction)
- `-%` (wraparound negation)
- `*%` (wraparound multiplication)

**`test_wraparound_semantics.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;
const minInt = std.math.minInt;
const maxInt = std.math.maxInt;

test "wraparound addition and subtraction" {
    const x: i32 = maxInt(i32);
    const min_val = x +% 1;
    try expect(min_val == minInt(i32));
    const max_val = min_val -% 1;
    try expect(max_val == maxInt(i32));
}

```

**Shell:**

```shell
$ zig test test_wraparound_semantics.zig
1/1 test_wraparound_semantics.test.wraparound addition and subtraction...OK
All 1 tests passed.

```

#### Exact Left Shift Overflow

At compile-time:

**`test_comptime_shlExact_overflow.zig`:**

```zig
comptime {
    const x = @shlExact(@as(u8, 0b01010101), 2);
    _ = x;
}

```

**Shell:**

```shell
$ zig test test_comptime_shlExact_overflow.zig
/home/andy/dev/zig/doc/langref/test_comptime_shlExact_overflow.zig:2:15: error: overflow of integer type 'u8' with value '340'
    const x = @shlExact(@as(u8, 0b01010101), 2);
              ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


```

At runtime:

**`runtime_shlExact_overflow.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    var x: u8 = 0b01010101; // runtime-known
    _ = &x;
    const y = @shlExact(x, 2);
    std.debug.print("value: {}\n", .{y});
}

```

**Shell:**

```shell
$ zig build-exe runtime_shlExact_overflow.zig
$ ./runtime_shlExact_overflow
thread 2896313 panic: left shift overflowed bits
/home/andy/dev/zig/doc/langref/runtime_shlExact_overflow.zig:6:5: 0x113e8a1 in main (runtime_shlExact_overflow.zig)
    const y = @shlExact(x, 2);
    ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Exact Right Shift Overflow

At compile-time:

**`test_comptime_shrExact_overflow.zig`:**

```zig
comptime {
    const x = @shrExact(@as(u8, 0b10101010), 2);
    _ = x;
}

```

**Shell:**

```shell
$ zig test test_comptime_shrExact_overflow.zig
/home/andy/dev/zig/doc/langref/test_comptime_shrExact_overflow.zig:2:15: error: exact shift shifted out 1 bits
    const x = @shrExact(@as(u8, 0b10101010), 2);
              ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


```

At runtime:

**`runtime_shrExact_overflow.zig`:**

```zig
const builtin = @import("builtin");
const std = @import("std");

pub fn main() void {
    var x: u8 = 0b10101010; // runtime-known
    _ = &x;
    const y = @shrExact(x, 2);
    std.debug.print("value: {}\n", .{y});

    if (builtin.cpu.arch.isRISCV() and builtin.zig_backend == .stage2_llvm) @panic("https://github.com/ziglang/zig/issues/24304");
}

```

**Shell:**

```shell
$ zig build-exe runtime_shrExact_overflow.zig
$ ./runtime_shrExact_overflow
thread 2897712 panic: right shift overflowed bits
/home/andy/dev/zig/doc/langref/runtime_shrExact_overflow.zig:7:5: 0x113e88a in main (runtime_shrExact_overflow.zig)
    const y = @shrExact(x, 2);
    ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Division by Zero

At compile-time:

**`test_comptime_division_by_zero.zig`:**

```zig
comptime {
    const a: i32 = 1;
    const b: i32 = 0;
    const c = a / b;
    _ = c;
}

```

**Shell:**

```shell
$ zig test test_comptime_division_by_zero.zig
/home/andy/dev/zig/doc/langref/test_comptime_division_by_zero.zig:4:19: error: division by zero here causes illegal behavior
    const c = a / b;
                  ^


```

At runtime:

**`runtime_division_by_zero.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    var a: u32 = 1;
    var b: u32 = 0;
    _ = .{ &a, &b };
    const c = a / b;
    std.debug.print("value: {}\n", .{c});
}

```

**Shell:**

```shell
$ zig build-exe runtime_division_by_zero.zig
$ ./runtime_division_by_zero
thread 2902461 panic: division by zero
/home/andy/dev/zig/doc/langref/runtime_division_by_zero.zig:7:17: 0x113e890 in main (runtime_division_by_zero.zig)
    const c = a / b;
                ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Remainder Division by Zero

At compile-time:

**`test_comptime_remainder_division_by_zero.zig`:**

```zig
comptime {
    const a: i32 = 10;
    const b: i32 = 0;
    const c = a % b;
    _ = c;
}

```

**Shell:**

```shell
$ zig test test_comptime_remainder_division_by_zero.zig
/home/andy/dev/zig/doc/langref/test_comptime_remainder_division_by_zero.zig:4:19: error: division by zero here causes illegal behavior
    const c = a % b;
                  ^


```

At runtime:

**`runtime_remainder_division_by_zero.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    var a: u32 = 10;
    var b: u32 = 0;
    _ = .{ &a, &b };
    const c = a % b;
    std.debug.print("value: {}\n", .{c});
}

```

**Shell:**

```shell
$ zig build-exe runtime_remainder_division_by_zero.zig
$ ./runtime_remainder_division_by_zero
thread 2899727 panic: division by zero
/home/andy/dev/zig/doc/langref/runtime_remainder_division_by_zero.zig:7:17: 0x113e890 in main (runtime_remainder_division_by_zero.zig)
    const c = a % b;
                ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Exact Division Remainder

At compile-time:

**`test_comptime_divExact_remainder.zig`:**

```zig
comptime {
    const a: u32 = 10;
    const b: u32 = 3;
    const c = @divExact(a, b);
    _ = c;
}

```

**Shell:**

```shell
$ zig test test_comptime_divExact_remainder.zig
/home/andy/dev/zig/doc/langref/test_comptime_divExact_remainder.zig:4:15: error: exact division produced remainder
    const c = @divExact(a, b);
              ^~~~~~~~~~~~~~~


```

At runtime:

**`runtime_divExact_remainder.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    var a: u32 = 10;
    var b: u32 = 3;
    _ = .{ &a, &b };
    const c = @divExact(a, b);
    std.debug.print("value: {}\n", .{c});
}

```

**Shell:**

```shell
$ zig build-exe runtime_divExact_remainder.zig
$ ./runtime_divExact_remainder
thread 2901529 panic: exact division produced remainder
/home/andy/dev/zig/doc/langref/runtime_divExact_remainder.zig:7:15: 0x113e8c7 in main (runtime_divExact_remainder.zig)
    const c = @divExact(a, b);
              ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Attempt to Unwrap Null

At compile-time:

**`test_comptime_unwrap_null.zig`:**

```zig
comptime {
    const optional_number: ?i32 = null;
    const number = optional_number.?;
    _ = number;
}

```

**Shell:**

```shell
$ zig test test_comptime_unwrap_null.zig
/home/andy/dev/zig/doc/langref/test_comptime_unwrap_null.zig:3:35: error: unable to unwrap null
    const number = optional_number.?;
                   ~~~~~~~~~~~~~~~^~


```

At runtime:

**`runtime_unwrap_null.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    var optional_number: ?i32 = null;
    _ = &optional_number;
    const number = optional_number.?;
    std.debug.print("value: {}\n", .{number});
}

```

**Shell:**

```shell
$ zig build-exe runtime_unwrap_null.zig
$ ./runtime_unwrap_null
thread 2892887 panic: attempt to use null value
/home/andy/dev/zig/doc/langref/runtime_unwrap_null.zig:6:35: 0x113e8b4 in main (runtime_unwrap_null.zig)
    const number = optional_number.?;
                                  ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

One way to avoid this crash is to test for null instead of assuming non-null, with
the `if` expression:

**`testing_null_with_if.zig`:**

```zig
const print = @import("std").debug.print;
pub fn main() void {
    const optional_number: ?i32 = null;

    if (optional_number) |number| {
        print("got number: {}\n", .{number});
    } else {
        print("it's null\n", .{});
    }
}

```

**Shell:**

```shell
$ zig build-exe testing_null_with_if.zig
$ ./testing_null_with_if
it's null

```

See also:

- [Optionals](29-optionals.md#Optionals)

#### Attempt to Unwrap Error

At compile-time:

**`test_comptime_unwrap_error.zig`:**

```zig
comptime {
    const number = getNumberOrFail() catch unreachable;
    _ = number;
}

fn getNumberOrFail() !i32 {
    return error.UnableToReturnNumber;
}

```

**Shell:**

```shell
$ zig test test_comptime_unwrap_error.zig
/home/andy/dev/zig/doc/langref/test_comptime_unwrap_error.zig:2:44: error: caught unexpected error 'UnableToReturnNumber'
    const number = getNumberOrFail() catch unreachable;
                                           ^~~~~~~~~~~
/home/andy/dev/zig/doc/langref/test_comptime_unwrap_error.zig:7:18: note: error returned here
    return error.UnableToReturnNumber;
                 ^~~~~~~~~~~~~~~~~~~~


```

At runtime:

**`runtime_unwrap_error.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    const number = getNumberOrFail() catch unreachable;
    std.debug.print("value: {}\n", .{number});
}

fn getNumberOrFail() !i32 {
    return error.UnableToReturnNumber;
}

```

**Shell:**

```shell
$ zig build-exe runtime_unwrap_error.zig
$ ./runtime_unwrap_error
thread 2895126 panic: attempt to unwrap error: UnableToReturnNumber
/home/andy/dev/zig/doc/langref/runtime_unwrap_error.zig:9:5: 0x113e86c in getNumberOrFail (runtime_unwrap_error.zig)
    return error.UnableToReturnNumber;
    ^
/home/andy/dev/zig/doc/langref/runtime_unwrap_error.zig:4:44: 0x113e8d3 in main (runtime_unwrap_error.zig)
    const number = getNumberOrFail() catch unreachable;
                                           ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

One way to avoid this crash is to test for an error instead of assuming a successful result, with
the `if` expression:

**`testing_error_with_if.zig`:**

```zig
const print = @import("std").debug.print;

pub fn main() void {
    const result = getNumberOrFail();

    if (result) |number| {
        print("got number: {}\n", .{number});
    } else |err| {
        print("got error: {s}\n", .{@errorName(err)});
    }
}

fn getNumberOrFail() !i32 {
    return error.UnableToReturnNumber;
}

```

**Shell:**

```shell
$ zig build-exe testing_error_with_if.zig
$ ./testing_error_with_if
got error: UnableToReturnNumber

```

See also:

- [Errors](28-errors.md#Errors)

#### Invalid Error Code

At compile-time:

**`test_comptime_invalid_error_code.zig`:**

```zig
comptime {
    const err = error.AnError;
    const number = @intFromError(err) + 10;
    const invalid_err = @errorFromInt(number);
    _ = invalid_err;
}

```

**Shell:**

```shell
$ zig test test_comptime_invalid_error_code.zig
/home/andy/dev/zig/doc/langref/test_comptime_invalid_error_code.zig:4:39: error: integer value '11' represents no error
    const invalid_err = @errorFromInt(number);
                                      ^~~~~~


```

At runtime:

**`runtime_invalid_error_code.zig`:**

```zig
const std = @import("std");

pub fn main() void {
    const err = error.AnError;
    var number = @intFromError(err) + 500;
    _ = &number;
    const invalid_err = @errorFromInt(number);
    std.debug.print("value: {}\n", .{invalid_err});
}

```

**Shell:**

```shell
$ zig build-exe runtime_invalid_error_code.zig
$ ./runtime_invalid_error_code
thread 2900570 panic: invalid error code
/home/andy/dev/zig/doc/langref/runtime_invalid_error_code.zig:7:5: 0x113e8a7 in main (runtime_invalid_error_code.zig)
    const invalid_err = @errorFromInt(number);
    ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Invalid Enum Cast

At compile-time:

**`test_comptime_invalid_enum_cast.zig`:**

```zig
const Foo = enum {
    a,
    b,
    c,
};
comptime {
    const a: u2 = 3;
    const b: Foo = @enumFromInt(a);
    _ = b;
}

```

**Shell:**

```shell
$ zig test test_comptime_invalid_enum_cast.zig
/home/andy/dev/zig/doc/langref/test_comptime_invalid_enum_cast.zig:8:20: error: enum 'test_comptime_invalid_enum_cast.Foo' has no tag with value '3'
    const b: Foo = @enumFromInt(a);
                   ^~~~~~~~~~~~~~~
/home/andy/dev/zig/doc/langref/test_comptime_invalid_enum_cast.zig:1:13: note: enum declared here
const Foo = enum {
            ^~~~


```

At runtime:

**`runtime_invalid_enum_cast.zig`:**

```zig
const std = @import("std");

const Foo = enum {
    a,
    b,
    c,
};

pub fn main() void {
    var a: u2 = 3;
    _ = &a;
    const b: Foo = @enumFromInt(a);
    std.debug.print("value: {s}\n", .{@tagName(b)});
}

```

**Shell:**

```shell
$ zig build-exe runtime_invalid_enum_cast.zig
$ ./runtime_invalid_enum_cast
thread 2902395 panic: invalid enum value
/home/andy/dev/zig/doc/langref/runtime_invalid_enum_cast.zig:12:20: 0x113e8f0 in main (runtime_invalid_enum_cast.zig)
    const b: Foo = @enumFromInt(a);
                   ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Invalid Error Set Cast

At compile-time:

**`test_comptime_invalid_error_set_cast.zig`:**

```zig
const Set1 = error{
    A,
    B,
};
const Set2 = error{
    A,
    C,
};
comptime {
    _ = @as(Set2, @errorCast(Set1.B));
}

```

**Shell:**

```shell
$ zig test test_comptime_invalid_error_set_cast.zig
/home/andy/dev/zig/doc/langref/test_comptime_invalid_error_set_cast.zig:10:19: error: 'error.B' not a member of error set 'error{A,C}'
    _ = @as(Set2, @errorCast(Set1.B));
                  ^~~~~~~~~~~~~~~~~~


```

At runtime:

**`runtime_invalid_error_set_cast.zig`:**

```zig
const std = @import("std");

const Set1 = error{
    A,
    B,
};
const Set2 = error{
    A,
    C,
};
pub fn main() void {
    foo(Set1.B);
}
fn foo(set1: Set1) void {
    const x: Set2 = @errorCast(set1);
    std.debug.print("value: {}\n", .{x});
}

```

**Shell:**

```shell
$ zig build-exe runtime_invalid_error_set_cast.zig
$ ./runtime_invalid_error_set_cast
thread 2900078 panic: invalid error code
/home/andy/dev/zig/doc/langref/runtime_invalid_error_set_cast.zig:15:21: 0x113fb3c in foo (runtime_invalid_error_set_cast.zig)
    const x: Set2 = @errorCast(set1);
                    ^
/home/andy/dev/zig/doc/langref/runtime_invalid_error_set_cast.zig:12:8: 0x113e877 in main (runtime_invalid_error_set_cast.zig)
    foo(Set1.B);
       ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Incorrect Pointer Alignment

At compile-time:

**`test_comptime_incorrect_pointer_alignment.zig`:**

```zig
comptime {
    const ptr: *align(1) i32 = @ptrFromInt(0x1);
    const aligned: *align(4) i32 = @alignCast(ptr);
    _ = aligned;
}

```

**Shell:**

```shell
$ zig test test_comptime_incorrect_pointer_alignment.zig
/home/andy/dev/zig/doc/langref/test_comptime_incorrect_pointer_alignment.zig:3:47: error: pointer address 0x1 is not aligned to 4 bytes
    const aligned: *align(4) i32 = @alignCast(ptr);
                                              ^~~


```

At runtime:

**`runtime_incorrect_pointer_alignment.zig`:**

```zig
const mem = @import("std").mem;
pub fn main() !void {
    var array align(4) = [_]u32{ 0x11111111, 0x11111111 };
    const bytes = mem.sliceAsBytes(array[0..]);
    if (foo(bytes) != 0x11111111) return error.Wrong;
}
fn foo(bytes: []u8) u32 {
    const slice4 = bytes[1..5];
    const int_slice = mem.bytesAsSlice(u32, @as([]align(4) u8, @alignCast(slice4)));
    return int_slice[0];
}

```

**Shell:**

```shell
$ zig build-exe runtime_incorrect_pointer_alignment.zig
$ ./runtime_incorrect_pointer_alignment
thread 2897041 panic: incorrect alignment
/home/andy/dev/zig/doc/langref/runtime_incorrect_pointer_alignment.zig:9:64: 0x113ec08 in foo (runtime_incorrect_pointer_alignment.zig)
    const int_slice = mem.bytesAsSlice(u32, @as([]align(4) u8, @alignCast(slice4)));
                                                               ^
/home/andy/dev/zig/doc/langref/runtime_incorrect_pointer_alignment.zig:5:12: 0x113d3f2 in main (runtime_incorrect_pointer_alignment.zig)
    if (foo(bytes) != 0x11111111) return error.Wrong;
           ^
/home/andy/dev/zig/lib/std/start.zig:627:37: 0x113dbc9 in posixCallMainAndExit (std.zig)
            const result = root.main() catch |err| {
                                    ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Wrong Union Field Access

At compile-time:

**`test_comptime_wrong_union_field_access.zig`:**

```zig
comptime {
    var f = Foo{ .int = 42 };
    f.float = 12.34;
}

const Foo = union {
    float: f32,
    int: u32,
};

```

**Shell:**

```shell
$ zig test test_comptime_wrong_union_field_access.zig
/home/andy/dev/zig/doc/langref/test_comptime_wrong_union_field_access.zig:3:6: error: access of union field 'float' while field 'int' is active
    f.float = 12.34;
    ~^~~~~~
/home/andy/dev/zig/doc/langref/test_comptime_wrong_union_field_access.zig:6:13: note: union declared here
const Foo = union {
            ^~~~~


```

At runtime:

**`runtime_wrong_union_field_access.zig`:**

```zig
const std = @import("std");

const Foo = union {
    float: f32,
    int: u32,
};

pub fn main() void {
    var f = Foo{ .int = 42 };
    bar(&f);
}

fn bar(f: *Foo) void {
    f.float = 12.34;
    std.debug.print("value: {}\n", .{f.float});
}

```

**Shell:**

```shell
$ zig build-exe runtime_wrong_union_field_access.zig
$ ./runtime_wrong_union_field_access
thread 2901950 panic: access of union field 'float' while field 'int' is active
/home/andy/dev/zig/doc/langref/runtime_wrong_union_field_access.zig:14:6: 0x113fb1e in bar (runtime_wrong_union_field_access.zig)
    f.float = 12.34;
     ^
/home/andy/dev/zig/doc/langref/runtime_wrong_union_field_access.zig:10:8: 0x113e89f in main (runtime_wrong_union_field_access.zig)
    bar(&f);
       ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

This safety is not available for `extern` or `packed` unions.

To change the active field of a union, assign the entire union, like this:

**`change_active_union_field.zig`:**

```zig
const std = @import("std");

const Foo = union {
    float: f32,
    int: u32,
};

pub fn main() void {
    var f = Foo{ .int = 42 };
    bar(&f);
}

fn bar(f: *Foo) void {
    f.* = Foo{ .float = 12.34 };
    std.debug.print("value: {}\n", .{f.float});
}

```

**Shell:**

```shell
$ zig build-exe change_active_union_field.zig
$ ./change_active_union_field
value: 12.34

```

To change the active field of a union when a meaningful value for the field is not known,
use [undefined](#undefined), like this:

**`undefined_active_union_field.zig`:**

```zig
const std = @import("std");

const Foo = union {
    float: f32,
    int: u32,
};

pub fn main() void {
    var f = Foo{ .int = 42 };
    f = Foo{ .float = undefined };
    bar(&f);
    std.debug.print("value: {}\n", .{f.float});
}

fn bar(f: *Foo) void {
    f.float = 12.34;
}

```

**Shell:**

```shell
$ zig build-exe undefined_active_union_field.zig
$ ./undefined_active_union_field
value: 12.34

```

See also:

- [union](17-union.md#union)
- [extern union](#extern-union)

#### Out of Bounds Float to Integer Cast

This happens when casting a float to an integer where the float has a value outside the
integer type's range.

At compile-time:

**`test_comptime_out_of_bounds_float_to_integer_cast.zig`:**

```zig
comptime {
    const float: f32 = 4294967296;
    const int: i32 = @intFromFloat(float);
    _ = int;
}

```

**Shell:**

```shell
$ zig test test_comptime_out_of_bounds_float_to_integer_cast.zig
/home/andy/dev/zig/doc/langref/test_comptime_out_of_bounds_float_to_integer_cast.zig:3:36: error: float value '4294967296' cannot be stored in integer type 'i32'
    const int: i32 = @intFromFloat(float);
                                   ^~~~~


```

At runtime:

**`runtime_out_of_bounds_float_to_integer_cast.zig`:**

```zig
pub fn main() void {
    var float: f32 = 4294967296; // runtime-known
    _ = &float;
    const int: i32 = @intFromFloat(float);
    _ = int;
}

```

**Shell:**

```shell
$ zig build-exe runtime_out_of_bounds_float_to_integer_cast.zig
$ ./runtime_out_of_bounds_float_to_integer_cast
thread 2898584 panic: integer part of floating point value out of bounds
/home/andy/dev/zig/doc/langref/runtime_out_of_bounds_float_to_integer_cast.zig:4:22: 0x113e8d2 in main (runtime_out_of_bounds_float_to_integer_cast.zig)
    const int: i32 = @intFromFloat(float);
                     ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```

#### Pointer Cast Invalid Null

This happens when casting a pointer with the address 0 to a pointer which may not have the address 0.
For example, [C Pointers](45-c.md#C-Pointers), [Optional Pointers](#Optional-Pointers), and [allowzero](#allowzero) pointers
allow address zero, but normal [Pointers](13-pointers.md#Pointers) do not.

At compile-time:

**`test_comptime_invalid_null_pointer_cast.zig`:**

```zig
comptime {
    const opt_ptr: ?*i32 = null;
    const ptr: *i32 = @ptrCast(opt_ptr);
    _ = ptr;
}

```

**Shell:**

```shell
$ zig test test_comptime_invalid_null_pointer_cast.zig
/home/andy/dev/zig/doc/langref/test_comptime_invalid_null_pointer_cast.zig:3:32: error: null pointer casted to type '*i32'
    const ptr: *i32 = @ptrCast(opt_ptr);
                               ^~~~~~~


```

At runtime:

**`runtime_invalid_null_pointer_cast.zig`:**

```zig
pub fn main() void {
    var opt_ptr: ?*i32 = null;
    _ = &opt_ptr;
    const ptr: *i32 = @ptrCast(opt_ptr);
    _ = ptr;
}

```

**Shell:**

```shell
$ zig build-exe runtime_invalid_null_pointer_cast.zig
$ ./runtime_invalid_null_pointer_cast
thread 2892939 panic: cast causes pointer to be null
/home/andy/dev/zig/doc/langref/runtime_invalid_null_pointer_cast.zig:4:23: 0x113e88a in main (runtime_invalid_null_pointer_cast.zig)
    const ptr: *i32 = @ptrCast(opt_ptr);
                      ^
/home/andy/dev/zig/lib/std/start.zig:618:22: 0x113dabd in posixCallMainAndExit (std.zig)
            root.main();
                     ^
/home/andy/dev/zig/lib/std/start.zig:232:5: 0x113d351 in _start (std.zig)
    asm volatile (switch (native_arch) {
    ^
???:?:?: 0x0 in ??? (???)
(process terminated by signal)

```


---

### Style Guide

These coding conventions are not enforced by the compiler, but they are shipped in
this documentation along with the compiler in order to provide a point of
reference, should anyone wish to point to an authority on agreed upon Zig
coding style.

#### Avoid Redundancy in Names

Avoid these words in type names:

- Value
- Data
- Context
- Manager
- utils, misc, or somebody's initials

Everything is a value, all types are data, everything is context, all logic manages state.
Nothing is communicated by using a word that applies to all types.

Temptation to use "utilities", "miscellaneous", or somebody's initials
is a failure to categorize, or more commonly, overcategorization. Such
declarations can live at the root of a module that needs them with no
namespace needed.

#### Avoid Redundant Names in Fully-Qualified Namespaces

Every declaration is assigned a **fully qualified
namespace** by the compiler, creating a tree structure. Choose names based
on the fully-qualified namespace, and avoid redundant name segments.

**`redundant_fqn.zig`:**

```zig
const std = @import("std");

pub const json = struct {
    pub const JsonValue = union(enum) {
        number: f64,
        boolean: bool,
        // ...
    };
};

pub fn main() void {
    std.debug.print("{s}\n", .{@typeName(json.JsonValue)});
}

```

**Shell:**

```shell
$ zig build-exe redundant_fqn.zig
$ ./redundant_fqn
redundant_fqn.json.JsonValue

```

In this example, "json" is repeated in the fully-qualified namespace. The solution
is to delete `Json` from `JsonValue`. In this example we have
an empty struct named `json` but remember that files also act
as part of the fully-qualified namespace.

This example is an exception to the rule specified in [Avoid Redundancy in Names](#Avoid-Redundancy-in-Names).
The meaning of the type has been reduced to its core: it is a json value. The name
cannot be any more specific without being incorrect.

#### Whitespace

- 4 space indentation
- Open braces on same line, unless you need to wrap.
- If a list of things is longer than 2, put each item on its own line and
  exercise the ability to put an extra comma at the end.
- Line length: aim for 100; use common sense.

#### Names

Roughly speaking: `camelCaseFunctionName`, `TitleCaseTypeName`,
`snake_case_variable_name`. More precisely:

- If `x` is a `type`
  then `x` should be `TitleCase`, unless it
  is a `struct` with 0 fields and is never meant to be instantiated,
  in which case it is considered to be a "namespace" and uses `snake_case`.
- If `x` is callable, and `x`'s return type is
  `type`, then `x` should be `TitleCase`.
- If `x` is otherwise callable, then `x` should
  be `camelCase`.
- Otherwise, `x` should be `snake_case`.

Acronyms, initialisms, proper nouns, or any other word that has capitalization
rules in written English are subject to naming conventions just like any other
word. Even acronyms that are only 2 letters long are subject to these
conventions.

File names fall into two categories: types and namespaces. If the file
(implicitly a struct) has top level fields, it should be named like any
other struct with fields using `TitleCase`. Otherwise,
it should use `snake_case`. Directory names should be
`snake_case`.

These are general rules of thumb; if it makes sense to do something different,
do what makes sense. For example, if there is an established convention such as
`ENOENT`, follow the established convention.

#### Examples

**`style_example.zig`:**

```zig
const namespace_name = @import("dir_name/file_name.zig");
const TypeName = @import("dir_name/TypeName.zig");
var global_var: i32 = undefined;
const const_name = 42;
const primitive_type_alias = f32;
const string_alias = []u8;

const StructName = struct {
    field: i32,
};
const StructAlias = StructName;

fn functionName(param_name: TypeName) void {
    var functionPointer = functionName;
    functionPointer();
    functionPointer = otherFunction;
    functionPointer();
}
const functionAlias = functionName;

fn ListTemplateFunction(comptime ChildType: type, comptime fixed_size: usize) type {
    return List(ChildType, fixed_size);
}

fn ShortList(comptime T: type, comptime n: usize) type {
    return struct {
        field_name: [n]T,
        fn methodName() void {}
    };
}

// The word XML loses its casing when used in Zig identifiers.
const xml_document =
    \\<?xml version="1.0" encoding="UTF-8"?>
    \\<document>
    \\</document>
;
const XmlParser = struct {
    field: i32,
};

// The initials BE (Big Endian) are just another word in Zig identifier names.
fn readU32Be() u32 {}

```

See the [Zig Standard Library](02-zig-standard-library.md#Zig-Standard-Library) for more examples.

#### Doc Comment Guidance

- Omit any information that is redundant based on the name of the thing being documented.
- Duplicating information onto multiple similar functions is encouraged because it helps IDEs and other tools provide better help text.
- Use the word **assume** to indicate invariants that cause *unchecked* [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior) when violated.
- Use the word **assert** to indicate invariants that cause *safety-checked* [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior) when violated.


---

### Source Encoding

Zig source code is encoded in UTF-8. An invalid UTF-8 byte sequence results in a compile error.

Throughout all zig source code (including in comments), some code points are never allowed:

- Ascii control characters, except for U+000a (LF), U+000d (CR), and U+0009 (HT): U+0000 - U+0008, U+000b - U+000c, U+000e - U+0001f, U+007f.
- Non-Ascii Unicode line endings: U+0085 (NEL), U+2028 (LS), U+2029 (PS).

LF (byte value 0x0a, code point U+000a, `'\n'`) is the line terminator in Zig source code.
This byte value terminates every line of zig source code except the last line of the file.
It is recommended that non-empty source files end with an empty line, which means the last byte would be 0x0a (LF).

Each LF may be immediately preceded by a single CR (byte value 0x0d, code point U+000d, `'\r'`)
to form a Windows style line ending, but this is discouraged. Note that in multiline strings, CRLF sequences will
be encoded as LF when compiled into a zig program.
A CR in any other context is not allowed.

HT hard tabs (byte value 0x09, code point U+0009, `'\t'`) are interchangeable with
SP spaces (byte value 0x20, code point U+0020, `' '`) as a token separator,
but use of hard tabs is discouraged. See [Grammar](#Grammar).

For compatibility with other tools, the compiler ignores a UTF-8-encoded byte order mark (U+FEFF)
if it is the first Unicode code point in the source text. A byte order mark is not allowed anywhere else in the source.

Note that running `zig fmt` on a source file will implement all recommendations mentioned here.

Note that a tool reading Zig source code can make assumptions if the source code is assumed to be correct Zig code.
For example, when identifying the ends of lines, a tool can use a naive search such as `/\n/`,
or an [advanced](https://msdn.microsoft.com/en-us/library/dd409797.aspx)
search such as `/\r\n?|[\n\u0085\u2028\u2029]/`, and in either case line endings will be correctly identified.
For another example, when identifying the whitespace before the first token on a line,
a tool can either use a naive search such as `/[ \t]/`,
or an [advanced](https://tc39.es/ecma262/#sec-characterclassescape) search such as `/\s/`,
and in either case whitespace will be correctly identified.


---
