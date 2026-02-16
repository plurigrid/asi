# Testing and Code Quality

*Testing framework, undefined behavior, and best practices*


---

### Zig Test

Code written within one or more `test` declarations can be used to ensure behavior meets expectations:

**`introducing_zig_test.zig`:**

```zig
const std = @import("std");

test "expect addOne adds one to 41" {

    // The Standard Library contains useful functions to help create tests.
    // `expect` is a function that verifies its argument is true.
    // It will return an error if its argument is false to indicate a failure.
    // `try` is used to return an error to the test runner to notify it that the test failed.
    try std.testing.expect(addOne(41) == 42);
}

/// The function `addOne` adds one to the number given as its argument.
fn addOne(number: i32) i32 {
    return number + 1;
}

```

**Shell:**

```shell
$ zig test introducing_zig_test.zig
1/1 test "expect addOne adds one to 41"... OK
All 1 tests passed.

```

The `introducing_zig_test.zig` code sample tests the [function](27-functions.md#Functions)
`addOne` to ensure that it returns `42` given the input
`41`. From this test's perspective, the `addOne` function is
said to be *code under test*.

`zig test` is a tool that creates and runs a test build. By default, it builds and runs an
executable program using the *default test runner* provided by the [Zig Standard Library](02-zig-standard-library.md#Zig-Standard-Library)
as its main entry point. During the build, `test` declarations found while
[resolving](44-root-source-file.md#Root-Source-File) the given Zig source file are included for the default test runner
to run and report on.

> **Note:** 
This documentation discusses the features of the default test runner as provided by the Zig Standard Library.
Its source code is located in `lib/std/special/test_runner.zig`.

The shell output shown above displays two lines after the `zig test` command. These lines are
printed to standard error by the default test runner:

**Test [1/1] test "expect addOne adds one to 41"...**
: Lines like this indicate which test, out of the total number of tests, is being run.
          In this case, [1/1] indicates that the first test, out of a total of
          one test, is being run. Note that, when the test runner program's standard error is output
          to the terminal, these lines are cleared when a test succeeds.

**All 1 tests passed.**
: This line indicates the total number of tests that have passed.

#### Test Declarations

Test declarations contain the [keyword](51-keyword-reference.md#Keyword-Reference) `test`, followed by an
optional name written as a [string literal](#String-Literals-and-Unicode-Code-Point-Literals), followed
by a [block](19-blocks.md#blocks) containing any valid Zig code that is allowed in a [function](27-functions.md#Functions).

> **Note:** 
By convention, non-named tests should only be used to [make other tests run](#Nested-Container-Tests).
Non-named tests cannot be [filtered](#Skip-Tests).

Test declarations are similar to [Functions](27-functions.md#Functions): they have a return type and a block of code. The implicit
return type of `test` is the [Error Union Type](#Error-Union-Type) `anyerror!void`,
and it cannot be changed. When a Zig source file is not built using the `zig test` tool, the test
declarations are omitted from the build.

Test declarations can be written in the same file, where code under test is written, or in a separate Zig source file.
Since test declarations are top-level declarations, they are order-independent and can
be written before or after the code under test.

See also:

- [The Global Error Set](#The-Global-Error-Set)
- [Grammar](52-grammar.md#Grammar)

#### Nested Container Tests

When the `zig test` tool is building a test runner, only resolved `test`
declarations are included in the build. Initially, only the given Zig source file's top-level
declarations are resolved. Unless nested containers are referenced from a top-level test declaration,
nested container tests will not be resolved.

The code sample below uses the `std.testing.refAllDecls(@This())` function call to
reference all of the containers that are in the file including the imported Zig source file. The code
sample also shows an alternative way to reference containers using the `_ = C;`
syntax. This syntax tells the compiler to ignore the result of the expression on the right side of the
assignment operator.

**`testdecl_container_top_level.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

// Imported source file tests will run when referenced from a top-level test declaration.
// The next line alone does not cause "introducing_zig_test.zig" tests to run.
const imported_file = @import("introducing_zig_test.zig");

test {
    // To run nested container tests, either, call `refAllDecls` which will
    // reference all declarations located in the given argument.
    // `@This()` is a builtin function that returns the innermost container it is called from.
    // In this example, the innermost container is this file (implicitly a struct).
    std.testing.refAllDecls(@This());

    // or, reference each container individually from a top-level test declaration.
    // The `_ = C;` syntax is a no-op reference to the identifier `C`.
    _ = S;
    _ = U;
    _ = @import("introducing_zig_test.zig");
}

const S = struct {
    test "S demo test" {
        try expect(true);
    }

    const SE = enum {
        V,

        // This test won't run because its container (SE) is not referenced.
        test "This Test Won't Run" {
            try expect(false);
        }
    };
};

const U = union { // U is referenced by the file's top-level test declaration
    s: US,        // and US is referenced here; therefore, "U.Us demo test" will run

    const US = struct {
        test "U.US demo test" {
            // This test is a top-level test declaration for the struct.
            // The struct is nested (declared) inside of a union.
            try expect(true);
        }
    };

    test "U demo test" {
        try expect(true);
    }
};

```

**Shell:**

```shell
$ zig test testdecl_container_top_level.zig
1/5 test ""... OK
2/5 S.test "S demo test"... OK
3/5 U.test "U demo test"... OK
4/5 introducing_zig_test.test "expect addOne adds one to 41"... OK
5/5 US.test "U.US demo test"... OK
All 5 tests passed.

```

#### Test Failure

The default test runner checks for an [error](28-errors.md#Errors) returned from a test.
When a test returns an error, the test is considered a failure and its [error return trace](#Error-Return-Traces)
is output to standard error. The total number of failures will be reported after all tests have run.

**`test.zig`:**

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
$ zig test test.zig
1/2 test "expect this to fail"... test "expect this to fail"... FAIL (TestUnexpectedResult)
FAIL (TestUnexpectedResult)
/home/andy/tmp/zig/lib/std/testing.zig:303:14: 0x207ebb in std.testing.expect (test)
    if (!ok) return error.TestUnexpectedResult;
             ^
/home/andy/tmp/zig/docgen_tmp/test.zig:4:5: 0x2078f1 in test "expect this to fail" (test)
    try std.testing.expect(false);
    ^
2/2 test "expect this to succeed"... OK
1 passed; 0 skipped; 1 failed.
error: the following test command failed with exit code 1:
docgen_tmp/zig-cache/o/e62d5b643d08f1acbb1386db92eb0f23/test /home/andy/tmp/zig/build-release/zig

```

#### Skip Tests

One way to skip tests is to filter them out by using the `zig test` command line parameter
`--test-filter [text]`. This makes the test build only include tests whose name contains the
supplied filter text. Note that non-named tests are run even when using the `--test-filter [text]`
command line parameter.

To programmatically skip a test, make a `test` return the error
`error.SkipZigTest` and the default test runner will consider the test as being skipped.
The total number of skipped tests will be reported after all tests have run.

**`test.zig`:**

```zig
test "this will be skipped" {
    return error.SkipZigTest;
}

```

**Shell:**

```shell
$ zig test test.zig
1/1 test "this will be skipped"... test "this will be skipped"... SKIP
SKIP
0 passed; 1 skipped; 0 failed.

```

The default test runner skips tests containing a [suspend point](37-async-functions.md#Async-Functions) while the
test is running using the default, blocking IO mode.
(The evented IO mode is enabled using the `--test-evented-io` command line parameter.)

**`async_skip.zig`:**

```zig
const std = @import("std");

test "async skip test" {
    var frame = async func();
    const result = await frame;
    try std.testing.expect(result == 1);
}

fn func() i32 {
    suspend {
        resume @frame();
    }
    return 1;
}

```

**Shell:**

```shell
$ zig test async_skip.zig
1/1 test "async skip test"... test "async skip test"... SKIP (async test)
SKIP (async test)
0 passed; 1 skipped; 0 failed.

```

In the code sample above, the test would not be skipped in blocking IO mode if the `nosuspend`
keyword was used (see [Async and Await](#Async-and-Await)).

#### Report Memory Leaks

When code allocates [Memory](42-memory.md#Memory) using the [Zig Standard Library](02-zig-standard-library.md#Zig-Standard-Library)'s testing allocator,
`std.testing.allocator`, the default test runner will report any leaks that are
found from using the testing allocator:

**`test.zig`:**

```zig
const std = @import("std");

test "detect leak" {
    var list = std.ArrayList(u21).init(std.testing.allocator);
    // missing `defer list.deinit();`
    try list.append('â');

    try std.testing.expect(list.items.len == 1);
}

```

**Shell:**

```shell
$ zig test test.zig
1/1 test "detect leak"... OK
[gpa] (err): memory address 0x7ff65e3b1000 leaked:
/home/andy/tmp/zig/lib/std/array_list.zig:325:69: 0x20ce89 in std.array_list.ArrayListAligned(u21,null).ensureTotalCapacityPrecise (test)
                const new_memory = try self.allocator.reallocAtLeast(self.allocatedSlice(), new_capacity);
                                                                    ^
/home/andy/tmp/zig/lib/std/array_list.zig:310:55: 0x20cc8e in std.array_list.ArrayListAligned(u21,null).ensureTotalCapacity (test)
                return self.ensureTotalCapacityPrecise(better_capacity);
                                                      ^
/home/andy/tmp/zig/lib/std/array_list.zig:349:41: 0x20cc08 in std.array_list.ArrayListAligned(u21,null).addOne (test)
            try self.ensureTotalCapacity(newlen);
                                        ^
/home/andy/tmp/zig/lib/std/array_list.zig:161:49: 0x209204 in std.array_list.ArrayListAligned(u21,null).append (test)
            const new_item_ptr = try self.addOne();
                                                ^
/home/andy/tmp/zig/docgen_tmp/test.zig:6:20: 0x208be0 in test "detect leak" (test)
    try list.append('â');
                   ^
/home/andy/tmp/zig/lib/std/special/test_runner.zig:80:28: 0x23b033 in std.special.main (test)
        } else test_fn.func();
                           ^
/home/andy/tmp/zig/lib/std/start.zig:551:22: 0x23390c in std.start.callMain (test)
            root.main();
                     ^
/home/andy/tmp/zig/lib/std/start.zig:495:12: 0x20dc7e in std.start.callMainWithArgs (test)
    return @call(.{ .modifier = .always_inline }, callMain, .{});
           ^


All 1 tests passed.
1 errors were logged.
1 tests leaked memory.
error: the following test command failed with exit code 1:
docgen_tmp/zig-cache/o/e62d5b643d08f1acbb1386db92eb0f23/test /home/andy/tmp/zig/build-release/zig

```

See also:

- [defer](24-defer.md#defer)
- [Memory](42-memory.md#Memory)

#### Detecting Test Build

Use the [compile variable](43-compile-variables.md#Compile-Variables) `@import("builtin").is_test`
to detect a test build:

**`detect_test.zig`:**

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
$ zig test detect_test.zig
1/1 test "builtin.is_test"... OK
All 1 tests passed.

```

#### Test Output and Logging

The default test runner and the Zig Standard Library's testing namespace output messages to standard error.

#### The Testing Namespace

The Zig Standard Library's `testing` namespace contains useful functions to help
you create tests. In addition to the `expect` function, this document uses a couple of more functions
as exemplified here:

**`testing_functions.zig`:**

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
$ zig test testing_functions.zig
1/2 test "expectEqual demo"... OK
2/2 test "expectError demo"... OK
All 2 tests passed.

```

The Zig Standard Library also contains functions to compare [Slices](14-slices.md#Slices), strings, and more. See the rest of the
`std.testing` namespace in the [Zig Standard Library](02-zig-standard-library.md#Zig-Standard-Library) for more available functions.

#### Test Tool Documentation

`zig test` has a few command line parameters which affect the compilation.
See `zig test --help` for a full list.


---
