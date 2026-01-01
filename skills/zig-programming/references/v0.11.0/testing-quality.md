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
1/2 test.expect addOne adds one to 41... OK
2/2 decltest.addOne... OK
All 2 tests passed.

```

The `testing_introduction.zig` code sample tests the [function](27-functions.md#Functions)
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
Its source code is located in `lib/test_runner.zig`.

The shell output shown above displays two lines after the `zig test` command. These lines are
printed to standard error by the default test runner:

**Test [1/2] test.expect addOne adds one to 41...**
: Lines like this indicate which test, out of the total number of tests, is being run.
          In this case, [1/2] indicates that the first test, out of a total of
          two test, is being run. Note that, when the test runner program's standard error is output
          to the terminal, these lines are cleared when a test succeeds.

**Test [2/2] decltest.addOne...**
: When the test name is an identifier, the default test runner uses the text
          decltest instead of test.

**All 2 tests passed.**
: This line indicates the total number of tests that have passed.

#### Test Declarations

Test declarations contain the [keyword](51-keyword-reference.md#Keyword-Reference) `test`, followed by an
optional name written as a [string literal](#String-Literals-and-Unicode-Code-Point-Literals) or an
[identifier](#Identifiers), followed by a [block](19-blocks.md#Blocks) containing any valid Zig code that
is allowed in a [function](27-functions.md#Functions).

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
- [Grammar](#Grammar)

#### Nested Container Tests

When the `zig test` tool is building a test runner, only resolved `test`
declarations are included in the build. Initially, only the given Zig source file's top-level
declarations are resolved. Unless nested [containers](46-c.md#Containers) are referenced from a top-level test declaration,
nested container tests will not be resolved.

The code sample below uses the `std.testing.refAllDecls(@This())` function call to
reference all of the containers that are in the file including the imported Zig source file. The code
sample also shows an alternative way to reference containers using the `_ = C;`
syntax. This syntax tells the compiler to ignore the result of the expression on the right side of the
assignment operator.

**`testing_nested_container_tests.zig`:**

```zig
const std = @import("std");
const expect = std.testing.expect;

// Imported source file tests will run when referenced from a top-level test declaration.
// The next line alone does not cause "testing_introduction.zig" tests to run.
const imported_file = @import("testing_introduction.zig");

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
    _ = @import("testing_introduction.zig");
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
$ zig test testing_nested_container_tests.zig
1/5 test_0... OK
2/5 test.S demo test... OK
3/5 test.U demo test... OK
4/5 test.expect addOne adds one to 41... OK
5/5 decltest.addOne... OK
All 5 tests passed.

```

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
1/2 test.expect this to fail... FAIL (TestUnexpectedResult)
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/testing.zig:515:14: 0x22425f in expect (test)
    if (!ok) return error.TestUnexpectedResult;
             ^
/home/ci/actions-runner/_work/zig-bootstrap/zig/docgen_tmp/testing_failure.zig:4:5: 0x224375 in test.expect this to fail (test)
    try std.testing.expect(false);
    ^
2/2 test.expect this to succeed... OK
1 passed; 0 skipped; 1 failed.
error: the following test command failed with exit code 1:
/home/ci/actions-runner/_work/zig-bootstrap/out/zig-local-cache/o/d4ffa468bf575e495decf1a50d3bbe44/test

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
1/1 test.this will be skipped... SKIP
0 passed; 1 skipped; 0 failed.

```

#### Report Memory Leaks

When code allocates [Memory](42-memory.md#Memory) using the [Zig Standard Library](02-zig-standard-library.md#Zig-Standard-Library)'s testing allocator,
`std.testing.allocator`, the default test runner will report any leaks that are
found from using the testing allocator:

**`testing_detect_leak.zig`:**

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
$ zig test testing_detect_leak.zig
1/1 test.detect leak... OK
[gpa] (err): memory address 0x7f2a48e13000 leaked:
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/array_list.zig:403:67: 0x234cde in ensureTotalCapacityPrecise (test)
                const new_memory = try self.allocator.alignedAlloc(T, alignment, new_capacity);
                                                                  ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/array_list.zig:379:51: 0x22b0e4 in ensureTotalCapacity (test)
            return self.ensureTotalCapacityPrecise(better_capacity);
                                                  ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/array_list.zig:426:41: 0x228890 in addOne (test)
            try self.ensureTotalCapacity(self.items.len + 1);
                                        ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/array_list.zig:207:49: 0x22464d in append (test)
            const new_item_ptr = try self.addOne();
                                                ^
/home/ci/actions-runner/_work/zig-bootstrap/zig/docgen_tmp/testing_detect_leak.zig:6:20: 0x224572 in test.detect leak (test)
    try list.append('â');
                   ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/test_runner.zig:176:28: 0x232319 in mainTerminal (test)
        } else test_fn.func();
                           ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/test_runner.zig:36:28: 0x22917a in main (test)
        return mainTerminal();
                           ^
/home/ci/actions-runner/_work/zig-bootstrap/out/host/lib/zig/std/start.zig:564:22: 0x224b62 in posixCallMainAndExit (test)
            root.main();
                     ^

All 1 tests passed.
1 errors were logged.
1 tests leaked memory.
error: the following test command failed with exit code 1:
/home/ci/actions-runner/_work/zig-bootstrap/out/zig-local-cache/o/54fbcd2f75b6aeb5afd27aeac12a6446/test

```

See also:

- [defer](24-defer.md#defer)
- [Memory](42-memory.md#Memory)

#### Detecting Test Build

Use the [compile variable](43-compile-variables.md#Compile-Variables) `@import("builtin").is_test`
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
1/1 test.builtin.is_test... OK
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
1/2 test.expectEqual demo... OK
2/2 test.expectError demo... OK
All 2 tests passed.

```

The Zig Standard Library also contains functions to compare [Slices](14-slices.md#Slices), strings, and more. See the rest of the
`std.testing` namespace in the [Zig Standard Library](02-zig-standard-library.md#Zig-Standard-Library) for more available functions.

#### Test Tool Documentation

`zig test` has a few command line parameters which affect the compilation.
See `zig test --help` for a full list.


---
