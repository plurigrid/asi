# Compile-Time Programming

*Compile-time code execution and metaprogramming*


---

### comptime

Zig places importance on the concept of whether an expression is known at compile-time.
There are a few different places this concept is used, and these building blocks are used
to keep the language small, readable, and powerful.

#### Introducing the Compile-Time Concept

##### Compile-Time Parameters

Compile-time parameters is how Zig implements generics. It is compile-time duck typing.

**`compile-time_duck_typing.zig`:**

```zig
fn max(comptime T: type, a: T, b: T) T {
    return if (a > b) a else b;
}
fn gimmeTheBiggerFloat(a: f32, b: f32) f32 {
    return max(f32, a, b);
}
fn gimmeTheBiggerInteger(a: u64, b: u64) u64 {
    return max(u64, a, b);
}

```

In Zig, types are first-class citizens. They can be assigned to variables, passed as parameters to functions,
and returned from functions. However, they can only be used in expressions which are known at *compile-time*,
which is why the parameter `T` in the above snippet must be marked with `comptime`.

A `comptime` parameter means that:

- At the callsite, the value must be known at compile-time, or it is a compile error.
- In the function definition, the value is known at compile-time.

For example, if we were to introduce another function to the above snippet:

**`test_unresolved_comptime_value.zig`:**

```zig
fn max(comptime T: type, a: T, b: T) T {
    return if (a > b) a else b;
}
test "try to pass a runtime type" {
    foo(false);
}
fn foo(condition: bool) void {
    const result = max(if (condition) f32 else u64, 1234, 5678);
    _ = result;
}

```

**Shell:**

```shell
$ zig test test_unresolved_comptime_value.zig
/home/andy/dev/zig/doc/langref/test_unresolved_comptime_value.zig:8:28: error: unable to resolve comptime value
    const result = max(if (condition) f32 else u64, 1234, 5678);
                           ^~~~~~~~~
/home/andy/dev/zig/doc/langref/test_unresolved_comptime_value.zig:8:24: note: argument to comptime parameter must be comptime-known
    const result = max(if (condition) f32 else u64, 1234, 5678);
                       ^~~~~~~~~~~~~~~~~~~~~~~~~~~
/home/andy/dev/zig/doc/langref/test_unresolved_comptime_value.zig:1:8: note: parameter declared comptime here
fn max(comptime T: type, a: T, b: T) T {
       ^~~~~~~~
referenced by:
    test.try to pass a runtime type: /home/andy/dev/zig/doc/langref/test_unresolved_comptime_value.zig:5:8


```

This is an error because the programmer attempted to pass a value only known at run-time
to a function which expects a value known at compile-time.

Another way to get an error is if we pass a type that violates the type checker when the
function is analyzed. This is what it means to have *compile-time duck typing*.

For example:

**`test_comptime_mismatched_type.zig`:**

```zig
fn max(comptime T: type, a: T, b: T) T {
    return if (a > b) a else b;
}
test "try to compare bools" {
    _ = max(bool, true, false);
}

```

**Shell:**

```shell
$ zig test test_comptime_mismatched_type.zig
/home/andy/dev/zig/doc/langref/test_comptime_mismatched_type.zig:2:18: error: operator > not allowed for type 'bool'
    return if (a > b) a else b;
               ~~^~~
referenced by:
    test.try to compare bools: /home/andy/dev/zig/doc/langref/test_comptime_mismatched_type.zig:5:12


```

On the flip side, inside the function definition with the `comptime` parameter, the
value is known at compile-time. This means that we actually could make this work for the bool type
if we wanted to:

**`test_comptime_max_with_bool.zig`:**

```zig
fn max(comptime T: type, a: T, b: T) T {
    if (T == bool) {
        return a or b;
    } else if (a > b) {
        return a;
    } else {
        return b;
    }
}
test "try to compare bools" {
    try @import("std").testing.expect(max(bool, false, true) == true);
}

```

**Shell:**

```shell
$ zig test test_comptime_max_with_bool.zig
1/1 test_comptime_max_with_bool.test.try to compare bools...OK
All 1 tests passed.

```

This works because Zig implicitly inlines `if` expressions when the condition
is known at compile-time, and the compiler guarantees that it will skip analysis of
the branch not taken.

This means that the actual function generated for `max` in this situation looks like
this:

**`compiler_generated_function.zig`:**

```zig
fn max(a: bool, b: bool) bool {
    {
        return a or b;
    }
}

```

All the code that dealt with compile-time known values is eliminated and we are left with only
the necessary run-time code to accomplish the task.

This works the same way for `switch` expressions - they are implicitly inlined
when the target expression is compile-time known.

##### Compile-Time Variables

In Zig, the programmer can label variables as `comptime`. This guarantees to the compiler
that every load and store of the variable is performed at compile-time. Any violation of this results in a
compile error.

This combined with the fact that we can `inline` loops allows us to write
a function which is partially evaluated at compile-time and partially at run-time.

For example:

**`test_comptime_evaluation.zig`:**

```zig
const expect = @import("std").testing.expect;

const CmdFn = struct {
    name: []const u8,
    func: fn (i32) i32,
};

const cmd_fns = [_]CmdFn{
    CmdFn{ .name = "one", .func = one },
    CmdFn{ .name = "two", .func = two },
    CmdFn{ .name = "three", .func = three },
};
fn one(value: i32) i32 {
    return value + 1;
}
fn two(value: i32) i32 {
    return value + 2;
}
fn three(value: i32) i32 {
    return value + 3;
}

fn performFn(comptime prefix_char: u8, start_value: i32) i32 {
    var result: i32 = start_value;
    comptime var i = 0;
    inline while (i < cmd_fns.len) : (i += 1) {
        if (cmd_fns[i].name[0] == prefix_char) {
            result = cmd_fns[i].func(result);
        }
    }
    return result;
}

test "perform fn" {
    try expect(performFn('t', 1) == 6);
    try expect(performFn('o', 0) == 1);
    try expect(performFn('w', 99) == 99);
}

```

**Shell:**

```shell
$ zig test test_comptime_evaluation.zig
1/1 test_comptime_evaluation.test.perform fn...OK
All 1 tests passed.

```

This example is a bit contrived, because the compile-time evaluation component is unnecessary;
this code would work fine if it was all done at run-time. But it does end up generating
different code. In this example, the function `performFn` is generated three different times,
for the different values of `prefix_char` provided:

**`performFn_1`:**

```zig
// From the line:
// expect(performFn('t', 1) == 6);
fn performFn(start_value: i32) i32 {
    var result: i32 = start_value;
    result = two(result);
    result = three(result);
    return result;
}

```

**`performFn_2`:**

```zig
// From the line:
// expect(performFn('o', 0) == 1);
fn performFn(start_value: i32) i32 {
    var result: i32 = start_value;
    result = one(result);
    return result;
}

```

**`performFn_3`:**

```zig
// From the line:
// expect(performFn('w', 99) == 99);
fn performFn(start_value: i32) i32 {
    var result: i32 = start_value;
    _ = &result;
    return result;
}

```

Note that this happens even in a debug build.
This is not a way to write more optimized code, but it is a way to make sure that what *should* happen
at compile-time, *does* happen at compile-time. This catches more errors and allows expressiveness
that in other languages requires using macros, generated code, or a preprocessor to accomplish.

##### Compile-Time Expressions

In Zig, it matters whether a given expression is known at compile-time or run-time. A programmer can
use a `comptime` expression to guarantee that the expression will be evaluated at compile-time.
If this cannot be accomplished, the compiler will emit an error. For example:

**`test_comptime_call_extern_function.zig`:**

```zig
extern fn exit() noreturn;

test "foo" {
    comptime {
        exit();
    }
}

```

**Shell:**

```shell
$ zig test test_comptime_call_extern_function.zig
/home/andy/dev/zig/doc/langref/test_comptime_call_extern_function.zig:5:13: error: comptime call of extern function
        exit();
        ~~~~^~
/home/andy/dev/zig/doc/langref/test_comptime_call_extern_function.zig:4:5: note: 'comptime' keyword forces comptime evaluation
    comptime {
    ^~~~~~~~


```

It doesn't make sense that a program could call `exit()` (or any other external function)
at compile-time, so this is a compile error. However, a `comptime` expression does much
more than sometimes cause a compile error.

Within a `comptime` expression:

- All variables are `comptime` variables.
- All `if`, `while`, `for`, and `switch`
  expressions are evaluated at compile-time, or emit a compile error if this is not possible.
- All `return` and `try` expressions are invalid (unless the function itself is called at compile-time).
- All code with runtime side effects or depending on runtime values emits a compile error.
- All function calls cause the compiler to interpret the function at compile-time, emitting a
  compile error if the function tries to do something that has global runtime side effects.

This means that a programmer can create a function which is called both at compile-time and run-time, with
no modification to the function required.

Let's look at an example:

**`test_fibonacci_recursion.zig`:**

```zig
const expect = @import("std").testing.expect;

fn fibonacci(index: u32) u32 {
    if (index < 2) return index;
    return fibonacci(index - 1) + fibonacci(index - 2);
}

test "fibonacci" {
    // test fibonacci at run-time
    try expect(fibonacci(7) == 13);

    // test fibonacci at compile-time
    try comptime expect(fibonacci(7) == 13);
}

```

**Shell:**

```shell
$ zig test test_fibonacci_recursion.zig
1/1 test_fibonacci_recursion.test.fibonacci...OK
All 1 tests passed.

```

Imagine if we had forgotten the base case of the recursive function and tried to run the tests:

**`test_fibonacci_comptime_overflow.zig`:**

```zig
const expect = @import("std").testing.expect;

fn fibonacci(index: u32) u32 {
    //if (index < 2) return index;
    return fibonacci(index - 1) + fibonacci(index - 2);
}

test "fibonacci" {
    try comptime expect(fibonacci(7) == 13);
}

```

**Shell:**

```shell
$ zig test test_fibonacci_comptime_overflow.zig
/home/andy/dev/zig/doc/langref/test_fibonacci_comptime_overflow.zig:5:28: error: overflow of integer type 'u32' with value '-1'
    return fibonacci(index - 1) + fibonacci(index - 2);
                     ~~~~~~^~~
/home/andy/dev/zig/doc/langref/test_fibonacci_comptime_overflow.zig:5:21: note: called at comptime here (7 times)
    return fibonacci(index - 1) + fibonacci(index - 2);
           ~~~~~~~~~^~~~~~~~~~~
/home/andy/dev/zig/doc/langref/test_fibonacci_comptime_overflow.zig:9:34: note: called at comptime here
    try comptime expect(fibonacci(7) == 13);
                        ~~~~~~~~~^~~


```

The compiler produces an error which is a stack trace from trying to evaluate the
function at compile-time.

Luckily, we used an unsigned integer, and so when we tried to subtract 1 from 0, it triggered
[Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior), which is always a compile error if the compiler knows it happened.
But what would have happened if we used a signed integer?

**`fibonacci_comptime_infinite_recursion.zig`:**

```zig
const assert = @import("std").debug.assert;

fn fibonacci(index: i32) i32 {
    //if (index < 2) return index;
    return fibonacci(index - 1) + fibonacci(index - 2);
}

test "fibonacci" {
    try comptime assert(fibonacci(7) == 13);
}

```

The compiler is supposed to notice that evaluating this function at
compile-time took more than 1000 branches, and thus emits an error and
gives up. If the programmer wants to increase the budget for compile-time
computation, they can use a built-in function called
[@setEvalBranchQuota](#setEvalBranchQuota) to change the default number 1000 to
something else.

However, there is a [design
flaw in the compiler](https://github.com/ziglang/zig/issues/13724) causing it to stack overflow instead of having the proper
behavior here. I'm terribly sorry about that. I hope to get this resolved
before the next release.

What if we fix the base case, but put the wrong value in the
`expect` line?

**`test_fibonacci_comptime_unreachable.zig`:**

```zig
const assert = @import("std").debug.assert;

fn fibonacci(index: i32) i32 {
    if (index < 2) return index;
    return fibonacci(index - 1) + fibonacci(index - 2);
}

test "fibonacci" {
    try comptime assert(fibonacci(7) == 99999);
}

```

**Shell:**

```shell
$ zig test test_fibonacci_comptime_unreachable.zig
/home/andy/dev/zig/lib/std/debug.zig:559:14: error: reached unreachable code
    if (!ok) unreachable; // assertion failure
             ^~~~~~~~~~~
/home/andy/dev/zig/doc/langref/test_fibonacci_comptime_unreachable.zig:9:24: note: called at comptime here
    try comptime assert(fibonacci(7) == 99999);
                 ~~~~~~^~~~~~~~~~~~~~~~~~~~~~~


```

At [container](45-c.md#Containers) level (outside of any function), all expressions are implicitly
`comptime` expressions. This means that we can use functions to
initialize complex static data. For example:

**`test_container-level_comptime_expressions.zig`:**

```zig
const first_25_primes = firstNPrimes(25);
const sum_of_first_25_primes = sum(&first_25_primes);

fn firstNPrimes(comptime n: usize) [n]i32 {
    var prime_list: [n]i32 = undefined;
    var next_index: usize = 0;
    var test_number: i32 = 2;
    while (next_index < prime_list.len) : (test_number += 1) {
        var test_prime_index: usize = 0;
        var is_prime = true;
        while (test_prime_index < next_index) : (test_prime_index += 1) {
            if (test_number % prime_list[test_prime_index] == 0) {
                is_prime = false;
                break;
            }
        }
        if (is_prime) {
            prime_list[next_index] = test_number;
            next_index += 1;
        }
    }
    return prime_list;
}

fn sum(numbers: []const i32) i32 {
    var result: i32 = 0;
    for (numbers) |x| {
        result += x;
    }
    return result;
}

test "variable values" {
    try @import("std").testing.expect(sum_of_first_25_primes == 1060);
}

```

**Shell:**

```shell
$ zig test test_container-level_comptime_expressions.zig
1/1 test_container-level_comptime_expressions.test.variable values...OK
All 1 tests passed.

```

When we compile this program, Zig generates the constants
with the answer pre-computed. Here are the lines from the generated LLVM IR:

```

@0 = internal unnamed_addr constant [25 x i32] [i32 2, i32 3, i32 5, i32 7, i32 11, i32 13, i32 17, i32 19, i32 23, i32 29, i32 31, i32 37, i32 41, i32 43, i32 47, i32 53, i32 59, i32 61, i32 67, i32 71, i32 73, i32 79, i32 83, i32 89, i32 97]
@1 = internal unnamed_addr constant i32 1060

```

Note that we did not have to do anything special with the syntax of these functions. For example,
we could call the `sum` function as is with a slice of numbers whose length and values were
only known at run-time.

#### Generic Data Structures

Zig uses comptime capabilities to implement generic data structures without introducing any
special-case syntax.

Here is an example of a generic `List` data structure.

**`generic_data_structure.zig`:**

```zig
fn List(comptime T: type) type {
    return struct {
        items: []T,
        len: usize,
    };
}

// The generic List data structure can be instantiated by passing in a type:
var buffer: [10]i32 = undefined;
var list = List(i32){
    .items = &buffer,
    .len = 0,
};

```

That's it. It's a function that returns an anonymous `struct`.
For the purposes of error messages and debugging, Zig infers the name
`"List(i32)"` from the function name and parameters invoked when creating
the anonymous struct.

To explicitly give a type a name, we assign it to a constant.

**`anonymous_struct_name.zig`:**

```zig
const Node = struct {
    next: ?*Node,
    name: []const u8,
};

var node_a = Node{
    .next = null,
    .name = "Node A",
};

var node_b = Node{
    .next = &node_a,
    .name = "Node B",
};

```

In this example, the `Node` struct refers to itself.
This works because all top level declarations are order-independent.
As long as the compiler can determine the size of the struct, it is free to refer to itself.
In this case, `Node` refers to itself as a pointer, which has a
well-defined size at compile time, so it works fine.

#### Case Study: print in Zig

Putting all of this together, let's see how `print` works in Zig.

**`print.zig`:**

```zig
const print = @import("std").debug.print;

const a_number: i32 = 1234;
const a_string = "foobar";

pub fn main() void {
    print("here is a string: '{s}' here is a number: {}\n", .{ a_string, a_number });
}

```

**Shell:**

```shell
$ zig build-exe print.zig
$ ./print
here is a string: 'foobar' here is a number: 1234

```

Let's crack open the implementation of this and see how it works:

**`poc_print_fn.zig`:**

```zig
const Writer = struct {
    /// Calls print and then flushes the buffer.
    pub fn print(self: *Writer, comptime format: []const u8, args: anytype) anyerror!void {
        const State = enum {
            start,
            open_brace,
            close_brace,
        };

        comptime var start_index: usize = 0;
        comptime var state = State.start;
        comptime var next_arg: usize = 0;

        inline for (format, 0..) |c, i| {
            switch (state) {
                State.start => switch (c) {
                    '{' => {
                        if (start_index < i) try self.write(format[start_index..i]);
                        state = State.open_brace;
                    },
                    '}' => {
                        if (start_index < i) try self.write(format[start_index..i]);
                        state = State.close_brace;
                    },
                    else => {},
                },
                State.open_brace => switch (c) {
                    '{' => {
                        state = State.start;
                        start_index = i;
                    },
                    '}' => {
                        try self.printValue(args[next_arg]);
                        next_arg += 1;
                        state = State.start;
                        start_index = i + 1;
                    },
                    's' => {
                        continue;
                    },
                    else => @compileError("Unknown format character: " ++ [1]u8{c}),
                },
                State.close_brace => switch (c) {
                    '}' => {
                        state = State.start;
                        start_index = i;
                    },
                    else => @compileError("Single '}' encountered in format string"),
                },
            }
        }
        comptime {
            if (args.len != next_arg) {
                @compileError("Unused arguments");
            }
            if (state != State.start) {
                @compileError("Incomplete format string: " ++ format);
            }
        }
        if (start_index < format.len) {
            try self.write(format[start_index..format.len]);
        }
        try self.flush();
    }

    fn write(self: *Writer, value: []const u8) !void {
        _ = self;
        _ = value;
    }
    pub fn printValue(self: *Writer, value: anytype) !void {
        _ = self;
        _ = value;
    }
    fn flush(self: *Writer) !void {
        _ = self;
    }
};

```

This is a proof of concept implementation; the actual function in the standard library has more
formatting capabilities.

Note that this is not hard-coded into the Zig compiler; this is userland code in the standard library.

When this function is analyzed from our example code above, Zig partially evaluates the function
and emits a function that actually looks like this:

**`Emitted print Function`:**

```zig
pub fn print(self: *Writer, arg0: []const u8, arg1: i32) !void {
    try self.write("here is a string: '");
    try self.printValue(arg0);
    try self.write("' here is a number: ");
    try self.printValue(arg1);
    try self.write("\n");
    try self.flush();
}

```

`printValue` is a function that takes a parameter of any type, and does different things depending
on the type:

**`poc_printValue_fn.zig`:**

```zig
const Writer = struct {
    pub fn printValue(self: *Writer, value: anytype) !void {
        switch (@typeInfo(@TypeOf(value))) {
            .int => {
                return self.writeInt(value);
            },
            .float => {
                return self.writeFloat(value);
            },
            .pointer => {
                return self.write(value);
            },
            else => {
                @compileError("Unable to print type '" ++ @typeName(@TypeOf(value)) ++ "'");
            },
        }
    }

    fn write(self: *Writer, value: []const u8) !void {
        _ = self;
        _ = value;
    }
    fn writeInt(self: *Writer, value: anytype) !void {
        _ = self;
        _ = value;
    }
    fn writeFloat(self: *Writer, value: anytype) !void {
        _ = self;
        _ = value;
    }
};

```

And now, what happens if we give too many arguments to `print`?

**`test_print_too_many_args.zig`:**

```zig
const print = @import("std").debug.print;

const a_number: i32 = 1234;
const a_string = "foobar";

test "print too many arguments" {
    print("here is a string: '{s}' here is a number: {}\n", .{
        a_string,
        a_number,
        a_number,
    });
}

```

**Shell:**

```shell
$ zig test test_print_too_many_args.zig
/home/andy/dev/zig/lib/std/Io/Writer.zig:717:18: error: unused argument in 'here is a string: '{s}' here is a number: {}
                                                        '
            1 => @compileError("unused argument in '" ++ fmt ++ "'"),
                 ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
referenced by:
    print__anon_454: /home/andy/dev/zig/lib/std/debug.zig:231:23
    test.print too many arguments: /home/andy/dev/zig/doc/langref/test_print_too_many_args.zig:7:10


```

Zig gives programmers the tools needed to protect themselves against their own mistakes.

Zig doesn't care whether the format argument is a string literal,
only that it is a compile-time known value that can be coerced to a `[]const u8`:

**`print_comptime-known_format.zig`:**

```zig
const print = @import("std").debug.print;

const a_number: i32 = 1234;
const a_string = "foobar";
const fmt = "here is a string: '{s}' here is a number: {}\n";

pub fn main() void {
    print(fmt, .{ a_string, a_number });
}

```

**Shell:**

```shell
$ zig build-exe print_comptime-known_format.zig
$ ./print_comptime-known_format
here is a string: 'foobar' here is a number: 1234

```

This works fine.

Zig does not special case string formatting in the compiler and instead exposes enough power to accomplish this
task in userland. It does so without introducing another language on top of Zig, such as
a macro language or a preprocessor language. It's Zig all the way down.

See also:

- [inline while](#inline-while)
- [inline for](#inline-for)


---

### Compile Variables

Compile variables are accessible by importing the `"builtin"` package,
which the compiler makes available to every Zig source file. It contains
compile-time constants such as the current target, endianness, and release mode.

**`compile_variables.zig`:**

```zig
const builtin = @import("builtin");
const separator = if (builtin.os.tag == .windows) '\\' else '/';

```

Example of what is imported with `@import("builtin")`:

**`@import("builtin")`:**

```zig
const std = @import("std");
/// Zig version. When writing code that supports multiple versions of Zig, prefer
/// feature detection (i.e. with `@hasDecl` or `@hasField`) over version checks.
pub const zig_version = std.SemanticVersion.parse(zig_version_string) catch unreachable;
pub const zig_version_string = "0.15.2";
pub const zig_backend = std.builtin.CompilerBackend.stage2_x86_64;

pub const output_mode: std.builtin.OutputMode = .Exe;
pub const link_mode: std.builtin.LinkMode = .static;
pub const unwind_tables: std.builtin.UnwindTables = .async;
pub const is_test = false;
pub const single_threaded = false;
pub const abi: std.Target.Abi = .gnu;
pub const cpu: std.Target.Cpu = .{
    .arch = .x86_64,
    .model = &std.Target.x86.cpu.znver4,
    .features = std.Target.x86.featureSet(&.{
        .@"64bit",
        .adx,
        .aes,
        .allow_light_256_bit,
        .avx,
        .avx2,
        .avx512bf16,
        .avx512bitalg,
        .avx512bw,
        .avx512cd,
        .avx512dq,
        .avx512f,
        .avx512ifma,
        .avx512vbmi,
        .avx512vbmi2,
        .avx512vl,
        .avx512vnni,
        .avx512vpopcntdq,
        .bmi,
        .bmi2,
        .branchfusion,
        .clflushopt,
        .clwb,
        .clzero,
        .cmov,
        .crc32,
        .cx16,
        .cx8,
        .evex512,
        .f16c,
        .fast_15bytenop,
        .fast_bextr,
        .fast_dpwssd,
        .fast_imm16,
        .fast_lzcnt,
        .fast_movbe,
        .fast_scalar_fsqrt,
        .fast_scalar_shift_masks,
        .fast_variable_perlane_shuffle,
        .fast_vector_fsqrt,
        .fma,
        .fsgsbase,
        .fsrm,
        .fxsr,
        .gfni,
        .idivq_to_divl,
        .invpcid,
        .lzcnt,
        .macrofusion,
        .mmx,
        .movbe,
        .mwaitx,
        .nopl,
        .pclmul,
        .pku,
        .popcnt,
        .prfchw,
        .rdpid,
        .rdpru,
        .rdrnd,
        .rdseed,
        .sahf,
        .sbb_dep_breaking,
        .sha,
        .shstk,
        .slow_shld,
        .smap,
        .smep,
        .sse,
        .sse2,
        .sse3,
        .sse4_1,
        .sse4_2,
        .sse4a,
        .ssse3,
        .vaes,
        .vpclmulqdq,
        .vzeroupper,
        .wbnoinvd,
        .x87,
        .xsave,
        .xsavec,
        .xsaveopt,
        .xsaves,
    }),
};
pub const os: std.Target.Os = .{
    .tag = .linux,
    .version_range = .{ .linux = .{
        .range = .{
            .min = .{
                .major = 6,
                .minor = 16,
                .patch = 0,
            },
            .max = .{
                .major = 6,
                .minor = 16,
                .patch = 0,
            },
        },
        .glibc = .{
            .major = 2,
            .minor = 39,
            .patch = 0,
        },
        .android = 29,
    }},
};
pub const target: std.Target = .{
    .cpu = cpu,
    .os = os,
    .abi = abi,
    .ofmt = object_format,
    .dynamic_linker = .init("/nix/store/zdpby3l6azi78sl83cpad2qjpfj25aqx-glibc-2.40-66/lib/ld-linux-x86-64.so.2"),
};
pub const object_format: std.Target.ObjectFormat = .elf;
pub const mode: std.builtin.OptimizeMode = .Debug;
pub const link_libc = false;
pub const link_libcpp = false;
pub const have_error_return_tracing = true;
pub const valgrind_support = true;
pub const sanitize_thread = false;
pub const fuzz = false;
pub const position_independent_code = false;
pub const position_independent_executable = false;
pub const strip_debug_info = false;
pub const code_model: std.builtin.CodeModel = .default;
pub const omit_frame_pointer = false;

```

See also:

- [Build Mode](38-build-mode.md#Build-Mode)


---
