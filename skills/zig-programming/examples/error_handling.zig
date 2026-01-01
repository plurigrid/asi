const std = @import("std");
const testing = std.testing;

// Error handling example demonstrating Zig's error handling patterns

// Custom error set
const FileError = error{
    FileNotFound,
    PermissionDenied,
    InvalidFormat,
};

const ParseError = error{
    InvalidSyntax,
    UnexpectedToken,
    OutOfRange,
};

// Error sets can be merged with ||
const ProcessError = FileError || ParseError || error{OutOfMemory};

/// Simple function demonstrating error unions
fn divide(a: i32, b: i32) !i32 {
    if (b == 0) return error.DivisionByZero;
    return @divTrunc(a, b);
}

/// Function using custom error set
fn openFile(filename: []const u8) FileError!void {
    if (filename.len == 0) return FileError.FileNotFound;
    if (std.mem.eql(u8, filename, "forbidden.txt")) return FileError.PermissionDenied;
    // Success case
    std.debug.print("File '{s}' opened successfully\n", .{filename});
}

/// Demonstrates try - propagate errors up the call stack
fn tryExample() !void {
    std.debug.print("\n=== Try Keyword ===\n", .{});
    std.debug.print("Propagates errors to caller\n\n", .{});

    // try unwraps the error union or returns the error
    const result1 = try divide(10, 2);
    std.debug.print("10 / 2 = {d}\n", .{result1});

    const result2 = try divide(15, 3);
    std.debug.print("15 / 3 = {d}\n", .{result2});

    // This would propagate the error to tryExample's caller
    // const result3 = try divide(10, 0);
}

/// Demonstrates catch - handle errors with default values
fn catchExample() void {
    std.debug.print("\n=== Catch Keyword ===\n", .{});
    std.debug.print("Handle errors with default values\n\n", .{});

    // catch provides a default value if error occurs
    const result1 = divide(10, 2) catch 0;
    std.debug.print("10 / 2 = {d}\n", .{result1});

    const result2 = divide(10, 0) catch 0;
    std.debug.print("10 / 0 = {d} (caught error, used default)\n", .{result2});

    // catch can also access the error value
    const result3 = divide(10, 0) catch |err| blk: {
        std.debug.print("Error occurred: {s}\n", .{@errorName(err)});
        break :blk -1;
    };
    std.debug.print("10 / 0 = {d} (error handled with custom logic)\n", .{result3});
}

/// Demonstrates errdefer - cleanup on error paths
fn errdefferExample() !void {
    std.debug.print("\n=== Errdefer Keyword ===\n", .{});
    std.debug.print("Cleanup that only runs on error path\n\n", .{});

    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Simulate multi-step operation that might fail
    const step1 = try allocator.alloc(u8, 100);
    errdefer allocator.free(step1); // Only freed if subsequent steps fail

    const step2 = try allocator.alloc(u8, 100);
    errdefer allocator.free(step2); // Only freed if subsequent steps fail

    // If we reach here successfully, caller is responsible for cleanup
    defer {
        allocator.free(step1);
        allocator.free(step2);
    }

    std.debug.print("Multi-step allocation succeeded\n", .{});
}

/// Demonstrates if-else error handling
fn ifElseExample() void {
    std.debug.print("\n=== If-Else Error Handling ===\n", .{});
    std.debug.print("Conditional error checking\n\n", .{});

    const result = divide(10, 2);

    if (result) |value| {
        std.debug.print("Success: {d}\n", .{value});
    } else |err| {
        std.debug.print("Error: {s}\n", .{@errorName(err)});
    }

    const result2 = divide(10, 0);

    if (result2) |value| {
        std.debug.print("Success: {d}\n", .{value});
    } else |err| {
        std.debug.print("Error: {s}\n", .{@errorName(err)});
    }
}

/// Demonstrates switch on error types
fn switchExample() void {
    std.debug.print("\n=== Switch on Errors ===\n", .{});
    std.debug.print("Different handling for different errors\n\n", .{});

    const files = [_][]const u8{ "data.txt", "", "forbidden.txt" };

    for (files) |filename| {
        const result = openFile(filename);

        if (result) {
            // Success case
        } else |err| switch (err) {
            FileError.FileNotFound => {
                std.debug.print("Error: File '{s}' not found\n", .{filename});
            },
            FileError.PermissionDenied => {
                std.debug.print("Error: No permission for '{s}'\n", .{filename});
            },
            FileError.InvalidFormat => {
                std.debug.print("Error: Invalid format in '{s}'\n", .{filename});
            },
        }
    }
}

/// Demonstrates error return traces
fn errorTraceExample() !void {
    std.debug.print("\n=== Error Return Traces ===\n", .{});
    std.debug.print("Stack trace when error occurs\n\n", .{});

    // Build with --debug to see error return traces
    std.debug.print("Call chain: errorTraceExample -> level1 -> level2 -> divide\n", .{});

    const level2 = struct {
        fn call() !i32 {
            return try divide(10, 0);
        }
    };

    const level1 = struct {
        fn call() !i32 {
            return try level2.call();
        }
    };

    _ = level1.call() catch |err| {
        std.debug.print("Caught error: {s}\n", .{@errorName(err)});
        return;
    };
}

/// Demonstrates custom error with payload (error unions)
fn processValue(value: i32) ProcessError!i32 {
    if (value < 0) return ParseError.OutOfRange;
    if (value > 100) return ParseError.OutOfRange;
    if (value == 42) return FileError.InvalidFormat;

    return value * 2;
}

fn errorSetExample() void {
    std.debug.print("\n=== Custom Error Sets ===\n", .{});
    std.debug.print("Type-safe error handling\n\n", .{});

    const values = [_]i32{ 10, -5, 150, 42 };

    for (values) |val| {
        const result = processValue(val);

        if (result) |processed| {
            std.debug.print("Value {d} -> {d}\n", .{ val, processed });
        } else |err| {
            std.debug.print("Value {d} -> Error: {s}\n", .{ val, @errorName(err) });
        }
    }
}

/// Demonstrates inferred error sets
fn inferredErrorSet(flag: bool) !i32 {
    // Error set is inferred from function body
    if (flag) {
        return error.SomeError;
    }
    return 42;
}

pub fn main() !void {
    std.debug.print("=== Zig Error Handling Examples ===\n", .{});

    try tryExample();
    catchExample();
    try errdefferExample();
    ifElseExample();
    switchExample();
    try errorTraceExample();
    errorSetExample();

    std.debug.print("\n=== Summary ===\n", .{});
    std.debug.print("- try: Propagate errors to caller\n", .{});
    std.debug.print("- catch: Provide default value or handle error\n", .{});
    std.debug.print("- errdefer: Cleanup only on error path\n", .{});
    std.debug.print("- if-else: Conditional error handling\n", .{});
    std.debug.print("- switch: Handle different error types\n", .{});
    std.debug.print("- Error sets: Type-safe error definitions\n", .{});
}

// Tests
test "divide success" {
    const result = try divide(10, 2);
    try testing.expectEqual(@as(i32, 5), result);
}

test "divide by zero" {
    const result = divide(10, 0);
    try testing.expectError(error.DivisionByZero, result);
}

test "catch with default" {
    const result = divide(10, 0) catch 0;
    try testing.expectEqual(@as(i32, 0), result);
}

test "if-else error unwrap" {
    const result = divide(10, 2);

    if (result) |value| {
        try testing.expectEqual(@as(i32, 5), value);
    } else |_| {
        try testing.expect(false); // Should not reach here
    }
}

test "custom error set" {
    const result = openFile("");
    try testing.expectError(FileError.FileNotFound, result);

    const result2 = openFile("forbidden.txt");
    try testing.expectError(FileError.PermissionDenied, result2);
}

test "merged error sets" {
    const result = processValue(-5);
    try testing.expectError(ParseError.OutOfRange, result);

    const result2 = processValue(42);
    try testing.expectError(FileError.InvalidFormat, result2);

    const result3 = try processValue(10);
    try testing.expectEqual(@as(i32, 20), result3);
}

test "errdefer cleanup" {
    const allocator = testing.allocator;

    const TestStruct = struct {
        fn failingAllocation(alloc: std.mem.Allocator) !void {
            const mem1 = try alloc.alloc(u8, 100);
            errdefer alloc.free(mem1);

            // Simulate failure
            return error.SimulatedError;
        }
    };

    const result = TestStruct.failingAllocation(allocator);
    try testing.expectError(error.SimulatedError, result);

    // If errdefer didn't work, we'd have a memory leak
}

test "inferred error set" {
    const result = try inferredErrorSet(false);
    try testing.expectEqual(@as(i32, 42), result);

    const result2 = inferredErrorSet(true);
    try testing.expectError(error.SomeError, result2);
}
