// Target Zig Version: 0.15.2
// For other versions, see references/version-differences.md

const std = @import("std");
const testing = std.testing;

// Example function to test
fn add(a: i32, b: i32) i32 {
    return a + b;
}

fn multiply(a: i32, b: i32) i32 {
    return a * b;
}

// Example error type
const MathError = error{
    DivisionByZero,
    Overflow,
};

fn divide(a: i32, b: i32) !i32 {
    if (b == 0) return MathError.DivisionByZero;
    return @divTrunc(a, b);
}

// Tests
test "add function" {
    try testing.expect(add(1, 2) == 3);
    try testing.expectEqual(@as(i32, 42), add(40, 2));
}

test "multiply function" {
    try testing.expectEqual(@as(i32, 20), multiply(4, 5));
    try testing.expectEqual(@as(i32, 0), multiply(0, 100));
}

test "divide function - success" {
    const result = try divide(10, 2);
    try testing.expectEqual(@as(i32, 5), result);
}

test "divide function - error" {
    const result = divide(10, 0);
    try testing.expectError(MathError.DivisionByZero, result);
}

test "string operations" {
    const hello = "Hello";
    const world = "World";

    var buffer: [100]u8 = undefined;
    const result = try std.fmt.bufPrint(&buffer, "{s}, {s}!", .{ hello, world });

    try testing.expectEqualStrings("Hello, World!", result);
}

test "allocator usage" {
    const allocator = testing.allocator;

    const list = try allocator.alloc(i32, 5);
    defer allocator.free(list);

    for (list, 0..) |*item, i| {
        item.* = @intCast(i * 2);
    }

    try testing.expectEqual(@as(i32, 0), list[0]);
    try testing.expectEqual(@as(i32, 8), list[4]);
}