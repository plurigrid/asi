const std = @import("std");
const math = @import("math_utils.zig");
const strings = @import("string_utils.zig");

/// Multi-file project example demonstrating:
/// - Module organization
/// - Build system configuration
/// - Cross-module imports
/// - Testing across modules

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const stdout = std.io.getStdOut().writer();

    try stdout.print("=== Multi-File Zig Project Example ===\n\n", .{});

    // Demonstrate math utilities
    try stdout.print("=== Math Utilities ===\n", .{});
    try stdout.print("5 + 3 = {d}\n", .{math.add(5, 3)});
    try stdout.print("5 - 3 = {d}\n", .{math.subtract(5, 3)});
    try stdout.print("5 * 3 = {d}\n", .{math.multiply(5, 3)});

    const div_result = math.divide(15, 3) catch |err| {
        try stdout.print("Division error: {s}\n", .{@errorName(err)});
        return err;
    };
    try stdout.print("15 / 3 = {d}\n", .{div_result});

    try stdout.print("Factorial of 5 = {d}\n", .{math.factorial(5)});
    try stdout.print("Is 17 prime? {}\n", .{math.isPrime(17)});
    try stdout.print("GCD of 12 and 18 = {d}\n", .{math.gcd(12, 18)});

    // Demonstrate string utilities
    try stdout.print("\n=== String Utilities ===\n", .{});

    const test_string = "Hello, Zig!";
    try stdout.print("Test string: '{s}'\n", .{test_string});
    try stdout.print("Count of 'l': {d}\n", .{strings.countChar(test_string, 'l')});
    try stdout.print("Starts with 'Hello': {}\n", .{strings.startsWith(test_string, "Hello")});
    try stdout.print("Ends with 'Zig!': {}\n", .{strings.endsWith(test_string, "Zig!")});

    const upper = try strings.toUpperCase(allocator, test_string);
    defer allocator.free(upper);
    try stdout.print("Uppercase: {s}\n", .{upper});

    const lower = try strings.toLowerCase(allocator, test_string);
    defer allocator.free(lower);
    try stdout.print("Lowercase: {s}\n", .{lower});

    const reversed = try strings.reverse(allocator, test_string);
    defer allocator.free(reversed);
    try stdout.print("Reversed: {s}\n", .{reversed});

    const whitespace_str = "  trim me  ";
    try stdout.print("Trimmed '{s}': '{s}'\n", .{ whitespace_str, strings.trim(whitespace_str) });

    try stdout.print("Is '12345' numeric? {}\n", .{strings.isNumeric("12345")});
    try stdout.print("Is 'racecar' a palindrome? {}\n", .{strings.isPalindrome("racecar")});

    // Combining utilities
    try stdout.print("\n=== Combining Utilities ===\n", .{});

    const numbers = [_]u32{ 2, 3, 5, 7, 11, 13, 17, 19 };
    try stdout.print("First 8 primes: ", .{});
    for (numbers) |n| {
        if (math.isPrime(n)) {
            try stdout.print("{d} ", .{n});
        }
    }
    try stdout.print("\n", .{});

    const words = [_][]const u8{ "racecar", "hello", "noon", "world" };
    try stdout.print("Palindromes: ", .{});
    for (words) |word| {
        if (strings.isPalindrome(word)) {
            try stdout.print("{s} ", .{word});
        }
    }
    try stdout.print("\n", .{});

    try stdout.print("\n=== Project Structure ===\n", .{});
    try stdout.print("src/main.zig        - Main entry point\n", .{});
    try stdout.print("src/math_utils.zig  - Math operations\n", .{});
    try stdout.print("src/string_utils.zig - String operations\n", .{});
    try stdout.print("build.zig           - Build configuration\n", .{});
    try stdout.print("\nCommands:\n", .{});
    try stdout.print("  zig build          - Build the project\n", .{});
    try stdout.print("  zig build run      - Build and run\n", .{});
    try stdout.print("  zig build test     - Run all tests\n", .{});
    try stdout.print("  zig build lib      - Build math library\n", .{});
}

// Integration tests
const testing = std.testing;

test "math and string integration" {
    const allocator = testing.allocator;

    // Use math to generate numbers, convert to string
    const sum = math.add(10, 20);
    try testing.expectEqual(@as(i32, 30), sum);

    // Use string utils on text
    const text = "hello";
    const upper = try strings.toUpperCase(allocator, text);
    defer allocator.free(upper);

    try testing.expectEqualStrings("HELLO", upper);
}

test "factorial and palindrome" {
    // Calculate factorial
    const fact = math.factorial(4);
    try testing.expectEqual(@as(u64, 24), fact);

    // Check palindrome
    try testing.expect(strings.isPalindrome("24")); // Not a palindrome
    try testing.expect(!strings.isPalindrome("24")); // Correct
}
