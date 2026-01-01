const std = @import("std");
const testing = std.testing;

// String manipulation example demonstrating common Zig patterns

const StringProcessor = struct {
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) StringProcessor {
        return .{ .allocator = allocator };
    }

    pub fn toUpperCase(self: StringProcessor, input: []const u8) ![]u8 {
        const result = try self.allocator.alloc(u8, input.len);
        errdefer self.allocator.free(result);

        for (input, 0..) |char, i| {
            result[i] = std.ascii.toUpper(char);
        }

        return result;
    }

    pub fn toLowerCase(self: StringProcessor, input: []const u8) ![]u8 {
        const result = try self.allocator.alloc(u8, input.len);
        errdefer self.allocator.free(result);

        for (input, 0..) |char, i| {
            result[i] = std.ascii.toLower(char);
        }

        return result;
    }

    pub fn reverse(self: StringProcessor, input: []const u8) ![]u8 {
        const result = try self.allocator.alloc(u8, input.len);
        errdefer self.allocator.free(result);

        var i: usize = 0;
        while (i < input.len) : (i += 1) {
            result[i] = input[input.len - 1 - i];
        }

        return result;
    }

    pub fn split(self: StringProcessor, input: []const u8, delimiter: u8) ![][]const u8 {
        var count: usize = 1;
        for (input) |char| {
            if (char == delimiter) count += 1;
        }

        const result = try self.allocator.alloc([]const u8, count);
        errdefer self.allocator.free(result);

        var iter = std.mem.splitScalar(u8, input, delimiter);
        var index: usize = 0;

        while (iter.next()) |part| {
            result[index] = part;
            index += 1;
        }

        return result;
    }
};

pub fn main() !void {
    // Initialize allocator
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Create processor
    const processor = StringProcessor.init(allocator);

    // Example usage
    const input = "Hello, World!";
    std.debug.print("Original: {s}\n", .{input});

    // Convert to uppercase
    const upper = try processor.toUpperCase(input);
    defer allocator.free(upper);
    std.debug.print("Uppercase: {s}\n", .{upper});

    // Convert to lowercase
    const lower = try processor.toLowerCase(input);
    defer allocator.free(lower);
    std.debug.print("Lowercase: {s}\n", .{lower});

    // Reverse string
    const reversed = try processor.reverse(input);
    defer allocator.free(reversed);
    std.debug.print("Reversed: {s}\n", .{reversed});

    // Split string
    const split_input = "apple,banana,orange";
    const parts = try processor.split(split_input, ',');
    defer allocator.free(parts);

    std.debug.print("Split '{s}' by ',':\n", .{split_input});
    for (parts, 0..) |part, i| {
        std.debug.print("  [{d}]: {s}\n", .{ i, part });
    }
}

// Tests
test "StringProcessor.toUpperCase" {
    const allocator = testing.allocator;
    const processor = StringProcessor.init(allocator);

    const input = "hello world";
    const result = try processor.toUpperCase(input);
    defer allocator.free(result);

    try testing.expectEqualStrings("HELLO WORLD", result);
}

test "StringProcessor.toLowerCase" {
    const allocator = testing.allocator;
    const processor = StringProcessor.init(allocator);

    const input = "HELLO WORLD";
    const result = try processor.toLowerCase(input);
    defer allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "StringProcessor.reverse" {
    const allocator = testing.allocator;
    const processor = StringProcessor.init(allocator);

    const input = "hello";
    const result = try processor.reverse(input);
    defer allocator.free(result);

    try testing.expectEqualStrings("olleh", result);
}

test "StringProcessor.split" {
    const allocator = testing.allocator;
    const processor = StringProcessor.init(allocator);

    const input = "a,b,c";
    const result = try processor.split(input, ',');
    defer allocator.free(result);

    try testing.expectEqual(@as(usize, 3), result.len);
    try testing.expectEqualStrings("a", result[0]);
    try testing.expectEqualStrings("b", result[1]);
    try testing.expectEqualStrings("c", result[2]);
}

test "StringProcessor edge cases" {
    const allocator = testing.allocator;
    const processor = StringProcessor.init(allocator);

    // Empty string
    const empty = "";
    const result = try processor.toUpperCase(empty);
    defer allocator.free(result);
    try testing.expectEqualStrings("", result);

    // Single character
    const single = "x";
    const reversed = try processor.reverse(single);
    defer allocator.free(reversed);
    try testing.expectEqualStrings("x", reversed);
}