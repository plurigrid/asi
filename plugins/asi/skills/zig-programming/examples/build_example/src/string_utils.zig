const std = @import("std");
const testing = std.testing;

/// String utilities module demonstrating string operations

/// Count occurrences of a character in a string
pub fn countChar(str: []const u8, char: u8) usize {
    var count: usize = 0;
    for (str) |c| {
        if (c == char) count += 1;
    }
    return count;
}

/// Check if string starts with prefix
pub fn startsWith(str: []const u8, prefix: []const u8) bool {
    if (prefix.len > str.len) return false;
    return std.mem.eql(u8, str[0..prefix.len], prefix);
}

/// Check if string ends with suffix
pub fn endsWith(str: []const u8, suffix: []const u8) bool {
    if (suffix.len > str.len) return false;
    return std.mem.eql(u8, str[str.len - suffix.len ..], suffix);
}

/// Convert string to uppercase (allocates memory)
pub fn toUpperCase(allocator: std.mem.Allocator, str: []const u8) ![]u8 {
    const result = try allocator.alloc(u8, str.len);
    for (str, 0..) |c, i| {
        result[i] = std.ascii.toUpper(c);
    }
    return result;
}

/// Convert string to lowercase (allocates memory)
pub fn toLowerCase(allocator: std.mem.Allocator, str: []const u8) ![]u8 {
    const result = try allocator.alloc(u8, str.len);
    for (str, 0..) |c, i| {
        result[i] = std.ascii.toLower(c);
    }
    return result;
}

/// Reverse a string (allocates memory)
pub fn reverse(allocator: std.mem.Allocator, str: []const u8) ![]u8 {
    const result = try allocator.alloc(u8, str.len);
    for (str, 0..) |c, i| {
        result[str.len - 1 - i] = c;
    }
    return result;
}

/// Trim whitespace from both ends (returns slice, no allocation)
pub fn trim(str: []const u8) []const u8 {
    return std.mem.trim(u8, str, &std.ascii.whitespace);
}

/// Check if string contains only digits
pub fn isNumeric(str: []const u8) bool {
    if (str.len == 0) return false;
    for (str) |c| {
        if (!std.ascii.isDigit(c)) return false;
    }
    return true;
}

/// Check if string is a palindrome
pub fn isPalindrome(str: []const u8) bool {
    if (str.len <= 1) return true;

    var left: usize = 0;
    var right: usize = str.len - 1;

    while (left < right) {
        if (str[left] != str[right]) return false;
        left += 1;
        right -= 1;
    }

    return true;
}

// Tests
test "count character" {
    try testing.expectEqual(@as(usize, 3), countChar("hello world", 'l'));
    try testing.expectEqual(@as(usize, 0), countChar("hello", 'z'));
    try testing.expectEqual(@as(usize, 2), countChar("banana", 'a'));
}

test "starts with" {
    try testing.expect(startsWith("hello world", "hello"));
    try testing.expect(!startsWith("hello world", "world"));
    try testing.expect(startsWith("test", "test"));
    try testing.expect(!startsWith("test", "testing"));
}

test "ends with" {
    try testing.expect(endsWith("hello world", "world"));
    try testing.expect(!endsWith("hello world", "hello"));
    try testing.expect(endsWith("test", "test"));
    try testing.expect(!endsWith("test", "atest"));
}

test "to uppercase" {
    const allocator = testing.allocator;

    const result = try toUpperCase(allocator, "hello");
    defer allocator.free(result);

    try testing.expectEqualStrings("HELLO", result);
}

test "to lowercase" {
    const allocator = testing.allocator;

    const result = try toLowerCase(allocator, "HELLO");
    defer allocator.free(result);

    try testing.expectEqualStrings("hello", result);
}

test "reverse string" {
    const allocator = testing.allocator;

    const result = try reverse(allocator, "hello");
    defer allocator.free(result);

    try testing.expectEqualStrings("olleh", result);
}

test "trim whitespace" {
    try testing.expectEqualStrings("hello", trim("  hello  "));
    try testing.expectEqualStrings("hello world", trim("hello world"));
    try testing.expectEqualStrings("test", trim("\t\ntest\r\n"));
}

test "is numeric" {
    try testing.expect(isNumeric("12345"));
    try testing.expect(!isNumeric("12a45"));
    try testing.expect(!isNumeric("hello"));
    try testing.expect(!isNumeric(""));
    try testing.expect(isNumeric("0"));
}

test "is palindrome" {
    try testing.expect(isPalindrome("racecar"));
    try testing.expect(isPalindrome("a"));
    try testing.expect(isPalindrome(""));
    try testing.expect(!isPalindrome("hello"));
    try testing.expect(isPalindrome("noon"));
}
