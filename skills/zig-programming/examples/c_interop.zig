const std = @import("std");
const testing = std.testing;

// C interoperability example demonstrating Zig's C FFI capabilities

// Import C standard library functions
const c = @cImport({
    @cInclude("stdio.h");
    @cInclude("stdlib.h");
    @cInclude("string.h");
    @cInclude("math.h");
});

/// Example 1: Calling C functions from Zig
fn callingCFunctions() void {
    std.debug.print("\n=== Calling C Functions ===\n", .{});
    std.debug.print("Using C standard library from Zig\n\n", .{});

    // Call C's printf
    _ = c.printf("Hello from C's printf!\n");

    // Call C's sqrt
    const value: f64 = 16.0;
    const result = c.sqrt(value);
    std.debug.print("C sqrt({d}) = {d}\n", .{ value, result });

    // Call C's strlen
    const str = "Hello, C!";
    const len = c.strlen(str.ptr);
    std.debug.print("C strlen(\"{s}\") = {d}\n", .{ str, len });
}

/// Example 2: Exporting Zig functions to C
/// These functions can be called from C code

export fn zigAdd(a: c_int, b: c_int) c_int {
    return a + b;
}

export fn zigMultiply(a: c_int, b: c_int) c_int {
    return a * b;
}

export fn zigGreet(name: [*:0]const u8) void {
    const stdout = std.io.getStdOut().writer();
    stdout.print("Hello from Zig, {s}!\n", .{name}) catch {};
}

fn demonstrateExports() void {
    std.debug.print("\n=== Exporting Zig Functions ===\n", .{});
    std.debug.print("Functions callable from C code\n\n", .{});

    const result1 = zigAdd(10, 20);
    std.debug.print("zigAdd(10, 20) = {d}\n", .{result1});

    const result2 = zigMultiply(5, 6);
    std.debug.print("zigMultiply(5, 6) = {d}\n", .{result2});

    zigGreet("World");
}

/// Example 3: C type conversions
fn cTypeConversions() void {
    std.debug.print("\n=== C Type Conversions ===\n", .{});
    std.debug.print("Mapping between Zig and C types\n\n", .{});

    // C integer types
    const c_byte: c_char = 65; // 'A'
    const c_num: c_int = 42;
    const c_long: c_long = 1234567890;

    std.debug.print("c_char: {c} (value: {d})\n", .{ c_byte, c_byte });
    std.debug.print("c_int: {d}\n", .{c_num});
    std.debug.print("c_long: {d}\n", .{c_long});

    // C floating point types
    const c_float_val: c_float = 3.14;
    const c_double_val: c_double = 2.71828;

    std.debug.print("c_float: {d}\n", .{c_float_val});
    std.debug.print("c_double: {d}\n", .{c_double_val});

    // Converting Zig to C types
    const zig_int: i32 = 100;
    const as_c_int: c_int = @intCast(zig_int);
    std.debug.print("Zig i32 {d} -> c_int {d}\n", .{ zig_int, as_c_int });
}

/// Example 4: Working with C strings (null-terminated)
fn cStringHandling() !void {
    std.debug.print("\n=== C String Handling ===\n", .{});
    std.debug.print("Null-terminated strings vs Zig slices\n\n", .{});

    // Zig string literal is compatible with C
    const zig_str = "Hello from Zig";
    _ = c.printf("C printf: %s\n", zig_str.ptr);

    // Convert C string to Zig slice
    const c_str: [*:0]const u8 = "C string";
    const c_len = c.strlen(c_str);
    const zig_slice = c_str[0..c_len];
    std.debug.print("C string as Zig slice: {s} (len: {d})\n", .{ zig_slice, zig_slice.len });

    // Allocate C string using malloc
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const c_allocated = c.malloc(100);
    if (c_allocated == null) return error.OutOfMemory;
    defer c.free(c_allocated);

    // Use Zig allocator for C-compatible memory
    const zig_allocated = try allocator.allocSentinel(u8, 20, 0);
    defer allocator.free(zig_allocated);

    // Copy string using C's strcpy
    _ = c.strcpy(@ptrCast(zig_allocated.ptr), "Zig allocated");
    std.debug.print("Zig-allocated C string: {s}\n", .{zig_allocated});
}

/// Example 5: Working with C structs
const CPoint = extern struct {
    x: c_int,
    y: c_int,

    pub fn init(x: c_int, y: c_int) CPoint {
        return .{ .x = x, .y = y };
    }

    pub fn distance(self: CPoint, other: CPoint) f64 {
        const dx: f64 = @floatFromInt(other.x - self.x);
        const dy: f64 = @floatFromInt(other.y - self.y);
        return c.sqrt(dx * dx + dy * dy);
    }
};

fn cStructExample() void {
    std.debug.print("\n=== C Struct Compatibility ===\n", .{});
    std.debug.print("Using extern struct for C ABI compatibility\n\n", .{});

    const p1 = CPoint.init(0, 0);
    const p2 = CPoint.init(3, 4);

    std.debug.print("Point 1: ({d}, {d})\n", .{ p1.x, p1.y });
    std.debug.print("Point 2: ({d}, {d})\n", .{ p2.x, p2.y });
    std.debug.print("Distance: {d}\n", .{p1.distance(p2)});
}

/// Example 6: C macros and constants
fn cMacrosAndConstants() void {
    std.debug.print("\n=== C Macros and Constants ===\n", .{});
    std.debug.print("Accessing C preprocessor definitions\n\n", .{});

    // Access C constants (from stdio.h)
    std.debug.print("EOF value: {d}\n", .{c.EOF});
    std.debug.print("NULL pointer: {*}\n", .{c.NULL});

    // Note: Function-like macros need to be wrapped in C helper functions
    // or redefined in Zig
}

/// Example 7: Variadic C functions
fn variadicCFunctions() void {
    std.debug.print("\n=== Variadic C Functions ===\n", .{});
    std.debug.print("Calling C functions with variable arguments\n\n", .{});

    // Call C's printf with different argument counts
    _ = c.printf("Integer: %d\n", @as(c_int, 42));
    _ = c.printf("Float: %.2f\n", @as(c_double, 3.14159));
    _ = c.printf("String: %s, Number: %d\n", "test", @as(c_int, 100));
}

/// Example 8: Translating C code with translate-c
fn translateCExample() void {
    std.debug.print("\n=== Translate-C ===\n", .{});
    std.debug.print("Zig can automatically translate C headers\n\n", .{});

    std.debug.print("Usage: zig translate-c file.h\n", .{});
    std.debug.print("- Converts C headers to Zig\n", .{});
    std.debug.print("- Handles macros, structs, functions\n", .{});
    std.debug.print("- Useful for binding generation\n", .{});
}

pub fn main() !void {
    std.debug.print("=== Zig C Interoperability Examples ===\n", .{});

    callingCFunctions();
    demonstrateExports();
    cTypeConversions();
    try cStringHandling();
    cStructExample();
    cMacrosAndConstants();
    variadicCFunctions();
    translateCExample();

    std.debug.print("\n=== Summary ===\n", .{});
    std.debug.print("- @cImport: Import C headers\n", .{});
    std.debug.print("- export: Export Zig functions to C\n", .{});
    std.debug.print("- c_int, c_float, etc.: C-compatible types\n", .{});
    std.debug.print("- [*:0]const u8: Null-terminated C strings\n", .{});
    std.debug.print("- extern struct: C ABI-compatible structs\n", .{});
    std.debug.print("- translate-c: Automatic C header translation\n", .{});
}

// Tests
test "C integer types" {
    const c_val: c_int = 42;
    const zig_val: i32 = @intCast(c_val);
    try testing.expectEqual(@as(i32, 42), zig_val);
}

test "exported functions" {
    const result = zigAdd(10, 20);
    try testing.expectEqual(@as(c_int, 30), result);

    const result2 = zigMultiply(5, 6);
    try testing.expectEqual(@as(c_int, 30), result2);
}

test "C string length" {
    const str = "Hello";
    const len = c.strlen(str.ptr);
    try testing.expectEqual(@as(usize, 5), len);
}

test "C struct layout" {
    const point = CPoint.init(10, 20);
    try testing.expectEqual(@as(c_int, 10), point.x);
    try testing.expectEqual(@as(c_int, 20), point.y);

    // Verify struct size matches C expectations
    try testing.expectEqual(@as(usize, @sizeOf(c_int) * 2), @sizeOf(CPoint));
}

test "C math functions" {
    const result = c.sqrt(16.0);
    try testing.expectEqual(@as(f64, 4.0), result);

    const result2 = c.pow(2.0, 3.0);
    try testing.expectEqual(@as(f64, 8.0), result2);
}

test "C memory allocation" {
    const ptr = c.malloc(100);
    try testing.expect(ptr != null);
    defer c.free(ptr);

    // Write and read through C pointer
    const bytes: [*]u8 = @ptrCast(ptr);
    bytes[0] = 42;
    try testing.expectEqual(@as(u8, 42), bytes[0]);
}
