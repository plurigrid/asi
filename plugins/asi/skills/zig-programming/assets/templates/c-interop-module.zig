// Target Zig Version: 0.15.2
// For other versions, see references/version-differences.md

const std = @import("std");
const testing = std.testing;

// C Interoperability Module Template
// Demonstrates C FFI, header imports, and exporting Zig functions to C

// Import C headers
const c = @cImport({
    // TODO: Include your C headers here
    @cInclude("stdio.h");
    @cInclude("stdlib.h");
    @cInclude("string.h");

    // For custom C libraries, specify include paths in build.zig:
    // exe.addIncludePath(.{ .path = "path/to/headers" });
    // exe.linkLibC();
    // exe.linkSystemLibrary("your_library");
});

// =============================================================================
// C-Compatible Types
// =============================================================================

/// C-compatible struct (uses C ABI layout)
pub const CPoint = extern struct {
    x: c_int,
    y: c_int,

    pub fn init(x: c_int, y: c_int) CPoint {
        return .{ .x = x, .y = y };
    }

    pub fn distanceFrom(self: CPoint, other: CPoint) f64 {
        const dx: f64 = @floatFromInt(other.x - self.x);
        const dy: f64 = @floatFromInt(other.y - self.y);
        return @sqrt(dx * dx + dy * dy);
    }
};

/// C-compatible enum
pub const CStatus = enum(c_int) {
    success = 0,
    error_invalid_input = -1,
    error_out_of_memory = -2,
    error_io = -3,
};

/// Opaque C struct (when you don't know the internal structure)
pub const CHandle = opaque {
    // Used for C types where internal structure is hidden
    // Example: typedef struct CHandle_t CHandle;
};

// =============================================================================
// Exporting Zig Functions to C
// =============================================================================

/// Add two integers (callable from C)
export fn zig_add(a: c_int, b: c_int) c_int {
    return a + b;
}

/// Multiply two integers (callable from C)
export fn zig_multiply(a: c_int, b: c_int) c_int {
    return a * b;
}

/// Process a C string (callable from C)
/// Note: Uses null-terminated strings [*:0]const u8
export fn zig_string_length(str: [*:0]const u8) c_int {
    return @intCast(std.mem.len(str));
}

/// Process array from C (callable from C)
/// C signature: int zig_sum_array(int* array, int length)
export fn zig_sum_array(array: [*]const c_int, length: c_int) c_int {
    var sum: c_int = 0;
    var i: usize = 0;
    while (i < length) : (i += 1) {
        sum += array[i];
    }
    return sum;
}

/// Create a point (callable from C)
export fn zig_create_point(x: c_int, y: c_int, out: *CPoint) void {
    out.* = CPoint.init(x, y);
}

/// Return status code (callable from C)
export fn zig_process_value(value: c_int) c_int {
    if (value < 0) {
        return @intFromEnum(CStatus.error_invalid_input);
    }
    if (value > 1000) {
        return @intFromEnum(CStatus.error_out_of_memory);
    }
    return @intFromEnum(CStatus.success);
}

// =============================================================================
// Calling C Functions from Zig
// =============================================================================

/// Wrapper around C's malloc
pub fn cMalloc(size: usize) ?*anyopaque {
    return c.malloc(size);
}

/// Wrapper around C's free
pub fn cFree(ptr: ?*anyopaque) void {
    c.free(ptr);
}

/// Use C string functions
pub fn copyString(dest: [*]u8, src: [*:0]const u8) [*]u8 {
    return @ptrCast(c.strcpy(@ptrCast(dest), src));
}

/// Call C's printf
pub fn printMessage(comptime fmt: [*:0]const u8, args: anytype) void {
    _ = @call(.auto, c.printf, .{fmt} ++ args);
}

// =============================================================================
// Memory Management with C
// =============================================================================

/// Allocate C-compatible memory using Zig allocator
pub fn allocCString(allocator: std.mem.Allocator, str: []const u8) ![:0]u8 {
    // Allocate with sentinel (null terminator)
    const result = try allocator.allocSentinel(u8, str.len, 0);
    @memcpy(result, str);
    return result;
}

/// Convert C string to Zig slice
pub fn cStringToSlice(c_str: [*:0]const u8) []const u8 {
    return std.mem.span(c_str);
}

// =============================================================================
// Working with C Arrays
// =============================================================================

/// Convert Zig slice to C array pointer
pub fn sliceToCArray(slice: []const c_int) [*]const c_int {
    return slice.ptr;
}

/// Convert C array to Zig slice (requires known length)
pub fn cArrayToSlice(array: [*]const c_int, length: usize) []const c_int {
    return array[0..length];
}

// =============================================================================
// Callbacks and Function Pointers
// =============================================================================

/// C-compatible function pointer type
pub const CCallback = *const fn (value: c_int) callconv(.C) void;

/// Example callback function
export fn example_callback(value: c_int) void {
    std.debug.print("Callback received: {d}\n", .{value});
}

/// Call a C callback from Zig
pub fn invokeCallback(callback: CCallback, value: c_int) void {
    callback(value);
}

// =============================================================================
// Error Handling with C
// =============================================================================

/// Convert C error codes to Zig errors
pub const CError = error{
    CInvalidInput,
    COutOfMemory,
    CIOError,
};

pub fn statusToError(status: c_int) CError!void {
    return switch (status) {
        0 => {},
        -1 => CError.CInvalidInput,
        -2 => CError.COutOfMemory,
        -3 => CError.CIOError,
        else => CError.CInvalidInput,
    };
}

// =============================================================================
// Tests
// =============================================================================

test "C types compatibility" {
    const point = CPoint.init(3, 4);
    try testing.expectEqual(@as(c_int, 3), point.x);
    try testing.expectEqual(@as(c_int, 4), point.y);

    const distance = point.distanceFrom(CPoint.init(0, 0));
    try testing.expectEqual(@as(f64, 5.0), distance);
}

test "exported functions" {
    try testing.expectEqual(@as(c_int, 7), zig_add(3, 4));
    try testing.expectEqual(@as(c_int, 12), zig_multiply(3, 4));
}

test "C string handling" {
    const c_str: [*:0]const u8 = "Hello";
    const len = zig_string_length(c_str);
    try testing.expectEqual(@as(c_int, 5), len);

    const slice = cStringToSlice(c_str);
    try testing.expectEqualStrings("Hello", slice);
}

test "C array operations" {
    const array = [_]c_int{ 1, 2, 3, 4, 5 };
    const sum = zig_sum_array(&array, 5);
    try testing.expectEqual(@as(c_int, 15), sum);
}

test "status codes" {
    const status1 = zig_process_value(50);
    try testing.expectEqual(@as(c_int, 0), status1);

    const status2 = zig_process_value(-10);
    try testing.expectEqual(@as(c_int, -1), status2);

    try statusToError(0);
    try testing.expectError(CError.CInvalidInput, statusToError(-1));
}

test "C memory allocation" {
    const allocator = testing.allocator;

    const zig_str = "Hello, C!";
    const c_str = try allocCString(allocator, zig_str);
    defer allocator.free(c_str);

    try testing.expectEqualStrings(zig_str, c_str);
}

test "callback invocation" {
    // Test that callback can be called
    invokeCallback(example_callback, 42);
}

test "C malloc/free" {
    const ptr = cMalloc(100);
    try testing.expect(ptr != null);
    defer cFree(ptr);

    // Use the memory
    const bytes: [*]u8 = @ptrCast(ptr);
    bytes[0] = 42;
    try testing.expectEqual(@as(u8, 42), bytes[0]);
}

// =============================================================================
// Build Configuration Example
// =============================================================================

// In your build.zig, add:
//
// const exe = b.addExecutable(.{
//     .name = "my_c_interop",
//     .root_source_file = .{ .path = "src/main.zig" },
//     .target = target,
//     .optimize = optimize,
// });
//
// // Link with C standard library
// exe.linkLibC();
//
// // Add C include directories
// exe.addIncludePath(.{ .path = "path/to/c/headers" });
//
// // Link with C libraries
// exe.linkSystemLibrary("your_c_library");
//
// // For static libraries
// exe.addObjectFile(.{ .path = "path/to/library.a" });
//
// // For dynamic libraries
// exe.addLibraryPath(.{ .path = "path/to/libs" });
// exe.linkSystemLibrary("your_shared_lib");

// =============================================================================
// Usage Examples
// =============================================================================

// To use translate-c for automatic C header conversion:
// zig translate-c your_header.h > bindings.zig
//
// To compile with C code:
// zig build-exe main.zig your_c_file.c -lc
//
// To create a shared library callable from C:
// zig build-lib -dynamic library.zig
