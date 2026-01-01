const std = @import("std");
const testing = std.testing;

// Compile-time programming example demonstrating Zig's comptime features

/// Example 1: Comptime variables and expressions
fn comptimeBasics() void {
    std.debug.print("\n=== Comptime Basics ===\n", .{});
    std.debug.print("Values computed at compile time\n\n", .{});

    // Comptime variables must be known at compile time
    comptime var x = 0;
    comptime var i = 0;
    inline while (i < 5) : (i += 1) {
        x += i;
    }

    std.debug.print("Sum of 0..4 (computed at comptime): {d}\n", .{x});

    // Comptime expressions
    const array_size = comptime blk: {
        var size: usize = 1;
        var j: usize = 0;
        while (j < 4) : (j += 1) {
            size *= 2;
        }
        break :blk size;
    };

    std.debug.print("Array size (computed at comptime): {d}\n", .{array_size});
}

/// Example 2: Generic functions using comptime parameters
fn maximum(comptime T: type, a: T, b: T) T {
    return if (a > b) a else b;
}

fn genericFunctions() void {
    std.debug.print("\n=== Generic Functions ===\n", .{});
    std.debug.print("Functions that work with any type\n\n", .{});

    const int_max = maximum(i32, 10, 20);
    std.debug.print("max(10, 20) = {d}\n", .{int_max});

    const float_max = maximum(f64, 3.14, 2.71);
    std.debug.print("max(3.14, 2.71) = {d}\n", .{float_max});

    const unsigned_max = maximum(u8, 100, 200);
    std.debug.print("max(100, 200) = {d}\n", .{unsigned_max});
}

/// Example 3: Generic data structures
fn ArrayList(comptime T: type) type {
    return struct {
        items: []T,
        len: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            return .{
                .items = &[_]T{},
                .len = 0,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            if (self.items.len > 0) {
                self.allocator.free(self.items);
            }
        }

        pub fn append(self: *Self, item: T) !void {
            const new_items = try self.allocator.alloc(T, self.len + 1);
            if (self.len > 0) {
                @memcpy(new_items[0..self.len], self.items);
                self.allocator.free(self.items);
            }
            new_items[self.len] = item;
            self.items = new_items;
            self.len += 1;
        }
    };
}

fn genericStructures() !void {
    std.debug.print("\n=== Generic Data Structures ===\n", .{});
    std.debug.print("Type-parameterized containers\n\n", .{});

    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Create ArrayList for integers
    var int_list = ArrayList(i32).init(allocator);
    defer int_list.deinit();

    try int_list.append(10);
    try int_list.append(20);
    try int_list.append(30);

    std.debug.print("ArrayList(i32): ", .{});
    for (int_list.items) |item| {
        std.debug.print("{d} ", .{item});
    }
    std.debug.print("\n", .{});

    // Create ArrayList for floats
    var float_list = ArrayList(f64).init(allocator);
    defer float_list.deinit();

    try float_list.append(3.14);
    try float_list.append(2.71);

    std.debug.print("ArrayList(f64): ", .{});
    for (float_list.items) |item| {
        std.debug.print("{d} ", .{item});
    }
    std.debug.print("\n", .{});
}

/// Example 4: Type introspection and reflection
fn typeIntrospection() void {
    std.debug.print("\n=== Type Introspection ===\n", .{});
    std.debug.print("Examining types at compile time\n\n", .{});

    const Point = struct {
        x: i32,
        y: i32,
        name: []const u8,
    };

    // Get type info
    const type_info = @typeInfo(Point);
    std.debug.print("Type: {s}\n", .{@typeName(Point)});
    std.debug.print("Kind: Struct\n", .{});
    std.debug.print("Fields: {d}\n", .{type_info.Struct.fields.len});

    inline for (type_info.Struct.fields) |field| {
        std.debug.print("  - {s}: {s}\n", .{ field.name, @typeName(field.type) });
    }

    // Check type properties
    std.debug.print("\nType checks:\n", .{});
    std.debug.print("  i32 is signed: {}\n", .{@typeInfo(i32).Int.signedness == .signed});
    std.debug.print("  u32 is signed: {}\n", .{@typeInfo(u32).Int.signedness == .signed});
    std.debug.print("  i32 bit size: {d}\n", .{@typeInfo(i32).Int.bits});
}

/// Example 5: Comptime string manipulation
fn comptimeStringManip() void {
    std.debug.print("\n=== Comptime String Manipulation ===\n", .{});
    std.debug.print("String operations at compile time\n\n", .{});

    const prefix = "Hello";
    const suffix = "World";

    // Concatenate at compile time
    const message = comptime prefix ++ ", " ++ suffix ++ "!";
    std.debug.print("Comptime string: {s}\n", .{message});

    // Compute string length at compile time
    const len = comptime message.len;
    std.debug.print("Length (computed at comptime): {d}\n", .{len});
}

/// Example 6: Conditional compilation based on type
fn printValue(comptime T: type, value: T) void {
    const type_info = @typeInfo(T);

    switch (type_info) {
        .Int => std.debug.print("Integer: {d}\n", .{value}),
        .Float => std.debug.print("Float: {d}\n", .{value}),
        .Bool => std.debug.print("Boolean: {}\n", .{value}),
        .Pointer => |ptr_info| {
            if (ptr_info.child == u8) {
                std.debug.print("String: {s}\n", .{value});
            } else {
                std.debug.print("Pointer to {s}\n", .{@typeName(ptr_info.child)});
            }
        },
        else => std.debug.print("Other type: {s}\n", .{@typeName(T)}),
    }
}

fn conditionalCompilation() void {
    std.debug.print("\n=== Conditional Compilation ===\n", .{});
    std.debug.print("Different code based on type\n\n", .{});

    printValue(i32, 42);
    printValue(f64, 3.14);
    printValue(bool, true);
    printValue([]const u8, "Hello");
}

/// Example 7: Comptime assertions and validation
fn Vector(comptime T: type, comptime size: usize) type {
    // Comptime assertions
    comptime {
        if (size == 0) @compileError("Vector size must be > 0");
        if (@typeInfo(T) != .Int and @typeInfo(T) != .Float) {
            @compileError("Vector only supports numeric types");
        }
    }

    return struct {
        data: [size]T,

        pub fn init() @This() {
            return .{ .data = [_]T{0} ** size };
        }

        pub fn dot(self: @This(), other: @This()) T {
            var result: T = 0;
            inline for (0..size) |i| {
                result += self.data[i] * other.data[i];
            }
            return result;
        }
    };
}

fn comptimeValidation() void {
    std.debug.print("\n=== Comptime Validation ===\n", .{});
    std.debug.print("Type safety enforced at compile time\n\n", .{});

    const Vec3i = Vector(i32, 3);
    var v1 = Vec3i.init();
    v1.data = .{ 1, 2, 3 };

    var v2 = Vec3i.init();
    v2.data = .{ 4, 5, 6 };

    const dot_product = v1.dot(v2);
    std.debug.print("Dot product: {d}\n", .{dot_product});

    // These would cause compile errors:
    // const BadVec = Vector(i32, 0); // Size must be > 0
    // const BadVec2 = Vector([]const u8, 3); // Only numeric types
}

/// Example 8: Inline loops for optimization
fn inlineLoops() void {
    std.debug.print("\n=== Inline Loops ===\n", .{});
    std.debug.print("Loop unrolling at compile time\n\n", .{});

    const values = [_]i32{ 10, 20, 30, 40, 50 };

    // inline for unrolls the loop at compile time
    std.debug.print("Values: ", .{});
    inline for (values) |val| {
        std.debug.print("{d} ", .{val});
    }
    std.debug.print("\n", .{});

    // Each iteration is a separate instruction (no loop overhead)
}

pub fn main() !void {
    std.debug.print("=== Zig Comptime Programming Examples ===\n", .{});

    comptimeBasics();
    genericFunctions();
    try genericStructures();
    typeIntrospection();
    comptimeStringManip();
    conditionalCompilation();
    comptimeValidation();
    inlineLoops();

    std.debug.print("\n=== Summary ===\n", .{});
    std.debug.print("- comptime: Execute code at compile time\n", .{});
    std.debug.print("- Generic functions: Type parameters with comptime\n", .{});
    std.debug.print("- Generic types: Functions that return types\n", .{});
    std.debug.print("- @typeInfo: Introspect types at compile time\n", .{});
    std.debug.print("- @compileError: Fail compilation with message\n", .{});
    std.debug.print("- inline for: Unroll loops at compile time\n", .{});
}

// Tests
test "generic maximum function" {
    try testing.expectEqual(@as(i32, 20), maximum(i32, 10, 20));
    try testing.expectEqual(@as(f64, 3.14), maximum(f64, 3.14, 2.71));
}

test "generic ArrayList" {
    const allocator = testing.allocator;

    var list = ArrayList(i32).init(allocator);
    defer list.deinit();

    try list.append(1);
    try list.append(2);
    try list.append(3);

    try testing.expectEqual(@as(usize, 3), list.len);
    try testing.expectEqual(@as(i32, 1), list.items[0]);
    try testing.expectEqual(@as(i32, 2), list.items[1]);
    try testing.expectEqual(@as(i32, 3), list.items[2]);
}

test "type introspection" {
    const T = i32;
    const info = @typeInfo(T);

    try testing.expect(info == .Int);
    try testing.expectEqual(@as(u16, 32), info.Int.bits);
    try testing.expect(info.Int.signedness == .signed);
}

test "Vector type" {
    const Vec2 = Vector(i32, 2);

    var v1 = Vec2.init();
    v1.data = .{ 3, 4 };

    var v2 = Vec2.init();
    v2.data = .{ 1, 2 };

    const dot = v1.dot(v2);
    try testing.expectEqual(@as(i32, 11), dot); // 3*1 + 4*2 = 11
}

test "comptime string operations" {
    const str1 = "Hello";
    const str2 = "World";
    const combined = comptime str1 ++ " " ++ str2;

    try testing.expectEqualStrings("Hello World", combined);
    try testing.expectEqual(@as(usize, 11), combined.len);
}

test "conditional type printing" {
    // This test mainly ensures the function compiles for various types
    const T1 = i32;
    const T2 = f64;
    const T3 = bool;

    comptime {
        const info1 = @typeInfo(T1);
        const info2 = @typeInfo(T2);
        const info3 = @typeInfo(T3);

        try testing.expect(info1 == .Int);
        try testing.expect(info2 == .Float);
        try testing.expect(info3 == .Bool);
    }
}
