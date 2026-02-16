# Functions & Callbacks Recipes

*11 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [7.1](#recipe-7-1) | Writing Functions That Accept Any Number of Arguments | intermediate |
| [7.2](#recipe-7-2) | Writing Functions That Only Accept Keyword Arguments | intermediate |
| [7.3](#recipe-7-3) | Attaching Informational Metadata to Function Arguments | intermediate |
| [7.4](#recipe-7-4) | Returning Multiple Values from a Function | intermediate |
| [7.5](#recipe-7-5) | Defining Functions with Default Arguments | intermediate |
| [7.6](#recipe-7-6) | Defining Anonymous or Inline Functions | intermediate |
| [7.7](#recipe-7-7) | Capturing Variables in Anonymous Functions | intermediate |
| [7.8](#recipe-7-8) | Making an N-Argument Callable Work As a Callable with Fewer Arguments | intermediate |
| [7.9](#recipe-7-9) | Replacing Single Method Classes with Functions | intermediate |
| [7.10](#recipe-7-10) | Carrying Extra State with Callback Functions | intermediate |
| [7.11](#recipe-7-11) | Inlining Callback Functions | intermediate |

---

## Recipe 7.1: Writing Functions That Accept Any Number of Arguments {#recipe-7-1}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, functions, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_1.zig`

### Problem

You need to write a function that can accept a variable number of arguments, similar to variadic functions in other languages.

### Solution

### Runtime Variadic

```zig
/// Sum using slice (runtime variadic)
pub fn sum(numbers: []const i32) i32 {
    var total: i32 = 0;
    for (numbers) |n| {
        total += n;
    }
    return total;
}
```

### Comptime Variadic

```zig
/// Sum using comptime tuple
pub fn sumComptime(args: anytype) @TypeOf(args[0]) {
    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    if (args_type_info != .@"struct") {
        @compileError("Expected tuple argument");
    }

    const fields = args_type_info.@"struct".fields;
    if (fields.len == 0) {
        @compileError("Need at least one argument");
    }

    var total: @TypeOf(args[0]) = 0;
    inline for (fields) |field| {
        total += @field(args, field.name);
    }
    return total;
}
```

### Generic Print

```zig
/// Generic print function
pub fn print(writer: anytype, args: anytype) !void {
    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    if (args_type_info != .@"struct") {
        @compileError("Expected tuple argument");
    }

    inline for (args_type_info.@"struct".fields) |field| {
        const value = @field(args, field.name);
        const ValueType = @TypeOf(value);
        const value_type_info = @typeInfo(ValueType);

        // Check if it's a string-like type (pointer to u8 array or slice)
        const is_string = switch (value_type_info) {
            .pointer => |ptr_info| blk: {
                const child_info = @typeInfo(ptr_info.child);
                break :blk switch (child_info) {
                    .array => |arr_info| arr_info.child == u8,
                    else => ptr_info.child == u8,
                };
            },
            else => false,
        };

        if (is_string) {
            try writer.print("{s} ", .{value});
        } else {
            try writer.print("{any} ", .{value});
        }
    }
}
```

### Discussion

### Compile-Time Variadic Functions

Use tuples for compile-time known arguments (see code examples above).
    }
    return total;
}

test "sum comptime" {
    const result = sumComptime(.{ 1, 2, 3, 4, 5 });
    try std.testing.expectEqual(@as(i32, 15), result);

    const result2 = sumComptime(.{ 1.5, 2.5, 3.0 });
    try std.testing.expectEqual(@as(f32, 7.0), result2);
}
```

### Generic Print Function

Accept any types at compile time:

```zig
pub fn print(writer: anytype, args: anytype) !void {
    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    if (args_type_info != .@"struct") {
        @compileError("Expected tuple argument");
    }

    inline for (args_type_info.@"struct".fields) |field| {
        const value = @field(args, field.name);
        const ValueType = @TypeOf(value);
        const value_type_info = @typeInfo(ValueType);

        // Check if it's a string-like type (pointer to u8 array or slice)
        const is_string = switch (value_type_info) {
            .pointer => |ptr_info| blk: {
                const child_info = @typeInfo(ptr_info.child);
                break :blk switch (child_info) {
                    .array => |arr_info| arr_info.child == u8,
                    else => ptr_info.child == u8,
                };
            },
            else => false,
        };

        if (is_string) {
            try writer.print("{s} ", .{value});
        } else {
            try writer.print("{any} ", .{value});
        }
    }
}

test "generic print" {
    var buffer: [256]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try print(fbs.writer(), .{ 42, "hello", 3.14 });

    try std.testing.expectEqualStrings("42 hello 3.14 ", fbs.getWritten());
}
```

### Formatted String Builder

Build strings with variable arguments:

```zig
pub fn buildString(
    allocator: std.mem.Allocator,
    args: anytype,
) ![]u8 {
    var list = std.ArrayList(u8){};
    errdefer list.deinit(allocator);

    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    inline for (args_type_info.@"struct".fields) |field| {
        const value = @field(args, field.name);
        const str = try std.fmt.allocPrint(allocator, "{any}", .{value});
        defer allocator.free(str);
        try list.appendSlice(allocator, str);
    }

    return list.toOwnedSlice(allocator);
}

test "build string" {
    const allocator = std.testing.allocator;

    const result = try buildString(allocator, .{ "Hello", " ", "World", "!" });
    defer allocator.free(result);

    try std.testing.expectEqualStrings("Hello World!", result);
}
```

### Minimum/Maximum Functions

Find min/max of any number of values:

```zig
pub fn min(args: anytype) @TypeOf(args[0]) {
    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    if (args_type_info != .@"struct") {
        @compileError("Expected tuple argument");
    }

    const fields = args_type_info.@"struct".fields;
    if (fields.len == 0) {
        @compileError("Need at least one argument");
    }

    var minimum = args[0];
    inline for (fields[1..]) |field| {
        const value = @field(args, field.name);
        if (value < minimum) {
            minimum = value;
        }
    }
    return minimum;
}

pub fn max(args: anytype) @TypeOf(args[0]) {
    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    if (args_type_info != .@"struct") {
        @compileError("Expected tuple argument");
    }

    const fields = args_type_info.@"struct".fields;
    if (fields.len == 0) {
        @compileError("Need at least one argument");
    }

    var maximum = args[0];
    inline for (fields[1..]) |field| {
        const value = @field(args, field.name);
        if (value > maximum) {
            maximum = value;
        }
    }
    return maximum;
}

test "min and max" {
    try std.testing.expectEqual(@as(i32, 1), min(.{ 5, 3, 1, 4, 2 }));
    try std.testing.expectEqual(@as(i32, 5), max(.{ 5, 3, 1, 4, 2 }));

    try std.testing.expectEqual(@as(f32, -2.5), min(.{ 1.5, -2.5, 3.0 }));
    try std.testing.expectEqual(@as(f32, 3.0), max(.{ 1.5, -2.5, 3.0 }));
}
```

### Type-Safe Logging

Log with type-checked arguments:

```zig
pub const LogLevel = enum {
    debug,
    info,
    warn,
    err,
};

pub fn log(
    writer: anytype,
    level: LogLevel,
    args: anytype,
) !void {
    try writer.print("[{s}] ", .{@tagName(level)});

    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    inline for (args_type_info.@"struct".fields, 0..) |field, i| {
        const value = @field(args, field.name);
        if (i > 0) {
            try writer.writeAll(" ");
        }
        try writer.print("{any}", .{value});
    }

    try writer.writeAll("\n");
}

test "logging" {
    var buffer: [256]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try log(fbs.writer(), .info, .{ "User", 42, "logged in" });

    try std.testing.expect(std.mem.startsWith(u8, fbs.getWritten(), "[info]"));
    try std.testing.expect(std.mem.indexOf(u8, fbs.getWritten(), "User") != null);
}
```

### Slice-Based Variadic for Runtime

Use slices when argument count is only known at runtime:

```zig
pub fn average(numbers: []const f64) f64 {
    if (numbers.len == 0) return 0.0;

    var sum: f64 = 0.0;
    for (numbers) |n| {
        sum += n;
    }
    return sum / @as(f64, @floatFromInt(numbers.len));
}

test "average" {
    const result1 = average(&[_]f64{ 1.0, 2.0, 3.0, 4.0, 5.0 });
    try std.testing.expectEqual(@as(f64, 3.0), result1);

    const result2 = average(&[_]f64{});
    try std.testing.expectEqual(@as(f64, 0.0), result2);
}
```

### Best Practices

**Compile-Time vs Runtime:**
```zig
// Use tuples for compile-time known arguments
const result = sum(.{ 1, 2, 3 }); // Comptime

// Use slices for runtime variable arguments
const numbers = try getUserInput();
const result = sum(numbers); // Runtime
```

**Type Safety:**
- Tuples provide compile-time type checking
- All tuple elements are accessible at comptime
- Use `anytype` parameter to accept tuples
- Use `@TypeOf` and `@typeInfo` to introspect

**Error Handling:**
```zig
pub fn processAll(allocator: std.mem.Allocator, items: anytype) !void {
    inline for (@typeInfo(@TypeOf(items)).@"struct".fields) |field| {
        const item = @field(items, field.name);
        try processItem(allocator, item);
    }
}
```

**Performance:**
- Tuple-based functions are inlined at compile time
- Slice-based functions have runtime overhead
- Use tuples when possible for zero-cost abstraction

### Related Functions

- `@TypeOf()` - Get type of expression
- `@typeInfo()` - Get reflection information
- `@field()` - Access struct/tuple field
- `@tagName()` - Get enum tag name as string
- `inline for` - Unroll loops at compile time
- `anytype` - Accept any type parameter

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: runtime_variadic
/// Sum using slice (runtime variadic)
pub fn sum(numbers: []const i32) i32 {
    var total: i32 = 0;
    for (numbers) |n| {
        total += n;
    }
    return total;
}
// ANCHOR_END: runtime_variadic

// ANCHOR: comptime_variadic
/// Sum using comptime tuple
pub fn sumComptime(args: anytype) @TypeOf(args[0]) {
    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    if (args_type_info != .@"struct") {
        @compileError("Expected tuple argument");
    }

    const fields = args_type_info.@"struct".fields;
    if (fields.len == 0) {
        @compileError("Need at least one argument");
    }

    var total: @TypeOf(args[0]) = 0;
    inline for (fields) |field| {
        total += @field(args, field.name);
    }
    return total;
}
// ANCHOR_END: comptime_variadic

// ANCHOR: generic_print
/// Generic print function
pub fn print(writer: anytype, args: anytype) !void {
    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    if (args_type_info != .@"struct") {
        @compileError("Expected tuple argument");
    }

    inline for (args_type_info.@"struct".fields) |field| {
        const value = @field(args, field.name);
        const ValueType = @TypeOf(value);
        const value_type_info = @typeInfo(ValueType);

        // Check if it's a string-like type (pointer to u8 array or slice)
        const is_string = switch (value_type_info) {
            .pointer => |ptr_info| blk: {
                const child_info = @typeInfo(ptr_info.child);
                break :blk switch (child_info) {
                    .array => |arr_info| arr_info.child == u8,
                    else => ptr_info.child == u8,
                };
            },
            else => false,
        };

        if (is_string) {
            try writer.print("{s} ", .{value});
        } else {
            try writer.print("{any} ", .{value});
        }
    }
}
// ANCHOR_END: generic_print

/// Build string from multiple arguments
pub fn buildString(
    allocator: std.mem.Allocator,
    args: anytype,
) ![]u8 {
    var list = std.ArrayList(u8){};
    errdefer list.deinit(allocator);

    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    inline for (args_type_info.@"struct".fields) |field| {
        const value = @field(args, field.name);
        const ValueType = @TypeOf(value);
        const value_type_info = @typeInfo(ValueType);

        // Check if it's a string-like type (pointer to u8 array or slice)
        const is_string = switch (value_type_info) {
            .pointer => |ptr_info| blk: {
                const child_info = @typeInfo(ptr_info.child);
                break :blk switch (child_info) {
                    .array => |arr_info| arr_info.child == u8,
                    else => ptr_info.child == u8,
                };
            },
            else => false,
        };

        const str = if (is_string)
            try std.fmt.allocPrint(allocator, "{s}", .{value})
        else
            try std.fmt.allocPrint(allocator, "{any}", .{value});
        defer allocator.free(str);
        try list.appendSlice(allocator, str);
    }

    return list.toOwnedSlice(allocator);
}

/// Find minimum value
pub fn min(args: anytype) @TypeOf(args[0]) {
    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    if (args_type_info != .@"struct") {
        @compileError("Expected tuple argument");
    }

    const fields = args_type_info.@"struct".fields;
    if (fields.len == 0) {
        @compileError("Need at least one argument");
    }

    var minimum = args[0];
    inline for (fields[1..]) |field| {
        const value = @field(args, field.name);
        if (value < minimum) {
            minimum = value;
        }
    }
    return minimum;
}

/// Find maximum value
pub fn max(args: anytype) @TypeOf(args[0]) {
    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    if (args_type_info != .@"struct") {
        @compileError("Expected tuple argument");
    }

    const fields = args_type_info.@"struct".fields;
    if (fields.len == 0) {
        @compileError("Need at least one argument");
    }

    var maximum = args[0];
    inline for (fields[1..]) |field| {
        const value = @field(args, field.name);
        if (value > maximum) {
            maximum = value;
        }
    }
    return maximum;
}

/// Log levels
pub const LogLevel = enum {
    debug,
    info,
    warn,
    err,
};

/// Logging with variable arguments
pub fn log(
    writer: anytype,
    level: LogLevel,
    args: anytype,
) !void {
    try writer.print("[{s}] ", .{@tagName(level)});

    const ArgsType = @TypeOf(args);
    const args_type_info = @typeInfo(ArgsType);

    inline for (args_type_info.@"struct".fields, 0..) |field, i| {
        const value = @field(args, field.name);
        const ValueType = @TypeOf(value);
        const value_type_info = @typeInfo(ValueType);

        // Check if it's a string-like type (pointer to u8 array or slice)
        const is_string = switch (value_type_info) {
            .pointer => |ptr_info| blk: {
                const child_info = @typeInfo(ptr_info.child);
                break :blk switch (child_info) {
                    .array => |arr_info| arr_info.child == u8,
                    else => ptr_info.child == u8,
                };
            },
            else => false,
        };

        if (i > 0) {
            try writer.writeAll(" ");
        }

        if (is_string) {
            try writer.print("{s}", .{value});
        } else {
            try writer.print("{any}", .{value});
        }
    }

    try writer.writeAll("\n");
}

/// Calculate average
pub fn average(numbers: []const f64) f64 {
    if (numbers.len == 0) return 0.0;

    var sum_total: f64 = 0.0;
    for (numbers) |n| {
        sum_total += n;
    }
    return sum_total / @as(f64, @floatFromInt(numbers.len));
}

// Tests

test "sum with slice" {
    const result1 = sum(&[_]i32{ 1, 2, 3 });
    try std.testing.expectEqual(@as(i32, 6), result1);

    const result2 = sum(&[_]i32{ 10, 20, 30, 40 });
    try std.testing.expectEqual(@as(i32, 100), result2);

    const result3 = sum(&[_]i32{});
    try std.testing.expectEqual(@as(i32, 0), result3);
}

test "sum comptime" {
    const result = sumComptime(.{ 1, 2, 3, 4, 5 });
    try std.testing.expectEqual(@as(i32, 15), result);

    const result2 = sumComptime(.{ 1.5, 2.5, 3.0 });
    try std.testing.expectEqual(@as(f32, 7.0), result2);
}

test "generic print" {
    var buffer: [256]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try print(fbs.writer(), .{ 42, "hello", 3.14 });

    try std.testing.expectEqualStrings("42 hello 3.14 ", fbs.getWritten());
}

test "build string" {
    const allocator = std.testing.allocator;

    const result = try buildString(allocator, .{ "Hello", " ", "World", "!" });
    defer allocator.free(result);

    try std.testing.expectEqualStrings("Hello World!", result);
}

test "min and max" {
    try std.testing.expectEqual(@as(i32, 1), min(.{ 5, 3, 1, 4, 2 }));
    try std.testing.expectEqual(@as(i32, 5), max(.{ 5, 3, 1, 4, 2 }));

    try std.testing.expectEqual(@as(f32, -2.5), min(.{ 1.5, -2.5, 3.0 }));
    try std.testing.expectEqual(@as(f32, 3.0), max(.{ 1.5, -2.5, 3.0 }));
}

test "logging" {
    var buffer: [256]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try log(fbs.writer(), .info, .{ "User", 42, "logged in" });

    try std.testing.expect(std.mem.startsWith(u8, fbs.getWritten(), "[info]"));
    try std.testing.expect(std.mem.indexOf(u8, fbs.getWritten(), "User") != null);
}

test "average" {
    const result1 = average(&[_]f64{ 1.0, 2.0, 3.0, 4.0, 5.0 });
    try std.testing.expectEqual(@as(f64, 3.0), result1);

    const result2 = average(&[_]f64{});
    try std.testing.expectEqual(@as(f64, 0.0), result2);
}

test "single value" {
    try std.testing.expectEqual(@as(i32, 42), min(.{42}));
    try std.testing.expectEqual(@as(i32, 42), max(.{42}));
}

test "negative numbers" {
    try std.testing.expectEqual(@as(i32, -10), min(.{ -5, -3, -10, -1 }));
    try std.testing.expectEqual(@as(i32, -1), max(.{ -5, -3, -10, -1 }));
}

test "mixed types in print" {
    var buffer: [256]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try print(fbs.writer(), .{ 1, 2.5, "test", true });

    const written = fbs.getWritten();
    try std.testing.expect(std.mem.indexOf(u8, written, "1 ") != null);
    try std.testing.expect(std.mem.indexOf(u8, written, "2.5") != null);
    try std.testing.expect(std.mem.indexOf(u8, written, "test") != null);
    try std.testing.expect(std.mem.indexOf(u8, written, "true") != null);
}

test "empty buildString" {
    const allocator = std.testing.allocator;

    const result = try buildString(allocator, .{});
    defer allocator.free(result);

    try std.testing.expectEqualStrings("", result);
}

test "log levels" {
    var buffer: [256]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try log(fbs.writer(), .debug, .{"Debug message"});
    try std.testing.expect(std.mem.startsWith(u8, fbs.getWritten(), "[debug]"));

    fbs.pos = 0;
    try log(fbs.writer(), .err, .{"Error occurred"});
    try std.testing.expect(std.mem.startsWith(u8, fbs.getWritten(), "[err]"));
}

test "large slice sum" {
    var numbers: [100]i32 = undefined;
    for (&numbers, 0..) |*n, i| {
        n.* = @intCast(i + 1);
    }

    const result = sum(&numbers);
    try std.testing.expectEqual(@as(i32, 5050), result);
}

test "float comptime sum" {
    const result = sumComptime(.{ 1.1, 2.2, 3.3 });
    try std.testing.expectApproxEqAbs(@as(f64, 6.6), result, 0.001);
}

test "single element average" {
    const result = average(&[_]f64{42.0});
    try std.testing.expectEqual(@as(f64, 42.0), result);
}
```

---

## Recipe 7.2: Writing Functions That Only Accept Keyword Arguments {#recipe-7-2}

**Tags:** allocators, arraylist, comptime, concurrency, data-structures, error-handling, functions, memory, resource-cleanup, slices, testing, threading
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_2.zig`

### Problem

You need to write a function with keyword-only arguments to make the API clearer and prevent argument order mistakes.

### Solution

### Basic Config

```zig
/// Connection configuration with defaults
const ConnectionConfig = struct {
    host: []const u8 = "localhost",
    port: u16 = 8080,
    timeout_ms: u32 = 5000,
    use_ssl: bool = false,
};

/// Connect with configuration
pub fn connect(config: ConnectionConfig) !void {
    std.debug.print("Connecting to {s}:{d}\n", .{ config.host, config.port });
    std.debug.print("SSL: {}, Timeout: {}ms\n", .{ config.use_ssl, config.timeout_ms });
}
```

### Required Optional

```zig
/// File options with required and optional fields
const FileOptions = struct {
    path: []const u8, // Required
    mode: std.fs.File.OpenMode = .read_only,
    buffer_size: usize = 4096,
    create_if_missing: bool = false,
};

/// Open file with options
pub fn openFile(allocator: std.mem.Allocator, options: FileOptions) !void {
    _ = allocator;
    std.debug.print("Opening {s} in mode {s}\n", .{
        options.path,
        @tagName(options.mode),
    });
    std.debug.print("Buffer: {} bytes, Create: {}\n", .{
        options.buffer_size,
        options.create_if_missing,
    });
}
```

### Builder Pattern

```zig
/// Query builder with fluent interface
const QueryBuilder = struct {
    allocator: std.mem.Allocator,
    table: ?[]const u8 = null,
    where_clause: ?[]const u8 = null,
    limit: ?usize = null,
    offset: ?usize = null,

    pub fn init(allocator: std.mem.Allocator) QueryBuilder {
        return .{ .allocator = allocator };
    }

    pub fn from(self: QueryBuilder, table_name: []const u8) QueryBuilder {
        var result = self;
        result.table = table_name;
        return result;
    }

    pub fn where(self: QueryBuilder, clause: []const u8) QueryBuilder {
        var result = self;
        result.where_clause = clause;
        return result;
    }

    pub fn limitTo(self: QueryBuilder, n: usize) QueryBuilder {
        var result = self;
        result.limit = n;
        return result;
    }

    pub fn offsetBy(self: QueryBuilder, n: usize) QueryBuilder {
        var result = self;
        result.offset = n;
        return result;
    }

    pub fn build(self: QueryBuilder) ![]const u8 {
        var list = std.ArrayList(u8){};
        errdefer list.deinit(self.allocator);

        try list.appendSlice(self.allocator, "SELECT * FROM ");
        try list.appendSlice(self.allocator, self.table orelse "unknown");

        if (self.where_clause) |clause| {
            try list.appendSlice(self.allocator, " WHERE ");
            try list.appendSlice(self.allocator, clause);
        }

        if (self.limit) |lim| {
            const limit_str = try std.fmt.allocPrint(self.allocator, " LIMIT {}", .{lim});
            defer self.allocator.free(limit_str);
            try list.appendSlice(self.allocator, limit_str);
        }

        if (self.offset) |off| {
            const offset_str = try std.fmt.allocPrint(self.allocator, " OFFSET {}", .{off});
            defer self.allocator.free(offset_str);
            try list.appendSlice(self.allocator, offset_str);
        }

        return list.toOwnedSlice(self.allocator);
    }
};
```

### Discussion

### Required and Optional Parameters

Mix required and optional fields (see code examples above).
    std.debug.print("Opening {s} in mode {s}\n", .{
        options.path,
        @tagName(options.mode),
    });
    std.debug.print("Buffer: {} bytes, Create: {}\n", .{
        options.buffer_size,
        options.create_if_missing,
    });

    // Placeholder - in real code, would open the file
    return error.NotImplemented;
}

test "required and optional parameters" {
    const allocator = std.testing.allocator;

    // Required parameter must be provided
    _ = openFile(allocator, .{ .path = "/tmp/test.txt" }) catch {};

    // Can override defaults
    _ = openFile(allocator, .{
        .path = "/tmp/data.bin",
        .mode = .read_write,
        .buffer_size = 8192,
    }) catch {};
}
```

### Builder Pattern

Create fluent interfaces with method chaining:

```zig
const QueryBuilder = struct {
    allocator: std.mem.Allocator,
    table: ?[]const u8 = null,
    where_clause: ?[]const u8 = null,
    limit: ?usize = null,
    offset: ?usize = null,

    pub fn init(allocator: std.mem.Allocator) QueryBuilder {
        return .{ .allocator = allocator };
    }

    pub fn from(self: QueryBuilder, table_name: []const u8) QueryBuilder {
        var result = self;
        result.table = table_name;
        return result;
    }

    pub fn where(self: QueryBuilder, clause: []const u8) QueryBuilder {
        var result = self;
        result.where_clause = clause;
        return result;
    }

    pub fn limitTo(self: QueryBuilder, n: usize) QueryBuilder {
        var result = self;
        result.limit = n;
        return result;
    }

    pub fn offsetBy(self: QueryBuilder, n: usize) QueryBuilder {
        var result = self;
        result.offset = n;
        return result;
    }

    pub fn build(self: QueryBuilder) ![]const u8 {
        var list = std.ArrayList(u8){};
        errdefer list.deinit(self.allocator);

        try list.appendSlice(self.allocator, "SELECT * FROM ");
        try list.appendSlice(self.allocator, self.table orelse "unknown");

        if (self.where_clause) |clause| {
            try list.appendSlice(self.allocator, " WHERE ");
            try list.appendSlice(self.allocator, clause);
        }

        if (self.limit) |lim| {
            const limit_str = try std.fmt.allocPrint(self.allocator, " LIMIT {}", .{lim});
            defer self.allocator.free(limit_str);
            try list.appendSlice(self.allocator, limit_str);
        }

        if (self.offset) |off| {
            const offset_str = try std.fmt.allocPrint(self.allocator, " OFFSET {}", .{off});
            defer self.allocator.free(offset_str);
            try list.appendSlice(self.allocator, offset_str);
        }

        return list.toOwnedSlice(self.allocator);
    }
};

test "builder pattern" {
    const allocator = std.testing.allocator;

    const query = try QueryBuilder.init(allocator)
        .from("users")
        .where("age > 21")
        .limitTo(10)
        .offsetBy(20)
        .build();
    defer allocator.free(query);

    try std.testing.expect(std.mem.indexOf(u8, query, "users") != null);
    try std.testing.expect(std.mem.indexOf(u8, query, "LIMIT 10") != null);
}
```

### Validation in Configuration

Validate configuration at construction:

```zig
const ServerConfig = struct {
    port: u16,
    max_connections: u32 = 100,
    thread_pool_size: u32 = 4,

    pub fn validate(self: ServerConfig) !void {
        if (self.port < 1024) {
            return error.PrivilegedPort;
        }
        if (self.max_connections == 0) {
            return error.InvalidMaxConnections;
        }
        if (self.thread_pool_size == 0 or self.thread_pool_size > 1000) {
            return error.InvalidThreadPoolSize;
        }
    }
};

pub fn startServer(config: ServerConfig) !void {
    try config.validate();
    std.debug.print("Starting server on port {}\n", .{config.port});
}

test "configuration validation" {
    // Valid config
    try startServer(.{ .port = 8080 });

    // Invalid configs
    try std.testing.expectError(error.PrivilegedPort, startServer(.{ .port = 80 }));
    try std.testing.expectError(
        error.InvalidMaxConnections,
        startServer(.{ .port = 8080, .max_connections = 0 }),
    );
}
```

### Nested Configuration

Handle complex configuration hierarchies:

```zig
const DatabaseConfig = struct {
    host: []const u8 = "localhost",
    port: u16 = 5432,
    username: []const u8,
    password: []const u8,
};

const CacheConfig = struct {
    enabled: bool = true,
    ttl_seconds: u32 = 300,
    max_size_mb: u32 = 100,
};

const AppConfig = struct {
    database: DatabaseConfig,
    cache: CacheConfig = .{},
    log_level: enum { debug, info, warn, err } = .info,
};

pub fn initializeApp(config: AppConfig) !void {
    std.debug.print("DB: {s}@{s}:{}\n", .{
        config.database.username,
        config.database.host,
        config.database.port,
    });
    std.debug.print("Cache: {}, TTL: {}s\n", .{
        config.cache.enabled,
        config.cache.ttl_seconds,
    });
    std.debug.print("Log level: {s}\n", .{@tagName(config.log_level)});
}

test "nested configuration" {
    try initializeApp(.{
        .database = .{
            .username = "admin",
            .password = "secret",
        },
    });

    try initializeApp(.{
        .database = .{
            .host = "db.example.com",
            .username = "user",
            .password = "pass",
        },
        .cache = .{
            .enabled = false,
        },
        .log_level = .debug,
    });
}
```

### Compile-Time Configuration

Use comptime for zero-cost configuration:

```zig
pub fn Logger(comptime config: struct {
    level: enum { debug, info, warn, err } = .info,
    with_timestamp: bool = true,
    with_color: bool = false,
}) type {
    return struct {
        const Self = @This();

        pub fn log(comptime level: @TypeOf(config.level), message: []const u8) void {
            // Compile-time check - no runtime overhead
            const level_value = @intFromEnum(level);
            const config_level_value = @intFromEnum(config.level);

            if (level_value < config_level_value) {
                return; // Log filtered out at compile time
            }

            if (config.with_timestamp) {
                std.debug.print("[timestamp] ", .{});
            }

            if (config.with_color) {
                std.debug.print("\x1b[32m", .{}); // Green color
            }

            std.debug.print("[{s}] {s}", .{ @tagName(level), message });

            if (config.with_color) {
                std.debug.print("\x1b[0m", .{}); // Reset color
            }

            std.debug.print("\n", .{});
        }
    };
}

test "compile-time configuration" {
    const DebugLogger = Logger(.{ .level = .debug, .with_timestamp = false });
    const ProdLogger = Logger(.{ .level = .warn, .with_color = true });

    DebugLogger.log(.debug, "This appears");
    DebugLogger.log(.info, "This also appears");

    ProdLogger.log(.debug, "This is filtered out at compile time");
    ProdLogger.log(.err, "This appears");
}
```

### Mutually Exclusive Options

Enforce constraints at the type level:

```zig
const OutputFormat = union(enum) {
    file: struct {
        path: []const u8,
        append: bool = false,
    },
    stdout: void,
    stderr: void,
};

pub fn writeOutput(format: OutputFormat, data: []const u8) !void {
    switch (format) {
        .file => |file_config| {
            std.debug.print("Writing to file: {s} (append: {})\n", .{
                file_config.path,
                file_config.append,
            });
            std.debug.print("Data: {s}\n", .{data});
        },
        .stdout => {
            std.debug.print("Writing to stdout: {s}\n", .{data});
        },
        .stderr => {
            std.debug.print("Writing to stderr: {s}\n", .{data});
        },
    }
}

test "mutually exclusive options" {
    try writeOutput(.{ .file = .{ .path = "/tmp/out.txt" } }, "Hello");
    try writeOutput(.stdout, "World");
    try writeOutput(.stderr, "Error!");
}
```

### Best Practices

**Struct Configuration:**
```zig
// Good: Clear parameter names, self-documenting
try connect(.{ .host = "example.com", .port = 443, .use_ssl = true });

// Bad: Positional parameters are unclear
// try connect("example.com", 443, true); // What does 'true' mean?
```

**Default Values:**
- Provide sensible defaults for optional parameters
- Make required parameters explicit (no default value)
- Document what defaults mean

**Validation:**
```zig
const Config = struct {
    value: u32,

    pub fn init(value: u32) !Config {
        if (value > 100) return error.ValueTooLarge;
        return .{ .value = value };
    }
};

// Use init for validation
const config = try Config.init(50);
```

**Naming:**
- Use clear, descriptive struct names (`ConnectionConfig`, not `Options`)
- Use descriptive field names (`timeout_ms`, not just `timeout`)
- Follow naming conventions from `std` library

### Related Functions

- Struct initialization syntax `.{}`
- Default field values in struct definitions
- `@typeInfo()` for struct reflection
- `@tagName()` for enum to string
- Tagged unions for mutually exclusive options
- Comptime struct parameters for zero-cost abstractions

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_config
/// Connection configuration with defaults
const ConnectionConfig = struct {
    host: []const u8 = "localhost",
    port: u16 = 8080,
    timeout_ms: u32 = 5000,
    use_ssl: bool = false,
};

/// Connect with configuration
pub fn connect(config: ConnectionConfig) !void {
    std.debug.print("Connecting to {s}:{d}\n", .{ config.host, config.port });
    std.debug.print("SSL: {}, Timeout: {}ms\n", .{ config.use_ssl, config.timeout_ms });
}
// ANCHOR_END: basic_config

// ANCHOR: required_optional
/// File options with required and optional fields
const FileOptions = struct {
    path: []const u8, // Required
    mode: std.fs.File.OpenMode = .read_only,
    buffer_size: usize = 4096,
    create_if_missing: bool = false,
};

/// Open file with options
pub fn openFile(allocator: std.mem.Allocator, options: FileOptions) !void {
    _ = allocator;
    std.debug.print("Opening {s} in mode {s}\n", .{
        options.path,
        @tagName(options.mode),
    });
    std.debug.print("Buffer: {} bytes, Create: {}\n", .{
        options.buffer_size,
        options.create_if_missing,
    });
}
// ANCHOR_END: required_optional

// ANCHOR: builder_pattern
/// Query builder with fluent interface
const QueryBuilder = struct {
    allocator: std.mem.Allocator,
    table: ?[]const u8 = null,
    where_clause: ?[]const u8 = null,
    limit: ?usize = null,
    offset: ?usize = null,

    pub fn init(allocator: std.mem.Allocator) QueryBuilder {
        return .{ .allocator = allocator };
    }

    pub fn from(self: QueryBuilder, table_name: []const u8) QueryBuilder {
        var result = self;
        result.table = table_name;
        return result;
    }

    pub fn where(self: QueryBuilder, clause: []const u8) QueryBuilder {
        var result = self;
        result.where_clause = clause;
        return result;
    }

    pub fn limitTo(self: QueryBuilder, n: usize) QueryBuilder {
        var result = self;
        result.limit = n;
        return result;
    }

    pub fn offsetBy(self: QueryBuilder, n: usize) QueryBuilder {
        var result = self;
        result.offset = n;
        return result;
    }

    pub fn build(self: QueryBuilder) ![]const u8 {
        var list = std.ArrayList(u8){};
        errdefer list.deinit(self.allocator);

        try list.appendSlice(self.allocator, "SELECT * FROM ");
        try list.appendSlice(self.allocator, self.table orelse "unknown");

        if (self.where_clause) |clause| {
            try list.appendSlice(self.allocator, " WHERE ");
            try list.appendSlice(self.allocator, clause);
        }

        if (self.limit) |lim| {
            const limit_str = try std.fmt.allocPrint(self.allocator, " LIMIT {}", .{lim});
            defer self.allocator.free(limit_str);
            try list.appendSlice(self.allocator, limit_str);
        }

        if (self.offset) |off| {
            const offset_str = try std.fmt.allocPrint(self.allocator, " OFFSET {}", .{off});
            defer self.allocator.free(offset_str);
            try list.appendSlice(self.allocator, offset_str);
        }

        return list.toOwnedSlice(self.allocator);
    }
};
// ANCHOR_END: builder_pattern

/// Server configuration with validation
const ServerConfig = struct {
    port: u16,
    max_connections: u32 = 100,
    thread_pool_size: u32 = 4,

    pub fn validate(self: ServerConfig) !void {
        if (self.port < 1024) {
            return error.PrivilegedPort;
        }
        if (self.max_connections == 0) {
            return error.InvalidMaxConnections;
        }
        if (self.thread_pool_size == 0 or self.thread_pool_size > 1000) {
            return error.InvalidThreadPoolSize;
        }
    }
};

/// Start server with validation
pub fn startServer(config: ServerConfig) !void {
    try config.validate();
    std.debug.print("Starting server on port {}\n", .{config.port});
}

/// Database configuration
const DatabaseConfig = struct {
    host: []const u8 = "localhost",
    port: u16 = 5432,
    username: []const u8,
    password: []const u8,
};

/// Cache configuration
const CacheConfig = struct {
    enabled: bool = true,
    ttl_seconds: u32 = 300,
    max_size_mb: u32 = 100,
};

/// Application configuration with nested configs
const AppConfig = struct {
    database: DatabaseConfig,
    cache: CacheConfig = .{},
    log_level: enum { debug, info, warn, err } = .info,
};

/// Initialize application with nested config
pub fn initializeApp(config: AppConfig) !void {
    std.debug.print("DB: {s}@{s}:{}\n", .{
        config.database.username,
        config.database.host,
        config.database.port,
    });
    std.debug.print("Cache: {}, TTL: {}s\n", .{
        config.cache.enabled,
        config.cache.ttl_seconds,
    });
    std.debug.print("Log level: {s}\n", .{@tagName(config.log_level)});
}

/// Compile-time logger configuration
pub fn Logger(comptime config: struct {
    level: enum { debug, info, warn, err } = .info,
    with_timestamp: bool = true,
    with_color: bool = false,
}) type {
    return struct {
        const Self = @This();

        pub fn log(comptime level: @TypeOf(config.level), message: []const u8) void {
            const level_value = @intFromEnum(level);
            const config_level_value = @intFromEnum(config.level);

            if (level_value < config_level_value) {
                return;
            }

            if (config.with_timestamp) {
                std.debug.print("[timestamp] ", .{});
            }

            if (config.with_color) {
                std.debug.print("\x1b[32m", .{});
            }

            std.debug.print("[{s}] {s}", .{ @tagName(level), message });

            if (config.with_color) {
                std.debug.print("\x1b[0m", .{});
            }

            std.debug.print("\n", .{});
        }
    };
}

/// Output format with mutually exclusive options
const OutputFormat = union(enum) {
    file: struct {
        path: []const u8,
        append: bool = false,
    },
    stdout: void,
    stderr: void,
};

/// Write output to different destinations
pub fn writeOutput(format: OutputFormat, data: []const u8) !void {
    switch (format) {
        .file => |file_config| {
            std.debug.print("Writing to file: {s} (append: {})\n", .{
                file_config.path,
                file_config.append,
            });
            std.debug.print("Data: {s}\n", .{data});
        },
        .stdout => {
            std.debug.print("Writing to stdout: {s}\n", .{data});
        },
        .stderr => {
            std.debug.print("Writing to stderr: {s}\n", .{data});
        },
    }
}

// Tests

test "keyword arguments" {
    // All defaults
    try connect(.{});

    // Override specific fields
    try connect(.{ .host = "example.com", .port = 443, .use_ssl = true });

    // Named parameters make intent clear
    try connect(.{
        .host = "api.example.com",
        .use_ssl = true,
    });
}

test "required and optional parameters" {
    const allocator = std.testing.allocator;

    // Required parameter must be provided
    try openFile(allocator, .{ .path = "/tmp/test.txt" });

    // Can override defaults
    try openFile(allocator, .{
        .path = "/tmp/data.bin",
        .mode = .read_write,
        .buffer_size = 8192,
    });
}

test "builder pattern" {
    const allocator = std.testing.allocator;

    const query = try QueryBuilder.init(allocator)
        .from("users")
        .where("age > 21")
        .limitTo(10)
        .offsetBy(20)
        .build();
    defer allocator.free(query);

    try std.testing.expect(std.mem.indexOf(u8, query, "users") != null);
    try std.testing.expect(std.mem.indexOf(u8, query, "LIMIT 10") != null);
}

test "configuration validation" {
    // Valid config
    try startServer(.{ .port = 8080 });

    // Invalid configs
    try std.testing.expectError(error.PrivilegedPort, startServer(.{ .port = 80 }));
    try std.testing.expectError(
        error.InvalidMaxConnections,
        startServer(.{ .port = 8080, .max_connections = 0 }),
    );
}

test "nested configuration" {
    try initializeApp(.{
        .database = .{
            .username = "admin",
            .password = "secret",
        },
    });

    try initializeApp(.{
        .database = .{
            .host = "db.example.com",
            .username = "user",
            .password = "pass",
        },
        .cache = .{
            .enabled = false,
        },
        .log_level = .debug,
    });
}

test "compile-time configuration" {
    const DebugLogger = Logger(.{ .level = .debug, .with_timestamp = false });
    const ProdLogger = Logger(.{ .level = .warn, .with_color = true });

    DebugLogger.log(.debug, "This appears");
    DebugLogger.log(.info, "This also appears");

    ProdLogger.log(.debug, "This is filtered out at compile time");
    ProdLogger.log(.err, "This appears");
}

test "mutually exclusive options" {
    try writeOutput(.{ .file = .{ .path = "/tmp/out.txt" } }, "Hello");
    try writeOutput(.stdout, "World");
    try writeOutput(.stderr, "Error!");
}

test "default values" {
    const config: ConnectionConfig = .{};
    try std.testing.expectEqualStrings("localhost", config.host);
    try std.testing.expectEqual(@as(u16, 8080), config.port);
    try std.testing.expectEqual(@as(u32, 5000), config.timeout_ms);
    try std.testing.expectEqual(false, config.use_ssl);
}

test "partial override" {
    const config: ConnectionConfig = .{ .port = 9000 };
    try std.testing.expectEqualStrings("localhost", config.host);
    try std.testing.expectEqual(@as(u16, 9000), config.port);
}

test "query builder no where clause" {
    const allocator = std.testing.allocator;

    const query = try QueryBuilder.init(allocator)
        .from("products")
        .build();
    defer allocator.free(query);

    try std.testing.expectEqualStrings("SELECT * FROM products", query);
}

test "query builder with limit only" {
    const allocator = std.testing.allocator;

    const query = try QueryBuilder.init(allocator)
        .from("items")
        .limitTo(5)
        .build();
    defer allocator.free(query);

    try std.testing.expect(std.mem.indexOf(u8, query, "LIMIT 5") != null);
}

test "validation passes with good values" {
    const config = ServerConfig{
        .port = 8080,
        .max_connections = 50,
        .thread_pool_size = 8,
    };
    try config.validate();
}

test "validation fails with thread pool too large" {
    const config = ServerConfig{
        .port = 8080,
        .thread_pool_size = 2000,
    };
    try std.testing.expectError(error.InvalidThreadPoolSize, config.validate());
}

test "nested config with all defaults" {
    try initializeApp(.{
        .database = .{
            .username = "user",
            .password = "pass",
        },
    });
}

test "output format file with append" {
    try writeOutput(.{
        .file = .{
            .path = "/tmp/log.txt",
            .append = true,
        },
    }, "Log entry");
}
```

---

## Recipe 7.3: Attaching Informational Metadata to Function Arguments {#recipe-7-3}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, functions, http, json, memory, networking, parsing, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_3.zig`

### Problem

You need to attach metadata or documentation to function arguments for validation, serialization, or documentation purposes.

### Solution

Use struct fields with compile-time reflection to attach metadata:

```zig
/// Parameter information metadata
const ParamInfo = struct {
    name: []const u8,
    description: []const u8,
    min_value: ?i32 = null,
    max_value: ?i32 = null,
};

/// Create user with metadata
pub fn createUser(params: struct {
    username: []const u8,
    age: i32,
    email: []const u8,

    pub const metadata = .{
        .username = ParamInfo{
            .name = "username",
            .description = "User's login name",
        },
        .age = ParamInfo{
            .name = "age",
            .description = "User's age in years",
            .min_value = 0,
            .max_value = 150,
        },
        .email = ParamInfo{
            .name = "email",
            .description = "User's email address",
        },
    };
}) !void {
    // Validate age using metadata
    if (params.age < @TypeOf(params).metadata.age.min_value.? or
        params.age > @TypeOf(params).metadata.age.max_value.?)
    {
        return error.InvalidAge;
    }

    std.debug.print("Creating user: {s}, age {}, email {s}\n", .{
        params.username,
        params.age,
        params.email,
    });
}
```

### Discussion

### Validation with Metadata

Automatically validate parameters using metadata:

```zig
/// Generic validator using metadata
const Validator = struct {
    pub fn validate(comptime T: type, value: T) !void {
        const type_info = @typeInfo(T);

        switch (type_info) {
            .@"struct" => |struct_info| {
                if (@hasDecl(T, "metadata")) {
                    const metadata = T.metadata;

                    inline for (struct_info.fields) |field| {
                        const field_value = @field(value, field.name);

                        if (@hasField(@TypeOf(metadata), field.name)) {
                            const field_meta = @field(metadata, field.name);

                            if (@hasField(@TypeOf(field_meta), "min_value")) {
                                const min = field_meta.min_value;
                                if (field_value < min) {
                                    return error.ValueTooSmall;
                                }
                            }

                            if (@hasField(@TypeOf(field_meta), "max_value")) {
                                const max = field_meta.max_value;
                                if (field_value > max) {
                                    return error.ValueTooLarge;
                                }
                            }
                        }
                    }
                }
            },
            else => {},
        }
    }
};
```

### Documentation Generation

Extract documentation from metadata:

```zig
pub fn generateDocs(comptime T: type) []const u8 {
    const type_info = @typeInfo(T);

    if (type_info != .@"struct") {
        return "Not a struct";
    }

    if (!@hasDecl(T, "metadata")) {
        return "No metadata available";
    }

    comptime var doc: []const u8 = "Parameters:\n";
    const metadata = T.metadata;

    inline for (type_info.@"struct".fields) |field| {
        if (@hasField(@TypeOf(metadata), field.name)) {
            const field_meta = @field(metadata, field.name);

            doc = doc ++ "  " ++ field.name ++ ": " ++ @typeName(field.type);

            if (@hasField(@TypeOf(field_meta), "description")) {
                doc = doc ++ " - " ++ field_meta.description;
            }

            doc = doc ++ "\n";
        }
    }

    return doc;
}

const ConfigParams = struct {
    timeout: u32,
    retries: u8,

    pub const metadata = .{
        .timeout = .{ .description = "Timeout in milliseconds" },
        .retries = .{ .description = "Number of retry attempts" },
    };
};

test "documentation generation" {
    const docs = comptime generateDocs(ConfigParams);
    try std.testing.expect(std.mem.indexOf(u8, docs, "timeout") != null);
    try std.testing.expect(std.mem.indexOf(u8, docs, "milliseconds") != null);
}
```

### Type Constraints

Enforce type constraints at compile time:

```zig
/// User parameters with metadata
const UserParams = struct {
    age: i32,
    score: f32,

    pub const metadata = .{
        .age = .{ .min_value = 0, .max_value = 150 },
        .score = .{ .min_value = 0.0, .max_value = 100.0 },
    };
};

/// Generate documentation from metadata
pub fn generateDocs(comptime T: type) []const u8 {
    const type_info = @typeInfo(T);

    if (type_info != .@"struct") {
        return "Not a struct";
    }

    if (!@hasDecl(T, "metadata")) {
        return "No metadata available";
    }

    comptime var doc: []const u8 = "Parameters:\n";
    const metadata = T.metadata;

    inline for (type_info.@"struct".fields) |field| {
        if (@hasField(@TypeOf(metadata), field.name)) {
            const field_meta = @field(metadata, field.name);

            doc = doc ++ "  " ++ field.name ++ ": " ++ @typeName(field.type);

            if (@hasField(@TypeOf(field_meta), "description")) {
                doc = doc ++ " - " ++ field_meta.description;
            }

            doc = doc ++ "\n";
        }
    }

    return doc;
}

/// Config parameters with metadata
const ConfigParams = struct {
    timeout: u32,
    retries: u8,

    pub const metadata = .{
        .timeout = .{ .description = "Timeout in milliseconds" },
        .retries = .{ .description = "Number of retry attempts" },
    };
};

/// Constrained type with validation
pub fn Constrained(comptime T: type, comptime constraints: anytype) type {
    return struct {
        value: T,

        pub fn init(val: T) !@This() {
            if (@hasField(@TypeOf(constraints), "min")) {
                if (val < constraints.min) {
                    return error.BelowMinimum;
                }
            }

            if (@hasField(@TypeOf(constraints), "max")) {
                if (val > constraints.max) {
                    return error.AboveMaximum;
                }
            }

            return .{ .value = val };
        }

        pub fn get(self: @This()) T {
            return self.value;
        }
    };
}

const Age = Constrained(u8, .{ .min = 0, .max = 150 });
const Percentage = Constrained(f32, .{ .min = 0.0, .max = 100.0 });
```

### Tagged Parameters

Use enums to tag parameter purposes:

```zig
const ParamTag = enum {
    required,
    optional,
    deprecated,
};

pub fn ApiFunction(comptime params: anytype) type {
    return struct {
        pub fn call(args: anytype) !void {
            const ArgsType = @TypeOf(args);
            const args_info = @typeInfo(ArgsType);

            // Check required parameters
            inline for (@typeInfo(@TypeOf(params)).@"struct".fields) |param_field| {
                const param_info = @field(params, param_field.name);

                if (param_info.tag == .required) {
                    if (!@hasField(ArgsType, param_field.name)) {
                        @compileError("Missing required parameter: " ++ param_field.name);
                    }
                }
            }

            // Warn about deprecated parameters
            if (args_info == .@"struct") {
                inline for (args_info.@"struct".fields) |arg_field| {
                    inline for (@typeInfo(@TypeOf(params)).@"struct".fields) |param_field| {
                        if (std.mem.eql(u8, arg_field.name, param_field.name)) {
                            const param_info = @field(params, param_field.name);
                            if (param_info.tag == .deprecated) {
                                @compileLog("Warning: parameter '" ++ param_field.name ++ "' is deprecated");
                            }
                        }
                    }
                }
            }

            std.debug.print("API call successful\n", .{});
        }
    };
}

const MyApi = ApiFunction(.{
    .username = .{ .tag = .required, .type = []const u8 },
    .email = .{ .tag = .required, .type = []const u8 },
    .phone = .{ .tag = .optional, .type = []const u8 },
});

test "tagged parameters" {
    try MyApi.call(.{
        .username = "alice",
        .email = "alice@example.com",
    });

    try MyApi.call(.{
        .username = "bob",
        .email = "bob@example.com",
        .phone = "555-1234",
    });
}
```

### Serialization Metadata

Add serialization hints to struct fields:

```zig
const SerializeInfo = struct {
    json_name: []const u8,
    omit_empty: bool = false,
    format: enum { default, timestamp, base64 } = .default,
};

const User = struct {
    id: u64,
    username: []const u8,
    created_at: i64,
    avatar_data: ?[]const u8,

    pub const serialize_info = .{
        .id = SerializeInfo{ .json_name = "user_id" },
        .username = SerializeInfo{ .json_name = "name" },
        .created_at = SerializeInfo{
            .json_name = "createdAt",
            .format = .timestamp,
        },
        .avatar_data = SerializeInfo{
            .json_name = "avatar",
            .omit_empty = true,
            .format = .base64,
        },
    };

    pub fn toJson(self: User, allocator: std.mem.Allocator) ![]u8 {
        var list = std.ArrayList(u8){};
        errdefer list.deinit(allocator);

        try list.appendSlice(allocator, "{");

        const type_info = @typeInfo(@This());
        inline for (type_info.@"struct".fields, 0..) |field, i| {
            if (i > 0) try list.appendSlice(allocator, ",");

            const serialize_meta = @field(serialize_info, field.name);
            const field_value = @field(self, field.name);

            try list.appendSlice(allocator, "\"");
            try list.appendSlice(allocator, serialize_meta.json_name);
            try list.appendSlice(allocator, "\":");

            const value_str = try std.fmt.allocPrint(allocator, "{any}", .{field_value});
            defer allocator.free(value_str);
            try list.appendSlice(allocator, value_str);
        }

        try list.appendSlice(allocator, "}");
        return list.toOwnedSlice(allocator);
    }
};

test "serialization metadata" {
    const allocator = std.testing.allocator;

    const user = User{
        .id = 42,
        .username = "alice",
        .created_at = 1234567890,
        .avatar_data = null,
    };

    const json = try user.toJson(allocator);
    defer allocator.free(json);

    try std.testing.expect(std.mem.indexOf(u8, json, "user_id") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "name") != null);
}
```

### Runtime Parameter Inspection

Inspect parameters at runtime:

```zig
pub fn inspectParams(comptime T: type) void {
    const type_info = @typeInfo(T);

    if (type_info != .@"struct") {
        std.debug.print("Not a struct\n", .{});
        return;
    }

    std.debug.print("Function parameters for {s}:\n", .{@typeName(T)});

    inline for (type_info.@"struct".fields) |field| {
        std.debug.print("  {s}: {s}", .{ field.name, @typeName(field.type) });

        if (@hasDecl(T, "metadata")) {
            const metadata = T.metadata;
            if (@hasField(@TypeOf(metadata), field.name)) {
                const field_meta = @field(metadata, field.name);
                if (@hasField(@TypeOf(field_meta), "description")) {
                    std.debug.print(" - {s}", .{field_meta.description});
                }
            }
        }

        std.debug.print("\n", .{});
    }
}

const ApiParams = struct {
    endpoint: []const u8,
    method: []const u8,
    timeout: u32,

    pub const metadata = .{
        .endpoint = .{ .description = "API endpoint URL" },
        .method = .{ .description = "HTTP method (GET, POST, etc.)" },
        .timeout = .{ .description = "Request timeout in milliseconds" },
    };
};

test "runtime inspection" {
    inspectParams(ApiParams);
}
```

### Best Practices

**Metadata Structure:**
```zig
// Good: Clear, reusable metadata type
const ParamMeta = struct {
    description: []const u8,
    min: ?i32 = null,
    max: ?i32 = null,
    deprecated: bool = false,
};

// Attach as pub const
pub const metadata = .{
    .field = ParamMeta{ .description = "Field description" },
};
```

**Compile-Time Validation:**
- Use `@compileError` for invalid configurations
- Validate metadata structure at comptime
- Provide clear error messages

**Documentation:**
- Use metadata for automatic documentation generation
- Include usage examples in metadata
- Document constraints and validation rules

**Performance:**
- Metadata is zero-cost at runtime
- Validation can be compile-time when possible
- Use comptime functions to process metadata

### Related Functions

- `@hasDecl()` - Check if type has declaration
- `@hasField()` - Check if struct has field
- `@typeInfo()` - Get type reflection information
- `@typeName()` - Get string name of type
- `@field()` - Access struct field by name
- `@compileError()` - Emit compile-time error
- `@compileLog()` - Emit compile-time warning

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_metadata
/// Parameter information metadata
const ParamInfo = struct {
    name: []const u8,
    description: []const u8,
    min_value: ?i32 = null,
    max_value: ?i32 = null,
};

/// Create user with metadata
pub fn createUser(params: struct {
    username: []const u8,
    age: i32,
    email: []const u8,

    pub const metadata = .{
        .username = ParamInfo{
            .name = "username",
            .description = "User's login name",
        },
        .age = ParamInfo{
            .name = "age",
            .description = "User's age in years",
            .min_value = 0,
            .max_value = 150,
        },
        .email = ParamInfo{
            .name = "email",
            .description = "User's email address",
        },
    };
}) !void {
    // Validate age using metadata
    if (params.age < @TypeOf(params).metadata.age.min_value.? or
        params.age > @TypeOf(params).metadata.age.max_value.?)
    {
        return error.InvalidAge;
    }

    std.debug.print("Creating user: {s}, age {}, email {s}\n", .{
        params.username,
        params.age,
        params.email,
    });
}
// ANCHOR_END: basic_metadata

// ANCHOR: generic_validator
/// Generic validator using metadata
const Validator = struct {
    pub fn validate(comptime T: type, value: T) !void {
        const type_info = @typeInfo(T);

        switch (type_info) {
            .@"struct" => |struct_info| {
                if (@hasDecl(T, "metadata")) {
                    const metadata = T.metadata;

                    inline for (struct_info.fields) |field| {
                        const field_value = @field(value, field.name);

                        if (@hasField(@TypeOf(metadata), field.name)) {
                            const field_meta = @field(metadata, field.name);

                            if (@hasField(@TypeOf(field_meta), "min_value")) {
                                const min = field_meta.min_value;
                                if (field_value < min) {
                                    return error.ValueTooSmall;
                                }
                            }

                            if (@hasField(@TypeOf(field_meta), "max_value")) {
                                const max = field_meta.max_value;
                                if (field_value > max) {
                                    return error.ValueTooLarge;
                                }
                            }
                        }
                    }
                }
            },
            else => {},
        }
    }
};
// ANCHOR_END: generic_validator

// ANCHOR: constrained_types
/// User parameters with metadata
const UserParams = struct {
    age: i32,
    score: f32,

    pub const metadata = .{
        .age = .{ .min_value = 0, .max_value = 150 },
        .score = .{ .min_value = 0.0, .max_value = 100.0 },
    };
};

/// Generate documentation from metadata
pub fn generateDocs(comptime T: type) []const u8 {
    const type_info = @typeInfo(T);

    if (type_info != .@"struct") {
        return "Not a struct";
    }

    if (!@hasDecl(T, "metadata")) {
        return "No metadata available";
    }

    comptime var doc: []const u8 = "Parameters:\n";
    const metadata = T.metadata;

    inline for (type_info.@"struct".fields) |field| {
        if (@hasField(@TypeOf(metadata), field.name)) {
            const field_meta = @field(metadata, field.name);

            doc = doc ++ "  " ++ field.name ++ ": " ++ @typeName(field.type);

            if (@hasField(@TypeOf(field_meta), "description")) {
                doc = doc ++ " - " ++ field_meta.description;
            }

            doc = doc ++ "\n";
        }
    }

    return doc;
}

/// Config parameters with metadata
const ConfigParams = struct {
    timeout: u32,
    retries: u8,

    pub const metadata = .{
        .timeout = .{ .description = "Timeout in milliseconds" },
        .retries = .{ .description = "Number of retry attempts" },
    };
};

/// Constrained type with validation
pub fn Constrained(comptime T: type, comptime constraints: anytype) type {
    return struct {
        value: T,

        pub fn init(val: T) !@This() {
            if (@hasField(@TypeOf(constraints), "min")) {
                if (val < constraints.min) {
                    return error.BelowMinimum;
                }
            }

            if (@hasField(@TypeOf(constraints), "max")) {
                if (val > constraints.max) {
                    return error.AboveMaximum;
                }
            }

            return .{ .value = val };
        }

        pub fn get(self: @This()) T {
            return self.value;
        }
    };
}

const Age = Constrained(u8, .{ .min = 0, .max = 150 });
const Percentage = Constrained(f32, .{ .min = 0.0, .max = 100.0 });
// ANCHOR_END: constrained_types

/// Parameter tag for API functions
const ParamTag = enum {
    required,
    optional,
    deprecated,
};

/// API function with tagged parameters
pub fn ApiFunction(comptime params: anytype) type {
    return struct {
        pub fn call(args: anytype) !void {
            const ArgsType = @TypeOf(args);
            const args_info = @typeInfo(ArgsType);

            // Check required parameters
            inline for (@typeInfo(@TypeOf(params)).@"struct".fields) |param_field| {
                const param_info = @field(params, param_field.name);

                if (param_info.tag == .required) {
                    if (!@hasField(ArgsType, param_field.name)) {
                        @compileError("Missing required parameter: " ++ param_field.name);
                    }
                }
            }

            std.debug.print("API call successful\n", .{});
            _ = args_info;
        }
    };
}

const MyApi = ApiFunction(.{
    .username = .{ .tag = .required, .type = []const u8 },
    .email = .{ .tag = .required, .type = []const u8 },
    .phone = .{ .tag = .optional, .type = []const u8 },
});

/// Serialization metadata
const SerializeInfo = struct {
    json_name: []const u8,
    omit_empty: bool = false,
    format: enum { default, timestamp, base64 } = .default,
};

/// User with serialization metadata
const User = struct {
    id: u64,
    username: []const u8,
    created_at: i64,
    avatar_data: ?[]const u8,

    pub const serialize_info = .{
        .id = SerializeInfo{ .json_name = "user_id" },
        .username = SerializeInfo{ .json_name = "name" },
        .created_at = SerializeInfo{
            .json_name = "createdAt",
            .format = .timestamp,
        },
        .avatar_data = SerializeInfo{
            .json_name = "avatar",
            .omit_empty = true,
            .format = .base64,
        },
    };

    pub fn toJson(self: User, allocator: std.mem.Allocator) ![]u8 {
        var list = std.ArrayList(u8){};
        errdefer list.deinit(allocator);

        try list.appendSlice(allocator, "{");

        const type_info = @typeInfo(@This());
        inline for (type_info.@"struct".fields, 0..) |field, i| {
            if (i > 0) try list.appendSlice(allocator, ",");

            const serialize_meta = @field(serialize_info, field.name);
            const field_value = @field(self, field.name);

            try list.appendSlice(allocator, "\"");
            try list.appendSlice(allocator, serialize_meta.json_name);
            try list.appendSlice(allocator, "\":");

            const value_str = try std.fmt.allocPrint(allocator, "{any}", .{field_value});
            defer allocator.free(value_str);
            try list.appendSlice(allocator, value_str);
        }

        try list.appendSlice(allocator, "}");
        return list.toOwnedSlice(allocator);
    }
};

/// Inspect parameters at runtime
pub fn inspectParams(comptime T: type) void {
    const type_info = @typeInfo(T);

    if (type_info != .@"struct") {
        std.debug.print("Not a struct\n", .{});
        return;
    }

    std.debug.print("Function parameters for {s}:\n", .{@typeName(T)});

    inline for (type_info.@"struct".fields) |field| {
        std.debug.print("  {s}: {s}", .{ field.name, @typeName(field.type) });

        if (@hasDecl(T, "metadata")) {
            const metadata = T.metadata;
            if (@hasField(@TypeOf(metadata), field.name)) {
                const field_meta = @field(metadata, field.name);
                if (@hasField(@TypeOf(field_meta), "description")) {
                    std.debug.print(" - {s}", .{field_meta.description});
                }
            }
        }

        std.debug.print("\n", .{});
    }
}

/// API parameters with metadata
const ApiParams = struct {
    endpoint: []const u8,
    method: []const u8,
    timeout: u32,

    pub const metadata = .{
        .endpoint = .{ .description = "API endpoint URL" },
        .method = .{ .description = "HTTP method (GET, POST, etc.)" },
        .timeout = .{ .description = "Request timeout in milliseconds" },
    };
};

// Tests

test "function with metadata" {
    try createUser(.{
        .username = "alice",
        .age = 30,
        .email = "alice@example.com",
    });

    try std.testing.expectError(
        error.InvalidAge,
        createUser(.{ .username = "bob", .age = 200, .email = "bob@example.com" }),
    );
}

test "automatic validation" {
    const valid = UserParams{ .age = 25, .score = 85.5 };
    try Validator.validate(UserParams, valid);

    const invalid_age = UserParams{ .age = 200, .score = 50.0 };
    try std.testing.expectError(error.ValueTooLarge, Validator.validate(UserParams, invalid_age));
}

test "documentation generation" {
    const docs = comptime generateDocs(ConfigParams);
    try std.testing.expect(std.mem.indexOf(u8, docs, "timeout") != null);
    try std.testing.expect(std.mem.indexOf(u8, docs, "milliseconds") != null);
}

test "type constraints" {
    const age = try Age.init(25);
    try std.testing.expectEqual(@as(u8, 25), age.get());

    try std.testing.expectError(error.AboveMaximum, Age.init(200));

    const pct = try Percentage.init(75.5);
    try std.testing.expectEqual(@as(f32, 75.5), pct.get());
}

test "tagged parameters" {
    try MyApi.call(.{
        .username = "alice",
        .email = "alice@example.com",
    });

    try MyApi.call(.{
        .username = "bob",
        .email = "bob@example.com",
        .phone = "555-1234",
    });
}

test "serialization metadata" {
    const allocator = std.testing.allocator;

    const user = User{
        .id = 42,
        .username = "alice",
        .created_at = 1234567890,
        .avatar_data = null,
    };

    const json = try user.toJson(allocator);
    defer allocator.free(json);

    try std.testing.expect(std.mem.indexOf(u8, json, "user_id") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "name") != null);
}

test "runtime inspection" {
    inspectParams(ApiParams);
}

test "validation with min value" {
    const invalid_small = UserParams{ .age = -10, .score = 50.0 };
    try std.testing.expectError(error.ValueTooSmall, Validator.validate(UserParams, invalid_small));
}

test "validation with max score" {
    const invalid_score = UserParams{ .age = 25, .score = 150.0 };
    try std.testing.expectError(error.ValueTooLarge, Validator.validate(UserParams, invalid_score));
}

test "constrained type at minimum" {
    const age = try Age.init(0);
    try std.testing.expectEqual(@as(u8, 0), age.get());
}

test "constrained type at maximum" {
    const age = try Age.init(150);
    try std.testing.expectEqual(@as(u8, 150), age.get());
}

test "constrained type below minimum" {
    // Age is u8, so can't test negative, but test 0 boundary
    const age = try Age.init(0);
    try std.testing.expectEqual(@as(u8, 0), age.get());
}

test "percentage at boundaries" {
    const min = try Percentage.init(0.0);
    try std.testing.expectEqual(@as(f32, 0.0), min.get());

    const max = try Percentage.init(100.0);
    try std.testing.expectEqual(@as(f32, 100.0), max.get());
}

test "percentage out of bounds" {
    try std.testing.expectError(error.AboveMaximum, Percentage.init(150.0));
    try std.testing.expectError(error.BelowMinimum, Percentage.init(-10.0));
}

test "metadata field access" {
    // Access metadata through ConfigParams
    const meta = ConfigParams.metadata;
    try std.testing.expect(std.mem.indexOf(u8, meta.timeout.description, "milliseconds") != null);
    try std.testing.expectEqualStrings("Number of retry attempts", meta.retries.description);
}
```

---

## Recipe 7.4: Returning Multiple Values from a Function {#recipe-7-4}

**Tags:** allocators, comptime, error-handling, functions, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_4.zig`

### Problem

You need to return multiple values from a function without creating a complex data structure.

### Solution

Use anonymous structs (tuples) for simple multiple return values:

```zig
// Anchor 'tuple_return' not found in ../../../code/03-advanced/07-functions/recipe_7_4.zig
```

### Discussion

### Named Return Types

Use named structs for clarity and reusability:

```zig
const DivResult = struct {
    quotient: i32,
    remainder: i32,
    is_exact: bool,
};

pub fn divideWithInfo(a: i32, b: i32) DivResult {
    const quot = @divTrunc(a, b);
    const rem = @mod(a, b);

    return .{
        .quotient = quot,
        .remainder = rem,
        .is_exact = rem == 0,
    };
}

test "named return type" {
    const result = divideWithInfo(20, 4);
    try std.testing.expectEqual(@as(i32, 5), result.quotient);
    try std.testing.expectEqual(@as(i32, 0), result.remainder);
    try std.testing.expect(result.is_exact);
}
```

### Error Union with Multiple Values

Combine error handling with multiple return values:

```zig
const ParseResult = struct {
    value: i32,
    remaining: []const u8,
};

pub fn parseInt(input: []const u8) !ParseResult {
    if (input.len == 0) {
        return error.EmptyInput;
    }

    var i: usize = 0;
    var value: i32 = 0;
    var sign: i32 = 1;

    // Handle sign
    if (input[0] == '-') {
        sign = -1;
        i = 1;
    } else if (input[0] == '+') {
        i = 1;
    }

    // Parse digits
    if (i >= input.len or !std.ascii.isDigit(input[i])) {
        return error.InvalidFormat;
    }

    while (i < input.len and std.ascii.isDigit(input[i])) : (i += 1) {
        value = value * 10 + @as(i32, input[i] - '0');
    }

    return .{
        .value = value * sign,
        .remaining = input[i..],
    };
}

test "error union with multiple values" {
    const result = try parseInt("123abc");
    try std.testing.expectEqual(@as(i32, 123), result.value);
    try std.testing.expectEqualStrings("abc", result.remaining);

    try std.testing.expectError(error.EmptyInput, parseInt(""));
    try std.testing.expectError(error.InvalidFormat, parseInt("abc"));
}
```

### Optional Multiple Values

Return optional results:

```zig
const SearchResult = struct {
    index: usize,
    value: u8,
};

pub fn findByte(haystack: []const u8, needle: u8) ?SearchResult {
    for (haystack, 0..) |byte, i| {
        if (byte == needle) {
            return .{ .index = i, .value = byte };
        }
    }
    return null;
}

test "optional multiple values" {
    const result = findByte("hello", 'l');
    try std.testing.expect(result != null);
    try std.testing.expectEqual(@as(usize, 2), result.?.index);

    const not_found = findByte("hello", 'x');
    try std.testing.expect(not_found == null);
}
```

### Tuple-Style Returns

Use tuples for simple, unnamed returns:

```zig
pub fn minMax(numbers: []const i32) struct { min: i32, max: i32 } {
    var min_val = numbers[0];
    var max_val = numbers[0];

    for (numbers[1..]) |n| {
        if (n < min_val) min_val = n;
        if (n > max_val) max_val = n;
    }

    return .{ .min = min_val, .max = max_val };
}

test "min max tuple" {
    const numbers = [_]i32{ 5, 2, 8, 1, 9, 3 };
    const result = minMax(&numbers);

    try std.testing.expectEqual(@as(i32, 1), result.min);
    try std.testing.expectEqual(@as(i32, 9), result.max);
}
```

### Multi-Step Computation Results

Return intermediate and final results:

```zig
const Statistics = struct {
    sum: i64,
    count: usize,
    mean: f64,
    min: i32,
    max: i32,
};

pub fn calculateStats(numbers: []const i32) Statistics {
    var sum: i64 = 0;
    var min_val = numbers[0];
    var max_val = numbers[0];

    for (numbers) |n| {
        sum += n;
        if (n < min_val) min_val = n;
        if (n > max_val) max_val = n;
    }

    const mean = @as(f64, @floatFromInt(sum)) / @as(f64, @floatFromInt(numbers.len));

    return .{
        .sum = sum,
        .count = numbers.len,
        .mean = mean,
        .min = min_val,
        .max = max_val,
    };
}

test "calculate statistics" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    const stats = calculateStats(&numbers);

    try std.testing.expectEqual(@as(i64, 15), stats.sum);
    try std.testing.expectEqual(@as(usize, 5), stats.count);
    try std.testing.expectEqual(@as(f64, 3.0), stats.mean);
}
```

### Tagged Union Returns

Return different types of results:

```zig
const ProcessResult = union(enum) {
    success: struct {
        value: i32,
        message: []const u8,
    },
    warning: struct {
        value: i32,
        warning: []const u8,
    },
    failure: []const u8,
};

pub fn processValue(input: i32) ProcessResult {
    if (input < 0) {
        return .{ .failure = "Negative value not allowed" };
    } else if (input > 100) {
        return .{ .warning = .{
            .value = 100,
            .warning = "Value clamped to maximum",
        } };
    } else {
        return .{ .success = .{
            .value = input,
            .message = "Processed successfully",
        } };
    }
}

test "tagged union return" {
    const ok = processValue(50);
    try std.testing.expect(ok == .success);
    try std.testing.expectEqual(@as(i32, 50), ok.success.value);

    const warned = processValue(150);
    try std.testing.expect(warned == .warning);
    try std.testing.expectEqual(@as(i32, 100), warned.warning.value);

    const err = processValue(-10);
    try std.testing.expect(err == .failure);
}
```

### Allocated Return Values

Return values that own their memory:

```zig
const SplitResult = struct {
    before: []const u8,
    after: []const u8,
    allocator: std.mem.Allocator,

    pub fn deinit(self: SplitResult) void {
        self.allocator.free(self.before);
        self.allocator.free(self.after);
    }
};

pub fn splitAndDuplicate(
    allocator: std.mem.Allocator,
    input: []const u8,
    delimiter: u8,
) !SplitResult {
    const index = std.mem.indexOfScalar(u8, input, delimiter) orelse input.len;

    const before = try allocator.dupe(u8, input[0..index]);
    errdefer allocator.free(before);

    const after = if (index < input.len)
        try allocator.dupe(u8, input[index + 1 ..])
    else
        try allocator.alloc(u8, 0);

    return .{
        .before = before,
        .after = after,
        .allocator = allocator,
    };
}

test "allocated return values" {
    const allocator = std.testing.allocator;

    const result = try splitAndDuplicate(allocator, "hello:world", ':');
    defer result.deinit();

    try std.testing.expectEqualStrings("hello", result.before);
    try std.testing.expectEqualStrings("world", result.after);
}
```

### Compile-Time Multiple Returns

Return multiple compile-time values:

```zig
pub fn splitType(comptime T: type) struct { base: type, is_pointer: bool } {
    const info = @typeInfo(T);
    return switch (info) {
        .pointer => |ptr| .{
            .base = ptr.child,
            .is_pointer = true,
        },
        else => .{
            .base = T,
            .is_pointer = false,
        },
    };
}

test "compile-time multiple returns" {
    const result1 = comptime splitType(*i32);
    try std.testing.expect(result1.is_pointer);
    try std.testing.expect(result1.base == i32);

    const result2 = comptime splitType(i32);
    try std.testing.expect(!result2.is_pointer);
    try std.testing.expect(result2.base == i32);
}
```

### Builder Pattern for Complex Returns

Use method chaining to build complex results:

```zig
const QueryResult = struct {
    rows: []const []const u8,
    count: usize,
    has_more: bool,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) QueryResult {
        return .{
            .rows = &[_][]const u8{},
            .count = 0,
            .has_more = false,
            .allocator = allocator,
        };
    }

    pub fn withRows(self: QueryResult, rows: []const []const u8) QueryResult {
        var result = self;
        result.rows = rows;
        result.count = rows.len;
        return result;
    }

    pub fn withMoreFlag(self: QueryResult, has_more: bool) QueryResult {
        var result = self;
        result.has_more = has_more;
        return result;
    }
};

test "builder pattern return" {
    const allocator = std.testing.allocator;

    const rows = [_][]const u8{ "row1", "row2", "row3" };
    const result = QueryResult.init(allocator)
        .withRows(&rows)
        .withMoreFlag(true);

    try std.testing.expectEqual(@as(usize, 3), result.count);
    try std.testing.expect(result.has_more);
}
```

### Best Practices

**Return Type Selection:**
```zig
// Simple pairs: use anonymous struct
fn getCoordinates() struct { x: f32, y: f32 }

// Reused type: use named struct
const Point = struct { x: f32, y: f32 };
fn getPoint() Point

// Different result types: use tagged union
const Result = union(enum) { ok: T, err: E };
```

**Destructuring:**
```zig
// Access fields directly
const result = divmod(17, 5);
std.debug.print("{} remainder {}\n", .{ result.quotient, result.remainder });

// Or destructure
const q, const r = .{ result.quotient, result.remainder };
```

**Error Handling:**
- Combine error unions with multiple values naturally
- Use tagged unions for different success/failure paths
- Return optionals when the entire result might be missing

**Memory Management:**
```zig
// Include allocator in return type for cleanup
const Result = struct {
    data: []u8,
    allocator: std.mem.Allocator,

    pub fn deinit(self: Result) void {
        self.allocator.free(self.data);
    }
};
```

### Related Functions

- Struct initialization syntax `.{}`
- Tuple destructuring with `const a, const b = tuple`
- `@typeInfo()` for compile-time type inspection
- Tagged unions for variant returns
- Error unions `!T` for fallible operations
- Optional `?T` for potentially missing values

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_multiple_returns
/// Simple division with quotient and remainder
pub fn divmod(a: i32, b: i32) struct { quotient: i32, remainder: i32 } {
    return .{
        .quotient = @divTrunc(a, b),
        .remainder = @mod(a, b),
    };
}

/// Named return type for division
const DivResult = struct {
    quotient: i32,
    remainder: i32,
    is_exact: bool,
};

pub fn divideWithInfo(a: i32, b: i32) DivResult {
    const quot = @divTrunc(a, b);
    const rem = @mod(a, b);

    return .{
        .quotient = quot,
        .remainder = rem,
        .is_exact = rem == 0,
    };
}
// ANCHOR_END: basic_multiple_returns

// ANCHOR: error_union_returns
/// Parse result with remaining input
const ParseResult = struct {
    value: i32,
    remaining: []const u8,
};

pub fn parseInt(input: []const u8) !ParseResult {
    if (input.len == 0) {
        return error.EmptyInput;
    }

    var i: usize = 0;
    var value: i32 = 0;
    var sign: i32 = 1;

    // Handle sign
    if (input[0] == '-') {
        sign = -1;
        i = 1;
    } else if (input[0] == '+') {
        i = 1;
    }

    // Parse digits
    if (i >= input.len or !std.ascii.isDigit(input[i])) {
        return error.InvalidFormat;
    }

    while (i < input.len and std.ascii.isDigit(input[i])) : (i += 1) {
        value = value * 10 + @as(i32, input[i] - '0');
    }

    return .{
        .value = value * sign,
        .remaining = input[i..],
    };
}
// ANCHOR_END: error_union_returns

// ANCHOR: tagged_union_returns
/// Search result with optional match
const SearchResult = struct {
    index: usize,
    value: u8,
};

pub fn findByte(haystack: []const u8, needle: u8) ?SearchResult {
    for (haystack, 0..) |byte, i| {
        if (byte == needle) {
            return .{ .index = i, .value = byte };
        }
    }
    return null;
}

/// Min and max from slice
pub fn minMax(numbers: []const i32) struct { min: i32, max: i32 } {
    var min_val = numbers[0];
    var max_val = numbers[0];

    for (numbers[1..]) |n| {
        if (n < min_val) min_val = n;
        if (n > max_val) max_val = n;
    }

    return .{ .min = min_val, .max = max_val };
}

/// Statistics calculation
const Statistics = struct {
    sum: i64,
    count: usize,
    mean: f64,
    min: i32,
    max: i32,
};

pub fn calculateStats(numbers: []const i32) Statistics {
    var sum: i64 = 0;
    var min_val = numbers[0];
    var max_val = numbers[0];

    for (numbers) |n| {
        sum += n;
        if (n < min_val) min_val = n;
        if (n > max_val) max_val = n;
    }

    const mean = @as(f64, @floatFromInt(sum)) / @as(f64, @floatFromInt(numbers.len));

    return .{
        .sum = sum,
        .count = numbers.len,
        .mean = mean,
        .min = min_val,
        .max = max_val,
    };
}

/// Tagged union for different result types
const ProcessResult = union(enum) {
    success: struct {
        value: i32,
        message: []const u8,
    },
    warning: struct {
        value: i32,
        warning: []const u8,
    },
    failure: []const u8,
};

pub fn processValue(input: i32) ProcessResult {
    if (input < 0) {
        return .{ .failure = "Negative value not allowed" };
    } else if (input > 100) {
        return .{ .warning = .{
            .value = 100,
            .warning = "Value clamped to maximum",
        } };
    } else {
        return .{ .success = .{
            .value = input,
            .message = "Processed successfully",
        } };
    }
}
// ANCHOR_END: tagged_union_returns

/// Split result with owned memory
const SplitResult = struct {
    before: []const u8,
    after: []const u8,
    allocator: std.mem.Allocator,

    pub fn deinit(self: SplitResult) void {
        self.allocator.free(self.before);
        self.allocator.free(self.after);
    }
};

pub fn splitAndDuplicate(
    allocator: std.mem.Allocator,
    input: []const u8,
    delimiter: u8,
) !SplitResult {
    const index = std.mem.indexOfScalar(u8, input, delimiter) orelse input.len;

    const before = try allocator.dupe(u8, input[0..index]);
    errdefer allocator.free(before);

    const after = if (index < input.len)
        try allocator.dupe(u8, input[index + 1 ..])
    else
        try allocator.alloc(u8, 0);

    return .{
        .before = before,
        .after = after,
        .allocator = allocator,
    };
}

/// Compile-time type splitting
pub fn splitType(comptime T: type) struct { base: type, is_pointer: bool } {
    const info = @typeInfo(T);
    return switch (info) {
        .pointer => |ptr| .{
            .base = ptr.child,
            .is_pointer = true,
        },
        else => .{
            .base = T,
            .is_pointer = false,
        },
    };
}

/// Query result with builder pattern
const QueryResult = struct {
    rows: []const []const u8,
    count: usize,
    has_more: bool,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) QueryResult {
        return .{
            .rows = &[_][]const u8{},
            .count = 0,
            .has_more = false,
            .allocator = allocator,
        };
    }

    pub fn withRows(self: QueryResult, rows: []const []const u8) QueryResult {
        var result = self;
        result.rows = rows;
        result.count = rows.len;
        return result;
    }

    pub fn withMoreFlag(self: QueryResult, has_more: bool) QueryResult {
        var result = self;
        result.has_more = has_more;
        return result;
    }
};

/// Coordinate pair
const Point = struct {
    x: f32,
    y: f32,
};

pub fn getCoordinates() struct { x: f32, y: f32 } {
    return .{ .x = 10.0, .y = 20.0 };
}

pub fn getPoint() Point {
    return .{ .x = 10.0, .y = 20.0 };
}

/// Error union with tuple return
pub fn parseCoordinates(input: []const u8) !struct { x: i32, y: i32 } {
    var iter = std.mem.splitScalar(u8, input, ',');
    const x_str = iter.next() orelse return error.InvalidFormat;
    const y_str = iter.next() orelse return error.InvalidFormat;

    const x = try std.fmt.parseInt(i32, std.mem.trim(u8, x_str, " "), 10);
    const y = try std.fmt.parseInt(i32, std.mem.trim(u8, y_str, " "), 10);

    return .{ .x = x, .y = y };
}

/// Range with start and end
pub fn getRange(start: usize, count: usize) struct { start: usize, end: usize } {
    return .{
        .start = start,
        .end = start + count,
    };
}

// Tests

test "returning multiple values" {
    const result = divmod(17, 5);
    try std.testing.expectEqual(@as(i32, 3), result.quotient);
    try std.testing.expectEqual(@as(i32, 2), result.remainder);

    // Destructure at call site
    const q, const r = .{ result.quotient, result.remainder };
    try std.testing.expectEqual(@as(i32, 3), q);
    try std.testing.expectEqual(@as(i32, 2), r);
}

test "named return type" {
    const result = divideWithInfo(20, 4);
    try std.testing.expectEqual(@as(i32, 5), result.quotient);
    try std.testing.expectEqual(@as(i32, 0), result.remainder);
    try std.testing.expect(result.is_exact);
}

test "error union with multiple values" {
    const result = try parseInt("123abc");
    try std.testing.expectEqual(@as(i32, 123), result.value);
    try std.testing.expectEqualStrings("abc", result.remaining);

    try std.testing.expectError(error.EmptyInput, parseInt(""));
    try std.testing.expectError(error.InvalidFormat, parseInt("abc"));
}

test "optional multiple values" {
    const result = findByte("hello", 'l');
    try std.testing.expect(result != null);
    try std.testing.expectEqual(@as(usize, 2), result.?.index);

    const not_found = findByte("hello", 'x');
    try std.testing.expect(not_found == null);
}

test "min max tuple" {
    const numbers = [_]i32{ 5, 2, 8, 1, 9, 3 };
    const result = minMax(&numbers);

    try std.testing.expectEqual(@as(i32, 1), result.min);
    try std.testing.expectEqual(@as(i32, 9), result.max);
}

test "calculate statistics" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    const stats = calculateStats(&numbers);

    try std.testing.expectEqual(@as(i64, 15), stats.sum);
    try std.testing.expectEqual(@as(usize, 5), stats.count);
    try std.testing.expectEqual(@as(f64, 3.0), stats.mean);
}

test "tagged union return" {
    const ok = processValue(50);
    try std.testing.expect(ok == .success);
    try std.testing.expectEqual(@as(i32, 50), ok.success.value);

    const warned = processValue(150);
    try std.testing.expect(warned == .warning);
    try std.testing.expectEqual(@as(i32, 100), warned.warning.value);

    const err = processValue(-10);
    try std.testing.expect(err == .failure);
}

test "allocated return values" {
    const allocator = std.testing.allocator;

    const result = try splitAndDuplicate(allocator, "hello:world", ':');
    defer result.deinit();

    try std.testing.expectEqualStrings("hello", result.before);
    try std.testing.expectEqualStrings("world", result.after);
}

test "compile-time multiple returns" {
    const result1 = comptime splitType(*i32);
    try std.testing.expect(result1.is_pointer);
    try std.testing.expect(result1.base == i32);

    const result2 = comptime splitType(i32);
    try std.testing.expect(!result2.is_pointer);
    try std.testing.expect(result2.base == i32);
}

test "builder pattern return" {
    const allocator = std.testing.allocator;

    const rows = [_][]const u8{ "row1", "row2", "row3" };
    const result = QueryResult.init(allocator)
        .withRows(&rows)
        .withMoreFlag(true);

    try std.testing.expectEqual(@as(usize, 3), result.count);
    try std.testing.expect(result.has_more);
}

test "anonymous vs named struct" {
    const anon = getCoordinates();
    const named = getPoint();

    try std.testing.expectEqual(@as(f32, 10.0), anon.x);
    try std.testing.expectEqual(@as(f32, 20.0), anon.y);
    try std.testing.expectEqual(@as(f32, 10.0), named.x);
    try std.testing.expectEqual(@as(f32, 20.0), named.y);
}

test "error union with tuple" {
    const result = try parseCoordinates("10, 20");
    try std.testing.expectEqual(@as(i32, 10), result.x);
    try std.testing.expectEqual(@as(i32, 20), result.y);

    try std.testing.expectError(error.InvalidFormat, parseCoordinates("10"));
}

test "range calculation" {
    const range = getRange(5, 10);
    try std.testing.expectEqual(@as(usize, 5), range.start);
    try std.testing.expectEqual(@as(usize, 15), range.end);
}

test "negative number parsing" {
    const result = try parseInt("-456xyz");
    try std.testing.expectEqual(@as(i32, -456), result.value);
    try std.testing.expectEqualStrings("xyz", result.remaining);
}

test "split with no delimiter" {
    const allocator = std.testing.allocator;

    const result = try splitAndDuplicate(allocator, "hello", ':');
    defer result.deinit();

    try std.testing.expectEqualStrings("hello", result.before);
    try std.testing.expectEqualStrings("", result.after);
}
```

---

## Recipe 7.5: Defining Functions with Default Arguments {#recipe-7-5}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, functions, hashmap, http, memory, networking, pointers, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_5.zig`

### Problem

You want to define functions with default argument values, but Zig doesn't have traditional default arguments like Python.

### Solution

Use configuration structs with default field values:

```zig
/// Connection options with defaults
const ConnectionOptions = struct {
    host: []const u8 = "localhost",
    port: u16 = 8080,
    timeout_ms: u32 = 5000,
    retries: u8 = 3,
};

pub fn connect(options: ConnectionOptions) !void {
    std.debug.print("Connecting to {s}:{d}\n", .{ options.host, options.port });
    std.debug.print("Timeout: {}ms, Retries: {}\n", .{ options.timeout_ms, options.retries });
}

/// Simple optional parameter
pub fn greet(name: ?[]const u8) void {
    const actual_name = name orelse "World";
    std.debug.print("Hello, {s}!\n", .{actual_name});
}
```

### Discussion

### Single Optional Parameter

For functions with one optional parameter, use optionals directly:

```zig
pub fn greet(name: ?[]const u8) void {
    const actual_name = name orelse "World";
    std.debug.print("Hello, {s}!\n", .{actual_name});
}

test "optional parameter" {
    greet(null); // Uses default
    greet("Alice"); // Uses provided value
}
```

### Mixed Required and Optional Parameters

Combine required fields (no default) with optional ones:

```zig
const EmailOptions = struct {
    to: []const u8, // Required
    subject: []const u8, // Required
    from: []const u8 = "noreply@example.com", // Optional
    cc: ?[]const u8 = null, // Optional
    priority: enum { low, normal, high } = .normal, // Optional
};

pub fn sendEmail(options: EmailOptions) !void {
    std.debug.print("From: {s}\n", .{options.from});
    std.debug.print("To: {s}\n", .{options.to});
    std.debug.print("Subject: {s}\n", .{options.subject});

    if (options.cc) |cc| {
        std.debug.print("CC: {s}\n", .{cc});
    }

    std.debug.print("Priority: {s}\n", .{@tagName(options.priority)});
}

test "mixed required and optional" {
    // Required fields must be provided
    try sendEmail(.{
        .to = "user@example.com",
        .subject = "Test Email",
    });

    // Can override defaults
    try sendEmail(.{
        .to = "admin@example.com",
        .subject = "Important",
        .from = "boss@example.com",
        .cc = "team@example.com",
        .priority = .high,
    });
}
```

### Default Arguments for Generic Functions

Use comptime parameters with defaults:

```zig
pub fn ArrayList(comptime T: type) type {
    return ArrayListAligned(T, null);
}

pub fn ArrayListAligned(comptime T: type, comptime alignment: ?u29) type {
    return struct {
        items: if (alignment) |a| []align(a) T else []T,
        capacity: usize,
        allocator: std.mem.Allocator,

        pub fn init(allocator: std.mem.Allocator) @This() {
            return .{
                .items = &[_]T{},
                .capacity = 0,
                .allocator = allocator,
            };
        }
    };
}

test "generic with defaults" {
    const allocator = std.testing.allocator;

    // Use default alignment
    var list1 = ArrayList(i32).init(allocator);
    _ = list1;

    // Specify custom alignment
    var list2 = ArrayListAligned(i32, 16).init(allocator);
    _ = list2;
}
```

### Default Function Behavior

Pass function pointers as optional parameters:

```zig
const CompareFn = fn (a: i32, b: i32) bool;

fn defaultCompare(a: i32, b: i32) bool {
    return a < b;
}

pub fn sortWith(items: []i32, compare_fn: ?CompareFn) void {
    const cmp = compare_fn orelse defaultCompare;

    // Simple bubble sort for demonstration
    for (items, 0..) |_, i| {
        for (items[0 .. items.len - i - 1], 0..) |_, j| {
            if (!cmp(items[j], items[j + 1])) {
                const temp = items[j];
                items[j] = items[j + 1];
                items[j + 1] = temp;
            }
        }
    }
}

test "default function behavior" {
    var numbers = [_]i32{ 5, 2, 8, 1, 9 };

    // Use default comparison
    sortWith(&numbers, null);
    try std.testing.expectEqual(@as(i32, 1), numbers[0]);

    // Use custom comparison (descending)
    const descending = struct {
        fn cmp(a: i32, b: i32) bool {
            return a > b;
        }
    }.cmp;

    sortWith(&numbers, descending);
    try std.testing.expectEqual(@as(i32, 9), numbers[0]);
}
```

### Default Allocator Pattern

Common pattern for functions needing memory allocation:

```zig
pub fn processData(
    data: []const u8,
    allocator: ?std.mem.Allocator,
) ![]u8 {
    const alloc = allocator orelse std.heap.page_allocator;

    var result = try alloc.alloc(u8, data.len);
    errdefer alloc.free(result);

    // Process data
    for (data, 0..) |byte, i| {
        result[i] = std.ascii.toUpper(byte);
    }

    return result;
}

test "default allocator" {
    const data = "hello";

    // Use default allocator
    const result1 = try processData(data, null);
    defer std.heap.page_allocator.free(result1);
    try std.testing.expectEqualStrings("HELLO", result1);

    // Use specific allocator
    const result2 = try processData(data, std.testing.allocator);
    defer std.testing.allocator.free(result2);
    try std.testing.expectEqualStrings("HELLO", result2);
}
```

### Builder Pattern with Defaults

Incremental configuration with sensible defaults:

```zig
const HttpRequest = struct {
    url: []const u8,
    method: []const u8 = "GET",
    headers: std.StringHashMap([]const u8),
    timeout_ms: u32 = 30000,
    follow_redirects: bool = true,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, url: []const u8) HttpRequest {
        return .{
            .url = url,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn setMethod(self: *HttpRequest, method: []const u8) *HttpRequest {
        self.method = method;
        return self;
    }

    pub fn setTimeout(self: *HttpRequest, ms: u32) *HttpRequest {
        self.timeout_ms = ms;
        return self;
    }

    pub fn addHeader(self: *HttpRequest, key: []const u8, value: []const u8) !*HttpRequest {
        try self.headers.put(key, value);
        return self;
    }

    pub fn deinit(self: *HttpRequest) void {
        self.headers.deinit();
    }
};

test "builder with defaults" {
    const allocator = std.testing.allocator;

    var request = HttpRequest.init(allocator, "https://example.com");
    defer request.deinit();

    _ = request.setMethod("POST")
        .setTimeout(5000);

    try std.testing.expectEqualStrings("POST", request.method);
    try std.testing.expectEqual(@as(u32, 5000), request.timeout_ms);
    try std.testing.expect(request.follow_redirects); // Still default
}
```

### Default Values for Buffers

Pre-allocate buffers with sensible defaults:

```zig
const BufferOptions = struct {
    initial_capacity: usize = 4096,
    max_size: ?usize = null,
    clear_on_free: bool = false,
};

pub fn Buffer(comptime options: BufferOptions) type {
    return struct {
        data: []u8,
        len: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) !Self {
            return .{
                .data = try allocator.alloc(u8, options.initial_capacity),
                .len = 0,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            if (options.clear_on_free) {
                @memset(self.data, 0);
            }
            self.allocator.free(self.data);
        }

        pub fn append(self: *Self, byte: u8) !void {
            if (options.max_size) |max| {
                if (self.len >= max) {
                    return error.BufferFull;
                }
            }

            if (self.len >= self.data.len) {
                const new_cap = self.data.len * 2;
                const new_data = try self.allocator.realloc(self.data, new_cap);
                self.data = new_data;
            }

            self.data[self.len] = byte;
            self.len += 1;
        }
    };
}

test "buffer with defaults" {
    const allocator = std.testing.allocator;

    // Default buffer
    var buf1 = try Buffer(.{}).init(allocator);
    defer buf1.deinit();

    try buf1.append('A');
    try std.testing.expectEqual(@as(usize, 1), buf1.len);

    // Custom buffer with size limit
    var buf2 = try Buffer(.{ .max_size = 10 }).init(allocator);
    defer buf2.deinit();

    for (0..10) |_| {
        try buf2.append('X');
    }

    try std.testing.expectError(error.BufferFull, buf2.append('Y'));
}
```

### Compile-Time Default Computation

Compute defaults at compile time:

```zig
pub fn Matrix(comptime rows: usize, comptime cols: usize, comptime default_value: f32) type {
    return struct {
        data: [rows][cols]f32,

        pub fn init() @This() {
            var result: @This() = undefined;
            for (&result.data) |*row| {
                for (row) |*cell| {
                    cell.* = default_value;
                }
            }
            return result;
        }

        pub fn get(self: @This(), row: usize, col: usize) f32 {
            return self.data[row][col];
        }
    };
}

test "compile-time defaults" {
    const Mat3x3 = Matrix(3, 3, 0.0);
    const matrix = Mat3x3.init();

    try std.testing.expectEqual(@as(f32, 0.0), matrix.get(0, 0));
    try std.testing.expectEqual(@as(f32, 0.0), matrix.get(2, 2));
}
```

### Default Error Handling Strategy

Provide default error handling:

```zig
const ErrorHandler = fn (err: anyerror) void;

fn defaultErrorHandler(err: anyerror) void {
    std.debug.print("Error occurred: {}\n", .{err});
}

pub fn executeWithHandler(
    operation: fn () anyerror!void,
    handler: ?ErrorHandler,
) void {
    const error_handler = handler orelse defaultErrorHandler;

    operation() catch |err| {
        error_handler(err);
    };
}

test "default error handler" {
    const failingOp = struct {
        fn run() anyerror!void {
            return error.SomethingWrong;
        }
    }.run;

    // Use default handler
    executeWithHandler(failingOp, null);

    // Use custom handler
    const customHandler = struct {
        fn handle(err: anyerror) void {
            _ = err;
            // Custom handling
        }
    }.handle;

    executeWithHandler(failingOp, customHandler);
}
```

### Best Practices

**Struct-Based Defaults:**
```zig
// Good: Clear defaults, named parameters
const Options = struct {
    size: usize = 100,
    enabled: bool = true,
};
fn process(options: Options) void {}

// Bad: Unclear what default values are
fn process(size: ?usize, enabled: ?bool) void {
    const s = size orelse 100;
    const e = enabled orelse true;
}
```

**Required vs Optional:**
- Make truly required parameters fields without defaults
- Use default values for optional parameters with sensible defaults
- Use `?T` for parameters that can be legitimately null

**Documentation:**
```zig
/// Opens a file with the specified options.
///
/// Default values:
/// - mode: .read_only
/// - buffer_size: 4096
/// - create_if_missing: false
const OpenOptions = struct {
    path: []const u8, // Required
    mode: std.fs.File.OpenMode = .read_only,
    buffer_size: usize = 4096,
    create_if_missing: bool = false,
};
```

**Type Safety:**
- Use enums for options with fixed choices
- Use distinct types for different kinds of parameters
- Leverage compile-time checks to validate configurations

### Related Functions

- Struct initialization syntax `.{}`
- Optional types `?T` and `orelse`
- Default struct field values
- `@hasField()` to check for optional configuration
- Comptime parameters for compile-time defaults
- Builder pattern for incremental configuration

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_defaults
/// Connection options with defaults
const ConnectionOptions = struct {
    host: []const u8 = "localhost",
    port: u16 = 8080,
    timeout_ms: u32 = 5000,
    retries: u8 = 3,
};

pub fn connect(options: ConnectionOptions) !void {
    std.debug.print("Connecting to {s}:{d}\n", .{ options.host, options.port });
    std.debug.print("Timeout: {}ms, Retries: {}\n", .{ options.timeout_ms, options.retries });
}

/// Simple optional parameter
pub fn greet(name: ?[]const u8) void {
    const actual_name = name orelse "World";
    std.debug.print("Hello, {s}!\n", .{actual_name});
}
// ANCHOR_END: basic_defaults

// ANCHOR: optional_parameters
/// Email options with required and optional fields
const EmailOptions = struct {
    to: []const u8, // Required
    subject: []const u8, // Required
    from: []const u8 = "noreply@example.com", // Optional
    cc: ?[]const u8 = null, // Optional
    priority: enum { low, normal, high } = .normal, // Optional
};

pub fn sendEmail(options: EmailOptions) !void {
    std.debug.print("From: {s}\n", .{options.from});
    std.debug.print("To: {s}\n", .{options.to});
    std.debug.print("Subject: {s}\n", .{options.subject});

    if (options.cc) |cc| {
        std.debug.print("CC: {s}\n", .{cc});
    }

    std.debug.print("Priority: {s}\n", .{@tagName(options.priority)});
}
// ANCHOR_END: optional_parameters

// ANCHOR: comptime_defaults
/// Generic array list with default alignment
pub fn ArrayList(comptime T: type) type {
    return ArrayListAligned(T, null);
}

pub fn ArrayListAligned(comptime T: type, comptime alignment: ?u29) type {
    return struct {
        items: if (alignment) |a| []align(a) T else []T,
        capacity: usize,
        allocator: std.mem.Allocator,

        pub fn init(allocator: std.mem.Allocator) @This() {
            return .{
                .items = &[_]T{},
                .capacity = 0,
                .allocator = allocator,
            };
        }
    };
}

/// Sorting with optional comparison function
const CompareFn = fn (a: i32, b: i32) bool;

fn defaultCompare(a: i32, b: i32) bool {
    return a < b;
}

pub fn sortWith(items: []i32, compare_fn: ?CompareFn) void {
    const cmp = compare_fn orelse defaultCompare;

    // Simple bubble sort for demonstration
    for (items, 0..) |_, i| {
        for (items[0 .. items.len - i - 1], 0..) |_, j| {
            if (!cmp(items[j], items[j + 1])) {
                const temp = items[j];
                items[j] = items[j + 1];
                items[j + 1] = temp;
            }
        }
    }
}

/// Process data with optional allocator
pub fn processData(
    data: []const u8,
    allocator: ?std.mem.Allocator,
) ![]u8 {
    const alloc = allocator orelse std.heap.page_allocator;

    var result = try alloc.alloc(u8, data.len);
    errdefer alloc.free(result);

    // Process data
    for (data, 0..) |byte, i| {
        result[i] = std.ascii.toUpper(byte);
    }

    return result;
}

/// HTTP request builder with defaults
const HttpRequest = struct {
    url: []const u8,
    method: []const u8 = "GET",
    headers: std.StringHashMap([]const u8),
    timeout_ms: u32 = 30000,
    follow_redirects: bool = true,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, url: []const u8) HttpRequest {
        return .{
            .url = url,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn setMethod(self: *HttpRequest, method: []const u8) *HttpRequest {
        self.method = method;
        return self;
    }

    pub fn setTimeout(self: *HttpRequest, ms: u32) *HttpRequest {
        self.timeout_ms = ms;
        return self;
    }

    pub fn addHeader(self: *HttpRequest, key: []const u8, value: []const u8) !*HttpRequest {
        try self.headers.put(key, value);
        return self;
    }

    pub fn deinit(self: *HttpRequest) void {
        self.headers.deinit();
    }
};

/// Buffer with compile-time options
const BufferOptions = struct {
    initial_capacity: usize = 4096,
    max_size: ?usize = null,
    clear_on_free: bool = false,
};

pub fn Buffer(comptime options: BufferOptions) type {
    return struct {
        data: []u8,
        len: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) !Self {
            return .{
                .data = try allocator.alloc(u8, options.initial_capacity),
                .len = 0,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            if (options.clear_on_free) {
                @memset(self.data, 0);
            }
            self.allocator.free(self.data);
        }

        pub fn append(self: *Self, byte: u8) !void {
            if (options.max_size) |max| {
                if (self.len >= max) {
                    return error.BufferFull;
                }
            }

            if (self.len >= self.data.len) {
                const new_cap = self.data.len * 2;
                const new_data = try self.allocator.realloc(self.data, new_cap);
                self.data = new_data;
            }

            self.data[self.len] = byte;
            self.len += 1;
        }
    };
}
// ANCHOR_END: comptime_defaults

/// Matrix with compile-time default value
pub fn Matrix(comptime rows: usize, comptime cols: usize, comptime default_value: f32) type {
    return struct {
        data: [rows][cols]f32,

        pub fn init() @This() {
            var result: @This() = undefined;
            for (&result.data) |*row| {
                for (row) |*cell| {
                    cell.* = default_value;
                }
            }
            return result;
        }

        pub fn get(self: @This(), row: usize, col: usize) f32 {
            return self.data[row][col];
        }
    };
}

/// Error handling with default handler
const ErrorHandler = fn (err: anyerror) void;

fn defaultErrorHandler(err: anyerror) void {
    std.debug.print("Error occurred: {}\n", .{err});
}

pub fn executeWithHandler(
    operation: fn () anyerror!void,
    handler: ?ErrorHandler,
) void {
    const error_handler = handler orelse defaultErrorHandler;

    operation() catch |err| {
        error_handler(err);
    };
}

/// File options
const FileOptions = struct {
    path: []const u8, // Required
    mode: enum { read, write, append } = .read,
    buffer_size: usize = 4096,
    create_if_missing: bool = false,
};

pub fn openFile(options: FileOptions) !void {
    std.debug.print("Opening: {s}\n", .{options.path});
    std.debug.print("Mode: {s}, Buffer: {}\n", .{
        @tagName(options.mode),
        options.buffer_size,
    });
    std.debug.print("Create if missing: {}\n", .{options.create_if_missing});
}

// Tests

test "default arguments" {
    // Use all defaults
    try connect(.{});

    // Override specific fields
    try connect(.{ .host = "example.com" });

    // Override multiple fields
    try connect(.{
        .host = "api.example.com",
        .port = 443,
        .timeout_ms = 10000,
    });
}

test "optional parameter" {
    greet(null); // Uses default
    greet("Alice"); // Uses provided value
}

test "mixed required and optional" {
    // Required fields must be provided
    try sendEmail(.{
        .to = "user@example.com",
        .subject = "Test Email",
    });

    // Can override defaults
    try sendEmail(.{
        .to = "admin@example.com",
        .subject = "Important",
        .from = "boss@example.com",
        .cc = "team@example.com",
        .priority = .high,
    });
}

test "generic with defaults" {
    const allocator = std.testing.allocator;

    // Use default alignment
    const list1 = ArrayList(i32).init(allocator);
    _ = list1;

    // Specify custom alignment
    const list2 = ArrayListAligned(i32, 16).init(allocator);
    _ = list2;
}

test "default function behavior" {
    var numbers = [_]i32{ 5, 2, 8, 1, 9 };

    // Use default comparison
    sortWith(&numbers, null);
    try std.testing.expectEqual(@as(i32, 1), numbers[0]);

    // Use custom comparison (descending)
    const descending = struct {
        fn cmp(a: i32, b: i32) bool {
            return a > b;
        }
    }.cmp;

    sortWith(&numbers, descending);
    try std.testing.expectEqual(@as(i32, 9), numbers[0]);
}

test "default allocator" {
    const data = "hello";

    // Use default allocator
    const result1 = try processData(data, null);
    defer std.heap.page_allocator.free(result1);
    try std.testing.expectEqualStrings("HELLO", result1);

    // Use specific allocator
    const result2 = try processData(data, std.testing.allocator);
    defer std.testing.allocator.free(result2);
    try std.testing.expectEqualStrings("HELLO", result2);
}

test "builder with defaults" {
    const allocator = std.testing.allocator;

    var request = HttpRequest.init(allocator, "https://example.com");
    defer request.deinit();

    _ = request.setMethod("POST")
        .setTimeout(5000);

    try std.testing.expectEqualStrings("POST", request.method);
    try std.testing.expectEqual(@as(u32, 5000), request.timeout_ms);
    try std.testing.expect(request.follow_redirects); // Still default
}

test "buffer with defaults" {
    const allocator = std.testing.allocator;

    // Default buffer
    var buf1 = try Buffer(.{}).init(allocator);
    defer buf1.deinit();

    try buf1.append('A');
    try std.testing.expectEqual(@as(usize, 1), buf1.len);

    // Custom buffer with size limit
    var buf2 = try Buffer(.{ .max_size = 10 }).init(allocator);
    defer buf2.deinit();

    for (0..10) |_| {
        try buf2.append('X');
    }

    try std.testing.expectError(error.BufferFull, buf2.append('Y'));
}

test "compile-time defaults" {
    const Mat3x3 = Matrix(3, 3, 0.0);
    const matrix = Mat3x3.init();

    try std.testing.expectEqual(@as(f32, 0.0), matrix.get(0, 0));
    try std.testing.expectEqual(@as(f32, 0.0), matrix.get(2, 2));
}

test "default error handler" {
    const failingOp = struct {
        fn run() anyerror!void {
            return error.SomethingWrong;
        }
    }.run;

    // Use default handler
    executeWithHandler(failingOp, null);

    // Use custom handler
    const customHandler = struct {
        var error_captured: ?anyerror = null;

        fn handle(err: anyerror) void {
            error_captured = err;
        }
    }.handle;

    executeWithHandler(failingOp, customHandler);
}

test "all defaults used" {
    const opts: ConnectionOptions = .{};
    try std.testing.expectEqualStrings("localhost", opts.host);
    try std.testing.expectEqual(@as(u16, 8080), opts.port);
    try std.testing.expectEqual(@as(u32, 5000), opts.timeout_ms);
    try std.testing.expectEqual(@as(u8, 3), opts.retries);
}

test "partial override" {
    const opts: ConnectionOptions = .{ .port = 443 };
    try std.testing.expectEqualStrings("localhost", opts.host);
    try std.testing.expectEqual(@as(u16, 443), opts.port);
}

test "file options with defaults" {
    try openFile(.{ .path = "/tmp/test.txt" });

    try openFile(.{
        .path = "/tmp/data.bin",
        .mode = .write,
        .create_if_missing = true,
    });
}

test "buffer initial capacity" {
    const allocator = std.testing.allocator;

    var buf = try Buffer(.{ .initial_capacity = 16 }).init(allocator);
    defer buf.deinit();

    try std.testing.expectEqual(@as(usize, 16), buf.data.len);
}

test "matrix with non-zero default" {
    const Mat2x2 = Matrix(2, 2, 1.0);
    const matrix = Mat2x2.init();

    try std.testing.expectEqual(@as(f32, 1.0), matrix.get(0, 0));
    try std.testing.expectEqual(@as(f32, 1.0), matrix.get(1, 1));
}
```

---

## Recipe 7.6: Defining Anonymous or Inline Functions {#recipe-7-6}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, functions, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_6.zig`

### Problem

You want to define small, anonymous functions (like lambdas in Python) for callbacks, comparisons, or local operations.

### Solution

Use anonymous structs with functions for simple callbacks:

```zig
/// Apply an operation to two integers
pub fn applyOperation(a: i32, b: i32, operation: fn (i32, i32) i32) i32 {
    return operation(a, b);
}

/// Inline addition function
inline fn add(a: i32, b: i32) i32 {
    return a + b;
}

/// Inline square function
inline fn square(x: i32) i32 {
    return x * x;
}

pub fn processValues(values: []i32) i32 {
    var sum: i32 = 0;
    for (values) |v| {
        sum = add(sum, square(v));
    }
    return sum;
}
```

### Discussion

### Inline Functions

Use the `inline` keyword to force inlining of small functions:

```zig
inline fn add(a: i32, b: i32) i32 {
    return a + b;
}

inline fn square(x: i32) i32 {
    return x * x;
}

pub fn processValues(values: []i32) i32 {
    var sum: i32 = 0;
    for (values) |v| {
        sum = add(sum, square(v));
    }
    return sum;
}

test "inline functions" {
    var values = [_]i32{ 1, 2, 3, 4 };
    const result = processValues(&values);
    try std.testing.expectEqual(@as(i32, 30), result); // 1 + 4 + 9 + 16
}
```

### Anonymous Comparison Functions

Common pattern for sorting with custom comparison:

```zig
pub fn sortBy(items: []i32, comptime descending: bool) void {
    const compare = if (descending)
        struct {
            fn cmp(_: void, a: i32, b: i32) bool {
                return a > b;
            }
        }.cmp
    else
        struct {
            fn cmp(_: void, a: i32, b: i32) bool {
                return a < b;
            }
        }.cmp;

    std.mem.sort(i32, items, {}, compare);
}

test "anonymous comparison" {
    var numbers = [_]i32{ 5, 2, 8, 1, 9 };

    sortBy(&numbers, false);
    try std.testing.expectEqual(@as(i32, 1), numbers[0]);

    sortBy(&numbers, true);
    try std.testing.expectEqual(@as(i32, 9), numbers[0]);
}
```

### Function Tables

Map operations to anonymous implementations:

```zig
const Operation = enum { add, subtract, multiply, divide };

pub fn calculate(op: Operation, a: i32, b: i32) !i32 {
    const functions = .{
        struct {
            fn call(x: i32, y: i32) !i32 {
                return x + y;
            }
        }.call,
        struct {
            fn call(x: i32, y: i32) !i32 {
                return x - y;
            }
        }.call,
        struct {
            fn call(x: i32, y: i32) !i32 {
                return x * y;
            }
        }.call,
        struct {
            fn call(x: i32, y: i32) !i32 {
                if (y == 0) return error.DivideByZero;
                return @divTrunc(x, y);
            }
        }.call,
    };

    return switch (op) {
        .add => functions[0](a, b),
        .subtract => functions[1](a, b),
        .multiply => functions[2](a, b),
        .divide => functions[3](a, b),
    };
}

test "function tables" {
    try std.testing.expectEqual(@as(i32, 8), try calculate(.add, 5, 3));
    try std.testing.expectEqual(@as(i32, 2), try calculate(.subtract, 5, 3));
    try std.testing.expectEqual(@as(i32, 15), try calculate(.multiply, 5, 3));
    try std.testing.expectEqual(@as(i32, 1), try calculate(.divide, 5, 3));
    try std.testing.expectError(error.DivideByZero, calculate(.divide, 5, 0));
}
```

### Filtering with Predicates

Use anonymous predicates for filtering:

```zig
pub fn filter(
    allocator: std.mem.Allocator,
    items: []const i32,
    predicate: fn (i32) bool,
) ![]i32 {
    var result = std.ArrayList(i32).init(allocator);
    errdefer result.deinit();

    for (items) |item| {
        if (predicate(item)) {
            try result.append(item);
        }
    }

    return result.toOwnedSlice();
}

test "anonymous predicates" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };

    // Filter even numbers
    const is_even = struct {
        fn call(n: i32) bool {
            return @mod(n, 2) == 0;
        }
    }.call;

    const evens = try filter(allocator, &numbers, is_even);
    defer allocator.free(evens);

    try std.testing.expectEqual(@as(usize, 5), evens.len);
    try std.testing.expectEqual(@as(i32, 2), evens[0]);

    // Filter numbers greater than 5
    const greater_than_five = struct {
        fn call(n: i32) bool {
            return n > 5;
        }
    }.call;

    const filtered = try filter(allocator, &numbers, greater_than_five);
    defer allocator.free(filtered);

    try std.testing.expectEqual(@as(usize, 5), filtered.len);
    try std.testing.expectEqual(@as(i32, 6), filtered[0]);
}
```

### Map/Transform Functions

Transform data with anonymous functions:

```zig
pub fn map(
    allocator: std.mem.Allocator,
    items: []const i32,
    transform: fn (i32) i32,
) ![]i32 {
    var result = try allocator.alloc(i32, items.len);
    errdefer allocator.free(result);

    for (items, 0..) |item, i| {
        result[i] = transform(item);
    }

    return result;
}

test "anonymous transformations" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    // Double all values
    const double = struct {
        fn call(n: i32) i32 {
            return n * 2;
        }
    }.call;

    const doubled = try map(allocator, &numbers, double);
    defer allocator.free(doubled);

    try std.testing.expectEqual(@as(i32, 2), doubled[0]);
    try std.testing.expectEqual(@as(i32, 10), doubled[4]);

    // Square all values
    const square = struct {
        fn call(n: i32) i32 {
            return n * n;
        }
    }.call;

    const squared = try map(allocator, &numbers, square);
    defer allocator.free(squared);

    try std.testing.expectEqual(@as(i32, 1), squared[0]);
    try std.testing.expectEqual(@as(i32, 25), squared[4]);
}
```

### Comptime Function Generation

Generate functions at compile time:

```zig
pub fn makeAdder(comptime n: i32) fn (i32) i32 {
    return struct {
        fn add(x: i32) i32 {
            return x + n;
        }
    }.add;
}

test "comptime function generation" {
    const add5 = makeAdder(5);
    const add10 = makeAdder(10);

    try std.testing.expectEqual(@as(i32, 15), add5(10));
    try std.testing.expectEqual(@as(i32, 20), add10(10));
}
```

### Generic Anonymous Functions

Create generic operations:

```zig
pub fn GenericOperation(comptime T: type) type {
    return struct {
        pub fn min(a: T, b: T) T {
            return if (a < b) a else b;
        }

        pub fn max(a: T, b: T) T {
            return if (a > b) a else b;
        }

        pub fn clamp(value: T, low: T, high: T) T {
            return max(low, min(value, high));
        }
    };
}

test "generic anonymous functions" {
    const IntOps = GenericOperation(i32);

    try std.testing.expectEqual(@as(i32, 3), IntOps.min(5, 3));
    try std.testing.expectEqual(@as(i32, 5), IntOps.max(5, 3));
    try std.testing.expectEqual(@as(i32, 5), IntOps.clamp(10, 0, 5));

    const FloatOps = GenericOperation(f32);

    try std.testing.expectEqual(@as(f32, 1.5), FloatOps.min(2.5, 1.5));
    try std.testing.expectEqual(@as(f32, 2.5), FloatOps.max(2.5, 1.5));
}
```

### Callback Registration

Register anonymous callbacks:

```zig
const EventHandler = struct {
    context: *anyopaque,
    callback: *const fn (*anyopaque, []const u8) void,

    pub fn init(
        context: anytype,
        comptime callback: fn (@TypeOf(context), []const u8) void,
    ) EventHandler {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, data: []const u8) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                callback(ptr, data);
            }
        };

        return .{
            .context = @ptrCast(context),
            .callback = Wrapper.call,
        };
    }

    pub fn trigger(self: EventHandler, data: []const u8) void {
        self.callback(self.context, data);
    }
};

test "callback registration" {
    const Handler = struct {
        count: usize = 0,

        fn onEvent(self: *@This(), data: []const u8) void {
            self.count += data.len;
        }
    };

    var handler = Handler{};
    const event = EventHandler.init(&handler, Handler.onEvent);

    event.trigger("hello");
    event.trigger("world");

    try std.testing.expectEqual(@as(usize, 10), handler.count);
}
```

### Reduce/Fold Operations

Implement reduce with anonymous functions:

```zig
pub fn reduce(
    items: []const i32,
    initial: i32,
    reducer: fn (i32, i32) i32,
) i32 {
    var accumulator = initial;
    for (items) |item| {
        accumulator = reducer(accumulator, item);
    }
    return accumulator;
}

test "anonymous reduce" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    // Sum
    const sum = struct {
        fn call(acc: i32, val: i32) i32 {
            return acc + val;
        }
    }.call;

    const total = reduce(&numbers, 0, sum);
    try std.testing.expectEqual(@as(i32, 15), total);

    // Product
    const multiply = struct {
        fn call(acc: i32, val: i32) i32 {
            return acc * val;
        }
    }.call;

    const product = reduce(&numbers, 1, multiply);
    try std.testing.expectEqual(@as(i32, 120), product);
}
```

### Inline Loop Unrolling

Use inline functions for loop unrolling:

```zig
pub fn processVector(data: @Vector(4, i32)) @Vector(4, i32) {
    inline for (0..4) |i| {
        data[i] = data[i] * 2;
    }
    return data;
}

test "inline loop unrolling" {
    const input: @Vector(4, i32) = .{ 1, 2, 3, 4 };
    const result = processVector(input);

    try std.testing.expectEqual(@as(i32, 2), result[0]);
    try std.testing.expectEqual(@as(i32, 8), result[3]);
}
```

### Best Practices

**Anonymous Struct Pattern:**
```zig
// Good: Clear intent, self-documenting
const is_positive = struct {
    fn call(n: i32) bool {
        return n > 0;
    }
}.call;

// Acceptable: Very short, obvious operation
const double = struct {
    fn f(n: i32) i32 {
        return n * 2;
    }
}.f;
```

**When to Use Inline:**
- Small, frequently called functions
- Performance-critical inner loops
- When function call overhead is significant
- Comptime-evaluated code

**When NOT to Use Inline:**
- Large functions (increases binary size)
- Rarely called code
- When debugging (inlined code harder to debug)
- Recursive functions

**Type Safety:**
```zig
// Good: Type-safe callback with context
pub fn forEach(
    items: []i32,
    context: anytype,
    callback: fn (@TypeOf(context), i32) void,
) void {
    for (items) |item| {
        callback(context, item);
    }
}

// Less safe: Type-erased context
pub fn forEachErased(
    items: []i32,
    context: *anyopaque,
    callback: fn (*anyopaque, i32) void,
) void {
    for (items) |item| {
        callback(context, item);
    }
}
```

**Performance Considerations:**
- Anonymous structs have zero runtime cost
- `inline` functions are expanded at call site
- Function pointers have call overhead
- Comptime functions are evaluated at compile time

### Related Functions

- `inline` keyword for forced inlining
- Anonymous struct syntax `struct { ... }`
- Function pointers `fn(T) R`
- `@ptrCast` and `@alignCast` for type-erased callbacks
- `std.mem.sort` for custom comparisons
- `comptime` for compile-time function generation

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_anonymous
/// Apply an operation to two integers
pub fn applyOperation(a: i32, b: i32, operation: fn (i32, i32) i32) i32 {
    return operation(a, b);
}

/// Inline addition function
inline fn add(a: i32, b: i32) i32 {
    return a + b;
}

/// Inline square function
inline fn square(x: i32) i32 {
    return x * x;
}

pub fn processValues(values: []i32) i32 {
    var sum: i32 = 0;
    for (values) |v| {
        sum = add(sum, square(v));
    }
    return sum;
}
// ANCHOR_END: basic_anonymous

// ANCHOR: inline_functions
/// Sort with compile-time direction
pub fn sortBy(items: []i32, comptime descending: bool) void {
    const compare = if (descending)
        struct {
            fn cmp(_: void, a: i32, b: i32) bool {
                return a > b;
            }
        }.cmp
    else
        struct {
            fn cmp(_: void, a: i32, b: i32) bool {
                return a < b;
            }
        }.cmp;

    std.mem.sort(i32, items, {}, compare);
}
// ANCHOR_END: inline_functions

// ANCHOR: function_tables
/// Operation enum
const Operation = enum { add, subtract, multiply, divide };

/// Calculate with operation selector
pub fn calculate(op: Operation, a: i32, b: i32) !i32 {
    const functions = .{
        struct {
            fn call(x: i32, y: i32) !i32 {
                return x + y;
            }
        }.call,
        struct {
            fn call(x: i32, y: i32) !i32 {
                return x - y;
            }
        }.call,
        struct {
            fn call(x: i32, y: i32) !i32 {
                return x * y;
            }
        }.call,
        struct {
            fn call(x: i32, y: i32) !i32 {
                if (y == 0) return error.DivideByZero;
                return @divTrunc(x, y);
            }
        }.call,
    };

    return switch (op) {
        .add => functions[0](a, b),
        .subtract => functions[1](a, b),
        .multiply => functions[2](a, b),
        .divide => functions[3](a, b),
    };
}
// ANCHOR_END: function_tables

/// Filter items by predicate
pub fn filter(
    allocator: std.mem.Allocator,
    items: []const i32,
    predicate: fn (i32) bool,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (predicate(item)) {
            try result.append(allocator, item);
        }
    }

    return try result.toOwnedSlice(allocator);
}

/// Map transformation over items
pub fn map(
    allocator: std.mem.Allocator,
    items: []const i32,
    transform: fn (i32) i32,
) ![]i32 {
    var result = try allocator.alloc(i32, items.len);
    errdefer allocator.free(result);

    for (items, 0..) |item, i| {
        result[i] = transform(item);
    }

    return result;
}

/// Generate adder function at compile time
pub fn makeAdder(comptime n: i32) fn (i32) i32 {
    return struct {
        fn add_impl(x: i32) i32 {
            return x + n;
        }
    }.add_impl;
}

/// Generic operations
pub fn GenericOperation(comptime T: type) type {
    return struct {
        pub fn min(a: T, b: T) T {
            return if (a < b) a else b;
        }

        pub fn max(a: T, b: T) T {
            return if (a > b) a else b;
        }

        pub fn clamp(value: T, low: T, high: T) T {
            return max(low, min(value, high));
        }
    };
}

/// Event handler with type-erased context
const EventHandler = struct {
    context: *anyopaque,
    callback: *const fn (*anyopaque, []const u8) void,

    pub fn init(
        context: anytype,
        comptime callback: fn (@TypeOf(context), []const u8) void,
    ) EventHandler {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, data: []const u8) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                callback(ptr, data);
            }
        };

        return .{
            .context = @ptrCast(context),
            .callback = Wrapper.call,
        };
    }

    pub fn trigger(self: EventHandler, data: []const u8) void {
        self.callback(self.context, data);
    }
};

/// Reduce operation
pub fn reduce(
    items: []const i32,
    initial: i32,
    reducer: fn (i32, i32) i32,
) i32 {
    var accumulator = initial;
    for (items) |item| {
        accumulator = reducer(accumulator, item);
    }
    return accumulator;
}

/// Process vector with inline operations
pub fn processVector(data: @Vector(4, i32)) @Vector(4, i32) {
    var result = data;
    inline for (0..4) |i| {
        result[i] = result[i] * 2;
    }
    return result;
}

// Tests

test "anonymous functions" {
    // Define anonymous function using struct
    const add_fn = struct {
        fn call(a: i32, b: i32) i32 {
            return a + b;
        }
    }.call;

    const result = applyOperation(5, 3, add_fn);
    try std.testing.expectEqual(@as(i32, 8), result);

    // Define multiply inline
    const multiply = struct {
        fn call(a: i32, b: i32) i32 {
            return a * b;
        }
    }.call;

    const result2 = applyOperation(5, 3, multiply);
    try std.testing.expectEqual(@as(i32, 15), result2);
}

test "inline functions" {
    var values = [_]i32{ 1, 2, 3, 4 };
    const result = processValues(&values);
    try std.testing.expectEqual(@as(i32, 30), result); // 1 + 4 + 9 + 16
}

test "anonymous comparison" {
    var numbers = [_]i32{ 5, 2, 8, 1, 9 };

    sortBy(&numbers, false);
    try std.testing.expectEqual(@as(i32, 1), numbers[0]);

    sortBy(&numbers, true);
    try std.testing.expectEqual(@as(i32, 9), numbers[0]);
}

test "function tables" {
    try std.testing.expectEqual(@as(i32, 8), try calculate(.add, 5, 3));
    try std.testing.expectEqual(@as(i32, 2), try calculate(.subtract, 5, 3));
    try std.testing.expectEqual(@as(i32, 15), try calculate(.multiply, 5, 3));
    try std.testing.expectEqual(@as(i32, 1), try calculate(.divide, 5, 3));
    try std.testing.expectError(error.DivideByZero, calculate(.divide, 5, 0));
}

test "anonymous predicates" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };

    // Filter even numbers
    const is_even = struct {
        fn call(n: i32) bool {
            return @mod(n, 2) == 0;
        }
    }.call;

    const evens = try filter(allocator, &numbers, is_even);
    defer allocator.free(evens);

    try std.testing.expectEqual(@as(usize, 5), evens.len);
    try std.testing.expectEqual(@as(i32, 2), evens[0]);

    // Filter numbers greater than 5
    const greater_than_five = struct {
        fn call(n: i32) bool {
            return n > 5;
        }
    }.call;

    const filtered = try filter(allocator, &numbers, greater_than_five);
    defer allocator.free(filtered);

    try std.testing.expectEqual(@as(usize, 5), filtered.len);
    try std.testing.expectEqual(@as(i32, 6), filtered[0]);
}

test "anonymous transformations" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    // Double all values
    const double = struct {
        fn call(n: i32) i32 {
            return n * 2;
        }
    }.call;

    const doubled = try map(allocator, &numbers, double);
    defer allocator.free(doubled);

    try std.testing.expectEqual(@as(i32, 2), doubled[0]);
    try std.testing.expectEqual(@as(i32, 10), doubled[4]);

    // Square all values
    const square_fn = struct {
        fn call(n: i32) i32 {
            return n * n;
        }
    }.call;

    const squared = try map(allocator, &numbers, square_fn);
    defer allocator.free(squared);

    try std.testing.expectEqual(@as(i32, 1), squared[0]);
    try std.testing.expectEqual(@as(i32, 25), squared[4]);
}

test "comptime function generation" {
    const add5 = makeAdder(5);
    const add10 = makeAdder(10);

    try std.testing.expectEqual(@as(i32, 15), add5(10));
    try std.testing.expectEqual(@as(i32, 20), add10(10));
}

test "generic anonymous functions" {
    const IntOps = GenericOperation(i32);

    try std.testing.expectEqual(@as(i32, 3), IntOps.min(5, 3));
    try std.testing.expectEqual(@as(i32, 5), IntOps.max(5, 3));
    try std.testing.expectEqual(@as(i32, 5), IntOps.clamp(10, 0, 5));

    const FloatOps = GenericOperation(f32);

    try std.testing.expectEqual(@as(f32, 1.5), FloatOps.min(2.5, 1.5));
    try std.testing.expectEqual(@as(f32, 2.5), FloatOps.max(2.5, 1.5));
}

test "callback registration" {
    const Handler = struct {
        count: usize = 0,

        fn onEvent(self: *@This(), data: []const u8) void {
            self.count += data.len;
        }
    };

    var handler = Handler{};
    const event = EventHandler.init(&handler, Handler.onEvent);

    event.trigger("hello");
    event.trigger("world");

    try std.testing.expectEqual(@as(usize, 10), handler.count);
}

test "anonymous reduce" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    // Sum
    const sum = struct {
        fn call(acc: i32, val: i32) i32 {
            return acc + val;
        }
    }.call;

    const total = reduce(&numbers, 0, sum);
    try std.testing.expectEqual(@as(i32, 15), total);

    // Product
    const multiply = struct {
        fn call(acc: i32, val: i32) i32 {
            return acc * val;
        }
    }.call;

    const product = reduce(&numbers, 1, multiply);
    try std.testing.expectEqual(@as(i32, 120), product);
}

test "inline loop unrolling" {
    const input: @Vector(4, i32) = .{ 1, 2, 3, 4 };
    const result = processVector(input);

    try std.testing.expectEqual(@as(i32, 2), result[0]);
    try std.testing.expectEqual(@as(i32, 8), result[3]);
}

test "subtract operation" {
    const subtract = struct {
        fn call(a: i32, b: i32) i32 {
            return a - b;
        }
    }.call;

    const result = applyOperation(10, 3, subtract);
    try std.testing.expectEqual(@as(i32, 7), result);
}

test "filter odd numbers" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    const is_odd = struct {
        fn call(n: i32) bool {
            return @mod(n, 2) != 0;
        }
    }.call;

    const odds = try filter(allocator, &numbers, is_odd);
    defer allocator.free(odds);

    try std.testing.expectEqual(@as(usize, 3), odds.len);
    try std.testing.expectEqual(@as(i32, 1), odds[0]);
}

test "map negate values" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, -2, 3, -4 };

    const negate = struct {
        fn call(n: i32) i32 {
            return -n;
        }
    }.call;

    const negated = try map(allocator, &numbers, negate);
    defer allocator.free(negated);

    try std.testing.expectEqual(@as(i32, -1), negated[0]);
    try std.testing.expectEqual(@as(i32, 2), negated[1]);
}

test "reduce maximum" {
    const numbers = [_]i32{ 3, 7, 2, 9, 1 };

    const max_fn = struct {
        fn call(acc: i32, val: i32) i32 {
            return if (val > acc) val else acc;
        }
    }.call;

    const maximum = reduce(&numbers, numbers[0], max_fn);
    try std.testing.expectEqual(@as(i32, 9), maximum);
}
```

---

## Recipe 7.7: Capturing Variables in Anonymous Functions {#recipe-7-7}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, functions, hashmap, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_7.zig`

### Problem

You want to create functions that capture and remember variables from their surrounding scope, similar to closures in Python.

### Solution

Use structs to manually capture state:

```zig
/// Counter with captured initial value
pub fn makeCounter(initial: i32) type {
    return struct {
        count: i32,

        pub fn init() @This() {
            return .{ .count = initial };
        }

        pub fn increment(self: *@This()) i32 {
            self.count += 1;
            return self.count;
        }

        pub fn get(self: @This()) i32 {
            return self.count;
        }
    };
}
```

### Discussion

### Simple Closure Pattern

Capture a single value:

```zig
pub fn makeAdder(n: i32) type {
    return struct {
        pub fn call(x: i32) i32 {
            return x + n;
        }
    };
}

test "simple closure" {
    const Add5 = makeAdder(5);
    const Add10 = makeAdder(10);

    try std.testing.expectEqual(@as(i32, 15), Add5.call(10));
    try std.testing.expectEqual(@as(i32, 20), Add10.call(10));
}
```

### Closure with Mutable State

Create stateful closures:

```zig
pub fn Accumulator(comptime T: type) type {
    return struct {
        sum: T,

        pub fn init(initial: T) @This() {
            return .{ .sum = initial };
        }

        pub fn add(self: *@This(), value: T) T {
            self.sum += value;
            return self.sum;
        }

        pub fn reset(self: *@This()) void {
            self.sum = 0;
        }
    };
}

test "mutable closure state" {
    var acc = Accumulator(i32).init(0);

    try std.testing.expectEqual(@as(i32, 5), acc.add(5));
    try std.testing.expectEqual(@as(i32, 8), acc.add(3));
    try std.testing.expectEqual(@as(i32, 15), acc.add(7));

    acc.reset();
    try std.testing.expectEqual(@as(i32, 10), acc.add(10));
}
```

### Closure with Multiple Captures

Capture multiple values:

```zig
pub fn makeMultiplier(factor: i32, offset: i32) type {
    return struct {
        pub fn call(x: i32) i32 {
            return x * factor + offset;
        }
    };
}

test "multiple captures" {
    const Transform = makeMultiplier(3, 10);

    try std.testing.expectEqual(@as(i32, 25), Transform.call(5)); // 5 * 3 + 10
    try std.testing.expectEqual(@as(i32, 40), Transform.call(10)); // 10 * 3 + 10
}
```

### Closure Factory

Generate closures dynamically:

```zig
const FilterFn = struct {
    threshold: i32,

    pub fn init(threshold: i32) FilterFn {
        return .{ .threshold = threshold };
    }

    pub fn check(self: FilterFn, value: i32) bool {
        return value > self.threshold;
    }
};

pub fn filterSlice(
    allocator: std.mem.Allocator,
    items: []const i32,
    filter_fn: FilterFn,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (filter_fn.check(item)) {
            try result.append(allocator, item);
        }
    }

    return try result.toOwnedSlice(allocator);
}

test "closure factory" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 5, 10, 15, 20 };

    const filter = FilterFn.init(10);
    const filtered = try filterSlice(allocator, &numbers, filter);
    defer allocator.free(filtered);

    try std.testing.expectEqual(@as(usize, 2), filtered.len);
    try std.testing.expectEqual(@as(i32, 15), filtered[0]);
}
```

### Closure with Allocator

Capture allocator for dynamic operations:

```zig
pub fn StringBuilder(allocator: std.mem.Allocator) type {
    return struct {
        buffer: std.ArrayList(u8),

        const Self = @This();

        pub fn init() Self {
            return .{
                .buffer = std.ArrayList(u8){},
            };
        }

        pub fn append(self: *Self, text: []const u8) !void {
            try self.buffer.appendSlice(allocator, text);
        }

        pub fn build(self: *Self) ![]u8 {
            return try self.buffer.toOwnedSlice(allocator);
        }

        pub fn deinit(self: *Self) void {
            self.buffer.deinit(allocator);
        }
    };
}

test "closure with allocator" {
    const allocator = std.testing.allocator;
    const Builder = StringBuilder(allocator);

    var builder = Builder.init();
    defer builder.deinit();

    try builder.append("Hello");
    try builder.append(" ");
    try builder.append("World");

    const result = try builder.build();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("Hello World", result);
}
```

### Callback with Captured Context

Pass captured state to callbacks:

```zig
const Callback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, i32) void,

    pub fn init(
        context: anytype,
        comptime callback: fn (@TypeOf(context), i32) void,
    ) Callback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, value: i32) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                callback(ptr, value);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
        };
    }

    pub fn invoke(self: Callback, value: i32) void {
        self.call_fn(self.context, value);
    }
};

test "callback with context" {
    const State = struct {
        sum: i32 = 0,

        fn onValue(self: *@This(), value: i32) void {
            self.sum += value;
        }
    };

    var state = State{};
    const callback = Callback.init(&state, State.onValue);

    callback.invoke(5);
    callback.invoke(10);
    callback.invoke(3);

    try std.testing.expectEqual(@as(i32, 18), state.sum);
}
```

### Closure Chain

Chain multiple closures together:

```zig
pub fn Pipeline(comptime T: type) type {
    return struct {
        transforms: []const *const fn (T) T,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            return .{
                .transforms = &[_]*const fn (T) T{},
                .allocator = allocator,
            };
        }

        pub fn add(self: *Self, transform: *const fn (T) T) !void {
            const new_transforms = try self.allocator.alloc(*const fn (T) T, self.transforms.len + 1);
            @memcpy(new_transforms[0..self.transforms.len], self.transforms);
            new_transforms[self.transforms.len] = transform;

            if (self.transforms.len > 0) {
                self.allocator.free(self.transforms);
            }
            self.transforms = new_transforms;
        }

        pub fn execute(self: Self, value: T) T {
            var result = value;
            for (self.transforms) |transform| {
                result = transform(result);
            }
            return result;
        }

        pub fn deinit(self: *Self) void {
            if (self.transforms.len > 0) {
                self.allocator.free(self.transforms);
            }
        }
    };
}

test "closure chain" {
    const allocator = std.testing.allocator;

    var pipeline = Pipeline(i32).init(allocator);
    defer pipeline.deinit();

    const double = struct {
        fn f(x: i32) i32 {
            return x * 2;
        }
    }.f;

    const add10 = struct {
        fn f(x: i32) i32 {
            return x + 10;
        }
    }.f;

    try pipeline.add(&double);
    try pipeline.add(&add10);

    const result = pipeline.execute(5); // (5 * 2) + 10 = 20
    try std.testing.expectEqual(@as(i32, 20), result);
}
```

### Lazy Evaluation Closure

Defer computation until needed:

```zig
pub fn Lazy(comptime T: type) type {
    return struct {
        compute_fn: *const fn () T,
        cached_value: ?T,
        is_computed: bool,

        const Self = @This();

        pub fn init(compute_fn: *const fn () T) Self {
            return .{
                .compute_fn = compute_fn,
                .cached_value = null,
                .is_computed = false,
            };
        }

        pub fn get(self: *Self) T {
            if (!self.is_computed) {
                self.cached_value = self.compute_fn();
                self.is_computed = true;
            }
            return self.cached_value.?;
        }

        pub fn reset(self: *Self) void {
            self.is_computed = false;
            self.cached_value = null;
        }
    };
}

test "lazy evaluation" {
    const expensive = struct {
        var call_count: usize = 0;

        fn compute() i32 {
            call_count += 1;
            return 42;
        }
    };

    var lazy = Lazy(i32).init(&expensive.compute);

    try std.testing.expectEqual(@as(usize, 0), expensive.call_count);

    const value1 = lazy.get();
    try std.testing.expectEqual(@as(i32, 42), value1);
    try std.testing.expectEqual(@as(usize, 1), expensive.call_count);

    const value2 = lazy.get();
    try std.testing.expectEqual(@as(i32, 42), value2);
    try std.testing.expectEqual(@as(usize, 1), expensive.call_count); // Not called again
}
```

### Memoization Pattern

Cache function results:

```zig
pub fn Memoized(comptime Input: type, comptime Output: type) type {
    return struct {
        cache: std.AutoHashMap(Input, Output),
        compute_fn: *const fn (Input) Output,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(
            allocator: std.mem.Allocator,
            compute_fn: *const fn (Input) Output,
        ) Self {
            return .{
                .cache = std.AutoHashMap(Input, Output).init(allocator),
                .compute_fn = compute_fn,
                .allocator = allocator,
            };
        }

        pub fn call(self: *Self, input: Input) !Output {
            if (self.cache.get(input)) |cached| {
                return cached;
            }

            const result = self.compute_fn(input);
            try self.cache.put(input, result);
            return result;
        }

        pub fn deinit(self: *Self) void {
            self.cache.deinit();
        }
    };
}

test "memoization" {
    const fibonacci = struct {
        var call_count: usize = 0;

        fn compute(n: u32) u32 {
            call_count += 1;
            if (n <= 1) return n;
            return n; // Simplified for testing
        }
    };

    const allocator = std.testing.allocator;
    var memo = Memoized(u32, u32).init(allocator, &fibonacci.compute);
    defer memo.deinit();

    _ = try memo.call(5);
    try std.testing.expectEqual(@as(usize, 1), fibonacci.call_count);

    _ = try memo.call(5);
    try std.testing.expectEqual(@as(usize, 1), fibonacci.call_count); // Cached
}
```

### Event Listener Pattern

Capture state for event handlers:

```zig
const EventListener = struct {
    id: usize,
    context: *anyopaque,
    handler: *const fn (*anyopaque, []const u8) void,

    pub fn init(
        id: usize,
        context: anytype,
        comptime handler: fn (@TypeOf(context), []const u8) void,
    ) EventListener {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, data: []const u8) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                handler(ptr, data);
            }
        };

        return .{
            .id = id,
            .context = @ptrCast(context),
            .handler = Wrapper.call,
        };
    }

    pub fn trigger(self: EventListener, data: []const u8) void {
        self.handler(self.context, data);
    }
};

test "event listener" {
    const Logger = struct {
        messages: std.ArrayList([]const u8),
        allocator: std.mem.Allocator,

        fn onEvent(self: *@This(), message: []const u8) void {
            self.messages.append(self.allocator, message) catch unreachable;
        }

        fn deinit(self: *@This()) void {
            self.messages.deinit();
        }
    };

    const allocator = std.testing.allocator;
    var logger = Logger{
        .messages = std.ArrayList([]const u8){},
        .allocator = allocator,
    };
    defer logger.deinit();

    const listener = EventListener.init(1, &logger, Logger.onEvent);

    listener.trigger("event1");
    listener.trigger("event2");

    try std.testing.expectEqual(@as(usize, 2), logger.messages.items.len);
}
```

### Best Practices

**Closure Pattern Selection:**
```zig
// Good: Comptime closure for zero runtime cost
pub fn makeAdder(comptime n: i32) type {
    return struct {
        pub fn call(x: i32) i32 {
            return x + n;
        }
    };
}

// Good: Runtime closure with mutable state
pub fn Counter() type {
    return struct {
        count: i32 = 0,

        pub fn increment(self: *@This()) i32 {
            self.count += 1;
            return self.count;
        }
    };
}
```

**Memory Management:**
- Always provide `deinit()` for closures that allocate
- Use `errdefer` for cleanup on error
- Capture allocators when dynamic allocation is needed
- Document ownership semantics clearly

**Type Safety:**
```zig
// Good: Type-safe context with comptime
pub fn Callback(comptime Context: type) type {
    return struct {
        context: *Context,
        fn_ptr: *const fn (*Context, i32) void,
    };
}

// Less safe: Type-erased with anyopaque
// Use only when generic context is truly needed
```

**Performance Considerations:**
- Comptime closures have zero runtime overhead
- Runtime closures are just struct instances
- Avoid unnecessary heap allocations in closures
- Cache expensive computations with memoization

### Related Functions

- `@TypeOf()` for capturing type information
- `@ptrCast()` and `@alignCast()` for type-erased contexts
- `comptime` for compile-time closure generation
- `std.ArrayList` for dynamic collections in closures
- `std.AutoHashMap` for memoization
- Function pointers `*const fn(T) R`

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_closure
/// Counter with captured initial value
pub fn makeCounter(initial: i32) type {
    return struct {
        count: i32,

        pub fn init() @This() {
            return .{ .count = initial };
        }

        pub fn increment(self: *@This()) i32 {
            self.count += 1;
            return self.count;
        }

        pub fn get(self: @This()) i32 {
            return self.count;
        }
    };
}
// ANCHOR_END: basic_closure

// ANCHOR: runtime_closure
/// Simple adder closure
pub fn makeAdder(n: i32) type {
    return struct {
        pub fn call(x: i32) i32 {
            return x + n;
        }
    };
}

/// Generic accumulator
pub fn Accumulator(comptime T: type) type {
    return struct {
        sum: T,

        pub fn init(initial: T) @This() {
            return .{ .sum = initial };
        }

        pub fn add(self: *@This(), value: T) T {
            self.sum += value;
            return self.sum;
        }

        pub fn reset(self: *@This()) void {
            self.sum = 0;
        }
    };
}

/// Multiplier with multiple captures
pub fn makeMultiplier(factor: i32, offset: i32) type {
    return struct {
        pub fn call(x: i32) i32 {
            return x * factor + offset;
        }
    };
}

/// Filter function with threshold
const FilterFn = struct {
    threshold: i32,

    pub fn init(threshold: i32) FilterFn {
        return .{ .threshold = threshold };
    }

    pub fn check(self: FilterFn, value: i32) bool {
        return value > self.threshold;
    }
};

pub fn filterSlice(
    allocator: std.mem.Allocator,
    items: []const i32,
    filter_fn: FilterFn,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (filter_fn.check(item)) {
            try result.append(allocator, item);
        }
    }

    return try result.toOwnedSlice(allocator);
}
// ANCHOR_END: runtime_closure

// ANCHOR: allocator_closure
/// String builder with captured allocator
pub fn StringBuilder(allocator: std.mem.Allocator) type {
    return struct {
        buffer: std.ArrayList(u8),

        const Self = @This();

        pub fn init() Self {
            return .{
                .buffer = std.ArrayList(u8){},
            };
        }

        pub fn append(self: *Self, text: []const u8) !void {
            try self.buffer.appendSlice(allocator, text);
        }

        pub fn build(self: *Self) ![]u8 {
            return try self.buffer.toOwnedSlice(allocator);
        }

        pub fn deinit(self: *Self) void {
            self.buffer.deinit(allocator);
        }
    };
}
// ANCHOR_END: allocator_closure

/// Callback with type-erased context
const Callback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, i32) void,

    pub fn init(
        context: anytype,
        comptime callback: fn (@TypeOf(context), i32) void,
    ) Callback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, value: i32) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                callback(ptr, value);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
        };
    }

    pub fn invoke(self: Callback, value: i32) void {
        self.call_fn(self.context, value);
    }
};

/// Pipeline for chaining transforms
pub fn Pipeline(comptime T: type) type {
    return struct {
        transforms: []const *const fn (T) T,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            return .{
                .transforms = &[_]*const fn (T) T{},
                .allocator = allocator,
            };
        }

        pub fn add(self: *Self, transform: *const fn (T) T) !void {
            const new_transforms = try self.allocator.alloc(*const fn (T) T, self.transforms.len + 1);
            @memcpy(new_transforms[0..self.transforms.len], self.transforms);
            new_transforms[self.transforms.len] = transform;

            if (self.transforms.len > 0) {
                self.allocator.free(self.transforms);
            }
            self.transforms = new_transforms;
        }

        pub fn execute(self: Self, value: T) T {
            var result = value;
            for (self.transforms) |transform| {
                result = transform(result);
            }
            return result;
        }

        pub fn deinit(self: *Self) void {
            if (self.transforms.len > 0) {
                self.allocator.free(self.transforms);
            }
        }
    };
}

/// Lazy evaluation
pub fn Lazy(comptime T: type) type {
    return struct {
        compute_fn: *const fn () T,
        cached_value: ?T,
        is_computed: bool,

        const Self = @This();

        pub fn init(compute_fn: *const fn () T) Self {
            return .{
                .compute_fn = compute_fn,
                .cached_value = null,
                .is_computed = false,
            };
        }

        pub fn get(self: *Self) T {
            if (!self.is_computed) {
                self.cached_value = self.compute_fn();
                self.is_computed = true;
            }
            return self.cached_value.?;
        }

        pub fn reset(self: *Self) void {
            self.is_computed = false;
            self.cached_value = null;
        }
    };
}

/// Memoization
pub fn Memoized(comptime Input: type, comptime Output: type) type {
    return struct {
        cache: std.AutoHashMap(Input, Output),
        compute_fn: *const fn (Input) Output,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(
            allocator: std.mem.Allocator,
            compute_fn: *const fn (Input) Output,
        ) Self {
            return .{
                .cache = std.AutoHashMap(Input, Output).init(allocator),
                .compute_fn = compute_fn,
                .allocator = allocator,
            };
        }

        pub fn call(self: *Self, input: Input) !Output {
            if (self.cache.get(input)) |cached| {
                return cached;
            }

            const result = self.compute_fn(input);
            try self.cache.put(input, result);
            return result;
        }

        pub fn deinit(self: *Self) void {
            self.cache.deinit();
        }
    };
}

/// Event listener
const EventListener = struct {
    id: usize,
    context: *anyopaque,
    handler: *const fn (*anyopaque, []const u8) void,

    pub fn init(
        id: usize,
        context: anytype,
        comptime handler: fn (@TypeOf(context), []const u8) void,
    ) EventListener {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, data: []const u8) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                handler(ptr, data);
            }
        };

        return .{
            .id = id,
            .context = @ptrCast(context),
            .handler = Wrapper.call,
        };
    }

    pub fn trigger(self: EventListener, data: []const u8) void {
        self.handler(self.context, data);
    }
};

// Tests

test "closure with captured state" {
    const Counter = makeCounter(10);
    var counter = Counter.init();

    try std.testing.expectEqual(@as(i32, 11), counter.increment());
    try std.testing.expectEqual(@as(i32, 12), counter.increment());
    try std.testing.expectEqual(@as(i32, 12), counter.get());
}

test "simple closure" {
    const Add5 = makeAdder(5);
    const Add10 = makeAdder(10);

    try std.testing.expectEqual(@as(i32, 15), Add5.call(10));
    try std.testing.expectEqual(@as(i32, 20), Add10.call(10));
}

test "mutable closure state" {
    var acc = Accumulator(i32).init(0);

    try std.testing.expectEqual(@as(i32, 5), acc.add(5));
    try std.testing.expectEqual(@as(i32, 8), acc.add(3));
    try std.testing.expectEqual(@as(i32, 15), acc.add(7));

    acc.reset();
    try std.testing.expectEqual(@as(i32, 10), acc.add(10));
}

test "multiple captures" {
    const Transform = makeMultiplier(3, 10);

    try std.testing.expectEqual(@as(i32, 25), Transform.call(5)); // 5 * 3 + 10
    try std.testing.expectEqual(@as(i32, 40), Transform.call(10)); // 10 * 3 + 10
}

test "closure factory" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 5, 10, 15, 20 };

    const filter = FilterFn.init(10);
    const filtered = try filterSlice(allocator, &numbers, filter);
    defer allocator.free(filtered);

    try std.testing.expectEqual(@as(usize, 2), filtered.len);
    try std.testing.expectEqual(@as(i32, 15), filtered[0]);
}

test "closure with allocator" {
    const allocator = std.testing.allocator;
    const Builder = StringBuilder(allocator);

    var builder = Builder.init();
    defer builder.deinit();

    try builder.append("Hello");
    try builder.append(" ");
    try builder.append("World");

    const result = try builder.build();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("Hello World", result);
}

test "callback with context" {
    const State = struct {
        sum: i32 = 0,

        fn onValue(self: *@This(), value: i32) void {
            self.sum += value;
        }
    };

    var state = State{};
    const callback = Callback.init(&state, State.onValue);

    callback.invoke(5);
    callback.invoke(10);
    callback.invoke(3);

    try std.testing.expectEqual(@as(i32, 18), state.sum);
}

test "closure chain" {
    const allocator = std.testing.allocator;

    var pipeline = Pipeline(i32).init(allocator);
    defer pipeline.deinit();

    const double = struct {
        fn f(x: i32) i32 {
            return x * 2;
        }
    }.f;

    const add10 = struct {
        fn f(x: i32) i32 {
            return x + 10;
        }
    }.f;

    try pipeline.add(&double);
    try pipeline.add(&add10);

    const result = pipeline.execute(5); // (5 * 2) + 10 = 20
    try std.testing.expectEqual(@as(i32, 20), result);
}

test "lazy evaluation" {
    const expensive = struct {
        var call_count: usize = 0;

        fn compute() i32 {
            call_count += 1;
            return 42;
        }
    };

    var lazy = Lazy(i32).init(&expensive.compute);

    try std.testing.expectEqual(@as(usize, 0), expensive.call_count);

    const value1 = lazy.get();
    try std.testing.expectEqual(@as(i32, 42), value1);
    try std.testing.expectEqual(@as(usize, 1), expensive.call_count);

    const value2 = lazy.get();
    try std.testing.expectEqual(@as(i32, 42), value2);
    try std.testing.expectEqual(@as(usize, 1), expensive.call_count); // Not called again
}

test "memoization" {
    const fibonacci = struct {
        var call_count: usize = 0;

        fn compute(n: u32) u32 {
            call_count += 1;
            if (n <= 1) return n;
            return n; // Simplified for testing
        }
    };

    const allocator = std.testing.allocator;
    var memo = Memoized(u32, u32).init(allocator, &fibonacci.compute);
    defer memo.deinit();

    _ = try memo.call(5);
    try std.testing.expectEqual(@as(usize, 1), fibonacci.call_count);

    _ = try memo.call(5);
    try std.testing.expectEqual(@as(usize, 1), fibonacci.call_count); // Cached
}

test "event listener" {
    const Logger = struct {
        messages: std.ArrayList([]const u8),
        allocator: std.mem.Allocator,

        fn onEvent(self: *@This(), message: []const u8) void {
            self.messages.append(self.allocator, message) catch unreachable;
        }

        fn deinit(self: *@This()) void {
            self.messages.deinit(self.allocator);
        }
    };

    const allocator = std.testing.allocator;
    var logger = Logger{
        .messages = std.ArrayList([]const u8){},
        .allocator = allocator,
    };
    defer logger.deinit();

    const listener = EventListener.init(1, &logger, Logger.onEvent);

    listener.trigger("event1");
    listener.trigger("event2");

    try std.testing.expectEqual(@as(usize, 2), logger.messages.items.len);
}

test "counter with different initial" {
    const Counter1 = makeCounter(0);
    const Counter2 = makeCounter(100);

    var c1 = Counter1.init();
    var c2 = Counter2.init();

    try std.testing.expectEqual(@as(i32, 1), c1.increment());
    try std.testing.expectEqual(@as(i32, 101), c2.increment());
}

test "accumulator with floats" {
    var acc = Accumulator(f32).init(0.0);

    try std.testing.expectEqual(@as(f32, 1.5), acc.add(1.5));
    try std.testing.expectEqual(@as(f32, 4.0), acc.add(2.5));
}

test "filter with different threshold" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    const filter = FilterFn.init(3);
    const filtered = try filterSlice(allocator, &numbers, filter);
    defer allocator.free(filtered);

    try std.testing.expectEqual(@as(usize, 2), filtered.len);
    try std.testing.expectEqual(@as(i32, 4), filtered[0]);
    try std.testing.expectEqual(@as(i32, 5), filtered[1]);
}

test "lazy reset" {
    const compute = struct {
        var value: i32 = 10;

        fn get() i32 {
            value += 5;
            return value;
        }
    };

    var lazy = Lazy(i32).init(&compute.get);

    try std.testing.expectEqual(@as(i32, 15), lazy.get());
    try std.testing.expectEqual(@as(i32, 15), lazy.get()); // Cached

    lazy.reset();
    try std.testing.expectEqual(@as(i32, 20), lazy.get()); // Recomputed
}
```

---

## Recipe 7.8: Making an N-Argument Callable Work As a Callable with Fewer Arguments {#recipe-7-8}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, functions, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_8.zig`

### Problem

You want to create a version of a function with some arguments pre-filled, similar to Python's `functools.partial`.

### Solution

Use structs to capture pre-filled arguments:

```zig
/// Power function
pub fn power(base: i32, exponent: i32) i32 {
    return std.math.powi(i32, base, exponent) catch unreachable;
}

/// Partial power application
pub fn partial_power(exponent: i32) type {
    return struct {
        pub fn call(base: i32) i32 {
            return power(base, exponent);
        }
    };
}

/// Basic math functions
fn add(a: i32, b: i32) i32 {
    return a + b;
}

fn multiply(a: i32, b: i32) i32 {
    return a * b;
}

/// Runtime partial add
pub fn PartialAdd(comptime T: type) type {
    return struct {
        value: T,

        pub fn init(value: T) @This() {
            return .{ .value = value };
        }

        pub fn call(self: @This(), other: T) T {
            return self.value + other;
        }
    };
}
```

### Discussion

### Generic Partial Application

Create a generic partial applicator:

```zig
pub fn Partial2(
    comptime Func: type,
    comptime arg1_val: anytype,
) type {
    return struct {
        pub fn call(arg2: anytype) @TypeOf(Func(arg1_val, arg2)) {
            return Func(arg1_val, arg2);
        }
    };
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

fn multiply(a: i32, b: i32) i32 {
    return a * b;
}

test "generic partial" {
    const add5 = Partial2(@TypeOf(add), 5);
    const times10 = Partial2(@TypeOf(multiply), 10);

    try std.testing.expectEqual(@as(i32, 15), add5.call(10));
    try std.testing.expectEqual(@as(i32, 50), times10.call(5));
}
```

### Runtime Partial Application

Capture arguments at runtime:

```zig
pub fn PartialAdd(comptime T: type) type {
    return struct {
        value: T,

        pub fn init(value: T) @This() {
            return .{ .value = value };
        }

        pub fn call(self: @This(), other: T) T {
            return self.value + other;
        }
    };
}

test "runtime partial" {
    const add5 = PartialAdd(i32).init(5);
    const add10 = PartialAdd(i32).init(10);

    try std.testing.expectEqual(@as(i32, 15), add5.call(10));
    try std.testing.expectEqual(@as(i32, 25), add10.call(15));
}
```

### Currying Pattern

Transform multi-argument function into nested single-argument functions:

```zig
pub fn curry3(
    comptime F: type,
) type {
    return struct {
        pub fn call(a: anytype) type {
            return struct {
                pub fn call2(b: anytype) type {
                    return struct {
                        pub fn call3(c: anytype) @TypeOf(F(a, b, c)) {
                            return F(a, b, c);
                        }
                    };
                }
            };
        }
    };
}

fn add3(a: i32, b: i32, c: i32) i32 {
    return a + b + c;
}

test "currying" {
    const curried = curry3(@TypeOf(add3));

    const step1 = curried.call(1);
    const step2 = step1.call2(2);
    const result = step2.call3(3);

    try std.testing.expectEqual(@as(i32, 6), result);
}
```

### Partial with String Formatting

Pre-fill format strings:

```zig
pub fn PartialFormat(comptime fmt: []const u8) type {
    return struct {
        pub fn call(
            allocator: std.mem.Allocator,
            args: anytype,
        ) ![]u8 {
            return try std.fmt.allocPrint(allocator, fmt, args);
        }
    };
}

test "partial format" {
    const allocator = std.testing.allocator;

    const format_name = PartialFormat("Hello, {s}!");
    const result = try format_name.call(allocator, .{"World"});
    defer allocator.free(result);

    try std.testing.expectEqualStrings("Hello, World!", result);
}
```

### Partial Application for Comparison

Pre-fill comparison thresholds:

```zig
pub fn GreaterThan(comptime T: type) type {
    return struct {
        threshold: T,

        pub fn init(threshold: T) @This() {
            return .{ .threshold = threshold };
        }

        pub fn check(self: @This(), value: T) bool {
            return value > self.threshold;
        }
    };
}

pub fn filter(
    allocator: std.mem.Allocator,
    items: []const i32,
    predicate: anytype,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (predicate.check(item)) {
            try result.append(allocator, item);
        }
    }

    return try result.toOwnedSlice(allocator);
}

test "partial comparison" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 5, 10, 15, 20 };

    const gt10 = GreaterThan(i32).init(10);
    const filtered = try filter(allocator, &numbers, gt10);
    defer allocator.free(filtered);

    try std.testing.expectEqual(@as(usize, 2), filtered.len);
    try std.testing.expectEqual(@as(i32, 15), filtered[0]);
}
```

### Partial with Error Handling

Pre-fill error handling strategy:

```zig
pub fn PartialTry(comptime ErrorSet: type, comptime T: type) type {
    return struct {
        fallback: T,

        pub fn init(fallback: T) @This() {
            return .{ .fallback = fallback };
        }

        pub fn call(self: @This(), result: ErrorSet!T) T {
            return result catch self.fallback;
        }
    };
}

fn mayFail(value: i32) !i32 {
    if (value < 0) return error.Negative;
    return value * 2;
}

test "partial error handling" {
    const safe_double = PartialTry(error{Negative}, i32).init(0);

    try std.testing.expectEqual(@as(i32, 10), safe_double.call(mayFail(5)));
    try std.testing.expectEqual(@as(i32, 0), safe_double.call(mayFail(-5)));
}
```

### Bind First Arguments

Bind multiple leading arguments:

```zig
pub fn BindFirst2(comptime T1: type, comptime T2: type) type {
    return struct {
        arg1: T1,
        arg2: T2,

        pub fn init(arg1: T1, arg2: T2) @This() {
            return .{ .arg1 = arg1, .arg2 = arg2 };
        }

        pub fn call(
            self: @This(),
            func: anytype,
            arg3: anytype,
        ) @TypeOf(func(self.arg1, self.arg2, arg3)) {
            return func(self.arg1, self.arg2, arg3);
        }
    };
}

fn format3(prefix: []const u8, middle: []const u8, suffix: []const u8) []const u8 {
    _ = prefix;
    _ = middle;
    return suffix; // Simplified
}

test "bind first arguments" {
    const bound = BindFirst2([]const u8, []const u8).init("Hello", "beautiful");

    const result = bound.call(format3, "World");
    try std.testing.expectEqualStrings("World", result);
}
```

### Partial Application Builder

Chain partial applications:

```zig
pub fn FunctionBuilder(comptime Ret: type) type {
    return struct {
        const Self = @This();

        pub fn arg(comptime T: type, value: T) type {
            return struct {
                captured: T,

                pub fn init() @This() {
                    return .{ .captured = value };
                }

                pub fn apply(self: @This(), func: fn (T) Ret) Ret {
                    return func(self.captured);
                }
            };
        }
    };
}

test "function builder" {
    const double = struct {
        fn f(x: i32) i32 {
            return x * 2;
        }
    }.f;

    const Builder = FunctionBuilder(i32);
    const partial = Builder.arg(i32, 5).init();

    try std.testing.expectEqual(@as(i32, 10), partial.apply(double));
}
```

### Method Partial Application

Bind object methods:

```zig
pub fn Calculator() type {
    return struct {
        base: i32,

        const Self = @This();

        pub fn init(base: i32) Self {
            return .{ .base = base };
        }

        pub fn add(self: Self, value: i32) i32 {
            return self.base + value;
        }

        pub fn multiply(self: Self, value: i32) i32 {
            return self.base * value;
        }

        pub fn partialAdd(self: Self) type {
            return struct {
                calc: Self,

                pub fn init() @This() {
                    return .{ .calc = self };
                }

                pub fn call(this: @This(), value: i32) i32 {
                    return this.calc.add(value);
                }
            };
        }
    };
}

test "method partial" {
    const calc = Calculator().init(10);

    const AddTo10 = calc.partialAdd().init();
    try std.testing.expectEqual(@as(i32, 15), AddTo10.call(5));
}
```

### Reverse Partial Application

Bind last argument instead of first:

```zig
pub fn PartialLast(comptime T: type) type {
    return struct {
        last_arg: T,

        pub fn init(last_arg: T) @This() {
            return .{ .last_arg = last_arg };
        }

        pub fn call(
            self: @This(),
            func: anytype,
            first_arg: anytype,
        ) @TypeOf(func(first_arg, self.last_arg)) {
            return func(first_arg, self.last_arg);
        }
    };
}

fn subtract(a: i32, b: i32) i32 {
    return a - b;
}

test "reverse partial" {
    const subtract5 = PartialLast(i32).init(5);

    try std.testing.expectEqual(@as(i32, 5), subtract5.call(subtract, 10));
    try std.testing.expectEqual(@as(i32, 15), subtract5.call(subtract, 20));
}
```

### Partial with Allocator

Pre-fill allocator for functions:

```zig
pub fn WithAllocator(allocator: std.mem.Allocator) type {
    return struct {
        pub fn duplicate(text: []const u8) ![]u8 {
            return try allocator.dupe(u8, text);
        }

        pub fn format(comptime fmt: []const u8, args: anytype) ![]u8 {
            return try std.fmt.allocPrint(allocator, fmt, args);
        }
    };
}

test "partial allocator" {
    const allocator = std.testing.allocator;
    const Mem = WithAllocator(allocator);

    const dup = try Mem.duplicate("hello");
    defer allocator.free(dup);
    try std.testing.expectEqualStrings("hello", dup);

    const formatted = try Mem.format("Value: {}", .{42});
    defer allocator.free(formatted);
    try std.testing.expectEqualStrings("Value: 42", formatted);
}
```

### Partial Application Combinator

Combine multiple partial applications:

```zig
pub fn Compose(comptime F: type, comptime G: type) type {
    return struct {
        pub fn call(x: anytype) @TypeOf(F(G(x))) {
            return F(G(x));
        }
    };
}

fn double(x: i32) i32 {
    return x * 2;
}

fn addTen(x: i32) i32 {
    return x + 10;
}

test "composition" {
    const doubleAndAdd = Compose(@TypeOf(addTen), @TypeOf(double));

    // (5 * 2) + 10 = 20
    try std.testing.expectEqual(@as(i32, 20), doubleAndAdd.call(5));
}
```

### Best Practices

**Choosing Between Comptime and Runtime:**
```zig
// Good: Comptime when values known at compile time
pub fn makeAdder(comptime n: i32) type {
    return struct {
        pub fn call(x: i32) i32 {
            return x + n;
        }
    };
}

// Good: Runtime when values known only at runtime
pub fn Adder() type {
    return struct {
        n: i32,

        pub fn init(n: i32) @This() {
            return .{ .n = n };
        }

        pub fn call(self: @This(), x: i32) i32 {
            return x + self.n;
        }
    };
}
```

**Type Safety:**
- Use comptime parameters for maximum type safety
- Leverage Zig's type system to catch errors early
- Document expected function signatures

**Performance:**
- Comptime partial application has zero runtime overhead
- Runtime partial application is just struct field access
- No hidden allocations or indirection

**API Design:**
```zig
// Good: Clear, self-documenting
const add5 = PartialAdd(i32).init(5);
result = add5.call(10);

// Less clear: Generic but harder to understand
const partial = Partial(add, 5);
result = partial.call(10);
```

### Related Functions

- `comptime` for compile-time partial application
- `@TypeOf()` for type inference
- Function pointers for flexible partial application
- Struct initialization for capturing arguments
- `anytype` for generic partial application

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_partial
/// Power function
pub fn power(base: i32, exponent: i32) i32 {
    return std.math.powi(i32, base, exponent) catch unreachable;
}

/// Partial power application
pub fn partial_power(exponent: i32) type {
    return struct {
        pub fn call(base: i32) i32 {
            return power(base, exponent);
        }
    };
}

/// Basic math functions
fn add(a: i32, b: i32) i32 {
    return a + b;
}

fn multiply(a: i32, b: i32) i32 {
    return a * b;
}

/// Runtime partial add
pub fn PartialAdd(comptime T: type) type {
    return struct {
        value: T,

        pub fn init(value: T) @This() {
            return .{ .value = value };
        }

        pub fn call(self: @This(), other: T) T {
            return self.value + other;
        }
    };
}
// ANCHOR_END: basic_partial

// ANCHOR: runtime_partial
/// Three-argument function for currying
fn add3(a: i32, b: i32, c: i32) i32 {
    return a + b + c;
}

/// Partial format
pub fn PartialFormat(comptime fmt: []const u8) type {
    return struct {
        pub fn call(
            allocator: std.mem.Allocator,
            args: anytype,
        ) ![]u8 {
            return try std.fmt.allocPrint(allocator, fmt, args);
        }
    };
}

/// Greater than predicate
pub fn GreaterThan(comptime T: type) type {
    return struct {
        threshold: T,

        pub fn init(threshold: T) @This() {
            return .{ .threshold = threshold };
        }

        pub fn check(self: @This(), value: T) bool {
            return value > self.threshold;
        }
    };
}

pub fn filter(
    allocator: std.mem.Allocator,
    items: []const i32,
    predicate: anytype,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (predicate.check(item)) {
            try result.append(allocator, item);
        }
    }

    return try result.toOwnedSlice(allocator);
}
// ANCHOR_END: runtime_partial

// ANCHOR: advanced_partial
/// Partial error handling
pub fn PartialTry(comptime ErrorSet: type, comptime T: type) type {
    return struct {
        fallback: T,

        pub fn init(fallback: T) @This() {
            return .{ .fallback = fallback };
        }

        pub fn call(self: @This(), result: ErrorSet!T) T {
            return result catch self.fallback;
        }
    };
}

fn mayFail(value: i32) !i32 {
    if (value < 0) return error.Negative;
    return value * 2;
}

/// Bind first two arguments
pub fn BindFirst2(comptime T1: type, comptime T2: type) type {
    return struct {
        arg1: T1,
        arg2: T2,

        pub fn init(arg1: T1, arg2: T2) @This() {
            return .{ .arg1 = arg1, .arg2 = arg2 };
        }

        pub fn call(
            self: @This(),
            func: anytype,
            arg3: anytype,
        ) @TypeOf(func(self.arg1, self.arg2, arg3)) {
            return func(self.arg1, self.arg2, arg3);
        }
    };
}

fn add3args(a: i32, b: i32, c: i32) i32 {
    return a + b + c;
}

/// Function builder
pub fn FunctionBuilder(comptime Ret: type) type {
    return struct {
        const Self = @This();

        pub fn arg(comptime T: type, value: T) type {
            return struct {
                captured: T,

                pub fn init() @This() {
                    return .{ .captured = value };
                }

                pub fn apply(self: @This(), func: fn (T) Ret) Ret {
                    return func(self.captured);
                }
            };
        }
    };
}

/// Calculator with partial methods
pub fn Calculator() type {
    return struct {
        base: i32,

        const Self = @This();

        pub fn init(base: i32) Self {
            return .{ .base = base };
        }

        pub fn add_impl(self: Self, value: i32) i32 {
            return self.base + value;
        }

        pub fn multiply_impl(self: Self, value: i32) i32 {
            return self.base * value;
        }

        pub const PartialAdder = struct {
            calc: Self,

            pub fn init(calc: Self) @This() {
                return .{ .calc = calc };
            }

            pub fn call(this: @This(), value: i32) i32 {
                return this.calc.add_impl(value);
            }
        };

        pub fn partialAdd(self: Self) PartialAdder {
            return PartialAdder.init(self);
        }
    };
}

/// Reverse partial application
pub fn PartialLast(comptime T: type) type {
    return struct {
        last_arg: T,

        pub fn init(last_arg: T) @This() {
            return .{ .last_arg = last_arg };
        }

        pub fn call(
            self: @This(),
            func: anytype,
            first_arg: anytype,
        ) @TypeOf(func(first_arg, self.last_arg)) {
            return func(first_arg, self.last_arg);
        }
    };
}

fn subtract(a: i32, b: i32) i32 {
    return a - b;
}
// ANCHOR_END: advanced_partial

/// Partial with allocator
pub fn WithAllocator(allocator: std.mem.Allocator) type {
    return struct {
        pub fn duplicate(text: []const u8) ![]u8 {
            return try allocator.dupe(u8, text);
        }

        pub fn format(comptime fmt: []const u8, args: anytype) ![]u8 {
            return try std.fmt.allocPrint(allocator, fmt, args);
        }
    };
}

/// Function composition
pub fn Compose(
    comptime f: fn (i32) i32,
    comptime g: fn (i32) i32,
) type {
    return struct {
        pub fn call(x: i32) i32 {
            return f(g(x));
        }
    };
}

fn double(x: i32) i32 {
    return x * 2;
}

fn addTen(x: i32) i32 {
    return x + 10;
}

/// Multiply partial
pub fn PartialMultiply(comptime T: type) type {
    return struct {
        factor: T,

        pub fn init(factor: T) @This() {
            return .{ .factor = factor };
        }

        pub fn call(self: @This(), value: T) T {
            return self.factor * value;
        }
    };
}

// Tests

test "partial application" {
    const square = partial_power(2);
    const cube = partial_power(3);

    try std.testing.expectEqual(@as(i32, 25), square.call(5));
    try std.testing.expectEqual(@as(i32, 125), cube.call(5));
}

test "runtime partial" {
    const add5 = PartialAdd(i32).init(5);
    const add10 = PartialAdd(i32).init(10);

    try std.testing.expectEqual(@as(i32, 15), add5.call(10));
    try std.testing.expectEqual(@as(i32, 25), add10.call(15));
}

test "partial format" {
    const allocator = std.testing.allocator;

    const format_name = PartialFormat("Hello, {s}!");
    const result = try format_name.call(allocator, .{"World"});
    defer allocator.free(result);

    try std.testing.expectEqualStrings("Hello, World!", result);
}

test "partial comparison" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 5, 10, 15, 20 };

    const gt10 = GreaterThan(i32).init(10);
    const filtered = try filter(allocator, &numbers, gt10);
    defer allocator.free(filtered);

    try std.testing.expectEqual(@as(usize, 2), filtered.len);
    try std.testing.expectEqual(@as(i32, 15), filtered[0]);
}

test "partial error handling" {
    const safe_double = PartialTry(error{Negative}, i32).init(0);

    try std.testing.expectEqual(@as(i32, 10), safe_double.call(mayFail(5)));
    try std.testing.expectEqual(@as(i32, 0), safe_double.call(mayFail(-5)));
}

test "bind first arguments" {
    const bound = BindFirst2(i32, i32).init(10, 20);

    const result = bound.call(add3args, 30);
    try std.testing.expectEqual(@as(i32, 60), result);
}

test "function builder" {
    const double_fn = struct {
        fn f(x: i32) i32 {
            return x * 2;
        }
    }.f;

    const Builder = FunctionBuilder(i32);
    const partial = Builder.arg(i32, 5).init();

    try std.testing.expectEqual(@as(i32, 10), partial.apply(double_fn));
}

test "method partial" {
    const calc = Calculator().init(10);

    const add_to_10 = calc.partialAdd();
    try std.testing.expectEqual(@as(i32, 15), add_to_10.call(5));
}

test "reverse partial" {
    const subtract5 = PartialLast(i32).init(5);

    try std.testing.expectEqual(@as(i32, 5), subtract5.call(subtract, 10));
    try std.testing.expectEqual(@as(i32, 15), subtract5.call(subtract, 20));
}

test "partial allocator" {
    const allocator = std.testing.allocator;
    const Mem = WithAllocator(allocator);

    const dup = try Mem.duplicate("hello");
    defer allocator.free(dup);
    try std.testing.expectEqualStrings("hello", dup);

    const formatted = try Mem.format("Value: {}", .{42});
    defer allocator.free(formatted);
    try std.testing.expectEqualStrings("Value: 42", formatted);
}

test "composition" {
    const doubleAndAdd = Compose(addTen, double);

    // (5 * 2) + 10 = 20
    try std.testing.expectEqual(@as(i32, 20), doubleAndAdd.call(5));
}

test "partial multiply" {
    const times3 = PartialMultiply(i32).init(3);
    const times5 = PartialMultiply(i32).init(5);

    try std.testing.expectEqual(@as(i32, 15), times3.call(5));
    try std.testing.expectEqual(@as(i32, 25), times5.call(5));
}

test "multiple partial instances" {
    const add2 = PartialAdd(i32).init(2);
    const add7 = PartialAdd(i32).init(7);

    try std.testing.expectEqual(@as(i32, 12), add2.call(10));
    try std.testing.expectEqual(@as(i32, 17), add7.call(10));
}

test "partial with floats" {
    const add_half = PartialAdd(f32).init(0.5);

    try std.testing.expectEqual(@as(f32, 5.5), add_half.call(5.0));
}

test "filter with different thresholds" {
    const allocator = std.testing.allocator;
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    const gt2 = GreaterThan(i32).init(2);
    const filtered = try filter(allocator, &numbers, gt2);
    defer allocator.free(filtered);

    try std.testing.expectEqual(@as(usize, 3), filtered.len);
}
```

---

## Recipe 7.9: Replacing Single Method Classes with Functions {#recipe-7-9}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, functions, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_9.zig`

### Problem

You have a "class" with a single method and want a simpler, more idiomatic Zig approach.

### Solution

Use function pointers with context instead of classes:

```zig
// Anchor 'basic_single_method' not found in ../../../code/03-advanced/07-functions/recipe_7_9.zig
```

### Discussion

### Simple Function Pointer Pattern

For stateless operations, use plain function pointers:

```zig
const TransformFn = *const fn ([]const u8) []const u8;

pub fn applyTransform(input: []const u8, transform: TransformFn) []const u8 {
    return transform(input);
}

fn toUpper(s: []const u8) []const u8 {
    _ = s;
    return "UPPER"; // Simplified
}

fn toLower(s: []const u8) []const u8 {
    _ = s;
    return "lower"; // Simplified
}

test "function pointers" {
    try std.testing.expectEqualStrings("UPPER", applyTransform("test", toUpper));
    try std.testing.expectEqualStrings("lower", applyTransform("TEST", toLower));
}
```

### Comparator Pattern

Replace comparator classes with function pointers:

```zig
const CompareFn = *const fn (*anyopaque, *anyopaque) bool;

pub fn sortWithComparator(
    items: []i32,
    context: *anyopaque,
    compare: CompareFn,
) void {
    // Simple bubble sort
    for (items, 0..) |_, i| {
        for (items[0 .. items.len - i - 1], 0..) |_, j| {
            const a = @as(*i32, @ptrCast(@alignCast(&items[j])));
            const b = @as(*i32, @ptrCast(@alignCast(&items[j + 1])));
            if (!compare(@ptrCast(a), @ptrCast(b))) {
                const temp = items[j];
                items[j] = items[j + 1];
                items[j + 1] = temp;
            }
        }
    }
    _ = context;
}

test "comparator pattern" {
    var numbers = [_]i32{ 5, 2, 8, 1, 9 };

    const ascending = struct {
        fn cmp(a: *anyopaque, b: *anyopaque) bool {
            const x: *i32 = @ptrCast(@alignCast(a));
            const y: *i32 = @ptrCast(@alignCast(b));
            return x.* < y.*;
        }
    }.cmp;

    var ctx: u8 = 0;
    sortWithComparator(&numbers, @ptrCast(&ctx), ascending);

    try std.testing.expectEqual(@as(i32, 1), numbers[0]);
    try std.testing.expectEqual(@as(i32, 9), numbers[4]);
}
```

### Strategy Pattern

Replace strategy classes with function pointers:

```zig
const Strategy = struct {
    context: *anyopaque,
    execute_fn: *const fn (*anyopaque, i32, i32) i32,

    pub fn init(
        context: anytype,
        comptime execute_fn: fn (@TypeOf(context), i32, i32) i32,
    ) Strategy {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, a: i32, b: i32) i32 {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                return execute_fn(ptr, a, b);
            }
        };

        return .{
            .context = @ptrCast(context),
            .execute_fn = Wrapper.call,
        };
    }

    pub fn execute(self: Strategy, a: i32, b: i32) i32 {
        return self.execute_fn(self.context, a, b);
    }
};

test "strategy pattern" {
    const AddStrategy = struct {
        bonus: i32,

        fn run(self: *@This(), a: i32, b: i32) i32 {
            return a + b + self.bonus;
        }
    };

    var add_ctx = AddStrategy{ .bonus = 10 };
    const strategy = Strategy.init(&add_ctx, AddStrategy.run);

    try std.testing.expectEqual(@as(i32, 25), strategy.execute(5, 10));
}
```

### Command Pattern

Replace command objects with functions:

```zig
const Command = struct {
    context: *anyopaque,
    execute_fn: *const fn (*anyopaque) void,

    pub fn init(
        context: anytype,
        comptime execute_fn: fn (@TypeOf(context)) void,
    ) Command {
        const Wrapper = struct {
            fn call(ctx: *anyopaque) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                execute_fn(ptr);
            }
        };

        return .{
            .context = @ptrCast(context),
            .execute_fn = Wrapper.call,
        };
    }

    pub fn execute(self: Command) void {
        self.execute_fn(self.context);
    }
};

test "command pattern" {
    const PrintCommand = struct {
        message: []const u8,
        count: *usize,

        fn run(self: *@This()) void {
            _ = self.message;
            self.count.* += 1;
        }
    };

    var execution_count: usize = 0;
    var cmd_ctx = PrintCommand{
        .message = "Hello",
        .count = &execution_count,
    };
    const command = Command.init(&cmd_ctx, PrintCommand.run);

    command.execute();
    command.execute();

    try std.testing.expectEqual(@as(usize, 2), execution_count);
}
```

### Callable Pattern

Generic callable with return value:

```zig
pub fn Callable(comptime Ret: type) type {
    return struct {
        context: *anyopaque,
        call_fn: *const fn (*anyopaque) Ret,

        pub fn init(
            context: anytype,
            comptime call_fn: fn (@TypeOf(context)) Ret,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque) Ret {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    return call_fn(ptr);
                }
            };

            return .{
                .context = @ptrCast(context),
                .call_fn = Wrapper.call,
            };
        }

        pub fn call(self: @This()) Ret {
            return self.call_fn(self.context);
        }
    };
}

test "callable pattern" {
    const Counter = struct {
        value: i32,

        fn get(self: *@This()) i32 {
            self.value += 1;
            return self.value;
        }
    };

    var counter = Counter{ .value = 0 };
    const callable = Callable(i32).init(&counter, Counter.get);

    try std.testing.expectEqual(@as(i32, 1), callable.call());
    try std.testing.expectEqual(@as(i32, 2), callable.call());
}
```

### Predicate Pattern

Replace predicate classes:

```zig
const Predicate = struct {
    context: *anyopaque,
    test_fn: *const fn (*anyopaque, i32) bool,

    pub fn init(
        context: anytype,
        comptime test_fn: fn (@TypeOf(context), i32) bool,
    ) Predicate {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, value: i32) bool {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                return test_fn(ptr, value);
            }
        };

        return .{
            .context = @ptrCast(context),
            .test_fn = Wrapper.call,
        };
    }

    pub fn test_(self: Predicate, value: i32) bool {
        return self.test_fn(self.context, value);
    }
};

pub fn filterWithPredicate(
    allocator: std.mem.Allocator,
    items: []const i32,
    predicate: Predicate,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (predicate.test_(item)) {
            try result.append(allocator, item);
        }
    }

    return try result.toOwnedSlice(allocator);
}

test "predicate pattern" {
    const allocator = std.testing.allocator;

    const RangePredicate = struct {
        min: i32,
        max: i32,

        fn inRange(self: *@This(), value: i32) bool {
            return value >= self.min and value <= self.max;
        }
    };

    var range = RangePredicate{ .min = 5, .max = 15 };
    const predicate = Predicate.init(&range, RangePredicate.inRange);

    const numbers = [_]i32{ 1, 7, 12, 20, 10 };
    const filtered = try filterWithPredicate(allocator, &numbers, predicate);
    defer allocator.free(filtered);

    try std.testing.expectEqual(@as(usize, 3), filtered.len);
}
```

### Factory Pattern

Replace factory classes with functions:

```zig
pub fn Factory(comptime T: type) type {
    return struct {
        context: *anyopaque,
        create_fn: *const fn (*anyopaque) T,

        pub fn init(
            context: anytype,
            comptime create_fn: fn (@TypeOf(context)) T,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque) T {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    return create_fn(ptr);
                }
            };

            return .{
                .context = @ptrCast(context),
                .create_fn = Wrapper.call,
            };
        }

        pub fn create(self: @This()) T {
            return self.create_fn(self.context);
        }
    };
}

test "factory pattern" {
    const Config = struct {
        default_value: i32,

        fn createInstance(self: *@This()) i32 {
            return self.default_value * 2;
        }
    };

    var config = Config{ .default_value = 21 };
    const factory = Factory(i32).init(&config, Config.createInstance);

    try std.testing.expectEqual(@as(i32, 42), factory.create());
}
```

### Handler Pattern

Replace event handler classes:

```zig
pub fn Handler(comptime Event: type) type {
    return struct {
        context: *anyopaque,
        handle_fn: *const fn (*anyopaque, Event) void,

        pub fn init(
            context: anytype,
            comptime handle_fn: fn (@TypeOf(context), Event) void,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque, event: Event) void {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    handle_fn(ptr, event);
                }
            };

            return .{
                .context = @ptrCast(context),
                .handle_fn = Wrapper.call,
            };
        }

        pub fn handle(self: @This(), event: Event) void {
            self.handle_fn(self.context, event);
        }
    };
}

const KeyEvent = struct {
    key: u8,
    pressed: bool,
};

test "handler pattern" {
    const KeyLogger = struct {
        count: *usize,

        fn onKey(self: *@This(), event: KeyEvent) void {
            if (event.pressed) {
                self.count.* += 1;
            }
        }
    };

    var press_count: usize = 0;
    var logger = KeyLogger{ .count = &press_count };
    const handler = Handler(KeyEvent).init(&logger, KeyLogger.onKey);

    handler.handle(.{ .key = 'A', .pressed = true });
    handler.handle(.{ .key = 'B', .pressed = false });
    handler.handle(.{ .key = 'C', .pressed = true });

    try std.testing.expectEqual(@as(usize, 2), press_count);
}
```

### Visitor Pattern

Replace visitor classes:

```zig
pub fn Visitor(comptime T: type) type {
    return struct {
        context: *anyopaque,
        visit_fn: *const fn (*anyopaque, T) void,

        pub fn init(
            context: anytype,
            comptime visit_fn: fn (@TypeOf(context), T) void,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque, item: T) void {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    visit_fn(ptr, item);
                }
            };

            return .{
                .context = @ptrCast(context),
                .visit_fn = Wrapper.call,
            };
        }

        pub fn visit(self: @This(), item: T) void {
            self.visit_fn(self.context, item);
        }
    };
}

test "visitor pattern" {
    const Accumulator = struct {
        sum: *i32,

        fn visitNumber(self: *@This(), n: i32) void {
            self.sum.* += n;
        }
    };

    var total: i32 = 0;
    var acc = Accumulator{ .sum = &total };
    const visitor = Visitor(i32).init(&acc, Accumulator.visitNumber);

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    for (numbers) |n| {
        visitor.visit(n);
    }

    try std.testing.expectEqual(@as(i32, 15), total);
}
```

### Transformer Pattern

Replace transformer classes:

```zig
pub fn Transformer(comptime In: type, comptime Out: type) type {
    return struct {
        context: *anyopaque,
        transform_fn: *const fn (*anyopaque, In) Out,

        pub fn init(
            context: anytype,
            comptime transform_fn: fn (@TypeOf(context), In) Out,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque, input: In) Out {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    return transform_fn(ptr, input);
                }
            };

            return .{
                .context = @ptrCast(context),
                .transform_fn = Wrapper.call,
            };
        }

        pub fn transform(self: @This(), input: In) Out {
            return self.transform_fn(self.context, input);
        }
    };
}

test "transformer pattern" {
    const Multiplier = struct {
        factor: i32,

        fn apply(self: *@This(), value: i32) i32 {
            return value * self.factor;
        }
    };

    var multiplier = Multiplier{ .factor = 3 };
    const transformer = Transformer(i32, i32).init(&multiplier, Multiplier.apply);

    try std.testing.expectEqual(@as(i32, 15), transformer.transform(5));
    try std.testing.expectEqual(@as(i32, 30), transformer.transform(10));
}
```

### Best Practices

**When to Use Function Pointers:**
```zig
// Good: Single method with context
const Handler = struct {
    context: *anyopaque,
    handle_fn: *const fn (*anyopaque, Event) void,
};

// Overkill: Multiple related methods - use struct
const FileHandler = struct {
    open: fn() void,
    read: fn() []u8,
    write: fn([]u8) void,
    close: fn() void,
};
```

**Type Safety:**
- Use typed contexts when possible
- Type-erase only when necessary
- Document expected context types

**Performance:**
- Function pointers have minimal overhead
- Type-erased contexts require runtime casting
- Consider comptime alternatives when possible

**API Clarity:**
```zig
// Good: Clear intent
pub fn processWithValidator(data: []const u8, validator: Validator) void

// Less clear: Generic function pointer
pub fn process(data: []const u8, fn_ptr: *const fn([]const u8) bool) void
```

### Related Functions

- `*const fn(T) R` for function pointer types
- `@ptrCast()` and `@alignCast()` for type erasure
- `*anyopaque` for generic contexts
- `@TypeOf()` for context type inference
- Comptime wrappers for type-safe erasure

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_pattern
/// Generic validator pattern
const Validator = struct {
    context: *anyopaque,
    validate_fn: *const fn (*anyopaque, []const u8) bool,

    pub fn init(
        context: anytype,
        comptime validate_fn: fn (@TypeOf(context), []const u8) bool,
    ) Validator {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, input: []const u8) bool {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                return validate_fn(ptr, input);
            }
        };

        return .{
            .context = @ptrCast(context),
            .validate_fn = Wrapper.call,
        };
    }

    pub fn validate(self: Validator, input: []const u8) bool {
        return self.validate_fn(self.context, input);
    }
};
// ANCHOR_END: basic_pattern

// ANCHOR: function_pointers
/// Function pointer type
const TransformFn = *const fn ([]const u8) []const u8;

pub fn applyTransform(input: []const u8, transform: TransformFn) []const u8 {
    return transform(input);
}

fn toUpper(s: []const u8) []const u8 {
    _ = s;
    return "UPPER";
}

fn toLower(s: []const u8) []const u8 {
    _ = s;
    return "lower";
}

/// Comparator pattern
const CompareFn = *const fn (*anyopaque, *anyopaque) bool;

pub fn sortWithComparator(
    items: []i32,
    context: *anyopaque,
    compare: CompareFn,
) void {
    for (items, 0..) |_, i| {
        for (items[0 .. items.len - i - 1], 0..) |_, j| {
            const a = @as(*i32, @ptrCast(@alignCast(&items[j])));
            const b = @as(*i32, @ptrCast(@alignCast(&items[j + 1])));
            if (!compare(@ptrCast(a), @ptrCast(b))) {
                const temp = items[j];
                items[j] = items[j + 1];
                items[j + 1] = temp;
            }
        }
    }
    _ = context;
}
// ANCHOR_END: function_pointers

// ANCHOR: strategy_pattern
/// Strategy pattern
const Strategy = struct {
    context: *anyopaque,
    execute_fn: *const fn (*anyopaque, i32, i32) i32,

    pub fn init(
        context: anytype,
        comptime execute_fn: fn (@TypeOf(context), i32, i32) i32,
    ) Strategy {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, a: i32, b: i32) i32 {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                return execute_fn(ptr, a, b);
            }
        };

        return .{
            .context = @ptrCast(context),
            .execute_fn = Wrapper.call,
        };
    }

    pub fn execute(self: Strategy, a: i32, b: i32) i32 {
        return self.execute_fn(self.context, a, b);
    }
};
// ANCHOR_END: strategy_pattern

/// Command pattern
const Command = struct {
    context: *anyopaque,
    execute_fn: *const fn (*anyopaque) void,

    pub fn init(
        context: anytype,
        comptime execute_fn: fn (@TypeOf(context)) void,
    ) Command {
        const Wrapper = struct {
            fn call(ctx: *anyopaque) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                execute_fn(ptr);
            }
        };

        return .{
            .context = @ptrCast(context),
            .execute_fn = Wrapper.call,
        };
    }

    pub fn execute(self: Command) void {
        self.execute_fn(self.context);
    }
};

/// Generic callable
pub fn Callable(comptime Ret: type) type {
    return struct {
        context: *anyopaque,
        call_fn: *const fn (*anyopaque) Ret,

        pub fn init(
            context: anytype,
            comptime call_fn: fn (@TypeOf(context)) Ret,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque) Ret {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    return call_fn(ptr);
                }
            };

            return .{
                .context = @ptrCast(context),
                .call_fn = Wrapper.call,
            };
        }

        pub fn call(self: @This()) Ret {
            return self.call_fn(self.context);
        }
    };
}

/// Predicate pattern
const Predicate = struct {
    context: *anyopaque,
    test_fn: *const fn (*anyopaque, i32) bool,

    pub fn init(
        context: anytype,
        comptime test_fn: fn (@TypeOf(context), i32) bool,
    ) Predicate {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, value: i32) bool {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                return test_fn(ptr, value);
            }
        };

        return .{
            .context = @ptrCast(context),
            .test_fn = Wrapper.call,
        };
    }

    pub fn test_(self: Predicate, value: i32) bool {
        return self.test_fn(self.context, value);
    }
};

pub fn filterWithPredicate(
    allocator: std.mem.Allocator,
    items: []const i32,
    predicate: Predicate,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (predicate.test_(item)) {
            try result.append(allocator, item);
        }
    }

    return try result.toOwnedSlice(allocator);
}

/// Factory pattern
pub fn Factory(comptime T: type) type {
    return struct {
        context: *anyopaque,
        create_fn: *const fn (*anyopaque) T,

        pub fn init(
            context: anytype,
            comptime create_fn: fn (@TypeOf(context)) T,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque) T {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    return create_fn(ptr);
                }
            };

            return .{
                .context = @ptrCast(context),
                .create_fn = Wrapper.call,
            };
        }

        pub fn create(self: @This()) T {
            return self.create_fn(self.context);
        }
    };
}

/// Handler pattern
pub fn Handler(comptime Event: type) type {
    return struct {
        context: *anyopaque,
        handle_fn: *const fn (*anyopaque, Event) void,

        pub fn init(
            context: anytype,
            comptime handle_fn: fn (@TypeOf(context), Event) void,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque, event: Event) void {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    handle_fn(ptr, event);
                }
            };

            return .{
                .context = @ptrCast(context),
                .handle_fn = Wrapper.call,
            };
        }

        pub fn handle(self: @This(), event: Event) void {
            self.handle_fn(self.context, event);
        }
    };
}

const KeyEvent = struct {
    key: u8,
    pressed: bool,
};

/// Visitor pattern
pub fn Visitor(comptime T: type) type {
    return struct {
        context: *anyopaque,
        visit_fn: *const fn (*anyopaque, T) void,

        pub fn init(
            context: anytype,
            comptime visit_fn: fn (@TypeOf(context), T) void,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque, item: T) void {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    visit_fn(ptr, item);
                }
            };

            return .{
                .context = @ptrCast(context),
                .visit_fn = Wrapper.call,
            };
        }

        pub fn visit(self: @This(), item: T) void {
            self.visit_fn(self.context, item);
        }
    };
}

/// Transformer pattern
pub fn Transformer(comptime In: type, comptime Out: type) type {
    return struct {
        context: *anyopaque,
        transform_fn: *const fn (*anyopaque, In) Out,

        pub fn init(
            context: anytype,
            comptime transform_fn: fn (@TypeOf(context), In) Out,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque, input: In) Out {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    return transform_fn(ptr, input);
                }
            };

            return .{
                .context = @ptrCast(context),
                .transform_fn = Wrapper.call,
            };
        }

        pub fn transform(self: @This(), input: In) Out {
            return self.transform_fn(self.context, input);
        }
    };
}

// Tests

test "single method replacement" {
    const EmailValidator = struct {
        domain: []const u8,

        fn check(self: *@This(), email: []const u8) bool {
            return std.mem.endsWith(u8, email, self.domain);
        }
    };

    var ctx = EmailValidator{ .domain = "@example.com" };
    const validator = Validator.init(&ctx, EmailValidator.check);

    try std.testing.expect(validator.validate("user@example.com"));
    try std.testing.expect(!validator.validate("user@other.com"));
}

test "function pointers" {
    try std.testing.expectEqualStrings("UPPER", applyTransform("test", toUpper));
    try std.testing.expectEqualStrings("lower", applyTransform("TEST", toLower));
}

test "comparator pattern" {
    var numbers = [_]i32{ 5, 2, 8, 1, 9 };

    const ascending = struct {
        fn cmp(a: *anyopaque, b: *anyopaque) bool {
            const x: *i32 = @ptrCast(@alignCast(a));
            const y: *i32 = @ptrCast(@alignCast(b));
            return x.* < y.*;
        }
    }.cmp;

    var ctx: u8 = 0;
    sortWithComparator(&numbers, @ptrCast(&ctx), ascending);

    try std.testing.expectEqual(@as(i32, 1), numbers[0]);
    try std.testing.expectEqual(@as(i32, 9), numbers[4]);
}

test "strategy pattern" {
    const AddStrategy = struct {
        bonus: i32,

        fn run(self: *@This(), a: i32, b: i32) i32 {
            return a + b + self.bonus;
        }
    };

    var add_ctx = AddStrategy{ .bonus = 10 };
    const strategy = Strategy.init(&add_ctx, AddStrategy.run);

    try std.testing.expectEqual(@as(i32, 25), strategy.execute(5, 10));
}

test "command pattern" {
    const PrintCommand = struct {
        message: []const u8,
        count: *usize,

        fn run(self: *@This()) void {
            _ = self.message;
            self.count.* += 1;
        }
    };

    var execution_count: usize = 0;
    var cmd_ctx = PrintCommand{
        .message = "Hello",
        .count = &execution_count,
    };
    const command = Command.init(&cmd_ctx, PrintCommand.run);

    command.execute();
    command.execute();

    try std.testing.expectEqual(@as(usize, 2), execution_count);
}

test "callable pattern" {
    const Counter = struct {
        value: i32,

        fn get(self: *@This()) i32 {
            self.value += 1;
            return self.value;
        }
    };

    var counter = Counter{ .value = 0 };
    const callable = Callable(i32).init(&counter, Counter.get);

    try std.testing.expectEqual(@as(i32, 1), callable.call());
    try std.testing.expectEqual(@as(i32, 2), callable.call());
}

test "predicate pattern" {
    const allocator = std.testing.allocator;

    const RangePredicate = struct {
        min: i32,
        max: i32,

        fn inRange(self: *@This(), value: i32) bool {
            return value >= self.min and value <= self.max;
        }
    };

    var range = RangePredicate{ .min = 5, .max = 15 };
    const predicate = Predicate.init(&range, RangePredicate.inRange);

    const numbers = [_]i32{ 1, 7, 12, 20, 10 };
    const filtered = try filterWithPredicate(allocator, &numbers, predicate);
    defer allocator.free(filtered);

    try std.testing.expectEqual(@as(usize, 3), filtered.len);
}

test "factory pattern" {
    const Config = struct {
        default_value: i32,

        fn createInstance(self: *@This()) i32 {
            return self.default_value * 2;
        }
    };

    var config = Config{ .default_value = 21 };
    const factory = Factory(i32).init(&config, Config.createInstance);

    try std.testing.expectEqual(@as(i32, 42), factory.create());
}

test "handler pattern" {
    const KeyLogger = struct {
        count: *usize,

        fn onKey(self: *@This(), event: KeyEvent) void {
            if (event.pressed) {
                self.count.* += 1;
            }
        }
    };

    var press_count: usize = 0;
    var logger = KeyLogger{ .count = &press_count };
    const handler = Handler(KeyEvent).init(&logger, KeyLogger.onKey);

    handler.handle(.{ .key = 'A', .pressed = true });
    handler.handle(.{ .key = 'B', .pressed = false });
    handler.handle(.{ .key = 'C', .pressed = true });

    try std.testing.expectEqual(@as(usize, 2), press_count);
}

test "visitor pattern" {
    const Accumulator = struct {
        sum: *i32,

        fn visitNumber(self: *@This(), n: i32) void {
            self.sum.* += n;
        }
    };

    var total: i32 = 0;
    var acc = Accumulator{ .sum = &total };
    const visitor = Visitor(i32).init(&acc, Accumulator.visitNumber);

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    for (numbers) |n| {
        visitor.visit(n);
    }

    try std.testing.expectEqual(@as(i32, 15), total);
}

test "transformer pattern" {
    const Multiplier = struct {
        factor: i32,

        fn apply(self: *@This(), value: i32) i32 {
            return value * self.factor;
        }
    };

    var multiplier = Multiplier{ .factor = 3 };
    const transformer = Transformer(i32, i32).init(&multiplier, Multiplier.apply);

    try std.testing.expectEqual(@as(i32, 15), transformer.transform(5));
    try std.testing.expectEqual(@as(i32, 30), transformer.transform(10));
}

test "validator with multiple domains" {
    const MultiDomainValidator = struct {
        domains: []const []const u8,

        fn check(self: *@This(), email: []const u8) bool {
            for (self.domains) |domain| {
                if (std.mem.endsWith(u8, email, domain)) {
                    return true;
                }
            }
            return false;
        }
    };

    const domains = [_][]const u8{ "@example.com", "@test.org" };
    var ctx = MultiDomainValidator{ .domains = &domains };
    const validator = Validator.init(&ctx, MultiDomainValidator.check);

    try std.testing.expect(validator.validate("user@example.com"));
    try std.testing.expect(validator.validate("admin@test.org"));
    try std.testing.expect(!validator.validate("user@other.net"));
}

test "strategy with subtraction" {
    const SubtractStrategy = struct {
        penalty: i32,

        fn run(self: *@This(), a: i32, b: i32) i32 {
            return a - b - self.penalty;
        }
    };

    var sub_ctx = SubtractStrategy{ .penalty = 5 };
    const strategy = Strategy.init(&sub_ctx, SubtractStrategy.run);

    try std.testing.expectEqual(@as(i32, 0), strategy.execute(10, 5));
}

test "callable with string return" {
    const StringProvider = struct {
        prefix: []const u8,

        fn get(self: *@This()) []const u8 {
            return self.prefix;
        }
    };

    var provider = StringProvider{ .prefix = "Hello" };
    const callable = Callable([]const u8).init(&provider, StringProvider.get);

    try std.testing.expectEqualStrings("Hello", callable.call());
}
```

---

## Recipe 7.10: Carrying Extra State with Callback Functions {#recipe-7-10}

**Tags:** allocators, arena-allocator, arraylist, atomics, comptime, concurrency, data-structures, error-handling, functions, memory, pointers, resource-cleanup, testing, threading
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_10.zig`

### Problem

You need to pass extra state or context to callback functions that will be invoked later.

### Solution

Use `*anyopaque` with type-safe wrappers to carry state:

```zig
// Anchor 'basic_callback_state' not found in ../../../code/03-advanced/07-functions/recipe_7_10.zig
```

### Discussion

### Multiple Callbacks with Shared State

Share state across multiple callbacks:

```zig
const EventSystem = struct {
    callbacks: std.ArrayList(Callback),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) EventSystem {
        return .{
            .callbacks = std.ArrayList(Callback){},
            .allocator = allocator,
        };
    }

    pub fn register(self: *EventSystem, callback: Callback) !void {
        try self.callbacks.append(self.allocator, callback);
    }

    pub fn trigger(self: EventSystem, value: i32) void {
        for (self.callbacks.items) |callback| {
            callback.invoke(value);
        }
    }

    pub fn deinit(self: *EventSystem) void {
        self.callbacks.deinit(self.allocator);
    }
};

test "shared state callbacks" {
    const allocator = std.testing.allocator;

    const Counter = struct {
        count: *usize,

        fn increment(self: *@This(), value: i32) void {
            self.count.* += @intCast(value);
        }
    };

    var total: usize = 0;
    var counter = Counter{ .count = &total };

    var events = EventSystem.init(allocator);
    defer events.deinit();

    try events.register(Callback.init(&counter, Counter.increment));
    try events.register(Callback.init(&counter, Counter.increment));

    events.trigger(5);

    try std.testing.expectEqual(@as(usize, 10), total);
}
```

### Callback with Allocator State

Carry allocator in callback context:

```zig
const AllocCallback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, std.mem.Allocator, []const u8) !void,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context), std.mem.Allocator, []const u8) !void,
    ) AllocCallback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, allocator: std.mem.Allocator, data: []const u8) !void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                try call_fn(ptr, allocator, data);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
        };
    }

    pub fn invoke(self: AllocCallback, allocator: std.mem.Allocator, data: []const u8) !void {
        try self.call_fn(self.context, allocator, data);
    }
};

test "callback with allocator" {
    const allocator = std.testing.allocator;

    const Logger = struct {
        messages: std.ArrayList([]u8),

        fn log(self: *@This(), alloc: std.mem.Allocator, msg: []const u8) !void {
            const copy = try alloc.dupe(u8, msg);
            try self.messages.append(alloc, copy);
        }

        fn deinit(self: *@This(), alloc: std.mem.Allocator) void {
            for (self.messages.items) |msg| {
                alloc.free(msg);
            }
            self.messages.deinit(alloc);
        }
    };

    var logger = Logger{ .messages = std.ArrayList([]u8){} };
    defer logger.deinit(allocator);

    const callback = AllocCallback.init(&logger, Logger.log);

    try callback.invoke(allocator, "message1");
    try callback.invoke(allocator, "message2");

    try std.testing.expectEqual(@as(usize, 2), logger.messages.items.len);
}
```

### Callback with Error Handling

Carry error handling state:

```zig
const ErrorCallback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, anyerror) void,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context), anyerror) void,
    ) ErrorCallback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, err: anyerror) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                call_fn(ptr, err);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
        };
    }

    pub fn invoke(self: ErrorCallback, err: anyerror) void {
        self.call_fn(self.context, err);
    }
};

test "error callback" {
    const ErrorTracker = struct {
        errors: *std.ArrayList(anyerror),

        fn track(self: *@This(), err: anyerror) void {
            self.errors.append(err) catch {};
        }
    };

    const allocator = std.testing.allocator;
    var errors = std.ArrayList(anyerror).init(allocator);
    defer errors.deinit();

    var tracker = ErrorTracker{ .errors = &errors };
    const callback = ErrorCallback.init(&tracker, ErrorTracker.track);

    callback.invoke(error.OutOfMemory);
    callback.invoke(error.InvalidInput);

    try std.testing.expectEqual(@as(usize, 2), errors.items.len);
}
```

### Timer Callback with Context

Callback for delayed execution:

```zig
const TimerCallback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque) void,
    deadline_ms: i64,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context)) void,
        deadline_ms: i64,
    ) TimerCallback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                call_fn(ptr);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
            .deadline_ms = deadline_ms,
        };
    }

    pub fn invoke(self: TimerCallback) void {
        self.call_fn(self.context);
    }

    pub fn isReady(self: TimerCallback, current_time: i64) bool {
        return current_time >= self.deadline_ms;
    }
};

test "timer callback" {
    const Task = struct {
        executed: *bool,

        fn run(self: *@This()) void {
            self.executed.* = true;
        }
    };

    var executed = false;
    var task = Task{ .executed = &executed };

    const timer = TimerCallback.init(&task, Task.run, 100);

    try std.testing.expect(!timer.isReady(50));
    try std.testing.expect(timer.isReady(100));

    timer.invoke();
    try std.testing.expect(executed);
}
```

### Async Callback with Result

Callback carrying result state:

```zig
pub fn ResultCallback(comptime T: type) type {
    return struct {
        context: *anyopaque,
        call_fn: *const fn (*anyopaque, T) void,

        pub fn init(
            context: anytype,
            comptime call_fn: fn (@TypeOf(context), T) void,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque, result: T) void {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    call_fn(ptr, result);
                }
            };

            return .{
                .context = @ptrCast(context),
                .call_fn = Wrapper.call,
            };
        }

        pub fn invoke(self: @This(), result: T) void {
            self.call_fn(self.context, result);
        }
    };
}

test "result callback" {
    const Receiver = struct {
        result: *?i32,

        fn onResult(self: *@This(), value: i32) void {
            self.result.* = value;
        }
    };

    var result: ?i32 = null;
    var receiver = Receiver{ .result = &result };

    const callback = ResultCallback(i32).init(&receiver, Receiver.onResult);

    callback.invoke(42);
    try std.testing.expectEqual(@as(i32, 42), result.?);
}
```

### Callback Chain

Chain callbacks with accumulated state:

```zig
const ChainCallback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, i32) i32,
    next: ?*const ChainCallback,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context), i32) i32,
    ) ChainCallback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, value: i32) i32 {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                return call_fn(ptr, value);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
            .next = null,
        };
    }

    pub fn invoke(self: ChainCallback, value: i32) i32 {
        var result = self.call_fn(self.context, value);
        if (self.next) |next| {
            result = next.invoke(result);
        }
        return result;
    }
};

test "callback chain" {
    const Doubler = struct {
        fn apply(_: *@This(), val: i32) i32 {
            return val * 2;
        }
    };

    const Adder = struct {
        amount: i32,

        fn apply(self: *@This(), val: i32) i32 {
            return val + self.amount;
        }
    };

    var doubler = Doubler{};
    var adder = Adder{ .amount = 10 };

    var cb1 = ChainCallback.init(&doubler, Doubler.apply);
    const cb2 = ChainCallback.init(&adder, Adder.apply);
    cb1.next = &cb2;

    const result = cb1.invoke(5); // (5 * 2) + 10 = 20
    try std.testing.expectEqual(@as(i32, 20), result);
}
```

### Callback with Multiple Parameters

Carry complex state with multiple parameters:

```zig
const MultiParamCallback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, []const u8, i32, bool) void,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context), []const u8, i32, bool) void,
    ) MultiParamCallback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, s: []const u8, n: i32, b: bool) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                call_fn(ptr, s, n, b);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
        };
    }

    pub fn invoke(self: MultiParamCallback, s: []const u8, n: i32, b: bool) void {
        self.call_fn(self.context, s, n, b);
    }
};

test "multi param callback" {
    const Collector = struct {
        count: *usize,

        fn collect(self: *@This(), _: []const u8, _: i32, flag: bool) void {
            if (flag) {
                self.count.* += 1;
            }
        }
    };

    var count: usize = 0;
    var collector = Collector{ .count = &count };
    const callback = MultiParamCallback.init(&collector, Collector.collect);

    callback.invoke("test", 42, true);
    callback.invoke("test", 42, false);
    callback.invoke("test", 42, true);

    try std.testing.expectEqual(@as(usize, 2), count);
}
```

### Callback Registry

Register and manage multiple callbacks:

```zig
const CallbackRegistry = struct {
    callbacks: std.ArrayList(Callback),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) CallbackRegistry {
        return .{
            .callbacks = std.ArrayList(Callback){},
            .allocator = allocator,
        };
    }

    pub fn add(self: *CallbackRegistry, callback: Callback) !void {
        try self.callbacks.append(self.allocator, callback);
    }

    pub fn invokeAll(self: CallbackRegistry, value: i32) void {
        for (self.callbacks.items) |callback| {
            callback.invoke(value);
        }
    }

    pub fn deinit(self: *CallbackRegistry) void {
        self.callbacks.deinit(self.allocator);
    }
};

test "callback registry" {
    const allocator = std.testing.allocator;

    const Tracker = struct {
        total: *i32,

        fn track(self: *@This(), value: i32) void {
            self.total.* += value;
        }
    };

    var total: i32 = 0;
    var tracker1 = Tracker{ .total = &total };
    var tracker2 = Tracker{ .total = &total };

    var registry = CallbackRegistry.init(allocator);
    defer registry.deinit();

    try registry.add(Callback.init(&tracker1, Tracker.track));
    try registry.add(Callback.init(&tracker2, Tracker.track));

    registry.invokeAll(10);

    try std.testing.expectEqual(@as(i32, 20), total);
}
```

### Best Practices

**Type Safety:**
```zig
// Good: Type-safe wrapper
const Callback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, T) void,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context), T) void,
    ) Callback { ... }
};

// Avoid: Raw function pointers without context
const BadCallback = *const fn (i32) void;
```

**Memory Management:**
- Document ownership of context
- Ensure context outlives callback
- Use arena allocators when appropriate
- Be explicit about cleanup requirements

**Error Handling:**
```zig
// Good: Explicit error handling
const ErrorAwareCallback = struct {
    call_fn: *const fn (*anyopaque, T) !void,

    pub fn invoke(self: @This(), value: T) !void {
        return self.call_fn(self.context, value);
    }
};
```

**Thread Safety:**
- Document if callbacks are thread-safe
- Use appropriate synchronization primitives
- Consider atomic operations for counters
- Be explicit about execution context

### Related Functions

- `*anyopaque` for type-erased context
- `@ptrCast()` and `@alignCast()` for type recovery
- `@TypeOf()` for context type inference
- Function pointer types `*const fn(T) R`
- Comptime wrappers for type-safe erasure

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_callback
/// Basic callback with state
const Callback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, i32) void,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context), i32) void,
    ) Callback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, value: i32) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                call_fn(ptr, value);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
        };
    }

    pub fn invoke(self: Callback, value: i32) void {
        self.call_fn(self.context, value);
    }
};
// ANCHOR_END: basic_callback

// ANCHOR: event_system
/// Event system with shared state
const EventSystem = struct {
    callbacks: std.ArrayList(Callback),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) EventSystem {
        return .{
            .callbacks = std.ArrayList(Callback){},
            .allocator = allocator,
        };
    }

    pub fn register(self: *EventSystem, callback: Callback) !void {
        try self.callbacks.append(self.allocator, callback);
    }

    pub fn trigger(self: EventSystem, value: i32) void {
        for (self.callbacks.items) |callback| {
            callback.invoke(value);
        }
    }

    pub fn deinit(self: *EventSystem) void {
        self.callbacks.deinit(self.allocator);
    }
};
// ANCHOR_END: event_system

// ANCHOR: advanced_callbacks
/// Callback with allocator
const AllocCallback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, std.mem.Allocator, []const u8) anyerror!void,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context), std.mem.Allocator, []const u8) anyerror!void,
    ) AllocCallback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, allocator: std.mem.Allocator, data: []const u8) anyerror!void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                try call_fn(ptr, allocator, data);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
        };
    }

    pub fn invoke(self: AllocCallback, allocator: std.mem.Allocator, data: []const u8) !void {
        try self.call_fn(self.context, allocator, data);
    }
};

/// Error callback
const ErrorCallback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, anyerror) void,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context), anyerror) void,
    ) ErrorCallback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, err: anyerror) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                call_fn(ptr, err);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
        };
    }

    pub fn invoke(self: ErrorCallback, err: anyerror) void {
        self.call_fn(self.context, err);
    }
};

/// Timer callback
const TimerCallback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque) void,
    deadline_ms: i64,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context)) void,
        deadline_ms: i64,
    ) TimerCallback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                call_fn(ptr);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
            .deadline_ms = deadline_ms,
        };
    }

    pub fn invoke(self: TimerCallback) void {
        self.call_fn(self.context);
    }

    pub fn isReady(self: TimerCallback, current_time: i64) bool {
        return current_time >= self.deadline_ms;
    }
};
// ANCHOR_END: advanced_callbacks

/// Result callback
pub fn ResultCallback(comptime T: type) type {
    return struct {
        context: *anyopaque,
        call_fn: *const fn (*anyopaque, T) void,

        pub fn init(
            context: anytype,
            comptime call_fn: fn (@TypeOf(context), T) void,
        ) @This() {
            const Wrapper = struct {
                fn call(ctx: *anyopaque, result: T) void {
                    const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                    call_fn(ptr, result);
                }
            };

            return .{
                .context = @ptrCast(context),
                .call_fn = Wrapper.call,
            };
        }

        pub fn invoke(self: @This(), result: T) void {
            self.call_fn(self.context, result);
        }
    };
}

/// Chain callback
const ChainCallback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, i32) i32,
    next: ?*const ChainCallback,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context), i32) i32,
    ) ChainCallback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, value: i32) i32 {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                return call_fn(ptr, value);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
            .next = null,
        };
    }

    pub fn invoke(self: ChainCallback, value: i32) i32 {
        var result = self.call_fn(self.context, value);
        if (self.next) |next| {
            result = next.invoke(result);
        }
        return result;
    }
};

/// Multi-param callback
const MultiParamCallback = struct {
    context: *anyopaque,
    call_fn: *const fn (*anyopaque, []const u8, i32, bool) void,

    pub fn init(
        context: anytype,
        comptime call_fn: fn (@TypeOf(context), []const u8, i32, bool) void,
    ) MultiParamCallback {
        const Wrapper = struct {
            fn call(ctx: *anyopaque, s: []const u8, n: i32, b: bool) void {
                const ptr: @TypeOf(context) = @ptrCast(@alignCast(ctx));
                call_fn(ptr, s, n, b);
            }
        };

        return .{
            .context = @ptrCast(context),
            .call_fn = Wrapper.call,
        };
    }

    pub fn invoke(self: MultiParamCallback, s: []const u8, n: i32, b: bool) void {
        self.call_fn(self.context, s, n, b);
    }
};

/// Callback registry
const CallbackRegistry = struct {
    callbacks: std.ArrayList(Callback),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) CallbackRegistry {
        return .{
            .callbacks = std.ArrayList(Callback){},
            .allocator = allocator,
        };
    }

    pub fn add(self: *CallbackRegistry, callback: Callback) !void {
        try self.callbacks.append(self.allocator, callback);
    }

    pub fn invokeAll(self: CallbackRegistry, value: i32) void {
        for (self.callbacks.items) |callback| {
            callback.invoke(value);
        }
    }

    pub fn deinit(self: *CallbackRegistry) void {
        self.callbacks.deinit(self.allocator);
    }
};

// Tests

test "callback with state" {
    const State = struct {
        sum: i32 = 0,

        fn onValue(self: *@This(), value: i32) void {
            self.sum += value;
        }
    };

    var state = State{};
    const callback = Callback.init(&state, State.onValue);

    callback.invoke(10);
    callback.invoke(20);
    callback.invoke(5);

    try std.testing.expectEqual(@as(i32, 35), state.sum);
}

test "shared state callbacks" {
    const allocator = std.testing.allocator;

    const Counter = struct {
        count: *usize,

        fn increment(self: *@This(), value: i32) void {
            self.count.* += @intCast(value);
        }
    };

    var total: usize = 0;
    var counter = Counter{ .count = &total };

    var events = EventSystem.init(allocator);
    defer events.deinit();

    try events.register(Callback.init(&counter, Counter.increment));
    try events.register(Callback.init(&counter, Counter.increment));

    events.trigger(5);

    try std.testing.expectEqual(@as(usize, 10), total);
}

test "callback with allocator" {
    const allocator = std.testing.allocator;

    const Logger = struct {
        messages: std.ArrayList([]u8),

        fn log(self: *@This(), alloc: std.mem.Allocator, msg: []const u8) !void {
            const copy = try alloc.dupe(u8, msg);
            try self.messages.append(alloc, copy);
        }

        fn deinit(self: *@This(), alloc: std.mem.Allocator) void {
            for (self.messages.items) |msg| {
                alloc.free(msg);
            }
            self.messages.deinit(alloc);
        }
    };

    var logger = Logger{ .messages = std.ArrayList([]u8){} };
    defer logger.deinit(allocator);

    const callback = AllocCallback.init(&logger, Logger.log);

    try callback.invoke(allocator, "message1");
    try callback.invoke(allocator, "message2");

    try std.testing.expectEqual(@as(usize, 2), logger.messages.items.len);
}

test "error callback" {
    const ErrorTracker = struct {
        last_error: *?anyerror,

        fn track(self: *@This(), err: anyerror) void {
            self.last_error.* = err;
        }
    };

    var last_error: ?anyerror = null;
    var tracker = ErrorTracker{ .last_error = &last_error };
    const callback = ErrorCallback.init(&tracker, ErrorTracker.track);

    callback.invoke(error.OutOfMemory);
    try std.testing.expectEqual(error.OutOfMemory, last_error.?);

    callback.invoke(error.InvalidInput);
    try std.testing.expectEqual(error.InvalidInput, last_error.?);
}

test "timer callback" {
    const Task = struct {
        executed: *bool,

        fn run(self: *@This()) void {
            self.executed.* = true;
        }
    };

    var executed = false;
    var task = Task{ .executed = &executed };

    const timer = TimerCallback.init(&task, Task.run, 100);

    try std.testing.expect(!timer.isReady(50));
    try std.testing.expect(timer.isReady(100));

    timer.invoke();
    try std.testing.expect(executed);
}

test "result callback" {
    const Receiver = struct {
        result: *?i32,

        fn onResult(self: *@This(), value: i32) void {
            self.result.* = value;
        }
    };

    var result: ?i32 = null;
    var receiver = Receiver{ .result = &result };

    const callback = ResultCallback(i32).init(&receiver, Receiver.onResult);

    callback.invoke(42);
    try std.testing.expectEqual(@as(i32, 42), result.?);
}

test "callback chain" {
    const Doubler = struct {
        fn apply(_: *@This(), val: i32) i32 {
            return val * 2;
        }
    };

    const Adder = struct {
        amount: i32,

        fn apply(self: *@This(), val: i32) i32 {
            return val + self.amount;
        }
    };

    var doubler = Doubler{};
    var adder = Adder{ .amount = 10 };

    var cb1 = ChainCallback.init(&doubler, Doubler.apply);
    const cb2 = ChainCallback.init(&adder, Adder.apply);
    cb1.next = &cb2;

    const result = cb1.invoke(5);
    try std.testing.expectEqual(@as(i32, 20), result);
}

test "multi param callback" {
    const Collector = struct {
        count: *usize,

        fn collect(self: *@This(), _: []const u8, _: i32, flag: bool) void {
            if (flag) {
                self.count.* += 1;
            }
        }
    };

    var count: usize = 0;
    var collector = Collector{ .count = &count };
    const callback = MultiParamCallback.init(&collector, Collector.collect);

    callback.invoke("test", 42, true);
    callback.invoke("test", 42, false);
    callback.invoke("test", 42, true);

    try std.testing.expectEqual(@as(usize, 2), count);
}

test "callback registry" {
    const allocator = std.testing.allocator;

    const Tracker = struct {
        total: *i32,

        fn track(self: *@This(), value: i32) void {
            self.total.* += value;
        }
    };

    var total: i32 = 0;
    var tracker1 = Tracker{ .total = &total };
    var tracker2 = Tracker{ .total = &total };

    var registry = CallbackRegistry.init(allocator);
    defer registry.deinit();

    try registry.add(Callback.init(&tracker1, Tracker.track));
    try registry.add(Callback.init(&tracker2, Tracker.track));

    registry.invokeAll(10);

    try std.testing.expectEqual(@as(i32, 20), total);
}

test "callback multiply" {
    const Multiplier = struct {
        factor: *i32,

        fn multiply(self: *@This(), value: i32) void {
            self.factor.* = value * 2;
        }
    };

    var result: i32 = 0;
    var multiplier = Multiplier{ .factor = &result };
    const callback = Callback.init(&multiplier, Multiplier.multiply);

    callback.invoke(7);
    try std.testing.expectEqual(@as(i32, 14), result);
}

test "multiple timer callbacks" {
    const Counter = struct {
        count: *usize,

        fn increment(self: *@This()) void {
            self.count.* += 1;
        }
    };

    var count: usize = 0;
    var counter = Counter{ .count = &count };

    const timer1 = TimerCallback.init(&counter, Counter.increment, 50);
    const timer2 = TimerCallback.init(&counter, Counter.increment, 100);

    try std.testing.expect(timer1.isReady(50));
    try std.testing.expect(!timer2.isReady(50));

    timer1.invoke();
    try std.testing.expectEqual(@as(usize, 1), count);

    timer2.invoke();
    try std.testing.expectEqual(@as(usize, 2), count);
}

test "result callback with string" {
    const StringReceiver = struct {
        result: *?[]const u8,

        fn onResult(self: *@This(), value: []const u8) void {
            self.result.* = value;
        }
    };

    var result: ?[]const u8 = null;
    var receiver = StringReceiver{ .result = &result };

    const callback = ResultCallback([]const u8).init(&receiver, StringReceiver.onResult);

    callback.invoke("hello");
    try std.testing.expectEqualStrings("hello", result.?);
}

test "event system with three callbacks" {
    const allocator = std.testing.allocator;

    const Accumulator = struct {
        value: *i32,

        fn add(self: *@This(), n: i32) void {
            self.value.* += n;
        }
    };

    var total: i32 = 0;
    var acc1 = Accumulator{ .value = &total };
    var acc2 = Accumulator{ .value = &total };
    var acc3 = Accumulator{ .value = &total };

    var events = EventSystem.init(allocator);
    defer events.deinit();

    try events.register(Callback.init(&acc1, Accumulator.add));
    try events.register(Callback.init(&acc2, Accumulator.add));
    try events.register(Callback.init(&acc3, Accumulator.add));

    events.trigger(3);

    try std.testing.expectEqual(@as(i32, 9), total);
}
```

---

## Recipe 7.11: Inlining Callback Functions {#recipe-7-11}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, functions, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/07-functions/recipe_7_11.zig`

### Problem

You want to use callbacks for flexibility but need to eliminate the function call overhead in performance-critical code.

### Solution

Use `inline` keyword and `comptime` to eliminate callback overhead:

```zig
// Anchor 'basic_inline_callback' not found in ../../../code/03-advanced/07-functions/recipe_7_11.zig
```

### Discussion

### Comptime Callback Specialization

Generate specialized versions at compile time:

```zig
pub fn forEach(
    items: []const i32,
    comptime callback: fn (i32) void,
) void {
    for (items) |item| {
        callback(item);
    }
}

test "comptime callback specialization" {
    var sum: i32 = 0;

    const Adder = struct {
        total: *i32,

        fn add(self: *@This(), value: i32) void {
            self.total.* += value;
        }
    };

    var adder = Adder{ .total = &sum };

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    // Comptime specialization
    forEach(&numbers, struct {
        fn call(x: i32) void {
            adder.add(x);
        }
    }.call);

    try std.testing.expectEqual(@as(i32, 15), sum);
}
```

### Inline Higher-Order Functions

Use `inline` keyword for zero-cost abstractions:

```zig
pub fn map(
    allocator: std.mem.Allocator,
    items: []const i32,
    comptime transform: fn (i32) i32,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        try result.append(allocator, transform(item));
    }

    return try result.toOwnedSlice(allocator);
}

test "inline map" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    const doubled = try map(allocator, &numbers, struct {
        fn transform(x: i32) i32 {
            return x * 2;
        }
    }.transform);
    defer allocator.free(doubled);

    try std.testing.expectEqual(@as(usize, 5), doubled.len);
    try std.testing.expectEqual(@as(i32, 2), doubled[0]);
    try std.testing.expectEqual(@as(i32, 10), doubled[4]);
}
```

### Filter with Inline Predicate

Zero-overhead filtering:

```zig
pub fn filter(
    allocator: std.mem.Allocator,
    items: []const i32,
    comptime predicate: fn (i32) bool,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (predicate(item)) {
            try result.append(allocator, item);
        }
    }

    return try result.toOwnedSlice(allocator);
}

test "inline filter" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    const evens = try filter(allocator, &numbers, struct {
        fn isEven(x: i32) bool {
            return @mod(x, 2) == 0;
        }
    }.isEven);
    defer allocator.free(evens);

    try std.testing.expectEqual(@as(usize, 5), evens.len);
    try std.testing.expectEqual(@as(i32, 2), evens[0]);
}
```

### Reduce with Inline Accumulator

Compile-time optimized reduction:

```zig
pub fn reduce(
    items: []const i32,
    initial: i32,
    comptime accumulate: fn (i32, i32) i32,
) i32 {
    var result = initial;
    for (items) |item| {
        result = accumulate(result, item);
    }
    return result;
}

test "inline reduce" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    const sum = reduce(&numbers, 0, struct {
        fn add(acc: i32, x: i32) i32 {
            return acc + x;
        }
    }.add);

    try std.testing.expectEqual(@as(i32, 15), sum);

    const product = reduce(&numbers, 1, struct {
        fn multiply(acc: i32, x: i32) i32 {
            return acc * x;
        }
    }.multiply);

    try std.testing.expectEqual(@as(i32, 120), product);
}
```

### Chained Operations

Compose inline operations:

```zig
pub fn pipeline(
    allocator: std.mem.Allocator,
    items: []const i32,
    comptime transform: fn (i32) i32,
    comptime pred: fn (i32) bool,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        const transformed = transform(item);
        if (pred(transformed)) {
            try result.append(allocator, transformed);
        }
    }

    return try result.toOwnedSlice(allocator);
}

test "inline pipeline" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    const result = try pipeline(
        allocator,
        &numbers,
        struct {
            fn double(x: i32) i32 {
                return x * 2;
            }
        }.double,
        struct {
            fn greaterThanFive(x: i32) bool {
                return x > 5;
            }
        }.greaterThanFive,
    );
    defer allocator.free(result);

    try std.testing.expectEqual(@as(usize, 3), result.len);
    try std.testing.expectEqual(@as(i32, 6), result[0]);
    try std.testing.expectEqual(@as(i32, 8), result[1]);
    try std.testing.expectEqual(@as(i32, 10), result[2]);
}
```

### Generic Inline Callbacks

Work with any type using comptime:

```zig
pub fn GenericMap(comptime T: type, comptime R: type) type {
    return struct {
        pub fn map(
            allocator: std.mem.Allocator,
            items: []const T,
            comptime transform: fn (T) R,
        ) ![]R {
            var result = std.ArrayList(R){};
            errdefer result.deinit(allocator);

            for (items) |item| {
                try result.append(allocator, transform(item));
            }

            return try result.toOwnedSlice(allocator);
        }
    };
}

test "generic inline map" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3 };
    const doubled = try GenericMap(i32, i32).map(allocator, &numbers, struct {
        fn double(x: i32) i32 {
            return x * 2;
        }
    }.double);
    defer allocator.free(doubled);

    try std.testing.expectEqual(@as(usize, 3), doubled.len);
    try std.testing.expectEqual(@as(i32, 2), doubled[0]);
}
```

### Inline Iterator Processing

Process iterators without function call overhead:

```zig
pub fn Iterator(comptime T: type) type {
    return struct {
        items: []const T,
        index: usize = 0,

        pub fn next(self: *@This()) ?T {
            if (self.index >= self.items.len) return null;
            const item = self.items[self.index];
            self.index += 1;
            return item;
        }

        pub fn collect(
            self: *@This(),
            allocator: std.mem.Allocator,
            comptime transform: fn (T) T,
        ) ![]T {
            var result = std.ArrayList(T){};
            errdefer result.deinit(allocator);

            while (self.next()) |item| {
                try result.append(allocator, transform(item));
            }

            return try result.toOwnedSlice(allocator);
        }
    };
}

test "inline iterator processing" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    var iter = Iterator(i32){ .items = &numbers };

    const doubled = try iter.collect(allocator, struct {
        fn double(x: i32) i32 {
            return x * 2;
        }
    }.double);
    defer allocator.free(doubled);

    try std.testing.expectEqual(@as(usize, 5), doubled.len);
    try std.testing.expectEqual(@as(i32, 10), doubled[4]);
}
```

### Conditional Inlining

Use comptime to choose implementation:

```zig
pub fn processWithStrategy(
    items: []const i32,
    comptime inline_it: bool,
) i32 {
    if (inline_it) {
        return processInline(items, struct {
            fn double(x: i32) i32 {
                return x * 2;
            }
        }.double);
    } else {
        var sum: i32 = 0;
        for (items) |item| {
            sum += item * 2;
        }
        return sum;
    }
}

test "conditional inlining" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    const result1 = processWithStrategy(&numbers, true);
    try std.testing.expectEqual(@as(i32, 30), result1);

    const result2 = processWithStrategy(&numbers, false);
    try std.testing.expectEqual(@as(i32, 30), result2);
}
```

### Inline Comparison Functions

Sorting with inline comparators:

```zig
pub fn sortWith(
    items: []i32,
    comptime lessThan: fn (i32, i32) bool,
) void {
    if (items.len <= 1) return;

    // Simple bubble sort for demonstration
    for (items, 0..) |_, i| {
        for (items[0 .. items.len - i - 1], 0..) |_, j| {
            if (!lessThan(items[j], items[j + 1])) {
                const temp = items[j];
                items[j] = items[j + 1];
                items[j + 1] = temp;
            }
        }
    }
}

test "inline comparison" {
    var ascending = [_]i32{ 5, 2, 8, 1, 9 };
    sortWith(&ascending, struct {
        fn lessThan(a: i32, b: i32) bool {
            return a < b;
        }
    }.lessThan);

    try std.testing.expectEqual(@as(i32, 1), ascending[0]);
    try std.testing.expectEqual(@as(i32, 9), ascending[4]);

    var descending = [_]i32{ 5, 2, 8, 1, 9 };
    sortWith(&descending, struct {
        fn greaterThan(a: i32, b: i32) bool {
            return a > b;
        }
    }.greaterThan);

    try std.testing.expectEqual(@as(i32, 9), descending[0]);
    try std.testing.expectEqual(@as(i32, 1), descending[4]);
}
```

### Best Practices

**When to Inline:**
```zig
// Good: Small, frequently called callbacks
pub fn fastMap(items: []const i32, comptime f: fn(i32) i32) []i32 {
    // Compiler can inline f() completely
}

// Avoid: Large callbacks that bloat code size
pub fn slowMap(items: []const i32, comptime f: fn(i32) ComplexResult) []ComplexResult {
    // May increase binary size significantly
}
```

**Performance:**
- Inline callbacks eliminate function call overhead
- Comptime callbacks enable better compiler optimizations
- Use for hot loops and performance-critical paths
- Profile before and after inlining

**Code Size:**
- Inlining increases code size (one copy per call site)
- Balance performance vs. binary size
- Use `inline` judiciously for critical paths only

**Debugging:**
```zig
// Good: Named inline functions for better stack traces
const Transform = struct {
    fn double(x: i32) i32 {
        return x * 2;
    }
};

processInline(&items, Transform.double);

// Harder to debug: Anonymous inline functions
processInline(&items, struct {
    fn call(x: i32) i32 {
        return x * 2;
    }
}.call);
```

**Comptime vs Runtime:**
```zig
// Comptime: Callback known at compile time
pub fn compiletimeProcess(comptime callback: fn(i32) i32) type {
    // Can use callback in type construction
}

// Runtime: Callback determined at runtime
pub fn runtimeProcess(callback: *const fn(i32) i32) void {
    // Cannot inline, regular function pointer
}
```

### Related Functions

- `inline` keyword for forced inlining
- `comptime` for compile-time function parameters
- Anonymous structs for inline function definitions
- `@inlineCall()` for explicit inline calls (advanced)
- Generic functions with `comptime` parameters

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: inline_callback
/// Inline callback for immediate execution
pub fn processInline(
    items: []const i32,
    comptime callback: fn (i32) i32,
) i32 {
    var sum: i32 = 0;
    for (items) |item| {
        sum += callback(item);
    }
    return sum;
}

fn double(x: i32) i32 {
    return x * 2;
}

/// Comptime callback specialization
pub fn forEach(
    items: []const i32,
    context: anytype,
    comptime callback: fn (@TypeOf(context), i32) void,
) void {
    for (items) |item| {
        callback(context, item);
    }
}
// ANCHOR_END: inline_callback

// ANCHOR: inline_transforms
/// Inline map function
pub fn map(
    allocator: std.mem.Allocator,
    items: []const i32,
    comptime transform: fn (i32) i32,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        try result.append(allocator, transform(item));
    }

    return try result.toOwnedSlice(allocator);
}

/// Inline filter function
pub fn filter(
    allocator: std.mem.Allocator,
    items: []const i32,
    comptime predicate: fn (i32) bool,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (predicate(item)) {
            try result.append(allocator, item);
        }
    }

    return try result.toOwnedSlice(allocator);
}

/// Inline reduce function
pub fn reduce(
    items: []const i32,
    initial: i32,
    comptime accumulate: fn (i32, i32) i32,
) i32 {
    var result = initial;
    for (items) |item| {
        result = accumulate(result, item);
    }
    return result;
}
// ANCHOR_END: inline_transforms

// ANCHOR: inline_pipeline
/// Pipeline function
pub fn pipeline(
    allocator: std.mem.Allocator,
    items: []const i32,
    comptime transform: fn (i32) i32,
    comptime pred: fn (i32) bool,
) ![]i32 {
    var result = std.ArrayList(i32){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        const transformed = transform(item);
        if (pred(transformed)) {
            try result.append(allocator, transformed);
        }
    }

    return try result.toOwnedSlice(allocator);
}
// ANCHOR_END: inline_pipeline

/// Generic map
pub fn GenericMap(comptime T: type, comptime R: type) type {
    return struct {
        pub fn map(
            allocator: std.mem.Allocator,
            items: []const T,
            comptime transform: fn (T) R,
        ) ![]R {
            var result = std.ArrayList(R){};
            errdefer result.deinit(allocator);

            for (items) |item| {
                try result.append(allocator, transform(item));
            }

            return try result.toOwnedSlice(allocator);
        }
    };
}

/// Iterator type
pub fn Iterator(comptime T: type) type {
    return struct {
        items: []const T,
        index: usize = 0,

        pub fn next(self: *@This()) ?T {
            if (self.index >= self.items.len) return null;
            const item = self.items[self.index];
            self.index += 1;
            return item;
        }

        pub fn collect(
            self: *@This(),
            allocator: std.mem.Allocator,
            comptime transform: fn (T) T,
        ) ![]T {
            var result = std.ArrayList(T){};
            errdefer result.deinit(allocator);

            while (self.next()) |item| {
                try result.append(allocator, transform(item));
            }

            return try result.toOwnedSlice(allocator);
        }
    };
}

/// Conditional inlining
pub fn processWithStrategy(
    items: []const i32,
    comptime inline_it: bool,
) i32 {
    if (inline_it) {
        return processInline(items, struct {
            fn double_fn(x: i32) i32 {
                return x * 2;
            }
        }.double_fn);
    } else {
        var sum: i32 = 0;
        for (items) |item| {
            sum += item * 2;
        }
        return sum;
    }
}

/// Sort with inline comparator
pub fn sortWith(
    items: []i32,
    comptime lessThan: fn (i32, i32) bool,
) void {
    if (items.len <= 1) return;

    for (items, 0..) |_, i| {
        for (items[0 .. items.len - i - 1], 0..) |_, j| {
            if (!lessThan(items[j], items[j + 1])) {
                const temp = items[j];
                items[j] = items[j + 1];
                items[j + 1] = temp;
            }
        }
    }
}

// Tests

test "inline callback" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    const result = processInline(&numbers, double);
    try std.testing.expectEqual(@as(i32, 30), result);
}

test "comptime callback specialization" {
    var sum: i32 = 0;

    const Adder = struct {
        fn add(ctx: *i32, value: i32) void {
            ctx.* += value;
        }
    };

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    forEach(&numbers, &sum, Adder.add);

    try std.testing.expectEqual(@as(i32, 15), sum);
}

test "inline map" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    const doubled = try map(allocator, &numbers, struct {
        fn transform(x: i32) i32 {
            return x * 2;
        }
    }.transform);
    defer allocator.free(doubled);

    try std.testing.expectEqual(@as(usize, 5), doubled.len);
    try std.testing.expectEqual(@as(i32, 2), doubled[0]);
    try std.testing.expectEqual(@as(i32, 10), doubled[4]);
}

test "inline filter" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    const evens = try filter(allocator, &numbers, struct {
        fn isEven(x: i32) bool {
            return @mod(x, 2) == 0;
        }
    }.isEven);
    defer allocator.free(evens);

    try std.testing.expectEqual(@as(usize, 5), evens.len);
    try std.testing.expectEqual(@as(i32, 2), evens[0]);
}

test "inline reduce" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    const sum = reduce(&numbers, 0, struct {
        fn add(acc: i32, x: i32) i32 {
            return acc + x;
        }
    }.add);

    try std.testing.expectEqual(@as(i32, 15), sum);

    const product = reduce(&numbers, 1, struct {
        fn multiply(acc: i32, x: i32) i32 {
            return acc * x;
        }
    }.multiply);

    try std.testing.expectEqual(@as(i32, 120), product);
}

test "inline pipeline" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    const result = try pipeline(
        allocator,
        &numbers,
        struct {
            fn double_fn(x: i32) i32 {
                return x * 2;
            }
        }.double_fn,
        struct {
            fn greaterThanFive(x: i32) bool {
                return x > 5;
            }
        }.greaterThanFive,
    );
    defer allocator.free(result);

    try std.testing.expectEqual(@as(usize, 3), result.len);
    try std.testing.expectEqual(@as(i32, 6), result[0]);
    try std.testing.expectEqual(@as(i32, 8), result[1]);
    try std.testing.expectEqual(@as(i32, 10), result[2]);
}

test "generic inline map" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3 };
    const doubled = try GenericMap(i32, i32).map(allocator, &numbers, struct {
        fn double_fn(x: i32) i32 {
            return x * 2;
        }
    }.double_fn);
    defer allocator.free(doubled);

    try std.testing.expectEqual(@as(usize, 3), doubled.len);
    try std.testing.expectEqual(@as(i32, 2), doubled[0]);
}

test "inline iterator processing" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    var iter = Iterator(i32){ .items = &numbers };

    const doubled = try iter.collect(allocator, struct {
        fn double_fn(x: i32) i32 {
            return x * 2;
        }
    }.double_fn);
    defer allocator.free(doubled);

    try std.testing.expectEqual(@as(usize, 5), doubled.len);
    try std.testing.expectEqual(@as(i32, 10), doubled[4]);
}

test "conditional inlining" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    const result1 = processWithStrategy(&numbers, true);
    try std.testing.expectEqual(@as(i32, 30), result1);

    const result2 = processWithStrategy(&numbers, false);
    try std.testing.expectEqual(@as(i32, 30), result2);
}

test "inline comparison ascending" {
    var ascending = [_]i32{ 5, 2, 8, 1, 9 };
    sortWith(&ascending, struct {
        fn lessThan(a: i32, b: i32) bool {
            return a < b;
        }
    }.lessThan);

    try std.testing.expectEqual(@as(i32, 1), ascending[0]);
    try std.testing.expectEqual(@as(i32, 9), ascending[4]);
}

test "inline comparison descending" {
    var descending = [_]i32{ 5, 2, 8, 1, 9 };
    sortWith(&descending, struct {
        fn greaterThan(a: i32, b: i32) bool {
            return a > b;
        }
    }.greaterThan);

    try std.testing.expectEqual(@as(i32, 9), descending[0]);
    try std.testing.expectEqual(@as(i32, 1), descending[4]);
}

test "map with triple" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3 };
    const tripled = try map(allocator, &numbers, struct {
        fn triple(x: i32) i32 {
            return x * 3;
        }
    }.triple);
    defer allocator.free(tripled);

    try std.testing.expectEqual(@as(usize, 3), tripled.len);
    try std.testing.expectEqual(@as(i32, 3), tripled[0]);
    try std.testing.expectEqual(@as(i32, 9), tripled[2]);
}

test "filter odds" {
    const allocator = std.testing.allocator;

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    const odds = try filter(allocator, &numbers, struct {
        fn isOdd(x: i32) bool {
            return @mod(x, 2) == 1;
        }
    }.isOdd);
    defer allocator.free(odds);

    try std.testing.expectEqual(@as(usize, 3), odds.len);
    try std.testing.expectEqual(@as(i32, 1), odds[0]);
    try std.testing.expectEqual(@as(i32, 5), odds[2]);
}

test "reduce with max" {
    const numbers = [_]i32{ 5, 2, 8, 1, 9 };

    const max_val = reduce(&numbers, numbers[0], struct {
        fn max(acc: i32, x: i32) i32 {
            return if (x > acc) x else acc;
        }
    }.max);

    try std.testing.expectEqual(@as(i32, 9), max_val);
}
```

---
