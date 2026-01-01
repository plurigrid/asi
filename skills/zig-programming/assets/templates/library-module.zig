// Target Zig Version: 0.15.2
// For other versions, see references/version-differences.md

const std = @import("std");
const testing = std.testing;

// Library Module Template
// Demonstrates creating a reusable library with public API, tests, and documentation

/// Library version information
pub const version = std.SemanticVersion{
    .major = 1,
    .minor = 0,
    .patch = 0,
};

/// Library configuration options
pub const Config = struct {
    /// Enable debug logging
    debug: bool = false,

    /// Maximum buffer size
    max_buffer_size: usize = 4096,

    /// Default initialization
    pub fn init() Config {
        return .{};
    }
};

/// Main library context
pub const Context = struct {
    allocator: std.mem.Allocator,
    config: Config,

    /// Initialize library context
    pub fn init(allocator: std.mem.Allocator, config: Config) Context {
        return .{
            .allocator = allocator,
            .config = config,
        };
    }

    /// Initialize with default configuration
    pub fn initDefault(allocator: std.mem.Allocator) Context {
        return init(allocator, Config.init());
    }

    /// Cleanup resources (if needed)
    pub fn deinit(self: *Context) void {
        _ = self;
        // TODO: Add cleanup logic if your library allocates resources
    }
};

/// Example public API function
/// Processes input data and returns result
pub fn process(ctx: *Context, input: []const u8) ![]u8 {
    if (ctx.config.debug) {
        std.debug.print("[DEBUG] Processing {d} bytes\n", .{input.len});
    }

    // TODO: Implement your processing logic
    const result = try ctx.allocator.alloc(u8, input.len);
    errdefer ctx.allocator.free(result);

    @memcpy(result, input);

    return result;
}

/// Example transformation function
/// Transforms data in-place
pub fn transform(ctx: *Context, data: []u8) !void {
    if (ctx.config.debug) {
        std.debug.print("[DEBUG] Transforming {d} bytes\n", .{data.len});
    }

    // TODO: Implement your transformation logic
    for (data) |*byte| {
        byte.* = byte.* +% 1; // Example: increment each byte
    }
}

/// Builder pattern example
pub const Builder = struct {
    allocator: std.mem.Allocator,
    items: std.ArrayList(u8),
    config: Config,

    /// Initialize builder
    pub fn init(allocator: std.mem.Allocator) Builder {
        return .{
            .allocator = allocator,
            .items = std.ArrayList(u8).init(allocator),
            .config = Config.init(),
        };
    }

    /// Clean up builder resources
    pub fn deinit(self: *Builder) void {
        self.items.deinit();
    }

    /// Add data to builder
    pub fn add(self: *Builder, data: []const u8) !*Builder {
        try self.items.appendSlice(data);
        return self;
    }

    /// Set configuration
    pub fn withConfig(self: *Builder, config: Config) *Builder {
        self.config = config;
        return self;
    }

    /// Build final result
    pub fn build(self: *Builder) ![]u8 {
        const result = try self.allocator.alloc(u8, self.items.items.len);
        @memcpy(result, self.items.items);
        return result;
    }
};

/// Error set for library operations
pub const Error = error{
    InvalidInput,
    BufferTooSmall,
    ProcessingFailed,
};

/// Example function with custom error set
pub fn validate(input: []const u8) Error!void {
    if (input.len == 0) {
        return Error.InvalidInput;
    }

    // TODO: Add your validation logic
}

/// Iterator pattern example
pub const Iterator = struct {
    data: []const u8,
    index: usize = 0,

    pub fn init(data: []const u8) Iterator {
        return .{ .data = data };
    }

    pub fn next(self: *Iterator) ?u8 {
        if (self.index >= self.data.len) return null;
        const value = self.data[self.index];
        self.index += 1;
        return value;
    }

    pub fn reset(self: *Iterator) void {
        self.index = 0;
    }
};

// =============================================================================
// Tests
// =============================================================================

test "version info" {
    try testing.expectEqual(@as(u32, 1), version.major);
    try testing.expectEqual(@as(u32, 0), version.minor);
    try testing.expectEqual(@as(u32, 0), version.patch);
}

test "Context initialization" {
    const allocator = testing.allocator;

    var ctx = Context.initDefault(allocator);
    defer ctx.deinit();

    try testing.expect(!ctx.config.debug);
    try testing.expectEqual(@as(usize, 4096), ctx.config.max_buffer_size);
}

test "process function" {
    const allocator = testing.allocator;

    var ctx = Context.initDefault(allocator);
    defer ctx.deinit();

    const input = "test data";
    const result = try process(&ctx, input);
    defer allocator.free(result);

    try testing.expectEqualStrings(input, result);
}

test "transform function" {
    const allocator = testing.allocator;

    var ctx = Context.initDefault(allocator);
    defer ctx.deinit();

    var data = try allocator.alloc(u8, 5);
    defer allocator.free(data);

    @memcpy(data, "hello");

    try transform(&ctx, data);

    // Each byte should be incremented by 1
    try testing.expectEqual(@as(u8, 'h' + 1), data[0]);
}

test "Builder pattern" {
    const allocator = testing.allocator;

    var builder = Builder.init(allocator);
    defer builder.deinit();

    _ = try builder.add("Hello");
    _ = try builder.add(" ");
    _ = try builder.add("World");

    const result = try builder.build();
    defer allocator.free(result);

    try testing.expectEqualStrings("Hello World", result);
}

test "error handling" {
    try testing.expectError(Error.InvalidInput, validate(""));

    // Valid input should succeed
    try validate("valid");
}

test "Iterator pattern" {
    const data = "abc";
    var iter = Iterator.init(data);

    try testing.expectEqual(@as(u8, 'a'), iter.next().?);
    try testing.expectEqual(@as(u8, 'b'), iter.next().?);
    try testing.expectEqual(@as(u8, 'c'), iter.next().?);
    try testing.expect(iter.next() == null);

    // Reset and iterate again
    iter.reset();
    try testing.expectEqual(@as(u8, 'a'), iter.next().?);
}

test "debug config" {
    const allocator = testing.allocator;

    var config = Config.init();
    config.debug = true;

    var ctx = Context.init(allocator, config);
    defer ctx.deinit();

    try testing.expect(ctx.config.debug);
}
