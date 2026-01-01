# Testing & Debugging Recipes

*14 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [14.1](#recipe-14-1) | Testing program output sent to stdout | intermediate |
| [14.2](#recipe-14-2) | Patching objects in unit tests | intermediate |
| [14.3](#recipe-14-3) | Testing for exceptional conditions in unit tests | intermediate |
| [14.4](#recipe-14-4) | Logging test output to a file | intermediate |
| [14.5](#recipe-14-5) | Skipping or anticipating test failures | intermediate |
| [14.6](#recipe-14-6) | Handling multiple exceptions at once | intermediate |
| [14.7](#recipe-14-7) | Catching all exceptions | intermediate |
| [14.8](#recipe-14-8) | Creating custom exception types | intermediate |
| [14.9](#recipe-14-9) | Raising an exception in response to another exception | intermediate |
| [14.10](#recipe-14-10) | Reraising the last exception | intermediate |
| [14.11](#recipe-14-11) | Issuing warning messages | intermediate |
| [14.12](#recipe-14-12) | Debugging basic program crashes | intermediate |
| [14.13](#recipe-14-13) | Profiling and timing your program | intermediate |
| [14.14](#recipe-14-14) | Making your programs run faster | intermediate |

---

## Recipe 14.1: Testing program output sent to stdout {#recipe-14-1}

**Tags:** allocators, arraylist, data-structures, error-handling, json, memory, parsing, resource-cleanup, testing, testing-debugging
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_1.zig`

### Problem

You need to test functions that print to stdout, but running tests shouldn't actually print anything. You want to capture and verify the output programmatically.

### Solution

Use `std.ArrayList(u8)` as an in-memory buffer to capture output. Pass the buffer's writer to functions instead of stdout, then verify the contents:

```zig
fn greet(writer: anytype, name: []const u8) !void {
    try writer.print("Hello, {s}!\n", .{name});
}
```

```zig
test "capture and verify stdout output" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    const writer = buffer.writer(testing.allocator);
    try greet(writer, "World");

    try testing.expectEqualStrings("Hello, World!\n", buffer.items);
}
```

### Discussion

Testing output is crucial for CLI tools and scripts. Instead of writing directly to `std.io.getStdOut()`, design your functions to accept any writer through the `anytype` parameter. This makes them testable and more flexible.

The pattern works because:

1. **Writer abstraction**: Functions use `anytype` for the writer parameter
2. **ArrayList as buffer**: `std.ArrayList(u8)` provides an in-memory writer
3. **Direct inspection**: After the function runs, check `buffer.items` for the output

### Testing Multiple Lines

Capture complex output with multiple print statements:

```zig
fn printReport(writer: anytype, items: usize, total: f64) !void {
    try writer.print("Items processed: {d}\n", .{items});
    try writer.print("Total value: ${d:.2}\n", .{total});
    try writer.writeAll("Status: Complete\n");
}

test "capture multiple output lines" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try printReport(buffer.writer(testing.allocator), 42, 123.45);

    const expected =
        \\Items processed: 42
        \\Total value: $123.45
        \\Status: Complete
        \\
    ;
    try testing.expectEqualStrings(expected, buffer.items);
}
```

The multiline string literal (`\\`) makes expected output easy to read and maintain.

### Pattern Matching Output

You don't always need exact string matches. Use `std.mem.indexOf` to verify specific content is present:

```zig
fn formatData(writer: anytype, data: []const u8) !void {
    try writer.print("[INFO] Processing: {s}\n", .{data});
    try writer.print("[INFO] Length: {d} bytes\n", .{data.len});
}

test "verify formatted output" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try formatData(buffer.writer(testing.allocator), "test data");

    try testing.expect(std.mem.indexOf(u8, buffer.items, "[INFO]") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "test data") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "9 bytes") != null);
}
```

This approach is more resilient to minor formatting changes.

### Testing Error and Success Messages

Capture output even when functions return errors:

```zig
fn processWithLogging(writer: anytype, value: i32) !void {
    if (value < 0) {
        try writer.print("ERROR: Invalid value {d}\n", .{value});
        return error.InvalidValue;
    }
    try writer.print("SUCCESS: Processed {d}\n", .{value});
}

test "capture error messages" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    const result = processWithLogging(buffer.writer(testing.allocator), -5);
    try testing.expectError(error.InvalidValue, result);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "ERROR") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "-5") != null);
}

test "capture success messages" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try processWithLogging(buffer.writer(testing.allocator), 42);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "SUCCESS") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "42") != null);
}
```

The buffer captures output before the error is returned, allowing you to verify error messages were printed correctly.

### Verifying Structured Output

Test complex formatted output like tables:

```zig
fn printTable(writer: anytype) !void {
    try writer.writeAll("Name       | Age | City\n");
    try writer.writeAll("-----------+-----+----------\n");
    try writer.writeAll("Alice      |  30 | Seattle\n");
    try writer.writeAll("Bob        |  25 | Portland\n");
}

test "capture table output" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try printTable(buffer.writer(testing.allocator));

    // Verify table structure
    try testing.expect(std.mem.indexOf(u8, buffer.items, "Name") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "Alice") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "Bob") != null);

    // Count lines
    var line_count: usize = 0;
    for (buffer.items) |char| {
        if (char == '\n') line_count += 1;
    }
    try testing.expectEqual(4, line_count);
}
```

### Testing Special Output

#### JSON Output

```zig
fn printJSON(writer: anytype, name: []const u8, age: u8) !void {
    try writer.writeAll("{\n");
    try writer.print("  \"name\": \"{s}\",\n", .{name});
    try writer.print("  \"age\": {d}\n", .{age});
    try writer.writeAll("}\n");
}

test "verify JSON output structure" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try printJSON(buffer.writer(testing.allocator), "Alice", 30);

    // Verify JSON structure
    try testing.expect(std.mem.indexOf(u8, buffer.items, "{") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "}") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\"name\"") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\"Alice\"") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\"age\"") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "30") != null);
}
```

#### Progress Indicators

```zig
fn printProgress(writer: anytype, current: usize, total: usize) !void {
    const percent = @as(f64, @floatFromInt(current)) / @as(f64, @floatFromInt(total)) * 100.0;
    try writer.print("Progress: {d}/{d} ({d:.1}%)\n", .{ current, total, percent });
}

test "verify progress output" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try printProgress(buffer.writer(testing.allocator), 25, 100);

    try testing.expect(std.mem.indexOf(u8, buffer.items, "25/100") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "25.0%") != null);
}
```

#### ANSI Color Codes

```zig
fn printColoredOutput(writer: anytype) !void {
    const red = "\x1b[31m";
    const green = "\x1b[32m";
    const reset = "\x1b[0m";

    try writer.print("{s}Error{s}: Something went wrong\n", .{ red, reset });
    try writer.print("{s}Success{s}: Operation completed\n", .{ green, reset });
}

test "verify ANSI color codes in output" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try printColoredOutput(buffer.writer(testing.allocator));

    // Verify ANSI codes are present
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[31m") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[32m") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[0m") != null);
}
```

### Best Practices

1. **Design for testability**: Accept writer parameters rather than hardcoding `stdout`
2. **Use exact matches for simple output**: `expectEqualStrings` for predictable output
3. **Use pattern matching for complex output**: `indexOf` when format might vary
4. **Test both success and error paths**: Verify output in all scenarios
5. **Count lines for structure**: Validate output structure without hardcoding content

### Common Gotchas

**Forgetting the allocator**: In Zig 0.15.2, `ArrayList` is unmanaged and requires passing the allocator to `deinit` and `writer`:

```zig
var buffer = std.ArrayList(u8){};
defer buffer.deinit(testing.allocator);  // Pass allocator here
const writer = buffer.writer(testing.allocator);  // And here
```

**Comparing with wrong string endings**: Remember to include newlines in expected output if your functions print them.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_output
fn greet(writer: anytype, name: []const u8) !void {
    try writer.print("Hello, {s}!\n", .{name});
}
// ANCHOR_END: basic_output

// ANCHOR: testing_output
test "capture and verify stdout output" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    const writer = buffer.writer(testing.allocator);
    try greet(writer, "World");

    try testing.expectEqualStrings("Hello, World!\n", buffer.items);
}
// ANCHOR_END: testing_output

// ANCHOR: multiple_outputs
fn printReport(writer: anytype, items: usize, total: f64) !void {
    try writer.print("Items processed: {d}\n", .{items});
    try writer.print("Total value: ${d:.2}\n", .{total});
    try writer.writeAll("Status: Complete\n");
}

test "capture multiple output lines" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try printReport(buffer.writer(testing.allocator), 42, 123.45);

    const expected =
        \\Items processed: 42
        \\Total value: $123.45
        \\Status: Complete
        \\
    ;
    try testing.expectEqualStrings(expected, buffer.items);
}
// ANCHOR_END: multiple_outputs

// ANCHOR: formatted_output
fn formatData(writer: anytype, data: []const u8) !void {
    try writer.print("[INFO] Processing: {s}\n", .{data});
    try writer.print("[INFO] Length: {d} bytes\n", .{data.len});
}

test "verify formatted output" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try formatData(buffer.writer(testing.allocator), "test data");

    try testing.expect(std.mem.indexOf(u8, buffer.items, "[INFO]") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "test data") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "9 bytes") != null);
}
// ANCHOR_END: formatted_output

// ANCHOR: table_output
fn printTable(writer: anytype) !void {
    try writer.writeAll("Name       | Age | City\n");
    try writer.writeAll("-----------+-----+----------\n");
    try writer.writeAll("Alice      |  30 | Seattle\n");
    try writer.writeAll("Bob        |  25 | Portland\n");
}

test "capture table output" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try printTable(buffer.writer(testing.allocator));

    // Verify table structure
    try testing.expect(std.mem.indexOf(u8, buffer.items, "Name") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "Alice") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "Bob") != null);

    // Count lines
    var line_count: usize = 0;
    for (buffer.items) |char| {
        if (char == '\n') line_count += 1;
    }
    try testing.expectEqual(4, line_count);
}
// ANCHOR_END: table_output

// ANCHOR: error_messages
fn processWithLogging(writer: anytype, value: i32) !void {
    if (value < 0) {
        try writer.print("ERROR: Invalid value {d}\n", .{value});
        return error.InvalidValue;
    }
    try writer.print("SUCCESS: Processed {d}\n", .{value});
}

test "capture error messages" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    const result = processWithLogging(buffer.writer(testing.allocator), -5);
    try testing.expectError(error.InvalidValue, result);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "ERROR") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "-5") != null);
}

test "capture success messages" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try processWithLogging(buffer.writer(testing.allocator), 42);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "SUCCESS") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "42") != null);
}
// ANCHOR_END: error_messages

// ANCHOR: json_output
fn printJSON(writer: anytype, name: []const u8, age: u8) !void {
    try writer.writeAll("{\n");
    try writer.print("  \"name\": \"{s}\",\n", .{name});
    try writer.print("  \"age\": {d}\n", .{age});
    try writer.writeAll("}\n");
}

test "verify JSON output structure" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try printJSON(buffer.writer(testing.allocator), "Alice", 30);

    // Verify JSON structure
    try testing.expect(std.mem.indexOf(u8, buffer.items, "{") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "}") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\"name\"") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\"Alice\"") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\"age\"") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "30") != null);
}
// ANCHOR_END: json_output

// ANCHOR: progress_output
fn printProgress(writer: anytype, current: usize, total: usize) !void {
    const percent = @as(f64, @floatFromInt(current)) / @as(f64, @floatFromInt(total)) * 100.0;
    try writer.print("Progress: {d}/{d} ({d:.1}%)\n", .{ current, total, percent });
}

test "verify progress output" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try printProgress(buffer.writer(testing.allocator), 25, 100);

    try testing.expect(std.mem.indexOf(u8, buffer.items, "25/100") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "25.0%") != null);
}
// ANCHOR_END: progress_output

// ANCHOR: color_codes
fn printColoredOutput(writer: anytype) !void {
    const red = "\x1b[31m";
    const green = "\x1b[32m";
    const reset = "\x1b[0m";

    try writer.print("{s}Error{s}: Something went wrong\n", .{ red, reset });
    try writer.print("{s}Success{s}: Operation completed\n", .{ green, reset });
}

test "verify ANSI color codes in output" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    try printColoredOutput(buffer.writer(testing.allocator));

    // Verify ANSI codes are present
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[31m") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[32m") != null);
    try testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[0m") != null);
}
// ANCHOR_END: color_codes
```

### See Also

- Recipe 13.1: Accepting script input via redirection or pipes
- Recipe 14.3: Testing for exceptional conditions in unit tests
- Recipe 14.4: Logging test output to a file

---

## Recipe 14.2: Patching objects in unit tests {#recipe-14-2}

**Tags:** allocators, arraylist, c-interop, comptime, data-structures, error-handling, http, memory, networking, pointers, resource-cleanup, slices, testing, testing-debugging
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_2.zig`

### Problem

You need to test code that depends on external systems (databases, APIs, file systems) without actually using those systems. You want to replace dependencies with test doubles that provide controlled behavior.

### Solution

Use dependency injection with function pointers to swap real implementations for test implementations. Design your code to accept dependencies rather than creating them internally:

```zig
const DataSource = struct {
    fetchDataFn: *const fn (allocator: std.mem.Allocator) anyerror![]const u8,

    fn fetchData(self: *const DataSource, allocator: std.mem.Allocator) ![]const u8 {
        return self.fetchDataFn(allocator);
    }
};

fn realFetchData(allocator: std.mem.Allocator) ![]const u8 {
    // In real code, this might call an API
    return allocator.dupe(u8, "real data from API");
}

fn processData(source: *const DataSource, allocator: std.mem.Allocator) ![]const u8 {
    const data = try source.fetchData(allocator);
    defer allocator.free(data);

    // Process the data
    return std.fmt.allocPrint(allocator, "Processed: {s}", .{data});
}

test "patch data source with test implementation" {
    const TestFetchData = struct {
        fn fetch(allocator: std.mem.Allocator) ![]const u8 {
            return allocator.dupe(u8, "test data");
        }
    };

    const test_source = DataSource{ .fetchDataFn = TestFetchData.fetch };
    const result = try processData(&test_source, testing.allocator);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Processed: test data", result);
}
```

### Discussion

Zig doesn't have traditional mocking frameworks, but its explicit design and compile-time features make testing flexible and straightforward. The key is designing for testability from the start.

### Interface Pattern with Function Pointers

Create interfaces using structs with function pointers. This allows complete control over behavior during testing:

```zig
const FileSystem = struct {
    readFileFn: *const fn (ctx: *anyopaque, path: []const u8, allocator: std.mem.Allocator) anyerror![]const u8,
    ctx: *anyopaque,

    fn readFile(self: *const FileSystem, path: []const u8, allocator: std.mem.Allocator) ![]const u8 {
        return self.readFileFn(self.ctx, path, allocator);
    }
};

const RealFileSystem = struct {
    fn readFile(ctx: *anyopaque, path: []const u8, allocator: std.mem.Allocator) ![]const u8 {
        _ = ctx;
        _ = path;
        // In real code: return std.fs.cwd().readFileAlloc(allocator, path, 1024 * 1024);
        return allocator.dupe(u8, "file contents");
    }

    fn init() FileSystem {
        return .{
            .readFileFn = readFile,
            .ctx = undefined,
        };
    }
};

fn loadConfig(fs: *const FileSystem, allocator: std.mem.Allocator) ![]const u8 {
    return fs.readFile("config.txt", allocator);
}

test "patch filesystem with mock implementation" {
    const MockFileSystem = struct {
        fn readFile(ctx: *anyopaque, path: []const u8, allocator: std.mem.Allocator) ![]const u8 {
            _ = ctx;
            if (std.mem.eql(u8, path, "config.txt")) {
                return allocator.dupe(u8, "mock config data");
            }
            return error.FileNotFound;
        }
    };

    const mock_fs = FileSystem{
        .readFileFn = MockFileSystem.readFile,
        .ctx = undefined,
    };

    const config = try loadConfig(&mock_fs, testing.allocator);
    defer testing.allocator.free(config);

    try testing.expectEqualStrings("mock config data", config);
}
```

This pattern gives you:
- Complete isolation from external dependencies
- Control over return values and errors
- No need for complex mocking libraries

### Tracking State in Tests

Create test doubles that capture calls and state for verification:

```zig
const Logger = struct {
    logFn: *const fn (ctx: *anyopaque, level: []const u8, message: []const u8) void,
    ctx: *anyopaque,

    fn log(self: *Logger, level: []const u8, message: []const u8) void {
        self.logFn(self.ctx, level, message);
    }
};

const TestLogger = struct {
    messages: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) TestLogger {
        return .{
            .messages = std.ArrayList([]const u8){},
            .allocator = allocator,
        };
    }

    fn deinit(self: *TestLogger) void {
        for (self.messages.items) |msg| {
            self.allocator.free(msg);
        }
        self.messages.deinit(self.allocator);
    }

    fn log(ctx: *anyopaque, level: []const u8, message: []const u8) void {
        const self: *TestLogger = @ptrCast(@alignCast(ctx));
        const combined = std.fmt.allocPrint(self.allocator, "[{s}] {s}", .{ level, message }) catch return;
        self.messages.append(self.allocator, combined) catch return;
    }

    fn toLogger(self: *TestLogger) Logger {
        return .{
            .logFn = log,
            .ctx = @ptrCast(self),
        };
    }
};

fn doWork(logger: *Logger) void {
    logger.log("INFO", "Starting work");
    logger.log("DEBUG", "Processing item 1");
    logger.log("DEBUG", "Processing item 2");
    logger.log("INFO", "Work complete");
}

test "track logging calls with test logger" {
    var test_logger = TestLogger.init(testing.allocator);
    defer test_logger.deinit();

    var logger = test_logger.toLogger();
    doWork(&logger);

    try testing.expectEqual(@as(usize, 4), test_logger.messages.items.len);
    try testing.expect(std.mem.indexOf(u8, test_logger.messages.items[0], "Starting work") != null);
    try testing.expect(std.mem.indexOf(u8, test_logger.messages.items[3], "Work complete") != null);
}
```

The test logger captures all log messages, letting you verify logging behavior without polluting test output.

### Simulating Errors

Test error handling by creating implementations that return specific errors:

```zig
const Database = struct {
    queryFn: *const fn (ctx: *anyopaque, sql: []const u8) anyerror!i32,
    ctx: *anyopaque,

    fn query(self: *const Database, sql: []const u8) !i32 {
        return self.queryFn(self.ctx, sql);
    }
};

fn getUserCount(db: *const Database) !i32 {
    return db.query("SELECT COUNT(*) FROM users");
}

test "simulate database errors" {
    const ErrorDB = struct {
        fn query(ctx: *anyopaque, sql: []const u8) !i32 {
            _ = ctx;
            _ = sql;
            return error.ConnectionRefused;
        }
    };

    const error_db = Database{
        .queryFn = ErrorDB.query,
        .ctx = undefined,
    };

    const result = getUserCount(&error_db);
    try testing.expectError(error.ConnectionRefused, result);
}

test "simulate successful database query" {
    const SuccessDB = struct {
        fn query(ctx: *anyopaque, sql: []const u8) !i32 {
            _ = ctx;
            _ = sql;
            return 42;
        }
    };

    const success_db = Database{
        .queryFn = SuccessDB.query,
        .ctx = undefined,
    };

    const count = try getUserCount(&success_db);
    try testing.expectEqual(@as(i32, 42), count);
}
```

This ensures your error handling works correctly without needing actual failures.

### Compile-Time Test Mode

Use `comptime` parameters to switch between test and production code:

```zig
fn HttpClient(comptime test_mode: bool) type {
    return struct {
        const Self = @This();

        fn get(self: Self, url: []const u8, allocator: std.mem.Allocator) ![]const u8 {
            _ = self;
            if (test_mode) {
                // Test implementation
                if (std.mem.eql(u8, url, "https://api.example.com/data")) {
                    return allocator.dupe(u8, "{\"status\":\"ok\"}");
                }
                return error.NotFound;
            } else {
                // Real implementation would make actual HTTP request
                // In production, url would be used here
                const response = try std.fmt.allocPrint(allocator, "real response from {s}", .{url});
                return response;
            }
        }
    };
}

fn fetchData(client: anytype, allocator: std.mem.Allocator) ![]const u8 {
    return client.get("https://api.example.com/data", allocator);
}

test "use comptime test mode" {
    const TestClient = HttpClient(true);
    const client = TestClient{};

    const data = try fetchData(client, testing.allocator);
    defer testing.allocator.free(data);

    try testing.expectEqualStrings("{\"status\":\"ok\"}", data);
}
```

The compiler eliminates the test code in release builds, giving you zero runtime overhead.

### Counting Function Calls

Verify that functions are called the expected number of times:

```zig
const Counter = struct {
    count: usize = 0,

    fn increment(self: *Counter) void {
        self.count += 1;
    }
};

const ApiClient = struct {
    requestFn: *const fn (ctx: *anyopaque, endpoint: []const u8) anyerror!void,
    ctx: *anyopaque,
    counter: *Counter,

    fn request(self: *ApiClient, endpoint: []const u8) !void {
        self.counter.increment();
        return self.requestFn(self.ctx, endpoint);
    }
};

fn syncData(client: *ApiClient) !void {
    try client.request("/api/users");
    try client.request("/api/posts");
    try client.request("/api/comments");
}

test "count API calls" {
    const MockApi = struct {
        fn request(ctx: *anyopaque, endpoint: []const u8) !void {
            _ = ctx;
            _ = endpoint;
            // Do nothing, just count
        }
    };

    var counter = Counter{};
    var client = ApiClient{
        .requestFn = MockApi.request,
        .ctx = undefined,
        .counter = &counter,
    };

    try syncData(&client);
    try testing.expectEqual(@as(usize, 3), counter.count);
}
```

### Returning Sequences of Values

Test code that makes multiple calls by returning different values each time:

```zig
const ValueProvider = struct {
    values: []const i32,
    index: usize = 0,

    fn next(self: *ValueProvider) ?i32 {
        if (self.index >= self.values.len) return null;
        const value = self.values[self.index];
        self.index += 1;
        return value;
    }
};

const Sensor = struct {
    readFn: *const fn (ctx: *anyopaque) anyerror!i32,
    ctx: *anyopaque,

    fn read(self: *Sensor) !i32 {
        return self.readFn(self.ctx);
    }
};

fn collectReadings(sensor: *Sensor, count: usize, allocator: std.mem.Allocator) ![]i32 {
    var readings = try std.ArrayList(i32).initCapacity(allocator, count);
    errdefer readings.deinit(allocator);

    var i: usize = 0;
    while (i < count) : (i += 1) {
        const value = try sensor.read();
        try readings.append(allocator, value);
    }

    return readings.toOwnedSlice(allocator);
}

test "return sequence of values" {
    const test_values = [_]i32{ 10, 20, 30, 40 };
    var provider = ValueProvider{ .values = &test_values };

    const MockSensor = struct {
        fn read(ctx: *anyopaque) !i32 {
            const self: *ValueProvider = @ptrCast(@alignCast(ctx));
            return self.next() orelse error.NoMoreData;
        }
    };

    var sensor = Sensor{
        .readFn = MockSensor.read,
        .ctx = @ptrCast(&provider),
    };

    const readings = try collectReadings(&sensor, 4, testing.allocator);
    defer testing.allocator.free(readings);

    try testing.expectEqual(@as(usize, 4), readings.len);
    try testing.expectEqual(@as(i32, 10), readings[0]);
    try testing.expectEqual(@as(i32, 40), readings[3]);
}
```

This lets you simulate changing conditions or progressive state.

### Design Patterns for Testability

**1. Dependency Injection**
Pass dependencies as parameters rather than creating them internally:

```zig
// Hard to test
fn processData() !void {
    const db = Database.connect("localhost");  // Fixed dependency
    // ...
}

// Easy to test
fn processData(db: *const Database) !void {
    // db can be real or mock
}
```

**2. Function Pointer Tables**
Use structs with function pointers as lightweight interfaces:

```zig
const Storage = struct {
    saveFn: *const fn(*anyopaque, []const u8) anyerror!void,
    ctx: *anyopaque,
};
```

**3. Comptime Switching**
Use comptime parameters for test-specific behavior:

```zig
fn Client(comptime testing: bool) type {
    // Different behavior based on testing flag
}
```

### Best Practices

1. **Accept interfaces, not concrete types**: Use function pointers for flexibility
2. **Keep context opaque**: Use `*anyopaque` for context pointers
3. **Design for injection**: Pass dependencies rather than creating them
4. **Leverage comptime**: Use compile-time switches for test modes
5. **Create test builders**: Make helper functions to create test doubles
6. **Document test doubles**: Explain what behavior they simulate

### Common Gotchas

**Type safety with anyopaque**: When casting from `*anyopaque`, you must use both `@ptrCast` and `@alignCast`:

```zig
const self: *MyType = @ptrCast(@alignCast(ctx));
```

**Context lifetime**: The context pointer must outlive all uses of the struct containing it. Stack-allocated contexts work fine for tests.

**Error set compatibility**: Test implementations must return errors compatible with the expected error set. Use `anyerror` if needed, but prefer explicit error sets.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: dependency_injection
const DataSource = struct {
    fetchDataFn: *const fn (allocator: std.mem.Allocator) anyerror![]const u8,

    fn fetchData(self: *const DataSource, allocator: std.mem.Allocator) ![]const u8 {
        return self.fetchDataFn(allocator);
    }
};

fn realFetchData(allocator: std.mem.Allocator) ![]const u8 {
    // In real code, this might call an API
    return allocator.dupe(u8, "real data from API");
}

fn processData(source: *const DataSource, allocator: std.mem.Allocator) ![]const u8 {
    const data = try source.fetchData(allocator);
    defer allocator.free(data);

    // Process the data
    return std.fmt.allocPrint(allocator, "Processed: {s}", .{data});
}

test "patch data source with test implementation" {
    const TestFetchData = struct {
        fn fetch(allocator: std.mem.Allocator) ![]const u8 {
            return allocator.dupe(u8, "test data");
        }
    };

    const test_source = DataSource{ .fetchDataFn = TestFetchData.fetch };
    const result = try processData(&test_source, testing.allocator);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Processed: test data", result);
}
// ANCHOR_END: dependency_injection

// ANCHOR: interface_pattern
const FileSystem = struct {
    readFileFn: *const fn (ctx: *anyopaque, path: []const u8, allocator: std.mem.Allocator) anyerror![]const u8,
    ctx: *anyopaque,

    fn readFile(self: *const FileSystem, path: []const u8, allocator: std.mem.Allocator) ![]const u8 {
        return self.readFileFn(self.ctx, path, allocator);
    }
};

const RealFileSystem = struct {
    fn readFile(ctx: *anyopaque, path: []const u8, allocator: std.mem.Allocator) ![]const u8 {
        _ = ctx;
        _ = path;
        // In real code: return std.fs.cwd().readFileAlloc(allocator, path, 1024 * 1024);
        return allocator.dupe(u8, "file contents");
    }

    fn init() FileSystem {
        return .{
            .readFileFn = readFile,
            .ctx = undefined,
        };
    }
};

fn loadConfig(fs: *const FileSystem, allocator: std.mem.Allocator) ![]const u8 {
    return fs.readFile("config.txt", allocator);
}

test "patch filesystem with mock implementation" {
    const MockFileSystem = struct {
        fn readFile(ctx: *anyopaque, path: []const u8, allocator: std.mem.Allocator) ![]const u8 {
            _ = ctx;
            if (std.mem.eql(u8, path, "config.txt")) {
                return allocator.dupe(u8, "mock config data");
            }
            return error.FileNotFound;
        }
    };

    const mock_fs = FileSystem{
        .readFileFn = MockFileSystem.readFile,
        .ctx = undefined,
    };

    const config = try loadConfig(&mock_fs, testing.allocator);
    defer testing.allocator.free(config);

    try testing.expectEqualStrings("mock config data", config);
}
// ANCHOR_END: interface_pattern

// ANCHOR: state_tracking
const Logger = struct {
    logFn: *const fn (ctx: *anyopaque, level: []const u8, message: []const u8) void,
    ctx: *anyopaque,

    fn log(self: *Logger, level: []const u8, message: []const u8) void {
        self.logFn(self.ctx, level, message);
    }
};

const TestLogger = struct {
    messages: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) TestLogger {
        return .{
            .messages = std.ArrayList([]const u8){},
            .allocator = allocator,
        };
    }

    fn deinit(self: *TestLogger) void {
        for (self.messages.items) |msg| {
            self.allocator.free(msg);
        }
        self.messages.deinit(self.allocator);
    }

    fn log(ctx: *anyopaque, level: []const u8, message: []const u8) void {
        const self: *TestLogger = @ptrCast(@alignCast(ctx));
        const combined = std.fmt.allocPrint(self.allocator, "[{s}] {s}", .{ level, message }) catch return;
        self.messages.append(self.allocator, combined) catch return;
    }

    fn toLogger(self: *TestLogger) Logger {
        return .{
            .logFn = log,
            .ctx = @ptrCast(self),
        };
    }
};

fn doWork(logger: *Logger) void {
    logger.log("INFO", "Starting work");
    logger.log("DEBUG", "Processing item 1");
    logger.log("DEBUG", "Processing item 2");
    logger.log("INFO", "Work complete");
}

test "track logging calls with test logger" {
    var test_logger = TestLogger.init(testing.allocator);
    defer test_logger.deinit();

    var logger = test_logger.toLogger();
    doWork(&logger);

    try testing.expectEqual(@as(usize, 4), test_logger.messages.items.len);
    try testing.expect(std.mem.indexOf(u8, test_logger.messages.items[0], "Starting work") != null);
    try testing.expect(std.mem.indexOf(u8, test_logger.messages.items[3], "Work complete") != null);
}
// ANCHOR_END: state_tracking

// ANCHOR: error_simulation
const Database = struct {
    queryFn: *const fn (ctx: *anyopaque, sql: []const u8) anyerror!i32,
    ctx: *anyopaque,

    fn query(self: *const Database, sql: []const u8) !i32 {
        return self.queryFn(self.ctx, sql);
    }
};

fn getUserCount(db: *const Database) !i32 {
    return db.query("SELECT COUNT(*) FROM users");
}

test "simulate database errors" {
    const ErrorDB = struct {
        fn query(ctx: *anyopaque, sql: []const u8) !i32 {
            _ = ctx;
            _ = sql;
            return error.ConnectionRefused;
        }
    };

    const error_db = Database{
        .queryFn = ErrorDB.query,
        .ctx = undefined,
    };

    const result = getUserCount(&error_db);
    try testing.expectError(error.ConnectionRefused, result);
}

test "simulate successful database query" {
    const SuccessDB = struct {
        fn query(ctx: *anyopaque, sql: []const u8) !i32 {
            _ = ctx;
            _ = sql;
            return 42;
        }
    };

    const success_db = Database{
        .queryFn = SuccessDB.query,
        .ctx = undefined,
    };

    const count = try getUserCount(&success_db);
    try testing.expectEqual(@as(i32, 42), count);
}
// ANCHOR_END: error_simulation

// ANCHOR: comptime_switching
fn HttpClient(comptime test_mode: bool) type {
    return struct {
        const Self = @This();

        fn get(self: Self, url: []const u8, allocator: std.mem.Allocator) ![]const u8 {
            _ = self;
            if (test_mode) {
                // Test implementation
                if (std.mem.eql(u8, url, "https://api.example.com/data")) {
                    return allocator.dupe(u8, "{\"status\":\"ok\"}");
                }
                return error.NotFound;
            } else {
                // Real implementation would make actual HTTP request
                // In production, url would be used here
                const response = try std.fmt.allocPrint(allocator, "real response from {s}", .{url});
                return response;
            }
        }
    };
}

fn fetchData(client: anytype, allocator: std.mem.Allocator) ![]const u8 {
    return client.get("https://api.example.com/data", allocator);
}

test "use comptime test mode" {
    const TestClient = HttpClient(true);
    const client = TestClient{};

    const data = try fetchData(client, testing.allocator);
    defer testing.allocator.free(data);

    try testing.expectEqualStrings("{\"status\":\"ok\"}", data);
}
// ANCHOR_END: comptime_switching

// ANCHOR: call_counting
const Counter = struct {
    count: usize = 0,

    fn increment(self: *Counter) void {
        self.count += 1;
    }
};

const ApiClient = struct {
    requestFn: *const fn (ctx: *anyopaque, endpoint: []const u8) anyerror!void,
    ctx: *anyopaque,
    counter: *Counter,

    fn request(self: *ApiClient, endpoint: []const u8) !void {
        self.counter.increment();
        return self.requestFn(self.ctx, endpoint);
    }
};

fn syncData(client: *ApiClient) !void {
    try client.request("/api/users");
    try client.request("/api/posts");
    try client.request("/api/comments");
}

test "count API calls" {
    const MockApi = struct {
        fn request(ctx: *anyopaque, endpoint: []const u8) !void {
            _ = ctx;
            _ = endpoint;
            // Do nothing, just count
        }
    };

    var counter = Counter{};
    var client = ApiClient{
        .requestFn = MockApi.request,
        .ctx = undefined,
        .counter = &counter,
    };

    try syncData(&client);
    try testing.expectEqual(@as(usize, 3), counter.count);
}
// ANCHOR_END: call_counting

// ANCHOR: return_sequence
const ValueProvider = struct {
    values: []const i32,
    index: usize = 0,

    fn next(self: *ValueProvider) ?i32 {
        if (self.index >= self.values.len) return null;
        const value = self.values[self.index];
        self.index += 1;
        return value;
    }
};

const Sensor = struct {
    readFn: *const fn (ctx: *anyopaque) anyerror!i32,
    ctx: *anyopaque,

    fn read(self: *Sensor) !i32 {
        return self.readFn(self.ctx);
    }
};

fn collectReadings(sensor: *Sensor, count: usize, allocator: std.mem.Allocator) ![]i32 {
    var readings = try std.ArrayList(i32).initCapacity(allocator, count);
    errdefer readings.deinit(allocator);

    var i: usize = 0;
    while (i < count) : (i += 1) {
        const value = try sensor.read();
        try readings.append(allocator, value);
    }

    return readings.toOwnedSlice(allocator);
}

test "return sequence of values" {
    const test_values = [_]i32{ 10, 20, 30, 40 };
    var provider = ValueProvider{ .values = &test_values };

    const MockSensor = struct {
        fn read(ctx: *anyopaque) !i32 {
            const self: *ValueProvider = @ptrCast(@alignCast(ctx));
            return self.next() orelse error.NoMoreData;
        }
    };

    var sensor = Sensor{
        .readFn = MockSensor.read,
        .ctx = @ptrCast(&provider),
    };

    const readings = try collectReadings(&sensor, 4, testing.allocator);
    defer testing.allocator.free(readings);

    try testing.expectEqual(@as(usize, 4), readings.len);
    try testing.expectEqual(@as(i32, 10), readings[0]);
    try testing.expectEqual(@as(i32, 40), readings[3]);
}
// ANCHOR_END: return_sequence
```

### See Also

- Recipe 14.1: Testing program output sent to stdout
- Recipe 14.3: Testing for exceptional conditions in unit tests
- Recipe 0.13: Testing and Debugging Fundamentals
- Recipe 8.12: Defining an interface

---

## Recipe 14.3: Testing for exceptional conditions in unit tests {#recipe-14-3}

**Tags:** error-handling, http, networking, resource-cleanup, testing, testing-debugging
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_3.zig`

### Problem

You need to verify that your code correctly handles error conditions. You want to test that functions return the right errors, propagate errors properly, and recover from failures as expected.

### Solution

Use `testing.expectError` to verify that functions return specific errors:

```zig
fn divide(a: i32, b: i32) !i32 {
    if (b == 0) return error.DivisionByZero;
    return @divTrunc(a, b);
}

test "expect specific error" {
    const result = divide(10, 0);
    try testing.expectError(error.DivisionByZero, result);
}

test "successful operation returns value" {
    const result = try divide(10, 2);
    try testing.expectEqual(@as(i32, 5), result);
}
```

### Discussion

Error handling is critical in Zig. Testing error conditions ensures your code fails gracefully and provides meaningful feedback to callers.

### Testing Multiple Error Conditions

Create comprehensive tests for all possible error cases:

```zig
const FileError = error{
    NotFound,
    PermissionDenied,
    TooLarge,
    InvalidFormat,
};

fn readFile(path: []const u8, max_size: usize) FileError![]const u8 {
    if (path.len == 0) return error.NotFound;
    if (std.mem.startsWith(u8, path, "/restricted/")) return error.PermissionDenied;
    if (std.mem.startsWith(u8, path, "/large/")) return error.TooLarge;
    if (std.mem.endsWith(u8, path, ".bin")) return error.InvalidFormat;
    _ = max_size;
    return "file contents";
}

test "file not found error" {
    try testing.expectError(error.NotFound, readFile("", 1024));
}

test "permission denied error" {
    try testing.expectError(error.PermissionDenied, readFile("/restricted/secret.txt", 1024));
}

test "file too large error" {
    try testing.expectError(error.TooLarge, readFile("/large/data.txt", 1024));
}

test "invalid format error" {
    try testing.expectError(error.InvalidFormat, readFile("/data/file.bin", 1024));
}

test "successful file read" {
    const contents = try readFile("/data/file.txt", 1024);
    try testing.expectEqualStrings("file contents", contents);
}
```

Test every error in your error set to ensure complete coverage. This catches bugs where the wrong error is returned for a condition.

### Error Context and Validation

Test complex validation logic with descriptive errors:

```zig
const ValidationError = error{ TooShort, TooLong, InvalidCharacter, EmptyString };

const ValidationResult = struct {
    valid: bool,
    error_msg: ?[]const u8 = null,
};

fn validatePassword(password: []const u8) ValidationError!ValidationResult {
    if (password.len == 0) {
        return error.EmptyString;
    }
    if (password.len < 8) {
        return error.TooShort;
    }
    if (password.len > 128) {
        return error.TooLong;
    }
    for (password) |char| {
        if (char < 32 or char > 126) {
            return error.InvalidCharacter;
        }
    }
    return .{ .valid = true };
}

test "password validation errors" {
    try testing.expectError(error.EmptyString, validatePassword(""));
    try testing.expectError(error.TooShort, validatePassword("short"));
    try testing.expectError(error.TooLong, validatePassword("a" ** 129));
    try testing.expectError(error.InvalidCharacter, validatePassword("pass\x00word"));
}

test "valid password" {
    const result = try validatePassword("ValidPass123!");
    try testing.expect(result.valid);
}
```

### Error Propagation Through Call Stacks

Verify that errors propagate correctly through multiple function calls:

```zig
fn innerOperation(value: i32) !i32 {
    if (value < 0) return error.NegativeValue;
    return value * 2;
}

fn middleOperation(value: i32) !i32 {
    const result = try innerOperation(value);
    return result + 10;
}

fn outerOperation(value: i32) !i32 {
    const result = try middleOperation(value);
    return result * 3;
}

test "error propagates through call stack" {
    try testing.expectError(error.NegativeValue, outerOperation(-5));
}

test "successful propagation through stack" {
    // innerOperation(5) = 10, middleOperation = 20, outerOperation = 60
    const result = try outerOperation(5);
    try testing.expectEqual(@as(i32, 60), result);
}
```

The `try` keyword automatically propagates errors up the call stack. Test this behavior to ensure errors flow correctly.

### Checking Error Union Values

Sometimes you need to inspect error unions directly:

```zig
fn parseNumber(str: []const u8) !i32 {
    if (str.len == 0) return error.EmptyString;
    return std.fmt.parseInt(i32, str, 10);
}

test "check error union type" {
    const result = parseNumber("invalid");

    // Check if result is an error
    if (result) |value| {
        // This path shouldn't be taken
        _ = value;
        try testing.expect(false);
    } else |err| {
        // Verify it's a parse error
        try testing.expect(err == error.InvalidCharacter);
    }
}

test "check successful value" {
    const result = parseNumber("42");

    if (result) |value| {
        try testing.expectEqual(@as(i32, 42), value);
    } else |_| {
        try testing.expect(false);
    }
}
```

This pattern is useful when you need to handle both success and error cases in the same test or when the specific error matters.

### Testing Error Recovery

Test code that recovers from errors:

```zig
fn fetchDataWithRetry(url: []const u8, max_retries: u32) ![]const u8 {
    var retries: u32 = 0;
    while (retries < max_retries) : (retries += 1) {
        if (std.mem.eql(u8, url, "fail")) {
            if (retries < max_retries - 1) continue; // Retry
            return error.MaxRetriesExceeded;
        }
        return "success data";
    }
    return error.MaxRetriesExceeded;
}

test "error recovery with retries" {
    try testing.expectError(error.MaxRetriesExceeded, fetchDataWithRetry("fail", 3));
}

test "successful fetch" {
    const data = try fetchDataWithRetry("https://api.example.com", 3);
    try testing.expectEqualStrings("success data", data);
}
```

Retry logic and fallback mechanisms need careful testing to ensure they handle transient failures correctly.

### Custom Error Messages and Context

Test parser and state machine errors:

```zig
const Parser = struct {
    input: []const u8,
    pos: usize = 0,

    const Error = error{ UnexpectedToken, EndOfInput, InvalidSyntax };

    fn expect(self: *Parser, expected: u8) Error!void {
        if (self.pos >= self.input.len) return error.EndOfInput;
        if (self.input[self.pos] != expected) return error.UnexpectedToken;
        self.pos += 1;
    }

    fn parseList(self: *Parser) Error!void {
        try self.expect('[');
        if (self.pos >= self.input.len) return error.EndOfInput;
        if (self.input[self.pos] == ']') {
            self.pos += 1;
            return;
        }
        while (self.pos < self.input.len and self.input[self.pos] != ']') {
            self.pos += 1;
        }
        if (self.pos >= self.input.len) return error.InvalidSyntax;
        self.pos += 1;
    }
};

test "parser error conditions" {
    var parser1 = Parser{ .input = "hello" };
    try testing.expectError(error.UnexpectedToken, parser1.expect('['));

    var parser2 = Parser{ .input = "" };
    try testing.expectError(error.EndOfInput, parser2.expect('['));

    var parser3 = Parser{ .input = "[incomplete" };
    try testing.expectError(error.InvalidSyntax, parser3.parseList());
}

test "successful parsing" {
    var parser = Parser{ .input = "[items]" };
    try parser.parseList();
    try testing.expectEqual(@as(usize, 7), parser.pos);
}
```

State machines and parsers often have complex error conditions that need thorough testing.

### Testing Functions with anyerror

When functions use `anyerror`, test the specific errors they can return:

```zig
fn dynamicOperation(op: []const u8, a: i32, b: i32) anyerror!i32 {
    if (std.mem.eql(u8, op, "add")) return a + b;
    if (std.mem.eql(u8, op, "sub")) return a - b;
    if (std.mem.eql(u8, op, "div")) {
        if (b == 0) return error.DivisionByZero;
        return @divTrunc(a, b);
    }
    return error.UnknownOperation;
}

test "anyerror operations" {
    try testing.expectError(error.UnknownOperation, dynamicOperation("mult", 5, 3));
    try testing.expectError(error.DivisionByZero, dynamicOperation("div", 10, 0));

    const add_result = try dynamicOperation("add", 5, 3);
    try testing.expectEqual(@as(i32, 8), add_result);
}
```

Even with `anyerror`, you can still test for specific error values.

### Testing Error Traces

Test errors that occur at different stages of multi-step processes:

```zig
const ProcessError = error{ InvalidInput, ProcessingFailed, OutputError };

fn processStep1(data: []const u8) ProcessError![]const u8 {
    if (data.len == 0) return error.InvalidInput;
    return data;
}

fn processStep2(data: []const u8) ProcessError![]const u8 {
    if (data.len < 3) return error.ProcessingFailed;
    return data;
}

fn processStep3(data: []const u8) ProcessError![]const u8 {
    if (!std.mem.startsWith(u8, data, "valid")) return error.OutputError;
    return data;
}

fn processData(input: []const u8) ProcessError![]const u8 {
    const step1 = try processStep1(input);
    const step2 = try processStep2(step1);
    return processStep3(step2);
}

test "error at different processing steps" {
    try testing.expectError(error.InvalidInput, processData(""));
    try testing.expectError(error.ProcessingFailed, processData("ab"));
    try testing.expectError(error.OutputError, processData("invalid"));
}

test "successful processing" {
    const result = try processData("valid data");
    try testing.expectEqualStrings("valid data", result);
}
```

This ensures each processing step validates correctly and returns appropriate errors.

### Best Practices

1. **Test every error case**: Cover all possible errors in your error set
2. **Test the happy path too**: Always include tests for successful operations
3. **Use specific error assertions**: Prefer `expectError` over generic checks
4. **Test error propagation**: Verify errors flow correctly through call chains
5. **Test error recovery**: Ensure retry and fallback logic works
6. **Document error conditions**: Explain when each error occurs

### Error Testing Patterns

**Pattern 1: Exhaustive Error Testing**
```zig
test "all error conditions" {
    try testing.expectError(error.Case1, function(input1));
    try testing.expectError(error.Case2, function(input2));
    try testing.expectError(error.Case3, function(input3));
    // Test success case last
    _ = try function(validInput);
}
```

**Pattern 2: Error Set Verification**
```zig
test "error belongs to set" {
    const result = riskyOperation();
    if (result) |_| {
        try testing.expect(false); // Should have failed
    } else |err| {
        // Verify error is one of the expected ones
        try testing.expect(err == error.Type1 or err == error.Type2);
    }
}
```

**Pattern 3: State After Error**
```zig
test "state preserved after error" {
    var obj = Object.init();
    defer obj.deinit();

    _ = obj.operation() catch {};  // May fail
    try testing.expect(obj.isValid());  // But object still valid
}
```

### Common Gotchas

**Testing wrong error**: Make sure you test for the specific error the function should return, not just any error:

```zig
// Wrong - too broad
try testing.expect(result == error.NotFound or result == error.PermissionDenied);

// Right - specific
try testing.expectError(error.NotFound, result);
```

**Forgetting the success case**: Always test that valid inputs succeed:

```zig
test "complete validation testing" {
    // Test all error cases
    try testing.expectError(error.Invalid, validate(bad_input));

    // Don't forget the success case!
    try validate(good_input);
}
```

**Not testing error propagation**: Errors should propagate through `try`. Test this:

```zig
test "error propagates correctly" {
    // This ensures inner function errors reach outer
    try testing.expectError(error.Inner, outerFunction());
}
```

### Testing Error Messages

When errors include context, you might want to test the error and related data separately:

```zig
const ResultWithContext = struct {
    data: ?[]const u8,
    error_detail: ?[]const u8,
};

fn operationWithContext() !ResultWithContext {
    // ... operation that might fail with context
}

test "error provides context" {
    const result = operationWithContext() catch |err| {
        try testing.expectEqual(error.OperationFailed, err);
        // Check error was logged, state updated, etc.
        return;
    };
    try testing.expect(result.data != null);
}
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_error_testing
fn divide(a: i32, b: i32) !i32 {
    if (b == 0) return error.DivisionByZero;
    return @divTrunc(a, b);
}

test "expect specific error" {
    const result = divide(10, 0);
    try testing.expectError(error.DivisionByZero, result);
}

test "successful operation returns value" {
    const result = try divide(10, 2);
    try testing.expectEqual(@as(i32, 5), result);
}
// ANCHOR_END: basic_error_testing

// ANCHOR: multiple_errors
const FileError = error{
    NotFound,
    PermissionDenied,
    TooLarge,
    InvalidFormat,
};

fn readFile(path: []const u8, max_size: usize) FileError![]const u8 {
    if (path.len == 0) return error.NotFound;
    if (std.mem.startsWith(u8, path, "/restricted/")) return error.PermissionDenied;
    if (std.mem.startsWith(u8, path, "/large/")) return error.TooLarge;
    if (std.mem.endsWith(u8, path, ".bin")) return error.InvalidFormat;
    _ = max_size;
    return "file contents";
}

test "file not found error" {
    try testing.expectError(error.NotFound, readFile("", 1024));
}

test "permission denied error" {
    try testing.expectError(error.PermissionDenied, readFile("/restricted/secret.txt", 1024));
}

test "file too large error" {
    try testing.expectError(error.TooLarge, readFile("/large/data.txt", 1024));
}

test "invalid format error" {
    try testing.expectError(error.InvalidFormat, readFile("/data/file.bin", 1024));
}

test "successful file read" {
    const contents = try readFile("/data/file.txt", 1024);
    try testing.expectEqualStrings("file contents", contents);
}
// ANCHOR_END: multiple_errors

// ANCHOR: error_context
const ValidationError = error{ TooShort, TooLong, InvalidCharacter, EmptyString };

const ValidationResult = struct {
    valid: bool,
    error_msg: ?[]const u8 = null,
};

fn validatePassword(password: []const u8) ValidationError!ValidationResult {
    if (password.len == 0) {
        return error.EmptyString;
    }
    if (password.len < 8) {
        return error.TooShort;
    }
    if (password.len > 128) {
        return error.TooLong;
    }
    for (password) |char| {
        if (char < 32 or char > 126) {
            return error.InvalidCharacter;
        }
    }
    return .{ .valid = true };
}

test "password validation errors" {
    try testing.expectError(error.EmptyString, validatePassword(""));
    try testing.expectError(error.TooShort, validatePassword("short"));
    try testing.expectError(error.TooLong, validatePassword("a" ** 129));
    try testing.expectError(error.InvalidCharacter, validatePassword("pass\x00word"));
}

test "valid password" {
    const result = try validatePassword("ValidPass123!");
    try testing.expect(result.valid);
}
// ANCHOR_END: error_context

// ANCHOR: error_propagation
fn innerOperation(value: i32) !i32 {
    if (value < 0) return error.NegativeValue;
    return value * 2;
}

fn middleOperation(value: i32) !i32 {
    const result = try innerOperation(value);
    return result + 10;
}

fn outerOperation(value: i32) !i32 {
    const result = try middleOperation(value);
    return result * 3;
}

test "error propagates through call stack" {
    try testing.expectError(error.NegativeValue, outerOperation(-5));
}

test "successful propagation through stack" {
    // innerOperation(5) = 10, middleOperation = 20, outerOperation = 60
    const result = try outerOperation(5);
    try testing.expectEqual(@as(i32, 60), result);
}
// ANCHOR_END: error_propagation

// ANCHOR: error_union_checking
fn parseNumber(str: []const u8) !i32 {
    if (str.len == 0) return error.EmptyString;
    return std.fmt.parseInt(i32, str, 10);
}

test "check error union type" {
    const result = parseNumber("invalid");

    // Check if result is an error
    if (result) |value| {
        // This path shouldn't be taken
        _ = value;
        try testing.expect(false);
    } else |err| {
        // Verify it's a parse error
        try testing.expect(err == error.InvalidCharacter);
    }
}

test "check successful value" {
    const result = parseNumber("42");

    if (result) |value| {
        try testing.expectEqual(@as(i32, 42), value);
    } else |_| {
        try testing.expect(false);
    }
}
// ANCHOR_END: error_union_checking

// ANCHOR: error_recovery
fn fetchDataWithRetry(url: []const u8, max_retries: u32) ![]const u8 {
    var retries: u32 = 0;
    while (retries < max_retries) : (retries += 1) {
        if (std.mem.eql(u8, url, "fail")) {
            if (retries < max_retries - 1) continue; // Retry
            return error.MaxRetriesExceeded;
        }
        return "success data";
    }
    return error.MaxRetriesExceeded;
}

test "error recovery with retries" {
    try testing.expectError(error.MaxRetriesExceeded, fetchDataWithRetry("fail", 3));
}

test "successful fetch" {
    const data = try fetchDataWithRetry("https://api.example.com", 3);
    try testing.expectEqualStrings("success data", data);
}
// ANCHOR_END: error_recovery

// ANCHOR: custom_error_messages
const Parser = struct {
    input: []const u8,
    pos: usize = 0,

    const Error = error{ UnexpectedToken, EndOfInput, InvalidSyntax };

    fn expect(self: *Parser, expected: u8) Error!void {
        if (self.pos >= self.input.len) return error.EndOfInput;
        if (self.input[self.pos] != expected) return error.UnexpectedToken;
        self.pos += 1;
    }

    fn parseList(self: *Parser) Error!void {
        try self.expect('[');
        if (self.pos >= self.input.len) return error.EndOfInput;
        if (self.input[self.pos] == ']') {
            self.pos += 1;
            return;
        }
        while (self.pos < self.input.len and self.input[self.pos] != ']') {
            self.pos += 1;
        }
        if (self.pos >= self.input.len) return error.InvalidSyntax;
        self.pos += 1;
    }
};

test "parser error conditions" {
    var parser1 = Parser{ .input = "hello" };
    try testing.expectError(error.UnexpectedToken, parser1.expect('['));

    var parser2 = Parser{ .input = "" };
    try testing.expectError(error.EndOfInput, parser2.expect('['));

    var parser3 = Parser{ .input = "[incomplete" };
    try testing.expectError(error.InvalidSyntax, parser3.parseList());
}

test "successful parsing" {
    var parser = Parser{ .input = "[items]" };
    try parser.parseList();
    try testing.expectEqual(@as(usize, 7), parser.pos);
}
// ANCHOR_END: custom_error_messages

// ANCHOR: anyerror_testing
fn dynamicOperation(op: []const u8, a: i32, b: i32) anyerror!i32 {
    if (std.mem.eql(u8, op, "add")) return a + b;
    if (std.mem.eql(u8, op, "sub")) return a - b;
    if (std.mem.eql(u8, op, "div")) {
        if (b == 0) return error.DivisionByZero;
        return @divTrunc(a, b);
    }
    return error.UnknownOperation;
}

test "anyerror operations" {
    try testing.expectError(error.UnknownOperation, dynamicOperation("mult", 5, 3));
    try testing.expectError(error.DivisionByZero, dynamicOperation("div", 10, 0));

    const add_result = try dynamicOperation("add", 5, 3);
    try testing.expectEqual(@as(i32, 8), add_result);
}
// ANCHOR_END: anyerror_testing

// ANCHOR: error_trace
const ProcessError = error{ InvalidInput, ProcessingFailed, OutputError };

fn processStep1(data: []const u8) ProcessError![]const u8 {
    if (data.len == 0) return error.InvalidInput;
    return data;
}

fn processStep2(data: []const u8) ProcessError![]const u8 {
    if (data.len < 3) return error.ProcessingFailed;
    return data;
}

fn processStep3(data: []const u8) ProcessError![]const u8 {
    if (!std.mem.startsWith(u8, data, "valid")) return error.OutputError;
    return data;
}

fn processData(input: []const u8) ProcessError![]const u8 {
    const step1 = try processStep1(input);
    const step2 = try processStep2(step1);
    return processStep3(step2);
}

test "error at different processing steps" {
    try testing.expectError(error.InvalidInput, processData(""));
    try testing.expectError(error.ProcessingFailed, processData("ab"));
    try testing.expectError(error.OutputError, processData("invalid"));
}

test "successful processing" {
    const result = try processData("valid data");
    try testing.expectEqualStrings("valid data", result);
}
// ANCHOR_END: error_trace
```

### See Also

- Recipe 14.1: Testing program output sent to stdout
- Recipe 14.2: Patching objects in unit tests
- Recipe 0.11: Optionals, Errors, and Resource Cleanup
- Recipe 1.2: Error Handling Patterns

---

## Recipe 14.4: Logging test output to a file {#recipe-14-4}

**Tags:** allocators, arraylist, comptime, concurrency, data-structures, error-handling, json, memory, parsing, resource-cleanup, testing, testing-debugging, threading
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_4.zig`

### Problem

You need to capture test output to files for later analysis, debugging, or record-keeping. You want structured logs that can be reviewed after tests complete, especially for long-running test suites or CI/CD pipelines.

### Solution

Create a logger that writes test output to files. Use file I/O to capture logs and verify them after tests complete:

```zig
const TestLogger = struct {
    file: std.fs.File,
    allocator: std.mem.Allocator,

    fn init(path: []const u8, allocator: std.mem.Allocator) !TestLogger {
        const file = try std.fs.cwd().createFile(path, .{});
        return .{
            .file = file,
            .allocator = allocator,
        };
    }

    fn deinit(self: *TestLogger) void {
        self.file.close();
    }

    fn log(self: *TestLogger, comptime fmt: []const u8, args: anytype) !void {
        const msg = try std.fmt.allocPrint(self.allocator, fmt ++ "\n", args);
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }
};

test "write test logs to file" {
    var logger = try TestLogger.init("test_output.log", testing.allocator);
    defer logger.deinit();
    defer std.fs.cwd().deleteFile("test_output.log") catch {};

    try logger.log("Test started", .{});
    try logger.log("Processing item {d}", .{42});
    try logger.log("Test completed", .{});

    // Verify file was written
    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "test_output.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Test started") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Processing item 42") != null);
}
```

### Discussion

File logging helps debug test failures, analyze performance, and maintain test records. Unlike console output, file logs persist and can be parsed by other tools.

### Timestamped Logging

Add timestamps to track test execution timing:

```zig
const TimestampedLogger = struct {
    file: std.fs.File,
    allocator: std.mem.Allocator,
    start_time: i64,

    fn init(path: []const u8, allocator: std.mem.Allocator) !TimestampedLogger {
        const file = try std.fs.cwd().createFile(path, .{});
        return .{
            .file = file,
            .allocator = allocator,
            .start_time = std.time.milliTimestamp(),
        };
    }

    fn deinit(self: *TimestampedLogger) void {
        self.file.close();
    }

    fn log(self: *TimestampedLogger, level: []const u8, comptime fmt: []const u8, args: anytype) !void {
        const elapsed = std.time.milliTimestamp() - self.start_time;
        const msg = try std.fmt.allocPrint(self.allocator, "[{d}ms] [{s}] " ++ fmt ++ "\n", .{ elapsed, level } ++ args);
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }
};

test "timestamped test logging" {
    var logger = try TimestampedLogger.init("timestamped.log", testing.allocator);
    defer logger.deinit();
    defer std.fs.cwd().deleteFile("timestamped.log") catch {};

    try logger.log("INFO", "Test initialization", .{});
    std.Thread.sleep(10 * std.time.ns_per_ms); // Sleep 10ms
    try logger.log("DEBUG", "Processing data", .{});
    try logger.log("INFO", "Test complete", .{});

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "timestamped.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "[INFO]") != null);
    try testing.expect(std.mem.indexOf(u8, content, "[DEBUG]") != null);
}
```

Timestamps help identify slow tests and understand execution flow.

### Using Temporary Directories

Use temporary directories for test logs to avoid cluttering your workspace:

```zig
fn runTestWithTempLog(allocator: std.mem.Allocator) ![]const u8 {
    // Create temporary file for test logs
    var tmp_dir = std.testing.tmpDir(.{});
    var dir = tmp_dir.dir;
    defer tmp_dir.cleanup();

    const log_file = try dir.createFile("test.log", .{ .read = true });
    defer log_file.close();

    try log_file.writeAll("Test execution started\n");
    try log_file.writeAll("Running validation checks\n");
    try log_file.writeAll("All checks passed\n");

    // Read back the log
    try log_file.seekTo(0);
    return log_file.readToEndAlloc(allocator, 1024 * 1024);
}

test "use temporary directory for test logs" {
    const log_content = try runTestWithTempLog(testing.allocator);
    defer testing.allocator.free(log_content);

    try testing.expect(std.mem.indexOf(u8, log_content, "Test execution started") != null);
    try testing.expect(std.mem.indexOf(u8, log_content, "All checks passed") != null);
}
```

Temporary directories are automatically cleaned up, keeping your file system clean.

### Structured JSON Logging

Log structured data for programmatic analysis:

```zig
const StructuredLogger = struct {
    file: std.fs.File,
    allocator: std.mem.Allocator,
    test_name: []const u8,

    fn init(path: []const u8, test_name: []const u8, allocator: std.mem.Allocator) !StructuredLogger {
        const file = try std.fs.cwd().createFile(path, .{});
        var self = StructuredLogger{
            .file = file,
            .allocator = allocator,
            .test_name = test_name,
        };
        try self.logTestStart();
        return self;
    }

    fn deinit(self: *StructuredLogger) void {
        self.logTestEnd() catch {};
        self.file.close();
    }

    fn logTestStart(self: *StructuredLogger) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "{{\"event\":\"test_start\",\"name\":\"{s}\"}}\n", .{self.test_name});
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }

    fn logTestEnd(self: *StructuredLogger) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "{{\"event\":\"test_end\",\"name\":\"{s}\"}}\n", .{self.test_name});
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }

    fn logAssertion(self: *StructuredLogger, assertion: []const u8, passed: bool) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "{{\"event\":\"assertion\",\"name\":\"{s}\",\"passed\":{}}}\n", .{ assertion, passed });
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }
};

test "structured JSON logging" {
    var logger = try StructuredLogger.init("structured.log", "validation_test", testing.allocator);
    defer std.fs.cwd().deleteFile("structured.log") catch {};

    try logger.logAssertion("value_is_positive", true);
    try logger.logAssertion("value_within_range", true);
    try logger.logAssertion("value_not_zero", false);

    logger.deinit(); // Close file before reading

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "structured.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "test_start") != null);
    try testing.expect(std.mem.indexOf(u8, content, "assertion") != null);
    try testing.expect(std.mem.indexOf(u8, content, "test_end") != null);
}
```

JSON logs can be parsed by log aggregation tools and analyzed programmatically.

### Logging Multiple Test Results

Track results from multiple tests in a single log file:

```zig
const TestSuite = struct {
    log_file: std.fs.File,
    allocator: std.mem.Allocator,
    tests_run: usize = 0,
    tests_passed: usize = 0,

    fn init(path: []const u8, allocator: std.mem.Allocator) !TestSuite {
        const file = try std.fs.cwd().createFile(path, .{});
        return .{
            .log_file = file,
            .allocator = allocator,
        };
    }

    fn deinit(self: *TestSuite) void {
        self.writeSummary() catch {};
        self.log_file.close();
    }

    fn runTest(self: *TestSuite, name: []const u8, passed: bool) !void {
        self.tests_run += 1;
        if (passed) self.tests_passed += 1;

        const status = if (passed) "PASS" else "FAIL";
        const msg = try std.fmt.allocPrint(self.allocator, "[{s}] {s}\n", .{ status, name });
        defer self.allocator.free(msg);
        try self.log_file.writeAll(msg);
    }

    fn writeSummary(self: *TestSuite) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "\nSummary: {d}/{d} tests passed\n", .{ self.tests_passed, self.tests_run });
        defer self.allocator.free(msg);
        try self.log_file.writeAll(msg);
    }
};

test "log multiple test results" {
    var suite = try TestSuite.init("suite.log", testing.allocator);
    defer std.fs.cwd().deleteFile("suite.log") catch {};

    try suite.runTest("test_addition", true);
    try suite.runTest("test_subtraction", true);
    try suite.runTest("test_division", false);
    try suite.runTest("test_multiplication", true);

    suite.deinit(); // Close file before reading

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "suite.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "[PASS] test_addition") != null);
    try testing.expect(std.mem.indexOf(u8, content, "[FAIL] test_division") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Summary: 3/4 tests passed") != null);
}
```

This pattern is useful for test runners and reporting tools.

### Error Logging

Capture and log errors during testing:

```zig
const ErrorLogger = struct {
    file: std.fs.File,
    allocator: std.mem.Allocator,

    fn init(path: []const u8, allocator: std.mem.Allocator) !ErrorLogger {
        const file = try std.fs.cwd().createFile(path, .{});
        return .{
            .file = file,
            .allocator = allocator,
        };
    }

    fn deinit(self: *ErrorLogger) void {
        self.file.close();
    }

    fn logError(self: *ErrorLogger, err: anyerror, context: []const u8) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "ERROR: {s} - {s}\n", .{ @errorName(err), context });
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }

    fn logSuccess(self: *ErrorLogger, operation: []const u8) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "SUCCESS: {s}\n", .{operation});
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }
};

fn riskyOperation(value: i32) !i32 {
    if (value < 0) return error.InvalidValue;
    if (value > 100) return error.OutOfRange;
    return value * 2;
}

test "log errors during testing" {
    var logger = try ErrorLogger.init("errors.log", testing.allocator);
    defer logger.deinit();
    defer std.fs.cwd().deleteFile("errors.log") catch {};

    // Test error cases
    if (riskyOperation(-5)) |_| {
        try logger.logSuccess("negative value handling");
    } else |err| {
        try logger.logError(err, "processing negative value");
    }

    if (riskyOperation(200)) |_| {
        try logger.logSuccess("large value handling");
    } else |err| {
        try logger.logError(err, "processing large value");
    }

    // Test success case
    if (riskyOperation(50)) |_| {
        try logger.logSuccess("valid value processing");
    } else |err| {
        try logger.logError(err, "processing valid value");
    }

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "errors.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "ERROR: InvalidValue") != null);
    try testing.expect(std.mem.indexOf(u8, content, "ERROR: OutOfRange") != null);
    try testing.expect(std.mem.indexOf(u8, content, "SUCCESS: valid value processing") != null);
}
```

Error logs help diagnose failures and track error patterns.

### Buffered Logging

Buffer log entries in memory before writing to reduce I/O:

```zig
const BufferedTestLogger = struct {
    buffer: std.ArrayList(u8),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) BufferedTestLogger {
        return .{
            .buffer = std.ArrayList(u8){},
            .allocator = allocator,
        };
    }

    fn deinit(self: *BufferedTestLogger) void {
        self.buffer.deinit(self.allocator);
    }

    fn log(self: *BufferedTestLogger, comptime fmt: []const u8, args: anytype) !void {
        const writer = self.buffer.writer(self.allocator);
        try writer.print(fmt, args);
        try writer.writeAll("\n");
    }

    fn writeToFile(self: *BufferedTestLogger, path: []const u8) !void {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
        try file.writeAll(self.buffer.items);
    }
};

test "buffered logging with file write" {
    var logger = BufferedTestLogger.init(testing.allocator);
    defer logger.deinit();

    try logger.log("Starting test suite", .{});
    try logger.log("Test 1: {s}", .{"PASSED"});
    try logger.log("Test 2: {s}", .{"PASSED"});
    try logger.log("Test 3: {s}", .{"FAILED"});

    // Write buffer to file
    try logger.writeToFile("buffered.log");
    defer std.fs.cwd().deleteFile("buffered.log") catch {};

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "buffered.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Starting test suite") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Test 3: FAILED") != null);
}
```

Buffering improves performance when writing many small log entries.

### Performance Logging

Log timing information to identify slow tests:

```zig
const PerfLogger = struct {
    file: std.fs.File,
    allocator: std.mem.Allocator,

    fn init(path: []const u8, allocator: std.mem.Allocator) !PerfLogger {
        const file = try std.fs.cwd().createFile(path, .{});
        return .{
            .file = file,
            .allocator = allocator,
        };
    }

    fn deinit(self: *PerfLogger) void {
        self.file.close();
    }

    fn logTiming(self: *PerfLogger, operation: []const u8, duration_ns: u64) !void {
        const duration_ms = @as(f64, @floatFromInt(duration_ns)) / @as(f64, @floatFromInt(std.time.ns_per_ms));
        const msg = try std.fmt.allocPrint(self.allocator, "{s}: {d:.3}ms\n", .{ operation, duration_ms });
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }
};

fn benchmarkOperation() void {
    var sum: u64 = 0;
    var i: u64 = 0;
    while (i < 1000000) : (i += 1) {
        sum +%= i;
    }
    std.mem.doNotOptimizeAway(sum);
}

test "log performance metrics" {
    var logger = try PerfLogger.init("perf.log", testing.allocator);
    defer logger.deinit();
    defer std.fs.cwd().deleteFile("perf.log") catch {};

    const start = std.time.nanoTimestamp();
    benchmarkOperation();
    const end = std.time.nanoTimestamp();

    try logger.logTiming("benchmark_operation", @intCast(end - start));

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "perf.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "benchmark_operation") != null);
    try testing.expect(std.mem.indexOf(u8, content, "ms") != null);
}
```

Performance logs help optimize slow tests and identify regressions.

### Best Practices

1. **Close files before reading**: Call `deinit()` before reading log files to ensure all data is flushed
2. **Use temporary directories**: Leverage `std.testing.tmpDir` for automatic cleanup
3. **Structure your logs**: Use JSON or other structured formats for easier parsing
4. **Include timestamps**: Help correlate log entries with test execution
5. **Log errors separately**: Make errors easy to find and analyze
6. **Clean up test files**: Always delete log files after tests complete
7. **Buffer when appropriate**: Use buffering for high-frequency logging

### File Logging Patterns

**Pattern 1: Logger with Auto-flush**
```zig
const Logger = struct {
    file: std.fs.File,

    fn deinit(self: *Logger) void {
        self.file.sync() catch {}; // Ensure data is written
        self.file.close();
    }
};
```

**Pattern 2: Test Suite Logger**
```zig
fn runTestSuite(log_path: []const u8) !void {
    var logger = try Logger.init(log_path);
    defer logger.deinit();

    // Run tests, logging results
    logger.logStart();
    defer logger.logEnd();
}
```

**Pattern 3: Hierarchical Logs**
```zig
// tests/
//   ├── suite1.log
//   ├── suite2.log
//   └── summary.log

// Each test suite writes to its own file
// Summary aggregates all results
```

### Common Gotchas

**Not flushing before reading**: Files must be closed or synced before reading:

```zig
// Wrong - file not yet flushed
logger.log("test");
const content = try std.fs.cwd().readFileAlloc(...);

// Right - close first
logger.log("test");
logger.deinit(); // Flushes and closes
const content = try std.fs.cwd().readFileAlloc(...);
```

**Forgetting cleanup**: Always delete test log files:

```zig
test "example" {
    var logger = try Logger.init("test.log");
    defer logger.deinit();
    defer std.fs.cwd().deleteFile("test.log") catch {}; // Don't forget!
}
```

**Wrong file permissions**: Open files with `.read = true` if you need to read back:

```zig
// For read-write access
const file = try dir.createFile("log.txt", .{ .read = true });
```

### Integration with CI/CD

File logs integrate well with continuous integration:

```zig
// CI-friendly logging
const ci_mode = std.process.getEnvVarOwned(allocator, "CI") catch null;
const logger = if (ci_mode != null)
    try StructuredLogger.init("ci-results.json")
else
    try ConsoleLogger.init();
```

This allows different logging strategies for local development versus CI environments.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_file_logging
const TestLogger = struct {
    file: std.fs.File,
    allocator: std.mem.Allocator,

    fn init(path: []const u8, allocator: std.mem.Allocator) !TestLogger {
        const file = try std.fs.cwd().createFile(path, .{});
        return .{
            .file = file,
            .allocator = allocator,
        };
    }

    fn deinit(self: *TestLogger) void {
        self.file.close();
    }

    fn log(self: *TestLogger, comptime fmt: []const u8, args: anytype) !void {
        const msg = try std.fmt.allocPrint(self.allocator, fmt ++ "\n", args);
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }
};

test "write test logs to file" {
    var logger = try TestLogger.init("test_output.log", testing.allocator);
    defer logger.deinit();
    defer std.fs.cwd().deleteFile("test_output.log") catch {};

    try logger.log("Test started", .{});
    try logger.log("Processing item {d}", .{42});
    try logger.log("Test completed", .{});

    // Verify file was written
    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "test_output.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Test started") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Processing item 42") != null);
}
// ANCHOR_END: basic_file_logging

// ANCHOR: timestamped_logging
const TimestampedLogger = struct {
    file: std.fs.File,
    allocator: std.mem.Allocator,
    start_time: i64,

    fn init(path: []const u8, allocator: std.mem.Allocator) !TimestampedLogger {
        const file = try std.fs.cwd().createFile(path, .{});
        return .{
            .file = file,
            .allocator = allocator,
            .start_time = std.time.milliTimestamp(),
        };
    }

    fn deinit(self: *TimestampedLogger) void {
        self.file.close();
    }

    fn log(self: *TimestampedLogger, level: []const u8, comptime fmt: []const u8, args: anytype) !void {
        const elapsed = std.time.milliTimestamp() - self.start_time;
        const msg = try std.fmt.allocPrint(self.allocator, "[{d}ms] [{s}] " ++ fmt ++ "\n", .{ elapsed, level } ++ args);
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }
};

test "timestamped test logging" {
    var logger = try TimestampedLogger.init("timestamped.log", testing.allocator);
    defer logger.deinit();
    defer std.fs.cwd().deleteFile("timestamped.log") catch {};

    try logger.log("INFO", "Test initialization", .{});
    std.Thread.sleep(10 * std.time.ns_per_ms); // Sleep 10ms
    try logger.log("DEBUG", "Processing data", .{});
    try logger.log("INFO", "Test complete", .{});

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "timestamped.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "[INFO]") != null);
    try testing.expect(std.mem.indexOf(u8, content, "[DEBUG]") != null);
}
// ANCHOR_END: timestamped_logging

// ANCHOR: temp_file_logging
fn runTestWithTempLog(allocator: std.mem.Allocator) ![]const u8 {
    // Create temporary file for test logs
    var tmp_dir = std.testing.tmpDir(.{});
    var dir = tmp_dir.dir;
    defer tmp_dir.cleanup();

    const log_file = try dir.createFile("test.log", .{ .read = true });
    defer log_file.close();

    try log_file.writeAll("Test execution started\n");
    try log_file.writeAll("Running validation checks\n");
    try log_file.writeAll("All checks passed\n");

    // Read back the log
    try log_file.seekTo(0);
    return log_file.readToEndAlloc(allocator, 1024 * 1024);
}

test "use temporary directory for test logs" {
    const log_content = try runTestWithTempLog(testing.allocator);
    defer testing.allocator.free(log_content);

    try testing.expect(std.mem.indexOf(u8, log_content, "Test execution started") != null);
    try testing.expect(std.mem.indexOf(u8, log_content, "All checks passed") != null);
}
// ANCHOR_END: temp_file_logging

// ANCHOR: structured_logging
const StructuredLogger = struct {
    file: std.fs.File,
    allocator: std.mem.Allocator,
    test_name: []const u8,

    fn init(path: []const u8, test_name: []const u8, allocator: std.mem.Allocator) !StructuredLogger {
        const file = try std.fs.cwd().createFile(path, .{});
        var self = StructuredLogger{
            .file = file,
            .allocator = allocator,
            .test_name = test_name,
        };
        try self.logTestStart();
        return self;
    }

    fn deinit(self: *StructuredLogger) void {
        self.logTestEnd() catch {};
        self.file.close();
    }

    fn logTestStart(self: *StructuredLogger) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "{{\"event\":\"test_start\",\"name\":\"{s}\"}}\n", .{self.test_name});
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }

    fn logTestEnd(self: *StructuredLogger) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "{{\"event\":\"test_end\",\"name\":\"{s}\"}}\n", .{self.test_name});
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }

    fn logAssertion(self: *StructuredLogger, assertion: []const u8, passed: bool) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "{{\"event\":\"assertion\",\"name\":\"{s}\",\"passed\":{}}}\n", .{ assertion, passed });
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }
};

test "structured JSON logging" {
    var logger = try StructuredLogger.init("structured.log", "validation_test", testing.allocator);
    defer std.fs.cwd().deleteFile("structured.log") catch {};

    try logger.logAssertion("value_is_positive", true);
    try logger.logAssertion("value_within_range", true);
    try logger.logAssertion("value_not_zero", false);

    logger.deinit(); // Close file before reading

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "structured.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "test_start") != null);
    try testing.expect(std.mem.indexOf(u8, content, "assertion") != null);
    try testing.expect(std.mem.indexOf(u8, content, "test_end") != null);
}
// ANCHOR_END: structured_logging

// ANCHOR: multi_test_logging
const TestSuite = struct {
    log_file: std.fs.File,
    allocator: std.mem.Allocator,
    tests_run: usize = 0,
    tests_passed: usize = 0,

    fn init(path: []const u8, allocator: std.mem.Allocator) !TestSuite {
        const file = try std.fs.cwd().createFile(path, .{});
        return .{
            .log_file = file,
            .allocator = allocator,
        };
    }

    fn deinit(self: *TestSuite) void {
        self.writeSummary() catch {};
        self.log_file.close();
    }

    fn runTest(self: *TestSuite, name: []const u8, passed: bool) !void {
        self.tests_run += 1;
        if (passed) self.tests_passed += 1;

        const status = if (passed) "PASS" else "FAIL";
        const msg = try std.fmt.allocPrint(self.allocator, "[{s}] {s}\n", .{ status, name });
        defer self.allocator.free(msg);
        try self.log_file.writeAll(msg);
    }

    fn writeSummary(self: *TestSuite) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "\nSummary: {d}/{d} tests passed\n", .{ self.tests_passed, self.tests_run });
        defer self.allocator.free(msg);
        try self.log_file.writeAll(msg);
    }
};

test "log multiple test results" {
    var suite = try TestSuite.init("suite.log", testing.allocator);
    defer std.fs.cwd().deleteFile("suite.log") catch {};

    try suite.runTest("test_addition", true);
    try suite.runTest("test_subtraction", true);
    try suite.runTest("test_division", false);
    try suite.runTest("test_multiplication", true);

    suite.deinit(); // Close file before reading

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "suite.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "[PASS] test_addition") != null);
    try testing.expect(std.mem.indexOf(u8, content, "[FAIL] test_division") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Summary: 3/4 tests passed") != null);
}
// ANCHOR_END: multi_test_logging

// ANCHOR: error_logging
const ErrorLogger = struct {
    file: std.fs.File,
    allocator: std.mem.Allocator,

    fn init(path: []const u8, allocator: std.mem.Allocator) !ErrorLogger {
        const file = try std.fs.cwd().createFile(path, .{});
        return .{
            .file = file,
            .allocator = allocator,
        };
    }

    fn deinit(self: *ErrorLogger) void {
        self.file.close();
    }

    fn logError(self: *ErrorLogger, err: anyerror, context: []const u8) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "ERROR: {s} - {s}\n", .{ @errorName(err), context });
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }

    fn logSuccess(self: *ErrorLogger, operation: []const u8) !void {
        const msg = try std.fmt.allocPrint(self.allocator, "SUCCESS: {s}\n", .{operation});
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }
};

fn riskyOperation(value: i32) !i32 {
    if (value < 0) return error.InvalidValue;
    if (value > 100) return error.OutOfRange;
    return value * 2;
}

test "log errors during testing" {
    var logger = try ErrorLogger.init("errors.log", testing.allocator);
    defer logger.deinit();
    defer std.fs.cwd().deleteFile("errors.log") catch {};

    // Test error cases
    if (riskyOperation(-5)) |_| {
        try logger.logSuccess("negative value handling");
    } else |err| {
        try logger.logError(err, "processing negative value");
    }

    if (riskyOperation(200)) |_| {
        try logger.logSuccess("large value handling");
    } else |err| {
        try logger.logError(err, "processing large value");
    }

    // Test success case
    if (riskyOperation(50)) |_| {
        try logger.logSuccess("valid value processing");
    } else |err| {
        try logger.logError(err, "processing valid value");
    }

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "errors.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "ERROR: InvalidValue") != null);
    try testing.expect(std.mem.indexOf(u8, content, "ERROR: OutOfRange") != null);
    try testing.expect(std.mem.indexOf(u8, content, "SUCCESS: valid value processing") != null);
}
// ANCHOR_END: error_logging

// ANCHOR: buffered_logging
const BufferedTestLogger = struct {
    buffer: std.ArrayList(u8),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) BufferedTestLogger {
        return .{
            .buffer = std.ArrayList(u8){},
            .allocator = allocator,
        };
    }

    fn deinit(self: *BufferedTestLogger) void {
        self.buffer.deinit(self.allocator);
    }

    fn log(self: *BufferedTestLogger, comptime fmt: []const u8, args: anytype) !void {
        const writer = self.buffer.writer(self.allocator);
        try writer.print(fmt, args);
        try writer.writeAll("\n");
    }

    fn writeToFile(self: *BufferedTestLogger, path: []const u8) !void {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
        try file.writeAll(self.buffer.items);
    }
};

test "buffered logging with file write" {
    var logger = BufferedTestLogger.init(testing.allocator);
    defer logger.deinit();

    try logger.log("Starting test suite", .{});
    try logger.log("Test 1: {s}", .{"PASSED"});
    try logger.log("Test 2: {s}", .{"PASSED"});
    try logger.log("Test 3: {s}", .{"FAILED"});

    // Write buffer to file
    try logger.writeToFile("buffered.log");
    defer std.fs.cwd().deleteFile("buffered.log") catch {};

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "buffered.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Starting test suite") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Test 3: FAILED") != null);
}
// ANCHOR_END: buffered_logging

// ANCHOR: performance_logging
const PerfLogger = struct {
    file: std.fs.File,
    allocator: std.mem.Allocator,

    fn init(path: []const u8, allocator: std.mem.Allocator) !PerfLogger {
        const file = try std.fs.cwd().createFile(path, .{});
        return .{
            .file = file,
            .allocator = allocator,
        };
    }

    fn deinit(self: *PerfLogger) void {
        self.file.close();
    }

    fn logTiming(self: *PerfLogger, operation: []const u8, duration_ns: u64) !void {
        const duration_ms = @as(f64, @floatFromInt(duration_ns)) / @as(f64, @floatFromInt(std.time.ns_per_ms));
        const msg = try std.fmt.allocPrint(self.allocator, "{s}: {d:.3}ms\n", .{ operation, duration_ms });
        defer self.allocator.free(msg);
        try self.file.writeAll(msg);
    }
};

fn benchmarkOperation() void {
    var sum: u64 = 0;
    var i: u64 = 0;
    while (i < 1000000) : (i += 1) {
        sum +%= i;
    }
    std.mem.doNotOptimizeAway(sum);
}

test "log performance metrics" {
    var logger = try PerfLogger.init("perf.log", testing.allocator);
    defer logger.deinit();
    defer std.fs.cwd().deleteFile("perf.log") catch {};

    const start = std.time.nanoTimestamp();
    benchmarkOperation();
    const end = std.time.nanoTimestamp();

    try logger.logTiming("benchmark_operation", @intCast(end - start));

    const content = try std.fs.cwd().readFileAlloc(testing.allocator, "perf.log", 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "benchmark_operation") != null);
    try testing.expect(std.mem.indexOf(u8, content, "ms") != null);
}
// ANCHOR_END: performance_logging
```

### See Also

- Recipe 14.1: Testing program output sent to stdout
- Recipe 13.10: Adding logging to simple scripts
- Recipe 13.11: Adding logging to a library
- Recipe 14.13: Profiling and timing your program

---

## Recipe 14.5: Skipping or anticipating test failures {#recipe-14-5}

**Tags:** allocators, c-interop, comptime, error-handling, memory, resource-cleanup, testing, testing-debugging
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_5.zig`

### Problem

You need to skip tests under certain conditions or document expected failures. You want to handle platform-specific tests, known bugs, incomplete features, and resource-dependent tests.

### Solution

Return `error.SkipZigTest` to skip a test conditionally:

```zig
test "skip on specific platform" {
    if (builtin.os.tag == .windows) {
        // Skip this test on Windows
        return error.SkipZigTest;
    }

    // Test runs on non-Windows platforms
    try testing.expectEqual(@as(i32, 42), 42);
}

test "skip based on build mode" {
    if (builtin.mode == .ReleaseFast) {
        // Skip in release mode
        return error.SkipZigTest;
    }

    // Only runs in debug mode
    try testing.expectEqual(@as(i32, 10), 10);
}
```

### Discussion

Zig doesn't have built-in test skip annotations, but returning `error.SkipZigTest` achieves the same result. This keeps tests in your codebase while preventing them from running under specific conditions.

### Expected Failures

Document known failures by testing that they fail as expected:

```zig
const ExperimentalFeature = struct {
    fn compute(value: i32) !i32 {
        // Known to fail for negative values
        if (value < 0) return error.NotImplemented;
        return value * 2;
    }
};

test "expect known failure" {
    const result = ExperimentalFeature.compute(-5);

    // We expect this to fail with NotImplemented
    try testing.expectError(error.NotImplemented, result);
}

test "works for positive values" {
    const result = try ExperimentalFeature.compute(5);
    try testing.expectEqual(@as(i32, 10), result);
}
```

This pattern is better than skipping because it verifies the failure still occurs. If the bug gets fixed, the test will fail, prompting you to update it.

### Version-Dependent Tests

Skip tests that require specific Zig versions:

```zig
const MIN_ZIG_VERSION = std.SemanticVersion{ .major = 0, .minor = 13, .patch = 0 };

fn requiresMinVersion() !void {
    if (builtin.zig_version.order(MIN_ZIG_VERSION) == .lt) {
        return error.SkipZigTest;
    }
}

test "skip if zig version too old" {
    try requiresMinVersion();

    // This test only runs on Zig 0.13.0 or newer
    try testing.expectEqual(@as(i32, 1), 1);
}
```

This is useful when testing new language features or maintaining compatibility across versions.

### Feature Flags

Use compile-time constants to enable/disable test groups:

```zig
const enable_experimental_tests = false;

test "experimental feature test" {
    if (!enable_experimental_tests) {
        return error.SkipZigTest;
    }

    // Experimental test code
    try testing.expectEqual(@as(i32, 100), 100);
}
```

Feature flags let you control which tests run without commenting them out.

### Environment-Based Skipping

Skip tests based on environment variables:

```zig
fn isCI() bool {
    const allocator = testing.allocator;
    const ci = std.process.getEnvVarOwned(allocator, "CI") catch return false;
    defer allocator.free(ci);
    return std.mem.eql(u8, ci, "true");
}

test "skip in CI environment" {
    if (isCI()) {
        return error.SkipZigTest;
    }

    // Only runs locally
    try testing.expectEqual(@as(i32, 5), 5);
}
```

This is useful for CI/CD environments where certain tests shouldn't run.

### Slow Tests

Mark slow tests so they can be skipped during development:

```zig
const run_slow_tests = false;

test "slow performance test" {
    if (!run_slow_tests) {
        return error.SkipZigTest;
    }

    // Slow test that's normally skipped
    var sum: u64 = 0;
    var i: u64 = 0;
    while (i < 10_000_000) : (i += 1) {
        sum +%= i;
    }
    try testing.expect(sum > 0);
}
```

Run slow tests with a flag: `const run_slow_tests = true;` before running tests.

### Resource Availability

Skip tests when required resources aren't available:

```zig
fn hasRequiredResource() bool {
    // Check if required file exists
    std.fs.cwd().access("test-resource.txt", .{}) catch return false;
    return true;
}

test "skip if resource missing" {
    if (!hasRequiredResource()) {
        return error.SkipZigTest;
    }

    // Test requires test-resource.txt
    try testing.expectEqual(@as(i32, 1), 1);
}
```

This prevents test failures due to missing test data or external dependencies.

### Documenting Known Issues

Link tests to known issues while expecting the failure:

```zig
test "known failing test - issue #123" {
    // Document known issues
    const result = brokenFunction();

    // Expect the known failure
    try testing.expectError(error.KnownBug, result);
}

fn brokenFunction() !void {
    // This function has a known bug tracked in issue #123
    return error.KnownBug;
}
```

This documents the bug in the test itself and ensures it's still present.

### Platform-Specific Tests

Write tests that behave differently on each platform:

```zig
test "platform-specific behavior" {
    switch (builtin.os.tag) {
        .linux => {
            // Linux-specific test
            try testing.expectEqual(@as(i32, 1), 1);
        },
        .macos => {
            // macOS-specific test
            try testing.expectEqual(@as(i32, 2), 2);
        },
        .windows => {
            // Windows-specific test
            try testing.expectEqual(@as(i32, 3), 3);
        },
        else => {
            // Skip on other platforms
            return error.SkipZigTest;
        },
    }
}
```

This allows platform-specific behavior to be tested appropriately.

### Handling Flaky Tests

Retry flaky tests before failing:

```zig
const max_retries = 3;

fn flakyOperation(attempt: usize) !i32 {
    // Simulates a flaky operation that sometimes fails
    if (attempt < 2) {
        return error.TransientFailure;
    }
    return 42;
}

test "retry flaky operation" {
    var attempt: usize = 0;
    const result = while (attempt < max_retries) : (attempt += 1) {
        if (flakyOperation(attempt)) |value| {
            break value;
        } else |err| {
            if (attempt == max_retries - 1) {
                return err;
            }
            continue;
        }
    } else unreachable;

    try testing.expectEqual(@as(i32, 42), result);
}
```

While flaky tests should be fixed, retries can help in the interim for tests involving timing or external resources.

### Compile-Time Skip Lists

Skip tests by name at compile time:

```zig
fn shouldRunTest(comptime test_name: []const u8) bool {
    // Skip specific tests at compile time
    const skip_list = &[_][]const u8{
        "broken_test",
        "disabled_test",
    };

    inline for (skip_list) |skip_name| {
        if (std.mem.eql(u8, test_name, skip_name)) {
            return false;
        }
    }
    return true;
}

test "conditionally run based on name" {
    if (!shouldRunTest("this_test")) {
        return error.SkipZigTest;
    }

    try testing.expectEqual(@as(i32, 1), 1);
}
```

This provides a centralized place to disable problematic tests.

### Graceful Degradation

Skip tests that depend on external services:

```zig
const NetworkTest = struct {
    fn requiresNetwork() !void {
        // Try to detect network availability
        const allocator = testing.allocator;
        const no_network = std.process.getEnvVarOwned(allocator, "NO_NETWORK") catch null;
        if (no_network) |val| {
            defer allocator.free(val);
            if (std.mem.eql(u8, val, "1")) {
                return error.SkipZigTest;
            }
        }
    }
};

test "network-dependent test" {
    try NetworkTest.requiresNetwork();

    // Network test code here
    try testing.expectEqual(@as(i32, 1), 1);
}
```

Set `NO_NETWORK=1` to skip network tests in offline environments.

### Architecture-Specific Tests

Skip tests on unsupported architectures:

```zig
test "skip on 32-bit architectures" {
    if (@sizeOf(usize) < 8) {
        // Skip on 32-bit systems
        return error.SkipZigTest;
    }

    // Test requires 64-bit architecture
    const large_number: u64 = 0xFFFFFFFFFFFFFFFF;
    try testing.expect(large_number > 0);
}
```

This ensures tests only run on architectures they support.

### CPU Capability Checks

Skip tests that require specific CPU features:

```zig
fn hasSSE2() bool {
    // Check for CPU features
    return std.Target.x86.featureSetHas(builtin.cpu.features, .sse2);
}

test "skip without SSE2" {
    if (builtin.cpu.arch != .x86_64) {
        return error.SkipZigTest;
    }

    if (!hasSSE2()) {
        return error.SkipZigTest;
    }

    // SSE2-specific test
    try testing.expectEqual(@as(i32, 1), 1);
}
```

This prevents tests from failing on older CPUs.

### Test Categories

Organize tests into categories that can be run selectively:

```zig
const TestCategory = enum {
    unit,
    integration,
    performance,
    flaky,
};

fn shouldRunCategory(category: TestCategory) bool {
    const allocator = testing.allocator;
    const test_category = std.process.getEnvVarOwned(allocator, "TEST_CATEGORY") catch return true;
    defer allocator.free(test_category);

    return switch (category) {
        .unit => std.mem.eql(u8, test_category, "unit") or std.mem.eql(u8, test_category, "all"),
        .integration => std.mem.eql(u8, test_category, "integration") or std.mem.eql(u8, test_category, "all"),
        .performance => std.mem.eql(u8, test_category, "performance") or std.mem.eql(u8, test_category, "all"),
        .flaky => std.mem.eql(u8, test_category, "flaky"),
    };
}

test "unit test category" {
    if (!shouldRunCategory(.unit)) {
        return error.SkipZigTest;
    }

    try testing.expectEqual(@as(i32, 1), 1);
}

test "integration test category" {
    if (!shouldRunCategory(.integration)) {
        return error.SkipZigTest;
    }

    try testing.expectEqual(@as(i32, 2), 2);
}
```

Run specific categories with environment variables:
```bash
TEST_CATEGORY=unit zig test
TEST_CATEGORY=integration zig test
TEST_CATEGORY=all zig test
```

### Best Practices

1. **Prefer expected failures over skips**: Use `expectError` for known bugs
2. **Document why tests skip**: Add comments explaining skip conditions
3. **Make skips temporary**: Track skipped tests and fix the underlying issues
4. **Use feature flags**: Group related skips under feature flags
5. **Test the skip logic**: Ensure skip conditions work as expected
6. **Avoid permanent skips**: Every skip should have a plan to remove it
7. **Link to issues**: Reference bug tracker issues in skip comments

### Skip Patterns

**Pattern 1: Conditional Compilation**
```zig
test "example" {
    if (comptime !featureEnabled()) {
        return error.SkipZigTest;
    }
    // ...
}
```

**Pattern 2: Environment Detection**
```zig
fn shouldSkip() bool {
    return std.process.getEnvVarOwned(allocator, "SKIP_TEST") catch null != null;
}
```

**Pattern 3: Resource Validation**
```zig
test "example" {
    validateResources() catch return error.SkipZigTest;
    // ...
}
```

### Common Gotchas

**Skipping too liberally**: Don't skip tests just because they're inconvenient. Fix the underlying issues instead.

**Not documenting skips**: Always explain why a test is skipped:

```zig
test "skip example" {
    // TODO(#123): Skip until database mock is implemented
    if (!hasDatabaseMock()) {
        return error.SkipZigTest;
    }
}
```

**Forgetting to remove skips**: Track skipped tests and revisit them regularly. Use grep to find all skips:

```bash
grep -r "SkipZigTest" src/
```

**Platform detection errors**: Test your skip conditions on all target platforms.

### CI/CD Integration

Organize tests for continuous integration:

```zig
const in_ci = std.process.getEnvVarOwned(allocator, "CI") catch null != null;

test "interactive test" {
    if (in_ci) {
        // Skip tests requiring human interaction in CI
        return error.SkipZigTest;
    }
}
```

This lets you run full test suites locally while keeping CI fast and focused.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;
const builtin = @import("builtin");

// ANCHOR: conditional_skip
test "skip on specific platform" {
    if (builtin.os.tag == .windows) {
        // Skip this test on Windows
        return error.SkipZigTest;
    }

    // Test runs on non-Windows platforms
    try testing.expectEqual(@as(i32, 42), 42);
}

test "skip based on build mode" {
    if (builtin.mode == .ReleaseFast) {
        // Skip in release mode
        return error.SkipZigTest;
    }

    // Only runs in debug mode
    try testing.expectEqual(@as(i32, 10), 10);
}
// ANCHOR_END: conditional_skip

// ANCHOR: expected_failure
const ExperimentalFeature = struct {
    fn compute(value: i32) !i32 {
        // Known to fail for negative values
        if (value < 0) return error.NotImplemented;
        return value * 2;
    }
};

test "expect known failure" {
    const result = ExperimentalFeature.compute(-5);

    // We expect this to fail with NotImplemented
    try testing.expectError(error.NotImplemented, result);
}

test "works for positive values" {
    const result = try ExperimentalFeature.compute(5);
    try testing.expectEqual(@as(i32, 10), result);
}
// ANCHOR_END: expected_failure

// ANCHOR: version_dependent
const MIN_ZIG_VERSION = std.SemanticVersion{ .major = 0, .minor = 13, .patch = 0 };

fn requiresMinVersion() !void {
    if (builtin.zig_version.order(MIN_ZIG_VERSION) == .lt) {
        return error.SkipZigTest;
    }
}

test "skip if zig version too old" {
    try requiresMinVersion();

    // This test only runs on Zig 0.13.0 or newer
    try testing.expectEqual(@as(i32, 1), 1);
}
// ANCHOR_END: version_dependent

// ANCHOR: feature_flag
const enable_experimental_tests = false;

test "experimental feature test" {
    if (!enable_experimental_tests) {
        return error.SkipZigTest;
    }

    // Experimental test code
    try testing.expectEqual(@as(i32, 100), 100);
}
// ANCHOR_END: feature_flag

// ANCHOR: environment_based
fn isCI() bool {
    const allocator = testing.allocator;
    const ci = std.process.getEnvVarOwned(allocator, "CI") catch return false;
    defer allocator.free(ci);
    return std.mem.eql(u8, ci, "true");
}

test "skip in CI environment" {
    if (isCI()) {
        return error.SkipZigTest;
    }

    // Only runs locally
    try testing.expectEqual(@as(i32, 5), 5);
}
// ANCHOR_END: environment_based

// ANCHOR: slow_test
const run_slow_tests = false;

test "slow performance test" {
    if (!run_slow_tests) {
        return error.SkipZigTest;
    }

    // Slow test that's normally skipped
    var sum: u64 = 0;
    var i: u64 = 0;
    while (i < 10_000_000) : (i += 1) {
        sum +%= i;
    }
    try testing.expect(sum > 0);
}
// ANCHOR_END: slow_test

// ANCHOR: resource_check
fn hasRequiredResource() bool {
    // Check if required file exists
    std.fs.cwd().access("test-resource.txt", .{}) catch return false;
    return true;
}

test "skip if resource missing" {
    if (!hasRequiredResource()) {
        return error.SkipZigTest;
    }

    // Test requires test-resource.txt
    try testing.expectEqual(@as(i32, 1), 1);
}
// ANCHOR_END: resource_check

// ANCHOR: known_issue
test "known failing test - issue #123" {
    // Document known issues
    const result = brokenFunction();

    // Expect the known failure
    try testing.expectError(error.KnownBug, result);
}

fn brokenFunction() !void {
    // This function has a known bug tracked in issue #123
    return error.KnownBug;
}
// ANCHOR_END: known_issue

// ANCHOR: platform_specific
test "platform-specific behavior" {
    switch (builtin.os.tag) {
        .linux => {
            // Linux-specific test
            try testing.expectEqual(@as(i32, 1), 1);
        },
        .macos => {
            // macOS-specific test
            try testing.expectEqual(@as(i32, 2), 2);
        },
        .windows => {
            // Windows-specific test
            try testing.expectEqual(@as(i32, 3), 3);
        },
        else => {
            // Skip on other platforms
            return error.SkipZigTest;
        },
    }
}
// ANCHOR_END: platform_specific

// ANCHOR: flaky_test
const max_retries = 3;

fn flakyOperation(attempt: usize) !i32 {
    // Simulates a flaky operation that sometimes fails
    if (attempt < 2) {
        return error.TransientFailure;
    }
    return 42;
}

test "retry flaky operation" {
    var attempt: usize = 0;
    const result = while (attempt < max_retries) : (attempt += 1) {
        if (flakyOperation(attempt)) |value| {
            break value;
        } else |err| {
            if (attempt == max_retries - 1) {
                return err;
            }
            continue;
        }
    } else unreachable;

    try testing.expectEqual(@as(i32, 42), result);
}
// ANCHOR_END: flaky_test

// ANCHOR: comptime_skip
fn shouldRunTest(comptime test_name: []const u8) bool {
    // Skip specific tests at compile time
    const skip_list = &[_][]const u8{
        "broken_test",
        "disabled_test",
    };

    inline for (skip_list) |skip_name| {
        if (std.mem.eql(u8, test_name, skip_name)) {
            return false;
        }
    }
    return true;
}

test "conditionally run based on name" {
    if (!shouldRunTest("this_test")) {
        return error.SkipZigTest;
    }

    try testing.expectEqual(@as(i32, 1), 1);
}
// ANCHOR_END: comptime_skip

// ANCHOR: graceful_degradation
const NetworkTest = struct {
    fn requiresNetwork() !void {
        // Try to detect network availability
        const allocator = testing.allocator;
        const no_network = std.process.getEnvVarOwned(allocator, "NO_NETWORK") catch null;
        if (no_network) |val| {
            defer allocator.free(val);
            if (std.mem.eql(u8, val, "1")) {
                return error.SkipZigTest;
            }
        }
    }
};

test "network-dependent test" {
    try NetworkTest.requiresNetwork();

    // Network test code here
    try testing.expectEqual(@as(i32, 1), 1);
}
// ANCHOR_END: graceful_degradation

// ANCHOR: architecture_specific
test "skip on 32-bit architectures" {
    if (@sizeOf(usize) < 8) {
        // Skip on 32-bit systems
        return error.SkipZigTest;
    }

    // Test requires 64-bit architecture
    const large_number: u64 = 0xFFFFFFFFFFFFFFFF;
    try testing.expect(large_number > 0);
}
// ANCHOR_END: architecture_specific

// ANCHOR: capability_check
fn hasSSE2() bool {
    // Check for CPU features
    return std.Target.x86.featureSetHas(builtin.cpu.features, .sse2);
}

test "skip without SSE2" {
    if (builtin.cpu.arch != .x86_64) {
        return error.SkipZigTest;
    }

    if (!hasSSE2()) {
        return error.SkipZigTest;
    }

    // SSE2-specific test
    try testing.expectEqual(@as(i32, 1), 1);
}
// ANCHOR_END: capability_check

// ANCHOR: test_categories
const TestCategory = enum {
    unit,
    integration,
    performance,
    flaky,
};

fn shouldRunCategory(category: TestCategory) bool {
    const allocator = testing.allocator;
    const test_category = std.process.getEnvVarOwned(allocator, "TEST_CATEGORY") catch return true;
    defer allocator.free(test_category);

    return switch (category) {
        .unit => std.mem.eql(u8, test_category, "unit") or std.mem.eql(u8, test_category, "all"),
        .integration => std.mem.eql(u8, test_category, "integration") or std.mem.eql(u8, test_category, "all"),
        .performance => std.mem.eql(u8, test_category, "performance") or std.mem.eql(u8, test_category, "all"),
        .flaky => std.mem.eql(u8, test_category, "flaky"),
    };
}

test "unit test category" {
    if (!shouldRunCategory(.unit)) {
        return error.SkipZigTest;
    }

    try testing.expectEqual(@as(i32, 1), 1);
}

test "integration test category" {
    if (!shouldRunCategory(.integration)) {
        return error.SkipZigTest;
    }

    try testing.expectEqual(@as(i32, 2), 2);
}
// ANCHOR_END: test_categories
```

### See Also

- Recipe 14.3: Testing for exceptional conditions in unit tests
- Recipe 14.4: Logging test output to a file
- Recipe 0.13: Testing and Debugging Fundamentals
- Recipe 1.3: Testing Strategy

---

## Recipe 14.6: Handling multiple exceptions at once {#recipe-14-6}

**Tags:** allocators, arraylist, data-structures, error-handling, memory, resource-cleanup, testing, testing-debugging
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_6.zig`

### Problem

You need to handle different types of errors in a single function or manage multiple errors from parallel operations. You want to apply different recovery strategies based on error type and context.

### Solution

Use error unions and switch statements to handle different error types:

```zig
const FileError = error{ NotFound, PermissionDenied, TooLarge };
const NetworkError = error{ Timeout, ConnectionRefused, HostUnreachable };
const AllErrors = FileError || NetworkError;

fn complexOperation(mode: u8) AllErrors!void {
    switch (mode) {
        1 => return error.NotFound,
        2 => return error.Timeout,
        3 => return error.PermissionDenied,
        else => {},
    }
}

test "handle multiple error types" {
    if (complexOperation(1)) |_| {
        try testing.expect(false);
    } else |err| {
        switch (err) {
            error.NotFound, error.PermissionDenied, error.TooLarge => {
                // Handle file errors
                try testing.expect(true);
            },
            error.Timeout, error.ConnectionRefused, error.HostUnreachable => {
                // Handle network errors
                try testing.expect(false);
            },
        }
    }
}
```

### Discussion

Zig's error handling shines when dealing with multiple error types. Error unions (`||`) combine error sets, and switch statements let you handle each error appropriately.

### Switching on Error Types

Handle each error with custom logic:

```zig
fn processData(data: []const u8) !void {
    if (data.len == 0) return error.EmptyData;
    if (data.len > 1000) return error.DataTooLarge;
    if (data[0] == 0) return error.InvalidFormat;
}

test "handle each error differently" {
    const cases = [_]struct {
        data: []const u8,
        expected_error: ?anyerror,
    }{
        .{ .data = "", .expected_error = error.EmptyData },
        .{ .data = &[_]u8{0} ** 1001, .expected_error = error.DataTooLarge },
        .{ .data = &[_]u8{0}, .expected_error = error.InvalidFormat },
        .{ .data = "valid", .expected_error = null },
    };

    for (cases) |case| {
        if (case.expected_error) |expected| {
            try testing.expectError(expected, processData(case.data));
        } else {
            try processData(case.data);
        }
    }
}
```

This pattern tests all error paths systematically.

### Error Context and Messages

Provide meaningful messages for each error type:

```zig
const Operation = struct {
    const Error = error{ InvalidInput, ProcessingFailed, OutputError };

    fn execute(input: i32) Error!i32 {
        if (input < 0) return error.InvalidInput;
        if (input > 100) return error.ProcessingFailed;
        return input * 2;
    }

    fn handleError(err: Error) []const u8 {
        return switch (err) {
            error.InvalidInput => "Input validation failed",
            error.ProcessingFailed => "Processing exceeded limits",
            error.OutputError => "Failed to produce output",
        };
    }
};

test "provide context for each error" {
    const result = Operation.execute(-5);
    if (result) |_| {
        try testing.expect(false);
    } else |err| {
        const message = Operation.handleError(err);
        try testing.expectEqualStrings("Input validation failed", message);
    }
}
```

Separating error handling from error messages improves maintainability.

### Cascading Error Handlers

Try multiple recovery strategies in sequence:

```zig
fn readConfig(path: []const u8) ![]const u8 {
    if (path.len == 0) return error.InvalidPath;
    if (std.mem.eql(u8, path, "missing.conf")) return error.FileNotFound;
    return "config data";
}

fn parseConfig(data: []const u8) !i32 {
    if (data.len == 0) return error.EmptyConfig;
    return 42;
}

fn loadConfiguration(path: []const u8) !i32 {
    const data = readConfig(path) catch |err| {
        switch (err) {
            error.InvalidPath => {
                // Try default path
                return parseConfig("default config");
            },
            error.FileNotFound => {
                // Create default config
                return 0;
            },
            else => return err,
        }
    };

    return parseConfig(data);
}

test "cascade through multiple error handlers" {
    try testing.expectEqual(@as(i32, 0), try loadConfiguration("missing.conf"));
    try testing.expectEqual(@as(i32, 42), try loadConfiguration("valid.conf"));
    try testing.expectEqual(@as(i32, 42), try loadConfiguration(""));
}
```

This pattern gracefully degrades through fallback options.

### Recovery Strategies

Apply different strategies based on error severity:

```zig
const RecoveryStrategy = enum { retry, fallback, abort };

fn unreliableOperation(attempt: usize) !i32 {
    if (attempt < 3) return error.Transient;
    return 42;
}

fn handleWithStrategy(err: anyerror, strategy: RecoveryStrategy) !i32 {
    return switch (strategy) {
        .retry => blk: {
            // Retry logic - ignore the original error
            std.debug.print("Retrying after error: {s}\n", .{@errorName(err)});
            var attempt: usize = 0;
            while (attempt < 5) : (attempt += 1) {
                if (unreliableOperation(attempt)) |val| {
                    break :blk val;
                } else |e| {
                    if (e != error.Transient) return e;
                }
            }
            return error.MaxRetriesExceeded;
        },
        .fallback => 0, // Return default value
        .abort => err,
    };
}

test "apply different recovery strategies" {
    try testing.expectEqual(@as(i32, 42), try handleWithStrategy(error.Transient, .retry));
    try testing.expectEqual(@as(i32, 0), try handleWithStrategy(error.Permanent, .fallback));
    try testing.expectError(error.Permanent, handleWithStrategy(error.Permanent, .abort));
}
```

Recovery strategies include:
- **Retry**: Try the operation again (for transient failures)
- **Fallback**: Use default values
- **Abort**: Propagate the error immediately

### Grouped Error Handling

Group related errors for common handling:

```zig
const IOError = error{ ReadError, WriteError, SeekError };
const ValidationError = error{ InvalidFormat, OutOfRange, MissingField };
const RuntimeError = error{ OutOfMemory, Overflow, Timeout };

fn handleIOErrors(err: anyerror) void {
    std.debug.print("IO Error: {s}\n", .{@errorName(err)});
}

fn handleValidationErrors(err: anyerror) void {
    std.debug.print("Validation Error: {s}\n", .{@errorName(err)});
}

fn handleRuntimeErrors(err: anyerror) void {
    std.debug.print("Runtime Error: {s}\n", .{@errorName(err)});
}

fn operation(mode: u8) (IOError || ValidationError || RuntimeError)!void {
    switch (mode) {
        1 => return error.ReadError,
        2 => return error.InvalidFormat,
        3 => return error.OutOfMemory,
        else => {},
    }
}

test "group and handle related errors" {
    const result = operation(1);

    if (result) |_| {
        try testing.expect(true);
    } else |err| {
        switch (err) {
            error.ReadError, error.WriteError, error.SeekError => {
                handleIOErrors(err);
            },
            error.InvalidFormat, error.OutOfRange, error.MissingField => {
                handleValidationErrors(err);
            },
            error.OutOfMemory, error.Overflow, error.Timeout => {
                handleRuntimeErrors(err);
            },
        }
    }
}
```

This reduces code duplication when errors need similar handling.

### Error Aggregation

Collect multiple errors from a sequence of operations:

```zig
const ErrorAggregator = struct {
    errors: std.ArrayList(anyerror),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) ErrorAggregator {
        return .{
            .errors = std.ArrayList(anyerror){},
            .allocator = allocator,
        };
    }

    fn deinit(self: *ErrorAggregator) void {
        self.errors.deinit(self.allocator);
    }

    fn addError(self: *ErrorAggregator, err: anyerror) !void {
        try self.errors.append(self.allocator, err);
    }

    fn hasErrors(self: *const ErrorAggregator) bool {
        return self.errors.items.len > 0;
    }

    fn getErrors(self: *const ErrorAggregator) []const anyerror {
        return self.errors.items;
    }
};

test "aggregate multiple errors" {
    var aggregator = ErrorAggregator.init(testing.allocator);
    defer aggregator.deinit();

    try aggregator.addError(error.FirstError);
    try aggregator.addError(error.SecondError);
    try aggregator.addError(error.ThirdError);

    try testing.expect(aggregator.hasErrors());
    try testing.expectEqual(@as(usize, 3), aggregator.getErrors().len);
}
```

Error aggregation is useful for validation where you want to report all errors, not just the first one.

### Error Chains

Preserve error context through call stacks:

```zig
const ErrorChain = struct {
    current: anyerror,
    cause: ?*const ErrorChain = null,

    fn wrap(err: anyerror, cause: ?*const ErrorChain) ErrorChain {
        return .{
            .current = err,
            .cause = cause,
        };
    }

    fn rootCause(self: *const ErrorChain) anyerror {
        var chain = self;
        while (chain.cause) |cause| {
            chain = cause;
        }
        return chain.current;
    }
};

test "chain errors to preserve context" {
    const root = ErrorChain.wrap(error.DatabaseError, null);
    const mid = ErrorChain.wrap(error.ConnectionError, &root);
    const top = ErrorChain.wrap(error.ServiceError, &mid);

    try testing.expectEqual(error.DatabaseError, top.rootCause());
    try testing.expectEqual(error.ServiceError, top.current);
}
```

Error chains help debug issues by showing the full error path.

### Error Priority

Handle errors by priority or severity:

```zig
fn handleByPriority(err: anyerror) !void {
    // Handle errors by priority
    const critical = [_]anyerror{ error.OutOfMemory, error.StackOverflow };
    const important = [_]anyerror{ error.FileNotFound, error.PermissionDenied };

    for (critical) |critical_err| {
        if (err == critical_err) {
            // Critical error - abort immediately
            return err;
        }
    }

    for (important) |important_err| {
        if (err == important_err) {
            // Important error - log and continue
            return;
        }
    }

    // Other errors - ignore
}

test "prioritize error handling" {
    try testing.expectError(error.OutOfMemory, handleByPriority(error.OutOfMemory));
    try handleByPriority(error.FileNotFound);
    try handleByPriority(error.UnknownError);
}
```

Critical errors get immediate attention while minor errors can be ignored.

### Parallel Operations

Collect errors from parallel or batch operations:

```zig
const ParallelResult = struct {
    success_count: usize = 0,
    errors: std.ArrayList(anyerror),

    fn init() ParallelResult {
        return .{
            .errors = std.ArrayList(anyerror){},
        };
    }

    fn deinit(self: *ParallelResult, allocator: std.mem.Allocator) void {
        self.errors.deinit(allocator);
    }

    fn recordSuccess(self: *ParallelResult) void {
        self.success_count += 1;
    }

    fn recordError(self: *ParallelResult, allocator: std.mem.Allocator, err: anyerror) !void {
        try self.errors.append(allocator, err);
    }
};

fn parallelOperations(allocator: std.mem.Allocator) !ParallelResult {
    var result = ParallelResult.init();

    // Simulate parallel operations
    const operations = [_]?anyerror{ null, error.Op1Failed, null, error.Op2Failed };

    for (operations) |maybe_err| {
        if (maybe_err) |err| {
            try result.recordError(allocator, err);
        } else {
            result.recordSuccess();
        }
    }

    return result;
}

test "collect errors from parallel operations" {
    var result = try parallelOperations(testing.allocator);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 2), result.success_count);
    try testing.expectEqual(@as(usize, 2), result.errors.items.len);
}
```

This pattern reports all failures rather than stopping at the first error.

### Best Practices

1. **Use error unions**: Combine error sets with `||` operator
2. **Switch exhaustively**: Handle all possible errors explicitly
3. **Provide context**: Include helpful error messages
4. **Cascade gracefully**: Try fallbacks before giving up
5. **Aggregate when appropriate**: Collect multiple errors for batch operations
6. **Chain for debugging**: Preserve error history through call stacks
7. **Prioritize correctly**: Handle critical errors first

### Error Handling Patterns

**Pattern 1: Type-Based Dispatch**
```zig
if (operation()) |value| {
    // Success
} else |err| switch (err) {
    error.NotFound => handleNotFound(),
    error.PermissionDenied => handlePermission(),
    else => return err,
}
```

**Pattern 2: Error Transformation**
```zig
const data = readFile(path) catch |err| switch (err) {
    error.FileNotFound => return error.ConfigMissing,
    error.AccessDenied => return error.PermissionError,
    else => return err,
};
```

**Pattern 3: Batch Processing**
```zig
var errors = ErrorList.init(allocator);
for (items) |item| {
    process(item) catch |err| {
        try errors.append(err);
        continue;
    };
}
if (errors.count() > 0) {
    return error.BatchProcessingFailed;
}
```

### Common Gotchas

**Not exhausting all cases**: Always handle all possible errors:

```zig
// Wrong - compiler error if new errors added
if (err == error.NotFound) { ... }

// Right - compiler enforces exhaustiveness
switch (err) {
    error.NotFound => { ... },
    error.PermissionDenied => { ... },
    // All errors must be handled
}
```

**Losing error context**: Preserve context when wrapping errors:

```zig
// Loses context
fn wrapper() !void {
    try innerFunction(); // Error info lost
}

// Preserves context
fn wrapper() !void {
    innerFunction() catch |err| {
        std.debug.print("Failed in wrapper: {s}\n", .{@errorName(err)});
        return err;
    };
}
```

**Ignoring partial failures**: In batch operations, track both successes and failures:

```zig
var result = BatchResult.init();
for (items) |item| {
    if (process(item)) {
        result.recordSuccess();
    } else |err| {
        result.recordError(err);
    }
}
```

### Advanced Techniques

**Error transformation pipeline**:
```zig
const result = step1()
    catch |err| transformError(err, .step1)
    catch step2()
    catch |err| transformError(err, .step2);
```

**Conditional retries**:
```zig
var attempt: usize = 0;
while (attempt < MAX_RETRIES) : (attempt += 1) {
    if (operation()) |val| return val else |err| {
        if (err == error.Permanent) return err;
        continue; // Retry on transient errors
    }
}
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: error_union
const FileError = error{ NotFound, PermissionDenied, TooLarge };
const NetworkError = error{ Timeout, ConnectionRefused, HostUnreachable };
const AllErrors = FileError || NetworkError;

fn complexOperation(mode: u8) AllErrors!void {
    switch (mode) {
        1 => return error.NotFound,
        2 => return error.Timeout,
        3 => return error.PermissionDenied,
        else => {},
    }
}

test "handle multiple error types" {
    if (complexOperation(1)) |_| {
        try testing.expect(false);
    } else |err| {
        switch (err) {
            error.NotFound, error.PermissionDenied, error.TooLarge => {
                // Handle file errors
                try testing.expect(true);
            },
            error.Timeout, error.ConnectionRefused, error.HostUnreachable => {
                // Handle network errors
                try testing.expect(false);
            },
        }
    }
}
// ANCHOR_END: error_union

// ANCHOR: switch_errors
fn processData(data: []const u8) !void {
    if (data.len == 0) return error.EmptyData;
    if (data.len > 1000) return error.DataTooLarge;
    if (data[0] == 0) return error.InvalidFormat;
}

test "handle each error differently" {
    const cases = [_]struct {
        data: []const u8,
        expected_error: ?anyerror,
    }{
        .{ .data = "", .expected_error = error.EmptyData },
        .{ .data = &[_]u8{0} ** 1001, .expected_error = error.DataTooLarge },
        .{ .data = &[_]u8{0}, .expected_error = error.InvalidFormat },
        .{ .data = "valid", .expected_error = null },
    };

    for (cases) |case| {
        if (case.expected_error) |expected| {
            try testing.expectError(expected, processData(case.data));
        } else {
            try processData(case.data);
        }
    }
}
// ANCHOR_END: switch_errors

// ANCHOR: error_context
const Operation = struct {
    const Error = error{ InvalidInput, ProcessingFailed, OutputError };

    fn execute(input: i32) Error!i32 {
        if (input < 0) return error.InvalidInput;
        if (input > 100) return error.ProcessingFailed;
        return input * 2;
    }

    fn handleError(err: Error) []const u8 {
        return switch (err) {
            error.InvalidInput => "Input validation failed",
            error.ProcessingFailed => "Processing exceeded limits",
            error.OutputError => "Failed to produce output",
        };
    }
};

test "provide context for each error" {
    const result = Operation.execute(-5);
    if (result) |_| {
        try testing.expect(false);
    } else |err| {
        const message = Operation.handleError(err);
        try testing.expectEqualStrings("Input validation failed", message);
    }
}
// ANCHOR_END: error_context

// ANCHOR: cascading_errors
fn readConfig(path: []const u8) ![]const u8 {
    if (path.len == 0) return error.InvalidPath;
    if (std.mem.eql(u8, path, "missing.conf")) return error.FileNotFound;
    return "config data";
}

fn parseConfig(data: []const u8) !i32 {
    if (data.len == 0) return error.EmptyConfig;
    return 42;
}

fn loadConfiguration(path: []const u8) !i32 {
    const data = readConfig(path) catch |err| {
        switch (err) {
            error.InvalidPath => {
                // Try default path
                return parseConfig("default config");
            },
            error.FileNotFound => {
                // Create default config
                return 0;
            },
            else => return err,
        }
    };

    return parseConfig(data);
}

test "cascade through multiple error handlers" {
    try testing.expectEqual(@as(i32, 0), try loadConfiguration("missing.conf"));
    try testing.expectEqual(@as(i32, 42), try loadConfiguration("valid.conf"));
    try testing.expectEqual(@as(i32, 42), try loadConfiguration(""));
}
// ANCHOR_END: cascading_errors

// ANCHOR: error_recovery
const RecoveryStrategy = enum { retry, fallback, abort };

fn unreliableOperation(attempt: usize) !i32 {
    if (attempt < 3) return error.Transient;
    return 42;
}

fn handleWithStrategy(err: anyerror, strategy: RecoveryStrategy) !i32 {
    return switch (strategy) {
        .retry => blk: {
            // Retry logic - ignore the original error
            std.debug.print("Retrying after error: {s}\n", .{@errorName(err)});
            var attempt: usize = 0;
            while (attempt < 5) : (attempt += 1) {
                if (unreliableOperation(attempt)) |val| {
                    break :blk val;
                } else |e| {
                    if (e != error.Transient) return e;
                }
            }
            return error.MaxRetriesExceeded;
        },
        .fallback => 0, // Return default value
        .abort => err,
    };
}

test "apply different recovery strategies" {
    try testing.expectEqual(@as(i32, 42), try handleWithStrategy(error.Transient, .retry));
    try testing.expectEqual(@as(i32, 0), try handleWithStrategy(error.Permanent, .fallback));
    try testing.expectError(error.Permanent, handleWithStrategy(error.Permanent, .abort));
}
// ANCHOR_END: error_recovery

// ANCHOR: grouped_handling
const IOError = error{ ReadError, WriteError, SeekError };
const ValidationError = error{ InvalidFormat, OutOfRange, MissingField };
const RuntimeError = error{ OutOfMemory, Overflow, Timeout };

fn handleIOErrors(err: anyerror) void {
    std.debug.print("IO Error: {s}\n", .{@errorName(err)});
}

fn handleValidationErrors(err: anyerror) void {
    std.debug.print("Validation Error: {s}\n", .{@errorName(err)});
}

fn handleRuntimeErrors(err: anyerror) void {
    std.debug.print("Runtime Error: {s}\n", .{@errorName(err)});
}

fn operation(mode: u8) (IOError || ValidationError || RuntimeError)!void {
    switch (mode) {
        1 => return error.ReadError,
        2 => return error.InvalidFormat,
        3 => return error.OutOfMemory,
        else => {},
    }
}

test "group and handle related errors" {
    const result = operation(1);

    if (result) |_| {
        try testing.expect(true);
    } else |err| {
        switch (err) {
            error.ReadError, error.WriteError, error.SeekError => {
                handleIOErrors(err);
            },
            error.InvalidFormat, error.OutOfRange, error.MissingField => {
                handleValidationErrors(err);
            },
            error.OutOfMemory, error.Overflow, error.Timeout => {
                handleRuntimeErrors(err);
            },
        }
    }
}
// ANCHOR_END: grouped_handling

// ANCHOR: error_aggregation
const ErrorAggregator = struct {
    errors: std.ArrayList(anyerror),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) ErrorAggregator {
        return .{
            .errors = std.ArrayList(anyerror){},
            .allocator = allocator,
        };
    }

    fn deinit(self: *ErrorAggregator) void {
        self.errors.deinit(self.allocator);
    }

    fn addError(self: *ErrorAggregator, err: anyerror) !void {
        try self.errors.append(self.allocator, err);
    }

    fn hasErrors(self: *const ErrorAggregator) bool {
        return self.errors.items.len > 0;
    }

    fn getErrors(self: *const ErrorAggregator) []const anyerror {
        return self.errors.items;
    }
};

test "aggregate multiple errors" {
    var aggregator = ErrorAggregator.init(testing.allocator);
    defer aggregator.deinit();

    try aggregator.addError(error.FirstError);
    try aggregator.addError(error.SecondError);
    try aggregator.addError(error.ThirdError);

    try testing.expect(aggregator.hasErrors());
    try testing.expectEqual(@as(usize, 3), aggregator.getErrors().len);
}
// ANCHOR_END: error_aggregation

// ANCHOR: error_chain
const ErrorChain = struct {
    current: anyerror,
    cause: ?*const ErrorChain = null,

    fn wrap(err: anyerror, cause: ?*const ErrorChain) ErrorChain {
        return .{
            .current = err,
            .cause = cause,
        };
    }

    fn rootCause(self: *const ErrorChain) anyerror {
        var chain = self;
        while (chain.cause) |cause| {
            chain = cause;
        }
        return chain.current;
    }
};

test "chain errors to preserve context" {
    const root = ErrorChain.wrap(error.DatabaseError, null);
    const mid = ErrorChain.wrap(error.ConnectionError, &root);
    const top = ErrorChain.wrap(error.ServiceError, &mid);

    try testing.expectEqual(error.DatabaseError, top.rootCause());
    try testing.expectEqual(error.ServiceError, top.current);
}
// ANCHOR_END: error_chain

// ANCHOR: error_priority
fn handleByPriority(err: anyerror) !void {
    // Handle errors by priority
    const critical = [_]anyerror{ error.OutOfMemory, error.StackOverflow };
    const important = [_]anyerror{ error.FileNotFound, error.PermissionDenied };

    for (critical) |critical_err| {
        if (err == critical_err) {
            // Critical error - abort immediately
            return err;
        }
    }

    for (important) |important_err| {
        if (err == important_err) {
            // Important error - log and continue
            return;
        }
    }

    // Other errors - ignore
}

test "prioritize error handling" {
    try testing.expectError(error.OutOfMemory, handleByPriority(error.OutOfMemory));
    try handleByPriority(error.FileNotFound);
    try handleByPriority(error.UnknownError);
}
// ANCHOR_END: error_priority

// ANCHOR: parallel_errors
const ParallelResult = struct {
    success_count: usize = 0,
    errors: std.ArrayList(anyerror),

    fn init() ParallelResult {
        return .{
            .errors = std.ArrayList(anyerror){},
        };
    }

    fn deinit(self: *ParallelResult, allocator: std.mem.Allocator) void {
        self.errors.deinit(allocator);
    }

    fn recordSuccess(self: *ParallelResult) void {
        self.success_count += 1;
    }

    fn recordError(self: *ParallelResult, allocator: std.mem.Allocator, err: anyerror) !void {
        try self.errors.append(allocator, err);
    }
};

fn parallelOperations(allocator: std.mem.Allocator) !ParallelResult {
    var result = ParallelResult.init();

    // Simulate parallel operations
    const operations = [_]?anyerror{ null, error.Op1Failed, null, error.Op2Failed };

    for (operations) |maybe_err| {
        if (maybe_err) |err| {
            try result.recordError(allocator, err);
        } else {
            result.recordSuccess();
        }
    }

    return result;
}

test "collect errors from parallel operations" {
    var result = try parallelOperations(testing.allocator);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 2), result.success_count);
    try testing.expectEqual(@as(usize, 2), result.errors.items.len);
}
// ANCHOR_END: parallel_errors
```

### See Also

- Recipe 14.3: Testing for exceptional conditions in unit tests
- Recipe 14.7: Catching all exceptions
- Recipe 1.2: Error Handling Patterns
- Recipe 0.11: Optionals, Errors, and Resource Cleanup

---

## Recipe 14.7: Catching all exceptions {#recipe-14-7}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, hashmap, memory, resource-cleanup, testing, testing-debugging
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_7.zig`

### Problem

You need to handle any error that might occur without knowing the specific error types in advance. You want generic error handling for logging, recovery, or providing fallback behavior.

### Solution

Use `catch` without specifying an error type to catch all errors. Access the error with `|err|`:

```zig
fn riskyOperation(value: i32) !i32 {
    if (value < 0) return error.NegativeValue;
    if (value == 0) return error.ZeroValue;
    if (value > 100) return error.TooLarge;
    return value * 2;
}

fn safeOperation(value: i32) i32 {
    return riskyOperation(value) catch |err| {
        std.debug.print("Caught error: {s}\n", .{@errorName(err)});
        return 0; // Default value
    };
}

test "catch all errors with anyerror" {
    try testing.expectEqual(@as(i32, 0), safeOperation(-5));
    try testing.expectEqual(@as(i32, 0), safeOperation(0));
    try testing.expectEqual(@as(i32, 0), safeOperation(200));
    try testing.expectEqual(@as(i32, 20), safeOperation(10));
}
```

### Discussion

Zig's `catch` keyword handles all errors when used without a specific error set. This is useful for logging, providing defaults, or implementing fallback behavior.

### Catching and Logging

Catch all errors while logging them for debugging:

```zig
fn processWithLogging(value: i32, logger: anytype) i32 {
    return riskyOperation(value) catch |err| {
        logger.log("Operation failed: {s}", .{@errorName(err)});
        return -1;
    };
}

const TestLogger = struct {
    message: ?[]const u8 = null,

    fn log(self: *TestLogger, comptime fmt: []const u8, args: anytype) void {
        _ = fmt;
        _ = args;
        self.message = "Error logged";
    }
};

test "catch all errors and log them" {
    var logger = TestLogger{};
    const result = processWithLogging(-5, &logger);

    try testing.expectEqual(@as(i32, -1), result);
    try testing.expect(logger.message != null);
}
```

This pattern ensures errors don't crash your program while still recording what went wrong.

### Inspecting Error Names

Use `@errorName()` to get the error name as a string:

```zig
fn handleAnyError(err: anyerror) []const u8 {
    const name = @errorName(err);

    // Check error name for special handling
    if (std.mem.startsWith(u8, name, "File")) {
        return "File system error";
    } else if (std.mem.startsWith(u8, name, "Network")) {
        return "Network error";
    } else if (std.mem.startsWith(u8, name, "Parse")) {
        return "Parsing error";
    }

    return "Unknown error";
}

test "inspect error names" {
    try testing.expectEqualStrings("File system error", handleAnyError(error.FileNotFound));
    try testing.expectEqualStrings("Network error", handleAnyError(error.NetworkTimeout));
    try testing.expectEqualStrings("Parsing error", handleAnyError(error.ParseError));
    try testing.expectEqualStrings("Unknown error", handleAnyError(error.GenericError));
}
```

Error name inspection allows dynamic error handling based on naming conventions.

### Global Error Handler

Create a centralized error handler:

```zig
const ErrorHandler = struct {
    error_count: usize = 0,
    last_error: ?anyerror = null,

    fn handle(self: *ErrorHandler, err: anyerror) void {
        self.error_count += 1;
        self.last_error = err;
        std.debug.print("Error #{d}: {s}\n", .{ self.error_count, @errorName(err) });
    }

    fn reset(self: *ErrorHandler) void {
        self.error_count = 0;
        self.last_error = null;
    }
};

fn operationWithHandler(value: i32, handler: *ErrorHandler) !i32 {
    return riskyOperation(value) catch |err| {
        handler.handle(err);
        return error.HandledError;
    };
}

test "use global error handler" {
    var handler = ErrorHandler{};

    _ = operationWithHandler(-5, &handler) catch {};
    try testing.expectEqual(@as(usize, 1), handler.error_count);
    try testing.expectEqual(error.NegativeValue, handler.last_error.?);

    _ = operationWithHandler(200, &handler) catch {};
    try testing.expectEqual(@as(usize, 2), handler.error_count);
}
```

Global error handlers track metrics and provide consistent error handling across your application.

### Try-Or-Default Pattern

Provide default values when operations fail:

```zig
fn tryOrDefault(comptime T: type, operation: anytype, default: T) T {
    return operation catch default;
}

test "try operation or return default" {
    const result1 = tryOrDefault(i32, riskyOperation(10), 0);
    try testing.expectEqual(@as(i32, 20), result1);

    const result2 = tryOrDefault(i32, riskyOperation(-5), 999);
    try testing.expectEqual(@as(i32, 999), result2);
}
```

This generic function works with any error-returning operation.

### Panic on Unexpected Errors

For operations that must succeed, panic on any error:

```zig
fn mustSucceed(value: i32) i32 {
    return riskyOperation(value) catch |err| {
        std.debug.panic("Operation must not fail: {s}", .{@errorName(err)});
    };
}

test "operations that must succeed" {
    // Only test valid cases since panic would terminate
    try testing.expectEqual(@as(i32, 20), mustSucceed(10));
    try testing.expectEqual(@as(i32, 100), mustSucceed(50));
}
```

Use this pattern sparingly, only for truly unrecoverable situations.

### Explicit Result Types

Return both results and error flags:

```zig
fn robustOperation(value: i32) !struct { result: i32, had_error: bool } {
    if (riskyOperation(value)) |val| {
        return .{ .result = val, .had_error = false };
    } else |err| {
        std.debug.print("Recovered from error: {s}\n", .{@errorName(err)});
        return .{ .result = 0, .had_error = true };
    }
}

test "catch all with explicit result type" {
    const success = try robustOperation(10);
    try testing.expectEqual(@as(i32, 20), success.result);
    try testing.expect(!success.had_error);

    const failure = try robustOperation(-5);
    try testing.expectEqual(@as(i32, 0), failure.result);
    try testing.expect(failure.had_error);
}
```

This pattern lets callers know an error occurred without propagating the error.

### Error Tracking

Track all errors encountered during execution:

```zig
const ErrorTracker = struct {
    errors: std.ArrayList(anyerror),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) ErrorTracker {
        return .{
            .errors = std.ArrayList(anyerror){},
            .allocator = allocator,
        };
    }

    fn deinit(self: *ErrorTracker) void {
        self.errors.deinit(self.allocator);
    }

    fn track(self: *ErrorTracker, err: anyerror) !void {
        try self.errors.append(self.allocator, err);
    }

    fn getErrors(self: *const ErrorTracker) []const anyerror {
        return self.errors.items;
    }
};

fn trackAllErrors(values: []const i32, tracker: *ErrorTracker) !void {
    for (values) |value| {
        _ = riskyOperation(value) catch |err| {
            try tracker.track(err);
            continue;
        };
    }
}

test "track all encountered errors" {
    var tracker = ErrorTracker.init(testing.allocator);
    defer tracker.deinit();

    const values = [_]i32{ -5, 0, 10, 200, -1 };
    try trackAllErrors(&values, &tracker);

    const errors = tracker.getErrors();
    try testing.expectEqual(@as(usize, 4), errors.len);
    try testing.expectEqual(error.NegativeValue, errors[0]);
    try testing.expectEqual(error.ZeroValue, errors[1]);
}
```

Error tracking is useful for batch operations where you want to collect all failures.

### Fallback Chains

Try multiple approaches before giving up:

```zig
fn withFallbacks(value: i32) i32 {
    // Try primary operation
    if (riskyOperation(value)) |result| {
        return result;
    } else |err1| {
        std.debug.print("Primary failed: {s}\n", .{@errorName(err1)});

        // Try fallback with adjusted value
        const adjusted = if (value < 0) -value else value;
        if (riskyOperation(adjusted)) |result| {
            return result;
        } else |err2| {
            std.debug.print("Fallback failed: {s}\n", .{@errorName(err2)});

            // Return safe default
            return 1;
        }
    }
}

test "fallback chain on any error" {
    try testing.expectEqual(@as(i32, 20), withFallbacks(10));
    try testing.expectEqual(@as(i32, 10), withFallbacks(-5)); // -(-5) = 5, * 2 = 10
    try testing.expectEqual(@as(i32, 1), withFallbacks(0)); // Both fail, return default
}
```

Fallback chains provide graceful degradation when primary methods fail.

### Error Metrics

Collect statistics about errors:

```zig
const ErrorMetrics = struct {
    total_operations: usize = 0,
    total_errors: usize = 0,
    error_types: std.StringHashMap(usize),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) ErrorMetrics {
        return .{
            .error_types = std.StringHashMap(usize).init(allocator),
            .allocator = allocator,
        };
    }

    fn deinit(self: *ErrorMetrics) void {
        self.error_types.deinit();
    }

    fn recordOperation(self: *ErrorMetrics, result: anytype) !void {
        self.total_operations += 1;

        if (result) |_| {
            // Success
        } else |err| {
            self.total_errors += 1;
            const name = @errorName(err);
            const count = self.error_types.get(name) orelse 0;
            try self.error_types.put(name, count + 1);
        }
    }

    fn errorRate(self: *const ErrorMetrics) f64 {
        if (self.total_operations == 0) return 0;
        return @as(f64, @floatFromInt(self.total_errors)) / @as(f64, @floatFromInt(self.total_operations));
    }
};

test "collect error metrics" {
    var metrics = ErrorMetrics.init(testing.allocator);
    defer metrics.deinit();

    try metrics.recordOperation(riskyOperation(10));
    try metrics.recordOperation(riskyOperation(-5));
    try metrics.recordOperation(riskyOperation(0));
    try metrics.recordOperation(riskyOperation(20));

    try testing.expectEqual(@as(usize, 4), metrics.total_operations);
    try testing.expectEqual(@as(usize, 2), metrics.total_errors);
    try testing.expect(metrics.errorRate() > 0.4);
}
```

Metrics help identify error patterns and reliability issues.

### Error Categorization

Categorize errors for appropriate handling:

```zig
const ErrorCategory = enum {
    validation,
    system,
    network,
    unknown,
};

fn categorizeError(err: anyerror) ErrorCategory {
    const name = @errorName(err);

    if (std.mem.indexOf(u8, name, "Invalid") != null or
        std.mem.indexOf(u8, name, "Zero") != null or
        std.mem.indexOf(u8, name, "Negative") != null or
        std.mem.indexOf(u8, name, "TooLarge") != null)
    {
        return .validation;
    } else if (std.mem.indexOf(u8, name, "File") != null or
        std.mem.indexOf(u8, name, "Memory") != null)
    {
        return .system;
    } else if (std.mem.indexOf(u8, name, "Network") != null or
        std.mem.indexOf(u8, name, "Timeout") != null)
    {
        return .network;
    }

    return .unknown;
}

test "categorize any error" {
    try testing.expectEqual(ErrorCategory.validation, categorizeError(error.NegativeValue));
    try testing.expectEqual(ErrorCategory.validation, categorizeError(error.ZeroValue));
    try testing.expectEqual(ErrorCategory.system, categorizeError(error.FileNotFound));
    try testing.expectEqual(ErrorCategory.network, categorizeError(error.NetworkTimeout));
    try testing.expectEqual(ErrorCategory.unknown, categorizeError(error.GenericError));
}
```

Categorization enables policy-based error handling.

### Best Practices

1. **Catch specifically when possible**: Only use catch-all when you truly don't know error types
2. **Always log**: When catching all errors, log them for debugging
3. **Provide context**: Include information about what operation failed
4. **Use `@errorName()`**: Get error names for logging and categorization
5. **Track errors**: Collect errors for analysis and reporting
6. **Implement fallbacks**: Try alternative approaches before failing
7. **Categorize errors**: Group errors by type for appropriate handling

### Catch-All Patterns

**Pattern 1: Log and Continue**
```zig
operation() catch |err| {
    logger.log("Operation failed: {s}", .{@errorName(err)});
    continue; // or return default
};
```

**Pattern 2: Retry with Backoff**
```zig
var attempt: usize = 0;
while (attempt < MAX_RETRIES) : (attempt += 1) {
    operation() catch |err| {
        if (isFatal(err)) return err;
        std.time.sleep(backoff_ms * (attempt + 1));
        continue;
    };
    break;
}
```

**Pattern 3: Error Transformation**
```zig
const result = operation() catch |err| {
    std.debug.print("Failed: {s}\n", .{@errorName(err)});
    return error.OperationFailed;
};
```

### Common Gotchas

**Catching too broadly**: Don't use catch-all when you can handle specific errors:

```zig
// Wrong - loses type safety
operation() catch |err| { ... }

// Right - handle known errors
operation() catch |err| switch (err) {
    error.NotFound => handleNotFound(),
    error.PermissionDenied => handlePermission(),
    else => return err,
};
```

**Forgetting to log**: Always log caught errors:

```zig
// Wrong - error silently discarded
_ = operation() catch {};

// Right - error logged
operation() catch |err| {
    std.debug.print("Error: {s}\n", .{@errorName(err)});
};
```

**Inappropriate panics**: Only panic for truly unrecoverable errors:

```zig
// Wrong - panic on recoverable error
operation() catch |err| std.debug.panic("Failed: {s}", .{@errorName(err)});

// Right - handle gracefully
const result = operation() catch fallbackValue;
```

### Error Recovery Strategies

**By Category**:
```zig
operation() catch |err| switch (categorizeError(err)) {
    .validation => return error.BadInput,
    .network => retryWithBackoff(),
    .system => reportAndAbort(err),
    .unknown => std.debug.panic("Unexpected: {s}", .{@errorName(err)}),
};
```

**By Severity**:
```zig
operation() catch |err| {
    if (isCritical(err)) return err;
    if (isWarning(err)) log.warn("{s}", .{@errorName(err)});
    return defaultValue;
};
```

### Integration with Libraries

Libraries should generally avoid catch-all to preserve error information:

```zig
// Library code - preserve specific errors
pub fn libraryFunction() !Result {
    return innerOperation(); // Propagate specific error
}

// Application code - can catch all
pub fn main() !void {
    libraryFunction() catch |err| {
        std.debug.print("Application error: {s}\n", .{@errorName(err)});
        std.process.exit(1);
    };
}
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: anyerror_catch
fn riskyOperation(value: i32) !i32 {
    if (value < 0) return error.NegativeValue;
    if (value == 0) return error.ZeroValue;
    if (value > 100) return error.TooLarge;
    return value * 2;
}

fn safeOperation(value: i32) i32 {
    return riskyOperation(value) catch |err| {
        std.debug.print("Caught error: {s}\n", .{@errorName(err)});
        return 0; // Default value
    };
}

test "catch all errors with anyerror" {
    try testing.expectEqual(@as(i32, 0), safeOperation(-5));
    try testing.expectEqual(@as(i32, 0), safeOperation(0));
    try testing.expectEqual(@as(i32, 0), safeOperation(200));
    try testing.expectEqual(@as(i32, 20), safeOperation(10));
}
// ANCHOR_END: anyerror_catch

// ANCHOR: catch_and_log
fn processWithLogging(value: i32, logger: anytype) i32 {
    return riskyOperation(value) catch |err| {
        logger.log("Operation failed: {s}", .{@errorName(err)});
        return -1;
    };
}

const TestLogger = struct {
    message: ?[]const u8 = null,

    fn log(self: *TestLogger, comptime fmt: []const u8, args: anytype) void {
        _ = fmt;
        _ = args;
        self.message = "Error logged";
    }
};

test "catch all errors and log them" {
    var logger = TestLogger{};
    const result = processWithLogging(-5, &logger);

    try testing.expectEqual(@as(i32, -1), result);
    try testing.expect(logger.message != null);
}
// ANCHOR_END: catch_and_log

// ANCHOR: error_name_inspection
fn handleAnyError(err: anyerror) []const u8 {
    const name = @errorName(err);

    // Check error name for special handling
    if (std.mem.startsWith(u8, name, "File")) {
        return "File system error";
    } else if (std.mem.startsWith(u8, name, "Network")) {
        return "Network error";
    } else if (std.mem.startsWith(u8, name, "Parse")) {
        return "Parsing error";
    }

    return "Unknown error";
}

test "inspect error names" {
    try testing.expectEqualStrings("File system error", handleAnyError(error.FileNotFound));
    try testing.expectEqualStrings("Network error", handleAnyError(error.NetworkTimeout));
    try testing.expectEqualStrings("Parsing error", handleAnyError(error.ParseError));
    try testing.expectEqualStrings("Unknown error", handleAnyError(error.GenericError));
}
// ANCHOR_END: error_name_inspection

// ANCHOR: global_error_handler
const ErrorHandler = struct {
    error_count: usize = 0,
    last_error: ?anyerror = null,

    fn handle(self: *ErrorHandler, err: anyerror) void {
        self.error_count += 1;
        self.last_error = err;
        std.debug.print("Error #{d}: {s}\n", .{ self.error_count, @errorName(err) });
    }

    fn reset(self: *ErrorHandler) void {
        self.error_count = 0;
        self.last_error = null;
    }
};

fn operationWithHandler(value: i32, handler: *ErrorHandler) !i32 {
    return riskyOperation(value) catch |err| {
        handler.handle(err);
        return error.HandledError;
    };
}

test "use global error handler" {
    var handler = ErrorHandler{};

    _ = operationWithHandler(-5, &handler) catch {};
    try testing.expectEqual(@as(usize, 1), handler.error_count);
    try testing.expectEqual(error.NegativeValue, handler.last_error.?);

    _ = operationWithHandler(200, &handler) catch {};
    try testing.expectEqual(@as(usize, 2), handler.error_count);
}
// ANCHOR_END: global_error_handler

// ANCHOR: try_or_default
fn tryOrDefault(comptime T: type, operation: anytype, default: T) T {
    return operation catch default;
}

test "try operation or return default" {
    const result1 = tryOrDefault(i32, riskyOperation(10), 0);
    try testing.expectEqual(@as(i32, 20), result1);

    const result2 = tryOrDefault(i32, riskyOperation(-5), 999);
    try testing.expectEqual(@as(i32, 999), result2);
}
// ANCHOR_END: try_or_default

// ANCHOR: panic_on_error
fn mustSucceed(value: i32) i32 {
    return riskyOperation(value) catch |err| {
        std.debug.panic("Operation must not fail: {s}", .{@errorName(err)});
    };
}

test "operations that must succeed" {
    // Only test valid cases since panic would terminate
    try testing.expectEqual(@as(i32, 20), mustSucceed(10));
    try testing.expectEqual(@as(i32, 100), mustSucceed(50));
}
// ANCHOR_END: panic_on_error

// ANCHOR: catch_all_pattern
fn robustOperation(value: i32) !struct { result: i32, had_error: bool } {
    if (riskyOperation(value)) |val| {
        return .{ .result = val, .had_error = false };
    } else |err| {
        std.debug.print("Recovered from error: {s}\n", .{@errorName(err)});
        return .{ .result = 0, .had_error = true };
    }
}

test "catch all with explicit result type" {
    const success = try robustOperation(10);
    try testing.expectEqual(@as(i32, 20), success.result);
    try testing.expect(!success.had_error);

    const failure = try robustOperation(-5);
    try testing.expectEqual(@as(i32, 0), failure.result);
    try testing.expect(failure.had_error);
}
// ANCHOR_END: catch_all_pattern

// ANCHOR: error_tracking
const ErrorTracker = struct {
    errors: std.ArrayList(anyerror),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) ErrorTracker {
        return .{
            .errors = std.ArrayList(anyerror){},
            .allocator = allocator,
        };
    }

    fn deinit(self: *ErrorTracker) void {
        self.errors.deinit(self.allocator);
    }

    fn track(self: *ErrorTracker, err: anyerror) !void {
        try self.errors.append(self.allocator, err);
    }

    fn getErrors(self: *const ErrorTracker) []const anyerror {
        return self.errors.items;
    }
};

fn trackAllErrors(values: []const i32, tracker: *ErrorTracker) !void {
    for (values) |value| {
        _ = riskyOperation(value) catch |err| {
            try tracker.track(err);
            continue;
        };
    }
}

test "track all encountered errors" {
    var tracker = ErrorTracker.init(testing.allocator);
    defer tracker.deinit();

    const values = [_]i32{ -5, 0, 10, 200, -1 };
    try trackAllErrors(&values, &tracker);

    const errors = tracker.getErrors();
    try testing.expectEqual(@as(usize, 4), errors.len);
    try testing.expectEqual(error.NegativeValue, errors[0]);
    try testing.expectEqual(error.ZeroValue, errors[1]);
}
// ANCHOR_END: error_tracking

// ANCHOR: fallback_chain
fn withFallbacks(value: i32) i32 {
    // Try primary operation
    if (riskyOperation(value)) |result| {
        return result;
    } else |err1| {
        std.debug.print("Primary failed: {s}\n", .{@errorName(err1)});

        // Try fallback with adjusted value
        const adjusted = if (value < 0) -value else value;
        if (riskyOperation(adjusted)) |result| {
            return result;
        } else |err2| {
            std.debug.print("Fallback failed: {s}\n", .{@errorName(err2)});

            // Return safe default
            return 1;
        }
    }
}

test "fallback chain on any error" {
    try testing.expectEqual(@as(i32, 20), withFallbacks(10));
    try testing.expectEqual(@as(i32, 10), withFallbacks(-5)); // -(-5) = 5, * 2 = 10
    try testing.expectEqual(@as(i32, 1), withFallbacks(0)); // Both fail, return default
}
// ANCHOR_END: fallback_chain

// ANCHOR: error_metrics
const ErrorMetrics = struct {
    total_operations: usize = 0,
    total_errors: usize = 0,
    error_types: std.StringHashMap(usize),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) ErrorMetrics {
        return .{
            .error_types = std.StringHashMap(usize).init(allocator),
            .allocator = allocator,
        };
    }

    fn deinit(self: *ErrorMetrics) void {
        self.error_types.deinit();
    }

    fn recordOperation(self: *ErrorMetrics, result: anytype) !void {
        self.total_operations += 1;

        if (result) |_| {
            // Success
        } else |err| {
            self.total_errors += 1;
            const name = @errorName(err);
            const count = self.error_types.get(name) orelse 0;
            try self.error_types.put(name, count + 1);
        }
    }

    fn errorRate(self: *const ErrorMetrics) f64 {
        if (self.total_operations == 0) return 0;
        return @as(f64, @floatFromInt(self.total_errors)) / @as(f64, @floatFromInt(self.total_operations));
    }
};

test "collect error metrics" {
    var metrics = ErrorMetrics.init(testing.allocator);
    defer metrics.deinit();

    try metrics.recordOperation(riskyOperation(10));
    try metrics.recordOperation(riskyOperation(-5));
    try metrics.recordOperation(riskyOperation(0));
    try metrics.recordOperation(riskyOperation(20));

    try testing.expectEqual(@as(usize, 4), metrics.total_operations);
    try testing.expectEqual(@as(usize, 2), metrics.total_errors);
    try testing.expect(metrics.errorRate() > 0.4);
}
// ANCHOR_END: error_metrics

// ANCHOR: error_categorization
const ErrorCategory = enum {
    validation,
    system,
    network,
    unknown,
};

fn categorizeError(err: anyerror) ErrorCategory {
    const name = @errorName(err);

    if (std.mem.indexOf(u8, name, "Invalid") != null or
        std.mem.indexOf(u8, name, "Zero") != null or
        std.mem.indexOf(u8, name, "Negative") != null or
        std.mem.indexOf(u8, name, "TooLarge") != null)
    {
        return .validation;
    } else if (std.mem.indexOf(u8, name, "File") != null or
        std.mem.indexOf(u8, name, "Memory") != null)
    {
        return .system;
    } else if (std.mem.indexOf(u8, name, "Network") != null or
        std.mem.indexOf(u8, name, "Timeout") != null)
    {
        return .network;
    }

    return .unknown;
}

test "categorize any error" {
    try testing.expectEqual(ErrorCategory.validation, categorizeError(error.NegativeValue));
    try testing.expectEqual(ErrorCategory.validation, categorizeError(error.ZeroValue));
    try testing.expectEqual(ErrorCategory.system, categorizeError(error.FileNotFound));
    try testing.expectEqual(ErrorCategory.network, categorizeError(error.NetworkTimeout));
    try testing.expectEqual(ErrorCategory.unknown, categorizeError(error.GenericError));
}
// ANCHOR_END: error_categorization
```

### See Also

- Recipe 14.3: Testing for exceptional conditions in unit tests
- Recipe 14.6: Handling multiple exceptions at once
- Recipe 1.2: Error Handling Patterns
- Recipe 0.11: Optionals, Errors, and Resource Cleanup

---

## Recipe 14.8: Creating custom exception types {#recipe-14-8}

**Tags:** comptime, error-handling, http, networking, testing, testing-debugging
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_8.zig`

### Problem

You need to define custom error types specific to your domain or application. You want to create meaningful, type-safe errors that make your code more maintainable and easier to debug.

### Solution

Define custom error sets using the `error` keyword:

```zig
const FileError = error{
    NotFound,
    PermissionDenied,
    AlreadyExists,
};

fn openFile(path: []const u8) FileError!void {
    if (std.mem.eql(u8, path, "missing.txt")) {
        return error.NotFound;
    }
    if (std.mem.eql(u8, path, "protected.txt")) {
        return error.PermissionDenied;
    }
    // Success
}

test "define and use custom error set" {
    try testing.expectError(error.NotFound, openFile("missing.txt"));
    try testing.expectError(error.PermissionDenied, openFile("protected.txt"));
    try openFile("valid.txt");
}
```

### Discussion

Zig's error sets are compile-time types that provide type-safe error handling without runtime overhead. Custom error sets make your code self-documenting and help catch error handling bugs at compile time.

### Composing Error Sets

Combine multiple error sets using the `||` operator:

```zig
const NetworkError = error{
    ConnectionRefused,
    Timeout,
    HostUnreachable,
};

const DatabaseError = error{
    QueryFailed,
    ConnectionLost,
    ConstraintViolation,
};

// Combine error sets with ||
const ServiceError = NetworkError || DatabaseError;

fn fetchData(source: u8) ServiceError![]const u8 {
    switch (source) {
        0 => return error.ConnectionRefused,
        1 => return error.QueryFailed,
        2 => return error.Timeout,
        else => return "data",
    }
}

test "compose multiple error sets" {
    try testing.expectError(error.ConnectionRefused, fetchData(0));
    try testing.expectError(error.QueryFailed, fetchData(1));
    try testing.expectError(error.Timeout, fetchData(2));
    try testing.expectEqualStrings("data", try fetchData(99));
}
```

Error set composition creates a union of all errors from both sets, enabling functions to return errors from multiple domains.

### Inferred Error Sets

Let Zig infer error sets automatically:

```zig
fn processValue(value: i32) !i32 {
    if (value < 0) return error.NegativeValue;
    if (value == 0) return error.ZeroValue;
    if (value > 100) return error.TooLarge;
    return value * 2;
}

test "error set inference" {
    try testing.expectError(error.NegativeValue, processValue(-1));
    try testing.expectError(error.ZeroValue, processValue(0));
    try testing.expectError(error.TooLarge, processValue(200));
    try testing.expectEqual(@as(i32, 20), try processValue(10));
}
```

The `!` operator without a specific error set means Zig will infer which errors the function can return. This is convenient but makes the error contract less explicit.

### Hierarchical Error Organization

Structure errors in a hierarchy for large applications:

```zig
const ValidationError = error{
    InvalidEmail,
    InvalidPhone,
    InvalidZipCode,
};

const AuthError = error{
    InvalidCredentials,
    SessionExpired,
    AccountLocked,
};

const UserError = ValidationError || AuthError;

const User = struct {
    email: []const u8,
    phone: []const u8,

    fn validate(self: User) ValidationError!void {
        if (!std.mem.containsAtLeast(u8, self.email, 1, "@")) {
            return error.InvalidEmail;
        }
        if (self.phone.len < 10) {
            return error.InvalidPhone;
        }
    }

    fn authenticate(self: User, password: []const u8) AuthError!void {
        _ = self;
        if (password.len < 8) {
            return error.InvalidCredentials;
        }
    }

    fn register(self: User, password: []const u8) UserError!void {
        try self.validate();
        try self.authenticate(password);
    }
};

test "hierarchical error sets" {
    const user1 = User{ .email = "invalid", .phone = "1234567890" };
    try testing.expectError(error.InvalidEmail, user1.validate());

    const user2 = User{ .email = "test@example.com", .phone = "123" };
    try testing.expectError(error.InvalidPhone, user2.validate());

    const user3 = User{ .email = "test@example.com", .phone = "1234567890" };
    try testing.expectError(error.InvalidCredentials, user3.register("short"));
}
```

Hierarchical organization lets you handle errors at different levels of abstraction.

### Domain-Specific Errors

Group errors by business domain:

```zig
const OrderError = error{
    InsufficientInventory,
    InvalidQuantity,
    PriceMismatch,
};

const PaymentError = error{
    InsufficientFunds,
    CardDeclined,
    PaymentGatewayError,
};

const ShippingError = error{
    InvalidAddress,
    ShippingUnavailable,
    WeightExceeded,
};

const CheckoutError = OrderError || PaymentError || ShippingError;

fn placeOrder(step: u8) CheckoutError!void {
    switch (step) {
        0 => return error.InsufficientInventory,
        1 => return error.InsufficientFunds,
        2 => return error.InvalidAddress,
        else => {},
    }
}

test "domain-specific error sets" {
    try testing.expectError(error.InsufficientInventory, placeOrder(0));
    try testing.expectError(error.InsufficientFunds, placeOrder(1));
    try testing.expectError(error.InvalidAddress, placeOrder(2));
    try placeOrder(99);
}
```

Domain-specific error sets make it clear which part of your system failed.

### Error Context and Metadata

Combine errors with additional context:

```zig
const ParseError = error{
    UnexpectedToken,
    UnexpectedEOF,
    InvalidSyntax,
};

const ParseResult = struct {
    error_type: ?ParseError,
    line: usize,
    column: usize,
    message: []const u8,

    fn fromError(err: ParseError, line: usize, column: usize) ParseResult {
        const message = switch (err) {
            error.UnexpectedToken => "Unexpected token",
            error.UnexpectedEOF => "Unexpected end of file",
            error.InvalidSyntax => "Invalid syntax",
        };
        return .{
            .error_type = err,
            .line = line,
            .column = column,
            .message = message,
        };
    }

    fn success() ParseResult {
        return .{
            .error_type = null,
            .line = 0,
            .column = 0,
            .message = "Success",
        };
    }
};

fn parseWithContext(input: []const u8) ParseError!ParseResult {
    if (input.len == 0) return error.UnexpectedEOF;
    if (input[0] == '!') return error.UnexpectedToken;
    return ParseResult.success();
}

test "error context and metadata" {
    const result = parseWithContext("!invalid") catch |err| {
        const context = ParseResult.fromError(err, 1, 5);
        try testing.expectEqual(error.UnexpectedToken, context.error_type.?);
        try testing.expectEqual(@as(usize, 1), context.line);
        try testing.expectEqualStrings("Unexpected token", context.message);
        return;
    };
    try testing.expect(result.error_type == null);
}
```

Wrapping errors in a struct preserves error information plus additional debugging context like line numbers and messages.

### Converting Between Error Sets

Transform errors from one domain to another:

```zig
fn convertNetworkError(err: NetworkError) DatabaseError {
    // Convert network errors to database errors
    return switch (err) {
        error.ConnectionRefused, error.HostUnreachable => error.ConnectionLost,
        error.Timeout => error.QueryFailed,
    };
}

test "convert between error sets" {
    try testing.expectEqual(error.ConnectionLost, convertNetworkError(error.ConnectionRefused));
    try testing.expectEqual(error.QueryFailed, convertNetworkError(error.Timeout));
}
```

Error conversion is useful when crossing abstraction boundaries.

### Namespacing Error Sets

Use structs to namespace related error sets:

```zig
const Http = struct {
    pub const Error = error{
        BadRequest,
        Unauthorized,
        NotFound,
        ServerError,
    };

    pub fn request(status: u16) Error!void {
        switch (status) {
            400 => return error.BadRequest,
            401 => return error.Unauthorized,
            404 => return error.NotFound,
            500 => return error.ServerError,
            else => {},
        }
    }
};

const Db = struct {
    pub const Error = error{
        NotFound,
        Duplicate,
        ConstraintViolation,
    };

    pub fn query(id: u32) Error!void {
        if (id == 0) return error.NotFound;
        if (id == 999) return error.Duplicate;
    }
};

test "namespaced error sets" {
    try testing.expectError(error.NotFound, Http.request(404));
    try testing.expectError(error.NotFound, Db.query(0));
    try testing.expectError(error.BadRequest, Http.request(400));
}
```

Namespacing prevents name collisions when different subsystems use similar error names like `NotFound`.

### Documenting Error Sets

Add documentation to your error sets:

```zig
/// Errors that can occur during file operations
const IoError = error{
    /// File or directory not found
    NotFound,
    /// Insufficient permissions to access resource
    AccessDenied,
    /// Disk is full or quota exceeded
    NoSpaceLeft,
    /// File or directory already exists
    AlreadyExists,
};

/// Opens a file for reading
/// Returns IoError if the file cannot be opened
fn readFile(path: []const u8) IoError!void {
    if (std.mem.eql(u8, path, "missing")) {
        return error.NotFound;
    }
}

test "documented error sets" {
    try testing.expectError(error.NotFound, readFile("missing"));
}
```

Doc comments on error sets and individual errors improve code maintainability.

### Generic Error Handling

Use comptime to work with any error set:

```zig
fn GenericResult(comptime T: type, comptime ErrorSet: type) type {
    return struct {
        data: T,
        err: ?ErrorSet,

        pub fn ok(value: T) @This() {
            return .{ .data = value, .err = null };
        }

        pub fn fail(err: ErrorSet) @This() {
            return .{ .data = undefined, .err = err };
        }

        pub fn unwrap(self: @This()) ErrorSet!T {
            if (self.err) |e| return e;
            return self.data;
        }
    };
}

fn processGeneric(comptime ErrorSet: type, value: i32) ErrorSet!i32 {
    if (value < 0) return error.NotFound;
    return value * 2;
}

test "generic error handling" {
    // Generic result type with FileError
    const FileResult = GenericResult(i32, FileError);
    const success = FileResult.ok(42);
    try testing.expectEqual(@as(i32, 42), try success.unwrap());

    const failure = FileResult.fail(error.NotFound);
    try testing.expectError(error.NotFound, failure.unwrap());

    // Generic function with FileError (which contains NotFound)
    try testing.expectEqual(@as(i32, 20), try processGeneric(FileError, 10));
    try testing.expectError(error.NotFound, processGeneric(FileError, -1));
}
```

Generic error handling enables reusable code that works with different error sets.

### Best Practices

1. **Be specific**: Create meaningful error names that describe what went wrong
2. **Use composition**: Combine error sets with `||` rather than creating large monolithic sets
3. **Namespace carefully**: Use structs to organize errors by subsystem
4. **Document errors**: Add doc comments explaining when errors occur
5. **Prefer explicit**: Use specific error sets instead of inferred `!` for public APIs
6. **Group by domain**: Organize errors by business domain, not implementation detail
7. **Convert at boundaries**: Transform errors when crossing abstraction layers

### Error Set Design Patterns

**Pattern 1: Layer-Based Organization**
```zig
const DataError = error{NotFound, InvalidFormat};
const NetworkError = error{Timeout, Refused};
const ApplicationError = DataError || NetworkError;
```

**Pattern 2: Fine-Grained Control**
```zig
const ReadError = error{FileNotFound, AccessDenied};
const WriteError = error{DiskFull, ReadOnly};
const IoError = ReadError || WriteError;
```

**Pattern 3: Context Enrichment**
```zig
const ErrorWithContext = struct {
    err: MyError,
    file: []const u8,
    line: usize,
};
```

### Common Gotchas

**Overly broad error sets**: Don't create catch-all error sets:

```zig
// Wrong - too generic
const AppError = error{Error, Failed, Bad};

// Right - specific and meaningful
const ValidationError = error{InvalidEmail, InvalidPhone};
const DatabaseError = error{ConnectionFailed, QueryTimeout};
```

**Not using composition**: Avoid duplicating errors across sets:

```zig
// Wrong - duplicated NotFound
const FileError = error{NotFound, AccessDenied};
const DbError = error{NotFound, QueryFailed};

// Right - compose from shared errors
const ResourceError = error{NotFound};
const FileError = ResourceError || error{AccessDenied};
const DbError = ResourceError || error{QueryFailed};
```

**Ignoring error documentation**: Always document complex error conditions:

```zig
// Wrong - no context
const Error = error{Failed};

// Right - explains when it occurs
/// Returned when database connection pool is exhausted
/// after MAX_RETRIES attempts with exponential backoff
const Error = error{ConnectionPoolExhausted};
```

### Error Set Size and Performance

Error sets have zero runtime cost:
- Errors are represented as `u16` values at runtime
- Error set membership is checked at compile time
- No memory allocation or overhead
- Perfect for performance-critical code

### Comparison with Other Languages

**Zig vs. Exceptions:**
- Zig errors are explicit in function signatures
- No hidden control flow or stack unwinding
- Compile-time verification of error handling
- Zero runtime overhead

**Zig vs. Result Types:**
- Similar to Rust's `Result<T, E>`
- But integrated into the language with `!` syntax
- Error sets are first-class types
- Automatic error set inference available

### Integration with Standard Library

Standard library functions use error sets extensively:

```zig
// std.fs uses IoError
pub const OpenError = error{
    FileNotFound,
    IsDir,
    AccessDenied,
    // ... many more
};

// Compose with your own errors
const MyFileError = std.fs.File.OpenError || error{ConfigInvalid};
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_error_set
const FileError = error{
    NotFound,
    PermissionDenied,
    AlreadyExists,
};

fn openFile(path: []const u8) FileError!void {
    if (std.mem.eql(u8, path, "missing.txt")) {
        return error.NotFound;
    }
    if (std.mem.eql(u8, path, "protected.txt")) {
        return error.PermissionDenied;
    }
    // Success
}

test "define and use custom error set" {
    try testing.expectError(error.NotFound, openFile("missing.txt"));
    try testing.expectError(error.PermissionDenied, openFile("protected.txt"));
    try openFile("valid.txt");
}
// ANCHOR_END: basic_error_set

// ANCHOR: composing_errors
const NetworkError = error{
    ConnectionRefused,
    Timeout,
    HostUnreachable,
};

const DatabaseError = error{
    QueryFailed,
    ConnectionLost,
    ConstraintViolation,
};

// Combine error sets with ||
const ServiceError = NetworkError || DatabaseError;

fn fetchData(source: u8) ServiceError![]const u8 {
    switch (source) {
        0 => return error.ConnectionRefused,
        1 => return error.QueryFailed,
        2 => return error.Timeout,
        else => return "data",
    }
}

test "compose multiple error sets" {
    try testing.expectError(error.ConnectionRefused, fetchData(0));
    try testing.expectError(error.QueryFailed, fetchData(1));
    try testing.expectError(error.Timeout, fetchData(2));
    try testing.expectEqualStrings("data", try fetchData(99));
}
// ANCHOR_END: composing_errors

// ANCHOR: inferred_errors
fn processValue(value: i32) !i32 {
    if (value < 0) return error.NegativeValue;
    if (value == 0) return error.ZeroValue;
    if (value > 100) return error.TooLarge;
    return value * 2;
}

test "error set inference" {
    try testing.expectError(error.NegativeValue, processValue(-1));
    try testing.expectError(error.ZeroValue, processValue(0));
    try testing.expectError(error.TooLarge, processValue(200));
    try testing.expectEqual(@as(i32, 20), try processValue(10));
}
// ANCHOR_END: inferred_errors

// ANCHOR: hierarchical_errors
const ValidationError = error{
    InvalidEmail,
    InvalidPhone,
    InvalidZipCode,
};

const AuthError = error{
    InvalidCredentials,
    SessionExpired,
    AccountLocked,
};

const UserError = ValidationError || AuthError;

const User = struct {
    email: []const u8,
    phone: []const u8,

    fn validate(self: User) ValidationError!void {
        if (!std.mem.containsAtLeast(u8, self.email, 1, "@")) {
            return error.InvalidEmail;
        }
        if (self.phone.len < 10) {
            return error.InvalidPhone;
        }
    }

    fn authenticate(self: User, password: []const u8) AuthError!void {
        _ = self;
        if (password.len < 8) {
            return error.InvalidCredentials;
        }
    }

    fn register(self: User, password: []const u8) UserError!void {
        try self.validate();
        try self.authenticate(password);
    }
};

test "hierarchical error sets" {
    const user1 = User{ .email = "invalid", .phone = "1234567890" };
    try testing.expectError(error.InvalidEmail, user1.validate());

    const user2 = User{ .email = "test@example.com", .phone = "123" };
    try testing.expectError(error.InvalidPhone, user2.validate());

    const user3 = User{ .email = "test@example.com", .phone = "1234567890" };
    try testing.expectError(error.InvalidCredentials, user3.register("short"));
}
// ANCHOR_END: hierarchical_errors

// ANCHOR: domain_errors
const OrderError = error{
    InsufficientInventory,
    InvalidQuantity,
    PriceMismatch,
};

const PaymentError = error{
    InsufficientFunds,
    CardDeclined,
    PaymentGatewayError,
};

const ShippingError = error{
    InvalidAddress,
    ShippingUnavailable,
    WeightExceeded,
};

const CheckoutError = OrderError || PaymentError || ShippingError;

fn placeOrder(step: u8) CheckoutError!void {
    switch (step) {
        0 => return error.InsufficientInventory,
        1 => return error.InsufficientFunds,
        2 => return error.InvalidAddress,
        else => {},
    }
}

test "domain-specific error sets" {
    try testing.expectError(error.InsufficientInventory, placeOrder(0));
    try testing.expectError(error.InsufficientFunds, placeOrder(1));
    try testing.expectError(error.InvalidAddress, placeOrder(2));
    try placeOrder(99);
}
// ANCHOR_END: domain_errors

// ANCHOR: error_context
const ParseError = error{
    UnexpectedToken,
    UnexpectedEOF,
    InvalidSyntax,
};

const ParseResult = struct {
    error_type: ?ParseError,
    line: usize,
    column: usize,
    message: []const u8,

    fn fromError(err: ParseError, line: usize, column: usize) ParseResult {
        const message = switch (err) {
            error.UnexpectedToken => "Unexpected token",
            error.UnexpectedEOF => "Unexpected end of file",
            error.InvalidSyntax => "Invalid syntax",
        };
        return .{
            .error_type = err,
            .line = line,
            .column = column,
            .message = message,
        };
    }

    fn success() ParseResult {
        return .{
            .error_type = null,
            .line = 0,
            .column = 0,
            .message = "Success",
        };
    }
};

fn parseWithContext(input: []const u8) ParseError!ParseResult {
    if (input.len == 0) return error.UnexpectedEOF;
    if (input[0] == '!') return error.UnexpectedToken;
    return ParseResult.success();
}

test "error context and metadata" {
    const result = parseWithContext("!invalid") catch |err| {
        const context = ParseResult.fromError(err, 1, 5);
        try testing.expectEqual(error.UnexpectedToken, context.error_type.?);
        try testing.expectEqual(@as(usize, 1), context.line);
        try testing.expectEqualStrings("Unexpected token", context.message);
        return;
    };
    try testing.expect(result.error_type == null);
}
// ANCHOR_END: error_context

// ANCHOR: error_conversion
fn convertNetworkError(err: NetworkError) DatabaseError {
    // Convert network errors to database errors
    return switch (err) {
        error.ConnectionRefused, error.HostUnreachable => error.ConnectionLost,
        error.Timeout => error.QueryFailed,
    };
}

test "convert between error sets" {
    try testing.expectEqual(error.ConnectionLost, convertNetworkError(error.ConnectionRefused));
    try testing.expectEqual(error.QueryFailed, convertNetworkError(error.Timeout));
}
// ANCHOR_END: error_conversion

// ANCHOR: error_namespacing
const Http = struct {
    pub const Error = error{
        BadRequest,
        Unauthorized,
        NotFound,
        ServerError,
    };

    pub fn request(status: u16) Error!void {
        switch (status) {
            400 => return error.BadRequest,
            401 => return error.Unauthorized,
            404 => return error.NotFound,
            500 => return error.ServerError,
            else => {},
        }
    }
};

const Db = struct {
    pub const Error = error{
        NotFound,
        Duplicate,
        ConstraintViolation,
    };

    pub fn query(id: u32) Error!void {
        if (id == 0) return error.NotFound;
        if (id == 999) return error.Duplicate;
    }
};

test "namespaced error sets" {
    try testing.expectError(error.NotFound, Http.request(404));
    try testing.expectError(error.NotFound, Db.query(0));
    try testing.expectError(error.BadRequest, Http.request(400));
}
// ANCHOR_END: error_namespacing

// ANCHOR: error_documentation
/// Errors that can occur during file operations
const IoError = error{
    /// File or directory not found
    NotFound,
    /// Insufficient permissions to access resource
    AccessDenied,
    /// Disk is full or quota exceeded
    NoSpaceLeft,
    /// File or directory already exists
    AlreadyExists,
};

/// Opens a file for reading
/// Returns IoError if the file cannot be opened
fn readFile(path: []const u8) IoError!void {
    if (std.mem.eql(u8, path, "missing")) {
        return error.NotFound;
    }
}

test "documented error sets" {
    try testing.expectError(error.NotFound, readFile("missing"));
}
// ANCHOR_END: error_documentation

// ANCHOR: generic_errors
fn GenericResult(comptime T: type, comptime ErrorSet: type) type {
    return struct {
        data: T,
        err: ?ErrorSet,

        pub fn ok(value: T) @This() {
            return .{ .data = value, .err = null };
        }

        pub fn fail(err: ErrorSet) @This() {
            return .{ .data = undefined, .err = err };
        }

        pub fn unwrap(self: @This()) ErrorSet!T {
            if (self.err) |e| return e;
            return self.data;
        }
    };
}

fn processGeneric(comptime ErrorSet: type, value: i32) ErrorSet!i32 {
    if (value < 0) return error.NotFound;
    return value * 2;
}

test "generic error handling" {
    // Generic result type with FileError
    const FileResult = GenericResult(i32, FileError);
    const success = FileResult.ok(42);
    try testing.expectEqual(@as(i32, 42), try success.unwrap());

    const failure = FileResult.fail(error.NotFound);
    try testing.expectError(error.NotFound, failure.unwrap());

    // Generic function with FileError (which contains NotFound)
    try testing.expectEqual(@as(i32, 20), try processGeneric(FileError, 10));
    try testing.expectError(error.NotFound, processGeneric(FileError, -1));
}
// ANCHOR_END: generic_errors
```

### See Also

- Recipe 14.6: Handling multiple exceptions at once
- Recipe 14.7: Catching all exceptions
- Recipe 14.9: Raising an exception in response to another exception
- Recipe 1.2: Error Handling Patterns
- Recipe 0.11: Optionals, Errors, and Resource Cleanup

---

## Recipe 14.9: Raising an exception in response to another exception {#recipe-14-9}

**Tags:** error-handling, testing, testing-debugging
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_9.zig`

### Problem

You need to catch one error and return a different error, transforming low-level errors into high-level ones or adding context. You want to maintain error information while crossing abstraction boundaries.

### Solution

Catch an error and return a new error with appropriate context:

```zig
const LowLevelError = error{
    FileNotFound,
    AccessDenied,
    DiskFull,
};

const HighLevelError = error{
    ConfigurationError,
    InitializationFailed,
    ResourceUnavailable,
};

fn readConfigFile(path: []const u8) LowLevelError![]const u8 {
    if (std.mem.eql(u8, path, "missing.conf")) {
        return error.FileNotFound;
    }
    if (std.mem.eql(u8, path, "protected.conf")) {
        return error.AccessDenied;
    }
    return "config data";
}

fn loadConfiguration(path: []const u8) HighLevelError![]const u8 {
    const config = readConfigFile(path) catch |err| {
        std.debug.print("Failed to read config: {s}\n", .{@errorName(err)});
        return error.ConfigurationError;
    };
    return config;
}

test "transform low-level errors to high-level" {
    try testing.expectError(error.ConfigurationError, loadConfiguration("missing.conf"));
    try testing.expectError(error.ConfigurationError, loadConfiguration("protected.conf"));
    try testing.expectEqualStrings("config data", try loadConfiguration("valid.conf"));
}
```

### Discussion

Error transformation is essential for maintaining clean abstraction layers. Low-level errors (like file I/O errors) should be transformed into domain-specific errors (like configuration errors) at API boundaries.

### Error Context Chaining

Chain errors through multiple layers while preserving context:

```zig
const IoError = error{ ReadFailed, WriteFailed, SeekFailed };
const DatabaseError = error{ QueryFailed, TransactionAborted };

const ErrorChain = struct {
    original: anyerror,
    context: []const u8,
    layer: u8,

    fn fromIoError(err: IoError, context: []const u8) DatabaseError {
        std.debug.print("IO Error ({s}) -> Database Error: {s}\n", .{ @errorName(err), context });
        return error.QueryFailed;
    }

    fn fromDbError(err: DatabaseError, context: []const u8) IoError {
        std.debug.print("DB Error ({s}) -> IO Error: {s}\n", .{ @errorName(err), context });
        return error.WriteFailed;
    }
};

fn lowLevelRead(should_fail: bool) IoError!i32 {
    if (should_fail) return error.ReadFailed;
    return 42;
}

fn databaseQuery(should_fail: bool) DatabaseError!i32 {
    const value = lowLevelRead(should_fail) catch |err| {
        return ErrorChain.fromIoError(err, "Database query requires file read");
    };
    return value;
}

test "chain errors with context" {
    try testing.expectEqual(@as(i32, 42), try databaseQuery(false));
    try testing.expectError(error.QueryFailed, databaseQuery(true));
}
```

Error chaining helps debug complex failures by showing which layer failed and why.

### Wrapping Errors with Metadata

Wrap errors in structs to preserve both the original error and additional context:

```zig
const OperationError = error{
    NetworkFailure,
    ParseFailure,
    ValidationFailure,
};

const Result = struct {
    value: ?i32,
    original_error: ?anyerror,
    wrapped_error: ?OperationError,
    message: []const u8,

    fn success(value: i32) Result {
        return .{
            .value = value,
            .original_error = null,
            .wrapped_error = null,
            .message = "Success",
        };
    }

    fn failure(original: anyerror, wrapped: OperationError, message: []const u8) Result {
        return .{
            .value = null,
            .original_error = original,
            .wrapped_error = wrapped,
            .message = message,
        };
    }
};

fn parseValue(input: []const u8) !i32 {
    if (input.len == 0) return error.EmptyInput;
    if (input[0] == 'x') return error.InvalidFormat;
    return 42;
}

fn processInput(input: []const u8) OperationError!Result {
    const value = parseValue(input) catch |err| {
        const wrapped_err = error.ParseFailure;
        const msg = "Failed to parse input value";
        return Result.failure(err, wrapped_err, msg);
    };
    return Result.success(value);
}

test "wrap errors with metadata" {
    const success = try processInput("42");
    try testing.expectEqual(@as(i32, 42), success.value.?);
    try testing.expect(success.wrapped_error == null);

    const failure = try processInput("");
    try testing.expect(failure.value == null);
    try testing.expectEqual(error.ParseFailure, failure.wrapped_error.?);
    try testing.expectEqualStrings("Failed to parse input value", failure.message);
}
```

This pattern is useful when you need to preserve the original error for debugging while providing user-friendly error information.

### Conditional Error Wrapping

Transform errors selectively based on type and context:

```zig
fn openResource(name: []const u8) !void {
    if (std.mem.eql(u8, name, "locked")) return error.ResourceLocked;
    if (std.mem.eql(u8, name, "missing")) return error.ResourceNotFound;
}

fn acquireResource(name: []const u8, retry: bool) !void {
    openResource(name) catch |err| {
        // Decide whether to wrap based on error type
        if (err == error.ResourceLocked) {
            return if (retry) error.RetryableError else err;
        } else if (err == error.ResourceNotFound) {
            return error.PermanentError;
        } else {
            return err;
        }
    };
}

test "conditionally wrap errors" {
    try acquireResource("available", false);
    try testing.expectError(error.RetryableError, acquireResource("locked", true));
    try testing.expectError(error.ResourceLocked, acquireResource("locked", false));
    try testing.expectError(error.PermanentError, acquireResource("missing", false));
}
```

Conditional wrapping lets you classify errors by recoverability, making retry logic easier to implement.

### Error Enrichment

Add metadata like timestamps and categorization to errors:

```zig
const EnrichedError = struct {
    category: ErrorCategory,
    original: anyerror,
    timestamp: i64,
    context: []const u8,

    fn fromError(err: anyerror, ctx: []const u8) EnrichedError {
        return .{
            .category = categorizeError(err),
            .original = err,
            .timestamp = std.time.milliTimestamp(),
            .context = ctx,
        };
    }
};

const ErrorCategory = enum {
    transient,
    permanent,
    unknown,
};

fn categorizeError(err: anyerror) ErrorCategory {
    const name = @errorName(err);
    if (std.mem.indexOf(u8, name, "Timeout") != null or
        std.mem.indexOf(u8, name, "Busy") != null)
    {
        return .transient;
    } else if (std.mem.indexOf(u8, name, "NotFound") != null or
        std.mem.indexOf(u8, name, "Invalid") != null)
    {
        return .permanent;
    }
    return .unknown;
}

fn performOperation(should_fail: bool) !i32 {
    if (should_fail) return error.Timeout;
    return 100;
}

fn wrappedOperation(should_fail: bool) !i32 {
    return performOperation(should_fail) catch |err| {
        const enriched = EnrichedError.fromError(err, "Operation context");
        std.debug.print("Enriched error: category={s}, error={s}\n", .{
            @tagName(enriched.category),
            @errorName(enriched.original),
        });

        return switch (enriched.category) {
            .transient => error.ShouldRetry,
            .permanent => error.ShouldAbort,
            .unknown => err,
        };
    };
}

test "enrich errors with metadata" {
    try testing.expectEqual(@as(i32, 100), try wrappedOperation(false));
    try testing.expectError(error.ShouldRetry, wrappedOperation(true));
}
```

Enrichment helps with error analytics and determining appropriate recovery strategies.

### Multi-Layer Error Wrapping

Transform errors through multiple abstraction layers:

```zig
const Layer1Error = error{ L1Failed };
const Layer2Error = error{ L2Failed };
const Layer3Error = error{ L3Failed };

fn layer1Operation(fail: bool) Layer1Error!i32 {
    if (fail) return error.L1Failed;
    return 1;
}

fn layer2Operation(fail: bool) Layer2Error!i32 {
    const result = layer1Operation(fail) catch |err| {
        std.debug.print("Layer 2 caught: {s}\n", .{@errorName(err)});
        return error.L2Failed;
    };
    return result * 2;
}

fn layer3Operation(fail: bool) Layer3Error!i32 {
    const result = layer2Operation(fail) catch |err| {
        std.debug.print("Layer 3 caught: {s}\n", .{@errorName(err)});
        return error.L3Failed;
    };
    return result * 3;
}

test "multi-layer error wrapping" {
    try testing.expectEqual(@as(i32, 6), try layer3Operation(false));
    try testing.expectError(error.L3Failed, layer3Operation(true));
}
```

Each layer wraps the error from the layer below, creating a chain of transformations.

### Error Recovery Strategy Chain

Use error information to determine recovery strategies:

```zig
const RecoveryStrategy = enum {
    retry,
    fallback,
    abort,
};

fn determineStrategy(err: anyerror) RecoveryStrategy {
    const name = @errorName(err);
    if (std.mem.indexOf(u8, name, "Timeout") != null) {
        return .retry;
    } else if (std.mem.indexOf(u8, name, "NotFound") != null) {
        return .fallback;
    }
    return .abort;
}

fn fetchData(source: u8) !i32 {
    switch (source) {
        0 => return error.Timeout,
        1 => return error.NotFound,
        2 => return error.FatalError,
        else => return 42,
    }
}

fn smartFetch(source: u8, default: i32) !i32 {
    return fetchData(source) catch |err| {
        const strategy = determineStrategy(err);
        std.debug.print("Error: {s}, Strategy: {s}\n", .{ @errorName(err), @tagName(strategy) });

        return switch (strategy) {
            .retry => error.ShouldRetry,
            .fallback => default,
            .abort => error.OperationAborted,
        };
    };
}

test "error recovery with strategy chain" {
    try testing.expectEqual(@as(i32, 42), try smartFetch(99, 0));
    try testing.expectError(error.ShouldRetry, smartFetch(0, 0));
    try testing.expectEqual(@as(i32, -1), try smartFetch(1, -1));
    try testing.expectError(error.OperationAborted, smartFetch(2, 0));
}
```

Strategy-based recovery makes error handling more maintainable and testable.

### Error Stack Tracking

Track the full error propagation path:

```zig
const ErrorStack = struct {
    errors: [10]?anyerror,
    contexts: [10][]const u8,
    count: usize,

    fn init() ErrorStack {
        return .{
            .errors = [_]?anyerror{null} ** 10,
            .contexts = [_][]const u8{""} ** 10,
            .count = 0,
        };
    }

    fn push(self: *ErrorStack, err: anyerror, context: []const u8) void {
        if (self.count < self.errors.len) {
            self.errors[self.count] = err;
            self.contexts[self.count] = context;
            self.count += 1;
        }
    }

    fn getStack(self: *const ErrorStack) []const ?anyerror {
        return self.errors[0..self.count];
    }
};

fn operation1(fail: bool, stack: *ErrorStack) !void {
    if (fail) {
        const err = error.Op1Failed;
        stack.push(err, "Operation 1");
        return err;
    }
}

fn operation2(fail: bool, stack: *ErrorStack) !void {
    operation1(fail, stack) catch {
        const wrapped = error.Op2Failed;
        stack.push(wrapped, "Operation 2 wrapping Op1");
        return wrapped;
    };
}

test "track error stack" {
    var stack = ErrorStack.init();
    operation2(true, &stack) catch {};

    try testing.expectEqual(@as(usize, 2), stack.count);
    try testing.expectEqual(error.Op1Failed, stack.errors[0].?);
    try testing.expectEqual(error.Op2Failed, stack.errors[1].?);
}
```

Error stack tracking provides detailed debugging information showing exactly where and how errors propagated.

### Best Practices

1. **Transform at boundaries**: Convert errors when crossing abstraction layers
2. **Preserve original errors**: Keep original error information for debugging
3. **Add context**: Include meaningful context like operation names and parameters
4. **Use type safety**: Leverage Zig's error sets to enforce error handling
5. **Document transformations**: Explain why errors are transformed
6. **Consider recovery**: Design error transformations to support retry and fallback
7. **Log before transforming**: Record original error before wrapping

### Error Transformation Patterns

**Pattern 1: Simple Mapping**
```zig
lowLevelOp() catch |err| {
    return switch (err) {
        error.FileNotFound => error.ConfigMissing,
        error.AccessDenied => error.Unauthorized,
        else => error.OperationFailed,
    };
};
```

**Pattern 2: Context Preservation**
```zig
lowLevelOp() catch |err| {
    std.debug.print("Failed: {s}\n", .{@errorName(err)});
    return error.HighLevelFailure;
};
```

**Pattern 3: Conditional Transformation**
```zig
lowLevelOp() catch |err| {
    if (isRetryable(err)) return error.ShouldRetry;
    if (isFatal(err)) return error.Abort;
    return err; // Propagate unchanged
};
```

### Common Gotchas

**Losing error information**: Always log or store original errors before transforming:

```zig
// Wrong - original error lost
lowLevelOp() catch {
    return error.Failed;
};

// Right - original error logged
lowLevelOp() catch |err| {
    std.debug.print("Original error: {s}\n", .{@errorName(err)});
    return error.Failed;
};
```

**Over-transforming**: Don't transform errors unnecessarily:

```zig
// Wrong - error transformed at every layer
fn layer1() !void { return error.Failed; }
fn layer2() !void { layer1() catch return error.L2Failed; }
fn layer3() !void { layer2() catch return error.L3Failed; }

// Right - only transform at API boundaries
fn layer1() !void { return error.Failed; }
fn layer2() !void { try layer1(); }  // Propagate unchanged
fn apiFunction() !void { layer2() catch return error.ApiFailed; }
```

**Incorrect error categorization**: Ensure error transformations are accurate:

```zig
// Wrong - timeout is retryable, not permanent
operation() catch |err| switch (err) {
    error.Timeout => error.PermanentFailure,  // Should be retryable
    else => err,
};

// Right - categorize appropriately
operation() catch |err| switch (err) {
    error.Timeout => error.Retryable,
    error.NotFound => error.Permanent,
    else => err,
};
```

### When to Transform Errors

**Transform when:**
- Crossing abstraction boundaries (file errors → config errors)
- Hiding implementation details from users
- Adding domain-specific context
- Supporting retry/fallback logic
- Aggregating multiple error sources

**Don't transform when:**
- Within the same abstraction layer
- Error information would be lost
- Original error is already meaningful
- No value added by transformation

### Integration with Error Recovery

Error transformation enables sophisticated recovery:

```zig
const result = operation() catch |err| {
    const category = categorize(err);

    return switch (category) {
        .transient => {
            std.time.sleep(1000);
            return operation(); // Retry
        },
        .permanent => {
            return fallbackOperation(); // Fallback
        },
        .fatal => {
            std.debug.panic("Unrecoverable: {s}", .{@errorName(err)});
        },
    };
};
```

### Error Transformation and Testing

Test both the transformation logic and error paths:

```zig
test "error transformation" {
    // Test that low-level errors are transformed
    try expectError(error.ConfigError, loadConfig("missing.conf"));

    // Test that context is preserved (via logging)
    // Test that original error can be recovered from metadata
}
```

### Performance Considerations

Error transformation has minimal overhead:
- No memory allocation (errors are `u16` values)
- No runtime cost for error set checks
- Logging and metadata structures may allocate
- Consider using stack-allocated error context structs

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: error_transformation
const LowLevelError = error{
    FileNotFound,
    AccessDenied,
    DiskFull,
};

const HighLevelError = error{
    ConfigurationError,
    InitializationFailed,
    ResourceUnavailable,
};

fn readConfigFile(path: []const u8) LowLevelError![]const u8 {
    if (std.mem.eql(u8, path, "missing.conf")) {
        return error.FileNotFound;
    }
    if (std.mem.eql(u8, path, "protected.conf")) {
        return error.AccessDenied;
    }
    return "config data";
}

fn loadConfiguration(path: []const u8) HighLevelError![]const u8 {
    const config = readConfigFile(path) catch |err| {
        std.debug.print("Failed to read config: {s}\n", .{@errorName(err)});
        return error.ConfigurationError;
    };
    return config;
}

test "transform low-level errors to high-level" {
    try testing.expectError(error.ConfigurationError, loadConfiguration("missing.conf"));
    try testing.expectError(error.ConfigurationError, loadConfiguration("protected.conf"));
    try testing.expectEqualStrings("config data", try loadConfiguration("valid.conf"));
}
// ANCHOR_END: error_transformation

// ANCHOR: error_context_chain
const IoError = error{ ReadFailed, WriteFailed, SeekFailed };
const DatabaseError = error{ QueryFailed, TransactionAborted };

const ErrorChain = struct {
    original: anyerror,
    context: []const u8,
    layer: u8,

    fn fromIoError(err: IoError, context: []const u8) DatabaseError {
        std.debug.print("IO Error ({s}) -> Database Error: {s}\n", .{ @errorName(err), context });
        return error.QueryFailed;
    }

    fn fromDbError(err: DatabaseError, context: []const u8) IoError {
        std.debug.print("DB Error ({s}) -> IO Error: {s}\n", .{ @errorName(err), context });
        return error.WriteFailed;
    }
};

fn lowLevelRead(should_fail: bool) IoError!i32 {
    if (should_fail) return error.ReadFailed;
    return 42;
}

fn databaseQuery(should_fail: bool) DatabaseError!i32 {
    const value = lowLevelRead(should_fail) catch |err| {
        return ErrorChain.fromIoError(err, "Database query requires file read");
    };
    return value;
}

test "chain errors with context" {
    try testing.expectEqual(@as(i32, 42), try databaseQuery(false));
    try testing.expectError(error.QueryFailed, databaseQuery(true));
}
// ANCHOR_END: error_context_chain

// ANCHOR: wrapping_errors
const OperationError = error{
    NetworkFailure,
    ParseFailure,
    ValidationFailure,
};

const Result = struct {
    value: ?i32,
    original_error: ?anyerror,
    wrapped_error: ?OperationError,
    message: []const u8,

    fn success(value: i32) Result {
        return .{
            .value = value,
            .original_error = null,
            .wrapped_error = null,
            .message = "Success",
        };
    }

    fn failure(original: anyerror, wrapped: OperationError, message: []const u8) Result {
        return .{
            .value = null,
            .original_error = original,
            .wrapped_error = wrapped,
            .message = message,
        };
    }
};

fn parseValue(input: []const u8) !i32 {
    if (input.len == 0) return error.EmptyInput;
    if (input[0] == 'x') return error.InvalidFormat;
    return 42;
}

fn processInput(input: []const u8) OperationError!Result {
    const value = parseValue(input) catch |err| {
        const wrapped_err = error.ParseFailure;
        const msg = "Failed to parse input value";
        return Result.failure(err, wrapped_err, msg);
    };
    return Result.success(value);
}

test "wrap errors with metadata" {
    const success = try processInput("42");
    try testing.expectEqual(@as(i32, 42), success.value.?);
    try testing.expect(success.wrapped_error == null);

    const failure = try processInput("");
    try testing.expect(failure.value == null);
    try testing.expectEqual(error.ParseFailure, failure.wrapped_error.?);
    try testing.expectEqualStrings("Failed to parse input value", failure.message);
}
// ANCHOR_END: wrapping_errors

// ANCHOR: conditional_wrapping
fn openResource(name: []const u8) !void {
    if (std.mem.eql(u8, name, "locked")) return error.ResourceLocked;
    if (std.mem.eql(u8, name, "missing")) return error.ResourceNotFound;
}

fn acquireResource(name: []const u8, retry: bool) !void {
    openResource(name) catch |err| {
        // Decide whether to wrap based on error type
        if (err == error.ResourceLocked) {
            return if (retry) error.RetryableError else err;
        } else if (err == error.ResourceNotFound) {
            return error.PermanentError;
        } else {
            return err;
        }
    };
}

test "conditionally wrap errors" {
    try acquireResource("available", false);
    try testing.expectError(error.RetryableError, acquireResource("locked", true));
    try testing.expectError(error.ResourceLocked, acquireResource("locked", false));
    try testing.expectError(error.PermanentError, acquireResource("missing", false));
}
// ANCHOR_END: conditional_wrapping

// ANCHOR: error_enrichment
const EnrichedError = struct {
    category: ErrorCategory,
    original: anyerror,
    timestamp: i64,
    context: []const u8,

    fn fromError(err: anyerror, ctx: []const u8) EnrichedError {
        return .{
            .category = categorizeError(err),
            .original = err,
            .timestamp = std.time.milliTimestamp(),
            .context = ctx,
        };
    }
};

const ErrorCategory = enum {
    transient,
    permanent,
    unknown,
};

fn categorizeError(err: anyerror) ErrorCategory {
    const name = @errorName(err);
    if (std.mem.indexOf(u8, name, "Timeout") != null or
        std.mem.indexOf(u8, name, "Busy") != null)
    {
        return .transient;
    } else if (std.mem.indexOf(u8, name, "NotFound") != null or
        std.mem.indexOf(u8, name, "Invalid") != null)
    {
        return .permanent;
    }
    return .unknown;
}

fn performOperation(should_fail: bool) !i32 {
    if (should_fail) return error.Timeout;
    return 100;
}

fn wrappedOperation(should_fail: bool) !i32 {
    return performOperation(should_fail) catch |err| {
        const enriched = EnrichedError.fromError(err, "Operation context");
        std.debug.print("Enriched error: category={s}, error={s}\n", .{
            @tagName(enriched.category),
            @errorName(enriched.original),
        });

        return switch (enriched.category) {
            .transient => error.ShouldRetry,
            .permanent => error.ShouldAbort,
            .unknown => err,
        };
    };
}

test "enrich errors with metadata" {
    try testing.expectEqual(@as(i32, 100), try wrappedOperation(false));
    try testing.expectError(error.ShouldRetry, wrappedOperation(true));
}
// ANCHOR_END: error_enrichment

// ANCHOR: multi_layer_wrapping
const Layer1Error = error{ L1Failed };
const Layer2Error = error{ L2Failed };
const Layer3Error = error{ L3Failed };

fn layer1Operation(fail: bool) Layer1Error!i32 {
    if (fail) return error.L1Failed;
    return 1;
}

fn layer2Operation(fail: bool) Layer2Error!i32 {
    const result = layer1Operation(fail) catch |err| {
        std.debug.print("Layer 2 caught: {s}\n", .{@errorName(err)});
        return error.L2Failed;
    };
    return result * 2;
}

fn layer3Operation(fail: bool) Layer3Error!i32 {
    const result = layer2Operation(fail) catch |err| {
        std.debug.print("Layer 3 caught: {s}\n", .{@errorName(err)});
        return error.L3Failed;
    };
    return result * 3;
}

test "multi-layer error wrapping" {
    try testing.expectEqual(@as(i32, 6), try layer3Operation(false));
    try testing.expectError(error.L3Failed, layer3Operation(true));
}
// ANCHOR_END: multi_layer_wrapping

// ANCHOR: error_recovery_chain
const RecoveryStrategy = enum {
    retry,
    fallback,
    abort,
};

fn determineStrategy(err: anyerror) RecoveryStrategy {
    const name = @errorName(err);
    if (std.mem.indexOf(u8, name, "Timeout") != null) {
        return .retry;
    } else if (std.mem.indexOf(u8, name, "NotFound") != null) {
        return .fallback;
    }
    return .abort;
}

fn fetchData(source: u8) !i32 {
    switch (source) {
        0 => return error.Timeout,
        1 => return error.NotFound,
        2 => return error.FatalError,
        else => return 42,
    }
}

fn smartFetch(source: u8, default: i32) !i32 {
    return fetchData(source) catch |err| {
        const strategy = determineStrategy(err);
        std.debug.print("Error: {s}, Strategy: {s}\n", .{ @errorName(err), @tagName(strategy) });

        return switch (strategy) {
            .retry => error.ShouldRetry,
            .fallback => default,
            .abort => error.OperationAborted,
        };
    };
}

test "error recovery with strategy chain" {
    try testing.expectEqual(@as(i32, 42), try smartFetch(99, 0));
    try testing.expectError(error.ShouldRetry, smartFetch(0, 0));
    try testing.expectEqual(@as(i32, -1), try smartFetch(1, -1));
    try testing.expectError(error.OperationAborted, smartFetch(2, 0));
}
// ANCHOR_END: error_recovery_chain

// ANCHOR: error_stack_tracking
const ErrorStack = struct {
    errors: [10]?anyerror,
    contexts: [10][]const u8,
    count: usize,

    fn init() ErrorStack {
        return .{
            .errors = [_]?anyerror{null} ** 10,
            .contexts = [_][]const u8{""} ** 10,
            .count = 0,
        };
    }

    fn push(self: *ErrorStack, err: anyerror, context: []const u8) void {
        if (self.count < self.errors.len) {
            self.errors[self.count] = err;
            self.contexts[self.count] = context;
            self.count += 1;
        }
    }

    fn getStack(self: *const ErrorStack) []const ?anyerror {
        return self.errors[0..self.count];
    }
};

fn operation1(fail: bool, stack: *ErrorStack) !void {
    if (fail) {
        const err = error.Op1Failed;
        stack.push(err, "Operation 1");
        return err;
    }
}

fn operation2(fail: bool, stack: *ErrorStack) !void {
    operation1(fail, stack) catch {
        const wrapped = error.Op2Failed;
        stack.push(wrapped, "Operation 2 wrapping Op1");
        return wrapped;
    };
}

test "track error stack" {
    var stack = ErrorStack.init();
    operation2(true, &stack) catch {};

    try testing.expectEqual(@as(usize, 2), stack.count);
    try testing.expectEqual(error.Op1Failed, stack.errors[0].?);
    try testing.expectEqual(error.Op2Failed, stack.errors[1].?);
}
// ANCHOR_END: error_stack_tracking
```

### See Also

- Recipe 14.8: Creating custom exception types
- Recipe 14.10: Reraising the last exception
- Recipe 14.6: Handling multiple exceptions at once
- Recipe 1.2: Error Handling Patterns
- Recipe 0.11: Optionals, Errors, and Resource Cleanup

---

## Recipe 14.10: Reraising the last exception {#recipe-14-10}

**Tags:** allocators, error-handling, memory, resource-cleanup, testing, testing-debugging
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_10.zig`

### Problem

You need to propagate an error up the call stack after performing cleanup, logging, or conditional handling. You want to reraise errors without losing information or breaking the error handling chain.

### Solution

Use `try` to automatically reraise errors, or `catch |err|` followed by `return err` to reraise after custom logic:

```zig
fn lowLevelOperation(value: i32) !i32 {
    if (value < 0) return error.InvalidValue;
    if (value == 0) return error.ZeroValue;
    return value * 2;
}

fn middleLayer(value: i32) !i32 {
    // Reraise error without modification
    return try lowLevelOperation(value);
}

fn topLayer(value: i32) !i32 {
    // Reraise error without modification
    return try middleLayer(value);
}

test "basic error reraising with try" {
    try testing.expectError(error.InvalidValue, topLayer(-1));
    try testing.expectError(error.ZeroValue, topLayer(0));
    try testing.expectEqual(@as(i32, 20), try topLayer(10));
}
```

### Discussion

Reraising errors is fundamental to Zig's error handling. The `try` keyword automatically propagates errors, while explicit reraising with `catch` gives you control for logging, cleanup, or conditional handling.

### Conditional Reraising with Logging

Log errors before reraising them:

```zig
fn performOperation(value: i32) !i32 {
    if (value < 0) return error.Negative;
    if (value == 0) return error.Zero;
    if (value > 100) return error.TooLarge;
    return value;
}

fn handleWithLogging(value: i32) !i32 {
    return performOperation(value) catch |err| {
        // Log error but reraise it
        std.debug.print("Error occurred: {s}\n", .{@errorName(err)});
        return err;
    };
}

test "conditionally reraise after logging" {
    try testing.expectError(error.Negative, handleWithLogging(-5));
    try testing.expectError(error.Zero, handleWithLogging(0));
    try testing.expectEqual(@as(i32, 50), try handleWithLogging(50));
}
```

This pattern ensures errors are logged while still being propagated to calling code.

### Reraising with Cleanup

Use `defer` and `errdefer` with error reraising:

```zig
const Resource = struct {
    allocated: bool,

    fn init() Resource {
        return .{ .allocated = true };
    }

    fn deinit(self: *Resource) void {
        self.allocated = false;
    }
};

fn operationWithCleanup(fail: bool) !i32 {
    var resource = Resource.init();
    defer resource.deinit();

    if (fail) return error.OperationFailed;
    return 42;
}

fn wrapperWithCleanup(fail: bool) !i32 {
    // Error is automatically reraised after defer cleanup
    return try operationWithCleanup(fail);
}

test "reraise with cleanup" {
    try testing.expectEqual(@as(i32, 42), try wrapperWithCleanup(false));
    try testing.expectError(error.OperationFailed, wrapperWithCleanup(true));
}
```

When `try` encounters an error, `defer` blocks run before the error is reraised, ensuring proper cleanup.

### Selective Reraising

Reraise some errors while handling others:

```zig
fn mayFail(value: i32) !i32 {
    if (value == 1) return error.Recoverable;
    if (value == 2) return error.Critical;
    if (value == 3) return error.Warning;
    return value;
}

fn selectiveHandler(value: i32) !i32 {
    return mayFail(value) catch |err| {
        // Reraise some errors, handle others
        switch (err) {
            error.Recoverable => {
                std.debug.print("Recovered from error\n", .{});
                return 0; // Handle this one
            },
            error.Warning => {
                std.debug.print("Warning: {s}\n", .{@errorName(err)});
                return 0; // Handle this one too
            },
            error.Critical => {
                std.debug.print("Critical error, reraising\n", .{});
                return err; // Reraise
            },
        }
    };
}

test "selectively reraise errors" {
    try testing.expectEqual(@as(i32, 0), try selectiveHandler(1)); // Handled
    try testing.expectError(error.Critical, selectiveHandler(2)); // Reraised
    try testing.expectEqual(@as(i32, 0), try selectiveHandler(3)); // Handled
    try testing.expectEqual(@as(i32, 99), try selectiveHandler(99)); // Success
}
```

This pattern lets you recover from specific errors while propagating critical ones.

### Reraising with Context

Add context before reraising:

```zig
const OperationContext = struct {
    name: []const u8,
    attempt: usize,

    fn execute(self: *OperationContext, value: i32) !i32 {
        self.attempt += 1;
        if (value < 0) {
            std.debug.print("[{s}] Attempt {d}: Error\n", .{ self.name, self.attempt });
            return error.Failed;
        }
        return value;
    }
};

fn executeWithContext(value: i32) !i32 {
    var ctx = OperationContext{ .name = "MyOperation", .attempt = 0 };

    // Try operation, reraise if it fails
    const result = ctx.execute(value) catch |err| {
        std.debug.print("Reraising error from {s}\n", .{ctx.name});
        return err;
    };

    return result;
}

test "reraise with context tracking" {
    try testing.expectEqual(@as(i32, 42), try executeWithContext(42));
    try testing.expectError(error.Failed, executeWithContext(-1));
}
```

Context tracking helps debug complex error scenarios by recording operation details.

### Error Reraising Chain

Reraise errors through multiple layers:

```zig
fn level1Operation(value: i32) !i32 {
    if (value == 1) return error.L1Error;
    return value;
}

fn level2Operation(value: i32) !i32 {
    // Reraise L1 error
    return level1Operation(value) catch |err| {
        std.debug.print("Level 2 reraising: {s}\n", .{@errorName(err)});
        return err;
    };
}

fn level3Operation(value: i32) !i32 {
    // Reraise from level 2
    return level2Operation(value) catch |err| {
        std.debug.print("Level 3 reraising: {s}\n", .{@errorName(err)});
        return err;
    };
}

test "error reraising chain" {
    try testing.expectEqual(@as(i32, 42), try level3Operation(42));
    try testing.expectError(error.L1Error, level3Operation(1));
}
```

Each layer can log or inspect the error before passing it up.

### Reraising with Errdefer

Combine `errdefer` with error propagation:

```zig
fn allocateAndProcess(allocator: std.mem.Allocator, fail: bool) ![]u8 {
    const buffer = try allocator.alloc(u8, 100);
    errdefer allocator.free(buffer);

    if (fail) {
        // errdefer will run, then error is reraised
        return error.ProcessingFailed;
    }

    return buffer;
}

fn wrapAllocate(allocator: std.mem.Allocator, fail: bool) ![]u8 {
    // Error from allocateAndProcess is automatically reraised
    return try allocateAndProcess(allocator, fail);
}

test "reraise with errdefer cleanup" {
    const buffer = try wrapAllocate(testing.allocator, false);
    defer testing.allocator.free(buffer);

    try testing.expectEqual(@as(usize, 100), buffer.len);
    try testing.expectError(error.ProcessingFailed, wrapAllocate(testing.allocator, true));
}
```

`errdefer` runs cleanup only on error paths, then the error is automatically reraised.

### Reraising or Default

Return a default value for some errors, reraise others:

```zig
fn operationWithDefault(value: i32, default: i32) i32 {
    return performOperation(value) catch |err| {
        // For some errors, reraise; for others, return default
        switch (err) {
            error.Negative, error.Zero => return default,
            error.TooLarge => {
                std.debug.print("Value too large, using default\n", .{});
                return default;
            },
        }
    };
}

test "reraise or return default" {
    try testing.expectEqual(@as(i32, 50), operationWithDefault(50, 0));
    try testing.expectEqual(@as(i32, 0), operationWithDefault(-1, 0));
    try testing.expectEqual(@as(i32, 99), operationWithDefault(0, 99));
}
```

This pattern provides graceful degradation for recoverable errors.

### Transparent Reraising

Reraise errors from multiple operations:

```zig
fn operation1(value: i32) !i32 {
    if (value == 1) return error.Op1Failed;
    return value * 2;
}

fn operation2(value: i32) !i32 {
    if (value == 2) return error.Op2Failed;
    return value * 3;
}

fn compositeOperation(value: i32) !i32 {
    // Transparently reraise errors from both operations
    const result1 = try operation1(value);
    const result2 = try operation2(value);
    return result1 + result2;
}

test "transparently reraise from multiple operations" {
    try testing.expectError(error.Op1Failed, compositeOperation(1));
    try testing.expectError(error.Op2Failed, compositeOperation(2));
    try testing.expectEqual(@as(i32, 25), try compositeOperation(5)); // (5*2) + (5*3) = 25
}
```

Using `try` keeps error handling transparent and composable.

### Tracking Reraise Metrics

Track which errors are reraised vs. handled:

```zig
const ErrorMetrics = struct {
    reraise_count: usize = 0,
    handled_count: usize = 0,

    fn recordReraise(self: *ErrorMetrics, err: anyerror) void {
        self.reraise_count += 1;
        std.debug.print("Reraising #{d}: {s}\n", .{ self.reraise_count, @errorName(err) });
    }

    fn recordHandled(self: *ErrorMetrics, err: anyerror) void {
        self.handled_count += 1;
        std.debug.print("Handled #{d}: {s}\n", .{ self.handled_count, @errorName(err) });
    }
};

fn operationWithMetrics(value: i32, metrics: *ErrorMetrics) !i32 {
    return performOperation(value) catch |err| {
        if (err == error.Negative) {
            metrics.recordHandled(err);
            return 0;
        } else {
            metrics.recordReraise(err);
            return err;
        }
    };
}

test "track reraise metrics" {
    var metrics = ErrorMetrics{};

    _ = try operationWithMetrics(50, &metrics);
    _ = try operationWithMetrics(-1, &metrics);
    _ = operationWithMetrics(0, &metrics) catch {};

    try testing.expectEqual(@as(usize, 1), metrics.reraise_count);
    try testing.expectEqual(@as(usize, 1), metrics.handled_count);
}
```

Metrics help understand error patterns and recovery effectiveness.

### Best Practices

1. **Use `try` when possible**: Simplest and clearest way to reraise
2. **Log before reraising**: Record error context without suppressing the error
3. **Clean up with defer/errdefer**: Ensure resources are freed before reraising
4. **Selective reraising**: Handle recoverable errors, reraise critical ones
5. **Preserve error type**: Don't transform errors unnecessarily when reraising
6. **Document reraising**: Make it clear which functions reraise errors
7. **Test error paths**: Ensure reraised errors propagate correctly

### Reraising Patterns

**Pattern 1: Transparent Propagation**
```zig
fn wrapper() !T {
    return try innerFunction(); // Simple reraise
}
```

**Pattern 2: Log and Reraise**
```zig
fn wrapper() !T {
    return innerFunction() catch |err| {
        log.error("Operation failed: {s}", .{@errorName(err)});
        return err;
    };
}
```

**Pattern 3: Cleanup and Reraise**
```zig
fn wrapper() !T {
    var resource = try acquire();
    defer release(resource);
    return try useResource(resource);
}
```

**Pattern 4: Conditional Reraise**
```zig
fn wrapper() !T {
    return innerFunction() catch |err| {
        if (isRecoverable(err)) return fallback();
        return err; // Reraise non-recoverable
    };
}
```

### Common Gotchas

**Forgetting to reraise**: Always reraise unless you intentionally handle the error:

```zig
// Wrong - error silently swallowed
operation() catch |err| {
    log.error("Failed: {s}", .{@errorName(err)});
    // Missing: return err;
};

// Right - error logged and reraised
operation() catch |err| {
    log.error("Failed: {s}", .{@errorName(err)});
    return err;
};
```

**Transforming when reraising**: Don't change error types unnecessarily:

```zig
// Wrong - loses specific error information
operation() catch |err| {
    return error.GenericFailure;
};

// Right - reraise original error
operation() catch |err| {
    log.error("Error: {s}", .{@errorName(err)});
    return err;
};
```

**Cleanup order issues**: Remember `defer` runs in reverse order:

```zig
// Wrong - may close file before buffer flush
var file = try open();
defer file.close();
var buffer = try allocate();
defer free(buffer);
return try processFile(file, buffer);

// Right - buffer freed first, then file closed
var file = try open();
errdefer file.close();
var buffer = try allocate();
errdefer free(buffer);
const result = try processFile(file, buffer);
defer file.close();
defer free(buffer);
return result;
```

### When to Reraise

**Reraise when:**
- Error cannot be handled at current level
- Need to log or track error before propagating
- Performing cleanup before propagation
- Error is critical and must reach top level
- Implementing middleware or wrapper functions

**Don't reraise when:**
- Error can be fully handled at current level
- You have a valid fallback value
- Error is expected and part of normal flow
- Transforming to a more appropriate error type
- Aggregating errors for batch reporting

### Difference Between `try` and Explicit Reraising

**Using `try`:**
```zig
fn simple() !void {
    try operation(); // Concise, automatic reraise
}
```

**Explicit catch and return:**
```zig
fn explicit() !void {
    operation() catch |err| {
        // Can add logic here
        std.debug.print("Error: {s}\n", .{@errorName(err)});
        return err; // Explicit reraise
    };
}
```

Both achieve the same result, but explicit reraising allows custom logic.

### Testing Reraised Errors

Verify errors propagate correctly:

```zig
test "errors are reraised" {
    try expectError(error.Specific, topLevelFunction());
}

test "cleanup happens before reraise" {
    // Verify resources are freed even when errors are reraised
    var tracker = ResourceTracker.init();
    _ = functionThatReraises() catch {};
    try expect(tracker.allFreed());
}
```

### Performance Considerations

Reraising has minimal overhead:
- No stack unwinding like exceptions
- Errors are just `u16` values
- `try` compiles to a simple branch
- Cleanup with `defer` is zero-cost when successful
- No memory allocation for error propagation

### Integration with Error Recovery

Reraising enables layered error handling:

```zig
fn application() void {
    businessLogic() catch |err| {
        handleApplicationError(err);
        return;
    };
}

fn businessLogic() !void {
    return try dataLayer(); // Reraise to application
}

fn dataLayer() !void {
    return try database(); // Reraise to business logic
}
```

Each layer can inspect errors without breaking the propagation chain.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_reraise
fn lowLevelOperation(value: i32) !i32 {
    if (value < 0) return error.InvalidValue;
    if (value == 0) return error.ZeroValue;
    return value * 2;
}

fn middleLayer(value: i32) !i32 {
    // Reraise error without modification
    return try lowLevelOperation(value);
}

fn topLayer(value: i32) !i32 {
    // Reraise error without modification
    return try middleLayer(value);
}

test "basic error reraising with try" {
    try testing.expectError(error.InvalidValue, topLayer(-1));
    try testing.expectError(error.ZeroValue, topLayer(0));
    try testing.expectEqual(@as(i32, 20), try topLayer(10));
}
// ANCHOR_END: basic_reraise

// ANCHOR: conditional_reraise
fn performOperation(value: i32) !i32 {
    if (value < 0) return error.Negative;
    if (value == 0) return error.Zero;
    if (value > 100) return error.TooLarge;
    return value;
}

fn handleWithLogging(value: i32) !i32 {
    return performOperation(value) catch |err| {
        // Log error but reraise it
        std.debug.print("Error occurred: {s}\n", .{@errorName(err)});
        return err;
    };
}

test "conditionally reraise after logging" {
    try testing.expectError(error.Negative, handleWithLogging(-5));
    try testing.expectError(error.Zero, handleWithLogging(0));
    try testing.expectEqual(@as(i32, 50), try handleWithLogging(50));
}
// ANCHOR_END: conditional_reraise

// ANCHOR: reraise_with_cleanup
const Resource = struct {
    allocated: bool,

    fn init() Resource {
        return .{ .allocated = true };
    }

    fn deinit(self: *Resource) void {
        self.allocated = false;
    }
};

fn operationWithCleanup(fail: bool) !i32 {
    var resource = Resource.init();
    defer resource.deinit();

    if (fail) return error.OperationFailed;
    return 42;
}

fn wrapperWithCleanup(fail: bool) !i32 {
    // Error is automatically reraised after defer cleanup
    return try operationWithCleanup(fail);
}

test "reraise with cleanup" {
    try testing.expectEqual(@as(i32, 42), try wrapperWithCleanup(false));
    try testing.expectError(error.OperationFailed, wrapperWithCleanup(true));
}
// ANCHOR_END: reraise_with_cleanup

// ANCHOR: selective_reraise
fn mayFail(value: i32) !i32 {
    if (value == 1) return error.Recoverable;
    if (value == 2) return error.Critical;
    if (value == 3) return error.Warning;
    return value;
}

fn selectiveHandler(value: i32) !i32 {
    return mayFail(value) catch |err| {
        // Reraise some errors, handle others
        switch (err) {
            error.Recoverable => {
                std.debug.print("Recovered from error\n", .{});
                return 0; // Handle this one
            },
            error.Warning => {
                std.debug.print("Warning: {s}\n", .{@errorName(err)});
                return 0; // Handle this one too
            },
            error.Critical => {
                std.debug.print("Critical error, reraising\n", .{});
                return err; // Reraise
            },
        }
    };
}

test "selectively reraise errors" {
    try testing.expectEqual(@as(i32, 0), try selectiveHandler(1)); // Handled
    try testing.expectError(error.Critical, selectiveHandler(2)); // Reraised
    try testing.expectEqual(@as(i32, 0), try selectiveHandler(3)); // Handled
    try testing.expectEqual(@as(i32, 99), try selectiveHandler(99)); // Success
}
// ANCHOR_END: selective_reraise

// ANCHOR: reraise_with_context
const OperationContext = struct {
    name: []const u8,
    attempt: usize,

    fn execute(self: *OperationContext, value: i32) !i32 {
        self.attempt += 1;
        if (value < 0) {
            std.debug.print("[{s}] Attempt {d}: Error\n", .{ self.name, self.attempt });
            return error.Failed;
        }
        return value;
    }
};

fn executeWithContext(value: i32) !i32 {
    var ctx = OperationContext{ .name = "MyOperation", .attempt = 0 };

    // Try operation, reraise if it fails
    const result = ctx.execute(value) catch |err| {
        std.debug.print("Reraising error from {s}\n", .{ctx.name});
        return err;
    };

    return result;
}

test "reraise with context tracking" {
    try testing.expectEqual(@as(i32, 42), try executeWithContext(42));
    try testing.expectError(error.Failed, executeWithContext(-1));
}
// ANCHOR_END: reraise_with_context

// ANCHOR: reraise_chain
fn level1Operation(value: i32) !i32 {
    if (value == 1) return error.L1Error;
    return value;
}

fn level2Operation(value: i32) !i32 {
    // Reraise L1 error
    return level1Operation(value) catch |err| {
        std.debug.print("Level 2 reraising: {s}\n", .{@errorName(err)});
        return err;
    };
}

fn level3Operation(value: i32) !i32 {
    // Reraise from level 2
    return level2Operation(value) catch |err| {
        std.debug.print("Level 3 reraising: {s}\n", .{@errorName(err)});
        return err;
    };
}

test "error reraising chain" {
    try testing.expectEqual(@as(i32, 42), try level3Operation(42));
    try testing.expectError(error.L1Error, level3Operation(1));
}
// ANCHOR_END: reraise_chain

// ANCHOR: errdefer_reraise
fn allocateAndProcess(allocator: std.mem.Allocator, fail: bool) ![]u8 {
    const buffer = try allocator.alloc(u8, 100);
    errdefer allocator.free(buffer);

    if (fail) {
        // errdefer will run, then error is reraised
        return error.ProcessingFailed;
    }

    return buffer;
}

fn wrapAllocate(allocator: std.mem.Allocator, fail: bool) ![]u8 {
    // Error from allocateAndProcess is automatically reraised
    return try allocateAndProcess(allocator, fail);
}

test "reraise with errdefer cleanup" {
    const buffer = try wrapAllocate(testing.allocator, false);
    defer testing.allocator.free(buffer);

    try testing.expectEqual(@as(usize, 100), buffer.len);
    try testing.expectError(error.ProcessingFailed, wrapAllocate(testing.allocator, true));
}
// ANCHOR_END: errdefer_reraise

// ANCHOR: reraise_or_default
fn operationWithDefault(value: i32, default: i32) i32 {
    return performOperation(value) catch |err| {
        // For some errors, reraise; for others, return default
        switch (err) {
            error.Negative, error.Zero => return default,
            error.TooLarge => {
                std.debug.print("Value too large, using default\n", .{});
                return default;
            },
        }
    };
}

test "reraise or return default" {
    try testing.expectEqual(@as(i32, 50), operationWithDefault(50, 0));
    try testing.expectEqual(@as(i32, 0), operationWithDefault(-1, 0));
    try testing.expectEqual(@as(i32, 99), operationWithDefault(0, 99));
}
// ANCHOR_END: reraise_or_default

// ANCHOR: transparent_reraise
fn operation1(value: i32) !i32 {
    if (value == 1) return error.Op1Failed;
    return value * 2;
}

fn operation2(value: i32) !i32 {
    if (value == 2) return error.Op2Failed;
    return value * 3;
}

fn compositeOperation(value: i32) !i32 {
    // Transparently reraise errors from both operations
    const result1 = try operation1(value);
    const result2 = try operation2(value);
    return result1 + result2;
}

test "transparently reraise from multiple operations" {
    try testing.expectError(error.Op1Failed, compositeOperation(1));
    try testing.expectError(error.Op2Failed, compositeOperation(2));
    try testing.expectEqual(@as(i32, 25), try compositeOperation(5)); // (5*2) + (5*3) = 25
}
// ANCHOR_END: transparent_reraise

// ANCHOR: reraise_with_metric
const ErrorMetrics = struct {
    reraise_count: usize = 0,
    handled_count: usize = 0,

    fn recordReraise(self: *ErrorMetrics, err: anyerror) void {
        self.reraise_count += 1;
        std.debug.print("Reraising #{d}: {s}\n", .{ self.reraise_count, @errorName(err) });
    }

    fn recordHandled(self: *ErrorMetrics, err: anyerror) void {
        self.handled_count += 1;
        std.debug.print("Handled #{d}: {s}\n", .{ self.handled_count, @errorName(err) });
    }
};

fn operationWithMetrics(value: i32, metrics: *ErrorMetrics) !i32 {
    return performOperation(value) catch |err| {
        if (err == error.Negative) {
            metrics.recordHandled(err);
            return 0;
        } else {
            metrics.recordReraise(err);
            return err;
        }
    };
}

test "track reraise metrics" {
    var metrics = ErrorMetrics{};

    _ = try operationWithMetrics(50, &metrics);
    _ = try operationWithMetrics(-1, &metrics);
    _ = operationWithMetrics(0, &metrics) catch {};

    try testing.expectEqual(@as(usize, 1), metrics.reraise_count);
    try testing.expectEqual(@as(usize, 1), metrics.handled_count);
}
// ANCHOR_END: reraise_with_metric
```

### See Also

- Recipe 14.9: Raising an exception in response to another exception
- Recipe 14.8: Creating custom exception types
- Recipe 14.6: Handling multiple exceptions at once
- Recipe 1.2: Error Handling Patterns
- Recipe 0.11: Optionals, Errors, and Resource Cleanup

---

## Recipe 14.11: Issuing warning messages {#recipe-14-11}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, memory, resource-cleanup, testing, testing-debugging
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_11.zig`

### Problem

You need to alert users about potential issues, deprecated features, or suboptimal conditions without failing the program. You want to provide informative warnings that help with debugging and maintenance.

### Solution

Use `std.debug.print` for simple warnings or `std.log` for structured logging:

```zig
fn processValue(value: i32) i32 {
    if (value < 0) {
        std.debug.print("Warning: Negative value {d} will be treated as zero\n", .{value});
        return 0;
    }
    if (value > 100) {
        std.debug.print("Warning: Value {d} exceeds maximum, capping at 100\n", .{value});
        return 100;
    }
    return value;
}

test "basic debug warnings" {
    try testing.expectEqual(@as(i32, 0), processValue(-10));
    try testing.expectEqual(@as(i32, 100), processValue(200));
    try testing.expectEqual(@as(i32, 50), processValue(50));
}
```

### Discussion

Zig doesn't have a built-in warning system like some languages, but provides powerful logging and debug printing capabilities. Warnings help users understand issues without halting execution.

### Structured Logging

Use `std.log` for categorized, scoped warnings:

```zig
const log = std.log.scoped(.cookbook);

fn validateInput(value: i32) i32 {
    if (value < 0) {
        log.warn("Invalid negative value: {d}", .{value});
        return 0;
    }
    if (value > 1000) {
        log.warn("Value {d} exceeds safe limit of 1000", .{value});
        return 1000;
    }
    log.info("Validated value: {d}", .{value});
    return value;
}

test "structured logging warnings" {
    try testing.expectEqual(@as(i32, 0), validateInput(-5));
    try testing.expectEqual(@as(i32, 1000), validateInput(5000));
    try testing.expectEqual(@as(i32, 500), validateInput(500));
}
```

The logging system supports different levels (debug, info, warn, err) and can be filtered at compile time.

### Warnings with Context

Include file, line, and context information:

```zig
const WarningContext = struct {
    file: []const u8,
    line: usize,
    message: []const u8,

    fn warn(self: WarningContext) void {
        std.debug.print("[WARNING] {s}:{d} - {s}\n", .{ self.file, self.line, self.message });
    }
};

fn riskyOperation(value: i32) i32 {
    if (value == 0) {
        const ctx = WarningContext{
            .file = "recipe_14_11.zig",
            .line = 54,
            .message = "Division by zero prevented",
        };
        ctx.warn();
        return 1;
    }
    return @divTrunc(100, value);
}

test "warnings with context" {
    try testing.expectEqual(@as(i32, 1), riskyOperation(0));
    try testing.expectEqual(@as(i32, 10), riskyOperation(10));
}
```

Context-rich warnings make it easier to locate and fix issues.

### Warning Levels

Categorize warnings by severity:

```zig
const WarningLevel = enum {
    info,
    warning,
    critical,

    fn emit(self: WarningLevel, message: []const u8) void {
        const prefix = switch (self) {
            .info => "INFO",
            .warning => "WARNING",
            .critical => "CRITICAL",
        };
        std.debug.print("[{s}] {s}\n", .{ prefix, message });
    }
};

fn checkStatus(status: u8) u8 {
    switch (status) {
        0...50 => WarningLevel.critical.emit("Status critically low"),
        51...80 => WarningLevel.warning.emit("Status below optimal"),
        81...100 => WarningLevel.info.emit("Status normal"),
        else => WarningLevel.critical.emit("Status out of range"),
    }
    return status;
}

test "warning levels" {
    _ = checkStatus(30);
    _ = checkStatus(70);
    _ = checkStatus(90);
    _ = checkStatus(150);
}
```

Different warning levels help prioritize which issues to address first.

### Conditional Warnings

Control warning output based on configuration:

```zig
const Config = struct {
    verbose: bool,
    debug: bool,

    fn warn(self: Config, comptime level: []const u8, comptime fmt: []const u8, args: anytype) void {
        if (std.mem.eql(u8, level, "debug") and !self.debug) return;
        if (!self.verbose and std.mem.eql(u8, level, "info")) return;

        std.debug.print("[{s}] ", .{level});
        std.debug.print(fmt ++ "\n", args);
    }
};

fn processWithConfig(config: Config, value: i32) i32 {
    config.warn("debug", "Processing value: {d}", .{value});

    if (value < 0) {
        config.warn("warning", "Negative value detected: {d}", .{value});
        return 0;
    }

    config.warn("info", "Processing completed successfully", .{});
    return value;
}

test "conditional warnings based on config" {
    const quiet_config = Config{ .verbose = false, .debug = false };
    const verbose_config = Config{ .verbose = true, .debug = true };

    try testing.expectEqual(@as(i32, 0), processWithConfig(quiet_config, -5));
    try testing.expectEqual(@as(i32, 42), processWithConfig(verbose_config, 42));
}
```

Conditional warnings reduce noise in production while providing detail during development.

### Deprecation Warnings

Warn users about deprecated APIs:

```zig
fn oldFunction(value: i32) i32 {
    std.debug.print("WARNING: oldFunction() is deprecated, use newFunction() instead\n", .{});
    return value * 2;
}

fn newFunction(value: i32) i32 {
    return value * 2;
}

test "deprecation warnings" {
    try testing.expectEqual(@as(i32, 20), oldFunction(10));
    try testing.expectEqual(@as(i32, 20), newFunction(10));
}
```

Deprecation warnings help users migrate to new APIs gradually.

### Warning Accumulation

Collect warnings for batch processing:

```zig
const WarningAccumulator = struct {
    warnings: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) WarningAccumulator {
        return .{
            .warnings = std.ArrayList([]const u8){},
            .allocator = allocator,
        };
    }

    fn deinit(self: *WarningAccumulator) void {
        for (self.warnings.items) |warning| {
            self.allocator.free(warning);
        }
        self.warnings.deinit(self.allocator);
    }

    fn add(self: *WarningAccumulator, comptime fmt: []const u8, args: anytype) !void {
        const message = try std.fmt.allocPrint(self.allocator, fmt, args);
        try self.warnings.append(self.allocator, message);
    }

    fn printAll(self: *const WarningAccumulator) void {
        for (self.warnings.items, 0..) |warning, i| {
            std.debug.print("Warning {d}: {s}\n", .{ i + 1, warning });
        }
    }

    fn count(self: *const WarningAccumulator) usize {
        return self.warnings.items.len;
    }
};

fn validateData(data: []const i32, accumulator: *WarningAccumulator) !void {
    for (data, 0..) |value, i| {
        if (value < 0) {
            try accumulator.add("Negative value at index {d}: {d}", .{ i, value });
        }
        if (value > 100) {
            try accumulator.add("Excessive value at index {d}: {d}", .{ i, value });
        }
    }
}

test "accumulate warnings" {
    var accumulator = WarningAccumulator.init(testing.allocator);
    defer accumulator.deinit();

    const data = [_]i32{ 50, -10, 200, 30, -5 };
    try validateData(&data, &accumulator);

    try testing.expectEqual(@as(usize, 3), accumulator.count());
}
```

Accumulation is useful for validation where you want to report all issues at once.

### Warning Callbacks

Use callbacks for custom warning handling:

```zig
const WarningHandler = struct {
    callback: *const fn ([]const u8) void,

    fn emit(self: WarningHandler, message: []const u8) void {
        self.callback(message);
    }
};

fn defaultWarningHandler(message: []const u8) void {
    std.debug.print("[DEFAULT] {s}\n", .{message});
}

fn customWarningHandler(message: []const u8) void {
    std.debug.print("[CUSTOM] WARNING: {s}\n", .{message});
}

fn processWithHandler(value: i32, handler: WarningHandler) i32 {
    if (value < 0) {
        handler.emit("Negative value detected");
        return 0;
    }
    return value;
}

test "warning callbacks" {
    const default_handler = WarningHandler{ .callback = &defaultWarningHandler };
    const custom_handler = WarningHandler{ .callback = &customWarningHandler };

    try testing.expectEqual(@as(i32, 0), processWithHandler(-5, default_handler));
    try testing.expectEqual(@as(i32, 0), processWithHandler(-10, custom_handler));
    try testing.expectEqual(@as(i32, 42), processWithHandler(42, default_handler));
}
```

Callbacks enable integration with logging systems, file output, or network reporting.

### Categorized Warnings

Organize warnings by category:

```zig
const WarningCategory = enum {
    security,
    performance,
    compatibility,
    deprecation,

    fn emit(self: WarningCategory, message: []const u8) void {
        const category_name = @tagName(self);
        std.debug.print("[{s}] {s}\n", .{ category_name, message });
    }
};

fn analyzeCode(code: []const u8) void {
    if (std.mem.indexOf(u8, code, "unsafe") != null) {
        WarningCategory.security.emit("Unsafe operation detected");
    }
    if (std.mem.indexOf(u8, code, "deprecated") != null) {
        WarningCategory.deprecation.emit("Deprecated API usage");
    }
    if (std.mem.indexOf(u8, code, "slow") != null) {
        WarningCategory.performance.emit("Potentially slow operation");
    }
}

test "categorized warnings" {
    analyzeCode("unsafe operation here");
    analyzeCode("using deprecated function");
    analyzeCode("slow algorithm detected");
}
```

Categories help users filter and respond to different warning types.

### Runtime Assertions with Warnings

Issue warnings for assertion violations without crashing:

```zig
fn assertValid(value: i32, min: i32, max: i32) i32 {
    if (value < min) {
        std.debug.print("Assertion: value {d} below minimum {d}\n", .{ value, min });
        return min;
    }
    if (value > max) {
        std.debug.print("Assertion: value {d} above maximum {d}\n", .{ value, max });
        return max;
    }
    return value;
}

test "runtime assertions with warnings" {
    try testing.expectEqual(@as(i32, 0), assertValid(-10, 0, 100));
    try testing.expectEqual(@as(i32, 100), assertValid(200, 0, 100));
    try testing.expectEqual(@as(i32, 50), assertValid(50, 0, 100));
}
```

Soft assertions continue execution while alerting to issues.

### Warning Suppression

Allow selective warning suppression:

```zig
const SuppressedWarnings = std.EnumSet(WarningCategory);

fn processWithSuppression(code: []const u8, suppressed: SuppressedWarnings) void {
    if (std.mem.indexOf(u8, code, "unsafe") != null) {
        if (!suppressed.contains(.security)) {
            WarningCategory.security.emit("Unsafe operation");
        }
    }
    if (std.mem.indexOf(u8, code, "deprecated") != null) {
        if (!suppressed.contains(.deprecation)) {
            WarningCategory.deprecation.emit("Deprecated usage");
        }
    }
}

test "warning suppression" {
    var suppressed = SuppressedWarnings.initEmpty();
    suppressed.insert(.security);

    processWithSuppression("unsafe code", suppressed); // No warning
    processWithSuppression("deprecated code", suppressed); // Warning emitted
}
```

Suppression is useful when certain warnings are expected and acceptable.

### Best Practices

1. **Be specific**: Include relevant context in warning messages
2. **Use appropriate levels**: Match severity to impact (info < warn < err)
3. **Make actionable**: Suggest how to fix the issue
4. **Don't spam**: Warn once per condition, not repeatedly
5. **Log strategically**: Use structured logging for production code
6. **Provide context**: Include file, line, and operation details
7. **Allow suppression**: Let users disable expected warnings

### Warning Patterns

**Pattern 1: Validation Warning**
```zig
if (value < min or value > max) {
    std.log.warn("Value {d} out of range [{d}, {d}]", .{ value, min, max });
    return clamp(value, min, max);
}
```

**Pattern 2: Deprecation Notice**
```zig
fn deprecatedFunction() void {
    std.log.warn("deprecatedFunction() is deprecated, use newFunction()", .{});
    // ... old implementation
}
```

**Pattern 3: Performance Warning**
```zig
if (array.len > 10000) {
    std.log.warn("Large array ({d} elements) may impact performance", .{array.len});
}
```

**Pattern 4: Configuration Warning**
```zig
if (config.cache_size < recommended_minimum) {
    std.log.warn("Cache size {d} below recommended {d}", .{
        config.cache_size,
        recommended_minimum,
    });
}
```

### Common Gotchas

**Warning spam**: Don't emit the same warning repeatedly:

```zig
// Wrong - warns on every iteration
for (items) |item| {
    if (item.deprecated) {
        std.log.warn("Deprecated item", .{});
    }
}

// Right - warn once
var warned = false;
for (items) |item| {
    if (item.deprecated and !warned) {
        std.log.warn("{d} deprecated items found", .{count_deprecated(items)});
        warned = true;
    }
}
```

**Insufficient context**: Provide enough information to act:

```zig
// Wrong - what value? where?
std.log.warn("Invalid value", .{});

// Right - specific and actionable
std.log.warn("Invalid temperature {d}C at sensor {s}: must be 0-100C", .{
    temp,
    sensor_id,
});
```

**Wrong log level**: Match severity appropriately:

```zig
// Wrong - this isn't an error, it's a warning
std.log.err("Cache miss", .{});

// Right - cache misses are expected, info level
std.log.info("Cache miss for key: {s}", .{key});
```

### Compile-Time Warnings

For compile-time issues, use `@compileError` or `@compileLog`:

```zig
fn validateConfig(comptime config: Config) void {
    if (config.size < 10) {
        @compileError("Config size must be at least 10");
    }
}
```

Note: Zig doesn't have `@compileWarn`, use `@compileLog` for non-fatal messages.

### Integration with Logging Systems

Integrate with structured logging:

```zig
pub const std_options = struct {
    pub const log_level = .warn;
    pub const log_scope_levels = &[_]std.log.ScopeLevel{
        .{ .scope = .cookbook, .level = .debug },
    };
};
```

This configuration controls which warnings appear.

### Warning Output Formatting

Format warnings for clarity:

```zig
const fmt_warning =
    \\Warning: {s}
    \\  Location: {s}:{d}
    \\  Suggestion: {s}
;

std.debug.print(fmt_warning, .{
    "Deprecated usage",
    file,
    line,
    "Use newApi() instead",
});
```

### Testing Warning Output

Test that warnings are emitted:

```zig
test "deprecated function warns" {
    // In practice, you'd capture output or use a test logger
    deprecatedFunction(); // Should emit warning
}
```

For production code, consider injectable loggers that can be mocked in tests.

### Performance Considerations

Warnings have minimal overhead:
- `std.debug.print` writes directly to stderr
- `std.log` can be compile-time filtered
- Log levels below the threshold compile to nothing
- No allocations for simple formatted output

However, be cautious with:
- Warnings in hot loops
- Complex string formatting in warnings
- Accumulating warnings that allocate memory

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_debug_warning
fn processValue(value: i32) i32 {
    if (value < 0) {
        std.debug.print("Warning: Negative value {d} will be treated as zero\n", .{value});
        return 0;
    }
    if (value > 100) {
        std.debug.print("Warning: Value {d} exceeds maximum, capping at 100\n", .{value});
        return 100;
    }
    return value;
}

test "basic debug warnings" {
    try testing.expectEqual(@as(i32, 0), processValue(-10));
    try testing.expectEqual(@as(i32, 100), processValue(200));
    try testing.expectEqual(@as(i32, 50), processValue(50));
}
// ANCHOR_END: basic_debug_warning

// ANCHOR: structured_logging
const log = std.log.scoped(.cookbook);

fn validateInput(value: i32) i32 {
    if (value < 0) {
        log.warn("Invalid negative value: {d}", .{value});
        return 0;
    }
    if (value > 1000) {
        log.warn("Value {d} exceeds safe limit of 1000", .{value});
        return 1000;
    }
    log.info("Validated value: {d}", .{value});
    return value;
}

test "structured logging warnings" {
    try testing.expectEqual(@as(i32, 0), validateInput(-5));
    try testing.expectEqual(@as(i32, 1000), validateInput(5000));
    try testing.expectEqual(@as(i32, 500), validateInput(500));
}
// ANCHOR_END: structured_logging

// ANCHOR: warning_with_context
const WarningContext = struct {
    file: []const u8,
    line: usize,
    message: []const u8,

    fn warn(self: WarningContext) void {
        std.debug.print("[WARNING] {s}:{d} - {s}\n", .{ self.file, self.line, self.message });
    }
};

fn riskyOperation(value: i32) i32 {
    if (value == 0) {
        const ctx = WarningContext{
            .file = "recipe_14_11.zig",
            .line = 54,
            .message = "Division by zero prevented",
        };
        ctx.warn();
        return 1;
    }
    return @divTrunc(100, value);
}

test "warnings with context" {
    try testing.expectEqual(@as(i32, 1), riskyOperation(0));
    try testing.expectEqual(@as(i32, 10), riskyOperation(10));
}
// ANCHOR_END: warning_with_context

// ANCHOR: warning_levels
const WarningLevel = enum {
    info,
    warning,
    critical,

    fn emit(self: WarningLevel, message: []const u8) void {
        const prefix = switch (self) {
            .info => "INFO",
            .warning => "WARNING",
            .critical => "CRITICAL",
        };
        std.debug.print("[{s}] {s}\n", .{ prefix, message });
    }
};

fn checkStatus(status: u8) u8 {
    switch (status) {
        0...50 => WarningLevel.critical.emit("Status critically low"),
        51...80 => WarningLevel.warning.emit("Status below optimal"),
        81...100 => WarningLevel.info.emit("Status normal"),
        else => WarningLevel.critical.emit("Status out of range"),
    }
    return status;
}

test "warning levels" {
    _ = checkStatus(30);
    _ = checkStatus(70);
    _ = checkStatus(90);
    _ = checkStatus(150);
}
// ANCHOR_END: warning_levels

// ANCHOR: conditional_warnings
const Config = struct {
    verbose: bool,
    debug: bool,

    fn warn(self: Config, comptime level: []const u8, comptime fmt: []const u8, args: anytype) void {
        if (std.mem.eql(u8, level, "debug") and !self.debug) return;
        if (!self.verbose and std.mem.eql(u8, level, "info")) return;

        std.debug.print("[{s}] ", .{level});
        std.debug.print(fmt ++ "\n", args);
    }
};

fn processWithConfig(config: Config, value: i32) i32 {
    config.warn("debug", "Processing value: {d}", .{value});

    if (value < 0) {
        config.warn("warning", "Negative value detected: {d}", .{value});
        return 0;
    }

    config.warn("info", "Processing completed successfully", .{});
    return value;
}

test "conditional warnings based on config" {
    const quiet_config = Config{ .verbose = false, .debug = false };
    const verbose_config = Config{ .verbose = true, .debug = true };

    try testing.expectEqual(@as(i32, 0), processWithConfig(quiet_config, -5));
    try testing.expectEqual(@as(i32, 42), processWithConfig(verbose_config, 42));
}
// ANCHOR_END: conditional_warnings

// ANCHOR: deprecation_warnings
fn oldFunction(value: i32) i32 {
    std.debug.print("WARNING: oldFunction() is deprecated, use newFunction() instead\n", .{});
    return value * 2;
}

fn newFunction(value: i32) i32 {
    return value * 2;
}

test "deprecation warnings" {
    try testing.expectEqual(@as(i32, 20), oldFunction(10));
    try testing.expectEqual(@as(i32, 20), newFunction(10));
}
// ANCHOR_END: deprecation_warnings

// ANCHOR: warning_accumulator
const WarningAccumulator = struct {
    warnings: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator) WarningAccumulator {
        return .{
            .warnings = std.ArrayList([]const u8){},
            .allocator = allocator,
        };
    }

    fn deinit(self: *WarningAccumulator) void {
        for (self.warnings.items) |warning| {
            self.allocator.free(warning);
        }
        self.warnings.deinit(self.allocator);
    }

    fn add(self: *WarningAccumulator, comptime fmt: []const u8, args: anytype) !void {
        const message = try std.fmt.allocPrint(self.allocator, fmt, args);
        try self.warnings.append(self.allocator, message);
    }

    fn printAll(self: *const WarningAccumulator) void {
        for (self.warnings.items, 0..) |warning, i| {
            std.debug.print("Warning {d}: {s}\n", .{ i + 1, warning });
        }
    }

    fn count(self: *const WarningAccumulator) usize {
        return self.warnings.items.len;
    }
};

fn validateData(data: []const i32, accumulator: *WarningAccumulator) !void {
    for (data, 0..) |value, i| {
        if (value < 0) {
            try accumulator.add("Negative value at index {d}: {d}", .{ i, value });
        }
        if (value > 100) {
            try accumulator.add("Excessive value at index {d}: {d}", .{ i, value });
        }
    }
}

test "accumulate warnings" {
    var accumulator = WarningAccumulator.init(testing.allocator);
    defer accumulator.deinit();

    const data = [_]i32{ 50, -10, 200, 30, -5 };
    try validateData(&data, &accumulator);

    try testing.expectEqual(@as(usize, 3), accumulator.count());
}
// ANCHOR_END: warning_accumulator

// ANCHOR: warning_callback
const WarningHandler = struct {
    callback: *const fn ([]const u8) void,

    fn emit(self: WarningHandler, message: []const u8) void {
        self.callback(message);
    }
};

fn defaultWarningHandler(message: []const u8) void {
    std.debug.print("[DEFAULT] {s}\n", .{message});
}

fn customWarningHandler(message: []const u8) void {
    std.debug.print("[CUSTOM] WARNING: {s}\n", .{message});
}

fn processWithHandler(value: i32, handler: WarningHandler) i32 {
    if (value < 0) {
        handler.emit("Negative value detected");
        return 0;
    }
    return value;
}

test "warning callbacks" {
    const default_handler = WarningHandler{ .callback = &defaultWarningHandler };
    const custom_handler = WarningHandler{ .callback = &customWarningHandler };

    try testing.expectEqual(@as(i32, 0), processWithHandler(-5, default_handler));
    try testing.expectEqual(@as(i32, 0), processWithHandler(-10, custom_handler));
    try testing.expectEqual(@as(i32, 42), processWithHandler(42, default_handler));
}
// ANCHOR_END: warning_callback

// ANCHOR: warning_categories
const WarningCategory = enum {
    security,
    performance,
    compatibility,
    deprecation,

    fn emit(self: WarningCategory, message: []const u8) void {
        const category_name = @tagName(self);
        std.debug.print("[{s}] {s}\n", .{ category_name, message });
    }
};

fn analyzeCode(code: []const u8) void {
    if (std.mem.indexOf(u8, code, "unsafe") != null) {
        WarningCategory.security.emit("Unsafe operation detected");
    }
    if (std.mem.indexOf(u8, code, "deprecated") != null) {
        WarningCategory.deprecation.emit("Deprecated API usage");
    }
    if (std.mem.indexOf(u8, code, "slow") != null) {
        WarningCategory.performance.emit("Potentially slow operation");
    }
}

test "categorized warnings" {
    analyzeCode("unsafe operation here");
    analyzeCode("using deprecated function");
    analyzeCode("slow algorithm detected");
}
// ANCHOR_END: warning_categories

// ANCHOR: runtime_assertions
fn assertValid(value: i32, min: i32, max: i32) i32 {
    if (value < min) {
        std.debug.print("Assertion: value {d} below minimum {d}\n", .{ value, min });
        return min;
    }
    if (value > max) {
        std.debug.print("Assertion: value {d} above maximum {d}\n", .{ value, max });
        return max;
    }
    return value;
}

test "runtime assertions with warnings" {
    try testing.expectEqual(@as(i32, 0), assertValid(-10, 0, 100));
    try testing.expectEqual(@as(i32, 100), assertValid(200, 0, 100));
    try testing.expectEqual(@as(i32, 50), assertValid(50, 0, 100));
}
// ANCHOR_END: runtime_assertions

// ANCHOR: warning_suppression
const SuppressedWarnings = std.EnumSet(WarningCategory);

fn processWithSuppression(code: []const u8, suppressed: SuppressedWarnings) void {
    if (std.mem.indexOf(u8, code, "unsafe") != null) {
        if (!suppressed.contains(.security)) {
            WarningCategory.security.emit("Unsafe operation");
        }
    }
    if (std.mem.indexOf(u8, code, "deprecated") != null) {
        if (!suppressed.contains(.deprecation)) {
            WarningCategory.deprecation.emit("Deprecated usage");
        }
    }
}

test "warning suppression" {
    var suppressed = SuppressedWarnings.initEmpty();
    suppressed.insert(.security);

    processWithSuppression("unsafe code", suppressed); // No warning
    processWithSuppression("deprecated code", suppressed); // Warning emitted
}
// ANCHOR_END: warning_suppression
```

### See Also

- Recipe 14.12: Debugging basic program crashes
- Recipe 0.13: Testing and Debugging Fundamentals
- Recipe 13.10: Adding logging to simple scripts
- Recipe 13.11: Adding logging to a library

---

## Recipe 14.12: Debugging basic program crashes {#recipe-14-12}

**Tags:** allocators, c-interop, comptime, concurrency, error-handling, memory, pointers, resource-cleanup, testing, testing-debugging, threading
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_12.zig`

### Problem

You need to diagnose and fix program crashes, null pointer dereferences, buffer overflows, and other common bugs. You want tools and techniques to identify the root cause of crashes quickly.

### Solution

Use Zig's built-in debugging features like stack traces, assertions, and safe unwrapping:

```zig
fn faultyFunction() void {
    // In debug mode, this provides a stack trace
    std.debug.print("Function called\n", .{});
}

fn intermediateFunction() void {
    faultyFunction();
}

fn topLevelFunction() void {
    intermediateFunction();
}

test "stack trace basics" {
    topLevelFunction();
}
```

### Discussion

Zig provides excellent debugging tools at both compile-time and runtime. Debug builds include stack traces, bounds checking, and assertions that help catch bugs early.

### Panic with Informative Messages

Use `std.debug.panic` to halt execution with context:

```zig
fn validateInput(value: i32) void {
    if (value < 0) {
        std.debug.panic("Invalid input: value {d} must be non-negative", .{value});
    }
    std.debug.print("Valid input: {d}\n", .{value});
}

test "panic with message" {
    // This test demonstrates panic (commented out to allow test suite to pass)
    // validateInput(-1);  // Would panic with stack trace
    validateInput(42); // Safe call
}
```

Panics include stack traces in debug mode, making it easy to trace the call chain.

### Debug Assertions

Add runtime checks that only run in debug mode:

```zig
fn processValue(value: i32) i32 {
    std.debug.assert(value >= 0); // Only active in Debug mode
    std.debug.assert(value <= 100);
    return value * 2;
}

test "debug assertions" {
    // Assertions are active in test builds
    try testing.expectEqual(@as(i32, 20), processValue(10));
    // processValue(-1);  // Would trigger assertion in debug mode
}
```

Assertions are zero-cost in release builds but catch bugs during development.

### Safe Optional Unwrapping

Prevent null pointer crashes with safe unwrapping:

```zig
fn safeUnwrap(optional: ?i32) !i32 {
    if (optional) |value| {
        return value;
    } else {
        std.debug.print("Attempted to unwrap null value\n", .{});
        return error.NullValue;
    }
}

test "safe optional unwrapping" {
    try testing.expectEqual(@as(i32, 42), try safeUnwrap(42));
    try testing.expectError(error.NullValue, safeUnwrap(null));
}
```

Using `if` or `orelse` for optionals is safer than `.?` which panics on null.

### Bounds Checking

Manually check array bounds to prevent crashes:

```zig
fn safeArrayAccess(array: []const i32, index: usize) !i32 {
    if (index >= array.len) {
        std.debug.print("Index {d} out of bounds (len: {d})\n", .{ index, array.len });
        return error.OutOfBounds;
    }
    return array[index];
}

test "bounds checking" {
    const array = [_]i32{ 1, 2, 3, 4, 5 };
    try testing.expectEqual(@as(i32, 3), try safeArrayAccess(&array, 2));
    try testing.expectError(error.OutOfBounds, safeArrayAccess(&array, 10));
}
```

Zig automatically checks bounds in debug/safe modes, but explicit checks provide better error messages.

### Null Pointer Checks

Safely handle potentially null pointers:

```zig
fn processPointer(ptr: ?*i32) !i32 {
    const value = ptr orelse {
        std.debug.print("Null pointer detected\n", .{});
        return error.NullPointer;
    };
    return value.*;
}

test "null pointer checks" {
    var value: i32 = 42;
    try testing.expectEqual(@as(i32, 42), try processPointer(&value));
    try testing.expectError(error.NullPointer, processPointer(null));
}
```

The `orelse` pattern converts null pointers into errors instead of crashes.

### Overflow Detection

Detect arithmetic overflow before it causes bugs:

```zig
fn safeAdd(a: i32, b: i32) !i32 {
    const result = @addWithOverflow(a, b);
    if (result[1] != 0) {
        std.debug.print("Overflow detected: {d} + {d}\n", .{ a, b });
        return error.Overflow;
    }
    return result[0];
}

test "overflow detection" {
    try testing.expectEqual(@as(i32, 100), try safeAdd(50, 50));
    try testing.expectError(error.Overflow, safeAdd(std.math.maxInt(i32), 1));
}
```

`@addWithOverflow` returns a tuple `{result, overflow_flag}` for safe arithmetic.

### Debug Print Inspection

Add debug printing to track program state:

```zig
const Point = struct {
    x: i32,
    y: i32,

    fn debug(self: Point) void {
        std.debug.print("Point{{ x: {d}, y: {d} }}\n", .{ self.x, self.y });
    }

    fn debugWithContext(self: Point, context: []const u8) void {
        std.debug.print("[{s}] Point{{ x: {d}, y: {d} }}\n", .{ context, self.x, self.y });
    }
};

fn processPoint(point: Point) Point {
    point.debug();
    const result = Point{ .x = point.x * 2, .y = point.y * 2 };
    result.debugWithContext("After doubling");
    return result;
}

test "debug print inspection" {
    const p = Point{ .x = 10, .y = 20 };
    const result = processPoint(p);
    try testing.expectEqual(@as(i32, 20), result.x);
    try testing.expectEqual(@as(i32, 40), result.y);
}
```

Debug methods help visualize data structures during execution.

### Error Trace Debugging

Track errors through the call stack:

```zig
fn level1() !void {
    return error.Level1Failed;
}

fn level2() !void {
    try level1();
}

fn level3() !void {
    level2() catch |err| {
        std.debug.print("Error caught at level3: {s}\n", .{@errorName(err)});
        std.debug.print("Stack trace available in debug mode\n", .{});
        return err;
    };
}

test "error trace" {
    try testing.expectError(error.Level1Failed, level3());
}
```

Error return traces show the path errors take through your program.

### Memory Debugging

Use testing allocator to catch memory leaks:

```zig
fn allocateAndFree(allocator: std.mem.Allocator) !void {
    std.debug.print("Allocating memory...\n", .{});
    const buffer = try allocator.alloc(u8, 100);
    defer {
        std.debug.print("Freeing memory...\n", .{});
        allocator.free(buffer);
    }

    std.debug.print("Using buffer of size {d}\n", .{buffer.len});
}

test "memory debugging with allocator tracking" {
    try allocateAndFree(testing.allocator);
    // testing.allocator detects leaks automatically
}
```

The testing allocator automatically detects memory leaks and double-frees.

### Conditional Debugging

Enable debug output only in debug builds:

```zig
const debug_enabled = builtin.mode == .Debug;

fn debugLog(comptime fmt: []const u8, args: anytype) void {
    if (debug_enabled) {
        std.debug.print("[DEBUG] " ++ fmt ++ "\n", args);
    }
}

fn computeValue(a: i32, b: i32) i32 {
    debugLog("Computing {d} + {d}", .{ a, b });
    const result = a + b;
    debugLog("Result: {d}", .{result});
    return result;
}

test "conditional debugging" {
    const result = computeValue(10, 20);
    try testing.expectEqual(@as(i32, 30), result);
}
```

Conditional debug code compiles to nothing in release builds.

### Crash Report Pattern

Generate detailed crash reports:

```zig
const CrashInfo = struct {
    message: []const u8,
    location: []const u8,
    value: ?i32,

    fn report(self: CrashInfo) void {
        std.debug.print("=== CRASH REPORT ===\n", .{});
        std.debug.print("Message: {s}\n", .{self.message});
        std.debug.print("Location: {s}\n", .{self.location});
        if (self.value) |v| {
            std.debug.print("Value: {d}\n", .{v});
        }
        std.debug.print("==================\n", .{});
    }
};

fn riskyOperation(value: i32) !i32 {
    if (value < 0) {
        const info = CrashInfo{
            .message = "Negative value not allowed",
            .location = "riskyOperation",
            .value = value,
        };
        info.report();
        return error.InvalidValue;
    }
    return value * 2;
}

test "crash handler pattern" {
    try testing.expectError(error.InvalidValue, riskyOperation(-5));
    try testing.expectEqual(@as(i32, 20), try riskyOperation(10));
}
```

Structured crash reports include context for easier debugging.

### Debugging with Intermediate Values

Print intermediate steps in complex computations:

```zig
fn complexFunction(a: i32, b: i32, c: i32) !i32 {
    std.debug.print("Input: a={d}, b={d}, c={d}\n", .{ a, b, c });

    if (a == 0) {
        std.debug.print("Error: a cannot be zero\n", .{});
        return error.DivisionByZero;
    }

    const step1 = @divTrunc(b, a);
    std.debug.print("Step 1: {d} / {d} = {d}\n", .{ b, a, step1 });

    const step2 = step1 + c;
    std.debug.print("Step 2: {d} + {d} = {d}\n", .{ step1, c, step2 });

    return step2;
}

test "debug with intermediate values" {
    try testing.expectEqual(@as(i32, 7), try complexFunction(2, 10, 2));
    try testing.expectError(error.DivisionByZero, complexFunction(0, 10, 2));
}
```

Step-by-step output helps identify where calculations go wrong.

### Handling Unreachable Code

Use exhaustive switches to eliminate unreachable code:

```zig
fn switchWithUnreachable(value: u8) u8 {
    switch (value) {
        0...10 => return value * 2,
        11...20 => return value * 3,
        21...255 => return value * 4,
    }
}

test "unreachable code paths" {
    try testing.expectEqual(@as(u8, 10), switchWithUnreachable(5));
    try testing.expectEqual(@as(u8, 45), switchWithUnreachable(15));
    try testing.expectEqual(@as(u8, 100), switchWithUnreachable(25));
}
```

Zig's compiler ensures all cases are handled, preventing unexpected crashes.

### Best Practices

1. **Use debug builds**: Always develop with `-Doptimize=Debug`
2. **Enable safety checks**: Use `-Doptimize=ReleaseSafe` for production
3. **Test with allocators**: Use `testing.allocator` to catch leaks
4. **Add assertions**: Use `std.debug.assert` liberally during development
5. **Safe unwrapping**: Prefer `orelse` and `if` over `.?`
6. **Print strategically**: Add debug output at key decision points
7. **Check return values**: Always handle errors, never ignore them

### Debugging Workflow

**Step 1: Reproduce**
```zig
test "reproduce the crash" {
    // Minimal test case that triggers the crash
    try problematicFunction();
}
```

**Step 2: Add Debug Output**
```zig
fn problematicFunction() !void {
    std.debug.print("Entering function\n", .{});
    const value = try getValue();
    std.debug.print("Got value: {d}\n", .{value});
    // ...
}
```

**Step 3: Identify Root Cause**
```zig
// Add assertions to catch invalid state
std.debug.assert(value >= 0);
std.debug.assert(pointer != null);
```

**Step 4: Fix and Verify**
```zig
test "verify fix" {
    // Ensure the crash no longer occurs
    try problematicFunction();
}
```

### Common Crash Patterns

**Pattern 1: Null Pointer Dereference**
```zig
// Wrong - crashes if null
const value = ptr.?.*;

// Right - safe handling
const value = if (ptr) |p| p.* else return error.NullPointer;
```

**Pattern 2: Out of Bounds Access**
```zig
// Wrong - crashes on invalid index
const item = array[index];

// Right - bounds checked
const item = if (index < array.len) array[index] else return error.OutOfBounds;
```

**Pattern 3: Integer Overflow**
```zig
// Wrong - silent overflow in release mode
const result = a + b;

// Right - explicit overflow checking
const overflow = @addWithOverflow(a, b);
if (overflow[1] != 0) return error.Overflow;
const result = overflow[0];
```

**Pattern 4: Use After Free**
```zig
// Wrong - dangling pointer
allocator.free(buffer);
return buffer[0]; // Crash!

// Right - use before free
const value = buffer[0];
allocator.free(buffer);
return value;
```

### Build Modes and Debugging

**Debug Mode** (`-Doptimize=Debug`):
- Full stack traces
- Runtime bounds checking
- Assertions enabled
- No optimizations
- Best for development

**ReleaseSafe** (`-Doptimize=ReleaseSafe`):
- Optimizations enabled
- Runtime safety checks preserved
- Assertions enabled
- Good for production with safety priority

**ReleaseFast** (`-Doptimize=ReleaseFast`):
- Maximum performance
- No safety checks
- Assertions disabled
- Use only when safety is verified

### Debugging Tools

**Built-in Tools:**
- `std.debug.print` - Console output
- `std.debug.panic` - Immediate halt with stack trace
- `std.debug.assert` - Development-time checks
- `@breakpoint()` - Debugger breakpoint
- Error return traces - Automatic error tracking

**External Tools:**
- `gdb` or `lldb` - Interactive debuggers
- `valgrind` - Memory error detection (Linux)
- Address Sanitizer - Memory safety (via `-fsanitize=address`)

### Stack Trace Analysis

When you get a crash, read the stack trace from bottom to top:

```
thread 12345 panic: index out of bounds
/path/to/project/src/main.zig:42:13: 0x1234 in processArray (main)
    return array[index];
            ^
/path/to/project/src/main.zig:100:5: 0x5678 in main (main)
    processArray(data, 999);
    ^
```

This shows:
1. Root cause: index out of bounds at line 42
2. Called from: main at line 100 with index 999

### Memory Leak Detection

```zig
test "detect memory leaks" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            std.debug.print("Memory leak detected!\n", .{});
        }
    }

    const allocator = gpa.allocator();
    // Your code here - leaks will be detected
}
```

### Integration with IDEs

Most IDEs support Zig debugging:
- VSCode: Zig Language extension + CodeLLDB
- CLion: Native Zig support
- Neovim/Vim: DAP integration

Set breakpoints and inspect variables interactively.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;
const builtin = @import("builtin");

// ANCHOR: stack_trace_basics
fn faultyFunction() void {
    // In debug mode, this provides a stack trace
    std.debug.print("Function called\n", .{});
}

fn intermediateFunction() void {
    faultyFunction();
}

fn topLevelFunction() void {
    intermediateFunction();
}

test "stack trace basics" {
    topLevelFunction();
}
// ANCHOR_END: stack_trace_basics

// ANCHOR: panic_with_message
fn validateInput(value: i32) void {
    if (value < 0) {
        std.debug.panic("Invalid input: value {d} must be non-negative", .{value});
    }
    std.debug.print("Valid input: {d}\n", .{value});
}

test "panic with message" {
    // This test demonstrates panic (commented out to allow test suite to pass)
    // validateInput(-1);  // Would panic with stack trace
    validateInput(42); // Safe call
}
// ANCHOR_END: panic_with_message

// ANCHOR: debug_assertions
fn processValue(value: i32) i32 {
    std.debug.assert(value >= 0); // Only active in Debug mode
    std.debug.assert(value <= 100);
    return value * 2;
}

test "debug assertions" {
    // Assertions are active in test builds
    try testing.expectEqual(@as(i32, 20), processValue(10));
    // processValue(-1);  // Would trigger assertion in debug mode
}
// ANCHOR_END: debug_assertions

// ANCHOR: safe_unwrapping
fn safeUnwrap(optional: ?i32) !i32 {
    if (optional) |value| {
        return value;
    } else {
        std.debug.print("Attempted to unwrap null value\n", .{});
        return error.NullValue;
    }
}

test "safe optional unwrapping" {
    try testing.expectEqual(@as(i32, 42), try safeUnwrap(42));
    try testing.expectError(error.NullValue, safeUnwrap(null));
}
// ANCHOR_END: safe_unwrapping

// ANCHOR: bounds_checking
fn safeArrayAccess(array: []const i32, index: usize) !i32 {
    if (index >= array.len) {
        std.debug.print("Index {d} out of bounds (len: {d})\n", .{ index, array.len });
        return error.OutOfBounds;
    }
    return array[index];
}

test "bounds checking" {
    const array = [_]i32{ 1, 2, 3, 4, 5 };
    try testing.expectEqual(@as(i32, 3), try safeArrayAccess(&array, 2));
    try testing.expectError(error.OutOfBounds, safeArrayAccess(&array, 10));
}
// ANCHOR_END: bounds_checking

// ANCHOR: null_checks
fn processPointer(ptr: ?*i32) !i32 {
    const value = ptr orelse {
        std.debug.print("Null pointer detected\n", .{});
        return error.NullPointer;
    };
    return value.*;
}

test "null pointer checks" {
    var value: i32 = 42;
    try testing.expectEqual(@as(i32, 42), try processPointer(&value));
    try testing.expectError(error.NullPointer, processPointer(null));
}
// ANCHOR_END: null_checks

// ANCHOR: overflow_detection
fn safeAdd(a: i32, b: i32) !i32 {
    const result = @addWithOverflow(a, b);
    if (result[1] != 0) {
        std.debug.print("Overflow detected: {d} + {d}\n", .{ a, b });
        return error.Overflow;
    }
    return result[0];
}

test "overflow detection" {
    try testing.expectEqual(@as(i32, 100), try safeAdd(50, 50));
    try testing.expectError(error.Overflow, safeAdd(std.math.maxInt(i32), 1));
}
// ANCHOR_END: overflow_detection

// ANCHOR: debug_print_inspection
const Point = struct {
    x: i32,
    y: i32,

    fn debug(self: Point) void {
        std.debug.print("Point{{ x: {d}, y: {d} }}\n", .{ self.x, self.y });
    }

    fn debugWithContext(self: Point, context: []const u8) void {
        std.debug.print("[{s}] Point{{ x: {d}, y: {d} }}\n", .{ context, self.x, self.y });
    }
};

fn processPoint(point: Point) Point {
    point.debug();
    const result = Point{ .x = point.x * 2, .y = point.y * 2 };
    result.debugWithContext("After doubling");
    return result;
}

test "debug print inspection" {
    const p = Point{ .x = 10, .y = 20 };
    const result = processPoint(p);
    try testing.expectEqual(@as(i32, 20), result.x);
    try testing.expectEqual(@as(i32, 40), result.y);
}
// ANCHOR_END: debug_print_inspection

// ANCHOR: error_trace
fn level1() !void {
    return error.Level1Failed;
}

fn level2() !void {
    try level1();
}

fn level3() !void {
    level2() catch |err| {
        std.debug.print("Error caught at level3: {s}\n", .{@errorName(err)});
        std.debug.print("Stack trace available in debug mode\n", .{});
        return err;
    };
}

test "error trace" {
    try testing.expectError(error.Level1Failed, level3());
}
// ANCHOR_END: error_trace

// ANCHOR: memory_debugging
fn allocateAndFree(allocator: std.mem.Allocator) !void {
    std.debug.print("Allocating memory...\n", .{});
    const buffer = try allocator.alloc(u8, 100);
    defer {
        std.debug.print("Freeing memory...\n", .{});
        allocator.free(buffer);
    }

    std.debug.print("Using buffer of size {d}\n", .{buffer.len});
}

test "memory debugging with allocator tracking" {
    try allocateAndFree(testing.allocator);
    // testing.allocator detects leaks automatically
}
// ANCHOR_END: memory_debugging

// ANCHOR: conditional_debugging
const debug_enabled = builtin.mode == .Debug;

fn debugLog(comptime fmt: []const u8, args: anytype) void {
    if (debug_enabled) {
        std.debug.print("[DEBUG] " ++ fmt ++ "\n", args);
    }
}

fn computeValue(a: i32, b: i32) i32 {
    debugLog("Computing {d} + {d}", .{ a, b });
    const result = a + b;
    debugLog("Result: {d}", .{result});
    return result;
}

test "conditional debugging" {
    const result = computeValue(10, 20);
    try testing.expectEqual(@as(i32, 30), result);
}
// ANCHOR_END: conditional_debugging

// ANCHOR: crash_handler
const CrashInfo = struct {
    message: []const u8,
    location: []const u8,
    value: ?i32,

    fn report(self: CrashInfo) void {
        std.debug.print("=== CRASH REPORT ===\n", .{});
        std.debug.print("Message: {s}\n", .{self.message});
        std.debug.print("Location: {s}\n", .{self.location});
        if (self.value) |v| {
            std.debug.print("Value: {d}\n", .{v});
        }
        std.debug.print("==================\n", .{});
    }
};

fn riskyOperation(value: i32) !i32 {
    if (value < 0) {
        const info = CrashInfo{
            .message = "Negative value not allowed",
            .location = "riskyOperation",
            .value = value,
        };
        info.report();
        return error.InvalidValue;
    }
    return value * 2;
}

test "crash handler pattern" {
    try testing.expectError(error.InvalidValue, riskyOperation(-5));
    try testing.expectEqual(@as(i32, 20), try riskyOperation(10));
}
// ANCHOR_END: crash_handler

// ANCHOR: debug_symbols
fn complexFunction(a: i32, b: i32, c: i32) !i32 {
    std.debug.print("Input: a={d}, b={d}, c={d}\n", .{ a, b, c });

    if (a == 0) {
        std.debug.print("Error: a cannot be zero\n", .{});
        return error.DivisionByZero;
    }

    const step1 = @divTrunc(b, a);
    std.debug.print("Step 1: {d} / {d} = {d}\n", .{ b, a, step1 });

    const step2 = step1 + c;
    std.debug.print("Step 2: {d} + {d} = {d}\n", .{ step1, c, step2 });

    return step2;
}

test "debug with intermediate values" {
    try testing.expectEqual(@as(i32, 7), try complexFunction(2, 10, 2));
    try testing.expectError(error.DivisionByZero, complexFunction(0, 10, 2));
}
// ANCHOR_END: debug_symbols

// ANCHOR: unreachable_code
fn switchWithUnreachable(value: u8) u8 {
    switch (value) {
        0...10 => return value * 2,
        11...20 => return value * 3,
        21...255 => return value * 4,
    }
}

test "unreachable code paths" {
    try testing.expectEqual(@as(u8, 10), switchWithUnreachable(5));
    try testing.expectEqual(@as(u8, 45), switchWithUnreachable(15));
    try testing.expectEqual(@as(u8, 100), switchWithUnreachable(25));
}
// ANCHOR_END: unreachable_code
```

### See Also

- Recipe 14.11: Issuing warning messages
- Recipe 14.13: Profiling and timing your program
- Recipe 0.13: Testing and Debugging Fundamentals
- Recipe 1.3: Testing Strategy

---

## Recipe 14.13: Profiling and timing your program {#recipe-14-13}

**Tags:** allocators, c-interop, comptime, concurrency, memory, resource-cleanup, testing, testing-debugging, threading
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_13.zig`

### Problem

You need to measure your program's performance, identify bottlenecks, and optimize slow code. You want to benchmark functions, track memory allocations, and measure throughput.

### Solution

Use `std.time.nanoTimestamp()` for high-resolution timing:

```zig
fn measureFunction() !void {
    const start = std.time.nanoTimestamp();

    // Simulate work
    std.Thread.sleep(1 * std.time.ns_per_ms);

    const end = std.time.nanoTimestamp();
    const elapsed = end - start;

    std.debug.print("Function took {d} nanoseconds ({d:.2} ms)\n", .{
        elapsed,
        @as(f64, @floatFromInt(elapsed)) / std.time.ns_per_ms,
    });
}

test "basic timing measurement" {
    try measureFunction();
}
```

### Discussion

Zig provides precise timing primitives for performance measurement. Profiling helps you understand where your program spends time and identify optimization opportunities.

### Timer Utility

Create a reusable timer for consistent measurements:

```zig
const Timer = struct {
    start_time: i128,
    name: []const u8,

    fn start(name: []const u8) Timer {
        return .{
            .start_time = std.time.nanoTimestamp(),
            .name = name,
        };
    }

    fn stop(self: *const Timer) i128 {
        const elapsed = std.time.nanoTimestamp() - self.start_time;
        std.debug.print("[{s}] Elapsed: {d} ns ({d:.2} ms)\n", .{
            self.name,
            elapsed,
            @as(f64, @floatFromInt(elapsed)) / std.time.ns_per_ms,
        });
        return elapsed;
    }

    fn lap(self: *Timer, label: []const u8) i128 {
        const elapsed = std.time.nanoTimestamp() - self.start_time;
        std.debug.print("[{s}] {s}: {d} ns\n", .{ self.name, label, elapsed });
        self.start_time = std.time.nanoTimestamp(); // Reset for next lap
        return elapsed;
    }
};

test "timer utility" {
    var timer = Timer.start("MyOperation");
    std.Thread.sleep(2 * std.time.ns_per_ms);
    _ = timer.stop();
}
```

Timers make it easy to measure multiple operations consistently.

### Benchmark Algorithm Comparison

Compare different implementations:

```zig
fn algorithmA(n: usize) usize {
    var sum: usize = 0;
    for (0..n) |i| {
        sum += i;
    }
    return sum;
}

fn algorithmB(n: usize) usize {
    return (n * (n - 1)) / 2;
}

fn benchmarkAlgorithms(n: usize) !void {
    const start_a = std.time.nanoTimestamp();
    const result_a = algorithmA(n);
    const time_a = std.time.nanoTimestamp() - start_a;

    const start_b = std.time.nanoTimestamp();
    const result_b = algorithmB(n);
    const time_b = std.time.nanoTimestamp() - start_b;

    std.debug.print("Algorithm A: {d} ns, result: {d}\n", .{ time_a, result_a });
    std.debug.print("Algorithm B: {d} ns, result: {d}\n", .{ time_b, result_b });
    std.debug.print("Speedup: {d:.2}x\n", .{@as(f64, @floatFromInt(time_a)) / @as(f64, @floatFromInt(time_b))});
}

test "benchmark algorithm comparison" {
    try benchmarkAlgorithms(100000);
}
```

Direct comparison reveals which algorithm performs better.

### Profiling Code Sections

Measure individual sections to find bottlenecks:

```zig
fn complexOperation() !void {
    var timer = Timer.start("ComplexOp");

    // Section 1
    std.Thread.sleep(1 * std.time.ns_per_ms);
    _ = timer.lap("Section 1: Setup");

    // Section 2
    std.Thread.sleep(3 * std.time.ns_per_ms);
    _ = timer.lap("Section 2: Processing");

    // Section 3
    std.Thread.sleep(1 * std.time.ns_per_ms);
    _ = timer.lap("Section 3: Cleanup");
}

test "profile code sections" {
    try complexOperation();
}
```

Lap timing shows where your function spends most of its time.

### Memory Profiling

Track memory usage patterns:

```zig
const MemoryStats = struct {
    allocations: usize,
    deallocations: usize,
    bytes_allocated: usize,
    bytes_freed: usize,

    fn init() MemoryStats {
        return .{
            .allocations = 0,
            .deallocations = 0,
            .bytes_allocated = 0,
            .bytes_freed = 0,
        };
    }

    fn report(self: MemoryStats) void {
        std.debug.print("Memory Stats:\n", .{});
        std.debug.print("  Allocations: {d}\n", .{self.allocations});
        std.debug.print("  Deallocations: {d}\n", .{self.deallocations});
        std.debug.print("  Bytes allocated: {d}\n", .{self.bytes_allocated});
        std.debug.print("  Bytes freed: {d}\n", .{self.bytes_freed});
        std.debug.print("  Net memory: {d}\n", .{self.bytes_allocated - self.bytes_freed});
    }
};

fn memoryIntensiveOperation(allocator: std.mem.Allocator) !void {
    var stats = MemoryStats.init();

    const buffer1 = try allocator.alloc(u8, 1024);
    stats.allocations += 1;
    stats.bytes_allocated += 1024;

    const buffer2 = try allocator.alloc(u8, 2048);
    stats.allocations += 1;
    stats.bytes_allocated += 2048;

    allocator.free(buffer1);
    stats.deallocations += 1;
    stats.bytes_freed += 1024;

    allocator.free(buffer2);
    stats.deallocations += 1;
    stats.bytes_freed += 2048;

    stats.report();
}

test "memory profiling" {
    try memoryIntensiveOperation(testing.allocator);
}
```

Memory profiling reveals allocation patterns and potential leaks.

### Iteration Benchmarking

Measure per-iteration performance:

```zig
fn benchmarkIterations(iterations: usize) !void {
    var sum: usize = 0;
    const start = std.time.nanoTimestamp();

    for (0..iterations) |i| {
        sum +%= i;
    }

    const elapsed = std.time.nanoTimestamp() - start;
    const per_iter = @as(f64, @floatFromInt(elapsed)) / @as(f64, @floatFromInt(iterations));

    std.debug.print("Iterations: {d}\n", .{iterations});
    std.debug.print("Total time: {d} ns\n", .{elapsed});
    std.debug.print("Per iteration: {d:.2} ns\n", .{per_iter});
    std.debug.print("Throughput: {d:.2} M ops/sec\n", .{
        @as(f64, @floatFromInt(iterations)) / @as(f64, @floatFromInt(elapsed)) * 1000.0,
    });
}

test "benchmark iterations" {
    try benchmarkIterations(1_000_000);
}
```

Per-iteration timing helps assess scalability.

### Warmup and Statistical Benchmarking

Account for warmup effects and get accurate measurements:

```zig
fn runBenchmarkWithWarmup(comptime func: fn () usize, warmup_runs: usize, measured_runs: usize) !void {
    // Warmup phase
    for (0..warmup_runs) |_| {
        _ = func();
    }

    // Measurement phase
    const start = std.time.nanoTimestamp();
    for (0..measured_runs) |_| {
        _ = func();
    }
    const elapsed = std.time.nanoTimestamp() - start;

    const avg = @as(f64, @floatFromInt(elapsed)) / @as(f64, @floatFromInt(measured_runs));
    std.debug.print("Average per run: {d:.2} ns ({d} runs after {d} warmup)\n", .{
        avg,
        measured_runs,
        warmup_runs,
    });
}

fn benchmarkedFunction() usize {
    var sum: usize = 0;
    for (0..1000) |i| {
        sum +%= i * i;
    }
    return sum;
}

test "benchmark with warmup" {
    try runBenchmarkWithWarmup(benchmarkedFunction, 100, 1000);
}
```

Warmup runs eliminate JIT compilation and cache effects.

### Statistical Analysis

Collect multiple samples for reliable results:

```zig
const BenchmarkStats = struct {
    samples: []i128,
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator, capacity: usize) !BenchmarkStats {
        return .{
            .samples = try allocator.alloc(i128, capacity),
            .allocator = allocator,
        };
    }

    fn deinit(self: *BenchmarkStats) void {
        self.allocator.free(self.samples);
    }

    fn addSample(self: *BenchmarkStats, index: usize, value: i128) void {
        self.samples[index] = value;
    }

    fn analyze(self: *const BenchmarkStats) void {
        var min = self.samples[0];
        var max = self.samples[0];
        var sum: i128 = 0;

        for (self.samples) |sample| {
            if (sample < min) min = sample;
            if (sample > max) max = sample;
            sum += sample;
        }

        const avg = @divTrunc(sum, @as(i128, @intCast(self.samples.len)));

        std.debug.print("Benchmark Statistics:\n", .{});
        std.debug.print("  Samples: {d}\n", .{self.samples.len});
        std.debug.print("  Min: {d} ns\n", .{min});
        std.debug.print("  Max: {d} ns\n", .{max});
        std.debug.print("  Avg: {d} ns\n", .{avg});
        std.debug.print("  Range: {d} ns\n", .{max - min});
    }
};

test "statistical benchmarking" {
    const runs = 10;
    var stats = try BenchmarkStats.init(testing.allocator, runs);
    defer stats.deinit();

    for (0..runs) |i| {
        const start = std.time.nanoTimestamp();
        _ = benchmarkedFunction();
        const elapsed = std.time.nanoTimestamp() - start;
        stats.addSample(i, elapsed);
    }

    stats.analyze();
}
```

Statistics reveal measurement variability and outliers.

### Allocation Tracking

Track allocations with a custom allocator:

```zig
const TrackingAllocator = struct {
    parent_allocator: std.mem.Allocator,
    allocation_count: usize,
    deallocation_count: usize,
    bytes_allocated: usize,

    fn init(parent: std.mem.Allocator) TrackingAllocator {
        return .{
            .parent_allocator = parent,
            .allocation_count = 0,
            .deallocation_count = 0,
            .bytes_allocated = 0,
        };
    }

    fn allocator(self: *TrackingAllocator) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .free = free,
                .remap = remap,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        self.allocation_count += 1;
        self.bytes_allocated += len;
        return self.parent_allocator.rawAlloc(len, ptr_align, ret_addr);
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent_allocator.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        self.deallocation_count += 1;
        self.parent_allocator.rawFree(buf, buf_align, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent_allocator.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn report(self: *const TrackingAllocator) void {
        std.debug.print("Allocation Tracking:\n", .{});
        std.debug.print("  Allocations: {d}\n", .{self.allocation_count});
        std.debug.print("  Deallocations: {d}\n", .{self.deallocation_count});
        std.debug.print("  Bytes allocated: {d}\n", .{self.bytes_allocated});
    }
};

test "allocation tracking" {
    var tracking = TrackingAllocator.init(testing.allocator);
    const allocator = tracking.allocator();

    const buffer1 = try allocator.alloc(u8, 100);
    defer allocator.free(buffer1);

    const buffer2 = try allocator.alloc(u8, 200);
    defer allocator.free(buffer2);

    tracking.report();
}
```

Tracking allocators provide detailed memory usage insights.

### Throughput Measurement

Measure data processing rates:

```zig
fn measureThroughput(data_size: usize, iterations: usize) !void {
    var sum: usize = 0;
    const start = std.time.nanoTimestamp();

    for (0..iterations) |_| {
        for (0..data_size) |i| {
            sum +%= i;
        }
    }

    const elapsed = std.time.nanoTimestamp() - start;
    const total_bytes = data_size * iterations * @sizeOf(usize);
    const throughput_mbps = @as(f64, @floatFromInt(total_bytes)) /
                            @as(f64, @floatFromInt(elapsed)) * 1000.0;

    std.debug.print("Throughput: {d:.2} MB/s\n", .{throughput_mbps});
    std.debug.print("Total data: {d} bytes in {d} ns\n", .{ total_bytes, elapsed });
}

test "throughput measurement" {
    try measureThroughput(10000, 100);
}
```

Throughput measurements help assess I/O and processing efficiency.

### Best Practices

1. **Use release builds**: Profile with `-Doptimize=ReleaseFast` for accurate results
2. **Warm up**: Run code multiple times before measuring
3. **Multiple samples**: Take many measurements and analyze statistics
4. **Isolate code**: Benchmark specific functions, not entire programs
5. **Minimize interference**: Close other programs during benchmarking
6. **Measure consistently**: Use the same environment for comparisons
7. **Profile first, optimize second**: Don't optimize without data

### Profiling Workflow

**Step 1: Identify Slow Code**
```zig
var timer = Timer.start("Entire Program");
// ... program code ...
_ = timer.stop();
```

**Step 2: Profile Sections**
```zig
var timer = Timer.start("Operations");
_ = timer.lap("Phase 1");
_ = timer.lap("Phase 2");
_ = timer.lap("Phase 3");
```

**Step 3: Benchmark Alternatives**
```zig
// Compare different implementations
benchmarkFunction(implementationA);
benchmarkFunction(implementationB);
```

**Step 4: Optimize and Verify**
```zig
// After optimization, verify improvement
const before = measureOriginal();
const after = measureOptimized();
std.debug.print("Speedup: {d:.2}x\n", .{before / after});
```

### Timing Patterns

**Pattern 1: Simple Timing**
```zig
const start = std.time.nanoTimestamp();
operation();
const elapsed = std.time.nanoTimestamp() - start;
```

**Pattern 2: Scoped Timing**
```zig
{
    var timer = Timer.start("Operation");
    defer _ = timer.stop();
    operation();
}
```

**Pattern 3: Comparative Benchmarking**
```zig
const times_a = benchmark(funcA, iterations);
const times_b = benchmark(funcB, iterations);
if (times_a < times_b) {
    std.debug.print("A is {d:.2}x faster\n", .{times_b / times_a});
}
```

### Common Gotchas

**Debug vs Release**: Always profile release builds:

```zig
// Wrong - debug builds are much slower
// zig test code.zig

// Right - profile optimized code
// zig test code.zig -Doptimize=ReleaseFast
```

**Cold vs Warm**: Account for warmup:

```zig
// Wrong - includes cold start overhead
const time = measure(func);

// Right - warm up first
for (0..100) |_| func(); // Warmup
const time = measure(func);
```

**Single sample unreliable**: Use statistics:

```zig
// Wrong - one measurement
const time = measure(func);

// Right - multiple samples
var stats = BenchmarkStats.init(100);
for (0..100) |i| {
    stats.addSample(i, measure(func));
}
stats.analyze();
```

### Build Modes and Performance

**Debug** (`-Doptimize=Debug`):
- Slowest execution
- Full safety checks
- Easiest debugging
- Not for profiling

**ReleaseSafe** (`-Doptimize=ReleaseSafe`):
- Fast execution
- Safety checks enabled
- Good for production profiling

**ReleaseFast** (`-Doptimize=ReleaseFast`):
- Fastest execution
- No safety checks
- Best for benchmarking

**ReleaseSmall** (`-Doptimize=ReleaseSmall`):
- Optimized for size
- Useful for embedded systems

### External Profiling Tools

**Linux:**
- `perf` - CPU profiling and hardware counters
- `valgrind --tool=callgrind` - Detailed call graphs
- `flamegraph` - Visualization of profiling data

**macOS:**
- Instruments - Xcode profiling suite
- `dtrace` - System-level tracing

**Cross-platform:**
- `tracy` - Real-time profiler
- `superluminal` - Low-overhead profiler

### Using perf on Linux

```bash
# Compile with debug symbols
zig build-exe -Doptimize=ReleaseFast -Ddebug-symbols=true main.zig

# Profile
perf record ./main

# Analyze
perf report
```

### Memory Profiling Techniques

**Heap Profiling:**
```zig
var gpa = std.heap.GeneralPurposeAllocator(.{
    .enable_memory_limit = true,
}){};
const allocator = gpa.allocator();
// ... use allocator ...
const leaked = gpa.deinit();
```

**Peak Memory Usage:**
```zig
var max_memory: usize = 0;
// Track allocations and update max_memory
```

**Allocation Hot Spots:**
Use a tracking allocator to find where most allocations occur.

### Micro-Benchmarking Pitfalls

**Compiler Optimization**: Prevent dead code elimination:

```zig
// Wrong - may be optimized away
for (0..1000) |_| {
    const result = compute();
    _ = result;
}

// Right - use result to prevent elimination
var sum: usize = 0;
for (0..1000) |_| {
    sum +%= compute();
}
std.mem.doNotOptimizeAway(&sum);
```

**Measurement Overhead**: Account for timer overhead:

```zig
const overhead = measureOverhead();
const measured = measure(func);
const actual = measured - overhead;
```

### Throughput vs Latency

**Latency**: Time for single operation
```zig
const start = std.time.nanoTimestamp();
singleOperation();
const latency = std.time.nanoTimestamp() - start;
```

**Throughput**: Operations per second
```zig
const start = std.time.nanoTimestamp();
for (0..operations) |_| {
    singleOperation();
}
const elapsed = std.time.nanoTimestamp() - start;
const throughput = operations * std.time.ns_per_s / elapsed;
```

### CI/CD Integration

Track performance over time:

```zig
test "performance regression check" {
    const max_allowed_ns = 1000000; // 1ms
    const elapsed = measureCriticalPath();
    try testing.expect(elapsed < max_allowed_ns);
}
```

Fail builds if performance degrades beyond thresholds.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_timing
fn measureFunction() !void {
    const start = std.time.nanoTimestamp();

    // Simulate work
    std.Thread.sleep(1 * std.time.ns_per_ms);

    const end = std.time.nanoTimestamp();
    const elapsed = end - start;

    std.debug.print("Function took {d} nanoseconds ({d:.2} ms)\n", .{
        elapsed,
        @as(f64, @floatFromInt(elapsed)) / std.time.ns_per_ms,
    });
}

test "basic timing measurement" {
    try measureFunction();
}
// ANCHOR_END: basic_timing

// ANCHOR: timer_utility
const Timer = struct {
    start_time: i128,
    name: []const u8,

    fn start(name: []const u8) Timer {
        return .{
            .start_time = std.time.nanoTimestamp(),
            .name = name,
        };
    }

    fn stop(self: *const Timer) i128 {
        const elapsed = std.time.nanoTimestamp() - self.start_time;
        std.debug.print("[{s}] Elapsed: {d} ns ({d:.2} ms)\n", .{
            self.name,
            elapsed,
            @as(f64, @floatFromInt(elapsed)) / std.time.ns_per_ms,
        });
        return elapsed;
    }

    fn lap(self: *Timer, label: []const u8) i128 {
        const elapsed = std.time.nanoTimestamp() - self.start_time;
        std.debug.print("[{s}] {s}: {d} ns\n", .{ self.name, label, elapsed });
        self.start_time = std.time.nanoTimestamp(); // Reset for next lap
        return elapsed;
    }
};

test "timer utility" {
    var timer = Timer.start("MyOperation");
    std.Thread.sleep(2 * std.time.ns_per_ms);
    _ = timer.stop();
}
// ANCHOR_END: timer_utility

// ANCHOR: benchmark_comparison
fn algorithmA(n: usize) usize {
    var sum: usize = 0;
    for (0..n) |i| {
        sum += i;
    }
    return sum;
}

fn algorithmB(n: usize) usize {
    return (n * (n - 1)) / 2;
}

fn benchmarkAlgorithms(n: usize) !void {
    const start_a = std.time.nanoTimestamp();
    const result_a = algorithmA(n);
    const time_a = std.time.nanoTimestamp() - start_a;

    const start_b = std.time.nanoTimestamp();
    const result_b = algorithmB(n);
    const time_b = std.time.nanoTimestamp() - start_b;

    std.debug.print("Algorithm A: {d} ns, result: {d}\n", .{ time_a, result_a });
    std.debug.print("Algorithm B: {d} ns, result: {d}\n", .{ time_b, result_b });
    std.debug.print("Speedup: {d:.2}x\n", .{@as(f64, @floatFromInt(time_a)) / @as(f64, @floatFromInt(time_b))});
}

test "benchmark algorithm comparison" {
    try benchmarkAlgorithms(100000);
}
// ANCHOR_END: benchmark_comparison

// ANCHOR: profiling_sections
fn complexOperation() !void {
    var timer = Timer.start("ComplexOp");

    // Section 1
    std.Thread.sleep(1 * std.time.ns_per_ms);
    _ = timer.lap("Section 1: Setup");

    // Section 2
    std.Thread.sleep(3 * std.time.ns_per_ms);
    _ = timer.lap("Section 2: Processing");

    // Section 3
    std.Thread.sleep(1 * std.time.ns_per_ms);
    _ = timer.lap("Section 3: Cleanup");
}

test "profile code sections" {
    try complexOperation();
}
// ANCHOR_END: profiling_sections

// ANCHOR: memory_profiling
const MemoryStats = struct {
    allocations: usize,
    deallocations: usize,
    bytes_allocated: usize,
    bytes_freed: usize,

    fn init() MemoryStats {
        return .{
            .allocations = 0,
            .deallocations = 0,
            .bytes_allocated = 0,
            .bytes_freed = 0,
        };
    }

    fn report(self: MemoryStats) void {
        std.debug.print("Memory Stats:\n", .{});
        std.debug.print("  Allocations: {d}\n", .{self.allocations});
        std.debug.print("  Deallocations: {d}\n", .{self.deallocations});
        std.debug.print("  Bytes allocated: {d}\n", .{self.bytes_allocated});
        std.debug.print("  Bytes freed: {d}\n", .{self.bytes_freed});
        std.debug.print("  Net memory: {d}\n", .{self.bytes_allocated - self.bytes_freed});
    }
};

fn memoryIntensiveOperation(allocator: std.mem.Allocator) !void {
    var stats = MemoryStats.init();

    const buffer1 = try allocator.alloc(u8, 1024);
    stats.allocations += 1;
    stats.bytes_allocated += 1024;

    const buffer2 = try allocator.alloc(u8, 2048);
    stats.allocations += 1;
    stats.bytes_allocated += 2048;

    allocator.free(buffer1);
    stats.deallocations += 1;
    stats.bytes_freed += 1024;

    allocator.free(buffer2);
    stats.deallocations += 1;
    stats.bytes_freed += 2048;

    stats.report();
}

test "memory profiling" {
    try memoryIntensiveOperation(testing.allocator);
}
// ANCHOR_END: memory_profiling

// ANCHOR: iteration_benchmark
fn benchmarkIterations(iterations: usize) !void {
    var sum: usize = 0;
    const start = std.time.nanoTimestamp();

    for (0..iterations) |i| {
        sum +%= i;
    }

    const elapsed = std.time.nanoTimestamp() - start;
    const per_iter = @as(f64, @floatFromInt(elapsed)) / @as(f64, @floatFromInt(iterations));

    std.debug.print("Iterations: {d}\n", .{iterations});
    std.debug.print("Total time: {d} ns\n", .{elapsed});
    std.debug.print("Per iteration: {d:.2} ns\n", .{per_iter});
    std.debug.print("Throughput: {d:.2} M ops/sec\n", .{
        @as(f64, @floatFromInt(iterations)) / @as(f64, @floatFromInt(elapsed)) * 1000.0,
    });
}

test "benchmark iterations" {
    try benchmarkIterations(1_000_000);
}
// ANCHOR_END: iteration_benchmark

// ANCHOR: warmup_benchmark
fn runBenchmarkWithWarmup(comptime func: fn () usize, warmup_runs: usize, measured_runs: usize) !void {
    // Warmup phase
    for (0..warmup_runs) |_| {
        _ = func();
    }

    // Measurement phase
    const start = std.time.nanoTimestamp();
    for (0..measured_runs) |_| {
        _ = func();
    }
    const elapsed = std.time.nanoTimestamp() - start;

    const avg = @as(f64, @floatFromInt(elapsed)) / @as(f64, @floatFromInt(measured_runs));
    std.debug.print("Average per run: {d:.2} ns ({d} runs after {d} warmup)\n", .{
        avg,
        measured_runs,
        warmup_runs,
    });
}

fn benchmarkedFunction() usize {
    var sum: usize = 0;
    for (0..1000) |i| {
        sum +%= i * i;
    }
    return sum;
}

test "benchmark with warmup" {
    try runBenchmarkWithWarmup(benchmarkedFunction, 100, 1000);
}
// ANCHOR_END: warmup_benchmark

// ANCHOR: statistical_benchmark
const BenchmarkStats = struct {
    samples: []i128,
    allocator: std.mem.Allocator,

    fn init(allocator: std.mem.Allocator, capacity: usize) !BenchmarkStats {
        return .{
            .samples = try allocator.alloc(i128, capacity),
            .allocator = allocator,
        };
    }

    fn deinit(self: *BenchmarkStats) void {
        self.allocator.free(self.samples);
    }

    fn addSample(self: *BenchmarkStats, index: usize, value: i128) void {
        self.samples[index] = value;
    }

    fn analyze(self: *const BenchmarkStats) void {
        var min = self.samples[0];
        var max = self.samples[0];
        var sum: i128 = 0;

        for (self.samples) |sample| {
            if (sample < min) min = sample;
            if (sample > max) max = sample;
            sum += sample;
        }

        const avg = @divTrunc(sum, @as(i128, @intCast(self.samples.len)));

        std.debug.print("Benchmark Statistics:\n", .{});
        std.debug.print("  Samples: {d}\n", .{self.samples.len});
        std.debug.print("  Min: {d} ns\n", .{min});
        std.debug.print("  Max: {d} ns\n", .{max});
        std.debug.print("  Avg: {d} ns\n", .{avg});
        std.debug.print("  Range: {d} ns\n", .{max - min});
    }
};

test "statistical benchmarking" {
    const runs = 10;
    var stats = try BenchmarkStats.init(testing.allocator, runs);
    defer stats.deinit();

    for (0..runs) |i| {
        const start = std.time.nanoTimestamp();
        _ = benchmarkedFunction();
        const elapsed = std.time.nanoTimestamp() - start;
        stats.addSample(i, elapsed);
    }

    stats.analyze();
}
// ANCHOR_END: statistical_benchmark

// ANCHOR: allocation_tracking
const TrackingAllocator = struct {
    parent_allocator: std.mem.Allocator,
    allocation_count: usize,
    deallocation_count: usize,
    bytes_allocated: usize,

    fn init(parent: std.mem.Allocator) TrackingAllocator {
        return .{
            .parent_allocator = parent,
            .allocation_count = 0,
            .deallocation_count = 0,
            .bytes_allocated = 0,
        };
    }

    fn allocator(self: *TrackingAllocator) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .free = free,
                .remap = remap,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        self.allocation_count += 1;
        self.bytes_allocated += len;
        return self.parent_allocator.rawAlloc(len, ptr_align, ret_addr);
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent_allocator.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        self.deallocation_count += 1;
        self.parent_allocator.rawFree(buf, buf_align, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent_allocator.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn report(self: *const TrackingAllocator) void {
        std.debug.print("Allocation Tracking:\n", .{});
        std.debug.print("  Allocations: {d}\n", .{self.allocation_count});
        std.debug.print("  Deallocations: {d}\n", .{self.deallocation_count});
        std.debug.print("  Bytes allocated: {d}\n", .{self.bytes_allocated});
    }
};

test "allocation tracking" {
    var tracking = TrackingAllocator.init(testing.allocator);
    const allocator = tracking.allocator();

    const buffer1 = try allocator.alloc(u8, 100);
    defer allocator.free(buffer1);

    const buffer2 = try allocator.alloc(u8, 200);
    defer allocator.free(buffer2);

    tracking.report();
}
// ANCHOR_END: allocation_tracking

// ANCHOR: throughput_measurement
fn measureThroughput(data_size: usize, iterations: usize) !void {
    var sum: usize = 0;
    const start = std.time.nanoTimestamp();

    for (0..iterations) |_| {
        for (0..data_size) |i| {
            sum +%= i;
        }
    }

    const elapsed = std.time.nanoTimestamp() - start;
    const total_bytes = data_size * iterations * @sizeOf(usize);
    const throughput_mbps = @as(f64, @floatFromInt(total_bytes)) /
                            @as(f64, @floatFromInt(elapsed)) * 1000.0;

    std.debug.print("Throughput: {d:.2} MB/s\n", .{throughput_mbps});
    std.debug.print("Total data: {d} bytes in {d} ns\n", .{ total_bytes, elapsed });
}

test "throughput measurement" {
    try measureThroughput(10000, 100);
}
// ANCHOR_END: throughput_measurement
```

### See Also

- Recipe 14.14: Making your programs run faster
- Recipe 14.12: Debugging basic program crashes
- Recipe 1.5: Build modes and safety
- Recipe 0.13: Testing and Debugging Fundamentals

---

## Recipe 14.14: Making your programs run faster {#recipe-14-14}

**Tags:** allocators, arraylist, comptime, concurrency, data-structures, error-handling, memory, pointers, resource-cleanup, slices, testing, testing-debugging, threading
**Difficulty:** intermediate
**Code:** `code/04-specialized/14-testing-debugging/recipe_14_14.zig`

### Problem

You need to optimize your program's performance. You want to apply proven optimization techniques without sacrificing code clarity or introducing bugs.

### Solution

Profile first, then apply targeted optimizations. Use SIMD vectorization for data-parallel operations:

```zig
fn sumScalar(data: []const f32) f32 {
    var sum: f32 = 0;
    for (data) |value| {
        sum += value;
    }
    return sum;
}

fn sumVectorized(data: []const f32) f32 {
    const Vector = @Vector(4, f32);
    var sum_vec: Vector = @splat(0.0);

    const len_aligned = data.len - (data.len % 4);
    var i: usize = 0;
    while (i < len_aligned) : (i += 4) {
        const vec: Vector = data[i..][0..4].*;
        sum_vec += vec;
    }

    var sum: f32 = @reduce(.Add, sum_vec);
    while (i < data.len) : (i += 1) {
        sum += data[i];
    }

    return sum;
}

test "SIMD vectorization" {
    const data = [_]f32{ 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0 };
    try testing.expectApproxEqAbs(sumScalar(&data), sumVectorized(&data), 0.001);
}
```

### Discussion

Performance optimization requires understanding both your code and the hardware it runs on. Always profile before optimizing to ensure you're improving the actual bottlenecks.

### Cache-Friendly Data Layouts

Structure data for better cache utilization:

```zig
const Point2D = struct {
    x: f32,
    y: f32,
};

// Array of Structs (AoS) - less cache friendly
fn processAoS(points: []Point2D) f32 {
    var sum_x: f32 = 0;
    for (points) |point| {
        sum_x += point.x;
    }
    return sum_x;
}

// Struct of Arrays (SoA) - more cache friendly
const Points2D_SoA = struct {
    x: []f32,
    y: []f32,
};

fn processSoA(points: Points2D_SoA) f32 {
    var sum_x: f32 = 0;
    for (points.x) |x| {
        sum_x += x;
    }
    return sum_x;
}

test "cache-friendly data layout" {
    var aos = [_]Point2D{
        .{ .x = 1.0, .y = 2.0 },
        .{ .x = 3.0, .y = 4.0 },
    };

    var x_data = [_]f32{ 1.0, 3.0 };
    var y_data = [_]f32{ 2.0, 4.0 };
    const soa = Points2D_SoA{ .x = &x_data, .y = &y_data };

    try testing.expectApproxEqAbs(processAoS(&aos), processSoA(soa), 0.001);
}
```

Struct of Arrays (SoA) layout improves cache hit rates when accessing a single field across many elements.

### Loop Unrolling

Reduce loop overhead by processing multiple elements per iteration:

```zig
fn sumLoopNormal(data: []const i32) i64 {
    var sum: i64 = 0;
    for (data) |value| {
        sum += value;
    }
    return sum;
}

fn sumLoopUnrolled(data: []const i32) i64 {
    var sum: i64 = 0;
    const len = data.len;
    var i: usize = 0;

    // Process 4 elements at a time
    while (i + 4 <= len) : (i += 4) {
        sum += data[i];
        sum += data[i + 1];
        sum += data[i + 2];
        sum += data[i + 3];
    }

    // Handle remaining elements
    while (i < len) : (i += 1) {
        sum += data[i];
    }

    return sum;
}

test "loop unrolling" {
    const data = [_]i32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    try testing.expectEqual(sumLoopNormal(&data), sumLoopUnrolled(&data));
}
```

Unrolling trades code size for fewer branch instructions and better instruction pipelining.

### Inline Functions

Eliminate function call overhead for small, frequently-called functions:

```zig
inline fn fastMultiply(a: i32, b: i32) i32 {
    return a * b;
}

fn computeWithInline(data: []const i32) i64 {
    var sum: i64 = 0;
    for (data) |value| {
        sum += fastMultiply(value, 2);
    }
    return sum;
}

test "inline functions" {
    const data = [_]i32{ 1, 2, 3, 4, 5 };
    try testing.expectEqual(@as(i64, 30), computeWithInline(&data));
}
```

The `inline` keyword suggests the compiler expand function calls at the call site.

### Branch Prediction

Write code that's friendly to CPU branch predictors:

```zig
fn branchUnpredictable(data: []const i32) i64 {
    var sum: i64 = 0;
    for (data) |value| {
        if (value > 50) {
            sum += value * 2;
        } else {
            sum += value;
        }
    }
    return sum;
}

fn branchlessPredictable(data: []const i32) i64 {
    var sum: i64 = 0;
    for (data) |value| {
        const multiplier: i32 = if (value > 50) 2 else 1;
        sum += value * multiplier;
    }
    return sum;
}

test "branch prediction" {
    const data = [_]i32{ 10, 20, 60, 70, 30 };
    try testing.expectEqual(branchUnpredictable(&data), branchlessPredictable(&data));
}
```

Predictable branches (same outcome repeatedly) perform better than random branches.

### Memory Pooling

Reduce allocation overhead with object pools:

```zig
const ObjectPool = struct {
    objects: []?Object,
    free_list: std.ArrayList(usize),
    allocator: std.mem.Allocator,

    const Object = struct {
        data: [64]u8,
    };

    fn init(allocator: std.mem.Allocator, capacity: usize) !ObjectPool {
        const objects = try allocator.alloc(?Object, capacity);
        @memset(objects, null);

        var free_list = std.ArrayList(usize){};
        try free_list.ensureTotalCapacity(allocator, capacity);
        for (0..capacity) |i| {
            try free_list.append(allocator, capacity - 1 - i);
        }

        return .{
            .objects = objects,
            .free_list = free_list,
            .allocator = allocator,
        };
    }

    fn deinit(self: *ObjectPool) void {
        self.allocator.free(self.objects);
        self.free_list.deinit(self.allocator);
    }

    fn acquire(self: *ObjectPool) !*Object {
        if (self.free_list.items.len == 0) return error.PoolExhausted;
        const index = self.free_list.items[self.free_list.items.len - 1];
        _ = self.free_list.pop();
        self.objects[index] = Object{ .data = undefined };
        return &self.objects[index].?;
    }

    fn release(self: *ObjectPool, obj: *Object) !void {
        const index = (@intFromPtr(obj) - @intFromPtr(self.objects.ptr)) / @sizeOf(?Object);
        self.objects[index] = null;
        try self.free_list.append(self.allocator, index);
    }
};

test "memory pooling" {
    var pool = try ObjectPool.init(testing.allocator, 10);
    defer pool.deinit();

    const obj1 = try pool.acquire();
    const obj2 = try pool.acquire();

    try pool.release(obj1);
    try pool.release(obj2);
}
```

Pools pre-allocate objects, eliminating per-object allocation costs.

### Reduce Allocations

Reuse buffers instead of repeatedly allocating:

```zig
fn processWithManyAllocations(allocator: std.mem.Allocator, count: usize) !void {
    for (0..count) |i| {
        const buffer = try allocator.alloc(u8, 100);
        defer allocator.free(buffer);
        // Use buffer
        buffer[0] = @intCast(i % 256);
    }
}

fn processWithSingleAllocation(allocator: std.mem.Allocator, count: usize) !void {
    const buffer = try allocator.alloc(u8, 100);
    defer allocator.free(buffer);

    for (0..count) |i| {
        // Reuse buffer
        buffer[0] = @intCast(i % 256);
    }
}

test "reduce allocations" {
    try processWithManyAllocations(testing.allocator, 10);
    try processWithSingleAllocation(testing.allocator, 10);
}
```

Single allocation and reuse is much faster than many small allocations.

### Comptime Optimization

Use compile-time parameters to eliminate runtime branches:

```zig
fn processData(comptime use_fast_path: bool, data: []i32) i64 {
    var sum: i64 = 0;
    if (use_fast_path) {
        // Compiler knows this branch at compile time
        for (data) |value| {
            sum += value;
        }
    } else {
        for (data) |value| {
            sum += value * value;
        }
    }
    return sum;
}

test "comptime optimization" {
    var data = [_]i32{ 1, 2, 3, 4, 5 };
    const fast = processData(true, &data);
    const slow = processData(false, &data);
    try testing.expectEqual(@as(i64, 15), fast);
    try testing.expectEqual(@as(i64, 55), slow);
}
```

Comptime parameters let the compiler optimize away entire code paths.

### Avoid Bounds Checks

Use iterators instead of indexing when possible:

```zig
fn sumWithBoundsChecks(data: []const i32) i64 {
    var sum: i64 = 0;
    for (0..data.len) |i| {
        sum += data[i]; // Bounds checked
    }
    return sum;
}

fn sumNoBoundsChecks(data: []const i32) i64 {
    var sum: i64 = 0;
    for (data) |value| { // Iterator, no bounds check
        sum += value;
    }
    return sum;
}

test "avoid bounds checks" {
    const data = [_]i32{ 1, 2, 3, 4, 5 };
    try testing.expectEqual(sumWithBoundsChecks(&data), sumNoBoundsChecks(&data));
}
```

Iterator-based loops are clearer and avoid redundant bounds checks.

### Efficient String Building

Pre-allocate capacity for string operations:

```zig
fn buildStringNaive(allocator: std.mem.Allocator) ![]u8 {
    var result = std.ArrayList(u8){};
    for (0..100) |i| {
        const str = try std.fmt.allocPrint(allocator, "{d} ", .{i});
        defer allocator.free(str);
        try result.appendSlice(allocator, str);
    }
    return result.toOwnedSlice(allocator);
}

fn buildStringEfficient(allocator: std.mem.Allocator) ![]u8 {
    var result = std.ArrayList(u8){};
    try result.ensureTotalCapacity(allocator, 400); // Pre-allocate

    for (0..100) |i| {
        try result.writer(allocator).print("{d} ", .{i});
    }
    return result.toOwnedSlice(allocator);
}

test "efficient string building" {
    const naive = try buildStringNaive(testing.allocator);
    defer testing.allocator.free(naive);

    const efficient = try buildStringEfficient(testing.allocator);
    defer testing.allocator.free(efficient);

    try testing.expectEqualStrings(naive, efficient);
}
```

Pre-allocation prevents repeated reallocation as the string grows.

### Packed Structs

Reduce memory usage with packed struct layouts:

```zig
const UnpackedFlags = struct {
    flag1: bool,
    flag2: bool,
    flag3: bool,
    flag4: bool,
    // 4 bytes (with padding)
};

const PackedFlags = packed struct {
    flag1: bool,
    flag2: bool,
    flag3: bool,
    flag4: bool,
    // 1 byte
};

test "packed structs" {
    const unpacked = UnpackedFlags{
        .flag1 = true,
        .flag2 = false,
        .flag3 = true,
        .flag4 = false,
    };

    const packed_flags = PackedFlags{
        .flag1 = true,
        .flag2 = false,
        .flag3 = true,
        .flag4 = false,
    };

    try testing.expect(@sizeOf(UnpackedFlags) >= @sizeOf(PackedFlags));
    _ = unpacked;
    _ = packed_flags;
}
```

Packed structs eliminate padding, reducing memory footprint.

### Best Practices

1. **Profile first**: Measure before optimizing
2. **Optimize bottlenecks**: Focus on hot paths (80/20 rule)
3. **Measure improvements**: Verify optimizations actually help
4. **Maintain clarity**: Don't sacrifice readability for marginal gains
5. **Use release builds**: Only optimize release builds
6. **Test thoroughly**: Ensure optimizations don't break correctness
7. **Document trade-offs**: Explain why complex optimizations are needed

### Optimization Workflow

**Step 1: Profile**
```bash
# Build with optimization and profiling symbols
zig build-exe -Doptimize=ReleaseFast -Ddebug-symbols=true main.zig

# Profile with perf (Linux) or Instruments (macOS)
perf record ./main
perf report
```

**Step 2: Identify Hotspots**
Find functions consuming the most CPU time.

**Step 3: Optimize Hot Paths**
Apply optimizations to functions that matter.

**Step 4: Verify Improvement**
Re-profile to confirm the optimization helped.

### Optimization Techniques by Category

**CPU-Bound:**
- SIMD vectorization
- Loop unrolling
- Inline functions
- Comptime specialization
- Better algorithms

**Memory-Bound:**
- Cache-friendly layouts (SoA)
- Memory pooling
- Reduce allocations
- Packed structs
- Alignment optimization

**I/O-Bound:**
- Buffering
- Batch operations
- Async I/O
- Memory-mapped files
- Read-ahead caching

### Common Performance Pitfalls

**Pitfall 1: Premature Optimization**
```zig
// Wrong - optimizing without profiling
fn compute(x: i32) i32 {
    // Complex "optimized" code that may not help
    return x * @as(i32, @intCast(@as(u32, @bitCast(x))));
}

// Right - clear code first
fn compute(x: i32) i32 {
    return x * x;
}
```

**Pitfall 2: Ignoring Algorithms**
```zig
// Wrong - optimizing bad algorithm
fn sortBubble(data: []i32) void {
    // ... bubble sort with SIMD ...
}

// Right - use better algorithm
fn sortQuick(data: []i32) void {
    std.sort.heap(i32, data, {}, std.sort.asc(i32));
}
```

**Pitfall 3: Over-Optimization**
```zig
// Wrong - unreadable for 1% gain
fn process(data: []const u8) u64 {
    // 500 lines of hand-crafted assembly
}

// Right - clear code with good-enough performance
fn process(data: []const u8) u64 {
    // 10 lines of readable Zig
}
```

### SIMD Guidelines

**When to use SIMD:**
- Processing large arrays
- Mathematical computations
- Image/signal processing
- Data transformations

**When not to use SIMD:**
- Small datasets (overhead dominates)
- Branch-heavy code
- Complex control flow
- Portability concerns

### Cache Optimization

**L1 Cache** (~4 cycles):
- Keep hot data small
- Use local variables
- Minimize pointer chasing

**L2 Cache** (~12 cycles):
- Group related data
- Use SoA layouts
- Prefetch when appropriate

**L3 Cache** (~40 cycles):
- Batch operations
- Sequential access patterns
- Minimize cache pollution

### Memory Alignment

Aligned data improves SIMD and cache performance:

```zig
const AlignedData = struct {
    data: [1024]f32 align(64),
};
```

### Compiler Optimizations

Enable different optimization levels:

**-Doptimize=Debug**: No optimization (default)
**-Doptimize=ReleaseSafe**: Optimized with safety checks
**-Doptimize=ReleaseFast**: Maximum speed, minimal safety
**-Doptimize=ReleaseSmall**: Optimized for size

### Platform-Specific Optimizations

**x86_64:**
- SSE/AVX instructions
- Cache line size: 64 bytes
- Strong memory ordering

**ARM:**
- NEON SIMD
- Cache line size: varies (32-128 bytes)
- Weak memory ordering

**RISC-V:**
- Vector extensions
- Explicit prefetching
- Relaxed memory model

### Micro-Optimizations

**Bit manipulation:**
```zig
// Fast power-of-2 check
inline fn isPowerOfTwo(x: u32) bool {
    return x != 0 and (x & (x - 1)) == 0;
}
```

**Multiply by constant:**
```zig
// Compiler optimizes this to shifts/adds
const result = value * 17;
```

**Avoid division:**
```zig
// Wrong - division is slow
const avg = sum / count;

// Right - multiply by reciprocal when possible
const reciprocal = 1.0 / @as(f64, @floatFromInt(count));
const avg = sum * reciprocal;
```

### Algorithmic Complexity

Optimization can't fix bad complexity:

**O(n²) → O(n log n)**: Use better sorting
**O(n) → O(1)**: Use hash tables for lookups
**O(2ⁿ) → O(n²)**: Use dynamic programming

Always choose the right algorithm before micro-optimizing.

### Parallel Processing

Use threading for CPU-bound tasks:

```zig
var threads: [4]std.Thread = undefined;
for (&threads, 0..) |*thread, i| {
    thread.* = try std.Thread.spawn(.{}, worker, .{i});
}
for (&threads) |thread| {
    thread.join();
}
```

### Performance Testing

Prevent regressions with performance tests:

```zig
test "performance regression check" {
    const start = std.time.nanoTimestamp();
    criticalFunction();
    const elapsed = std.time.nanoTimestamp() - start;

    const max_ns = 1_000_000; // 1ms limit
    try testing.expect(elapsed < max_ns);
}
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: simd_optimization
fn sumScalar(data: []const f32) f32 {
    var sum: f32 = 0;
    for (data) |value| {
        sum += value;
    }
    return sum;
}

fn sumVectorized(data: []const f32) f32 {
    const Vector = @Vector(4, f32);
    var sum_vec: Vector = @splat(0.0);

    const len_aligned = data.len - (data.len % 4);
    var i: usize = 0;
    while (i < len_aligned) : (i += 4) {
        const vec: Vector = data[i..][0..4].*;
        sum_vec += vec;
    }

    var sum: f32 = @reduce(.Add, sum_vec);
    while (i < data.len) : (i += 1) {
        sum += data[i];
    }

    return sum;
}

test "SIMD vectorization" {
    const data = [_]f32{ 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0 };
    try testing.expectApproxEqAbs(sumScalar(&data), sumVectorized(&data), 0.001);
}
// ANCHOR_END: simd_optimization

// ANCHOR: cache_friendly
const Point2D = struct {
    x: f32,
    y: f32,
};

// Array of Structs (AoS) - less cache friendly
fn processAoS(points: []Point2D) f32 {
    var sum_x: f32 = 0;
    for (points) |point| {
        sum_x += point.x;
    }
    return sum_x;
}

// Struct of Arrays (SoA) - more cache friendly
const Points2D_SoA = struct {
    x: []f32,
    y: []f32,
};

fn processSoA(points: Points2D_SoA) f32 {
    var sum_x: f32 = 0;
    for (points.x) |x| {
        sum_x += x;
    }
    return sum_x;
}

test "cache-friendly data layout" {
    var aos = [_]Point2D{
        .{ .x = 1.0, .y = 2.0 },
        .{ .x = 3.0, .y = 4.0 },
    };

    var x_data = [_]f32{ 1.0, 3.0 };
    var y_data = [_]f32{ 2.0, 4.0 };
    const soa = Points2D_SoA{ .x = &x_data, .y = &y_data };

    try testing.expectApproxEqAbs(processAoS(&aos), processSoA(soa), 0.001);
}
// ANCHOR_END: cache_friendly

// ANCHOR: loop_unrolling
fn sumLoopNormal(data: []const i32) i64 {
    var sum: i64 = 0;
    for (data) |value| {
        sum += value;
    }
    return sum;
}

fn sumLoopUnrolled(data: []const i32) i64 {
    var sum: i64 = 0;
    const len = data.len;
    var i: usize = 0;

    // Process 4 elements at a time
    while (i + 4 <= len) : (i += 4) {
        sum += data[i];
        sum += data[i + 1];
        sum += data[i + 2];
        sum += data[i + 3];
    }

    // Handle remaining elements
    while (i < len) : (i += 1) {
        sum += data[i];
    }

    return sum;
}

test "loop unrolling" {
    const data = [_]i32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    try testing.expectEqual(sumLoopNormal(&data), sumLoopUnrolled(&data));
}
// ANCHOR_END: loop_unrolling

// ANCHOR: inline_functions
inline fn fastMultiply(a: i32, b: i32) i32 {
    return a * b;
}

fn computeWithInline(data: []const i32) i64 {
    var sum: i64 = 0;
    for (data) |value| {
        sum += fastMultiply(value, 2);
    }
    return sum;
}

test "inline functions" {
    const data = [_]i32{ 1, 2, 3, 4, 5 };
    try testing.expectEqual(@as(i64, 30), computeWithInline(&data));
}
// ANCHOR_END: inline_functions

// ANCHOR: branch_prediction
fn branchUnpredictable(data: []const i32) i64 {
    var sum: i64 = 0;
    for (data) |value| {
        if (value > 50) {
            sum += value * 2;
        } else {
            sum += value;
        }
    }
    return sum;
}

fn branchlessPredictable(data: []const i32) i64 {
    var sum: i64 = 0;
    for (data) |value| {
        const multiplier: i32 = if (value > 50) 2 else 1;
        sum += value * multiplier;
    }
    return sum;
}

test "branch prediction" {
    const data = [_]i32{ 10, 20, 60, 70, 30 };
    try testing.expectEqual(branchUnpredictable(&data), branchlessPredictable(&data));
}
// ANCHOR_END: branch_prediction

// ANCHOR: memory_pooling
const ObjectPool = struct {
    objects: []?Object,
    free_list: std.ArrayList(usize),
    allocator: std.mem.Allocator,

    const Object = struct {
        data: [64]u8,
    };

    fn init(allocator: std.mem.Allocator, capacity: usize) !ObjectPool {
        const objects = try allocator.alloc(?Object, capacity);
        @memset(objects, null);

        var free_list = std.ArrayList(usize){};
        try free_list.ensureTotalCapacity(allocator, capacity);
        for (0..capacity) |i| {
            try free_list.append(allocator, capacity - 1 - i);
        }

        return .{
            .objects = objects,
            .free_list = free_list,
            .allocator = allocator,
        };
    }

    fn deinit(self: *ObjectPool) void {
        self.allocator.free(self.objects);
        self.free_list.deinit(self.allocator);
    }

    fn acquire(self: *ObjectPool) !*Object {
        if (self.free_list.items.len == 0) return error.PoolExhausted;
        const index = self.free_list.items[self.free_list.items.len - 1];
        _ = self.free_list.pop();
        self.objects[index] = Object{ .data = undefined };
        return &self.objects[index].?;
    }

    fn release(self: *ObjectPool, obj: *Object) !void {
        const index = (@intFromPtr(obj) - @intFromPtr(self.objects.ptr)) / @sizeOf(?Object);
        self.objects[index] = null;
        try self.free_list.append(self.allocator, index);
    }
};

test "memory pooling" {
    var pool = try ObjectPool.init(testing.allocator, 10);
    defer pool.deinit();

    const obj1 = try pool.acquire();
    const obj2 = try pool.acquire();

    try pool.release(obj1);
    try pool.release(obj2);
}
// ANCHOR_END: memory_pooling

// ANCHOR: reduce_allocations
fn processWithManyAllocations(allocator: std.mem.Allocator, count: usize) !void {
    for (0..count) |i| {
        const buffer = try allocator.alloc(u8, 100);
        defer allocator.free(buffer);
        // Use buffer
        buffer[0] = @intCast(i % 256);
    }
}

fn processWithSingleAllocation(allocator: std.mem.Allocator, count: usize) !void {
    const buffer = try allocator.alloc(u8, 100);
    defer allocator.free(buffer);

    for (0..count) |i| {
        // Reuse buffer
        buffer[0] = @intCast(i % 256);
    }
}

test "reduce allocations" {
    try processWithManyAllocations(testing.allocator, 10);
    try processWithSingleAllocation(testing.allocator, 10);
}
// ANCHOR_END: reduce_allocations

// ANCHOR: const_parameters
fn processData(comptime use_fast_path: bool, data: []i32) i64 {
    var sum: i64 = 0;
    if (use_fast_path) {
        // Compiler knows this branch at compile time
        for (data) |value| {
            sum += value;
        }
    } else {
        for (data) |value| {
            sum += value * value;
        }
    }
    return sum;
}

test "comptime optimization" {
    var data = [_]i32{ 1, 2, 3, 4, 5 };
    const fast = processData(true, &data);
    const slow = processData(false, &data);
    try testing.expectEqual(@as(i64, 15), fast);
    try testing.expectEqual(@as(i64, 55), slow);
}
// ANCHOR_END: const_parameters

// ANCHOR: avoid_bounds_checks
fn sumWithBoundsChecks(data: []const i32) i64 {
    var sum: i64 = 0;
    for (0..data.len) |i| {
        sum += data[i]; // Bounds checked
    }
    return sum;
}

fn sumNoBoundsChecks(data: []const i32) i64 {
    var sum: i64 = 0;
    for (data) |value| { // Iterator, no bounds check
        sum += value;
    }
    return sum;
}

test "avoid bounds checks" {
    const data = [_]i32{ 1, 2, 3, 4, 5 };
    try testing.expectEqual(sumWithBoundsChecks(&data), sumNoBoundsChecks(&data));
}
// ANCHOR_END: avoid_bounds_checks

// ANCHOR: string_building
fn buildStringNaive(allocator: std.mem.Allocator) ![]u8 {
    var result = std.ArrayList(u8){};
    for (0..100) |i| {
        const str = try std.fmt.allocPrint(allocator, "{d} ", .{i});
        defer allocator.free(str);
        try result.appendSlice(allocator, str);
    }
    return result.toOwnedSlice(allocator);
}

fn buildStringEfficient(allocator: std.mem.Allocator) ![]u8 {
    var result = std.ArrayList(u8){};
    try result.ensureTotalCapacity(allocator, 400); // Pre-allocate

    for (0..100) |i| {
        try result.writer(allocator).print("{d} ", .{i});
    }
    return result.toOwnedSlice(allocator);
}

test "efficient string building" {
    const naive = try buildStringNaive(testing.allocator);
    defer testing.allocator.free(naive);

    const efficient = try buildStringEfficient(testing.allocator);
    defer testing.allocator.free(efficient);

    try testing.expectEqualStrings(naive, efficient);
}
// ANCHOR_END: string_building

// ANCHOR: packed_structs
const UnpackedFlags = struct {
    flag1: bool,
    flag2: bool,
    flag3: bool,
    flag4: bool,
    // 4 bytes (with padding)
};

const PackedFlags = packed struct {
    flag1: bool,
    flag2: bool,
    flag3: bool,
    flag4: bool,
    // 1 byte
};

test "packed structs" {
    const unpacked = UnpackedFlags{
        .flag1 = true,
        .flag2 = false,
        .flag3 = true,
        .flag4 = false,
    };

    const packed_flags = PackedFlags{
        .flag1 = true,
        .flag2 = false,
        .flag3 = true,
        .flag4 = false,
    };

    try testing.expect(@sizeOf(UnpackedFlags) >= @sizeOf(PackedFlags));
    _ = unpacked;
    _ = packed_flags;
}
// ANCHOR_END: packed_structs
```

### See Also

- Recipe 14.13: Profiling and timing your program
- Recipe 14.12: Debugging basic program crashes
- Recipe 1.5: Build modes and safety
- Recipe 12.4: Thread pools for parallel work

---
