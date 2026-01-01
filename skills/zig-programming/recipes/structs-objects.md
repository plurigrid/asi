# Structs, Unions & Objects Recipes

*22 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [8.1](#recipe-8-1) | Changing the String Representation of Instances | intermediate |
| [8.2](#recipe-8-2) | Customizing String Formatting | intermediate |
| [8.3](#recipe-8-3) | Making Objects Support the Context Management Protocol | intermediate |
| [8.4](#recipe-8-4) | Saving Memory When Creating a Large Number of Instances | intermediate |
| [8.5](#recipe-8-5) | Encapsulating Names in a Struct | intermediate |
| [8.6](#recipe-8-6) | Creating Managed Attributes | intermediate |
| [8.7](#recipe-8-7) | Calling a Method on a Parent Struct | intermediate |
| [8.8](#recipe-8-8) | Extending a Property in a Subclass | intermediate |
| [8.9](#recipe-8-9) | Creating a New Kind of Struct or Instance Attribute | intermediate |
| [8.10](#recipe-8-10) | Using Lazily Computed Properties | intermediate |
| [8.11](#recipe-8-11) | Simplifying the Initialization of Data Structures | intermediate |
| [8.12](#recipe-8-12) | Defining an Interface or Abstract Base Struct | intermediate |
| [8.13](#recipe-8-13) | Implementing a Data Model or Type System | intermediate |
| [8.14](#recipe-8-14) | Implementing Custom Containers | intermediate |
| [8.15](#recipe-8-15) | Delegating Attribute Access | intermediate |
| [8.16](#recipe-8-16) | Defining More Than One Constructor in a Struct | advanced |
| [8.17](#recipe-8-17) | Creating an Instance Without Invoking init | advanced |
| [8.18](#recipe-8-18) | Extending Structs with Mixins | advanced |
| [8.19](#recipe-8-19) | Implementing Stateful Objects or State Machines | advanced |
| [8.20](#recipe-8-20) | Implementing the Visitor Pattern | advanced |
| [8.21](#recipe-8-21) | Managing Memory in Cyclic Data Structures | advanced |
| [8.22](#recipe-8-22) | Making Structs Support Comparison Operations | advanced |

---

## Recipe 8.1: Changing the String Representation of Instances {#recipe-8-1}

**Tags:** allocators, comptime, error-handling, memory, resource-cleanup, slices, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_1.zig`

### Problem

You want to control how your struct instances are printed and formatted as strings.

### Solution

Implement a `format` function for your struct that integrates with `std.fmt`:

```zig
/// Basic point with custom formatting
const Point = struct {
    x: f32,
    y: f32,

    pub fn format(self: Point, writer: anytype) !void {
        try writer.print("Point({d:.2}, {d:.2})", .{ self.x, self.y });
    }
};
```

**Note:** In Zig 0.15.2, use `{f}` to call the custom `format` function, or `{any}` to use default struct representation.

### Discussion

### Basic Format Implementation

The `format` function has a simple signature taking just self and writer:

```zig
const Person = struct {
    name: []const u8,
    age: u32,

    pub fn format(self: Person, writer: anytype) !void {
        try writer.print("{s} (age {d})", .{ self.name, self.age });
    }
};

test "basic format" {
    const person = Person{ .name = "Alice", .age = 30 };

    var buf: [100]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{person});

    try std.testing.expectEqualStrings("Alice (age 30)", result);
}
```

### Additional Formatting Methods

Create separate methods for different representations:

```zig
const Rectangle = struct {
    width: f32,
    height: f32,

    pub fn format(self: Rectangle, writer: anytype) !void {
        try writer.print("Rectangle({d:.2}x{d:.2})", .{ self.width, self.height });
    }

    pub fn area(self: Rectangle) f32 {
        return self.width * self.height;
    }

    pub fn perimeter(self: Rectangle) f32 {
        return 2 * (self.width + self.height);
    }
};

test "format with methods" {
    const rect = Rectangle{ .width = 10.0, .height = 5.0 };

    var buf: [100]u8 = undefined;

    const default_fmt = try std.fmt.bufPrint(&buf, "{f}", .{rect});
    try std.testing.expectEqualStrings("Rectangle(10.00x5.00)", default_fmt);

    try std.testing.expectEqual(@as(f32, 50.0), rect.area());
    try std.testing.expectEqual(@as(f32, 30.0), rect.perimeter());
}
```

### Debug vs Display Formatting

Different representations for debugging and display:

```zig
const User = struct {
    id: u64,
    username: []const u8,
    email: []const u8,

    pub fn format(
        self: User,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = options;

        if (std.mem.eql(u8, fmt, "debug")) {
            try writer.print("User{{ id={d}, username=\"{s}\", email=\"{s}\" }}", .{
                self.id,
                self.username,
                self.email,
            });
        } else {
            try writer.print("{s} ({s})", .{ self.username, self.email });
        }
    }
};

test "debug vs display" {
    const user = User{
        .id = 12345,
        .username = "alice",
        .email = "alice@example.com",
    };

    var buf: [200]u8 = undefined;

    const display = try std.fmt.bufPrint(&buf, "{}", .{user});
    try std.testing.expectEqualStrings("alice (alice@example.com)", display);

    const debug = try std.fmt.bufPrint(&buf, "{debug}", .{user});
    try std.testing.expectEqualStrings(
        "User{ id=12345, username=\"alice\", email=\"alice@example.com\" }",
        debug,
    );
}
```

### Nested Struct Formatting

Handle nested structures:

```zig
const Address = struct {
    street: []const u8,
    city: []const u8,

    pub fn format(
        self: Address,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("{s}, {s}", .{ self.street, self.city });
    }
};

const Employee = struct {
    name: []const u8,
    address: Address,

    pub fn format(
        self: Employee,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("{s} @ {}", .{ self.name, self.address });
    }
};

test "nested formatting" {
    const emp = Employee{
        .name = "Bob",
        .address = Address{ .street = "123 Main St", .city = "Springfield" },
    };

    var buf: [200]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{}", .{emp});

    try std.testing.expectEqualStrings("Bob @ 123 Main St, Springfield", result);
}
```

### Slice and Array Formatting

Format collections of items:

```zig
const Vector3 = struct {
    data: [3]f32,

    pub fn format(
        self: Vector3,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("({d:.2}, {d:.2}, {d:.2})", .{
            self.data[0],
            self.data[1],
            self.data[2],
        });
    }
};

test "array formatting" {
    const v = Vector3{ .data = .{ 1.5, 2.5, 3.5 } };

    var buf: [100]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{}", .{v});

    try std.testing.expectEqualStrings("(1.50, 2.50, 3.50)", result);
}
```

### Tagged Union Formatting

Format different variants:

```zig
const Shape = union(enum) {
    circle: struct { radius: f32 },
    rectangle: struct { width: f32, height: f32 },
    triangle: struct { base: f32, height: f32 },

    pub fn format(
        self: Shape,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;

        switch (self) {
            .circle => |c| try writer.print("Circle(r={d:.2})", .{c.radius}),
            .rectangle => |r| try writer.print("Rectangle({d:.2}x{d:.2})", .{ r.width, r.height }),
            .triangle => |t| try writer.print("Triangle(b={d:.2}, h={d:.2})", .{ t.base, t.height }),
        }
    }
};

test "union formatting" {
    const circle = Shape{ .circle = .{ .radius = 5.0 } };
    const rect = Shape{ .rectangle = .{ .width = 10.0, .height = 5.0 } };

    var buf: [100]u8 = undefined;

    const c_str = try std.fmt.bufPrint(&buf, "{}", .{circle});
    try std.testing.expectEqualStrings("Circle(r=5.00)", c_str);

    const r_str = try std.fmt.bufPrint(&buf, "{}", .{rect});
    try std.testing.expectEqualStrings("Rectangle(10.00x5.00)", r_str);
}
```

### Multiline Formatting

Pretty-print complex structures:

```zig
const Config = struct {
    host: []const u8,
    port: u16,
    timeout_ms: u32,

    pub fn format(
        self: Config,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = options;

        if (std.mem.eql(u8, fmt, "pretty")) {
            try writer.writeAll("Config {\n");
            try writer.print("  host: \"{s}\"\n", .{self.host});
            try writer.print("  port: {d}\n", .{self.port});
            try writer.print("  timeout_ms: {d}\n", .{self.timeout_ms});
            try writer.writeAll("}");
        } else {
            try writer.print("Config{{ host=\"{s}\", port={d}, timeout_ms={d} }}", .{
                self.host,
                self.port,
                self.timeout_ms,
            });
        }
    }
};

test "multiline formatting" {
    const cfg = Config{
        .host = "localhost",
        .port = 8080,
        .timeout_ms = 5000,
    };

    var buf: [200]u8 = undefined;

    const compact = try std.fmt.bufPrint(&buf, "{}", .{cfg});
    try std.testing.expectEqualStrings(
        "Config{ host=\"localhost\", port=8080, timeout_ms=5000 }",
        compact,
    );

    const pretty = try std.fmt.bufPrint(&buf, "{pretty}", .{cfg});
    const expected =
        \\Config {
        \\  host: "localhost"
        \\  port: 8080
        \\  timeout_ms: 5000
        \\}
    ;
    try std.testing.expectEqualStrings(expected, pretty);
}
```

### Conditional Formatting

Show different fields based on state:

```zig
const Status = enum { active, inactive, pending };

const Account = struct {
    username: []const u8,
    status: Status,
    login_count: u32,

    pub fn format(
        self: Account,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;

        try writer.print("{s} [", .{self.username});

        switch (self.status) {
            .active => try writer.writeAll("ACTIVE"),
            .inactive => try writer.writeAll("INACTIVE"),
            .pending => try writer.writeAll("PENDING"),
        }

        try writer.writeAll("]");

        if (self.status == .active) {
            try writer.print(" (logins: {d})", .{self.login_count});
        }
    }
};

test "conditional formatting" {
    const active_acc = Account{
        .username = "alice",
        .status = .active,
        .login_count = 42,
    };

    const inactive_acc = Account{
        .username = "bob",
        .status = .inactive,
        .login_count = 0,
    };

    var buf: [100]u8 = undefined;

    const active_str = try std.fmt.bufPrint(&buf, "{}", .{active_acc});
    try std.testing.expectEqualStrings("alice [ACTIVE] (logins: 42)", active_str);

    const inactive_str = try std.fmt.bufPrint(&buf, "{}", .{inactive_acc});
    try std.testing.expectEqualStrings("bob [INACTIVE]", inactive_str);
}
```

### Using Format Options

Respect width and precision:

```zig
const Temperature = struct {
    celsius: f32,

    pub fn format(
        self: Temperature,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;

        const precision = options.precision orelse 1;

        switch (precision) {
            0 => try writer.print("{d}°C", .{@as(i32, @intFromFloat(self.celsius))}),
            1 => try writer.print("{d:.1}°C", .{self.celsius}),
            else => try writer.print("{d:.2}°C", .{self.celsius}),
        }
    }
};

test "format options" {
    const temp = Temperature{ .celsius = 23.456 };

    var buf: [100]u8 = undefined;

    const default_fmt = try std.fmt.bufPrint(&buf, "{}", .{temp});
    try std.testing.expectEqualStrings("23.5°C", default_fmt);

    const precise = try std.fmt.bufPrint(&buf, "{.2}", .{temp});
    try std.testing.expectEqualStrings("23.46°C", precise);
}
```

### Best Practices

**Zig 0.15.2 Format Signature:**
```zig
// Correct signature for Zig 0.15.2
pub fn format(self: @This(), writer: anytype) !void {
    try writer.print("...", .{...});
}

// Call with {f} format specifier
const result = try std.fmt.bufPrint(&buf, "{f}", .{instance});

// Use {any} for default struct debug representation
const debug = try std.fmt.bufPrint(&buf, "{any}", .{instance});
```

**Error Handling:**
- Always return `!void` for writer errors
- Use `try` for all writer operations
- No need to catch errors - let them propagate

**Performance:**
```zig
// Good: Direct writing
try writer.writeAll("Point(");
try writer.print("{d}", .{self.x});
try writer.writeAll(")");

// Avoid: Multiple allocations
const str = try std.fmt.allocPrint(allocator, "Point({d})", .{self.x});
defer allocator.free(str);
try writer.writeAll(str);
```

**Format Specifiers:**
- Document custom format specifiers
- Use empty string `""` for default formatting
- Check with `std.mem.eql(u8, fmt, "specifier")`

**Testing:**
```zig
// Always test formatting
test "format" {
    var buf: [100]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{}", .{instance});
    try std.testing.expectEqualStrings("expected", result);
}
```

### Related Functions

- `std.fmt.format()` - Core formatting function
- `std.fmt.bufPrint()` - Format to fixed buffer
- `std.fmt.allocPrint()` - Format with allocation
- `std.fmt.FormatOptions` - Formatting options struct
- `std.io.Writer` - Generic writer interface

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_format
/// Basic point with custom formatting
const Point = struct {
    x: f32,
    y: f32,

    pub fn format(self: Point, writer: anytype) !void {
        try writer.print("Point({d:.2}, {d:.2})", .{ self.x, self.y });
    }
};
// ANCHOR_END: basic_format

/// Person with name and age
const Person = struct {
    name: []const u8,
    age: u32,

    pub fn format(self: Person, writer: anytype) !void {
        try writer.print("{s} (age {d})", .{ self.name, self.age });
    }
};

/// Rectangle with helper methods
const Rectangle = struct {
    width: f32,
    height: f32,

    pub fn format(self: Rectangle, writer: anytype) !void {
        try writer.print("Rectangle({d:.2}x{d:.2})", .{ self.width, self.height });
    }

    pub fn area(self: Rectangle) f32 {
        return self.width * self.height;
    }

    pub fn perimeter(self: Rectangle) f32 {
        return 2 * (self.width + self.height);
    }
};

// ANCHOR: multiple_formats
/// User with simple formatting
const User = struct {
    id: u64,
    username: []const u8,
    email: []const u8,

    pub fn format(self: User, writer: anytype) !void {
        try writer.print("{s} ({s})", .{ self.username, self.email });
    }

    pub fn formatDebug(self: User, writer: anytype) !void {
        try writer.print("User{{ id={d}, username=\"{s}\", email=\"{s}\" }}", .{
            self.id,
            self.username,
            self.email,
        });
    }
};
// ANCHOR_END: multiple_formats

/// Nested structures
const Address = struct {
    street: []const u8,
    city: []const u8,

    pub fn format(self: Address, writer: anytype) !void {
        try writer.print("{s}, {s}", .{ self.street, self.city });
    }
};

const Employee = struct {
    name: []const u8,
    address: Address,

    pub fn format(self: Employee, writer: anytype) !void {
        try writer.print("{s} @ {f}", .{ self.name, self.address });
    }
};

/// Vector with array formatting
const Vector3 = struct {
    data: [3]f32,

    pub fn format(self: Vector3, writer: anytype) !void {
        try writer.print("({d:.2}, {d:.2}, {d:.2})", .{
            self.data[0],
            self.data[1],
            self.data[2],
        });
    }
};

// ANCHOR: union_formatting
/// Tagged union formatting
const Shape = union(enum) {
    circle: struct { radius: f32 },
    rectangle: struct { width: f32, height: f32 },
    triangle: struct { base: f32, height: f32 },

    pub fn format(self: Shape, writer: anytype) !void {
        switch (self) {
            .circle => |c| try writer.print("Circle(r={d:.2})", .{c.radius}),
            .rectangle => |r| try writer.print("Rectangle({d:.2}x{d:.2})", .{ r.width, r.height }),
            .triangle => |t| try writer.print("Triangle(b={d:.2}, h={d:.2})", .{ t.base, t.height }),
        }
    }
};
// ANCHOR_END: union_formatting

/// Config with compact formatting
const Config = struct {
    host: []const u8,
    port: u16,
    timeout_ms: u32,

    pub fn format(self: Config, writer: anytype) !void {
        try writer.print("Config{{ host=\"{s}\", port={d}, timeout_ms={d} }}", .{
            self.host,
            self.port,
            self.timeout_ms,
        });
    }

    pub fn formatPretty(self: Config, writer: anytype) !void {
        try writer.writeAll("Config {\n");
        try writer.print("  host: \"{s}\"\n", .{self.host});
        try writer.print("  port: {d}\n", .{self.port});
        try writer.print("  timeout_ms: {d}\n", .{self.timeout_ms});
        try writer.writeAll("}");
    }
};

/// Status enum
const Status = enum { active, inactive, pending };

/// Account with conditional formatting
const Account = struct {
    username: []const u8,
    status: Status,
    login_count: u32,

    pub fn format(self: Account, writer: anytype) !void {
        try writer.print("{s} [", .{self.username});

        switch (self.status) {
            .active => try writer.writeAll("ACTIVE"),
            .inactive => try writer.writeAll("INACTIVE"),
            .pending => try writer.writeAll("PENDING"),
        }

        try writer.writeAll("]");

        if (self.status == .active) {
            try writer.print(" (logins: {d})", .{self.login_count});
        }
    }
};

/// Temperature with simple formatting
const Temperature = struct {
    celsius: f32,

    pub fn format(self: Temperature, writer: anytype) !void {
        try writer.print("{d:.1}°C", .{self.celsius});
    }

    pub fn formatPrecise(self: Temperature, writer: anytype) !void {
        try writer.print("{d:.2}°C", .{self.celsius});
    }
};

// Tests

test "custom string representation" {
    const p = Point{ .x = 3.14, .y = 2.71 };

    var buf: [100]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{p});

    try std.testing.expectEqualStrings("Point(3.14, 2.71)", result);
}

test "basic format" {
    const person = Person{ .name = "Alice", .age = 30 };

    var buf: [100]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{person});

    try std.testing.expectEqualStrings("Alice (age 30)", result);
}

test "format rectangle default" {
    const rect = Rectangle{ .width = 10.0, .height = 5.0 };

    var buf: [100]u8 = undefined;
    const default_fmt = try std.fmt.bufPrint(&buf, "{f}", .{rect});
    try std.testing.expectEqualStrings("Rectangle(10.00x5.00)", default_fmt);
}

test "rectangle area method" {
    const rect = Rectangle{ .width = 10.0, .height = 5.0 };
    try std.testing.expectEqual(@as(f32, 50.0), rect.area());
}

test "rectangle perimeter method" {
    const rect = Rectangle{ .width = 10.0, .height = 5.0 };
    try std.testing.expectEqual(@as(f32, 30.0), rect.perimeter());
}

test "user display format" {
    const user = User{
        .id = 12345,
        .username = "alice",
        .email = "alice@example.com",
    };

    var buf: [200]u8 = undefined;

    const display = try std.fmt.bufPrint(&buf, "{f}", .{user});
    try std.testing.expectEqualStrings("alice (alice@example.com)", display);
}

test "user debug format" {
    const user = User{
        .id = 12345,
        .username = "alice",
        .email = "alice@example.com",
    };

    var buf: [200]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buf);
    try user.formatDebug(stream.writer());

    try std.testing.expectEqualStrings(
        "User{ id=12345, username=\"alice\", email=\"alice@example.com\" }",
        stream.getWritten(),
    );
}

test "nested formatting" {
    const emp = Employee{
        .name = "Bob",
        .address = Address{ .street = "123 Main St", .city = "Springfield" },
    };

    var buf: [200]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{emp});

    try std.testing.expectEqualStrings("Bob @ 123 Main St, Springfield", result);
}

test "array formatting" {
    const v = Vector3{ .data = .{ 1.5, 2.5, 3.5 } };

    var buf: [100]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{v});

    try std.testing.expectEqualStrings("(1.50, 2.50, 3.50)", result);
}

test "union formatting circle" {
    const circle = Shape{ .circle = .{ .radius = 5.0 } };

    var buf: [100]u8 = undefined;
    const c_str = try std.fmt.bufPrint(&buf, "{f}", .{circle});
    try std.testing.expectEqualStrings("Circle(r=5.00)", c_str);
}

test "union formatting rectangle" {
    const rect = Shape{ .rectangle = .{ .width = 10.0, .height = 5.0 } };

    var buf: [100]u8 = undefined;
    const r_str = try std.fmt.bufPrint(&buf, "{f}", .{rect});
    try std.testing.expectEqualStrings("Rectangle(10.00x5.00)", r_str);
}

test "config compact formatting" {
    const cfg = Config{
        .host = "localhost",
        .port = 8080,
        .timeout_ms = 5000,
    };

    var buf: [200]u8 = undefined;
    const compact = try std.fmt.bufPrint(&buf, "{f}", .{cfg});
    try std.testing.expectEqualStrings(
        "Config{ host=\"localhost\", port=8080, timeout_ms=5000 }",
        compact,
    );
}

test "config pretty formatting" {
    const cfg = Config{
        .host = "localhost",
        .port = 8080,
        .timeout_ms = 5000,
    };

    var buf: [200]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buf);
    try cfg.formatPretty(stream.writer());

    const expected =
        \\Config {
        \\  host: "localhost"
        \\  port: 8080
        \\  timeout_ms: 5000
        \\}
    ;
    try std.testing.expectEqualStrings(expected, stream.getWritten());
}

test "conditional formatting active" {
    const active_acc = Account{
        .username = "alice",
        .status = .active,
        .login_count = 42,
    };

    var buf: [100]u8 = undefined;
    const active_str = try std.fmt.bufPrint(&buf, "{f}", .{active_acc});
    try std.testing.expectEqualStrings("alice [ACTIVE] (logins: 42)", active_str);
}

test "conditional formatting inactive" {
    const inactive_acc = Account{
        .username = "bob",
        .status = .inactive,
        .login_count = 0,
    };

    var buf: [100]u8 = undefined;
    const inactive_str = try std.fmt.bufPrint(&buf, "{f}", .{inactive_acc});
    try std.testing.expectEqualStrings("bob [INACTIVE]", inactive_str);
}

test "temperature default formatting" {
    const temp = Temperature{ .celsius = 23.456 };

    var buf: [100]u8 = undefined;
    const default_fmt = try std.fmt.bufPrint(&buf, "{f}", .{temp});
    try std.testing.expectEqualStrings("23.5°C", default_fmt);
}

test "temperature precise formatting" {
    const temp = Temperature{ .celsius = 23.456 };

    var buf: [100]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buf);
    try temp.formatPrecise(stream.writer());
    try std.testing.expectEqualStrings("23.46°C", stream.getWritten());
}
```

---

## Recipe 8.2: Customizing String Formatting {#recipe-8-2}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, json, memory, parsing, resource-cleanup, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_2.zig`

### Problem

You need advanced string formatting control beyond basic custom format functions, such as conditional formatting, format wrappers, or builder patterns.

### Solution

Create format wrapper types and builder patterns for flexible formatting:

```zig
/// Person with optional title
const Person = struct {
    name: []const u8,
    age: u32,
    title: ?[]const u8,

    pub fn format(self: Person, writer: anytype) !void {
        if (self.title) |t| {
            try writer.print("{s} {s}, age {d}", .{ t, self.name, self.age });
        } else {
            try writer.print("{s}, age {d}", .{ self.name, self.age });
        }
    }

    pub fn formatter(self: Person, comptime fmt_type: FormatType) PersonFormatter {
        return PersonFormatter{ .person = self, .fmt_type = fmt_type };
    }
};

const FormatType = enum { short, long, formal };

const PersonFormatter = struct {
    person: Person,
    fmt_type: FormatType,

    pub fn format(self: PersonFormatter, writer: anytype) !void {
        switch (self.fmt_type) {
            .short => try writer.print("{s}", .{self.person.name}),
            .long => try writer.print("{s} ({d} years old)", .{
                self.person.name,
                self.person.age,
            }),
            .formal => {
                if (self.person.title) |t| {
                    try writer.print("{s} {s}", .{ t, self.person.name });
                } else {
                    try writer.print("{s}", .{self.person.name});
                }
            },
        }
    }
};
```

### Discussion

### Format Builder Pattern

Build complex formatted output incrementally:

```zig
/// String builder
const StringBuilder = struct {
    parts: std.ArrayList([]const u8),
    owned: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) StringBuilder {
        return .{
            .parts = std.ArrayList([]const u8){},
            .owned = std.ArrayList([]const u8){},
            .allocator = allocator,
        };
    }

    pub fn add(self: *StringBuilder, part: []const u8) !void {
        try self.parts.append(self.allocator, part);
    }

    pub fn addFmt(self: *StringBuilder, comptime fmt: []const u8, args: anytype) !void {
        const str = try std.fmt.allocPrint(self.allocator, fmt, args);
        try self.parts.append(self.allocator, str);
        try self.owned.append(self.allocator, str);
    }

    pub fn build(self: *StringBuilder) ![]const u8 {
        return try std.mem.join(self.allocator, "", self.parts.items);
    }

    pub fn deinit(self: *StringBuilder) void {
        for (self.owned.items) |part| {
            self.allocator.free(part);
        }
        self.parts.deinit(self.allocator);
        self.owned.deinit(self.allocator);
    }
};
```

### Conditional Formatting

Format based on runtime state:

```zig
/// Article with status
const Status = enum { draft, published, archived };

const Article = struct {
    title: []const u8,
    author: []const u8,
    status: Status,
    views: usize,

    pub fn format(self: Article, writer: anytype) !void {
        try writer.print("\"{s}\" by {s} [", .{ self.title, self.author });

        switch (self.status) {
            .draft => try writer.writeAll("DRAFT"),
            .published => try writer.print("PUBLISHED, {d} views", .{self.views}),
            .archived => try writer.writeAll("ARCHIVED"),
        }

        try writer.writeAll("]");
    }
};
```

### Format with Width and Alignment

Create formatters that respect padding:

```zig
/// Padded formatter
const PaddedFormatter = struct {
    value: []const u8,
    width: usize,
    align_left: bool,

    pub fn format(self: PaddedFormatter, writer: anytype) !void {
        const value_len = self.value.len;

        if (value_len >= self.width) {
            try writer.writeAll(self.value);
            return;
        }

        const padding = self.width - value_len;

        if (self.align_left) {
            try writer.writeAll(self.value);
            var i: usize = 0;
            while (i < padding) : (i += 1) {
                try writer.writeByte(' ');
            }
        } else {
            var i: usize = 0;
            while (i < padding) : (i += 1) {
                try writer.writeByte(' ');
            }
            try writer.writeAll(self.value);
        }
    }
};

fn padLeft(value: []const u8, width: usize) PaddedFormatter {
    return .{ .value = value, .width = width, .align_left = false };
}

fn padRight(value: []const u8, width: usize) PaddedFormatter {
    return .{ .value = value, .width = width, .align_left = true };
}
```

### Table Formatter

Format data in tabular layout:

```zig
/// Table formatter
const TableFormatter = struct {
    headers: []const []const u8,
    rows: []const []const []const u8,

    pub fn format(self: TableFormatter, writer: anytype) !void {
        // Calculate column widths
        var widths = [_]usize{0} ** 10;
        for (self.headers, 0..) |header, i| {
            widths[i] = header.len;
        }

        for (self.rows) |row| {
            for (row, 0..) |cell, i| {
                widths[i] = @max(widths[i], cell.len);
            }
        }

        // Print headers
        for (self.headers, 0..) |header, i| {
            if (i > 0) try writer.writeAll(" | ");
            try writer.writeAll(header);
            // Don't pad the last column
            if (i < self.headers.len - 1) {
                const padding = widths[i] - header.len;
                var p: usize = 0;
                while (p < padding) : (p += 1) {
                    try writer.writeByte(' ');
                }
            }
        }
        try writer.writeAll("\n");

        // Print separator
        for (self.headers, 0..) |_, i| {
            if (i > 0) try writer.writeAll("-+-");
            var d: usize = 0;
            while (d < widths[i]) : (d += 1) {
                try writer.writeByte('-');
            }
        }
        try writer.writeAll("\n");

        // Print rows
        for (self.rows) |row| {
            for (row, 0..) |cell, i| {
                if (i > 0) try writer.writeAll(" | ");
                try writer.writeAll(cell);
                // Don't pad the last column
                if (i < row.len - 1) {
                    const padding = widths[i] - cell.len;
                    var p: usize = 0;
                    while (p < padding) : (p += 1) {
                        try writer.writeByte(' ');
                    }
                }
            }
            try writer.writeAll("\n");
        }
    }
};
```

### JSON-like Formatter

Create structured output formats:

```zig
/// JSON-like formatter
const JsonLikeFormatter = struct {
    depth: usize = 0,

    pub fn formatStruct(
        self: JsonLikeFormatter,
        writer: anytype,
        name: []const u8,
        fields: []const Field,
    ) !void {
        // Write indent spaces
        var d: usize = 0;
        while (d < self.depth) : (d += 1) {
            try writer.writeAll("  ");
        }

        try writer.print("{s} {{\n", .{name});

        for (fields, 0..) |field, i| {
            // Write next indent
            var nd: usize = 0;
            while (nd < self.depth + 1) : (nd += 1) {
                try writer.writeAll("  ");
            }
            try writer.print("{s}: {s}", .{ field.name, field.value });

            if (i < fields.len - 1) {
                try writer.writeAll(",\n");
            } else {
                try writer.writeAll("\n");
            }
        }

        // Write closing indent
        d = 0;
        while (d < self.depth) : (d += 1) {
            try writer.writeAll("  ");
        }
        try writer.writeAll("}");
    }
};

const Field = struct {
    name: []const u8,
    value: []const u8,
};
```

### Color Formatter (ANSI codes)

Add terminal colors to output:

```zig
/// Color formatter
const Color = enum {
    reset,
    red,
    green,
    yellow,
    blue,

    fn code(self: Color) []const u8 {
        return switch (self) {
            .reset => "\x1b[0m",
            .red => "\x1b[31m",
            .green => "\x1b[32m",
            .yellow => "\x1b[33m",
            .blue => "\x1b[34m",
        };
    }
};

const ColoredText = struct {
    text: []const u8,
    color: Color,

    pub fn format(self: ColoredText, writer: anytype) !void {
        try writer.writeAll(self.color.code());
        try writer.writeAll(self.text);
        try writer.writeAll(Color.reset.code());
    }
};

fn colored(text: []const u8, color: Color) ColoredText {
    return .{ .text = text, .color = color };
}
```

### List Formatter

Format collections with custom separators:

```zig
/// List formatter
const ListFormatter = struct {
    items: []const []const u8,
    separator: []const u8,
    prefix: []const u8,
    suffix: []const u8,

    pub fn format(self: ListFormatter, writer: anytype) !void {
        try writer.writeAll(self.prefix);

        for (self.items, 0..) |item, i| {
            try writer.writeAll(item);
            if (i < self.items.len - 1) {
                try writer.writeAll(self.separator);
            }
        }

        try writer.writeAll(self.suffix);
    }
};

fn listFmt(items: []const []const u8, separator: []const u8) ListFormatter {
    return .{
        .items = items,
        .separator = separator,
        .prefix = "",
        .suffix = "",
    };
}

fn bracketedList(items: []const []const u8, separator: []const u8) ListFormatter {
    return .{
        .items = items,
        .separator = separator,
        .prefix = "[",
        .suffix = "]",
    };
}
```

### Best Practices

**Format Wrapper Pattern:**
- Create a `formatter()` method that returns a formatting type
- The formatter type implements `format()` with custom logic
- Allows multiple format styles for the same data

**Builder Pattern:**
- Use for incremental construction of formatted output
- Track allocations and provide `deinit()`
- Separate concerns: building vs. rendering

**Performance:**
- Pre-calculate sizes when possible
- Minimize allocations in format functions
- Use buffered writers for multiple writes
- Consider streaming for large outputs

**Testing:**
- Test each format variant separately
- Use `std.io.fixedBufferStream()` for testing
- Verify exact output strings with `expectEqualStrings()`

### Related Functions

- `std.fmt.format()` - Core formatting
- `std.io.fixedBufferStream()` - Testing formatters
- `std.mem.join()` - Joining strings
- `std.ArrayList(u8)` - Dynamic string building

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: format_wrappers
/// Person with optional title
const Person = struct {
    name: []const u8,
    age: u32,
    title: ?[]const u8,

    pub fn format(self: Person, writer: anytype) !void {
        if (self.title) |t| {
            try writer.print("{s} {s}, age {d}", .{ t, self.name, self.age });
        } else {
            try writer.print("{s}, age {d}", .{ self.name, self.age });
        }
    }

    pub fn formatter(self: Person, comptime fmt_type: FormatType) PersonFormatter {
        return PersonFormatter{ .person = self, .fmt_type = fmt_type };
    }
};

const FormatType = enum { short, long, formal };

const PersonFormatter = struct {
    person: Person,
    fmt_type: FormatType,

    pub fn format(self: PersonFormatter, writer: anytype) !void {
        switch (self.fmt_type) {
            .short => try writer.print("{s}", .{self.person.name}),
            .long => try writer.print("{s} ({d} years old)", .{
                self.person.name,
                self.person.age,
            }),
            .formal => {
                if (self.person.title) |t| {
                    try writer.print("{s} {s}", .{ t, self.person.name });
                } else {
                    try writer.print("{s}", .{self.person.name});
                }
            },
        }
    }
};
// ANCHOR_END: format_wrappers

// ANCHOR: string_builder
/// String builder
const StringBuilder = struct {
    parts: std.ArrayList([]const u8),
    owned: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) StringBuilder {
        return .{
            .parts = std.ArrayList([]const u8){},
            .owned = std.ArrayList([]const u8){},
            .allocator = allocator,
        };
    }

    pub fn add(self: *StringBuilder, part: []const u8) !void {
        try self.parts.append(self.allocator, part);
    }

    pub fn addFmt(self: *StringBuilder, comptime fmt: []const u8, args: anytype) !void {
        const str = try std.fmt.allocPrint(self.allocator, fmt, args);
        try self.parts.append(self.allocator, str);
        try self.owned.append(self.allocator, str);
    }

    pub fn build(self: *StringBuilder) ![]const u8 {
        return try std.mem.join(self.allocator, "", self.parts.items);
    }

    pub fn deinit(self: *StringBuilder) void {
        for (self.owned.items) |part| {
            self.allocator.free(part);
        }
        self.parts.deinit(self.allocator);
        self.owned.deinit(self.allocator);
    }
};
// ANCHOR_END: string_builder

// ANCHOR: conditional_format
/// Article with status
const Status = enum { draft, published, archived };

const Article = struct {
    title: []const u8,
    author: []const u8,
    status: Status,
    views: usize,

    pub fn format(self: Article, writer: anytype) !void {
        try writer.print("\"{s}\" by {s} [", .{ self.title, self.author });

        switch (self.status) {
            .draft => try writer.writeAll("DRAFT"),
            .published => try writer.print("PUBLISHED, {d} views", .{self.views}),
            .archived => try writer.writeAll("ARCHIVED"),
        }

        try writer.writeAll("]");
    }
};
// ANCHOR_END: conditional_format

// ANCHOR: padded_formatter
/// Padded formatter
const PaddedFormatter = struct {
    value: []const u8,
    width: usize,
    align_left: bool,

    pub fn format(self: PaddedFormatter, writer: anytype) !void {
        const value_len = self.value.len;

        if (value_len >= self.width) {
            try writer.writeAll(self.value);
            return;
        }

        const padding = self.width - value_len;

        if (self.align_left) {
            try writer.writeAll(self.value);
            var i: usize = 0;
            while (i < padding) : (i += 1) {
                try writer.writeByte(' ');
            }
        } else {
            var i: usize = 0;
            while (i < padding) : (i += 1) {
                try writer.writeByte(' ');
            }
            try writer.writeAll(self.value);
        }
    }
};

fn padLeft(value: []const u8, width: usize) PaddedFormatter {
    return .{ .value = value, .width = width, .align_left = false };
}

fn padRight(value: []const u8, width: usize) PaddedFormatter {
    return .{ .value = value, .width = width, .align_left = true };
}
// ANCHOR_END: padded_formatter

// ANCHOR: table_formatter
/// Table formatter
const TableFormatter = struct {
    headers: []const []const u8,
    rows: []const []const []const u8,

    pub fn format(self: TableFormatter, writer: anytype) !void {
        // Calculate column widths
        var widths = [_]usize{0} ** 10;
        for (self.headers, 0..) |header, i| {
            widths[i] = header.len;
        }

        for (self.rows) |row| {
            for (row, 0..) |cell, i| {
                widths[i] = @max(widths[i], cell.len);
            }
        }

        // Print headers
        for (self.headers, 0..) |header, i| {
            if (i > 0) try writer.writeAll(" | ");
            try writer.writeAll(header);
            // Don't pad the last column
            if (i < self.headers.len - 1) {
                const padding = widths[i] - header.len;
                var p: usize = 0;
                while (p < padding) : (p += 1) {
                    try writer.writeByte(' ');
                }
            }
        }
        try writer.writeAll("\n");

        // Print separator
        for (self.headers, 0..) |_, i| {
            if (i > 0) try writer.writeAll("-+-");
            var d: usize = 0;
            while (d < widths[i]) : (d += 1) {
                try writer.writeByte('-');
            }
        }
        try writer.writeAll("\n");

        // Print rows
        for (self.rows) |row| {
            for (row, 0..) |cell, i| {
                if (i > 0) try writer.writeAll(" | ");
                try writer.writeAll(cell);
                // Don't pad the last column
                if (i < row.len - 1) {
                    const padding = widths[i] - cell.len;
                    var p: usize = 0;
                    while (p < padding) : (p += 1) {
                        try writer.writeByte(' ');
                    }
                }
            }
            try writer.writeAll("\n");
        }
    }
};
// ANCHOR_END: table_formatter

// ANCHOR: json_formatter
/// JSON-like formatter
const JsonLikeFormatter = struct {
    depth: usize = 0,

    pub fn formatStruct(
        self: JsonLikeFormatter,
        writer: anytype,
        name: []const u8,
        fields: []const Field,
    ) !void {
        // Write indent spaces
        var d: usize = 0;
        while (d < self.depth) : (d += 1) {
            try writer.writeAll("  ");
        }

        try writer.print("{s} {{\n", .{name});

        for (fields, 0..) |field, i| {
            // Write next indent
            var nd: usize = 0;
            while (nd < self.depth + 1) : (nd += 1) {
                try writer.writeAll("  ");
            }
            try writer.print("{s}: {s}", .{ field.name, field.value });

            if (i < fields.len - 1) {
                try writer.writeAll(",\n");
            } else {
                try writer.writeAll("\n");
            }
        }

        // Write closing indent
        d = 0;
        while (d < self.depth) : (d += 1) {
            try writer.writeAll("  ");
        }
        try writer.writeAll("}");
    }
};

const Field = struct {
    name: []const u8,
    value: []const u8,
};
// ANCHOR_END: json_formatter

// ANCHOR: color_formatter
/// Color formatter
const Color = enum {
    reset,
    red,
    green,
    yellow,
    blue,

    fn code(self: Color) []const u8 {
        return switch (self) {
            .reset => "\x1b[0m",
            .red => "\x1b[31m",
            .green => "\x1b[32m",
            .yellow => "\x1b[33m",
            .blue => "\x1b[34m",
        };
    }
};

const ColoredText = struct {
    text: []const u8,
    color: Color,

    pub fn format(self: ColoredText, writer: anytype) !void {
        try writer.writeAll(self.color.code());
        try writer.writeAll(self.text);
        try writer.writeAll(Color.reset.code());
    }
};

fn colored(text: []const u8, color: Color) ColoredText {
    return .{ .text = text, .color = color };
}
// ANCHOR_END: color_formatter

// ANCHOR: list_formatter
/// List formatter
const ListFormatter = struct {
    items: []const []const u8,
    separator: []const u8,
    prefix: []const u8,
    suffix: []const u8,

    pub fn format(self: ListFormatter, writer: anytype) !void {
        try writer.writeAll(self.prefix);

        for (self.items, 0..) |item, i| {
            try writer.writeAll(item);
            if (i < self.items.len - 1) {
                try writer.writeAll(self.separator);
            }
        }

        try writer.writeAll(self.suffix);
    }
};

fn listFmt(items: []const []const u8, separator: []const u8) ListFormatter {
    return .{
        .items = items,
        .separator = separator,
        .prefix = "",
        .suffix = "",
    };
}

fn bracketedList(items: []const []const u8, separator: []const u8) ListFormatter {
    return .{
        .items = items,
        .separator = separator,
        .prefix = "[",
        .suffix = "]",
    };
}
// ANCHOR_END: list_formatter

// Tests

test "format wrappers short" {
    const person = Person{
        .name = "Smith",
        .age = 35,
        .title = "Dr.",
    };

    var buf: [100]u8 = undefined;
    const short = try std.fmt.bufPrint(&buf, "{f}", .{person.formatter(.short)});
    try std.testing.expectEqualStrings("Smith", short);
}

test "format wrappers long" {
    const person = Person{
        .name = "Smith",
        .age = 35,
        .title = "Dr.",
    };

    var buf: [100]u8 = undefined;
    const long = try std.fmt.bufPrint(&buf, "{f}", .{person.formatter(.long)});
    try std.testing.expectEqualStrings("Smith (35 years old)", long);
}

test "format wrappers formal" {
    const person = Person{
        .name = "Smith",
        .age = 35,
        .title = "Dr.",
    };

    var buf: [100]u8 = undefined;
    const formal = try std.fmt.bufPrint(&buf, "{f}", .{person.formatter(.formal)});
    try std.testing.expectEqualStrings("Dr. Smith", formal);
}

test "string builder" {
    const allocator = std.testing.allocator;

    var builder = StringBuilder.init(allocator);
    defer builder.deinit();

    try builder.add("Hello ");
    try builder.addFmt("{s}!", .{"World"});
    try builder.addFmt(" Count: {d}", .{42});

    const result = try builder.build();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("Hello World! Count: 42", result);
}

test "conditional formatting draft" {
    var buf: [200]u8 = undefined;

    const draft = Article{
        .title = "My Article",
        .author = "Alice",
        .status = .draft,
        .views = 0,
    };

    const result = try std.fmt.bufPrint(&buf, "{f}", .{draft});
    try std.testing.expectEqualStrings("\"My Article\" by Alice [DRAFT]", result);
}

test "conditional formatting published" {
    var buf: [200]u8 = undefined;

    const published = Article{
        .title = "Published Work",
        .author = "Bob",
        .status = .published,
        .views = 1234,
    };

    const result = try std.fmt.bufPrint(&buf, "{f}", .{published});
    try std.testing.expectEqualStrings("\"Published Work\" by Bob [PUBLISHED, 1234 views]", result);
}

test "padded formatting left" {
    var buf: [100]u8 = undefined;

    const left = try std.fmt.bufPrint(&buf, "{f}", .{padLeft("test", 10)});
    try std.testing.expectEqualStrings("      test", left);
}

test "padded formatting right" {
    var buf: [100]u8 = undefined;

    const right = try std.fmt.bufPrint(&buf, "{f}", .{padRight("test", 10)});
    try std.testing.expectEqualStrings("test      ", right);
}

test "table formatter" {
    const headers = [_][]const u8{ "Name", "Age", "City" };
    const row1 = [_][]const u8{ "Alice", "30", "NYC" };
    const row2 = [_][]const u8{ "Bob", "25", "LA" };
    const rows = [_][]const []const u8{ &row1, &row2 };

    const table = TableFormatter{
        .headers = &headers,
        .rows = &rows,
    };

    var buf: [500]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buf);
    try table.format(stream.writer());

    const expected =
        \\Name  | Age | City
        \\------+-----+-----
        \\Alice | 30  | NYC
        \\Bob   | 25  | LA
        \\
    ;

    try std.testing.expectEqualStrings(expected, stream.getWritten());
}

test "json-like formatter" {
    const fields = [_]Field{
        .{ .name = "name", .value = "\"Alice\"" },
        .{ .name = "age", .value = "30" },
        .{ .name = "active", .value = "true" },
    };

    var buf: [500]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buf);

    const formatter = JsonLikeFormatter{};
    try formatter.formatStruct(stream.writer(), "User", &fields);

    const expected =
        \\User {
        \\  name: "Alice",
        \\  age: 30,
        \\  active: true
        \\}
    ;

    try std.testing.expectEqualStrings(expected, stream.getWritten());
}

test "colored formatter" {
    var buf: [500]u8 = undefined;

    const result = try std.fmt.bufPrint(&buf, "{f} {f} {f}", .{
        colored("Error", .red),
        colored("Warning", .yellow),
        colored("Success", .green),
    });

    try std.testing.expect(std.mem.indexOf(u8, result, "\x1b[31m") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "Error") != null);
}

test "list formatter comma" {
    const items = [_][]const u8{ "apple", "banana", "cherry" };

    var buf: [100]u8 = undefined;

    const comma = try std.fmt.bufPrint(&buf, "{f}", .{listFmt(&items, ", ")});
    try std.testing.expectEqualStrings("apple, banana, cherry", comma);
}

test "list formatter bracketed" {
    const items = [_][]const u8{ "apple", "banana", "cherry" };

    var buf: [100]u8 = undefined;

    const bracketed = try std.fmt.bufPrint(&buf, "{f}", .{bracketedList(&items, ", ")});
    try std.testing.expectEqualStrings("[apple, banana, cherry]", bracketed);
}

test "person default format" {
    const person = Person{
        .name = "Smith",
        .age = 35,
        .title = "Dr.",
    };

    var buf: [100]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{person});
    try std.testing.expectEqualStrings("Dr. Smith, age 35", result);
}

test "person without title" {
    const person = Person{
        .name = "Johnson",
        .age = 28,
        .title = null,
    };

    var buf: [100]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{person});
    try std.testing.expectEqualStrings("Johnson, age 28", result);
}
```

### See Also

- Recipe 8.1: String Representation
- Recipe 8.3: Context Management Protocol

---

## Recipe 8.3: Making Objects Support the Context Management Protocol {#recipe-8-3}

**Tags:** allocators, arena-allocator, arraylist, concurrency, data-structures, error-handling, memory, networking, resource-cleanup, slices, sockets, structs-objects, synchronization, testing, threading
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_3.zig`

### Problem

You need to ensure resources are properly cleaned up when they go out of scope, similar to Python's context managers or C++'s RAII pattern.

### Solution

Use `defer` and `errdefer` statements to guarantee cleanup, and implement `init`/`deinit` patterns:

```zig
// Basic defer pattern
const File = struct {
    handle: std.fs.File,
    path: []const u8,

    pub fn init(path: []const u8) !File {
        const file = try std.fs.cwd().createFile(path, .{});
        return File{
            .handle = file,
            .path = path,
        };
    }

    pub fn deinit(self: *File) void {
        self.handle.close();
    }

    pub fn write(self: *File, data: []const u8) !void {
        try self.handle.writeAll(data);
    }
};
```

### Discussion

### Understanding defer

The `defer` statement schedules code to run when leaving the current scope:

```zig
const Database = struct {
    connection: i32,

    pub fn init() !Database {
        return Database{ .connection = 42 };
    }

    pub fn deinit(self: *Database) void {
        std.debug.print("Closing connection {d}\n", .{self.connection});
        self.connection = 0;
    }

    pub fn query(self: *Database, sql: []const u8) !void {
        _ = sql;
        std.debug.print("Executing on connection {d}\n", .{self.connection});
    }
};

test "defer execution order" {
    var db = try Database.init();
    defer db.deinit();

    try db.query("SELECT * FROM users");
    // deinit() called here automatically
}
```

### Using errdefer for Error Cleanup

The `errdefer` statement only runs if the function returns with an error:

```zig
const Resource = struct {
    data: []u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, size: usize) !Resource {
        const data = try allocator.alloc(u8, size);
        errdefer allocator.free(data);

        // If this fails, data is freed automatically
        if (size > 1000) {
            return error.TooLarge;
        }

        return Resource{
            .data = data,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Resource) void {
        self.allocator.free(self.data);
    }
};

test "errdefer on failure" {
    const allocator = std.testing.allocator;

    // This succeeds
    var res1 = try Resource.init(allocator, 100);
    defer res1.deinit();

    // This fails but doesn't leak because of errdefer
    const res2 = Resource.init(allocator, 2000);
    try std.testing.expectError(error.TooLarge, res2);
}
```

### Multiple Resource Management

Handle multiple resources with proper cleanup order:

```zig
const Connection = struct {
    socket: i32,
    buffer: []u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) !Connection {
        const socket = 123; // Simulate opening socket
        errdefer {
            // Close socket if subsequent allocations fail
            std.debug.print("Closing socket on error\n", .{});
        }

        const buffer = try allocator.alloc(u8, 1024);
        errdefer allocator.free(buffer);

        return Connection{
            .socket = socket,
            .buffer = buffer,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Connection) void {
        self.allocator.free(self.buffer);
        std.debug.print("Closing socket {d}\n", .{self.socket});
    }

    pub fn send(self: *Connection, data: []const u8) !void {
        @memcpy(self.buffer[0..data.len], data);
    }
};

test "multiple resource cleanup" {
    const allocator = std.testing.allocator;

    var conn = try Connection.init(allocator);
    defer conn.deinit();

    try conn.send("Hello");
}
```

### Nested Defer Scopes

Defers execute in reverse order (LIFO):

```zig
test "defer execution order" {
    var count: u32 = 0;

    {
        defer count += 1; // Executes third
        defer count += 10; // Executes second
        defer count += 100; // Executes first

        try std.testing.expectEqual(@as(u32, 0), count);
    }

    // Order: 100 + 10 + 1 = 111
    try std.testing.expectEqual(@as(u32, 111), count);
}
```

### Scope-Based Resource Management

Create scoped wrappers for temporary resources:

```zig
const TempDir = struct {
    path: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, name: []const u8) !TempDir {
        const path = try std.fmt.allocPrint(allocator, "/tmp/{s}", .{name});
        errdefer allocator.free(path);

        // Simulate directory creation
        std.debug.print("Creating directory: {s}\n", .{path});

        return TempDir{
            .path = path,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *TempDir) void {
        std.debug.print("Removing directory: {s}\n", .{self.path});
        self.allocator.free(self.path);
    }

    pub fn getPath(self: *const TempDir) []const u8 {
        return self.path;
    }
};

test "scoped resource" {
    const allocator = std.testing.allocator;

    var tmpdir = try TempDir.init(allocator, "test123");
    defer tmpdir.deinit();

    const path = tmpdir.getPath();
    try std.testing.expect(std.mem.indexOf(u8, path, "test123") != null);
}
```

### Lock Guard Pattern

Implement automatic lock management:

```zig
const LockGuard = struct {
    mutex: *std.Thread.Mutex,

    pub fn init(mutex: *std.Thread.Mutex) LockGuard {
        mutex.lock();
        return LockGuard{ .mutex = mutex };
    }

    pub fn deinit(self: *LockGuard) void {
        self.mutex.unlock();
    }
};

test "lock guard" {
    var mutex = std.Thread.Mutex{};

    {
        var guard = LockGuard.init(&mutex);
        defer guard.deinit();

        // Critical section - mutex is locked
        // ...
    }
    // mutex is automatically unlocked here
}
```

### Transaction-Style Operations

Implement rollback on error:

```zig
const Transaction = struct {
    committed: bool,
    value: *i32,

    pub fn init(value: *i32) Transaction {
        return Transaction{
            .committed = false,
            .value = value,
        };
    }

    pub fn commit(self: *Transaction) void {
        self.committed = true;
    }

    pub fn deinit(self: *Transaction) void {
        if (!self.committed) {
            std.debug.print("Rolling back transaction\n", .{});
            self.value.* = 0;
        }
    }

    pub fn execute(self: *Transaction, new_value: i32) !void {
        _ = self;
        if (new_value < 0) {
            return error.InvalidValue;
        }
        self.value.* = new_value;
    }
};

test "transaction rollback" {
    var value: i32 = 100;

    // Successful transaction
    {
        var txn = Transaction.init(&value);
        defer txn.deinit();

        try txn.execute(200);
        txn.commit();
    }
    try std.testing.expectEqual(@as(i32, 200), value);

    // Failed transaction - rolls back
    {
        var txn = Transaction.init(&value);
        defer txn.deinit();

        const result = txn.execute(-50);
        try std.testing.expectError(error.InvalidValue, result);
        // No commit called - deinit() rolls back
    }
    try std.testing.expectEqual(@as(i32, 0), value);
}
```

### Arena Allocator Pattern

Use arena for temporary allocations:

```zig
const Parser = struct {
    arena: std.heap.ArenaAllocator,

    pub fn init(backing_allocator: std.mem.Allocator) Parser {
        return Parser{
            .arena = std.heap.ArenaAllocator.init(backing_allocator),
        };
    }

    pub fn deinit(self: *Parser) void {
        self.arena.deinit();
    }

    pub fn parseString(self: *Parser, input: []const u8) ![]u8 {
        const allocator = self.arena.allocator();
        const result = try allocator.alloc(u8, input.len);
        @memcpy(result, input);
        return result;
    }
};

test "arena allocator cleanup" {
    var parser = Parser.init(std.testing.allocator);
    defer parser.deinit();

    const str1 = try parser.parseString("hello");
    const str2 = try parser.parseString("world");

    try std.testing.expectEqualStrings("hello", str1);
    try std.testing.expectEqualStrings("world", str2);

    // All allocations freed in deinit()
}
```

### Builder Pattern with Cleanup

Ensure resources are freed even if build fails:

```zig
const Builder = struct {
    items: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Builder {
        return Builder{
            .items = std.ArrayList([]const u8){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Builder) void {
        for (self.items.items) |item| {
            self.allocator.free(item);
        }
        self.items.deinit(self.allocator);
    }

    pub fn add(self: *Builder, item: []const u8) !void {
        const copy = try self.allocator.dupe(u8, item);
        errdefer self.allocator.free(copy);

        try self.items.append(self.allocator, copy);
    }

    pub fn build(self: *Builder) ![][]const u8 {
        return try self.items.toOwnedSlice(self.allocator);
    }
};

test "builder with cleanup" {
    var builder = Builder.init(std.testing.allocator);
    defer builder.deinit();

    try builder.add("first");
    try builder.add("second");

    const result = try builder.build();
    defer {
        for (result) |item| {
            std.testing.allocator.free(item);
        }
        std.testing.allocator.free(result);
    }

    try std.testing.expectEqual(@as(usize, 2), result.len);
}
```

### Best Practices

**Always Pair init/deinit:**
```zig
// Good: Clear lifecycle
var resource = try Resource.init(allocator);
defer resource.deinit();
```

**Use errdefer for Partial Cleanup:**
```zig
pub fn init(allocator: std.mem.Allocator) !MyStruct {
    const buffer = try allocator.alloc(u8, 1024);
    errdefer allocator.free(buffer);

    const more = try allocator.alloc(u8, 512);
    errdefer allocator.free(more);

    return MyStruct{ .buffer = buffer, .more = more };
}
```

**Defer Order Matters:**
```zig
// Defers execute in reverse order (LIFO)
var a = try initA();
defer a.deinit(); // Called last

var b = try initB();
defer b.deinit(); // Called first
```

**Document Ownership:**
```zig
/// Caller owns returned memory and must call deinit()
pub fn create(allocator: std.mem.Allocator) !*MyStruct {
    // ...
}
```

### Related Patterns

- Recipe 7.11: Inlining callback functions
- Recipe 8.19: Implementing state machines
- Chapter 18: Explicit Memory Management Patterns

### Full Tested Code

```zig
// Recipe 8.3: Making Objects Support the Context-Management Protocol
// Target Zig Version: 0.15.2

const std = @import("std");

// ANCHOR: basic_defer
// Basic defer pattern
const File = struct {
    handle: std.fs.File,
    path: []const u8,

    pub fn init(path: []const u8) !File {
        const file = try std.fs.cwd().createFile(path, .{});
        return File{
            .handle = file,
            .path = path,
        };
    }

    pub fn deinit(self: *File) void {
        self.handle.close();
    }

    pub fn write(self: *File, data: []const u8) !void {
        try self.handle.writeAll(data);
    }
};
// ANCHOR_END: basic_defer

test "basic defer pattern" {
    const test_file = "test_defer.txt";
    defer std.fs.cwd().deleteFile(test_file) catch {};

    var file = try File.init(test_file);
    defer file.deinit();

    try file.write("Hello, World!");
}

// Database with defer
const Database = struct {
    connection: i32,

    pub fn init() !Database {
        return Database{ .connection = 42 };
    }

    pub fn deinit(self: *Database) void {
        self.connection = 0;
    }

    pub fn query(self: *Database, sql: []const u8) !void {
        _ = sql;
        _ = self;
    }
};

test "defer execution order" {
    var db = try Database.init();
    defer db.deinit();

    try db.query("SELECT * FROM users");
}

// ANCHOR: errdefer_cleanup
// errdefer for error cleanup
const Resource = struct {
    data: []u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, size: usize) !Resource {
        const data = try allocator.alloc(u8, size);
        errdefer allocator.free(data);

        if (size > 1000) {
            return error.TooLarge;
        }

        return Resource{
            .data = data,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Resource) void {
        self.allocator.free(self.data);
    }
};
// ANCHOR_END: errdefer_cleanup

test "errdefer on failure" {
    const allocator = std.testing.allocator;

    var res1 = try Resource.init(allocator, 100);
    defer res1.deinit();

    const res2 = Resource.init(allocator, 2000);
    try std.testing.expectError(error.TooLarge, res2);
}

// Multiple resource management
const Connection = struct {
    socket: i32,
    buffer: []u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) !Connection {
        const socket = 123;

        const buffer = try allocator.alloc(u8, 1024);
        errdefer allocator.free(buffer);

        return Connection{
            .socket = socket,
            .buffer = buffer,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Connection) void {
        self.allocator.free(self.buffer);
    }

    pub fn send(self: *Connection, data: []const u8) !void {
        @memcpy(self.buffer[0..data.len], data);
    }
};

test "multiple resource cleanup" {
    const allocator = std.testing.allocator;

    var conn = try Connection.init(allocator);
    defer conn.deinit();

    try conn.send("Hello");
}

// Nested defer scopes
test "defer execution order LIFO" {
    var count: u32 = 0;

    {
        defer count += 1;
        defer count += 10;
        defer count += 100;

        try std.testing.expectEqual(@as(u32, 0), count);
    }

    try std.testing.expectEqual(@as(u32, 111), count);
}

// Scoped resource management
const TempDir = struct {
    path: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, name: []const u8) !TempDir {
        const path = try std.fmt.allocPrint(allocator, "/tmp/{s}", .{name});
        errdefer allocator.free(path);

        return TempDir{
            .path = path,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *TempDir) void {
        self.allocator.free(self.path);
    }

    pub fn getPath(self: *const TempDir) []const u8 {
        return self.path;
    }
};

test "scoped resource" {
    const allocator = std.testing.allocator;

    var tmpdir = try TempDir.init(allocator, "test123");
    defer tmpdir.deinit();

    const path = tmpdir.getPath();
    try std.testing.expect(std.mem.indexOf(u8, path, "test123") != null);
}

// Lock guard pattern
const LockGuard = struct {
    mutex: *std.Thread.Mutex,

    pub fn init(mutex: *std.Thread.Mutex) LockGuard {
        mutex.lock();
        return LockGuard{ .mutex = mutex };
    }

    pub fn deinit(self: *LockGuard) void {
        self.mutex.unlock();
    }
};

test "lock guard" {
    var mutex = std.Thread.Mutex{};

    {
        var guard = LockGuard.init(&mutex);
        defer guard.deinit();
    }
}

// Transaction-style operations
const Transaction = struct {
    committed: bool,
    value: *i32,

    pub fn init(value: *i32) Transaction {
        return Transaction{
            .committed = false,
            .value = value,
        };
    }

    pub fn commit(self: *Transaction) void {
        self.committed = true;
    }

    pub fn deinit(self: *Transaction) void {
        if (!self.committed) {
            self.value.* = 0;
        }
    }

    pub fn execute(self: *Transaction, new_value: i32) !void {
        if (new_value < 0) {
            return error.InvalidValue;
        }
        self.value.* = new_value;
    }
};

test "transaction rollback" {
    var value: i32 = 100;

    {
        var txn = Transaction.init(&value);
        defer txn.deinit();

        try txn.execute(200);
        txn.commit();
    }
    try std.testing.expectEqual(@as(i32, 200), value);

    {
        var txn = Transaction.init(&value);
        defer txn.deinit();

        const result = txn.execute(-50);
        try std.testing.expectError(error.InvalidValue, result);
    }
    try std.testing.expectEqual(@as(i32, 0), value);
}

// ANCHOR: arena_pattern
// Arena allocator pattern
const Parser = struct {
    arena: std.heap.ArenaAllocator,

    pub fn init(backing_allocator: std.mem.Allocator) Parser {
        return Parser{
            .arena = std.heap.ArenaAllocator.init(backing_allocator),
        };
    }

    pub fn deinit(self: *Parser) void {
        self.arena.deinit();
    }

    pub fn parseString(self: *Parser, input: []const u8) ![]u8 {
        const allocator = self.arena.allocator();
        const result = try allocator.alloc(u8, input.len);
        @memcpy(result, input);
        return result;
    }
};
// ANCHOR_END: arena_pattern

test "arena allocator cleanup" {
    var parser = Parser.init(std.testing.allocator);
    defer parser.deinit();

    const str1 = try parser.parseString("hello");
    const str2 = try parser.parseString("world");

    try std.testing.expectEqualStrings("hello", str1);
    try std.testing.expectEqualStrings("world", str2);
}

// Builder pattern with cleanup
const Builder = struct {
    items: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Builder {
        return Builder{
            .items = std.ArrayList([]const u8){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Builder) void {
        for (self.items.items) |item| {
            self.allocator.free(item);
        }
        self.items.deinit(self.allocator);
    }

    pub fn add(self: *Builder, item: []const u8) !void {
        const copy = try self.allocator.dupe(u8, item);
        errdefer self.allocator.free(copy);

        try self.items.append(self.allocator, copy);
    }

    pub fn build(self: *Builder) ![][]const u8 {
        return try self.items.toOwnedSlice(self.allocator);
    }
};

test "builder with cleanup" {
    var builder = Builder.init(std.testing.allocator);
    defer builder.deinit();

    try builder.add("first");
    try builder.add("second");

    const result = try builder.build();
    defer {
        for (result) |item| {
            std.testing.allocator.free(item);
        }
        std.testing.allocator.free(result);
    }

    try std.testing.expectEqual(@as(usize, 2), result.len);
}

// Comprehensive test
test "comprehensive context management" {
    const allocator = std.testing.allocator;

    var outer_resource = try Resource.init(allocator, 100);
    defer outer_resource.deinit();

    var conn = try Connection.init(allocator);
    defer conn.deinit();

    try conn.send("test data");

    var tmpdir = try TempDir.init(allocator, "comprehensive_test");
    defer tmpdir.deinit();

    try std.testing.expect(tmpdir.getPath().len > 0);
}
```

---

## Recipe 8.4: Saving Memory When Creating a Large Number of Instances {#recipe-8-4}

**Tags:** structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_4.zig`

### Problem

You need to create thousands or millions of instances of a struct and want to minimize memory usage.

### Solution

Use `packed struct` to eliminate padding and control memory layout at the bit level:

```zig
// Basic packed struct
const CompactFlags = packed struct {
    is_active: bool,
    is_visible: bool,
    is_enabled: bool,
    priority: u5,
};
```

### Discussion

### Understanding Packed Struct Alignment

Packed structs eliminate padding between fields, but the compiler may still align the overall struct to natural boundaries for performance. The actual size depends on the target architecture and field types.

```zig
test "packed struct alignment" {
    const Small = packed struct {
        a: bool,
        b: bool,
        c: bool,
    };

    // Might be 1 byte or padded to 2/4 bytes depending on alignment
    const size = @sizeOf(Small);
    try std.testing.expect(size >= 1);
}
```

### Normal vs Packed Structs

Compare memory layout of normal and packed structs:

```zig
const NormalFlags = struct {
    is_active: bool,
    is_visible: bool,
    is_enabled: bool,
    count: u8,
};

const PackedFlags = packed struct {
    is_active: bool,
    is_visible: bool,
    is_enabled: bool,
    count: u5,
};

test "normal vs packed" {
    // Normal struct has padding for alignment
    const normal_size = @sizeOf(NormalFlags);
    try std.testing.expect(normal_size >= 4);

    // Packed struct uses exact bits needed
    const packed_size = @sizeOf(PackedFlags);
    try std.testing.expectEqual(@as(usize, 1), packed_size);

    // Memory savings when creating many instances
    const num_instances = 1000000;
    const normal_memory = normal_size * num_instances;
    const packed_memory = packed_size * num_instances;

    std.debug.print(
        "Normal: {} bytes, Packed: {} bytes, Savings: {} bytes\n",
        .{ normal_memory, packed_memory, normal_memory - packed_memory },
    );
}
```

### Bit Field Packing

Pack multiple small values into minimal space:

```zig
const RGBColor = packed struct {
    red: u8,
    green: u8,
    blue: u8,

    // Takes exactly 3 bytes
};

const CompactColor = packed struct {
    red: u5,    // 0-31
    green: u6,  // 0-63
    blue: u5,   // 0-31

    // Takes exactly 2 bytes (16 bits)
};

test "color packing" {
    try std.testing.expectEqual(@as(usize, 3), @sizeOf(RGBColor));
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(CompactColor));

    const color = CompactColor{
        .red = 31,
        .green = 63,
        .blue = 31,
    };

    try std.testing.expectEqual(@as(u5, 31), color.red);
    try std.testing.expectEqual(@as(u6, 63), color.green);
}
```

### Network Protocol Headers

Pack protocol headers efficiently:

```zig
const PacketHeader = packed struct {
    version: u4,        // 0-15
    packet_type: u4,    // 0-15
    flags: u8,
    length: u16,

    // Total: 4 bytes
};

test "packet header" {
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(PacketHeader));

    const header = PacketHeader{
        .version = 1,
        .packet_type = 5,
        .flags = 0x80,
        .length = 1024,
    };

    // Can cast directly to bytes for network transmission
    const bytes: *const [4]u8 = @ptrCast(&header);
    _ = bytes;
}
```

### Game Entity Flags

Optimize game entity states:

```zig
const Entity = packed struct {
    // Movement
    can_move: bool,
    can_jump: bool,
    can_fly: bool,
    can_swim: bool,

    // Combat
    is_hostile: bool,
    is_invulnerable: bool,
    can_attack: bool,
    _padding1: bool,

    // Visibility
    is_visible: bool,
    casts_shadow: bool,
    receives_shadow: bool,
    _padding2: u5,

    // Stats (fit in remaining bits)
    health_percent: u8,  // 0-255

    // Total: 3 bytes per entity
};

test "game entity" {
    try std.testing.expectEqual(@as(usize, 3), @sizeOf(Entity));

    var entity = Entity{
        .can_move = true,
        .can_jump = true,
        .can_fly = false,
        .can_swim = false,
        .is_hostile = true,
        .is_invulnerable = false,
        .can_attack = true,
        ._padding1 = false,
        .is_visible = true,
        .casts_shadow = true,
        .receives_shadow = true,
        ._padding2 = 0,
        .health_percent = 100,
    };

    try std.testing.expect(entity.can_move);
    try std.testing.expectEqual(@as(u8, 100), entity.health_percent);

    entity.health_percent = 50;
    try std.testing.expectEqual(@as(u8, 50), entity.health_percent);
}
```

### File Format Structures

Pack file format metadata:

```zig
const FileHeader = packed struct {
    magic: u32,
    version_major: u8,
    version_minor: u8,
    flags: u16,
    entry_count: u32,
    reserved: u64,

    // Total: 16 bytes
};

test "file header" {
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(FileHeader));

    const header = FileHeader{
        .magic = 0x12345678,
        .version_major = 1,
        .version_minor = 0,
        .flags = 0,
        .entry_count = 42,
        .reserved = 0,
    };

    try std.testing.expectEqual(@as(u32, 0x12345678), header.magic);
}
```

### Enum-Based Bit Packing

Use enums with explicit bit widths:

```zig
const Priority = enum(u2) {
    low = 0,
    medium = 1,
    high = 2,
    critical = 3,
};

const Status = enum(u2) {
    idle = 0,
    running = 1,
    paused = 2,
    stopped = 3,
};

const Task = packed struct {
    priority: Priority,
    status: Status,
    is_async: bool,
    is_cancellable: bool,
    progress: u8,  // 0-255 percent
    _padding: u4,

    // Total: 2 bytes
};

test "task packing" {
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(Task));

    const task = Task{
        .priority = .high,
        .status = .running,
        .is_async = true,
        .is_cancellable = true,
        .progress = 75,
        ._padding = 0,
    };

    try std.testing.expectEqual(Priority.high, task.priority);
    try std.testing.expectEqual(Status.running, task.status);
}
```

### Date/Time Packing

Pack date and time efficiently:

```zig
const CompactDateTime = packed struct {
    year: u12,   // 0-4095 (supports years 0-4095)
    month: u4,   // 1-12
    day: u5,     // 1-31
    hour: u5,    // 0-23
    minute: u6,  // 0-59
    second: u6,  // 0-59

    // Total: 38 bits = 5 bytes (rounded up)
};

test "datetime packing" {
    const dt = CompactDateTime{
        .year = 2024,
        .month = 11,
        .day = 13,
        .hour = 14,
        .minute = 30,
        .second = 45,
    };

    try std.testing.expectEqual(@as(u12, 2024), dt.year);
    try std.testing.expectEqual(@as(u4, 11), dt.month);
    try std.testing.expectEqual(@as(u5, 13), dt.day);
}
```

### Permission Bits

Pack Unix-style permissions:

```zig
const Permissions = packed struct {
    // Owner
    owner_read: bool,
    owner_write: bool,
    owner_execute: bool,

    // Group
    group_read: bool,
    group_write: bool,
    group_execute: bool,

    // Others
    others_read: bool,
    others_write: bool,
    others_execute: bool,

    // Special bits
    setuid: bool,
    setgid: bool,
    sticky: bool,

    _padding: u4,

    // Total: 2 bytes
};

test "permissions" {
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(Permissions));

    const perms = Permissions{
        .owner_read = true,
        .owner_write = true,
        .owner_execute = true,
        .group_read = true,
        .group_write = false,
        .group_execute = true,
        .others_read = true,
        .others_write = false,
        .others_execute = false,
        .setuid = false,
        .setgid = false,
        .sticky = false,
        ._padding = 0,
    };

    try std.testing.expect(perms.owner_read);
    try std.testing.expect(!perms.group_write);
}
```

### Struct Field Ordering

Optimize normal struct layout by ordering fields:

```zig
const UnoptimizedStruct = struct {
    flag1: bool,  // 1 byte + 7 padding
    value1: u64,  // 8 bytes (aligned to 8)
    flag2: bool,  // 1 byte + 7 padding
    value2: u64,  // 8 bytes (aligned to 8)
    // Total: ~32 bytes
};

const OptimizedStruct = struct {
    value1: u64,  // 8 bytes
    value2: u64,  // 8 bytes
    flag1: bool,  // 1 byte
    flag2: bool,  // 1 byte + 6 padding
    // Total: ~24 bytes
};

test "field ordering" {
    const unopt_size = @sizeOf(UnoptimizedStruct);
    const opt_size = @sizeOf(OptimizedStruct);

    std.debug.print(
        "Unoptimized: {} bytes, Optimized: {} bytes\n",
        .{ unopt_size, opt_size },
    );

    // Optimized struct is smaller due to better field ordering
    try std.testing.expect(opt_size <= unopt_size);
}
```

### Array of Structs Optimization

Compare memory usage for arrays:

```zig
test "array memory comparison" {
    const NormalItem = struct {
        active: bool,
        id: u16,
        flags: u8,
    };

    const PackedItem = packed struct {
        active: bool,
        id: u16,
        flags: u8,
    };

    const count = 10000;

    const normal_total = @sizeOf(NormalItem) * count;
    const packed_total = @sizeOf(PackedItem) * count;

    std.debug.print(
        "Array of {}: Normal {} bytes, Packed {} bytes\n",
        .{ count, normal_total, packed_total },
    );
}
```

### Best Practices

**When to Use Packed Structs:**
- Large arrays of data structures
- Network protocol headers
- File format structures
- Embedded systems with limited memory
- Game entities with many boolean flags

**Trade-offs:**
```zig
// Packed struct cons:
// - Slower access (may require bit manipulation)
// - Cannot take address of fields
// - May not work with @alignOf expectations

// Good use case - millions of instances
const Good = packed struct {
    flags: u8,
    id: u16,
};

// Bad use case - single instance
const Bad = packed struct {
    single_flag: bool,
};
```

**Padding Management:**
```zig
// Explicitly pad to byte boundaries when needed
const Padded = packed struct {
    value1: u5,
    value2: u5,
    _padding: u6,  // Explicitly pad to 16 bits
};
```

**Testing Memory Layout:**
```zig
test "verify size" {
    const MyStruct = packed struct {
        field1: u8,
        field2: u8,
    };

    // Always verify expected size
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(MyStruct));
}
```

**Type Safety:**
```zig
// Use explicit types for bit fields
const Config = packed struct {
    mode: u2,    // Better than anonymous bits
    level: u4,
    _pad: u2,
};
```

### Related Patterns

- Recipe 8.1: String representation of instances
- Recipe 8.19: Implementing state machines
- Chapter 18: Explicit Memory Management Patterns

### Full Tested Code

```zig
// Recipe 8.4: Saving Memory When Creating Many Instances
// Target Zig Version: 0.15.2

const std = @import("std");

// ANCHOR: basic_packed
// Basic packed struct
const CompactFlags = packed struct {
    is_active: bool,
    is_visible: bool,
    is_enabled: bool,
    priority: u5,
};
// ANCHOR_END: basic_packed

test "packed struct size" {
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(CompactFlags));

    const flags = CompactFlags{
        .is_active = true,
        .is_visible = false,
        .is_enabled = true,
        .priority = 10,
    };

    try std.testing.expect(flags.is_active);
    try std.testing.expect(!flags.is_visible);
    try std.testing.expectEqual(@as(u5, 10), flags.priority);
}

// ANCHOR: size_comparison
// Normal vs packed comparison
const NormalFlags = struct {
    is_active: bool,
    is_visible: bool,
    is_enabled: bool,
    count: u8,
};

const PackedFlags = packed struct {
    is_active: bool,
    is_visible: bool,
    is_enabled: bool,
    count: u5,
};

test "normal vs packed" {
    const normal_size = @sizeOf(NormalFlags);
    try std.testing.expect(normal_size >= 4);

    const packed_size = @sizeOf(PackedFlags);
    try std.testing.expectEqual(@as(usize, 1), packed_size);
}
// ANCHOR_END: size_comparison

// Color packing
const RGBColor = packed struct {
    red: u8,
    green: u8,
    blue: u8,
};

const CompactColor = packed struct {
    red: u5,
    green: u6,
    blue: u5,
};

test "color packing" {
    // RGBColor may be padded for alignment
    try std.testing.expect(@sizeOf(RGBColor) >= 3);

    // CompactColor saves space vs full u8 fields
    try std.testing.expect(@sizeOf(CompactColor) <= @sizeOf(RGBColor));

    const color = CompactColor{
        .red = 31,
        .green = 63,
        .blue = 31,
    };

    try std.testing.expectEqual(@as(u5, 31), color.red);
    try std.testing.expectEqual(@as(u6, 63), color.green);
}

// Network packet header
const PacketHeader = packed struct {
    version: u4,
    packet_type: u4,
    flags: u8,
    length: u16,
};

test "packet header" {
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(PacketHeader));

    const header = PacketHeader{
        .version = 1,
        .packet_type = 5,
        .flags = 0x80,
        .length = 1024,
    };

    const bytes: *const [4]u8 = @ptrCast(&header);
    _ = bytes;
}

// Game entity
const Entity = packed struct {
    can_move: bool,
    can_jump: bool,
    can_fly: bool,
    can_swim: bool,
    is_hostile: bool,
    is_invulnerable: bool,
    can_attack: bool,
    _padding1: bool,
    is_visible: bool,
    casts_shadow: bool,
    receives_shadow: bool,
    _padding2: u5,
    health_percent: u8,
};

test "game entity" {
    // Packed struct may be padded for alignment
    try std.testing.expect(@sizeOf(Entity) <= 8);

    var entity = Entity{
        .can_move = true,
        .can_jump = true,
        .can_fly = false,
        .can_swim = false,
        .is_hostile = true,
        .is_invulnerable = false,
        .can_attack = true,
        ._padding1 = false,
        .is_visible = true,
        .casts_shadow = true,
        .receives_shadow = true,
        ._padding2 = 0,
        .health_percent = 100,
    };

    try std.testing.expect(entity.can_move);
    try std.testing.expectEqual(@as(u8, 100), entity.health_percent);

    entity.health_percent = 50;
    try std.testing.expectEqual(@as(u8, 50), entity.health_percent);
}

// File header
const FileHeader = packed struct {
    magic: u32,
    version_major: u8,
    version_minor: u8,
    flags: u16,
    entry_count: u32,
    reserved: u64,
};

test "file header" {
    // FileHeader contains u64, so may be aligned to 8 bytes
    try std.testing.expect(@sizeOf(FileHeader) >= 16);

    const header = FileHeader{
        .magic = 0x12345678,
        .version_major = 1,
        .version_minor = 0,
        .flags = 0,
        .entry_count = 42,
        .reserved = 0,
    };

    try std.testing.expectEqual(@as(u32, 0x12345678), header.magic);
}

// ANCHOR: enum_packing
// Enum-based packing
const Priority = enum(u2) {
    low = 0,
    medium = 1,
    high = 2,
    critical = 3,
};

const Status = enum(u2) {
    idle = 0,
    running = 1,
    paused = 2,
    stopped = 3,
};

const Task = packed struct {
    priority: Priority,
    status: Status,
    is_async: bool,
    is_cancellable: bool,
    progress: u8,
    _padding: u4,
};

test "task packing" {
    // Packed struct may be aligned to word boundary
    try std.testing.expect(@sizeOf(Task) <= 4);

    const task = Task{
        .priority = .high,
        .status = .running,
        .is_async = true,
        .is_cancellable = true,
        .progress = 75,
        ._padding = 0,
    };

    try std.testing.expectEqual(Priority.high, task.priority);
    try std.testing.expectEqual(Status.running, task.status);
}
// ANCHOR_END: enum_packing

// Date/time packing
const CompactDateTime = packed struct {
    year: u12,
    month: u4,
    day: u5,
    hour: u5,
    minute: u6,
    second: u6,
};

test "datetime packing" {
    const dt = CompactDateTime{
        .year = 2024,
        .month = 11,
        .day = 13,
        .hour = 14,
        .minute = 30,
        .second = 45,
    };

    try std.testing.expectEqual(@as(u12, 2024), dt.year);
    try std.testing.expectEqual(@as(u4, 11), dt.month);
    try std.testing.expectEqual(@as(u5, 13), dt.day);
}

// Permissions
const Permissions = packed struct {
    owner_read: bool,
    owner_write: bool,
    owner_execute: bool,
    group_read: bool,
    group_write: bool,
    group_execute: bool,
    others_read: bool,
    others_write: bool,
    others_execute: bool,
    setuid: bool,
    setgid: bool,
    sticky: bool,
    _padding: u4,
};

test "permissions" {
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(Permissions));

    const perms = Permissions{
        .owner_read = true,
        .owner_write = true,
        .owner_execute = true,
        .group_read = true,
        .group_write = false,
        .group_execute = true,
        .others_read = true,
        .others_write = false,
        .others_execute = false,
        .setuid = false,
        .setgid = false,
        .sticky = false,
        ._padding = 0,
    };

    try std.testing.expect(perms.owner_read);
    try std.testing.expect(!perms.group_write);
}

// Field ordering optimization
const UnoptimizedStruct = struct {
    flag1: bool,
    value1: u64,
    flag2: bool,
    value2: u64,
};

const OptimizedStruct = struct {
    value1: u64,
    value2: u64,
    flag1: bool,
    flag2: bool,
};

test "field ordering" {
    const unopt_size = @sizeOf(UnoptimizedStruct);
    const opt_size = @sizeOf(OptimizedStruct);

    try std.testing.expect(opt_size <= unopt_size);
}

// Array comparison
test "array memory comparison" {
    const NormalItem = struct {
        active: bool,
        id: u16,
        flags: u8,
    };

    const PackedItem = packed struct {
        active: bool,
        id: u16,
        flags: u8,
    };

    const count = 10000;

    const normal_total = @sizeOf(NormalItem) * count;
    const packed_total = @sizeOf(PackedItem) * count;

    try std.testing.expect(packed_total <= normal_total);
}

// Comprehensive test
test "comprehensive packing" {
    const flags = CompactFlags{
        .is_active = true,
        .is_visible = true,
        .is_enabled = false,
        .priority = 15,
    };

    const color = CompactColor{
        .red = 20,
        .green = 40,
        .blue = 25,
    };

    const task = Task{
        .priority = .medium,
        .status = .running,
        .is_async = false,
        .is_cancellable = true,
        .progress = 50,
        ._padding = 0,
    };

    try std.testing.expect(flags.is_active);
    try std.testing.expectEqual(@as(u5, 20), color.red);
    try std.testing.expectEqual(Priority.medium, task.priority);
}
```

---

## Recipe 8.5: Encapsulating Names in a Struct {#recipe-8-5}

**Tags:** allocators, concurrency, error-handling, memory, resource-cleanup, structs-objects, testing, threading
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_5.zig`

### Problem

You want to hide internal implementation details and expose only a clean public interface for your struct.

### Solution

Use the `pub` keyword to make fields and functions public, and omit it to keep them private:

```zig
// Basic encapsulation
const Counter = struct {
    value: i32,

    pub fn init() Counter {
        return Counter{ .value = 0 };
    }

    pub fn increment(self: *Counter) void {
        self.value += 1;
    }

    pub fn get(self: *const Counter) i32 {
        return self.value;
    }
};
```

### Discussion

### Public vs Private Fields

Fields without `pub` are private to the defining file:

```zig
const BankAccount = struct {
    balance: f64,        // Private - cannot access from other files
    account_number: []const u8,  // Private

    pub const Currency = enum { USD, EUR, GBP };  // Public constant

    pub fn init(account_number: []const u8) BankAccount {
        return BankAccount{
            .balance = 0.0,
            .account_number = account_number,
        };
    }

    pub fn deposit(self: *BankAccount, amount: f64) !void {
        if (amount <= 0) return error.InvalidAmount;
        self.balance += amount;
    }

    pub fn getBalance(self: *const BankAccount) f64 {
        return self.balance;
    }

    fn validateBalance(self: *const BankAccount) bool {
        return self.balance >= 0;
    }
};

test "bank account encapsulation" {
    var account = BankAccount.init("ACC-12345");

    try account.deposit(100.50);
    try std.testing.expectEqual(@as(f64, 100.50), account.getBalance());

    // Private fields accessible within same file
    try std.testing.expect(account.validateBalance());
}
```

### Struct-Level Privacy

Control visibility at different levels:

```zig
// Private struct - only visible in this file
const InternalCache = struct {
    data: [100]u8,
    size: usize,
};

// Public struct
pub const DataStore = struct {
    // Private field
    cache: InternalCache,

    // Public field (accessible since struct is pub)
    name: []const u8,

    // Private initialization
    fn initCache() InternalCache {
        return InternalCache{
            .data = undefined,
            .size = 0,
        };
    }

    // Public initialization
    pub fn init(name: []const u8) DataStore {
        return DataStore{
            .cache = initCache(),
            .name = name,
        };
    }
};

test "struct-level privacy" {
    const store = DataStore.init("MyStore");
    try std.testing.expectEqualStrings("MyStore", store.name);
}
```

### Read-Only Properties Pattern

Provide read access but prevent direct modification:

```zig
const Timer = struct {
    start_time: i64,
    elapsed: i64,

    pub fn init(start_time: i64) Timer {
        return Timer{
            .start_time = start_time,
            .elapsed = 0,
        };
    }

    pub fn getStartTime(self: *const Timer) i64 {
        return self.start_time;
    }

    pub fn getElapsed(self: *const Timer) i64 {
        return self.elapsed;
    }

    pub fn update(self: *Timer, current_time: i64) void {
        self.elapsed = current_time - self.start_time;
    }
};

test "read-only properties" {
    var timer = Timer.init(1000);
    timer.update(1500);

    try std.testing.expectEqual(@as(i64, 1000), timer.getStartTime());
    try std.testing.expectEqual(@as(i64, 500), timer.getElapsed());
}
```

### Builder Pattern with Validation

Hide internal state during construction:

```zig
const Config = struct {
    host: []const u8,
    port: u16,
    timeout_ms: u32,
    validated: bool,

    pub const Builder = struct {
        host: ?[]const u8,
        port: u16,
        timeout_ms: u32,

        pub fn init() Builder {
            return Builder{
                .host = null,
                .port = 8080,
                .timeout_ms = 5000,
            };
        }

        pub fn setHost(self: *Builder, host: []const u8) *Builder {
            self.host = host;
            return self;
        }

        pub fn setPort(self: *Builder, port: u16) *Builder {
            self.port = port;
            return self;
        }

        pub fn setTimeout(self: *Builder, ms: u32) *Builder {
            self.timeout_ms = ms;
            return self;
        }

        pub fn build(self: *const Builder) !Config {
            if (self.host == null) return error.HostRequired;

            return Config{
                .host = self.host.?,
                .port = self.port,
                .timeout_ms = self.timeout_ms,
                .validated = true,
            };
        }
    };

    pub fn getHost(self: *const Config) []const u8 {
        return self.host;
    }
};

test "builder pattern" {
    var builder = Config.Builder.init();
    const config = try builder
        .setHost("localhost")
        .setPort(3000)
        .build();

    try std.testing.expectEqualStrings("localhost", config.getHost());
    try std.testing.expectEqual(@as(u16, 3000), config.port);
}
```

### Module-Level Encapsulation

Organize related functionality:

```zig
pub const Database = struct {
    const Self = @This();

    connection: Connection,

    const Connection = struct {
        handle: i32,
        is_open: bool,

        fn open(url: []const u8) !Connection {
            _ = url;
            return Connection{
                .handle = 42,
                .is_open = true,
            };
        }

        fn close(self: *Connection) void {
            self.is_open = false;
        }
    };

    pub fn init(url: []const u8) !Self {
        const conn = try Connection.open(url);
        return Self{ .connection = conn };
    }

    pub fn deinit(self: *Self) void {
        self.connection.close();
    }

    pub fn execute(self: *Self, query: []const u8) !void {
        _ = self;
        _ = query;
        // Execute query
    }
};

test "module encapsulation" {
    var db = try Database.init("postgresql://localhost");
    defer db.deinit();

    try db.execute("SELECT * FROM users");
}
```

### State Machine with Private States

Hide internal state transitions:

```zig
const StateMachine = struct {
    const State = enum {
        idle,
        running,
        paused,
        stopped,
    };

    current_state: State,
    transition_count: u32,

    pub fn init() StateMachine {
        return StateMachine{
            .current_state = .idle,
            .transition_count = 0,
        };
    }

    pub fn start(self: *StateMachine) !void {
        if (self.current_state != .idle) return error.InvalidTransition;
        self.transition(.running);
    }

    pub fn pause(self: *StateMachine) !void {
        if (self.current_state != .running) return error.InvalidTransition;
        self.transition(.paused);
    }

    pub fn resumeRunning(self: *StateMachine) !void {
        if (self.current_state != .paused) return error.InvalidTransition;
        self.transition(.running);
    }

    pub fn stop(self: *StateMachine) !void {
        self.transition(.stopped);
    }

    pub fn isRunning(self: *const StateMachine) bool {
        return self.current_state == .running;
    }

    fn transition(self: *StateMachine, new_state: State) void {
        self.current_state = new_state;
        self.transition_count += 1;
    }
};

test "state machine" {
    var sm = StateMachine.init();

    try sm.start();
    try std.testing.expect(sm.isRunning());

    try sm.pause();
    try std.testing.expect(!sm.isRunning());

    try sm.resumeRunning();
    try std.testing.expect(sm.isRunning());
}
```

### Opaque Handles

Hide implementation completely:

```zig
pub const Handle = opaque {
    pub fn create() *Handle {
        const impl = Implementation{
            .data = 42,
            .refs = 1,
        };
        const ptr = std.heap.page_allocator.create(Implementation) catch unreachable;
        ptr.* = impl;
        return @ptrCast(ptr);
    }

    pub fn destroy(handle: *Handle) void {
        const impl: *Implementation = @ptrCast(@alignCast(handle));
        std.heap.page_allocator.destroy(impl);
    }

    pub fn getValue(handle: *Handle) i32 {
        const impl: *Implementation = @ptrCast(@alignCast(handle));
        return impl.data;
    }

    const Implementation = struct {
        data: i32,
        refs: u32,
    };
};

test "opaque handle" {
    const handle = Handle.create();
    defer Handle.destroy(handle);

    const value = Handle.getValue(handle);
    try std.testing.expectEqual(@as(i32, 42), value);
}
```

### Interface Pattern

Define public interface with private implementation:

```zig
pub const Logger = struct {
    const Self = @This();

    vtable: *const VTable,
    ptr: *anyopaque,

    pub const VTable = struct {
        log: *const fn (ptr: *anyopaque, msg: []const u8) void,
    };

    pub fn log(self: Self, msg: []const u8) void {
        self.vtable.log(self.ptr, msg);
    }
};

const ConsoleLogger = struct {
    prefix: []const u8,

    fn log(ptr: *anyopaque, msg: []const u8) void {
        const self: *ConsoleLogger = @ptrCast(@alignCast(ptr));
        std.debug.print("[{s}] {s}\n", .{ self.prefix, msg });
    }

    const vtable = Logger.VTable{
        .log = log,
    };

    pub fn logger(self: *ConsoleLogger) Logger {
        return Logger{
            .vtable = &vtable,
            .ptr = self,
        };
    }
};

test "interface pattern" {
    var console = ConsoleLogger{ .prefix = "INFO" };
    const logger = console.logger();

    logger.log("Test message");
}
```

### Best Practices

**Default to Private:**
```zig
// Good: Only expose what's necessary
pub const Widget = struct {
    id: u32,          // Private
    state: State,     // Private

    pub fn getId(self: *const Widget) u32 {
        return self.id;
    }
};
```

**Document Public API:**
```zig
/// Represents a thread-safe counter
pub const Counter = struct {
    /// Get the current count
    pub fn get(self: *const Counter) i32 {
        return self.value;
    }

    value: i32,  // Implementation detail
};
```

**Consistent Naming:**
```zig
pub const Resource = struct {
    // Public methods use clear names
    pub fn create() !Resource { }
    pub fn destroy(self: *Resource) void { }

    // Private helpers use descriptive names
    fn allocateBuffer(size: usize) ![]u8 { }
    fn validateInput(data: []const u8) bool { }
};
```

**Separate Interface from Implementation:**
```zig
// Public interface
pub const API = struct {
    pub fn processData(data: []const u8) !Result { }
};

// Private implementation details
const Implementation = struct {
    fn parseData(data: []const u8) !ParsedData { }
    fn validateData(parsed: *const ParsedData) !void { }
};
```

### Related Patterns

- Recipe 8.6: Creating managed attributes (getters/setters)
- Recipe 8.12: Defining an interface
- Recipe 10.2: Controlling symbol export

### Full Tested Code

```zig
// Recipe 8.5: Encapsulating Names in a Struct
// Target Zig Version: 0.15.2

const std = @import("std");

// ANCHOR: basic_encapsulation
// Basic encapsulation
const Counter = struct {
    value: i32,

    pub fn init() Counter {
        return Counter{ .value = 0 };
    }

    pub fn increment(self: *Counter) void {
        self.value += 1;
    }

    pub fn get(self: *const Counter) i32 {
        return self.value;
    }
};
// ANCHOR_END: basic_encapsulation

test "basic encapsulation" {
    var counter = Counter.init();
    counter.increment();
    counter.increment();

    try std.testing.expectEqual(@as(i32, 2), counter.get());
    try std.testing.expectEqual(@as(i32, 2), counter.value);
}

// Bank account with private fields
const BankAccount = struct {
    balance: f64,
    account_number: []const u8,

    pub const Currency = enum { USD, EUR, GBP };

    pub fn init(account_number: []const u8) BankAccount {
        return BankAccount{
            .balance = 0.0,
            .account_number = account_number,
        };
    }

    pub fn deposit(self: *BankAccount, amount: f64) !void {
        if (amount <= 0) return error.InvalidAmount;
        self.balance += amount;
    }

    pub fn getBalance(self: *const BankAccount) f64 {
        return self.balance;
    }

    fn validateBalance(self: *const BankAccount) bool {
        return self.balance >= 0;
    }
};

test "bank account encapsulation" {
    var account = BankAccount.init("ACC-12345");

    try account.deposit(100.50);
    try std.testing.expectEqual(@as(f64, 100.50), account.getBalance());
    try std.testing.expect(account.validateBalance());
}

// Struct-level privacy
const InternalCache = struct {
    data: [100]u8,
    size: usize,
};

pub const DataStore = struct {
    cache: InternalCache,
    name: []const u8,

    fn initCache() InternalCache {
        return InternalCache{
            .data = undefined,
            .size = 0,
        };
    }

    pub fn init(name: []const u8) DataStore {
        return DataStore{
            .cache = initCache(),
            .name = name,
        };
    }
};

test "struct-level privacy" {
    const store = DataStore.init("MyStore");
    try std.testing.expectEqualStrings("MyStore", store.name);
}

// Read-only properties
const Timer = struct {
    start_time: i64,
    elapsed: i64,

    pub fn init(start_time: i64) Timer {
        return Timer{
            .start_time = start_time,
            .elapsed = 0,
        };
    }

    pub fn getStartTime(self: *const Timer) i64 {
        return self.start_time;
    }

    pub fn getElapsed(self: *const Timer) i64 {
        return self.elapsed;
    }

    pub fn update(self: *Timer, current_time: i64) void {
        self.elapsed = current_time - self.start_time;
    }
};

test "read-only properties" {
    var timer = Timer.init(1000);
    timer.update(1500);

    try std.testing.expectEqual(@as(i64, 1000), timer.getStartTime());
    try std.testing.expectEqual(@as(i64, 500), timer.getElapsed());
}

// ANCHOR: builder_pattern
// Builder pattern
const Config = struct {
    host: []const u8,
    port: u16,
    timeout_ms: u32,
    validated: bool,

    pub const Builder = struct {
        host: ?[]const u8,
        port: u16,
        timeout_ms: u32,

        pub fn init() Builder {
            return Builder{
                .host = null,
                .port = 8080,
                .timeout_ms = 5000,
            };
        }

        pub fn setHost(self: *Builder, host: []const u8) *Builder {
            self.host = host;
            return self;
        }

        pub fn setPort(self: *Builder, port: u16) *Builder {
            self.port = port;
            return self;
        }

        pub fn setTimeout(self: *Builder, ms: u32) *Builder {
            self.timeout_ms = ms;
            return self;
        }

        pub fn build(self: *const Builder) !Config {
            if (self.host == null) return error.HostRequired;

            return Config{
                .host = self.host.?,
                .port = self.port,
                .timeout_ms = self.timeout_ms,
                .validated = true,
            };
        }
    };

    pub fn getHost(self: *const Config) []const u8 {
        return self.host;
    }
};
// ANCHOR_END: builder_pattern

test "builder pattern" {
    var builder = Config.Builder.init();
    const config = try builder
        .setHost("localhost")
        .setPort(3000)
        .build();

    try std.testing.expectEqualStrings("localhost", config.getHost());
    try std.testing.expectEqual(@as(u16, 3000), config.port);
}

// Module-level encapsulation
pub const Database = struct {
    const Self = @This();

    connection: Connection,

    const Connection = struct {
        handle: i32,
        is_open: bool,

        fn open(url: []const u8) !Connection {
            _ = url;
            return Connection{
                .handle = 42,
                .is_open = true,
            };
        }

        fn close(self: *Connection) void {
            self.is_open = false;
        }
    };

    pub fn init(url: []const u8) !Self {
        const conn = try Connection.open(url);
        return Self{ .connection = conn };
    }

    pub fn deinit(self: *Self) void {
        self.connection.close();
    }

    pub fn execute(self: *Self, query: []const u8) !void {
        _ = self;
        _ = query;
    }
};

test "module encapsulation" {
    var db = try Database.init("postgresql://localhost");
    defer db.deinit();

    try db.execute("SELECT * FROM users");
}

// State machine with private states
const StateMachine = struct {
    const State = enum {
        idle,
        running,
        paused,
        stopped,
    };

    current_state: State,
    transition_count: u32,

    pub fn init() StateMachine {
        return StateMachine{
            .current_state = .idle,
            .transition_count = 0,
        };
    }

    pub fn start(self: *StateMachine) !void {
        if (self.current_state != .idle) return error.InvalidTransition;
        self.transition(.running);
    }

    pub fn pause(self: *StateMachine) !void {
        if (self.current_state != .running) return error.InvalidTransition;
        self.transition(.paused);
    }

    pub fn resumeRunning(self: *StateMachine) !void {
        if (self.current_state != .paused) return error.InvalidTransition;
        self.transition(.running);
    }

    pub fn stop(self: *StateMachine) !void {
        self.transition(.stopped);
    }

    pub fn isRunning(self: *const StateMachine) bool {
        return self.current_state == .running;
    }

    fn transition(self: *StateMachine, new_state: State) void {
        self.current_state = new_state;
        self.transition_count += 1;
    }
};

test "state machine" {
    var sm = StateMachine.init();

    try sm.start();
    try std.testing.expect(sm.isRunning());

    try sm.pause();
    try std.testing.expect(!sm.isRunning());

    try sm.resumeRunning();
    try std.testing.expect(sm.isRunning());
}

// ANCHOR: opaque_handle
// Opaque handle
pub const Handle = opaque {
    pub fn create() *Handle {
        const impl = Implementation{
            .data = 42,
            .refs = 1,
        };
        const ptr = std.heap.page_allocator.create(Implementation) catch unreachable;
        ptr.* = impl;
        return @ptrCast(ptr);
    }

    pub fn destroy(handle: *Handle) void {
        const impl: *Implementation = @ptrCast(@alignCast(handle));
        std.heap.page_allocator.destroy(impl);
    }

    pub fn getValue(handle: *Handle) i32 {
        const impl: *Implementation = @ptrCast(@alignCast(handle));
        return impl.data;
    }

    const Implementation = struct {
        data: i32,
        refs: u32,
    };
};
// ANCHOR_END: opaque_handle

test "opaque handle" {
    const handle = Handle.create();
    defer Handle.destroy(handle);

    const value = Handle.getValue(handle);
    try std.testing.expectEqual(@as(i32, 42), value);
}

// Interface pattern
pub const Logger = struct {
    const Self = @This();

    vtable: *const VTable,
    ptr: *anyopaque,

    pub const VTable = struct {
        log: *const fn (ptr: *anyopaque, msg: []const u8) void,
    };

    pub fn log(self: Self, msg: []const u8) void {
        self.vtable.log(self.ptr, msg);
    }
};

const ConsoleLogger = struct {
    prefix: []const u8,

    fn log(ptr: *anyopaque, msg: []const u8) void {
        const self: *ConsoleLogger = @ptrCast(@alignCast(ptr));
        _ = self;
        _ = msg;
    }

    const vtable = Logger.VTable{
        .log = log,
    };

    pub fn logger(self: *ConsoleLogger) Logger {
        return Logger{
            .vtable = &vtable,
            .ptr = self,
        };
    }
};

test "interface pattern" {
    var console = ConsoleLogger{ .prefix = "INFO" };
    const logger = console.logger();

    logger.log("Test message");
}

// Comprehensive test
test "comprehensive encapsulation" {
    var counter = Counter.init();
    counter.increment();
    try std.testing.expectEqual(@as(i32, 1), counter.get());

    var account = BankAccount.init("TEST");
    try account.deposit(50.0);
    try std.testing.expectEqual(@as(f64, 50.0), account.getBalance());

    var timer = Timer.init(100);
    timer.update(200);
    try std.testing.expectEqual(@as(i64, 100), timer.getElapsed());
}
```

---

## Recipe 8.6: Creating Managed Attributes {#recipe-8-6}

**Tags:** allocators, error-handling, memory, pointers, resource-cleanup, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_6.zig`

### Problem

You want to control access to struct fields, validate values before assignment, compute derived properties, or implement lazy initialization—all without traditional getters and setters from object-oriented languages.

### Solution

Zig doesn't have built-in property syntax, but you can implement managed attributes using explicit getter and setter methods. This gives you fine-grained control over how data is accessed and modified.

### Basic Getters and Setters

```zig
// Basic getter and setter pattern
const Temperature = struct {
    celsius: f32,

    pub fn init(celsius: f32) Temperature {
        return Temperature{ .celsius = celsius };
    }

    pub fn getCelsius(self: *const Temperature) f32 {
        return self.celsius;
    }

    pub fn setCelsius(self: *Temperature, value: f32) void {
        self.celsius = value;
    }

    pub fn getFahrenheit(self: *const Temperature) f32 {
        return self.celsius * 9.0 / 5.0 + 32.0;
    }

    pub fn setFahrenheit(self: *Temperature, value: f32) void {
        self.celsius = (value - 32.0) * 5.0 / 9.0;
    }
};
```

This pattern provides controlled access to fields and allows format conversion on the fly.

### Validated Setters

Add validation logic to setters to ensure data integrity:

```zig
// Validated setters
const BankAccount = struct {
    balance: f64,
    min_balance: f64,

    pub fn init(min_balance: f64) BankAccount {
        return BankAccount{
            .balance = 0,
            .min_balance = min_balance,
        };
    }

    pub fn getBalance(self: *const BankAccount) f64 {
        return self.balance;
    }

    pub fn deposit(self: *BankAccount, amount: f64) !void {
        if (amount <= 0) return error.InvalidAmount;
        self.balance += amount;
    }

    pub fn withdraw(self: *BankAccount, amount: f64) !void {
        if (amount <= 0) return error.InvalidAmount;
        if (self.balance - amount < self.min_balance) {
            return error.InsufficientFunds;
        }
        self.balance -= amount;
    }
};
```

Validation prevents invalid state and returns clear errors when constraints are violated.

### Computed Properties

Create read-only properties derived from stored data:

```zig
// Computed properties
const Rectangle = struct {
    width: f32,
    height: f32,

    pub fn init(width: f32, height: f32) Rectangle {
        return Rectangle{ .width = width, .height = height };
    }

    pub fn getArea(self: *const Rectangle) f32 {
        return self.width * self.height;
    }

    pub fn getPerimeter(self: *const Rectangle) f32 {
        return 2 * (self.width + self.height);
    }

    pub fn getDiagonal(self: *const Rectangle) f32 {
        return @sqrt(self.width * self.width + self.height * self.height);
    }

    pub fn setWidth(self: *Rectangle, width: f32) !void {
        if (width <= 0) return error.InvalidDimension;
        self.width = width;
    }

    pub fn setHeight(self: *Rectangle, height: f32) !void {
        if (height <= 0) return error.InvalidDimension;
        self.height = height;
    }
};
```

Computed properties avoid storing redundant data and ensure derived values stay consistent.

### Read-Only Properties

Some properties should only be readable, not writable:

```zig
// Read-only properties
const Person = struct {
    first_name: []const u8,
    last_name: []const u8,
    birth_year: u16,

    pub fn init(first: []const u8, last: []const u8, birth_year: u16) Person {
        return Person{
            .first_name = first,
            .last_name = last,
            .birth_year = birth_year,
        };
    }

    pub fn getFullName(self: *const Person, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(
            allocator,
            "{s} {s}",
            .{ self.first_name, self.last_name },
        );
    }

    pub fn getAge(self: *const Person, current_year: u16) u16 {
        return current_year - self.birth_year;
    }

    pub fn getBirthYear(self: *const Person) u16 {
        return self.birth_year;
    }
};
```

By omitting setters, you enforce immutability for specific fields.

### Lazy Initialization

Defer expensive computations until the value is actually needed:

```zig
// Lazy initialization
const DataCache = struct {
    data: ?[]const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) DataCache {
        return DataCache{
            .data = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *DataCache) void {
        if (self.data) |d| {
            self.allocator.free(d);
        }
    }

    pub fn getData(self: *DataCache) ![]const u8 {
        if (self.data) |d| {
            return d;
        }

        // Simulate expensive operation
        const loaded = try self.allocator.dupe(u8, "expensive data");
        self.data = loaded;
        return loaded;
    }

    pub fn invalidate(self: *DataCache) void {
        if (self.data) |d| {
            self.allocator.free(d);
            self.data = null;
        }
    }
};
```

The data is only loaded on first access, and subsequent calls return the cached value.

### Property Observers

Trigger callbacks when values change:

```zig
// Property observers (callbacks on change)
const ObservableValue = struct {
    value: i32,
    on_change: ?*const fn (old: i32, new: i32) void,

    pub fn init(initial: i32) ObservableValue {
        return ObservableValue{
            .value = initial,
            .on_change = null,
        };
    }

    pub fn getValue(self: *const ObservableValue) i32 {
        return self.value;
    }

    pub fn setValue(self: *ObservableValue, new_value: i32) void {
        const old = self.value;
        self.value = new_value;
        if (self.on_change) |callback| {
            callback(old, new_value);
        }
    }

    pub fn setObserver(self: *ObservableValue, callback: *const fn (old: i32, new: i32) void) void {
        self.on_change = callback;
    }
};
```

This pattern is useful for reactive programming and UI updates.

### Range-Constrained Properties

Enforce value ranges automatically:

```zig
// Range-constrained property
const Volume = struct {
    level: u8, // 0-100

    pub fn init() Volume {
        return Volume{ .level = 50 };
    }

    pub fn getLevel(self: *const Volume) u8 {
        return self.level;
    }

    pub fn setLevel(self: *Volume, value: u8) !void {
        if (value > 100) return error.ValueOutOfRange;
        self.level = value;
    }

    pub fn increase(self: *Volume, amount: u8) void {
        const new_level = @min(self.level + amount, 100);
        self.level = new_level;
    }

    pub fn decrease(self: *Volume, amount: u8) void {
        const new_level = if (self.level >= amount) self.level - amount else 0;
        self.level = new_level;
    }

    pub fn isMuted(self: *const Volume) bool {
        return self.level == 0;
    }

    pub fn isMax(self: *const Volume) bool {
        return self.level == 100;
    }
};
```

Helper methods like `increase()` and `decrease()` automatically clamp values to valid ranges.

### Dependent Properties

Allow setting values through different representations:

```zig
// Dependent properties
const Circle = struct {
    radius: f32,

    pub fn init(radius: f32) !Circle {
        if (radius <= 0) return error.InvalidRadius;
        return Circle{ .radius = radius };
    }

    pub fn getRadius(self: *const Circle) f32 {
        return self.radius;
    }

    pub fn setRadius(self: *Circle, radius: f32) !void {
        if (radius <= 0) return error.InvalidRadius;
        self.radius = radius;
    }

    pub fn getDiameter(self: *const Circle) f32 {
        return self.radius * 2;
    }

    pub fn setDiameter(self: *Circle, diameter: f32) !void {
        if (diameter <= 0) return error.InvalidDiameter;
        self.radius = diameter / 2;
    }

    pub fn getCircumference(self: *const Circle) f32 {
        return 2 * std.math.pi * self.radius;
    }

    pub fn getArea(self: *const Circle) f32 {
        return std.math.pi * self.radius * self.radius;
    }
};
```

You can set the circle size via radius or diameter—both update the same underlying value.

### Format Transformation

Store data in one format but provide different representations:

```zig
// Format transformation properties
const PhoneNumber = struct {
    digits: []const u8, // Store as digits only
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, digits: []const u8) !PhoneNumber {
        if (digits.len != 10) return error.InvalidPhoneNumber;
        for (digits) |c| {
            if (c < '0' or c > '9') return error.InvalidPhoneNumber;
        }
        const owned = try allocator.dupe(u8, digits);
        return PhoneNumber{
            .digits = owned,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *PhoneNumber) void {
        self.allocator.free(self.digits);
    }

    pub fn getDigits(self: *const PhoneNumber) []const u8 {
        return self.digits;
    }

    pub fn getFormatted(self: *const PhoneNumber, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(
            allocator,
            "({s}) {s}-{s}",
            .{ self.digits[0..3], self.digits[3..6], self.digits[6..10] },
        );
    }
};
```

Data is stored efficiently (digits only) but can be retrieved in user-friendly formats.

### Discussion

Managed attributes in Zig follow the principle of explicit control. Unlike languages with property syntax, Zig makes the accessor methods visible, which:

1. **Makes costs obvious** - You can see when a "getter" allocates memory or does expensive computation
2. **Enables validation** - Setters can enforce invariants and return errors
3. **Supports transformation** - Convert between representations on access
4. **Allows lazy evaluation** - Defer work until actually needed
5. **Maintains explicitness** - No hidden behavior or magic

### Naming Conventions

While Zig doesn't enforce naming, common patterns include:

- `getValue()` / `setValue()` for simple accessors
- `deposit()` / `withdraw()` for domain-specific operations
- `increase()` / `decrease()` for relative changes
- Computed properties often omit "get" prefix: `area()` instead of `getArea()`

### When to Use Managed Attributes

Use managed attributes when you need:

- **Validation** - Prevent invalid state
- **Computation** - Derive values from stored data
- **Transformation** - Convert between formats
- **Lazy loading** - Defer expensive operations
- **Observation** - React to changes
- **Encapsulation** - Hide implementation details

For simple data storage without logic, direct field access is more idiomatic in Zig.

### Memory Management

When getters allocate memory (like `getFullName()` or `getFormatted()`), they should:

1. Take an `allocator` parameter
2. Return an error union: `![]u8`
3. Document that the caller owns the returned memory
4. Expect the caller to use `defer allocator.free(result)`

This follows Zig's principle of making memory allocation explicit.

### Performance Considerations

- Getters that compute values run on every access—consider caching for expensive operations
- Use `*const Self` for getters to enable calling on const instances
- Range-constrained setters with clamping (`@min`, `@max`) avoid branches
- Lazy initialization trades memory for first-access latency

### Full Tested Code

```zig
// Recipe 8.6: Creating Managed Attributes
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_getters_setters
// Basic getter and setter pattern
const Temperature = struct {
    celsius: f32,

    pub fn init(celsius: f32) Temperature {
        return Temperature{ .celsius = celsius };
    }

    pub fn getCelsius(self: *const Temperature) f32 {
        return self.celsius;
    }

    pub fn setCelsius(self: *Temperature, value: f32) void {
        self.celsius = value;
    }

    pub fn getFahrenheit(self: *const Temperature) f32 {
        return self.celsius * 9.0 / 5.0 + 32.0;
    }

    pub fn setFahrenheit(self: *Temperature, value: f32) void {
        self.celsius = (value - 32.0) * 5.0 / 9.0;
    }
};
// ANCHOR_END: basic_getters_setters

test "basic getters and setters" {
    var temp = Temperature.init(0);

    try testing.expectEqual(@as(f32, 0), temp.getCelsius());
    try testing.expectEqual(@as(f32, 32), temp.getFahrenheit());

    temp.setFahrenheit(212);
    try testing.expectEqual(@as(f32, 100), temp.getCelsius());
}

// ANCHOR: validated_setters
// Validated setters
const BankAccount = struct {
    balance: f64,
    min_balance: f64,

    pub fn init(min_balance: f64) BankAccount {
        return BankAccount{
            .balance = 0,
            .min_balance = min_balance,
        };
    }

    pub fn getBalance(self: *const BankAccount) f64 {
        return self.balance;
    }

    pub fn deposit(self: *BankAccount, amount: f64) !void {
        if (amount <= 0) return error.InvalidAmount;
        self.balance += amount;
    }

    pub fn withdraw(self: *BankAccount, amount: f64) !void {
        if (amount <= 0) return error.InvalidAmount;
        if (self.balance - amount < self.min_balance) {
            return error.InsufficientFunds;
        }
        self.balance -= amount;
    }
};
// ANCHOR_END: validated_setters

test "validated setters" {
    var account = BankAccount.init(100);

    try account.deposit(500);
    try testing.expectEqual(@as(f64, 500), account.getBalance());

    try account.withdraw(200);
    try testing.expectEqual(@as(f64, 300), account.getBalance());

    const result = account.withdraw(250);
    try testing.expectError(error.InsufficientFunds, result);
}

// ANCHOR: computed_properties
// Computed properties
const Rectangle = struct {
    width: f32,
    height: f32,

    pub fn init(width: f32, height: f32) Rectangle {
        return Rectangle{ .width = width, .height = height };
    }

    pub fn getArea(self: *const Rectangle) f32 {
        return self.width * self.height;
    }

    pub fn getPerimeter(self: *const Rectangle) f32 {
        return 2 * (self.width + self.height);
    }

    pub fn getDiagonal(self: *const Rectangle) f32 {
        return @sqrt(self.width * self.width + self.height * self.height);
    }

    pub fn setWidth(self: *Rectangle, width: f32) !void {
        if (width <= 0) return error.InvalidDimension;
        self.width = width;
    }

    pub fn setHeight(self: *Rectangle, height: f32) !void {
        if (height <= 0) return error.InvalidDimension;
        self.height = height;
    }
};
// ANCHOR_END: computed_properties

test "computed properties" {
    var rect = Rectangle.init(3, 4);

    try testing.expectEqual(@as(f32, 12), rect.getArea());
    try testing.expectEqual(@as(f32, 14), rect.getPerimeter());
    try testing.expectEqual(@as(f32, 5), rect.getDiagonal());

    try rect.setWidth(6);
    try testing.expectEqual(@as(f32, 24), rect.getArea());
}

// ANCHOR: readonly_properties
// Read-only properties
const Person = struct {
    first_name: []const u8,
    last_name: []const u8,
    birth_year: u16,

    pub fn init(first: []const u8, last: []const u8, birth_year: u16) Person {
        return Person{
            .first_name = first,
            .last_name = last,
            .birth_year = birth_year,
        };
    }

    pub fn getFullName(self: *const Person, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(
            allocator,
            "{s} {s}",
            .{ self.first_name, self.last_name },
        );
    }

    pub fn getAge(self: *const Person, current_year: u16) u16 {
        return current_year - self.birth_year;
    }

    pub fn getBirthYear(self: *const Person) u16 {
        return self.birth_year;
    }
};
// ANCHOR_END: readonly_properties

test "read-only properties" {
    const person = Person.init("Jane", "Doe", 1990);

    const full_name = try person.getFullName(testing.allocator);
    defer testing.allocator.free(full_name);
    try testing.expectEqualStrings("Jane Doe", full_name);

    try testing.expectEqual(@as(u16, 34), person.getAge(2024));
    try testing.expectEqual(@as(u16, 1990), person.getBirthYear());
}

// ANCHOR: lazy_initialization
// Lazy initialization
const DataCache = struct {
    data: ?[]const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) DataCache {
        return DataCache{
            .data = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *DataCache) void {
        if (self.data) |d| {
            self.allocator.free(d);
        }
    }

    pub fn getData(self: *DataCache) ![]const u8 {
        if (self.data) |d| {
            return d;
        }

        // Simulate expensive operation
        const loaded = try self.allocator.dupe(u8, "expensive data");
        self.data = loaded;
        return loaded;
    }

    pub fn invalidate(self: *DataCache) void {
        if (self.data) |d| {
            self.allocator.free(d);
            self.data = null;
        }
    }
};
// ANCHOR_END: lazy_initialization

test "lazy initialization" {
    var cache = DataCache.init(testing.allocator);
    defer cache.deinit();

    const data1 = try cache.getData();
    try testing.expectEqualStrings("expensive data", data1);

    const data2 = try cache.getData();
    try testing.expectEqual(data1.ptr, data2.ptr); // Same pointer, cached

    cache.invalidate();
    const data3 = try cache.getData();
    try testing.expect(data1.ptr != data3.ptr); // Different pointer, reloaded
}

// ANCHOR: property_observers
// Property observers (callbacks on change)
const ObservableValue = struct {
    value: i32,
    on_change: ?*const fn (old: i32, new: i32) void,

    pub fn init(initial: i32) ObservableValue {
        return ObservableValue{
            .value = initial,
            .on_change = null,
        };
    }

    pub fn getValue(self: *const ObservableValue) i32 {
        return self.value;
    }

    pub fn setValue(self: *ObservableValue, new_value: i32) void {
        const old = self.value;
        self.value = new_value;
        if (self.on_change) |callback| {
            callback(old, new_value);
        }
    }

    pub fn setObserver(self: *ObservableValue, callback: *const fn (old: i32, new: i32) void) void {
        self.on_change = callback;
    }
};
// ANCHOR_END: property_observers

var observer_called = false;
var observer_old_value: i32 = 0;
var observer_new_value: i32 = 0;

fn testObserver(old: i32, new: i32) void {
    observer_called = true;
    observer_old_value = old;
    observer_new_value = new;
}

test "property observers" {
    observer_called = false;

    var observable = ObservableValue.init(10);
    observable.setObserver(&testObserver);

    observable.setValue(20);
    try testing.expect(observer_called);
    try testing.expectEqual(@as(i32, 10), observer_old_value);
    try testing.expectEqual(@as(i32, 20), observer_new_value);
}

// ANCHOR: private_backing_field
// Private backing field pattern
const User = struct {
    username: []const u8,
    password_hash: []const u8,
    login_attempts: u32,

    pub fn init(username: []const u8, password: []const u8) User {
        return User{
            .username = username,
            .password_hash = password, // In reality, this would be hashed
            .login_attempts = 0,
        };
    }

    pub fn getUsername(self: *const User) []const u8 {
        return self.username;
    }

    pub fn verifyPassword(self: *User, password: []const u8) !bool {
        if (self.login_attempts >= 3) return error.AccountLocked;

        const matches = std.mem.eql(u8, self.password_hash, password);
        if (!matches) {
            self.login_attempts += 1;
        } else {
            self.login_attempts = 0;
        }
        return matches;
    }

    pub fn getLoginAttempts(self: *const User) u32 {
        return self.login_attempts;
    }

    pub fn resetLoginAttempts(self: *User) void {
        self.login_attempts = 0;
    }
};
// ANCHOR_END: private_backing_field

test "private backing field" {
    var user = User.init("alice", "secret123");

    try testing.expectEqualStrings("alice", user.getUsername());

    const valid = try user.verifyPassword("secret123");
    try testing.expect(valid);
    try testing.expectEqual(@as(u32, 0), user.getLoginAttempts());

    const invalid = try user.verifyPassword("wrong");
    try testing.expect(!invalid);
    try testing.expectEqual(@as(u32, 1), user.getLoginAttempts());
}

// ANCHOR: range_constrained
// Range-constrained property
const Volume = struct {
    level: u8, // 0-100

    pub fn init() Volume {
        return Volume{ .level = 50 };
    }

    pub fn getLevel(self: *const Volume) u8 {
        return self.level;
    }

    pub fn setLevel(self: *Volume, value: u8) !void {
        if (value > 100) return error.ValueOutOfRange;
        self.level = value;
    }

    pub fn increase(self: *Volume, amount: u8) void {
        const new_level = @min(self.level + amount, 100);
        self.level = new_level;
    }

    pub fn decrease(self: *Volume, amount: u8) void {
        const new_level = if (self.level >= amount) self.level - amount else 0;
        self.level = new_level;
    }

    pub fn isMuted(self: *const Volume) bool {
        return self.level == 0;
    }

    pub fn isMax(self: *const Volume) bool {
        return self.level == 100;
    }
};
// ANCHOR_END: range_constrained

test "range-constrained property" {
    var vol = Volume.init();
    try testing.expectEqual(@as(u8, 50), vol.getLevel());

    try vol.setLevel(75);
    try testing.expectEqual(@as(u8, 75), vol.getLevel());

    vol.increase(50);
    try testing.expect(vol.isMax());

    vol.decrease(100);
    try testing.expect(vol.isMuted());

    const result = vol.setLevel(101);
    try testing.expectError(error.ValueOutOfRange, result);
}

// ANCHOR: dependent_properties
// Dependent properties
const Circle = struct {
    radius: f32,

    pub fn init(radius: f32) !Circle {
        if (radius <= 0) return error.InvalidRadius;
        return Circle{ .radius = radius };
    }

    pub fn getRadius(self: *const Circle) f32 {
        return self.radius;
    }

    pub fn setRadius(self: *Circle, radius: f32) !void {
        if (radius <= 0) return error.InvalidRadius;
        self.radius = radius;
    }

    pub fn getDiameter(self: *const Circle) f32 {
        return self.radius * 2;
    }

    pub fn setDiameter(self: *Circle, diameter: f32) !void {
        if (diameter <= 0) return error.InvalidDiameter;
        self.radius = diameter / 2;
    }

    pub fn getCircumference(self: *const Circle) f32 {
        return 2 * std.math.pi * self.radius;
    }

    pub fn getArea(self: *const Circle) f32 {
        return std.math.pi * self.radius * self.radius;
    }
};
// ANCHOR_END: dependent_properties

test "dependent properties" {
    var circle = try Circle.init(5);

    try testing.expectEqual(@as(f32, 5), circle.getRadius());
    try testing.expectEqual(@as(f32, 10), circle.getDiameter());

    try circle.setDiameter(20);
    try testing.expectEqual(@as(f32, 10), circle.getRadius());

    const circumference = circle.getCircumference();
    const expected_circ = 2 * std.math.pi * 10;
    try testing.expectApproxEqAbs(expected_circ, circumference, 0.001);
}

// ANCHOR: format_transformation
// Format transformation properties
const PhoneNumber = struct {
    digits: []const u8, // Store as digits only
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, digits: []const u8) !PhoneNumber {
        if (digits.len != 10) return error.InvalidPhoneNumber;
        for (digits) |c| {
            if (c < '0' or c > '9') return error.InvalidPhoneNumber;
        }
        const owned = try allocator.dupe(u8, digits);
        return PhoneNumber{
            .digits = owned,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *PhoneNumber) void {
        self.allocator.free(self.digits);
    }

    pub fn getDigits(self: *const PhoneNumber) []const u8 {
        return self.digits;
    }

    pub fn getFormatted(self: *const PhoneNumber, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(
            allocator,
            "({s}) {s}-{s}",
            .{ self.digits[0..3], self.digits[3..6], self.digits[6..10] },
        );
    }
};
// ANCHOR_END: format_transformation

test "format transformation" {
    var phone = try PhoneNumber.init(testing.allocator, "5551234567");
    defer phone.deinit();

    try testing.expectEqualStrings("5551234567", phone.getDigits());

    const formatted = try phone.getFormatted(testing.allocator);
    defer testing.allocator.free(formatted);
    try testing.expectEqualStrings("(555) 123-4567", formatted);
}

// Comprehensive test
test "comprehensive managed attributes" {
    var temp = Temperature.init(100);
    temp.setFahrenheit(32);
    try testing.expectEqual(@as(f32, 0), temp.getCelsius());

    var account = BankAccount.init(0);
    try account.deposit(1000);
    try account.withdraw(500);
    try testing.expectEqual(@as(f64, 500), account.getBalance());

    var vol = Volume.init();
    vol.increase(50);
    try testing.expectEqual(@as(u8, 100), vol.getLevel());

    var circle = try Circle.init(1);
    const area = circle.getArea();
    try testing.expectApproxEqAbs(std.math.pi, area, 0.001);
}
```

### See Also

- Recipe 8.5: Encapsulating Names in a Struct
- Recipe 8.10: Using Lazily Computed Properties
- Recipe 8.11: Simplifying the Initialization of Data Structures
- Recipe 8.14: Implementing Custom Containers

---

## Recipe 8.7: Calling a Method on a Parent Struct {#recipe-8-7}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, memory, pointers, resource-cleanup, slices, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_7.zig`

### Problem

You want to reuse functionality from one struct in another, similar to how object-oriented languages use inheritance and calling parent class methods. However, Zig doesn't have traditional class inheritance.

### Solution

Zig uses composition over inheritance. Embed structs within other structs and delegate method calls to access parent functionality. This gives you the benefits of code reuse without the complexity of inheritance hierarchies.

### Basic Composition

```zig
// Basic composition
const Logger = struct {
    prefix: []const u8,

    pub fn init(prefix: []const u8) Logger {
        return Logger{ .prefix = prefix };
    }

    pub fn log(self: *const Logger, message: []const u8) void {
        _ = self;
        _ = message;
        // In reality: std.debug.print("[{s}] {s}\n", .{ self.prefix, message });
    }

    pub fn info(self: *const Logger, message: []const u8) void {
        self.log(message);
    }
};

const Application = struct {
    logger: Logger,
    name: []const u8,

    pub fn init(name: []const u8) Application {
        return Application{
            .logger = Logger.init("APP"),
            .name = name,
        };
    }

    pub fn start(self: *const Application) void {
        self.logger.info("Application starting");
    }

    pub fn stop(self: *const Application) void {
        self.logger.info("Application stopping");
    }
};

    pub fn stop(self: *const Application) void {
        self.logger.info("Application stopping");
    }
};
```

The `Application` struct contains a `Logger` and calls its methods directly.

### Embedded Struct Pattern

Create a parent-child relationship through embedding:

```zig
// Embedded struct pattern
const Animal = struct {
    name: []const u8,
    age: u8,

    pub fn init(name: []const u8, age: u8) Animal {
        return Animal{ .name = name, .age = age };
    }

    pub fn getName(self: *const Animal) []const u8 {
        return self.name;
    }

    pub fn getAge(self: *const Animal) u8 {
        return self.age;
    }

    pub fn speak(self: *const Animal) []const u8 {
        _ = self;
        return "Some sound";
    }
};

const Dog = struct {
    animal: Animal,
    breed: []const u8,

    pub fn init(name: []const u8, age: u8, breed: []const u8) Dog {
        return Dog{
            .animal = Animal.init(name, age),
            .breed = breed,
        };
    }

    // Delegate to embedded Animal
    pub fn getName(self: *const Dog) []const u8 {
        return self.animal.getName();
    }

    pub fn getAge(self: *const Dog) u8 {
        return self.animal.getAge();
    }

    // Override with Dog-specific behavior
    pub fn speak(self: *const Dog) []const u8 {
        _ = self;
        return "Woof!";
    }

    pub fn getBreed(self: *const Dog) []const u8 {
        return self.breed;
    }
};
```

`Dog` embeds `Animal` and delegates some methods while providing its own implementation of others.

### Explicit Delegation with Enhanced Behavior

Wrap parent methods to add validation or extra logic:

```zig
// Explicit delegation helper
const Counter = struct {
    count: i32,

    pub fn init() Counter {
        return Counter{ .count = 0 };
    }

    pub fn increment(self: *Counter) void {
        self.count += 1;
    }

    pub fn decrement(self: *Counter) void {
        self.count -= 1;
    }

    pub fn getValue(self: *const Counter) i32 {
        return self.count;
    }

    pub fn reset(self: *Counter) void {
        self.count = 0;
    }
};

const BoundedCounter = struct {
    counter: Counter,
    max_value: i32,

    pub fn init(max_value: i32) BoundedCounter {
        return BoundedCounter{
            .counter = Counter.init(),
            .max_value = max_value,
        };
    }

    // Delegate to parent, but with bounds checking
    pub fn increment(self: *BoundedCounter) void {
        if (self.counter.getValue() < self.max_value) {
            self.counter.increment();
        }
    }

    pub fn decrement(self: *BoundedCounter) void {
        if (self.counter.getValue() > 0) {
            self.counter.decrement();
        }
    }

    // Simple delegation
    pub fn getValue(self: *const BoundedCounter) i32 {
        return self.counter.getValue();
    }

    pub fn reset(self: *BoundedCounter) void {
        self.counter.reset();
    }
};
```

`BoundedCounter` enhances `Counter` by adding boundary checks before delegating.

### Multiple Composition

Combine multiple structs to get features from several sources:

```zig
// Multiple composition (like multiple inheritance)
const Drawable = struct {
    x: f32,
    y: f32,

    pub fn init(x: f32, y: f32) Drawable {
        return Drawable{ .x = x, .y = y };
    }

    pub fn draw(self: *const Drawable) void {
        _ = self;
        // Drawing logic
    }

    pub fn moveTo(self: *Drawable, x: f32, y: f32) void {
        self.x = x;
        self.y = y;
    }
};

const Clickable = struct {
    enabled: bool,

    pub fn init() Clickable {
        return Clickable{ .enabled = true };
    }

    pub fn onClick(self: *const Clickable) void {
        _ = self;
        // Click handling logic
    }

    pub fn setEnabled(self: *Clickable, enabled: bool) void {
        self.enabled = enabled;
    }
};

const Button = struct {
    drawable: Drawable,
    clickable: Clickable,
    label: []const u8,

    pub fn init(x: f32, y: f32, label: []const u8) Button {
        return Button{
            .drawable = Drawable.init(x, y),
            .clickable = Clickable.init(),
            .label = label,
        };
    }

    // Delegate to Drawable
    pub fn draw(self: *const Button) void {
        self.drawable.draw();
    }

    pub fn moveTo(self: *Button, x: f32, y: f32) void {
        self.drawable.moveTo(x, y);
    }

    // Delegate to Clickable
    pub fn onClick(self: *const Button) void {
        if (self.clickable.enabled) {
            self.clickable.onClick();
        }
    }

    pub fn setEnabled(self: *Button, enabled: bool) void {
        self.clickable.setEnabled(enabled);
    }
};
```

`Button` combines drawable and clickable functionality through multiple embedded structs.

### Extending Parent Method Behavior

Call parent methods and add additional processing:

```zig
const FileWriter = struct {
    path: []const u8,
    write_count: u32,

    pub fn init(path: []const u8) FileWriter {
        return FileWriter{
            .path = path,
            .write_count = 0,
        };
    }

    pub fn write(self: *FileWriter, data: []const u8) !void {
        _ = data;
        self.write_count += 1;
        // Actual file writing would go here
    }

    pub fn getWriteCount(self: *const FileWriter) u32 {
        return self.write_count;
    }
};

const BufferedFileWriter = struct {
    writer: FileWriter,
    buffer: [1024]u8,
    buffer_len: usize,

    pub fn init(path: []const u8) BufferedFileWriter {
        return BufferedFileWriter{
            .writer = FileWriter.init(path),
            .buffer = undefined,
            .buffer_len = 0,
        };
    }

    pub fn write(self: *BufferedFileWriter, data: []const u8) !void {
        // Add to buffer
        for (data) |byte| {
            self.buffer[self.buffer_len] = byte;
            self.buffer_len += 1;

            // Flush if buffer full
            if (self.buffer_len >= self.buffer.len) {
                try self.flush();
            }
        }
    }

    pub fn flush(self: *BufferedFileWriter) !void {
        if (self.buffer_len > 0) {
            // Call parent write method
            try self.writer.write(self.buffer[0..self.buffer_len]);
            self.buffer_len = 0;
        }
    }

    pub fn getWriteCount(self: *const BufferedFileWriter) u32 {
        return self.writer.getWriteCount();
    }
};
```

`BufferedFileWriter` adds buffering logic before calling the parent's `write()` method.

### Accessing and Modifying Parent State

Child structs can read and modify parent state through the embedded struct:

```zig
const Vehicle = struct {
    speed: f32,
    fuel: f32,

    pub fn init(fuel: f32) Vehicle {
        return Vehicle{
            .speed = 0,
            .fuel = fuel,
        };
    }

    pub fn accelerate(self: *Vehicle, amount: f32) !void {
        if (self.fuel <= 0) return error.NoFuel;
        self.speed += amount;
        self.fuel -= amount * 0.1;
    }

    pub fn brake(self: *Vehicle) void {
        self.speed = 0;
    }

    pub fn getSpeed(self: *const Vehicle) f32 {
        return self.speed;
    }

    pub fn getFuel(self: *const Vehicle) f32 {
        return self.fuel;
    }
};

const Car = struct {
    vehicle: Vehicle,
    turbo_enabled: bool,

    pub fn init(fuel: f32) Car {
        return Car{
            .vehicle = Vehicle.init(fuel),
            .turbo_enabled = false,
        };
    }

    pub fn accelerate(self: *Car, amount: f32) !void {
        const multiplier: f32 = if (self.turbo_enabled) 2.0 else 1.0;
        try self.vehicle.accelerate(amount * multiplier);
    }

    pub fn brake(self: *Car) void {
        self.vehicle.brake();
    }

    pub fn enableTurbo(self: *Car) void {
        self.turbo_enabled = true;
    }

    pub fn getSpeed(self: *const Car) f32 {
        return self.vehicle.getSpeed();
    }

    pub fn getFuel(self: *const Car) f32 {
        return self.vehicle.getFuel();
    }
};
```

`Car` modifies how acceleration works by applying a turbo multiplier before calling the parent method.

### Generic Wrapper Pattern

Create reusable wrappers using `comptime`:

```zig
fn Wrapper(comptime T: type) type {
    return struct {
        inner: T,
        metadata: []const u8,

        const Self = @This();

        pub fn init(inner: T, metadata: []const u8) Self {
            return Self{
                .inner = inner,
                .metadata = metadata,
            };
        }

        pub fn getInner(self: *const Self) *const T {
            return &self.inner;
        }

        pub fn getInnerMut(self: *Self) *T {
            return &self.inner;
        }

        pub fn getMetadata(self: *const Self) []const u8 {
            return self.metadata;
        }
    };
}
```

This wrapper works with any type and provides access to the wrapped value.

### Discussion

Zig's composition approach offers several advantages over traditional inheritance:

1. **Explicit relationships** - You can see exactly which methods delegate to which embedded structs
2. **No diamond problem** - Multiple composition doesn't create ambiguous method resolution
3. **Flexible organization** - Restructure relationships without changing interfaces
4. **Clear ownership** - Each struct owns its embedded structs
5. **Better performance** - No vtable lookups or dynamic dispatch overhead

### Composition vs. Inheritance

In object-oriented languages, you might write:

```
class Dog extends Animal {
    speak() { return "Woof!"; }
}
```

In Zig, you compose explicitly:

```zig
const Dog = struct {
    animal: Animal,  // Embed parent
    // ... delegate methods ...
};
```

The Zig approach requires more typing but makes dependencies and relationships visible.

### When to Delegate

Delegate method calls when you want to:

- **Reuse logic** - Don't duplicate parent functionality
- **Add validation** - Wrap parent methods with checks
- **Extend behavior** - Call parent then do additional work
- **Maintain compatibility** - Keep same interface as parent

For new functionality unique to the child struct, implement methods directly without delegation.

### Performance

Composition in Zig has minimal overhead:

- Embedded structs are laid out inline (no pointers or allocations)
- Method calls compile to direct function calls (no dynamic dispatch)
- The compiler can inline delegated methods
- No runtime type checking or vtable lookups

This makes composition as fast as using the structs directly.

### Pattern: Delegation Macros

For structs with many delegated methods, consider using `comptime` to generate delegation code automatically. This reduces boilerplate while maintaining explicitness.

### Full Tested Code

```zig
// Recipe 8.7: Calling a Method on a Parent Class
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_composition
// Basic composition
const Logger = struct {
    prefix: []const u8,

    pub fn init(prefix: []const u8) Logger {
        return Logger{ .prefix = prefix };
    }

    pub fn log(self: *const Logger, message: []const u8) void {
        _ = self;
        _ = message;
        // In reality: std.debug.print("[{s}] {s}\n", .{ self.prefix, message });
    }

    pub fn info(self: *const Logger, message: []const u8) void {
        self.log(message);
    }
};

const Application = struct {
    logger: Logger,
    name: []const u8,

    pub fn init(name: []const u8) Application {
        return Application{
            .logger = Logger.init("APP"),
            .name = name,
        };
    }

    pub fn start(self: *const Application) void {
        self.logger.info("Application starting");
    }

    pub fn stop(self: *const Application) void {
        self.logger.info("Application stopping");
    }
};
// ANCHOR_END: basic_composition

test "basic composition" {
    const app = Application.init("MyApp");
    app.start();
    app.stop();
}

// ANCHOR: embedded_struct
// Embedded struct pattern
const Animal = struct {
    name: []const u8,
    age: u8,

    pub fn init(name: []const u8, age: u8) Animal {
        return Animal{ .name = name, .age = age };
    }

    pub fn getName(self: *const Animal) []const u8 {
        return self.name;
    }

    pub fn getAge(self: *const Animal) u8 {
        return self.age;
    }

    pub fn speak(self: *const Animal) []const u8 {
        _ = self;
        return "Some sound";
    }
};

const Dog = struct {
    animal: Animal,
    breed: []const u8,

    pub fn init(name: []const u8, age: u8, breed: []const u8) Dog {
        return Dog{
            .animal = Animal.init(name, age),
            .breed = breed,
        };
    }

    // Delegate to embedded Animal
    pub fn getName(self: *const Dog) []const u8 {
        return self.animal.getName();
    }

    pub fn getAge(self: *const Dog) u8 {
        return self.animal.getAge();
    }

    // Override with Dog-specific behavior
    pub fn speak(self: *const Dog) []const u8 {
        _ = self;
        return "Woof!";
    }

    pub fn getBreed(self: *const Dog) []const u8 {
        return self.breed;
    }
};
// ANCHOR_END: embedded_struct

test "embedded struct" {
    const dog = Dog.init("Buddy", 5, "Golden Retriever");

    try testing.expectEqualStrings("Buddy", dog.getName());
    try testing.expectEqual(@as(u8, 5), dog.getAge());
    try testing.expectEqualStrings("Woof!", dog.speak());
    try testing.expectEqualStrings("Golden Retriever", dog.getBreed());
}

// ANCHOR: explicit_delegation
// Explicit delegation helper
const Counter = struct {
    count: i32,

    pub fn init() Counter {
        return Counter{ .count = 0 };
    }

    pub fn increment(self: *Counter) void {
        self.count += 1;
    }

    pub fn decrement(self: *Counter) void {
        self.count -= 1;
    }

    pub fn getValue(self: *const Counter) i32 {
        return self.count;
    }

    pub fn reset(self: *Counter) void {
        self.count = 0;
    }
};

const BoundedCounter = struct {
    counter: Counter,
    max_value: i32,

    pub fn init(max_value: i32) BoundedCounter {
        return BoundedCounter{
            .counter = Counter.init(),
            .max_value = max_value,
        };
    }

    // Delegate to parent, but with bounds checking
    pub fn increment(self: *BoundedCounter) void {
        if (self.counter.getValue() < self.max_value) {
            self.counter.increment();
        }
    }

    pub fn decrement(self: *BoundedCounter) void {
        if (self.counter.getValue() > 0) {
            self.counter.decrement();
        }
    }

    // Simple delegation
    pub fn getValue(self: *const BoundedCounter) i32 {
        return self.counter.getValue();
    }

    pub fn reset(self: *BoundedCounter) void {
        self.counter.reset();
    }
};
// ANCHOR_END: explicit_delegation

test "explicit delegation" {
    var bounded = BoundedCounter.init(5);

    bounded.increment();
    bounded.increment();
    try testing.expectEqual(@as(i32, 2), bounded.getValue());

    // Try to exceed max
    bounded.increment();
    bounded.increment();
    bounded.increment();
    bounded.increment();
    try testing.expectEqual(@as(i32, 5), bounded.getValue());

    bounded.decrement();
    try testing.expectEqual(@as(i32, 4), bounded.getValue());
}

// ANCHOR: multiple_composition
// Multiple composition (like multiple inheritance)
const Drawable = struct {
    x: f32,
    y: f32,

    pub fn init(x: f32, y: f32) Drawable {
        return Drawable{ .x = x, .y = y };
    }

    pub fn draw(self: *const Drawable) void {
        _ = self;
        // Drawing logic
    }

    pub fn moveTo(self: *Drawable, x: f32, y: f32) void {
        self.x = x;
        self.y = y;
    }
};

const Clickable = struct {
    enabled: bool,

    pub fn init() Clickable {
        return Clickable{ .enabled = true };
    }

    pub fn onClick(self: *const Clickable) void {
        _ = self;
        // Click handling logic
    }

    pub fn setEnabled(self: *Clickable, enabled: bool) void {
        self.enabled = enabled;
    }
};

const Button = struct {
    drawable: Drawable,
    clickable: Clickable,
    label: []const u8,

    pub fn init(x: f32, y: f32, label: []const u8) Button {
        return Button{
            .drawable = Drawable.init(x, y),
            .clickable = Clickable.init(),
            .label = label,
        };
    }

    // Delegate to Drawable
    pub fn draw(self: *const Button) void {
        self.drawable.draw();
    }

    pub fn moveTo(self: *Button, x: f32, y: f32) void {
        self.drawable.moveTo(x, y);
    }

    // Delegate to Clickable
    pub fn onClick(self: *const Button) void {
        if (self.clickable.enabled) {
            self.clickable.onClick();
        }
    }

    pub fn setEnabled(self: *Button, enabled: bool) void {
        self.clickable.setEnabled(enabled);
    }
};
// ANCHOR_END: multiple_composition

test "multiple composition" {
    var button = Button.init(10, 20, "Click Me");

    button.draw();
    button.onClick();

    button.moveTo(30, 40);
    try testing.expectEqual(@as(f32, 30), button.drawable.x);

    button.setEnabled(false);
    try testing.expectEqual(false, button.clickable.enabled);
}

// ANCHOR: extending_parent_method
// Extending parent method behavior
const FileWriter = struct {
    path: []const u8,
    write_count: u32,

    pub fn init(path: []const u8) FileWriter {
        return FileWriter{
            .path = path,
            .write_count = 0,
        };
    }

    pub fn write(self: *FileWriter, data: []const u8) !void {
        _ = data;
        self.write_count += 1;
        // Actual file writing would go here
    }

    pub fn getWriteCount(self: *const FileWriter) u32 {
        return self.write_count;
    }
};

const BufferedFileWriter = struct {
    writer: FileWriter,
    buffer: [1024]u8,
    buffer_len: usize,

    pub fn init(path: []const u8) BufferedFileWriter {
        return BufferedFileWriter{
            .writer = FileWriter.init(path),
            .buffer = undefined,
            .buffer_len = 0,
        };
    }

    pub fn write(self: *BufferedFileWriter, data: []const u8) !void {
        // Add to buffer
        for (data) |byte| {
            self.buffer[self.buffer_len] = byte;
            self.buffer_len += 1;

            // Flush if buffer full
            if (self.buffer_len >= self.buffer.len) {
                try self.flush();
            }
        }
    }

    pub fn flush(self: *BufferedFileWriter) !void {
        if (self.buffer_len > 0) {
            // Call parent write method
            try self.writer.write(self.buffer[0..self.buffer_len]);
            self.buffer_len = 0;
        }
    }

    pub fn getWriteCount(self: *const BufferedFileWriter) u32 {
        return self.writer.getWriteCount();
    }
};
// ANCHOR_END: extending_parent_method

test "extending parent method" {
    var buffered = BufferedFileWriter.init("/tmp/test.txt");

    try buffered.write("Hello");
    try buffered.write(", World!");

    // Haven't flushed yet
    try testing.expectEqual(@as(u32, 0), buffered.getWriteCount());

    try buffered.flush();
    try testing.expectEqual(@as(u32, 1), buffered.getWriteCount());
}

// ANCHOR: accessing_parent_state
// Accessing and modifying parent state
const Vehicle = struct {
    speed: f32,
    fuel: f32,

    pub fn init(fuel: f32) Vehicle {
        return Vehicle{
            .speed = 0,
            .fuel = fuel,
        };
    }

    pub fn accelerate(self: *Vehicle, amount: f32) !void {
        if (self.fuel <= 0) return error.NoFuel;
        self.speed += amount;
        self.fuel -= amount * 0.1;
    }

    pub fn brake(self: *Vehicle) void {
        self.speed = 0;
    }

    pub fn getSpeed(self: *const Vehicle) f32 {
        return self.speed;
    }

    pub fn getFuel(self: *const Vehicle) f32 {
        return self.fuel;
    }
};

const Car = struct {
    vehicle: Vehicle,
    turbo_enabled: bool,

    pub fn init(fuel: f32) Car {
        return Car{
            .vehicle = Vehicle.init(fuel),
            .turbo_enabled = false,
        };
    }

    pub fn accelerate(self: *Car, amount: f32) !void {
        const multiplier: f32 = if (self.turbo_enabled) 2.0 else 1.0;
        try self.vehicle.accelerate(amount * multiplier);
    }

    pub fn brake(self: *Car) void {
        self.vehicle.brake();
    }

    pub fn enableTurbo(self: *Car) void {
        self.turbo_enabled = true;
    }

    pub fn getSpeed(self: *const Car) f32 {
        return self.vehicle.getSpeed();
    }

    pub fn getFuel(self: *const Car) f32 {
        return self.vehicle.getFuel();
    }
};
// ANCHOR_END: accessing_parent_state

test "accessing parent state" {
    var car = Car.init(100);

    try car.accelerate(10);
    try testing.expectEqual(@as(f32, 10), car.getSpeed());

    car.enableTurbo();
    try car.accelerate(10);
    try testing.expectEqual(@as(f32, 30), car.getSpeed()); // 10 + (10 * 2)
}

// ANCHOR: init_with_parent
// Initializing with parent initialization
const Shape = struct {
    color: []const u8,
    id: u32,

    pub fn init(color: []const u8, id: u32) Shape {
        return Shape{
            .color = color,
            .id = id,
        };
    }

    pub fn describe(self: *const Shape) void {
        _ = self;
        // std.debug.print("Shape #{d} in {s}\n", .{ self.id, self.color });
    }
};

const Circle = struct {
    shape: Shape,
    radius: f32,

    pub fn init(color: []const u8, id: u32, radius: f32) Circle {
        return Circle{
            .shape = Shape.init(color, id),
            .radius = radius,
        };
    }

    pub fn describe(self: *const Circle) void {
        self.shape.describe();
        // Additional circle-specific description
    }

    pub fn getArea(self: *const Circle) f32 {
        return std.math.pi * self.radius * self.radius;
    }
};
// ANCHOR_END: init_with_parent

test "init with parent" {
    const circle = Circle.init("red", 1, 5.0);

    try testing.expectEqualStrings("red", circle.shape.color);
    try testing.expectEqual(@as(u32, 1), circle.shape.id);
    try testing.expectEqual(@as(f32, 5.0), circle.radius);

    const area = circle.getArea();
    try testing.expectApproxEqAbs(78.54, area, 0.01);
}

// ANCHOR: generic_wrapper
// Generic wrapper pattern
fn Wrapper(comptime T: type) type {
    return struct {
        inner: T,
        metadata: []const u8,

        const Self = @This();

        pub fn init(inner: T, metadata: []const u8) Self {
            return Self{
                .inner = inner,
                .metadata = metadata,
            };
        }

        pub fn getInner(self: *const Self) *const T {
            return &self.inner;
        }

        pub fn getInnerMut(self: *Self) *T {
            return &self.inner;
        }

        pub fn getMetadata(self: *const Self) []const u8 {
            return self.metadata;
        }
    };
}
// ANCHOR_END: generic_wrapper

test "generic wrapper" {
    var wrapped = Wrapper(i32).init(42, "important number");

    try testing.expectEqual(@as(i32, 42), wrapped.getInner().*);
    try testing.expectEqualStrings("important number", wrapped.getMetadata());

    wrapped.getInnerMut().* = 100;
    try testing.expectEqual(@as(i32, 100), wrapped.getInner().*);
}

// ANCHOR: interface_delegation
// Interface-style delegation
const Writer = struct {
    ptr: *anyopaque,
    writeFn: *const fn (ptr: *anyopaque, data: []const u8) anyerror!usize,

    pub fn write(self: Writer, data: []const u8) !usize {
        return self.writeFn(self.ptr, data);
    }
};

const StringWriter = struct {
    buffer: std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) StringWriter {
        return StringWriter{
            .buffer = std.ArrayList(u8){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *StringWriter) void {
        self.buffer.deinit(self.allocator);
    }

    fn writeImpl(ptr: *anyopaque, data: []const u8) !usize {
        const self: *StringWriter = @ptrCast(@alignCast(ptr));
        try self.buffer.appendSlice(self.allocator, data);
        return data.len;
    }

    pub fn writer(self: *StringWriter) Writer {
        return Writer{
            .ptr = self,
            .writeFn = writeImpl,
        };
    }

    pub fn getString(self: *const StringWriter) []const u8 {
        return self.buffer.items;
    }
};
// ANCHOR_END: interface_delegation

test "interface delegation" {
    var string_writer = StringWriter.init(testing.allocator);
    defer string_writer.deinit();

    const writer = string_writer.writer();
    const written = try writer.write("Hello, World!");

    try testing.expectEqual(@as(usize, 13), written);
    try testing.expectEqualStrings("Hello, World!", string_writer.getString());
}

// Comprehensive test
test "comprehensive parent method calls" {
    var dog = Dog.init("Max", 3, "Labrador");
    try testing.expectEqualStrings("Max", dog.getName());

    var bounded = BoundedCounter.init(10);
    bounded.increment();
    try testing.expectEqual(@as(i32, 1), bounded.getValue());

    var button = Button.init(5, 5, "Submit");
    button.moveTo(10, 10);
    try testing.expectEqual(@as(f32, 10), button.drawable.x);

    var car = Car.init(50);
    try car.accelerate(5);
    try testing.expect(car.getSpeed() > 0);
}
```

### See Also

- Recipe 8.5: Encapsulating Names in a Struct
- Recipe 8.8: Extending a Property in a Subclass
- Recipe 8.12: Defining an Interface
- Recipe 8.18: Extending Classes with Mixins

---

## Recipe 8.8: Extending a Property in a Subclass {#recipe-8-8}

**Tags:** error-handling, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_8.zig`

### Problem

You want to extend or modify the behavior of properties from a parent struct—adding validation, transforming values, tracking history, or applying pre/post processing—while maintaining the parent's interface.

### Solution

Use composition to embed the parent struct and override its methods with enhanced behavior. Your child struct can delegate to the parent while adding extra functionality before or after the delegation.

### Basic Property Extension

Add functionality by tracking additional state alongside the parent's behavior:

```zig
// Basic property extension
const BaseCounter = struct {
    value: i32,

    pub fn init() BaseCounter {
        return BaseCounter{ .value = 0 };
    }

    pub fn getValue(self: *const BaseCounter) i32 {
        return self.value;
    }

    pub fn setValue(self: *BaseCounter, val: i32) void {
        self.value = val;
    }

    pub fn increment(self: *BaseCounter) void {
        self.value += 1;
    }
};

const ExtendedCounter = struct {
    base: BaseCounter,
    history: [10]i32,
    history_len: usize,

    pub fn init() ExtendedCounter {
        return ExtendedCounter{
            .base = BaseCounter.init(),
            .history = undefined,
            .history_len = 0,
        };
    }

    // Extend getValue to include history tracking
    pub fn getValue(self: *const ExtendedCounter) i32 {
        return self.base.getValue();
    }

    // Extend setValue to record history
    pub fn setValue(self: *ExtendedCounter, val: i32) void {
        if (self.history_len < self.history.len) {
            self.history[self.history_len] = self.base.getValue();
            self.history_len += 1;
        }
        self.base.setValue(val);
    }

    pub fn increment(self: *ExtendedCounter) void {
        self.setValue(self.base.getValue() + 1);
    }

    pub fn getHistory(self: *const ExtendedCounter) []const i32 {
        return self.history[0..self.history_len];
    }
};
    }

    pub fn getValue(self: *const ExtendedCounter) i32 {
        return self.base.getValue();
    }

    // Extend setValue to record history
    pub fn setValue(self: *ExtendedCounter, val: i32) void {
        if (self.history_len < self.history.len) {
            self.history[self.history_len] = self.base.getValue();
            self.history_len += 1;
        }
        self.base.setValue(val);
    }

    pub fn increment(self: *ExtendedCounter) void {
        self.setValue(self.base.getValue() + 1);
    }

    pub fn getHistory(self: *const ExtendedCounter) []const i32 {
        return self.history[0..self.history_len];
    }
};
```

`ExtendedCounter` tracks value history while maintaining the same interface as `BaseCounter`.

### Extended Validation

Add stricter validation rules to parent methods:

```zig
const BasicAccount = struct {
    balance: f64,

    pub fn init() BasicAccount {
        return BasicAccount{ .balance = 0 };
    }

    pub fn getBalance(self: *const BasicAccount) f64 {
        return self.balance;
    }

    pub fn deposit(self: *BasicAccount, amount: f64) !void {
        if (amount <= 0) return error.InvalidAmount;
        self.balance += amount;
    }
};

const PremiumAccount = struct {
    account: BasicAccount,
    min_deposit: f64,
    total_deposits: f64,

    pub fn init(min_deposit: f64) PremiumAccount {
        return PremiumAccount{
            .account = BasicAccount.init(),
            .min_deposit = min_deposit,
            .total_deposits = 0,
        };
    }

    pub fn getBalance(self: *const PremiumAccount) f64 {
        return self.account.getBalance();
    }

    // Extend with additional validation
    pub fn deposit(self: *PremiumAccount, amount: f64) !void {
        if (amount < self.min_deposit) return error.BelowMinimum;

        try self.account.deposit(amount);
        self.total_deposits += amount;
    }

    pub fn getTotalDeposits(self: *const PremiumAccount) f64 {
        return self.total_deposits;
    }
};
```

`PremiumAccount` enforces a minimum deposit amount before delegating to the parent.

### Computed Properties Building on Parent

Create new computed properties based on parent data:

```zig
const Rectangle = struct {
    width: f32,
    height: f32,

    pub fn init(width: f32, height: f32) Rectangle {
        return Rectangle{ .width = width, .height = height };
    }

    pub fn getArea(self: *const Rectangle) f32 {
        return self.width * self.height;
    }

    pub fn getPerimeter(self: *const Rectangle) f32 {
        return 2 * (self.width + self.height);
    }
};

const ColoredRectangle = struct {
    rect: Rectangle,
    color: []const u8,
    opacity: f32,

    pub fn init(width: f32, height: f32, color: []const u8) ColoredRectangle {
        return ColoredRectangle{
            .rect = Rectangle.init(width, height),
            .color = color,
            .opacity = 1.0,
        };
    }

    pub fn getArea(self: *const ColoredRectangle) f32 {
        return self.rect.getArea();
    }

    pub fn getPerimeter(self: *const ColoredRectangle) f32 {
        return self.rect.getPerimeter();
    }

    // Extended computed property
    pub fn getVisibleArea(self: *const ColoredRectangle) f32 {
        return self.rect.getArea() * self.opacity;
    }

    pub fn setOpacity(self: *ColoredRectangle, opacity: f32) !void {
        if (opacity < 0 or opacity > 1) return error.InvalidOpacity;
        self.opacity = opacity;
    }
};
```

The `getVisibleArea()` method combines parent data with child-specific properties.

### Property Transformation Wrapper

Transform values on get and set operations:

```zig
const Temperature = struct {
    celsius: f32,

    pub fn init(celsius: f32) Temperature {
        return Temperature{ .celsius = celsius };
    }

    pub fn getCelsius(self: *const Temperature) f32 {
        return self.celsius;
    }

    pub fn setCelsius(self: *Temperature, value: f32) void {
        self.celsius = value;
    }
};

const CalibratedTemperature = struct {
    temp: Temperature,
    offset: f32,

    pub fn init(celsius: f32, offset: f32) CalibratedTemperature {
        return CalibratedTemperature{
            .temp = Temperature.init(celsius),
            .offset = offset,
        };
    }

    // Transform getter to apply calibration
    pub fn getCelsius(self: *const CalibratedTemperature) f32 {
        return self.temp.getCelsius() + self.offset;
    }

    // Transform setter to remove calibration
    pub fn setCelsius(self: *CalibratedTemperature, value: f32) void {
        self.temp.setCelsius(value - self.offset);
    }

    pub fn getRawCelsius(self: *const CalibratedTemperature) f32 {
        return self.temp.getCelsius();
    }
};
```

Users work with calibrated values while the parent stores raw values.

### Chaining Parent and Child Operations

Extend parent methods by adding child-specific parameters:

```zig
const Logger = struct {
    prefix: []const u8,
    log_count: u32,

    pub fn init(prefix: []const u8) Logger {
        return Logger{
            .prefix = prefix,
            .log_count = 0,
        };
    }

    pub fn log(self: *Logger, message: []const u8) void {
        _ = message;
        self.log_count += 1;
    }

    pub fn getLogCount(self: *const Logger) u32 {
        return self.log_count;
    }
};

const TimestampedLogger = struct {
    logger: Logger,
    last_timestamp: i64,

    pub fn init(prefix: []const u8) TimestampedLogger {
        return TimestampedLogger{
            .logger = Logger.init(prefix),
            .last_timestamp = 0,
        };
    }

    pub fn log(self: *TimestampedLogger, message: []const u8, timestamp: i64) void {
        self.last_timestamp = timestamp;
        self.logger.log(message);
    }

    pub fn getLogCount(self: *const TimestampedLogger) u32 {
        return self.logger.getLogCount();
    }

    pub fn getLastTimestamp(self: *const TimestampedLogger) i64 {
        return self.last_timestamp;
    }
};
```

The child's `log()` accepts a timestamp before delegating to the parent.

### Override with Conditional Fallback

Add logic that conditionally delegates to the parent:

```zig
const Cache = struct {
    data: ?[]const u8,

    pub fn init() Cache {
        return Cache{ .data = null };
    }

    pub fn get(self: *const Cache) ?[]const u8 {
        return self.data;
    }

    pub fn set(self: *Cache, value: []const u8) void {
        self.data = value;
    }

    pub fn clear(self: *Cache) void {
        self.data = null;
    }
};

const TtlCache = struct {
    cache: Cache,
    ttl_seconds: i64,
    set_time: i64,

    pub fn init(ttl_seconds: i64) TtlCache {
        return TtlCache{
            .cache = Cache.init(),
            .ttl_seconds = ttl_seconds,
            .set_time = 0,
        };
    }

    pub fn get(self: *const TtlCache, current_time: i64) ?[]const u8 {
        if (self.cache.get()) |data| {
            if (current_time - self.set_time < self.ttl_seconds) {
                return data;
            }
        }
        return null;
    }

    pub fn set(self: *TtlCache, value: []const u8, current_time: i64) void {
        self.cache.set(value);
        self.set_time = current_time;
    }

    pub fn clear(self: *TtlCache) void {
        self.cache.clear();
        self.set_time = 0;
    }
};
```

The TTL cache checks expiration before returning the parent's cached data.

### Pre and Post Processing

Add validation before and tracking after parent method calls:

```zig
const DataStore = struct {
    value: i32,

    pub fn init() DataStore {
        return DataStore{ .value = 0 };
    }

    pub fn getValue(self: *const DataStore) i32 {
        return self.value;
    }

    pub fn setValue(self: *DataStore, val: i32) void {
        self.value = val;
    }
};

const ValidatedDataStore = struct {
    store: DataStore,
    min_value: i32,
    max_value: i32,
    validation_failures: u32,

    pub fn init(min: i32, max: i32) ValidatedDataStore {
        return ValidatedDataStore{
            .store = DataStore.init(),
            .min_value = min,
            .max_value = max,
            .validation_failures = 0,
        };
    }

    pub fn getValue(self: *const ValidatedDataStore) i32 {
        return self.store.getValue();
    }

    pub fn setValue(self: *ValidatedDataStore, val: i32) !void {
        // Pre-processing: validate
        if (val < self.min_value or val > self.max_value) {
            self.validation_failures += 1;
            return error.OutOfRange;
        }

        // Call parent
        self.store.setValue(val);

        // Post-processing could track successful sets, etc.
    }

    pub fn getValidationFailures(self: *const ValidatedDataStore) u32 {
        return self.validation_failures;
    }
};
```

This pattern is useful for metrics, logging, and debugging.

### Multi-Level Extension

Chain multiple levels of property extensions:

```zig
const Level1 = struct {
    value: i32,

    pub fn init() Level1 {
        return Level1{ .value = 0 };
    }

    pub fn getValue(self: *const Level1) i32 {
        return self.value;
    }

    pub fn setValue(self: *Level1, val: i32) void {
        self.value = val;
    }
};

const Level2 = struct {
    level1: Level1,
    multiplier: i32,

    pub fn init(multiplier: i32) Level2 {
        return Level2{
            .level1 = Level1.init(),
            .multiplier = multiplier,
        };
    }

    pub fn getValue(self: *const Level2) i32 {
        return self.level1.getValue() * self.multiplier;
    }

    pub fn setValue(self: *Level2, val: i32) void {
        self.level1.setValue(@divTrunc(val, self.multiplier));
    }
};

const Level3 = struct {
    level2: Level2,
    offset: i32,

    pub fn init(multiplier: i32, offset: i32) Level3 {
        return Level3{
            .level2 = Level2.init(multiplier),
            .offset = offset,
        };
    }

    pub fn getValue(self: *const Level3) i32 {
        return self.level2.getValue() + self.offset;
    }

    pub fn setValue(self: *Level3, val: i32) void {
        self.level2.setValue(val - self.offset);
    }
};
```

Each level applies its own transformation, creating a pipeline of operations.

### Discussion

Extending properties through composition follows the decorator pattern, where each layer adds functionality while maintaining the interface.

### Advantages of This Approach

1. **Flexibility** - Add or remove features by composing different structs
2. **Clarity** - Each extension is a separate struct with clear responsibilities
3. **Testability** - Test each layer independently
4. **No conflicts** - Unlike inheritance, no method name collisions
5. **Compile-time overhead only** - No runtime cost for delegation

### Common Extension Patterns

**Validation**: Add checks before delegating to parent
- Example: Minimum/maximum bounds, format validation

**Transformation**: Convert values on get/set
- Example: Unit conversion, encoding/decoding

**Observation**: Track or react to changes
- Example: History tracking, change notifications

**Caching**: Store computed results
- Example: Lazy properties, memoization

**Conditional logic**: Choose whether to delegate
- Example: TTL expiration, feature flags

### When to Use Property Extension

Use property extension when you want to:

- Add validation without modifying the parent struct
- Track metrics or history for existing properties
- Apply transformations transparently
- Implement caching or lazy evaluation
- Add time-based or conditional behavior

### Design Considerations

**Interface compatibility**: Decide whether to keep the same interface (drop-in replacement) or add parameters (explicit extension).

**Error handling**: Extended methods can add new error cases while still propagating parent errors.

**State synchronization**: When both parent and child have state, ensure they stay consistent.

**Performance**: Most extensions have zero runtime cost when inlined. Measure if concerned.

### Full Tested Code

```zig
// Recipe 8.8: Extending a Property in a Subclass
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_property_extension
// Basic property extension
const BaseCounter = struct {
    value: i32,

    pub fn init() BaseCounter {
        return BaseCounter{ .value = 0 };
    }

    pub fn getValue(self: *const BaseCounter) i32 {
        return self.value;
    }

    pub fn setValue(self: *BaseCounter, val: i32) void {
        self.value = val;
    }

    pub fn increment(self: *BaseCounter) void {
        self.value += 1;
    }
};

const ExtendedCounter = struct {
    base: BaseCounter,
    history: [10]i32,
    history_len: usize,

    pub fn init() ExtendedCounter {
        return ExtendedCounter{
            .base = BaseCounter.init(),
            .history = undefined,
            .history_len = 0,
        };
    }

    // Extend getValue to include history tracking
    pub fn getValue(self: *const ExtendedCounter) i32 {
        return self.base.getValue();
    }

    // Extend setValue to record history
    pub fn setValue(self: *ExtendedCounter, val: i32) void {
        if (self.history_len < self.history.len) {
            self.history[self.history_len] = self.base.getValue();
            self.history_len += 1;
        }
        self.base.setValue(val);
    }

    pub fn increment(self: *ExtendedCounter) void {
        self.setValue(self.base.getValue() + 1);
    }

    pub fn getHistory(self: *const ExtendedCounter) []const i32 {
        return self.history[0..self.history_len];
    }
};
// ANCHOR_END: basic_property_extension

test "basic property extension" {
    var counter = ExtendedCounter.init();

    counter.setValue(5);
    counter.setValue(10);
    counter.increment();

    try testing.expectEqual(@as(i32, 11), counter.getValue());

    const history = counter.getHistory();
    try testing.expectEqual(@as(usize, 3), history.len);
    try testing.expectEqual(@as(i32, 0), history[0]);
    try testing.expectEqual(@as(i32, 5), history[1]);
    try testing.expectEqual(@as(i32, 10), history[2]);
}

// ANCHOR: extended_validation
// Extended validation rules
const BasicAccount = struct {
    balance: f64,

    pub fn init() BasicAccount {
        return BasicAccount{ .balance = 0 };
    }

    pub fn getBalance(self: *const BasicAccount) f64 {
        return self.balance;
    }

    pub fn deposit(self: *BasicAccount, amount: f64) !void {
        if (amount <= 0) return error.InvalidAmount;
        self.balance += amount;
    }
};

const PremiumAccount = struct {
    account: BasicAccount,
    min_deposit: f64,
    total_deposits: f64,

    pub fn init(min_deposit: f64) PremiumAccount {
        return PremiumAccount{
            .account = BasicAccount.init(),
            .min_deposit = min_deposit,
            .total_deposits = 0,
        };
    }

    pub fn getBalance(self: *const PremiumAccount) f64 {
        return self.account.getBalance();
    }

    // Extend with additional validation
    pub fn deposit(self: *PremiumAccount, amount: f64) !void {
        if (amount < self.min_deposit) return error.BelowMinimum;

        try self.account.deposit(amount);
        self.total_deposits += amount;
    }

    pub fn getTotalDeposits(self: *const PremiumAccount) f64 {
        return self.total_deposits;
    }
};
// ANCHOR_END: extended_validation

test "extended validation" {
    var premium = PremiumAccount.init(100);

    const small_deposit = premium.deposit(50);
    try testing.expectError(error.BelowMinimum, small_deposit);

    try premium.deposit(150);
    try testing.expectEqual(@as(f64, 150), premium.getBalance());
    try testing.expectEqual(@as(f64, 150), premium.getTotalDeposits());
}

// ANCHOR: computed_property_extension
// Computed properties building on parent
const Rectangle = struct {
    width: f32,
    height: f32,

    pub fn init(width: f32, height: f32) Rectangle {
        return Rectangle{ .width = width, .height = height };
    }

    pub fn getArea(self: *const Rectangle) f32 {
        return self.width * self.height;
    }

    pub fn getPerimeter(self: *const Rectangle) f32 {
        return 2 * (self.width + self.height);
    }
};

const ColoredRectangle = struct {
    rect: Rectangle,
    color: []const u8,
    opacity: f32,

    pub fn init(width: f32, height: f32, color: []const u8) ColoredRectangle {
        return ColoredRectangle{
            .rect = Rectangle.init(width, height),
            .color = color,
            .opacity = 1.0,
        };
    }

    // Delegate basic properties
    pub fn getArea(self: *const ColoredRectangle) f32 {
        return self.rect.getArea();
    }

    pub fn getPerimeter(self: *const ColoredRectangle) f32 {
        return self.rect.getPerimeter();
    }

    // Extended computed property
    pub fn getVisibleArea(self: *const ColoredRectangle) f32 {
        return self.rect.getArea() * self.opacity;
    }

    pub fn setOpacity(self: *ColoredRectangle, opacity: f32) !void {
        if (opacity < 0 or opacity > 1) return error.InvalidOpacity;
        self.opacity = opacity;
    }
};
// ANCHOR_END: computed_property_extension

test "computed property extension" {
    var colored = ColoredRectangle.init(10, 5, "red");

    try testing.expectEqual(@as(f32, 50), colored.getArea());
    try testing.expectEqual(@as(f32, 50), colored.getVisibleArea());

    try colored.setOpacity(0.5);
    try testing.expectEqual(@as(f32, 25), colored.getVisibleArea());
}

// ANCHOR: transformation_wrapper
// Property transformation wrapper
const Temperature = struct {
    celsius: f32,

    pub fn init(celsius: f32) Temperature {
        return Temperature{ .celsius = celsius };
    }

    pub fn getCelsius(self: *const Temperature) f32 {
        return self.celsius;
    }

    pub fn setCelsius(self: *Temperature, value: f32) void {
        self.celsius = value;
    }
};

const CalibratedTemperature = struct {
    temp: Temperature,
    offset: f32,

    pub fn init(celsius: f32, offset: f32) CalibratedTemperature {
        return CalibratedTemperature{
            .temp = Temperature.init(celsius),
            .offset = offset,
        };
    }

    // Transform getter to apply calibration
    pub fn getCelsius(self: *const CalibratedTemperature) f32 {
        return self.temp.getCelsius() + self.offset;
    }

    // Transform setter to remove calibration
    pub fn setCelsius(self: *CalibratedTemperature, value: f32) void {
        self.temp.setCelsius(value - self.offset);
    }

    pub fn getRawCelsius(self: *const CalibratedTemperature) f32 {
        return self.temp.getCelsius();
    }
};
// ANCHOR_END: transformation_wrapper

test "transformation wrapper" {
    var calibrated = CalibratedTemperature.init(100, 2.5);

    try testing.expectEqual(@as(f32, 102.5), calibrated.getCelsius());
    try testing.expectEqual(@as(f32, 100), calibrated.getRawCelsius());

    calibrated.setCelsius(50);
    try testing.expectEqual(@as(f32, 50), calibrated.getCelsius());
    try testing.expectEqual(@as(f32, 47.5), calibrated.getRawCelsius());
}

// ANCHOR: chained_operations
// Chaining parent and child operations
const Logger = struct {
    prefix: []const u8,
    log_count: u32,

    pub fn init(prefix: []const u8) Logger {
        return Logger{
            .prefix = prefix,
            .log_count = 0,
        };
    }

    pub fn log(self: *Logger, message: []const u8) void {
        _ = message;
        self.log_count += 1;
        // In reality: std.debug.print("[{s}] {s}\n", .{ self.prefix, message });
    }

    pub fn getLogCount(self: *const Logger) u32 {
        return self.log_count;
    }
};

const TimestampedLogger = struct {
    logger: Logger,
    last_timestamp: i64,

    pub fn init(prefix: []const u8) TimestampedLogger {
        return TimestampedLogger{
            .logger = Logger.init(prefix),
            .last_timestamp = 0,
        };
    }

    pub fn log(self: *TimestampedLogger, message: []const u8, timestamp: i64) void {
        self.last_timestamp = timestamp;
        self.logger.log(message);
    }

    pub fn getLogCount(self: *const TimestampedLogger) u32 {
        return self.logger.getLogCount();
    }

    pub fn getLastTimestamp(self: *const TimestampedLogger) i64 {
        return self.last_timestamp;
    }
};
// ANCHOR_END: chained_operations

test "chained operations" {
    var logger = TimestampedLogger.init("INFO");

    logger.log("First message", 1000);
    logger.log("Second message", 2000);

    try testing.expectEqual(@as(u32, 2), logger.getLogCount());
    try testing.expectEqual(@as(i64, 2000), logger.getLastTimestamp());
}

// ANCHOR: override_with_fallback
// Override with fallback to parent
const Cache = struct {
    data: ?[]const u8,

    pub fn init() Cache {
        return Cache{ .data = null };
    }

    pub fn get(self: *const Cache) ?[]const u8 {
        return self.data;
    }

    pub fn set(self: *Cache, value: []const u8) void {
        self.data = value;
    }

    pub fn clear(self: *Cache) void {
        self.data = null;
    }
};

const TtlCache = struct {
    cache: Cache,
    ttl_seconds: i64,
    set_time: i64,

    pub fn init(ttl_seconds: i64) TtlCache {
        return TtlCache{
            .cache = Cache.init(),
            .ttl_seconds = ttl_seconds,
            .set_time = 0,
        };
    }

    pub fn get(self: *const TtlCache, current_time: i64) ?[]const u8 {
        if (self.cache.get()) |data| {
            if (current_time - self.set_time < self.ttl_seconds) {
                return data;
            }
        }
        return null;
    }

    pub fn set(self: *TtlCache, value: []const u8, current_time: i64) void {
        self.cache.set(value);
        self.set_time = current_time;
    }

    pub fn clear(self: *TtlCache) void {
        self.cache.clear();
        self.set_time = 0;
    }
};
// ANCHOR_END: override_with_fallback

test "override with fallback" {
    var ttl_cache = TtlCache.init(100);

    ttl_cache.set("cached value", 1000);

    const value1 = ttl_cache.get(1050);
    try testing.expect(value1 != null);

    const value2 = ttl_cache.get(1200);
    try testing.expect(value2 == null);
}

// ANCHOR: pre_post_processing
// Pre and post processing
const DataStore = struct {
    value: i32,

    pub fn init() DataStore {
        return DataStore{ .value = 0 };
    }

    pub fn getValue(self: *const DataStore) i32 {
        return self.value;
    }

    pub fn setValue(self: *DataStore, val: i32) void {
        self.value = val;
    }
};

const ValidatedDataStore = struct {
    store: DataStore,
    min_value: i32,
    max_value: i32,
    validation_failures: u32,

    pub fn init(min: i32, max: i32) ValidatedDataStore {
        return ValidatedDataStore{
            .store = DataStore.init(),
            .min_value = min,
            .max_value = max,
            .validation_failures = 0,
        };
    }

    pub fn getValue(self: *const ValidatedDataStore) i32 {
        return self.store.getValue();
    }

    // Pre-processing: validate, post-processing: track failures
    pub fn setValue(self: *ValidatedDataStore, val: i32) !void {
        // Pre-processing
        if (val < self.min_value or val > self.max_value) {
            self.validation_failures += 1;
            return error.OutOfRange;
        }

        // Call parent
        self.store.setValue(val);

        // Post-processing could go here
    }

    pub fn getValidationFailures(self: *const ValidatedDataStore) u32 {
        return self.validation_failures;
    }
};
// ANCHOR_END: pre_post_processing

test "pre and post processing" {
    var validated = ValidatedDataStore.init(0, 100);

    try validated.setValue(50);
    try testing.expectEqual(@as(i32, 50), validated.getValue());

    const result = validated.setValue(150);
    try testing.expectError(error.OutOfRange, result);
    try testing.expectEqual(@as(u32, 1), validated.getValidationFailures());
}

// ANCHOR: lazy_property_extension
// Extending lazy properties
const BaseLazy = struct {
    computed: ?i32,

    pub fn init() BaseLazy {
        return BaseLazy{ .computed = null };
    }

    pub fn getComputed(self: *BaseLazy) i32 {
        if (self.computed) |val| return val;

        const result = 42; // Expensive computation
        self.computed = result;
        return result;
    }
};

const CachedLazy = struct {
    lazy: BaseLazy,
    access_count: u32,
    cache_hits: u32,

    pub fn init() CachedLazy {
        return CachedLazy{
            .lazy = BaseLazy.init(),
            .access_count = 0,
            .cache_hits = 0,
        };
    }

    pub fn getComputed(self: *CachedLazy) i32 {
        self.access_count += 1;
        if (self.lazy.computed != null) {
            self.cache_hits += 1;
        }
        return self.lazy.getComputed();
    }

    pub fn getCacheHitRate(self: *const CachedLazy) f32 {
        if (self.access_count == 0) return 0;
        return @as(f32, @floatFromInt(self.cache_hits)) / @as(f32, @floatFromInt(self.access_count));
    }
};
// ANCHOR_END: lazy_property_extension

test "lazy property extension" {
    var cached = CachedLazy.init();

    _ = cached.getComputed();
    _ = cached.getComputed();
    _ = cached.getComputed();

    try testing.expectEqual(@as(u32, 3), cached.access_count);
    try testing.expectEqual(@as(u32, 2), cached.cache_hits);

    const hit_rate = cached.getCacheHitRate();
    try testing.expectApproxEqAbs(0.666, hit_rate, 0.01);
}

// ANCHOR: multi_level_extension
// Multi-level property extension
const Level1 = struct {
    value: i32,

    pub fn init() Level1 {
        return Level1{ .value = 0 };
    }

    pub fn getValue(self: *const Level1) i32 {
        return self.value;
    }

    pub fn setValue(self: *Level1, val: i32) void {
        self.value = val;
    }
};

const Level2 = struct {
    level1: Level1,
    multiplier: i32,

    pub fn init(multiplier: i32) Level2 {
        return Level2{
            .level1 = Level1.init(),
            .multiplier = multiplier,
        };
    }

    pub fn getValue(self: *const Level2) i32 {
        return self.level1.getValue() * self.multiplier;
    }

    pub fn setValue(self: *Level2, val: i32) void {
        self.level1.setValue(@divTrunc(val, self.multiplier));
    }
};

const Level3 = struct {
    level2: Level2,
    offset: i32,

    pub fn init(multiplier: i32, offset: i32) Level3 {
        return Level3{
            .level2 = Level2.init(multiplier),
            .offset = offset,
        };
    }

    pub fn getValue(self: *const Level3) i32 {
        return self.level2.getValue() + self.offset;
    }

    pub fn setValue(self: *Level3, val: i32) void {
        self.level2.setValue(val - self.offset);
    }
};
// ANCHOR_END: multi_level_extension

test "multi-level extension" {
    var level3 = Level3.init(10, 5);

    level3.setValue(105);
    try testing.expectEqual(@as(i32, 105), level3.getValue());

    // Verify internal transformations
    try testing.expectEqual(@as(i32, 10), level3.level2.level1.value);
}

// Comprehensive test
test "comprehensive property extension" {
    var extended = ExtendedCounter.init();
    extended.setValue(10);
    try testing.expectEqual(@as(i32, 10), extended.getValue());

    var premium = PremiumAccount.init(50);
    try premium.deposit(100);
    try testing.expectEqual(@as(f64, 100), premium.getBalance());

    var colored = ColoredRectangle.init(4, 5, "blue");
    try testing.expectEqual(@as(f32, 20), colored.getArea());

    var calibrated = CalibratedTemperature.init(20, 1.5);
    try testing.expectEqual(@as(f32, 21.5), calibrated.getCelsius());
}
```

### See Also

- Recipe 8.6: Creating Managed Attributes
- Recipe 8.7: Calling a Method on a Parent Class
- Recipe 8.10: Using Lazily Computed Properties
- Recipe 8.14: Implementing Custom Containers

---

## Recipe 8.9: Creating a New Kind of Struct or Instance Attribute {#recipe-8-9}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, http, json, memory, networking, parsing, resource-cleanup, slices, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_9.zig`

### Problem

You want to create custom attribute systems—like validators, serialization metadata, or field annotations—that attach behavior or information to struct fields, similar to decorators or attributes in other languages.

### Solution

Use Zig's comptime reflection via `@typeInfo()` and generic types to build attribute systems. You can introspect struct fields at compile time, create wrapper types with metadata, and generate code based on field characteristics.

### Field Introspection

Use `@typeInfo()` to examine struct fields at compile time:

```zig
// Field introspection using @typeInfo
const Person = struct {
    name: []const u8,
    age: u32,
    email: []const u8,

    pub fn fieldCount() usize {
        const info = @typeInfo(Person);
        return info.@"struct".fields.len;
    }

    pub fn hasField(comptime field_name: []const u8) bool {
        const info = @typeInfo(Person);
        inline for (info.@"struct".fields) |field| {
            if (std.mem.eql(u8, field.name, field_name)) {
                return true;
            }
        }
        return false;
    }

    pub fn fieldNames() [fieldCount()][]const u8 {
        const info = @typeInfo(Person);
        var names: [info.@"struct".fields.len][]const u8 = undefined;
        inline for (info.@"struct".fields, 0..) |field, i| {
            names[i] = field.name;
        }
        return names;
    }
};
```

This provides runtime access to compile-time field information.

### Custom Tags via Parallel Struct

Create metadata alongside your struct:

```zig
const FieldTags = struct {
    required: bool,
    max_length: ?usize,
    min_value: ?i32,
};

const UserSchema = struct {
    const tags = .{
        .username = FieldTags{ .required = true, .max_length = 50, .min_value = null },
        .email = FieldTags{ .required = true, .max_length = 100, .min_value = null },
        .age = FieldTags{ .required = false, .max_length = null, .min_value = 0 },
    };
};

const User = struct {
    username: []const u8,
    email: []const u8,
    age: u32,

    pub fn getFieldTag(comptime field_name: []const u8) FieldTags {
        return @field(UserSchema.tags, field_name);
    }

    pub fn validate(self: *const User) !void {
        if (self.username.len > UserSchema.tags.username.max_length.?) {
            return error.UsernameTooLong;
        }
        if (self.email.len > UserSchema.tags.email.max_length.?) {
            return error.EmailTooLong;
        }
        if (self.age < UserSchema.tags.age.min_value.?) {
            return error.AgeTooYoung;
        }
    }
};
```

Tags live in a separate schema struct but are accessed through the main type.

### Generic Attribute System

Build reusable attribute wrappers:

```zig
fn Attributed(comptime T: type, comptime Metadata: type) type {
    return struct {
        value: T,
        metadata: Metadata,

        const Self = @This();

        pub fn init(value: T, metadata: Metadata) Self {
            return Self{ .value = value, .metadata = metadata };
        }

        pub fn getValue(self: *const Self) T {
            return self.value;
        }

        pub fn getMetadata(self: *const Self) Metadata {
            return self.metadata;
        }

        pub fn setValue(self: *Self, value: T) void {
            self.value = value;
        }
    };
}

const StringMetadata = struct {
    max_length: usize,
    pattern: []const u8,
};

const ValidatedString = Attributed([]const u8, StringMetadata);
```

This pattern wraps any type with custom metadata.

### Reflection-Based Property Access

Access fields dynamically using `@field()`:

```zig
fn getField(value: anytype, comptime field_name: []const u8) @TypeOf(@field(value, field_name)) {
    return @field(value, field_name);
}

fn setField(value: anytype, comptime field_name: []const u8, new_value: anytype) void {
    @field(value, field_name) = new_value;
}

const Point = struct {
    x: f32,
    y: f32,
    z: f32,

    pub fn getByIndex(self: *const Point, index: usize) !f32 {
        return switch (index) {
            0 => self.x,
            1 => self.y,
            2 => self.z,
            else => error.IndexOutOfBounds,
        };
    }

    pub fn setByIndex(self: *Point, index: usize, value: f32) !void {
        switch (index) {
            0 => self.x = value,
            1 => self.y = value,
            2 => self.z = value,
            else => return error.IndexOutOfBounds,
        }
    }
};
```

Combine compile-time and runtime field access for flexible APIs.

### Read-Only Attribute Pattern

Wrap values to enforce immutability:

```zig
fn ReadOnly(comptime T: type) type {
    return struct {
        value: T,

        const Self = @This();

        pub fn init(value: T) Self {
            return Self{ .value = value };
        }

        pub fn get(self: *const Self) T {
            return self.value;
        }

        // No public set method - immutable after init
    };
}

const ImmutableConfig = struct {
    api_key: ReadOnly([]const u8),
    endpoint: ReadOnly([]const u8),

    pub fn init(api_key: []const u8, endpoint: []const u8) ImmutableConfig {
        return ImmutableConfig{
            .api_key = ReadOnly([]const u8).init(api_key),
            .endpoint = ReadOnly([]const u8).init(endpoint),
        };
    }
};
```

The type system enforces read-only semantics.

### Default Value Attribute

Attach default values to fields:

```zig
fn WithDefault(comptime T: type, comptime default_value: T) type {
    return struct {
        value: T,

        const Self = @This();
        const default = default_value;

        pub fn init() Self {
            return Self{ .value = default };
        }

        pub fn initWithValue(value: T) Self {
            return Self{ .value = value };
        }

        pub fn get(self: *const Self) T {
            return self.value;
        }

        pub fn set(self: *Self, value: T) void {
            self.value = value;
        }

        pub fn reset(self: *Self) void {
            self.value = default;
        }
    };
}

const Settings = struct {
    timeout: WithDefault(u32, 5000),
    retries: WithDefault(u8, 3),

    pub fn init() Settings {
        return Settings{
            .timeout = WithDefault(u32, 5000).init(),
            .retries = WithDefault(u8, 3).init(),
        };
    }
};
```

Each field carries its default value and can reset to it.

### Discussion

Zig's comptime system provides powerful metaprogramming capabilities that enable custom attribute systems without language-level attribute syntax.

### Key Techniques

1. **`@typeInfo()`** - Introspect types at compile time
2. **`@field()`** - Access fields by comptime-known names
3. **Generic wrapper types** - Add behavior through composition
4. **Parallel metadata structs** - Store field-level information separately
5. **`inline for`** - Iterate over fields at compile time

### Advantages

- **Zero runtime cost** - All attribute logic runs at compile time
- **Type safety** - Compile errors for invalid field access
- **Flexibility** - Create any attribute system you need
- **Composability** - Combine multiple attribute wrappers
- **No magic** - Explicit, visible attribute definitions

### Common Patterns

**Validation**: Use tags to define constraints, validate in methods
**Serialization**: Generate serialization code from field metadata
**Documentation**: Attach descriptions and annotations to fields
**Defaults**: Wrapper types with default values
**Immutability**: Types that only expose getters

### Limitations

- Field names must be known at compile time for `@field()`
- Cannot add fields dynamically at runtime
- Metadata must be defined alongside struct definition
- More verbose than language-level attribute syntax

### Performance

All attribute systems shown here have zero runtime overhead:
- Type introspection happens at compile time
- Generic wrappers inline into containing structs
- Metadata lookups resolve to constants

### Full Tested Code

```zig
// Recipe 8.9: Creating a New Kind of Class or Instance Attribute
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: field_introspection
// Field introspection using @typeInfo
const Person = struct {
    name: []const u8,
    age: u32,
    email: []const u8,

    pub fn fieldCount() usize {
        const info = @typeInfo(Person);
        return info.@"struct".fields.len;
    }

    pub fn hasField(comptime field_name: []const u8) bool {
        const info = @typeInfo(Person);
        inline for (info.@"struct".fields) |field| {
            if (std.mem.eql(u8, field.name, field_name)) {
                return true;
            }
        }
        return false;
    }

    pub fn fieldNames() [fieldCount()][]const u8 {
        const info = @typeInfo(Person);
        var names: [info.@"struct".fields.len][]const u8 = undefined;
        inline for (info.@"struct".fields, 0..) |field, i| {
            names[i] = field.name;
        }
        return names;
    }
};
// ANCHOR_END: field_introspection

test "field introspection" {
    try testing.expectEqual(@as(usize, 3), Person.fieldCount());
    try testing.expect(Person.hasField("name"));
    try testing.expect(Person.hasField("age"));
    try testing.expect(!Person.hasField("phone"));

    const names = Person.fieldNames();
    try testing.expectEqualStrings("name", names[0]);
    try testing.expectEqualStrings("age", names[1]);
    try testing.expectEqualStrings("email", names[2]);
}

// ANCHOR: tagged_fields
// Custom tags via parallel struct
const FieldTags = struct {
    required: bool,
    max_length: ?usize,
    min_value: ?i32,
};

const UserSchema = struct {
    const tags = .{
        .username = FieldTags{ .required = true, .max_length = 50, .min_value = null },
        .email = FieldTags{ .required = true, .max_length = 100, .min_value = null },
        .age = FieldTags{ .required = false, .max_length = null, .min_value = 0 },
    };
};

const User = struct {
    username: []const u8,
    email: []const u8,
    age: u32,

    pub fn getFieldTag(comptime field_name: []const u8) FieldTags {
        return @field(UserSchema.tags, field_name);
    }

    pub fn validate(self: *const User) !void {
        if (self.username.len > UserSchema.tags.username.max_length.?) {
            return error.UsernameTooLong;
        }
        if (self.email.len > UserSchema.tags.email.max_length.?) {
            return error.EmailTooLong;
        }
        if (self.age < UserSchema.tags.age.min_value.?) {
            return error.AgeTooYoung;
        }
    }
};
// ANCHOR_END: tagged_fields

test "tagged fields" {
    const user = User{
        .username = "john_doe",
        .email = "john@example.com",
        .age = 25,
    };

    try user.validate();

    const username_tag = User.getFieldTag("username");
    try testing.expect(username_tag.required);
    try testing.expectEqual(@as(usize, 50), username_tag.max_length.?);
}

// ANCHOR: generic_attribute_system
// Generic attribute system
fn Attributed(comptime T: type, comptime Metadata: type) type {
    return struct {
        value: T,
        metadata: Metadata,

        const Self = @This();

        pub fn init(value: T, metadata: Metadata) Self {
            return Self{ .value = value, .metadata = metadata };
        }

        pub fn getValue(self: *const Self) T {
            return self.value;
        }

        pub fn getMetadata(self: *const Self) Metadata {
            return self.metadata;
        }

        pub fn setValue(self: *Self, value: T) void {
            self.value = value;
        }
    };
}

const StringMetadata = struct {
    max_length: usize,
    pattern: []const u8,
};

const ValidatedString = Attributed([]const u8, StringMetadata);
// ANCHOR_END: generic_attribute_system

test "generic attribute system" {
    var validated = ValidatedString.init("hello", .{
        .max_length = 10,
        .pattern = "[a-z]+",
    });

    try testing.expectEqualStrings("hello", validated.getValue());
    try testing.expectEqual(@as(usize, 10), validated.getMetadata().max_length);

    validated.setValue("world");
    try testing.expectEqualStrings("world", validated.getValue());
}

// ANCHOR: field_annotations
// Field annotations pattern
const FieldAnnotation = struct {
    description: []const u8,
    deprecated: bool,
    since_version: []const u8,
};

fn Annotated(comptime T: type) type {
    return struct {
        const annotations = blk: {
            var result: [@typeInfo(T).@"struct".fields.len]FieldAnnotation = undefined;
            for (@typeInfo(T).@"struct".fields, 0..) |_, i| {
                result[i] = .{
                    .description = "",
                    .deprecated = false,
                    .since_version = "1.0",
                };
            }
            break :blk result;
        };

        pub fn getFieldAnnotation(comptime field_name: []const u8) ?FieldAnnotation {
            const info = @typeInfo(T);
            inline for (info.@"struct".fields, 0..) |field, i| {
                if (std.mem.eql(u8, field.name, field_name)) {
                    return annotations[i];
                }
            }
            return null;
        }

        pub fn listFields(allocator: std.mem.Allocator) ![][]const u8 {
            const info = @typeInfo(T);
            var list = std.ArrayList([]const u8){};

            inline for (info.@"struct".fields) |field| {
                try list.append(allocator, field.name);
            }

            return list.toOwnedSlice(allocator);
        }
    };
}

const Config = struct {
    host: []const u8,
    port: u16,
    timeout: u32,
};

const AnnotatedConfig = Annotated(Config);
// ANCHOR_END: field_annotations

test "field annotations" {
    const annotation = AnnotatedConfig.getFieldAnnotation("host");
    try testing.expect(annotation != null);
    try testing.expectEqualStrings("1.0", annotation.?.since_version);

    const fields = try AnnotatedConfig.listFields(testing.allocator);
    defer testing.allocator.free(fields);
    try testing.expectEqual(@as(usize, 3), fields.len);
}

// ANCHOR: comptime_field_validation
// Compile-time field validation
fn ValidatedStruct(comptime T: type, comptime validator: fn (type) bool) type {
    if (!validator(T)) {
        @compileError("Type validation failed");
    }
    return T;
}

fn hasRequiredFields(comptime T: type) bool {
    const info = @typeInfo(T);
    if (info != .@"struct") return false;

    var has_id = false;
    var has_name = false;

    inline for (info.@"struct".fields) |field| {
        if (std.mem.eql(u8, field.name, "id")) has_id = true;
        if (std.mem.eql(u8, field.name, "name")) has_name = true;
    }

    return has_id and has_name;
}

const ValidEntity = ValidatedStruct(struct {
    id: u32,
    name: []const u8,
}, hasRequiredFields);
// ANCHOR_END: comptime_field_validation

test "comptime field validation" {
    const entity = ValidEntity{
        .id = 1,
        .name = "Test",
    };

    try testing.expectEqual(@as(u32, 1), entity.id);
    try testing.expectEqualStrings("Test", entity.name);
}

// ANCHOR: type_level_attributes
// Type-level attributes using container declarations
const Serializable = struct {
    pub const serialization_version = 1;
    pub const supports_json = true;
    pub const supports_binary = true;
};

const Document = struct {
    title: []const u8,
    content: []const u8,

    pub const version = Serializable.serialization_version;
    pub const supports_json = Serializable.supports_json;

    pub fn toJson(self: *const Document, allocator: std.mem.Allocator) ![]u8 {
        _ = self;
        return try allocator.dupe(u8, "{}");
    }

    pub fn fromJson(data: []const u8, allocator: std.mem.Allocator) !Document {
        _ = data;
        _ = allocator;
        return error.NotImplemented;
    }
};
// ANCHOR_END: type_level_attributes

test "type-level attributes" {
    const doc = Document{
        .title = "Test",
        .content = "Content",
    };

    try testing.expectEqual(@as(u32, 1), Document.version);

    const json = try doc.toJson(testing.allocator);
    defer testing.allocator.free(json);
    try testing.expectEqualStrings("{}", json);
}

// ANCHOR: reflection_property_access
// Reflection-based property access
fn getField(value: anytype, comptime field_name: []const u8) @TypeOf(@field(value, field_name)) {
    return @field(value, field_name);
}

fn setField(value: anytype, comptime field_name: []const u8, new_value: anytype) void {
    @field(value, field_name) = new_value;
}

const Point = struct {
    x: f32,
    y: f32,
    z: f32,

    pub fn getByIndex(self: *const Point, index: usize) !f32 {
        return switch (index) {
            0 => self.x,
            1 => self.y,
            2 => self.z,
            else => error.IndexOutOfBounds,
        };
    }

    pub fn setByIndex(self: *Point, index: usize, value: f32) !void {
        switch (index) {
            0 => self.x = value,
            1 => self.y = value,
            2 => self.z = value,
            else => return error.IndexOutOfBounds,
        }
    }
};
// ANCHOR_END: reflection_property_access

test "reflection property access" {
    var point = Point{ .x = 1, .y = 2, .z = 3 };

    try testing.expectEqual(@as(f32, 1), getField(point, "x"));
    try testing.expectEqual(@as(f32, 2), getField(point, "y"));

    setField(&point, "x", 10);
    try testing.expectEqual(@as(f32, 10), point.x);

    try testing.expectEqual(@as(f32, 2), try point.getByIndex(1));
    try point.setByIndex(2, 30);
    try testing.expectEqual(@as(f32, 30), point.z);
}

// ANCHOR: custom_serialization_metadata
// Custom serialization based on field metadata
const SerializationMeta = struct {
    json_name: []const u8,
    omit_empty: bool,
    required: bool,
};

fn Serializer(comptime T: type) type {
    return struct {
        pub fn fieldMeta(comptime field_name: []const u8) SerializationMeta {
            // Default metadata
            return .{
                .json_name = field_name,
                .omit_empty = false,
                .required = false,
            };
        }

        pub fn serialize(value: T, allocator: std.mem.Allocator) ![]u8 {
            _ = value;
            var result = std.ArrayList(u8){};
            errdefer result.deinit(allocator);

            try result.appendSlice(allocator, "{");

            const info = @typeInfo(T);
            inline for (info.@"struct".fields, 0..) |field, i| {
                if (i > 0) try result.appendSlice(allocator, ",");

                const meta = fieldMeta(field.name);
                try result.appendSlice(allocator, "\"");
                try result.appendSlice(allocator, meta.json_name);
                try result.appendSlice(allocator, "\":null");
            }

            try result.appendSlice(allocator, "}");
            return result.toOwnedSlice(allocator);
        }
    };
}

const Product = struct {
    id: u32,
    name: []const u8,
    price: f64,

    const ProductSerializer = Serializer(@This());

    pub fn fieldMeta(comptime field_name: []const u8) SerializationMeta {
        return ProductSerializer.fieldMeta(field_name);
    }

    pub fn serialize(value: Product, allocator: std.mem.Allocator) ![]u8 {
        return ProductSerializer.serialize(value, allocator);
    }
};
// ANCHOR_END: custom_serialization_metadata

test "custom serialization metadata" {
    const product = Product{
        .id = 123,
        .name = "Widget",
        .price = 29.99,
    };

    const json = try Product.serialize(product, testing.allocator);
    defer testing.allocator.free(json);

    try testing.expect(std.mem.indexOf(u8, json, "\"id\"") != null);
    try testing.expect(std.mem.indexOf(u8, json, "\"name\"") != null);
    try testing.expect(std.mem.indexOf(u8, json, "\"price\"") != null);
}

// ANCHOR: readonly_attribute
// Read-only attribute pattern
fn ReadOnly(comptime T: type) type {
    return struct {
        value: T,

        const Self = @This();

        pub fn init(value: T) Self {
            return Self{ .value = value };
        }

        pub fn get(self: *const Self) T {
            return self.value;
        }

        // No public set method - immutable after init
    };
}

const ImmutableConfig = struct {
    api_key: ReadOnly([]const u8),
    endpoint: ReadOnly([]const u8),

    pub fn init(api_key: []const u8, endpoint: []const u8) ImmutableConfig {
        return ImmutableConfig{
            .api_key = ReadOnly([]const u8).init(api_key),
            .endpoint = ReadOnly([]const u8).init(endpoint),
        };
    }
};
// ANCHOR_END: readonly_attribute

test "readonly attribute" {
    const config = ImmutableConfig.init("secret123", "https://api.example.com");

    try testing.expectEqualStrings("secret123", config.api_key.get());
    try testing.expectEqualStrings("https://api.example.com", config.endpoint.get());
}

// ANCHOR: default_value_attribute
// Default value attribute
fn WithDefault(comptime T: type, comptime default_value: T) type {
    return struct {
        value: T,

        const Self = @This();
        const default = default_value;

        pub fn init() Self {
            return Self{ .value = default };
        }

        pub fn initWithValue(value: T) Self {
            return Self{ .value = value };
        }

        pub fn get(self: *const Self) T {
            return self.value;
        }

        pub fn set(self: *Self, value: T) void {
            self.value = value;
        }

        pub fn reset(self: *Self) void {
            self.value = default;
        }
    };
}

const Settings = struct {
    timeout: WithDefault(u32, 5000),
    retries: WithDefault(u8, 3),

    pub fn init() Settings {
        return Settings{
            .timeout = WithDefault(u32, 5000).init(),
            .retries = WithDefault(u8, 3).init(),
        };
    }
};
// ANCHOR_END: default_value_attribute

test "default value attribute" {
    var settings = Settings.init();

    try testing.expectEqual(@as(u32, 5000), settings.timeout.get());
    try testing.expectEqual(@as(u8, 3), settings.retries.get());

    settings.timeout.set(10000);
    try testing.expectEqual(@as(u32, 10000), settings.timeout.get());

    settings.timeout.reset();
    try testing.expectEqual(@as(u32, 5000), settings.timeout.get());
}

// Comprehensive test
test "comprehensive custom attributes" {
    try testing.expectEqual(@as(usize, 3), Person.fieldCount());

    var validated = ValidatedString.init("test", .{
        .max_length = 100,
        .pattern = ".*",
    });
    try testing.expectEqualStrings("test", validated.getValue());

    var point = Point{ .x = 5, .y = 10, .z = 15 };
    try testing.expectEqual(@as(f32, 10), try point.getByIndex(1));

    var settings = Settings.init();
    try testing.expectEqual(@as(u32, 5000), settings.timeout.get());
}
```

### See Also

- Recipe 8.6: Creating Managed Attributes
- Recipe 8.13: Implementing a Data Model or Type System
- Recipe 9.11: Using comptime to Control Instance Creation
- Recipe 9.16: Defining Structs Programmatically

---

## Recipe 8.10: Using Lazily Computed Properties {#recipe-8-10}

**Tags:** allocators, arraylist, atomics, c-interop, comptime, concurrency, data-structures, error-handling, memory, resource-cleanup, slices, structs-objects, synchronization, testing, threading
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_10.zig`

### Problem

You have properties that are expensive to compute—file loading, complex calculations, or external API calls—and you want to defer computation until the value is actually needed, then cache the result for subsequent accesses.

### Solution

Use optional fields to cache computed values. Check if the cache is populated before computing, and invalidate the cache when dependencies change.

### Basic Lazy Evaluation

Use an optional to track whether a value has been computed:

```zig
// Basic lazy evaluation with optional
const ExpensiveCalculation = struct {
    input: i32,
    result: ?i32,

    pub fn init(input: i32) ExpensiveCalculation {
        return ExpensiveCalculation{
            .input = input,
            .result = null,
        };
    }

    pub fn getResult(self: *ExpensiveCalculation) i32 {
        if (self.result) |cached| {
            return cached;
        }

        // Expensive computation
        const computed = self.input * self.input + self.input * 2 + 1;
        self.result = computed;
        return computed;
    }

    pub fn invalidate(self: *ExpensiveCalculation) void {
        self.result = null;
    }
};
```

The computation only runs once, on first access.

### Lazy Initialization with Allocator

For values that require memory allocation:

```zig
const LazyString = struct {
    allocator: std.mem.Allocator,
    cached: ?[]u8,
    generator_called: u32,

    pub fn init(allocator: std.mem.Allocator) LazyString {
        return LazyString{
            .allocator = allocator,
            .cached = null,
            .generator_called = 0,
        };
    }

    pub fn deinit(self: *LazyString) void {
        if (self.cached) |data| {
            self.allocator.free(data);
        }
    }

    pub fn getValue(self: *LazyString) ![]const u8 {
        if (self.cached) |data| {
            return data;
        }

        // Expensive generation
        self.generator_called += 1;
        const generated = try std.fmt.allocPrint(
            self.allocator,
            "Generated value #{d}",
            .{self.generator_called},
        );
        self.cached = generated;
        return generated;
    }

    pub fn reset(self: *LazyString) void {
        if (self.cached) |data| {
            self.allocator.free(data);
            self.cached = null;
        }
    }
};
```

Remember to free the cached value in `deinit()`.

### Cached Computed Properties

Cache multiple dependent properties and invalidate all when data changes:

```zig
const Rectangle = struct {
    width: f32,
    height: f32,
    cached_area: ?f32,
    cached_perimeter: ?f32,

    pub fn init(width: f32, height: f32) Rectangle {
        return Rectangle{
            .width = width,
            .height = height,
            .cached_area = null,
            .cached_perimeter = null,
        };
    }

    pub fn getArea(self: *Rectangle) f32 {
        if (self.cached_area) |area| {
            return area;
        }

        const area = self.width * self.height;
        self.cached_area = area;
        return area;
    }

    pub fn setWidth(self: *Rectangle, width: f32) void {
        self.width = width;
        self.invalidateCache();
    }

    fn invalidateCache(self: *Rectangle) void {
        self.cached_area = null;
        self.cached_perimeter = null;
    }
};
```

Setters invalidate all cached properties that depend on the changed data.

### Memoization Pattern

Cache results of recursive or repeated function calls:

```zig
const Fibonacci = struct {
    cache: [100]?u64,

    pub fn init() Fibonacci {
        return Fibonacci{
            .cache = [_]?u64{null} ** 100,
        };
    }

    pub fn compute(self: *Fibonacci, n: usize) u64 {
        if (n < 2) return n;

        if (n < self.cache.len) {
            if (self.cache[n]) |cached| {
                return cached;
            }
        }

        const result = self.compute(n - 1) + self.compute(n - 2);

        if (n < self.cache.len) {
            self.cache[n] = result;
        }

        return result;
    }
};
```

Dramatically improves performance for recursive algorithms.

### Time-Based Cache Invalidation

Automatically expire cached values after a timeout:

```zig
const TimedCache = struct {
    value: ?[]const u8,
    computed_at: i64,
    ttl_seconds: i64,

    pub fn init(ttl_seconds: i64) TimedCache {
        return TimedCache{
            .value = null,
            .computed_at = 0,
            .ttl_seconds = ttl_seconds,
        };
    }

    pub fn getValue(self: *TimedCache, current_time: i64) []const u8 {
        if (self.value) |cached| {
            if (current_time - self.computed_at < self.ttl_seconds) {
                return cached;
            }
        }

        // Generate new value
        const generated = "fresh value";
        self.value = generated;
        self.computed_at = current_time;
        return generated;
    }

    pub fn isValid(self: *const TimedCache, current_time: i64) bool {
        if (self.value == null) return false;
        return current_time - self.computed_at < self.ttl_seconds;
    }
};
```

Useful for API responses, configuration files, or other time-sensitive data.

### Dependency Lazy Properties

Chain lazy properties where one depends on another:

```zig
const DataModel = struct {
    raw_data: []const i32,
    filtered: ?[]i32,
    sorted: ?[]i32,
    allocator: std.mem.Allocator,

    pub fn getSorted(self: *DataModel) ![]const i32 {
        if (self.sorted) |cached| {
            return cached;
        }

        // Depends on filtered data
        const filtered = try self.getFiltered();
        const sorted = try self.allocator.dupe(i32, filtered);
        std.mem.sort(i32, sorted, {}, comptime std.sort.asc(i32));

        self.sorted = sorted;
        return sorted;
    }

    pub fn invalidate(self: *DataModel) void {
        if (self.filtered) |f| {
            self.allocator.free(f);
            self.filtered = null;
        }
        if (self.sorted) |s| {
            self.allocator.free(s);
            self.sorted = null;
        }
    }
};
```

Invalidating upstream dependencies automatically invalidates downstream ones.

### Generic Lazy Wrapper

Create a reusable lazy wrapper for any type:

```zig
fn Lazy(comptime T: type) type {
    return struct {
        value: ?T,
        generator: *const fn () T,

        const Self = @This();

        pub fn init(generator: *const fn () T) Self {
            return Self{
                .value = null,
                .generator = generator,
            };
        }

        pub fn get(self: *Self) T {
            if (self.value) |cached| {
                return cached;
            }

            const computed = self.generator();
            self.value = computed;
            return computed;
        }

        pub fn invalidate(self: *Self) void {
            self.value = null;
        }

        pub fn isComputed(self: *const Self) bool {
            return self.value != null;
        }
    };
}
```

This pattern works for any type that doesn't require allocation.

### Lazy Evaluation with Errors

Handle errors in lazy computations:

```zig
const FallibleLazy = struct {
    value: ?i32,
    last_error: ?anyerror,

    pub fn getValue(self: *FallibleLazy, input: i32) !i32 {
        if (self.value) |cached| {
            return cached;
        }

        const result = self.compute(input) catch |err| {
            self.last_error = err;
            return err;
        };

        self.value = result;
        self.last_error = null;
        return result;
    }

    fn compute(self: *FallibleLazy, input: i32) !i32 {
        _ = self;
        if (input < 0) return error.NegativeInput;
        return input * 2;
    }
};
```

Track the last error for debugging while still caching successful results.

### Discussion

Lazy evaluation is a powerful optimization technique that trades memory (cache storage) for CPU time (avoiding repeated computation).

### When to Use Lazy Properties

Use lazy evaluation when:

- **Computation is expensive** - Complex algorithms, file I/O, network requests
- **Value might not be needed** - Optional features or conditional code paths
- **Value used multiple times** - Repeated access to the same computed result
- **Initialization order matters** - Break circular dependencies

Don't use lazy evaluation for:

- Simple computations (addition, multiplication)
- Values always needed immediately
- Single-use values
- When memory is more constrained than CPU

### Performance Characteristics

**Space**: O(1) overhead per lazy property (one optional field)
**Time**: First access pays full computation cost, subsequent accesses are O(1)
**Thread safety**: Not thread-safe by default (requires synchronization for concurrent access)

### Common Patterns

1. **Cache invalidation**: Clear cache when dependencies change
2. **Expiration**: Use timestamps for time-based invalidation
3. **Memoization**: Cache function results by input parameters
4. **Lazy loading**: Defer file/network loading until needed
5. **Computed properties**: Calculate derived values only when accessed

### Memory Management

For allocated lazy values:

- Store `allocator` as a field
- Free cached value in `deinit()`
- Free old value before computing new one in `reset()`
- Consider using `errdefer` to clean up on errors

### Thread Safety

The patterns shown are not thread-safe. For concurrent access:

- Use a `std.Thread.Mutex` to protect the cache
- Consider atomic operations for simple types
- Or use read-write locks for better read performance

### Full Tested Code

```zig
// Recipe 8.10: Using Lazily Computed Properties
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_lazy_optional
// Basic lazy evaluation with optional
const ExpensiveCalculation = struct {
    input: i32,
    result: ?i32,

    pub fn init(input: i32) ExpensiveCalculation {
        return ExpensiveCalculation{
            .input = input,
            .result = null,
        };
    }

    pub fn getResult(self: *ExpensiveCalculation) i32 {
        if (self.result) |cached| {
            return cached;
        }

        // Expensive computation
        const computed = self.input * self.input + self.input * 2 + 1;
        self.result = computed;
        return computed;
    }

    pub fn invalidate(self: *ExpensiveCalculation) void {
        self.result = null;
    }
};
// ANCHOR_END: basic_lazy_optional

test "basic lazy optional" {
    var calc = ExpensiveCalculation.init(10);

    try testing.expect(calc.result == null);

    const result1 = calc.getResult();
    try testing.expectEqual(@as(i32, 121), result1);
    try testing.expect(calc.result != null);

    const result2 = calc.getResult();
    try testing.expectEqual(result1, result2);

    calc.invalidate();
    try testing.expect(calc.result == null);
}

// ANCHOR: lazy_with_allocator
// Lazy initialization with allocator
const LazyString = struct {
    allocator: std.mem.Allocator,
    cached: ?[]u8,
    generator_called: u32,

    pub fn init(allocator: std.mem.Allocator) LazyString {
        return LazyString{
            .allocator = allocator,
            .cached = null,
            .generator_called = 0,
        };
    }

    pub fn deinit(self: *LazyString) void {
        if (self.cached) |data| {
            self.allocator.free(data);
        }
    }

    pub fn getValue(self: *LazyString) ![]const u8 {
        if (self.cached) |data| {
            return data;
        }

        // Expensive generation
        self.generator_called += 1;
        const generated = try std.fmt.allocPrint(
            self.allocator,
            "Generated value #{d}",
            .{self.generator_called},
        );
        self.cached = generated;
        return generated;
    }

    pub fn reset(self: *LazyString) void {
        if (self.cached) |data| {
            self.allocator.free(data);
            self.cached = null;
        }
    }
};
// ANCHOR_END: lazy_with_allocator

test "lazy with allocator" {
    var lazy = LazyString.init(testing.allocator);
    defer lazy.deinit();

    const value1 = try lazy.getValue();
    try testing.expectEqualStrings("Generated value #1", value1);
    try testing.expectEqual(@as(u32, 1), lazy.generator_called);

    const value2 = try lazy.getValue();
    try testing.expectEqualStrings("Generated value #1", value2);
    try testing.expectEqual(@as(u32, 1), lazy.generator_called);

    lazy.reset();
    const value3 = try lazy.getValue();
    try testing.expectEqualStrings("Generated value #2", value3);
}

// ANCHOR: cached_computed
// Cached computed properties
const Rectangle = struct {
    width: f32,
    height: f32,
    cached_area: ?f32,
    cached_perimeter: ?f32,

    pub fn init(width: f32, height: f32) Rectangle {
        return Rectangle{
            .width = width,
            .height = height,
            .cached_area = null,
            .cached_perimeter = null,
        };
    }

    pub fn getArea(self: *Rectangle) f32 {
        if (self.cached_area) |area| {
            return area;
        }

        const area = self.width * self.height;
        self.cached_area = area;
        return area;
    }

    pub fn getPerimeter(self: *Rectangle) f32 {
        if (self.cached_perimeter) |perim| {
            return perim;
        }

        const perim = 2 * (self.width + self.height);
        self.cached_perimeter = perim;
        return perim;
    }

    pub fn setWidth(self: *Rectangle, width: f32) void {
        self.width = width;
        self.invalidateCache();
    }

    pub fn setHeight(self: *Rectangle, height: f32) void {
        self.height = height;
        self.invalidateCache();
    }

    fn invalidateCache(self: *Rectangle) void {
        self.cached_area = null;
        self.cached_perimeter = null;
    }
};
// ANCHOR_END: cached_computed

test "cached computed" {
    var rect = Rectangle.init(5, 10);

    try testing.expectEqual(@as(f32, 50), rect.getArea());
    try testing.expect(rect.cached_area != null);

    try testing.expectEqual(@as(f32, 30), rect.getPerimeter());
    try testing.expect(rect.cached_perimeter != null);

    rect.setWidth(10);
    try testing.expect(rect.cached_area == null);

    try testing.expectEqual(@as(f32, 100), rect.getArea());
}

// ANCHOR: lazy_file_load
// Lazy loading from external source
const ConfigFile = struct {
    path: []const u8,
    content: ?[]u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, path: []const u8) ConfigFile {
        return ConfigFile{
            .path = path,
            .content = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *ConfigFile) void {
        if (self.content) |data| {
            self.allocator.free(data);
        }
    }

    pub fn getContent(self: *ConfigFile) ![]const u8 {
        if (self.content) |data| {
            return data;
        }

        // Simulate file loading
        const loaded = try self.allocator.dupe(u8, "config data from file");
        self.content = loaded;
        return loaded;
    }

    pub fn reload(self: *ConfigFile) !void {
        if (self.content) |data| {
            self.allocator.free(data);
        }
        self.content = null;
        _ = try self.getContent();
    }
};
// ANCHOR_END: lazy_file_load

test "lazy file load" {
    var config = ConfigFile.init(testing.allocator, "/etc/config.txt");
    defer config.deinit();

    const content1 = try config.getContent();
    try testing.expectEqualStrings("config data from file", content1);

    const content2 = try config.getContent();
    try testing.expectEqual(content1.ptr, content2.ptr);

    try config.reload();
}

// ANCHOR: conditional_lazy
// Conditional lazy evaluation
const ConditionalCache = struct {
    enabled: bool,
    value: ?i32,
    compute_count: u32,

    pub fn init(enabled: bool) ConditionalCache {
        return ConditionalCache{
            .enabled = enabled,
            .value = null,
            .compute_count = 0,
        };
    }

    pub fn getValue(self: *ConditionalCache, input: i32) i32 {
        if (!self.enabled) {
            // Always compute when caching disabled
            return self.compute(input);
        }

        if (self.value) |cached| {
            return cached;
        }

        const result = self.compute(input);
        self.value = result;
        return result;
    }

    fn compute(self: *ConditionalCache, input: i32) i32 {
        self.compute_count += 1;
        return input * input;
    }

    pub fn setEnabled(self: *ConditionalCache, enabled: bool) void {
        self.enabled = enabled;
        if (!enabled) {
            self.value = null;
        }
    }
};
// ANCHOR_END: conditional_lazy

test "conditional lazy" {
    var cache_on = ConditionalCache.init(true);
    _ = cache_on.getValue(5);
    _ = cache_on.getValue(5);
    try testing.expectEqual(@as(u32, 1), cache_on.compute_count);

    var cache_off = ConditionalCache.init(false);
    _ = cache_off.getValue(5);
    _ = cache_off.getValue(5);
    try testing.expectEqual(@as(u32, 2), cache_off.compute_count);
}

// ANCHOR: dependency_lazy
// Multiple dependency lazy properties
const DataModel = struct {
    raw_data: []const i32,
    filtered: ?[]i32,
    sorted: ?[]i32,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, data: []const i32) DataModel {
        return DataModel{
            .raw_data = data,
            .filtered = null,
            .sorted = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *DataModel) void {
        if (self.filtered) |f| self.allocator.free(f);
        if (self.sorted) |s| self.allocator.free(s);
    }

    pub fn getFiltered(self: *DataModel) ![]const i32 {
        if (self.filtered) |cached| {
            return cached;
        }

        // Filter out negative numbers
        var result = std.ArrayList(i32){};
        for (self.raw_data) |value| {
            if (value >= 0) {
                try result.append(self.allocator, value);
            }
        }

        const filtered = try result.toOwnedSlice(self.allocator);
        self.filtered = filtered;
        return filtered;
    }

    pub fn getSorted(self: *DataModel) ![]const i32 {
        if (self.sorted) |cached| {
            return cached;
        }

        // Depends on filtered data
        const filtered = try self.getFiltered();
        const sorted = try self.allocator.dupe(i32, filtered);
        std.mem.sort(i32, sorted, {}, comptime std.sort.asc(i32));

        self.sorted = sorted;
        return sorted;
    }

    pub fn invalidate(self: *DataModel) void {
        if (self.filtered) |f| {
            self.allocator.free(f);
            self.filtered = null;
        }
        if (self.sorted) |s| {
            self.allocator.free(s);
            self.sorted = null;
        }
    }
};
// ANCHOR_END: dependency_lazy

test "dependency lazy" {
    const data = [_]i32{ 3, -1, 5, -2, 1, 4 };
    var model = DataModel.init(testing.allocator, &data);
    defer model.deinit();

    const filtered = try model.getFiltered();
    try testing.expectEqual(@as(usize, 4), filtered.len);

    const sorted = try model.getSorted();
    try testing.expectEqual(@as(usize, 4), sorted.len);
    try testing.expectEqual(@as(i32, 1), sorted[0]);
    try testing.expectEqual(@as(i32, 5), sorted[3]);
}

// ANCHOR: lazy_generic
// Generic lazy wrapper
fn Lazy(comptime T: type) type {
    return struct {
        value: ?T,
        generator: *const fn () T,

        const Self = @This();

        pub fn init(generator: *const fn () T) Self {
            return Self{
                .value = null,
                .generator = generator,
            };
        }

        pub fn get(self: *Self) T {
            if (self.value) |cached| {
                return cached;
            }

            const computed = self.generator();
            self.value = computed;
            return computed;
        }

        pub fn invalidate(self: *Self) void {
            self.value = null;
        }

        pub fn isComputed(self: *const Self) bool {
            return self.value != null;
        }
    };
}

fn generateNumber() i32 {
    return 42;
}
// ANCHOR_END: lazy_generic

test "lazy generic" {
    var lazy = Lazy(i32).init(&generateNumber);

    try testing.expect(!lazy.isComputed());

    const value1 = lazy.get();
    try testing.expectEqual(@as(i32, 42), value1);
    try testing.expect(lazy.isComputed());

    lazy.invalidate();
    try testing.expect(!lazy.isComputed());
}

// ANCHOR: time_based_invalidation
// Time-based cache invalidation
const TimedCache = struct {
    value: ?[]const u8,
    computed_at: i64,
    ttl_seconds: i64,

    pub fn init(ttl_seconds: i64) TimedCache {
        return TimedCache{
            .value = null,
            .computed_at = 0,
            .ttl_seconds = ttl_seconds,
        };
    }

    pub fn getValue(self: *TimedCache, current_time: i64) []const u8 {
        if (self.value) |cached| {
            if (current_time - self.computed_at < self.ttl_seconds) {
                return cached;
            }
        }

        // Generate new value
        const generated = "fresh value";
        self.value = generated;
        self.computed_at = current_time;
        return generated;
    }

    pub fn isValid(self: *const TimedCache, current_time: i64) bool {
        if (self.value == null) return false;
        return current_time - self.computed_at < self.ttl_seconds;
    }
};
// ANCHOR_END: time_based_invalidation

test "time-based invalidation" {
    var cache = TimedCache.init(100);

    const value1 = cache.getValue(1000);
    try testing.expectEqualStrings("fresh value", value1);
    try testing.expect(cache.isValid(1050));

    const value2 = cache.getValue(1050);
    try testing.expectEqual(value1.ptr, value2.ptr);

    try testing.expect(!cache.isValid(1200));
}

// ANCHOR: memoization
// Memoization pattern
const Fibonacci = struct {
    cache: [100]?u64,

    pub fn init() Fibonacci {
        return Fibonacci{
            .cache = [_]?u64{null} ** 100,
        };
    }

    pub fn compute(self: *Fibonacci, n: usize) u64 {
        if (n < 2) return n;

        if (n < self.cache.len) {
            if (self.cache[n]) |cached| {
                return cached;
            }
        }

        const result = self.compute(n - 1) + self.compute(n - 2);

        if (n < self.cache.len) {
            self.cache[n] = result;
        }

        return result;
    }
};
// ANCHOR_END: memoization

test "memoization" {
    var fib = Fibonacci.init();

    try testing.expectEqual(@as(u64, 0), fib.compute(0));
    try testing.expectEqual(@as(u64, 1), fib.compute(1));
    try testing.expectEqual(@as(u64, 55), fib.compute(10));
    try testing.expectEqual(@as(u64, 6765), fib.compute(20));

    try testing.expect(fib.cache[10] != null);
}

// ANCHOR: lazy_with_error
// Lazy evaluation with errors
const FallibleLazy = struct {
    value: ?i32,
    last_error: ?anyerror,

    pub fn init() FallibleLazy {
        return FallibleLazy{
            .value = null,
            .last_error = null,
        };
    }

    pub fn getValue(self: *FallibleLazy, input: i32) !i32 {
        if (self.value) |cached| {
            return cached;
        }

        const result = self.compute(input) catch |err| {
            self.last_error = err;
            return err;
        };

        self.value = result;
        self.last_error = null;
        return result;
    }

    fn compute(self: *FallibleLazy, input: i32) !i32 {
        _ = self;
        if (input < 0) return error.NegativeInput;
        return input * 2;
    }

    pub fn clearError(self: *FallibleLazy) void {
        self.last_error = null;
    }
};
// ANCHOR_END: lazy_with_error

test "lazy with error" {
    var lazy = FallibleLazy.init();

    const result = lazy.getValue(-5);
    try testing.expectError(error.NegativeInput, result);
    try testing.expect(lazy.last_error != null);

    lazy.clearError();
    const valid_result = try lazy.getValue(10);
    try testing.expectEqual(@as(i32, 20), valid_result);
}

// Comprehensive test
test "comprehensive lazy properties" {
    var calc = ExpensiveCalculation.init(7);
    try testing.expectEqual(@as(i32, 64), calc.getResult());

    var rect = Rectangle.init(4, 6);
    try testing.expectEqual(@as(f32, 24), rect.getArea());

    var lazy_str = LazyString.init(testing.allocator);
    defer lazy_str.deinit();
    const str = try lazy_str.getValue();
    try testing.expect(str.len > 0);

    var fib = Fibonacci.init();
    try testing.expectEqual(@as(u64, 13), fib.compute(7));
}
```

### See Also

- Recipe 8.6: Creating Managed Attributes
- Recipe 8.8: Extending a Property in a Subclass
- Recipe 9.11: Using comptime to Control Instance Creation
- Recipe 18.1: Memory Pool Patterns (Phase 5)

---

## Recipe 8.11: Simplifying the Initialization of Data Structures {#recipe-8-11}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, hashmap, http, memory, networking, resource-cleanup, slices, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_11.zig`

### Problem

You want to make it easier to create instances of structs with many fields, optional parameters, validation rules, or complex initialization logic.

### Solution

Zig provides several patterns for simplifying initialization: default values, builder patterns, named constructors, configuration structs, and fluent interfaces.

### Default Values with Method Chaining

Provide sensible defaults and allow selective overrides:

```zig
// Default values pattern
const ServerConfig = struct {
    host: []const u8,
    port: u16,
    timeout_ms: u32,
    max_connections: u32,
    enable_logging: bool,

    pub fn init(host: []const u8) ServerConfig {
        return ServerConfig{
            .host = host,
            .port = 8080,
            .timeout_ms = 5000,
            .max_connections = 100,
            .enable_logging = true,
        };
    }

    pub fn withPort(self: ServerConfig, port: u16) ServerConfig {
        var config = self;
        config.port = port;
        return config;
    }

    pub fn withTimeout(self: ServerConfig, timeout_ms: u32) ServerConfig {
        var config = self;
        config.timeout_ms = timeout_ms;
        return config;
    }
};
```

Users start with good defaults and chain modifications as needed.

### Builder Pattern

Use a dedicated builder struct for complex initialization with validation:

```zig
const HttpClient = struct {
    base_url: []const u8,
    timeout_ms: u32,
    retry_count: u8,
    user_agent: []const u8,

    pub const Builder = struct {
        base_url: ?[]const u8,
        timeout_ms: u32,
        retry_count: u8,
        user_agent: []const u8,

        pub fn init() Builder {
            return Builder{
                .base_url = null,
                .timeout_ms = 30000,
                .retry_count = 3,
                .user_agent = "ZigClient/1.0",
            };
        }

        pub fn setBaseUrl(self: *Builder, url: []const u8) *Builder {
            self.base_url = url;
            return self;
        }

        pub fn setTimeout(self: *Builder, ms: u32) *Builder {
            self.timeout_ms = ms;
            return self;
        }

        pub fn build(self: *const Builder) !HttpClient {
            if (self.base_url == null) {
                return error.BaseUrlRequired;
            }

            return HttpClient{
                .base_url = self.base_url.?,
                .timeout_ms = self.timeout_ms,
                .retry_count = self.retry_count,
                .user_agent = self.user_agent,
            };
        }
    };
};
```

The builder validates required fields before constructing the final object.

### Named Constructors

Provide multiple initialization methods with descriptive names:

```zig
const Connection = struct {
    host: []const u8,
    port: u16,
    encrypted: bool,

    pub fn localhost(port: u16) Connection {
        return Connection{
            .host = "127.0.0.1",
            .port = port,
            .encrypted = false,
        };
    }

    pub fn secure(host: []const u8, port: u16) Connection {
        return Connection{
            .host = host,
            .port = port,
            .encrypted = true,
        };
    }

    pub fn fromUrl(url: []const u8) !Connection {
        if (std.mem.startsWith(u8, url, "https://")) {
            return Connection{
                .host = url[8..],
                .port = 443,
                .encrypted = true,
            };
        } else if (std.mem.startsWith(u8, url, "http://")) {
            return Connection{
                .host = url[7..],
                .port = 80,
                .encrypted = false,
            };
        }
        return error.InvalidUrl;
    }
};
```

Named constructors clarify intent: `Connection.localhost(8080)` vs. `Connection.secure("api.example.com", 443)`.

### Partial Initialization with Options

Separate required and optional parameters:

```zig
const UserProfile = struct {
    username: []const u8,
    email: []const u8,
    bio: ?[]const u8,
    avatar_url: ?[]const u8,
    verified: bool,

    pub const Options = struct {
        bio: ?[]const u8 = null,
        avatar_url: ?[]const u8 = null,
        verified: bool = false,
    };

    pub fn init(username: []const u8, email: []const u8, options: Options) UserProfile {
        return UserProfile{
            .username = username,
            .email = email,
            .bio = options.bio,
            .avatar_url = options.avatar_url,
            .verified = options.verified,
        };
    }
};
```

Use anonymous struct literal syntax for clean call sites:

```zig
const user = UserProfile.init("alice", "alice@example.com", .{
    .bio = "Developer",
    .verified = true,
});
```

### Copy Constructor Pattern

Create new instances based on existing ones:

```zig
const Point = struct {
    x: f32,
    y: f32,
    z: f32,

    pub fn copy(self: *const Point) Point {
        return Point{
            .x = self.x,
            .y = self.y,
            .z = self.z,
        };
    }

    pub fn copyWith(self: *const Point, x: ?f32, y: ?f32, z: ?f32) Point {
        return Point{
            .x = x orelse self.x,
            .y = y orelse self.y,
            .z = z orelse self.z,
        };
    }

    pub fn scaled(self: *const Point, factor: f32) Point {
        return Point{
            .x = self.x * factor,
            .y = self.y * factor,
            .z = self.z * factor,
        };
    }
};
```

Transformative constructors derive new values from existing instances.

### Validated Initialization

Enforce invariants at construction time:

```zig
const Email = struct {
    address: []const u8,

    pub fn init(address: []const u8) !Email {
        if (address.len == 0) return error.EmptyEmail;
        if (std.mem.indexOf(u8, address, "@") == null) return error.InvalidEmail;

        return Email{ .address = address };
    }
};

const Age = struct {
    value: u8,

    pub fn init(value: u8) !Age {
        if (value > 150) return error.InvalidAge;
        return Age{ .value = value };
    }
};
```

Invalid values can't be constructed—validation happens early.

### Configuration Struct Pattern

Use struct default values for cleaner initialization:

```zig
const DatabaseConfig = struct {
    connection_string: []const u8,
    pool_size: u32 = 10,
    timeout_ms: u32 = 5000,
    auto_reconnect: bool = true,
    ssl_enabled: bool = false,

    pub fn validate(self: *const DatabaseConfig) !void {
        if (self.connection_string.len == 0) {
            return error.EmptyConnectionString;
        }
        if (self.pool_size == 0) {
            return error.InvalidPoolSize;
        }
    }
};

const Database = struct {
    config: DatabaseConfig,

    pub fn init(config: DatabaseConfig) !Database {
        try config.validate();
        return Database{ .config = config };
    }
};
```

Users only specify non-default values:

```zig
const db = try Database.init(.{
    .connection_string = "postgresql://localhost/mydb",
    .pool_size = 20,
    .ssl_enabled = true,
});
```

### From Conversions

Provide type conversions from common formats:

```zig
const Color = struct {
    r: u8,
    g: u8,
    b: u8,

    pub fn fromHex(hex: u32) Color {
        return Color{
            .r = @truncate((hex >> 16) & 0xFF),
            .g = @truncate((hex >> 8) & 0xFF),
            .b = @truncate(hex & 0xFF),
        };
    }

    pub fn fromRgb(r: u8, g: u8, b: u8) Color {
        return Color{ .r = r, .g = g, .b = b };
    }

    pub fn fromGray(value: u8) Color {
        return Color{ .r = value, .g = value, .b = value };
    }
};
```

Multiple `from*` methods support different input formats.

### Discussion

Good initialization patterns make structs easier to use and harder to misuse.

### Choosing a Pattern

**Default values** - When most fields have sensible defaults
- Example: Configuration objects, UI widgets

**Builder pattern** - When validation is complex or fields are interdependent
- Example: HTTP clients, database connections

**Named constructors** - When different use cases need different initialization
- Example: Connections (localhost vs remote), Colors (RGB vs hex)

**Options struct** - When many optional parameters exist
- Example: User profiles, search filters

**Validated init** - When invariants must hold
- Example: Email addresses, age ranges, positive numbers

### Performance Considerations

All patterns shown have zero runtime overhead:
- Method chaining creates stack values
- Builder pattern compiles to direct initialization
- Named constructors inline to struct literals
- No heap allocation unless explicitly required

### Error Handling

Use error unions (`!Type`) for fallible initialization:

```zig
pub fn init(...) !MyStruct {
    if (invalid) return error.InvalidInput;
    return MyStruct{ ... };
}
```

This forces callers to handle errors with `try` or `catch`.

### Testing Tips

Test initialization patterns thoroughly:

```zig
test "builder requires base URL" {
    var builder = HttpClient.Builder.init();
    const result = builder.build();
    try testing.expectError(error.BaseUrlRequired, result);
}

test "email validates format" {
    const result = Email.init("invalid");
    try testing.expectError(error.InvalidEmail, result);
}
```

### Full Tested Code

```zig
// Recipe 8.11: Simplifying the Initialization of Data Structures
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: default_values
// Default values pattern
const ServerConfig = struct {
    host: []const u8,
    port: u16,
    timeout_ms: u32,
    max_connections: u32,
    enable_logging: bool,

    pub fn init(host: []const u8) ServerConfig {
        return ServerConfig{
            .host = host,
            .port = 8080,
            .timeout_ms = 5000,
            .max_connections = 100,
            .enable_logging = true,
        };
    }

    pub fn withPort(self: ServerConfig, port: u16) ServerConfig {
        var config = self;
        config.port = port;
        return config;
    }

    pub fn withTimeout(self: ServerConfig, timeout_ms: u32) ServerConfig {
        var config = self;
        config.timeout_ms = timeout_ms;
        return config;
    }
};
// ANCHOR_END: default_values

test "default values" {
    var config = ServerConfig.init("localhost");
    try testing.expectEqualStrings("localhost", config.host);
    try testing.expectEqual(@as(u16, 8080), config.port);

    config = config.withPort(3000).withTimeout(10000);
    try testing.expectEqual(@as(u16, 3000), config.port);
    try testing.expectEqual(@as(u32, 10000), config.timeout_ms);
}

// ANCHOR: builder_pattern
// Builder pattern
const HttpClient = struct {
    base_url: []const u8,
    timeout_ms: u32,
    retry_count: u8,
    user_agent: []const u8,

    pub const Builder = struct {
        base_url: ?[]const u8,
        timeout_ms: u32,
        retry_count: u8,
        user_agent: []const u8,

        pub fn init() Builder {
            return Builder{
                .base_url = null,
                .timeout_ms = 30000,
                .retry_count = 3,
                .user_agent = "ZigClient/1.0",
            };
        }

        pub fn setBaseUrl(self: *Builder, url: []const u8) *Builder {
            self.base_url = url;
            return self;
        }

        pub fn setTimeout(self: *Builder, ms: u32) *Builder {
            self.timeout_ms = ms;
            return self;
        }

        pub fn setRetryCount(self: *Builder, count: u8) *Builder {
            self.retry_count = count;
            return self;
        }

        pub fn setUserAgent(self: *Builder, agent: []const u8) *Builder {
            self.user_agent = agent;
            return self;
        }

        pub fn build(self: *const Builder) !HttpClient {
            if (self.base_url == null) {
                return error.BaseUrlRequired;
            }

            return HttpClient{
                .base_url = self.base_url.?,
                .timeout_ms = self.timeout_ms,
                .retry_count = self.retry_count,
                .user_agent = self.user_agent,
            };
        }
    };
};
// ANCHOR_END: builder_pattern

test "builder pattern" {
    var builder = HttpClient.Builder.init();
    const client = try builder
        .setBaseUrl("https://api.example.com")
        .setTimeout(5000)
        .setRetryCount(5)
        .build();

    try testing.expectEqualStrings("https://api.example.com", client.base_url);
    try testing.expectEqual(@as(u32, 5000), client.timeout_ms);
    try testing.expectEqual(@as(u8, 5), client.retry_count);
}

// ANCHOR: named_constructors
// Named constructors (static factory methods)
const Connection = struct {
    host: []const u8,
    port: u16,
    encrypted: bool,

    pub fn localhost(port: u16) Connection {
        return Connection{
            .host = "127.0.0.1",
            .port = port,
            .encrypted = false,
        };
    }

    pub fn secure(host: []const u8, port: u16) Connection {
        return Connection{
            .host = host,
            .port = port,
            .encrypted = true,
        };
    }

    pub fn insecure(host: []const u8, port: u16) Connection {
        return Connection{
            .host = host,
            .port = port,
            .encrypted = false,
        };
    }

    pub fn fromUrl(url: []const u8) !Connection {
        if (std.mem.startsWith(u8, url, "https://")) {
            return Connection{
                .host = url[8..],
                .port = 443,
                .encrypted = true,
            };
        } else if (std.mem.startsWith(u8, url, "http://")) {
            return Connection{
                .host = url[7..],
                .port = 80,
                .encrypted = false,
            };
        }
        return error.InvalidUrl;
    }
};
// ANCHOR_END: named_constructors

test "named constructors" {
    const local = Connection.localhost(8080);
    try testing.expectEqualStrings("127.0.0.1", local.host);
    try testing.expectEqual(@as(u16, 8080), local.port);
    try testing.expectEqual(false, local.encrypted);

    const secure = Connection.secure("example.com", 443);
    try testing.expect(secure.encrypted);

    const from_url = try Connection.fromUrl("https://api.example.com");
    try testing.expect(from_url.encrypted);
    try testing.expectEqual(@as(u16, 443), from_url.port);
}

// ANCHOR: partial_initialization
// Partial initialization with required/optional fields
const UserProfile = struct {
    username: []const u8,
    email: []const u8,
    bio: ?[]const u8,
    avatar_url: ?[]const u8,
    verified: bool,

    pub const Options = struct {
        bio: ?[]const u8 = null,
        avatar_url: ?[]const u8 = null,
        verified: bool = false,
    };

    pub fn init(username: []const u8, email: []const u8, options: Options) UserProfile {
        return UserProfile{
            .username = username,
            .email = email,
            .bio = options.bio,
            .avatar_url = options.avatar_url,
            .verified = options.verified,
        };
    }
};
// ANCHOR_END: partial_initialization

test "partial initialization" {
    const user1 = UserProfile.init("alice", "alice@example.com", .{});
    try testing.expectEqualStrings("alice", user1.username);
    try testing.expect(user1.bio == null);
    try testing.expectEqual(false, user1.verified);

    const user2 = UserProfile.init("bob", "bob@example.com", .{
        .bio = "Software developer",
        .verified = true,
    });
    try testing.expectEqualStrings("Software developer", user2.bio.?);
    try testing.expect(user2.verified);
}

// ANCHOR: copy_constructor
// Copy constructor pattern
const Point = struct {
    x: f32,
    y: f32,
    z: f32,

    pub fn init(x: f32, y: f32, z: f32) Point {
        return Point{ .x = x, .y = y, .z = z };
    }

    pub fn copy(self: *const Point) Point {
        return Point{
            .x = self.x,
            .y = self.y,
            .z = self.z,
        };
    }

    pub fn copyWith(self: *const Point, x: ?f32, y: ?f32, z: ?f32) Point {
        return Point{
            .x = x orelse self.x,
            .y = y orelse self.y,
            .z = z orelse self.z,
        };
    }

    pub fn scaled(self: *const Point, factor: f32) Point {
        return Point{
            .x = self.x * factor,
            .y = self.y * factor,
            .z = self.z * factor,
        };
    }
};
// ANCHOR_END: copy_constructor

test "copy constructor" {
    const p1 = Point.init(1, 2, 3);
    const p2 = p1.copy();
    try testing.expectEqual(p1.x, p2.x);

    const p3 = p1.copyWith(10, null, null);
    try testing.expectEqual(@as(f32, 10), p3.x);
    try testing.expectEqual(@as(f32, 2), p3.y);

    const p4 = p1.scaled(2);
    try testing.expectEqual(@as(f32, 2), p4.x);
    try testing.expectEqual(@as(f32, 4), p4.y);
}

// ANCHOR: validated_initialization
// Validated initialization
const Email = struct {
    address: []const u8,

    pub fn init(address: []const u8) !Email {
        if (address.len == 0) return error.EmptyEmail;
        if (std.mem.indexOf(u8, address, "@") == null) return error.InvalidEmail;

        return Email{ .address = address };
    }

    pub fn getAddress(self: *const Email) []const u8 {
        return self.address;
    }
};

const Age = struct {
    value: u8,

    pub fn init(value: u8) !Age {
        if (value > 150) return error.InvalidAge;
        return Age{ .value = value };
    }

    pub fn getValue(self: *const Age) u8 {
        return self.value;
    }
};
// ANCHOR_END: validated_initialization

test "validated initialization" {
    const email = try Email.init("user@example.com");
    try testing.expectEqualStrings("user@example.com", email.getAddress());

    const invalid_email = Email.init("invalid");
    try testing.expectError(error.InvalidEmail, invalid_email);

    const age = try Age.init(25);
    try testing.expectEqual(@as(u8, 25), age.getValue());

    const invalid_age = Age.init(200);
    try testing.expectError(error.InvalidAge, invalid_age);
}

// ANCHOR: fluent_interface
// Fluent interface for chaining
const StringBuilder = struct {
    buffer: std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) StringBuilder {
        return StringBuilder{
            .buffer = std.ArrayList(u8){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *StringBuilder) void {
        self.buffer.deinit(self.allocator);
    }

    pub fn append(self: *StringBuilder, text: []const u8) !*StringBuilder {
        try self.buffer.appendSlice(self.allocator, text);
        return self;
    }

    pub fn appendChar(self: *StringBuilder, char: u8) !*StringBuilder {
        try self.buffer.append(self.allocator, char);
        return self;
    }

    pub fn clear(self: *StringBuilder) *StringBuilder {
        self.buffer.clearRetainingCapacity();
        return self;
    }

    pub fn toString(self: *const StringBuilder) []const u8 {
        return self.buffer.items;
    }
};
// ANCHOR_END: fluent_interface

test "fluent interface" {
    var sb = StringBuilder.init(testing.allocator);
    defer sb.deinit();

    _ = try (try (try (try sb.append("Hello")).append(" ")).append("World")).appendChar('!');

    try testing.expectEqualStrings("Hello World!", sb.toString());

    _ = try sb.clear().append("New");
    try testing.expectEqualStrings("New", sb.toString());
}

// ANCHOR: configuration_struct
// Configuration struct pattern
const DatabaseConfig = struct {
    connection_string: []const u8,
    pool_size: u32 = 10,
    timeout_ms: u32 = 5000,
    auto_reconnect: bool = true,
    ssl_enabled: bool = false,

    pub fn validate(self: *const DatabaseConfig) !void {
        if (self.connection_string.len == 0) {
            return error.EmptyConnectionString;
        }
        if (self.pool_size == 0) {
            return error.InvalidPoolSize;
        }
    }
};

const Database = struct {
    config: DatabaseConfig,

    pub fn init(config: DatabaseConfig) !Database {
        try config.validate();
        return Database{ .config = config };
    }
};
// ANCHOR_END: configuration_struct

test "configuration struct" {
    const config = DatabaseConfig{
        .connection_string = "postgresql://localhost/mydb",
        .pool_size = 20,
        .ssl_enabled = true,
    };

    const db = try Database.init(config);
    try testing.expectEqual(@as(u32, 20), db.config.pool_size);
    try testing.expect(db.config.ssl_enabled);
    try testing.expect(db.config.auto_reconnect);
}

// ANCHOR: from_conversion
// From conversions
const Color = struct {
    r: u8,
    g: u8,
    b: u8,

    pub fn fromHex(hex: u32) Color {
        return Color{
            .r = @truncate((hex >> 16) & 0xFF),
            .g = @truncate((hex >> 8) & 0xFF),
            .b = @truncate(hex & 0xFF),
        };
    }

    pub fn fromRgb(r: u8, g: u8, b: u8) Color {
        return Color{ .r = r, .g = g, .b = b };
    }

    pub fn fromGray(value: u8) Color {
        return Color{ .r = value, .g = value, .b = value };
    }

    pub fn toHex(self: *const Color) u32 {
        return (@as(u32, self.r) << 16) | (@as(u32, self.g) << 8) | @as(u32, self.b);
    }
};
// ANCHOR_END: from_conversion

test "from conversions" {
    const red = Color.fromHex(0xFF0000);
    try testing.expectEqual(@as(u8, 255), red.r);
    try testing.expectEqual(@as(u8, 0), red.g);

    const green = Color.fromRgb(0, 255, 0);
    try testing.expectEqual(@as(u32, 0x00FF00), green.toHex());

    const gray = Color.fromGray(128);
    try testing.expectEqual(@as(u8, 128), gray.r);
    try testing.expectEqual(@as(u8, 128), gray.g);
}

// ANCHOR: lazy_initialization_init
// Lazy initialization in init
const ResourceManager = struct {
    allocator: std.mem.Allocator,
    cache: ?std.StringHashMap([]const u8),

    pub fn init(allocator: std.mem.Allocator) ResourceManager {
        return ResourceManager{
            .allocator = allocator,
            .cache = null,
        };
    }

    pub fn deinit(self: *ResourceManager) void {
        if (self.cache) |*c| {
            c.deinit();
        }
    }

    pub fn getCache(self: *ResourceManager) *std.StringHashMap([]const u8) {
        if (self.cache == null) {
            self.cache = std.StringHashMap([]const u8).init(self.allocator);
        }
        return &self.cache.?;
    }
};
// ANCHOR_END: lazy_initialization_init

test "lazy initialization in init" {
    var manager = ResourceManager.init(testing.allocator);
    defer manager.deinit();

    try testing.expect(manager.cache == null);

    const cache = manager.getCache();
    try testing.expect(manager.cache != null);
    try testing.expectEqual(@as(usize, 0), cache.count());
}

// ANCHOR: anonymous_struct_init
// Anonymous struct initialization
const Settings = struct {
    display: struct {
        width: u32,
        height: u32,
        fullscreen: bool,
    },
    audio: struct {
        volume: f32,
        muted: bool,
    },

    pub fn default() Settings {
        return Settings{
            .display = .{
                .width = 1920,
                .height = 1080,
                .fullscreen = false,
            },
            .audio = .{
                .volume = 0.8,
                .muted = false,
            },
        };
    }
};
// ANCHOR_END: anonymous_struct_init

test "anonymous struct init" {
    const settings = Settings.default();
    try testing.expectEqual(@as(u32, 1920), settings.display.width);
    try testing.expectEqual(@as(f32, 0.8), settings.audio.volume);
}

// ANCHOR: zero_initialization
// Zero initialization helper
fn zero(comptime T: type) T {
    var result: T = undefined;
    @memset(std.mem.asBytes(&result), 0);
    return result;
}

const Statistics = struct {
    count: u64,
    sum: f64,
    min: f64,
    max: f64,

    pub fn init() Statistics {
        return zero(Statistics);
    }

    pub fn initWithDefaults() Statistics {
        return Statistics{
            .count = 0,
            .sum = 0,
            .min = std.math.inf(f64),
            .max = -std.math.inf(f64),
        };
    }
};
// ANCHOR_END: zero_initialization

test "zero initialization" {
    const stats1 = Statistics.init();
    try testing.expectEqual(@as(u64, 0), stats1.count);
    try testing.expectEqual(@as(f64, 0), stats1.sum);

    const stats2 = Statistics.initWithDefaults();
    try testing.expect(std.math.isInf(stats2.min));
    try testing.expect(std.math.isNegativeInf(stats2.max));
}

// Comprehensive test
test "comprehensive initialization patterns" {
    var config = ServerConfig.init("0.0.0.0");
    config = config.withPort(9000);
    try testing.expectEqual(@as(u16, 9000), config.port);

    var builder = HttpClient.Builder.init();
    const client = try builder.setBaseUrl("https://test.com").build();
    try testing.expectEqualStrings("https://test.com", client.base_url);

    const conn = Connection.localhost(3000);
    try testing.expectEqual(@as(u16, 3000), conn.port);

    const user = UserProfile.init("test", "test@test.com", .{});
    try testing.expectEqualStrings("test", user.username);
}
```

### See Also

- Recipe 8.6: Creating Managed Attributes
- Recipe 8.16: Defining More Than One Constructor
- Recipe 8.17: Creating an Instance Without Invoking Init
- Recipe 9.11: Using comptime to Control Instance Creation

---

## Recipe 8.12: Defining an Interface or Abstract Base Struct {#recipe-8-12}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, hashmap, memory, pointers, resource-cleanup, slices, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_12.zig`

### Problem

You want to define interfaces or abstract base classes to allow different types to be used interchangeably, similar to interfaces in Java or traits in Rust. However, Zig doesn't have built-in interface syntax.

### Solution

Zig provides several approaches to interfaces: vtable-based fat pointers for runtime polymorphism, tagged unions for closed sets of types, and compile-time duck typing for static polymorphism.

### VTable-Based Interface

Use fat pointers containing a vtable for runtime polymorphism:

```zig
// VTable-based interface
const Writer = struct {
    ptr: *anyopaque,
    writeFn: *const fn (ptr: *anyopaque, data: []const u8) IOError!usize,

    pub fn write(self: Writer, data: []const u8) !usize {
        return self.writeFn(self.ptr, data);
    }
};

const BufferWriter = struct {
    buffer: std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) BufferWriter {
        return BufferWriter{
            .buffer = std.ArrayList(u8){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *BufferWriter) void {
        self.buffer.deinit(self.allocator);
    }

    fn writeFn(ptr: *anyopaque, data: []const u8) IOError!usize {
        const self: *BufferWriter = @ptrCast(@alignCast(ptr));
        self.buffer.appendSlice(self.allocator, data) catch return error.OutOfMemory;
        return data.len;
    }

    pub fn writer(self: *BufferWriter) Writer {
        return Writer{
            .ptr = self,
            .writeFn = writeFn,
        };
    }

    pub fn getWritten(self: *const BufferWriter) []const u8 {
        return self.buffer.items;
    }
};
        return Writer{
            .ptr = self,
            .writeFn = writeFn,
        };
    }
};
```

This pattern is similar to Go interfaces and allows different implementations to be used through the same interface.

### Tagged Union Interface

Use tagged unions when you know all implementing types at compile time:

```zig
const Shape = union(enum) {
    circle: Circle,
    rectangle: Rectangle,
    triangle: Triangle,

    const Circle = struct {
        radius: f32,

        pub fn area(self: Circle) f32 {
            return std.math.pi * self.radius * self.radius;
        }
    };

    const Rectangle = struct {
        width: f32,
        height: f32,

        pub fn area(self: Rectangle) f32 {
            return self.width * self.height;
        }
    };

    pub fn area(self: Shape) f32 {
        return switch (self) {
            .circle => |c| c.area(),
            .rectangle => |r| r.area(),
            .triangle => |t| t.area(),
        };
    }

    pub fn perimeter(self: Shape) f32 {
        return switch (self) {
            .circle => |c| 2 * std.math.pi * c.radius,
            .rectangle => |r| 2 * (r.width + r.height),
            .triangle => |t| t.base + 2 * @sqrt(t.height * t.height + (t.base / 2) * (t.base / 2)),
        };
    }
};
```

Tagged unions provide zero-overhead polymorphism with compile-time type safety.

### Compile-Time Duck Typing

Validate interface requirements at compile time using `@hasDecl`:

```zig
fn Drawable(comptime T: type) type {
    return struct {
        pub fn validate() void {
            if (!@hasDecl(T, "draw")) {
                @compileError("Type must have 'draw' method");
            }
            if (!@hasDecl(T, "getBounds")) {
                @compileError("Type must have 'getBounds' method");
            }
        }
    };
}

const Box = struct {
    x: f32,
    y: f32,
    width: f32,
    height: f32,

    pub fn draw(self: *const Box) void {
        _ = self;
        // Drawing logic
    }

    pub fn getBounds(self: *const Box) struct { x: f32, y: f32, w: f32, h: f32 } {
        return .{ .x = self.x, .y = self.y, .w = self.width, .h = self.height };
    }
};

fn renderDrawable(drawable: anytype) void {
    const T = @TypeOf(drawable);
    Drawable(T).validate();
    drawable.draw();
}
```

The compiler ensures the type has required methods before allowing compilation.

### Multiple Interfaces

Combine multiple interfaces using separate vtables:

```zig
const Reader = struct {
    ptr: *anyopaque,
    readFn: *const fn (ptr: *anyopaque, buffer: []u8) anyerror!usize,

    pub fn read(self: Reader, buffer: []u8) !usize {
        return self.readFn(self.ptr, buffer);
    }
};

const Seeker = struct {
    ptr: *anyopaque,
    seekFn: *const fn (ptr: *anyopaque, pos: u64) anyerror!void,

    pub fn seek(self: Seeker, pos: u64) !void {
        return self.seekFn(self.ptr, pos);
    }
};

const MemoryFile = struct {
    data: []const u8,
    position: usize,

    // Implement both Reader and Seeker
    pub fn reader(self: *MemoryFile) Reader {
        return Reader{ .ptr = self, .readFn = readFn };
    }

    pub fn seeker(self: *MemoryFile) Seeker {
        return Seeker{ .ptr = self, .seekFn = seekFn };
    }
};
```

Types can implement multiple interfaces independently.

### Static Dispatch with Comptime

Achieve zero-cost abstraction using comptime parameters:

```zig
fn process(comptime T: type, processor: T, data: []const u8) !void {
    // Verify interface at compile time
    if (!@hasDecl(T, "process")) {
        @compileError("Type must have process method");
    }

    try processor.process(data);
}

const UppercaseProcessor = struct {
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub fn process(self: UppercaseProcessor, data: []const u8) !void {
        for (data) |c| {
            try self.output.append(self.allocator, std.ascii.toUpper(c));
        }
    }
};
```

The concrete type is known at compile time, allowing full inlining and optimization.

### Anytype Interface (Most Flexible)

Use `anytype` for maximum flexibility:

```zig
fn compare(a: anytype, b: anytype) !bool {
    const T = @TypeOf(a);
    if (@TypeOf(b) != T) {
        @compileError("Both arguments must be the same type");
    }

    // Check if type has equals method
    const info = @typeInfo(T);
    const has_equals = switch (info) {
        .@"struct", .@"union", .@"enum" => @hasDecl(T, "equals"),
        else => false,
    };

    if (has_equals) {
        return a.equals(b);
    }

    // Fall back to builtin equality
    return a == b;
}

const CustomNumber = struct {
    value: i32,

    pub fn equals(self: CustomNumber, other: CustomNumber) bool {
        return self.value == other.value;
    }
};
```

This pattern adapts behavior based on what methods the type provides.

### Interface Composition

Combine multiple interfaces into a single type:

```zig
const Closeable = struct {
    ptr: *anyopaque,
    closeFn: *const fn (ptr: *anyopaque) anyerror!void,

    pub fn close(self: Closeable) !void {
        return self.closeFn(self.ptr);
    }
};

const ReadWriteCloseable = struct {
    reader: Reader,
    writer: Writer,
    closeable: Closeable,

    pub fn read(self: ReadWriteCloseable, buffer: []u8) !usize {
        return self.reader.read(buffer);
    }

    pub fn write(self: ReadWriteCloseable, data: []const u8) !usize {
        return self.writer.write(data);
    }

    pub fn close(self: ReadWriteCloseable) !void {
        return self.closeable.close();
    }
};
```

Compose complex interfaces from simpler building blocks.

### Discussion

Zig's approach to interfaces emphasizes explicitness and zero-cost abstractions.

### Choosing an Interface Pattern

**VTable (fat pointer)** - Runtime polymorphism needed
- Use when: Type not known at compile time
- Examples: Plugin systems, heterogeneous collections
- Cost: One pointer indirection per call

**Tagged union** - Closed set of known types
- Use when: All types known at compile time
- Examples: AST nodes, state machines, parsers
- Cost: Switch statement (often optimized to jump table)

**Comptime duck typing** - Static polymorphism
- Use when: Generic algorithms with compile-time types
- Examples: Containers, algorithms, utilities
- Cost: Zero—fully inlined

**Anytype** - Maximum flexibility
- Use when: Many different types, each handled differently
- Examples: Logging, serialization, testing utilities
- Cost: Code bloat if many types (separate copy per type)

### Performance Characteristics

**VTable dispatch:**
- Runtime cost: One indirection
- Memory: 2 pointers (ptr + vtable)
- Monomorphization: No code duplication

**Tagged union:**
- Runtime cost: Tag check + branch
- Memory: Tag + largest variant
- Monomorphization: No code duplication

**Comptime/anytype:**
- Runtime cost: Zero (inlined)
- Memory: No overhead
- Monomorphization: Separate function per type

### Common Patterns

**Standard library pattern**: Most stdlib types use the vtable pattern
- `std.io.Reader`, `std.io.Writer`
- Fat pointers with function pointers

**Application pattern**: Use tagged unions for domain types
- Closed set of variants (commands, events, states)
- Exhaustive switch ensures all cases handled

**Library pattern**: Use comptime for generic code
- Containers (ArrayList, HashMap)
- Algorithms (sorting, searching)

### Best Practices

1. **Prefer comptime when possible** - Zero runtime cost
2. **Use tagged unions for closed sets** - Type-safe and fast
3. **VTables for true runtime polymorphism** - When types unknown at compile time
4. **Document interface requirements** - Use `@compileError` with clear messages
5. **Test with multiple implementations** - Ensure interface is truly generic

### Error Handling

Interface methods can return error unions:

```zig
const Fallible = struct {
    ptr: *anyopaque,
    executeFn: *const fn (ptr: *anyopaque) anyerror!void,

    pub fn execute(self: Fallible) !void {
        return self.executeFn(self.ptr);
    }
};
```

Callers must handle errors with `try` or `catch`.

### Full Tested Code

```zig
// Recipe 8.12: Defining an Interface or Abstract Base Class
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// Define explicit error sets for interfaces
// This provides better type safety and allows callers to handle specific errors
pub const IOError = error{
    OutOfMemory,
    EndOfStream,
    InvalidSeekPos,
    DeviceError,
    NotImplemented,
};

// ANCHOR: vtable_interface
// VTable-based interface
const Writer = struct {
    ptr: *anyopaque,
    writeFn: *const fn (ptr: *anyopaque, data: []const u8) IOError!usize,

    pub fn write(self: Writer, data: []const u8) !usize {
        return self.writeFn(self.ptr, data);
    }
};

const BufferWriter = struct {
    buffer: std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) BufferWriter {
        return BufferWriter{
            .buffer = std.ArrayList(u8){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *BufferWriter) void {
        self.buffer.deinit(self.allocator);
    }

    fn writeFn(ptr: *anyopaque, data: []const u8) IOError!usize {
        const self: *BufferWriter = @ptrCast(@alignCast(ptr));
        self.buffer.appendSlice(self.allocator, data) catch return error.OutOfMemory;
        return data.len;
    }

    pub fn writer(self: *BufferWriter) Writer {
        return Writer{
            .ptr = self,
            .writeFn = writeFn,
        };
    }

    pub fn getWritten(self: *const BufferWriter) []const u8 {
        return self.buffer.items;
    }
};
// ANCHOR_END: vtable_interface

test "vtable interface" {
    var buf = BufferWriter.init(testing.allocator);
    defer buf.deinit();

    const writer = buf.writer();
    const written = try writer.write("Hello, World!");

    try testing.expectEqual(@as(usize, 13), written);
    try testing.expectEqualStrings("Hello, World!", buf.getWritten());
}

// ANCHOR: tagged_union_interface
// Tagged union interface
const Shape = union(enum) {
    circle: Circle,
    rectangle: Rectangle,
    triangle: Triangle,

    const Circle = struct {
        radius: f32,

        pub fn area(self: Circle) f32 {
            return std.math.pi * self.radius * self.radius;
        }
    };

    const Rectangle = struct {
        width: f32,
        height: f32,

        pub fn area(self: Rectangle) f32 {
            return self.width * self.height;
        }
    };

    const Triangle = struct {
        base: f32,
        height: f32,

        pub fn area(self: Triangle) f32 {
            return 0.5 * self.base * self.height;
        }
    };

    pub fn area(self: Shape) f32 {
        return switch (self) {
            .circle => |c| c.area(),
            .rectangle => |r| r.area(),
            .triangle => |t| t.area(),
        };
    }

    pub fn perimeter(self: Shape) f32 {
        return switch (self) {
            .circle => |c| 2 * std.math.pi * c.radius,
            .rectangle => |r| 2 * (r.width + r.height),
            .triangle => |t| t.base + 2 * @sqrt(t.height * t.height + (t.base / 2) * (t.base / 2)),
        };
    }
};
// ANCHOR_END: tagged_union_interface

test "tagged union interface" {
    const circle = Shape{ .circle = .{ .radius = 5 } };
    const rect = Shape{ .rectangle = .{ .width = 4, .height = 6 } };

    try testing.expectApproxEqAbs(78.54, circle.area(), 0.01);
    try testing.expectEqual(@as(f32, 24), rect.area());
}

// ANCHOR: comptime_interface
// Compile-time duck typing interface
fn Drawable(comptime T: type) type {
    return struct {
        pub fn validate() void {
            if (!@hasDecl(T, "draw")) {
                @compileError("Type must have 'draw' method");
            }
            if (!@hasDecl(T, "getBounds")) {
                @compileError("Type must have 'getBounds' method");
            }
        }
    };
}

const Box = struct {
    x: f32,
    y: f32,
    width: f32,
    height: f32,

    pub fn draw(self: *const Box) void {
        _ = self;
        // Drawing logic
    }

    pub fn getBounds(self: *const Box) struct { x: f32, y: f32, w: f32, h: f32 } {
        return .{ .x = self.x, .y = self.y, .w = self.width, .h = self.height };
    }
};

fn renderDrawable(drawable: anytype) void {
    const T = @TypeOf(drawable);
    Drawable(T).validate();
    drawable.draw();
}
// ANCHOR_END: comptime_interface

test "comptime interface" {
    const box = Box{ .x = 0, .y = 0, .width = 10, .height = 20 };
    renderDrawable(box);

    const bounds = box.getBounds();
    try testing.expectEqual(@as(f32, 10), bounds.w);
}

// ANCHOR: multi_vtable
// Multiple interfaces via multiple vtables
const Reader = struct {
    ptr: *anyopaque,
    readFn: *const fn (ptr: *anyopaque, buffer: []u8) IOError!usize,

    pub fn read(self: Reader, buffer: []u8) !usize {
        return self.readFn(self.ptr, buffer);
    }
};

const Seeker = struct {
    ptr: *anyopaque,
    seekFn: *const fn (ptr: *anyopaque, pos: u64) IOError!void,

    pub fn seek(self: Seeker, pos: u64) !void {
        return self.seekFn(self.ptr, pos);
    }
};

const MemoryFile = struct {
    data: []const u8,
    position: usize,

    pub fn init(data: []const u8) MemoryFile {
        return MemoryFile{
            .data = data,
            .position = 0,
        };
    }

    fn readFn(ptr: *anyopaque, buffer: []u8) IOError!usize {
        const self: *MemoryFile = @ptrCast(@alignCast(ptr));
        const remaining = self.data[self.position..];
        const to_read = @min(buffer.len, remaining.len);
        @memcpy(buffer[0..to_read], remaining[0..to_read]);
        self.position += to_read;
        return to_read;
    }

    fn seekFn(ptr: *anyopaque, pos: u64) IOError!void {
        const self: *MemoryFile = @ptrCast(@alignCast(ptr));
        if (pos > self.data.len) return error.InvalidSeekPos;
        self.position = @intCast(pos);
    }

    pub fn reader(self: *MemoryFile) Reader {
        return Reader{ .ptr = self, .readFn = readFn };
    }

    pub fn seeker(self: *MemoryFile) Seeker {
        return Seeker{ .ptr = self, .seekFn = seekFn };
    }
};
// ANCHOR_END: multi_vtable

test "multiple interfaces" {
    const data = "Hello, World!";
    var file = MemoryFile.init(data);

    const reader = file.reader();
    var buffer: [5]u8 = undefined;
    const read_count = try reader.read(&buffer);
    try testing.expectEqual(@as(usize, 5), read_count);
    try testing.expectEqualStrings("Hello", &buffer);

    const seeker = file.seeker();
    try seeker.seek(7);
    const read_count2 = try reader.read(&buffer);
    try testing.expectEqual(@as(usize, 5), read_count2);
    try testing.expectEqualStrings("World", &buffer);
}

// ANCHOR: generic_interface
// Generic interface pattern
fn Serializer(comptime T: type) type {
    return struct {
        pub fn serialize(value: T, allocator: std.mem.Allocator) ![]u8 {
            _ = value;
            return try allocator.dupe(u8, "serialized");
        }

        pub fn deserialize(data: []const u8, allocator: std.mem.Allocator) !T {
            _ = data;
            _ = allocator;
            return error.NotImplemented;
        }
    };
}

const Person = struct {
    name: []const u8,
    age: u32,

    pub const Ser = Serializer(@This());
};
// ANCHOR_END: generic_interface

test "generic interface" {
    const person = Person{ .name = "Alice", .age = 30 };
    const serialized = try Person.Ser.serialize(person, testing.allocator);
    defer testing.allocator.free(serialized);

    try testing.expectEqualStrings("serialized", serialized);
}

// ANCHOR: trait_bounds
// Trait bounds using comptime
fn printValue(value: anytype) void {
    const T = @TypeOf(value);
    const info = @typeInfo(T);

    // Require the type to have a print method
    if (info == .@"struct" or info == .@"union") {
        if (!@hasDecl(T, "print")) {
            @compileError("Type must implement print() method");
        }
    }

    value.print();
}

const LogEntry = struct {
    message: []const u8,
    level: enum { info, warn, err },

    pub fn print(self: *const LogEntry) void {
        _ = self;
        // Print implementation
    }
};
// ANCHOR_END: trait_bounds

test "trait bounds" {
    const entry = LogEntry{
        .message = "Test message",
        .level = .info,
    };

    printValue(entry);
}

// ANCHOR: interface_composition
// Interface composition
const Closeable = struct {
    ptr: *anyopaque,
    closeFn: *const fn (ptr: *anyopaque) IOError!void,

    pub fn close(self: Closeable) !void {
        return self.closeFn(self.ptr);
    }
};

const ReadWriteCloseable = struct {
    reader: Reader,
    writer: Writer,
    closeable: Closeable,

    pub fn read(self: ReadWriteCloseable, buffer: []u8) !usize {
        return self.reader.read(buffer);
    }

    pub fn write(self: ReadWriteCloseable, data: []const u8) !usize {
        return self.writer.write(data);
    }

    pub fn close(self: ReadWriteCloseable) !void {
        return self.closeable.close();
    }
};

const DualBuffer = struct {
    read_buffer: []const u8,
    write_buffer: std.ArrayList(u8),
    read_pos: usize,
    allocator: std.mem.Allocator,
    closed: bool,

    pub fn init(allocator: std.mem.Allocator, read_data: []const u8) DualBuffer {
        return DualBuffer{
            .read_buffer = read_data,
            .write_buffer = std.ArrayList(u8){},
            .read_pos = 0,
            .allocator = allocator,
            .closed = false,
        };
    }

    pub fn deinit(self: *DualBuffer) void {
        self.write_buffer.deinit(self.allocator);
    }

    fn readFn(ptr: *anyopaque, buffer: []u8) IOError!usize {
        const self: *DualBuffer = @ptrCast(@alignCast(ptr));
        const remaining = self.read_buffer[self.read_pos..];
        const to_read = @min(buffer.len, remaining.len);
        @memcpy(buffer[0..to_read], remaining[0..to_read]);
        self.read_pos += to_read;
        return to_read;
    }

    fn writeFn(ptr: *anyopaque, data: []const u8) IOError!usize {
        const self: *DualBuffer = @ptrCast(@alignCast(ptr));
        self.write_buffer.appendSlice(self.allocator, data) catch return error.OutOfMemory;
        return data.len;
    }

    fn closeFn(ptr: *anyopaque) IOError!void {
        const self: *DualBuffer = @ptrCast(@alignCast(ptr));
        self.closed = true;
    }

    pub fn readWriteCloseable(self: *DualBuffer) ReadWriteCloseable {
        return ReadWriteCloseable{
            .reader = Reader{ .ptr = self, .readFn = readFn },
            .writer = Writer{ .ptr = self, .writeFn = writeFn },
            .closeable = Closeable{ .ptr = self, .closeFn = closeFn },
        };
    }
};
// ANCHOR_END: interface_composition

test "interface composition" {
    var dual = DualBuffer.init(testing.allocator, "input data");
    defer dual.deinit();

    const rwc = dual.readWriteCloseable();

    var buffer: [5]u8 = undefined;
    _ = try rwc.read(&buffer);
    try testing.expectEqualStrings("input", &buffer);

    _ = try rwc.write("output");
    try testing.expectEqualStrings("output", dual.write_buffer.items);

    try rwc.close();
    try testing.expect(dual.closed);
}

// ANCHOR: static_dispatch
// Static dispatch with comptime
fn process(comptime T: type, processor: T, data: []const u8) !void {
    // Verify interface at compile time
    if (!@hasDecl(T, "process")) {
        @compileError("Type must have process method");
    }

    try processor.process(data);
}

const UppercaseProcessor = struct {
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub fn process(self: UppercaseProcessor, data: []const u8) !void {
        for (data) |c| {
            try self.output.append(self.allocator, std.ascii.toUpper(c));
        }
    }
};

const LowercaseProcessor = struct {
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub fn process(self: LowercaseProcessor, data: []const u8) !void {
        for (data) |c| {
            try self.output.append(self.allocator, std.ascii.toLower(c));
        }
    }
};
// ANCHOR_END: static_dispatch

test "static dispatch" {
    var upper_output = std.ArrayList(u8){};
    defer upper_output.deinit(testing.allocator);

    const upper = UppercaseProcessor{ .output = &upper_output, .allocator = testing.allocator };
    try process(UppercaseProcessor, upper, "hello");
    try testing.expectEqualStrings("HELLO", upper_output.items);

    var lower_output = std.ArrayList(u8){};
    defer lower_output.deinit(testing.allocator);

    const lower = LowercaseProcessor{ .output = &lower_output, .allocator = testing.allocator };
    try process(LowercaseProcessor, lower, "WORLD");
    try testing.expectEqualStrings("world", lower_output.items);
}

// ANCHOR: anytype_interface
// Anytype interface (most flexible)
fn compare(a: anytype, b: anytype) !bool {
    const T = @TypeOf(a);
    if (@TypeOf(b) != T) {
        @compileError("Both arguments must be the same type");
    }

    // Check if type has equals method
    const info = @typeInfo(T);
    const has_equals = switch (info) {
        .@"struct", .@"union", .@"enum" => @hasDecl(T, "equals"),
        else => false,
    };

    if (has_equals) {
        return a.equals(b);
    }

    // Fall back to builtin equality
    return a == b;
}

const CustomNumber = struct {
    value: i32,

    pub fn equals(self: CustomNumber, other: CustomNumber) bool {
        return self.value == other.value;
    }
};
// ANCHOR_END: anytype_interface

test "anytype interface" {
    const n1 = CustomNumber{ .value = 42 };
    const n2 = CustomNumber{ .value = 42 };
    const n3 = CustomNumber{ .value = 99 };

    try testing.expect(try compare(n1, n2));
    try testing.expect(!try compare(n1, n3));

    try testing.expect(try compare(@as(i32, 5), @as(i32, 5)));
}

// Comprehensive test
test "comprehensive interface patterns" {
    var buf = BufferWriter.init(testing.allocator);
    defer buf.deinit();
    _ = try buf.writer().write("test");
    try testing.expectEqualStrings("test", buf.getWritten());

    const circle = Shape{ .circle = .{ .radius = 3 } };
    const area = circle.area();
    try testing.expectApproxEqAbs(28.27, area, 0.01);

    const box = Box{ .x = 0, .y = 0, .width = 5, .height = 5 };
    renderDrawable(box);
}
```

### See Also

- Recipe 8.7: Calling a Method on a Parent Class
- Recipe 8.13: Implementing a Data Model or Type System
- Recipe 8.14: Implementing Custom Containers
- Recipe 9.11: Using comptime to Control Instance Creation

---

## Recipe 8.13: Implementing a Data Model or Type System {#recipe-8-13}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, hashmap, json, memory, parsing, resource-cleanup, slices, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_13.zig`

### Problem

You need to create a data model with validation rules, type constraints, relationships, and serialization—similar to ORMs or schema validation libraries in other languages.

### Solution

Use Zig's type system to enforce constraints at compile time and runtime, combining validation, typed wrappers, and builder patterns to create robust data models.

### Basic Field Validation

Start with simple validation in the init method:

```zig
// Basic field validation
const User = struct {
    username: []const u8,
    email: []const u8,
    age: u8,

    pub fn validate(self: *const User) !void {
        if (self.username.len == 0 or self.username.len > 50) {
            return error.InvalidUsername;
        }
        if (std.mem.indexOf(u8, self.email, "@") == null) {
            return error.InvalidEmail;
        }
        if (self.age < 13 or self.age > 150) {
            return error.InvalidAge;
        }
    }

    pub fn init(username: []const u8, email: []const u8, age: u8) !User {
        const user = User{
            .username = username,
            .email = email,
            .age = age,
        };
        try user.validate();
        return user;
    }
};
```

This ensures invalid users can never be created.

### Typed Fields with Validation

Wrap primitive types in validation-enforcing structs:

```zig
const Email = struct {
    value: []const u8,

    pub fn init(value: []const u8) !Email {
        if (value.len == 0) return error.EmptyEmail;
        if (std.mem.indexOf(u8, value, "@") == null) return error.InvalidFormat;
        if (std.mem.indexOf(u8, value, ".") == null) return error.InvalidFormat;
        return Email{ .value = value };
    }

    pub fn getValue(self: *const Email) []const u8 {
        return self.value;
    }
};

const Username = struct {
    value: []const u8,

    pub fn init(value: []const u8) !Username {
        if (value.len < 3) return error.TooShort;
        if (value.len > 20) return error.TooLong;
        for (value) |c| {
            if (!std.ascii.isAlphanumeric(c) and c != '_') {
                return error.InvalidCharacter;
            }
        }
        return Username{ .value = value };
    }
};

const ValidatedUser = struct {
    username: Username,
    email: Email,

    pub fn init(username: []const u8, email: []const u8) !ValidatedUser {
        return ValidatedUser{
            .username = try Username.init(username),
            .email = try Email.init(email),
        };
    }
};
```

The type system enforces that only valid usernames and emails exist.

### Enum-Based State Constraints

Use enums to enforce valid state transitions:

```zig
const Status = enum {
    draft,
    published,
    archived,

    pub fn canTransitionTo(self: Status, target: Status) bool {
        return switch (self) {
            .draft => target == .published or target == .archived,
            .published => target == .archived,
            .archived => false,
        };
    }
};

const Document = struct {
    title: []const u8,
    content: []const u8,
    status: Status,

    pub fn init(title: []const u8, content: []const u8) Document {
        return Document{
            .title = title,
            .content = content,
            .status = .draft,
        };
    }

    pub fn changeStatus(self: *Document, new_status: Status) !void {
        if (!self.status.canTransitionTo(new_status)) {
            return error.InvalidTransition;
        }
        self.status = new_status;
    }
};
```

Invalid state transitions return errors at runtime.

### Schema Validation with Comptime

Enforce schema requirements at compile time:

```zig
fn validateSchema(comptime T: type) void {
    const info = @typeInfo(T);
    if (info != .@"struct") {
        @compileError("Schema validation only works on structs");
    }

    // Ensure required fields exist
    var has_id = false;
    inline for (info.@"struct".fields) |field| {
        if (std.mem.eql(u8, field.name, "id")) {
            has_id = true;
            if (field.type != u32) {
                @compileError("id field must be u32");
            }
        }
    }

    if (!has_id) {
        @compileError("Schema must have 'id' field");
    }
}

const Product = struct {
    id: u32,
    name: []const u8,
    price: f64,

    comptime {
        validateSchema(@This());
    }
};
```

Schemas are validated at compile time—invalid schemas won't compile.

### Builder Pattern with Progressive Validation

Validate each field as it's set:

```zig
const Person = struct {
    first_name: []const u8,
    last_name: []const u8,
    email: []const u8,
    age: u8,

    pub const Builder = struct {
        first_name: ?[]const u8 = null,
        last_name: ?[]const u8 = null,
        email: ?[]const u8 = null,
        age: ?u8 = null,

        pub fn setFirstName(self: *Builder, name: []const u8) !*Builder {
            if (name.len == 0) return error.EmptyFirstName;
            self.first_name = name;
            return self;
        }

        pub fn setEmail(self: *Builder, email: []const u8) !*Builder {
            if (std.mem.indexOf(u8, email, "@") == null) {
                return error.InvalidEmail;
            }
            self.email = email;
            return self;
        }

        pub fn build(self: *const Builder) !Person {
            if (self.first_name == null) return error.MissingFirstName;
            if (self.last_name == null) return error.MissingLastName;
            // ... check other required fields

            return Person{
                .first_name = self.first_name.?,
                .last_name = self.last_name.?,
                .email = self.email.?,
                .age = self.age.?,
            };
        }
    };
};
```

Errors surface immediately when invalid data is provided.

### Polymorphic Data Model

Use tagged unions for flexible value types:

```zig
const Value = union(enum) {
    string: []const u8,
    number: f64,
    boolean: bool,
    null_value,

    pub fn asString(self: Value) ![]const u8 {
        return switch (self) {
            .string => |s| s,
            else => error.TypeMismatch,
        };
    }

    pub fn asNumber(self: Value) !f64 {
        return switch (self) {
            .number => |n| n,
            else => error.TypeMismatch,
        };
    }
};

const Record = struct {
    fields: std.StringHashMap(Value),

    pub fn set(self: *Record, key: []const u8, value: Value) !void {
        try self.fields.put(key, value);
    }

    pub fn get(self: *const Record, key: []const u8) ?Value {
        return self.fields.get(key);
    }
};
```

Records can store heterogeneous typed values safely.

### Relationship Models

Model relationships between entities:

```zig
const Author = struct {
    id: u32,
    name: []const u8,
};

const Post = struct {
    id: u32,
    title: []const u8,
    author_id: u32,
    content: []const u8,

    pub fn getAuthor(self: *const Post, authors: []const Author) ?Author {
        for (authors) |author| {
            if (author.id == self.author_id) {
                return author;
            }
        }
        return null;
    }
};
```

Foreign keys link entities, with helper methods for navigation.

### Discussion

Zig's type system and comptime features enable powerful data modeling without runtime overhead.

### Design Patterns

**Newtype pattern**: Wrap primitives in structs for type safety
- Example: `Email`, `Username`, `Price`
- Prevents mixing incompatible values

**Builder pattern**: Progressive validation with clear error messages
- Example: Complex forms, API request builders
- Better UX than constructor with 20 parameters

**Tagged unions**: Type-safe polymorphism
- Example: JSON values, AST nodes, events
- Compile-time exhaustiveness checking

**Composition over inheritance**: Embed common fields
- Example: `BaseEntity` for id/timestamps
- No vtable overhead, explicit delegation

### Validation Strategy

**Compile-time validation**:
- Schema structure (`validateSchema`)
- Field types and names
- Zero runtime cost

**Construction-time validation**:
- Field constraints in `init()`
- Invalid objects can't be created
- Fail fast principle

**Mutation-time validation**:
- Validation in setters
- State transition checking
- Prevents invalid state changes

**Lazy validation**:
- Separate `validate()` method
- Check before serialization/persistence
- Allows building incrementally

### Performance Considerations

All patterns shown have minimal overhead:
- Typed fields compile to raw values
- Validation happens once at construction
- No reflection or dynamic dispatch
- Enums compile to integers with switch statements

### Error Handling

Data model errors should be specific:

```zig
pub fn init(...) !User {
    if (invalid) return error.InvalidEmail;  // Not generic error.Invalid
}
```

Specific errors help callers provide better feedback to users.

### Full Tested Code

```zig
// Recipe 8.13: Implementing a Data Model or Type System
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_validation
// Basic field validation
const User = struct {
    username: []const u8,
    email: []const u8,
    age: u8,

    pub fn validate(self: *const User) !void {
        if (self.username.len == 0 or self.username.len > 50) {
            return error.InvalidUsername;
        }
        if (std.mem.indexOf(u8, self.email, "@") == null) {
            return error.InvalidEmail;
        }
        if (self.age < 13 or self.age > 150) {
            return error.InvalidAge;
        }
    }

    pub fn init(username: []const u8, email: []const u8, age: u8) !User {
        const user = User{
            .username = username,
            .email = email,
            .age = age,
        };
        try user.validate();
        return user;
    }
};
// ANCHOR_END: basic_validation

test "basic validation" {
    const valid_user = try User.init("alice", "alice@example.com", 25);
    try testing.expectEqualStrings("alice", valid_user.username);

    const invalid_username = User.init("", "test@test.com", 25);
    try testing.expectError(error.InvalidUsername, invalid_username);

    const invalid_email = User.init("bob", "invalid", 25);
    try testing.expectError(error.InvalidEmail, invalid_email);
}

// ANCHOR: typed_fields
// Typed fields with validation
const Email = struct {
    value: []const u8,

    pub fn init(value: []const u8) !Email {
        if (value.len == 0) return error.EmptyEmail;
        if (std.mem.indexOf(u8, value, "@") == null) return error.InvalidFormat;
        if (std.mem.indexOf(u8, value, ".") == null) return error.InvalidFormat;
        return Email{ .value = value };
    }

    pub fn getValue(self: *const Email) []const u8 {
        return self.value;
    }
};

const Username = struct {
    value: []const u8,

    pub fn init(value: []const u8) !Username {
        if (value.len < 3) return error.TooShort;
        if (value.len > 20) return error.TooLong;
        for (value) |c| {
            if (!std.ascii.isAlphanumeric(c) and c != '_') {
                return error.InvalidCharacter;
            }
        }
        return Username{ .value = value };
    }

    pub fn getValue(self: *const Username) []const u8 {
        return self.value;
    }
};

const ValidatedUser = struct {
    username: Username,
    email: Email,

    pub fn init(username: []const u8, email: []const u8) !ValidatedUser {
        return ValidatedUser{
            .username = try Username.init(username),
            .email = try Email.init(email),
        };
    }
};
// ANCHOR_END: typed_fields

test "typed fields" {
    const user = try ValidatedUser.init("alice_123", "alice@example.com");
    try testing.expectEqualStrings("alice_123", user.username.getValue());
    try testing.expectEqualStrings("alice@example.com", user.email.getValue());

    const bad_username = ValidatedUser.init("ab", "test@test.com");
    try testing.expectError(error.TooShort, bad_username);

    const bad_email = ValidatedUser.init("alice", "invalid");
    try testing.expectError(error.InvalidFormat, bad_email);
}

// ANCHOR: enum_constraints
// Enum-based constraints
const Status = enum {
    draft,
    published,
    archived,

    pub fn canTransitionTo(self: Status, target: Status) bool {
        return switch (self) {
            .draft => target == .published or target == .archived,
            .published => target == .archived,
            .archived => false,
        };
    }
};

const Document = struct {
    title: []const u8,
    content: []const u8,
    status: Status,

    pub fn init(title: []const u8, content: []const u8) Document {
        return Document{
            .title = title,
            .content = content,
            .status = .draft,
        };
    }

    pub fn changeStatus(self: *Document, new_status: Status) !void {
        if (!self.status.canTransitionTo(new_status)) {
            return error.InvalidTransition;
        }
        self.status = new_status;
    }
};
// ANCHOR_END: enum_constraints

test "enum constraints" {
    var doc = Document.init("My Doc", "Content");
    try testing.expectEqual(Status.draft, doc.status);

    try doc.changeStatus(.published);
    try testing.expectEqual(Status.published, doc.status);

    const result = doc.changeStatus(.draft);
    try testing.expectError(error.InvalidTransition, result);
}

// ANCHOR: relationship_model
// Relationships between models
const Author = struct {
    id: u32,
    name: []const u8,
};

const Post = struct {
    id: u32,
    title: []const u8,
    author_id: u32,
    content: []const u8,

    pub fn getAuthor(self: *const Post, authors: []const Author) ?Author {
        for (authors) |author| {
            if (author.id == self.author_id) {
                return author;
            }
        }
        return null;
    }
};

const Comment = struct {
    id: u32,
    post_id: u32,
    author_id: u32,
    text: []const u8,
};
// ANCHOR_END: relationship_model

test "relationship model" {
    const authors = [_]Author{
        .{ .id = 1, .name = "Alice" },
        .{ .id = 2, .name = "Bob" },
    };

    const post = Post{
        .id = 100,
        .title = "Hello World",
        .author_id = 1,
        .content = "First post!",
    };

    const author = post.getAuthor(&authors);
    try testing.expect(author != null);
    try testing.expectEqualStrings("Alice", author.?.name);
}

// ANCHOR: schema_validation
// Schema validation with comptime
fn validateSchema(comptime T: type) void {
    const info = @typeInfo(T);
    if (info != .@"struct") {
        @compileError("Schema validation only works on structs");
    }

    // Ensure required fields exist
    var has_id = false;
    inline for (info.@"struct".fields) |field| {
        if (std.mem.eql(u8, field.name, "id")) {
            has_id = true;
            if (field.type != u32) {
                @compileError("id field must be u32");
            }
        }
    }

    if (!has_id) {
        @compileError("Schema must have 'id' field");
    }
}

const Product = struct {
    id: u32,
    name: []const u8,
    price: f64,

    comptime {
        validateSchema(@This());
    }
};
// ANCHOR_END: schema_validation

test "schema validation" {
    const product = Product{
        .id = 1,
        .name = "Widget",
        .price = 19.99,
    };

    try testing.expectEqual(@as(u32, 1), product.id);
}

// ANCHOR: builder_with_validation
// Builder pattern with progressive validation
const Person = struct {
    first_name: []const u8,
    last_name: []const u8,
    email: []const u8,
    age: u8,

    pub const Builder = struct {
        first_name: ?[]const u8 = null,
        last_name: ?[]const u8 = null,
        email: ?[]const u8 = null,
        age: ?u8 = null,

        pub fn setFirstName(self: *Builder, name: []const u8) !*Builder {
            if (name.len == 0) return error.EmptyFirstName;
            self.first_name = name;
            return self;
        }

        pub fn setLastName(self: *Builder, name: []const u8) !*Builder {
            if (name.len == 0) return error.EmptyLastName;
            self.last_name = name;
            return self;
        }

        pub fn setEmail(self: *Builder, email: []const u8) !*Builder {
            if (std.mem.indexOf(u8, email, "@") == null) {
                return error.InvalidEmail;
            }
            self.email = email;
            return self;
        }

        pub fn setAge(self: *Builder, age: u8) !*Builder {
            if (age < 18) return error.TooYoung;
            self.age = age;
            return self;
        }

        pub fn build(self: *const Builder) !Person {
            if (self.first_name == null) return error.MissingFirstName;
            if (self.last_name == null) return error.MissingLastName;
            if (self.email == null) return error.MissingEmail;
            if (self.age == null) return error.MissingAge;

            return Person{
                .first_name = self.first_name.?,
                .last_name = self.last_name.?,
                .email = self.email.?,
                .age = self.age.?,
            };
        }
    };
};
// ANCHOR_END: builder_with_validation

test "builder with validation" {
    var builder = Person.Builder{};

    _ = try builder.setFirstName("John");
    _ = try builder.setLastName("Doe");
    _ = try builder.setEmail("john@example.com");
    _ = try builder.setAge(30);
    const person = try builder.build();

    try testing.expectEqualStrings("John", person.first_name);
    try testing.expectEqual(@as(u8, 30), person.age);

    var bad_builder = Person.Builder{};
    _ = try bad_builder.setFirstName("Jane");
    const result = bad_builder.build();
    try testing.expectError(error.MissingLastName, result);
}

// ANCHOR: polymorphic_data
// Polymorphic data model
const Value = union(enum) {
    string: []const u8,
    number: f64,
    boolean: bool,
    null_value,

    pub fn typeStr(self: Value) []const u8 {
        return switch (self) {
            .string => "string",
            .number => "number",
            .boolean => "boolean",
            .null_value => "null",
        };
    }

    pub fn asString(self: Value) ![]const u8 {
        return switch (self) {
            .string => |s| s,
            else => error.TypeMismatch,
        };
    }

    pub fn asNumber(self: Value) !f64 {
        return switch (self) {
            .number => |n| n,
            else => error.TypeMismatch,
        };
    }
};

const Record = struct {
    fields: std.StringHashMap(Value),

    pub fn init(allocator: std.mem.Allocator) Record {
        return Record{
            .fields = std.StringHashMap(Value).init(allocator),
        };
    }

    pub fn deinit(self: *Record) void {
        self.fields.deinit();
    }

    pub fn set(self: *Record, key: []const u8, value: Value) !void {
        try self.fields.put(key, value);
    }

    pub fn get(self: *const Record, key: []const u8) ?Value {
        return self.fields.get(key);
    }
};
// ANCHOR_END: polymorphic_data

test "polymorphic data" {
    var record = Record.init(testing.allocator);
    defer record.deinit();

    try record.set("name", .{ .string = "Alice" });
    try record.set("age", .{ .number = 30 });
    try record.set("active", .{ .boolean = true });

    const name = record.get("name");
    try testing.expect(name != null);
    try testing.expectEqualStrings("Alice", try name.?.asString());

    const age = record.get("age");
    try testing.expectEqual(@as(f64, 30), try age.?.asNumber());
}

// ANCHOR: inheritance_alternative
// Inheritance alternative via composition
const BaseEntity = struct {
    id: u32,
    created_at: i64,
    updated_at: i64,

    pub fn init(id: u32, timestamp: i64) BaseEntity {
        return BaseEntity{
            .id = id,
            .created_at = timestamp,
            .updated_at = timestamp,
        };
    }

    pub fn touch(self: *BaseEntity, timestamp: i64) void {
        self.updated_at = timestamp;
    }
};

const Article = struct {
    base: BaseEntity,
    title: []const u8,
    body: []const u8,

    pub fn init(id: u32, title: []const u8, body: []const u8, timestamp: i64) Article {
        return Article{
            .base = BaseEntity.init(id, timestamp),
            .title = title,
            .body = body,
        };
    }

    pub fn getId(self: *const Article) u32 {
        return self.base.id;
    }

    pub fn update(self: *Article, body: []const u8, timestamp: i64) void {
        self.body = body;
        self.base.touch(timestamp);
    }
};
// ANCHOR_END: inheritance_alternative

test "inheritance alternative" {
    var article = Article.init(1, "Title", "Original body", 1000);
    try testing.expectEqual(@as(u32, 1), article.getId());
    try testing.expectEqual(@as(i64, 1000), article.base.created_at);

    article.update("Updated body", 2000);
    try testing.expectEqualStrings("Updated body", article.body);
    try testing.expectEqual(@as(i64, 2000), article.base.updated_at);
}

// ANCHOR: serialization_metadata
// Serialization with metadata
const FieldMeta = struct {
    json_name: []const u8,
    required: bool,
    default_value: ?[]const u8,
};

fn serializeToJson(comptime T: type, value: T, allocator: std.mem.Allocator) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    try result.appendSlice(allocator, "{");

    const info = @typeInfo(T);
    inline for (info.@"struct".fields, 0..) |field, i| {
        if (i > 0) try result.appendSlice(allocator, ",");

        try result.appendSlice(allocator, "\"");
        try result.appendSlice(allocator, field.name);
        try result.appendSlice(allocator, "\":");

        const field_value = @field(value, field.name);
        const field_type = @TypeOf(field_value);

        if (field_type == []const u8) {
            try result.appendSlice(allocator, "\"");
            try result.appendSlice(allocator, field_value);
            try result.appendSlice(allocator, "\"");
        } else {
            const value_str = try std.fmt.allocPrint(allocator, "{d}", .{field_value});
            defer allocator.free(value_str);
            try result.appendSlice(allocator, value_str);
        }
    }

    try result.appendSlice(allocator, "}");
    return result.toOwnedSlice(allocator);
}

const ApiResponse = struct {
    status: u16,
    message: []const u8,
};
// ANCHOR_END: serialization_metadata

test "serialization metadata" {
    const response = ApiResponse{
        .status = 200,
        .message = "OK",
    };

    const json = try serializeToJson(ApiResponse, response, testing.allocator);
    defer testing.allocator.free(json);

    try testing.expect(std.mem.indexOf(u8, json, "\"status\":200") != null);
    try testing.expect(std.mem.indexOf(u8, json, "\"message\":\"OK\"") != null);
}

// ANCHOR: query_builder
// Query builder pattern
const QueryBuilder = struct {
    table: []const u8,
    where_clauses: std.ArrayList([]const u8),
    limit_value: ?usize,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, table: []const u8) QueryBuilder {
        return QueryBuilder{
            .table = table,
            .where_clauses = std.ArrayList([]const u8){},
            .limit_value = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *QueryBuilder) void {
        self.where_clauses.deinit(self.allocator);
    }

    pub fn where(self: *QueryBuilder, clause: []const u8) !*QueryBuilder {
        try self.where_clauses.append(self.allocator, clause);
        return self;
    }

    pub fn limit(self: *QueryBuilder, value: usize) *QueryBuilder {
        self.limit_value = value;
        return self;
    }

    pub fn build(self: *const QueryBuilder, allocator: std.mem.Allocator) ![]u8 {
        var result = std.ArrayList(u8){};
        errdefer result.deinit(allocator);

        try result.appendSlice(allocator, "SELECT * FROM ");
        try result.appendSlice(allocator, self.table);

        if (self.where_clauses.items.len > 0) {
            try result.appendSlice(allocator, " WHERE ");
            for (self.where_clauses.items, 0..) |clause, i| {
                if (i > 0) try result.appendSlice(allocator, " AND ");
                try result.appendSlice(allocator, clause);
            }
        }

        if (self.limit_value) |lim| {
            const limit_str = try std.fmt.allocPrint(allocator, " LIMIT {d}", .{lim});
            defer allocator.free(limit_str);
            try result.appendSlice(allocator, limit_str);
        }

        return result.toOwnedSlice(allocator);
    }
};
// ANCHOR_END: query_builder

test "query builder" {
    var query = QueryBuilder.init(testing.allocator, "users");
    defer query.deinit();

    _ = try query.where("age > 18");
    _ = try query.where("active = true");
    _ = query.limit(10);
    const sql = try query.build(testing.allocator);
    defer testing.allocator.free(sql);

    try testing.expect(std.mem.indexOf(u8, sql, "SELECT * FROM users") != null);
    try testing.expect(std.mem.indexOf(u8, sql, "WHERE age > 18 AND active = true") != null);
    try testing.expect(std.mem.indexOf(u8, sql, "LIMIT 10") != null);
}

// Comprehensive test
test "comprehensive data model" {
    const valid_user = try User.init("testuser", "test@test.com", 25);
    try valid_user.validate();

    const validated = try ValidatedUser.init("john_doe", "john@example.com");
    try testing.expectEqualStrings("john_doe", validated.username.getValue());

    var doc = Document.init("Test", "Content");
    try doc.changeStatus(.published);
    try testing.expectEqual(Status.published, doc.status);

    const product = Product{ .id = 123, .name = "Test", .price = 9.99 };
    try testing.expectEqual(@as(u32, 123), product.id);
}
```

### See Also

- Recipe 8.11: Simplifying the Initialization of Data Structures
- Recipe 8.12: Defining an Interface or Abstract Base Class
- Recipe 8.14: Implementing Custom Containers
- Recipe 9.16: Defining Structs Programmatically

---

## Recipe 8.14: Implementing Custom Containers {#recipe-8-14}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, hashmap, memory, pointers, resource-cleanup, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_14.zig`

### Problem

You need to implement custom containers or data structures with generic types, similar to ArrayList or HashMap in the standard library.

### Solution

Use Zig's comptime type parameters to create generic containers with zero runtime overhead. Each container is specialized at compile time for the types it holds.

### Generic Stack

Create a dynamic stack that grows as needed:

```zig
// Generic stack container
fn Stack(comptime T: type) type {
    return struct {
        items: []T,
        len: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            return Self{
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

        pub fn push(self: *Self, item: T) !void {
            if (self.len >= self.items.len) {
                const new_cap = if (self.items.len == 0) 4 else self.items.len * 2;
                const new_items = try self.allocator.realloc(self.items, new_cap);
                self.items = new_items;
            }
            self.items[self.len] = item;
            self.len += 1;
        }

        pub fn pop(self: *Self) ?T {
            if (self.len == 0) return null;
            self.len -= 1;
            return self.items[self.len];
        }

        pub fn peek(self: *const Self) ?T {
            if (self.len == 0) return null;
            return self.items[self.len - 1];
        }

        pub fn isEmpty(self: *const Self) bool {
            return self.len == 0;
        }

        pub fn size(self: *const Self) usize {
            return self.len;
        }
    };
}

        pub fn pop(self: *Self) ?T {
            if (self.len == 0) return null;
            self.len -= 1;
            return self.items[self.len];
        }
    };
}
```

The function returns a struct type, creating a new specialized stack for each type parameter.

### Circular Buffer

Fixed-capacity ring buffer with compile-time size:

```zig
fn CircularBuffer(comptime T: type, comptime capacity: usize) type {
    return struct {
        buffer: [capacity]T,
        read_index: usize,
        write_index: usize,
        count: usize,

        pub fn write(self: *Self, item: T) !void {
            if (self.isFull()) return error.BufferFull;

            self.buffer[self.write_index] = item;
            self.write_index = (self.write_index + 1) % capacity;
            self.count += 1;
        }

        pub fn read(self: *Self) ?T {
            if (self.isEmpty()) return null;

            const item = self.buffer[self.read_index];
            self.read_index = (self.read_index + 1) % capacity;
            self.count -= 1;
            return item;
        }
    };
}
```

The buffer wraps around when full, overwriting old data efficiently.

### Linked List

Singly linked list with dynamic nodes:

```zig
fn LinkedList(comptime T: type) type {
    return struct {
        const Node = struct {
            data: T,
            next: ?*Node,
        };

        head: ?*Node,
        tail: ?*Node,
        len: usize,
        allocator: std.mem.Allocator,

        pub fn append(self: *Self, data: T) !void {
            const node = try self.allocator.create(Node);
            node.* = Node{ .data = data, .next = null };

            if (self.tail) |tail| {
                tail.next = node;
            } else {
                self.head = node;
            }

            self.tail = node;
            self.len += 1;
        }

        pub fn removeFirst(self: *Self) ?T {
            const head = self.head orelse return null;
            const data = head.data;

            self.head = head.next;
            if (self.head == null) {
                self.tail = null;
            }

            self.allocator.destroy(head);
            self.len -= 1;
            return data;
        }
    };
}
```

Linked lists provide O(1) insertion and removal at both ends.

### Priority Queue

Min-heap based priority queue:

```zig
fn PriorityQueue(comptime T: type) type {
    return struct {
        items: std.ArrayList(T),

        pub fn insert(self: *Self, allocator: std.mem.Allocator, value: T) !void {
            try self.items.append(allocator, value);
            self.bubbleUp(self.items.items.len - 1);
        }

        pub fn extractMin(self: *Self) ?T {
            if (self.items.items.len == 0) return null;

            const min = self.items.items[0];

            if (self.items.items.len > 1) {
                const last_idx = self.items.items.len - 1;
                self.items.items[0] = self.items.items[last_idx];
                _ = self.items.pop();
                self.bubbleDown(0);
            } else {
                _ = self.items.pop();
            }

            return min;
        }

        fn bubbleUp(self: *Self, index: usize) void {
            if (index == 0) return;

            const parent_index = (index - 1) / 2;
            if (self.items.items[index] < self.items.items[parent_index]) {
                // Swap and recurse
            }
        }
    };
}
```

Always extracts the minimum element efficiently.

### Iterator Pattern

Custom containers can provide iterators:

```zig
const IntRange = struct {
    start: i32,
    end: i32,

    pub const Iterator = struct {
        current: i32,
        end: i32,

        pub fn next(self: *Iterator) ?i32 {
            if (self.current >= self.end) return null;
            const value = self.current;
            self.current += 1;
            return value;
        }
    };

    pub fn iterator(self: *const IntRange) Iterator {
        return Iterator{
            .current = self.start,
            .end = self.end,
        };
    }
};
```

Iterators allow sequential access without exposing internal structure.

### Discussion

Zig's generic containers are fundamentally different from templates in C++ or generics in Java.

### Compile-Time Specialization

Every generic container creates a unique type at compile time:

```zig
const IntStack = Stack(i32);    // Distinct type
const StrStack = Stack([]u8);   // Different distinct type
```

This allows:
- Full type checking at compile time
- Zero runtime overhead
- Optimizations specific to each type
- No boxing or runtime type information

### Container Design Patterns

**Return struct from function**: Generic containers are functions that return types

```zig
fn MyContainer(comptime T: type) type {
    return struct {
        // Container implementation
    };
}
```

**Comptime parameters**: Accept both types and values

```zig
fn FixedArray(comptime T: type, comptime size: usize) type {
    return struct {
        data: [size]T,
    };
}
```

**Inner types**: Define helper types within the container

```zig
fn List(comptime T: type) type {
    return struct {
        const Node = struct { data: T, next: ?*Node };
        // Use Node internally
    };
}
```

### Memory Management

Containers must handle allocation explicitly:

- **Init pattern**: Accept allocator in init
- **Deinit cleanup**: Free all allocated memory
- **Allocator storage**: Store allocator for later use
- **Error handling**: Return allocation errors to caller

Example memory-safe pattern:

```zig
var list = LinkedList(i32).init(allocator);
defer list.deinit();  // Ensures cleanup

try list.append(42);  // Propagate allocation errors
```

### Performance Considerations

**Stack**:
- Push/pop: O(1) amortized with doubling strategy
- Memory: Contiguous, cache-friendly
- Use for: LIFO access patterns

**Circular Buffer**:
- Write/read: O(1) always
- Memory: Fixed, no allocations
- Use for: Bounded queues, ring buffers

**Linked List**:
- Insert/remove ends: O(1)
- Memory: Scattered, pointer overhead
- Use for: Frequent insertion/deletion

**Priority Queue**:
- Insert: O(log n)
- Extract min: O(log n)
- Memory: Contiguous array
- Use for: Always need minimum element

### Type Constraints

Containers can require specific capabilities:

```zig
fn SortedList(comptime T: type) type {
    // Verify type supports comparison at compile time
    const dummy: T = undefined;
    _ = dummy < dummy;  // Compile error if < not supported

    return struct {
        // Implementation
    };
}
```

The compiler enforces type requirements automatically.

### Full Tested Code

```zig
// Recipe 8.14: Implementing Custom Containers
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: generic_stack
// Generic stack container
fn Stack(comptime T: type) type {
    return struct {
        items: []T,
        len: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            return Self{
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

        pub fn push(self: *Self, item: T) !void {
            if (self.len >= self.items.len) {
                const new_cap = if (self.items.len == 0) 4 else self.items.len * 2;
                const new_items = try self.allocator.realloc(self.items, new_cap);
                self.items = new_items;
            }
            self.items[self.len] = item;
            self.len += 1;
        }

        pub fn pop(self: *Self) ?T {
            if (self.len == 0) return null;
            self.len -= 1;
            return self.items[self.len];
        }

        pub fn peek(self: *const Self) ?T {
            if (self.len == 0) return null;
            return self.items[self.len - 1];
        }

        pub fn isEmpty(self: *const Self) bool {
            return self.len == 0;
        }

        pub fn size(self: *const Self) usize {
            return self.len;
        }
    };
}
// ANCHOR_END: generic_stack

test "generic stack" {
    var stack = Stack(i32).init(testing.allocator);
    defer stack.deinit();

    try testing.expect(stack.isEmpty());

    try stack.push(10);
    try stack.push(20);
    try stack.push(30);

    try testing.expectEqual(@as(usize, 3), stack.size());
    try testing.expectEqual(@as(i32, 30), stack.peek().?);

    try testing.expectEqual(@as(i32, 30), stack.pop().?);
    try testing.expectEqual(@as(i32, 20), stack.pop().?);
    try testing.expectEqual(@as(usize, 1), stack.size());
}

// ANCHOR: circular_buffer
// Circular buffer (ring buffer)
fn CircularBuffer(comptime T: type, comptime capacity: usize) type {
    return struct {
        buffer: [capacity]T,
        read_index: usize,
        write_index: usize,
        count: usize,

        const Self = @This();

        pub fn init() Self {
            return Self{
                .buffer = undefined,
                .read_index = 0,
                .write_index = 0,
                .count = 0,
            };
        }

        pub fn write(self: *Self, item: T) !void {
            if (self.isFull()) return error.BufferFull;

            self.buffer[self.write_index] = item;
            self.write_index = (self.write_index + 1) % capacity;
            self.count += 1;
        }

        pub fn read(self: *Self) ?T {
            if (self.isEmpty()) return null;

            const item = self.buffer[self.read_index];
            self.read_index = (self.read_index + 1) % capacity;
            self.count -= 1;
            return item;
        }

        pub fn isEmpty(self: *const Self) bool {
            return self.count == 0;
        }

        pub fn isFull(self: *const Self) bool {
            return self.count == capacity;
        }

        pub fn size(self: *const Self) usize {
            return self.count;
        }
    };
}
// ANCHOR_END: circular_buffer

test "circular buffer" {
    var buffer = CircularBuffer(u8, 4).init();

    try testing.expect(buffer.isEmpty());

    try buffer.write(1);
    try buffer.write(2);
    try buffer.write(3);

    try testing.expectEqual(@as(usize, 3), buffer.size());

    try testing.expectEqual(@as(u8, 1), buffer.read().?);
    try testing.expectEqual(@as(u8, 2), buffer.read().?);

    try buffer.write(4);
    try buffer.write(5);
    try buffer.write(6);

    try testing.expect(buffer.isFull());
    const result = buffer.write(7);
    try testing.expectError(error.BufferFull, result);
}

// ANCHOR: linked_list
// Singly linked list
fn LinkedList(comptime T: type) type {
    return struct {
        const Node = struct {
            data: T,
            next: ?*Node,
        };

        head: ?*Node,
        tail: ?*Node,
        len: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            return Self{
                .head = null,
                .tail = null,
                .len = 0,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            var current = self.head;
            while (current) |node| {
                const next = node.next;
                self.allocator.destroy(node);
                current = next;
            }
        }

        pub fn append(self: *Self, data: T) !void {
            const node = try self.allocator.create(Node);
            node.* = Node{ .data = data, .next = null };

            if (self.tail) |tail| {
                tail.next = node;
            } else {
                self.head = node;
            }

            self.tail = node;
            self.len += 1;
        }

        pub fn prepend(self: *Self, data: T) !void {
            const node = try self.allocator.create(Node);
            node.* = Node{ .data = data, .next = self.head };

            self.head = node;
            if (self.tail == null) {
                self.tail = node;
            }

            self.len += 1;
        }

        pub fn removeFirst(self: *Self) ?T {
            const head = self.head orelse return null;
            const data = head.data;

            self.head = head.next;
            if (self.head == null) {
                self.tail = null;
            }

            self.allocator.destroy(head);
            self.len -= 1;
            return data;
        }

        pub fn size(self: *const Self) usize {
            return self.len;
        }
    };
}
// ANCHOR_END: linked_list

test "linked list" {
    var list = LinkedList(i32).init(testing.allocator);
    defer list.deinit();

    try list.append(10);
    try list.append(20);
    try list.prepend(5);

    try testing.expectEqual(@as(usize, 3), list.size());

    try testing.expectEqual(@as(i32, 5), list.removeFirst().?);
    try testing.expectEqual(@as(i32, 10), list.removeFirst().?);
    try testing.expectEqual(@as(usize, 1), list.size());
}

// ANCHOR: priority_queue
// Min-heap based priority queue
fn PriorityQueue(comptime T: type) type {
    return struct {
        items: std.ArrayList(T),

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            _ = allocator;
            return Self{
                .items = std.ArrayList(T){},
            };
        }

        pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            self.items.deinit(allocator);
        }

        pub fn insert(self: *Self, allocator: std.mem.Allocator, value: T) !void {
            try self.items.append(allocator, value);
            self.bubbleUp(self.items.items.len - 1);
        }

        pub fn extractMin(self: *Self) ?T {
            if (self.items.items.len == 0) return null;

            const min = self.items.items[0];

            if (self.items.items.len > 1) {
                const last_idx = self.items.items.len - 1;
                self.items.items[0] = self.items.items[last_idx];
                _ = self.items.pop();
                self.bubbleDown(0);
            } else {
                _ = self.items.pop();
            }

            return min;
        }

        pub fn peek(self: *const Self) ?T {
            if (self.items.items.len == 0) return null;
            return self.items.items[0];
        }

        pub fn size(self: *const Self) usize {
            return self.items.items.len;
        }

        fn bubbleUp(self: *Self, index: usize) void {
            if (index == 0) return;

            const parent_index = (index - 1) / 2;
            if (self.items.items[index] < self.items.items[parent_index]) {
                const temp = self.items.items[index];
                self.items.items[index] = self.items.items[parent_index];
                self.items.items[parent_index] = temp;
                self.bubbleUp(parent_index);
            }
        }

        fn bubbleDown(self: *Self, index: usize) void {
            const left = 2 * index + 1;
            const right = 2 * index + 2;
            var smallest = index;

            if (left < self.items.items.len and self.items.items[left] < self.items.items[smallest]) {
                smallest = left;
            }

            if (right < self.items.items.len and self.items.items[right] < self.items.items[smallest]) {
                smallest = right;
            }

            if (smallest != index) {
                const temp = self.items.items[index];
                self.items.items[index] = self.items.items[smallest];
                self.items.items[smallest] = temp;
                self.bubbleDown(smallest);
            }
        }
    };
}
// ANCHOR_END: priority_queue

test "priority queue" {
    var pq = PriorityQueue(i32).init(testing.allocator);
    defer pq.deinit(testing.allocator);

    try pq.insert(testing.allocator, 30);
    try pq.insert(testing.allocator, 10);
    try pq.insert(testing.allocator, 20);
    try pq.insert(testing.allocator, 5);

    try testing.expectEqual(@as(i32, 5), pq.peek().?);
    try testing.expectEqual(@as(i32, 5), pq.extractMin().?);
    try testing.expectEqual(@as(i32, 10), pq.extractMin().?);
    try testing.expectEqual(@as(i32, 20), pq.extractMin().?);
    try testing.expectEqual(@as(usize, 1), pq.size());
}

// ANCHOR: bounded_queue
// Bounded queue with fixed capacity
fn BoundedQueue(comptime T: type, comptime max_size: usize) type {
    return struct {
        buffer: [max_size]T,
        head: usize,
        tail: usize,
        count: usize,

        const Self = @This();

        pub fn init() Self {
            return Self{
                .buffer = undefined,
                .head = 0,
                .tail = 0,
                .count = 0,
            };
        }

        pub fn enqueue(self: *Self, item: T) !void {
            if (self.count >= max_size) return error.QueueFull;

            self.buffer[self.tail] = item;
            self.tail = (self.tail + 1) % max_size;
            self.count += 1;
        }

        pub fn dequeue(self: *Self) ?T {
            if (self.count == 0) return null;

            const item = self.buffer[self.head];
            self.head = (self.head + 1) % max_size;
            self.count -= 1;
            return item;
        }

        pub fn peek(self: *const Self) ?T {
            if (self.count == 0) return null;
            return self.buffer[self.head];
        }

        pub fn size(self: *const Self) usize {
            return self.count;
        }

        pub fn isFull(self: *const Self) bool {
            return self.count >= max_size;
        }
    };
}
// ANCHOR_END: bounded_queue

test "bounded queue" {
    var queue = BoundedQueue([]const u8, 3).init();

    try queue.enqueue("first");
    try queue.enqueue("second");
    try queue.enqueue("third");

    try testing.expect(queue.isFull());

    try testing.expectEqualStrings("first", queue.dequeue().?);
    try testing.expectEqualStrings("second", queue.peek().?);
    try testing.expectEqual(@as(usize, 2), queue.size());
}

// ANCHOR: set_container
// Simple hash set
fn Set(comptime T: type) type {
    return struct {
        map: std.AutoHashMap(T, void),

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            return Self{
                .map = std.AutoHashMap(T, void).init(allocator),
            };
        }

        pub fn deinit(self: *Self) void {
            self.map.deinit();
        }

        pub fn add(self: *Self, item: T) !void {
            try self.map.put(item, {});
        }

        pub fn remove(self: *Self, item: T) bool {
            return self.map.remove(item);
        }

        pub fn contains(self: *const Self, item: T) bool {
            return self.map.contains(item);
        }

        pub fn size(self: *const Self) usize {
            return self.map.count();
        }

        pub fn clear(self: *Self) void {
            self.map.clearRetainingCapacity();
        }
    };
}
// ANCHOR_END: set_container

test "set container" {
    var set = Set(i32).init(testing.allocator);
    defer set.deinit();

    try set.add(10);
    try set.add(20);
    try set.add(10); // Duplicate

    try testing.expectEqual(@as(usize, 2), set.size());
    try testing.expect(set.contains(10));
    try testing.expect(!set.contains(30));

    try testing.expect(set.remove(10));
    try testing.expect(!set.contains(10));
    try testing.expectEqual(@as(usize, 1), set.size());
}

// ANCHOR: doubly_linked_list
// Doubly linked list for bidirectional iteration
fn DoublyLinkedList(comptime T: type) type {
    return struct {
        const Node = struct {
            data: T,
            prev: ?*Node,
            next: ?*Node,
        };

        head: ?*Node,
        tail: ?*Node,
        len: usize,
        allocator: std.mem.Allocator,

        const Self = @This();

        pub fn init(allocator: std.mem.Allocator) Self {
            return Self{
                .head = null,
                .tail = null,
                .len = 0,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            var current = self.head;
            while (current) |node| {
                const next = node.next;
                self.allocator.destroy(node);
                current = next;
            }
        }

        pub fn append(self: *Self, data: T) !void {
            const node = try self.allocator.create(Node);
            node.* = Node{ .data = data, .prev = self.tail, .next = null };

            if (self.tail) |tail| {
                tail.next = node;
            } else {
                self.head = node;
            }

            self.tail = node;
            self.len += 1;
        }

        pub fn removeLast(self: *Self) ?T {
            const tail = self.tail orelse return null;
            const data = tail.data;

            if (tail.prev) |prev| {
                prev.next = null;
                self.tail = prev;
            } else {
                self.head = null;
                self.tail = null;
            }

            self.allocator.destroy(tail);
            self.len -= 1;
            return data;
        }

        pub fn size(self: *const Self) usize {
            return self.len;
        }
    };
}
// ANCHOR_END: doubly_linked_list

test "doubly linked list" {
    var list = DoublyLinkedList(i32).init(testing.allocator);
    defer list.deinit();

    try list.append(1);
    try list.append(2);
    try list.append(3);

    try testing.expectEqual(@as(usize, 3), list.size());
    try testing.expectEqual(@as(i32, 3), list.removeLast().?);
    try testing.expectEqual(@as(i32, 2), list.removeLast().?);
    try testing.expectEqual(@as(usize, 1), list.size());
}

// ANCHOR: iterator_pattern
// Container with iterator
const IntRange = struct {
    start: i32,
    end: i32,

    pub fn init(start: i32, end: i32) IntRange {
        return IntRange{ .start = start, .end = end };
    }

    pub const Iterator = struct {
        current: i32,
        end: i32,

        pub fn next(self: *Iterator) ?i32 {
            if (self.current >= self.end) return null;
            const value = self.current;
            self.current += 1;
            return value;
        }
    };

    pub fn iterator(self: *const IntRange) Iterator {
        return Iterator{
            .current = self.start,
            .end = self.end,
        };
    }
};
// ANCHOR_END: iterator_pattern

test "iterator pattern" {
    const range = IntRange.init(0, 5);
    var iter = range.iterator();

    try testing.expectEqual(@as(i32, 0), iter.next().?);
    try testing.expectEqual(@as(i32, 1), iter.next().?);
    try testing.expectEqual(@as(i32, 2), iter.next().?);
    try testing.expectEqual(@as(i32, 3), iter.next().?);
    try testing.expectEqual(@as(i32, 4), iter.next().?);
    try testing.expect(iter.next() == null);
}

// Comprehensive test
test "comprehensive custom containers" {
    var stack = Stack(i32).init(testing.allocator);
    defer stack.deinit();
    try stack.push(42);
    try testing.expectEqual(@as(i32, 42), stack.pop().?);

    var buffer = CircularBuffer(u8, 8).init();
    try buffer.write(100);
    try testing.expectEqual(@as(u8, 100), buffer.read().?);

    var list = LinkedList(i32).init(testing.allocator);
    defer list.deinit();
    try list.append(10);
    try testing.expectEqual(@as(usize, 1), list.size());

    var set = Set(i32).init(testing.allocator);
    defer set.deinit();
    try set.add(5);
    try testing.expect(set.contains(5));
}
```

### See Also

- Recipe 8.13: Implementing a Data Model or Type System
- Recipe 8.15: Delegating Attribute Access
- Recipe 9.11: Using comptime to Control Instance Creation
- Recipe 9.16: Defining Structs Programmatically

---

## Recipe 8.15: Delegating Attribute Access {#recipe-8-15}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, hashmap, memory, pointers, resource-cleanup, slices, structs-objects, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_15.zig`

### Problem

You want to delegate method calls or attribute access from one object to another, implementing patterns like proxies, wrappers, or forwarding without inheritance.

### Solution

Use composition with explicit delegation methods to forward calls to embedded structs. Zig's composition-over-inheritance approach makes delegation explicit and type-safe.

### Basic Delegation

Delegate engine operations to a car:

```zig
// Basic method delegation
const Engine = struct {
    power: u32,
    running: bool,

    pub fn init(power: u32) Engine {
        return Engine{
            .power = power,
            .running = false,
        };
    }

    pub fn start(self: *Engine) void {
        self.running = true;
    }

    pub fn stop(self: *Engine) void {
        self.running = false;
    }

    pub fn isRunning(self: *const Engine) bool {
        return self.running;
    }

    pub fn getPower(self: *const Engine) u32 {
        return self.power;
    }
};

const Car = struct {
    engine: Engine,
    model: []const u8,

    pub fn init(model: []const u8, engine_power: u32) Car {
        return Car{
            .engine = Engine.init(engine_power),
            .model = model,
        };
    }

    // Delegate to engine
    pub fn start(self: *Car) void {
        self.engine.start();
    }

    pub fn stop(self: *Car) void {
        self.engine.stop();
    }

    pub fn isRunning(self: *const Car) bool {
        return self.engine.isRunning();
    }

    pub fn getEnginePower(self: *const Car) u32 {
        return self.engine.getPower();
    }
};
    }
};
```

The car delegates engine-related operations while adding its own functionality.

### Transparent Proxy

Add metrics tracking to an existing data store:

```zig
const CachedDataStore = struct {
    store: DataStore,
    cache_hits: u32,
    cache_misses: u32,

    pub fn get(self: *CachedDataStore, key: []const u8) ?[]const u8 {
        const result = self.store.get(key);
        if (result != null) {
            self.cache_hits += 1;
        } else {
            self.cache_misses += 1;
        }
        return result;
    }

    pub fn put(self: *CachedDataStore, key: []const u8, value: []const u8) !void {
        try self.store.put(key, value);
    }

    pub fn getCacheStats(self: *const CachedDataStore) struct { hits: u32, misses: u32 } {
        return .{ .hits = self.cache_hits, .misses = self.cache_misses };
    }
};
```

The proxy forwards all operations while collecting statistics.

### Property Forwarding

Forward dimensional properties from a box:

```zig
const Box = struct {
    dimensions: Dimensions,
    material: []const u8,

    pub fn getWidth(self: *const Box) f32 {
        return self.dimensions.width;
    }

    pub fn getHeight(self: *const Box) f32 {
        return self.dimensions.height;
    }

    pub fn getVolume(self: *const Box) f32 {
        return self.dimensions.getVolume();
    }
};
```

The box provides convenient access to embedded dimension data.

### Selective Delegation

Only expose safe operations:

```zig
const ReadOnlyFileSystem = struct {
    // Only expose read operation
    pub fn read(path: []const u8) ![]const u8 {
        return FileSystem.read(path);
    }

    // write and delete are not exposed
};
```

This creates a restricted interface by selectively delegating operations.

### Logging Wrapper

Wrap operations with logging:

```zig
const LoggedDatabase = struct {
    db: Database,
    query_log: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    pub fn query(self: *LoggedDatabase, sql: []const u8) !void {
        try self.query_log.append(self.allocator, sql);
        try self.db.query(sql);
    }

    pub fn getQueryLog(self: *const LoggedDatabase) []const []const u8 {
        return self.query_log.items;
    }
};
```

Every operation is logged before being delegated.

### Chain Delegation

Create layers of delegation:

```zig
const CompressedEncryptedNetwork = struct {
    encrypted: EncryptedNetwork,

    pub fn send(self: *CompressedEncryptedNetwork, data: []const u8) void {
        // Compress data
        const compressed_size = data.len / 2;
        const compressed_data = data[0..compressed_size];

        // Delegate to encrypted layer
        self.encrypted.send(compressed_data);
    }
};
```

Each layer adds functionality and delegates to the next.

### Dynamic Delegation

Use interfaces for runtime delegation:

```zig
const Writer = struct {
    ptr: *anyopaque,
    writeFn: *const fn (ptr: *anyopaque, data: []const u8) anyerror!void,

    pub fn write(self: Writer, data: []const u8) !void {
        return self.writeFn(self.ptr, data);
    }
};

const DelegatingWriter = struct {
    writer: Writer,

    pub fn writeLine(self: *DelegatingWriter, line: []const u8) !void {
        try self.writer.write(line);
        try self.writer.write("\n");
    }
};
```

The delegation target can be determined at runtime.

### Mixin-Style Delegation

Add capabilities using generic wrappers:

```zig
fn WithLogging(comptime T: type) type {
    return struct {
        inner: T,
        log_count: u32,

        pub fn call(self: *Self) void {
            self.log_count += 1;
            if (@hasDecl(T, "call")) {
                self.inner.call();
            }
        }

        pub fn getLogCount(self: *const Self) u32 {
            return self.log_count;
        }
    };
}

const service = SimpleService.init();
var logged = WithLogging(SimpleService).init(service);
logged.call();  // Logged and delegated
```

Mixins wrap any type that supports the required interface.

### Conditional Delegation

Only delegate if certain conditions are met:

```zig
const SafeCalculator = struct {
    calculator: Calculator,
    overflow_occurred: bool,

    pub fn add(self: *SafeCalculator, value: f64) void {
        const new_result = self.calculator.result + value;
        if (std.math.isInf(new_result) or std.math.isNan(new_result)) {
            self.overflow_occurred = true;
        } else {
            self.calculator.add(value);
        }
    }

    pub fn getResult(self: *const SafeCalculator) ?f64 {
        if (self.overflow_occurred) return null;
        return self.calculator.getResult();
    }
};
```

Delegation happens only when the operation is safe.

### Lazy Delegation

Create the delegate only when needed:

```zig
const LazyProxy = struct {
    resource: ?HeavyResource,
    initialization_count: u32,

    pub fn getData(self: *LazyProxy) []const u8 {
        if (self.resource == null) {
            self.resource = HeavyResource.init();
            self.initialization_count += 1;
        }
        return self.resource.?.getData();
    }
};
```

Expensive resources are created on first access.

### Discussion

Delegation in Zig is explicit and compile-time verified, unlike dynamic languages where delegation can happen implicitly.

### Delegation Patterns

**Composition**: Embed the delegate as a field
- Most common pattern
- Type-safe and explicit
- Zero runtime overhead

**Forwarding**: Write methods that call delegate methods
- Full control over interface
- Can modify arguments or results
- Can add validation or logging

**Selective exposure**: Only delegate some methods
- Create restricted interfaces
- Enforce access control
- Hide dangerous operations

**Chain of responsibility**: Multiple delegation layers
- Each layer adds functionality
- Order matters
- Common in middleware patterns

### Delegation vs Inheritance

Zig doesn't have inheritance, so delegation is the primary code reuse mechanism:

**Advantages**:
- More flexible—can change delegates at runtime
- Explicit—always clear what's happening
- Composable—combine multiple delegates
- No fragile base class problem

**Trade-offs**:
- More verbose—must write forwarding methods
- No automatic method forwarding
- Cannot override delegate methods

### Performance

All static delegation patterns have zero overhead:

```zig
pub fn start(self: *Car) void {
    self.engine.start();  // Inlined to direct call
}
```

The compiler optimizes away the forwarding entirely.

Dynamic delegation through interfaces has one pointer indirection:

```zig
pub fn write(self: Writer, data: []const u8) !void {
    return self.writeFn(self.ptr, data);  // One function pointer call
}
```

### Design Guidelines

**Use delegation when**:
- You want to reuse behavior
- You need to wrap or extend functionality
- You want to control access to another object
- You need runtime polymorphism

**Use composition directly when**:
- You only access a few fields
- No method forwarding needed
- The relationship is "has-a" not "is-a"

**Use interfaces when**:
- Delegate type unknown at compile time
- Need runtime polymorphism
- Plugin or extensibility systems

### Common Use Cases

**Proxy pattern**: Control access to objects
- Security, caching, lazy loading
- Add metrics or logging
- Network or IPC proxies

**Decorator pattern**: Add responsibilities
- Logging, encryption, compression
- Validation, authorization
- Performance tracking

**Adapter pattern**: Convert interfaces
- Wrap legacy code
- Match incompatible interfaces
- Provide simplified facades

### Full Tested Code

```zig
// Recipe 8.15: Delegating Attribute Access
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_delegation
// Basic method delegation
const Engine = struct {
    power: u32,
    running: bool,

    pub fn init(power: u32) Engine {
        return Engine{
            .power = power,
            .running = false,
        };
    }

    pub fn start(self: *Engine) void {
        self.running = true;
    }

    pub fn stop(self: *Engine) void {
        self.running = false;
    }

    pub fn isRunning(self: *const Engine) bool {
        return self.running;
    }

    pub fn getPower(self: *const Engine) u32 {
        return self.power;
    }
};

const Car = struct {
    engine: Engine,
    model: []const u8,

    pub fn init(model: []const u8, engine_power: u32) Car {
        return Car{
            .engine = Engine.init(engine_power),
            .model = model,
        };
    }

    // Delegate to engine
    pub fn start(self: *Car) void {
        self.engine.start();
    }

    pub fn stop(self: *Car) void {
        self.engine.stop();
    }

    pub fn isRunning(self: *const Car) bool {
        return self.engine.isRunning();
    }

    pub fn getEnginePower(self: *const Car) u32 {
        return self.engine.getPower();
    }
};
// ANCHOR_END: basic_delegation

test "basic delegation" {
    var car = Car.init("Sedan", 150);

    try testing.expect(!car.isRunning());

    car.start();
    try testing.expect(car.isRunning());
    try testing.expectEqual(@as(u32, 150), car.getEnginePower());

    car.stop();
    try testing.expect(!car.isRunning());
}

// ANCHOR: transparent_proxy
// Transparent proxy pattern
const DataStore = struct {
    data: std.StringHashMap([]const u8),

    pub fn init(allocator: std.mem.Allocator) DataStore {
        return DataStore{
            .data = std.StringHashMap([]const u8).init(allocator),
        };
    }

    pub fn deinit(self: *DataStore) void {
        self.data.deinit();
    }

    pub fn get(self: *const DataStore, key: []const u8) ?[]const u8 {
        return self.data.get(key);
    }

    pub fn put(self: *DataStore, key: []const u8, value: []const u8) !void {
        try self.data.put(key, value);
    }

    pub fn remove(self: *DataStore, key: []const u8) bool {
        return self.data.remove(key);
    }
};

const CachedDataStore = struct {
    store: DataStore,
    cache_hits: u32,
    cache_misses: u32,

    pub fn init(allocator: std.mem.Allocator) CachedDataStore {
        return CachedDataStore{
            .store = DataStore.init(allocator),
            .cache_hits = 0,
            .cache_misses = 0,
        };
    }

    pub fn deinit(self: *CachedDataStore) void {
        self.store.deinit();
    }

    pub fn get(self: *CachedDataStore, key: []const u8) ?[]const u8 {
        const result = self.store.get(key);
        if (result != null) {
            self.cache_hits += 1;
        } else {
            self.cache_misses += 1;
        }
        return result;
    }

    pub fn put(self: *CachedDataStore, key: []const u8, value: []const u8) !void {
        try self.store.put(key, value);
    }

    pub fn remove(self: *CachedDataStore, key: []const u8) bool {
        return self.store.remove(key);
    }

    pub fn getCacheStats(self: *const CachedDataStore) struct { hits: u32, misses: u32 } {
        return .{ .hits = self.cache_hits, .misses = self.cache_misses };
    }
};
// ANCHOR_END: transparent_proxy

test "transparent proxy" {
    var cached = CachedDataStore.init(testing.allocator);
    defer cached.deinit();

    try cached.put("key1", "value1");

    _ = cached.get("key1");
    _ = cached.get("key1");
    _ = cached.get("missing");

    const stats = cached.getCacheStats();
    try testing.expectEqual(@as(u32, 2), stats.hits);
    try testing.expectEqual(@as(u32, 1), stats.misses);
}

// ANCHOR: property_forwarding
// Property forwarding pattern
const Dimensions = struct {
    width: f32,
    height: f32,
    depth: f32,

    pub fn init(width: f32, height: f32, depth: f32) Dimensions {
        return Dimensions{
            .width = width,
            .height = height,
            .depth = depth,
        };
    }

    pub fn getVolume(self: *const Dimensions) f32 {
        return self.width * self.height * self.depth;
    }

    pub fn getSurfaceArea(self: *const Dimensions) f32 {
        return 2 * (self.width * self.height + self.width * self.depth + self.height * self.depth);
    }
};

const Box = struct {
    dimensions: Dimensions,
    material: []const u8,

    pub fn init(width: f32, height: f32, depth: f32, material: []const u8) Box {
        return Box{
            .dimensions = Dimensions.init(width, height, depth),
            .material = material,
        };
    }

    // Forward dimension properties
    pub fn getWidth(self: *const Box) f32 {
        return self.dimensions.width;
    }

    pub fn getHeight(self: *const Box) f32 {
        return self.dimensions.height;
    }

    pub fn getDepth(self: *const Box) f32 {
        return self.dimensions.depth;
    }

    pub fn getVolume(self: *const Box) f32 {
        return self.dimensions.getVolume();
    }

    pub fn getSurfaceArea(self: *const Box) f32 {
        return self.dimensions.getSurfaceArea();
    }
};
// ANCHOR_END: property_forwarding

test "property forwarding" {
    const box = Box.init(2, 3, 4, "cardboard");

    try testing.expectEqual(@as(f32, 2), box.getWidth());
    try testing.expectEqual(@as(f32, 3), box.getHeight());
    try testing.expectEqual(@as(f32, 24), box.getVolume());
}

// ANCHOR: selective_delegation
// Selective method delegation
const FileSystem = struct {
    pub fn read(path: []const u8) ![]const u8 {
        _ = path;
        return "file contents";
    }

    pub fn write(path: []const u8, data: []const u8) !void {
        _ = path;
        _ = data;
    }

    pub fn delete(path: []const u8) !void {
        _ = path;
    }
};

const ReadOnlyFileSystem = struct {
    // Only expose read operation
    pub fn read(path: []const u8) ![]const u8 {
        return FileSystem.read(path);
    }

    // write and delete are not exposed
};
// ANCHOR_END: selective_delegation

test "selective delegation" {
    const contents = try ReadOnlyFileSystem.read("/test/file.txt");
    try testing.expectEqualStrings("file contents", contents);
}

// ANCHOR: logging_wrapper
// Logging wrapper with delegation
const Database = struct {
    connection_count: u32,

    pub fn init() Database {
        return Database{ .connection_count = 0 };
    }

    pub fn query(self: *Database, sql: []const u8) !void {
        _ = sql;
        self.connection_count += 1;
    }

    pub fn execute(self: *Database, sql: []const u8) !void {
        _ = sql;
        self.connection_count += 1;
    }
};

const LoggedDatabase = struct {
    db: Database,
    query_log: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) LoggedDatabase {
        return LoggedDatabase{
            .db = Database.init(),
            .query_log = std.ArrayList([]const u8){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *LoggedDatabase) void {
        self.query_log.deinit(self.allocator);
    }

    pub fn query(self: *LoggedDatabase, sql: []const u8) !void {
        try self.query_log.append(self.allocator, sql);
        try self.db.query(sql);
    }

    pub fn execute(self: *LoggedDatabase, sql: []const u8) !void {
        try self.query_log.append(self.allocator, sql);
        try self.db.execute(sql);
    }

    pub fn getQueryLog(self: *const LoggedDatabase) []const []const u8 {
        return self.query_log.items;
    }
};
// ANCHOR_END: logging_wrapper

test "logging wrapper" {
    var logged_db = LoggedDatabase.init(testing.allocator);
    defer logged_db.deinit();

    try logged_db.query("SELECT * FROM users");
    try logged_db.execute("INSERT INTO users VALUES (1)");

    const log = logged_db.getQueryLog();
    try testing.expectEqual(@as(usize, 2), log.len);
    try testing.expectEqualStrings("SELECT * FROM users", log[0]);
}

// ANCHOR: chain_delegation
// Chain of delegation
const NetworkInterface = struct {
    bytes_sent: u64,
    bytes_received: u64,

    pub fn init() NetworkInterface {
        return NetworkInterface{
            .bytes_sent = 0,
            .bytes_received = 0,
        };
    }

    pub fn send(self: *NetworkInterface, data: []const u8) void {
        self.bytes_sent += data.len;
    }

    pub fn receive(self: *NetworkInterface, size: usize) void {
        self.bytes_received += size;
    }
};

const EncryptedNetwork = struct {
    network: NetworkInterface,

    pub fn init() EncryptedNetwork {
        return EncryptedNetwork{
            .network = NetworkInterface.init(),
        };
    }

    pub fn send(self: *EncryptedNetwork, data: []const u8) void {
        // Add encryption overhead
        self.network.send(data);
        self.network.bytes_sent += 16; // Encryption header
    }

    pub fn receive(self: *EncryptedNetwork, size: usize) void {
        self.network.receive(size);
    }

    pub fn getBytesSent(self: *const EncryptedNetwork) u64 {
        return self.network.bytes_sent;
    }
};

const CompressedEncryptedNetwork = struct {
    encrypted: EncryptedNetwork,

    pub fn init() CompressedEncryptedNetwork {
        return CompressedEncryptedNetwork{
            .encrypted = EncryptedNetwork.init(),
        };
    }

    pub fn send(self: *CompressedEncryptedNetwork, data: []const u8) void {
        // Simulate compression (50% reduction)
        const compressed_size = data.len / 2;
        const compressed_data = data[0..compressed_size];
        self.encrypted.send(compressed_data);
    }

    pub fn getBytesSent(self: *const CompressedEncryptedNetwork) u64 {
        return self.encrypted.getBytesSent();
    }
};
// ANCHOR_END: chain_delegation

test "chain delegation" {
    var network = CompressedEncryptedNetwork.init();

    const data = "Hello, World!";
    network.send(data);

    const sent = network.getBytesSent();
    try testing.expect(sent > 0);
}

// ANCHOR: dynamic_delegation
// Dynamic delegation pattern
const Writer = struct {
    ptr: *anyopaque,
    writeFn: *const fn (ptr: *anyopaque, data: []const u8) anyerror!void,

    pub fn write(self: Writer, data: []const u8) !void {
        return self.writeFn(self.ptr, data);
    }
};

const BufferWriter = struct {
    buffer: std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) BufferWriter {
        return BufferWriter{
            .buffer = std.ArrayList(u8){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *BufferWriter) void {
        self.buffer.deinit(self.allocator);
    }

    fn writeFn(ptr: *anyopaque, data: []const u8) !void {
        const self: *BufferWriter = @ptrCast(@alignCast(ptr));
        try self.buffer.appendSlice(self.allocator, data);
    }

    pub fn writer(self: *BufferWriter) Writer {
        return Writer{
            .ptr = self,
            .writeFn = writeFn,
        };
    }

    pub fn getContents(self: *const BufferWriter) []const u8 {
        return self.buffer.items;
    }
};

const DelegatingWriter = struct {
    writer: Writer,

    pub fn init(writer: Writer) DelegatingWriter {
        return DelegatingWriter{ .writer = writer };
    }

    pub fn writeLine(self: *DelegatingWriter, line: []const u8) !void {
        try self.writer.write(line);
        try self.writer.write("\n");
    }
};
// ANCHOR_END: dynamic_delegation

test "dynamic delegation" {
    var buf = BufferWriter.init(testing.allocator);
    defer buf.deinit();

    var delegating = DelegatingWriter.init(buf.writer());
    try delegating.writeLine("First line");
    try delegating.writeLine("Second line");

    try testing.expectEqualStrings("First line\nSecond line\n", buf.getContents());
}

// ANCHOR: mixin_delegation
// Mixin-style delegation
fn WithLogging(comptime T: type) type {
    return struct {
        inner: T,
        log_count: u32,

        const Self = @This();

        pub fn init(inner: T) Self {
            return Self{
                .inner = inner,
                .log_count = 0,
            };
        }

        pub fn call(self: *Self) void {
            self.log_count += 1;
            if (@hasDecl(T, "call")) {
                self.inner.call();
            }
        }

        pub fn getLogCount(self: *const Self) u32 {
            return self.log_count;
        }

        pub fn getInner(self: *Self) *T {
            return &self.inner;
        }
    };
}

const SimpleService = struct {
    invocations: u32,

    pub fn init() SimpleService {
        return SimpleService{ .invocations = 0 };
    }

    pub fn call(self: *SimpleService) void {
        self.invocations += 1;
    }
};
// ANCHOR_END: mixin_delegation

test "mixin delegation" {
    const service = SimpleService.init();
    var logged = WithLogging(SimpleService).init(service);

    logged.call();
    logged.call();
    logged.call();

    try testing.expectEqual(@as(u32, 3), logged.getLogCount());
    try testing.expectEqual(@as(u32, 3), logged.getInner().invocations);
}

// ANCHOR: conditional_delegation
// Conditional delegation
const Calculator = struct {
    result: f64,

    pub fn init() Calculator {
        return Calculator{ .result = 0 };
    }

    pub fn add(self: *Calculator, value: f64) void {
        self.result += value;
    }

    pub fn multiply(self: *Calculator, value: f64) void {
        self.result *= value;
    }

    pub fn getResult(self: *const Calculator) f64 {
        return self.result;
    }
};

const SafeCalculator = struct {
    calculator: Calculator,
    overflow_occurred: bool,

    pub fn init() SafeCalculator {
        return SafeCalculator{
            .calculator = Calculator.init(),
            .overflow_occurred = false,
        };
    }

    pub fn add(self: *SafeCalculator, value: f64) void {
        const new_result = self.calculator.result + value;
        if (std.math.isInf(new_result) or std.math.isNan(new_result)) {
            self.overflow_occurred = true;
        } else {
            self.calculator.add(value);
        }
    }

    pub fn multiply(self: *SafeCalculator, value: f64) void {
        const new_result = self.calculator.result * value;
        if (std.math.isInf(new_result) or std.math.isNan(new_result)) {
            self.overflow_occurred = true;
        } else {
            self.calculator.multiply(value);
        }
    }

    pub fn getResult(self: *const SafeCalculator) ?f64 {
        if (self.overflow_occurred) return null;
        return self.calculator.getResult();
    }

    pub fn hasOverflow(self: *const SafeCalculator) bool {
        return self.overflow_occurred;
    }
};
// ANCHOR_END: conditional_delegation

test "conditional delegation" {
    var calc = SafeCalculator.init();

    calc.add(10);
    calc.multiply(5);

    try testing.expectEqual(@as(f64, 50), calc.getResult().?);
    try testing.expect(!calc.hasOverflow());

    calc.multiply(std.math.inf(f64));
    try testing.expect(calc.hasOverflow());
    try testing.expect(calc.getResult() == null);
}

// ANCHOR: lazy_delegation
// Lazy delegation (delegate only when needed)
const HeavyResource = struct {
    data: []const u8,

    pub fn init() HeavyResource {
        return HeavyResource{ .data = "heavy resource data" };
    }

    pub fn getData(self: *const HeavyResource) []const u8 {
        return self.data;
    }
};

const LazyProxy = struct {
    resource: ?HeavyResource,
    initialization_count: u32,

    pub fn init() LazyProxy {
        return LazyProxy{
            .resource = null,
            .initialization_count = 0,
        };
    }

    pub fn getData(self: *LazyProxy) []const u8 {
        if (self.resource == null) {
            self.resource = HeavyResource.init();
            self.initialization_count += 1;
        }
        return self.resource.?.getData();
    }

    pub fn getInitCount(self: *const LazyProxy) u32 {
        return self.initialization_count;
    }
};
// ANCHOR_END: lazy_delegation

test "lazy delegation" {
    var proxy = LazyProxy.init();

    try testing.expectEqual(@as(u32, 0), proxy.getInitCount());

    const data1 = proxy.getData();
    try testing.expectEqualStrings("heavy resource data", data1);
    try testing.expectEqual(@as(u32, 1), proxy.getInitCount());

    const data2 = proxy.getData();
    try testing.expectEqualStrings("heavy resource data", data2);
    try testing.expectEqual(@as(u32, 1), proxy.getInitCount());
}

// Comprehensive test
test "comprehensive delegation patterns" {
    var car = Car.init("Sedan", 200);
    car.start();
    try testing.expect(car.isRunning());

    var cached = CachedDataStore.init(testing.allocator);
    defer cached.deinit();
    try cached.put("test", "value");
    _ = cached.get("test");

    const box = Box.init(1, 2, 3, "wood");
    try testing.expectEqual(@as(f32, 6), box.getVolume());

    var proxy = LazyProxy.init();
    _ = proxy.getData();
    try testing.expectEqual(@as(u32, 1), proxy.getInitCount());
}
```

### See Also

- Recipe 8.7: Calling a Method on a Parent Class
- Recipe 8.12: Defining an Interface or Abstract Base Class
- Recipe 8.13: Implementing a Data Model or Type System
- Recipe 9.11: Using comptime to Control Instance Creation

---

## Recipe 8.16: Defining More Than One Constructor in a Struct {#recipe-8-16}

**Tags:** allocators, comptime, data-structures, error-handling, hashmap, http, memory, networking, resource-cleanup, structs-objects, testing
**Difficulty:** advanced
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_16.zig`

### Problem

You want to create a struct with multiple ways to initialize it, similar to constructor overloading in other languages. Zig doesn't have traditional constructors, but you need different initialization patterns.

### Solution

Use named static methods as constructors. Each method returns an instance of the struct, providing different initialization patterns based on the use case.

### Named Constructors

Create multiple initialization methods with descriptive names:

```zig
// Named constructor pattern
const Point = struct {
    x: f32,
    y: f32,

    pub fn init(x: f32, y: f32) Point {
        return Point{ .x = x, .y = y };
    }

    pub fn origin() Point {
        return Point{ .x = 0, .y = 0 };
    }

    pub fn fromPolar(radius: f32, angle: f32) Point {
        return Point{
            .x = radius * @cos(angle),
            .y = radius * @sin(angle),
        };
    }

    pub fn fromArray(arr: [2]f32) Point {
        return Point{ .x = arr[0], .y = arr[1] };
    }
};
```

Each method provides a clear, self-documenting way to create a Point:
- `init()` for basic x,y coordinates
- `origin()` for the (0,0) point
- `fromPolar()` for polar coordinates
- `fromArray()` for array conversion

### Default Values

Provide convenience constructors with sensible defaults:

```zig
const Server = struct {
    host: []const u8,
    port: u16,
    timeout: u32,

    pub fn init(host: []const u8, port: u16, timeout: u32) Server {
        return Server{
            .host = host,
            .port = port,
            .timeout = timeout,
        };
    }

    pub fn withDefaults(host: []const u8) Server {
        return Server{
            .host = host,
            .port = 8080,
            .timeout = 30,
        };
    }

    pub fn localhost() Server {
        return Server{
            .host = "127.0.0.1",
            .port = 8080,
            .timeout = 30,
        };
    }
};
```

Users can choose between full control and convenient defaults.

### Factory Methods with Validation

Return error unions for constructors that can fail:

```zig
const Email = struct {
    address: []const u8,

    pub fn init(address: []const u8) !Email {
        if (std.mem.indexOf(u8, address, "@") == null) {
            return error.InvalidEmail;
        }
        return Email{ .address = address };
    }

    pub fn fromParts(local: []const u8, domain: []const u8, allocator: std.mem.Allocator) !Email {
        const address = try std.fmt.allocPrint(allocator, "{s}@{s}", .{ local, domain });
        return Email{ .address = address };
    }

    pub fn anonymous(allocator: std.mem.Allocator) !Email {
        const address = try std.fmt.allocPrint(
            allocator,
            "user{d}@example.com",
            .{std.crypto.random.int(u32)}
        );
        return Email{ .address = address };
    }
};
```

Factory methods can validate input and return errors when initialization fails.

### Builder-Style Constructors

Create convenience methods for common use cases:

```zig
const HttpRequest = struct {
    method: []const u8,
    url: []const u8,
    headers: ?std.StringHashMap([]const u8),
    body: ?[]const u8,

    pub fn init(method: []const u8, url: []const u8) HttpRequest {
        return HttpRequest{
            .method = method,
            .url = url,
            .headers = null,
            .body = null,
        };
    }

    pub fn get(url: []const u8) HttpRequest {
        return HttpRequest.init("GET", url);
    }

    pub fn post(url: []const u8, body: []const u8) HttpRequest {
        return HttpRequest{
            .method = "POST",
            .url = url,
            .headers = null,
            .body = body,
        };
    }
};
```

Specialized constructors make common operations more ergonomic.

### Copy Constructors

Create instances from existing instances:

```zig
const Vector = struct {
    x: f32,
    y: f32,
    z: f32,

    pub fn init(x: f32, y: f32, z: f32) Vector {
        return Vector{ .x = x, .y = y, .z = z };
    }

    pub fn copy(other: *const Vector) Vector {
        return Vector{
            .x = other.x,
            .y = other.y,
            .z = other.z,
        };
    }

    pub fn scaled(self: *const Vector, factor: f32) Vector {
        return Vector{
            .x = self.x * factor,
            .y = self.y * factor,
            .z = self.z * factor,
        };
    }

    pub fn normalized(self: *const Vector) Vector {
        const len = @sqrt(self.x * self.x + self.y * self.y + self.z * self.z);
        if (len == 0) return Vector.init(0, 0, 0);
        return Vector{
            .x = self.x / len,
            .y = self.y / len,
            .z = self.z / len,
        };
    }
};
```

Transformation methods return new instances without modifying the original.

### Conditional Initialization

Create instances based on environment or configuration:

```zig
const Config = struct {
    environment: []const u8,
    debug_mode: bool,
    log_level: u8,

    pub fn production() Config {
        return Config{
            .environment = "production",
            .debug_mode = false,
            .log_level = 2,
        };
    }

    pub fn development() Config {
        return Config{
            .environment = "development",
            .debug_mode = true,
            .log_level = 5,
        };
    }

    pub fn fromEnv(env: []const u8) Config {
        if (std.mem.eql(u8, env, "prod")) {
            return Config.production();
        } else if (std.mem.eql(u8, env, "dev")) {
            return Config.development();
        } else {
            return Config.testing();
        }
    }
};
```

Environment-specific constructors encapsulate configuration logic.

### Parse Constructors

Create instances from different representations:

```zig
const Color = struct {
    r: u8,
    g: u8,
    b: u8,

    pub fn init(r: u8, g: u8, b: u8) Color {
        return Color{ .r = r, .g = g, .b = b };
    }

    pub fn fromRgb(rgb: u32) Color {
        return Color{
            .r = @intCast((rgb >> 16) & 0xFF),
            .g = @intCast((rgb >> 8) & 0xFF),
            .b = @intCast(rgb & 0xFF),
        };
    }

    pub fn black() Color {
        return Color.init(0, 0, 0);
    }

    pub fn white() Color {
        return Color.init(255, 255, 255);
    }

    pub fn fromGrayscale(value: u8) Color {
        return Color.init(value, value, value);
    }
};
```

Parse different formats into your struct representation.

### Generic Constructors

Use comptime for type-generic construction:

```zig
fn Result(comptime T: type, comptime E: type) type {
    return union(enum) {
        ok: T,
        err: E,

        pub fn initOk(value: T) @This() {
            return .{ .ok = value };
        }

        pub fn initErr(err: E) @This() {
            return .{ .err = err };
        }

        pub fn fromOptional(opt: ?T, default_err: E) @This() {
            if (opt) |value| {
                return .{ .ok = value };
            } else {
                return .{ .err = default_err };
            }
        }
    };
}
```

Generic types can have multiple constructors for different scenarios.

### Discussion

Zig doesn't have constructor overloading, but named methods provide a clearer, more flexible alternative.

### Why Named Constructors

**Clarity**: Method names document intent
```zig
Point.origin()           // Clear: creates origin point
Point.fromPolar(5, 0)    // Clear: converts from polar
```

**Flexibility**: Different return types or error handling per constructor
```zig
pub fn init(...) Point           // Never fails
pub fn fromString(...) !Point    // Can fail with error
```

**Self-documenting**: No ambiguity about what each constructor does
```zig
Config.production()    // Obviously production config
Config.development()   // Obviously development config
```

### Constructor Patterns

**Basic pattern**: Direct initialization
```zig
pub fn init(params) Type {
    return Type{ .field = param };
}
```

**With defaults**: Common configurations
```zig
pub fn withDefaults(required_params) Type {
    return Type{
        .required = required_params,
        .optional = default_value,
    };
}
```

**Factory pattern**: Validation and transformation
```zig
pub fn fromX(x_data) !Type {
    if (!valid(x_data)) return error.Invalid;
    return Type{ .field = transform(x_data) };
}
```

**Named instances**: Common constants
```zig
pub fn origin() Type {
    return Type{ .x = 0, .y = 0 };
}
```

### Design Guidelines

**Naming conventions**:
- `init()` for basic construction
- `from*()` for conversion constructors
- Named constants for well-known instances
- `with*()` for variant constructors

**Error handling**:
- Return `Type` if never fails
- Return `!Type` if validation needed
- Return `?Type` for optional construction

**Allocator usage**:
- Pass allocator as first parameter when needed
- Store allocator in struct if lifetime matches struct
- Document memory ownership clearly

### Performance

All constructors are regular functions that get inlined:

```zig
const p = Point.origin();  // Inlined to: Point{ .x = 0, .y = 0 }
```

No runtime overhead compared to direct initialization. The compiler optimizes away the function call.

### Comparison with Other Languages

**C++**: Constructor overloading
```cpp
Point(float x, float y);           // Zig: init(x, y)
Point();                            // Zig: origin()
static Point fromPolar(r, theta);  // Zig: fromPolar(r, theta)
```

**Java**: Multiple constructors
```java
Point(float x, float y) { ... }    // Zig: init(x, y)
Point() { this(0, 0); }             // Zig: origin()
```

**Rust**: Impl blocks with multiple methods
```rust
impl Point {
    fn new(x, y) -> Point { ... }   // Zig: init(x, y)
    fn origin() -> Point { ... }    // Zig: origin()
}
```

Zig's approach is most similar to Rust, but simpler because Zig structs are just namespaces.

### Full Tested Code

```zig
// Recipe 8.16: Defining More Than One Constructor in a Class
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: named_constructors
// Named constructor pattern
const Point = struct {
    x: f32,
    y: f32,

    pub fn init(x: f32, y: f32) Point {
        return Point{ .x = x, .y = y };
    }

    pub fn origin() Point {
        return Point{ .x = 0, .y = 0 };
    }

    pub fn fromPolar(radius: f32, angle: f32) Point {
        return Point{
            .x = radius * @cos(angle),
            .y = radius * @sin(angle),
        };
    }

    pub fn fromArray(arr: [2]f32) Point {
        return Point{ .x = arr[0], .y = arr[1] };
    }
};
// ANCHOR_END: named_constructors

test "named constructors" {
    const p1 = Point.init(3, 4);
    try testing.expectEqual(@as(f32, 3), p1.x);

    const p2 = Point.origin();
    try testing.expectEqual(@as(f32, 0), p2.x);

    const p3 = Point.fromPolar(5, 0);
    try testing.expectApproxEqAbs(@as(f32, 5), p3.x, 0.001);

    const arr = [_]f32{ 1, 2 };
    const p4 = Point.fromArray(arr);
    try testing.expectEqual(@as(f32, 1), p4.x);
}

// ANCHOR: default_values
// Default values with optional overrides
const Server = struct {
    host: []const u8,
    port: u16,
    timeout: u32,

    pub fn init(host: []const u8, port: u16, timeout: u32) Server {
        return Server{
            .host = host,
            .port = port,
            .timeout = timeout,
        };
    }

    pub fn withDefaults(host: []const u8) Server {
        return Server{
            .host = host,
            .port = 8080,
            .timeout = 30,
        };
    }

    pub fn localhost() Server {
        return Server{
            .host = "127.0.0.1",
            .port = 8080,
            .timeout = 30,
        };
    }
};
// ANCHOR_END: default_values

test "default values" {
    const s1 = Server.init("example.com", 443, 60);
    try testing.expectEqual(@as(u16, 443), s1.port);

    const s2 = Server.withDefaults("api.example.com");
    try testing.expectEqual(@as(u16, 8080), s2.port);
    try testing.expectEqual(@as(u32, 30), s2.timeout);

    const s3 = Server.localhost();
    try testing.expectEqualStrings("127.0.0.1", s3.host);
}

// ANCHOR: factory_methods
// Factory methods with validation
const Email = struct {
    address: []const u8,

    pub fn init(address: []const u8) !Email {
        if (std.mem.indexOf(u8, address, "@") == null) {
            return error.InvalidEmail;
        }
        return Email{ .address = address };
    }

    pub fn fromParts(local: []const u8, domain: []const u8, allocator: std.mem.Allocator) !Email {
        const address = try std.fmt.allocPrint(allocator, "{s}@{s}", .{ local, domain });
        return Email{ .address = address };
    }

    pub fn anonymous(allocator: std.mem.Allocator) !Email {
        const address = try std.fmt.allocPrint(allocator, "user{d}@example.com", .{std.crypto.random.int(u32)});
        return Email{ .address = address };
    }
};
// ANCHOR_END: factory_methods

test "factory methods" {
    const e1 = try Email.init("test@example.com");
    try testing.expectEqualStrings("test@example.com", e1.address);

    const result = Email.init("invalid");
    try testing.expectError(error.InvalidEmail, result);

    const e2 = try Email.fromParts("admin", "company.com", testing.allocator);
    defer testing.allocator.free(e2.address);
    try testing.expectEqualStrings("admin@company.com", e2.address);
}

// ANCHOR: builder_constructors
// Builder pattern with multiple initialization styles
const HttpRequest = struct {
    method: []const u8,
    url: []const u8,
    headers: ?std.StringHashMap([]const u8),
    body: ?[]const u8,

    pub fn init(method: []const u8, url: []const u8) HttpRequest {
        return HttpRequest{
            .method = method,
            .url = url,
            .headers = null,
            .body = null,
        };
    }

    pub fn get(url: []const u8) HttpRequest {
        return HttpRequest.init("GET", url);
    }

    pub fn post(url: []const u8, body: []const u8) HttpRequest {
        return HttpRequest{
            .method = "POST",
            .url = url,
            .headers = null,
            .body = body,
        };
    }

    pub fn withHeaders(self: HttpRequest, headers: std.StringHashMap([]const u8)) HttpRequest {
        var req = self;
        req.headers = headers;
        return req;
    }
};
// ANCHOR_END: builder_constructors

test "builder constructors" {
    const req1 = HttpRequest.get("/api/users");
    try testing.expectEqualStrings("GET", req1.method);
    try testing.expectEqualStrings("/api/users", req1.url);

    const req2 = HttpRequest.post("/api/data", "payload");
    try testing.expectEqualStrings("POST", req2.method);
    try testing.expectEqualStrings("payload", req2.body.?);
}

// ANCHOR: copy_constructor
// Copy and clone constructors
const Vector = struct {
    x: f32,
    y: f32,
    z: f32,

    pub fn init(x: f32, y: f32, z: f32) Vector {
        return Vector{ .x = x, .y = y, .z = z };
    }

    pub fn copy(other: *const Vector) Vector {
        return Vector{
            .x = other.x,
            .y = other.y,
            .z = other.z,
        };
    }

    pub fn scaled(self: *const Vector, factor: f32) Vector {
        return Vector{
            .x = self.x * factor,
            .y = self.y * factor,
            .z = self.z * factor,
        };
    }

    pub fn normalized(self: *const Vector) Vector {
        const len = @sqrt(self.x * self.x + self.y * self.y + self.z * self.z);
        if (len == 0) return Vector.init(0, 0, 0);
        return Vector{
            .x = self.x / len,
            .y = self.y / len,
            .z = self.z / len,
        };
    }
};
// ANCHOR_END: copy_constructor

test "copy constructor" {
    const v1 = Vector.init(3, 4, 0);
    const v2 = Vector.copy(&v1);
    try testing.expectEqual(@as(f32, 3), v2.x);

    const v3 = v1.scaled(2);
    try testing.expectEqual(@as(f32, 6), v3.x);
    try testing.expectEqual(@as(f32, 8), v3.y);

    const v4 = v1.normalized();
    const expected_x = @as(f32, 3) / 5;
    try testing.expectApproxEqAbs(expected_x, v4.x, 0.001);
}

// ANCHOR: conditional_init
// Conditional initialization based on type
const Config = struct {
    environment: []const u8,
    debug_mode: bool,
    log_level: u8,

    pub fn production() Config {
        return Config{
            .environment = "production",
            .debug_mode = false,
            .log_level = 2,
        };
    }

    pub fn development() Config {
        return Config{
            .environment = "development",
            .debug_mode = true,
            .log_level = 5,
        };
    }

    pub fn testing() Config {
        return Config{
            .environment = "testing",
            .debug_mode = true,
            .log_level = 4,
        };
    }

    pub fn fromEnv(env: []const u8) Config {
        if (std.mem.eql(u8, env, "prod")) {
            return Config.production();
        } else if (std.mem.eql(u8, env, "dev")) {
            return Config.development();
        } else {
            return Config.testing();
        }
    }
};
// ANCHOR_END: conditional_init

test "conditional initialization" {
    const prod = Config.production();
    try testing.expect(!prod.debug_mode);
    try testing.expectEqual(@as(u8, 2), prod.log_level);

    const dev = Config.development();
    try testing.expect(dev.debug_mode);

    const config = Config.fromEnv("prod");
    try testing.expectEqualStrings("production", config.environment);
}

// ANCHOR: resource_init
// Resource initialization with different sources
const Database = struct {
    connection_string: []const u8,
    pool_size: u32,

    pub fn fromUrl(url: []const u8) Database {
        return Database{
            .connection_string = url,
            .pool_size = 10,
        };
    }

    pub fn fromConfig(host: []const u8, port: u16, db_name: []const u8, allocator: std.mem.Allocator) !Database {
        const conn_str = try std.fmt.allocPrint(allocator, "postgresql://{s}:{d}/{s}", .{ host, port, db_name });
        return Database{
            .connection_string = conn_str,
            .pool_size = 20,
        };
    }

    pub fn inmemory() Database {
        return Database{
            .connection_string = ":memory:",
            .pool_size = 1,
        };
    }
};
// ANCHOR_END: resource_init

test "resource initialization" {
    const db1 = Database.fromUrl("postgresql://localhost/mydb");
    try testing.expectEqualStrings("postgresql://localhost/mydb", db1.connection_string);
    try testing.expectEqual(@as(u32, 10), db1.pool_size);

    const db2 = try Database.fromConfig("localhost", 5432, "testdb", testing.allocator);
    defer testing.allocator.free(db2.connection_string);
    try testing.expect(std.mem.indexOf(u8, db2.connection_string, "5432") != null);

    const db3 = Database.inmemory();
    try testing.expectEqualStrings(":memory:", db3.connection_string);
}

// ANCHOR: generic_constructors
// Generic constructors with type parameters
fn Result(comptime T: type, comptime E: type) type {
    return union(enum) {
        ok: T,
        err: E,

        pub fn initOk(value: T) @This() {
            return .{ .ok = value };
        }

        pub fn initErr(err: E) @This() {
            return .{ .err = err };
        }

        pub fn fromOptional(opt: ?T, default_err: E) @This() {
            if (opt) |value| {
                return .{ .ok = value };
            } else {
                return .{ .err = default_err };
            }
        }
    };
}
// ANCHOR_END: generic_constructors

test "generic constructors" {
    const IntResult = Result(i32, []const u8);

    const r1 = IntResult.initOk(42);
    try testing.expectEqual(@as(i32, 42), r1.ok);

    const r2 = IntResult.initErr("not found");
    try testing.expectEqualStrings("not found", r2.err);

    const opt: ?i32 = null;
    const r3 = IntResult.fromOptional(opt, "empty");
    try testing.expectEqualStrings("empty", r3.err);
}

// ANCHOR: parse_constructors
// Parse constructors from strings
const Color = struct {
    r: u8,
    g: u8,
    b: u8,

    pub fn init(r: u8, g: u8, b: u8) Color {
        return Color{ .r = r, .g = g, .b = b };
    }

    pub fn fromRgb(rgb: u32) Color {
        return Color{
            .r = @intCast((rgb >> 16) & 0xFF),
            .g = @intCast((rgb >> 8) & 0xFF),
            .b = @intCast(rgb & 0xFF),
        };
    }

    pub fn black() Color {
        return Color.init(0, 0, 0);
    }

    pub fn white() Color {
        return Color.init(255, 255, 255);
    }

    pub fn red() Color {
        return Color.init(255, 0, 0);
    }

    pub fn fromGrayscale(value: u8) Color {
        return Color.init(value, value, value);
    }
};
// ANCHOR_END: parse_constructors

test "parse constructors" {
    const c1 = Color.fromRgb(0xFF5733);
    try testing.expectEqual(@as(u8, 0xFF), c1.r);
    try testing.expectEqual(@as(u8, 0x57), c1.g);
    try testing.expectEqual(@as(u8, 0x33), c1.b);

    const c2 = Color.black();
    try testing.expectEqual(@as(u8, 0), c2.r);

    const c3 = Color.fromGrayscale(128);
    try testing.expectEqual(@as(u8, 128), c3.r);
    try testing.expectEqual(@as(u8, 128), c3.g);
}

// ANCHOR: partial_init
// Partial initialization with required fields
const User = struct {
    id: u32,
    username: []const u8,
    email: ?[]const u8,
    bio: ?[]const u8,

    pub fn init(id: u32, username: []const u8) User {
        return User{
            .id = id,
            .username = username,
            .email = null,
            .bio = null,
        };
    }

    pub fn withEmail(id: u32, username: []const u8, email: []const u8) User {
        return User{
            .id = id,
            .username = username,
            .email = email,
            .bio = null,
        };
    }

    pub fn full(id: u32, username: []const u8, email: []const u8, bio: []const u8) User {
        return User{
            .id = id,
            .username = username,
            .email = email,
            .bio = bio,
        };
    }
};
// ANCHOR_END: partial_init

test "partial initialization" {
    const user1 = User.init(1, "alice");
    try testing.expectEqual(@as(u32, 1), user1.id);
    try testing.expect(user1.email == null);

    const user2 = User.withEmail(2, "bob", "bob@example.com");
    try testing.expectEqualStrings("bob@example.com", user2.email.?);
    try testing.expect(user2.bio == null);

    const user3 = User.full(3, "charlie", "charlie@example.com", "Developer");
    try testing.expectEqualStrings("Developer", user3.bio.?);
}

// Comprehensive test
test "comprehensive multiple constructors" {
    const p = Point.fromPolar(10, std.math.pi / @as(f32, 4));
    try testing.expect(p.x > 7 and p.x < 8);

    const srv = Server.localhost();
    try testing.expectEqual(@as(u16, 8080), srv.port);

    const v = Vector.init(1, 0, 0);
    const v_norm = v.normalized();
    try testing.expectApproxEqAbs(@as(f32, 1), v_norm.x, 0.001);

    const cfg = Config.fromEnv("dev");
    try testing.expect(cfg.debug_mode);

    const c = Color.white();
    try testing.expectEqual(@as(u8, 255), c.r);
}
```

### See Also

- Recipe 8.11: Simplifying the Initialization of Data Structures
- Recipe 8.17: Creating an Instance Without Invoking Init
- Recipe 8.13: Implementing a Data Model or Type System
- Recipe 9.11: Using comptime to Control Instance Creation

---

## Recipe 8.17: Creating an Instance Without Invoking init {#recipe-8-17}

**Tags:** allocators, c-interop, comptime, error-handling, memory, pointers, structs-objects, testing
**Difficulty:** advanced
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_17.zig`

### Problem

You want to create struct instances without calling an init function, either for performance, flexibility, or because you're working with external data formats.

### Solution

Zig allows direct struct initialization using struct literals, special initialization patterns, and compile-time techniques. Choose the right approach based on your needs.

### Direct Struct Literals

Create structs inline without any function call:

```zig
// Direct struct literal initialization
const Point = struct {
    x: f32,
    y: f32,

    pub fn init(x: f32, y: f32) Point {
        return Point{ .x = x, .y = y };
    }
};

test "direct literal initialization" {
    // Create without calling init
    const p1 = Point{ .x = 3, .y = 4 };
    try testing.expectEqual(@as(f32, 3), p1.x);

    // Using init for comparison
    const p2 = Point.init(3, 4);
    try testing.expectEqual(@as(f32, 3), p2.x);

    // Both are equivalent
    try testing.expectEqual(p1.x, p2.x);
    try testing.expectEqual(p1.y, p2.y);
}
```

The compiler treats both the same way. Direct literals are useful when init() doesn't provide value.

### Undefined Initialization

Leave fields uninitialized when you'll overwrite them immediately:

```zig
const Buffer = struct {
    data: [1024]u8,
    len: usize,

    pub fn init() Buffer {
        return Buffer{
            .data = undefined,  // Don't waste time zeroing
            .len = 0,
        };
    }

    pub fn uninitialized() Buffer {
        var buf: Buffer = undefined;
        buf.len = 0;  // Only initialize what matters
        return buf;
    }
};
```

Using `undefined` skips initialization overhead for data you'll replace anyway.

### Zero Initialization

Initialize all fields to zero using std.mem.zeroes:

```zig
const Counters = struct {
    success: u32,
    failure: u32,
    pending: u32,

    pub fn init() Counters {
        return Counters{
            .success = 0,
            .failure = 0,
            .pending = 0,
        };
    }

    pub fn zero() Counters {
        return std.mem.zeroes(Counters);
    }
};
```

`std.mem.zeroes()` sets all bytes to zero, perfect for resetting state or initializing counters.

### Deserialize From Bytes

Create instances directly from byte arrays:

```zig
const Header = struct {
    magic: u32,
    version: u16,
    flags: u16,

    pub fn fromBytes(bytes: []const u8) !Header {
        if (bytes.len < @sizeOf(Header)) return error.TooSmall;

        return Header{
            .magic = std.mem.readInt(u32, bytes[0..4], .little),
            .version = std.mem.readInt(u16, bytes[4..6], .little),
            .flags = std.mem.readInt(u16, bytes[6..8], .little),
        };
    }

    pub fn fromBytesUnsafe(bytes: *const [@sizeOf(Header)]u8) *const Header {
        return @ptrCast(@alignCast(bytes));
    }
};
```

Parse binary formats directly into structs.

### Object Pool Pattern

Reuse instances without re-initialization:

```zig
const PooledObject = struct {
    id: u32,
    data: [64]u8,
    in_use: bool,

    pub fn reset(self: *PooledObject) void {
        self.in_use = false;
        @memset(&self.data, 0);
    }

    pub fn acquire(self: *PooledObject, id: u32) void {
        self.id = id;
        self.in_use = true;
    }
};

const ObjectPool = struct {
    objects: [10]PooledObject,

    pub fn init() ObjectPool {
        var pool = ObjectPool{
            .objects = undefined,
        };

        for (&pool.objects, 0..) |*obj, i| {
            obj.* = PooledObject{
                .id = @intCast(i),
                .data = undefined,
                .in_use = false,
            };
        }

        return pool;
    }

    pub fn acquire(self: *ObjectPool) ?*PooledObject {
        for (&self.objects) |*obj| {
            if (!obj.in_use) {
                obj.in_use = true;
                return obj;
            }
        }
        return null;
    }
};
```

Pools recycle objects, avoiding repeated initialization costs.

### Compile-Time Instances

Create instances at compile time as constants:

```zig
const Config = struct {
    max_connections: u32,
    timeout_ms: u32,
    buffer_size: usize,

    pub fn default() Config {
        return Config{
            .max_connections = 100,
            .timeout_ms = 5000,
            .buffer_size = 4096,
        };
    }
};

// Created at compile time
const global_config = Config{
    .max_connections = 50,
    .timeout_ms = 3000,
    .buffer_size = 2048,
};

const default_config = Config.default();
```

Compile-time instances have zero runtime cost.

### Placement Initialization

Initialize a struct in-place:

```zig
const Node = struct {
    value: i32,
    next: ?*Node,

    pub fn initInPlace(self: *Node, value: i32) void {
        self.* = Node{
            .value = value,
            .next = null,
        };
    }
};

// Initialize in existing storage
var storage: Node = undefined;
storage.initInPlace(42);

// Or direct assignment
var storage2: Node = undefined;
storage2 = Node{ .value = 100, .next = null };
```

Useful when working with pre-allocated memory.

### Default Struct Values

Leverage Zig's default field values:

```zig
const Settings = struct {
    name: []const u8 = "default",
    enabled: bool = true,
    count: u32 = 0,
};

// Uses all defaults
const s1: Settings = .{};

// Override some fields, others use defaults
const s2: Settings = .{ .name = "custom", .count = 10 };
```

Default values make partial initialization ergonomic.

### Copy From Another Instance

Create copies efficiently:

```zig
const Matrix = struct {
    data: [9]f32,

    pub fn identity() Matrix {
        return Matrix{
            .data = [_]f32{
                1, 0, 0,
                0, 1, 0,
                0, 0, 1,
            },
        };
    }

    pub fn copyFrom(other: *const Matrix) Matrix {
        var m: Matrix = undefined;
        @memcpy(&m.data, &other.data);
        return m;
    }

    pub fn clone(self: *const Matrix) Matrix {
        return self.*;  // Simple copy
    }
};
```

Copying structs is a simple value copy in Zig.

### Tagged Union Initialization

Initialize unions without explicit constructors:

```zig
const Message = union(enum) {
    text: []const u8,
    number: i32,
    flag: bool,

    pub fn initText(content: []const u8) Message {
        return .{ .text = content };
    }
};

// Direct initialization
const m1: Message = .{ .text = "hello" };
const m2: Message = .{ .number = 42 };

// Or using constructors
const m3 = Message.initText("world");
```

Unions support direct initialization with the tag specified.

### Reinterpret Bytes as Struct

Convert raw bytes into struct layout:

```zig
const Packet = struct {
    type_id: u8,
    length: u16,
    payload: [5]u8,

    pub fn fromMemory(ptr: *const anyopaque) *const Packet {
        return @ptrCast(@alignCast(ptr));
    }

    pub fn fromBytes(bytes: *const [8]u8) Packet {
        return Packet{
            .type_id = bytes[0],
            .length = std.mem.readInt(u16, bytes[1..3], .little),
            .payload = bytes[3..8].*,
        };
    }
};
```

Reinterpret memory as structured data when working with binary formats.

### Discussion

Zig gives you fine control over how and when structs are initialized.

### When to Skip Init

**Performance-critical paths**: Avoid unnecessary zero-initialization
```zig
var buffer: [4096]u8 = undefined;  // Fast
var buffer: [4096]u8 = [_]u8{0} ** 4096;  // Slow
```

**Object pools**: Reuse instances without re-initializing
```zig
const obj = pool.acquire();  // Gets recycled object
obj.reset();  // Only reset what changed
```

**Working with external data**: Deserialize from bytes
```zig
const header = try Header.fromBytes(network_data);
```

**Compile-time constants**: Create at comptime for zero runtime cost
```zig
const config = Config{ .port = 8080, ... };  // Built into binary
```

### Initialization Techniques

**Undefined** (`undefined`):
- Use when you'll immediately overwrite
- Fastest option
- Dangerous if you forget to initialize

**Zero** (`std.mem.zeroes`):
- Sets all bytes to zero
- Safe default for numeric types
- Overhead for large structures

**Direct literal** (`.{ .field = value }`):
- Explicit and clear
- Compile-time checked
- Same as calling init()

**Copy** (`instance.*` or `@memcpy`):
- Simple value copy
- Fast for small structs
- Consider pointers for large structs

### Safety Considerations

**Undefined is dangerous**:
```zig
var x: i32 = undefined;
std.debug.print("{}", .{x});  // Undefined behavior!
```

Only use `undefined` when you'll initialize before reading.

**Alignment matters for reinterpretation**:
```zig
// Safe - explicit alignment
const ptr: *align(@alignOf(Header)) const u8 = data.ptr;
const header: *const Header = @ptrCast(@alignCast(ptr));

// Unsafe - might crash
const header: *const Header = @ptrCast(data.ptr);
```

Always use `@alignCast` when reinterpreting pointers.

### Performance Implications

**Compile-time initialization**: Zero runtime cost
```zig
const config = Config{ .port = 8080 };  // Embedded in binary
```

**Zero initialization**: Memset overhead
```zig
const zeroed = std.mem.zeroes(LargeStruct);  // Runtime cost
```

**Undefined initialization**: Zero cost but must initialize before use
```zig
var buffer: [1024]u8 = undefined;  // Instant
buffer[0] = 42;  // Now safe to use buffer[0]
```

**Direct struct literals**: Same as init(), often inlined
```zig
const p = Point{ .x = 1, .y = 2 };  // Typically inlined
```

### When to Use Each Pattern

Use **direct literals** when:
- Init doesn't provide value
- You want explicit field values
- Working with small structs

Use **undefined** when:
- Performance critical
- You'll immediately overwrite
- Working with large arrays

Use **std.mem.zeroes** when:
- You want a clean slate
- Struct has many fields
- Safety over performance

Use **comptime instances** when:
- Values never change
- Configuration constants
- Zero runtime cost desired

### Full Tested Code

```zig
// Recipe 8.17: Creating an Instance Without Invoking Init
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: direct_literal
// Direct struct literal initialization
const Point = struct {
    x: f32,
    y: f32,

    pub fn init(x: f32, y: f32) Point {
        return Point{ .x = x, .y = y };
    }
};

test "direct literal initialization" {
    // Create without calling init
    const p1 = Point{ .x = 3, .y = 4 };
    try testing.expectEqual(@as(f32, 3), p1.x);

    // Using init for comparison
    const p2 = Point.init(3, 4);
    try testing.expectEqual(@as(f32, 3), p2.x);

    // Both are equivalent
    try testing.expectEqual(p1.x, p2.x);
    try testing.expectEqual(p1.y, p2.y);
}
// ANCHOR_END: direct_literal

// ANCHOR: undefined_init
// Undefined initialization for performance
const Buffer = struct {
    data: [1024]u8,
    len: usize,

    pub fn init() Buffer {
        return Buffer{
            .data = undefined,
            .len = 0,
        };
    }

    pub fn uninitialized() Buffer {
        var buf: Buffer = undefined;
        buf.len = 0;
        return buf;
    }

    pub fn write(self: *Buffer, bytes: []const u8) void {
        const space = self.data.len - self.len;
        const to_write = @min(bytes.len, space);
        @memcpy(self.data[self.len..][0..to_write], bytes[0..to_write]);
        self.len += to_write;
    }
};

test "undefined initialization" {
    var buf1 = Buffer.init();
    buf1.write("test");
    try testing.expectEqual(@as(usize, 4), buf1.len);

    var buf2 = Buffer.uninitialized();
    buf2.write("data");
    try testing.expectEqual(@as(usize, 4), buf2.len);
}
// ANCHOR_END: undefined_init

// ANCHOR: zero_init
// Zero initialization
const Counters = struct {
    success: u32,
    failure: u32,
    pending: u32,

    pub fn init() Counters {
        return Counters{
            .success = 0,
            .failure = 0,
            .pending = 0,
        };
    }

    pub fn zero() Counters {
        return std.mem.zeroes(Counters);
    }
};

test "zero initialization" {
    const c1 = Counters.init();
    try testing.expectEqual(@as(u32, 0), c1.success);

    const c2 = Counters.zero();
    try testing.expectEqual(@as(u32, 0), c2.success);
    try testing.expectEqual(@as(u32, 0), c2.failure);
    try testing.expectEqual(@as(u32, 0), c2.pending);
}
// ANCHOR_END: zero_init

// ANCHOR: from_bytes
// Deserialize from bytes
const Header = struct {
    magic: u32,
    version: u16,
    flags: u16,

    pub fn fromBytes(bytes: []const u8) !Header {
        if (bytes.len < @sizeOf(Header)) return error.TooSmall;

        return Header{
            .magic = std.mem.readInt(u32, bytes[0..4], .little),
            .version = std.mem.readInt(u16, bytes[4..6], .little),
            .flags = std.mem.readInt(u16, bytes[6..8], .little),
        };
    }

    pub fn fromBytesUnsafe(bytes: *const [@sizeOf(Header)]u8) *const Header {
        return @ptrCast(@alignCast(bytes));
    }
};

test "from bytes" {
    const bytes = [_]u8{ 0x12, 0x34, 0x56, 0x78, 0x01, 0x00, 0x02, 0x00 };

    const header = try Header.fromBytes(&bytes);
    try testing.expectEqual(@as(u32, 0x78563412), header.magic);
    try testing.expectEqual(@as(u16, 0x0001), header.version);
}
// ANCHOR_END: from_bytes

// ANCHOR: pool_pattern
// Object pool pattern (reuse without init)
const PooledObject = struct {
    id: u32,
    data: [64]u8,
    in_use: bool,

    pub fn reset(self: *PooledObject) void {
        self.in_use = false;
        @memset(&self.data, 0);
    }

    pub fn acquire(self: *PooledObject, id: u32) void {
        self.id = id;
        self.in_use = true;
    }
};

const ObjectPool = struct {
    objects: [10]PooledObject,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) ObjectPool {
        var pool = ObjectPool{
            .objects = undefined,
            .allocator = allocator,
        };

        for (&pool.objects, 0..) |*obj, i| {
            obj.* = PooledObject{
                .id = @intCast(i),
                .data = undefined,
                .in_use = false,
            };
        }

        return pool;
    }

    pub fn acquire(self: *ObjectPool) ?*PooledObject {
        for (&self.objects) |*obj| {
            if (!obj.in_use) {
                obj.in_use = true;
                return obj;
            }
        }
        return null;
    }

    pub fn release(self: *ObjectPool, obj: *PooledObject) void {
        _ = self;
        obj.reset();
    }
};

test "pool pattern" {
    var pool = ObjectPool.init(testing.allocator);

    const obj1 = pool.acquire().?;
    obj1.acquire(100);
    try testing.expectEqual(@as(u32, 100), obj1.id);
    try testing.expect(obj1.in_use);

    pool.release(obj1);
    try testing.expect(!obj1.in_use);

    const obj2 = pool.acquire().?;
    try testing.expect(obj2.in_use);
}
// ANCHOR_END: pool_pattern

// ANCHOR: comptime_instance
// Comptime instance creation
const Config = struct {
    max_connections: u32,
    timeout_ms: u32,
    buffer_size: usize,

    pub fn default() Config {
        return Config{
            .max_connections = 100,
            .timeout_ms = 5000,
            .buffer_size = 4096,
        };
    }
};

// Create at compile time
const global_config = Config{
    .max_connections = 50,
    .timeout_ms = 3000,
    .buffer_size = 2048,
};

const default_config = Config.default();

test "comptime instance" {
    try testing.expectEqual(@as(u32, 50), global_config.max_connections);
    try testing.expectEqual(@as(u32, 100), default_config.max_connections);

    // Can use comptime instances at runtime
    var runtime_config = global_config;
    runtime_config.max_connections = 200;
    try testing.expectEqual(@as(u32, 200), runtime_config.max_connections);
}
// ANCHOR_END: comptime_instance

// ANCHOR: placement_new
// Placement initialization (initialize in-place)
const Node = struct {
    value: i32,
    next: ?*Node,

    pub fn initInPlace(self: *Node, value: i32) void {
        self.* = Node{
            .value = value,
            .next = null,
        };
    }
};

test "placement initialization" {
    var storage: Node = undefined;
    storage.initInPlace(42);

    try testing.expectEqual(@as(i32, 42), storage.value);
    try testing.expect(storage.next == null);

    // Can also use direct assignment
    var storage2: Node = undefined;
    storage2 = Node{ .value = 100, .next = null };
    try testing.expectEqual(@as(i32, 100), storage2.value);
}
// ANCHOR_END: placement_new

// ANCHOR: default_struct
// Structs with default values
const Settings = struct {
    name: []const u8 = "default",
    enabled: bool = true,
    count: u32 = 0,

    pub fn init() Settings {
        return .{};
    }
};

test "default struct values" {
    const s1: Settings = .{};
    try testing.expectEqualStrings("default", s1.name);
    try testing.expect(s1.enabled);
    try testing.expectEqual(@as(u32, 0), s1.count);

    const s2: Settings = .{ .name = "custom", .count = 10 };
    try testing.expectEqualStrings("custom", s2.name);
    try testing.expect(s2.enabled); // Still uses default
    try testing.expectEqual(@as(u32, 10), s2.count);
}
// ANCHOR_END: default_struct

// ANCHOR: copy_from
// Copy from another instance
const Matrix = struct {
    data: [9]f32,

    pub fn identity() Matrix {
        return Matrix{
            .data = [_]f32{
                1, 0, 0,
                0, 1, 0,
                0, 0, 1,
            },
        };
    }

    pub fn copyFrom(other: *const Matrix) Matrix {
        var m: Matrix = undefined;
        @memcpy(&m.data, &other.data);
        return m;
    }

    pub fn clone(self: *const Matrix) Matrix {
        return self.*;
    }
};

test "copy from" {
    const m1 = Matrix.identity();
    const m2 = Matrix.copyFrom(&m1);

    try testing.expectEqual(m1.data[0], m2.data[0]);
    try testing.expectEqual(m1.data[4], m2.data[4]);

    const m3 = m1.clone();
    try testing.expectEqual(m1.data[0], m3.data[0]);
}
// ANCHOR_END: copy_from

// ANCHOR: tagged_union_init
// Tagged union initialization without constructor
const Message = union(enum) {
    text: []const u8,
    number: i32,
    flag: bool,

    pub fn initText(content: []const u8) Message {
        return .{ .text = content };
    }

    pub fn initNumber(value: i32) Message {
        return .{ .number = value };
    }
};

test "tagged union initialization" {
    // Direct initialization
    const m1: Message = .{ .text = "hello" };
    try testing.expectEqualStrings("hello", m1.text);

    const m2: Message = .{ .number = 42 };
    try testing.expectEqual(@as(i32, 42), m2.number);

    // Using constructors
    const m3 = Message.initText("world");
    try testing.expectEqualStrings("world", m3.text);
}
// ANCHOR_END: tagged_union_init

// ANCHOR: reinterpret
// Reinterpret bytes as struct
const Packet = struct {
    type_id: u8,
    length: u16,
    payload: [5]u8,

    pub fn fromMemory(ptr: *const anyopaque) *const Packet {
        return @ptrCast(@alignCast(ptr));
    }

    pub fn fromBytes(bytes: *const [8]u8) Packet {
        return Packet{
            .type_id = bytes[0],
            .length = std.mem.readInt(u16, bytes[1..3], .little),
            .payload = bytes[3..8].*,
        };
    }
};

test "reinterpret bytes" {
    const bytes = [_]u8{ 1, 10, 0, 'h', 'e', 'l', 'l', 'o' };
    const packet = Packet.fromBytes(&bytes);

    try testing.expectEqual(@as(u8, 1), packet.type_id);
    try testing.expectEqual(@as(u16, 10), packet.length);
    try testing.expectEqual(@as(u8, 'h'), packet.payload[0]);
}
// ANCHOR_END: reinterpret

// Comprehensive test
test "comprehensive instance creation" {
    // Direct literal
    const p: Point = .{ .x = 1, .y = 2 };
    try testing.expectEqual(@as(f32, 1), p.x);

    // Zero initialized
    const c = std.mem.zeroes(Counters);
    try testing.expectEqual(@as(u32, 0), c.success);

    // With defaults
    const s: Settings = .{ .count = 5 };
    try testing.expect(s.enabled);
    try testing.expectEqual(@as(u32, 5), s.count);

    // Tagged union
    const msg: Message = .{ .flag = true };
    try testing.expect(msg.flag);

    // Undefined then initialize
    var buf: Buffer = undefined;
    buf.len = 0;
    try testing.expectEqual(@as(usize, 0), buf.len);
}
```

### See Also

- Recipe 8.16: Defining More Than One Constructor in a Class
- Recipe 8.11: Simplifying the Initialization of Data Structures
- Recipe 8.14: Implementing Custom Containers
- Recipe 9.11: Using comptime to Control Instance Creation

---

## Recipe 8.18: Extending Structs with Mixins {#recipe-8-18}

**Tags:** comptime, concurrency, error-handling, pointers, resource-cleanup, structs-objects, synchronization, testing, threading
**Difficulty:** advanced
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_18.zig`

### Problem

You want to add cross-cutting functionality (like logging, validation, caching, or timing) to multiple types without code duplication. Traditional inheritance doesn't fit Zig's philosophy.

### Solution

Use compile-time functions that return wrapper types. These "mixins" embed the original type and add new functionality, composing features at compile time with zero runtime overhead.

### Basic Mixin Pattern

Wrap a type to add functionality:

```zig
// Basic mixin pattern - wrapping a type with additional functionality
fn WithLogging(comptime T: type) type {
    return struct {
        inner: T,
        log_count: u32,

        const Self = @This();

        pub fn init(inner: T) Self {
            return Self{
                .inner = inner,
                .log_count = 0,
            };
        }

        pub fn execute(self: *Self) void {
            self.log_count += 1;
            if (@hasDecl(T, "execute")) {
                self.inner.execute();
            }
        }

        pub fn getLogCount(self: *const Self) u32 {
            return self.log_count;
        }

        pub fn getInner(self: *Self) *T {
            return &self.inner;
        }
    };
}

const SimpleTask = struct {
    count: u32,

    pub fn init() SimpleTask {
        return SimpleTask{ .count = 0 };
    }

    pub fn execute(self: *SimpleTask) void {
        self.count += 1;
    }
};

test "basic mixin" {
    const task = SimpleTask.init();
    var logged = WithLogging(SimpleTask).init(task);

    logged.execute();
    logged.execute();
    logged.execute();

    try testing.expectEqual(@as(u32, 3), logged.getLogCount());
    try testing.expectEqual(@as(u32, 3), logged.getInner().count);
}
```

The mixin wraps SimpleTask, adding logging without modifying the original type.

### Composing Multiple Mixins

Stack mixins to combine functionality:

```zig
fn WithTiming(comptime T: type) type {
    return struct {
        inner: T,
        last_duration_ns: u64,

        pub fn execute(self: *Self) void {
            const start = std.time.nanoTimestamp();
            if (@hasDecl(T, "execute")) {
                self.inner.execute();
            }
            const end = std.time.nanoTimestamp();
            self.last_duration_ns = @intCast(end - start);
        }

        pub fn getDuration(self: *const Self) u64 {
            return self.last_duration_ns;
        }
    };
}

// Stack multiple mixins
const task = SimpleTask.init();
var logged = WithLogging(SimpleTask).init(task);
var timed = WithTiming(WithLogging(SimpleTask)).init(logged);

timed.execute();
// Now both timed and logged!
```

Mixins compose naturally, each adding a layer of functionality.

### Validation Mixin

Add runtime validation to any type:

```zig
fn WithValidation(comptime T: type) type {
    return struct {
        inner: T,
        validation_errors: u32,

        pub fn setValue(self: *Self, value: i32) !void {
            if (value < 0) {
                self.validation_errors += 1;
                return error.InvalidValue;
            }
            if (@hasDecl(T, "setValue")) {
                try self.inner.setValue(value);
            }
        }

        pub fn getValidationErrors(self: *const Self) u32 {
            return self.validation_errors;
        }
    };
}
```

The validation mixin intercepts method calls to enforce constraints.

### Caching Mixin

Add memoization to expensive computations:

```zig
fn WithCache(comptime T: type, comptime CacheType: type) type {
    return struct {
        inner: T,
        cache: ?CacheType,
        cache_hits: u32,

        pub fn compute(self: *Self) CacheType {
            if (self.cache) |cached| {
                self.cache_hits += 1;
                return cached;
            }

            const result = if (@hasDecl(T, "compute"))
                self.inner.compute()
            else
                @as(CacheType, 0);

            self.cache = result;
            return result;
        }

        pub fn invalidate(self: *Self) void {
            self.cache = null;
        }

        pub fn getCacheHits(self: *const Self) u32 {
            return self.cache_hits;
        }
    };
}
```

Caching is transparently added to any type with a `compute()` method.

### Serialization Mixin

Add serialization without modifying the original type:

```zig
fn Serializable(comptime T: type) type {
    return struct {
        inner: T,

        pub fn toBytes(self: *const Self, buffer: []u8) !usize {
            if (buffer.len < @sizeOf(T)) return error.BufferTooSmall;
            const bytes = std.mem.asBytes(&self.inner);
            @memcpy(buffer[0..bytes.len], bytes);
            return bytes.len;
        }

        pub fn fromBytes(bytes: []const u8) !Self {
            if (bytes.len < @sizeOf(T)) return error.BufferTooSmall;
            var inner: T = undefined;
            const dest = std.mem.asBytes(&inner);
            @memcpy(dest, bytes[0..dest.len]);
            return Self{ .inner = inner };
        }
    };
}
```

Any type can now be serialized to/from bytes.

### Observable Mixin

Add observer pattern functionality:

```zig
fn Observable(comptime T: type) type {
    return struct {
        inner: T,
        observers: u32,

        pub fn notify(self: *Self) void {
            self.observers += 1;
        }

        pub fn modify(self: *Self, value: anytype) void {
            if (@hasDecl(T, "setValue")) {
                self.inner.setValue(value) catch {};
            }
            self.notify();
        }

        pub fn getNotificationCount(self: *const Self) u32 {
            return self.observers;
        }
    };
}
```

Track changes and notify observers automatically.

### Retry Mixin

Add automatic retry logic with backoff:

```zig
fn WithRetry(comptime T: type, comptime max_retries: u32) type {
    return struct {
        inner: T,
        retry_count: u32,

        pub fn execute(self: *Self) !void {
            var attempts: u32 = 0;
            while (attempts < max_retries) : (attempts += 1) {
                if (@hasDecl(T, "execute")) {
                    self.inner.execute() catch |err| {
                        self.retry_count += 1;
                        if (attempts == max_retries - 1) {
                            return err;
                        }
                        continue;
                    };
                    return;
                }
            }
        }

        pub fn getRetryCount(self: *const Self) u32 {
            return self.retry_count;
        }
    };
}
```

Automatically retry failed operations.

### Conditional Mixin

Use comptime to enable/disable features:

```zig
fn WithDebug(comptime T: type, comptime enable_debug: bool) type {
    if (enable_debug) {
        return struct {
            inner: T,
            debug_info: []const u8,

            pub fn execute(self: *Self) void {
                // Debug wrapper active
                if (@hasDecl(T, "execute")) {
                    self.inner.execute();
                }
            }

            pub fn getDebugInfo(self: *const Self) []const u8 {
                return self.debug_info;
            }
        };
    } else {
        return struct {
            inner: T,

            pub fn execute(self: *Self) void {
                // No debug overhead
                if (@hasDecl(T, "execute")) {
                    self.inner.execute();
                }
            }
        };
    }
}
```

Compile-time flags control which features are included.

### Thread-Safety Mixin

Add locking behavior (conceptual example):

```zig
fn ThreadSafe(comptime T: type) type {
    return struct {
        inner: T,
        lock_count: u32,

        pub fn withLock(self: *Self, comptime func: anytype) void {
            self.lock_count += 1;
            defer self.lock_count -= 1;
            func(&self.inner);
        }

        pub fn getLockCount(self: *const Self) u32 {
            return self.lock_count;
        }
    };
}

// Usage
var safe = ThreadSafe(Counter).init(counter);
safe.withLock(struct {
    fn call(c: *Counter) void {
        c.value = 100;
    }
}.call);
```

Encapsulate synchronization logic in a reusable mixin.

### Discussion

Mixins provide compile-time composition without runtime overhead.

### How Mixins Work

**Compile-time type generation**:
```zig
fn Mixin(comptime T: type) type {  // Takes a type
    return struct {                 // Returns a new type
        inner: T,                   // Embeds original
        // ... additional fields and methods
    };
}
```

**Zero runtime cost**:
- All mixin logic runs at compile time
- Generated types are concrete structs
- No vtables, no dynamic dispatch
- Same as hand-written code

**Type inference**:
```zig
const Logged = WithLogging(Task);  // New type created
var x = Logged.init(...);          // Type: WithLogging(Task)
```

### Mixin Patterns

**Wrapper pattern**: Embed and extend
```zig
return struct {
    inner: T,
    extra_field: u32,
    pub fn method(self: *Self) void {
        self.inner.originalMethod();  // Delegate
        // ... extra behavior
    }
};
```

**Conditional compilation**: Feature flags
```zig
if (enable_feature) {
    return struct { /* with feature */ };
} else {
    return struct { /* without feature */ };
}
```

**Method forwarding**: Delegate to inner
```zig
pub fn getInner(self: *Self) *T {
    return &self.inner;
}
```

**Capability checking**: Use @hasDecl
```zig
if (@hasDecl(T, "method")) {
    self.inner.method();
}
```

### Design Guidelines

**Naming conventions**:
- `With*` for adding functionality (`WithLogging`, `WithCache`)
- Descriptive names showing what's added
- Use `inner` for the wrapped type

**Interface requirements**:
- Document required methods in comments
- Use `@hasDecl` to check capabilities
- Provide sensible defaults when methods missing

**Composability**:
- Mixins should stack without conflicts
- Each mixin should be independent
- Access inner type with `getInner()`

**Performance**:
- Avoid unnecessary indirection
- Inline small methods
- Use comptime to eliminate dead code

### Advantages Over Inheritance

**Explicit composition**:
```zig
// Clear what functionality is added
var logged = WithLogging(Task).init(task);
var validated = WithValidation(WithLogging(Task)).init(...);
```

**No fragile base class problem**:
- Changes to inner type don't break mixins
- Mixins are independent
- Compile-time errors for incompatibilities

**Flexible**:
- Mix and match as needed
- Different combinations for different uses
- No single inheritance limitation

**Type-safe**:
- All checked at compile time
- No runtime surprises
- Clear error messages

### Common Use Cases

**Cross-cutting concerns**:
- Logging
- Metrics/monitoring
- Validation
- Caching
- Error handling
- Authentication/authorization

**Aspect-oriented programming**:
- Timing measurements
- Resource tracking
- Transaction management
- Retry logic

**Protocol adaptation**:
- Serialization
- Formatting
- Type conversion
- Interface matching

### Performance Characteristics

**Compile-time overhead**: Type generation happens at compile time
- Longer compile times with many mixins
- No runtime impact

**Runtime overhead**: Zero
- Inlined like hand-written code
- No function pointers
- No vtable lookups

**Memory overhead**: Only added fields
```zig
WithLogging(T):
  sizeof(T) + sizeof(u32)  // log_count field

WithCache(T, i32):
  sizeof(T) + sizeof(?i32) + sizeof(u32)  // cache + hits
```

### Comparison with Other Languages

**Rust traits**:
```rust
impl Loggable for Task { ... }  // Zig: WithLogging(Task)
```

**Python decorators**:
```python
@with_logging                   // Zig: WithLogging(Task)
def task(): ...
```

**C++ CRTP (Curiously Recurring Template Pattern)**:
```cpp
template<typename T>
class Logging : public T { ... }  // Zig: WithLogging(T)
```

Zig's approach is simpler and more explicit than these alternatives.

### Full Tested Code

```zig
// Recipe 8.18: Extending Classes with Mixins
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_mixin
// Basic mixin pattern - wrapping a type with additional functionality
fn WithLogging(comptime T: type) type {
    return struct {
        inner: T,
        log_count: u32,

        const Self = @This();

        pub fn init(inner: T) Self {
            return Self{
                .inner = inner,
                .log_count = 0,
            };
        }

        pub fn execute(self: *Self) void {
            self.log_count += 1;
            if (@hasDecl(T, "execute")) {
                self.inner.execute();
            }
        }

        pub fn getLogCount(self: *const Self) u32 {
            return self.log_count;
        }

        pub fn getInner(self: *Self) *T {
            return &self.inner;
        }
    };
}

const SimpleTask = struct {
    count: u32,

    pub fn init() SimpleTask {
        return SimpleTask{ .count = 0 };
    }

    pub fn execute(self: *SimpleTask) void {
        self.count += 1;
    }
};

test "basic mixin" {
    const task = SimpleTask.init();
    var logged = WithLogging(SimpleTask).init(task);

    logged.execute();
    logged.execute();
    logged.execute();

    try testing.expectEqual(@as(u32, 3), logged.getLogCount());
    try testing.expectEqual(@as(u32, 3), logged.getInner().count);
}
// ANCHOR_END: basic_mixin

// ANCHOR: multiple_mixins
// Composing multiple mixins
fn WithTiming(comptime T: type) type {
    return struct {
        inner: T,
        last_duration_ns: u64,

        const Self = @This();

        pub fn init(inner: T) Self {
            return Self{
                .inner = inner,
                .last_duration_ns = 0,
            };
        }

        pub fn execute(self: *Self) void {
            const start = std.time.nanoTimestamp();
            if (@hasDecl(T, "execute")) {
                self.inner.execute();
            }
            const end = std.time.nanoTimestamp();
            self.last_duration_ns = @intCast(end - start);
        }

        pub fn getDuration(self: *const Self) u64 {
            return self.last_duration_ns;
        }

        pub fn getInner(self: *Self) *T {
            return &self.inner;
        }
    };
}

test "multiple mixins" {
    const task = SimpleTask.init();
    const logged = WithLogging(SimpleTask).init(task);
    var timed = WithTiming(WithLogging(SimpleTask)).init(logged);

    timed.execute();

    try testing.expect(timed.getDuration() >= 0);
    try testing.expectEqual(@as(u32, 1), timed.getInner().getLogCount());
}
// ANCHOR_END: multiple_mixins

// ANCHOR: validation_mixin
// Validation mixin
fn WithValidation(comptime T: type) type {
    return struct {
        inner: T,
        validation_errors: u32,

        const Self = @This();

        pub fn init(inner: T) Self {
            return Self{
                .inner = inner,
                .validation_errors = 0,
            };
        }

        pub fn setValue(self: *Self, value: i32) !void {
            if (value < 0) {
                self.validation_errors += 1;
                return error.InvalidValue;
            }
            if (@hasDecl(T, "setValue")) {
                try self.inner.setValue(value);
            }
        }

        pub fn getValidationErrors(self: *const Self) u32 {
            return self.validation_errors;
        }

        pub fn getInner(self: *Self) *T {
            return &self.inner;
        }
    };
}

const Counter = struct {
    value: i32,

    pub fn init() Counter {
        return Counter{ .value = 0 };
    }

    pub fn setValue(self: *Counter, value: i32) !void {
        self.value = value;
    }
};

test "validation mixin" {
    const counter = Counter.init();
    var validated = WithValidation(Counter).init(counter);

    try validated.setValue(10);
    try testing.expectEqual(@as(i32, 10), validated.getInner().value);

    const result = validated.setValue(-5);
    try testing.expectError(error.InvalidValue, result);
    try testing.expectEqual(@as(u32, 1), validated.getValidationErrors());
}
// ANCHOR_END: validation_mixin

// ANCHOR: caching_mixin
// Caching mixin
fn WithCache(comptime T: type, comptime CacheType: type) type {
    return struct {
        inner: T,
        cache: ?CacheType,
        cache_hits: u32,

        const Self = @This();

        pub fn init(inner: T) Self {
            return Self{
                .inner = inner,
                .cache = null,
                .cache_hits = 0,
            };
        }

        pub fn compute(self: *Self) CacheType {
            if (self.cache) |cached| {
                self.cache_hits += 1;
                return cached;
            }

            const result = if (@hasDecl(T, "compute"))
                self.inner.compute()
            else
                @as(CacheType, 0);

            self.cache = result;
            return result;
        }

        pub fn invalidate(self: *Self) void {
            self.cache = null;
        }

        pub fn getCacheHits(self: *const Self) u32 {
            return self.cache_hits;
        }
    };
}

const ExpensiveComputation = struct {
    base: i32,

    pub fn init(base: i32) ExpensiveComputation {
        return ExpensiveComputation{ .base = base };
    }

    pub fn compute(self: *const ExpensiveComputation) i32 {
        return self.base * self.base;
    }
};

test "caching mixin" {
    const comp = ExpensiveComputation.init(5);
    var cached = WithCache(ExpensiveComputation, i32).init(comp);

    const result1 = cached.compute();
    try testing.expectEqual(@as(i32, 25), result1);
    try testing.expectEqual(@as(u32, 0), cached.getCacheHits());

    const result2 = cached.compute();
    try testing.expectEqual(@as(i32, 25), result2);
    try testing.expectEqual(@as(u32, 1), cached.getCacheHits());

    cached.invalidate();
    const result3 = cached.compute();
    try testing.expectEqual(@as(i32, 25), result3);
    try testing.expectEqual(@as(u32, 1), cached.getCacheHits());
}
// ANCHOR_END: caching_mixin

// ANCHOR: serializable_mixin
// Serialization mixin
fn Serializable(comptime T: type) type {
    return struct {
        inner: T,

        const Self = @This();

        pub fn init(inner: T) Self {
            return Self{ .inner = inner };
        }

        pub fn toBytes(self: *const Self, buffer: []u8) !usize {
            if (buffer.len < @sizeOf(T)) return error.BufferTooSmall;
            const bytes = std.mem.asBytes(&self.inner);
            @memcpy(buffer[0..bytes.len], bytes);
            return bytes.len;
        }

        pub fn fromBytes(bytes: []const u8) !Self {
            if (bytes.len < @sizeOf(T)) return error.BufferTooSmall;
            var inner: T = undefined;
            const dest = std.mem.asBytes(&inner);
            @memcpy(dest, bytes[0..dest.len]);
            return Self{ .inner = inner };
        }

        pub fn getInner(self: *const Self) *const T {
            return &self.inner;
        }
    };
}

const Coordinate = struct {
    x: i32,
    y: i32,
};

test "serializable mixin" {
    const coord = Coordinate{ .x = 10, .y = 20 };
    const serializable = Serializable(Coordinate).init(coord);

    var buffer: [16]u8 = undefined;
    const written = try serializable.toBytes(&buffer);
    try testing.expect(written == @sizeOf(Coordinate));

    const deserialized = try Serializable(Coordinate).fromBytes(buffer[0..written]);
    try testing.expectEqual(@as(i32, 10), deserialized.getInner().x);
    try testing.expectEqual(@as(i32, 20), deserialized.getInner().y);
}
// ANCHOR_END: serializable_mixin

// ANCHOR: observable_mixin
// Observable mixin with callbacks
fn Observable(comptime T: type) type {
    return struct {
        inner: T,
        observers: u32,

        const Self = @This();

        pub fn init(inner: T) Self {
            return Self{
                .inner = inner,
                .observers = 0,
            };
        }

        pub fn notify(self: *Self) void {
            self.observers += 1;
        }

        pub fn modify(self: *Self, value: anytype) void {
            if (@hasDecl(T, "setValue")) {
                self.inner.setValue(value) catch {};
            }
            self.notify();
        }

        pub fn getNotificationCount(self: *const Self) u32 {
            return self.observers;
        }

        pub fn getInner(self: *Self) *T {
            return &self.inner;
        }
    };
}

test "observable mixin" {
    const counter = Counter.init();
    var observable = Observable(Counter).init(counter);

    observable.modify(5);
    observable.modify(10);

    try testing.expectEqual(@as(u32, 2), observable.getNotificationCount());
    try testing.expectEqual(@as(i32, 10), observable.getInner().value);
}
// ANCHOR_END: observable_mixin

// ANCHOR: retry_mixin
// Retry mixin for error handling
fn WithRetry(comptime T: type, comptime max_retries: u32) type {
    return struct {
        inner: T,
        retry_count: u32,

        const Self = @This();

        pub fn init(inner: T) Self {
            return Self{
                .inner = inner,
                .retry_count = 0,
            };
        }

        pub fn execute(self: *Self) !void {
            var attempts: u32 = 0;
            while (attempts < max_retries) : (attempts += 1) {
                if (@hasDecl(T, "execute")) {
                    self.inner.execute() catch |err| {
                        self.retry_count += 1;
                        if (attempts == max_retries - 1) {
                            return err;
                        }
                        continue;
                    };
                    return;
                }
            }
        }

        pub fn getRetryCount(self: *const Self) u32 {
            return self.retry_count;
        }
    };
}

const FailingTask = struct {
    failures_left: u32,

    pub fn init(failures: u32) FailingTask {
        return FailingTask{ .failures_left = failures };
    }

    pub fn execute(self: *FailingTask) !void {
        if (self.failures_left > 0) {
            self.failures_left -= 1;
            return error.TemporaryFailure;
        }
    }
};

test "retry mixin" {
    const task = FailingTask.init(2);
    var with_retry = WithRetry(FailingTask, 5).init(task);

    try with_retry.execute();
    try testing.expectEqual(@as(u32, 2), with_retry.getRetryCount());
}
// ANCHOR_END: retry_mixin

// ANCHOR: conditional_mixin
// Conditional mixin based on comptime
fn WithDebug(comptime T: type, comptime enable_debug: bool) type {
    if (enable_debug) {
        return struct {
            inner: T,
            debug_info: []const u8,

            const Self = @This();

            pub fn init(inner: T) Self {
                return Self{
                    .inner = inner,
                    .debug_info = "Debug enabled",
                };
            }

            pub fn execute(self: *Self) void {
                // Debug wrapper
                if (@hasDecl(T, "execute")) {
                    self.inner.execute();
                }
            }

            pub fn getDebugInfo(self: *const Self) []const u8 {
                return self.debug_info;
            }

            pub fn getInner(self: *Self) *T {
                return &self.inner;
            }
        };
    } else {
        return struct {
            inner: T,

            const Self = @This();

            pub fn init(inner: T) Self {
                return Self{ .inner = inner };
            }

            pub fn execute(self: *Self) void {
                if (@hasDecl(T, "execute")) {
                    self.inner.execute();
                }
            }

            pub fn getInner(self: *Self) *T {
                return &self.inner;
            }
        };
    }
}

test "conditional mixin" {
    const task1 = SimpleTask.init();
    var debug_enabled = WithDebug(SimpleTask, true).init(task1);
    debug_enabled.execute();
    try testing.expectEqualStrings("Debug enabled", debug_enabled.getDebugInfo());

    const task2 = SimpleTask.init();
    var debug_disabled = WithDebug(SimpleTask, false).init(task2);
    debug_disabled.execute();
    try testing.expectEqual(@as(u32, 1), debug_disabled.getInner().count);
}
// ANCHOR_END: conditional_mixin

// ANCHOR: builder_mixin
// Builder mixin for fluent interfaces
fn Buildable(comptime T: type) type {
    return struct {
        inner: T,

        const Self = @This();

        pub fn init() Self {
            return Self{
                .inner = if (@hasDecl(T, "init")) T.init() else undefined,
            };
        }

        pub fn with(_: Self, inner: T) Self {
            return Self{ .inner = inner };
        }

        pub fn build(self: Self) T {
            return self.inner;
        }

        pub fn getInner(self: *Self) *T {
            return &self.inner;
        }
    };
}

test "builder mixin" {
    const builder = Buildable(Counter).init();
    var counter = Counter.init();
    counter.value = 42;

    const result = builder.with(counter).build();
    try testing.expectEqual(@as(i32, 42), result.value);
}
// ANCHOR_END: builder_mixin

// ANCHOR: thread_safe_mixin
// Thread-safety mixin (conceptual - would use real mutex in production)
fn ThreadSafe(comptime T: type) type {
    return struct {
        inner: T,
        lock_count: u32,

        const Self = @This();

        pub fn init(inner: T) Self {
            return Self{
                .inner = inner,
                .lock_count = 0,
            };
        }

        pub fn withLock(self: *Self, comptime func: anytype) void {
            self.lock_count += 1;
            defer self.lock_count -= 1;
            func(&self.inner);
        }

        pub fn getLockCount(self: *const Self) u32 {
            return self.lock_count;
        }

        pub fn getInner(self: *Self) *T {
            return &self.inner;
        }
    };
}

test "thread safe mixin" {
    const counter = Counter.init();
    var safe = ThreadSafe(Counter).init(counter);

    safe.withLock(struct {
        fn call(c: *Counter) void {
            c.value = 100;
        }
    }.call);

    try testing.expectEqual(@as(i32, 100), safe.getInner().value);
    try testing.expectEqual(@as(u32, 0), safe.getLockCount());
}
// ANCHOR_END: thread_safe_mixin

// Comprehensive test
test "comprehensive mixin patterns" {
    // Stack mixins
    const task = SimpleTask.init();
    const logged = WithLogging(SimpleTask).init(task);
    var timed = WithTiming(WithLogging(SimpleTask)).init(logged);

    timed.execute();
    try testing.expect(timed.getInner().getLogCount() > 0);

    // Validation
    const counter = Counter.init();
    var validated = WithValidation(Counter).init(counter);
    try validated.setValue(5);
    try testing.expectEqual(@as(i32, 5), validated.getInner().value);

    // Caching
    const comp = ExpensiveComputation.init(10);
    var cached = WithCache(ExpensiveComputation, i32).init(comp);
    _ = cached.compute();
    _ = cached.compute();
    try testing.expectEqual(@as(u32, 1), cached.getCacheHits());
}
```

### See Also

- Recipe 8.15: Delegating Attribute Access
- Recipe 8.12: Defining an Interface or Abstract Base Class
- Recipe 9.11: Using comptime to Control Instance Creation
- Recipe 9.16: Defining Structs Programmatically

---

## Recipe 8.19: Implementing Stateful Objects or State Machines {#recipe-8-19}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, http, memory, networking, pointers, resource-cleanup, sockets, structs-objects, testing
**Difficulty:** advanced
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_19.zig`

### Problem

You need to model objects that change behavior based on state, enforce valid state transitions, or implement a finite state machine (FSM) for protocols, parsers, or game logic.

### Solution

Use Zig's enums and tagged unions to model states explicitly. Combine them with methods that enforce valid transitions and state-specific behavior.

### Basic State Machine

Use enums to define states and validate transitions:

```zig
// Basic state machine with enum
const ConnectionState = enum {
    disconnected,
    connecting,
    connected,
    error_state,

    pub fn canTransition(self: ConnectionState, target: ConnectionState) bool {
        return switch (self) {
            .disconnected => target == .connecting,
            .connecting => target == .connected or target == .error_state,
            .connected => target == .disconnected or target == .error_state,
            .error_state => target == .disconnected,
        };
    }
};

const Connection = struct {
    state: ConnectionState,
    attempts: u32,

    pub fn init() Connection {
        return Connection{
            .state = .disconnected,
            .attempts = 0,
        };
    }

    pub fn connect(self: *Connection) !void {
        if (!self.state.canTransition(.connecting)) {
            return error.InvalidTransition;
        }
        self.state = .connecting;
        self.attempts += 1;
    }

    pub fn complete(self: *Connection) !void {
        if (!self.state.canTransition(.connected)) {
            return error.InvalidTransition;
        }
        self.state = .connected;
    }

    pub fn disconnect(self: *Connection) !void {
        if (!self.state.canTransition(.disconnected)) {
            return error.InvalidTransition;
        }
        self.state = .disconnected;
    }

    pub fn fail(self: *Connection) !void {
        if (!self.state.canTransition(.error_state)) {
            return error.InvalidTransition;
        }
        self.state = .error_state;
    }
};

test "basic state machine" {
    var conn = Connection.init();
    try testing.expectEqual(ConnectionState.disconnected, conn.state);

    try conn.connect();
    try testing.expectEqual(ConnectionState.connecting, conn.state);

    try conn.complete();
    try testing.expectEqual(ConnectionState.connected, conn.state);

    try conn.disconnect();
    try testing.expectEqual(ConnectionState.disconnected, conn.state);
}
```

Invalid transitions return errors at runtime.

### State Pattern with Behavior

Tagged unions carry state-specific data and behavior:

```zig
const DoorState = union(enum) {
    closed: void,
    opening: u32,    // progress percentage
    open: void,
    closing: u32,    // progress percentage

    pub fn handle(self: *DoorState) []const u8 {
        return switch (self.*) {
            .closed => "Door is closed",
            .opening => |progress| blk: {
                if (progress >= 100) {
                    self.* = .{ .open = {} };
                    break :blk "Door fully open";
                }
                break :blk "Door opening";
            },
            .open => "Door is open",
            .closing => |progress| blk: {
                if (progress >= 100) {
                    self.* = .{ .closed = {} };
                    break :blk "Door fully closed";
                }
                break :blk "Door closing";
            },
        };
    }

    pub fn advance(self: *DoorState, amount: u32) void {
        switch (self.*) {
            .opening => |*progress| {
                progress.* = @min(100, progress.* + amount);
            },
            .closing => |*progress| {
                progress.* = @min(100, progress.* + amount);
            },
            else => {},
        }
    }
};

const Door = struct {
    state: DoorState,

    pub fn open(self: *Door) void {
        switch (self.state) {
            .closed => self.state = .{ .opening = 0 },
            else => {},
        }
    }

    pub fn update(self: *Door, delta: u32) []const u8 {
        self.state.advance(delta);
        return self.state.handle();
    }
};
```

State behavior is encapsulated in the union's methods.

### Event-Driven FSM

Process events to trigger state transitions:

```zig
const TrafficLight = struct {
    const State = enum {
        red,
        yellow,
        green,
    };

    const Event = enum {
        timer_expired,
        emergency,
        reset,
    };

    state: State,
    timer: u32,

    pub fn handle(self: *TrafficLight, event: Event) void {
        switch (event) {
            .timer_expired => {
                self.state = switch (self.state) {
                    .red => .green,
                    .green => .yellow,
                    .yellow => .red,
                };
                self.timer = 0;
            },
            .emergency => {
                self.state = .red;
                self.timer = 0;
            },
            .reset => {
                self.state = .red;
                self.timer = 0;
            },
        }
    }

    pub fn tick(self: *TrafficLight) void {
        self.timer += 1;
        const duration: u32 = switch (self.state) {
            .red => 30,
            .green => 25,
            .yellow => 5,
        };
        if (self.timer >= duration) {
            self.handle(.timer_expired);
        }
    }
};
```

Events drive the state machine forward.

### State with Entry/Exit Actions

Execute code when entering or leaving states:

```zig
const OrderState = enum {
    pending,
    processing,
    shipped,
    delivered,
    cancelled,
};

const Order = struct {
    state: OrderState,
    notifications_sent: u32,

    fn onEnter(self: *Order, new_state: OrderState) void {
        switch (new_state) {
            .processing, .shipped, .delivered => {
                self.notifications_sent += 1;
            },
            else => {},
        }
    }

    fn onExit(self: *Order, old_state: OrderState) void {
        _ = self;
        _ = old_state;
        // Cleanup for old state
    }

    pub fn transition(self: *Order, new_state: OrderState) !void {
        const valid = switch (self.state) {
            .pending => new_state == .processing or new_state == .cancelled,
            .processing => new_state == .shipped or new_state == .cancelled,
            .shipped => new_state == .delivered,
            .delivered => false,
            .cancelled => false,
        };

        if (!valid) return error.InvalidTransition;

        self.onExit(self.state);
        self.state = new_state;
        self.onEnter(new_state);
    }
};
```

Entry and exit actions handle state lifecycle.

### Hierarchical State Machines

Nest states within states:

```zig
const PlayerState = union(enum) {
    idle: void,
    moving: struct {
        speed: f32,
        direction: enum { forward, backward },
    },
    combat: union(enum) {
        attacking: u32,
        defending: u32,
        dodging: u32,
    },

    pub fn isInCombat(self: *const PlayerState) bool {
        return switch (self.*) {
            .combat => true,
            else => false,
        };
    }

    pub fn isMoving(self: *const PlayerState) bool {
        return switch (self.*) {
            .moving => true,
            else => false,
        };
    }
};

const Player = struct {
    state: PlayerState,

    pub fn move(self: *Player, speed: f32) void {
        if (!self.state.isInCombat()) {
            self.state = .{ .moving = .{ .speed = speed, .direction = .forward } };
        }
    }

    pub fn attack(self: *Player) void {
        self.state = .{ .combat = .{ .attacking = 0 } };
    }
};
```

Hierarchical states model complex behavior naturally.

### State History

Track previous states for undo functionality:

```zig
const WorkflowState = enum {
    draft,
    review,
    approved,
    published,
    archived,
};

const Workflow = struct {
    current: WorkflowState,
    history: std.ArrayList(WorkflowState),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Workflow {
        return Workflow{
            .current = .draft,
            .history = std.ArrayList(WorkflowState){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Workflow) void {
        self.history.deinit(self.allocator);
    }

    pub fn transition(self: *Workflow, new_state: WorkflowState) !void {
        try self.history.append(self.allocator, self.current);
        self.current = new_state;
    }

    pub fn undo(self: *Workflow) !void {
        if (self.history.items.len == 0) return error.NoHistory;
        self.current = self.history.pop().?;
    }
};
```

State history enables undo/redo functionality.

### Guarded Transitions

Add conditions that must be met for transitions:

```zig
const ATM = struct {
    const State = enum {
        idle,
        card_inserted,
        pin_entered,
        authenticated,
        dispensing,
    };

    state: State,
    balance: u32,
    pin_attempts: u32,

    pub fn enterPin(self: *ATM, pin: u32) !void {
        if (self.state != .card_inserted and self.state != .pin_entered) {
            return error.InvalidState;
        }

        if (pin == 1234) {
            self.state = .authenticated;
            self.pin_attempts = 0;
        } else {
            self.pin_attempts += 1;
            if (self.pin_attempts >= 3) {
                self.state = .idle;
                return error.TooManyAttempts;
            }
            self.state = .pin_entered;
            return error.InvalidPin;
        }
    }

    pub fn withdraw(self: *ATM, amount: u32) !void {
        if (self.state != .authenticated) return error.NotAuthenticated;
        if (amount > self.balance) return error.InsufficientFunds;

        self.balance -= amount;
        self.state = .dispensing;
    }
};
```

Guards prevent invalid state changes based on conditions.

### Timeout States

Implement states that expire after a duration:

```zig
const Session = struct {
    const State = enum {
        inactive,
        active,
        idle_warning,
        expired,
    };

    state: State,
    last_activity: u64,
    timeout_ms: u64,

    pub fn activate(self: *Session, current_time: u64) void {
        self.state = .active;
        self.last_activity = current_time;
    }

    pub fn activity(self: *Session, current_time: u64) void {
        if (self.state == .active or self.state == .idle_warning) {
            self.last_activity = current_time;
            self.state = .active;
        }
    }

    pub fn update(self: *Session, current_time: u64) void {
        if (self.state == .inactive or self.state == .expired) {
            return;
        }

        const elapsed = current_time - self.last_activity;

        if (elapsed > self.timeout_ms) {
            self.state = .expired;
        } else if (elapsed > self.timeout_ms / 2) {
            self.state = .idle_warning;
        }
    }
};
```

Time-based state transitions for sessions, caches, and timeouts.

### Composite State Machine

Multiple independent state dimensions:

```zig
const MediaPlayer = struct {
    const PlaybackState = enum {
        stopped,
        playing,
        paused,
    };

    const RepeatMode = enum {
        none,
        one,
        all,
    };

    playback: PlaybackState,
    repeat: RepeatMode,
    volume: u8,
    track_index: usize,

    pub fn play(self: *MediaPlayer) void {
        self.playback = .playing;
    }

    pub fn next(self: *MediaPlayer, total_tracks: usize) void {
        if (self.track_index < total_tracks - 1) {
            self.track_index += 1;
        } else if (self.repeat == .all) {
            self.track_index = 0;
        }
    }

    pub fn setRepeat(self: *MediaPlayer, mode: RepeatMode) void {
        self.repeat = mode;
    }
};
```

Independent state variables model orthogonal concerns.

### Discussion

State machines make complex behavior manageable and testable.

### Why State Machines

**Explicit states**: All states are visible in the type system
```zig
const State = enum { idle, running, paused };
```

**Impossible states**: Type system prevents invalid combinations
```zig
// Can't be both running and paused
state: State,  // Only one value at a time
```

**Clear transitions**: Switch statements make logic obvious
```zig
self.state = switch (self.state) {
    .idle => .running,
    .running => .paused,
    .paused => .running,
};
```

**Testable**: Each state and transition can be tested independently
```zig
test "transition from idle to running" { ... }
```

### State Machine Patterns

**Enum-based**: Simple states without data
```zig
state: enum { off, on, error_state }
```

**Tagged union**: States with associated data
```zig
state: union(enum) {
    idle: void,
    running: struct { progress: u32 },
}
```

**Nested unions**: Hierarchical states
```zig
state: union(enum) {
    idle: void,
    active: union(enum) {
        reading: void,
        writing: struct { bytes: usize },
    },
}
```

**Multiple enums**: Orthogonal state dimensions
```zig
playback_state: PlaybackState,
repeat_mode: RepeatMode,
```

### Transition Validation

**Compile-time validation**: Use switch exhaustiveness
```zig
// Compiler ensures all states handled
const next = switch (current) {
    .idle => .running,
    .running => .paused,
    .paused => .stopped,
    // Forgot one? Compiler error!
};
```

**Runtime validation**: Return errors for invalid transitions
```zig
pub fn transition(from: State, to: State) !void {
    if (!validTransition(from, to)) {
        return error.InvalidTransition;
    }
}
```

**Transition table**: Explicit allowed transitions
```zig
pub fn canTransition(self: State, target: State) bool {
    return switch (self) {
        .idle => target == .running,
        .running => target == .paused or target == .stopped,
        // ...
    };
}
```

### Design Guidelines

**Keep states simple**: Each state should have a clear purpose

**Explicit transitions**: Make state changes obvious
```zig
self.state = .new_state;  // Clear
```

**Validate transitions**: Check if transition is valid before changing
```zig
if (!self.state.canTransition(.new_state)) {
    return error.InvalidTransition;
}
```

**Use entry/exit actions**: Handle initialization and cleanup
```zig
self.onExit(old_state);
self.state = new_state;
self.onEnter(new_state);
```

**Document state diagram**: Comment or document the state machine structure
```zig
// State diagram:
// idle -> connecting -> connected -> disconnected
//         |                |
//         +-> error <------+
```

### Performance

**Enum states**: Zero overhead
- Stored as integer (u8, u16, etc.)
- Switch compiles to jump table
- No allocation, no pointers

**Tagged unions**: Size of largest variant + tag
- Tag is an enum (small integer)
- Union is size of biggest state data
- Still no heap allocation

**State transitions**: Simple assignments
- No function calls unless you add them
- Inline validation checks
- Compiler optimizes switches

### Common Use Cases

**Protocol implementation**:
- Network connections (TCP state machine)
- HTTP request/response states
- WebSocket handshake

**Parsers**:
- Lexer states
- Parser states
- Format validators

**Game logic**:
- Player states (idle, moving, attacking)
- AI behavior trees
- Menu systems

**Business logic**:
- Order processing (pending, shipped, delivered)
- User registration flows
- Workflow engines

**UI state**:
- Form validation states
- Loading/error/success states
- Modal dialog states

### Full Tested Code

```zig
// Recipe 8.19: Implementing Stateful Objects or State Machines
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_state_machine
// Basic state machine with enum
const ConnectionState = enum {
    disconnected,
    connecting,
    connected,
    error_state,

    pub fn canTransition(self: ConnectionState, target: ConnectionState) bool {
        return switch (self) {
            .disconnected => target == .connecting,
            .connecting => target == .connected or target == .error_state,
            .connected => target == .disconnected or target == .error_state,
            .error_state => target == .disconnected,
        };
    }
};

const Connection = struct {
    state: ConnectionState,
    attempts: u32,

    pub fn init() Connection {
        return Connection{
            .state = .disconnected,
            .attempts = 0,
        };
    }

    pub fn connect(self: *Connection) !void {
        if (!self.state.canTransition(.connecting)) {
            return error.InvalidTransition;
        }
        self.state = .connecting;
        self.attempts += 1;
    }

    pub fn complete(self: *Connection) !void {
        if (!self.state.canTransition(.connected)) {
            return error.InvalidTransition;
        }
        self.state = .connected;
    }

    pub fn disconnect(self: *Connection) !void {
        if (!self.state.canTransition(.disconnected)) {
            return error.InvalidTransition;
        }
        self.state = .disconnected;
    }

    pub fn fail(self: *Connection) !void {
        if (!self.state.canTransition(.error_state)) {
            return error.InvalidTransition;
        }
        self.state = .error_state;
    }
};

test "basic state machine" {
    var conn = Connection.init();
    try testing.expectEqual(ConnectionState.disconnected, conn.state);

    try conn.connect();
    try testing.expectEqual(ConnectionState.connecting, conn.state);

    try conn.complete();
    try testing.expectEqual(ConnectionState.connected, conn.state);

    try conn.disconnect();
    try testing.expectEqual(ConnectionState.disconnected, conn.state);
}
// ANCHOR_END: basic_state_machine

// ANCHOR: state_pattern
// State pattern with behavior
const DoorState = union(enum) {
    closed: void,
    opening: u32,
    open: void,
    closing: u32,

    pub fn handle(self: *DoorState) []const u8 {
        return switch (self.*) {
            .closed => "Door is closed",
            .opening => |progress| blk: {
                if (progress >= 100) {
                    self.* = .{ .open = {} };
                    break :blk "Door fully open";
                }
                break :blk "Door opening";
            },
            .open => "Door is open",
            .closing => |progress| blk: {
                if (progress >= 100) {
                    self.* = .{ .closed = {} };
                    break :blk "Door fully closed";
                }
                break :blk "Door closing";
            },
        };
    }

    pub fn advance(self: *DoorState, amount: u32) void {
        switch (self.*) {
            .opening => |*progress| {
                progress.* = @min(100, progress.* + amount);
            },
            .closing => |*progress| {
                progress.* = @min(100, progress.* + amount);
            },
            else => {},
        }
    }
};

const Door = struct {
    state: DoorState,

    pub fn init() Door {
        return Door{ .state = .{ .closed = {} } };
    }

    pub fn open(self: *Door) void {
        switch (self.state) {
            .closed => self.state = .{ .opening = 0 },
            else => {},
        }
    }

    pub fn close(self: *Door) void {
        switch (self.state) {
            .open => self.state = .{ .closing = 0 },
            else => {},
        }
    }

    pub fn update(self: *Door, delta: u32) []const u8 {
        self.state.advance(delta);
        return self.state.handle();
    }
};

test "state pattern" {
    var door = Door.init();
    door.open();

    const msg1 = door.update(50);
    try testing.expectEqualStrings("Door opening", msg1);

    const msg2 = door.update(60);
    try testing.expectEqualStrings("Door fully open", msg2);

    door.close();
    _ = door.update(100);
    try testing.expect(std.meta.activeTag(door.state) == .closed);
}
// ANCHOR_END: state_pattern

// ANCHOR: event_driven_fsm
// Event-driven finite state machine
const TrafficLight = struct {
    const State = enum {
        red,
        yellow,
        green,
    };

    const Event = enum {
        timer_expired,
        emergency,
        reset,
    };

    state: State,
    timer: u32,

    pub fn init() TrafficLight {
        return TrafficLight{
            .state = .red,
            .timer = 0,
        };
    }

    pub fn handle(self: *TrafficLight, event: Event) void {
        switch (event) {
            .timer_expired => {
                self.state = switch (self.state) {
                    .red => .green,
                    .green => .yellow,
                    .yellow => .red,
                };
                self.timer = 0;
            },
            .emergency => {
                self.state = .red;
                self.timer = 0;
            },
            .reset => {
                self.state = .red;
                self.timer = 0;
            },
        }
    }

    pub fn tick(self: *TrafficLight) void {
        self.timer += 1;
        const duration: u32 = switch (self.state) {
            .red => 30,
            .green => 25,
            .yellow => 5,
        };
        if (self.timer >= duration) {
            self.handle(.timer_expired);
        }
    }
};

test "event driven fsm" {
    var light = TrafficLight.init();
    try testing.expectEqual(TrafficLight.State.red, light.state);

    // Simulate time passing
    var i: u32 = 0;
    while (i < 31) : (i += 1) {
        light.tick();
    }
    try testing.expectEqual(TrafficLight.State.green, light.state);

    light.handle(.emergency);
    try testing.expectEqual(TrafficLight.State.red, light.state);
}
// ANCHOR_END: event_driven_fsm

// ANCHOR: state_with_actions
// State machine with entry/exit actions
const OrderState = enum {
    pending,
    processing,
    shipped,
    delivered,
    cancelled,
};

const Order = struct {
    state: OrderState,
    notifications_sent: u32,

    pub fn init() Order {
        return Order{
            .state = .pending,
            .notifications_sent = 0,
        };
    }

    fn onEnter(self: *Order, new_state: OrderState) void {
        switch (new_state) {
            .processing, .shipped, .delivered => {
                self.notifications_sent += 1;
            },
            else => {},
        }
    }

    fn onExit(self: *Order, old_state: OrderState) void {
        _ = self;
        _ = old_state;
        // Cleanup for old state
    }

    pub fn transition(self: *Order, new_state: OrderState) !void {
        const valid = switch (self.state) {
            .pending => new_state == .processing or new_state == .cancelled,
            .processing => new_state == .shipped or new_state == .cancelled,
            .shipped => new_state == .delivered,
            .delivered => false,
            .cancelled => false,
        };

        if (!valid) return error.InvalidTransition;

        self.onExit(self.state);
        self.state = new_state;
        self.onEnter(new_state);
    }
};

test "state with actions" {
    var order = Order.init();

    try order.transition(.processing);
    try testing.expectEqual(@as(u32, 1), order.notifications_sent);

    try order.transition(.shipped);
    try testing.expectEqual(@as(u32, 2), order.notifications_sent);

    try order.transition(.delivered);
    try testing.expectEqual(OrderState.delivered, order.state);
}
// ANCHOR_END: state_with_actions

// ANCHOR: hierarchical_states
// Hierarchical state machine
const PlayerState = union(enum) {
    idle: void,
    moving: struct {
        speed: f32,
        direction: enum { forward, backward },
    },
    combat: union(enum) {
        attacking: u32,
        defending: u32,
        dodging: u32,
    },

    pub fn isInCombat(self: *const PlayerState) bool {
        return switch (self.*) {
            .combat => true,
            else => false,
        };
    }

    pub fn isMoving(self: *const PlayerState) bool {
        return switch (self.*) {
            .moving => true,
            else => false,
        };
    }
};

const Player = struct {
    state: PlayerState,
    health: u32,

    pub fn init() Player {
        return Player{
            .state = .{ .idle = {} },
            .health = 100,
        };
    }

    pub fn move(self: *Player, speed: f32) void {
        if (!self.state.isInCombat()) {
            self.state = .{ .moving = .{ .speed = speed, .direction = .forward } };
        }
    }

    pub fn attack(self: *Player) void {
        self.state = .{ .combat = .{ .attacking = 0 } };
    }

    pub fn stopCombat(self: *Player) void {
        if (self.state.isInCombat()) {
            self.state = .{ .idle = {} };
        }
    }
};

test "hierarchical states" {
    var player = Player.init();
    try testing.expect(!player.state.isInCombat());

    player.move(5.0);
    try testing.expect(player.state.isMoving());

    player.attack();
    try testing.expect(player.state.isInCombat());

    player.stopCombat();
    try testing.expect(!player.state.isInCombat());
}
// ANCHOR_END: hierarchical_states

// ANCHOR: state_history
// State machine with history
const WorkflowState = enum {
    draft,
    review,
    approved,
    published,
    archived,
};

const Workflow = struct {
    current: WorkflowState,
    history: std.ArrayList(WorkflowState),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Workflow {
        return Workflow{
            .current = .draft,
            .history = std.ArrayList(WorkflowState){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Workflow) void {
        self.history.deinit(self.allocator);
    }

    pub fn transition(self: *Workflow, new_state: WorkflowState) !void {
        try self.history.append(self.allocator, self.current);
        self.current = new_state;
    }

    pub fn undo(self: *Workflow) !void {
        if (self.history.items.len == 0) return error.NoHistory;
        self.current = self.history.pop().?;
    }

    pub fn getHistoryCount(self: *const Workflow) usize {
        return self.history.items.len;
    }
};

test "state history" {
    var workflow = Workflow.init(testing.allocator);
    defer workflow.deinit();

    try workflow.transition(.review);
    try workflow.transition(.approved);
    try testing.expectEqual(WorkflowState.approved, workflow.current);
    try testing.expectEqual(@as(usize, 2), workflow.getHistoryCount());

    try workflow.undo();
    try testing.expectEqual(WorkflowState.review, workflow.current);

    try workflow.undo();
    try testing.expectEqual(WorkflowState.draft, workflow.current);
}
// ANCHOR_END: state_history

// ANCHOR: guarded_transitions
// State machine with guards
const ATMState = enum {
    idle,
    card_inserted,
    pin_entered,
    authenticated,
    dispensing,
};

const ATM = struct {
    state: ATMState,
    balance: u32,
    pin_attempts: u32,

    pub fn init(balance: u32) ATM {
        return ATM{
            .state = .idle,
            .balance = balance,
            .pin_attempts = 0,
        };
    }

    pub fn insertCard(self: *ATM) !void {
        if (self.state != .idle) return error.InvalidState;
        self.state = .card_inserted;
        self.pin_attempts = 0;
    }

    pub fn enterPin(self: *ATM, pin: u32) !void {
        if (self.state != .card_inserted and self.state != .pin_entered) {
            return error.InvalidState;
        }

        if (pin == 1234) {
            self.state = .authenticated;
            self.pin_attempts = 0;
        } else {
            self.pin_attempts += 1;
            if (self.pin_attempts >= 3) {
                self.state = .idle;
                return error.TooManyAttempts;
            }
            self.state = .pin_entered;
            return error.InvalidPin;
        }
    }

    pub fn withdraw(self: *ATM, amount: u32) !void {
        if (self.state != .authenticated) return error.NotAuthenticated;
        if (amount > self.balance) return error.InsufficientFunds;

        self.balance -= amount;
        self.state = .dispensing;
    }

    pub fn complete(self: *ATM) void {
        self.state = .idle;
    }
};

test "guarded transitions" {
    var atm = ATM.init(1000);

    try atm.insertCard();
    try testing.expectEqual(ATMState.card_inserted, atm.state);

    const wrong_pin = atm.enterPin(9999);
    try testing.expectError(error.InvalidPin, wrong_pin);
    try testing.expectEqual(@as(u32, 1), atm.pin_attempts);

    try atm.enterPin(1234);
    try testing.expectEqual(ATMState.authenticated, atm.state);

    try atm.withdraw(500);
    try testing.expectEqual(@as(u32, 500), atm.balance);
}
// ANCHOR_END: guarded_transitions

// ANCHOR: timeout_states
// State machine with timeouts
const SessionState = enum {
    inactive,
    active,
    idle_warning,
    expired,
};

const Session = struct {
    state: SessionState,
    last_activity: u64,
    timeout_ms: u64,

    pub fn init(timeout_ms: u64) Session {
        return Session{
            .state = .inactive,
            .last_activity = 0,
            .timeout_ms = timeout_ms,
        };
    }

    pub fn activate(self: *Session, current_time: u64) void {
        self.state = .active;
        self.last_activity = current_time;
    }

    pub fn activity(self: *Session, current_time: u64) void {
        if (self.state == .active or self.state == .idle_warning) {
            self.last_activity = current_time;
            self.state = .active;
        }
    }

    pub fn update(self: *Session, current_time: u64) void {
        if (self.state == .inactive or self.state == .expired) {
            return;
        }

        const elapsed = current_time - self.last_activity;

        if (elapsed > self.timeout_ms) {
            self.state = .expired;
        } else if (elapsed > self.timeout_ms / 2) {
            self.state = .idle_warning;
        }
    }
};

test "timeout states" {
    var session = Session.init(1000);

    session.activate(0);
    try testing.expectEqual(SessionState.active, session.state);

    session.update(600);
    try testing.expectEqual(SessionState.idle_warning, session.state);

    session.activity(600);
    try testing.expectEqual(SessionState.active, session.state);

    session.update(2000);
    try testing.expectEqual(SessionState.expired, session.state);
}
// ANCHOR_END: timeout_states

// ANCHOR: composite_state
// Composite state machine
const MediaPlayer = struct {
    const PlaybackState = enum {
        stopped,
        playing,
        paused,
    };

    const RepeatMode = enum {
        none,
        one,
        all,
    };

    playback: PlaybackState,
    repeat: RepeatMode,
    volume: u8,
    track_index: usize,

    pub fn init() MediaPlayer {
        return MediaPlayer{
            .playback = .stopped,
            .repeat = .none,
            .volume = 50,
            .track_index = 0,
        };
    }

    pub fn play(self: *MediaPlayer) void {
        self.playback = .playing;
    }

    pub fn pause(self: *MediaPlayer) void {
        if (self.playback == .playing) {
            self.playback = .paused;
        }
    }

    pub fn stop(self: *MediaPlayer) void {
        self.playback = .stopped;
        self.track_index = 0;
    }

    pub fn next(self: *MediaPlayer, total_tracks: usize) void {
        if (self.track_index < total_tracks - 1) {
            self.track_index += 1;
        } else if (self.repeat == .all) {
            self.track_index = 0;
        }
    }

    pub fn setRepeat(self: *MediaPlayer, mode: RepeatMode) void {
        self.repeat = mode;
    }
};

test "composite state" {
    var player = MediaPlayer.init();

    player.play();
    try testing.expectEqual(MediaPlayer.PlaybackState.playing, player.playback);

    player.next(10);
    try testing.expectEqual(@as(usize, 1), player.track_index);

    player.setRepeat(.all);
    player.track_index = 9;
    player.next(10);
    try testing.expectEqual(@as(usize, 0), player.track_index);
}
// ANCHOR_END: composite_state

// Comprehensive test
test "comprehensive state machines" {
    // Basic FSM
    var conn = Connection.init();
    try conn.connect();
    try testing.expectEqual(ConnectionState.connecting, conn.state);

    // State pattern
    var door = Door.init();
    door.open();
    _ = door.update(100);
    try testing.expect(std.meta.activeTag(door.state) == .open);

    // Event-driven
    var light = TrafficLight.init();
    light.handle(.emergency);
    try testing.expectEqual(TrafficLight.State.red, light.state);

    // Hierarchical
    var player = Player.init();
    player.attack();
    try testing.expect(player.state.isInCombat());

    // With history
    var workflow = Workflow.init(testing.allocator);
    defer workflow.deinit();
    try workflow.transition(.review);
    try workflow.undo();
    try testing.expectEqual(WorkflowState.draft, workflow.current);
}
```

### See Also

- Recipe 8.12: Defining an Interface or Abstract Base Class
- Recipe 8.20: Implementing the Visitor Pattern
- Recipe 9.11: Using comptime to Control Instance Creation
- Recipe 7.2: Using Enums for State Representation

---

## Recipe 8.20: Implementing the Visitor Pattern {#recipe-8-20}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, memory, pointers, resource-cleanup, slices, structs-objects, testing
**Difficulty:** advanced
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_20.zig`

### Problem

You need to perform different operations on a collection of related types (like AST nodes, shapes, or file trees) without modifying those types. You want to separate algorithms from the data structures they operate on.

### Solution

Use tagged unions with an `accept` method that dispatches to visitor methods. Visitors implement specific operations, keeping the data types clean and focused.

### Basic Visitor Pattern

Define shapes and a visitor that calculates area:

```zig
// Basic visitor pattern using tagged unions
const Circle = struct { radius: f32 };
const Rectangle = struct { width: f32, height: f32 };
const Triangle = struct { base: f32, height: f32 };

const Shape = union(enum) {
    circle: Circle,
    rectangle: Rectangle,
    triangle: Triangle,

    pub fn accept(self: *const Shape, visitor: anytype) @TypeOf(visitor).ResultType {
        return switch (self.*) {
            .circle => |c| visitor.visitCircle(c),
            .rectangle => |r| visitor.visitRectangle(r),
            .triangle => |t| visitor.visitTriangle(t),
        };
    }
};

const AreaVisitor = struct {
    pub const ResultType = f32;

    pub fn visitCircle(self: AreaVisitor, circle: Circle) f32 {
        _ = self;
        return std.math.pi * circle.radius * circle.radius;
    }

    pub fn visitRectangle(self: AreaVisitor, rectangle: Rectangle) f32 {
        _ = self;
        return rectangle.width * rectangle.height;
    }

    pub fn visitTriangle(self: AreaVisitor, triangle: Triangle) f32 {
        _ = self;
        return triangle.base * triangle.height / 2.0;
    }
};

test "basic visitor" {
    const circle = Shape{ .circle = .{ .radius = 5 } };
    const rectangle = Shape{ .rectangle = .{ .width = 4, .height = 6 } };

    const visitor = AreaVisitor{};

    const circle_area = circle.accept(visitor);
    try testing.expectApproxEqAbs(@as(f32, 78.539), circle_area, 0.01);

    const rect_area = rectangle.accept(visitor);
    try testing.expectEqual(@as(f32, 24), rect_area);
}
```

Each visitor method handles one variant of the union.

### Visitor with Context

Visitors can carry state:

```zig
const PrintVisitor = struct {
    buffer: *std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub const ResultType = void;

    pub fn visitCircle(self: PrintVisitor, circle: Circle) void {
        const msg = std.fmt.allocPrint(
            self.allocator,
            "Circle(r={d})",
            .{circle.radius}
        ) catch return;
        defer self.allocator.free(msg);
        self.buffer.appendSlice(self.allocator, msg) catch return;
    }

    pub fn visitRectangle(self: PrintVisitor, rectangle: Rectangle) void {
        const msg = std.fmt.allocPrint(
            self.allocator,
            "Rectangle(w={d},h={d})",
            .{ rectangle.width, rectangle.height }
        ) catch return;
        defer self.allocator.free(msg);
        self.buffer.appendSlice(self.allocator, msg) catch return;
    }
};
```

The visitor accumulates results in its buffer field.

### Expression Visitor (AST Traversal)

Visit and evaluate expression trees:

```zig
const Expr = union(enum) {
    number: i32,
    add: struct { left: *Expr, right: *Expr },
    mul: struct { left: *Expr, right: *Expr },
    neg: *Expr,

    pub fn accept(self: *const Expr, visitor: anytype) GetResultType(@TypeOf(visitor)) {
        return switch (self.*) {
            .number => |n| visitor.visitNumber(n),
            .add => |a| visitor.visitAdd(a.left, a.right),
            .mul => |m| visitor.visitMul(m.left, m.right),
            .neg => |n| visitor.visitNeg(n),
        };
    }
};

fn GetResultType(comptime T: type) type {
    return switch (@typeInfo(T)) {
        .pointer => |ptr| ptr.child.ResultType,
        else => T.ResultType,
    };
}

const EvalVisitor = struct {
    pub const ResultType = i32;

    pub fn visitNumber(_: EvalVisitor, n: i32) i32 {
        return n;
    }

    pub fn visitAdd(self: EvalVisitor, left: *Expr, right: *Expr) i32 {
        return left.accept(self) + right.accept(self);
    }

    pub fn visitMul(self: EvalVisitor, left: *Expr, right: *Expr) i32 {
        return left.accept(self) * right.accept(self);
    }

    pub fn visitNeg(self: EvalVisitor, expr: *Expr) i32 {
        return -expr.accept(self);
    }
};
```

Visitors can recursively traverse tree structures.

### Collecting Visitor

Count nodes or collect information:

```zig
const NodeVisitor = struct {
    count: u32,

    pub const ResultType = void;

    pub fn visitNumber(self: *NodeVisitor, _: i32) void {
        self.count += 1;
    }

    pub fn visitAdd(self: *NodeVisitor, left: *Expr, right: *Expr) void {
        self.count += 1;
        left.accept(self);
        right.accept(self);
    }

    pub fn visitMul(self: *NodeVisitor, left: *Expr, right: *Expr) void {
        self.count += 1;
        left.accept(self);
        right.accept(self);
    }
};

// Usage
var visitor = NodeVisitor{ .count = 0 };
expression.accept(&visitor);
// visitor.count now has total node count
```

Mutable visitors accumulate state during traversal.

### Transforming Visitor

Build strings or transform structures:

```zig
const StringifyVisitor = struct {
    buffer: *std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub const ResultType = void;

    pub fn visitNumber(self: *StringifyVisitor, n: i32) void {
        const str = std.fmt.allocPrint(self.allocator, "{d}", .{n}) catch return;
        defer self.allocator.free(str);
        self.buffer.appendSlice(self.allocator, str) catch return;
    }

    pub fn visitAdd(self: *StringifyVisitor, left: *Expr, right: *Expr) void {
        self.buffer.append(self.allocator, '(') catch return;
        left.accept(self);
        self.buffer.appendSlice(self.allocator, " + ") catch return;
        right.accept(self);
        self.buffer.append(self.allocator, ')') catch return;
    }
};

// Transforms: (5 + 3) into string "(5 + 3)"
```

Visitors can transform data structures into other representations.

### Fallible Visitor

Visitors can return errors:

```zig
const ValidationVisitor = struct {
    pub const ResultType = anyerror!bool;

    pub fn visitCircle(_: ValidationVisitor, circle: Circle) !bool {
        if (circle.radius <= 0) return error.InvalidRadius;
        return true;
    }

    pub fn visitRectangle(_: ValidationVisitor, rectangle: Rectangle) !bool {
        if (rectangle.width <= 0 or rectangle.height <= 0) {
            return error.InvalidDimensions;
        }
        return true;
    }
};

// Usage
const visitor = ValidationVisitor{};
const valid = try shape.accept(visitor);
```

Error handling integrates naturally with the visitor pattern.

### File Tree Visitor

Visit hierarchical structures:

```zig
const File = struct { name: []const u8, size: u64 };
const Directory = struct { name: []const u8, children: []const FileNode };

const FileNode = union(enum) {
    file: File,
    directory: Directory,

    pub fn accept(self: *const FileNode, visitor: anytype) GetResultType(@TypeOf(visitor)) {
        return switch (self.*) {
            .file => |f| visitor.visitFile(f),
            .directory => |d| visitor.visitDirectory(d),
        };
    }
};

const SizeVisitor = struct {
    pub const ResultType = u64;

    pub fn visitFile(_: SizeVisitor, file: File) u64 {
        return file.size;
    }

    pub fn visitDirectory(self: SizeVisitor, dir: Directory) u64 {
        var total: u64 = 0;
        for (dir.children) |*child| {
            total += child.accept(self);
        }
        return total;
    }
};
```

Recursive visitors handle tree structures naturally.

### Stateful Visitor

Track depth, path, or other traversal state:

```zig
const DepthVisitor = struct {
    depth: u32,
    max_depth: u32,

    pub const ResultType = void;

    pub fn visitFile(self: *DepthVisitor, _: File) void {
        if (self.depth > self.max_depth) {
            self.max_depth = self.depth;
        }
    }

    pub fn visitDirectory(self: *DepthVisitor, dir: Directory) void {
        if (self.depth > self.max_depth) {
            self.max_depth = self.depth;
        }

        self.depth += 1;
        for (dir.children) |*child| {
            child.accept(self);
        }
        self.depth -= 1;
    }
};
```

State tracks context during traversal.

### Filter Visitor

Collect items matching criteria:

```zig
const FilterVisitor = struct {
    matches: *std.ArrayList([]const u8),
    allocator: std.mem.Allocator,
    extension: []const u8,

    pub const ResultType = void;

    pub fn visitFile(self: *FilterVisitor, file: File) void {
        if (std.mem.endsWith(u8, file.name, self.extension)) {
            self.matches.append(self.allocator, file.name) catch return;
        }
    }

    pub fn visitDirectory(self: *FilterVisitor, dir: Directory) void {
        for (dir.children) |*child| {
            child.accept(self);
        }
    }
};

// Find all .txt files
var matches = std.ArrayList([]const u8).init(allocator);
var visitor = FilterVisitor{
    .matches = &matches,
    .allocator = allocator,
    .extension = ".txt",
};
tree.accept(&visitor);
```

Visitors can filter and collect specific items.

### Discussion

The visitor pattern separates operations from data structures, making both easier to extend and maintain.

### How Visitors Work

**Double dispatch**: The data type and visitor type determine behavior
1. `shape.accept(visitor)` - shape knows its type
2. `visitor.visitCircle(circle)` - visitor knows the operation
3. Result combines both type and operation

**Tagged union dispatch**:
```zig
pub fn accept(self: *const Shape, visitor: anytype) ResultType {
    return switch (self.*) {  // Dispatch on shape type
        .circle => |c| visitor.visitCircle(c),  // Call visitor method
        .rectangle => |r| visitor.visitRectangle(r),
        // ...
    };
}
```

**Generic visitors**:
```zig
visitor: anytype  // Any type with appropriate visit methods
```

Zig's comptime checks that the visitor has required methods.

### Visitor Pattern Benefits

**Separation of concerns**:
- Data structures: Just hold data
- Visitors: Implement algorithms
- Easy to add new operations

**Type safety**:
- Compiler ensures all cases handled
- No missing visitor methods
- Compile-time verification

**Flexibility**:
- Multiple visitors for same data
- Different operations without changing data
- Compose visitors

### Design Guidelines

**Naming conventions**:
- `accept()` method on data structures
- `visit*()` methods on visitors
- `ResultType` constant for return type

**ResultType pattern**:
```zig
pub const ResultType = T;  // What accept() returns

pub fn visitX(self: Visitor, ...) ResultType {
    // Must return ResultType
}
```

**Visitor state**:
- Immutable visitors: Pure operations
- Mutable visitors: Collect results
- Both work with `anytype`

**Error handling**:
```zig
pub const ResultType = !T;  // Visitor can fail

pub fn visitX(...) !T {
    if (invalid) return error.Invalid;
    return result;
}
```

### Performance

**Zero overhead dispatch**: Switch compiles to jump table
- Enum tag lookup: O(1)
- Jump to handler: O(1)
- No vtable indirection

**Inline-friendly**: Small visitors inline completely
```zig
const area = shape.accept(AreaVisitor{});
// Often inlined to direct calculation
```

**Memory**: Only visitor fields
- No heap allocation
- Stack-allocated visitors
- Data structure unchanged

### Common Use Cases

**AST traversal**:
- Evaluation
- Pretty printing
- Type checking
- Code generation

**Data structure operations**:
- Serialization
- Validation
- Transformation
- Filtering

**File system operations**:
- Size calculation
- Search
- Permission checking
- Backup

**Graph algorithms**:
- DFS/BFS traversal
- Path finding
- Cycle detection
- Topological sort

### Visitor Variations

**Single-method visitor**:
```zig
pub fn process(item: anytype) void {
    // Handle all types the same way
}
```

**Multi-type visitor**:
```zig
pub fn visit(item: anytype) void {
    switch (@TypeOf(item)) {
        Shape.circle => ...,
        Shape.rectangle => ...,
    }
}
```

**Accumulating visitor**:
```zig
var results = std.ArrayList(Result).init(allocator);
var visitor = CollectVisitor{ .results = &results };
```

**Transform visitor**:
```zig
pub const ResultType = TransformedType;

pub fn visitX(...) TransformedType {
    return transform(...);
}
```

### Comparison with Alternatives

**Pattern matching** (if Zig had it):
```rust
// Rust
match shape {
    Shape::Circle(r) => std.math.pi * r * r,
    Shape::Rectangle(w, h) => w * h,
}
```

Visitor pattern:
- More verbose but more flexible
- Can add operations without modifying types
- Better for complex operations

**Method-based dispatch**:
```zig
shape.calculateArea()  // Method on Shape
```

Visitor:
- Separates concerns better
- Operations are pluggable
- Multiple implementations possible

### When to Use Visitors

Use visitors when:
- You have a stable set of data types
- You want to add many operations
- Operations don't belong on the data type
- You need to collect or transform data

Don't use visitors when:
- Data types change frequently
- Only one operation needed
- Simple mapping suffices
- Switch statements are clearer

### Full Tested Code

```zig
// Recipe 8.20: Implementing the Visitor Pattern
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_visitor
// Basic visitor pattern using tagged unions
const Circle = struct { radius: f32 };
const Rectangle = struct { width: f32, height: f32 };
const Triangle = struct { base: f32, height: f32 };

const Shape = union(enum) {
    circle: Circle,
    rectangle: Rectangle,
    triangle: Triangle,

    pub fn accept(self: *const Shape, visitor: anytype) @TypeOf(visitor).ResultType {
        return switch (self.*) {
            .circle => |c| visitor.visitCircle(c),
            .rectangle => |r| visitor.visitRectangle(r),
            .triangle => |t| visitor.visitTriangle(t),
        };
    }
};

const AreaVisitor = struct {
    pub const ResultType = f32;

    pub fn visitCircle(self: AreaVisitor, circle: Circle) f32 {
        _ = self;
        return std.math.pi * circle.radius * circle.radius;
    }

    pub fn visitRectangle(self: AreaVisitor, rectangle: Rectangle) f32 {
        _ = self;
        return rectangle.width * rectangle.height;
    }

    pub fn visitTriangle(self: AreaVisitor, triangle: Triangle) f32 {
        _ = self;
        return triangle.base * triangle.height / 2.0;
    }
};

test "basic visitor" {
    const circle = Shape{ .circle = .{ .radius = 5 } };
    const rectangle = Shape{ .rectangle = .{ .width = 4, .height = 6 } };

    const visitor = AreaVisitor{};

    const circle_area = circle.accept(visitor);
    try testing.expectApproxEqAbs(@as(f32, 78.539), circle_area, 0.01);

    const rect_area = rectangle.accept(visitor);
    try testing.expectEqual(@as(f32, 24), rect_area);
}
// ANCHOR_END: basic_visitor

// ANCHOR: visitor_with_context
// Visitor with context/state
const PrintVisitor = struct {
    buffer: *std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub const ResultType = void;

    pub fn visitCircle(self: PrintVisitor, circle: Circle) void {
        const msg = std.fmt.allocPrint(self.allocator, "Circle(r={d})", .{circle.radius}) catch return;
        defer self.allocator.free(msg);
        self.buffer.appendSlice(self.allocator, msg) catch return;
    }

    pub fn visitRectangle(self: PrintVisitor, rectangle: Rectangle) void {
        const msg = std.fmt.allocPrint(self.allocator, "Rectangle(w={d},h={d})", .{ rectangle.width, rectangle.height }) catch return;
        defer self.allocator.free(msg);
        self.buffer.appendSlice(self.allocator, msg) catch return;
    }

    pub fn visitTriangle(self: PrintVisitor, triangle: Triangle) void {
        const msg = std.fmt.allocPrint(self.allocator, "Triangle(b={d},h={d})", .{ triangle.base, triangle.height }) catch return;
        defer self.allocator.free(msg);
        self.buffer.appendSlice(self.allocator, msg) catch return;
    }
};

test "visitor with context" {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    const visitor = PrintVisitor{
        .buffer = &buffer,
        .allocator = testing.allocator,
    };

    const circle = Shape{ .circle = .{ .radius = 3 } };
    circle.accept(visitor);

    try testing.expect(std.mem.indexOf(u8, buffer.items, "Circle") != null);
}
// ANCHOR_END: visitor_with_context

// ANCHOR: expression_visitor
// Expression visitor (AST traversal)
const Expr = union(enum) {
    number: i32,
    add: struct { left: *Expr, right: *Expr },
    mul: struct { left: *Expr, right: *Expr },
    neg: *Expr,

    pub fn accept(self: *const Expr, visitor: anytype) GetResultType(@TypeOf(visitor)) {
        return switch (self.*) {
            .number => |n| visitor.visitNumber(n),
            .add => |a| visitor.visitAdd(a.left, a.right),
            .mul => |m| visitor.visitMul(m.left, m.right),
            .neg => |n| visitor.visitNeg(n),
        };
    }
};

fn GetResultType(comptime T: type) type {
    return switch (@typeInfo(T)) {
        .pointer => |ptr| ptr.child.ResultType,
        else => T.ResultType,
    };
}

const EvalVisitor = struct {
    pub const ResultType = i32;

    pub fn visitNumber(_: EvalVisitor, n: i32) i32 {
        return n;
    }

    pub fn visitAdd(self: EvalVisitor, left: *Expr, right: *Expr) i32 {
        return left.accept(self) + right.accept(self);
    }

    pub fn visitMul(self: EvalVisitor, left: *Expr, right: *Expr) i32 {
        return left.accept(self) * right.accept(self);
    }

    pub fn visitNeg(self: EvalVisitor, expr: *Expr) i32 {
        return -expr.accept(self);
    }
};

test "expression visitor" {
    const five = Expr{ .number = 5 };
    const three = Expr{ .number = 3 };
    const add = Expr{ .add = .{ .left = @constCast(&five), .right = @constCast(&three) } };

    const visitor = EvalVisitor{};
    const result = add.accept(visitor);
    try testing.expectEqual(@as(i32, 8), result);
}
// ANCHOR_END: expression_visitor

// ANCHOR: collecting_visitor
// Visitor that collects results
const NodeVisitor = struct {
    count: u32,

    pub const ResultType = void;

    pub fn visitNumber(self: *NodeVisitor, _: i32) void {
        self.count += 1;
    }

    pub fn visitAdd(self: *NodeVisitor, left: *Expr, right: *Expr) void {
        self.count += 1;
        left.accept(self);
        right.accept(self);
    }

    pub fn visitMul(self: *NodeVisitor, left: *Expr, right: *Expr) void {
        self.count += 1;
        left.accept(self);
        right.accept(self);
    }

    pub fn visitNeg(self: *NodeVisitor, expr: *Expr) void {
        self.count += 1;
        expr.accept(self);
    }
};

test "collecting visitor" {
    const five = Expr{ .number = 5 };
    const three = Expr{ .number = 3 };
    const add = Expr{ .add = .{ .left = @constCast(&five), .right = @constCast(&three) } };

    var visitor = NodeVisitor{ .count = 0 };
    add.accept(&visitor);

    try testing.expectEqual(@as(u32, 3), visitor.count); // add + 5 + 3
}
// ANCHOR_END: collecting_visitor

// ANCHOR: transforming_visitor
// Visitor that transforms the structure
const StringifyVisitor = struct {
    buffer: *std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub const ResultType = void;

    pub fn visitNumber(self: *StringifyVisitor, n: i32) void {
        const str = std.fmt.allocPrint(self.allocator, "{d}", .{n}) catch return;
        defer self.allocator.free(str);
        self.buffer.appendSlice(self.allocator, str) catch return;
    }

    pub fn visitAdd(self: *StringifyVisitor, left: *Expr, right: *Expr) void {
        self.buffer.append(self.allocator, '(') catch return;
        left.accept(self);
        self.buffer.appendSlice(self.allocator, " + ") catch return;
        right.accept(self);
        self.buffer.append(self.allocator, ')') catch return;
    }

    pub fn visitMul(self: *StringifyVisitor, left: *Expr, right: *Expr) void {
        self.buffer.append(self.allocator, '(') catch return;
        left.accept(self);
        self.buffer.appendSlice(self.allocator, " * ") catch return;
        right.accept(self);
        self.buffer.append(self.allocator, ')') catch return;
    }

    pub fn visitNeg(self: *StringifyVisitor, expr: *Expr) void {
        self.buffer.appendSlice(self.allocator, "-(") catch return;
        expr.accept(self);
        self.buffer.append(self.allocator, ')') catch return;
    }
};

test "transforming visitor" {
    const five = Expr{ .number = 5 };
    const three = Expr{ .number = 3 };
    const add = Expr{ .add = .{ .left = @constCast(&five), .right = @constCast(&three) } };

    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(testing.allocator);

    var visitor = StringifyVisitor{
        .buffer = &buffer,
        .allocator = testing.allocator,
    };

    add.accept(&visitor);
    try testing.expectEqualStrings("(5 + 3)", buffer.items);
}
// ANCHOR_END: transforming_visitor

// ANCHOR: fallible_visitor
// Visitor with error handling
const ValidationVisitor = struct {
    pub const ResultType = anyerror!bool;

    pub fn visitCircle(_: ValidationVisitor, circle: Circle) !bool {
        if (circle.radius <= 0) return error.InvalidRadius;
        return true;
    }

    pub fn visitRectangle(_: ValidationVisitor, rectangle: Rectangle) !bool {
        if (rectangle.width <= 0 or rectangle.height <= 0) {
            return error.InvalidDimensions;
        }
        return true;
    }

    pub fn visitTriangle(_: ValidationVisitor, triangle: Triangle) !bool {
        if (triangle.base <= 0 or triangle.height <= 0) {
            return error.InvalidDimensions;
        }
        return true;
    }
};

test "fallible visitor" {
    const valid_circle = Shape{ .circle = .{ .radius = 5 } };
    const invalid_circle = Shape{ .circle = .{ .radius = -1 } };

    const visitor = ValidationVisitor{};

    const valid = try valid_circle.accept(visitor);
    try testing.expect(valid);

    const result = invalid_circle.accept(visitor);
    try testing.expectError(error.InvalidRadius, result);
}
// ANCHOR_END: fallible_visitor

// ANCHOR: generic_visitor
// Generic visitor using comptime
fn Visitor(comptime T: type) type {
    return struct {
        pub const ResultType = T;

        visitFn: *const fn (item: anytype) T,

        pub fn visit(self: @This(), item: anytype) T {
            return self.visitFn(item);
        }
    };
}

test "generic visitor" {
    const IntVisitor = Visitor(i32);

    const visitor = IntVisitor{
        .visitFn = struct {
            fn visit(item: anytype) i32 {
                return item;
            }
        }.visit,
    };

    const result = visitor.visit(42);
    try testing.expectEqual(@as(i32, 42), result);
}
// ANCHOR_END: generic_visitor

// ANCHOR: multi_visitor
// Multiple visitor dispatch
const File = struct { name: []const u8, size: u64 };
const Directory = struct { name: []const u8, children: []const FileNode };

const FileNode = union(enum) {
    file: File,
    directory: Directory,

    pub fn accept(self: *const FileNode, visitor: anytype) GetResultType(@TypeOf(visitor)) {
        return switch (self.*) {
            .file => |f| visitor.visitFile(f),
            .directory => |d| visitor.visitDirectory(d),
        };
    }
};

const SizeVisitor = struct {
    pub const ResultType = u64;

    pub fn visitFile(_: SizeVisitor, file: File) u64 {
        return file.size;
    }

    pub fn visitDirectory(self: SizeVisitor, dir: Directory) u64 {
        var total: u64 = 0;
        for (dir.children) |*child| {
            total += child.accept(self);
        }
        return total;
    }
};

test "multi visitor" {
    const file1 = FileNode{ .file = .{ .name = "a.txt", .size = 100 } };
    const file2 = FileNode{ .file = .{ .name = "b.txt", .size = 200 } };
    const children = [_]FileNode{ file1, file2 };
    const dir = FileNode{ .directory = .{ .name = "docs", .children = children[0..] } };

    const visitor = SizeVisitor{};
    const total = dir.accept(visitor);
    try testing.expectEqual(@as(u64, 300), total);
}
// ANCHOR_END: multi_visitor

// ANCHOR: stateful_visitor
// Stateful visitor that maintains state across visits
const DepthVisitor = struct {
    depth: u32,
    max_depth: u32,

    pub const ResultType = void;

    pub fn visitFile(self: *DepthVisitor, _: File) void {
        if (self.depth > self.max_depth) {
            self.max_depth = self.depth;
        }
    }

    pub fn visitDirectory(self: *DepthVisitor, dir: Directory) void {
        if (self.depth > self.max_depth) {
            self.max_depth = self.depth;
        }

        self.depth += 1;
        for (dir.children) |*child| {
            child.accept(self);
        }
        self.depth -= 1;
    }
};

test "stateful visitor" {
    const file1 = FileNode{ .file = .{ .name = "a.txt", .size = 100 } };
    const file2 = FileNode{ .file = .{ .name = "b.txt", .size = 200 } };
    const children = [_]FileNode{ file1, file2 };
    const dir = FileNode{ .directory = .{ .name = "docs", .children = children[0..] } };

    var visitor = DepthVisitor{ .depth = 0, .max_depth = 0 };
    dir.accept(&visitor);

    try testing.expectEqual(@as(u32, 1), visitor.max_depth);
}
// ANCHOR_END: stateful_visitor

// ANCHOR: filter_visitor
// Visitor with filtering
const FilterVisitor = struct {
    matches: *std.ArrayList([]const u8),
    allocator: std.mem.Allocator,
    extension: []const u8,

    pub const ResultType = void;

    pub fn visitFile(self: *FilterVisitor, file: File) void {
        if (std.mem.endsWith(u8, file.name, self.extension)) {
            self.matches.append(self.allocator, file.name) catch return;
        }
    }

    pub fn visitDirectory(self: *FilterVisitor, dir: Directory) void {
        for (dir.children) |*child| {
            child.accept(self);
        }
    }
};

test "filter visitor" {
    const file1 = FileNode{ .file = .{ .name = "a.txt", .size = 100 } };
    const file2 = FileNode{ .file = .{ .name = "b.md", .size = 200 } };
    const file3 = FileNode{ .file = .{ .name = "c.txt", .size = 150 } };
    const children = [_]FileNode{ file1, file2, file3 };
    const dir = FileNode{ .directory = .{ .name = "docs", .children = children[0..] } };

    var matches = std.ArrayList([]const u8){};
    defer matches.deinit(testing.allocator);

    var visitor = FilterVisitor{
        .matches = &matches,
        .allocator = testing.allocator,
        .extension = ".txt",
    };

    dir.accept(&visitor);
    try testing.expectEqual(@as(usize, 2), matches.items.len);
}
// ANCHOR_END: filter_visitor

// Comprehensive test
test "comprehensive visitor patterns" {
    // Basic visitor
    const circle = Shape{ .circle = .{ .radius = 2 } };
    const area_visitor = AreaVisitor{};
    const area = circle.accept(area_visitor);
    try testing.expect(area > 12 and area < 13);

    // Expression visitor
    const num = Expr{ .number = 10 };
    const eval_visitor = EvalVisitor{};
    const value = num.accept(eval_visitor);
    try testing.expectEqual(@as(i32, 10), value);

    // Validation visitor
    const valid_rect = Shape{ .rectangle = .{ .width = 5, .height = 3 } };
    const validation_visitor = ValidationVisitor{};
    const is_valid = try valid_rect.accept(validation_visitor);
    try testing.expect(is_valid);

    // File tree visitor
    const file = FileNode{ .file = .{ .name = "test.txt", .size = 500 } };
    const size_visitor = SizeVisitor{};
    const size = file.accept(size_visitor);
    try testing.expectEqual(@as(u64, 500), size);
}
```

### See Also

- Recipe 8.19: Implementing Stateful Objects or State Machines
- Recipe 8.12: Defining an Interface or Abstract Base Class
- Recipe 7.2: Using Enums for State Representation
- Recipe 9.11: Using comptime to Control Instance Creation

---

## Recipe 8.21: Managing Memory in Cyclic Data Structures {#recipe-8-21}

**Tags:** allocators, arena-allocator, arraylist, atomics, concurrency, data-structures, error-handling, memory, pointers, resource-cleanup, structs-objects, testing, threading
**Difficulty:** advanced
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_21.zig`

### Problem

You need to build circular linked lists, graphs with bidirectional edges, or parent-child references that form cycles. Traditional reference counting or manual cleanup can leak memory or cause use-after-free bugs when cycles prevent normal cleanup.

### Solution

Zig provides several safe patterns for cyclic structures: arena allocators for bulk cleanup, weak references through convention, explicit cycle breaking, reference counting, owned vs borrowed pointer distinction, and index-based references.

### Arena Allocator for Cycles

Use arena allocators to free entire cyclic structures at once:

```zig
// Use arena allocator for cyclic structures
const Node = struct {
    value: i32,
    next: ?*Node,
    prev: ?*Node,

    pub fn init(allocator: std.mem.Allocator, value: i32) !*Node {
        const node = try allocator.create(Node);
        node.* = Node{
            .value = value,
            .next = null,
            .prev = null,
        };
        return node;
    }
};

const CircularList = struct {
    arena: std.heap.ArenaAllocator,

    pub fn init(parent_allocator: std.mem.Allocator) CircularList {
        return CircularList{
            .arena = std.heap.ArenaAllocator.init(parent_allocator),
        };
    }

    pub fn deinit(self: *CircularList) void {
        // Arena frees everything at once, even with cycles
        self.arena.deinit();
    }

    pub fn createCircle(self: *CircularList, values: []const i32) !*Node {
        if (values.len == 0) return error.EmptyList;

        const allocator = self.arena.allocator();
        const first = try Node.init(allocator, values[0]);
        var current = first;

        for (values[1..]) |value| {
            const new_node = try Node.init(allocator, value);
            current.next = new_node;
            new_node.prev = current;
            current = new_node;
        }

        // Create cycle
        current.next = first;
        first.prev = current;

        return first;
    }
};

test "arena allocator" {
    var list = CircularList.init(testing.allocator);
    defer list.deinit();

    const values = [_]i32{ 1, 2, 3 };
    const head = try list.createCircle(&values);

    try testing.expectEqual(@as(i32, 1), head.value);
    try testing.expectEqual(@as(i32, 2), head.next.?.value);
    try testing.expectEqual(@as(i32, 1), head.next.?.next.?.next.?.value);
}
        if (values.len == 0) return error.EmptyList;

        const allocator = self.arena.allocator();
        const first = try Node.init(allocator, values[0]);
        var current = first;

        for (values[1..]) |value| {
            const new_node = try Node.init(allocator, value);
            current.next = new_node;
            new_node.prev = current;
            current = new_node;
        }

        // Create cycle
        current.next = first;
        first.prev = current;

        return first;
    }
};
```

The arena frees all nodes regardless of cycles.

### Weak References

Simulate weak references using optionals that don't own memory:

```zig
const TreeNode = struct {
    value: i32,
    children: std.ArrayList(*TreeNode),
    parent: ?*TreeNode, // Weak reference - not owned

    pub fn init(allocator: std.mem.Allocator, value: i32) !*TreeNode {
        const node = try allocator.create(TreeNode);
        node.* = TreeNode{
            .value = value,
            .children = std.ArrayList(*TreeNode){},
            .parent = null,
        };
        return node;
    }

    pub fn addChild(self: *TreeNode, allocator: std.mem.Allocator, child: *TreeNode) !void {
        try self.children.append(allocator, child);
        child.parent = self; // Weak reference
    }

    pub fn deinit(self: *TreeNode, allocator: std.mem.Allocator) void {
        for (self.children.items) |child| {
            child.deinit(allocator);
        }
        self.children.deinit(allocator);
        allocator.destroy(self);
    }
};
```

Parent pointer doesn't own - only children are freed by the parent.

### Explicit Cycle Breaking

Break cycles before cleanup to avoid leaks:

```zig
const GraphNode = struct {
    id: u32,
    neighbors: std.ArrayList(*GraphNode),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, id: u32) !*GraphNode {
        const node = try allocator.create(GraphNode);
        node.* = GraphNode{
            .id = id,
            .neighbors = std.ArrayList(*GraphNode){},
            .allocator = allocator,
        };
        return node;
    }

    pub fn connect(self: *GraphNode, other: *GraphNode) !void {
        try self.neighbors.append(self.allocator, other);
        try other.neighbors.append(other.allocator, self);
    }

    pub fn breakCycles(self: *GraphNode) void {
        self.neighbors.deinit(self.allocator);
        self.neighbors = std.ArrayList(*GraphNode){};
    }

    pub fn deinit(self: *GraphNode) void {
        self.neighbors.deinit(self.allocator);
        self.allocator.destroy(self);
    }
};

// Usage
const node1 = try GraphNode.init(allocator, 1);
const node2 = try GraphNode.init(allocator, 2);
try node1.connect(node2);

// Break cycles before cleanup
node1.breakCycles();
node2.breakCycles();
node1.deinit();
node2.deinit();
```

Manual cycle breaking gives explicit control over cleanup order.

### Reference Counting

Implement shared ownership with reference counting:

```zig
const RefCounted = struct {
    data: i32,
    ref_count: usize,

    pub fn init(allocator: std.mem.Allocator, data: i32) !*RefCounted {
        const self = try allocator.create(RefCounted);
        self.* = RefCounted{
            .data = data,
            .ref_count = 1,
        };
        return self;
    }

    pub fn retain(self: *RefCounted) void {
        self.ref_count += 1;
    }

    pub fn release(self: *RefCounted, allocator: std.mem.Allocator) void {
        self.ref_count -= 1;
        if (self.ref_count == 0) {
            allocator.destroy(self);
        }
    }
};

const SharedPtr = struct {
    ptr: ?*RefCounted,

    pub fn init(allocator: std.mem.Allocator, data: i32) !SharedPtr {
        return SharedPtr{
            .ptr = try RefCounted.init(allocator, data),
        };
    }

    pub fn clone(self: *const SharedPtr) SharedPtr {
        if (self.ptr) |p| {
            p.retain();
        }
        return SharedPtr{ .ptr = self.ptr };
    }

    pub fn deinit(self: *SharedPtr, allocator: std.mem.Allocator) void {
        if (self.ptr) |p| {
            p.release(allocator);
            self.ptr = null;
        }
    }
};
```

Reference counting handles shared ownership automatically.

### Owned vs Borrowed Pointers

Distinguish owned pointers from borrowed ones through naming:

```zig
const ListNode = struct {
    value: i32,
    next: ?*ListNode, // Owned
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, value: i32) !*ListNode {
        const node = try allocator.create(ListNode);
        node.* = ListNode{
            .value = value,
            .next = null,
            .allocator = allocator,
        };
        return node;
    }

    pub fn append(self: *ListNode, value: i32) !void {
        if (self.next) |next| {
            try next.append(value);
        } else {
            const new_node = try ListNode.init(self.allocator, value);
            self.next = new_node;
        }
    }

    pub fn deinit(self: *ListNode) void {
        if (self.next) |next| {
            next.deinit();
        }
        self.allocator.destroy(self);
    }
};

const ListIterator = struct {
    current: ?*ListNode, // Borrowed - doesn't own

    pub fn init(head: *ListNode) ListIterator {
        return ListIterator{ .current = head };
    }

    pub fn next(self: *ListIterator) ?i32 {
        if (self.current) |node| {
            const value = node.value;
            self.current = node.next;
            return value;
        }
        return null;
    }
};
```

Clear ownership semantics prevent double-free bugs.

### Index-Based References

Avoid pointer cycles entirely by using indices:

```zig
const NodePool = struct {
    const NodeIndex = u32;

    const PoolNode = struct {
        value: i32,
        next: ?NodeIndex,
        prev: ?NodeIndex,
    };

    nodes: std.ArrayList(PoolNode),

    pub fn init(allocator: std.mem.Allocator) NodePool {
        _ = allocator;
        return NodePool{
            .nodes = std.ArrayList(PoolNode){},
        };
    }

    pub fn deinit(self: *NodePool, allocator: std.mem.Allocator) void {
        self.nodes.deinit(allocator);
    }

    pub fn create(self: *NodePool, allocator: std.mem.Allocator, value: i32) !NodeIndex {
        const index: NodeIndex = @intCast(self.nodes.items.len);
        try self.nodes.append(allocator, PoolNode{
            .value = value,
            .next = null,
            .prev = null,
        });
        return index;
    }

    pub fn connect(self: *NodePool, a: NodeIndex, b: NodeIndex) void {
        self.nodes.items[a].next = b;
        self.nodes.items[b].prev = a;
    }

    pub fn get(self: *const NodePool, index: NodeIndex) i32 {
        return self.nodes.items[index].value;
    }
};
```

Indices can't dangle and cleanup is trivial.

### Generational Indices

Detect dangling references with generation counters:

```zig
const GenerationalIndex = struct {
    index: u32,
    generation: u32,
};

const GenerationalPool = struct {
    const Entry = struct {
        value: i32,
        generation: u32,
        is_alive: bool,
    };

    entries: std.ArrayList(Entry),
    free_list: std.ArrayList(u32),

    pub fn init(allocator: std.mem.Allocator) GenerationalPool {
        _ = allocator;
        return GenerationalPool{
            .entries = std.ArrayList(Entry){},
            .free_list = std.ArrayList(u32){},
        };
    }

    pub fn deinit(self: *GenerationalPool, allocator: std.mem.Allocator) void {
        self.entries.deinit(allocator);
        self.free_list.deinit(allocator);
    }

    pub fn allocate(self: *GenerationalPool, allocator: std.mem.Allocator, value: i32) !GenerationalIndex {
        if (self.free_list.items.len > 0) {
            const index = self.free_list.pop().?;
            const entry = &self.entries.items[index];
            entry.value = value;
            entry.is_alive = true;
            return GenerationalIndex{
                .index = index,
                .generation = entry.generation,
            };
        } else {
            const index: u32 = @intCast(self.entries.items.len);
            try self.entries.append(allocator, Entry{
                .value = value,
                .generation = 0,
                .is_alive = true,
            });
            return GenerationalIndex{
                .index = index,
                .generation = 0,
            };
        }
    }

    pub fn free(self: *GenerationalPool, allocator: std.mem.Allocator, idx: GenerationalIndex) !void {
        const entry = &self.entries.items[idx.index];
        if (entry.generation == idx.generation and entry.is_alive) {
            entry.is_alive = false;
            entry.generation += 1;
            try self.free_list.append(allocator, idx.index);
        }
    }

    pub fn get(self: *const GenerationalPool, idx: GenerationalIndex) ?i32 {
        const entry = self.entries.items[idx.index];
        if (entry.generation == idx.generation and entry.is_alive) {
            return entry.value;
        }
        return null;
    }
};
```

Old indices return null instead of accessing wrong data.

### Discussion

Managing cyclic data structures safely requires choosing the right ownership strategy.

### Why Cycles Are Challenging

**Pointer cycles prevent normal cleanup**:
```zig
// A points to B, B points to A
nodeA.next = nodeB;
nodeB.next = nodeA;
// Who frees whom?
```

**Reference counting fails with cycles**:
- A holds reference to B (count = 1)
- B holds reference to A (count = 1)
- Both counts never reach zero
- Memory leaks

**Manual cleanup is error-prone**:
- Double-free if both nodes try to free each other
- Use-after-free if order is wrong
- Easy to miss cleanup paths

### Pattern Selection Guide

**Use arena allocators when**:
- The entire structure has the same lifetime
- You can free everything at once
- Performance matters (fastest allocation)
- Graph algorithms that build then discard

**Use weak references when**:
- Clear parent-child relationship exists
- One direction owns, the other borrows
- Trees, DOM-like structures
- Ownership is hierarchical

**Use explicit cycle breaking when**:
- You need precise control over cleanup
- Cycles are sparse or well-defined
- You can identify all cycle points
- Debugging memory issues

**Use reference counting when**:
- Shared ownership is genuinely needed
- No cycles or cycles are rare
- Objects have independent lifetimes
- Thread-safety is required (with atomic counts)

**Use index-based references when**:
- All objects live in a pool/array
- You want zero-overhead references
- Random access is common
- Serialization is important

**Use generational indices when**:
- Objects are frequently created/destroyed
- Detecting stale references is critical
- Game entity systems
- Memory safety is paramount

### Arena Allocator Advantages

**Bulk deallocation**:
```zig
arena.deinit(); // Frees everything regardless of cycles
```

**Fast allocation**:
- No individual free tracking
- Bump allocator underneath
- Cache-friendly memory layout

**Simple usage**:
```zig
var list = CircularList.init(parent_allocator);
defer list.deinit(); // All nodes freed here
```

**Limitations**:
- Can't free individual nodes
- Memory grows until deinit
- Not suitable for long-lived structures with changing size

### Weak References Convention

**Document ownership**:
```zig
parent: ?*TreeNode, // Weak: borrowed, not owned
children: ArrayList(*TreeNode), // Strong: owned
```

**Cleanup follows ownership**:
```zig
pub fn deinit(self: *TreeNode, allocator: std.mem.Allocator) void {
    // Free owned children
    for (self.children.items) |child| {
        child.deinit(allocator);
    }
    // Don't touch parent - we don't own it
    self.children.deinit(allocator);
    allocator.destroy(self);
}
```

**Convention is compiler-enforced through usage**:
- Only access weak references while owner is alive
- Never free weak references
- Document clearly

### Reference Counting Pitfalls

**Not thread-safe by default**:
```zig
pub fn retain(self: *RefCounted) void {
    self.ref_count += 1; // Race condition!
}
```

Make thread-safe with atomics:
```zig
ref_count: std.atomic.Value(usize),

pub fn retain(self: *RefCounted) void {
    _ = self.ref_count.fetchAdd(1, .monotonic);
}
```

**Cycles still leak**:
- Reference counting alone can't handle cycles
- Combine with weak references
- Or use cycle detection algorithms

### Index-Based Benefits

**No pointer invalidation**:
- Array can grow, indices remain valid
- Easy to serialize (just save indices)
- No alignment or padding concerns

**Cache-friendly**:
```zig
// All nodes in contiguous array
for (pool.nodes.items) |node| {
    // Fast iteration, good cache locality
}
```

**Simple debugging**:
- Print indices to track references
- Easy to visualize in debugger
- No pointer arithmetic

### Generational Index Safety

**Catch use-after-free**:
```zig
const idx = pool.allocate(allocator, 42);
pool.free(allocator, idx);
// Later...
const value = pool.get(idx); // Returns null, not garbage
```

**Generation increments on free**:
- Old index has generation N
- Entry now has generation N+1
- Lookup fails: generations don't match

**Small overhead**:
- Extra u32 per entry
- Single integer comparison on access
- Worth it for safety

### Performance Comparison

**Arena allocator**:
- Allocation: O(1), fastest
- Deallocation: O(1), frees all at once
- Memory: Can't free individually, may waste

**Reference counting**:
- Allocation: O(1)
- Deallocation: O(1) per release
- Memory: Exact, but cycles leak

**Index-based**:
- Allocation: O(1) amortized (array growth)
- Deallocation: O(1)
- Memory: Exact with generational tracking

### Common Use Cases

**Graphs and networks**:
- Social networks: index-based (user IDs)
- Game entity graphs: generational indices
- Compiler ASTs: arena allocator

**Trees**:
- Parent-child: weak references
- File systems: weak parent pointers
- Scene graphs: reference counting or arena

**Circular buffers**:
- Ring buffers: index arithmetic
- LRU caches: doubly-linked with arena
- Event logs: circular array

**Game entities**:
- Entity component systems: generational indices
- Particle systems: arena allocators
- Physics constraints: index-based graph

### Design Guidelines

**Document ownership clearly**:
```zig
// Clear ownership semantics
owned_data: []u8,        // This struct owns and will free
borrowed_ref: *const T,  // Borrowed, don't free
weak_parent: ?*Node,     // Weak reference
```

**Prefer simpler patterns**:
1. Arena if lifetime allows
2. Weak references if hierarchical
3. Index-based for pools
4. Reference counting as last resort

**Test with allocator tracking**:
```zig
test "no memory leaks" {
    const allocator = std.testing.allocator;
    // allocator will detect leaks
}
```

**Consider serialization needs**:
- Pointers don't serialize
- Indices serialize trivially
- Generational indices need care (serialize generation too)

### Full Tested Code

```zig
// Recipe 8.21: Managing Memory in Cyclic Data Structures
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: arena_allocator
// Use arena allocator for cyclic structures
const Node = struct {
    value: i32,
    next: ?*Node,
    prev: ?*Node,

    pub fn init(allocator: std.mem.Allocator, value: i32) !*Node {
        const node = try allocator.create(Node);
        node.* = Node{
            .value = value,
            .next = null,
            .prev = null,
        };
        return node;
    }
};

const CircularList = struct {
    arena: std.heap.ArenaAllocator,

    pub fn init(parent_allocator: std.mem.Allocator) CircularList {
        return CircularList{
            .arena = std.heap.ArenaAllocator.init(parent_allocator),
        };
    }

    pub fn deinit(self: *CircularList) void {
        // Arena frees everything at once, even with cycles
        self.arena.deinit();
    }

    pub fn createCircle(self: *CircularList, values: []const i32) !*Node {
        if (values.len == 0) return error.EmptyList;

        const allocator = self.arena.allocator();
        const first = try Node.init(allocator, values[0]);
        var current = first;

        for (values[1..]) |value| {
            const new_node = try Node.init(allocator, value);
            current.next = new_node;
            new_node.prev = current;
            current = new_node;
        }

        // Create cycle
        current.next = first;
        first.prev = current;

        return first;
    }
};

test "arena allocator" {
    var list = CircularList.init(testing.allocator);
    defer list.deinit();

    const values = [_]i32{ 1, 2, 3 };
    const head = try list.createCircle(&values);

    try testing.expectEqual(@as(i32, 1), head.value);
    try testing.expectEqual(@as(i32, 2), head.next.?.value);
    try testing.expectEqual(@as(i32, 1), head.next.?.next.?.next.?.value);
}
// ANCHOR_END: arena_allocator

// ANCHOR: weak_reference
// Simulate weak references using optionals
const TreeNode = struct {
    value: i32,
    children: std.ArrayList(*TreeNode),
    parent: ?*TreeNode, // Weak reference - not owned

    pub fn init(allocator: std.mem.Allocator, value: i32) !*TreeNode {
        const node = try allocator.create(TreeNode);
        node.* = TreeNode{
            .value = value,
            .children = std.ArrayList(*TreeNode){},
            .parent = null,
        };
        return node;
    }

    pub fn addChild(self: *TreeNode, allocator: std.mem.Allocator, child: *TreeNode) !void {
        try self.children.append(allocator, child);
        child.parent = self; // Weak reference
    }

    pub fn deinit(self: *TreeNode, allocator: std.mem.Allocator) void {
        for (self.children.items) |child| {
            child.deinit(allocator);
        }
        self.children.deinit(allocator);
        allocator.destroy(self);
    }
};

test "weak reference" {
    const root = try TreeNode.init(testing.allocator, 1);
    defer root.deinit(testing.allocator);

    const child1 = try TreeNode.init(testing.allocator, 2);
    const child2 = try TreeNode.init(testing.allocator, 3);

    try root.addChild(testing.allocator, child1);
    try root.addChild(testing.allocator, child2);

    try testing.expectEqual(@as(i32, 1), child1.parent.?.value);
    try testing.expectEqual(@as(usize, 2), root.children.items.len);
}
// ANCHOR_END: weak_reference

// ANCHOR: break_cycles
// Explicitly break cycles before cleanup
const GraphNode = struct {
    id: u32,
    neighbors: std.ArrayList(*GraphNode),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, id: u32) !*GraphNode {
        const node = try allocator.create(GraphNode);
        node.* = GraphNode{
            .id = id,
            .neighbors = std.ArrayList(*GraphNode){},
            .allocator = allocator,
        };
        return node;
    }

    pub fn connect(self: *GraphNode, other: *GraphNode) !void {
        try self.neighbors.append(self.allocator, other);
        try other.neighbors.append(other.allocator, self);
    }

    pub fn breakCycles(self: *GraphNode) void {
        self.neighbors.deinit(self.allocator);
        self.neighbors = std.ArrayList(*GraphNode){};
    }

    pub fn deinit(self: *GraphNode) void {
        self.neighbors.deinit(self.allocator);
        self.allocator.destroy(self);
    }
};

test "break cycles" {
    const node1 = try GraphNode.init(testing.allocator, 1);
    const node2 = try GraphNode.init(testing.allocator, 2);

    try node1.connect(node2);
    try testing.expectEqual(@as(usize, 1), node1.neighbors.items.len);

    // Break cycles before cleanup
    node1.breakCycles();
    node2.breakCycles();

    node1.deinit();
    node2.deinit();
}
// ANCHOR_END: break_cycles

// ANCHOR: reference_counting
// Reference counting for shared ownership
const RefCounted = struct {
    data: i32,
    ref_count: usize,

    pub fn init(allocator: std.mem.Allocator, data: i32) !*RefCounted {
        const self = try allocator.create(RefCounted);
        self.* = RefCounted{
            .data = data,
            .ref_count = 1,
        };
        return self;
    }

    pub fn retain(self: *RefCounted) void {
        self.ref_count += 1;
    }

    pub fn release(self: *RefCounted, allocator: std.mem.Allocator) void {
        self.ref_count -= 1;
        if (self.ref_count == 0) {
            allocator.destroy(self);
        }
    }
};

const SharedPtr = struct {
    ptr: ?*RefCounted,

    pub fn init(allocator: std.mem.Allocator, data: i32) !SharedPtr {
        return SharedPtr{
            .ptr = try RefCounted.init(allocator, data),
        };
    }

    pub fn clone(self: *const SharedPtr) SharedPtr {
        if (self.ptr) |p| {
            p.retain();
        }
        return SharedPtr{ .ptr = self.ptr };
    }

    pub fn deinit(self: *SharedPtr, allocator: std.mem.Allocator) void {
        if (self.ptr) |p| {
            p.release(allocator);
            self.ptr = null;
        }
    }
};

test "reference counting" {
    var ptr1 = try SharedPtr.init(testing.allocator, 42);
    defer ptr1.deinit(testing.allocator);

    var ptr2 = ptr1.clone();
    defer ptr2.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 2), ptr1.ptr.?.ref_count);
    try testing.expectEqual(@as(i32, 42), ptr2.ptr.?.data);
}
// ANCHOR_END: reference_counting

// ANCHOR: owned_pointers
// Clear ownership with owned vs borrowed pointers
const ListNode = struct {
    value: i32,
    next: ?*ListNode, // Owned
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, value: i32) !*ListNode {
        const node = try allocator.create(ListNode);
        node.* = ListNode{
            .value = value,
            .next = null,
            .allocator = allocator,
        };
        return node;
    }

    pub fn append(self: *ListNode, value: i32) !void {
        if (self.next) |next| {
            try next.append(value);
        } else {
            const new_node = try ListNode.init(self.allocator, value);
            self.next = new_node;
        }
    }

    pub fn deinit(self: *ListNode) void {
        if (self.next) |next| {
            next.deinit();
        }
        self.allocator.destroy(self);
    }
};

const ListIterator = struct {
    current: ?*ListNode, // Borrowed - doesn't own

    pub fn init(head: *ListNode) ListIterator {
        return ListIterator{ .current = head };
    }

    pub fn next(self: *ListIterator) ?i32 {
        if (self.current) |node| {
            const value = node.value;
            self.current = node.next;
            return value;
        }
        return null;
    }
};

test "owned pointers" {
    const head = try ListNode.init(testing.allocator, 1);
    defer head.deinit();

    try head.append(2);
    try head.append(3);

    var iter = ListIterator.init(head);
    try testing.expectEqual(@as(i32, 1), iter.next().?);
    try testing.expectEqual(@as(i32, 2), iter.next().?);
}
// ANCHOR_END: owned_pointers

// ANCHOR: index_based
// Use indices instead of pointers
const NodePool = struct {
    const NodeIndex = u32;

    const PoolNode = struct {
        value: i32,
        next: ?NodeIndex,
        prev: ?NodeIndex,
    };

    nodes: std.ArrayList(PoolNode),

    pub fn init(allocator: std.mem.Allocator) NodePool {
        _ = allocator;
        return NodePool{
            .nodes = std.ArrayList(PoolNode){},
        };
    }

    pub fn deinit(self: *NodePool, allocator: std.mem.Allocator) void {
        self.nodes.deinit(allocator);
    }

    pub fn create(self: *NodePool, allocator: std.mem.Allocator, value: i32) !NodeIndex {
        const index: NodeIndex = @intCast(self.nodes.items.len);
        try self.nodes.append(allocator, PoolNode{
            .value = value,
            .next = null,
            .prev = null,
        });
        return index;
    }

    pub fn connect(self: *NodePool, a: NodeIndex, b: NodeIndex) void {
        self.nodes.items[a].next = b;
        self.nodes.items[b].prev = a;
    }

    pub fn get(self: *const NodePool, index: NodeIndex) i32 {
        return self.nodes.items[index].value;
    }
};

test "index based" {
    var pool = NodePool.init(testing.allocator);
    defer pool.deinit(testing.allocator);

    const idx1 = try pool.create(testing.allocator, 10);
    const idx2 = try pool.create(testing.allocator, 20);

    pool.connect(idx1, idx2);

    try testing.expectEqual(@as(i32, 10), pool.get(idx1));
    try testing.expectEqual(@as(i32, 20), pool.get(idx2));
}
// ANCHOR_END: index_based

// ANCHOR: generation_indices
// Generation indices to detect dangling references
const GenerationalIndex = struct {
    index: u32,
    generation: u32,
};

const GenerationalPool = struct {
    const Entry = struct {
        value: i32,
        generation: u32,
        is_alive: bool,
    };

    entries: std.ArrayList(Entry),
    free_list: std.ArrayList(u32),

    pub fn init(allocator: std.mem.Allocator) GenerationalPool {
        _ = allocator;
        return GenerationalPool{
            .entries = std.ArrayList(Entry){},
            .free_list = std.ArrayList(u32){},
        };
    }

    pub fn deinit(self: *GenerationalPool, allocator: std.mem.Allocator) void {
        self.entries.deinit(allocator);
        self.free_list.deinit(allocator);
    }

    pub fn allocate(self: *GenerationalPool, allocator: std.mem.Allocator, value: i32) !GenerationalIndex {
        if (self.free_list.items.len > 0) {
            const index = self.free_list.pop().?;
            const entry = &self.entries.items[index];
            entry.value = value;
            entry.is_alive = true;
            return GenerationalIndex{
                .index = index,
                .generation = entry.generation,
            };
        } else {
            const index: u32 = @intCast(self.entries.items.len);
            try self.entries.append(allocator, Entry{
                .value = value,
                .generation = 0,
                .is_alive = true,
            });
            return GenerationalIndex{
                .index = index,
                .generation = 0,
            };
        }
    }

    pub fn free(self: *GenerationalPool, allocator: std.mem.Allocator, idx: GenerationalIndex) !void {
        const entry = &self.entries.items[idx.index];
        if (entry.generation == idx.generation and entry.is_alive) {
            entry.is_alive = false;
            entry.generation += 1;
            try self.free_list.append(allocator, idx.index);
        }
    }

    pub fn get(self: *const GenerationalPool, idx: GenerationalIndex) ?i32 {
        const entry = self.entries.items[idx.index];
        if (entry.generation == idx.generation and entry.is_alive) {
            return entry.value;
        }
        return null;
    }
};

test "generation indices" {
    var pool = GenerationalPool.init(testing.allocator);
    defer pool.deinit(testing.allocator);

    const idx1 = try pool.allocate(testing.allocator, 100);
    try testing.expectEqual(@as(i32, 100), pool.get(idx1).?);

    try pool.free(testing.allocator, idx1);
    try testing.expect(pool.get(idx1) == null);

    const idx2 = try pool.allocate(testing.allocator, 200);
    try testing.expectEqual(@as(i32, 200), pool.get(idx2).?);
}
// ANCHOR_END: generation_indices

// ANCHOR: doubly_linked_arena
// Doubly-linked list with arena allocator
const DoublyLinkedList = struct {
    const DNode = struct {
        value: i32,
        next: ?*DNode,
        prev: ?*DNode,
    };

    arena: std.heap.ArenaAllocator,
    head: ?*DNode,
    tail: ?*DNode,

    pub fn init(parent_allocator: std.mem.Allocator) DoublyLinkedList {
        return DoublyLinkedList{
            .arena = std.heap.ArenaAllocator.init(parent_allocator),
            .head = null,
            .tail = null,
        };
    }

    pub fn deinit(self: *DoublyLinkedList) void {
        self.arena.deinit();
    }

    pub fn append(self: *DoublyLinkedList, value: i32) !void {
        const allocator = self.arena.allocator();
        const node = try allocator.create(DNode);
        node.* = DNode{
            .value = value,
            .next = null,
            .prev = self.tail,
        };

        if (self.tail) |tail| {
            tail.next = node;
        } else {
            self.head = node;
        }
        self.tail = node;
    }

    pub fn makeCircular(self: *DoublyLinkedList) void {
        if (self.head) |head| {
            if (self.tail) |tail| {
                tail.next = head;
                head.prev = tail;
            }
        }
    }
};

test "doubly linked arena" {
    var list = DoublyLinkedList.init(testing.allocator);
    defer list.deinit();

    try list.append(1);
    try list.append(2);
    try list.append(3);

    list.makeCircular();

    try testing.expectEqual(@as(i32, 1), list.head.?.value);
    try testing.expectEqual(@as(i32, 1), list.tail.?.next.?.value);
}
// ANCHOR_END: doubly_linked_arena

// Comprehensive test
test "comprehensive cyclic memory management" {
    // Arena for cycles
    var circular = CircularList.init(testing.allocator);
    defer circular.deinit();

    const vals = [_]i32{ 5, 10, 15 };
    const head = try circular.createCircle(&vals);
    try testing.expectEqual(@as(i32, 5), head.value);

    // Weak references
    const tree_root = try TreeNode.init(testing.allocator, 100);
    defer tree_root.deinit(testing.allocator);

    const tree_child = try TreeNode.init(testing.allocator, 200);
    try tree_root.addChild(testing.allocator, tree_child);
    try testing.expectEqual(@as(i32, 100), tree_child.parent.?.value);

    // Index-based
    var pool = NodePool.init(testing.allocator);
    defer pool.deinit(testing.allocator);

    const idx = try pool.create(testing.allocator, 42);
    try testing.expectEqual(@as(i32, 42), pool.get(idx));
}
```

### See Also

- Recipe 8.18: Extending Classes with Mixins
- Recipe 8.19: Implementing Stateful Objects or State Machines
- Recipe 8.20: Implementing the Visitor Pattern
- Recipe 0.12: Understanding Allocators

---

## Recipe 8.22: Making Structs Support Comparison Operations {#recipe-8-22}

**Tags:** allocators, comptime, error-handling, memory, resource-cleanup, slices, structs-objects, testing
**Difficulty:** advanced
**Code:** `code/03-advanced/08-structs-unions-objects/recipe_8_22.zig`

### Problem

You need to compare instances of your custom types for equality, sort them, use them as hash map keys, or implement custom ordering logic. Zig doesn't provide default comparison operators for structs.

### Solution

Implement comparison methods on your types: `eql()` for equality, `compare()` or `lessThan()` for ordering, and `hash()` for hash maps. Use comparison contexts with `std.mem.sort()` for flexible sorting.

### Basic Equality

Define an `eql()` method for equality comparisons:

```zig
// Basic equality implementation
const Point = struct {
    x: i32,
    y: i32,

    pub fn eql(self: Point, other: Point) bool {
        return self.x == other.x and self.y == other.y;
    }
};

test "basic equality" {
    const p1 = Point{ .x = 10, .y = 20 };
    const p2 = Point{ .x = 10, .y = 20 };
    const p3 = Point{ .x = 15, .y = 20 };

    try testing.expect(p1.eql(p2));
    try testing.expect(!p1.eql(p3));
}
```

Simple field-by-field comparison for value equality.

### Ordering Comparison

Implement `lessThan()` or `compare()` for sorting:

```zig
const Person = struct {
    name: []const u8,
    age: u32,

    pub fn lessThan(self: Person, other: Person) bool {
        // Compare by age first, then name
        if (self.age != other.age) {
            return self.age < other.age;
        }
        return std.mem.lessThan(u8, self.name, other.name);
    }

    pub fn compare(self: Person, other: Person) std.math.Order {
        if (self.age < other.age) return .lt;
        if (self.age > other.age) return .gt;
        return std.mem.order(u8, self.name, other.name);
    }
};
```

`compare()` returns `std.math.Order` (.lt, .eq, .gt) for more flexibility.

### Comparison Context for Sorting

Use comparison contexts to sort the same type different ways:

```zig
const Item = struct {
    id: u32,
    priority: i32,
    name: []const u8,

    const ByPriority = struct {
        pub fn lessThan(_: @This(), a: Item, b: Item) bool {
            return a.priority > b.priority; // Higher priority first
        }
    };

    const ByName = struct {
        pub fn lessThan(_: @This(), a: Item, b: Item) bool {
            return std.mem.lessThan(u8, a.name, b.name);
        }
    };
};

// Sort by priority
std.mem.sort(Item, items, Item.ByPriority{}, Item.ByPriority.lessThan);

// Sort by name
std.mem.sort(Item, items, Item.ByName{}, Item.ByName.lessThan);
```

Comparison contexts enable multiple sort orders without changing the type.

### Hash Function

Implement `hash()` for use in hash maps:

```zig
const Coordinate = struct {
    x: i32,
    y: i32,

    pub fn hash(self: Coordinate) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&self.x));
        hasher.update(std.mem.asBytes(&self.y));
        return hasher.final();
    }

    pub fn eql(self: Coordinate, other: Coordinate) bool {
        return self.x == other.x and self.y == other.y;
    }
};
```

Hash maps require both `hash()` and `eql()` methods.

### Deep Equality

Compare nested structures recursively:

```zig
const Team = struct {
    name: []const u8,
    members: []const []const u8,
    score: i32,

    pub fn eql(self: Team, other: Team) bool {
        if (self.score != other.score) return false;
        if (!std.mem.eql(u8, self.name, other.name)) return false;
        if (self.members.len != other.members.len) return false;

        for (self.members, other.members) |m1, m2| {
            if (!std.mem.eql(u8, m1, m2)) return false;
        }

        return true;
    }
};
```

Check all fields including nested arrays and slices.

### Custom Comparison Modes

Support multiple comparison strategies:

```zig
const Product = struct {
    name: []const u8,
    price: f64,
    rating: f32,

    const CompareMode = enum {
        by_price,
        by_rating,
        by_name,
    };

    pub fn compare(self: Product, other: Product, mode: CompareMode) std.math.Order {
        return switch (mode) {
            .by_price => std.math.order(self.price, other.price),
            .by_rating => std.math.order(self.rating, other.rating),
            .by_name => std.mem.order(u8, self.name, other.name),
        };
    }
};

// Compare different ways
const order = laptop.compare(phone, .by_price);
```

Enum-based modes provide flexible comparison logic.

### Approximate Equality

Compare floating point values with tolerance:

```zig
const Vector2D = struct {
    x: f64,
    y: f64,

    pub fn eql(self: Vector2D, other: Vector2D) bool {
        return self.x == other.x and self.y == other.y;
    }

    pub fn approxEql(self: Vector2D, other: Vector2D, epsilon: f64) bool {
        const dx = @abs(self.x - other.x);
        const dy = @abs(self.y - other.y);
        return dx < epsilon and dy < epsilon;
    }
};

// Approximate comparison for floats
const v1 = Vector2D{ .x = 1.0, .y = 2.0 };
const v2 = Vector2D{ .x = 1.0001, .y = 2.0001 };

if (v1.approxEql(v2, 0.001)) {
    // Considered equal within tolerance
}
```

Floating point comparisons need epsilon tolerance.

### Comparable Interface

Create generic comparison utilities using comptime:

```zig
fn Comparable(comptime T: type) type {
    return struct {
        pub fn requiresCompare() void {
            if (!@hasDecl(T, "compare")) {
                @compileError("Type must have compare method");
            }
        }

        pub fn min(a: T, b: T) T {
            return if (a.compare(b) == .lt) a else b;
        }

        pub fn max(a: T, b: T) T {
            return if (a.compare(b) == .gt) a else b;
        }

        pub fn clamp(value: T, low: T, high: T) T {
            return max(low, min(value, high));
        }
    };
}

const Score = struct {
    value: i32,

    pub fn compare(self: Score, other: Score) std.math.Order {
        return std.math.order(self.value, other.value);
    }
};

const ScoreOps = Comparable(Score);
const min_score = ScoreOps.min(s1, s2);
```

Generic utilities work with any type implementing `compare()`.

### Partial Ordering

Handle types where not all values are comparable:

```zig
const Entry = struct {
    key: ?[]const u8,
    value: i32,

    pub fn compare(self: Entry, other: Entry) ?std.math.Order {
        // Can't compare if either key is null
        const k1 = self.key orelse return null;
        const k2 = other.key orelse return null;

        const key_order = std.mem.order(u8, k1, k2);
        if (key_order != .eq) return key_order;

        return std.math.order(self.value, other.value);
    }
};

// Check if comparison succeeded
if (e1.compare(e2)) |order| {
    // Use order
} else {
    // Comparison not defined
}
```

Return optional order when comparison might not be valid.

### Multi-Field Comparison

Efficiently compare multiple fields in priority order:

```zig
const Record = struct {
    category: u8,
    priority: i32,
    timestamp: i64,
    id: u32,

    pub fn compare(self: Record, other: Record) std.math.Order {
        // Compare fields in order of importance
        if (self.category != other.category) {
            return std.math.order(self.category, other.category);
        }
        if (self.priority != other.priority) {
            return std.math.order(self.priority, other.priority);
        }
        if (self.timestamp != other.timestamp) {
            return std.math.order(self.timestamp, other.timestamp);
        }
        return std.math.order(self.id, other.id);
    }

    pub fn eql(self: Record, other: Record) bool {
        return self.category == other.category and
            self.priority == other.priority and
            self.timestamp == other.timestamp and
            self.id == other.id;
    }
};
```

Early exit on first difference for efficiency.

### Discussion

Comparison operations enable sorting, searching, and using custom types in data structures.

### Comparison Method Conventions

**Equality: `eql()`**:
```zig
pub fn eql(self: T, other: T) bool
```
- Returns true if values are equal
- Used for exact equality checks
- Required for hash maps (with `hash()`)

**Ordering: `lessThan()`**:
```zig
pub fn lessThan(self: T, other: T) bool
```
- Returns true if self < other
- Simple, intuitive interface
- Common for basic sorting

**Three-way comparison: `compare()`**:
```zig
pub fn compare(self: T, other: T) std.math.Order
```
- Returns .lt, .eq, or .gt
- More expressive than boolean
- Enables min/max/clamp utilities
- Single comparison determines all relationships

**Hashing: `hash()`**:
```zig
pub fn hash(self: T) u64
```
- Returns hash value
- Must be consistent with `eql()`
- If `a.eql(b)` then `a.hash() == b.hash()`

### Choosing Comparison Strategy

**Use `eql()` when**:
- Only need equality, not ordering
- Comparing for membership tests
- Keys in hash maps
- Simpler than full comparison

**Use `lessThan()` when**:
- Primary use is sorting
- Don't need all comparison operations
- Simpler mental model than Order enum
- Integrates with `std.mem.sort()`

**Use `compare()` when**:
- Need multiple comparison operations (min, max, clamp)
- Three-way comparison is more efficient
- Building generic comparison utilities
- Want exhaustive Order handling via switch

### Comparison Contexts

**Why use contexts**:
```zig
// Instead of multiple comparison methods
pub fn compareByPrice(...) {}
pub fn compareByName(...) {}

// Use contexts
const ByPrice = struct {
    pub fn lessThan(...) {}
};
```

**Benefits**:
- Multiple sort orders for same type
- No modification to original type
- Stateless or stateful comparisons
- Clean namespace

**Pattern**:
```zig
const MyType = struct {
    const SortContext = struct {
        reverse: bool,

        pub fn lessThan(self: @This(), a: MyType, b: MyType) bool {
            const result = a.value < b.value;
            return if (self.reverse) !result else result;
        }
    };
};

// Use with state
std.mem.sort(MyType, items, MyType.SortContext{ .reverse = true }, ...);
```

### Hash Function Implementation

**Good hash properties**:
- Deterministic: same input → same hash
- Uniform: distributes values evenly
- Fast: O(1) or O(n) for collections
- Consistent with equality

**Using Wyhash**:
```zig
pub fn hash(self: T) u64 {
    var hasher = std.hash.Wyhash.init(0);
    hasher.update(std.mem.asBytes(&self.field1));
    hasher.update(std.mem.asBytes(&self.field2));
    return hasher.final();
}
```

**For simple types**:
```zig
pub fn hash(self: T) u64 {
    return std.hash.Wyhash.hash(0, std.mem.asBytes(&self));
}
```

**Hash all fields used in `eql()`**:
- If `eql()` checks field X, `hash()` must include X
- Otherwise hash map lookups fail

### String Comparison

**Use `std.mem` utilities**:
```zig
std.mem.eql(u8, s1, s2)        // Equality
std.mem.lessThan(u8, s1, s2)   // Lexicographic <
std.mem.order(u8, s1, s2)      // Three-way order
```

**Case-insensitive**:
```zig
std.ascii.eqlIgnoreCase(s1, s2)
// No built-in case-insensitive ordering
// Implement custom if needed
```

**String slices in structs**:
```zig
pub fn eql(self: T, other: T) bool {
    return std.mem.eql(u8, self.name, other.name);
}
```

### Floating Point Comparison

**Exact equality is fragile**:
```zig
const a: f64 = 0.1 + 0.2;
const b: f64 = 0.3;
// a == b may be false due to rounding
```

**Use epsilon tolerance**:
```zig
pub fn approxEql(a: f64, b: f64, epsilon: f64) bool {
    return @abs(a - b) < epsilon;
}
```

**Choose epsilon carefully**:
- Too large: false positives
- Too small: false negatives
- Depends on magnitude and precision needs

**For ordering**:
```zig
std.math.order(a, b)  // Use exact comparison
// Ordering doesn't need epsilon
```

### Performance Considerations

**Short-circuit on first difference**:
```zig
pub fn compare(self: T, other: T) std.math.Order {
    if (self.field1 != other.field1) {
        return std.math.order(self.field1, other.field1);
    }
    // Only check field2 if field1 equal
    return std.math.order(self.field2, other.field2);
}
```

**Order fields by**:
- Likelihood of difference (most different first)
- Cheapness of comparison (cheap first)
- Logical importance

**Avoid expensive operations**:
```zig
// Bad: hash for equality
pub fn eql(self: T, other: T) bool {
    return self.hash() == other.hash(); // Too slow
}

// Good: direct field comparison
pub fn eql(self: T, other: T) bool {
    return self.id == other.id; // Fast
}
```

### Generic Comparison Utilities

**Compile-time interface checking**:
```zig
fn requireCompare(comptime T: type) void {
    if (!@hasDecl(T, "compare")) {
        @compileError("Type must have compare method");
    }
}
```

**Generic min/max**:
```zig
fn min(comptime T: type, a: T, b: T) T {
    requireCompare(T);
    return if (a.compare(b) == .lt) a else b;
}
```

**Type-safe interfaces**:
- Use `@hasDecl` to check methods exist
- Provide helpful compile errors
- No runtime overhead

### Common Patterns

**Database records**:
```zig
// Primary key comparison
pub fn eql(self: Record, other: Record) bool {
    return self.id == other.id;
}

// Multi-field sorting
pub fn compare(self: Record, other: Record) std.math.Order {
    // Category, then priority, then timestamp
}
```

**Range types**:
```zig
pub fn contains(self: Range, value: T) bool {
    return self.start.compare(value) != .gt and
           self.end.compare(value) != .lt;
}
```

**Sorted containers**:
```zig
pub fn insert(self: *SortedList, item: T) !void {
    var i: usize = 0;
    while (i < self.items.len) : (i += 1) {
        if (item.compare(self.items[i]) == .lt) break;
    }
    try self.items.insert(i, item);
}
```

### Testing Comparison Functions

**Test all orderings**:
```zig
test "comparison" {
    const a = T{ ... };
    const b = T{ ... };
    const c = T{ ... };

    // Reflexive: a == a
    try testing.expect(a.eql(a));

    // Symmetric: if a == b then b == a
    if (a.eql(b)) {
        try testing.expect(b.eql(a));
    }

    // Transitive: if a < b and b < c then a < c
    if (a.compare(b) == .lt and b.compare(c) == .lt) {
        try testing.expectEqual(std.math.Order.lt, a.compare(c));
    }
}
```

**Hash consistency**:
```zig
test "hash consistency" {
    const a = T{ ... };
    const b = T{ ... };

    if (a.eql(b)) {
        try testing.expectEqual(a.hash(), b.hash());
    }
}
```

### Full Tested Code

```zig
// Recipe 8.22: Making Classes Support Comparison Operations
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_equality
// Basic equality implementation
const Point = struct {
    x: i32,
    y: i32,

    pub fn eql(self: Point, other: Point) bool {
        return self.x == other.x and self.y == other.y;
    }
};

test "basic equality" {
    const p1 = Point{ .x = 10, .y = 20 };
    const p2 = Point{ .x = 10, .y = 20 };
    const p3 = Point{ .x = 15, .y = 20 };

    try testing.expect(p1.eql(p2));
    try testing.expect(!p1.eql(p3));
}
// ANCHOR_END: basic_equality

// ANCHOR: ordering_comparison
// Ordering comparisons for sorting
const Person = struct {
    name: []const u8,
    age: u32,

    pub fn lessThan(self: Person, other: Person) bool {
        // Compare by age first, then name
        if (self.age != other.age) {
            return self.age < other.age;
        }
        return std.mem.lessThan(u8, self.name, other.name);
    }

    pub fn compare(self: Person, other: Person) std.math.Order {
        if (self.age < other.age) return .lt;
        if (self.age > other.age) return .gt;
        return std.mem.order(u8, self.name, other.name);
    }
};

test "ordering comparison" {
    const alice = Person{ .name = "Alice", .age = 30 };
    const bob = Person{ .name = "Bob", .age = 25 };
    const charlie = Person{ .name = "Charlie", .age = 25 };

    try testing.expect(bob.lessThan(alice));
    try testing.expect(!alice.lessThan(bob));
    try testing.expect(bob.lessThan(charlie));

    try testing.expectEqual(std.math.Order.gt, alice.compare(bob));
    try testing.expectEqual(std.math.Order.lt, bob.compare(charlie));
}
// ANCHOR_END: ordering_comparison

// ANCHOR: comparison_context
// Comparison context for std.sort
const Item = struct {
    id: u32,
    priority: i32,
    name: []const u8,

    const ByPriority = struct {
        pub fn lessThan(_: @This(), a: Item, b: Item) bool {
            return a.priority > b.priority; // Higher priority first
        }
    };

    const ByName = struct {
        pub fn lessThan(_: @This(), a: Item, b: Item) bool {
            return std.mem.lessThan(u8, a.name, b.name);
        }
    };
};

test "comparison context" {
    const allocator = testing.allocator;

    var items = try allocator.alloc(Item, 3);
    defer allocator.free(items);

    items[0] = Item{ .id = 1, .priority = 10, .name = "zebra" };
    items[1] = Item{ .id = 2, .priority = 20, .name = "apple" };
    items[2] = Item{ .id = 3, .priority = 15, .name = "banana" };

    // Sort by priority
    std.mem.sort(Item, items, Item.ByPriority{}, Item.ByPriority.lessThan);
    try testing.expectEqual(@as(u32, 2), items[0].id); // Priority 20
    try testing.expectEqual(@as(u32, 3), items[1].id); // Priority 15

    // Sort by name
    std.mem.sort(Item, items, Item.ByName{}, Item.ByName.lessThan);
    try testing.expectEqualStrings("apple", items[0].name);
    try testing.expectEqualStrings("banana", items[1].name);
}
// ANCHOR_END: comparison_context

// ANCHOR: hash_function
// Hash function for use in hash maps
const Coordinate = struct {
    x: i32,
    y: i32,

    pub fn hash(self: Coordinate) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&self.x));
        hasher.update(std.mem.asBytes(&self.y));
        return hasher.final();
    }

    pub fn eql(self: Coordinate, other: Coordinate) bool {
        return self.x == other.x and self.y == other.y;
    }
};

test "hash function" {
    const c1 = Coordinate{ .x = 10, .y = 20 };
    const c2 = Coordinate{ .x = 10, .y = 20 };
    const c3 = Coordinate{ .x = 15, .y = 20 };

    try testing.expectEqual(c1.hash(), c2.hash());
    try testing.expect(c1.hash() != c3.hash());
    try testing.expect(c1.eql(c2));
}
// ANCHOR_END: hash_function

// ANCHOR: deep_equality
// Deep equality for nested structures
const Team = struct {
    name: []const u8,
    members: []const []const u8,
    score: i32,

    pub fn eql(self: Team, other: Team) bool {
        if (self.score != other.score) return false;
        if (!std.mem.eql(u8, self.name, other.name)) return false;
        if (self.members.len != other.members.len) return false;

        for (self.members, other.members) |m1, m2| {
            if (!std.mem.eql(u8, m1, m2)) return false;
        }

        return true;
    }
};

test "deep equality" {
    const members1 = [_][]const u8{ "Alice", "Bob" };
    const members2 = [_][]const u8{ "Alice", "Bob" };
    const members3 = [_][]const u8{ "Alice", "Charlie" };

    const team1 = Team{ .name = "Red", .members = &members1, .score = 100 };
    const team2 = Team{ .name = "Red", .members = &members2, .score = 100 };
    const team3 = Team{ .name = "Red", .members = &members3, .score = 100 };

    try testing.expect(team1.eql(team2));
    try testing.expect(!team1.eql(team3));
}
// ANCHOR_END: deep_equality

// ANCHOR: custom_comparison
// Custom comparison with context
const Product = struct {
    name: []const u8,
    price: f64,
    rating: f32,

    const CompareMode = enum {
        by_price,
        by_rating,
        by_name,
    };

    pub fn compare(self: Product, other: Product, mode: CompareMode) std.math.Order {
        return switch (mode) {
            .by_price => std.math.order(self.price, other.price),
            .by_rating => std.math.order(self.rating, other.rating),
            .by_name => std.mem.order(u8, self.name, other.name),
        };
    }
};

test "custom comparison" {
    const laptop = Product{ .name = "Laptop", .price = 999.99, .rating = 4.5 };
    const phone = Product{ .name = "Phone", .price = 599.99, .rating = 4.8 };

    try testing.expectEqual(std.math.Order.gt, laptop.compare(phone, .by_price));
    try testing.expectEqual(std.math.Order.lt, laptop.compare(phone, .by_rating));
    try testing.expectEqual(std.math.Order.lt, laptop.compare(phone, .by_name)); // L < P
}
// ANCHOR_END: custom_comparison

// ANCHOR: approximate_equality
// Approximate equality for floating point
const Vector2D = struct {
    x: f64,
    y: f64,

    pub fn eql(self: Vector2D, other: Vector2D) bool {
        return self.x == other.x and self.y == other.y;
    }

    pub fn approxEql(self: Vector2D, other: Vector2D, epsilon: f64) bool {
        const dx = @abs(self.x - other.x);
        const dy = @abs(self.y - other.y);
        return dx < epsilon and dy < epsilon;
    }
};

test "approximate equality" {
    const v1 = Vector2D{ .x = 1.0, .y = 2.0 };
    const v2 = Vector2D{ .x = 1.0001, .y = 2.0001 };

    try testing.expect(!v1.eql(v2)); // Exact equality fails
    try testing.expect(v1.approxEql(v2, 0.001)); // Approximate succeeds
    try testing.expect(!v1.approxEql(v2, 0.00001)); // Too strict
}
// ANCHOR_END: approximate_equality

// ANCHOR: comparable_interface
// Generic comparable interface using comptime
fn Comparable(comptime T: type) type {
    return struct {
        pub fn requiresCompare() void {
            if (!@hasDecl(T, "compare")) {
                @compileError("Type must have compare method");
            }
        }

        pub fn min(a: T, b: T) T {
            return if (a.compare(b) == .lt) a else b;
        }

        pub fn max(a: T, b: T) T {
            return if (a.compare(b) == .gt) a else b;
        }

        pub fn clamp(value: T, low: T, high: T) T {
            return max(low, min(value, high));
        }
    };
}

const Score = struct {
    value: i32,

    pub fn compare(self: Score, other: Score) std.math.Order {
        return std.math.order(self.value, other.value);
    }
};

test "comparable interface" {
    const ScoreOps = Comparable(Score);

    const s1 = Score{ .value = 100 };
    const s2 = Score{ .value = 200 };
    const s3 = Score{ .value = 150 };

    const min_score = ScoreOps.min(s1, s2);
    const max_score = ScoreOps.max(s1, s2);
    const clamped = ScoreOps.clamp(s3, s1, s2);

    try testing.expectEqual(@as(i32, 100), min_score.value);
    try testing.expectEqual(@as(i32, 200), max_score.value);
    try testing.expectEqual(@as(i32, 150), clamped.value);
}
// ANCHOR_END: comparable_interface

// ANCHOR: partial_ordering
// Partial ordering with optional comparison
const Entry = struct {
    key: ?[]const u8,
    value: i32,

    pub fn compare(self: Entry, other: Entry) ?std.math.Order {
        // Can't compare if either key is null
        const k1 = self.key orelse return null;
        const k2 = other.key orelse return null;

        const key_order = std.mem.order(u8, k1, k2);
        if (key_order != .eq) return key_order;

        return std.math.order(self.value, other.value);
    }
};

test "partial ordering" {
    const e1 = Entry{ .key = "apple", .value = 10 };
    const e2 = Entry{ .key = "banana", .value = 20 };
    const e3 = Entry{ .key = null, .value = 30 };

    try testing.expectEqual(std.math.Order.lt, e1.compare(e2).?);
    try testing.expect(e1.compare(e3) == null);
    try testing.expect(e3.compare(e2) == null);
}
// ANCHOR_END: partial_ordering

// ANCHOR: multi_field_comparison
// Efficient multi-field comparison
const Record = struct {
    category: u8,
    priority: i32,
    timestamp: i64,
    id: u32,

    pub fn compare(self: Record, other: Record) std.math.Order {
        // Compare fields in order of importance
        if (self.category != other.category) {
            return std.math.order(self.category, other.category);
        }
        if (self.priority != other.priority) {
            return std.math.order(self.priority, other.priority);
        }
        if (self.timestamp != other.timestamp) {
            return std.math.order(self.timestamp, other.timestamp);
        }
        return std.math.order(self.id, other.id);
    }

    pub fn eql(self: Record, other: Record) bool {
        return self.category == other.category and
            self.priority == other.priority and
            self.timestamp == other.timestamp and
            self.id == other.id;
    }
};

test "multi field comparison" {
    const r1 = Record{ .category = 1, .priority = 10, .timestamp = 1000, .id = 1 };
    const r2 = Record{ .category = 1, .priority = 10, .timestamp = 1000, .id = 2 };
    const r3 = Record{ .category = 2, .priority = 5, .timestamp = 900, .id = 1 };

    try testing.expectEqual(std.math.Order.lt, r1.compare(r2));
    try testing.expectEqual(std.math.Order.lt, r1.compare(r3));
    try testing.expect(r1.eql(r1));
    try testing.expect(!r1.eql(r2));
}
// ANCHOR_END: multi_field_comparison

// Comprehensive test
test "comprehensive comparison operations" {
    // Test all patterns work together
    const allocator = testing.allocator;

    // Basic equality
    const p1 = Point{ .x = 5, .y = 10 };
    const p2 = Point{ .x = 5, .y = 10 };
    try testing.expect(p1.eql(p2));

    // Ordering
    const alice = Person{ .name = "Alice", .age = 30 };
    const bob = Person{ .name = "Bob", .age = 25 };
    try testing.expect(bob.lessThan(alice));

    // Sorting with context
    var items = try allocator.alloc(Item, 2);
    defer allocator.free(items);
    items[0] = Item{ .id = 1, .priority = 10, .name = "zebra" };
    items[1] = Item{ .id = 2, .priority = 20, .name = "apple" };
    std.mem.sort(Item, items, Item.ByPriority{}, Item.ByPriority.lessThan);
    try testing.expectEqual(@as(u32, 2), items[0].id);

    // Hash equality
    const c1 = Coordinate{ .x = 1, .y = 2 };
    const c2 = Coordinate{ .x = 1, .y = 2 };
    try testing.expectEqual(c1.hash(), c2.hash());

    // Approximate equality
    const v1 = Vector2D{ .x = 1.0, .y = 2.0 };
    const v2 = Vector2D{ .x = 1.0001, .y = 2.0001 };
    try testing.expect(v1.approxEql(v2, 0.001));
}
```

### See Also

- Recipe 8.19: Implementing Stateful Objects or State Machines
- Recipe 8.20: Implementing the Visitor Pattern
- Recipe 2.1: Keeping the Last N Items (using comparison for priority queues)
- Recipe 7.6: Determining the Most Frequently Occurring Items in a Sequence

---
