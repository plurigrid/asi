# Build System & Modules Recipes

*18 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [10.1](#recipe-10-1) | Making a Hierarchical Package of Modules | intermediate |
| [10.2](#recipe-10-2) | Controlling the Import of Everything with pub | intermediate |
| [10.3](#recipe-10-3) | Importing Package Submodules Using Relative Names | intermediate |
| [10.4](#recipe-10-4) | Splitting a Module into Multiple Files | intermediate |
| [10.5](#recipe-10-5) | Making Separate Directories of Code Import Under a Common Namespace | intermediate |
| [10.6](#recipe-10-6) | Reloading Modules | intermediate |
| [10.7](#recipe-10-7) | Making a Directory or Archive File Runnable As a Main Script | intermediate |
| [10.8](#recipe-10-8) | Reading Datafiles Within a Package | intermediate |
| [10.9](#recipe-10-9) | Adding Directories to the Module Search Path | intermediate |
| [10.10](#recipe-10-10) | Importing Modules Using a Name Given in a String | intermediate |
| [10.11](#recipe-10-11) | Distributing Packages | intermediate |
| [16.1](#recipe-16-1) | Basic build.zig setup | advanced |
| [16.2](#recipe-16-2) | Multiple executables and libraries | advanced |
| [16.3](#recipe-16-3) | Managing dependencies | advanced |
| [16.4](#recipe-16-4) | Custom build steps | advanced |
| [16.5](#recipe-16-5) | Cross-compilation | advanced |
| [16.6](#recipe-16-6) | Build options and configurations | advanced |
| [16.7](#recipe-16-7) | Testing in the build system | advanced |

---

## Recipe 10.1: Making a Hierarchical Package of Modules {#recipe-10-1}

**Tags:** allocators, build-system, comptime, error-handling, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_1.zig`

### Problem

You need to organize a growing codebase into logical modules with clear hierarchy. You want to group related functionality, control what's exposed publicly, provide convenient access patterns, and maintain a clean API as your project scales.

### Solution

Zig uses explicit imports with `@import()` to create module hierarchies. Structure your code in directories, create parent modules that aggregate child modules, selectively re-export functionality, and design clean public APIs through controlled exports.

### Module Structure

Create a hierarchical organization:

```
recipe_10_1.zig (root)
├── math.zig (parent module)
│   ├── math/basic.zig (basic operations)
│   └── math/advanced.zig (advanced operations)
└── utils.zig (peer module)
```

### Importing Modules

Import modules using file paths relative to the importing file:

```zig
// Import top-level modules from the package
const math = @import("recipe_10_1/math.zig");
const utils = @import("recipe_10_1/utils.zig");
```

The path is relative to your project structure. Child modules import their siblings or parent modules similarly.

### Accessing Nested Modules

Access functionality through the module hierarchy:

```zig
test "accessing nested modules" {
    // Access through parent module
    const sum = math.add(5, 3);
    try testing.expectEqual(@as(i32, 8), sum);

    // Access through child module directly
    const product = math.basic.multiply(4, 5);
    try testing.expectEqual(@as(i32, 20), product);

    // Access advanced math through the hierarchy
    const pow = math.advanced.power(2, 10);
    try testing.expectEqual(@as(i64, 1024), pow);
}
```

You can access functions through re-exports at the parent level or directly through child modules.

### Discussion

### Creating Child Modules

Child modules define focused functionality. Here's a basic operations module:

```zig
// basic.zig
const std = @import("std");

/// Add two numbers
pub fn add(a: i32, b: i32) i32 {
    return a + b;
}

/// Divide two numbers (returns error on division by zero)
pub fn divide(a: i32, b: i32) !i32 {
    if (b == 0) {
        return error.DivisionByZero;
    }
    return @divTrunc(a, b);
}
```

Use `pub` to expose functions publicly. Private functions (without `pub`) are only accessible within the module.

### Parent Module Aggregation

Parent modules import and organize child modules:

```zig
// math.zig
const std = @import("std");

// Import child modules
pub const basic = @import("math/basic.zig");
pub const advanced = @import("math/advanced.zig");

// Re-export commonly used functions at this level
pub const add = basic.add;
pub const subtract = basic.subtract;
pub const multiply = basic.multiply;
pub const divide = basic.divide;
```

This provides two access patterns: `math.add(a, b)` or `math.basic.add(a, b)`.

### Re-Exported Functions

Re-exports make common operations more convenient:

```zig
test "using re-exported functions" {
    // These are re-exported at the math module level
    const a = math.add(10, 20);
    const b = math.subtract(50, 15);
    const c = math.multiply(3, 7);

    try testing.expectEqual(@as(i32, 30), a);
    try testing.expectEqual(@as(i32, 35), b);
    try testing.expectEqual(@as(i32, 21), c);

    // Division returns error union
    const d = try math.divide(100, 4);
    try testing.expectEqual(@as(i32, 25), d);
}
```

Users can choose between convenience (re-exports) and explicitness (child module access).

### Module-Level Coordination Functions

Parent modules can provide coordination functions:

```zig
// In math.zig
pub fn calculate(operation: Operation, a: i32, b: i32) !i32 {
    return switch (operation) {
        .add => basic.add(a, b),
        .subtract => basic.subtract(a, b),
        .multiply => basic.multiply(a, b),
        .divide => try basic.divide(a, b),
    };
}

pub const Operation = enum {
    add,
    subtract,
    multiply,
    divide,
};
```

This provides a unified interface across child module functionality:

```zig
test "module-level functions" {
    const result1 = try math.calculate(.add, 15, 25);
    try testing.expectEqual(@as(i32, 40), result1);

    const result2 = try math.calculate(.multiply, 6, 7);
    try testing.expectEqual(@as(i32, 42), result2);
}
```

### Advanced Operations Module

Separate complex functionality into dedicated modules:

```zig
// advanced.zig
pub fn power(a: i32, b: u32) i64 {
    if (b == 0) return 1;

    var result: i64 = 1;
    var i: u32 = 0;
    while (i < b) : (i += 1) {
        result *= a;
    }
    return result;
}

pub fn factorial(n: u32) u64 {
    if (n == 0 or n == 1) return 1;

    var result: u64 = 1;
    var i: u32 = 2;
    while (i <= n) : (i += 1) {
        result *= i;
    }
    return result;
}

pub fn isPrime(n: u32) bool {
    if (n < 2) return false;
    if (n == 2) return true;
    if (n % 2 == 0) return false;

    var i: u32 = 3;
    while (i * i <= n) : (i += 2) {
        if (n % i == 0) return false;
    }
    return true;
}
```

Access these through the parent module:

```zig
test "advanced math operations" {
    // Power function
    try testing.expectEqual(@as(i64, 8), math.advanced.power(2, 3));

    // Factorial function
    try testing.expectEqual(@as(u64, 120), math.advanced.factorial(5));

    // Prime checking
    try testing.expect(math.advanced.isPrime(7));
    try testing.expect(!math.advanced.isPrime(9));
}
```

### Peer Modules

Create peer modules at the same level for different concerns:

```zig
// utils.zig
const std = @import("std");

/// Convert integer to string
pub fn intToString(allocator: std.mem.Allocator, value: i32) ![]u8 {
    return std.fmt.allocPrint(allocator, "{d}", .{value});
}

/// Check if string is numeric
pub fn isNumeric(str: []const u8) bool {
    if (str.len == 0) return false;

    var start: usize = 0;
    if (str[0] == '-' or str[0] == '+') {
        if (str.len == 1) return false;
        start = 1;
    }

    for (str[start..]) |c| {
        if (c < '0' or c > '9') return false;
    }
    return true;
}
```

Use peer modules alongside hierarchical ones:

```zig
test "utility functions" {
    const allocator = testing.allocator;

    const str = try utils.intToString(allocator, 42);
    defer allocator.free(str);
    try testing.expectEqualStrings("42", str);

    try testing.expect(utils.isNumeric("123"));
    try testing.expect(!utils.isNumeric("abc"));
}
```

### Cross-Module Usage

Combine multiple modules in your application:

```zig
test "cross-module usage" {
    const allocator = testing.allocator;

    // Calculate using math module
    const result = try math.calculate(.add, 10, 32);

    // Convert result to string using utils module
    const str = try utils.intToString(allocator, result);
    defer allocator.free(str);

    try testing.expectEqualStrings("42", str);

    // Verify it's numeric
    try testing.expect(utils.isNumeric(str));
}
```

Modules remain independent but compose naturally.

### Hierarchical Access Patterns

Provide flexibility in how users access functionality:

```zig
test "hierarchical access patterns" {
    // Direct access through re-export
    const a = math.add(5, 3);

    // Access through child module
    const b = math.basic.add(5, 3);

    // Both should give same result
    try testing.expectEqual(a, b);

    // Can access enum through parent module
    const op: math.Operation = .add;
    const c = try math.calculate(op, 5, 3);

    try testing.expectEqual(a, c);
}
```

Different patterns suit different use cases and preferences.

### Public API Design

Design clean public APIs through selective exports:

```zig
const math_mod = math;
const utils_mod = utils;

const PublicAPI = struct {
    // Expose only selected functionality
    pub const MathOps = struct {
        pub const add = math_mod.add;
        pub const subtract = math_mod.subtract;
        pub const power = math_mod.advanced.power;
        pub const factorial = math_mod.advanced.factorial;
    };

    pub const Utils = struct {
        pub const parseInt = utils_mod.parseInt;
        pub const isNumeric = utils_mod.isNumeric;
    };
};

test "public API design" {
    // Users only see curated public API
    const sum = PublicAPI.MathOps.add(10, 20);
    try testing.expectEqual(@as(i32, 30), sum);

    const pow = PublicAPI.MathOps.power(2, 8);
    try testing.expectEqual(@as(i64, 256), pow);
}
```

This creates a stable public API while keeping implementation details private.

### Module Organization Benefits

Hierarchical organization provides several advantages:

**Namespace Separation:**
- Clear boundaries between different areas of functionality
- Prevents naming conflicts
- Makes dependencies explicit

**Selective Imports:**
- Import only what you need
- Reduces compilation dependencies
- Clearer code intent

**Consistent API Structure:**
- Predictable organization
- Similar operations grouped together
- Easier to discover functionality

**Clear Dependencies:**
- Explicit import statements show relationships
- No hidden dependencies
- Easy to understand data flow

**Scalability:**
- Add new modules without restructuring existing code
- Split large modules into smaller ones
- Maintain backward compatibility through re-exports

### Best Practices

Follow these guidelines for module organization:

**File Organization:**
- One module per file
- Group related modules in directories
- Mirror module hierarchy in filesystem structure

**Naming Conventions:**
- Use lowercase for module files (`math.zig`, not `Math.zig`)
- Descriptive module names (`basic.zig`, `advanced.zig`)
- Match module name to its primary purpose

**Public Interface:**
- Make only necessary items `pub`
- Group related exports in parent modules
- Provide re-exports for common operations
- Document public API with `///` comments

**Module Size:**
- Keep modules focused on single responsibility
- Split large modules into child modules
- Aim for 200-500 lines per module
- Create sub-directories when > 5 related modules

**Import Strategy:**
- Import modules, not individual functions
- Use const declarations for imports
- Avoid circular dependencies
- Keep import list at top of file

### When to Create Hierarchies

Use hierarchical modules when:

**Growing Codebase:**
- File exceeds 500 lines
- Multiple related functions
- Distinct logical groupings emerge

**Multiple Developers:**
- Clear ownership boundaries
- Parallel development needed
- Independent testing required

**Public Libraries:**
- Need version stability
- Want to hide implementation details
- Provide multiple access patterns

**Domain Complexity:**
- Multiple layers of abstraction
- Different levels of user sophistication
- Gradual feature exposure

### Common Patterns

**Feature Modules:**
```
features/
├── auth.zig (authentication)
├── db.zig (database access)
└── api.zig (API handlers)
```

**Layer Architecture:**
```
app/
├── presentation/ (UI layer)
├── business/ (logic layer)
└── data/ (persistence layer)
```

**Component-Based:**
```
components/
├── button/
│   ├── button.zig
│   └── styles.zig
└── input/
    ├── input.zig
    └── validation.zig
```

### Testing Hierarchical Modules

Test at multiple levels:

**Unit Tests** (in child modules):
```zig
// In basic.zig
test "add" {
    const testing = @import("std").testing;
    try testing.expectEqual(@as(i32, 7), add(3, 4));
}
```

**Integration Tests** (in parent modules):
```zig
// In math.zig
test "calculate all operations" {
    try testing.expectEqual(@as(i32, 7), try calculate(.add, 3, 4));
    try testing.expectEqual(@as(i32, 12), try calculate(.multiply, 3, 4));
}
```

**System Tests** (in root):
```zig
// In recipe_10_1.zig
test "comprehensive usage" {
    // Tests cross-module integration
}
```

### Documentation Generation

Zig generates documentation from module structure:

```bash
zig build-lib math.zig -femit-docs
```

This creates HTML documentation showing the hierarchy. Use `///` doc comments:

```zig
/// Add two integers.
/// Returns the sum of a and b.
pub fn add(a: i32, b: i32) i32 {
    return a + b;
}
```

### Module Initialization

Modules can have initialization code:

```zig
const std = @import("std");

// Module-level constant
const VERSION = "1.0.0";

// Comptime initialization
const lookup_table = blk: {
    var table: [256]u8 = undefined;
    for (&table, 0..) |*val, i| {
        val.* = @intCast(i);
    }
    break :blk table;
};
```

This code runs once when the module is first imported.

### Avoiding Circular Dependencies

Circular dependencies cause compilation errors:

```zig
// DON'T: Circular dependency
// a.zig imports b.zig
// b.zig imports a.zig
```

Solutions:

1. **Extract Common Code:**
   Create a third module for shared functionality

2. **Dependency Inversion:**
   Pass dependencies as parameters instead of importing

3. **Interface Definitions:**
   Define interfaces in a separate module

### Full Tested Code

```zig
// Recipe 10.1: Making a Hierarchical Package of Modules
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to organize code into a hierarchical
// module structure with multiple levels of imports and re-exports.
//
// Module structure:
// recipe_10_1.zig (root)
// ├── math.zig (parent module)
// │   ├── math/basic.zig (child module)
// │   └── math/advanced.zig (child module)
// └── utils.zig (peer module)

const std = @import("std");
const testing = std.testing;

// ANCHOR: importing_modules
// Import top-level modules from the package
const math = @import("recipe_10_1/math.zig");
const utils = @import("recipe_10_1/utils.zig");
// ANCHOR_END: importing_modules

// ANCHOR: accessing_nested_modules
// Access functions from nested modules in different ways
test "accessing nested modules" {
    // Access through parent module
    const sum = math.add(5, 3);
    try testing.expectEqual(@as(i32, 8), sum);

    // Access through child module directly
    const product = math.basic.multiply(4, 5);
    try testing.expectEqual(@as(i32, 20), product);

    // Access advanced math through the hierarchy
    const pow = math.advanced.power(2, 10);
    try testing.expectEqual(@as(i64, 1024), pow);
}
// ANCHOR_END: accessing_nested_modules

// ANCHOR: using_reexported_functions
// Use re-exported functions from parent module
test "using re-exported functions" {
    // These are re-exported at the math module level
    const a = math.add(10, 20);
    const b = math.subtract(50, 15);
    const c = math.multiply(3, 7);

    try testing.expectEqual(@as(i32, 30), a);
    try testing.expectEqual(@as(i32, 35), b);
    try testing.expectEqual(@as(i32, 21), c);

    // Division returns error union
    const d = try math.divide(100, 4);
    try testing.expectEqual(@as(i32, 25), d);

    // Test error case
    const err = math.divide(10, 0);
    try testing.expectError(error.DivisionByZero, err);
}
// ANCHOR_END: using_reexported_functions

// ANCHOR: module_level_functions
// Use module-level functions that coordinate child modules
test "module-level functions" {
    const result1 = try math.calculate(.add, 15, 25);
    try testing.expectEqual(@as(i32, 40), result1);

    const result2 = try math.calculate(.multiply, 6, 7);
    try testing.expectEqual(@as(i32, 42), result2);

    const result3 = try math.calculate(.subtract, 100, 42);
    try testing.expectEqual(@as(i32, 58), result3);

    const result4 = try math.calculate(.divide, 50, 5);
    try testing.expectEqual(@as(i32, 10), result4);
}
// ANCHOR_END: module_level_functions

// ANCHOR: basic_math_operations
// Test basic math operations from the basic module
test "basic math operations" {
    try testing.expectEqual(@as(i32, 7), math.basic.add(3, 4));
    try testing.expectEqual(@as(i32, 1), math.basic.subtract(5, 4));
    try testing.expectEqual(@as(i32, 12), math.basic.multiply(3, 4));
    try testing.expectEqual(@as(i32, 3), try math.basic.divide(9, 3));
}
// ANCHOR_END: basic_math_operations

// ANCHOR: advanced_math_operations
// Test advanced math operations from the advanced module
test "advanced math operations" {
    // Power function
    try testing.expectEqual(@as(i64, 8), math.advanced.power(2, 3));
    try testing.expectEqual(@as(i64, 1), math.advanced.power(5, 0));
    try testing.expectEqual(@as(i64, 125), math.advanced.power(5, 3));

    // Factorial function
    try testing.expectEqual(@as(u64, 1), math.advanced.factorial(0));
    try testing.expectEqual(@as(u64, 1), math.advanced.factorial(1));
    try testing.expectEqual(@as(u64, 120), math.advanced.factorial(5));
    try testing.expectEqual(@as(u64, 3628800), math.advanced.factorial(10));

    // Prime checking
    try testing.expect(!math.advanced.isPrime(0));
    try testing.expect(!math.advanced.isPrime(1));
    try testing.expect(math.advanced.isPrime(2));
    try testing.expect(math.advanced.isPrime(7));
    try testing.expect(!math.advanced.isPrime(9));
    try testing.expect(math.advanced.isPrime(13));
}
// ANCHOR_END: advanced_math_operations

// ANCHOR: utility_functions
// Test utility functions from utils module
test "utility functions" {
    const allocator = testing.allocator;

    // Integer to string conversion
    const str = try utils.intToString(allocator, 42);
    defer allocator.free(str);
    try testing.expectEqualStrings("42", str);

    // Numeric checking
    try testing.expect(utils.isNumeric("123"));
    try testing.expect(utils.isNumeric("-456"));
    try testing.expect(!utils.isNumeric("abc"));
    try testing.expect(!utils.isNumeric("12a3"));
    try testing.expect(!utils.isNumeric(""));

    // Integer parsing
    try testing.expectEqual(@as(i32, 123), try utils.parseInt("123"));
    try testing.expectEqual(@as(i32, -456), try utils.parseInt("-456"));

    // Clamping
    try testing.expectEqual(@as(i32, 5), utils.clamp(5, 0, 10));
    try testing.expectEqual(@as(i32, 0), utils.clamp(-5, 0, 10));
    try testing.expectEqual(@as(i32, 10), utils.clamp(15, 0, 10));
}
// ANCHOR_END: utility_functions

// ANCHOR: cross_module_usage
// Demonstrate using multiple modules together
test "cross-module usage" {
    const allocator = testing.allocator;

    // Calculate using math module
    const result = try math.calculate(.add, 10, 32);

    // Convert result to string using utils module
    const str = try utils.intToString(allocator, result);
    defer allocator.free(str);

    try testing.expectEqualStrings("42", str);

    // Verify it's numeric
    try testing.expect(utils.isNumeric(str));

    // Parse it back
    const parsed = try utils.parseInt(str);
    try testing.expectEqual(result, parsed);
}
// ANCHOR_END: cross_module_usage

// ANCHOR: hierarchical_access_patterns
// Different ways to access the same functionality
test "hierarchical access patterns" {
    // Direct access through re-export
    const a = math.add(5, 3);

    // Access through child module
    const b = math.basic.add(5, 3);

    // Both should give same result
    try testing.expectEqual(a, b);

    // Can access enum through parent module
    const op: math.Operation = .add;
    const c = try math.calculate(op, 5, 3);

    try testing.expectEqual(a, c);
}
// ANCHOR_END: hierarchical_access_patterns

// ANCHOR: public_api_design
// Demonstrate a clean public API through selective exports
const math_mod = math;
const utils_mod = utils;

const PublicAPI = struct {
    // Expose only selected functionality
    pub const MathOps = struct {
        pub const add = math_mod.add;
        pub const subtract = math_mod.subtract;
        pub const power = math_mod.advanced.power;
        pub const factorial = math_mod.advanced.factorial;
    };

    pub const Utils = struct {
        pub const parseInt = utils_mod.parseInt;
        pub const isNumeric = utils_mod.isNumeric;
    };
};

test "public API design" {
    // Users only see curated public API
    const sum = PublicAPI.MathOps.add(10, 20);
    try testing.expectEqual(@as(i32, 30), sum);

    const pow = PublicAPI.MathOps.power(2, 8);
    try testing.expectEqual(@as(i64, 256), pow);

    try testing.expect(PublicAPI.Utils.isNumeric("123"));
}
// ANCHOR_END: public_api_design

// ANCHOR: module_organization_benefits
// Demonstrate benefits of hierarchical organization
test "module organization benefits" {
    // 1. Namespace separation
    const math_result = math.basic.add(5, 3);
    _ = math_result;

    // 2. Selective imports (only import what you need)
    const basic = math.basic;
    const advanced = math.advanced;
    _ = basic.add(1, 2);
    _ = advanced.power(2, 3);

    // 3. Consistent API structure
    _ = try math.calculate(.add, 1, 2);
    _ = try math.calculate(.divide, 10, 2);

    // 4. Clear dependencies
    const allocator = testing.allocator;
    const str = try utils.intToString(allocator, 42);
    defer allocator.free(str);

    try testing.expect(true);
}
// ANCHOR_END: module_organization_benefits

// Comprehensive test
test "comprehensive hierarchical modules" {
    const allocator = testing.allocator;

    // Use basic math
    const sum = math.add(10, 20);
    try testing.expectEqual(@as(i32, 30), sum);

    // Use advanced math
    const fact = math.advanced.factorial(5);
    try testing.expectEqual(@as(u64, 120), fact);

    // Use utils
    const str = try utils.intToString(allocator, @intCast(fact));
    defer allocator.free(str);
    try testing.expectEqualStrings("120", str);

    // Use module-level function
    const result = try math.calculate(.multiply, 6, 7);
    try testing.expectEqual(@as(i32, 42), result);

    try testing.expect(true);
}
```

### See Also

- Recipe 10.2: Controlling the export of symbols
- Recipe 10.4: Splitting a module into multiple files
- Recipe 10.5: Making separate directories of code import under a common namespace

---

## Recipe 10.2: Controlling the Import of Everything with pub {#recipe-10-2}

**Tags:** allocators, build-system, c-interop, error-handling, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_2.zig`

### Problem

You need to control which symbols are visible to users of your module. You want to create a clean public API, hide implementation details, prevent misuse of internal functions, and maintain flexibility to refactor private code without breaking users.

### Solution

Use the `pub` keyword to mark declarations as public. Anything without `pub` is private to the file/module. Design your API surface carefully by exposing only what users need and keeping implementation details private.

### Public vs Private Declarations

Public declarations use `pub`, private ones don't:

```zig
// Public vs Private declarations
const InternalCounter = struct {
    // Private field (no pub keyword)
    value: i32,

    // Public function
    pub fn init() InternalCounter {
        return .{ .value = 0 };
    }

    // Public function
    pub fn increment(self: *InternalCounter) void {
        self.value += 1;
    }

    // Public function
    pub fn getValue(self: *const InternalCounter) i32 {
        return self.value;
    }

    // Private function (no pub keyword)
    fn reset(self: *InternalCounter) void {
        self.value = 0;
    }
};

test "public vs private" {
    var counter = InternalCounter.init();
    counter.increment();

    try testing.expectEqual(@as(i32, 1), counter.getValue());

    // Can access private function within same file
    counter.reset();
    try testing.expectEqual(@as(i32, 0), counter.getValue());

    // Note: Outside this file, reset() wouldn't be accessible
}
```

Within the same file, all declarations are accessible. In importing modules, only `pub` declarations are visible.

### Discussion

### Selective Exports

Export only the types and functions users need:

```zig
const Database = struct {
    // Public type for users
    pub const Connection = struct {
        handle: *ConnectionImpl,

        pub fn query(self: *Connection, sql: []const u8) !void {
            return self.handle.execute(sql);
        }
    };

    // Private implementation (not exported)
    const ConnectionImpl = struct {
        connected: bool,

        fn execute(self: *ConnectionImpl, sql: []const u8) !void {
            if (!self.connected) {
                return error.NotConnected;
            }
            // Simulated query execution
            _ = sql;
        }
    };

    // Public factory function
    pub fn connect() !Connection {
        var impl = ConnectionImpl{ .connected = true };
        // NOTE: For demonstration only - in production, ConnectionImpl
        // would be heap-allocated with allocator.create()
        return Connection{ .handle = &impl };
    }
};

test "selective exports" {
    var conn = try Database.connect();

    // Can use public Connection type
    try conn.query("SELECT * FROM users");

    // Cannot access ConnectionImpl - it's private to Database
    // const impl: Database.ConnectionImpl = undefined; // Compile error
}
```

Users see `Connection` but `ConnectionImpl` remains private.

### Controlling API Surface

Keep helper functions private:

```zig
const StringUtils = struct {
    // Public API
    pub fn toUpper(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
        const result = try allocator.alloc(u8, input.len);
        for (input, 0..) |c, i| {
            result[i] = upperCaseChar(c);
        }
        return result;
    }

    pub fn toLower(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
        const result = try allocator.alloc(u8, input.len);
        for (input, 0..) |c, i| {
            result[i] = lowerCaseChar(c);
        }
        return result;
    }

    // Private helper functions (implementation details)
    fn upperCaseChar(c: u8) u8 {
        if (c >= 'a' and c <= 'z') {
            return c - 32;
        }
        return c;
    }

    fn lowerCaseChar(c: u8) u8 {
        if (c >= 'A' and c <= 'Z') {
            return c + 32;
        }
        return c;
    }
};

test "API surface control" {
    const allocator = testing.allocator;

    const upper = try StringUtils.toUpper(allocator, "hello");
    defer allocator.free(upper);
    try testing.expectEqualStrings("HELLO", upper);

    // Helper functions are private, users can't call them directly
    // StringUtils.upperCaseChar('a'); // Compile error outside this file
}
```

Users call `toUpper()` and `toLower()` without seeing implementation details.

### Namespace Exports

Create namespaces with public and private members:

```zig
pub const Math = struct {
    // Public constants
    pub const PI: f64 = 3.14159265358979323846;
    pub const E: f64 = 2.71828182845904523536;

    // Private constant (implementation detail)
    const EPSILON: f64 = 1e-10;

    // Public functions
    pub fn abs(x: f64) f64 {
        return if (x < 0) -x else x;
    }

    pub fn isClose(a: f64, b: f64) bool {
        return abs(a - b) < EPSILON;
    }

    // Private helper
    fn square(x: f64) f64 {
        return x * x;
    }

    // Public function using private helper
    pub fn distance(x1: f64, y1: f64, x2: f64, y2: f64) f64 {
        const dx = x2 - x1;
        const dy = y2 - y1;
        return @sqrt(square(dx) + square(dy));
    }
};

test "namespace exports" {
    try testing.expect(Math.PI > 3.14);
    try testing.expect(Math.E > 2.71);

    try testing.expectEqual(@as(f64, 5.0), Math.abs(-5.0));
    try testing.expect(Math.isClose(1.0, 1.00000000001));

    const dist = Math.distance(0, 0, 3, 4);
    try testing.expectEqual(@as(f64, 5.0), dist);

    // Cannot access private members
    // const eps = Math.EPSILON; // Compile error
    // Math.square(2.0); // Compile error
}
```

Public functions can use private helpers internally.

### Selective Re-Exporting

Re-export only some symbols from internal modules:

```zig
const internal = struct {
    pub fn internalFunc1() i32 {
        return 42;
    }

    pub fn internalFunc2() i32 {
        return 24;
    }

    pub fn internalFunc3() i32 {
        return 99;
    }
};

pub const PublicAPI = struct {
    // Selectively re-export only some functions
    pub const func1 = internal.internalFunc1;
    pub const func2 = internal.internalFunc2;

    // Don't export internalFunc3 - it's an implementation detail
};

test "selective re-exporting" {
    try testing.expectEqual(@as(i32, 42), PublicAPI.func1());
    try testing.expectEqual(@as(i32, 24), PublicAPI.func2());

    // func3 is not exported
    // PublicAPI.func3(); // Compile error

    // But we can still test internal functions in the same file
    try testing.expectEqual(@as(i32, 99), internal.internalFunc3());
}
```

This creates a curated public interface while keeping full functionality for internal use.

### Versioned API Exports

Maintain multiple API versions:

```zig
pub const V1 = struct {
    pub fn process(value: i32) i32 {
        return value * 2;
    }
};

pub const V2 = struct {
    pub fn process(value: i32, multiplier: i32) i32 {
        return value * multiplier;
    }

    // V2 can delegate to V1 for compatibility
    pub fn processSimple(value: i32) i32 {
        return V1.process(value);
    }
};

// Latest version alias
pub const Latest = V2;

test "versioned API" {
    try testing.expectEqual(@as(i32, 10), V1.process(5));
    try testing.expectEqual(@as(i32, 15), V2.process(5, 3));
    try testing.expectEqual(@as(i32, 10), V2.processSimple(5));
    try testing.expectEqual(@as(i32, 15), Latest.process(5, 3));
}
```

Users can choose which version to use, and `Latest` always points to the newest.

### Privacy Levels

Demonstrate different levels of encapsulation:

```zig
pub const Library = struct {
    // Level 1: Public type with fields accessible
    pub const PublicType = struct {
        value: i32, // Fields are accessible where struct is accessible

        pub fn new(val: i32) PublicType {
            return .{ .value = val };
        }
    };

    // Level 2: Public type, recommended accessor pattern
    pub const EncapsulatedType = struct {
        value: i32,

        pub fn new(val: i32) EncapsulatedType {
            return .{ .value = val };
        }

        pub fn getValue(self: *const EncapsulatedType) i32 {
            return self.value;
        }

        pub fn setValue(self: *EncapsulatedType, val: i32) void {
            self.value = val;
        }
    };

    // Level 3: Completely private (no pub)
    const PrivateType = struct {
        value: i32,
    };

    // Public function using private type
    pub fn usePrivateType() i32 {
        const p = PrivateType{ .value = 100 };
        return p.value;
    }
};

test "privacy levels" {
    // Level 1: Full access (fields accessible in same module)
    var public_var = Library.PublicType.new(10);
    public_var.value = 20;
    try testing.expectEqual(@as(i32, 20), public_var.value);

    // Level 2: Encapsulation pattern (use accessors)
    var encap = Library.EncapsulatedType.new(30);
    try testing.expectEqual(@as(i32, 30), encap.getValue());
    encap.setValue(40);
    try testing.expectEqual(@as(i32, 40), encap.getValue());

    // Level 3: Cannot access type at all from outside module
    // const priv: Library.PrivateType = undefined; // Compile error

    // But can use functions that return values from private types
    try testing.expectEqual(@as(i32, 100), Library.usePrivateType());
}
```

Choose the privacy level that matches your needs.

### Testing Private Implementation

Tests in the same file can verify private functions:

```zig
const Calculator = struct {
    // Private implementation
    fn add_internal(a: i32, b: i32) i32 {
        return a + b;
    }

    fn multiply_internal(a: i32, b: i32) i32 {
        return a * b;
    }

    // Public API
    pub fn calculate(a: i32, b: i32, op: Op) i32 {
        return switch (op) {
            .add => add_internal(a, b),
            .multiply => multiply_internal(a, b),
        };
    }

    pub const Op = enum {
        add,
        multiply,
    };
};

test "testing private implementation" {
    // Within the same file, we can test private functions
    try testing.expectEqual(@as(i32, 7), Calculator.add_internal(3, 4));
    try testing.expectEqual(@as(i32, 12), Calculator.multiply_internal(3, 4));

    // Public API still works
    try testing.expectEqual(@as(i32, 7), Calculator.calculate(3, 4, .add));
    try testing.expectEqual(@as(i32, 12), Calculator.calculate(3, 4, .multiply));
}
```

This allows thorough testing while keeping implementation details private to external users.

### Common Export Patterns

**Pattern 1: Factory with Private Constructor**

```zig
pub const Widget = struct {
    id: u32,

    // Private - users must use factory
    fn init(id: u32) Widget {
        return .{ .id = id };
    }

    // Public factory
    pub fn create() Widget {
        return init(generateId());
    }

    pub fn getId(self: *const Widget) u32 {
        return self.id;
    }
};
```

Forces users to use controlled initialization.

**Pattern 2: Opaque Handle**

```zig
pub const Handle = struct {
    ptr: *anyopaque,

    pub fn fromInt(value: usize) Handle {
        return .{ .ptr = @ptrFromInt(value) };
    }

    pub fn toInt(self: Handle) usize {
        return @intFromPtr(self.ptr);
    }
};
```

Hides internal representation completely.

### Conditional Exports

Export symbols conditionally based on build configuration:

```zig
const build_options = struct {
    // In production, this would be: @import("build_options")
    // configured via: exe.addOptions(options) in build.zig
    const enable_debug = true;
};

pub const Debug = if (build_options.enable_debug) struct {
    pub fn log(msg: []const u8) void {
        std.debug.print("[DEBUG] {s}\n", .{msg});
    }

    pub fn assert(condition: bool) void {
        std.debug.assert(condition);
    }
} else struct {
    // Empty struct when debug is disabled
};

test "conditional exports" {
    if (build_options.enable_debug) {
        Debug.log("Test message");
        Debug.assert(true);
    }
    try testing.expect(true);
}
```

This allows different APIs for different build configurations.

### Documentation Exports

Document public APIs with `///` comments:

```zig
pub const Documented = struct {
    /// A documented public function
    /// that shows how to use doc comments.
    ///
    /// Example:
    /// ```
    /// const result = Documented.add(5, 3);
    /// ```
    pub fn add(a: i32, b: i32) i32 {
        return addImpl(a, b);
    }

    // Private implementation (no doc comment needed)
    fn addImpl(a: i32, b: i32) i32 {
        return a + b;
    }

    /// Maximum supported value
    pub const MAX_VALUE: i32 = 1000;

    // Private constant (no doc comment)
    const INTERNAL_BUFFER_SIZE: usize = 4096;
};
```

Only public declarations need documentation comments.

### Best Practices

**Start with Everything Private:**
- Make declarations private by default
- Add `pub` only when needed
- This prevents accidental API exposure

**Group Related Exports:**
- Use structs as namespaces
- Keep related functions together
- Provide clear module boundaries

**Use Accessor Patterns:**
- Provide getters/setters for encapsulated types
- Validate inputs in setters
- Keep fields private when validation is needed

**Version Your APIs:**
- Export versioned namespaces (V1, V2, etc.)
- Provide `Latest` alias for current version
- Maintain backward compatibility when possible

**Document Public APIs:**
- Use `///` for all public functions
- Include examples in doc comments
- Explain error conditions

**Test Private Code:**
- Write tests in the same file
- Verify implementation details
- Keep integration tests in separate files

### Design Considerations

**When to Make Something Public:**
- Users need to call/access it
- Part of the stable API contract
- Designed for external use

**When to Keep Something Private:**
- Implementation detail
- May change in future versions
- Internal helper function
- Validation or sanitization logic

**Privacy and Performance:**
- Privacy is compile-time only (zero runtime cost)
- Private functions inline just like public ones
- No performance penalty for encapsulation

### Common Patterns Summary

| Pattern | Use Case | Example |
|---------|----------|---------|
| Public struct with private fields | Encapsulation | `pub const Type = struct { value: i32, ... }` |
| Private helper functions | Implementation details | `fn helper() void { ... }` |
| Factory pattern | Controlled initialization | `pub fn create() T { ... }` |
| Opaque handle | Complete abstraction | `pub const Handle = struct { ptr: *anyopaque }` |
| Namespace | Grouping related functions | `pub const Math = struct { ... }` |
| Re-exporting | API facade | `pub const api = internal.func;` |
| Versioned exports | API stability | `pub const V1 = struct { ... }` |
| Conditional exports | Build-specific APIs | `pub const Debug = if (enable) ...` |

### Avoiding Common Mistakes

**Don't expose internals accidentally:**
```zig
// Bad: exposes implementation
pub const Config = struct {
    pub internal_state: i32, // Users can modify this!
};

// Good: encapsulated
pub const Config = struct {
    internal_state: i32,

    pub fn getState(self: *const Config) i32 {
        return self.internal_state;
    }
};
```

**Don't make everything public:**
```zig
// Bad: too much exposure
pub fn publicFunc() void {
    pub fn helperA() void { ... } // Compile error anyway
    pub fn helperB() void { ... } // Compile error anyway
}

// Good: only what's needed
pub fn publicFunc() void {
    helperA();
    helperB();
}

fn helperA() void { ... }
fn helperB() void { ... }
```

**Don't forget to document public APIs:**
```zig
// Bad: no documentation
pub fn process(data: []const u8) !void { ... }

// Good: documented
/// Process the input data.
/// Returns error.InvalidData if data is malformed.
pub fn process(data: []const u8) !void { ... }
```

### Full Tested Code

```zig
// Recipe 10.2: Controlling the Export of Symbols
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to control symbol visibility using the pub keyword,
// creating clean public APIs while hiding implementation details.

const std = @import("std");
const testing = std.testing;

// ANCHOR: public_vs_private
// Public vs Private declarations
const InternalCounter = struct {
    // Private field (no pub keyword)
    value: i32,

    // Public function
    pub fn init() InternalCounter {
        return .{ .value = 0 };
    }

    // Public function
    pub fn increment(self: *InternalCounter) void {
        self.value += 1;
    }

    // Public function
    pub fn getValue(self: *const InternalCounter) i32 {
        return self.value;
    }

    // Private function (no pub keyword)
    fn reset(self: *InternalCounter) void {
        self.value = 0;
    }
};

test "public vs private" {
    var counter = InternalCounter.init();
    counter.increment();

    try testing.expectEqual(@as(i32, 1), counter.getValue());

    // Can access private function within same file
    counter.reset();
    try testing.expectEqual(@as(i32, 0), counter.getValue());

    // Note: Outside this file, reset() wouldn't be accessible
}
// ANCHOR_END: public_vs_private

// ANCHOR: selective_exports
// Module with selective exports
const Database = struct {
    // Public type for users
    pub const Connection = struct {
        handle: *ConnectionImpl,

        pub fn query(self: *Connection, sql: []const u8) !void {
            return self.handle.execute(sql);
        }
    };

    // Private implementation (not exported)
    const ConnectionImpl = struct {
        connected: bool,

        fn execute(self: *ConnectionImpl, sql: []const u8) !void {
            if (!self.connected) {
                return error.NotConnected;
            }
            // Simulated query execution
            _ = sql;
        }
    };

    // Public factory function
    pub fn connect() !Connection {
        var impl = ConnectionImpl{ .connected = true };
        // NOTE: For demonstration only - in production, ConnectionImpl
        // would be heap-allocated with allocator.create()
        return Connection{ .handle = &impl };
    }
};

test "selective exports" {
    var conn = try Database.connect();

    // Can use public Connection type
    try conn.query("SELECT * FROM users");

    // Cannot access ConnectionImpl - it's private to Database
    // const impl: Database.ConnectionImpl = undefined; // Compile error
}
// ANCHOR_END: selective_exports

// ANCHOR: api_surface
// Control API surface area with selective exports
const StringUtils = struct {
    // Public API
    pub fn toUpper(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
        const result = try allocator.alloc(u8, input.len);
        for (input, 0..) |c, i| {
            result[i] = upperCaseChar(c);
        }
        return result;
    }

    pub fn toLower(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
        const result = try allocator.alloc(u8, input.len);
        for (input, 0..) |c, i| {
            result[i] = lowerCaseChar(c);
        }
        return result;
    }

    // Private helper functions (implementation details)
    fn upperCaseChar(c: u8) u8 {
        if (c >= 'a' and c <= 'z') {
            return c - 32;
        }
        return c;
    }

    fn lowerCaseChar(c: u8) u8 {
        if (c >= 'A' and c <= 'Z') {
            return c + 32;
        }
        return c;
    }
};

test "API surface control" {
    const allocator = testing.allocator;

    const upper = try StringUtils.toUpper(allocator, "hello");
    defer allocator.free(upper);
    try testing.expectEqualStrings("HELLO", upper);

    const lower = try StringUtils.toLower(allocator, "WORLD");
    defer allocator.free(lower);
    try testing.expectEqualStrings("world", lower);

    // Helper functions are private, users can't call them directly
    // StringUtils.upperCaseChar('a'); // Compile error outside this file
}
// ANCHOR_END: api_surface

// ANCHOR: namespace_exports
// Create namespace with controlled exports
pub const Math = struct {
    // Public constants
    pub const PI: f64 = 3.14159265358979323846;
    pub const E: f64 = 2.71828182845904523536;

    // Private constant (implementation detail)
    const EPSILON: f64 = 1e-10;

    // Public functions
    pub fn abs(x: f64) f64 {
        return if (x < 0) -x else x;
    }

    pub fn isClose(a: f64, b: f64) bool {
        return abs(a - b) < EPSILON;
    }

    // Private helper
    fn square(x: f64) f64 {
        return x * x;
    }

    // Public function using private helper
    pub fn distance(x1: f64, y1: f64, x2: f64, y2: f64) f64 {
        const dx = x2 - x1;
        const dy = y2 - y1;
        return @sqrt(square(dx) + square(dy));
    }
};

test "namespace exports" {
    try testing.expect(Math.PI > 3.14);
    try testing.expect(Math.E > 2.71);

    try testing.expectEqual(@as(f64, 5.0), Math.abs(-5.0));
    try testing.expect(Math.isClose(1.0, 1.00000000001)); // Within EPSILON

    const dist = Math.distance(0, 0, 3, 4);
    try testing.expectEqual(@as(f64, 5.0), dist);

    // Cannot access private members
    // const eps = Math.EPSILON; // Compile error
    // Math.square(2.0); // Compile error
}
// ANCHOR_END: namespace_exports

// ANCHOR: reexporting
// Re-export symbols from other modules with control
const internal = struct {
    pub fn internalFunc1() i32 {
        return 42;
    }

    pub fn internalFunc2() i32 {
        return 24;
    }

    pub fn internalFunc3() i32 {
        return 99;
    }
};

pub const PublicAPI = struct {
    // Selectively re-export only some functions
    pub const func1 = internal.internalFunc1;
    pub const func2 = internal.internalFunc2;

    // Don't export internalFunc3 - it's an implementation detail
};

test "selective re-exporting" {
    try testing.expectEqual(@as(i32, 42), PublicAPI.func1());
    try testing.expectEqual(@as(i32, 24), PublicAPI.func2());

    // func3 is not exported
    // PublicAPI.func3(); // Compile error

    // But we can still test internal functions in the same file
    try testing.expectEqual(@as(i32, 99), internal.internalFunc3());
}
// ANCHOR_END: reexporting

// ANCHOR: versioned_api
// Create versioned API exports
pub const V1 = struct {
    pub fn process(value: i32) i32 {
        return value * 2;
    }
};

pub const V2 = struct {
    pub fn process(value: i32, multiplier: i32) i32 {
        return value * multiplier;
    }

    // V2 can delegate to V1 for compatibility
    pub fn processSimple(value: i32) i32 {
        return V1.process(value);
    }
};

// Latest version alias
pub const Latest = V2;

test "versioned API" {
    try testing.expectEqual(@as(i32, 10), V1.process(5));
    try testing.expectEqual(@as(i32, 15), V2.process(5, 3));
    try testing.expectEqual(@as(i32, 10), V2.processSimple(5));
    try testing.expectEqual(@as(i32, 15), Latest.process(5, 3));
}
// ANCHOR_END: versioned_api

// ANCHOR: privacy_levels
// Demonstrate different privacy levels
pub const Library = struct {
    // Level 1: Public type with fields accessible
    pub const PublicType = struct {
        value: i32, // Fields are accessible where struct is accessible

        pub fn new(val: i32) PublicType {
            return .{ .value = val };
        }
    };

    // Level 2: Public type, recommended accessor pattern
    pub const EncapsulatedType = struct {
        value: i32,

        pub fn new(val: i32) EncapsulatedType {
            return .{ .value = val };
        }

        pub fn getValue(self: *const EncapsulatedType) i32 {
            return self.value;
        }

        pub fn setValue(self: *EncapsulatedType, val: i32) void {
            self.value = val;
        }
    };

    // Level 3: Completely private (no pub)
    const PrivateType = struct {
        value: i32,
    };

    // Public function using private type
    pub fn usePrivateType() i32 {
        const p = PrivateType{ .value = 100 };
        return p.value;
    }
};

test "privacy levels" {
    // Level 1: Full access (fields accessible in same module)
    var public_var = Library.PublicType.new(10);
    public_var.value = 20;
    try testing.expectEqual(@as(i32, 20), public_var.value);

    // Level 2: Encapsulation pattern (use accessors)
    var encap = Library.EncapsulatedType.new(30);
    try testing.expectEqual(@as(i32, 30), encap.getValue());
    encap.setValue(40);
    try testing.expectEqual(@as(i32, 40), encap.getValue());

    // Level 3: Cannot access type at all from outside module
    // const priv: Library.PrivateType = undefined; // Compile error

    // But can use functions that return values from private types
    try testing.expectEqual(@as(i32, 100), Library.usePrivateType());
}
// ANCHOR_END: privacy_levels

// ANCHOR: testing_private
// Testing private implementation within the same file
const Calculator = struct {
    // Private implementation
    fn add_internal(a: i32, b: i32) i32 {
        return a + b;
    }

    fn multiply_internal(a: i32, b: i32) i32 {
        return a * b;
    }

    // Public API
    pub fn calculate(a: i32, b: i32, op: Op) i32 {
        return switch (op) {
            .add => add_internal(a, b),
            .multiply => multiply_internal(a, b),
        };
    }

    pub const Op = enum {
        add,
        multiply,
    };
};

test "testing private implementation" {
    // Within the same file, we can test private functions
    try testing.expectEqual(@as(i32, 7), Calculator.add_internal(3, 4));
    try testing.expectEqual(@as(i32, 12), Calculator.multiply_internal(3, 4));

    // Public API still works
    try testing.expectEqual(@as(i32, 7), Calculator.calculate(3, 4, .add));
    try testing.expectEqual(@as(i32, 12), Calculator.calculate(3, 4, .multiply));
}
// ANCHOR_END: testing_private

// ANCHOR: export_patterns
// Common export patterns
pub const Patterns = struct {
    // Pattern 1: Factory with private constructor
    pub const Widget = struct {
        id: u32,

        // Private - users must use factory
        fn init(id: u32) Widget {
            return .{ .id = id };
        }

        // Public factory
        pub fn create() Widget {
            return init(generateId());
        }

        pub fn getId(self: *const Widget) u32 {
            return self.id;
        }
    };

    // Pattern 2: Opaque handle
    pub const Handle = struct {
        const Self = @This();

        ptr: *anyopaque,

        // Prevent direct construction
        pub fn fromInt(value: usize) Handle {
            return .{ .ptr = @ptrFromInt(value) };
        }

        pub fn toInt(self: Handle) usize {
            return @intFromPtr(self.ptr);
        }
    };

    // Private helper for Widget
    var next_id: u32 = 1;

    fn generateId() u32 {
        const id = next_id;
        next_id += 1;
        return id;
    }
};

test "export patterns" {
    // Pattern 1: Factory
    const w1 = Patterns.Widget.create();
    const w2 = Patterns.Widget.create();
    try testing.expect(w1.getId() != w2.getId());

    // Cannot call private init directly (outside this file)
    // const w3 = Patterns.Widget.init(99); // Would compile in same file

    // Pattern 2: Opaque handle
    const handle = Patterns.Handle.fromInt(12345);
    try testing.expectEqual(@as(usize, 12345), handle.toInt());
}
// ANCHOR_END: export_patterns

// ANCHOR: conditional_exports
// Conditional exports based on build options
const build_options = struct {
    // In production, this would be: @import("build_options")
    // configured via: exe.addOptions(options) in build.zig
    const enable_debug = true;
};

pub const Debug = if (build_options.enable_debug) struct {
    pub fn log(msg: []const u8) void {
        std.debug.print("[DEBUG] {s}\n", .{msg});
    }

    pub fn assert(condition: bool) void {
        std.debug.assert(condition);
    }
} else struct {
    // Empty struct when debug is disabled
};

test "conditional exports" {
    if (build_options.enable_debug) {
        Debug.log("Test message");
        Debug.assert(true);
    }
    try testing.expect(true);
}
// ANCHOR_END: conditional_exports

// ANCHOR: documentation_exports
// Export symbols with documentation
pub const Documented = struct {
    /// A documented public function
    /// that shows how to use doc comments.
    ///
    /// Example:
    /// ```
    /// const result = Documented.add(5, 3);
    /// ```
    pub fn add(a: i32, b: i32) i32 {
        return addImpl(a, b);
    }

    // Private implementation (no doc comment needed)
    fn addImpl(a: i32, b: i32) i32 {
        return a + b;
    }

    /// Maximum supported value
    pub const MAX_VALUE: i32 = 1000;

    // Private constant (no doc comment)
    const INTERNAL_BUFFER_SIZE: usize = 4096;
};

test "documented exports" {
    try testing.expectEqual(@as(i32, 8), Documented.add(5, 3));
    try testing.expectEqual(@as(i32, 1000), Documented.MAX_VALUE);

    // Can still test private constants in same file
    try testing.expectEqual(@as(usize, 4096), Documented.INTERNAL_BUFFER_SIZE);
}
// ANCHOR_END: documentation_exports

// Comprehensive test
test "comprehensive export control" {
    // Public vs private
    var counter = InternalCounter.init();
    counter.increment();
    try testing.expectEqual(@as(i32, 1), counter.getValue());

    // Selective exports
    const allocator = testing.allocator;
    const upper = try StringUtils.toUpper(allocator, "test");
    defer allocator.free(upper);
    try testing.expectEqualStrings("TEST", upper);

    // Namespace exports
    try testing.expect(Math.PI > 3.0);

    // Versioned API
    try testing.expectEqual(@as(i32, 10), Latest.process(5, 2));

    // Privacy levels
    const public_obj = Library.PublicType.new(42);
    try testing.expectEqual(@as(i32, 42), public_obj.value);

    try testing.expect(true);
}
```

### See Also

- Recipe 10.1: Making a hierarchical package of modules
- Recipe 10.4: Splitting a module into multiple files
- Recipe 8.12: Defining an interface

---

## Recipe 10.3: Importing Package Submodules Using Relative Names {#recipe-10-3}

**Tags:** build-system, c-interop, error-handling, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_3.zig`

### Problem

You need to import modules using relative paths within your package. You want siblings to import each other, child modules to access parent functionality, and a clear dependency hierarchy. You need to avoid absolute paths that make refactoring difficult.

### Solution

Use relative paths with `@import()` to reference modules based on their position in the file system. Import children with `directory/file.zig`, siblings with `file.zig`, and parents with `../file.zig`. Organize your package into logical layers to prevent circular dependencies.

### Package Structure

Create a hierarchical module organization:

```
recipe_10_3/
├── core.zig (parent module)
│   ├── core/logger.zig (utility)
│   └── core/config.zig (uses logger)
└── services.zig (parent module)
    ├── services/database.zig (uses core)
    └── services/api.zig (uses database + core)
```

### Root Imports

Import top-level modules from your main file:

```zig
// Root module imports top-level submodules
const core = @import("recipe_10_3/core.zig");
const services = @import("recipe_10_3/services.zig");
```

Paths are relative to your project root or build configuration.

### Using Imported Modules

Access functionality from imported modules:

```zig
test "using imported modules" {
    const config = core.Config.init("localhost", 8080);
    try testing.expectEqualStrings("localhost", config.host);
    try testing.expectEqual(@as(u16, 8080), config.port);
}
```

The `core` module exposes its types and functions.

### Discussion

### Sibling Imports

Modules in the same directory import each other using just the filename:

```zig
// In core/config.zig
const std = @import("std");

// Import sibling module using relative path
const logger = @import("logger.zig");

pub const Config = struct {
    host: []const u8,
    port: u16,

    pub fn init(host: []const u8, port: u16) Config {
        logger.info("Initializing configuration");
        return .{
            .host = host,
            .port = port,
        };
    }

    pub fn validate(self: *const Config) bool {
        if (self.port == 0) {
            logger.log(.err, "Invalid port: 0");
            return false;
        }
        logger.debug("Configuration validated");
        return true;
    }
};
```

The `config` module imports `logger` from the same directory using `@import("logger.zig")`.

Test sibling imports:

```zig
test "sibling module imports" {
    // config.zig imports logger.zig (both in core/ directory)
    const config = core.config.Config.init("127.0.0.1", 3000);

    // Validation uses logger (sibling import)
    try testing.expect(config.validate());

    // Invalid config uses logger for error
    const bad_config = core.config.Config.init("localhost", 0);
    try testing.expect(!bad_config.validate());
}
```

### Parent-to-Child Imports

Parent modules import children using directory paths:

```zig
// In core.zig
const std = @import("std");

// Import child modules from subdirectory
pub const logger = @import("core/logger.zig");
pub const config = @import("core/config.zig");

// Re-export commonly used types
pub const Config = config.Config;
pub const LogLevel = logger.Level;
```

The parent `core.zig` imports modules from the `core/` subdirectory.

### Child-to-Parent Imports

Child modules access parent packages using `../`:

```zig
// In services/database.zig
const std = @import("std");

// Import from parent package using relative path
const core = @import("../core.zig");

pub const Database = struct {
    config: core.Config,
    connected: bool,

    pub fn init(config: core.Config) Database {
        core.logger.info("Database initialized");
        return .{
            .config = config,
            .connected = false,
        };
    }

    pub fn connect(self: *Database) !void {
        if (!self.config.validate()) {
            return error.InvalidConfig;
        }
        self.connected = true;
        core.logger.info("Database connected");
    }

    pub fn disconnect(self: *Database) void {
        self.connected = false;
        core.logger.info("Database disconnected");
    }
};
```

The `database` module uses `../core.zig` to access the parent package.

Test child-to-parent imports:

```zig
test "child to parent imports" {
    const config = core.Config.init("db.example.com", 5432);

    // database.zig imports ../core.zig to access Config and logger
    var db = services.database.Database.init(config);

    try db.connect();
    try testing.expect(db.connected);

    db.disconnect();
    try testing.expect(!db.connected);
}
```

### Multiple Relative Imports

Modules can import both siblings and parents:

```zig
// In services/api.zig
const std = @import("std");

// Import sibling module
const database = @import("database.zig");

// Import from parent package
const core = @import("../core.zig");

pub const API = struct {
    db: database.Database,

    pub fn init(config: core.Config) API {
        core.logger.info("API initialized");
        return .{
            .db = database.Database.init(config),
        };
    }

    pub fn start(self: *API) !void {
        try self.db.connect();
        core.logger.info("API started");
    }

    pub fn stop(self: *API) void {
        self.db.disconnect();
        core.logger.info("API stopped");
    }
};
```

The `api` module imports both `database.zig` (sibling) and `../core.zig` (parent).

Test multiple imports:

```zig
test "multiple relative imports" {
    const config = core.Config.init("api.example.com", 8080);

    // api.zig imports both database.zig (sibling) and ../core.zig (parent)
    var api = services.api.API.init(config);

    try api.start();
    try testing.expect(api.db.connected);

    api.stop();
    try testing.expect(!api.db.connected);
}
```

### Accessing Through Hierarchy

Access modules either directly or through re-exports:

```zig
test "accessing through hierarchy" {
    // Can access through parent module
    const config1 = core.Config.init("host1", 1111);

    // Or through re-exported type
    const config2 = core.config.Config.init("host2", 2222);

    // Both work the same way
    try testing.expect(true);
}
```

Re-exports in `core.zig` provide convenient shortcuts.

### Re-Exported Types

Parent modules re-export types for convenience:

```zig
test "re-exported types" {
    // Use re-exported Config type
    const config: core.Config = .{
        .host = "localhost",
        .port = 8080,
    };
    try testing.expectEqualStrings("localhost", config.host);

    // Use re-exported LogLevel enum
    const level: core.LogLevel = .info;
    try testing.expectEqual(core.LogLevel.info, level);
}
```

Users can choose between `core.Config` (re-export) or `core.config.Config` (full path).

### Cross-Package Communication

Different package sections communicate through shared modules:

```zig
test "cross-package communication" {
    // Core provides configuration
    const config = core.Config.init("myapp.local", 9000);

    // Services use core configuration
    const db = services.Database.init(config);
    const api = services.API.init(config);

    // Both services share the same config
    try testing.expectEqualStrings(db.config.host, api.db.config.host);
    try testing.expectEqual(db.config.port, api.db.config.port);
}
```

The `core` package provides shared types and utilities used by `services`.

### Relative Path Rules

Follow these rules for relative imports:

**Rule 1: Paths are relative to the importing file**
```zig
// In core.zig
@import("core/logger.zig")  // Child in subdirectory
```

**Rule 2: Use ".." to go up one directory level**
```zig
// In services/database.zig
@import("../core.zig")  // Parent directory
```

**Rule 3: Sibling imports use just the filename**
```zig
// In core/config.zig
@import("logger.zig")  // Same directory
```

**Rule 4: Can chain ".." to go up multiple levels**
```zig
@import("../../module.zig")  // Two levels up
```

### Import Pattern Summary

| Pattern | Example Path | Use Case |
|---------|-------------|----------|
| Root → Child | `@import("pkg/module.zig")` | Main imports package |
| Parent → Child | `@import("dir/file.zig")` | Aggregator imports submodules |
| Sibling → Sibling | `@import("sibling.zig")` | Same directory imports |
| Child → Parent | `@import("../parent.zig")` | Access package utilities |
| Multi-level | `@import("../../file.zig")` | Deep hierarchy navigation |

### Avoiding Circular Dependencies

Organize modules into layers to prevent circular imports:

```zig
test "avoiding circular imports" {
    // Good: Layered architecture
    // core/ (foundation layer) - no dependencies on services/
    // services/ (application layer) - depends on core/

    // Core modules don't import services
    const config = core.Config.init("localhost", 8080);

    // Services import core (one-way dependency)
    const db = services.Database.init(config);

    // This creates a clear dependency hierarchy
    try testing.expectEqualStrings(config.host, db.config.host);
}
```

Dependencies flow in one direction: `services` → `core`, never the reverse.

### Package Organization Benefits

Relative imports provide several advantages:

**Clear module relationships:**
- Dependencies are explicit in import statements
- Easy to see which modules depend on others
- Refactoring updates are localized

**Self-contained packages:**
- Modules can be moved as a group
- Relative paths remain valid
- No global namespace concerns

**Easy refactoring:**
- Move entire directories without updating imports
- Rename packages without breaking internal imports
- Reorganize structure with minimal changes

**No global namespace pollution:**
- Each module declares dependencies explicitly
- No hidden or implicit imports
- Clear separation of concerns

### Best Practices

**Use Layered Architecture:**
```
foundation/ (no external dependencies)
    ├── core utilities
    └── shared types
application/ (depends on foundation)
    ├── business logic
    └── services
```

**Keep Imports at Top:**
```zig
const std = @import("std");
const core = @import("../core.zig");
const sibling = @import("sibling.zig");

// Then your code
```

**Avoid Deep Hierarchies:**
- Limit nesting to 2-3 levels
- Use aggregator modules for deep trees
- Consider flattening if paths get complex

**Document Dependencies:**
```zig
// Import from core utilities layer
const logger = @import("../core/logger.zig");

// Import sibling service
const database = @import("database.zig");
```

**Group Related Modules:**
```
services/
    ├── database.zig
    ├── api.zig
    └── cache.zig
```

### Common Patterns

**Utility Layer:**
```
core/
    ├── logger.zig (logging)
    ├── config.zig (configuration)
    └── errors.zig (error types)
```

**Service Layer:**
```
services/
    ├── database.zig (imports core)
    ├── api.zig (imports database + core)
    └── worker.zig (imports core)
```

**Feature Modules:**
```
features/
    ├── auth/ (authentication)
    │   ├── auth.zig
    │   └── auth/providers.zig
    └── users/ (user management)
        ├── users.zig
        └── users/repository.zig
```

### Preventing Common Mistakes

**Don't use absolute paths when relative works:**
```zig
// Bad: hardcoded absolute path
const logger = @import("myapp/core/logger.zig");

// Good: relative path
const logger = @import("../core/logger.zig");
```

**Don't create circular dependencies:**
```zig
// Bad: A imports B, B imports A
// a.zig: const b = @import("b.zig");
// b.zig: const a = @import("a.zig"); // Circular!

// Good: Extract shared code to C
// a.zig: const c = @import("c.zig");
// b.zig: const c = @import("c.zig");
```

**Don't nest too deeply:**
```zig
// Bad: too many levels
@import("../../../../shared/utils.zig")

// Good: restructure or use aggregator
@import("../shared.zig")
```

### Working with Build System

In `build.zig`, configure module paths:

```zig
const exe = b.addExecutable(.{
    .name = "myapp",
    .root_source_file = b.path("src/main.zig"),
});

// Modules can now import relative to src/
```

The build system resolves import paths relative to the root source file.

### Testing Module Imports

Test that imports work correctly:

```zig
test "module imports compile" {
    // Simply importing tests the import path
    _ = @import("core.zig");
    _ = @import("services.zig");
}

test "module functionality" {
    // Test actual behavior
    const config = core.Config.init("test", 8080);
    try testing.expect(config.validate());
}
```

### Refactoring with Relative Imports

When restructuring code:

1. **Move related modules together** - Relative imports update automatically
2. **Keep import paths short** - Minimize `../` usage
3. **Test after moving** - Verify imports still resolve
4. **Update parent aggregators** - Adjust re-exports if needed

### Import Resolution

Zig resolves imports in this order:

1. Check for standard library (`std`)
2. Check build system packages
3. Resolve relative to importing file
4. Report error if not found

Relative paths always resolve from the current file's location.

### Full Tested Code

```zig
// Recipe 10.3: Importing Package Submodules Using Relative Names
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to import submodules using relative paths,
// showing parent-to-child, child-to-parent, and sibling imports.
//
// Package structure:
// recipe_10_3.zig (root)
// ├── core.zig (parent module)
// │   ├── core/logger.zig (child module)
// │   └── core/config.zig (child module, imports sibling logger)
// ├── services.zig (parent module)
//     ├── services/database.zig (child module, imports ../core.zig)
//     └── services/api.zig (child module, imports sibling + parent)

const std = @import("std");
const testing = std.testing;

// ANCHOR: root_imports
// Root module imports top-level submodules
const core = @import("recipe_10_3/core.zig");
const services = @import("recipe_10_3/services.zig");
// ANCHOR_END: root_imports

// ANCHOR: using_imported_modules
// Use modules imported from the package
test "using imported modules" {
    const config = core.Config.init("localhost", 8080);
    try testing.expectEqualStrings("localhost", config.host);
    try testing.expectEqual(@as(u16, 8080), config.port);
}
// ANCHOR_END: using_imported_modules

// ANCHOR: sibling_imports
// Demonstrate modules that import siblings
test "sibling module imports" {
    // config.zig imports logger.zig (both in core/ directory)
    const config = core.config.Config.init("127.0.0.1", 3000);

    // Validation uses logger (sibling import)
    try testing.expect(config.validate());

    // Invalid config uses logger for error
    const bad_config = core.config.Config.init("localhost", 0);
    try testing.expect(!bad_config.validate());
}
// ANCHOR_END: sibling_imports

// ANCHOR: parent_imports
// Demonstrate child importing parent package
test "child to parent imports" {
    const config = core.Config.init("db.example.com", 5432);

    // database.zig imports ../core.zig to access Config and logger
    var db = services.database.Database.init(config);

    try db.connect();
    try testing.expect(db.connected);

    db.disconnect();
    try testing.expect(!db.connected);
}
// ANCHOR_END: parent_imports

// ANCHOR: multiple_relative_imports
// Demonstrate module with multiple relative imports
test "multiple relative imports" {
    const config = core.Config.init("api.example.com", 8080);

    // api.zig imports both database.zig (sibling) and ../core.zig (parent)
    var api = services.api.API.init(config);

    try api.start();
    try testing.expect(api.db.connected);

    api.stop();
    try testing.expect(!api.db.connected);
}
// ANCHOR_END: multiple_relative_imports

// ANCHOR: accessing_through_hierarchy
// Access modules through the import hierarchy
test "accessing through hierarchy" {
    // Can access through parent module
    const config1 = core.Config.init("host1", 1111);
    _ = config1;

    // Or through re-exported type
    const config2 = core.config.Config.init("host2", 2222);
    _ = config2;

    // Both work the same way
    try testing.expect(true);
}
// ANCHOR_END: accessing_through_hierarchy

// ANCHOR: logger_usage
// Use logger from different import paths
test "logger usage from multiple paths" {
    // Access logger through core module
    core.logger.info("Test from core.logger");

    // Access through re-export
    core.logger.debug("Test from re-export");

    // Access log function directly
    core.logger.log(.warn, "Warning message");

    try testing.expect(true);
}
// ANCHOR_END: logger_usage

// ANCHOR: reexported_types
// Use re-exported types from parent modules
test "re-exported types" {
    // Use re-exported Config type
    const config: core.Config = .{
        .host = "localhost",
        .port = 8080,
    };
    try testing.expectEqualStrings("localhost", config.host);

    // Use re-exported LogLevel enum
    const level: core.LogLevel = .info;
    try testing.expectEqual(core.LogLevel.info, level);
}
// ANCHOR_END: reexported_types

// ANCHOR: cross_package_communication
// Demonstrate communication between different package sections
test "cross-package communication" {
    // Core provides configuration
    const config = core.Config.init("myapp.local", 9000);

    // Services use core configuration
    const db = services.Database.init(config);
    const api = services.API.init(config);

    // Both services share the same config
    try testing.expectEqualStrings(db.config.host, api.db.config.host);
    try testing.expectEqual(db.config.port, api.db.config.port);
}
// ANCHOR_END: cross_package_communication

// ANCHOR: import_patterns
// Different import patterns demonstrated
const ImportPatterns = struct {
    // Pattern 1: Direct child import (parent → child)
    // In core.zig: @import("core/logger.zig")

    // Pattern 2: Sibling import (child → sibling)
    // In core/config.zig: @import("logger.zig")

    // Pattern 3: Parent import (child → parent)
    // In services/database.zig: @import("../core.zig")

    // Pattern 4: Complex relative (child → sibling + parent)
    // In services/api.zig: @import("database.zig") and @import("../core.zig")
};

test "import pattern documentation" {
    _ = ImportPatterns;
    try testing.expect(true);
}
// ANCHOR_END: import_patterns

// ANCHOR: relative_path_rules
// Demonstrate relative path rules
test "relative path rules" {
    // Rule 1: Paths are relative to the importing file
    // core.zig imports "core/logger.zig" (child in subdirectory)

    // Rule 2: Use ".." to go up one directory level
    // services/database.zig imports "../core.zig" (parent directory)

    // Rule 3: Sibling imports use just the filename
    // core/config.zig imports "logger.zig" (same directory)

    // Rule 4: Can chain ".." to go up multiple levels
    // (Not demonstrated here, but "../../module.zig" would work)

    try testing.expect(true);
}
// ANCHOR_END: relative_path_rules

// ANCHOR: package_organization_benefits
// Benefits of relative imports
test "package organization benefits" {
    // Benefit 1: Clear module relationships
    const config = core.Config.init("localhost", 8080);

    // Benefit 2: Self-contained packages
    const db = services.Database.init(config);

    // Benefit 3: Easy refactoring (move modules together)
    const api = services.API.init(config);

    // Benefit 4: No global namespace pollution
    // Each module explicitly declares its dependencies
    try testing.expectEqualStrings(config.host, db.config.host);
    try testing.expectEqualStrings(config.host, api.db.config.host);
}
// ANCHOR_END: package_organization_benefits

// ANCHOR: avoiding_circular_imports
// Avoid circular dependencies with proper layering
test "avoiding circular imports" {
    // Good: Layered architecture
    // core/ (foundation layer) - no dependencies on services/
    // services/ (application layer) - depends on core/

    // Core modules don't import services
    const config = core.Config.init("localhost", 8080);

    // Services import core (one-way dependency)
    const db = services.Database.init(config);

    // This creates a clear dependency hierarchy
    try testing.expectEqualStrings(config.host, db.config.host);
}
// ANCHOR_END: avoiding_circular_imports

// Comprehensive test
test "comprehensive relative imports" {
    // Use core modules
    const config = core.Config.init("comprehensive.test", 8080);
    try testing.expect(config.validate());

    // Use services that import core
    var db = services.Database.init(config);
    try db.connect();
    try testing.expect(db.connected);

    // Use API that imports both services and core
    var api = services.API.init(config);
    try api.start();
    try testing.expect(api.db.connected);

    // Cleanup
    api.stop();
    try testing.expect(!api.db.connected);

    try testing.expect(true);
}
```

### See Also

- Recipe 10.1: Making a hierarchical package of modules
- Recipe 10.4: Splitting a module into multiple files
- Recipe 10.5: Making separate directories of code import under a common namespace

---

## Recipe 10.4: Splitting a Module into Multiple Files {#recipe-10-4}

**Tags:** allocators, arraylist, build-system, data-structures, error-handling, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_4.zig`

### Problem

Your module has grown too large and handles multiple responsibilities. You want to split it into smaller, focused files organized by concern (types, validation, storage) while maintaining a simple, unified public API. You need to avoid forcing users to import from multiple files.

### Solution

Use the aggregator pattern: split your module into multiple specialized files, then create a main module that imports and re-exports them. Organize files by responsibility (types, logic, storage) and use relative imports to connect them. The aggregator provides a single import point for users.

### Module Structure

Create a directory for your split module:

```
recipe_10_4/
├── user_manager.zig (aggregator - public API)
├── user_types.zig (data structures)
├── user_validation.zig (validation logic)
└── user_storage.zig (storage operations)
```

### Importing the Aggregator

Users import only the aggregator module:

```zig
// Import the aggregator module which re-exports the split components
const UserManager = @import("recipe_10_4/user_manager.zig");
```

The aggregator re-exports everything users need.

### Using the Split Module

Access all functionality through the aggregator:

```zig
test "using split module" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Use the aggregated API - implementation is split across files
    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    const user = UserManager.User{
        .id = 1,
        .username = "alice",
        .email = "alice@example.com",
        .age = 25,
    };

    try manager.addUser(user);
    try testing.expectEqual(@as(usize, 1), manager.count());
}
```

Users don't need to know the implementation is split.

### Discussion

### Step 1: Define Types

Create `user_types.zig` for data structures:

```zig
// User data structures and types
const std = @import("std");

pub const User = struct {
    id: u32,
    username: []const u8,
    email: []const u8,
    age: u8,
};

pub const UserError = error{
    InvalidUser,
    UserNotFound,
    DuplicateUser,
};
```

Types have no dependencies except the standard library.

### Step 2: Implement Validation

Create `user_validation.zig` for validation logic:

```zig
// User validation logic
const std = @import("std");
const types = @import("user_types.zig");

pub fn validateUser(user: *const types.User) bool {
    if (user.id == 0) return false;
    if (!validateUsername(user.username)) return false;
    if (!validateEmail(user.email)) return false;
    if (!validateAge(user.age)) return false;
    return true;
}

pub fn validateUsername(username: []const u8) bool {
    if (username.len < 3) return false;
    if (username.len > 32) return false;

    // Username must contain only alphanumeric and underscores
    for (username) |c| {
        const valid = (c >= 'a' and c <= 'z') or
            (c >= 'A' and c <= 'Z') or
            (c >= '0' and c <= '9') or
            c == '_';
        if (!valid) return false;
    }

    return true;
}

pub fn validateEmail(email: []const u8) bool {
    if (email.len < 5) return false;

    // Simple email validation: must contain @ and . after @
    var has_at = false;
    var at_index: usize = 0;

    for (email, 0..) |c, i| {
        if (c == '@') {
            if (has_at) return false; // Multiple @ symbols
            if (i == 0) return false; // @ at start
            has_at = true;
            at_index = i;
        }
    }

    if (!has_at) return false;
    if (at_index == email.len - 1) return false; // @ at end

    // Check for . after @
    const domain = email[at_index + 1 ..];
    var has_dot = false;
    for (domain) |c| {
        if (c == '.') {
            has_dot = true;
            break;
        }
    }

    return has_dot;
}

pub fn validateAge(age: u8) bool {
    return age >= 18 and age <= 120;
}
```

Validation imports types but has no storage dependencies.

### Step 3: Implement Storage

Create `user_storage.zig` for storage operations:

```zig
// User storage operations
const std = @import("std");
const types = @import("user_types.zig");
const validation = @import("user_validation.zig");

pub const Storage = struct {
    users: std.ArrayList(types.User),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) !Storage {
        return .{
            .users = .{},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Storage) void {
        self.users.deinit(self.allocator);
    }

    pub fn addUser(self: *Storage, user: types.User) !void {
        if (!validation.validateUser(&user)) {
            return error.InvalidUser;
        }

        // Check for duplicate ID
        for (self.users.items) |existing| {
            if (existing.id == user.id) {
                return error.DuplicateUser;
            }
        }

        try self.users.append(self.allocator, user);
    }

    pub fn findUser(self: *Storage, id: u32) ?*types.User {
        for (self.users.items) |*user| {
            if (user.id == id) {
                return user;
            }
        }
        return null;
    }

    pub fn removeUser(self: *Storage, id: u32) bool {
        for (self.users.items, 0..) |user, i| {
            if (user.id == id) {
                _ = self.users.swapRemove(i);
                return true;
            }
        }
        return false;
    }

    pub fn count(self: *const Storage) usize {
        return self.users.items.len;
    }

    pub fn clear(self: *Storage) void {
        self.users.clearRetainingCapacity();
    }
};
```

Storage imports both types and validation.

### Step 4: Create the Aggregator

Create `user_manager.zig` to unify the API:

```zig
// User Manager - Aggregator module
const std = @import("std");

// Import the split components
const types = @import("user_types.zig");
const validation = @import("user_validation.zig");
const storage = @import("user_storage.zig");

// Re-export types for public API
pub const User = types.User;
pub const UserError = types.UserError;

// Re-export validation functions
pub const validateUser = validation.validateUser;
pub const validateUsername = validation.validateUsername;
pub const validateEmail = validation.validateEmail;
pub const validateAge = validation.validateAge;

// Provide a convenience wrapper around storage
const Storage = storage.Storage;

pub fn init(allocator: std.mem.Allocator) !Storage {
    return Storage.init(allocator);
}

pub const deinit = Storage.deinit;
pub const addUser = Storage.addUser;
pub const findUser = Storage.findUser;
pub const removeUser = Storage.removeUser;
pub const count = Storage.count;
pub const clear = Storage.clear;
```

The aggregator imports all components and re-exports their public interfaces.

### Accessing Types

Types are accessible through the aggregator:

```zig
test "accessing types from split module" {
    // Types are re-exported from the aggregator
    const user: UserManager.User = .{
        .id = 1,
        .username = "bob",
        .email = "bob@example.com",
        .age = 30,
    };

    try testing.expectEqual(@as(u32, 1), user.id);
    try testing.expectEqualStrings("bob", user.username);
}
```

Users access `UserManager.User`, not `user_types.User`.

### Validation Through Aggregator

Validation functions work through the aggregator:

```zig
test "validation through aggregator" {
    // Validation functions are exposed through the aggregator
    const valid_user = UserManager.User{
        .id = 1,
        .username = "charlie",
        .email = "charlie@example.com",
        .age = 25,
    };

    try testing.expect(UserManager.validateUser(&valid_user));

    const invalid_user = UserManager.User{
        .id = 0,
        .username = "",
        .email = "invalid",
        .age = 150,
    };

    try testing.expect(!UserManager.validateUser(&invalid_user));
}
```

All validation is centralized and accessible.

### Storage Operations

Storage operations work seamlessly:

```zig
test "storage operations" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    const user1 = UserManager.User{
        .id = 1,
        .username = "dave",
        .email = "dave@example.com",
        .age = 28,
    };

    const user2 = UserManager.User{
        .id = 2,
        .username = "eve",
        .email = "eve@example.com",
        .age = 32,
    };

    try manager.addUser(user1);
    try manager.addUser(user2);

    const found = manager.findUser(1);
    try testing.expect(found != null);
    try testing.expectEqualStrings("dave", found.?.username);

    const not_found = manager.findUser(999);
    try testing.expect(not_found == null);
}
```

Storage, validation, and types work together transparently.

### Error Handling

Errors propagate through the aggregator:

```zig
test "error handling in split module" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    // Invalid user should fail validation
    const invalid_user = UserManager.User{
        .id = 0,
        .username = "",
        .email = "bad",
        .age = 150,
    };

    const result = manager.addUser(invalid_user);
    try testing.expectError(error.InvalidUser, result);
}
```

Validation errors are returned to the caller.

### Username Validation

Test username validation rules:

```zig
test "username validation" {
    // Valid usernames
    try testing.expect(UserManager.validateUsername("alice"));
    try testing.expect(UserManager.validateUsername("bob123"));
    try testing.expect(UserManager.validateUsername("user_name"));

    // Invalid usernames
    try testing.expect(!UserManager.validateUsername(""));
    try testing.expect(!UserManager.validateUsername("ab"));
    try testing.expect(!UserManager.validateUsername("this_username_is_way_too_long_to_be_valid"));
}
```

Usernames must be 3-32 characters, alphanumeric plus underscores.

### Email Validation

Test email validation:

```zig
test "email validation" {
    // Valid emails
    try testing.expect(UserManager.validateEmail("user@example.com"));
    try testing.expect(UserManager.validateEmail("test.user@domain.org"));
    try testing.expect(UserManager.validateEmail("name+tag@site.co.uk"));

    // Invalid emails
    try testing.expect(!UserManager.validateEmail(""));
    try testing.expect(!UserManager.validateEmail("notanemail"));
    try testing.expect(!UserManager.validateEmail("missing@domain"));
    try testing.expect(!UserManager.validateEmail("@nodomain.com"));
}
```

Emails must contain @ with a domain including a dot.

### Age Validation

Test age bounds:

```zig
test "age validation" {
    // Valid ages
    try testing.expect(UserManager.validateAge(18));
    try testing.expect(UserManager.validateAge(25));
    try testing.expect(UserManager.validateAge(120));

    // Invalid ages
    try testing.expect(!UserManager.validateAge(0));
    try testing.expect(!UserManager.validateAge(17));
    try testing.expect(!UserManager.validateAge(121));
}
```

Age must be between 18 and 120 inclusive.

### Bulk Operations

Manage multiple users:

```zig
test "bulk operations" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    const users = [_]UserManager.User{
        .{ .id = 1, .username = "user1", .email = "user1@test.com", .age = 25 },
        .{ .id = 2, .username = "user2", .email = "user2@test.com", .age = 30 },
        .{ .id = 3, .username = "user3", .email = "user3@test.com", .age = 35 },
    };

    for (users) |user| {
        try manager.addUser(user);
    }

    try testing.expectEqual(@as(usize, 3), manager.count());

    // Remove one user
    const removed = manager.removeUser(2);
    try testing.expect(removed);
    try testing.expectEqual(@as(usize, 2), manager.count());

    // Try to remove non-existent user
    const not_removed = manager.removeUser(999);
    try testing.expect(!not_removed);
}
```

The API supports efficient batch operations.

### Clear All Users

Reset the storage:

```zig
test "clear all users" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    try manager.addUser(.{ .id = 1, .username = "user1", .email = "u1@test.com", .age = 25 });
    try manager.addUser(.{ .id = 2, .username = "user2", .email = "u2@test.com", .age = 30 });

    try testing.expectEqual(@as(usize, 2), manager.count());

    manager.clear();
    try testing.expectEqual(@as(usize, 0), manager.count());
}
```

Clearing retains capacity for performance.

### Organizational Benefits

Splitting modules provides clear advantages:

```zig
test "organizational benefits of splitting" {
    // Benefit 1: Types are in a dedicated file (user_types.zig)
    // Benefit 2: Validation logic is separate (user_validation.zig)
    // Benefit 3: Storage operations are isolated (user_storage.zig)
    // Benefit 4: Aggregator provides unified API (user_manager.zig)

    // Users interact with a single clean interface
    const user = UserManager.User{
        .id = 1,
        .username = "organized",
        .email = "org@example.com",
        .age = 25,
    };

    // But implementation is logically organized across files
    try testing.expect(UserManager.validateUser(&user));
}
```

Each file has a single, clear responsibility.

### Dependency Layering

Organize modules in layers:

```
Layer 1: user_types.zig (no dependencies)
         ↑
Layer 2: user_validation.zig (depends on types)
         ↑
Layer 3: user_storage.zig (depends on types + validation)
         ↑
Layer 4: user_manager.zig (aggregates all layers)
```

Dependencies flow in one direction, preventing circular imports.

### Module Responsibilities

Each file has a focused purpose:

**user_types.zig (Data Layer):**
- Define data structures
- Define error types
- No logic, just definitions

**user_validation.zig (Logic Layer):**
- Stateless validation functions
- No storage dependencies
- Pure functions

**user_storage.zig (Storage Layer):**
- Stateful operations
- Uses validation before mutations
- Manages ArrayList lifecycle

**user_manager.zig (API Layer):**
- Re-exports public types
- Re-exports public functions
- Single import point for users

### Benefits of Splitting

**Better Organization:**
- Each file is small and focused
- Easy to find specific functionality
- Clear separation of concerns

**Easier Testing:**
- Test validation independently
- Test storage independently
- Integration tests use aggregator

**Simpler Refactoring:**
- Change validation without touching storage
- Change storage implementation without affecting API
- Modify types with clear impact analysis

**Team Collaboration:**
- Different developers can work on different layers
- Merge conflicts are less likely
- Code review is easier with smaller files

### When to Split Modules

Split a module when:

**Size:** File exceeds 300-500 lines
**Responsibilities:** Module handles multiple concerns
**Testing:** Tests become difficult to organize
**Collaboration:** Multiple developers work on the same file

Don't split when:

**Small:** File is under 200 lines
**Cohesive:** All code serves a single purpose
**Simple:** Few public functions
**Stable:** Code rarely changes

### Best Practices

**Use Layered Dependencies:**
```
foundation → logic → storage → API
```

**Keep Aggregator Thin:**
```zig
// Good: Just re-exports
pub const User = types.User;
pub const validate = validation.validate;

// Bad: Logic in aggregator
pub fn processUser(user: User) !void {
    // Complex logic here - belongs in a layer file
}
```

**Name Files Clearly:**
```
user_types.zig     (not types.zig)
user_validation.zig (not validate.zig)
user_storage.zig   (not store.zig)
```

**Document Dependencies:**
```zig
// user_storage.zig - depends on types and validation
const types = @import("user_types.zig");
const validation = @import("user_validation.zig");
```

### Common Patterns

**Simple Aggregator:**
```zig
pub const Type = submodule.Type;
pub const function = submodule.function;
```

**Wrapper Aggregator:**
```zig
pub fn init(allocator: std.mem.Allocator) !Storage {
    return Storage.init(allocator);
}
```

**Selective Export:**
```zig
// Export only public API, hide internals
pub const Public = internal.PublicType;
// Don't export: internal.PrivateType
```

### Preventing Circular Dependencies

Avoid cycles by layering:

**Bad (Circular):**
```
validation.zig imports storage.zig
storage.zig imports validation.zig
```

**Good (Layered):**
```
types.zig (no dependencies)
validation.zig imports types.zig
storage.zig imports types.zig + validation.zig
```

Cycles indicate unclear responsibilities - refactor to extract shared types.

### Testing Split Modules

Test each layer independently:

```zig
// Test validation alone
test "validation logic" {
    const valid = validation.validateUsername("alice");
    try testing.expect(valid);
}

// Test storage with mocked validation
test "storage operations" {
    var manager = try Storage.init(allocator);
    defer manager.deinit();
    // ...
}

// Integration test through aggregator
test "complete workflow" {
    var manager = try UserManager.init(allocator);
    defer manager.deinit();
    // ...
}
```

### File Size Guidelines

Keep files focused and readable:

**Types:** 50-150 lines (simple definitions)
**Validation:** 100-300 lines (logic functions)
**Storage:** 200-500 lines (stateful operations)
**Aggregator:** 50-100 lines (just re-exports)

If a file grows larger, consider splitting it further.

### Refactoring to Split Modules

Start with a large module:

```zig
// user.zig - 800 lines, too large
pub const User = struct { ... };
pub fn validate(...) bool { ... }
pub const Storage = struct { ... };
```

Extract types first:

```zig
// user_types.zig - new file
pub const User = struct { ... };
```

Then extract validation:

```zig
// user_validation.zig - new file
const types = @import("user_types.zig");
pub fn validate(user: *const types.User) bool { ... }
```

Then extract storage:

```zig
// user_storage.zig - new file
const types = @import("user_types.zig");
const validation = @import("user_validation.zig");
pub const Storage = struct { ... };
```

Finally create aggregator:

```zig
// user.zig - now an aggregator
const types = @import("user_types.zig");
const validation = @import("user_validation.zig");
const storage = @import("user_storage.zig");

pub const User = types.User;
pub const validate = validation.validate;
pub const Storage = storage.Storage;
```

Users' code doesn't change - they still import `user.zig`.

### Full Tested Code

```zig
// Recipe 10.4: Splitting a Module into Multiple Files
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to split a large module into multiple files
// while maintaining a clean public API through an aggregator module.
//
// Package structure:
// recipe_10_4.zig (root test file)
// └── recipe_10_4/
//     ├── user_manager.zig (aggregator - public API)
//     ├── user_types.zig (data structures)
//     ├── user_validation.zig (validation logic)
//     └── user_storage.zig (storage operations)

const std = @import("std");
const testing = std.testing;

// ANCHOR: import_aggregator
// Import the aggregator module which re-exports the split components
const UserManager = @import("recipe_10_4/user_manager.zig");
// ANCHOR_END: import_aggregator

// ANCHOR: using_split_module
test "using split module" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }
    const allocator = gpa.allocator();

    // Use the aggregated API - implementation is split across files
    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    const user = UserManager.User{
        .id = 1,
        .username = "alice",
        .email = "alice@example.com",
        .age = 25,
    };

    try manager.addUser(user);
    try testing.expectEqual(@as(usize, 1), manager.count());
}
// ANCHOR_END: using_split_module

// ANCHOR: type_access
test "accessing types from split module" {
    // Types are re-exported from the aggregator
    const user: UserManager.User = .{
        .id = 1,
        .username = "bob",
        .email = "bob@example.com",
        .age = 30,
    };

    try testing.expectEqual(@as(u32, 1), user.id);
    try testing.expectEqualStrings("bob", user.username);
}
// ANCHOR_END: type_access

// ANCHOR: validation_through_aggregator
test "validation through aggregator" {
    // Validation functions are exposed through the aggregator
    const valid_user = UserManager.User{
        .id = 1,
        .username = "charlie",
        .email = "charlie@example.com",
        .age = 25,
    };

    try testing.expect(UserManager.validateUser(&valid_user));

    const invalid_user = UserManager.User{
        .id = 0,
        .username = "",
        .email = "invalid",
        .age = 150,
    };

    try testing.expect(!UserManager.validateUser(&invalid_user));
}
// ANCHOR_END: validation_through_aggregator

// ANCHOR: storage_operations
test "storage operations" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }
    const allocator = gpa.allocator();

    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    const user1 = UserManager.User{
        .id = 1,
        .username = "dave",
        .email = "dave@example.com",
        .age = 28,
    };

    const user2 = UserManager.User{
        .id = 2,
        .username = "eve",
        .email = "eve@example.com",
        .age = 32,
    };

    try manager.addUser(user1);
    try manager.addUser(user2);

    const found = manager.findUser(1);
    try testing.expect(found != null);
    try testing.expectEqualStrings("dave", found.?.username);

    const not_found = manager.findUser(999);
    try testing.expect(not_found == null);
}
// ANCHOR_END: storage_operations

// ANCHOR: error_handling
test "error handling in split module" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }
    const allocator = gpa.allocator();

    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    // Invalid user should fail validation
    const invalid_user = UserManager.User{
        .id = 0,
        .username = "",
        .email = "bad",
        .age = 150,
    };

    const result = manager.addUser(invalid_user);
    try testing.expectError(error.InvalidUser, result);
}
// ANCHOR_END: error_handling

// ANCHOR: username_validation
test "username validation" {
    // Valid usernames
    try testing.expect(UserManager.validateUsername("alice"));
    try testing.expect(UserManager.validateUsername("bob123"));
    try testing.expect(UserManager.validateUsername("user_name"));

    // Invalid usernames
    try testing.expect(!UserManager.validateUsername(""));
    try testing.expect(!UserManager.validateUsername("ab"));
    try testing.expect(!UserManager.validateUsername("this_username_is_way_too_long_to_be_valid"));
}
// ANCHOR_END: username_validation

// ANCHOR: email_validation
test "email validation" {
    // Valid emails
    try testing.expect(UserManager.validateEmail("user@example.com"));
    try testing.expect(UserManager.validateEmail("test.user@domain.org"));
    try testing.expect(UserManager.validateEmail("name+tag@site.co.uk"));

    // Invalid emails
    try testing.expect(!UserManager.validateEmail(""));
    try testing.expect(!UserManager.validateEmail("notanemail"));
    try testing.expect(!UserManager.validateEmail("missing@domain"));
    try testing.expect(!UserManager.validateEmail("@nodomain.com"));
}
// ANCHOR_END: email_validation

// ANCHOR: age_validation
test "age validation" {
    // Valid ages
    try testing.expect(UserManager.validateAge(18));
    try testing.expect(UserManager.validateAge(25));
    try testing.expect(UserManager.validateAge(120));

    // Invalid ages
    try testing.expect(!UserManager.validateAge(0));
    try testing.expect(!UserManager.validateAge(17));
    try testing.expect(!UserManager.validateAge(121));
}
// ANCHOR_END: age_validation

// ANCHOR: bulk_operations
test "bulk operations" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }
    const allocator = gpa.allocator();

    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    const users = [_]UserManager.User{
        .{ .id = 1, .username = "user1", .email = "user1@test.com", .age = 25 },
        .{ .id = 2, .username = "user2", .email = "user2@test.com", .age = 30 },
        .{ .id = 3, .username = "user3", .email = "user3@test.com", .age = 35 },
    };

    for (users) |user| {
        try manager.addUser(user);
    }

    try testing.expectEqual(@as(usize, 3), manager.count());

    // Remove one user
    const removed = manager.removeUser(2);
    try testing.expect(removed);
    try testing.expectEqual(@as(usize, 2), manager.count());

    // Try to remove non-existent user
    const not_removed = manager.removeUser(999);
    try testing.expect(!not_removed);
}
// ANCHOR_END: bulk_operations

// ANCHOR: clear_all
test "clear all users" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }
    const allocator = gpa.allocator();

    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    try manager.addUser(.{ .id = 1, .username = "user1", .email = "u1@test.com", .age = 25 });
    try manager.addUser(.{ .id = 2, .username = "user2", .email = "u2@test.com", .age = 30 });

    try testing.expectEqual(@as(usize, 2), manager.count());

    manager.clear();
    try testing.expectEqual(@as(usize, 0), manager.count());
}
// ANCHOR_END: clear_all

// ANCHOR: organizational_benefits
test "organizational benefits of splitting" {
    // Benefit 1: Types are in a dedicated file (user_types.zig)
    // Benefit 2: Validation logic is separate (user_validation.zig)
    // Benefit 3: Storage operations are isolated (user_storage.zig)
    // Benefit 4: Aggregator provides unified API (user_manager.zig)

    // Users interact with a single clean interface
    const user = UserManager.User{
        .id = 1,
        .username = "organized",
        .email = "org@example.com",
        .age = 25,
    };

    // But implementation is logically organized across files
    try testing.expect(UserManager.validateUser(&user));
}
// ANCHOR_END: organizational_benefits

// Comprehensive test
test "comprehensive split module usage" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }
    const allocator = gpa.allocator();

    var manager = try UserManager.init(allocator);
    defer manager.deinit();

    const users = [_]UserManager.User{
        .{ .id = 1, .username = "alice", .email = "alice@example.com", .age = 25 },
        .{ .id = 2, .username = "bob", .email = "bob@example.com", .age = 30 },
        .{ .id = 3, .username = "charlie", .email = "charlie@example.com", .age = 35 },
    };

    for (users) |user| {
        try testing.expect(UserManager.validateUser(&user));
        try manager.addUser(user);
    }

    try testing.expectEqual(@as(usize, 3), manager.count());

    for (users) |user| {
        const found = manager.findUser(user.id);
        try testing.expect(found != null);
        try testing.expectEqualStrings(user.username, found.?.username);
    }

    const removed = manager.removeUser(2);
    try testing.expect(removed);
    try testing.expectEqual(@as(usize, 2), manager.count());

    manager.clear();
    try testing.expectEqual(@as(usize, 0), manager.count());
}
```

### See Also

- Recipe 10.1: Making a hierarchical package of modules
- Recipe 10.2: Controlling the export of symbols
- Recipe 10.3: Importing package submodules using relative names
- Recipe 10.5: Making separate directories of code import under a common namespace

---

## Recipe 10.5: Making Separate Directories of Code Import Under a Common Namespace {#recipe-10-5}

**Tags:** allocators, build-system, c-interop, concurrency, memory, testing, threading
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_5.zig`

### Problem

You have multiple independent feature modules (auth, billing, analytics) organized in separate directories. You want users to access all features through a common namespace (`features.auth`, `features.billing`, `features.analytics`) instead of importing each directory separately. You need a clean organizational structure that makes adding new features straightforward.

### Solution

Create a namespace aggregator module that imports all feature directories and re-exports them under a common namespace. Each feature lives in its own directory with its own submodules. The aggregator provides a single import point and consistent access pattern.

### Module Structure

Organize features in separate directories:

```
recipe_10_5/
├── features.zig (namespace aggregator)
├── auth/
│   ├── auth.zig
│   └── auth/login.zig
├── billing/
│   ├── billing.zig
│   └── billing/invoice.zig
└── analytics/
    ├── analytics.zig
    └── analytics/tracking.zig
```

### Import the Namespace

Users import only the namespace aggregator:

```zig
// Anchor 'namespace_imports' not found in ../../../code/03-advanced/10-modules-build-system/recipe_10_5.zig
```

All features are accessible through this single import.

### Using Features Through the Namespace

Access all features through the common namespace:

```zig
test "accessing features through namespace" {
    // All features are accessible through the common namespace
    const auth_result = features.auth.authenticate("alice", "password123");
    try testing.expect(auth_result);

    const invoice = features.billing.Invoice{
        .id = 1,
        .customer = "ACME Corp",
        .amount = 1000.50,
    };
    try testing.expectEqual(@as(u32, 1), invoice.id);

    const event = features.analytics.Event{
        .name = "page_view",
        .user_id = 42,
        .timestamp = 1234567890,
    };
    features.analytics.track(event);
}
```

Clear organization: `features.{feature}.{function}`.

### Discussion

### Creating the Namespace Aggregator

The `features.zig` file imports and re-exports all feature modules:

```zig
// Features namespace aggregator
const std = @import("std");

// Import each feature directory's main module
pub const auth = @import("auth/auth.zig");
pub const billing = @import("billing/billing.zig");
pub const analytics = @import("analytics/analytics.zig");
```

This creates the namespace structure:
- `features.auth` (authentication feature)
- `features.billing` (billing feature)
- `features.analytics` (analytics feature)

### Auth Feature

The auth feature demonstrates a stateful module:

```zig
// Authentication feature module
const std = @import("std");
const login = @import("auth/login.zig");

pub const User = struct {
    id: u32,
    username: []const u8,
};

// Simple in-memory auth state (for demonstration)
// WARNING: Global state is NOT thread-safe and for demonstration only.
// Production code should use explicit context structs passed to functions.
var current_user: ?User = null;
var logged_in: bool = false;

pub fn authenticate(username: []const u8, password: []const u8) bool {
    // Use login module for authentication logic
    const result = login.verifyCredentials(username, password);

    if (result) {
        current_user = User{
            .id = 1,
            .username = username,
        };
        logged_in = true;
    }

    return result;
}

pub fn logout() void {
    current_user = null;
    logged_in = false;
}

pub fn isLoggedIn() bool {
    return logged_in;
}

pub fn getCurrentUser() User {
    return current_user orelse User{ .id = 0, .username = "guest" };
}
```

The auth feature maintains state and provides authentication services.

Test the auth feature:

```zig
test "auth feature" {
    // Authentication through namespace
    try testing.expect(features.auth.authenticate("alice", "password123"));
    try testing.expect(!features.auth.authenticate("alice", "wrong"));

    const user = features.auth.getCurrentUser();
    try testing.expectEqualStrings("alice", user.username);

    features.auth.logout();
    try testing.expect(!features.auth.isLoggedIn());
}
```

### Billing Feature

The billing feature demonstrates a stateless module:

```zig
// Billing feature module
const std = @import("std");
const invoice_mod = @import("billing/invoice.zig");

pub const Invoice = struct {
    id: u32,
    customer: []const u8,
    amount: f64,
};

pub fn calculateTotal(invoice: *const Invoice, tax_rate: f64) f64 {
    return invoice_mod.applyTax(invoice.amount, tax_rate);
}
```

Billing works on data structures without maintaining state.

Test the billing feature:

```zig
test "billing feature" {
    // Billing operations through namespace
    const invoice = features.billing.Invoice{
        .id = 123,
        .customer = "Test Customer",
        .amount = 500.00,
    };

    try testing.expectEqual(@as(u32, 123), invoice.id);
    try testing.expectEqualStrings("Test Customer", invoice.customer);
    try testing.expectApproxEqAbs(@as(f64, 500.00), invoice.amount, 0.01);

    const total = features.billing.calculateTotal(&invoice, 0.1);
    try testing.expectApproxEqAbs(@as(f64, 550.00), total, 0.01);
}
```

### Analytics Feature

The analytics feature demonstrates event tracking:

```zig
// Analytics feature module
const std = @import("std");
const tracking = @import("analytics/tracking.zig");

pub const Event = struct {
    name: []const u8,
    user_id: u32,
    timestamp: u64,
};

// Simple in-memory event storage (for demonstration)
// WARNING: Global state is NOT thread-safe and for demonstration only.
// Production code should use explicit context structs passed to functions.
var event_count: usize = 0;

pub fn track(event: Event) void {
    tracking.recordEvent(event);
    event_count += 1;
}

pub fn getEventCount() usize {
    return event_count;
}

pub fn reset() void {
    event_count = 0;
}
```

Analytics tracks events and maintains counts.

Test the analytics feature:

```zig
test "analytics feature" {
    // Reset analytics state for clean test
    features.analytics.reset();

    // Analytics through namespace
    const event1 = features.analytics.Event{
        .name = "button_click",
        .user_id = 1,
        .timestamp = 1000,
    };

    const event2 = features.analytics.Event{
        .name = "page_view",
        .user_id = 2,
        .timestamp = 2000,
    };

    features.analytics.track(event1);
    features.analytics.track(event2);

    const count = features.analytics.getEventCount();
    try testing.expectEqual(@as(usize, 2), count);

    features.analytics.reset();
    try testing.expectEqual(@as(usize, 0), features.analytics.getEventCount());
}
```

### Cross-Feature Usage

Features work together through the namespace:

```zig
test "using multiple features together" {
    // Reset state for clean test
    features.analytics.reset();
    features.auth.logout();

    // Features can work together through the common namespace

    // Authenticate user
    const logged_in = features.auth.authenticate("bob", "secret123");
    try testing.expect(logged_in);

    // Track login event
    const login_event = features.analytics.Event{
        .name = "user_login",
        .user_id = 1,
        .timestamp = 1234567890,
    };
    features.analytics.track(login_event);

    // Create invoice for logged-in user
    const user = features.auth.getCurrentUser();
    const invoice = features.billing.Invoice{
        .id = 1,
        .customer = user.username,
        .amount = 99.99,
    };

    try testing.expectEqualStrings("bob", invoice.customer);

    // Track billing event
    const billing_event = features.analytics.Event{
        .name = "invoice_created",
        .user_id = user.id,
        .timestamp = 1234567891,
    };
    features.analytics.track(billing_event);

    try testing.expectEqual(@as(usize, 2), features.analytics.getEventCount());
}
```

Features coordinate through the shared namespace without direct imports.

### Namespace Benefits

The namespace pattern provides clear advantages:

```zig
test "namespace benefits" {
    // Benefit 1: All features under one import
    // Benefit 2: Clear feature separation
    // Benefit 3: Easy to add new features
    // Benefit 4: Features can be developed independently

    // Single import gives access to all features
    try testing.expect(features.auth.authenticate("test", "password"));
    _ = features.billing.Invoice{ .id = 1, .customer = "Test", .amount = 100 };
    _ = features.analytics.Event{ .name = "test", .user_id = 1, .timestamp = 0 };
}
```

One import provides access to the entire feature set.

### Feature Independence

Each feature is independent and testable:

```zig
test "feature modules are independent" {
    // Each feature can be tested independently

    // Auth feature
    try testing.expect(features.auth.authenticate("user1", "password1"));

    // Billing feature (doesn't depend on auth being called)
    const inv = features.billing.Invoice{
        .id = 1,
        .customer = "Customer",
        .amount = 100,
    };
    try testing.expectEqual(@as(u32, 1), inv.id);

    // Analytics feature (doesn't depend on others)
    features.analytics.reset();
    try testing.expectEqual(@as(usize, 0), features.analytics.getEventCount());
}
```

Features don't require each other to function.

### Namespace Organization

Clear organizational structure:

```zig
test "namespace organization" {
    // Clear organization: features.{feature}.{function}

    // Auth namespace
    _ = features.auth.authenticate("user", "pass");
    _ = features.auth.logout();
    _ = features.auth.isLoggedIn();

    // Billing namespace
    const invoice = features.billing.Invoice{
        .id = 1,
        .customer = "Test",
        .amount = 50,
    };
    _ = features.billing.calculateTotal(&invoice, 0.1);

    // Analytics namespace
    const event = features.analytics.Event{
        .name = "test",
        .user_id = 1,
        .timestamp = 0,
    };
    features.analytics.track(event);
    _ = features.analytics.getEventCount();

    try testing.expect(true);
}
```

Consistent access pattern across all features.

### Adding New Features

The pattern makes extension straightforward:

```zig
test "adding new features is easy" {
    // To add a new feature:
    // 1. Create a new directory: features/newfeature/
    // 2. Create newfeature.zig with public API
    // 3. Add to features.zig: pub const newfeature = @import("newfeature/newfeature.zig");
    // 4. Use it: features.newfeature.doSomething()

    // The namespace pattern makes feature addition straightforward
    try testing.expect(true);
}
```

Adding features requires minimal changes to existing code.

### Feature Isolation

Each feature maintains its own state:

```zig
test "features are isolated" {
    // Each feature directory is self-contained

    // Auth state is isolated
    try testing.expect(features.auth.authenticate("user", "password"));

    // Analytics state is isolated
    const count_before = features.analytics.getEventCount();
    features.analytics.track(.{
        .name = "test",
        .user_id = 1,
        .timestamp = 0,
    });
    try testing.expectEqual(count_before + 1, features.analytics.getEventCount());

    // Billing has no state (just functions on data)
    const inv = features.billing.Invoice{
        .id = 1,
        .customer = "Test",
        .amount = 100,
    };
    _ = features.billing.calculateTotal(&inv, 0.1);
}
```

Features don't interfere with each other.

### Feature Directory Structure

Each feature is self-contained:

```
auth/
├── auth.zig (public API)
└── auth/
    └── login.zig (implementation details)

billing/
├── billing.zig (public API)
└── billing/
    └── invoice.zig (implementation details)

analytics/
├── analytics.zig (public API)
└── analytics/
    └── tracking.zig (implementation details)
```

Public API in the top-level file, implementation in subdirectories.

### Login Verification

The login module provides credential verification:

```zig
// Login verification logic
pub fn verifyCredentials(username: []const u8, password: []const u8) bool {
    // WARNING: This is UNSAFE demonstration code only!
    // NEVER use in production. Always:
    // - Hash passwords with bcrypt/argon2
    // - Validate against secure database
    // - Implement rate limiting
    // - Use constant-time comparison

    if (username.len == 0 or password.len < 6) {
        return false;
    }

    // Accept any username with password length >= 6 (demonstration only!)
    return true;
}
```

This demonstrates the pattern, not secure authentication.

### Invoice Calculations

The invoice module handles tax calculations:

```zig
// Invoice calculation logic
pub fn applyTax(amount: f64, tax_rate: f64) f64 {
    return amount * (1.0 + tax_rate);
}
```

Simple calculation isolated in its own module.

### Event Tracking

The tracking module records events:

```zig
// Event tracking logic
pub fn recordEvent(event: anytype) void {
    // In production, this would send events to an analytics service
    // For demonstration, we just acknowledge the event
    _ = event;
}
```

Placeholder for external service integration.

### Benefits of Namespace Organization

**Single Import Point:**
- Users import one module
- Access all features through namespace
- Consistent API surface

**Clear Organization:**
- Features grouped logically
- Easy to find functionality
- Self-documenting structure

**Independent Development:**
- Features don't share code
- Can be developed separately
- No cross-dependencies

**Easy Extension:**
- Add new features without changing existing code
- Just add to aggregator
- No breaking changes

### When to Use Namespace Aggregation

Use namespace aggregation when:

**Multiple Features:** You have distinct features to organize
**Clear Boundaries:** Features have well-defined responsibilities
**Independent Development:** Different teams work on different features
**Plugin Architecture:** You want to add features dynamically

Don't use namespace aggregation when:

**Single Feature:** Only one feature exists
**Tight Coupling:** Features depend heavily on each other
**Simple API:** A flat module structure is clearer
**Performance Critical:** Extra indirection matters

### Best Practices

**Keep Aggregator Thin:**
```zig
// Good: Just re-exports
pub const auth = @import("auth/auth.zig");
pub const billing = @import("billing/billing.zig");

// Bad: Logic in aggregator
pub fn crossFeatureOperation() void {
    // Don't put logic here
}
```

**Feature Independence:**
```zig
// Good: Features don't import each other
// auth/auth.zig doesn't import billing or analytics

// Bad: Cross-feature imports
// auth/auth.zig imports billing/billing.zig
```

**Consistent Naming:**
```
features/auth/auth.zig
features/billing/billing.zig
features/analytics/analytics.zig
```

**Public API at Top Level:**
```zig
// feature/feature.zig - Public API
pub const Type = ...;
pub fn publicFunction() void { ... }

// feature/feature/internal.zig - Implementation details
fn internalFunction() void { ... }
```

### Global State Considerations

The example uses global state for simplicity, but has important limitations:

**Demonstration Pattern:**
```zig
// WARNING: Global state is NOT thread-safe and for demonstration only.
// Production code should use explicit context structs passed to functions.
var current_user: ?User = null;
```

**Production Pattern:**
```zig
// Better: Explicit context struct
pub const AuthContext = struct {
    current_user: ?User,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) AuthContext {
        return .{ .current_user = null, .allocator = allocator };
    }

    pub fn authenticate(self: *AuthContext, username: []const u8, password: []const u8) !void {
        // Thread-safe, explicit state management
    }
};
```

For production code, use context structs instead of global state.

### Testing Strategy

Test features independently:

```zig
// Test each feature in isolation
test "auth works alone" {
    try testing.expect(features.auth.authenticate("user", "password"));
}

test "billing works alone" {
    const inv = features.billing.Invoice{ ... };
    _ = features.billing.calculateTotal(&inv, 0.1);
}

test "analytics works alone" {
    features.analytics.reset();
    features.analytics.track(...);
}
```

Then test integration:

```zig
// Test features working together
test "features integrate" {
    features.auth.authenticate(...);
    const user = features.auth.getCurrentUser();
    const invoice = features.billing.Invoice{ .customer = user.username, ... };
    features.analytics.track(...);
}
```

### Refactoring to Namespace Pattern

Start with separate imports:

```zig
// Before: Multiple imports
const auth = @import("auth.zig");
const billing = @import("billing.zig");
const analytics = @import("analytics.zig");
```

Refactor to namespace:

```zig
// After: Single namespace import
const features = @import("features.zig");

// Access through namespace
features.auth.authenticate(...);
features.billing.calculateTotal(...);
features.analytics.track(...);
```

Create the aggregator:

```zig
// features.zig
pub const auth = @import("auth/auth.zig");
pub const billing = @import("billing/billing.zig");
pub const analytics = @import("analytics/analytics.zig");
```

### Common Patterns

**Simple Aggregator:**
```zig
pub const feature1 = @import("feature1/feature1.zig");
pub const feature2 = @import("feature2/feature2.zig");
```

**Selective Export:**
```zig
const internal = @import("internal/internal.zig");
pub const PublicAPI = internal.PublicType;
// Don't export internal.PrivateType
```

**Nested Namespaces:**
```zig
pub const core = struct {
    pub const auth = @import("core/auth.zig");
    pub const config = @import("core/config.zig");
};

pub const plugins = struct {
    pub const billing = @import("plugins/billing.zig");
    pub const analytics = @import("plugins/analytics.zig");
};
```

### Directory Naming Conventions

Use consistent naming:

```
features/
├── auth/ (feature name)
│   └── auth.zig (feature name + .zig)
├── billing/
│   └── billing.zig
└── analytics/
    └── analytics.zig
```

This makes the structure predictable and easy to navigate.

### Documentation Strategy

Document at the namespace level:

```zig
//! Features namespace
//!
//! This module provides access to all application features:
//! - auth: User authentication and authorization
//! - billing: Invoice generation and payment processing
//! - analytics: Event tracking and analytics

pub const auth = @import("auth/auth.zig");
pub const billing = @import("billing/billing.zig");
pub const analytics = @import("analytics/analytics.zig");
```

Document each feature:

```zig
//! Authentication feature
//!
//! Provides user authentication, session management, and access control.
//!
//! WARNING: This implementation uses global state for demonstration.
//! Production code should use explicit context structs.

pub const User = struct { ... };
```

### Performance Considerations

The namespace pattern has minimal overhead:

- **Compile time:** No impact - imports are resolved at compile time
- **Runtime:** Zero overhead - just namespace organization
- **Code size:** No increase - no additional indirection

The pattern is purely organizational with no performance cost.

### Migration Path

Migrate incrementally:

**Step 1:** Create aggregator
```zig
// features.zig
pub const auth = @import("auth.zig");
```

**Step 2:** Update imports
```zig
// Old: const auth = @import("auth.zig");
// New: const features = @import("features.zig");
```

**Step 3:** Move features to directories
```
auth.zig → auth/auth.zig
```

**Step 4:** Update aggregator paths
```zig
pub const auth = @import("auth/auth.zig");
```

Each step is independent and testable.

### Full Tested Code

```zig
// Recipe 10.5: Making Separate Directories of Code Import Under a Common Namespace
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to organize separate feature directories
// under a common namespace using a namespace aggregator module.
//
// Package structure:
// recipe_10_5.zig (root test file)
// └── recipe_10_5/
//     ├── features.zig (namespace aggregator)
//     ├── auth/ (authentication feature)
//     │   ├── auth.zig
//     │   └── auth/login.zig
//     ├── billing/ (billing feature)
//     │   ├── billing.zig
//     │   └── billing/invoice.zig
//     └── analytics/ (analytics feature)
//         ├── analytics.zig
//         └── analytics/tracking.zig

const std = @import("std");
const testing = std.testing;

// ANCHOR: import_namespace
// Import the namespace aggregator
const features = @import("recipe_10_5/features.zig");
// ANCHOR_END: import_namespace

// ANCHOR: accessing_features
test "accessing features through namespace" {
    // All features are accessible through the common namespace
    const auth_result = features.auth.authenticate("alice", "password123");
    try testing.expect(auth_result);

    const invoice = features.billing.Invoice{
        .id = 1,
        .customer = "ACME Corp",
        .amount = 1000.50,
    };
    try testing.expectEqual(@as(u32, 1), invoice.id);

    const event = features.analytics.Event{
        .name = "page_view",
        .user_id = 42,
        .timestamp = 1234567890,
    };
    features.analytics.track(event);
}
// ANCHOR_END: accessing_features

// ANCHOR: auth_feature
test "auth feature" {
    // Authentication through namespace
    try testing.expect(features.auth.authenticate("alice", "password123"));
    try testing.expect(!features.auth.authenticate("alice", "wrong"));

    const user = features.auth.getCurrentUser();
    try testing.expectEqualStrings("alice", user.username);

    features.auth.logout();
    try testing.expect(!features.auth.isLoggedIn());
}
// ANCHOR_END: auth_feature

// ANCHOR: billing_feature
test "billing feature" {
    // Billing operations through namespace
    const invoice = features.billing.Invoice{
        .id = 123,
        .customer = "Test Customer",
        .amount = 500.00,
    };

    try testing.expectEqual(@as(u32, 123), invoice.id);
    try testing.expectEqualStrings("Test Customer", invoice.customer);
    try testing.expectApproxEqAbs(@as(f64, 500.00), invoice.amount, 0.01);

    const total = features.billing.calculateTotal(&invoice, 0.1);
    try testing.expectApproxEqAbs(@as(f64, 550.00), total, 0.01);
}
// ANCHOR_END: billing_feature

// ANCHOR: analytics_feature
test "analytics feature" {
    // Reset analytics state for clean test
    features.analytics.reset();

    // Analytics through namespace
    const event1 = features.analytics.Event{
        .name = "button_click",
        .user_id = 1,
        .timestamp = 1000,
    };

    const event2 = features.analytics.Event{
        .name = "page_view",
        .user_id = 2,
        .timestamp = 2000,
    };

    features.analytics.track(event1);
    features.analytics.track(event2);

    const count = features.analytics.getEventCount();
    try testing.expectEqual(@as(usize, 2), count);

    features.analytics.reset();
    try testing.expectEqual(@as(usize, 0), features.analytics.getEventCount());
}
// ANCHOR_END: analytics_feature

// ANCHOR: cross_feature_usage
test "using multiple features together" {
    // Reset state for clean test
    features.analytics.reset();
    features.auth.logout();

    // Features can work together through the common namespace

    // Authenticate user
    const logged_in = features.auth.authenticate("bob", "secret123");
    try testing.expect(logged_in);

    // Track login event
    const login_event = features.analytics.Event{
        .name = "user_login",
        .user_id = 1,
        .timestamp = 1234567890,
    };
    features.analytics.track(login_event);

    // Create invoice for logged-in user
    const user = features.auth.getCurrentUser();
    const invoice = features.billing.Invoice{
        .id = 1,
        .customer = user.username,
        .amount = 99.99,
    };

    try testing.expectEqualStrings("bob", invoice.customer);

    // Track billing event
    const billing_event = features.analytics.Event{
        .name = "invoice_created",
        .user_id = user.id,
        .timestamp = 1234567891,
    };
    features.analytics.track(billing_event);

    try testing.expectEqual(@as(usize, 2), features.analytics.getEventCount());
}
// ANCHOR_END: cross_feature_usage

// ANCHOR: namespace_benefits
test "namespace benefits" {
    // Benefit 1: All features under one import
    // Benefit 2: Clear feature separation
    // Benefit 3: Easy to add new features
    // Benefit 4: Features can be developed independently

    // Single import gives access to all features
    try testing.expect(features.auth.authenticate("test", "password"));
    _ = features.billing.Invoice{ .id = 1, .customer = "Test", .amount = 100 };
    _ = features.analytics.Event{ .name = "test", .user_id = 1, .timestamp = 0 };
}
// ANCHOR_END: namespace_benefits

// ANCHOR: feature_modules
test "feature modules are independent" {
    // Each feature can be tested independently

    // Auth feature
    try testing.expect(features.auth.authenticate("user1", "password1"));

    // Billing feature (doesn't depend on auth being called)
    const inv = features.billing.Invoice{
        .id = 1,
        .customer = "Customer",
        .amount = 100,
    };
    try testing.expectEqual(@as(u32, 1), inv.id);

    // Analytics feature (doesn't depend on others)
    features.analytics.reset();
    try testing.expectEqual(@as(usize, 0), features.analytics.getEventCount());
}
// ANCHOR_END: feature_modules

// ANCHOR: namespace_organization
test "namespace organization" {
    // Clear organization: features.{feature}.{function}

    // Auth namespace
    _ = features.auth.authenticate("user", "pass");
    _ = features.auth.logout();
    _ = features.auth.isLoggedIn();

    // Billing namespace
    const invoice = features.billing.Invoice{
        .id = 1,
        .customer = "Test",
        .amount = 50,
    };
    _ = features.billing.calculateTotal(&invoice, 0.1);

    // Analytics namespace
    const event = features.analytics.Event{
        .name = "test",
        .user_id = 1,
        .timestamp = 0,
    };
    features.analytics.track(event);
    _ = features.analytics.getEventCount();

    try testing.expect(true);
}
// ANCHOR_END: namespace_organization

// ANCHOR: adding_features
test "adding new features is easy" {
    // To add a new feature:
    // 1. Create a new directory: features/newfeature/
    // 2. Create newfeature.zig with public API
    // 3. Add to features.zig: pub const newfeature = @import("newfeature/newfeature.zig");
    // 4. Use it: features.newfeature.doSomething()

    // The namespace pattern makes feature addition straightforward
    try testing.expect(true);
}
// ANCHOR_END: adding_features

// ANCHOR: feature_isolation
test "features are isolated" {
    // Each feature directory is self-contained

    // Auth state is isolated
    try testing.expect(features.auth.authenticate("user", "password"));

    // Analytics state is isolated
    const count_before = features.analytics.getEventCount();
    features.analytics.track(.{
        .name = "test",
        .user_id = 1,
        .timestamp = 0,
    });
    try testing.expectEqual(count_before + 1, features.analytics.getEventCount());

    // Billing has no state (just functions on data)
    const inv = features.billing.Invoice{
        .id = 1,
        .customer = "Test",
        .amount = 100,
    };
    _ = features.billing.calculateTotal(&inv, 0.1);
}
// ANCHOR_END: feature_isolation

// Comprehensive test
test "comprehensive namespace usage" {
    // Authenticate
    try testing.expect(features.auth.authenticate("alice", "secret"));
    const user = features.auth.getCurrentUser();
    try testing.expectEqual(@as(u32, 1), user.id);

    // Create invoice
    const invoice = features.billing.Invoice{
        .id = 100,
        .customer = user.username,
        .amount = 250.00,
    };
    const total = features.billing.calculateTotal(&invoice, 0.15);
    try testing.expectApproxEqAbs(@as(f64, 287.50), total, 0.01);

    // Track events
    features.analytics.reset();
    features.analytics.track(.{
        .name = "login",
        .user_id = user.id,
        .timestamp = 1000,
    });
    features.analytics.track(.{
        .name = "invoice_created",
        .user_id = user.id,
        .timestamp = 1001,
    });

    try testing.expectEqual(@as(usize, 2), features.analytics.getEventCount());

    // Logout
    features.auth.logout();
    try testing.expect(!features.auth.isLoggedIn());
}
```

### See Also

- Recipe 10.1: Making a hierarchical package of modules
- Recipe 10.3: Importing package submodules using relative names
- Recipe 10.4: Splitting a module into multiple files

---

## Recipe 10.6: Reloading Modules {#recipe-10-6}

**Tags:** allocators, arraylist, atomics, build-system, c-interop, comptime, concurrency, data-structures, error-handling, hashmap, json, memory, parsing, resource-cleanup, synchronization, testing, threading
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_6.zig`

### Problem

You're familiar with dynamic languages like Python's `importlib.reload()` that reload modules at runtime. You want to update module code without restarting your program, or you need to understand how Zig handles module imports and state. You're concerned about module state being shared between different parts of your code.

### Solution

Recognize that Zig is a compiled language with static module resolution. Modules cannot be "reloaded" at runtime like Python. Instead, use Zig-appropriate patterns: understand import caching (modules are singletons at compile time), use reset functions for state management, prefer instance structs over global state, and leverage the build system for code updates.

### Understanding Import Caching

Zig caches `@import()` results at compile time:

```zig
// Zig caches @import() results at compile time
const counter1 = @import("recipe_10_6/counter.zig");
const counter2 = @import("recipe_10_6/counter.zig");
// counter1 and counter2 refer to the SAME module instance
```

Multiple imports of the same module return the same instance.

### Imports Are Cached

Test that imports share the same module:

```zig
test "imports are cached at compile time" {
    // Multiple imports of the same module return the same instance
    const c1 = @import("recipe_10_6/counter.zig");
    const c2 = @import("recipe_10_6/counter.zig");

    // They share the same state
    c1.reset();
    c1.increment();
    c1.increment();

    // c2 sees the same state because it's the same module
    try testing.expectEqual(@as(usize, 2), c2.getValue());
}
```

This is by design - modules are compile-time singletons.

### Discussion

### Module State is Shared

All imports of a module share the same state:

```zig
test "module state is shared across imports" {
    counter1.reset();

    counter1.increment();
    try testing.expectEqual(@as(usize, 1), counter1.getValue());

    // counter2 is the same module, so sees the same state
    try testing.expectEqual(@as(usize, 1), counter2.getValue());

    counter2.increment();
    try testing.expectEqual(@as(usize, 2), counter1.getValue());
}
```

Changes through one import affect all other imports.

### Counter Module

The counter module demonstrates global state:

```zig
// Counter module - demonstrates module state and caching
const std = @import("std");

// Module-level state (shared across all imports)
// NOTE: Global state has limitations - see recipe for alternatives
var count: usize = 0;

pub fn increment() void {
    count += 1;
}

pub fn decrement() void {
    if (count > 0) {
        count -= 1;
    }
}

pub fn getValue() usize {
    return count;
}

pub fn reset() void {
    count = 0;
}

pub fn setValue(value: usize) void {
    count = value;
}
```

Global module state is simple but has testing challenges.

### Reset Pattern

Modules with state should provide reset functions:

```zig
test "resetting module state" {
    // Modules with state should provide reset() functions
    counter1.reset();
    try testing.expectEqual(@as(usize, 0), counter1.getValue());

    counter1.increment();
    counter1.increment();
    counter1.increment();
    try testing.expectEqual(@as(usize, 3), counter1.getValue());

    // Reset to initial state
    counter1.reset();
    try testing.expectEqual(@as(usize, 0), counter1.getValue());
}
```

Reset functions enable clean test isolation.

### Initialization Pattern

For modules needing setup/teardown:

```zig
test "module initialization pattern" {
    // For modules that need setup/teardown, use explicit init/deinit
    defer config.reset(); // Clean up for next test
    config.reset(); // Reset to defaults

    config.setValue("debug_mode", true);
    try testing.expect(config.getValue("debug_mode"));

    config.setIntValue("log_level", 3);
    try testing.expectEqual(@as(i32, 3), config.getIntValue("log_level"));

    // Config will be reset by defer
    try testing.expect(config.getValue("debug_mode"));
}
```

Use defer for automatic cleanup.

### Configuration Module

The config module demonstrates compile-time constants and runtime state:

```zig
// Configuration module
const std = @import("std");

// Compile-time constants - cannot be changed without recompiling
pub const VERSION = "1.0.0";
pub const APP_NAME = "MyApp";
pub const MAX_CONNECTIONS = 100;

// Runtime configuration state
var debug_mode: bool = false;
var log_level: i32 = 0;
var feature_x_enabled: bool = false;
var timeout_seconds: i32 = 30;

// Simple key-value storage for demonstration
var bool_config: std.StringHashMap(bool) = undefined;
var int_config: std.StringHashMap(i32) = undefined;
var initialized: bool = false;

fn ensureInit() void {
    if (!initialized) {
        bool_config = std.StringHashMap(bool).init(std.heap.page_allocator);
        int_config = std.StringHashMap(i32).init(std.heap.page_allocator);
        initialized = true;
    }
}

pub fn setValue(key: []const u8, value: bool) void {
    ensureInit();
    bool_config.put(key, value) catch return;
}

pub fn setIntValue(key: []const u8, value: i32) void {
    ensureInit();
    int_config.put(key, value) catch return;
}

pub fn getValue(key: []const u8) bool {
    ensureInit();
    return bool_config.get(key) orelse false;
}

pub fn getIntValue(key: []const u8) i32 {
    ensureInit();
    return int_config.get(key) orelse 0;
}

pub fn reset() void {
    if (initialized) {
        bool_config.clearRetainingCapacity();
        int_config.clearRetainingCapacity();
    }
    debug_mode = false;
    log_level = 0;
    feature_x_enabled = false;
    timeout_seconds = 30;
}

pub fn deinit() void {
    if (initialized) {
        bool_config.deinit();
        int_config.deinit();
        initialized = false;
    }
}
```

Separate compile-time constants from runtime state.

### Compile-Time Constants

Compile-time constants cannot change without recompilation:

```zig
test "compile-time constants are truly constant" {
    const version = @import("recipe_10_6/config.zig").VERSION;
    const name = @import("recipe_10_6/config.zig").APP_NAME;

    // These are compile-time constants and cannot be "reloaded"
    try testing.expectEqualStrings("1.0.0", version);
    try testing.expectEqualStrings("MyApp", name);

    // To change these, you must recompile
}
```

Use `pub const` for truly constant values.

### Module Singleton Pattern

Each module is a compile-time singleton:

```zig
test "module singleton pattern" {
    // Each module is effectively a singleton at compile time
    const mod1 = @import("recipe_10_6/counter.zig");
    const mod2 = @import("recipe_10_6/counter.zig");

    mod1.reset();
    mod1.increment();

    // Same instance
    try testing.expectEqual(mod1.getValue(), mod2.getValue());

    // You cannot have multiple independent instances
    // (unless the module provides its own instance management)
}
```

Modules are singletons - you can't have multiple independent instances.

### Instance Pattern

To get independent state, use instance structs:

```zig
// To get "reloadable" behavior, use instance structs instead of module globals
const CounterInstance = struct {
    value: usize,

    pub fn init() CounterInstance {
        return .{ .value = 0 };
    }

    pub fn increment(self: *CounterInstance) void {
        self.value += 1;
    }

    pub fn getValue(self: *const CounterInstance) usize {
        return self.value;
    }

    pub fn reset(self: *CounterInstance) void {
        self.value = 0;
    }
};

test "instance pattern for independent state" {
    // Create independent instances instead of using module globals
    var counter_a = CounterInstance.init();
    var counter_b = CounterInstance.init();

    counter_a.increment();
    counter_a.increment();
    try testing.expectEqual(@as(usize, 2), counter_a.getValue());

    counter_b.increment();
    try testing.expectEqual(@as(usize, 1), counter_b.getValue());

    // Independent state
    try testing.expectEqual(@as(usize, 2), counter_a.getValue());
}
```

Instance structs allow multiple independent state containers.

### Avoiding Global State

Global state complicates testing:

```zig
test "avoiding global state for testability" {
    // Global module state makes testing difficult
    // Because imports are cached, tests can interfere with each other

    counter1.reset(); // Must reset before each test

    counter1.increment();
    try testing.expectEqual(@as(usize, 1), counter1.getValue());

    // If we forget to reset, the next test might fail
}
```

Tests must carefully manage shared state.

### Scoped State Management

Use defer for reliable cleanup:

```zig
test "scoped state management" {
    // Better pattern: Use defer for cleanup
    counter1.reset(); // Reset at start for clean state
    defer counter1.reset(); // Always reset after test

    counter1.increment();
    counter1.increment();
    counter1.increment();

    try testing.expectEqual(@as(usize, 3), counter1.getValue());

    // reset() will be called on test exit
}
```

Defer ensures cleanup even if the test fails.

### Configuration Changes

"Reloading" means resetting and applying new values:

```zig
test "configuration changes" {
    defer config.reset();

    // Simulate "reloading" configuration by resetting and setting new values
    config.reset();
    config.setValue("feature_x", true);
    config.setIntValue("timeout", 30);

    try testing.expect(config.getValue("feature_x"));
    try testing.expectEqual(@as(i32, 30), config.getIntValue("timeout"));

    // "Reload" with different values
    config.reset();
    config.setValue("feature_x", false);
    config.setIntValue("timeout", 60);

    try testing.expect(!config.getValue("feature_x"));
    try testing.expectEqual(@as(i32, 60), config.getIntValue("timeout"));
}
```

Runtime state can change, but requires explicit reset and reconfiguration.

### Compile-Time vs Runtime

Understand the distinction:

```zig
test "understanding compile-time vs runtime" {
    // At compile time:
    // - @import() resolves modules
    // - Module structure is fixed
    // - Const values are embedded
    //
    // At runtime:
    // - Module state can change
    // - Functions can be called
    // - Variables can be modified
    //
    // To "reload" code, you must recompile

    const module_version = config.VERSION;
    try testing.expectEqualStrings("1.0.0", module_version);

    // Runtime state can change
    config.setIntValue("runtime_value", 42);
    try testing.expectEqual(@as(i32, 42), config.getIntValue("runtime_value"));
}
```

Compile-time code is baked in; runtime state is mutable.

### Best Practices

Follow these patterns for module state:

```zig
test "best practices for module state" {
    // 1. Prefer stateless modules when possible
    // 2. If state is needed, provide reset() function
    // 3. Use explicit init/deinit for resources
    // 4. Consider instance pattern instead of globals
    // 5. Use defer for cleanup in tests

    defer counter1.reset();

    counter1.increment();
    try testing.expect(counter1.getValue() > 0);
}
```

These patterns prevent state pollution and testing issues.

### Cleanup Resources

Modules that allocate should provide deinit:

```zig
test "cleanup module resources" {
    // For modules that allocate resources, call deinit when done
    // This test should run last to clean up the config module
    defer config.deinit();

    config.setValue("final_test", true);
    try testing.expect(config.getValue("final_test"));

    // deinit() will be called, freeing HashMaps
}
```

Proper cleanup prevents memory leaks.

### When to Use Global State

Global module state is appropriate when:

**Single Instance:** Only one instance makes sense (logger, allocator registry)
**Constant Data:** Tables, lookup maps that never change
**Process-Wide Config:** Settings that apply to entire program

Avoid global state when:

**Testing:** State pollution between tests
**Concurrency:** Thread safety becomes complex
**Flexibility:** Users might want multiple instances
**Isolation:** Components should be independent

### Instance Pattern Benefits

The instance pattern offers advantages:

**Testability:**
- Each test creates fresh instances
- No state pollution
- Parallel test execution possible

**Flexibility:**
- Multiple independent instances
- Different configurations per instance
- Easy to pass around

**Clarity:**
- Explicit state ownership
- Clear initialization/cleanup
- Type-safe state access

### Zig vs Dynamic Languages

Comparison with Python's `reload()`:

**Python:**
```python
import mymodule
# Modify mymodule.py
importlib.reload(mymodule)  # Reload at runtime
```

**Zig Equivalent:**
```zig
// Modify module source
// Run: zig build
// Restart program with new code
```

Zig requires recompilation for code changes.

### Development Workflow

For interactive development:

**Watch Mode:**
```bash
# Use file watcher to trigger rebuild
while inotifywait -r src/; do
    zig build && ./zig-out/bin/myapp
done
```

**Build System Integration:**
```bash
# Some build tools support watch mode
zig build --watch  # (proposed feature)
```

**Dynamic Libraries:**
```zig
// For runtime updates, use dynamic loading
const lib = try std.DynLib.open("plugin.so");
defer lib.close();

const loadFn = lib.lookup(*const fn() void, "pluginInit") orelse return error.SymbolNotFound;
loadFn();
```

Shared libraries enable runtime code updates.

### Thread Safety Considerations

Global state and concurrency:

```zig
// WARNING: Module-level state is NOT thread-safe
var counter: usize = 0;  // Data race if accessed from multiple threads

pub fn increment() void {
    counter += 1;  // Race condition!
}
```

For thread-safe code:

```zig
const std = @import("std");

var counter_mutex: std.Thread.Mutex = .{};
var counter: usize = 0;

pub fn increment() void {
    counter_mutex.lock();
    defer counter_mutex.unlock();
    counter += 1;
}
```

Or use atomic operations:

```zig
var counter = std.atomic.Value(usize).init(0);

pub fn increment() void {
    _ = counter.fetchAdd(1, .monotonic);
}
```

Prefer instance pattern for better thread safety.

### Configuration Files

For runtime configuration updates:

```zig
const Config = struct {
    debug_mode: bool,
    log_level: i32,

    pub fn loadFromFile(allocator: std.mem.Allocator, path: []const u8) !Config {
        const file = try std.fs.cwd().openFile(path, .{});
        defer file.close();

        // Parse configuration file
        // Return Config instance
    }
};

test "reload config from file" {
    const allocator = std.testing.allocator;

    var config = try Config.loadFromFile(allocator, "config.json");

    // Modify config.json externally

    // "Reload" by reading file again
    config = try Config.loadFromFile(allocator, "config.json");
}
```

External files provide runtime configurability.

### Comptime vs Var

Understand the difference:

```zig
// Compile-time: Baked into binary
pub const VERSION = "1.0.0";
comptime var build_number = 0;  // Computed at compile time

// Runtime: Can change during execution
var connection_count: usize = 0;
var is_ready: bool = false;
```

Use `const` for unchanging values, `var` for mutable state.

### Hot Reload Patterns

For development, consider:

**Separate Data from Code:**
```zig
// config.json - can be edited while running
{
    "timeout": 30,
    "retries": 3
}

// Code reads config periodically
const config = try readConfig("config.json");
```

**Plugin Architecture:**
```zig
// Load plugins as shared libraries
const plugin = try std.DynLib.open("feature.so");
const init_fn = plugin.lookup(*const fn() void, "init") orelse return error.Missing;
init_fn();

// Can reload by closing and reopening
plugin.close();
const new_plugin = try std.DynLib.open("feature.so");
```

**Asset Reloading:**
```zig
// Watch for file changes
while (true) {
    const mtime = try getModificationTime("assets/textures.png");
    if (mtime != last_mtime) {
        texture = try loadTexture("assets/textures.png");
        last_mtime = mtime;
    }
    std.time.sleep(1 * std.time.ns_per_s);
}
```

These patterns enable development workflows without full restarts.

### Memory Management

Module state should be cleaned up:

```zig
// Bad: Leaks memory
var list: std.ArrayList(u8) = undefined;

pub fn init(allocator: std.mem.Allocator) void {
    list = std.ArrayList(u8).init(allocator);
}

// Good: Provides cleanup
pub fn deinit() void {
    list.deinit();
}
```

Always provide deinit for allocated resources.

### Testing Isolation

Ensure tests don't interfere:

```zig
test "isolated test 1" {
    counter.reset();
    defer counter.reset();

    counter.increment();
    try testing.expectEqual(@as(usize, 1), counter.getValue());
}

test "isolated test 2" {
    counter.reset();
    defer counter.reset();

    // Starts fresh even if previous test forgot to reset
    try testing.expectEqual(@as(usize, 0), counter.getValue());
}
```

Reset at start and cleanup with defer.

### Summary

Key takeaways for module "reloading" in Zig:

1. **Imports are cached** - Each module is a compile-time singleton
2. **No runtime reload** - Code changes require recompilation
3. **Global state shared** - All imports see the same state
4. **Use reset functions** - Enable clean test isolation
5. **Prefer instances** - Better than global state for flexibility
6. **Use defer** - Ensures cleanup even on errors
7. **Separate concerns** - Compile-time constants vs runtime state
8. **Provide deinit** - Clean up allocated resources
9. **Consider concurrency** - Global state isn't thread-safe
10. **Use configuration files** - For runtime-changeable settings

### Full Tested Code

```zig
// Recipe 10.6: Reloading Modules
// Target Zig Version: 0.15.2
//
// This recipe demonstrates module import caching, state management,
// and patterns for dynamic code updates in Zig.
//
// NOTE: Unlike Python's importlib.reload(), Zig modules are compiled statically.
// This recipe shows Zig-appropriate patterns for similar concepts:
// - Import caching behavior
// - State reset patterns
// - Build system integration for code updates
// - Dynamic library loading (runtime updates)
//
// Package structure:
// recipe_10_6.zig (root test file)
// └── recipe_10_6/
//     ├── counter.zig (stateful module)
//     └── config.zig (configuration module)

const std = @import("std");
const testing = std.testing;
const builtin = @import("builtin");

// ANCHOR: import_caching
// Zig caches @import() results at compile time
const counter1 = @import("recipe_10_6/counter.zig");
const counter2 = @import("recipe_10_6/counter.zig");
// counter1 and counter2 refer to the SAME module instance
// ANCHOR_END: import_caching

const config = @import("recipe_10_6/config.zig");

// ANCHOR: imports_are_cached
test "imports are cached at compile time" {
    // Multiple imports of the same module return the same instance
    const c1 = @import("recipe_10_6/counter.zig");
    const c2 = @import("recipe_10_6/counter.zig");

    // They share the same state
    c1.reset();
    c1.increment();
    c1.increment();

    // c2 sees the same state because it's the same module
    try testing.expectEqual(@as(usize, 2), c2.getValue());
}
// ANCHOR_END: imports_are_cached

// ANCHOR: shared_module_state
test "module state is shared across imports" {
    counter1.reset();

    counter1.increment();
    try testing.expectEqual(@as(usize, 1), counter1.getValue());

    // counter2 is the same module, so sees the same state
    try testing.expectEqual(@as(usize, 1), counter2.getValue());

    counter2.increment();
    try testing.expectEqual(@as(usize, 2), counter1.getValue());
}
// ANCHOR_END: shared_module_state

// ANCHOR: reset_pattern
test "resetting module state" {
    // Modules with state should provide reset functions
    counter1.reset();
    try testing.expectEqual(@as(usize, 0), counter1.getValue());

    counter1.increment();
    counter1.increment();
    counter1.increment();
    try testing.expectEqual(@as(usize, 3), counter1.getValue());

    // Reset to initial state
    counter1.reset();
    try testing.expectEqual(@as(usize, 0), counter1.getValue());
}
// ANCHOR_END: reset_pattern

// ANCHOR: initialization_pattern
test "module initialization pattern" {
    // For modules that need setup/teardown, use explicit init/deinit
    defer config.reset(); // Clean up for next test
    config.reset(); // Reset to defaults

    config.setValue("debug_mode", true);
    try testing.expect(config.getValue("debug_mode"));

    config.setIntValue("log_level", 3);
    try testing.expectEqual(@as(i32, 3), config.getIntValue("log_level"));

    // Config will be reset by defer
    try testing.expect(config.getValue("debug_mode"));
}
// ANCHOR_END: initialization_pattern

// ANCHOR: compile_time_constants
test "compile-time constants are truly constant" {
    const version = @import("recipe_10_6/config.zig").VERSION;
    const name = @import("recipe_10_6/config.zig").APP_NAME;

    // These are compile-time constants and cannot be "reloaded"
    try testing.expectEqualStrings("1.0.0", version);
    try testing.expectEqualStrings("MyApp", name);

    // To change these, you must recompile
}
// ANCHOR_END: compile_time_constants

// ANCHOR: module_singleton_pattern
test "module singleton pattern" {
    // Each module is effectively a singleton at compile time
    const mod1 = @import("recipe_10_6/counter.zig");
    const mod2 = @import("recipe_10_6/counter.zig");

    mod1.reset();
    mod1.increment();

    // Same instance
    try testing.expectEqual(mod1.getValue(), mod2.getValue());

    // You cannot have multiple independent instances
    // (unless the module provides its own instance management)
}
// ANCHOR_END: module_singleton_pattern

// ANCHOR: instance_pattern
// To get "reloadable" behavior, use instance structs instead of module globals
const CounterInstance = struct {
    value: usize,

    pub fn init() CounterInstance {
        return .{ .value = 0 };
    }

    pub fn increment(self: *CounterInstance) void {
        self.value += 1;
    }

    pub fn getValue(self: *const CounterInstance) usize {
        return self.value;
    }

    pub fn reset(self: *CounterInstance) void {
        self.value = 0;
    }
};

test "instance pattern for independent state" {
    // Create independent instances instead of using module globals
    var counter_a = CounterInstance.init();
    var counter_b = CounterInstance.init();

    counter_a.increment();
    counter_a.increment();
    try testing.expectEqual(@as(usize, 2), counter_a.getValue());

    counter_b.increment();
    try testing.expectEqual(@as(usize, 1), counter_b.getValue());

    // Independent state
    try testing.expectEqual(@as(usize, 2), counter_a.getValue());
}
// ANCHOR_END: instance_pattern

// ANCHOR: avoiding_global_state
test "avoiding global state for testability" {
    // Global module state makes testing difficult
    // Because imports are cached, tests can interfere with each other

    counter1.reset(); // Must reset before each test

    counter1.increment();
    try testing.expectEqual(@as(usize, 1), counter1.getValue());

    // If we forget to reset, the next test might fail
}
// ANCHOR_END: avoiding_global_state

// ANCHOR: scoped_reset
test "scoped state management" {
    // Better pattern: Use defer for cleanup
    counter1.reset(); // Reset at start for clean state
    defer counter1.reset(); // Always reset after test

    counter1.increment();
    counter1.increment();
    counter1.increment();

    try testing.expectEqual(@as(usize, 3), counter1.getValue());

    // reset() will be called on test exit
}
// ANCHOR_END: scoped_reset

// ANCHOR: configuration_reload
test "configuration changes" {
    defer config.reset();

    // Simulate "reloading" configuration by resetting and setting new values
    config.reset();
    config.setValue("feature_x", true);
    config.setIntValue("timeout", 30);

    try testing.expect(config.getValue("feature_x"));
    try testing.expectEqual(@as(i32, 30), config.getIntValue("timeout"));

    // "Reload" with different values
    config.reset();
    config.setValue("feature_x", false);
    config.setIntValue("timeout", 60);

    try testing.expect(!config.getValue("feature_x"));
    try testing.expectEqual(@as(i32, 60), config.getIntValue("timeout"));
}
// ANCHOR_END: configuration_reload

// ANCHOR: build_system_pattern
test "understanding compile-time vs runtime" {
    // At compile time:
    // - @import() resolves modules
    // - Module structure is fixed
    // - Const values are embedded
    //
    // At runtime:
    // - Module state can change
    // - Functions can be called
    // - Variables can be modified
    //
    // To "reload" code, you must recompile

    const module_version = config.VERSION;
    try testing.expectEqualStrings("1.0.0", module_version);

    // Runtime state can change
    config.setIntValue("runtime_value", 42);
    try testing.expectEqual(@as(i32, 42), config.getIntValue("runtime_value"));
}
// ANCHOR_END: build_system_pattern

// ANCHOR: best_practices
test "best practices for module state" {
    // 1. Prefer stateless modules when possible
    // 2. If state is needed, provide reset() function
    // 3. Use explicit init/deinit for resources
    // 4. Consider instance pattern instead of globals
    // 5. Use defer for cleanup in tests

    defer counter1.reset();

    counter1.increment();
    try testing.expect(counter1.getValue() > 0);
}
// ANCHOR_END: best_practices

// Comprehensive test
test "comprehensive module caching and state management" {
    // Reset all module state
    counter1.reset();
    config.reset();

    // Demonstrate import caching
    const c1 = @import("recipe_10_6/counter.zig");
    const c2 = @import("recipe_10_6/counter.zig");

    c1.increment();
    c1.increment();

    // Same module instance
    try testing.expectEqual(@as(usize, 2), c2.getValue());

    // Configuration changes
    config.setValue("test_mode", true);
    config.setIntValue("value", 123);

    try testing.expect(config.getValue("test_mode"));
    try testing.expectEqual(@as(i32, 123), config.getIntValue("value"));

    // Instance pattern for independence
    var instance1 = CounterInstance.init();
    var instance2 = CounterInstance.init();

    instance1.increment();
    instance1.increment();
    instance1.increment();

    try testing.expectEqual(@as(usize, 3), instance1.getValue());
    try testing.expectEqual(@as(usize, 0), instance2.getValue());

    // Cleanup
    counter1.reset();
    config.reset();
}

// ANCHOR: cleanup_resources
test "cleanup module resources" {
    // For modules that allocate resources, call deinit when done
    // This test should run last to clean up the config module
    defer config.deinit();

    config.setValue("final_test", true);
    try testing.expect(config.getValue("final_test"));

    // deinit() will be called, freeing HashMaps
}
// ANCHOR_END: cleanup_resources
```

### See Also

- Recipe 10.1: Making a hierarchical package of modules
- Recipe 10.4: Splitting a module into multiple files
- Recipe 10.5: Making separate directories of code import under a common namespace

---

## Recipe 10.7: Making a Directory or Archive File Runnable As a Main Script {#recipe-10-7}

**Tags:** allocators, build-system, comptime, error-handling, json, memory, parsing, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_7.zig`

### Problem

You're familiar with Python's approach where you can run a package directly (`python -m mypackage` or `python mypackage.zip`). You want to create a runnable Zig package with a clear entry point. You need to understand how Zig's compiled approach differs from Python's interpreted model for creating executable packages.

### Solution

Use Zig's build system to define executable entry points. Unlike Python's runtime discovery of `__main__.py`, Zig requires explicit configuration in `build.zig` and a public `main` function in your entry point file. The build system produces standalone executables, not zip files with source code.

### Understanding Entry Points

Zig's approach differs from Python:

```zig
// In Python: python -m mypackage
// or: python mypackage.zip
//
// In Zig: zig build run
// or: ./zig-out/bin/myapp
//
// Entry point is defined in build.zig, not by file location
```

Python discovers entry points at runtime; Zig specifies them at build time.

### The Main Function

A runnable Zig program requires a public main function:

```zig
// A runnable Zig program requires a public main function
pub fn main() !void {
    const stdout = std.io.getStdOut().writer();
    try stdout.print("Recipe 10.7: Executable Package Example\n", .{});
}
```

The `!void` return type means the function returns nothing or an error.

### Discussion

### Application Structure

Typical application organization:

```zig
// Typical application structure:
// src/
// ├── main.zig (this file - entry point)
// ├── app/ (application logic)
// │   ├── app.zig
// │   ├── commands.zig
// │   └── config.zig
// └── lib/ (reusable library code)
//     ├── utils.zig
//     └── types.zig
//
// build.zig at project root defines how to build
```

The `build.zig` file specifies which file contains your entry point.

### Error Sets

Define explicit error sets for better type safety:

```zig
const CommandError = error{
    InvalidArguments,
    ExecutionFailed,
    ResourceNotFound,
};
```

Avoid using `anyerror` - be specific about what can fail.

### Command Pattern

Structure commands with clear interfaces:

```zig
const Command = struct {
    name: []const u8,
    description: []const u8,
    run: *const fn () CommandError!void,
};

fn runHelp() !void {
    // Command implementation omitted for testing - not called at compile time
    _ = "help";
}

fn runVersion() !void {
    // Command implementation omitted for testing - not called at compile time
    _ = "version";
}

const commands = [_]Command{
    .{ .name = "help", .description = "Show help", .run = runHelp },
    .{ .name = "version", .description = "Show version", .run = runVersion },
};
```

This pattern allows for extensible command-line applications.

### Testing Entry Points

Test the application structure without calling main:

```zig
test "application has main entry point" {
    // The presence of pub fn main() makes this file executable
    // Tests verify application logic, not main() itself

    // Verify command structure
    try testing.expectEqual(@as(usize, 2), commands.len);
    try testing.expectEqualStrings("help", commands[0].name);
    try testing.expectEqualStrings("version", commands[1].name);
}
```

You can't easily test `main()` directly, but you can test the components it uses.

### Package Metadata

Include version and package information:

```zig
pub const PackageInfo = struct {
    name: []const u8,
    version: []const u8,
    description: []const u8,
    author: []const u8,
};

pub const package_info = PackageInfo{
    .name = "recipe_10_7",
    .version = "1.0.0",
    .description = "Executable package example",
    .author = "Zig BBQ Cookbook",
};
```

Test metadata accessibility:

```zig
test "package metadata" {
    try testing.expectEqualStrings("recipe_10_7", package_info.name);
    try testing.expectEqualStrings("1.0.0", package_info.version);
}
```

### Build Configuration

Configure your executable in `build.zig`:

```zig
// Build configuration (would be in build.zig):
//
// const exe = b.addExecutable(.{
//     .name = "recipe_10_7",
//     .root_source_file = b.path("src/recipe_10_7.zig"),
//     .target = target,
//     .optimize = optimize,
// });
//
// b.installArtifact(exe);
//
// const run_cmd = b.addRunArtifact(exe);
// const run_step = b.step("run", "Run the app");
// run_step.dependOn(&run_cmd.step);
```

This tells the build system how to create your executable.

### Argument Parsing

Parse command-line arguments:

```zig
const ParseError = error{
    UnknownCommand,
};

fn parseArgs(args: []const []const u8) ParseError!?[]const u8 {
    if (args.len < 2) {
        return null; // No command specified
    }

    // Find command
    const cmd_name = args[1];
    for (commands) |cmd| {
        if (std.mem.eql(u8, cmd.name, cmd_name)) {
            return cmd.name;
        }
    }

    // Command not found
    return ParseError.UnknownCommand;
}
```

Test argument parsing:

```zig
test "argument parsing" {
    // No arguments
    const args1 = [_][]const u8{"program"};
    const result1 = try parseArgs(&args1);
    try testing.expect(result1 == null);

    // Valid command
    const args2 = [_][]const u8{ "program", "help" };
    const result2 = try parseArgs(&args2);
    try testing.expect(result2 != null);
    try testing.expectEqualStrings("help", result2.?);

    // Another valid command
    const args3 = [_][]const u8{ "program", "version" };
    const result3 = try parseArgs(&args3);
    try testing.expectEqualStrings("version", result3.?);

    // Invalid command
    const args4 = [_][]const u8{ "program", "invalid" };
    const result4 = parseArgs(&args4);
    try testing.expectError(ParseError.UnknownCommand, result4);
}
```

Always test both success and error cases.

### Subcommand Pattern

Structure applications with subcommands:

```zig
const SubCommandError = error{
    InvalidArguments,
    InitFailed,
    BuildFailed,
    TestFailed,
};

const SubCommand = struct {
    name: []const u8,
    handler: *const fn ([]const []const u8) SubCommandError!void,
};

fn handleInit(args: []const []const u8) !void {
    _ = args;
    // Implementation omitted - not called at compile time
}

fn handleBuild(args: []const []const u8) !void {
    _ = args;
    // Implementation omitted - not called at compile time
}

fn handleTest(args: []const []const u8) !void {
    _ = args;
    // Implementation omitted - not called at compile time
}

const subcommands = [_]SubCommand{
    .{ .name = "init", .handler = handleInit },
    .{ .name = "build", .handler = handleBuild },
    .{ .name = "test", .handler = handleTest },
};
```

Subcommands allow complex CLI tools like `git`, where you have `git commit`, `git push`, etc.

Test subcommand structure:

```zig
test "subcommand structure" {
    try testing.expectEqual(@as(usize, 3), subcommands.len);

    // Verify subcommand names
    try testing.expectEqualStrings("init", subcommands[0].name);
    try testing.expectEqualStrings("build", subcommands[1].name);
    try testing.expectEqualStrings("test", subcommands[2].name);
}
```

### Application Context

Manage application state:

```zig
const AppContext = struct {
    allocator: std.mem.Allocator,
    verbose: bool,
    config_path: ?[]const u8,

    pub fn init(allocator: std.mem.Allocator) AppContext {
        return .{
            .allocator = allocator,
            .verbose = false,
            .config_path = null,
        };
    }

    pub fn setVerbose(self: *AppContext, verbose: bool) void {
        self.verbose = verbose;
    }

    pub fn setConfigPath(self: *AppContext, path: []const u8) void {
        self.config_path = path;
    }
};
```

Test context management:

```zig
test "application context" {
    var ctx = AppContext.init(testing.allocator);

    try testing.expect(!ctx.verbose);
    try testing.expect(ctx.config_path == null);

    ctx.setVerbose(true);
    try testing.expect(ctx.verbose);

    ctx.setConfigPath("config.json");
    try testing.expect(ctx.config_path != null);
    try testing.expectEqualStrings("config.json", ctx.config_path.?);
}
```

The context pattern centralizes application state.

### Exit Codes

Define standard exit codes:

```zig
pub const ExitCode = enum(u8) {
    success = 0,
    general_error = 1,
    usage_error = 2,
    config_error = 3,
    runtime_error = 4,
};

fn exitWithCode(code: ExitCode) noreturn {
    std.process.exit(@intFromEnum(code));
}
```

Test exit code values:

```zig
test "exit codes" {
    try testing.expectEqual(@as(u8, 0), @intFromEnum(ExitCode.success));
    try testing.expectEqual(@as(u8, 1), @intFromEnum(ExitCode.general_error));
    try testing.expectEqual(@as(u8, 2), @intFromEnum(ExitCode.usage_error));
}
```

Standard exit codes help shell scripts handle errors.

### Version Information

Implement custom version formatting:

```zig
pub const Version = struct {
    major: u32,
    minor: u32,
    patch: u32,

    pub fn format(
        self: Version,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("{d}.{d}.{d}", .{ self.major, self.minor, self.patch });
    }
};

pub const version = Version{ .major = 1, .minor = 0, .patch = 0 };
```

Test version handling:

```zig
test "version formatting" {
    // Test version values directly
    try testing.expectEqual(@as(u32, 1), version.major);
    try testing.expectEqual(@as(u32, 0), version.minor);
    try testing.expectEqual(@as(u32, 0), version.patch);
}
```

The `format()` function enables `std.fmt.print("{}", .{version})`.

### Resource Embedding

Embed files at compile time:

```zig
// In build.zig, you can embed files:
// const embed = b.addModule("embed", .{
//     .root_source_file = b.path("embed.zig"),
// });
//
// Then in embed.zig:
// pub const help_text = @embedFile("help.txt");
// pub const config_template = @embedFile("config.json");
```

Embedded files become part of the binary.

### Build-Time Information

Access build information:

```zig
pub const build_info = struct {
    pub const zig_version = @import("builtin").zig_version_string;
    pub const build_mode = @import("builtin").mode;
};
```

Test build information access:

```zig
test "build time information" {
    // Verify we can access build information
    _ = build_info.zig_version;
    _ = build_info.build_mode;
}
```

Use this for debugging and diagnostics.

### Complete Example

A comprehensive application structure:

```zig
test "comprehensive executable package patterns" {
    // Package metadata
    try testing.expectEqualStrings("recipe_10_7", package_info.name);

    // Command structure
    try testing.expectEqual(@as(usize, 2), commands.len);

    // Subcommands
    try testing.expectEqual(@as(usize, 3), subcommands.len);

    // Application context
    var ctx = AppContext.init(testing.allocator);
    ctx.setVerbose(true);
    try testing.expect(ctx.verbose);

    // Exit codes
    try testing.expectEqual(@as(u8, 0), @intFromEnum(ExitCode.success));

    // Version
    try testing.expectEqual(@as(u32, 1), version.major);
    try testing.expectEqual(@as(u32, 0), version.minor);
    try testing.expectEqual(@as(u32, 0), version.patch);
}
```

All components work together to create a complete application.

### Python vs Zig Comparison

**Python Approach (Interpreted):**
```python
# Directory structure:
# mypackage/
#   __init__.py
#   __main__.py  # Discovered at runtime
#   commands.py

# Run with:
python -m mypackage

# Or package as zip:
python mypackage.zip
```

**Zig Approach (Compiled):**
```zig
// Directory structure:
// src/
//   main.zig  // Specified in build.zig
//   commands.zig
// build.zig  // Defines entry point

// Build and run:
zig build run

// Or run the binary:
./zig-out/bin/myapp
```

Key difference: Zig produces standalone executables, not zip files with source.

### Build.zig Example

A complete build configuration:

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Define the executable
    const exe = b.addExecutable(.{
        .name = "myapp",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Install the executable
    b.installArtifact(exe);

    // Add run step
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());

    // Allow passing args: zig build run -- arg1 arg2
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the app");
    run_step.dependOn(&run_cmd.step);

    // Add tests
    const unit_tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    const run_unit_tests = b.addRunArtifact(unit_tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_unit_tests.step);
}
```

This creates both `zig build run` and `zig build test` commands.

### Command Execution Pattern

Implement a complete command dispatcher:

```zig
pub fn executeCommand(allocator: std.mem.Allocator, args: []const []const u8) !void {
    const cmd_name = try parseArgs(args) orelse {
        try showHelp();
        return;
    };

    for (commands) |cmd| {
        if (std.mem.eql(u8, cmd.name, cmd_name)) {
            try cmd.run();
            return;
        }
    }

    return ParseError.UnknownCommand;
}

fn showHelp() !void {
    const stdout = std.io.getStdOut().writer();
    try stdout.print("Available commands:\n", .{});
    for (commands) |cmd| {
        try stdout.print("  {s}: {s}\n", .{ cmd.name, cmd.description });
    }
}
```

This pattern dispatches to the appropriate command handler.

### Argument Handling

Process arguments in main:

```zig
pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Get command-line arguments
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    // Execute command
    executeCommand(allocator, args) catch |err| {
        const stderr = std.io.getStdErr().writer();
        try stderr.print("Error: {}\n", .{err});
        std.process.exit(@intFromEnum(ExitCode.general_error));
    };
}
```

Always clean up allocated arguments.

### Error Handling Strategy

Handle errors at the appropriate level:

```zig
pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const deinit_status = gpa.deinit();
        if (deinit_status == .leak) {
            std.debug.print("Memory leak detected!\n", .{});
        }
    }
    const allocator = gpa.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    // Try to execute, catch and report errors
    executeCommand(allocator, args) catch |err| switch (err) {
        ParseError.UnknownCommand => {
            const stderr = std.io.getStdErr().writer();
            try stderr.print("Unknown command. Use 'help' for available commands.\n", .{});
            std.process.exit(@intFromEnum(ExitCode.usage_error));
        },
        else => {
            const stderr = std.io.getStdErr().writer();
            try stderr.print("Error: {}\n", .{err});
            std.process.exit(@intFromEnum(ExitCode.general_error));
        },
    };
}
```

Different error types should result in different exit codes.

### Configuration Files

Load configuration at startup:

```zig
const Config = struct {
    verbose: bool,
    log_level: i32,
    output_path: []const u8,

    pub fn loadFromFile(allocator: std.mem.Allocator, path: []const u8) !Config {
        const file = try std.fs.cwd().openFile(path, .{});
        defer file.close();

        const contents = try file.readToEndAlloc(allocator, 1024 * 1024);
        defer allocator.free(contents);

        // Parse config file (JSON, TOML, etc.)
        // Return parsed config
    }
};
```

Load config early in main and pass to commands.

### Directory vs Executable

Unlike Python, Zig doesn't execute directories:

**Python:**
```bash
# Python can execute a directory
python mypackage/

# Or a zip file
python mypackage.zip
```

**Zig:**
```bash
# Zig produces a binary
zig build

# Execute the binary
./zig-out/bin/myapp

# Or run directly
zig build run
```

Zig's approach produces faster, standalone executables.

### Best Practices

**Use Explicit Error Sets:**
```zig
// Good: Specific errors
const ParseError = error{
    UnknownCommand,
    MissingArgument,
};

// Bad: Too general
fn parseArgs(args: []const u8) anyerror!void { ... }
```

**Centralize Application State:**
```zig
// Good: Single context
const AppContext = struct {
    allocator: std.mem.Allocator,
    config: Config,
    verbose: bool,
};

// Bad: Global variables
var verbose: bool = false;
var config: Config = undefined;
```

**Provide Help Text:**
```zig
const commands = [_]Command{
    .{ .name = "help", .description = "Show this help message", .run = showHelp },
    .{ .name = "version", .description = "Show version information", .run = showVersion },
    .{ .name = "build", .description = "Build the project", .run = runBuild },
};
```

**Handle Signals Gracefully:**
```zig
// Catch Ctrl+C for cleanup
const signal_action = std.os.Sigaction{
    .handler = .{ .handler = handleSignal },
    .mask = std.os.empty_sigset,
    .flags = 0,
};
try std.os.sigaction(std.os.SIG.INT, &signal_action, null);
```

### Testing CLI Applications

Test components individually:

```zig
test "command parsing" {
    // Test argument parsing
    const result = try parseArgs(&.{ "myapp", "build", "--release" });
    try testing.expectEqualStrings("build", result.?);
}

test "config loading" {
    // Test configuration
    const config = try Config.loadDefaults(testing.allocator);
    try testing.expect(!config.verbose);
}

test "error handling" {
    // Test error cases
    const result = parseArgs(&.{ "myapp", "invalid" });
    try testing.expectError(ParseError.UnknownCommand, result);
}
```

Integration tests can spawn the actual binary and test output.

### Summary

Key differences between Python and Zig executable packages:

**Python:**
- Runtime discovery of entry points
- Can execute directories and zip files
- Slower startup (interpreter overhead)
- Requires Python installed

**Zig:**
- Build-time specification in build.zig
- Produces standalone binaries
- Fast startup (native code)
- No runtime dependencies

Both approaches work, but Zig's compiled model offers better performance and simpler deployment.

### Full Tested Code

```zig
// Recipe 10.7: Making a Directory or Zip File Runnable as a Main Script
// Target Zig Version: 0.15.2
//
// This recipe demonstrates Zig's approach to creating executable packages.
// Unlike Python's __main__.py pattern, Zig uses build.zig to define entry points.
//
// Key concepts:
// - Using build.zig to create executables
// - Package entry points with main functions
// - Organizing application packages
// - Build system configuration
//
// Package structure:
// recipe_10_7/
// ├── build.zig (would define the executable)
// ├── main.zig (entry point with pub fn main)
// ├── app/ (application modules)
// │   ├── app.zig
// │   └── commands.zig
// └── lib/ (library modules)
//     └── lib.zig

const std = @import("std");
const testing = std.testing;

// ANCHOR: entry_point_concept
// In Python: python -m mypackage
// or: python mypackage.zip
//
// In Zig: zig build run
// or: ./zig-out/bin/myapp
//
// Entry point is defined in build.zig, not by file location
// ANCHOR_END: entry_point_concept

// ANCHOR: main_function
// A runnable Zig program requires a public main function
pub fn main() !void {
    const stdout = std.io.getStdOut().writer();
    try stdout.print("Recipe 10.7: Executable Package Example\n", .{});
}
// ANCHOR_END: main_function

// ANCHOR: application_structure
// Typical application structure:
// src/
// ├── main.zig (this file - entry point)
// ├── app/ (application logic)
// │   ├── app.zig
// │   ├── commands.zig
// │   └── config.zig
// └── lib/ (reusable library code)
//     ├── utils.zig
//     └── types.zig
//
// build.zig at project root defines how to build
// ANCHOR_END: application_structure

// ANCHOR: error_sets
const CommandError = error{
    InvalidArguments,
    ExecutionFailed,
    ResourceNotFound,
};
// ANCHOR_END: error_sets

// ANCHOR: command_pattern
const Command = struct {
    name: []const u8,
    description: []const u8,
    run: *const fn () CommandError!void,
};

fn runHelp() !void {
    // Command implementation omitted for testing - not called at compile time
    _ = "help";
}

fn runVersion() !void {
    // Command implementation omitted for testing - not called at compile time
    _ = "version";
}

const commands = [_]Command{
    .{ .name = "help", .description = "Show help", .run = runHelp },
    .{ .name = "version", .description = "Show version", .run = runVersion },
};
// ANCHOR_END: command_pattern

// ANCHOR: test_entry_point
test "application has main entry point" {
    // The presence of pub fn main() makes this file executable
    // Tests verify application logic, not main() itself

    // Verify command structure
    try testing.expectEqual(@as(usize, 2), commands.len);
    try testing.expectEqualStrings("help", commands[0].name);
    try testing.expectEqualStrings("version", commands[1].name);
}
// ANCHOR_END: test_entry_point

// ANCHOR: package_metadata
pub const PackageInfo = struct {
    name: []const u8,
    version: []const u8,
    description: []const u8,
    author: []const u8,
};

pub const package_info = PackageInfo{
    .name = "recipe_10_7",
    .version = "1.0.0",
    .description = "Executable package example",
    .author = "Zig BBQ Cookbook",
};
// ANCHOR_END: package_metadata

// ANCHOR: test_package_metadata
test "package metadata" {
    try testing.expectEqualStrings("recipe_10_7", package_info.name);
    try testing.expectEqualStrings("1.0.0", package_info.version);
}
// ANCHOR_END: test_package_metadata

// ANCHOR: build_configuration
// Build configuration (would be in build.zig):
//
// const exe = b.addExecutable(.{
//     .name = "recipe_10_7",
//     .root_source_file = b.path("src/recipe_10_7.zig"),
//     .target = target,
//     .optimize = optimize,
// });
//
// b.installArtifact(exe);
//
// const run_cmd = b.addRunArtifact(exe);
// const run_step = b.step("run", "Run the app");
// run_step.dependOn(&run_cmd.step);
// ANCHOR_END: build_configuration

// ANCHOR: argument_parsing
const ParseError = error{
    UnknownCommand,
};

fn parseArgs(args: []const []const u8) ParseError!?[]const u8 {
    if (args.len < 2) {
        return null; // No command specified
    }

    // Find command
    const cmd_name = args[1];
    for (commands) |cmd| {
        if (std.mem.eql(u8, cmd.name, cmd_name)) {
            return cmd.name;
        }
    }

    // Command not found
    return ParseError.UnknownCommand;
}
// ANCHOR_END: argument_parsing

// ANCHOR: test_argument_parsing
test "argument parsing" {
    // No arguments
    const args1 = [_][]const u8{"program"};
    const result1 = try parseArgs(&args1);
    try testing.expect(result1 == null);

    // Valid command
    const args2 = [_][]const u8{ "program", "help" };
    const result2 = try parseArgs(&args2);
    try testing.expect(result2 != null);
    try testing.expectEqualStrings("help", result2.?);

    // Another valid command
    const args3 = [_][]const u8{ "program", "version" };
    const result3 = try parseArgs(&args3);
    try testing.expectEqualStrings("version", result3.?);

    // Invalid command
    const args4 = [_][]const u8{ "program", "invalid" };
    const result4 = parseArgs(&args4);
    try testing.expectError(ParseError.UnknownCommand, result4);
}
// ANCHOR_END: test_argument_parsing

// ANCHOR: subcommand_pattern
const SubCommandError = error{
    InvalidArguments,
    InitFailed,
    BuildFailed,
    TestFailed,
};

const SubCommand = struct {
    name: []const u8,
    handler: *const fn ([]const []const u8) SubCommandError!void,
};

fn handleInit(args: []const []const u8) !void {
    _ = args;
    // Implementation omitted - not called at compile time
}

fn handleBuild(args: []const []const u8) !void {
    _ = args;
    // Implementation omitted - not called at compile time
}

fn handleTest(args: []const []const u8) !void {
    _ = args;
    // Implementation omitted - not called at compile time
}

const subcommands = [_]SubCommand{
    .{ .name = "init", .handler = handleInit },
    .{ .name = "build", .handler = handleBuild },
    .{ .name = "test", .handler = handleTest },
};
// ANCHOR_END: subcommand_pattern

// ANCHOR: test_subcommands
test "subcommand structure" {
    try testing.expectEqual(@as(usize, 3), subcommands.len);

    // Verify subcommand names
    try testing.expectEqualStrings("init", subcommands[0].name);
    try testing.expectEqualStrings("build", subcommands[1].name);
    try testing.expectEqualStrings("test", subcommands[2].name);
}
// ANCHOR_END: test_subcommands

// ANCHOR: application_context
const AppContext = struct {
    allocator: std.mem.Allocator,
    verbose: bool,
    config_path: ?[]const u8,

    pub fn init(allocator: std.mem.Allocator) AppContext {
        return .{
            .allocator = allocator,
            .verbose = false,
            .config_path = null,
        };
    }

    pub fn setVerbose(self: *AppContext, verbose: bool) void {
        self.verbose = verbose;
    }

    pub fn setConfigPath(self: *AppContext, path: []const u8) void {
        self.config_path = path;
    }
};
// ANCHOR_END: application_context

// ANCHOR: test_app_context
test "application context" {
    var ctx = AppContext.init(testing.allocator);

    try testing.expect(!ctx.verbose);
    try testing.expect(ctx.config_path == null);

    ctx.setVerbose(true);
    try testing.expect(ctx.verbose);

    ctx.setConfigPath("config.json");
    try testing.expect(ctx.config_path != null);
    try testing.expectEqualStrings("config.json", ctx.config_path.?);
}
// ANCHOR_END: test_app_context

// ANCHOR: exit_codes
pub const ExitCode = enum(u8) {
    success = 0,
    general_error = 1,
    usage_error = 2,
    config_error = 3,
    runtime_error = 4,
};

fn exitWithCode(code: ExitCode) noreturn {
    std.process.exit(@intFromEnum(code));
}
// ANCHOR_END: exit_codes

// ANCHOR: test_exit_codes
test "exit codes" {
    try testing.expectEqual(@as(u8, 0), @intFromEnum(ExitCode.success));
    try testing.expectEqual(@as(u8, 1), @intFromEnum(ExitCode.general_error));
    try testing.expectEqual(@as(u8, 2), @intFromEnum(ExitCode.usage_error));
}
// ANCHOR_END: test_exit_codes

// ANCHOR: version_info
pub const Version = struct {
    major: u32,
    minor: u32,
    patch: u32,

    pub fn format(
        self: Version,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("{d}.{d}.{d}", .{ self.major, self.minor, self.patch });
    }
};

pub const version = Version{ .major = 1, .minor = 0, .patch = 0 };
// ANCHOR_END: version_info

// ANCHOR: test_version_info
test "version formatting" {
    // Test version values directly
    try testing.expectEqual(@as(u32, 1), version.major);
    try testing.expectEqual(@as(u32, 0), version.minor);
    try testing.expectEqual(@as(u32, 0), version.patch);
}
// ANCHOR_END: test_version_info

// ANCHOR: resource_embedding
// In build.zig, you can embed files:
// const embed = b.addModule("embed", .{
//     .root_source_file = b.path("embed.zig"),
// });
//
// Then in embed.zig:
// pub const help_text = @embedFile("help.txt");
// pub const config_template = @embedFile("config.json");
// ANCHOR_END: resource_embedding

// ANCHOR: build_time_info
pub const build_info = struct {
    pub const zig_version = @import("builtin").zig_version_string;
    pub const build_mode = @import("builtin").mode;
};
// ANCHOR_END: build_time_info

// ANCHOR: test_build_info
test "build time information" {
    // Verify we can access build information
    _ = build_info.zig_version;
    _ = build_info.build_mode;
}
// ANCHOR_END: test_build_info

// Comprehensive test
test "comprehensive executable package patterns" {
    // Package metadata
    try testing.expectEqualStrings("recipe_10_7", package_info.name);

    // Command structure
    try testing.expectEqual(@as(usize, 2), commands.len);

    // Subcommands
    try testing.expectEqual(@as(usize, 3), subcommands.len);

    // Application context
    var ctx = AppContext.init(testing.allocator);
    ctx.setVerbose(true);
    try testing.expect(ctx.verbose);

    // Exit codes
    try testing.expectEqual(@as(u8, 0), @intFromEnum(ExitCode.success));

    // Version
    try testing.expectEqual(@as(u32, 1), version.major);
    try testing.expectEqual(@as(u32, 0), version.minor);
    try testing.expectEqual(@as(u32, 0), version.patch);
}
```

### See Also

- Recipe 10.1: Making a hierarchical package of modules
- Recipe 10.4: Splitting a module into multiple files
- Recipe 10.6: Reloading modules

---

## Recipe 10.8: Reading Datafiles Within a Package {#recipe-10-8}

**Tags:** allocators, arraylist, build-system, comptime, data-structures, error-handling, hashmap, json, memory, parsing, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_8.zig`

### Problem

You need to include data files (configuration, templates, messages, binary data) with your application and access them reliably at compile-time or runtime.

### Solution

Zig provides `@embedFile` for compile-time embedding of data files directly into your binary, and standard file I/O for runtime access. Each approach has different trade-offs.

### Basic File Embedding

The simplest approach uses `@embedFile` to include file contents at compile time:

```zig
// Embed a file at compile time - contents become part of the binary
pub const config_data = @embedFile("data/sample_config.txt");
pub const template_data = @embedFile("data/sample_template.txt");

test "embed file basic usage" {
    // Embedded file is a null-terminated string constant
    try testing.expect(config_data.len > 0);
    try testing.expect(template_data.len > 0);
}
```

Files are embedded relative to the source file containing the `@embedFile` call.

### Parsing Embedded Configuration

You can parse embedded data at runtime:

```zig
const Config = struct {
    name: []const u8,
    version: []const u8,
    enabled: bool,

    pub fn parseFromEmbedded(allocator: std.mem.Allocator, data: []const u8) !Config {
        var lines = std.mem.tokenizeScalar(u8, data, '\n');

        var name: ?[]const u8 = null;
        var version: ?[]const u8 = null;
        var enabled: ?bool = null;

        while (lines.next()) |line| {
            if (std.mem.startsWith(u8, line, "name=")) {
                const value = line[5..];
                name = try allocator.dupe(u8, value);
            } else if (std.mem.startsWith(u8, line, "version=")) {
                const value = line[8..];
                version = try allocator.dupe(u8, value);
            } else if (std.mem.startsWith(u8, line, "enabled=")) {
                const value = line[8..];
                enabled = std.mem.eql(u8, value, "true");
            }
        }

        return Config{
            .name = name orelse return error.MissingName,
            .version = version orelse return error.MissingVersion,
            .enabled = enabled orelse return error.MissingEnabled,
        };
    }

    pub fn deinit(self: Config, allocator: std.mem.Allocator) void {
        allocator.free(self.name);
        allocator.free(self.version);
    }
};
```

### Discussion

### Embedded vs Runtime File Access

**Compile-Time Embedding (`@embedFile`):**
- Files become part of the binary
- No runtime file I/O needed
- Guaranteed availability (can't be missing)
- Increases binary size
- Changes require recompilation
- Perfect for templates, default configs, small assets

**Runtime File Access:**
- Files stay separate from binary
- Smaller binary size
- Can be updated without recompilation
- Requires file system access
- Files might be missing (need error handling)
- Better for large data, user configs

### Python Comparison

Zig's approach differs significantly from Python's resource handling:

**Python:**
```python
# Using importlib.resources (Python 3.9+)
from importlib.resources import files
import my_package

config = files(my_package).joinpath("data/config.txt").read_text()
```

**Zig:**
```zig
// Compile-time embedding
const config = @embedFile("data/config.txt");

// Or runtime loading
const file = try std.fs.cwd().openFile("data/config.txt", .{});
defer file.close();
const config = try file.readToEndAlloc(allocator, max_size);
defer allocator.free(config);
```

Python's approach is runtime-based and relies on the package structure. Zig offers both compile-time (zero runtime cost) and runtime options.

### Template Substitution Pattern

A common pattern is using embedded templates with variable substitution:

```zig
const Template = struct {
    content: []const u8,

    pub fn init(embedded_data: []const u8) Template {
        return .{ .content = embedded_data };
    }

    pub fn render(
        self: Template,
        allocator: std.mem.Allocator,
        vars: std.StringHashMap([]const u8),
    ) ![]u8 {
        var result = std.ArrayList(u8){};
        errdefer result.deinit(allocator);

        var i: usize = 0;
        while (i < self.content.len) {
            if (i + 1 < self.content.len and
                self.content[i] == '{' and
                self.content[i + 1] == '{') {

                const end = std.mem.indexOfPos(u8, self.content, i + 2, "}}") orelse {
                    return error.UnclosedTemplate;
                };

                const var_name = self.content[i + 2 .. end];
                const value = vars.get(var_name) orelse return error.MissingVariable;
                try result.appendSlice(allocator, value);

                i = end + 2;
            } else {
                try result.append(allocator, self.content[i]);
                i += 1;
            }
        }

        return result.toOwnedSlice(allocator);
    }
};
```

Use it like this:

```zig
const template_content = "Hello {{name}}, version {{version}}!";
const tmpl = Template.init(template_content);

var vars = std.StringHashMap([]const u8).init(allocator);
defer vars.deinit();

try vars.put("name", "World");
try vars.put("version", "1.0");

const rendered = try tmpl.render(allocator, vars);
defer allocator.free(rendered);
// Result: "Hello World, version 1.0!"
```

### Resource Loader Pattern

For flexibility, create a resource loader that supports both approaches:

```zig
const ResourceLoader = struct {
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) ResourceLoader {
        return .{ .allocator = allocator };
    }

    pub fn loadEmbedded(comptime name: []const u8) []const u8 {
        return @embedFile(name);
    }

    pub fn loadRuntime(self: ResourceLoader, path: []const u8) ![]u8 {
        const file = try std.fs.cwd().openFile(path, .{});
        defer file.close();

        const stat = try file.stat();
        const contents = try file.readToEndAlloc(self.allocator, stat.size);
        return contents;
    }
};
```

### Organizing Multiple Resources

Group related resources using a struct:

```zig
const Resources = struct {
    pub const config = @embedFile("data/sample_config.txt");
    pub const template = @embedFile("data/sample_template.txt");
    pub const messages = @embedFile("data/sample_messages.txt");
};
```

Or use an enum for type-safe access:

```zig
const ResourceType = enum {
    config,
    template,
    messages,

    pub fn getData(self: ResourceType) []const u8 {
        return switch (self) {
            .config => Resources.config,
            .template => Resources.template,
            .messages => Resources.messages,
        };
    }

    pub fn getPath(self: ResourceType) []const u8 {
        return switch (self) {
            .config => "data/sample_config.txt",
            .template => "data/sample_template.txt",
            .messages => "data/sample_messages.txt",
        };
    }
};
```

### Resource Manager with Caching

For more complex applications, implement a resource manager:

```zig
const ResourceManager = struct {
    allocator: std.mem.Allocator,
    cache: std.StringHashMap([]const u8),

    pub fn init(allocator: std.mem.Allocator) ResourceManager {
        return .{
            .allocator = allocator,
            .cache = std.StringHashMap([]const u8).init(allocator),
        };
    }

    pub fn deinit(self: *ResourceManager) void {
        var it = self.cache.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.cache.deinit();
    }

    pub fn load(self: *ResourceManager, name: []const u8, data: []const u8) !void {
        // Check if key exists and free old data
        if (self.cache.getPtr(name)) |old_value| {
            self.allocator.free(old_value.*);
            const owned_data = try self.allocator.dupe(u8, data);
            old_value.* = owned_data;
        } else {
            const owned_name = try self.allocator.dupe(u8, name);
            const owned_data = try self.allocator.dupe(u8, data);

            self.cache.put(owned_name, owned_data) catch |err| {
                self.allocator.free(owned_name);
                self.allocator.free(owned_data);
                return err;
            };
        }
    }

    pub fn get(self: *ResourceManager, name: []const u8) ?[]const u8 {
        return self.cache.get(name);
    }
};
```

This manager:
- Caches loaded resources
- Handles duplicate keys properly (frees old data)
- Provides error safety with proper cleanup
- Allows updating resources at runtime

### Binary Data Handling

For binary files, use structured access:

```zig
const BinaryResource = struct {
    data: []const u8,

    pub fn init(embedded: []const u8) BinaryResource {
        return .{ .data = embedded };
    }

    pub fn asBytes(self: BinaryResource) []const u8 {
        return self.data;
    }

    pub fn readU32(self: BinaryResource, offset: usize) !u32 {
        if (offset + 4 > self.data.len) {
            return error.OutOfBounds;
        }
        return std.mem.readInt(u32, self.data[offset..][0..4], .little);
    }

    pub fn readString(self: BinaryResource, offset: usize, len: usize) ![]const u8 {
        if (offset + len > self.data.len) {
            return error.OutOfBounds;
        }
        return self.data[offset .. offset + len];
    }
};
```

### Build-Time Information

Combine embedded resources with build metadata:

```zig
pub const build_info = struct {
    pub const version = "1.0.0";
    pub const commit = "abc123def";
    pub const build_date = "2025-01-15";

    pub const embedded_resources = true;
    pub const resource_count = 3;
};
```

This information can be populated by build.zig using the options system.

### Full Tested Code

```zig
// Recipe 10.8: Reading Datafiles Within a Package
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to access data files packaged with your code.
// Unlike Python's importlib.resources or pkg_resources, Zig provides compile-time
// embedding via @embedFile and runtime file access.
//
// Key concepts:
// - Using @embedFile for compile-time data embedding
// - Runtime file access relative to executable
// - Build system integration for data files
// - Handling different deployment scenarios
//
// Package structure:
// recipe_10_8/
// ├── build.zig
// ├── src/
// │   └── main.zig
// └── data/
//     ├── config.json
//     ├── template.txt
//     └── messages.txt

const std = @import("std");
const testing = std.testing;

// ANCHOR: embed_file_basic
// Embed a file at compile time - contents become part of the binary
pub const config_data = @embedFile("data/sample_config.txt");
pub const template_data = @embedFile("data/sample_template.txt");

test "embed file basic usage" {
    // Embedded file is a null-terminated string constant
    try testing.expect(config_data.len > 0);
    try testing.expect(template_data.len > 0);
}
// ANCHOR_END: embed_file_basic

// ANCHOR: embed_file_parsing
const Config = struct {
    name: []const u8,
    version: []const u8,
    enabled: bool,

    pub fn parseFromEmbedded(allocator: std.mem.Allocator, data: []const u8) !Config {
        // Simple parser for demonstration
        var lines = std.mem.tokenizeScalar(u8, data, '\n');

        var name: ?[]const u8 = null;
        var version: ?[]const u8 = null;
        var enabled: ?bool = null;

        while (lines.next()) |line| {
            if (std.mem.startsWith(u8, line, "name=")) {
                const value = line[5..];
                name = try allocator.dupe(u8, value);
            } else if (std.mem.startsWith(u8, line, "version=")) {
                const value = line[8..];
                version = try allocator.dupe(u8, value);
            } else if (std.mem.startsWith(u8, line, "enabled=")) {
                const value = line[8..];
                enabled = std.mem.eql(u8, value, "true");
            }
        }

        return Config{
            .name = name orelse return error.MissingName,
            .version = version orelse return error.MissingVersion,
            .enabled = enabled orelse return error.MissingEnabled,
        };
    }

    pub fn deinit(self: Config, allocator: std.mem.Allocator) void {
        allocator.free(self.name);
        allocator.free(self.version);
    }
};

test "parse embedded config" {
    const sample_config =
        \\name=MyApp
        \\version=1.0.0
        \\enabled=true
    ;

    const config = try Config.parseFromEmbedded(testing.allocator, sample_config);
    defer config.deinit(testing.allocator);

    try testing.expectEqualStrings("MyApp", config.name);
    try testing.expectEqualStrings("1.0.0", config.version);
    try testing.expect(config.enabled);
}
// ANCHOR_END: embed_file_parsing

// ANCHOR: template_substitution
const Template = struct {
    content: []const u8,

    pub fn init(embedded_data: []const u8) Template {
        return .{ .content = embedded_data };
    }

    pub fn render(
        self: Template,
        allocator: std.mem.Allocator,
        vars: std.StringHashMap([]const u8),
    ) ![]u8 {
        var result = std.ArrayList(u8){};
        errdefer result.deinit(allocator);

        var i: usize = 0;
        while (i < self.content.len) {
            if (i + 1 < self.content.len and self.content[i] == '{' and self.content[i + 1] == '{') {
                // Find closing }}
                const end = std.mem.indexOfPos(u8, self.content, i + 2, "}}") orelse {
                    return error.UnclosedTemplate;
                };

                const var_name = self.content[i + 2 .. end];
                const value = vars.get(var_name) orelse return error.MissingVariable;
                try result.appendSlice(allocator, value);

                i = end + 2;
            } else {
                try result.append(allocator, self.content[i]);
                i += 1;
            }
        }

        return result.toOwnedSlice(allocator);
    }
};

test "template substitution" {
    const template_content = "Hello {{name}}, version {{version}}!";
    const tmpl = Template.init(template_content);

    var vars = std.StringHashMap([]const u8).init(testing.allocator);
    defer vars.deinit();

    try vars.put("name", "World");
    try vars.put("version", "1.0");

    const rendered = try tmpl.render(testing.allocator, vars);
    defer testing.allocator.free(rendered);

    try testing.expectEqualStrings("Hello World, version 1.0!", rendered);
}
// ANCHOR_END: template_substitution

// ANCHOR: resource_loader
const ResourceLoader = struct {
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) ResourceLoader {
        return .{ .allocator = allocator };
    }

    pub fn loadEmbedded(comptime name: []const u8) []const u8 {
        return @embedFile(name);
    }

    pub fn loadRuntime(self: ResourceLoader, path: []const u8) ![]u8 {
        const file = try std.fs.cwd().openFile(path, .{});
        defer file.close();

        const stat = try file.stat();
        const contents = try file.readToEndAlloc(self.allocator, stat.size);
        return contents;
    }
};

test "resource loader embedded" {
    const data = ResourceLoader.loadEmbedded("data/sample_config.txt");
    try testing.expect(data.len > 0);
}
// ANCHOR_END: resource_loader

// ANCHOR: multi_resource_pattern
const Resources = struct {
    pub const config = @embedFile("data/sample_config.txt");
    pub const template = @embedFile("data/sample_template.txt");
    pub const messages = @embedFile("data/sample_messages.txt");
};

test "multi resource pattern" {
    try testing.expect(Resources.config.len > 0);
    try testing.expect(Resources.template.len > 0);
    try testing.expect(Resources.messages.len > 0);
}
// ANCHOR_END: multi_resource_pattern

// ANCHOR: resource_enum
const ResourceType = enum {
    config,
    template,
    messages,

    pub fn getData(self: ResourceType) []const u8 {
        return switch (self) {
            .config => Resources.config,
            .template => Resources.template,
            .messages => Resources.messages,
        };
    }

    pub fn getPath(self: ResourceType) []const u8 {
        return switch (self) {
            .config => "data/sample_config.txt",
            .template => "data/sample_template.txt",
            .messages => "data/sample_messages.txt",
        };
    }
};

test "resource enum" {
    const config_data_enum = ResourceType.config.getData();
    try testing.expect(config_data_enum.len > 0);
    try testing.expectEqualStrings("data/sample_config.txt", ResourceType.config.getPath());
}
// ANCHOR_END: resource_enum

// ANCHOR: lazy_resource_loading
const LazyResource = struct {
    data: ?[]const u8,
    embedded: []const u8,

    pub fn init(comptime embedded_data: []const u8) LazyResource {
        return .{
            .data = null,
            .embedded = embedded_data,
        };
    }

    pub fn get(self: *LazyResource) []const u8 {
        if (self.data) |d| {
            return d;
        }
        self.data = self.embedded;
        return self.embedded;
    }
};

test "lazy resource loading" {
    var resource = LazyResource.init("embedded content");

    try testing.expect(resource.data == null);

    const data1 = resource.get();
    try testing.expectEqualStrings("embedded content", data1);
    try testing.expect(resource.data != null);

    const data2 = resource.get();
    try testing.expectEqualStrings("embedded content", data2);
}
// ANCHOR_END: lazy_resource_loading

// ANCHOR: versioned_resources
const VersionedResources = struct {
    pub fn getConfigV1() []const u8 {
        return @embedFile("data/sample_config.txt");
    }

    pub fn getConfigV2() []const u8 {
        return @embedFile("data/sample_template.txt");
    }

    pub fn getConfigV3() []const u8 {
        return @embedFile("data/sample_messages.txt");
    }
};

test "versioned resources" {
    const v1_config = VersionedResources.getConfigV1();
    const v2_config = VersionedResources.getConfigV2();
    const v3_config = VersionedResources.getConfigV3();

    try testing.expect(v1_config.len > 0);
    try testing.expect(v2_config.len > 0);
    try testing.expect(v3_config.len > 0);
}
// ANCHOR_END: versioned_resources

// ANCHOR: resource_manager
const ResourceManager = struct {
    allocator: std.mem.Allocator,
    cache: std.StringHashMap([]const u8),

    pub fn init(allocator: std.mem.Allocator) ResourceManager {
        return .{
            .allocator = allocator,
            .cache = std.StringHashMap([]const u8).init(allocator),
        };
    }

    pub fn deinit(self: *ResourceManager) void {
        var it = self.cache.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.cache.deinit();
    }

    pub fn load(self: *ResourceManager, name: []const u8, data: []const u8) !void {
        // Check if key exists and free old data
        if (self.cache.getPtr(name)) |old_value| {
            self.allocator.free(old_value.*);
            const owned_data = try self.allocator.dupe(u8, data);
            old_value.* = owned_data;
        } else {
            const owned_name = try self.allocator.dupe(u8, name);
            const owned_data = try self.allocator.dupe(u8, data);

            self.cache.put(owned_name, owned_data) catch |err| {
                self.allocator.free(owned_name);
                self.allocator.free(owned_data);
                return err;
            };
        }
    }

    pub fn get(self: *ResourceManager, name: []const u8) ?[]const u8 {
        return self.cache.get(name);
    }
};

test "resource manager" {
    var manager = ResourceManager.init(testing.allocator);
    defer manager.deinit();

    try manager.load("config", "config_data");
    try manager.load("template", "template_data");

    const config = manager.get("config");
    try testing.expect(config != null);
    try testing.expectEqualStrings("config_data", config.?);

    const missing = manager.get("missing");
    try testing.expect(missing == null);

    // Test updating existing resource (replaces old value)
    try manager.load("config", "updated_config_data");
    const updated = manager.get("config");
    try testing.expect(updated != null);
    try testing.expectEqualStrings("updated_config_data", updated.?);
}
// ANCHOR_END: resource_manager

// ANCHOR: binary_data_handling
const BinaryResource = struct {
    data: []const u8,

    pub fn init(embedded: []const u8) BinaryResource {
        return .{ .data = embedded };
    }

    pub fn asBytes(self: BinaryResource) []const u8 {
        return self.data;
    }

    pub fn readU32(self: BinaryResource, offset: usize) !u32 {
        if (offset + 4 > self.data.len) {
            return error.OutOfBounds;
        }
        return std.mem.readInt(u32, self.data[offset..][0..4], .little);
    }

    pub fn readString(self: BinaryResource, offset: usize, len: usize) ![]const u8 {
        if (offset + len > self.data.len) {
            return error.OutOfBounds;
        }
        return self.data[offset .. offset + len];
    }
};

test "binary data handling" {
    const binary_data = "\x01\x02\x03\x04Hello";
    const resource = BinaryResource.init(binary_data);

    const value = try resource.readU32(0);
    try testing.expectEqual(@as(u32, 0x04030201), value);

    const str = try resource.readString(4, 5);
    try testing.expectEqualStrings("Hello", str);

    const out_of_bounds = resource.readU32(100);
    try testing.expectError(error.OutOfBounds, out_of_bounds);
}
// ANCHOR_END: binary_data_handling

// ANCHOR: build_info_pattern
pub const build_info = struct {
    pub const version = "1.0.0";
    pub const commit = "abc123def";
    pub const build_date = "2025-01-15";

    // These would typically come from build.zig via options
    pub const embedded_resources = true;
    pub const resource_count = 3;
};

test "build info pattern" {
    try testing.expectEqualStrings("1.0.0", build_info.version);
    try testing.expect(build_info.embedded_resources);
    try testing.expectEqual(@as(usize, 3), build_info.resource_count);
}
// ANCHOR_END: build_info_pattern

// Comprehensive test
test "comprehensive data file handling" {
    // Embedded resources
    try testing.expect(Resources.config.len > 0);

    // Resource manager
    var manager = ResourceManager.init(testing.allocator);
    defer manager.deinit();
    try manager.load("test", "data");
    try testing.expect(manager.get("test") != null);

    // Template rendering
    const tmpl = Template.init("{{key}}");
    var vars = std.StringHashMap([]const u8).init(testing.allocator);
    defer vars.deinit();
    try vars.put("key", "value");
    const rendered = try tmpl.render(testing.allocator, vars);
    defer testing.allocator.free(rendered);
    try testing.expectEqualStrings("value", rendered);
}
```

### See Also

- Recipe 10.7: Making a Directory or Zip File Runnable
- Recipe 10.9: Adding Directories to the Build Path
- Recipe 10.11: Distributing Packages

---

## Recipe 10.9: Adding Directories to the Module Search Path {#recipe-10-9}

**Tags:** allocators, arraylist, build-system, c-interop, data-structures, error-handling, hashmap, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_9.zig`

### Problem

You need to organize a large Zig project across multiple directories (like `lib/`, `vendor/`, `src/`) and configure the build system to locate and link modules from these different locations.

### Solution

Zig's build system uses `build.zig` to define modules from different directories and establish their relationships. Unlike languages with implicit path resolution, Zig requires explicit module declaration and dependency management.

### Project Structure

A typical multi-directory project looks like this:

```
project/
├── build.zig
├── src/
│   └── main.zig
├── lib/
│   ├── core/
│   │   └── core.zig
│   └── utils/
│       └── utils.zig
└── vendor/
    └── external/
        └── external.zig
```

### Basic build.zig Configuration

Here's how to configure modules from different directories:

```zig
pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Define core module from lib directory
    const core = b.addModule("core", .{
        .root_source_file = b.path("lib/core/core.zig"),
    });

    // Define utils module with dependency on core
    const utils = b.addModule("utils", .{
        .root_source_file = b.path("lib/utils/utils.zig"),
        .imports = &.{
            .{ .name = "core", .module = core },
        },
    });

    // Define external vendor module
    const external = b.addModule("external", .{
        .root_source_file = b.path("vendor/external/external.zig"),
    });

    // Create executable
    const exe = b.addExecutable(.{
        .name = "myapp",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Add module imports to executable
    exe.root_module.addImport("core", core);
    exe.root_module.addImport("utils", utils);
    exe.root_module.addImport("external", external);

    b.installArtifact(exe);
}
```

In `src/main.zig`, you can then import these modules:

```zig
const std = @import("std");
const core = @import("core");
const utils = @import("utils");
const external = @import("external");

pub fn main() !void {
    core.initialize();
    // Use modules...
}
```

### Discussion

### Python vs Zig Module Systems

The approaches differ significantly:

**Python:**
```python
# Implicit path-based imports
import lib.core.core
from lib.utils import formatString
import vendor.external

# Or modify sys.path
import sys
sys.path.append('vendor')
import external
```

**Zig:**
```zig
// Explicit module declaration in build.zig required
const core = @import("core");  // Maps to module defined in build.zig
const utils = @import("utils"); // Not a file path!

// build.zig controls all module resolution
```

Key differences:
- **Explicit vs Implicit**: Zig requires build.zig configuration; Python uses file paths directly
- **Dependency Management**: Zig declares dependencies explicitly; Python resolves at import time
- **Compile-Time Safety**: Zig catches missing modules at build time; Python fails at runtime
- **No Search Paths**: Zig doesn't search directories; all modules must be declared

### Module Registry Pattern

For complex projects, you might implement a module registry to track available modules:

```zig
const ModuleRegistry = struct {
    modules: std.StringHashMap(ModuleInfo),
    allocator: std.mem.Allocator,

    pub const ModuleInfo = struct {
        name: []const u8,
        path: []const u8,
        dependencies: []const []const u8,

        pub fn deinit(self: ModuleInfo, allocator: std.mem.Allocator) void {
            allocator.free(self.name);
            allocator.free(self.path);
            for (self.dependencies) |dep| {
                allocator.free(dep);
            }
            allocator.free(self.dependencies);
        }
    };

    pub fn init(allocator: std.mem.Allocator) ModuleRegistry {
        return .{
            .modules = std.StringHashMap(ModuleInfo).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *ModuleRegistry) void {
        var it = self.modules.iterator();
        while (it.next()) |entry| {
            entry.value_ptr.deinit(self.allocator);
            self.allocator.free(entry.key_ptr.*);
        }
        self.modules.deinit();
    }

    pub fn register(
        self: *ModuleRegistry,
        name: []const u8,
        path: []const u8,
        dependencies: []const []const u8,
    ) !void {
        const owned_name = try self.allocator.dupe(u8, name);
        errdefer self.allocator.free(owned_name);

        const owned_path = try self.allocator.dupe(u8, path);
        errdefer self.allocator.free(owned_path);

        const owned_deps = try self.allocator.alloc([]const u8, dependencies.len);
        errdefer self.allocator.free(owned_deps);

        var i: usize = 0;
        errdefer {
            for (owned_deps[0..i]) |dep| {
                self.allocator.free(dep);
            }
        }
        for (dependencies) |dep| {
            owned_deps[i] = try self.allocator.dupe(u8, dep);
            i += 1;
        }

        const info = ModuleInfo{
            .name = owned_name,
            .path = owned_path,
            .dependencies = owned_deps,
        };

        try self.modules.put(try self.allocator.dupe(u8, name), info);
    }

    pub fn get(self: *const ModuleRegistry, name: []const u8) ?ModuleInfo {
        return self.modules.get(name);
    }
};

test "module registry" {
    var registry = ModuleRegistry.init(testing.allocator);
    defer registry.deinit();

    try registry.register("core", "lib/core/core.zig", &.{});
    try registry.register("utils", "lib/utils/utils.zig", &.{"core"});

    const core = registry.get("core");
    try testing.expect(core != null);
    try testing.expectEqualStrings("lib/core/core.zig", core.?.path);

    const utils = registry.get("utils");
    try testing.expect(utils != null);
    try testing.expectEqual(@as(usize, 1), utils.?.dependencies.len);
}
```

This helps when generating build configurations or validating module dependencies.

### Path Resolution

When working with multiple directories, path resolution becomes important:

```zig
const PathResolver = struct {
    base_paths: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    pub fn addPath(self: *PathResolver, path: []const u8) !void {
        const owned_path = try self.allocator.dupe(u8, path);
        try self.base_paths.append(self.allocator, owned_path);
    }

    pub fn resolve(self: *PathResolver, relative_path: []const u8) !?[]u8 {
        for (self.base_paths.items) |base| {
            const full_path = try std.fs.path.join(
                self.allocator,
                &.{ base, relative_path },
            );
            // Check if file exists
            std.fs.cwd().access(full_path, .{}) catch {
                self.allocator.free(full_path);
                continue;
            };
            return full_path;
        }
        return null;
    }
};
```

This pattern searches multiple base directories for a file, similar to how compilers search include paths.

### Dependency Graphs

Complex projects benefit from dependency graph analysis to detect cycles and ensure correct build order:

```zig
const DependencyGraph = struct {
    nodes: std.StringHashMap(Node),
    allocator: std.mem.Allocator,

    const Node = struct {
        name: []const u8,
        dependencies: std.ArrayList([]const u8),
    };

    pub fn addNode(self: *DependencyGraph, name: []const u8) !void {
        const owned_name = try self.allocator.dupe(u8, name);
        const node = Node{
            .name = owned_name,
            .dependencies = std.ArrayList([]const u8){},
        };
        try self.nodes.put(try self.allocator.dupe(u8, name), node);
    }

    pub fn addDependency(
        self: *DependencyGraph,
        from: []const u8,
        to: []const u8,
    ) !void {
        var node = self.nodes.getPtr(from) orelse return error.NodeNotFound;
        const owned_dep = try self.allocator.dupe(u8, to);
        try node.dependencies.append(self.allocator, owned_dep);
    }

    pub fn hasCycle(self: *DependencyGraph) !bool {
        // Use DFS with visited/in-path tracking
        // Returns true if cycle detected
    }
};
```

Example usage:

```zig
var graph = DependencyGraph.init(allocator);
defer graph.deinit();

try graph.addNode("main");
try graph.addNode("utils");
try graph.addNode("core");

try graph.addDependency("main", "utils");
try graph.addDependency("utils", "core");

if (try graph.hasCycle()) {
    std.debug.print("Circular dependency detected!\n", .{});
}
```

### Module Loader Pattern

A module loader tracks what's been loaded to avoid duplicate work:

```zig
const ModuleLoader = struct {
    search_paths: std.ArrayList([]const u8),
    loaded_modules: std.StringHashMap(void),
    allocator: std.mem.Allocator,

    pub fn addSearchPath(self: *ModuleLoader, path: []const u8) !void {
        const owned = try self.allocator.dupe(u8, path);
        try self.search_paths.append(self.allocator, owned);
    }

    pub fn loadModule(self: *ModuleLoader, name: []const u8) !void {
        if (self.loaded_modules.contains(name)) {
            return; // Already loaded
        }

        const owned = try self.allocator.dupe(u8, name);
        try self.loaded_modules.put(owned, {});
    }

    pub fn isLoaded(self: *const ModuleLoader, name: []const u8) bool {
        return self.loaded_modules.contains(name);
    }
};
```

### Project Structure Helpers

Create utilities to work with standard project layouts:

```zig
const ProjectStructure = struct {
    root: []const u8,
    src_dir: []const u8,
    lib_dir: []const u8,
    vendor_dir: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, root: []const u8) !ProjectStructure {
        return .{
            .root = try allocator.dupe(u8, root),
            .src_dir = try std.fs.path.join(allocator, &.{ root, "src" }),
            .lib_dir = try std.fs.path.join(allocator, &.{ root, "lib" }),
            .vendor_dir = try std.fs.path.join(allocator, &.{ root, "vendor" }),
            .allocator = allocator,
        };
    }

    pub fn getModulePath(
        self: *ProjectStructure,
        category: []const u8,
        module: []const u8,
    ) ![]u8 {
        const base = if (std.mem.eql(u8, category, "lib"))
            self.lib_dir
        else if (std.mem.eql(u8, category, "vendor"))
            self.vendor_dir
        else
            self.src_dir;

        return std.fs.path.join(self.allocator, &.{ base, module });
    }
};
```

### Import Validation

For large teams, you might want to enforce module visibility rules:

```zig
const ImportValidator = struct {
    allowed_imports: std.StringHashMap(std.ArrayList([]const u8)),
    allocator: std.mem.Allocator,

    pub fn allowImport(
        self: *ImportValidator,
        module: []const u8,
        import: []const u8,
    ) !void {
        const gop = try self.allowed_imports.getOrPut(module);
        if (!gop.found_existing) {
            gop.key_ptr.* = try self.allocator.dupe(u8, module);
            gop.value_ptr.* = std.ArrayList([]const u8){};
        }

        const owned_import = try self.allocator.dupe(u8, import);
        try gop.value_ptr.append(self.allocator, owned_import);
    }

    pub fn canImport(
        self: *ImportValidator,
        module: []const u8,
        import: []const u8,
    ) bool {
        const imports = self.allowed_imports.get(module) orelse return false;
        for (imports.items) |allowed| {
            if (std.mem.eql(u8, allowed, import)) {
                return true;
            }
        }
        return false;
    }
};
```

Example usage:

```zig
var validator = ImportValidator.init(allocator);
defer validator.deinit();

// Define allowed imports
try validator.allowImport("main", "core");
try validator.allowImport("main", "utils");
try validator.allowImport("utils", "core");

// Validate an import
if (!validator.canImport("main", "vendor")) {
    std.debug.print("Import not allowed!\n", .{});
}
```

### Full Tested Code

```zig
// Recipe 10.9: Adding Directories to the Build Path
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to organize code across multiple directories
// and configure the build system to find modules in different locations.
//
// Key concepts:
// - Module organization across directories
// - Build.zig module configuration
// - Import paths and module resolution
// - Dependency management between modules
//
// Directory structure example:
// project/
// ├── build.zig
// ├── src/
// │   └── main.zig
// ├── lib/
// │   ├── core/
// │   │   └── core.zig
// │   └── utils/
// │       └── utils.zig
// └── vendor/
//     └── external/
//         └── external.zig

const std = @import("std");
const testing = std.testing;

// ANCHOR: module_structure
// This file demonstrates patterns for multi-directory projects.
// In a real project, these would be separate files in different directories.

// Simulating a core library module (lib/core/core.zig)
pub const CoreLib = struct {
    pub const version = "1.0.0";

    pub fn initialize() void {
        // Core initialization
    }

    pub fn shutdown() void {
        // Core shutdown
    }
};

// Simulating a utils library module (lib/utils/utils.zig)
pub const UtilsLib = struct {
    pub fn formatString(allocator: std.mem.Allocator, value: i32) ![]u8 {
        return std.fmt.allocPrint(allocator, "Value: {d}", .{value});
    }

    pub fn parseInteger(str: []const u8) !i32 {
        return std.fmt.parseInt(i32, str, 10);
    }
};

// Simulating an external vendor module (vendor/external/external.zig)
pub const ExternalLib = struct {
    pub const name = "external-lib";

    pub fn process(data: []const u8) usize {
        return data.len;
    }
};
// ANCHOR_END: module_structure

// ANCHOR: build_config_pattern
// In build.zig, modules are configured like this:
//
// const core = b.addModule("core", .{
//     .root_source_file = b.path("lib/core/core.zig"),
// });
//
// const utils = b.addModule("utils", .{
//     .root_source_file = b.path("lib/utils/utils.zig"),
//     .imports = &.{
//         .{ .name = "core", .module = core },
//     },
// });
//
// const external = b.addModule("external", .{
//     .root_source_file = b.path("vendor/external/external.zig"),
// });
//
// exe.root_module.addImport("core", core);
// exe.root_module.addImport("utils", utils);
// exe.root_module.addImport("external", external);
// ANCHOR_END: build_config_pattern

// ANCHOR: module_registry
const ModuleRegistry = struct {
    modules: std.StringHashMap(ModuleInfo),
    allocator: std.mem.Allocator,

    pub const ModuleInfo = struct {
        name: []const u8,
        path: []const u8,
        dependencies: []const []const u8,

        pub fn deinit(self: ModuleInfo, allocator: std.mem.Allocator) void {
            allocator.free(self.name);
            allocator.free(self.path);
            for (self.dependencies) |dep| {
                allocator.free(dep);
            }
            allocator.free(self.dependencies);
        }
    };

    pub fn init(allocator: std.mem.Allocator) ModuleRegistry {
        return .{
            .modules = std.StringHashMap(ModuleInfo).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *ModuleRegistry) void {
        var it = self.modules.iterator();
        while (it.next()) |entry| {
            entry.value_ptr.deinit(self.allocator);
            self.allocator.free(entry.key_ptr.*);
        }
        self.modules.deinit();
    }

    pub fn register(
        self: *ModuleRegistry,
        name: []const u8,
        path: []const u8,
        dependencies: []const []const u8,
    ) !void {
        const owned_name = try self.allocator.dupe(u8, name);
        errdefer self.allocator.free(owned_name);

        const owned_path = try self.allocator.dupe(u8, path);
        errdefer self.allocator.free(owned_path);

        const owned_deps = try self.allocator.alloc([]const u8, dependencies.len);
        errdefer self.allocator.free(owned_deps);

        var i: usize = 0;
        errdefer {
            for (owned_deps[0..i]) |dep| {
                self.allocator.free(dep);
            }
        }
        for (dependencies) |dep| {
            owned_deps[i] = try self.allocator.dupe(u8, dep);
            i += 1;
        }

        const info = ModuleInfo{
            .name = owned_name,
            .path = owned_path,
            .dependencies = owned_deps,
        };

        try self.modules.put(try self.allocator.dupe(u8, name), info);
    }

    pub fn get(self: *const ModuleRegistry, name: []const u8) ?ModuleInfo {
        return self.modules.get(name);
    }
};

test "module registry" {
    var registry = ModuleRegistry.init(testing.allocator);
    defer registry.deinit();

    try registry.register("core", "lib/core/core.zig", &.{});
    try registry.register("utils", "lib/utils/utils.zig", &.{"core"});

    const core = registry.get("core");
    try testing.expect(core != null);
    try testing.expectEqualStrings("lib/core/core.zig", core.?.path);

    const utils = registry.get("utils");
    try testing.expect(utils != null);
    try testing.expectEqual(@as(usize, 1), utils.?.dependencies.len);
}
// ANCHOR_END: module_registry

// ANCHOR: path_resolution
const PathResolver = struct {
    base_paths: std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) PathResolver {
        return .{
            .base_paths = std.ArrayList([]const u8){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *PathResolver) void {
        for (self.base_paths.items) |path| {
            self.allocator.free(path);
        }
        self.base_paths.deinit(self.allocator);
    }

    pub fn addPath(self: *PathResolver, path: []const u8) !void {
        const owned_path = try self.allocator.dupe(u8, path);
        try self.base_paths.append(self.allocator, owned_path);
    }

    pub fn resolve(self: *PathResolver, relative_path: []const u8) !?[]u8 {
        // Note: This is a stub implementation for demonstration.
        // Production code should check if file exists using std.fs.cwd().access()
        // before returning the path.
        for (self.base_paths.items) |base| {
            const full_path = try std.fs.path.join(
                self.allocator,
                &.{ base, relative_path },
            );
            // Always returns first path for demonstration purposes
            return full_path;
        }
        return null;
    }
};

test "path resolution" {
    var resolver = PathResolver.init(testing.allocator);
    defer resolver.deinit();

    try resolver.addPath("lib");
    try resolver.addPath("vendor");

    const resolved = try resolver.resolve("core/core.zig");
    try testing.expect(resolved != null);
    defer testing.allocator.free(resolved.?);

    try testing.expect(std.mem.endsWith(u8, resolved.?, "core/core.zig"));
}
// ANCHOR_END: path_resolution

// ANCHOR: dependency_graph
const DependencyGraph = struct {
    nodes: std.StringHashMap(Node),
    allocator: std.mem.Allocator,

    const Node = struct {
        name: []const u8,
        dependencies: std.ArrayList([]const u8),

        pub fn deinit(self: *Node, allocator: std.mem.Allocator) void {
            allocator.free(self.name);
            for (self.dependencies.items) |dep| {
                allocator.free(dep);
            }
            self.dependencies.deinit(allocator);
        }
    };

    pub fn init(allocator: std.mem.Allocator) DependencyGraph {
        return .{
            .nodes = std.StringHashMap(Node).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *DependencyGraph) void {
        var it = self.nodes.iterator();
        while (it.next()) |entry| {
            entry.value_ptr.deinit(self.allocator);
            self.allocator.free(entry.key_ptr.*);
        }
        self.nodes.deinit();
    }

    pub fn addNode(self: *DependencyGraph, name: []const u8) !void {
        const owned_name = try self.allocator.dupe(u8, name);
        const node = Node{
            .name = owned_name,
            .dependencies = std.ArrayList([]const u8){},
        };
        try self.nodes.put(try self.allocator.dupe(u8, name), node);
    }

    pub fn addDependency(
        self: *DependencyGraph,
        from: []const u8,
        to: []const u8,
    ) !void {
        var node = self.nodes.getPtr(from) orelse return error.NodeNotFound;
        const owned_dep = try self.allocator.dupe(u8, to);
        try node.dependencies.append(self.allocator, owned_dep);
    }

    pub fn hasCycle(self: *DependencyGraph) !bool {
        var visited = std.StringHashMap(bool).init(self.allocator);
        defer visited.deinit();

        var in_path = std.StringHashMap(bool).init(self.allocator);
        defer in_path.deinit();

        var it = self.nodes.iterator();
        while (it.next()) |entry| {
            if (try self.detectCycle(entry.key_ptr.*, &visited, &in_path)) {
                return true;
            }
        }

        return false;
    }

    fn detectCycle(
        self: *DependencyGraph,
        node_name: []const u8,
        visited: *std.StringHashMap(bool),
        in_path: *std.StringHashMap(bool),
    ) !bool {
        if (in_path.get(node_name)) |_| {
            return true; // Cycle detected
        }

        if (visited.get(node_name)) |_| {
            return false; // Already visited
        }

        try visited.put(node_name, true);
        try in_path.put(node_name, true);

        const node = self.nodes.get(node_name) orelse return false;
        for (node.dependencies.items) |dep| {
            if (try self.detectCycle(dep, visited, in_path)) {
                return true;
            }
        }

        _ = in_path.remove(node_name);
        return false;
    }
};

test "dependency graph" {
    var graph = DependencyGraph.init(testing.allocator);
    defer graph.deinit();

    try graph.addNode("main");
    try graph.addNode("utils");
    try graph.addNode("core");

    try graph.addDependency("main", "utils");
    try graph.addDependency("utils", "core");

    const has_cycle = try graph.hasCycle();
    try testing.expect(!has_cycle);
}

test "dependency graph cycle detection" {
    var graph = DependencyGraph.init(testing.allocator);
    defer graph.deinit();

    try graph.addNode("a");
    try graph.addNode("b");
    try graph.addNode("c");

    try graph.addDependency("a", "b");
    try graph.addDependency("b", "c");
    try graph.addDependency("c", "a"); // Creates cycle

    const has_cycle = try graph.hasCycle();
    try testing.expect(has_cycle);
}
// ANCHOR_END: dependency_graph

// ANCHOR: module_loader
const ModuleLoader = struct {
    search_paths: std.ArrayList([]const u8),
    loaded_modules: std.StringHashMap(void),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) ModuleLoader {
        return .{
            .search_paths = std.ArrayList([]const u8){},
            .loaded_modules = std.StringHashMap(void).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *ModuleLoader) void {
        for (self.search_paths.items) |path| {
            self.allocator.free(path);
        }
        self.search_paths.deinit(self.allocator);

        var it = self.loaded_modules.keyIterator();
        while (it.next()) |key| {
            self.allocator.free(key.*);
        }
        self.loaded_modules.deinit();
    }

    pub fn addSearchPath(self: *ModuleLoader, path: []const u8) !void {
        const owned = try self.allocator.dupe(u8, path);
        try self.search_paths.append(self.allocator, owned);
    }

    pub fn loadModule(self: *ModuleLoader, name: []const u8) !void {
        if (self.loaded_modules.contains(name)) {
            return; // Already loaded
        }

        const owned = try self.allocator.dupe(u8, name);
        try self.loaded_modules.put(owned, {});
    }

    pub fn isLoaded(self: *const ModuleLoader, name: []const u8) bool {
        return self.loaded_modules.contains(name);
    }
};

test "module loader" {
    var loader = ModuleLoader.init(testing.allocator);
    defer loader.deinit();

    try loader.addSearchPath("lib");
    try loader.addSearchPath("vendor");

    try loader.loadModule("core");
    try testing.expect(loader.isLoaded("core"));
    try testing.expect(!loader.isLoaded("utils"));

    try loader.loadModule("utils");
    try testing.expect(loader.isLoaded("utils"));
}
// ANCHOR_END: module_loader

// ANCHOR: project_structure
const ProjectStructure = struct {
    root: []const u8,
    src_dir: []const u8,
    lib_dir: []const u8,
    vendor_dir: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, root: []const u8) !ProjectStructure {
        return .{
            .root = try allocator.dupe(u8, root),
            .src_dir = try std.fs.path.join(allocator, &.{ root, "src" }),
            .lib_dir = try std.fs.path.join(allocator, &.{ root, "lib" }),
            .vendor_dir = try std.fs.path.join(allocator, &.{ root, "vendor" }),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *ProjectStructure) void {
        self.allocator.free(self.root);
        self.allocator.free(self.src_dir);
        self.allocator.free(self.lib_dir);
        self.allocator.free(self.vendor_dir);
    }

    pub fn getModulePath(
        self: *ProjectStructure,
        category: []const u8,
        module: []const u8,
    ) ![]u8 {
        const base = if (std.mem.eql(u8, category, "lib"))
            self.lib_dir
        else if (std.mem.eql(u8, category, "vendor"))
            self.vendor_dir
        else
            self.src_dir;

        return std.fs.path.join(
            self.allocator,
            &.{ base, module },
        );
    }
};

test "project structure" {
    var structure = try ProjectStructure.init(testing.allocator, "/project");
    defer structure.deinit();

    const lib_path = try structure.getModulePath("lib", "core.zig");
    defer testing.allocator.free(lib_path);

    try testing.expect(std.mem.endsWith(u8, lib_path, "lib/core.zig"));
}
// ANCHOR_END: project_structure

// ANCHOR: import_validator
const ImportValidator = struct {
    allowed_imports: std.StringHashMap(std.ArrayList([]const u8)),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) ImportValidator {
        return .{
            .allowed_imports = std.StringHashMap(std.ArrayList([]const u8)).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *ImportValidator) void {
        var it = self.allowed_imports.iterator();
        while (it.next()) |entry| {
            for (entry.value_ptr.items) |item| {
                self.allocator.free(item);
            }
            entry.value_ptr.deinit(self.allocator);
            self.allocator.free(entry.key_ptr.*);
        }
        self.allowed_imports.deinit();
    }

    pub fn allowImport(
        self: *ImportValidator,
        module: []const u8,
        import: []const u8,
    ) !void {
        const gop = try self.allowed_imports.getOrPut(module);
        if (!gop.found_existing) {
            gop.key_ptr.* = try self.allocator.dupe(u8, module);
            gop.value_ptr.* = std.ArrayList([]const u8){};
        }

        const owned_import = try self.allocator.dupe(u8, import);
        try gop.value_ptr.append(self.allocator, owned_import);
    }

    pub fn canImport(
        self: *ImportValidator,
        module: []const u8,
        import: []const u8,
    ) bool {
        const imports = self.allowed_imports.get(module) orelse return false;
        for (imports.items) |allowed| {
            if (std.mem.eql(u8, allowed, import)) {
                return true;
            }
        }
        return false;
    }
};

test "import validator" {
    var validator = ImportValidator.init(testing.allocator);
    defer validator.deinit();

    try validator.allowImport("main", "core");
    try validator.allowImport("main", "utils");
    try validator.allowImport("utils", "core");

    try testing.expect(validator.canImport("main", "core"));
    try testing.expect(validator.canImport("main", "utils"));
    try testing.expect(!validator.canImport("main", "vendor"));
    try testing.expect(validator.canImport("utils", "core"));
}
// ANCHOR_END: import_validator

// ANCHOR: build_example
// Example build.zig structure for multi-directory projects:
//
// pub fn build(b: *std.Build) void {
//     const target = b.standardTargetOptions(.{});
//     const optimize = b.standardOptimizeOption(.{});
//
//     // Define modules from different directories
//     const core = b.addModule("core", .{
//         .root_source_file = b.path("lib/core/core.zig"),
//     });
//
//     const utils = b.addModule("utils", .{
//         .root_source_file = b.path("lib/utils/utils.zig"),
//         .imports = &.{
//             .{ .name = "core", .module = core },
//         },
//     });
//
//     const external = b.addModule("external", .{
//         .root_source_file = b.path("vendor/external/external.zig"),
//     });
//
//     // Create executable
//     const exe = b.addExecutable(.{
//         .name = "myapp",
//         .root_source_file = b.path("src/main.zig"),
//         .target = target,
//         .optimize = optimize,
//     });
//
//     // Add module imports to executable
//     exe.root_module.addImport("core", core);
//     exe.root_module.addImport("utils", utils);
//     exe.root_module.addImport("external", external);
//
//     b.installArtifact(exe);
// }
// ANCHOR_END: build_example

// Comprehensive test
test "comprehensive build path management" {
    // Module registry
    var registry = ModuleRegistry.init(testing.allocator);
    defer registry.deinit();
    try registry.register("core", "lib/core/core.zig", &.{});

    // Path resolution
    var resolver = PathResolver.init(testing.allocator);
    defer resolver.deinit();
    try resolver.addPath("lib");

    // Dependency graph
    var graph = DependencyGraph.init(testing.allocator);
    defer graph.deinit();
    try graph.addNode("main");
    try graph.addNode("core");
    try graph.addDependency("main", "core");
    try testing.expect(!try graph.hasCycle());

    // Module loader
    var loader = ModuleLoader.init(testing.allocator);
    defer loader.deinit();
    try loader.loadModule("core");
    try testing.expect(loader.isLoaded("core"));
}
```

### See Also

- Recipe 10.1: Making a Hierarchical Package of Modules
- Recipe 10.3: Importing Package Submodules
- Recipe 10.4: Splitting a Module into Multiple Files
- Recipe 10.11: Distributing Packages

---

## Recipe 10.10: Importing Modules Using a Name Given in a String {#recipe-10-10}

**Tags:** build-system, comptime, error-handling, pointers, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_10.zig`

### Problem

You want to import or select a module dynamically based on a string value, similar to Python's `importlib.import_module()`. However, Zig's `@import` only accepts compile-time known string literals.

### Solution

While Zig doesn't support true runtime dynamic imports (by design), you can achieve similar functionality using compile-time module selection patterns. The key is distinguishing between compile-time module resolution and runtime module dispatch.

### Compile-Time Module Lookup

For string values known at compile time, use conditional logic:

```zig
fn getModule(comptime name: []const u8) type {
    if (std.mem.eql(u8, name, "module_a")) {
        return ModuleA;
    } else if (std.mem.eql(u8, name, "module_b")) {
        return ModuleB;
    } else if (std.mem.eql(u8, name, "module_c")) {
        return ModuleC;
    } else {
        @compileError("Unknown module: " ++ name);
    }
}

// Usage
const mod = getModule("module_a");
const result = mod.process(10);
```

### Switch-Based Selection with Enums

For cleaner code, use enums with `std.meta.stringToEnum`:

```zig
const ModuleName = enum {
    module_a,
    module_b,
    module_c,
};

fn selectModule(comptime name: []const u8) type {
    return switch (std.meta.stringToEnum(ModuleName, name) orelse
                   @compileError("Invalid module")) {
        .module_a => ModuleA,
        .module_b => ModuleB,
        .module_c => ModuleC,
    };
}

// Usage
const mod = selectModule("module_b");
```

### Module Registry Pattern

For more sophisticated module management:

```zig
const ModuleRegistry = struct {
    pub fn get(comptime name: []const u8) type {
        return inline for (registered_modules) |module| {
            if (std.mem.eql(u8, name, module.name)) {
                break module.type;
            }
        } else @compileError("Module not registered: " ++ name);
    }

    pub fn has(comptime name: []const u8) bool {
        inline for (registered_modules) |module| {
            if (std.mem.eql(u8, name, module.name)) {
                return true;
            }
        }
        return false;
    }

    pub fn list() []const ModuleEntry {
        return &registered_modules;
    }
};

const ModuleEntry = struct {
    name: []const u8,
    type: type,
};

const registered_modules = [_]ModuleEntry{
    .{ .name = "module_a", .type = ModuleA },
    .{ .name = "module_b", .type = ModuleB },
    .{ .name = "module_c", .type = ModuleC },
};
```

Usage:

```zig
// Check if module exists
if (ModuleRegistry.has("module_b")) {
    const mod = ModuleRegistry.get("module_b");
    // Use module...
}

// List all registered modules
const all_modules = ModuleRegistry.list();
```

### Discussion

### Why Zig Doesn't Have Dynamic Imports

Zig's philosophy prioritizes:
- **No hidden control flow**: All imports are visible at compile time
- **Performance**: No runtime module loading overhead
- **Safety**: Missing modules are compile errors, not runtime failures
- **Simplicity**: No need for complex module loading systems

This makes Zig programs more predictable and easier to analyze.

### Python vs Zig Comparison

**Python (Runtime Dynamic):**
```python
import importlib

# Runtime module loading
module_name = "module_a"  # Could come from config file
mod = importlib.import_module(module_name)
result = mod.process(10)

# Can load modules not known at compile time
user_input = input("Which module? ")
mod = importlib.import_module(user_input)
```

**Zig (Compile-Time Selection):**
```zig
// Compile-time module selection
const module_name = "module_a"; // Must be comptime known
const mod = getModule(module_name);
const result = mod.process(10);

// Cannot use runtime values for @import
// var user_input = getUserInput();
// const mod = @import(user_input); // ERROR!
```

The fundamental difference: Python loads modules at runtime; Zig resolves all modules at compile time.

### Runtime Dispatch Alternative

If you need runtime selection (e.g., loading different implementations based on config), use function pointer tables:

```zig
const ModuleInterface = struct {
    process_fn: *const fn (i32) i32,
    name: []const u8,
    version: []const u8,
};

const RuntimeModuleEntry = struct {
    name: []const u8,
    interface: ModuleInterface,
};

const module_entries = [_]RuntimeModuleEntry{
    .{ .name = "module_a", .interface = .{
        .process_fn = &ModuleA.process,
        .name = ModuleA.name,
        .version = ModuleA.version,
    } },
    .{ .name = "module_b", .interface = .{
        .process_fn = &ModuleB.process,
        .name = ModuleB.name,
        .version = ModuleB.version,
    } },
};

fn getModuleRuntime(name: []const u8) ?ModuleInterface {
    for (module_entries) |entry| {
        if (std.mem.eql(u8, entry.name, name)) {
            return entry.interface;
        }
    }
    return null;
}
```

Usage:

```zig
// Can use runtime value
var config = try loadConfig();
const module_name = config.preferred_module;

if (getModuleRuntime(module_name)) |mod| {
    const result = mod.process_fn(10);
    std.debug.print("Module: {s}, Result: {d}\n", .{ mod.name, result });
}
```

This provides runtime flexibility while maintaining compile-time safety (all possible modules are known at compile time).

### Generic Module Wrapper

Create a unified interface for different module types:

```zig
fn ModuleWrapper(comptime T: type) type {
    return struct {
        pub fn getName() []const u8 {
            return T.name;
        }

        pub fn getVersion() []const u8 {
            return T.version;
        }

        pub fn process(value: i32) i32 {
            return T.process(value);
        }

        pub fn getInfo() ModuleInfo {
            return .{
                .name = T.name,
                .version = T.version,
            };
        }
    };
}

// Usage
const wrapped = ModuleWrapper(ModuleA);
const name = wrapped.getName();
const result = wrapped.process(10);
```

### Module Loader with Fallback

Provide graceful fallback for missing modules:

```zig
const ModuleLoader = struct {
    pub fn load(comptime name: []const u8) type {
        if (ModuleRegistry.has(name)) {
            return ModuleRegistry.get(name);
        } else {
            @compileError("Failed to load module: " ++ name);
        }
    }

    pub fn loadWithFallback(comptime name: []const u8, comptime fallback: type) type {
        if (ModuleRegistry.has(name)) {
            return ModuleRegistry.get(name);
        } else {
            return fallback;
        }
    }
};

// Usage
const mod = ModuleLoader.loadWithFallback("optional_module", DefaultModule);
```

### Plugin System Pattern

For plugin architectures:

```zig
const PluginInterface = struct {
    init_fn: *const fn () void,
    process_fn: *const fn (i32) i32,
    deinit_fn: *const fn () void,
    name: []const u8,
};

const PluginRegistry = struct {
    const plugins = [_]PluginInterface{
        .{
            .init_fn = &pluginAInit,
            .process_fn = &ModuleA.process,
            .deinit_fn = &pluginADeinit,
            .name = "plugin_a",
        },
        .{
            .init_fn = &pluginBInit,
            .process_fn = &ModuleB.process,
            .deinit_fn = &pluginBDeinit,
            .name = "plugin_b",
        },
    };

    pub fn get(name: []const u8) ?PluginInterface {
        for (plugins) |plugin| {
            if (std.mem.eql(u8, plugin.name, name)) {
                return plugin;
            }
        }
        return null;
    }

    pub fn getAll() []const PluginInterface {
        return &plugins;
    }
};

fn pluginAInit() void {}
fn pluginADeinit() void {}
fn pluginBInit() void {}
fn pluginBDeinit() void {}

test "plugin system" {
    const plugin = PluginRegistry.get("plugin_a");
    try testing.expect(plugin != null);

    plugin.?.init_fn();
    const result = plugin.?.process_fn(10);
    try testing.expectEqual(@as(i32, 20), result);
    plugin.?.deinit_fn();

    const all = PluginRegistry.getAll();
    try testing.expectEqual(@as(usize, 2), all.len);
}
```

Usage:

```zig
// Load plugin by name at runtime
if (PluginRegistry.get("plugin_a")) |plugin| {
    plugin.init_fn();
    const result = plugin.process_fn(10);
    plugin.deinit_fn();
}

// Iterate all plugins
for (PluginRegistry.getAll()) |plugin| {
    std.debug.print("Plugin: {s}\n", .{plugin.name});
}
```

### Feature Flags Pattern

Enable/disable modules based on compile-time configuration:

```zig
const Features = struct {
    enable_module_a: bool = true,
    enable_module_b: bool = false,
    enable_module_c: bool = true,
};

fn getEnabledModule(comptime features: Features) type {
    if (features.enable_module_a) {
        return ModuleA;
    } else if (features.enable_module_b) {
        return ModuleB;
    } else if (features.enable_module_c) {
        return ModuleC;
    } else {
        @compileError("No module enabled");
    }
}

// Usage (typically configured in build.zig)
const features = Features{
    .enable_module_a = false,
    .enable_module_b = true,
    .enable_module_c = false,
};

const mod = getEnabledModule(features);
```

### Environment-Based Selection

Choose modules based on build environment:

```zig
fn getModuleForEnvironment(comptime env: []const u8) type {
    if (std.mem.eql(u8, env, "development")) {
        return DevelopmentModule;
    } else if (std.mem.eql(u8, env, "staging")) {
        return StagingModule;
    } else if (std.mem.eql(u8, env, "production")) {
        return ProductionModule;
    } else {
        @compileError("Unknown environment: " ++ env);
    }
}

// In build.zig, pass environment as build option
const env = b.option([]const u8, "env", "Build environment") orelse "development";
const mod = getModuleForEnvironment(env);
```

### Module Aliases

Create friendly names for modules:

```zig
const ModuleAlias = struct {
    pub const Primary = ModuleA;
    pub const Secondary = ModuleB;
    pub const Fallback = ModuleC;

    pub fn resolve(comptime alias: []const u8) type {
        if (std.mem.eql(u8, alias, "primary")) {
            return Primary;
        } else if (std.mem.eql(u8, alias, "secondary")) {
            return Secondary;
        } else if (std.mem.eql(u8, alias, "fallback")) {
            return Fallback;
        } else {
            @compileError("Unknown alias: " ++ alias);
        }
    }
};

// Usage
const mod = ModuleAlias.resolve("primary");
```

### Full Tested Code

```zig
// Recipe 10.10: Importing Modules Using a Name Given in a String
// Target Zig Version: 0.15.2
//
// This recipe demonstrates working with dynamic module selection in Zig.
// Unlike Python's importlib, Zig's @import requires compile-time known strings.
// This recipe shows patterns for achieving dynamic module selection at comptime.
//
// Key concepts:
// - Compile-time string matching
// - Module registry patterns
// - Switch-based module selection
// - Function pointer tables
// - Comptime module resolution

const std = @import("std");
const testing = std.testing;

// ANCHOR: module_simulation
// In a real project, these would be separate module files
pub const ModuleA = struct {
    pub const name = "module_a";
    pub const version = "1.0.0";

    pub fn process(value: i32) i32 {
        return value * 2;
    }
};

pub const ModuleB = struct {
    pub const name = "module_b";
    pub const version = "1.1.0";

    pub fn process(value: i32) i32 {
        return value + 10;
    }
};

pub const ModuleC = struct {
    pub const name = "module_c";
    pub const version = "2.0.0";

    pub fn process(value: i32) i32 {
        return value - 5;
    }
};
// ANCHOR_END: module_simulation

// ANCHOR: comptime_module_lookup
// Select a module at compile time based on a string
fn getModule(comptime name: []const u8) type {
    if (std.mem.eql(u8, name, "module_a")) {
        return ModuleA;
    } else if (std.mem.eql(u8, name, "module_b")) {
        return ModuleB;
    } else if (std.mem.eql(u8, name, "module_c")) {
        return ModuleC;
    } else {
        @compileError("Unknown module: " ++ name);
    }
}

test "comptime module lookup" {
    const mod = getModule("module_a");
    try testing.expectEqualStrings("module_a", mod.name);
    try testing.expectEqual(@as(i32, 20), mod.process(10));

    const mod_b = getModule("module_b");
    try testing.expectEqual(@as(i32, 20), mod_b.process(10));
}
// ANCHOR_END: comptime_module_lookup

// ANCHOR: switch_module_selection
fn selectModule(comptime name: []const u8) type {
    return switch (std.meta.stringToEnum(ModuleName, name) orelse @compileError("Invalid module")) {
        .module_a => ModuleA,
        .module_b => ModuleB,
        .module_c => ModuleC,
    };
}

const ModuleName = enum {
    module_a,
    module_b,
    module_c,
};

test "switch module selection" {
    const mod = selectModule("module_a");
    try testing.expectEqualStrings("module_a", mod.name);

    const mod_c = selectModule("module_c");
    try testing.expectEqual(@as(i32, 5), mod_c.process(10));
}
// ANCHOR_END: switch_module_selection

// ANCHOR: module_registry
const ModuleRegistry = struct {
    pub fn get(comptime name: []const u8) type {
        return inline for (registered_modules) |module| {
            if (std.mem.eql(u8, name, module.name)) {
                break module.type;
            }
        } else @compileError("Module not registered: " ++ name);
    }

    pub fn has(comptime name: []const u8) bool {
        inline for (registered_modules) |module| {
            if (std.mem.eql(u8, name, module.name)) {
                return true;
            }
        }
        return false;
    }

    pub fn list() []const ModuleEntry {
        return &registered_modules;
    }
};

const ModuleEntry = struct {
    name: []const u8,
    type: type,
};

const registered_modules = [_]ModuleEntry{
    .{ .name = "module_a", .type = ModuleA },
    .{ .name = "module_b", .type = ModuleB },
    .{ .name = "module_c", .type = ModuleC },
};

test "module registry" {
    const mod = ModuleRegistry.get("module_a");
    try testing.expectEqualStrings("module_a", mod.name);

    try testing.expect(ModuleRegistry.has("module_b"));
    try testing.expect(!ModuleRegistry.has("module_d"));

    const all_modules = ModuleRegistry.list();
    try testing.expectEqual(@as(usize, 3), all_modules.len);
}
// ANCHOR_END: module_registry

// ANCHOR: runtime_dispatch
const ModuleInterface = struct {
    process_fn: *const fn (i32) i32,
    name: []const u8,
    version: []const u8,
};

const RuntimeModuleEntry = struct {
    name: []const u8,
    interface: ModuleInterface,
};

const module_entries = [_]RuntimeModuleEntry{
    .{ .name = "module_a", .interface = .{
        .process_fn = &ModuleA.process,
        .name = ModuleA.name,
        .version = ModuleA.version,
    } },
    .{ .name = "module_b", .interface = .{
        .process_fn = &ModuleB.process,
        .name = ModuleB.name,
        .version = ModuleB.version,
    } },
    .{ .name = "module_c", .interface = .{
        .process_fn = &ModuleC.process,
        .name = ModuleC.name,
        .version = ModuleC.version,
    } },
};

fn getModuleRuntime(name: []const u8) ?ModuleInterface {
    for (module_entries) |entry| {
        if (std.mem.eql(u8, entry.name, name)) {
            return entry.interface;
        }
    }
    return null;
}

test "runtime module dispatch" {
    const module_name = "module_a"; // Could be runtime value
    const mod = getModuleRuntime(module_name);

    try testing.expect(mod != null);
    try testing.expectEqualStrings("module_a", mod.?.name);
    try testing.expectEqual(@as(i32, 20), mod.?.process_fn(10));

    const missing = getModuleRuntime("nonexistent");
    try testing.expect(missing == null);
}
// ANCHOR_END: runtime_dispatch

// ANCHOR: generic_module_wrapper
fn ModuleWrapper(comptime T: type) type {
    return struct {
        const Self = @This();

        pub fn getName() []const u8 {
            return T.name;
        }

        pub fn getVersion() []const u8 {
            return T.version;
        }

        pub fn process(value: i32) i32 {
            return T.process(value);
        }

        pub fn getInfo() ModuleInfo {
            return .{
                .name = T.name,
                .version = T.version,
            };
        }
    };
}

const ModuleInfo = struct {
    name: []const u8,
    version: []const u8,
};

test "generic module wrapper" {
    const wrapped = ModuleWrapper(ModuleA);

    try testing.expectEqualStrings("module_a", wrapped.getName());
    try testing.expectEqualStrings("1.0.0", wrapped.getVersion());
    try testing.expectEqual(@as(i32, 20), wrapped.process(10));
}
// ANCHOR_END: generic_module_wrapper

// ANCHOR: module_loader
const ModuleLoader = struct {
    pub fn load(comptime name: []const u8) type {
        if (ModuleRegistry.has(name)) {
            return ModuleRegistry.get(name);
        } else {
            @compileError("Failed to load module: " ++ name);
        }
    }

    pub fn loadWithFallback(comptime name: []const u8, comptime fallback: type) type {
        if (ModuleRegistry.has(name)) {
            return ModuleRegistry.get(name);
        } else {
            return fallback;
        }
    }
};

test "module loader" {
    const mod = ModuleLoader.load("module_a");
    try testing.expectEqualStrings("module_a", mod.name);

    const mod_with_fallback = ModuleLoader.loadWithFallback("nonexistent", ModuleB);
    try testing.expectEqualStrings("module_b", mod_with_fallback.name);
}
// ANCHOR_END: module_loader

// ANCHOR: conditional_import
fn conditionalModule(comptime condition: bool) type {
    if (condition) {
        return ModuleA;
    } else {
        return ModuleB;
    }
}

test "conditional module import" {
    const use_module_a = true;
    const mod = conditionalModule(use_module_a);

    try testing.expectEqualStrings("module_a", mod.name);
}
// ANCHOR_END: conditional_import

// ANCHOR: version_based_selection
fn getModuleByVersion(comptime min_version: []const u8) type {
    // Note: This is a simplified example. For production code, use
    // std.SemanticVersion for proper version parsing and comparison.
    // Currently always returns the latest version module.
    _ = min_version;

    if (std.mem.eql(u8, ModuleC.version, "2.0.0")) {
        return ModuleC;
    } else if (std.mem.eql(u8, ModuleB.version, "1.1.0")) {
        return ModuleB;
    } else {
        return ModuleA;
    }
}

test "version based selection" {
    const mod = getModuleByVersion("1.0.0");
    try testing.expectEqualStrings("2.0.0", mod.version);
}
// ANCHOR_END: version_based_selection

// ANCHOR: plugin_system
const PluginInterface = struct {
    init_fn: *const fn () void,
    process_fn: *const fn (i32) i32,
    deinit_fn: *const fn () void,
    name: []const u8,
};

const PluginRegistry = struct {
    const plugins = [_]PluginInterface{
        .{
            .init_fn = &pluginAInit,
            .process_fn = &ModuleA.process,
            .deinit_fn = &pluginADeinit,
            .name = "plugin_a",
        },
        .{
            .init_fn = &pluginBInit,
            .process_fn = &ModuleB.process,
            .deinit_fn = &pluginBDeinit,
            .name = "plugin_b",
        },
    };

    pub fn get(name: []const u8) ?PluginInterface {
        for (plugins) |plugin| {
            if (std.mem.eql(u8, plugin.name, name)) {
                return plugin;
            }
        }
        return null;
    }

    pub fn getAll() []const PluginInterface {
        return &plugins;
    }
};

fn pluginAInit() void {}
fn pluginADeinit() void {}
fn pluginBInit() void {}
fn pluginBDeinit() void {}

test "plugin system" {
    const plugin = PluginRegistry.get("plugin_a");
    try testing.expect(plugin != null);

    plugin.?.init_fn();
    const result = plugin.?.process_fn(10);
    try testing.expectEqual(@as(i32, 20), result);
    plugin.?.deinit_fn();

    const all = PluginRegistry.getAll();
    try testing.expectEqual(@as(usize, 2), all.len);
}
// ANCHOR_END: plugin_system

// ANCHOR: feature_flags
const Features = struct {
    enable_module_a: bool = true,
    enable_module_b: bool = false,
    enable_module_c: bool = true,
};

fn getEnabledModule(comptime features: Features) type {
    if (features.enable_module_a) {
        return ModuleA;
    } else if (features.enable_module_b) {
        return ModuleB;
    } else if (features.enable_module_c) {
        return ModuleC;
    } else {
        @compileError("No module enabled");
    }
}

test "feature flag selection" {
    const features = Features{
        .enable_module_a = false,
        .enable_module_b = true,
        .enable_module_c = false,
    };

    const mod = getEnabledModule(features);
    try testing.expectEqualStrings("module_b", mod.name);
}
// ANCHOR_END: feature_flags

// ANCHOR: lazy_module_loading
// Note: This demonstrates the lazy loading pattern conceptually.
// Since everything is comptime, there's no runtime performance benefit.
// For actual runtime lazy loading, use optionals with runtime checks.
const LazyModule = struct {
    loaded: bool = false,
    module_type: type,

    pub fn get(comptime self: *LazyModule) type {
        if (!self.loaded) {
            self.loaded = true;
        }
        return self.module_type;
    }
};

test "lazy module loading" {
    comptime var lazy = LazyModule{ .module_type = ModuleA };
    try testing.expect(!lazy.loaded);

    const mod = lazy.get();
    try testing.expect(lazy.loaded);
    try testing.expectEqualStrings("module_a", mod.name);
}
// ANCHOR_END: lazy_module_loading

// ANCHOR: module_alias
const ModuleAlias = struct {
    pub const Primary = ModuleA;
    pub const Secondary = ModuleB;
    pub const Fallback = ModuleC;

    pub fn resolve(comptime alias: []const u8) type {
        if (std.mem.eql(u8, alias, "primary")) {
            return Primary;
        } else if (std.mem.eql(u8, alias, "secondary")) {
            return Secondary;
        } else if (std.mem.eql(u8, alias, "fallback")) {
            return Fallback;
        } else {
            @compileError("Unknown alias: " ++ alias);
        }
    }
};

test "module aliases" {
    const mod = ModuleAlias.resolve("primary");
    try testing.expectEqualStrings("module_a", mod.name);

    const fallback = ModuleAlias.resolve("fallback");
    try testing.expectEqualStrings("module_c", fallback.name);
}
// ANCHOR_END: module_alias

// ANCHOR: environment_based
fn getModuleForEnvironment(comptime env: []const u8) type {
    if (std.mem.eql(u8, env, "development")) {
        return ModuleA;
    } else if (std.mem.eql(u8, env, "staging")) {
        return ModuleB;
    } else if (std.mem.eql(u8, env, "production")) {
        return ModuleC;
    } else {
        @compileError("Unknown environment: " ++ env);
    }
}

test "environment based selection" {
    const mod = getModuleForEnvironment("production");
    try testing.expectEqualStrings("module_c", mod.name);
}
// ANCHOR_END: environment_based

// Comprehensive test
test "comprehensive module selection patterns" {
    // Comptime lookup
    const mod_a = getModule("module_a");
    try testing.expectEqual(@as(i32, 20), mod_a.process(10));

    // Switch selection
    const mod_b = selectModule("module_b");
    try testing.expectEqual(@as(i32, 20), mod_b.process(10));

    // Registry
    try testing.expect(ModuleRegistry.has("module_c"));

    // Runtime dispatch
    const runtime_mod = getModuleRuntime("module_a");
    try testing.expect(runtime_mod != null);

    // Plugin system
    const plugin = PluginRegistry.get("plugin_a");
    try testing.expect(plugin != null);
}
```

### See Also

- Recipe 10.1: Making a Hierarchical Package of Modules
- Recipe 10.7: Making a Directory or Zip File Runnable
- Recipe 9.11: Using Comptime to Control Instance Creation
- Recipe 9.13: Defining a Generic that Takes Optional Arguments

---

## Recipe 10.11: Distributing Packages {#recipe-10-11}

**Tags:** allocators, arraylist, build-system, comptime, data-structures, error-handling, http, memory, networking, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/10-modules-build-system/recipe_10_11.zig`

### Problem

You want to package your Zig code for distribution so others can use it as a dependency, similar to publishing to PyPI in Python. You need to manage metadata, versioning, dependencies, and public APIs.

### Solution

Zig uses a Git-based package system with `build.zig.zon` for metadata, rather than a central package repository like PyPI. This recipe demonstrates patterns for creating distributable Zig packages.

### Package Metadata

Define package information in a structured format:

```zig
// Package metadata (typically in build.zig.zon)
pub const PackageMetadata = struct {
    name: []const u8,
    version: SemanticVersion,
    description: []const u8,
    author: []const u8,
    license: []const u8,
    repository: ?[]const u8,
    homepage: ?[]const u8,

    pub fn format(
        self: PackageMetadata,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("{s} v{}", .{ self.name, self.version });
    }
};

test "package metadata" {
    const pkg = PackageMetadata{
        .name = "my-awesome-lib",
        .version = .{ .major = 1, .minor = 2, .patch = 3 },
        .description = "An awesome Zig library",
        .author = "Jane Developer",
        .license = "MIT",
        .repository = "https://github.com/user/my-awesome-lib",
        .homepage = "https://my-awesome-lib.dev",
    };

    try testing.expectEqualStrings("my-awesome-lib", pkg.name);
    try testing.expectEqual(@as(u32, 1), pkg.version.major);
}
```

Example usage:

```zig
const pkg = PackageMetadata{
    .name = "my-awesome-lib",
    .version = .{ .major = 1, .minor = 2, .patch = 3 },
    .description = "An awesome Zig library",
    .author = "Jane Developer",
    .license = "MIT",
    .repository = "https://github.com/user/my-awesome-lib",
    .homepage = "https://my-awesome-lib.dev",
};
```

### Semantic Versioning

Implement proper semantic versioning with compatibility checks:

```zig
pub const SemanticVersion = struct {
    major: u32,
    minor: u32,
    patch: u32,
    prerelease: ?[]const u8 = null,
    build: ?[]const u8 = null,

    pub fn isCompatible(self: SemanticVersion, required: SemanticVersion) bool {
        // Major version must match for compatibility
        if (self.major != required.major) return false;

        // Special case: 0.x.x versions are unstable
        // Minor version must match exactly for 0.x.x
        if (self.major == 0) {
            if (self.minor != required.minor) return false;
            // Patch can be >= for 0.x.x within same minor version
            return self.patch >= required.patch;
        }

        // For stable versions (1.x.x+), minor.patch must be >= required
        if (self.minor < required.minor) return false;
        if (self.minor == required.minor and self.patch < required.patch) return false;

        return true;
    }
};
```

Version compatibility examples:
- `1.2.3` is compatible with `1.2.0` ✓
- `1.2.3` is compatible with `1.1.0` ✓
- `1.2.3` is NOT compatible with `2.0.0` ✗
- `0.2.0` is NOT compatible with `0.1.0` ✗ (0.x.x is unstable)

### Dependency Specification

Define dependencies with URLs and optional version/hash constraints:

```zig
pub const DependencySpec = struct {
    name: []const u8,
    url: []const u8,
    hash: ?[]const u8 = null,
    version: ?SemanticVersion = null,

    pub fn isValid(self: DependencySpec) bool {
        return self.name.len > 0 and self.url.len > 0;
    }
};
```

Example:

```zig
const dep = DependencySpec{
    .name = "zlib",
    .url = "https://github.com/madler/zlib",
    .hash = "1234567890abcdef",
    .version = .{ .major = 1, .minor = 3, .patch = 0 },
};
```

### Discussion

### Python vs Zig Package Distribution

The approaches differ fundamentally:

**Python (PyPI):**
```python
# setup.py
from setuptools import setup

setup(
    name='my-package',
    version='1.2.3',
    description='My awesome package',
    author='Jane Developer',
    install_requires=[
        'requests>=2.28.0',
        'numpy>=1.20.0',
    ],
    # ... more metadata
)

# Publish:
# python setup.py sdist upload
```

**Zig (Git-based):**
```zig
// build.zig.zon
.{
    .name = "my-package",
    .version = "1.2.3",
    .dependencies = .{
        .httpz = .{
            .url = "https://github.com/karlseguin/http.zig/archive/master.tar.gz",
            .hash = "1220abcdef...",
        },
    },
}

// Publish:
// git tag v1.2.3
// git push origin v1.2.3
```

Key differences:
- **Distribution**: Zig uses Git tags; Python uses PyPI
- **Dependencies**: Zig references Git URLs; Python uses package names
- **Verification**: Zig uses content hashes; Python uses signatures
- **Centralization**: Zig is decentralized; Python has a central repository

### Public API Design

Design a clean, stable public API for your package:

```zig
pub const PublicAPI = struct {
    // Version information
    pub const version = SemanticVersion{ .major = 1, .minor = 0, .patch = 0 };

    // Main functionality
    pub fn process(value: i32) i32 {
        return value * 2;
    }

    pub fn processWithOptions(value: i32, options: ProcessOptions) i32 {
        var result = value;
        if (options.double) result *= 2;
        if (options.add_ten) result += 10;
        return result;
    }

    // Configuration
    pub const ProcessOptions = struct {
        double: bool = true,
        add_ten: bool = false,
    };

    // Error types
    pub const Error = error{
        InvalidInput,
        ProcessingFailed,
    };

    /// Process multiple values and return owned slice.
    /// Caller owns returned memory and must free it.
    pub fn processAdvanced(allocator: std.mem.Allocator, values: []const i32) ![]i32 {
        const result = try allocator.alloc(i32, values.len);
        errdefer allocator.free(result);

        for (values, 0..) |val, i| {
            result[i] = val * 2;
        }
        return result;
    }
};
```

Usage:

```zig
const result = PublicAPI.process(10);

const options = PublicAPI.ProcessOptions{ .double = true, .add_ten = true };
const result2 = PublicAPI.processWithOptions(10, options);

const values = [_]i32{ 1, 2, 3 };
const results = try PublicAPI.processAdvanced(allocator, &values);
defer allocator.free(results);
```

### Library Organization

Organize exports into logical namespaces:

```zig
pub const Library = struct {
    // Core functionality
    pub const core = struct {
        pub fn initialize() void {}
        pub fn shutdown() void {}
    };

    // Utilities
    pub const utils = struct {
        pub fn helper(value: i32) i32 {
            return value + 1;
        }
    };

    // Types
    pub const types = struct {
        pub const Config = struct {
            enabled: bool = true,
            timeout: u32 = 5000,
        };
    };

    // Constants
    pub const constants = struct {
        pub const MAX_SIZE: usize = 1024;
        pub const DEFAULT_TIMEOUT: u32 = 5000;
    };
};
```

Usage:

```zig
Library.core.initialize();
defer Library.core.shutdown();

const result = Library.utils.helper(10);
const config = Library.types.Config{};
```

### Package Builder Pattern

Use the builder pattern for constructing package manifests:

```zig
var builder = PackageBuilder.init(allocator, metadata);
defer builder.deinit();

try builder.addDependency(.{
    .name = "dep1",
    .url = "https://example.com/dep1",
});

try builder.addDependency(.{
    .name = "dep2",
    .url = "https://example.com/dep2",
    .version = .{ .major = 1, .minor = 0, .patch = 0 },
});

const manifest = try builder.build();
defer manifest.deinit(allocator);
```

### Package Validation

Validate package metadata before distribution:

```zig
pub const PackageValidator = struct {
    pub const ValidationError = error{
        InvalidName,
        InvalidVersion,
        MissingDescription,
        MissingLicense,
        InvalidDependency,
    };

    pub fn validate(pkg: PackageMetadata) ValidationError!void {
        if (pkg.name.len == 0) {
            return ValidationError.InvalidName;
        }

        if (pkg.version.major == 0 and
            pkg.version.minor == 0 and
            pkg.version.patch == 0) {
            return ValidationError.InvalidVersion;
        }

        if (pkg.description.len == 0) {
            return ValidationError.MissingDescription;
        }

        if (pkg.license.len == 0) {
            return ValidationError.MissingLicense;
        }
    }
};
```

Usage:

```zig
try PackageValidator.validate(metadata);
```

### License Management

Define and validate licenses:

```zig
pub const License = enum {
    MIT,
    Apache2,
    GPL3,
    BSD3Clause,
    Custom,

    pub fn getSPDXIdentifier(self: License) []const u8 {
        return switch (self) {
            .MIT => "MIT",
            .Apache2 => "Apache-2.0",
            .GPL3 => "GPL-3.0-or-later",
            .BSD3Clause => "BSD-3-Clause",
            .Custom => "SEE LICENSE IN LICENSE",
        };
    }

    pub fn requiresAttribution(self: License) bool {
        // All these licenses require copyright notice preservation
        return switch (self) {
            .MIT, .Apache2, .BSD3Clause, .GPL3 => true,
            .Custom => true, // Assume yes for safety
        };
    }
};
```

### Build Configuration

Define build options for different scenarios:

```zig
pub const BuildConfig = struct {
    optimization: OptimizationMode = .Debug,
    target_arch: ?[]const u8 = null,
    target_os: ?[]const u8 = null,
    strip_debug: bool = false,
    enable_tests: bool = true,

    pub const OptimizationMode = enum {
        Debug,
        ReleaseSafe,
        ReleaseFast,
        ReleaseSmall,
    };

    pub fn isRelease(self: BuildConfig) bool {
        return self.optimization != .Debug;
    }
};
```

### Documentation Metadata

Embed documentation in your package:

```zig
pub const Documentation = struct {
    summary: []const u8,
    detailed: []const u8,
    examples: []const Example,

    pub const Example = struct {
        title: []const u8,
        code: []const u8,
        description: []const u8,
    };
};

pub const module_docs = Documentation{
    .summary = "A package distribution example for Zig",
    .detailed = "This module demonstrates patterns for distributing Zig packages.",
    .examples = &.{
        .{
            .title = "Basic usage",
            .code = "const result = PublicAPI.process(10);",
            .description = "Process a value using the public API",
        },
    },
};
```

### Full Tested Code

```zig
// Recipe 10.11: Distributing Packages
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to prepare and distribute Zig packages.
// Unlike Python's setup.py and PyPI, Zig uses build.zig.zon and Git-based packages.
//
// Key concepts:
// - Package metadata in build.zig.zon
// - Semantic versioning
// - Dependency declarations
// - Library vs executable distribution
// - Public API design
// - Package documentation

const std = @import("std");
const testing = std.testing;

// ANCHOR: package_metadata
// Package metadata (typically in build.zig.zon)
pub const PackageMetadata = struct {
    name: []const u8,
    version: SemanticVersion,
    description: []const u8,
    author: []const u8,
    license: []const u8,
    repository: ?[]const u8,
    homepage: ?[]const u8,

    pub fn format(
        self: PackageMetadata,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("{s} v{}", .{ self.name, self.version });
    }
};

test "package metadata" {
    const pkg = PackageMetadata{
        .name = "my-awesome-lib",
        .version = .{ .major = 1, .minor = 2, .patch = 3 },
        .description = "An awesome Zig library",
        .author = "Jane Developer",
        .license = "MIT",
        .repository = "https://github.com/user/my-awesome-lib",
        .homepage = "https://my-awesome-lib.dev",
    };

    try testing.expectEqualStrings("my-awesome-lib", pkg.name);
    try testing.expectEqual(@as(u32, 1), pkg.version.major);
}
// ANCHOR_END: package_metadata

// ANCHOR: semantic_version
pub const SemanticVersion = struct {
    major: u32,
    minor: u32,
    patch: u32,
    prerelease: ?[]const u8 = null,
    build: ?[]const u8 = null,

    pub fn format(
        self: SemanticVersion,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("{d}.{d}.{d}", .{ self.major, self.minor, self.patch });
        if (self.prerelease) |pre| {
            try writer.print("-{s}", .{pre});
        }
        if (self.build) |b| {
            try writer.print("+{s}", .{b});
        }
    }

    pub fn isCompatible(self: SemanticVersion, required: SemanticVersion) bool {
        // Major version must match for compatibility
        if (self.major != required.major) return false;

        // Special case: 0.x.x versions are unstable
        // Minor version must match exactly for 0.x.x
        if (self.major == 0) {
            if (self.minor != required.minor) return false;
            // Patch can be >= for 0.x.x within same minor version
            return self.patch >= required.patch;
        }

        // For stable versions (1.x.x+), minor.patch must be >= required
        if (self.minor < required.minor) return false;
        if (self.minor == required.minor and self.patch < required.patch) return false;

        return true;
    }
};

test "semantic version formatting" {
    const v1 = SemanticVersion{ .major = 1, .minor = 2, .patch = 3 };
    const v2 = SemanticVersion{
        .major = 2,
        .minor = 0,
        .patch = 0,
        .prerelease = "beta.1",
        .build = "20250115",
    };

    _ = v1;
    _ = v2;
}

test "semantic version compatibility" {
    const v1_2_3 = SemanticVersion{ .major = 1, .minor = 2, .patch = 3 };
    const v1_2_0 = SemanticVersion{ .major = 1, .minor = 2, .patch = 0 };
    const v1_1_0 = SemanticVersion{ .major = 1, .minor = 1, .patch = 0 };
    const v2_0_0 = SemanticVersion{ .major = 2, .minor = 0, .patch = 0 };

    try testing.expect(v1_2_3.isCompatible(v1_2_0));
    try testing.expect(v1_2_3.isCompatible(v1_1_0));
    try testing.expect(!v1_2_3.isCompatible(v2_0_0));
    try testing.expect(!v1_1_0.isCompatible(v1_2_0));
}
// ANCHOR_END: semantic_version

// ANCHOR: dependency_spec
pub const DependencySpec = struct {
    name: []const u8,
    url: []const u8,
    hash: ?[]const u8 = null,
    version: ?SemanticVersion = null,

    pub fn isValid(self: DependencySpec) bool {
        return self.name.len > 0 and self.url.len > 0;
    }
};

test "dependency specification" {
    const dep = DependencySpec{
        .name = "zlib",
        .url = "https://github.com/madler/zlib",
        .hash = "1234567890abcdef",
        .version = .{ .major = 1, .minor = 3, .patch = 0 },
    };

    try testing.expect(dep.isValid());
    try testing.expectEqualStrings("zlib", dep.name);
}
// ANCHOR_END: dependency_spec

// ANCHOR: public_api
// A well-designed public API for a distributed package
pub const PublicAPI = struct {
    // Version information
    pub const version = SemanticVersion{ .major = 1, .minor = 0, .patch = 0 };

    // Main functionality
    pub fn process(value: i32) i32 {
        return value * 2;
    }

    pub fn processWithOptions(value: i32, options: ProcessOptions) i32 {
        var result = value;
        if (options.double) result *= 2;
        if (options.add_ten) result += 10;
        return result;
    }

    // Configuration
    pub const ProcessOptions = struct {
        double: bool = true,
        add_ten: bool = false,
    };

    // Error types
    pub const Error = error{
        InvalidInput,
        ProcessingFailed,
    };

    // Advanced functionality
    /// Process multiple values and return owned slice.
    /// Caller owns returned memory and must free it.
    pub fn processAdvanced(allocator: std.mem.Allocator, values: []const i32) ![]i32 {
        const result = try allocator.alloc(i32, values.len);
        errdefer allocator.free(result);

        for (values, 0..) |val, i| {
            result[i] = val * 2;
        }
        return result;
    }
};

test "public API usage" {
    const result = PublicAPI.process(10);
    try testing.expectEqual(@as(i32, 20), result);

    const options = PublicAPI.ProcessOptions{ .double = true, .add_ten = true };
    const result2 = PublicAPI.processWithOptions(10, options);
    try testing.expectEqual(@as(i32, 30), result2);

    const values = [_]i32{ 1, 2, 3 };
    const results = try PublicAPI.processAdvanced(testing.allocator, &values);
    defer testing.allocator.free(results);

    try testing.expectEqual(@as(i32, 2), results[0]);
    try testing.expectEqual(@as(i32, 4), results[1]);
    try testing.expectEqual(@as(i32, 6), results[2]);
}
// ANCHOR_END: public_api

// ANCHOR: library_exports
// Pattern for organizing library exports
pub const Library = struct {
    // Core functionality
    pub const core = struct {
        pub fn initialize() void {}
        pub fn shutdown() void {}
    };

    // Utilities
    pub const utils = struct {
        pub fn helper(value: i32) i32 {
            return value + 1;
        }
    };

    // Types
    pub const types = struct {
        pub const Config = struct {
            enabled: bool = true,
            timeout: u32 = 5000,
        };
    };

    // Constants
    pub const constants = struct {
        pub const MAX_SIZE: usize = 1024;
        pub const DEFAULT_TIMEOUT: u32 = 5000;
    };
};

test "library exports" {
    Library.core.initialize();
    defer Library.core.shutdown();

    const result = Library.utils.helper(10);
    try testing.expectEqual(@as(i32, 11), result);

    const config = Library.types.Config{};
    try testing.expect(config.enabled);
    try testing.expectEqual(@as(u32, 5000), config.timeout);

    try testing.expectEqual(@as(usize, 1024), Library.constants.MAX_SIZE);
}
// ANCHOR_END: library_exports

// ANCHOR: package_builder
/// Builder pattern for constructing package manifests.
///
/// Example:
///     var builder = PackageBuilder.init(allocator, metadata);
///     defer builder.deinit();
///     try builder.addDependency(dep1);
///     try builder.addDependency(dep2);
///     const manifest = try builder.build();
///     defer manifest.deinit(allocator);
pub const PackageBuilder = struct {
    metadata: PackageMetadata,
    dependencies: std.ArrayList(DependencySpec),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, metadata: PackageMetadata) PackageBuilder {
        return .{
            .metadata = metadata,
            .dependencies = std.ArrayList(DependencySpec){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *PackageBuilder) void {
        self.dependencies.deinit(self.allocator);
    }

    pub fn addDependency(self: *PackageBuilder, dep: DependencySpec) !void {
        try self.dependencies.append(self.allocator, dep);
    }

    pub fn build(self: *PackageBuilder) !PackageManifest {
        return PackageManifest{
            .metadata = self.metadata,
            .dependencies = try self.dependencies.toOwnedSlice(self.allocator),
        };
    }
};

pub const PackageManifest = struct {
    metadata: PackageMetadata,
    dependencies: []DependencySpec,

    pub fn deinit(self: PackageManifest, allocator: std.mem.Allocator) void {
        allocator.free(self.dependencies);
    }
};

test "package builder" {
    const metadata = PackageMetadata{
        .name = "test-package",
        .version = .{ .major = 1, .minor = 0, .patch = 0 },
        .description = "Test package",
        .author = "Test Author",
        .license = "MIT",
        .repository = null,
        .homepage = null,
    };

    var builder = PackageBuilder.init(testing.allocator, metadata);
    defer builder.deinit();

    try builder.addDependency(.{
        .name = "dep1",
        .url = "https://example.com/dep1",
    });

    const manifest = try builder.build();
    defer manifest.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 1), manifest.dependencies.len);
}
// ANCHOR_END: package_builder

// ANCHOR: compatibility_check
pub const CompatibilityChecker = struct {
    pub fn checkVersion(
        provided: SemanticVersion,
        required: SemanticVersion,
    ) CompatibilityResult {
        if (provided.major != required.major) {
            return .incompatible;
        }

        if (provided.major == 0) {
            // Pre-1.0, minor version must match
            if (provided.minor != required.minor) {
                return .incompatible;
            }
        }

        if (provided.minor < required.minor) {
            return .incompatible;
        }

        if (provided.minor == required.minor and provided.patch < required.patch) {
            return .incompatible;
        }

        if (provided.minor > required.minor or provided.patch > required.patch) {
            return .compatible_newer;
        }

        return .compatible_exact;
    }
};

pub const CompatibilityResult = enum {
    compatible_exact,
    compatible_newer,
    incompatible,
};

test "compatibility checker" {
    const v1_0_0 = SemanticVersion{ .major = 1, .minor = 0, .patch = 0 };
    const v1_1_0 = SemanticVersion{ .major = 1, .minor = 1, .patch = 0 };
    const v2_0_0 = SemanticVersion{ .major = 2, .minor = 0, .patch = 0 };

    const result1 = CompatibilityChecker.checkVersion(v1_0_0, v1_0_0);
    try testing.expectEqual(CompatibilityResult.compatible_exact, result1);

    const result2 = CompatibilityChecker.checkVersion(v1_1_0, v1_0_0);
    try testing.expectEqual(CompatibilityResult.compatible_newer, result2);

    const result3 = CompatibilityChecker.checkVersion(v1_0_0, v2_0_0);
    try testing.expectEqual(CompatibilityResult.incompatible, result3);
}
// ANCHOR_END: compatibility_check

// ANCHOR: documentation_metadata
pub const Documentation = struct {
    summary: []const u8,
    detailed: []const u8,
    examples: []const Example,

    pub const Example = struct {
        title: []const u8,
        code: []const u8,
        description: []const u8,
    };
};

pub const module_docs = Documentation{
    .summary = "A package distribution example for Zig",
    .detailed = "This module demonstrates patterns for distributing Zig packages.",
    .examples = &.{
        .{
            .title = "Basic usage",
            .code = "const result = PublicAPI.process(10);",
            .description = "Process a value using the public API",
        },
    },
};

test "documentation metadata" {
    try testing.expectEqualStrings("A package distribution example for Zig", module_docs.summary);
    try testing.expectEqual(@as(usize, 1), module_docs.examples.len);
}
// ANCHOR_END: documentation_metadata

// ANCHOR: build_configuration
pub const BuildConfig = struct {
    optimization: OptimizationMode = .Debug,
    target_arch: ?[]const u8 = null,
    target_os: ?[]const u8 = null,
    strip_debug: bool = false,
    enable_tests: bool = true,

    pub const OptimizationMode = enum {
        Debug,
        ReleaseSafe,
        ReleaseFast,
        ReleaseSmall,
    };

    pub fn isRelease(self: BuildConfig) bool {
        return self.optimization != .Debug;
    }
};

test "build configuration" {
    const debug_config = BuildConfig{};
    try testing.expect(!debug_config.isRelease());

    const release_config = BuildConfig{ .optimization = .ReleaseFast };
    try testing.expect(release_config.isRelease());
}
// ANCHOR_END: build_configuration

// ANCHOR: package_validator
pub const PackageValidator = struct {
    pub const ValidationError = error{
        InvalidName,
        InvalidVersion,
        MissingDescription,
        MissingLicense,
        InvalidDependency,
    };

    pub fn validate(pkg: PackageMetadata) ValidationError!void {
        if (pkg.name.len == 0) {
            return ValidationError.InvalidName;
        }

        if (pkg.version.major == 0 and pkg.version.minor == 0 and pkg.version.patch == 0) {
            return ValidationError.InvalidVersion;
        }

        if (pkg.description.len == 0) {
            return ValidationError.MissingDescription;
        }

        if (pkg.license.len == 0) {
            return ValidationError.MissingLicense;
        }
    }
};

test "package validator" {
    const valid_pkg = PackageMetadata{
        .name = "valid-package",
        .version = .{ .major = 1, .minor = 0, .patch = 0 },
        .description = "A valid package",
        .author = "Author",
        .license = "MIT",
        .repository = null,
        .homepage = null,
    };

    try PackageValidator.validate(valid_pkg);

    const invalid_pkg = PackageMetadata{
        .name = "",
        .version = .{ .major = 0, .minor = 0, .patch = 0 },
        .description = "",
        .author = "",
        .license = "",
        .repository = null,
        .homepage = null,
    };

    const result = PackageValidator.validate(invalid_pkg);
    try testing.expectError(PackageValidator.ValidationError.InvalidName, result);
}
// ANCHOR_END: package_validator

// ANCHOR: license_info
pub const License = enum {
    MIT,
    Apache2,
    GPL3,
    BSD3Clause,
    Custom,

    pub fn getSPDXIdentifier(self: License) []const u8 {
        return switch (self) {
            .MIT => "MIT",
            .Apache2 => "Apache-2.0",
            .GPL3 => "GPL-3.0-or-later",
            .BSD3Clause => "BSD-3-Clause",
            .Custom => "SEE LICENSE IN LICENSE",
        };
    }

    pub fn requiresAttribution(self: License) bool {
        // All these licenses require copyright notice preservation
        return switch (self) {
            .MIT, .Apache2, .BSD3Clause, .GPL3 => true,
            .Custom => true, // Assume yes for safety
        };
    }
};

test "license info" {
    const mit = License.MIT;
    try testing.expectEqualStrings("MIT", mit.getSPDXIdentifier());
    try testing.expect(mit.requiresAttribution());
}
// ANCHOR_END: license_info

// Comprehensive test
test "comprehensive package distribution" {
    // Package metadata
    const metadata = PackageMetadata{
        .name = "example-lib",
        .version = .{ .major = 1, .minor = 0, .patch = 0 },
        .description = "Example library",
        .author = "Developer",
        .license = "MIT",
        .repository = "https://github.com/user/example-lib",
        .homepage = null,
    };

    // Validate package
    try PackageValidator.validate(metadata);

    // Version compatibility
    const v1_1_0 = SemanticVersion{ .major = 1, .minor = 1, .patch = 0 };
    try testing.expect(v1_1_0.isCompatible(metadata.version));

    // Public API usage
    const result = PublicAPI.process(5);
    try testing.expectEqual(@as(i32, 10), result);

    // License check
    const license = License.MIT;
    try testing.expect(license.requiresAttribution());
}
```

### See Also

- Recipe 10.1: Making a Hierarchical Package of Modules
- Recipe 10.9: Adding Directories to the Build Path
- Recipe 1.3: Testing Strategy
- Recipe 9.11: Using Comptime to Control Instance Creation

---

## Recipe 16.1: Basic build.zig setup {#recipe-16-1}

**Tags:** allocators, build-system, concurrency, http, memory, networking, resource-cleanup, testing, threading
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/16-zig-build-system/recipe_16_1.zig`

### Problem

You need to create a build configuration for your Zig project that handles compilation, optimization levels, and target platforms.

### Solution

Create a `build.zig` file that uses the modern Zig build system API:

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    // Standard optimization options
    const optimize = b.standardOptimizeOption(.{});

    // Standard target options
    const target = b.standardTargetOptions(.{});

    // Create an executable
    const exe = b.addExecutable(.{
        .name = "hello",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    // Install the executable
    b.installArtifact(exe);

    // Create a run step
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());

    // Allow passing arguments
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    // Create the run step
    const run_step = b.step("run", "Run the application");
    run_step.dependOn(&run_cmd.step);
}
```

Build and run your project:

```bash
zig build                    # Build with default settings (Debug)
zig build -Doptimize=ReleaseFast  # Build optimized
zig build run                # Build and run
zig build run -- arg1 arg2   # Pass arguments
```

### Discussion

### The Build Function

Every `build.zig` file exports a `build` function that receives a `*std.Build` parameter. This is the entry point for the build system.

### Optimization Options

The `standardOptimizeOption` method provides four build modes:

**Debug** (default)
- Fast compilation
- Safety checks enabled
- Slow runtime performance
- Useful for development

**ReleaseSafe**
- Optimized code
- Safety checks enabled
- Good balance for production

**ReleaseFast**
- Maximum performance
- Safety checks disabled
- Use when performance is critical

**ReleaseSmall**
- Optimized for binary size
- Safety checks disabled
- Useful for embedded systems

### Target Options

The `standardTargetOptions` method allows cross-compilation:

```bash
# Build for Linux x86_64
zig build -Dtarget=x86_64-linux

# Build for Windows
zig build -Dtarget=x86_64-windows

# Build for ARM
zig build -Dtarget=aarch64-linux
```

### Creating Executables

The `addExecutable` method creates an executable artifact:

```zig
const exe = b.addExecutable(.{
    .name = "myapp",              // Output name
    .root_module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    }),
});
```

### Installing Artifacts

`installArtifact` copies the built executable to `zig-out/bin/`:

```zig
b.installArtifact(exe);
```

This runs automatically when you execute `zig build`.

### Run Steps

Create a run step to execute your program:

```zig
const run_cmd = b.addRunArtifact(exe);
run_cmd.step.dependOn(b.getInstallStep());

// Allow command-line arguments
if (b.args) |args| {
    run_cmd.addArgs(args);
}

const run_step = b.step("run", "Run the application");
run_step.dependOn(&run_cmd.step);
```

Now you can use `zig build run`.

### Build Modes in Detail

**Debug Mode:**
```bash
zig build
# - Safety checks: ON
# - Optimizations: OFF
# - Assertions: ON
# - Best for: Development
```

**ReleaseSafe Mode:**
```bash
zig build -Doptimize=ReleaseSafe
# - Safety checks: ON
# - Optimizations: ON
# - Assertions: OFF
# - Best for: Production with safety
```

**ReleaseFast Mode:**
```bash
zig build -Doptimize=ReleaseFast
# - Safety checks: OFF
# - Optimizations: MAXIMUM
# - Assertions: OFF
# - Best for: Performance-critical production
```

**ReleaseSmall Mode:**
```bash
zig build -Doptimize=ReleaseSmall
# - Safety checks: OFF
# - Optimizations: SIZE
# - Assertions: OFF
# - Best for: Embedded systems, small binaries
```

### Common Build Commands

```bash
# List all build steps
zig build --help

# Clean build artifacts
rm -rf zig-out .zig-cache

# Verbose output
zig build --verbose

# Summary output
zig build --summary all
```

### Project Structure

A typical Zig project structure:

```
myproject/
├── build.zig           # Build configuration
├── build.zig.zon       # Dependencies (optional)
├── src/
│   └── main.zig       # Main source file
└── zig-out/           # Build output (created by build)
    └── bin/
        └── myapp      # Executable
```

### Best Practices

1. **Use `b.path()` for file paths** - Ensures correct resolution
2. **Add standard options** - Makes your build flexible
3. **Create run steps** - Makes testing easier
4. **Install artifacts** - Ensures outputs go to standard locations
5. **Handle arguments** - Allow passing args to your program
6. **Document custom steps** - Use descriptive step names

### Advanced Configuration

You can add custom build options:

```zig
const enable_logging = b.option(bool, "logging", "Enable logging") orelse false;
const max_threads = b.option(u32, "threads", "Maximum threads") orelse 4;
```

Use them:

```bash
zig build -Dlogging=true -Dthreads=8
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// This file demonstrates build system concepts through testable code
// The actual build.zig files are in the recipe_16_1/ subdirectory

// ANCHOR: build_concepts
// Build system concepts demonstrated through types

pub const BuildMode = enum {
    Debug,
    ReleaseSafe,
    ReleaseFast,
    ReleaseSmall,

    pub fn description(self: BuildMode) []const u8 {
        return switch (self) {
            .Debug => "Fast compilation, safety checks, slow runtime",
            .ReleaseSafe => "Optimized with safety checks",
            .ReleaseFast => "Maximum performance, no safety checks",
            .ReleaseSmall => "Optimized for size",
        };
    }
};

test "build modes" {
    try testing.expect(std.mem.eql(u8, BuildMode.Debug.description(), "Fast compilation, safety checks, slow runtime"));
    try testing.expect(std.mem.eql(u8, BuildMode.ReleaseFast.description(), "Maximum performance, no safety checks"));
}
// ANCHOR_END: build_concepts

// ANCHOR: target_triple
// Understanding target triples
pub const TargetTriple = struct {
    arch: []const u8,
    os: []const u8,
    abi: []const u8,

    pub fn format(self: TargetTriple, allocator: std.mem.Allocator) ![]const u8 {
        return std.fmt.allocPrint(allocator, "{s}-{s}-{s}", .{ self.arch, self.os, self.abi });
    }
};

test "target triple formatting" {
    const target = TargetTriple{
        .arch = "x86_64",
        .os = "linux",
        .abi = "gnu",
    };

    const formatted = try target.format(testing.allocator);
    defer testing.allocator.free(formatted);

    try testing.expect(std.mem.eql(u8, formatted, "x86_64-linux-gnu"));
}
// ANCHOR_END: target_triple

// ANCHOR: build_options
// Simulating build options pattern
pub const BuildOptions = struct {
    version: []const u8,
    enable_logging: bool,
    max_connections: u32,

    pub fn init(version: []const u8, enable_logging: bool, max_connections: u32) BuildOptions {
        return .{
            .version = version,
            .enable_logging = enable_logging,
            .max_connections = max_connections,
        };
    }
};

test "build options" {
    const options = BuildOptions.init("1.0.0", true, 100);
    try testing.expect(std.mem.eql(u8, options.version, "1.0.0"));
    try testing.expectEqual(true, options.enable_logging);
    try testing.expectEqual(@as(u32, 100), options.max_connections);
}
// ANCHOR_END: build_options

// ANCHOR: artifact_types
// Different artifact types in the build system
pub const ArtifactType = enum {
    Executable,
    StaticLibrary,
    DynamicLibrary,
    Object,
    Test,

    pub fn extension(self: ArtifactType, os: std.Target.Os.Tag) []const u8 {
        return switch (self) {
            .Executable => if (os == .windows) ".exe" else "",
            .StaticLibrary => if (os == .windows) ".lib" else ".a",
            .DynamicLibrary => if (os == .windows) ".dll" else if (os == .macos) ".dylib" else ".so",
            .Object => ".o",
            .Test => "",
        };
    }
};

test "artifact extensions" {
    try testing.expect(std.mem.eql(u8, ArtifactType.Executable.extension(.linux), ""));
    try testing.expect(std.mem.eql(u8, ArtifactType.Executable.extension(.windows), ".exe"));
    try testing.expect(std.mem.eql(u8, ArtifactType.StaticLibrary.extension(.linux), ".a"));
    try testing.expect(std.mem.eql(u8, ArtifactType.DynamicLibrary.extension(.macos), ".dylib"));
}
// ANCHOR_END: artifact_types

// ANCHOR: dependency_resolution
// Simulating dependency resolution
pub const Dependency = struct {
    name: []const u8,
    version: []const u8,
    url: ?[]const u8,

    pub fn init(name: []const u8, version: []const u8, url: ?[]const u8) Dependency {
        return .{
            .name = name,
            .version = version,
            .url = url,
        };
    }

    pub fn isLocal(self: Dependency) bool {
        return self.url == null;
    }
};

test "dependency handling" {
    const local_dep = Dependency.init("mylib", "1.0.0", null);
    const remote_dep = Dependency.init("thirdparty", "2.1.0", "https://example.com/lib.git");

    try testing.expect(local_dep.isLocal());
    try testing.expect(!remote_dep.isLocal());
}
// ANCHOR_END: dependency_resolution

// ANCHOR: build_steps
// Build step management
pub const BuildStep = struct {
    name: []const u8,
    description: []const u8,
    dependencies: []const []const u8,

    pub fn init(name: []const u8, description: []const u8, dependencies: []const []const u8) BuildStep {
        return .{
            .name = name,
            .description = description,
            .dependencies = dependencies,
        };
    }

    pub fn hasDependency(self: BuildStep, dep_name: []const u8) bool {
        for (self.dependencies) |dep| {
            if (std.mem.eql(u8, dep, dep_name)) return true;
        }
        return false;
    }
};

test "build step dependencies" {
    const deps = [_][]const u8{ "compile", "link" };
    const step = BuildStep.init("run", "Run the application", &deps);

    try testing.expect(step.hasDependency("compile"));
    try testing.expect(step.hasDependency("link"));
    try testing.expect(!step.hasDependency("test"));
}
// ANCHOR_END: build_steps

// ANCHOR: install_directory
// Install directory structure
pub const InstallDir = enum {
    Prefix,
    Bin,
    Lib,
    Include,
    Share,

    pub fn path(self: InstallDir, prefix: []const u8, allocator: std.mem.Allocator) ![]const u8 {
        const subdir = switch (self) {
            .Prefix => "",
            .Bin => "bin",
            .Lib => "lib",
            .Include => "include",
            .Share => "share",
        };

        if (subdir.len == 0) {
            return try allocator.dupe(u8, prefix);
        }

        return try std.fs.path.join(allocator, &[_][]const u8{ prefix, subdir });
    }
};

test "install directories" {
    const prefix = "/usr/local";

    const bin_path = try InstallDir.Bin.path(prefix, testing.allocator);
    defer testing.allocator.free(bin_path);
    try testing.expect(std.mem.eql(u8, bin_path, "/usr/local/bin"));

    const lib_path = try InstallDir.Lib.path(prefix, testing.allocator);
    defer testing.allocator.free(lib_path);
    try testing.expect(std.mem.eql(u8, lib_path, "/usr/local/lib"));
}
// ANCHOR_END: install_directory

// ANCHOR: module_system
// Module system concepts
pub const Module = struct {
    name: []const u8,
    root_file: []const u8,
    dependencies: []const []const u8,

    pub fn init(name: []const u8, root_file: []const u8, dependencies: []const []const u8) Module {
        return .{
            .name = name,
            .root_file = root_file,
            .dependencies = dependencies,
        };
    }

    pub fn dependsOn(self: Module, module_name: []const u8) bool {
        for (self.dependencies) |dep| {
            if (std.mem.eql(u8, dep, module_name)) return true;
        }
        return false;
    }
};

test "module dependencies" {
    const deps = [_][]const u8{ "std", "network" };
    const mod = Module.init("app", "src/main.zig", &deps);

    try testing.expect(mod.dependsOn("std"));
    try testing.expect(mod.dependsOn("network"));
    try testing.expect(!mod.dependsOn("database"));
}
// ANCHOR_END: module_system
```

### See Also

- Recipe 16.2: Multiple Executables and Libraries
- Recipe 16.5: Cross
- Recipe 16.6: Build Options and Configurations

---

## Recipe 16.2: Multiple executables and libraries {#recipe-16-2}

**Tags:** allocators, build-system, memory, resource-cleanup, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/16-zig-build-system/recipe_16_2.zig`

### Problem

You need to build multiple executables and libraries in a single project, with some executables depending on the libraries.

### Solution

Configure multiple artifacts in your `build.zig`:

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    // Build a library
    const lib = b.addStaticLibrary(.{
        .name = "mylib",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lib.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    b.installArtifact(lib);

    // Build first executable that uses the library
    const exe1 = b.addExecutable(.{
        .name = "app1",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/app1.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    exe1.root_module.linkLibrary(lib);
    b.installArtifact(exe1);

    // Build second executable
    const exe2 = b.addExecutable(.{
        .name = "app2",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/app2.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    exe2.root_module.linkLibrary(lib);
    b.installArtifact(exe2);

    // Create run steps for each executable
    const run_app1 = b.addRunArtifact(exe1);
    const run_app2 = b.addRunArtifact(exe2);

    const run_app1_step = b.step("run-app1", "Run application 1");
    run_app1_step.dependOn(&run_app1.step);

    const run_app2_step = b.step("run-app2", "Run application 2");
    run_app2_step.dependOn(&run_app2.step);

    // Build a shared library
    const shared_lib = b.addSharedLibrary(.{
        .name = "shared",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/shared.zig"),
            .target = target,
            .optimize = optimize,
        }),
        .version = .{ .major = 1, .minor = 0, .patch = 0 },
    });
    b.installArtifact(shared_lib);
}
```

Build everything:

```bash
zig build                    # Build all artifacts
zig build run-app1           # Run first application
zig build run-app2           # Run second application
```

### Discussion

### Building Static Libraries

Static libraries are linked at compile time:

```zig
const lib = b.addStaticLibrary(.{
    .name = "mylib",
    .root_module = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    }),
});
b.installArtifact(lib);
```

Output: `zig-out/lib/libmylib.a` (Linux/macOS) or `mylib.lib` (Windows)

### Building Shared Libraries

Shared libraries are loaded at runtime:

```zig
const shared_lib = b.addSharedLibrary(.{
    .name = "shared",
    .root_module = b.createModule(.{
        .root_source_file = b.path("src/shared.zig"),
        .target = target,
        .optimize = optimize,
    }),
    .version = .{ .major = 1, .minor = 0, .patch = 0 },
});
b.installArtifact(shared_lib);
```

Output: `libshared.so.1.0.0` (Linux), `libshared.1.0.0.dylib` (macOS), or `shared.dll` (Windows)

### Linking Against Libraries

Executables can link against your libraries:

```zig
const exe = b.addExecutable(.{
    .name = "app",
    .root_module = b.createModule(.{
        .root_source_file = b.path("src/app.zig"),
        .target = target,
        .optimize = optimize,
    }),
});
exe.root_module.linkLibrary(lib);  // Link against library
b.installArtifact(exe);
```

In your source code, import the library:

```zig
const mylib = @import("mylib");

pub fn main() !void {
    const result = mylib.add(10, 20);
    std.debug.print("Result: {d}\n", .{result});
}
```

### Multiple Executables

Build several executables from different source files:

```zig
const exe1 = b.addExecutable(.{
    .name = "app1",
    .root_module = b.createModule(.{
        .root_source_file = b.path("src/app1.zig"),
        .target = target,
        .optimize = optimize,
    }),
});

const exe2 = b.addExecutable(.{
    .name = "app2",
    .root_module = b.createModule(.{
        .root_source_file = b.path("src/app2.zig"),
        .target = target,
        .optimize = optimize,
    }),
});

b.installArtifact(exe1);
b.installArtifact(exe2);
```

### Custom Run Steps

Create named run steps for each executable:

```zig
const run_app1 = b.addRunArtifact(exe1);
const run_app1_step = b.step("run-app1", "Run application 1");
run_app1_step.dependOn(&run_app1.step);

const run_app2 = b.addRunArtifact(exe2);
const run_app2_step = b.step("run-app2", "Run application 2");
run_app2_step.dependOn(&run_app2.step);
```

Usage:

```bash
zig build run-app1
zig build run-app2
```

### Library Versioning

Specify semantic versioning for shared libraries:

```zig
.version = .{ .major = 1, .minor = 2, .patch = 3 }
```

This creates proper symlinks on Unix systems:
- `libmylib.so.1.2.3` (actual file)
- `libmylib.so.1` → `libmylib.so.1.2.3`
- `libmylib.so` → `libmylib.so.1`

### Organizing Multi-Artifact Projects

```
myproject/
├── build.zig
├── src/
│   ├── lib.zig          # Static library
│   ├── shared.zig       # Shared library
│   ├── app1.zig         # First executable
│   └── app2.zig         # Second executable
└── zig-out/
    ├── bin/
    │   ├── app1
    │   └── app2
    └── lib/
        ├── libmylib.a
        └── libshared.so
```

### Library Source Code

A library typically exports public functions:

```zig
// src/lib.zig
const std = @import("std");

pub fn add(a: i32, b: i32) i32 {
    return a + b;
}

pub fn multiply(a: i32, b: i32) i32 {
    return a * b;
}

test "library functions" {
    const testing = std.testing;
    try testing.expectEqual(@as(i32, 5), add(2, 3));
}
```

### Executable Using Library

```zig
// src/app.zig
const std = @import("std");
const mylib = @import("mylib");

pub fn main() !void {
    const result = mylib.add(10, 20);
    std.debug.print("10 + 20 = {d}\n", .{result});
}
```

### Static vs Dynamic Linking

**Static Linking:**
- Library code embedded in executable
- Larger executable size
- No runtime dependencies
- Single file to distribute

**Dynamic Linking:**
- Smaller executable size
- Shared library must be present at runtime
- Multiple programs can share one library
- Library can be updated independently

### Installing to Custom Directories

Install artifacts to specific locations:

```zig
const lib_install = b.addInstallArtifact(lib, .{
    .dest_dir = .{ .override = .{ .custom = "mylibs" } },
});
```

### Building Object Files

Sometimes you need just object files:

```zig
const obj = b.addObject(.{
    .name = "myobj",
    .root_module = b.createModule(.{
        .root_source_file = b.path("src/obj.zig"),
        .target = target,
        .optimize = optimize,
    }),
});
b.installArtifact(obj);
```

### Conditional Artifact Building

Build different artifacts based on configuration:

```zig
const build_server = b.option(bool, "server", "Build server") orelse true;
const build_client = b.option(bool, "client", "Build client") orelse true;

if (build_server) {
    const server = b.addExecutable(.{
        .name = "server",
        // ...
    });
    b.installArtifact(server);
}

if (build_client) {
    const client = b.addExecutable(.{
        .name = "client",
        // ...
    });
    b.installArtifact(client);
}
```

Usage:

```bash
zig build -Dserver=true -Dclient=false   # Build only server
zig build -Dserver=false -Dclient=true   # Build only client
```

### Best Practices

1. **Organize by artifact type** - Keep executables, libraries separate
2. **Use meaningful names** - Clear artifact and step names
3. **Version shared libraries** - Always specify versions
4. **Create run steps** - One for each executable
5. **Document dependencies** - Comment which exe uses which lib
6. **Test libraries** - Include tests in library source files

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// This file demonstrates building multiple artifacts through testable code
// The actual build.zig is in recipe_16_2/ subdirectory

// ANCHOR: library_types
// Different types of libraries
pub const LibraryType = enum {
    Static,
    Dynamic,
    Object,

    pub fn fileName(self: LibraryType, name: []const u8, os: std.Target.Os.Tag, allocator: std.mem.Allocator) ![]const u8 {
        const prefix = if (os != .windows) "lib" else "";
        const ext = switch (self) {
            .Static => if (os == .windows) ".lib" else ".a",
            .Dynamic => if (os == .windows) ".dll" else if (os == .macos) ".dylib" else ".so",
            .Object => ".o",
        };
        return try std.fmt.allocPrint(allocator, "{s}{s}{s}", .{ prefix, name, ext });
    }
};

test "library file names" {
    const name = try LibraryType.Static.fileName("mylib", .linux, testing.allocator);
    defer testing.allocator.free(name);
    try testing.expect(std.mem.eql(u8, name, "libmylib.a"));

    const dyn_name = try LibraryType.Dynamic.fileName("mylib", .macos, testing.allocator);
    defer testing.allocator.free(dyn_name);
    try testing.expect(std.mem.eql(u8, dyn_name, "libmylib.dylib"));
}
// ANCHOR_END: library_types

// ANCHOR: executable_configuration
// Executable configuration
pub const ExecutableConfig = struct {
    name: []const u8,
    source_file: []const u8,
    link_libc: bool,
    dependencies: []const []const u8,

    pub fn init(name: []const u8, source_file: []const u8) ExecutableConfig {
        return .{
            .name = name,
            .source_file = source_file,
            .link_libc = false,
            .dependencies = &[_][]const u8{},
        };
    }

    pub fn withLibc(self: ExecutableConfig) ExecutableConfig {
        var config = self;
        config.link_libc = true;
        return config;
    }

    pub fn hasDependency(self: ExecutableConfig, dep: []const u8) bool {
        for (self.dependencies) |d| {
            if (std.mem.eql(u8, d, dep)) return true;
        }
        return false;
    }
};

test "executable configuration" {
    const config = ExecutableConfig.init("myapp", "src/main.zig").withLibc();
    try testing.expect(std.mem.eql(u8, config.name, "myapp"));
    try testing.expectEqual(true, config.link_libc);
}
// ANCHOR_END: executable_configuration

// ANCHOR: artifact_linking
// Artifact linking relationships
pub const LinkageType = enum {
    Static,
    Dynamic,

    pub fn description(self: LinkageType) []const u8 {
        return switch (self) {
            .Static => "Statically linked at compile time",
            .Dynamic => "Dynamically linked at runtime",
        };
    }
};

pub const LinkedArtifact = struct {
    name: []const u8,
    linkage: LinkageType,

    pub fn init(name: []const u8, linkage: LinkageType) LinkedArtifact {
        return .{ .name = name, .linkage = linkage };
    }

    pub fn isStatic(self: LinkedArtifact) bool {
        return self.linkage == .Static;
    }
};

test "artifact linking" {
    const artifact = LinkedArtifact.init("mylib", .Static);
    try testing.expect(artifact.isStatic());
    try testing.expect(std.mem.eql(u8, artifact.name, "mylib"));
}
// ANCHOR_END: artifact_linking

// ANCHOR: install_artifacts
// Install artifact management
pub const InstallArtifact = struct {
    name: []const u8,
    destination: []const u8,
    artifact_type: enum { Executable, Library, Header },

    pub fn init(name: []const u8, destination: []const u8, artifact_type: @TypeOf(artifact_type)) InstallArtifact {
        return .{
            .name = name,
            .destination = destination,
            .artifact_type = artifact_type,
        };
    }

    pub fn fullPath(self: InstallArtifact, prefix: []const u8, allocator: std.mem.Allocator) ![]const u8 {
        return try std.fs.path.join(allocator, &[_][]const u8{ prefix, self.destination, self.name });
    }
};

test "install artifact paths" {
    const artifact = InstallArtifact.init("myapp", "bin", .Executable);
    const path = try artifact.fullPath("/usr/local", testing.allocator);
    defer testing.allocator.free(path);
    try testing.expect(std.mem.eql(u8, path, "/usr/local/bin/myapp"));
}
// ANCHOR_END: install_artifacts

// ANCHOR: version_management
// Library versioning
pub const LibraryVersion = struct {
    major: u32,
    minor: u32,
    patch: u32,

    pub fn init(major: u32, minor: u32, patch: u32) LibraryVersion {
        return .{ .major = major, .minor = minor, .patch = patch };
    }

    pub fn format(self: LibraryVersion, allocator: std.mem.Allocator) ![]const u8 {
        return try std.fmt.allocPrint(allocator, "{d}.{d}.{d}", .{ self.major, self.minor, self.patch });
    }

    pub fn isCompatible(self: LibraryVersion, required: LibraryVersion) bool {
        if (self.major != required.major) return false;
        if (self.minor < required.minor) return false;
        return true;
    }
};

test "library versioning" {
    const version = LibraryVersion.init(1, 2, 3);
    const version_str = try version.format(testing.allocator);
    defer testing.allocator.free(version_str);
    try testing.expect(std.mem.eql(u8, version_str, "1.2.3"));

    const required = LibraryVersion.init(1, 1, 0);
    try testing.expect(version.isCompatible(required));

    const incompatible = LibraryVersion.init(2, 0, 0);
    try testing.expect(!version.isCompatible(incompatible));
}
// ANCHOR_END: version_management

// ANCHOR: run_steps
// Run step configuration
pub const RunStep = struct {
    artifact_name: []const u8,
    args: []const []const u8,
    cwd: ?[]const u8,

    pub fn init(artifact_name: []const u8) RunStep {
        return .{
            .artifact_name = artifact_name,
            .args = &[_][]const u8{},
            .cwd = null,
        };
    }

    pub fn withArgs(self: RunStep, args: []const []const u8) RunStep {
        var step = self;
        step.args = args;
        return step;
    }

    pub fn hasArgs(self: RunStep) bool {
        return self.args.len > 0;
    }
};

test "run step configuration" {
    const args = [_][]const u8{ "--verbose", "--debug" };
    const step = RunStep.init("myapp").withArgs(&args);
    try testing.expect(step.hasArgs());
    try testing.expectEqual(@as(usize, 2), step.args.len);
}
// ANCHOR_END: run_steps

// ANCHOR: multi_target_build
// Multi-target build configuration
pub const TargetConfig = struct {
    arch: []const u8,
    os: []const u8,
    abi: []const u8,

    pub fn init(arch: []const u8, os: []const u8, abi: []const u8) TargetConfig {
        return .{ .arch = arch, .os = os, .abi = abi };
    }

    pub fn triple(self: TargetConfig, allocator: std.mem.Allocator) ![]const u8 {
        return try std.fmt.allocPrint(allocator, "{s}-{s}-{s}", .{ self.arch, self.os, self.abi });
    }

    pub fn isNative(self: TargetConfig) bool {
        const builtin = @import("builtin");
        const native_arch = @tagName(builtin.cpu.arch);
        const native_os = @tagName(builtin.os.tag);
        return std.mem.eql(u8, self.arch, native_arch) and std.mem.eql(u8, self.os, native_os);
    }
};

test "target configuration" {
    const target = TargetConfig.init("x86_64", "linux", "gnu");
    const triple = try target.triple(testing.allocator);
    defer testing.allocator.free(triple);
    try testing.expect(std.mem.eql(u8, triple, "x86_64-linux-gnu"));
}
// ANCHOR_END: multi_target_build

// ANCHOR: build_dependencies
// Build step dependencies
pub const BuildDependency = struct {
    name: []const u8,
    depends_on: []const []const u8,

    pub fn init(name: []const u8, depends_on: []const []const u8) BuildDependency {
        return .{ .name = name, .depends_on = depends_on };
    }

    pub fn hasDependency(self: BuildDependency, dep_name: []const u8) bool {
        for (self.depends_on) |dep| {
            if (std.mem.eql(u8, dep, dep_name)) return true;
        }
        return false;
    }

    pub fn dependencyCount(self: BuildDependency) usize {
        return self.depends_on.len;
    }
};

test "build dependencies" {
    const deps = [_][]const u8{ "compile", "link", "install" };
    const build_dep = BuildDependency.init("run", &deps);
    try testing.expect(build_dep.hasDependency("compile"));
    try testing.expectEqual(@as(usize, 3), build_dep.dependencyCount());
}
// ANCHOR_END: build_dependencies
```

### See Also

- Recipe 16.1: Basic build.zig Setup
- Recipe 16.3: Managing Dependencies
- Recipe 16.4: Custom Build Steps

---

## Recipe 16.3: Managing dependencies {#recipe-16-3}

**Tags:** build-system, c-interop, error-handling, http, networking, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/16-zig-build-system/recipe_16_3.zig`

### Problem

You need to use external libraries in your project and want to manage dependencies properly with Zig's package manager.

### Solution

Zig uses `build.zig.zon` files to declare dependencies. Create a manifest file in your project root:

```zig
.{
    .name = "myproject",
    .version = "0.1.0",
    .minimum_zig_version = "0.15.0",

    .dependencies = .{
        .@"my-dependency" = .{
            .url = "https://github.com/example/my-dependency/archive/main.tar.gz",
            .hash = "12200000000000000000000000000000000000000000000000000000000000000000",
        },
    },

    .paths = .{
        "build.zig",
        "build.zig.zon",
        "src",
    },
}
```

Then reference the dependency in your `build.zig`:

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    // Get a dependency from build.zig.zon
    const my_dep = b.dependency("my-dependency", .{
        .target = target,
        .optimize = optimize,
    });

    // Create executable
    const exe = b.addExecutable(.{
        .name = "myapp",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    // Import the dependency as a module
    exe.root_module.addImport("my-dependency", my_dep.module("my-dependency"));

    b.installArtifact(exe);
}
```

### Discussion

Zig's dependency management system is built directly into the build system. Dependencies are declared in `build.zig.zon` files using a structured format.

### Dependency Information

Each dependency needs basic metadata:

```zig
// Dependency information structure
pub const DependencyInfo = struct {
    name: []const u8,
    version: []const u8,
    url: []const u8,
    hash: []const u8,

    pub fn init(name: []const u8, version: []const u8, url: []const u8, hash: []const u8) DependencyInfo {
        return .{
            .name = name,
            .version = version,
            .url = url,
            .hash = hash,
        };
    }

    pub fn isValid(self: DependencyInfo) bool {
        return self.name.len > 0 and self.hash.len == 68; // SHA256 hash length with prefix
    }
};

test "dependency info" {
    const dep = DependencyInfo.init(
        "mylib",
        "1.0.0",
        "https://example.com/mylib.tar.gz",
        "12200000000000000000000000000000000000000000000000000000000000000000",
    );
    try testing.expect(dep.isValid());
    try testing.expect(std.mem.eql(u8, dep.name, "mylib"));
}
```

The hash field is critical - it's a SHA256 hash with a "1220" prefix (multihash format) that ensures dependency integrity. If the downloaded package doesn't match the hash, the build will fail.

### Version Constraints

You can specify version requirements:

```zig
// Version constraint handling
pub const VersionConstraint = struct {
    minimum: []const u8,
    maximum: ?[]const u8,

    pub fn init(minimum: []const u8, maximum: ?[]const u8) VersionConstraint {
        return .{
            .minimum = minimum,
            .maximum = maximum,
        };
    }

    pub fn hasMaximum(self: VersionConstraint) bool {
        return self.maximum != null;
    }
};

test "version constraints" {
    const constraint = VersionConstraint.init("1.0.0", "2.0.0");
    try testing.expect(constraint.hasMaximum());
    try testing.expect(std.mem.eql(u8, constraint.minimum, "1.0.0"));
}
```

Version constraints help ensure compatibility. You can specify a minimum version, or both minimum and maximum for more control.

### Module Imports

Dependencies expose modules that you import into your code:

```zig
// Module import configuration
pub const ModuleImport = struct {
    name: []const u8,
    dependency_name: []const u8,

    pub fn init(name: []const u8, dependency_name: []const u8) ModuleImport {
        return .{
            .name = name,
            .dependency_name = dependency_name,
        };
    }

    pub fn matches(self: ModuleImport, dep_name: []const u8) bool {
        return std.mem.eql(u8, self.dependency_name, dep_name);
    }
};

test "module imports" {
    const import = ModuleImport.init("mylib", "my-dependency");
    try testing.expect(import.matches("my-dependency"));
    try testing.expect(!import.matches("other-dependency"));
}
```

The module name in your code can differ from the dependency name in `build.zig.zon`, giving you flexibility in how you organize imports.

### Dependency Graphs

Projects often have complex dependency relationships:

```zig
// Simple dependency graph representation
pub const DependencyNode = struct {
    name: []const u8,
    dependencies: []const []const u8,

    pub fn init(name: []const u8, dependencies: []const []const u8) DependencyNode {
        return .{
            .name = name,
            .dependencies = dependencies,
        };
    }

    pub fn dependsOn(self: DependencyNode, dep_name: []const u8) bool {
        for (self.dependencies) |dep| {
            if (std.mem.eql(u8, dep, dep_name)) return true;
        }
        return false;
    }

    pub fn dependencyCount(self: DependencyNode) usize {
        return self.dependencies.len;
    }
};

test "dependency graph" {
    const deps = [_][]const u8{ "dep1", "dep2", "dep3" };
    const node = DependencyNode.init("myproject", &deps);

    try testing.expectEqual(@as(usize, 3), node.dependencyCount());
    try testing.expect(node.dependsOn("dep1"));
    try testing.expect(!node.dependsOn("dep4"));
}
```

Understanding the dependency graph helps avoid circular dependencies and minimize build times.

### Local Dependencies

For development or monorepo setups, use path-based dependencies:

```zig
// Local dependency (path-based)
pub const LocalDependency = struct {
    name: []const u8,
    path: []const u8,

    pub fn init(name: []const u8, path: []const u8) LocalDependency {
        return .{
            .name = name,
            .path = path,
        };
    }

    pub fn isRelative(self: LocalDependency) bool {
        return !std.fs.path.isAbsolute(self.path);
    }
};

test "local dependencies" {
    const dep = LocalDependency.init("mylib", "../mylib");
    try testing.expect(dep.isRelative());

    const abs_dep = LocalDependency.init("other", "/usr/local/lib/other");
    try testing.expect(!abs_dep.isRelative());
}
```

Local dependencies are useful during development or when working with unpublished packages. They can be relative or absolute paths.

### Dependency Options

Pass build options to dependencies:

```zig
// Options passed to dependencies
pub const DependencyOptions = struct {
    optimize: std.builtin.OptimizeMode,
    target: ?[]const u8,
    features: []const []const u8,

    pub fn init(optimize: std.builtin.OptimizeMode) DependencyOptions {
        return .{
            .optimize = optimize,
            .target = null,
            .features = &[_][]const u8{},
        };
    }

    pub fn hasFeatures(self: DependencyOptions) bool {
        return self.features.len > 0;
    }

    pub fn hasTarget(self: DependencyOptions) bool {
        return self.target != null;
    }
};

test "dependency options" {
    const options = DependencyOptions.init(.ReleaseFast);
    try testing.expectEqual(std.builtin.OptimizeMode.ReleaseFast, options.optimize);
    try testing.expect(!options.hasFeatures());
    try testing.expect(!options.hasTarget());
}
```

This allows dependencies to be built with the same optimization level and target as your main project, or with different settings if needed.

### Hash Verification

Zig verifies package integrity using cryptographic hashes:

```zig
// Hash verification for dependencies
pub const DependencyHash = struct {
    algorithm: []const u8,
    value: []const u8,

    pub fn init(algorithm: []const u8, value: []const u8) DependencyHash {
        return .{
            .algorithm = algorithm,
            .value = value,
        };
    }

    pub fn isSHA256(self: DependencyHash) bool {
        return std.mem.eql(u8, self.algorithm, "sha256");
    }

    pub fn isValid(self: DependencyHash) bool {
        if (self.isSHA256()) {
            // SHA256 hash with "1220" prefix is 68 characters
            return self.value.len == 68;
        }
        return false;
    }
};

test "hash verification" {
    const hash = DependencyHash.init("sha256", "12200000000000000000000000000000000000000000000000000000000000000000");
    try testing.expect(hash.isSHA256());
    try testing.expect(hash.isValid());
}
```

The hash format uses multihash encoding:
- "12" = SHA256 algorithm
- "20" = 32 bytes (hex-encoded as 64 characters)
- Total: 68 characters including prefix

If you need to get the hash for a new dependency, Zig will tell you the correct hash when you first try to fetch it with the wrong hash.

### Transitive Dependencies

Dependencies can have their own dependencies:

```zig
// Managing transitive dependencies
pub const DependencyTree = struct {
    root: []const u8,
    direct: []const []const u8,
    transitive: []const []const u8,

    pub fn init(root: []const u8, direct: []const []const u8, transitive: []const []const u8) DependencyTree {
        return .{
            .root = root,
            .direct = direct,
            .transitive = transitive,
        };
    }

    pub fn totalDependencies(self: DependencyTree) usize {
        return self.direct.len + self.transitive.len;
    }

    pub fn isDirect(self: DependencyTree, name: []const u8) bool {
        for (self.direct) |dep| {
            if (std.mem.eql(u8, dep, name)) return true;
        }
        return false;
    }
};

test "transitive dependencies" {
    const direct = [_][]const u8{ "dep1", "dep2" };
    const transitive = [_][]const u8{ "dep3", "dep4", "dep5" };
    const tree = DependencyTree.init("myproject", &direct, &transitive);

    try testing.expectEqual(@as(usize, 5), tree.totalDependencies());
    try testing.expect(tree.isDirect("dep1"));
    try testing.expect(!tree.isDirect("dep3"));
}
```

Zig handles transitive dependencies automatically. Your `build.zig.zon` only needs to list direct dependencies; their dependencies are resolved recursively.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// This file demonstrates dependency management concepts

// ANCHOR: dependency_info
// Dependency information structure
pub const DependencyInfo = struct {
    name: []const u8,
    version: []const u8,
    url: []const u8,
    hash: []const u8,

    pub fn init(name: []const u8, version: []const u8, url: []const u8, hash: []const u8) DependencyInfo {
        return .{
            .name = name,
            .version = version,
            .url = url,
            .hash = hash,
        };
    }

    pub fn isValid(self: DependencyInfo) bool {
        return self.name.len > 0 and self.hash.len == 68; // SHA256 hash length with prefix
    }
};

test "dependency info" {
    const dep = DependencyInfo.init(
        "mylib",
        "1.0.0",
        "https://example.com/mylib.tar.gz",
        "12200000000000000000000000000000000000000000000000000000000000000000",
    );
    try testing.expect(dep.isValid());
    try testing.expect(std.mem.eql(u8, dep.name, "mylib"));
}
// ANCHOR_END: dependency_info

// ANCHOR: version_constraint
// Version constraint handling
pub const VersionConstraint = struct {
    minimum: []const u8,
    maximum: ?[]const u8,

    pub fn init(minimum: []const u8, maximum: ?[]const u8) VersionConstraint {
        return .{
            .minimum = minimum,
            .maximum = maximum,
        };
    }

    pub fn hasMaximum(self: VersionConstraint) bool {
        return self.maximum != null;
    }
};

test "version constraints" {
    const constraint = VersionConstraint.init("1.0.0", "2.0.0");
    try testing.expect(constraint.hasMaximum());
    try testing.expect(std.mem.eql(u8, constraint.minimum, "1.0.0"));
}
// ANCHOR_END: version_constraint

// ANCHOR: module_import
// Module import configuration
pub const ModuleImport = struct {
    name: []const u8,
    dependency_name: []const u8,

    pub fn init(name: []const u8, dependency_name: []const u8) ModuleImport {
        return .{
            .name = name,
            .dependency_name = dependency_name,
        };
    }

    pub fn matches(self: ModuleImport, dep_name: []const u8) bool {
        return std.mem.eql(u8, self.dependency_name, dep_name);
    }
};

test "module imports" {
    const import = ModuleImport.init("mylib", "my-dependency");
    try testing.expect(import.matches("my-dependency"));
    try testing.expect(!import.matches("other-dependency"));
}
// ANCHOR_END: module_import

// ANCHOR: dependency_graph
// Simple dependency graph representation
pub const DependencyNode = struct {
    name: []const u8,
    dependencies: []const []const u8,

    pub fn init(name: []const u8, dependencies: []const []const u8) DependencyNode {
        return .{
            .name = name,
            .dependencies = dependencies,
        };
    }

    pub fn dependsOn(self: DependencyNode, dep_name: []const u8) bool {
        for (self.dependencies) |dep| {
            if (std.mem.eql(u8, dep, dep_name)) return true;
        }
        return false;
    }

    pub fn dependencyCount(self: DependencyNode) usize {
        return self.dependencies.len;
    }
};

test "dependency graph" {
    const deps = [_][]const u8{ "dep1", "dep2", "dep3" };
    const node = DependencyNode.init("myproject", &deps);

    try testing.expectEqual(@as(usize, 3), node.dependencyCount());
    try testing.expect(node.dependsOn("dep1"));
    try testing.expect(!node.dependsOn("dep4"));
}
// ANCHOR_END: dependency_graph

// ANCHOR: local_dependency
// Local dependency (path-based)
pub const LocalDependency = struct {
    name: []const u8,
    path: []const u8,

    pub fn init(name: []const u8, path: []const u8) LocalDependency {
        return .{
            .name = name,
            .path = path,
        };
    }

    pub fn isRelative(self: LocalDependency) bool {
        return !std.fs.path.isAbsolute(self.path);
    }
};

test "local dependencies" {
    const dep = LocalDependency.init("mylib", "../mylib");
    try testing.expect(dep.isRelative());

    const abs_dep = LocalDependency.init("other", "/usr/local/lib/other");
    try testing.expect(!abs_dep.isRelative());
}
// ANCHOR_END: local_dependency

// ANCHOR: dependency_options
// Options passed to dependencies
pub const DependencyOptions = struct {
    optimize: std.builtin.OptimizeMode,
    target: ?[]const u8,
    features: []const []const u8,

    pub fn init(optimize: std.builtin.OptimizeMode) DependencyOptions {
        return .{
            .optimize = optimize,
            .target = null,
            .features = &[_][]const u8{},
        };
    }

    pub fn hasFeatures(self: DependencyOptions) bool {
        return self.features.len > 0;
    }

    pub fn hasTarget(self: DependencyOptions) bool {
        return self.target != null;
    }
};

test "dependency options" {
    const options = DependencyOptions.init(.ReleaseFast);
    try testing.expectEqual(std.builtin.OptimizeMode.ReleaseFast, options.optimize);
    try testing.expect(!options.hasFeatures());
    try testing.expect(!options.hasTarget());
}
// ANCHOR_END: dependency_options

// ANCHOR: hash_verification
// Hash verification for dependencies
pub const DependencyHash = struct {
    algorithm: []const u8,
    value: []const u8,

    pub fn init(algorithm: []const u8, value: []const u8) DependencyHash {
        return .{
            .algorithm = algorithm,
            .value = value,
        };
    }

    pub fn isSHA256(self: DependencyHash) bool {
        return std.mem.eql(u8, self.algorithm, "sha256");
    }

    pub fn isValid(self: DependencyHash) bool {
        if (self.isSHA256()) {
            // SHA256 hash with "1220" prefix is 68 characters
            return self.value.len == 68;
        }
        return false;
    }
};

test "hash verification" {
    const hash = DependencyHash.init("sha256", "12200000000000000000000000000000000000000000000000000000000000000000");
    try testing.expect(hash.isSHA256());
    try testing.expect(hash.isValid());
}
// ANCHOR_END: hash_verification

// ANCHOR: transitive_dependencies
// Managing transitive dependencies
pub const DependencyTree = struct {
    root: []const u8,
    direct: []const []const u8,
    transitive: []const []const u8,

    pub fn init(root: []const u8, direct: []const []const u8, transitive: []const []const u8) DependencyTree {
        return .{
            .root = root,
            .direct = direct,
            .transitive = transitive,
        };
    }

    pub fn totalDependencies(self: DependencyTree) usize {
        return self.direct.len + self.transitive.len;
    }

    pub fn isDirect(self: DependencyTree, name: []const u8) bool {
        for (self.direct) |dep| {
            if (std.mem.eql(u8, dep, name)) return true;
        }
        return false;
    }
};

test "transitive dependencies" {
    const direct = [_][]const u8{ "dep1", "dep2" };
    const transitive = [_][]const u8{ "dep3", "dep4", "dep5" };
    const tree = DependencyTree.init("myproject", &direct, &transitive);

    try testing.expectEqual(@as(usize, 5), tree.totalDependencies());
    try testing.expect(tree.isDirect("dep1"));
    try testing.expect(!tree.isDirect("dep3"));
}
// ANCHOR_END: transitive_dependencies
```

### See Also

- Recipe 16.1: Basic build.zig setup
- Recipe 16.2: Multiple executables and libraries
- Recipe 16.4: Custom build steps
- Recipe 16.6: Build options and configurations

---

## Recipe 16.4: Custom build steps {#recipe-16-4}

**Tags:** build-system, c-interop, error-handling, json, parsing, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/16-zig-build-system/recipe_16_4.zig`

### Problem

You need to extend your build process with custom commands like code generation, formatting, running external tools, or creating complex build pipelines.

### Solution

Use Zig's build system API to create custom build steps. Here's a comprehensive example showing various custom steps:

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Create executable
    const exe = b.addExecutable(.{
        .name = "myapp",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    b.installArtifact(exe);

    // Custom run step with arguments
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());

    // Forward command line arguments
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the application");
    run_step.dependOn(&run_cmd.step);

    // Custom step: Run formatter
    const fmt_cmd = b.addSystemCommand(&[_][]const u8{
        "zig",
        "fmt",
        "src",
    });

    const fmt_step = b.step("fmt", "Format source code");
    fmt_step.dependOn(&fmt_cmd.step);

    // Custom step: Generate code
    const codegen_cmd = b.addSystemCommand(&[_][]const u8{
        "echo",
        "// Generated code",
    });

    const codegen_output = codegen_cmd.captureStdOut();
    const write_generated = b.addWriteFiles();
    _ = write_generated.addCopyFile(codegen_output, "generated.zig");

    const codegen_step = b.step("codegen", "Generate code");
    codegen_step.dependOn(&write_generated.step);

    // Custom step: Run tests
    const tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    const run_tests = b.addRunArtifact(tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_tests.step);

    // Custom step: Check compilation without building
    const check = b.addExecutable(.{
        .name = "check",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    const check_step = b.step("check", "Check compilation");
    check_step.dependOn(&check.step);

    // Custom composite step
    const all_step = b.step("all", "Run fmt, codegen, build, and test");
    all_step.dependOn(fmt_step);
    all_step.dependOn(codegen_step);
    all_step.dependOn(b.getInstallStep());
    all_step.dependOn(test_step);
}
```

### Discussion

Custom build steps let you extend the build process beyond compiling code. The build system provides APIs for running commands, generating files, and orchestrating complex workflows.

### Step Information

Track metadata about build steps:

```zig
// Information about a build step
pub const StepInfo = struct {
    name: []const u8,
    description: []const u8,
    is_default: bool,

    pub fn init(name: []const u8, description: []const u8, is_default: bool) StepInfo {
        return .{
            .name = name,
            .description = description,
            .is_default = is_default,
        };
    }

    pub fn isRunnable(self: StepInfo) bool {
        return self.name.len > 0;
    }
};

test "step info" {
    const step = StepInfo.init("codegen", "Generate code", false);
    try testing.expect(step.isRunnable());
    try testing.expect(!step.is_default);
    try testing.expect(std.mem.eql(u8, step.name, "codegen"));
}
```

Each step has a name, description, and configuration. Steps can be marked as default (run when no target specified) or optional.

### Running External Commands

Execute external programs during the build:

```zig
// Represents an external command to run
pub const CommandStep = struct {
    program: []const u8,
    args: []const []const u8,
    working_dir: ?[]const u8,

    pub fn init(program: []const u8, args: []const []const u8) CommandStep {
        return .{
            .program = program,
            .args = args,
            .working_dir = null,
        };
    }

    pub fn withWorkingDir(self: CommandStep, dir: []const u8) CommandStep {
        var result = self;
        result.working_dir = dir;
        return result;
    }

    pub fn argCount(self: CommandStep) usize {
        return self.args.len;
    }
};

test "command step" {
    const args = [_][]const u8{ "--version" };
    const cmd = CommandStep.init("zig", &args);

    try testing.expectEqual(@as(usize, 1), cmd.argCount());
    try testing.expect(std.mem.eql(u8, cmd.program, "zig"));
    try testing.expect(cmd.working_dir == null);

    const cmd_with_dir = cmd.withWorkingDir("/tmp");
    try testing.expect(cmd_with_dir.working_dir != null);
}
```

Use `b.addSystemCommand()` to run any external command. You can:
- Pass arguments as an array of strings
- Set the working directory
- Capture stdout/stderr
- Chain commands together

### File Generation

Generate source files during the build process:

```zig
// File generation step
pub const FileGenerationStep = struct {
    source_file: []const u8,
    output_file: []const u8,
    generator: []const u8,

    pub fn init(source: []const u8, output: []const u8, generator: []const u8) FileGenerationStep {
        return .{
            .source_file = source,
            .output_file = output,
            .generator = generator,
        };
    }

    pub fn hasSource(self: FileGenerationStep) bool {
        return self.source_file.len > 0;
    }

    pub fn hasOutput(self: FileGenerationStep) bool {
        return self.output_file.len > 0;
    }

    pub fn isValid(self: FileGenerationStep) bool {
        return self.hasSource() and self.hasOutput() and self.generator.len > 0;
    }
};

test "file generation" {
    const gen = FileGenerationStep.init("schema.json", "generated.zig", "codegen");

    try testing.expect(gen.isValid());
    try testing.expect(gen.hasSource());
    try testing.expect(gen.hasOutput());
    try testing.expect(std.mem.eql(u8, gen.output_file, "generated.zig"));
}
```

Code generation is common in Zig projects. You might generate:
- Bindings from C headers
- Code from schema files (JSON, Protobuf, etc.)
- Configuration constants from build-time data
- Documentation or API clients

### Step Dependencies

Create dependency relationships between steps:

```zig
// Dependency between build steps
pub const StepDependency = struct {
    dependent: []const u8,
    dependency: []const u8,

    pub fn init(dependent: []const u8, dependency: []const u8) StepDependency {
        return .{
            .dependent = dependent,
            .dependency = dependency,
        };
    }

    pub fn dependsOn(self: StepDependency, step_name: []const u8) bool {
        return std.mem.eql(u8, self.dependency, step_name);
    }
};

test "step dependencies" {
    const dep = StepDependency.init("build", "codegen");

    try testing.expect(dep.dependsOn("codegen"));
    try testing.expect(!dep.dependsOn("test"));
    try testing.expect(std.mem.eql(u8, dep.dependent, "build"));
}
```

Use `step.dependOn()` to ensure steps run in the correct order. For example, code generation must complete before compilation starts.

### Installation Steps

Control where artifacts are installed:

```zig
// Installation step configuration
pub const InstallStep = struct {
    artifact_name: []const u8,
    destination: []const u8,
    install_subdir: ?[]const u8,

    pub fn init(artifact: []const u8, destination: []const u8) InstallStep {
        return .{
            .artifact_name = artifact,
            .destination = destination,
            .install_subdir = null,
        };
    }

    pub fn withSubdir(self: InstallStep, subdir: []const u8) InstallStep {
        var result = self;
        result.install_subdir = subdir;
        return result;
    }

    pub fn hasSubdir(self: InstallStep) bool {
        return self.install_subdir != null;
    }
};

test "install step" {
    const install = InstallStep.init("myapp", "bin");

    try testing.expect(!install.hasSubdir());
    try testing.expect(std.mem.eql(u8, install.artifact_name, "myapp"));

    const with_sub = install.withSubdir("tools");
    try testing.expect(with_sub.hasSubdir());
}
```

Installation steps copy built artifacts to the output directory (typically `zig-out/`). You can customize:
- Destination directory (bin, lib, share, etc.)
- Subdirectories within destinations
- File permissions and names

### Run Steps

Create named run configurations:

```zig
// Run step configuration
pub const RunStep = struct {
    executable: []const u8,
    args: []const []const u8,
    description: []const u8,

    pub fn init(exe: []const u8, args: []const []const u8, desc: []const u8) RunStep {
        return .{
            .executable = exe,
            .args = args,
            .description = desc,
        };
    }

    pub fn hasArgs(self: RunStep) bool {
        return self.args.len > 0;
    }

    pub fn argCount(self: RunStep) usize {
        return self.args.len;
    }
};

test "run step" {
    const args = [_][]const u8{ "--help", "--version" };
    const run = RunStep.init("myapp", &args, "Run application");

    try testing.expect(run.hasArgs());
    try testing.expectEqual(@as(usize, 2), run.argCount());
    try testing.expect(std.mem.eql(u8, run.description, "Run application"));
}
```

Run steps execute built artifacts. Use them for:
- Running your application with specific arguments
- Running tests
- Benchmarking
- Development servers

### Check Steps

Add validation and linting:

```zig
// Check/lint step configuration
pub const CheckStep = struct {
    source_files: []const []const u8,
    checker: []const u8,
    fail_on_error: bool,

    pub fn init(files: []const []const u8, checker: []const u8) CheckStep {
        return .{
            .source_files = files,
            .checker = checker,
            .fail_on_error = true,
        };
    }

    pub fn allowErrors(self: CheckStep) CheckStep {
        var result = self;
        result.fail_on_error = false;
        return result;
    }

    pub fn fileCount(self: CheckStep) usize {
        return self.source_files.len;
    }
};

test "check step" {
    const files = [_][]const u8{ "main.zig", "lib.zig" };
    const check = CheckStep.init(&files, "zig fmt");

    try testing.expectEqual(@as(usize, 2), check.fileCount());
    try testing.expect(check.fail_on_error);

    const no_fail = check.allowErrors();
    try testing.expect(!no_fail.fail_on_error);
}
```

Check steps verify code quality without building. Common checks include:
- Formatting (`zig fmt --check`)
- Compilation checks without code generation
- Custom linters
- License header validation

### Custom Targets

Group multiple steps into named targets:

```zig
// Custom build target
pub const CustomTarget = struct {
    name: []const u8,
    steps: []const []const u8,
    description: []const u8,

    pub fn init(name: []const u8, steps: []const []const u8, desc: []const u8) CustomTarget {
        return .{
            .name = name,
            .steps = steps,
            .description = desc,
        };
    }

    pub fn stepCount(self: CustomTarget) usize {
        return self.steps.len;
    }

    pub fn hasStep(self: CustomTarget, step_name: []const u8) bool {
        for (self.steps) |step| {
            if (std.mem.eql(u8, step, step_name)) return true;
        }
        return false;
    }
};

test "custom target" {
    const steps = [_][]const u8{ "codegen", "compile", "test" };
    const target = CustomTarget.init("full-build", &steps, "Complete build pipeline");

    try testing.expectEqual(@as(usize, 3), target.stepCount());
    try testing.expect(target.hasStep("codegen"));
    try testing.expect(!target.hasStep("deploy"));
}
```

Custom targets orchestrate complex workflows. For example, a "release" target might:
1. Run all tests
2. Format code
3. Build optimized artifacts
4. Generate documentation
5. Create distribution archives

### Build Options

Add configurable options to your build:

```zig
// Build option configuration
pub const BuildOption = struct {
    name: []const u8,
    option_type: []const u8,
    default_value: ?[]const u8,
    description: []const u8,

    pub fn init(name: []const u8, opt_type: []const u8, desc: []const u8) BuildOption {
        return .{
            .name = name,
            .option_type = opt_type,
            .default_value = null,
            .description = desc,
        };
    }

    pub fn withDefault(self: BuildOption, default: []const u8) BuildOption {
        var result = self;
        result.default_value = default;
        return result;
    }

    pub fn hasDefault(self: BuildOption) bool {
        return self.default_value != null;
    }
};

test "build option" {
    const opt = BuildOption.init("enable-logging", "bool", "Enable debug logging");

    try testing.expect(!opt.hasDefault());
    try testing.expect(std.mem.eql(u8, opt.name, "enable-logging"));

    const with_default = opt.withDefault("true");
    try testing.expect(with_default.hasDefault());
}
```

Build options let users customize the build process:
```bash
zig build -Denable-logging=true
zig build -Dstrip=true -Doptimize=ReleaseFast
```

Options can be:
- Booleans (`bool`)
- Strings (`[]const u8`)
- Enums (custom types)
- Integers (`u32`, `i64`, etc.)

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// This file demonstrates custom build step concepts

// ANCHOR: step_info
// Information about a build step
pub const StepInfo = struct {
    name: []const u8,
    description: []const u8,
    is_default: bool,

    pub fn init(name: []const u8, description: []const u8, is_default: bool) StepInfo {
        return .{
            .name = name,
            .description = description,
            .is_default = is_default,
        };
    }

    pub fn isRunnable(self: StepInfo) bool {
        return self.name.len > 0;
    }
};

test "step info" {
    const step = StepInfo.init("codegen", "Generate code", false);
    try testing.expect(step.isRunnable());
    try testing.expect(!step.is_default);
    try testing.expect(std.mem.eql(u8, step.name, "codegen"));
}
// ANCHOR_END: step_info

// ANCHOR: command_step
// Represents an external command to run
pub const CommandStep = struct {
    program: []const u8,
    args: []const []const u8,
    working_dir: ?[]const u8,

    pub fn init(program: []const u8, args: []const []const u8) CommandStep {
        return .{
            .program = program,
            .args = args,
            .working_dir = null,
        };
    }

    pub fn withWorkingDir(self: CommandStep, dir: []const u8) CommandStep {
        var result = self;
        result.working_dir = dir;
        return result;
    }

    pub fn argCount(self: CommandStep) usize {
        return self.args.len;
    }
};

test "command step" {
    const args = [_][]const u8{ "--version" };
    const cmd = CommandStep.init("zig", &args);

    try testing.expectEqual(@as(usize, 1), cmd.argCount());
    try testing.expect(std.mem.eql(u8, cmd.program, "zig"));
    try testing.expect(cmd.working_dir == null);

    const cmd_with_dir = cmd.withWorkingDir("/tmp");
    try testing.expect(cmd_with_dir.working_dir != null);
}
// ANCHOR_END: command_step

// ANCHOR: file_generation
// File generation step
pub const FileGenerationStep = struct {
    source_file: []const u8,
    output_file: []const u8,
    generator: []const u8,

    pub fn init(source: []const u8, output: []const u8, generator: []const u8) FileGenerationStep {
        return .{
            .source_file = source,
            .output_file = output,
            .generator = generator,
        };
    }

    pub fn hasSource(self: FileGenerationStep) bool {
        return self.source_file.len > 0;
    }

    pub fn hasOutput(self: FileGenerationStep) bool {
        return self.output_file.len > 0;
    }

    pub fn isValid(self: FileGenerationStep) bool {
        return self.hasSource() and self.hasOutput() and self.generator.len > 0;
    }
};

test "file generation" {
    const gen = FileGenerationStep.init("schema.json", "generated.zig", "codegen");

    try testing.expect(gen.isValid());
    try testing.expect(gen.hasSource());
    try testing.expect(gen.hasOutput());
    try testing.expect(std.mem.eql(u8, gen.output_file, "generated.zig"));
}
// ANCHOR_END: file_generation

// ANCHOR: step_dependency
// Dependency between build steps
pub const StepDependency = struct {
    dependent: []const u8,
    dependency: []const u8,

    pub fn init(dependent: []const u8, dependency: []const u8) StepDependency {
        return .{
            .dependent = dependent,
            .dependency = dependency,
        };
    }

    pub fn dependsOn(self: StepDependency, step_name: []const u8) bool {
        return std.mem.eql(u8, self.dependency, step_name);
    }
};

test "step dependencies" {
    const dep = StepDependency.init("build", "codegen");

    try testing.expect(dep.dependsOn("codegen"));
    try testing.expect(!dep.dependsOn("test"));
    try testing.expect(std.mem.eql(u8, dep.dependent, "build"));
}
// ANCHOR_END: step_dependency

// ANCHOR: install_step
// Installation step configuration
pub const InstallStep = struct {
    artifact_name: []const u8,
    destination: []const u8,
    install_subdir: ?[]const u8,

    pub fn init(artifact: []const u8, destination: []const u8) InstallStep {
        return .{
            .artifact_name = artifact,
            .destination = destination,
            .install_subdir = null,
        };
    }

    pub fn withSubdir(self: InstallStep, subdir: []const u8) InstallStep {
        var result = self;
        result.install_subdir = subdir;
        return result;
    }

    pub fn hasSubdir(self: InstallStep) bool {
        return self.install_subdir != null;
    }
};

test "install step" {
    const install = InstallStep.init("myapp", "bin");

    try testing.expect(!install.hasSubdir());
    try testing.expect(std.mem.eql(u8, install.artifact_name, "myapp"));

    const with_sub = install.withSubdir("tools");
    try testing.expect(with_sub.hasSubdir());
}
// ANCHOR_END: install_step

// ANCHOR: run_step
// Run step configuration
pub const RunStep = struct {
    executable: []const u8,
    args: []const []const u8,
    description: []const u8,

    pub fn init(exe: []const u8, args: []const []const u8, desc: []const u8) RunStep {
        return .{
            .executable = exe,
            .args = args,
            .description = desc,
        };
    }

    pub fn hasArgs(self: RunStep) bool {
        return self.args.len > 0;
    }

    pub fn argCount(self: RunStep) usize {
        return self.args.len;
    }
};

test "run step" {
    const args = [_][]const u8{ "--help", "--version" };
    const run = RunStep.init("myapp", &args, "Run application");

    try testing.expect(run.hasArgs());
    try testing.expectEqual(@as(usize, 2), run.argCount());
    try testing.expect(std.mem.eql(u8, run.description, "Run application"));
}
// ANCHOR_END: run_step

// ANCHOR: check_step
// Check/lint step configuration
pub const CheckStep = struct {
    source_files: []const []const u8,
    checker: []const u8,
    fail_on_error: bool,

    pub fn init(files: []const []const u8, checker: []const u8) CheckStep {
        return .{
            .source_files = files,
            .checker = checker,
            .fail_on_error = true,
        };
    }

    pub fn allowErrors(self: CheckStep) CheckStep {
        var result = self;
        result.fail_on_error = false;
        return result;
    }

    pub fn fileCount(self: CheckStep) usize {
        return self.source_files.len;
    }
};

test "check step" {
    const files = [_][]const u8{ "main.zig", "lib.zig" };
    const check = CheckStep.init(&files, "zig fmt");

    try testing.expectEqual(@as(usize, 2), check.fileCount());
    try testing.expect(check.fail_on_error);

    const no_fail = check.allowErrors();
    try testing.expect(!no_fail.fail_on_error);
}
// ANCHOR_END: check_step

// ANCHOR: custom_target
// Custom build target
pub const CustomTarget = struct {
    name: []const u8,
    steps: []const []const u8,
    description: []const u8,

    pub fn init(name: []const u8, steps: []const []const u8, desc: []const u8) CustomTarget {
        return .{
            .name = name,
            .steps = steps,
            .description = desc,
        };
    }

    pub fn stepCount(self: CustomTarget) usize {
        return self.steps.len;
    }

    pub fn hasStep(self: CustomTarget, step_name: []const u8) bool {
        for (self.steps) |step| {
            if (std.mem.eql(u8, step, step_name)) return true;
        }
        return false;
    }
};

test "custom target" {
    const steps = [_][]const u8{ "codegen", "compile", "test" };
    const target = CustomTarget.init("full-build", &steps, "Complete build pipeline");

    try testing.expectEqual(@as(usize, 3), target.stepCount());
    try testing.expect(target.hasStep("codegen"));
    try testing.expect(!target.hasStep("deploy"));
}
// ANCHOR_END: custom_target

// ANCHOR: build_option
// Build option configuration
pub const BuildOption = struct {
    name: []const u8,
    option_type: []const u8,
    default_value: ?[]const u8,
    description: []const u8,

    pub fn init(name: []const u8, opt_type: []const u8, desc: []const u8) BuildOption {
        return .{
            .name = name,
            .option_type = opt_type,
            .default_value = null,
            .description = desc,
        };
    }

    pub fn withDefault(self: BuildOption, default: []const u8) BuildOption {
        var result = self;
        result.default_value = default;
        return result;
    }

    pub fn hasDefault(self: BuildOption) bool {
        return self.default_value != null;
    }
};

test "build option" {
    const opt = BuildOption.init("enable-logging", "bool", "Enable debug logging");

    try testing.expect(!opt.hasDefault());
    try testing.expect(std.mem.eql(u8, opt.name, "enable-logging"));

    const with_default = opt.withDefault("true");
    try testing.expect(with_default.hasDefault());
}
// ANCHOR_END: build_option
```

### See Also

- Recipe 16.1: Basic build.zig setup
- Recipe 16.2: Multiple executables and libraries
- Recipe 16.3: Managing dependencies
- Recipe 16.6: Build options and configurations
- Recipe 16.7: Testing in build system

---

## Recipe 16.5: Cross-compilation {#recipe-16-5}

**Tags:** allocators, atomics, build-system, concurrency, error-handling, freestanding, json, memory, parsing, pointers, resource-cleanup, testing, threading, webassembly
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/16-zig-build-system/recipe_16_5.zig`

### Problem

You need to build your Zig application for different operating systems and architectures without setting up multiple development environments.

### Solution

Zig makes cross-compilation trivial with built-in support for multiple targets. Configure your build.zig to support various platforms:

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    // Target and optimization from command line
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Create executable
    const exe = b.addExecutable(.{
        .name = "myapp",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    b.installArtifact(exe);

    // Predefined cross-compilation targets
    const targets = [_]std.Build.ResolvedTarget{
        b.resolveTargetQuery(.{
            .cpu_arch = .x86_64,
            .os_tag = .linux,
            .abi = .gnu,
        }),
        b.resolveTargetQuery(.{
            .cpu_arch = .x86_64,
            .os_tag = .windows,
            .abi = .gnu,
        }),
        b.resolveTargetQuery(.{
            .cpu_arch = .aarch64,
            .os_tag = .macos,
        }),
        b.resolveTargetQuery(.{
            .cpu_arch = .aarch64,
            .os_tag = .linux,
            .abi = .musl,
        }),
    };

    // Create build step for all targets
    const all_step = b.step("all-targets", "Build for all predefined targets");

    for (targets) |cross_target| {
        const cross_exe = b.addExecutable(.{
            .name = "myapp",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/main.zig"),
                .target = cross_target,
                .optimize = optimize,
            }),
        });

        const install_artifact = b.addInstallArtifact(cross_exe, .{});
        all_step.dependOn(&install_artifact.step);
    }

    // Platform-specific builds
    const linux_x64 = b.step("linux-x64", "Build for Linux x86_64");
    const linux_exe = b.addExecutable(.{
        .name = "myapp-linux",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = b.resolveTargetQuery(.{
                .cpu_arch = .x86_64,
                .os_tag = .linux,
                .abi = .gnu,
            }),
            .optimize = optimize,
        }),
    });
    const install_linux = b.addInstallArtifact(linux_exe, .{});
    linux_x64.dependOn(&install_linux.step);

    const windows_x64 = b.step("windows-x64", "Build for Windows x86_64");
    const windows_exe = b.addExecutable(.{
        .name = "myapp-windows",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = b.resolveTargetQuery(.{
                .cpu_arch = .x86_64,
                .os_tag = .windows,
                .abi = .gnu,
            }),
            .optimize = optimize,
        }),
    });
    const install_windows = b.addInstallArtifact(windows_exe, .{});
    windows_x64.dependOn(&install_windows.step);

    const macos_arm = b.step("macos-arm", "Build for macOS ARM64");
    const macos_exe = b.addExecutable(.{
        .name = "myapp-macos",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = b.resolveTargetQuery(.{
                .cpu_arch = .aarch64,
                .os_tag = .macos,
            }),
            .optimize = optimize,
        }),
    });
    const install_macos = b.addInstallArtifact(macos_exe, .{});
    macos_arm.dependOn(&install_macos.step);
}
```

### Discussion

One of Zig's standout features is zero-friction cross-compilation. Zig ships with cross-compilation toolchains for all supported targets, making it easy to build for any platform from any platform.

### Target Information

Targets are defined by architecture, OS, and ABI:

```zig
// Target platform information
pub const TargetInfo = struct {
    arch: []const u8,
    os: []const u8,
    abi: []const u8,

    pub fn init(arch: []const u8, os: []const u8, abi: []const u8) TargetInfo {
        return .{
            .arch = arch,
            .os = os,
            .abi = abi,
        };
    }

    pub fn targetTriple(self: TargetInfo, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(allocator, "{s}-{s}-{s}", .{ self.arch, self.os, self.abi });
    }

    pub fn isNative(self: TargetInfo) bool {
        return std.mem.eql(u8, self.arch, @tagName(builtin.cpu.arch)) and
            std.mem.eql(u8, self.os, @tagName(builtin.os.tag));
    }
};

test "target info" {
    const target = TargetInfo.init("x86_64", "linux", "gnu");
    const triple = try target.targetTriple(testing.allocator);
    defer testing.allocator.free(triple);

    try testing.expect(std.mem.eql(u8, triple, "x86_64-linux-gnu"));
}
```

Common target combinations:
- `x86_64-linux-gnu` - 64-bit Linux with GNU libc
- `x86_64-linux-musl` - 64-bit Linux with musl libc
- `x86_64-windows-gnu` - 64-bit Windows with MinGW
- `aarch64-macos-none` - ARM64 macOS (Apple Silicon)
- `aarch64-linux-gnu` - ARM64 Linux
- `wasm32-freestanding-musl` - WebAssembly

### Cross-Compilation Configuration

Configure cross-compilation builds:

```zig
// Cross-compilation configuration
pub const CrossCompileConfig = struct {
    target: TargetInfo,
    optimize: []const u8,
    strip: bool,

    pub fn init(target: TargetInfo, optimize: []const u8) CrossCompileConfig {
        return .{
            .target = target,
            .optimize = optimize,
            .strip = false,
        };
    }

    pub fn withStrip(self: CrossCompileConfig) CrossCompileConfig {
        var result = self;
        result.strip = true;
        return result;
    }

    pub fn isOptimized(self: CrossCompileConfig) bool {
        return !std.mem.eql(u8, self.optimize, "Debug");
    }
};

test "cross compile config" {
    const target = TargetInfo.init("aarch64", "macos", "none");
    const config = CrossCompileConfig.init(target, "ReleaseFast");

    try testing.expect(config.isOptimized());
    try testing.expect(!config.strip);

    const stripped = config.withStrip();
    try testing.expect(stripped.strip);
}
```

Each cross-compilation target can have its own optimization level, strip settings, and other build options.

### Target Queries

Filter and select targets programmatically:

```zig
// Target query and filtering
pub const TargetQuery = struct {
    arch_filter: ?[]const u8,
    os_filter: ?[]const u8,

    pub fn init() TargetQuery {
        return .{
            .arch_filter = null,
            .os_filter = null,
        };
    }

    pub fn filterByArch(self: TargetQuery, arch: []const u8) TargetQuery {
        var result = self;
        result.arch_filter = arch;
        return result;
    }

    pub fn filterByOS(self: TargetQuery, os: []const u8) TargetQuery {
        var result = self;
        result.os_filter = os;
        return result;
    }

    pub fn matches(self: TargetQuery, target: TargetInfo) bool {
        if (self.arch_filter) |arch| {
            if (!std.mem.eql(u8, arch, target.arch)) return false;
        }
        if (self.os_filter) |os| {
            if (!std.mem.eql(u8, os, target.os)) return false;
        }
        return true;
    }
};

test "target query" {
    const query = TargetQuery.init().filterByArch("x86_64").filterByOS("linux");

    const linux_target = TargetInfo.init("x86_64", "linux", "gnu");
    const windows_target = TargetInfo.init("x86_64", "windows", "gnu");

    try testing.expect(query.matches(linux_target));
    try testing.expect(!query.matches(windows_target));
}
```

Target queries help when building for multiple platforms. You might want to:
- Build only for specific architectures (e.g., all ARM targets)
- Build only for specific operating systems (e.g., all Linux variants)
- Exclude certain combinations (e.g., skip 32-bit targets)

### Platform Features

Different platforms support different CPU features:

```zig
// Platform-specific features
pub const PlatformFeatures = struct {
    target: TargetInfo,
    features: []const []const u8,

    pub fn init(target: TargetInfo, features: []const []const u8) PlatformFeatures {
        return .{
            .target = target,
            .features = features,
        };
    }

    pub fn hasFeature(self: PlatformFeatures, feature: []const u8) bool {
        for (self.features) |f| {
            if (std.mem.eql(u8, f, feature)) return true;
        }
        return false;
    }

    pub fn featureCount(self: PlatformFeatures) usize {
        return self.features.len;
    }
};

test "platform features" {
    const target = TargetInfo.init("x86_64", "linux", "gnu");
    const features = [_][]const u8{ "sse4", "avx2" };
    const platform = PlatformFeatures.init(target, &features);

    try testing.expectEqual(@as(usize, 2), platform.featureCount());
    try testing.expect(platform.hasFeature("avx2"));
    try testing.expect(!platform.hasFeature("neon"));
}
```

CPU features affect performance and compatibility:
- **x86_64**: SSE, SSE2, SSE4, AVX, AVX2, AVX512
- **ARM**: NEON, SVE, crypto extensions
- **WebAssembly**: SIMD, threads, atomics

Zig lets you specify baseline CPU features and target specific CPU models.

### Parsing Target Triples

Work with target triple strings:

```zig
// Parse target triple strings
pub const TargetTriple = struct {
    raw: []const u8,

    pub fn init(triple: []const u8) TargetTriple {
        return .{ .raw = triple };
    }

    pub fn parse(self: TargetTriple, allocator: std.mem.Allocator) !TargetInfo {
        var parts = std.mem.splitSequence(u8, self.raw, "-");

        const arch = parts.next() orelse return error.InvalidTriple;
        const os = parts.next() orelse return error.InvalidTriple;
        const abi = parts.next() orelse return error.InvalidTriple;

        const arch_copy = try allocator.dupe(u8, arch);
        errdefer allocator.free(arch_copy);

        const os_copy = try allocator.dupe(u8, os);
        errdefer allocator.free(os_copy);

        const abi_copy = try allocator.dupe(u8, abi);

        return TargetInfo.init(arch_copy, os_copy, abi_copy);
    }

    pub fn isValid(self: TargetTriple) bool {
        var count: usize = 0;
        var iter = std.mem.splitSequence(u8, self.raw, "-");
        while (iter.next()) |_| {
            count += 1;
        }
        return count >= 3;
    }
};

test "target triple parsing" {
    const triple = TargetTriple.init("x86_64-linux-gnu");
    try testing.expect(triple.isValid());

    const target = try triple.parse(testing.allocator);
    defer {
        testing.allocator.free(target.arch);
        testing.allocator.free(target.os);
        testing.allocator.free(target.abi);
    }

    try testing.expect(std.mem.eql(u8, target.arch, "x86_64"));
    try testing.expect(std.mem.eql(u8, target.os, "linux"));
}
```

Target triples follow the format: `<arch>-<os>-<abi>`. Some examples:
- `x86_64-linux-gnu`
- `aarch64-macos-none`
- `riscv64-linux-musl`
- `wasm32-wasi-musl`

### Build Matrix

Build for multiple targets and optimization levels:

```zig
// Multi-target build matrix
pub const BuildMatrix = struct {
    targets: []const TargetInfo,
    optimizations: []const []const u8,

    pub fn init(targets: []const TargetInfo, opts: []const []const u8) BuildMatrix {
        return .{
            .targets = targets,
            .optimizations = opts,
        };
    }

    pub fn totalBuilds(self: BuildMatrix) usize {
        return self.targets.len * self.optimizations.len;
    }

    pub fn targetCount(self: BuildMatrix) usize {
        return self.targets.len;
    }
};

test "build matrix" {
    const targets = [_]TargetInfo{
        TargetInfo.init("x86_64", "linux", "gnu"),
        TargetInfo.init("x86_64", "windows", "gnu"),
        TargetInfo.init("aarch64", "linux", "gnu"),
    };
    const opts = [_][]const u8{ "Debug", "ReleaseFast", "ReleaseSmall" };
    const matrix = BuildMatrix.init(&targets, &opts);

    try testing.expectEqual(@as(usize, 9), matrix.totalBuilds());
    try testing.expectEqual(@as(usize, 3), matrix.targetCount());
}
```

Build matrices are common in CI/CD pipelines. You might want to test all combinations of:
- Targets (Linux, Windows, macOS)
- Architectures (x86_64, aarch64)
- Optimization levels (Debug, ReleaseFast, ReleaseSmall)

### Native Platform Detection

Detect the current platform at compile time:

```zig
// Detect native platform
pub const NativeDetection = struct {
    pub fn detect() TargetInfo {
        return TargetInfo.init(
            @tagName(builtin.cpu.arch),
            @tagName(builtin.os.tag),
            @tagName(builtin.abi),
        );
    }

    pub fn isLinux() bool {
        return builtin.os.tag == .linux;
    }

    pub fn isWindows() bool {
        return builtin.os.tag == .windows;
    }

    pub fn isMacOS() bool {
        return builtin.os.tag == .macos;
    }

    pub fn is64Bit() bool {
        return @sizeOf(usize) == 8;
    }
};

test "native detection" {
    const native = NativeDetection.detect();
    try testing.expect(native.arch.len > 0);
    try testing.expect(native.os.len > 0);

    // At least one should be true
    const has_os = NativeDetection.isLinux() or
        NativeDetection.isWindows() or
        NativeDetection.isMacOS();
    try testing.expect(has_os);
}
```

Use `builtin` to access compile-time platform information:
- `builtin.cpu.arch` - CPU architecture
- `builtin.os.tag` - Operating system
- `builtin.abi` - ABI/calling convention
- `builtin.mode` - Optimization mode

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;
const builtin = @import("builtin");

// This file demonstrates cross-compilation concepts

// ANCHOR: target_info
// Target platform information
pub const TargetInfo = struct {
    arch: []const u8,
    os: []const u8,
    abi: []const u8,

    pub fn init(arch: []const u8, os: []const u8, abi: []const u8) TargetInfo {
        return .{
            .arch = arch,
            .os = os,
            .abi = abi,
        };
    }

    pub fn targetTriple(self: TargetInfo, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(allocator, "{s}-{s}-{s}", .{ self.arch, self.os, self.abi });
    }

    pub fn isNative(self: TargetInfo) bool {
        return std.mem.eql(u8, self.arch, @tagName(builtin.cpu.arch)) and
            std.mem.eql(u8, self.os, @tagName(builtin.os.tag));
    }
};

test "target info" {
    const target = TargetInfo.init("x86_64", "linux", "gnu");
    const triple = try target.targetTriple(testing.allocator);
    defer testing.allocator.free(triple);

    try testing.expect(std.mem.eql(u8, triple, "x86_64-linux-gnu"));
}
// ANCHOR_END: target_info

// ANCHOR: cross_compile_config
// Cross-compilation configuration
pub const CrossCompileConfig = struct {
    target: TargetInfo,
    optimize: []const u8,
    strip: bool,

    pub fn init(target: TargetInfo, optimize: []const u8) CrossCompileConfig {
        return .{
            .target = target,
            .optimize = optimize,
            .strip = false,
        };
    }

    pub fn withStrip(self: CrossCompileConfig) CrossCompileConfig {
        var result = self;
        result.strip = true;
        return result;
    }

    pub fn isOptimized(self: CrossCompileConfig) bool {
        return !std.mem.eql(u8, self.optimize, "Debug");
    }
};

test "cross compile config" {
    const target = TargetInfo.init("aarch64", "macos", "none");
    const config = CrossCompileConfig.init(target, "ReleaseFast");

    try testing.expect(config.isOptimized());
    try testing.expect(!config.strip);

    const stripped = config.withStrip();
    try testing.expect(stripped.strip);
}
// ANCHOR_END: cross_compile_config

// ANCHOR: target_query
// Target query and filtering
pub const TargetQuery = struct {
    arch_filter: ?[]const u8,
    os_filter: ?[]const u8,

    pub fn init() TargetQuery {
        return .{
            .arch_filter = null,
            .os_filter = null,
        };
    }

    pub fn filterByArch(self: TargetQuery, arch: []const u8) TargetQuery {
        var result = self;
        result.arch_filter = arch;
        return result;
    }

    pub fn filterByOS(self: TargetQuery, os: []const u8) TargetQuery {
        var result = self;
        result.os_filter = os;
        return result;
    }

    pub fn matches(self: TargetQuery, target: TargetInfo) bool {
        if (self.arch_filter) |arch| {
            if (!std.mem.eql(u8, arch, target.arch)) return false;
        }
        if (self.os_filter) |os| {
            if (!std.mem.eql(u8, os, target.os)) return false;
        }
        return true;
    }
};

test "target query" {
    const query = TargetQuery.init().filterByArch("x86_64").filterByOS("linux");

    const linux_target = TargetInfo.init("x86_64", "linux", "gnu");
    const windows_target = TargetInfo.init("x86_64", "windows", "gnu");

    try testing.expect(query.matches(linux_target));
    try testing.expect(!query.matches(windows_target));
}
// ANCHOR_END: target_query

// ANCHOR: platform_features
// Platform-specific features
pub const PlatformFeatures = struct {
    target: TargetInfo,
    features: []const []const u8,

    pub fn init(target: TargetInfo, features: []const []const u8) PlatformFeatures {
        return .{
            .target = target,
            .features = features,
        };
    }

    pub fn hasFeature(self: PlatformFeatures, feature: []const u8) bool {
        for (self.features) |f| {
            if (std.mem.eql(u8, f, feature)) return true;
        }
        return false;
    }

    pub fn featureCount(self: PlatformFeatures) usize {
        return self.features.len;
    }
};

test "platform features" {
    const target = TargetInfo.init("x86_64", "linux", "gnu");
    const features = [_][]const u8{ "sse4", "avx2" };
    const platform = PlatformFeatures.init(target, &features);

    try testing.expectEqual(@as(usize, 2), platform.featureCount());
    try testing.expect(platform.hasFeature("avx2"));
    try testing.expect(!platform.hasFeature("neon"));
}
// ANCHOR_END: platform_features

// ANCHOR: target_triple_parsing
// Parse target triple strings
pub const TargetTriple = struct {
    raw: []const u8,

    pub fn init(triple: []const u8) TargetTriple {
        return .{ .raw = triple };
    }

    pub fn parse(self: TargetTriple, allocator: std.mem.Allocator) !TargetInfo {
        var parts = std.mem.splitSequence(u8, self.raw, "-");

        const arch = parts.next() orelse return error.InvalidTriple;
        const os = parts.next() orelse return error.InvalidTriple;
        const abi = parts.next() orelse return error.InvalidTriple;

        const arch_copy = try allocator.dupe(u8, arch);
        errdefer allocator.free(arch_copy);

        const os_copy = try allocator.dupe(u8, os);
        errdefer allocator.free(os_copy);

        const abi_copy = try allocator.dupe(u8, abi);

        return TargetInfo.init(arch_copy, os_copy, abi_copy);
    }

    pub fn isValid(self: TargetTriple) bool {
        var count: usize = 0;
        var iter = std.mem.splitSequence(u8, self.raw, "-");
        while (iter.next()) |_| {
            count += 1;
        }
        return count >= 3;
    }
};

test "target triple parsing" {
    const triple = TargetTriple.init("x86_64-linux-gnu");
    try testing.expect(triple.isValid());

    const target = try triple.parse(testing.allocator);
    defer {
        testing.allocator.free(target.arch);
        testing.allocator.free(target.os);
        testing.allocator.free(target.abi);
    }

    try testing.expect(std.mem.eql(u8, target.arch, "x86_64"));
    try testing.expect(std.mem.eql(u8, target.os, "linux"));
}
// ANCHOR_END: target_triple_parsing

// ANCHOR: build_matrix
// Multi-target build matrix
pub const BuildMatrix = struct {
    targets: []const TargetInfo,
    optimizations: []const []const u8,

    pub fn init(targets: []const TargetInfo, opts: []const []const u8) BuildMatrix {
        return .{
            .targets = targets,
            .optimizations = opts,
        };
    }

    pub fn totalBuilds(self: BuildMatrix) usize {
        return self.targets.len * self.optimizations.len;
    }

    pub fn targetCount(self: BuildMatrix) usize {
        return self.targets.len;
    }
};

test "build matrix" {
    const targets = [_]TargetInfo{
        TargetInfo.init("x86_64", "linux", "gnu"),
        TargetInfo.init("x86_64", "windows", "gnu"),
        TargetInfo.init("aarch64", "linux", "gnu"),
    };
    const opts = [_][]const u8{ "Debug", "ReleaseFast", "ReleaseSmall" };
    const matrix = BuildMatrix.init(&targets, &opts);

    try testing.expectEqual(@as(usize, 9), matrix.totalBuilds());
    try testing.expectEqual(@as(usize, 3), matrix.targetCount());
}
// ANCHOR_END: build_matrix

// ANCHOR: native_detection
// Detect native platform
pub const NativeDetection = struct {
    pub fn detect() TargetInfo {
        return TargetInfo.init(
            @tagName(builtin.cpu.arch),
            @tagName(builtin.os.tag),
            @tagName(builtin.abi),
        );
    }

    pub fn isLinux() bool {
        return builtin.os.tag == .linux;
    }

    pub fn isWindows() bool {
        return builtin.os.tag == .windows;
    }

    pub fn isMacOS() bool {
        return builtin.os.tag == .macos;
    }

    pub fn is64Bit() bool {
        return @sizeOf(usize) == 8;
    }
};

test "native detection" {
    const native = NativeDetection.detect();
    try testing.expect(native.arch.len > 0);
    try testing.expect(native.os.len > 0);

    // At least one should be true
    const has_os = NativeDetection.isLinux() or
        NativeDetection.isWindows() or
        NativeDetection.isMacOS();
    try testing.expect(has_os);
}
// ANCHOR_END: native_detection
```

### See Also

- Recipe 16.1: Basic build.zig setup
- Recipe 16.2: Multiple executables and libraries
- Recipe 16.6: Build options and configurations

---

## Recipe 16.6: Build options and configurations {#recipe-16-6}

**Tags:** allocators, build-system, comptime, data-structures, error-handling, hashmap, memory, resource-cleanup, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/16-zig-build-system/recipe_16_6.zig`

### Problem

You need to make your build process configurable with options that users can customize without modifying build.zig, and you want to inject configuration values into your code at compile time.

### Solution

Use Zig's build options system to create configurable builds. Define options in build.zig and access them in your code:

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Boolean option
    const enable_logging = b.option(
        bool,
        "enable-logging",
        "Enable debug logging (default: false)",
    ) orelse false;

    // String option
    const server_name = b.option(
        []const u8,
        "server-name",
        "Server name (default: myserver)",
    ) orelse "myserver";

    // Integer option
    const max_connections = b.option(
        u32,
        "max-connections",
        "Maximum connections (default: 100)",
    ) orelse 100;

    // Enum option
    const Environment = enum { development, staging, production };
    const environment = b.option(
        Environment,
        "environment",
        "Deployment environment (default: development)",
    ) orelse .development;

    // Create a build options module
    const options = b.addOptions();
    options.addOption(bool, "enable_logging", enable_logging);
    options.addOption([]const u8, "server_name", server_name);
    options.addOption(u32, "max_connections", max_connections);
    options.addOption(Environment, "environment", environment);
    options.addOption([]const u8, "version", "1.0.0");
    options.addOption([]const u8, "build_date", getBuildDate(b));

    // Create executable with options
    const exe = b.addExecutable(.{
        .name = "myapp",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    exe.root_module.addImport("build_options", options.createModule());
    b.installArtifact(exe);

    // Run step
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());

    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the application");
    run_step.dependOn(&run_cmd.step);

    // Print configuration
    const print_config = b.addSystemCommand(&[_][]const u8{"echo", "Build Configuration:"});
    const print_step = b.step("config", "Print build configuration");
    print_step.dependOn(&print_config.step);
}

fn getBuildDate(b: *std.Build) []const u8 {
    _ = b;
    return "2025-11-20";
}
```

Then use these options in your source code:

```zig
const build_options = @import("build_options");

pub fn main() !void {
    if (build_options.enable_logging) {
        // Logging code
    }
}
```

### Discussion

Build options let you configure builds at compile time. They're evaluated during compilation, allowing the compiler to optimize away unused code paths.

### Build Configuration

Structure your configuration logically:

```zig
// Build configuration structure
pub const BuildConfig = struct {
    enable_logging: bool,
    max_connections: u32,
    server_name: []const u8,
    port: u16,

    pub fn init(logging: bool, max_conn: u32, name: []const u8, port: u16) BuildConfig {
        return .{
            .enable_logging = logging,
            .max_connections = max_conn,
            .server_name = name,
            .port = port,
        };
    }

    pub fn isProduction(self: BuildConfig) bool {
        return !self.enable_logging and self.max_connections > 100;
    }
};

test "build config" {
    const config = BuildConfig.init(true, 50, "dev-server", 8080);

    try testing.expect(!config.isProduction());
    try testing.expectEqual(@as(u16, 8080), config.port);
    try testing.expect(std.mem.eql(u8, config.server_name, "dev-server"));
}
```

This creates a typed configuration structure that can be validated and reasoned about.

### Option Types

Zig supports various option types:

```zig
// Different types of build options
pub const OptionTypes = struct {
    // Boolean option
    pub const BoolOption = struct {
        name: []const u8,
        default: bool,
        description: []const u8,

        pub fn init(name: []const u8, default: bool, desc: []const u8) BoolOption {
            return .{ .name = name, .default = default, .description = desc };
        }
    };

    // String option
    pub const StringOption = struct {
        name: []const u8,
        default: ?[]const u8,
        description: []const u8,

        pub fn init(name: []const u8, default: ?[]const u8, desc: []const u8) StringOption {
            return .{ .name = name, .default = default, .description = desc };
        }

        pub fn hasDefault(self: StringOption) bool {
            return self.default != null;
        }
    };

    // Integer option
    pub const IntOption = struct {
        name: []const u8,
        default: i64,
        min: ?i64,
        max: ?i64,
        description: []const u8,

        pub fn init(name: []const u8, default: i64, desc: []const u8) IntOption {
            return .{ .name = name, .default = default, .min = null, .max = null, .description = desc };
        }

        pub fn withRange(self: IntOption, min: i64, max: i64) IntOption {
            var result = self;
            result.min = min;
            result.max = max;
            return result;
        }

        pub fn isValid(self: IntOption, value: i64) bool {
            if (self.min) |min| {
                if (value < min) return false;
            }
            if (self.max) |max| {
                if (value > max) return false;
            }
            return true;
        }
    };
};

test "option types" {
    const bool_opt = OptionTypes.BoolOption.init("enable-feature", true, "Enable feature");
    try testing.expect(bool_opt.default);

    const str_opt = OptionTypes.StringOption.init("name", "default", "Server name");
    try testing.expect(str_opt.hasDefault());

    const int_opt = OptionTypes.IntOption.init("port", 8080, "Server port").withRange(1024, 65535);
    try testing.expect(int_opt.isValid(8080));
    try testing.expect(!int_opt.isValid(80));
}
```

Common option types:
- **Boolean**: Enable/disable features (`bool`)
- **String**: Names, paths, URLs (`[]const u8`)
- **Integer**: Ports, limits, sizes (`u32`, `i64`, etc.)
- **Enum**: Predefined choices (`enum { dev, prod }`)

### Feature Flags

Manage feature flags systematically:

```zig
// Feature flag management
pub const FeatureFlags = struct {
    flags: std.StringHashMap(bool),

    pub fn init(allocator: std.mem.Allocator) FeatureFlags {
        return .{ .flags = std.StringHashMap(bool).init(allocator) };
    }

    pub fn deinit(self: *FeatureFlags) void {
        self.flags.deinit();
    }

    pub fn enable(self: *FeatureFlags, feature: []const u8) !void {
        try self.flags.put(feature, true);
    }

    pub fn disable(self: *FeatureFlags, feature: []const u8) !void {
        try self.flags.put(feature, false);
    }

    pub fn isEnabled(self: FeatureFlags, feature: []const u8) bool {
        return self.flags.get(feature) orelse false;
    }

    pub fn count(self: FeatureFlags) usize {
        return self.flags.count();
    }
};

test "feature flags" {
    var flags = FeatureFlags.init(testing.allocator);
    defer flags.deinit();

    try flags.enable("logging");
    try flags.enable("metrics");
    try flags.disable("deprecated-api");

    try testing.expect(flags.isEnabled("logging"));
    try testing.expect(!flags.isEnabled("deprecated-api"));
    try testing.expect(!flags.isEnabled("nonexistent"));
    try testing.expectEqual(@as(usize, 3), flags.count());
}
```

Feature flags control optional functionality:
- Enable experimental features
- Toggle debugging tools
- Control API versions
- Manage deprecated code paths

### Environment Configuration

Different environments need different settings:

```zig
// Environment-specific configuration
pub const EnvironmentConfig = struct {
    pub const Environment = enum {
        development,
        staging,
        production,

        pub fn isProduction(self: Environment) bool {
            return self == .production;
        }

        pub fn isDevelopment(self: Environment) bool {
            return self == .development;
        }
    };

    env: Environment,
    debug_mode: bool,
    optimize_level: []const u8,

    pub fn init(env: Environment) EnvironmentConfig {
        return .{
            .env = env,
            .debug_mode = env.isDevelopment(),
            .optimize_level = if (env.isProduction()) "ReleaseFast" else "Debug",
        };
    }

    pub fn shouldLog(self: EnvironmentConfig) bool {
        return self.debug_mode;
    }
};

test "environment config" {
    const dev = EnvironmentConfig.init(.development);
    try testing.expect(dev.debug_mode);
    try testing.expect(dev.shouldLog());

    const prod = EnvironmentConfig.init(.production);
    try testing.expect(!prod.debug_mode);
    try testing.expect(!prod.shouldLog());
    try testing.expect(std.mem.eql(u8, prod.optimize_level, "ReleaseFast"));
}
```

Common environments:
- **Development**: Debug logging, hot reload, relaxed validation
- **Staging**: Production-like with debug capabilities
- **Production**: Optimized, minimal logging, strict validation

### Conditional Compilation

Use comptime to conditionally include code:

```zig
// Conditional compilation configuration
pub const ConditionalCompilation = struct {
    pub fn hasFeature(comptime feature: []const u8) bool {
        _ = feature;
        // In real code, this would check build options
        return true;
    }

    pub fn getVersion() []const u8 {
        return "1.0.0";
    }

    pub fn getConfig(comptime T: type) T {
        // Return compile-time configuration
        return undefined;
    }
};

test "conditional compilation" {
    try testing.expect(ConditionalCompilation.hasFeature("test"));
    const version = ConditionalCompilation.getVersion();
    try testing.expect(version.len > 0);
}
```

This enables:
- Platform-specific code
- Feature-gated functionality
- Debug-only instrumentation
- Version-specific compatibility layers

### Optimization Profiles

Create named optimization profiles:

```zig
// Optimization profiles
pub const OptimizationProfile = struct {
    name: []const u8,
    mode: []const u8,
    strip_debug: bool,
    lto: bool,

    pub fn init(name: []const u8, mode: []const u8) OptimizationProfile {
        return .{
            .name = name,
            .mode = mode,
            .strip_debug = !std.mem.eql(u8, mode, "Debug"),
            .lto = std.mem.eql(u8, mode, "ReleaseFast"),
        };
    }

    pub fn isDebug(self: OptimizationProfile) bool {
        return std.mem.eql(u8, self.mode, "Debug");
    }

    pub fn isRelease(self: OptimizationProfile) bool {
        return !self.isDebug();
    }
};

test "optimization profiles" {
    const debug = OptimizationProfile.init("debug", "Debug");
    try testing.expect(debug.isDebug());
    try testing.expect(!debug.strip_debug);

    const release = OptimizationProfile.init("release", "ReleaseFast");
    try testing.expect(release.isRelease());
    try testing.expect(release.strip_debug);
    try testing.expect(release.lto);
}
```

Profiles combine multiple settings:
- Optimization mode (Debug, ReleaseFast, ReleaseSmall, ReleaseSafe)
- Debug symbol stripping
- Link-time optimization (LTO)
- Assertions and safety checks

### Platform Options

Handle platform-specific configuration:

```zig
// Platform-specific options
pub const PlatformOptions = struct {
    target_os: []const u8,
    target_arch: []const u8,
    use_libc: bool,

    pub fn init(os: []const u8, arch: []const u8, libc: bool) PlatformOptions {
        return .{
            .target_os = os,
            .target_arch = arch,
            .use_libc = libc,
        };
    }

    pub fn isUnix(self: PlatformOptions) bool {
        return std.mem.eql(u8, self.target_os, "linux") or
            std.mem.eql(u8, self.target_os, "macos");
    }

    pub fn isWindows(self: PlatformOptions) bool {
        return std.mem.eql(u8, self.target_os, "windows");
    }

    pub fn is64Bit(self: PlatformOptions) bool {
        return std.mem.eql(u8, self.target_arch, "x86_64") or
            std.mem.eql(u8, self.target_arch, "aarch64");
    }
};

test "platform options" {
    const linux = PlatformOptions.init("linux", "x86_64", true);
    try testing.expect(linux.isUnix());
    try testing.expect(!linux.isWindows());
    try testing.expect(linux.is64Bit());

    const windows = PlatformOptions.init("windows", "x86_64", false);
    try testing.expect(windows.isWindows());
    try testing.expect(!windows.isUnix());
}
```

Platform options control:
- System library linking
- Platform-specific features
- OS-specific code paths
- Architecture optimizations

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// This file demonstrates build options and configuration concepts

// ANCHOR: build_config
// Build configuration structure
pub const BuildConfig = struct {
    enable_logging: bool,
    max_connections: u32,
    server_name: []const u8,
    port: u16,

    pub fn init(logging: bool, max_conn: u32, name: []const u8, port: u16) BuildConfig {
        return .{
            .enable_logging = logging,
            .max_connections = max_conn,
            .server_name = name,
            .port = port,
        };
    }

    pub fn isProduction(self: BuildConfig) bool {
        return !self.enable_logging and self.max_connections > 100;
    }
};

test "build config" {
    const config = BuildConfig.init(true, 50, "dev-server", 8080);

    try testing.expect(!config.isProduction());
    try testing.expectEqual(@as(u16, 8080), config.port);
    try testing.expect(std.mem.eql(u8, config.server_name, "dev-server"));
}
// ANCHOR_END: build_config

// ANCHOR: option_types
// Different types of build options
pub const OptionTypes = struct {
    // Boolean option
    pub const BoolOption = struct {
        name: []const u8,
        default: bool,
        description: []const u8,

        pub fn init(name: []const u8, default: bool, desc: []const u8) BoolOption {
            return .{ .name = name, .default = default, .description = desc };
        }
    };

    // String option
    pub const StringOption = struct {
        name: []const u8,
        default: ?[]const u8,
        description: []const u8,

        pub fn init(name: []const u8, default: ?[]const u8, desc: []const u8) StringOption {
            return .{ .name = name, .default = default, .description = desc };
        }

        pub fn hasDefault(self: StringOption) bool {
            return self.default != null;
        }
    };

    // Integer option
    pub const IntOption = struct {
        name: []const u8,
        default: i64,
        min: ?i64,
        max: ?i64,
        description: []const u8,

        pub fn init(name: []const u8, default: i64, desc: []const u8) IntOption {
            return .{ .name = name, .default = default, .min = null, .max = null, .description = desc };
        }

        pub fn withRange(self: IntOption, min: i64, max: i64) IntOption {
            var result = self;
            result.min = min;
            result.max = max;
            return result;
        }

        pub fn isValid(self: IntOption, value: i64) bool {
            if (self.min) |min| {
                if (value < min) return false;
            }
            if (self.max) |max| {
                if (value > max) return false;
            }
            return true;
        }
    };
};

test "option types" {
    const bool_opt = OptionTypes.BoolOption.init("enable-feature", true, "Enable feature");
    try testing.expect(bool_opt.default);

    const str_opt = OptionTypes.StringOption.init("name", "default", "Server name");
    try testing.expect(str_opt.hasDefault());

    const int_opt = OptionTypes.IntOption.init("port", 8080, "Server port").withRange(1024, 65535);
    try testing.expect(int_opt.isValid(8080));
    try testing.expect(!int_opt.isValid(80));
}
// ANCHOR_END: option_types

// ANCHOR: feature_flags
// Feature flag management
pub const FeatureFlags = struct {
    flags: std.StringHashMap(bool),

    pub fn init(allocator: std.mem.Allocator) FeatureFlags {
        return .{ .flags = std.StringHashMap(bool).init(allocator) };
    }

    pub fn deinit(self: *FeatureFlags) void {
        self.flags.deinit();
    }

    pub fn enable(self: *FeatureFlags, feature: []const u8) !void {
        try self.flags.put(feature, true);
    }

    pub fn disable(self: *FeatureFlags, feature: []const u8) !void {
        try self.flags.put(feature, false);
    }

    pub fn isEnabled(self: FeatureFlags, feature: []const u8) bool {
        return self.flags.get(feature) orelse false;
    }

    pub fn count(self: FeatureFlags) usize {
        return self.flags.count();
    }
};

test "feature flags" {
    var flags = FeatureFlags.init(testing.allocator);
    defer flags.deinit();

    try flags.enable("logging");
    try flags.enable("metrics");
    try flags.disable("deprecated-api");

    try testing.expect(flags.isEnabled("logging"));
    try testing.expect(!flags.isEnabled("deprecated-api"));
    try testing.expect(!flags.isEnabled("nonexistent"));
    try testing.expectEqual(@as(usize, 3), flags.count());
}
// ANCHOR_END: feature_flags

// ANCHOR: environment_config
// Environment-specific configuration
pub const EnvironmentConfig = struct {
    pub const Environment = enum {
        development,
        staging,
        production,

        pub fn isProduction(self: Environment) bool {
            return self == .production;
        }

        pub fn isDevelopment(self: Environment) bool {
            return self == .development;
        }
    };

    env: Environment,
    debug_mode: bool,
    optimize_level: []const u8,

    pub fn init(env: Environment) EnvironmentConfig {
        return .{
            .env = env,
            .debug_mode = env.isDevelopment(),
            .optimize_level = if (env.isProduction()) "ReleaseFast" else "Debug",
        };
    }

    pub fn shouldLog(self: EnvironmentConfig) bool {
        return self.debug_mode;
    }
};

test "environment config" {
    const dev = EnvironmentConfig.init(.development);
    try testing.expect(dev.debug_mode);
    try testing.expect(dev.shouldLog());

    const prod = EnvironmentConfig.init(.production);
    try testing.expect(!prod.debug_mode);
    try testing.expect(!prod.shouldLog());
    try testing.expect(std.mem.eql(u8, prod.optimize_level, "ReleaseFast"));
}
// ANCHOR_END: environment_config

// ANCHOR: conditional_compilation
// Conditional compilation configuration
pub const ConditionalCompilation = struct {
    pub fn hasFeature(comptime feature: []const u8) bool {
        _ = feature;
        // In real code, this would check build options
        return true;
    }

    pub fn getVersion() []const u8 {
        return "1.0.0";
    }

    pub fn getConfig(comptime T: type) T {
        // Return compile-time configuration
        return undefined;
    }
};

test "conditional compilation" {
    try testing.expect(ConditionalCompilation.hasFeature("test"));
    const version = ConditionalCompilation.getVersion();
    try testing.expect(version.len > 0);
}
// ANCHOR_END: conditional_compilation

// ANCHOR: optimization_profiles
// Optimization profiles
pub const OptimizationProfile = struct {
    name: []const u8,
    mode: []const u8,
    strip_debug: bool,
    lto: bool,

    pub fn init(name: []const u8, mode: []const u8) OptimizationProfile {
        return .{
            .name = name,
            .mode = mode,
            .strip_debug = !std.mem.eql(u8, mode, "Debug"),
            .lto = std.mem.eql(u8, mode, "ReleaseFast"),
        };
    }

    pub fn isDebug(self: OptimizationProfile) bool {
        return std.mem.eql(u8, self.mode, "Debug");
    }

    pub fn isRelease(self: OptimizationProfile) bool {
        return !self.isDebug();
    }
};

test "optimization profiles" {
    const debug = OptimizationProfile.init("debug", "Debug");
    try testing.expect(debug.isDebug());
    try testing.expect(!debug.strip_debug);

    const release = OptimizationProfile.init("release", "ReleaseFast");
    try testing.expect(release.isRelease());
    try testing.expect(release.strip_debug);
    try testing.expect(release.lto);
}
// ANCHOR_END: optimization_profiles

// ANCHOR: platform_options
// Platform-specific options
pub const PlatformOptions = struct {
    target_os: []const u8,
    target_arch: []const u8,
    use_libc: bool,

    pub fn init(os: []const u8, arch: []const u8, libc: bool) PlatformOptions {
        return .{
            .target_os = os,
            .target_arch = arch,
            .use_libc = libc,
        };
    }

    pub fn isUnix(self: PlatformOptions) bool {
        return std.mem.eql(u8, self.target_os, "linux") or
            std.mem.eql(u8, self.target_os, "macos");
    }

    pub fn isWindows(self: PlatformOptions) bool {
        return std.mem.eql(u8, self.target_os, "windows");
    }

    pub fn is64Bit(self: PlatformOptions) bool {
        return std.mem.eql(u8, self.target_arch, "x86_64") or
            std.mem.eql(u8, self.target_arch, "aarch64");
    }
};

test "platform options" {
    const linux = PlatformOptions.init("linux", "x86_64", true);
    try testing.expect(linux.isUnix());
    try testing.expect(!linux.isWindows());
    try testing.expect(linux.is64Bit());

    const windows = PlatformOptions.init("windows", "x86_64", false);
    try testing.expect(windows.isWindows());
    try testing.expect(!windows.isUnix());
}
// ANCHOR_END: platform_options
```

### See Also

- Recipe 16.1: Basic build.zig setup
- Recipe 16.4: Custom build steps
- Recipe 16.5: Cross

---

## Recipe 16.7: Testing in the build system {#recipe-16-7}

**Tags:** allocators, build-system, c-interop, comptime, error-handling, memory, resource-cleanup, slices, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/16-zig-build-system/recipe_16_7.zig`

### Problem

You need to organize and run different types of tests (unit, integration, benchmarks) as part of your build process, with the ability to run subsets of tests and configure test behavior.

### Solution

Use Zig's build system to create multiple test targets with different configurations:

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Create library
    const lib = b.addStaticLibrary(.{
        .name = "mylib",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lib.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    b.installArtifact(lib);

    // Unit tests for the library
    const lib_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lib.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    const run_lib_tests = b.addRunArtifact(lib_tests);

    // Integration tests
    const integration_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("test/integration.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    // Link integration tests with the library
    integration_tests.root_module.linkLibrary(lib);
    const run_integration_tests = b.addRunArtifact(integration_tests);

    // Default test step (runs all tests)
    const test_step = b.step("test", "Run all tests");
    test_step.dependOn(&run_lib_tests.step);
    test_step.dependOn(&run_integration_tests.step);

    // Unit tests only
    const unit_test_step = b.step("test-unit", "Run unit tests");
    unit_test_step.dependOn(&run_lib_tests.step);

    // Integration tests only
    const integration_test_step = b.step("test-integration", "Run integration tests");
    integration_test_step.dependOn(&run_integration_tests.step);

    // Filtered tests
    const fast_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lib.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    fast_tests.filters = &[_][]const u8{"fast"};

    const run_fast_tests = b.addRunArtifact(fast_tests);
    const fast_test_step = b.step("test-fast", "Run fast tests only");
    fast_test_step.dependOn(&run_fast_tests.step);

    // Benchmark tests
    const bench_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("test/benchmark.zig"),
            .target = target,
            .optimize = .ReleaseFast,
        }),
    });

    const run_bench = b.addRunArtifact(bench_tests);
    const bench_step = b.step("bench", "Run benchmarks");
    bench_step.dependOn(&run_bench.step);

    // Create executable for testing
    const exe = b.addExecutable(.{
        .name = "myapp",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    exe.root_module.linkLibrary(lib);
    b.installArtifact(exe);

    // Create a check step (compile without running)
    const check_step = b.step("check", "Check if code compiles");
    check_step.dependOn(&lib.step);
    check_step.dependOn(&exe.step);
    check_step.dependOn(&lib_tests.step);
    check_step.dependOn(&integration_tests.step);
}
```

### Discussion

Zig's build system integrates testing directly, making it easy to organize and run tests at different levels of granularity.

### Test Configuration

Configure tests programmatically:

```zig
// Test configuration
pub const TestConfig = struct {
    name: []const u8,
    source_file: []const u8,
    filters: []const []const u8,

    pub fn init(name: []const u8, source: []const u8) TestConfig {
        return .{
            .name = name,
            .source_file = source,
            .filters = &[_][]const u8{},
        };
    }

    pub fn withFilters(self: TestConfig, filters: []const []const u8) TestConfig {
        var result = self;
        result.filters = filters;
        return result;
    }

    pub fn hasFilters(self: TestConfig) bool {
        return self.filters.len > 0;
    }
};

test "test configuration" {
    const config = TestConfig.init("unit-tests", "src/lib.zig");
    try testing.expect(!config.hasFilters());
    try testing.expect(std.mem.eql(u8, config.name, "unit-tests"));

    const filters = [_][]const u8{"integration"};
    const filtered = config.withFilters(&filters);
    try testing.expect(filtered.hasFilters());
}
```

Test configuration lets you:
- Name test suites
- Specify source files
- Apply filters to run specific tests
- Set test-specific build options

### Test Suites

Organize tests into logical suites:

```zig
// Test suite organization
pub const TestSuite = struct {
    name: []const u8,
    tests: []const TestConfig,

    pub fn init(name: []const u8, tests: []const TestConfig) TestSuite {
        return .{
            .name = name,
            .tests = tests,
        };
    }

    pub fn testCount(self: TestSuite) usize {
        return self.tests.len;
    }

    pub fn hasTest(self: TestSuite, test_name: []const u8) bool {
        for (self.tests) |t| {
            if (std.mem.eql(u8, t.name, test_name)) return true;
        }
        return false;
    }
};

test "test suite" {
    const tests = [_]TestConfig{
        TestConfig.init("unit", "test/unit.zig"),
        TestConfig.init("integration", "test/integration.zig"),
    };
    const suite = TestSuite.init("all-tests", &tests);

    try testing.expectEqual(@as(usize, 2), suite.testCount());
    try testing.expect(suite.hasTest("unit"));
    try testing.expect(!suite.hasTest("e2e"));
}
```

Test suites help organize:
- Unit tests (fast, isolated function tests)
- Integration tests (component interaction tests)
- End-to-end tests (full system tests)
- Performance tests (benchmarks)

### Test Filtering

Run specific tests using filters:

```zig
// Test filtering
pub const TestFilter = struct {
    include_patterns: []const []const u8,
    exclude_patterns: []const []const u8,

    pub fn init() TestFilter {
        return .{
            .include_patterns = &[_][]const u8{},
            .exclude_patterns = &[_][]const u8{},
        };
    }

    pub fn withIncludes(self: TestFilter, patterns: []const []const u8) TestFilter {
        var result = self;
        result.include_patterns = patterns;
        return result;
    }

    pub fn withExcludes(self: TestFilter, patterns: []const []const u8) TestFilter {
        var result = self;
        result.exclude_patterns = patterns;
        return result;
    }

    pub fn matches(self: TestFilter, test_name: []const u8) bool {
        // If includes specified, must match at least one
        if (self.include_patterns.len > 0) {
            var matched = false;
            for (self.include_patterns) |pattern| {
                if (std.mem.indexOf(u8, test_name, pattern) != null) {
                    matched = true;
                    break;
                }
            }
            if (!matched) return false;
        }

        // Must not match any exclude patterns
        for (self.exclude_patterns) |pattern| {
            if (std.mem.indexOf(u8, test_name, pattern) != null) {
                return false;
            }
        }

        return true;
    }
};

test "test filter" {
    const includes = [_][]const u8{"unit"};
    const excludes = [_][]const u8{"slow"};
    const filter = TestFilter.init().withIncludes(&includes).withExcludes(&excludes);

    try testing.expect(filter.matches("unit_test"));
    try testing.expect(!filter.matches("integration_test"));
    try testing.expect(!filter.matches("unit_slow_test"));
}
```

Filters are powerful for:
- Running fast tests during development
- Skipping slow integration tests
- Running only specific test categories
- CI/CD selective test execution

### Coverage Configuration

Track test coverage:

```zig
// Test coverage configuration
pub const CoverageConfig = struct {
    enabled: bool,
    output_dir: []const u8,
    format: []const u8,

    pub fn init(enabled: bool, output: []const u8) CoverageConfig {
        return .{
            .enabled = enabled,
            .output_dir = output,
            .format = "lcov",
        };
    }

    pub fn withFormat(self: CoverageConfig, format: []const u8) CoverageConfig {
        var result = self;
        result.format = format;
        return result;
    }

    pub fn isLcov(self: CoverageConfig) bool {
        return std.mem.eql(u8, self.format, "lcov");
    }
};

test "coverage config" {
    const coverage = CoverageConfig.init(true, "coverage");
    try testing.expect(coverage.enabled);
    try testing.expect(coverage.isLcov());

    const html = coverage.withFormat("html");
    try testing.expect(!html.isLcov());
}
```

Coverage helps identify:
- Untested code paths
- Dead code
- Missing edge case tests
- Areas needing more testing

### Benchmark Configuration

Configure performance benchmarks:

```zig
// Benchmark configuration
pub const BenchmarkConfig = struct {
    name: []const u8,
    iterations: u32,
    warmup_iterations: u32,

    pub fn init(name: []const u8, iterations: u32) BenchmarkConfig {
        return .{
            .name = name,
            .iterations = iterations,
            .warmup_iterations = iterations / 10,
        };
    }

    pub fn withWarmup(self: BenchmarkConfig, warmup: u32) BenchmarkConfig {
        var result = self;
        result.warmup_iterations = warmup;
        return result;
    }

    pub fn totalIterations(self: BenchmarkConfig) u32 {
        return self.iterations + self.warmup_iterations;
    }
};

test "benchmark config" {
    const bench = BenchmarkConfig.init("sort_benchmark", 1000);
    try testing.expectEqual(@as(u32, 100), bench.warmup_iterations);
    try testing.expectEqual(@as(u32, 1100), bench.totalIterations());

    const custom = bench.withWarmup(50);
    try testing.expectEqual(@as(u32, 1050), custom.totalIterations());
}
```

Benchmarks measure:
- Function execution time
- Algorithm efficiency
- Memory allocation patterns
- Throughput and latency

### Test Runner Options

Customize test execution:

```zig
// Test runner options
pub const TestRunnerOptions = struct {
    verbose: bool,
    fail_fast: bool,
    parallel: bool,
    timeout_seconds: ?u32,

    pub fn init() TestRunnerOptions {
        return .{
            .verbose = false,
            .fail_fast = false,
            .parallel = true,
            .timeout_seconds = null,
        };
    }

    pub fn withVerbose(self: TestRunnerOptions) TestRunnerOptions {
        var result = self;
        result.verbose = true;
        return result;
    }

    pub fn withFailFast(self: TestRunnerOptions) TestRunnerOptions {
        var result = self;
        result.fail_fast = true;
        return result;
    }

    pub fn withTimeout(self: TestRunnerOptions, timeout: u32) TestRunnerOptions {
        var result = self;
        result.timeout_seconds = timeout;
        return result;
    }

    pub fn hasTimeout(self: TestRunnerOptions) bool {
        return self.timeout_seconds != null;
    }
};

test "test runner options" {
    const opts = TestRunnerOptions.init();
    try testing.expect(!opts.verbose);
    try testing.expect(opts.parallel);
    try testing.expect(!opts.hasTimeout());

    const verbose = opts.withVerbose().withFailFast().withTimeout(300);
    try testing.expect(verbose.verbose);
    try testing.expect(verbose.fail_fast);
    try testing.expect(verbose.hasTimeout());
}
```

Runner options control:
- Verbose output for debugging
- Fail-fast behavior (stop on first failure)
- Parallel test execution
- Test timeouts

### Integration Test Configuration

Set up integration tests properly:

```zig
// Integration test configuration
pub const IntegrationTestConfig = struct {
    name: []const u8,
    setup_required: bool,
    cleanup_required: bool,
    dependencies: []const []const u8,

    pub fn init(name: []const u8) IntegrationTestConfig {
        return .{
            .name = name,
            .setup_required = false,
            .cleanup_required = false,
            .dependencies = &[_][]const u8{},
        };
    }

    pub fn requiresSetup(self: IntegrationTestConfig) IntegrationTestConfig {
        var result = self;
        result.setup_required = true;
        return result;
    }

    pub fn requiresCleanup(self: IntegrationTestConfig) IntegrationTestConfig {
        var result = self;
        result.cleanup_required = true;
        return result;
    }

    pub fn withDependencies(self: IntegrationTestConfig, deps: []const []const u8) IntegrationTestConfig {
        var result = self;
        result.dependencies = deps;
        return result;
    }

    pub fn hasDependencies(self: IntegrationTestConfig) bool {
        return self.dependencies.len > 0;
    }
};

test "integration test config" {
    const config = IntegrationTestConfig.init("api-test");
    try testing.expect(!config.setup_required);
    try testing.expect(!config.hasDependencies());

    const deps = [_][]const u8{ "database", "redis" };
    const full = config.requiresSetup().requiresCleanup().withDependencies(&deps);
    try testing.expect(full.setup_required);
    try testing.expect(full.cleanup_required);
    try testing.expect(full.hasDependencies());
}
```

Integration tests often need:
- Database setup/teardown
- External service mocking
- Test data fixtures
- Environment configuration

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// This file demonstrates testing in the build system

// ANCHOR: test_configuration
// Test configuration
pub const TestConfig = struct {
    name: []const u8,
    source_file: []const u8,
    filters: []const []const u8,

    pub fn init(name: []const u8, source: []const u8) TestConfig {
        return .{
            .name = name,
            .source_file = source,
            .filters = &[_][]const u8{},
        };
    }

    pub fn withFilters(self: TestConfig, filters: []const []const u8) TestConfig {
        var result = self;
        result.filters = filters;
        return result;
    }

    pub fn hasFilters(self: TestConfig) bool {
        return self.filters.len > 0;
    }
};

test "test configuration" {
    const config = TestConfig.init("unit-tests", "src/lib.zig");
    try testing.expect(!config.hasFilters());
    try testing.expect(std.mem.eql(u8, config.name, "unit-tests"));

    const filters = [_][]const u8{"integration"};
    const filtered = config.withFilters(&filters);
    try testing.expect(filtered.hasFilters());
}
// ANCHOR_END: test_configuration

// ANCHOR: test_suite
// Test suite organization
pub const TestSuite = struct {
    name: []const u8,
    tests: []const TestConfig,

    pub fn init(name: []const u8, tests: []const TestConfig) TestSuite {
        return .{
            .name = name,
            .tests = tests,
        };
    }

    pub fn testCount(self: TestSuite) usize {
        return self.tests.len;
    }

    pub fn hasTest(self: TestSuite, test_name: []const u8) bool {
        for (self.tests) |t| {
            if (std.mem.eql(u8, t.name, test_name)) return true;
        }
        return false;
    }
};

test "test suite" {
    const tests = [_]TestConfig{
        TestConfig.init("unit", "test/unit.zig"),
        TestConfig.init("integration", "test/integration.zig"),
    };
    const suite = TestSuite.init("all-tests", &tests);

    try testing.expectEqual(@as(usize, 2), suite.testCount());
    try testing.expect(suite.hasTest("unit"));
    try testing.expect(!suite.hasTest("e2e"));
}
// ANCHOR_END: test_suite

// ANCHOR: test_filter
// Test filtering
pub const TestFilter = struct {
    include_patterns: []const []const u8,
    exclude_patterns: []const []const u8,

    pub fn init() TestFilter {
        return .{
            .include_patterns = &[_][]const u8{},
            .exclude_patterns = &[_][]const u8{},
        };
    }

    pub fn withIncludes(self: TestFilter, patterns: []const []const u8) TestFilter {
        var result = self;
        result.include_patterns = patterns;
        return result;
    }

    pub fn withExcludes(self: TestFilter, patterns: []const []const u8) TestFilter {
        var result = self;
        result.exclude_patterns = patterns;
        return result;
    }

    pub fn matches(self: TestFilter, test_name: []const u8) bool {
        // If includes specified, must match at least one
        if (self.include_patterns.len > 0) {
            var matched = false;
            for (self.include_patterns) |pattern| {
                if (std.mem.indexOf(u8, test_name, pattern) != null) {
                    matched = true;
                    break;
                }
            }
            if (!matched) return false;
        }

        // Must not match any exclude patterns
        for (self.exclude_patterns) |pattern| {
            if (std.mem.indexOf(u8, test_name, pattern) != null) {
                return false;
            }
        }

        return true;
    }
};

test "test filter" {
    const includes = [_][]const u8{"unit"};
    const excludes = [_][]const u8{"slow"};
    const filter = TestFilter.init().withIncludes(&includes).withExcludes(&excludes);

    try testing.expect(filter.matches("unit_test"));
    try testing.expect(!filter.matches("integration_test"));
    try testing.expect(!filter.matches("unit_slow_test"));
}
// ANCHOR_END: test_filter

// ANCHOR: coverage_config
// Test coverage configuration
pub const CoverageConfig = struct {
    enabled: bool,
    output_dir: []const u8,
    format: []const u8,

    pub fn init(enabled: bool, output: []const u8) CoverageConfig {
        return .{
            .enabled = enabled,
            .output_dir = output,
            .format = "lcov",
        };
    }

    pub fn withFormat(self: CoverageConfig, format: []const u8) CoverageConfig {
        var result = self;
        result.format = format;
        return result;
    }

    pub fn isLcov(self: CoverageConfig) bool {
        return std.mem.eql(u8, self.format, "lcov");
    }
};

test "coverage config" {
    const coverage = CoverageConfig.init(true, "coverage");
    try testing.expect(coverage.enabled);
    try testing.expect(coverage.isLcov());

    const html = coverage.withFormat("html");
    try testing.expect(!html.isLcov());
}
// ANCHOR_END: coverage_config

// ANCHOR: benchmark_config
// Benchmark configuration
pub const BenchmarkConfig = struct {
    name: []const u8,
    iterations: u32,
    warmup_iterations: u32,

    pub fn init(name: []const u8, iterations: u32) BenchmarkConfig {
        return .{
            .name = name,
            .iterations = iterations,
            .warmup_iterations = iterations / 10,
        };
    }

    pub fn withWarmup(self: BenchmarkConfig, warmup: u32) BenchmarkConfig {
        var result = self;
        result.warmup_iterations = warmup;
        return result;
    }

    pub fn totalIterations(self: BenchmarkConfig) u32 {
        return self.iterations + self.warmup_iterations;
    }
};

test "benchmark config" {
    const bench = BenchmarkConfig.init("sort_benchmark", 1000);
    try testing.expectEqual(@as(u32, 100), bench.warmup_iterations);
    try testing.expectEqual(@as(u32, 1100), bench.totalIterations());

    const custom = bench.withWarmup(50);
    try testing.expectEqual(@as(u32, 1050), custom.totalIterations());
}
// ANCHOR_END: benchmark_config

// ANCHOR: test_runner_options
// Test runner options
pub const TestRunnerOptions = struct {
    verbose: bool,
    fail_fast: bool,
    parallel: bool,
    timeout_seconds: ?u32,

    pub fn init() TestRunnerOptions {
        return .{
            .verbose = false,
            .fail_fast = false,
            .parallel = true,
            .timeout_seconds = null,
        };
    }

    pub fn withVerbose(self: TestRunnerOptions) TestRunnerOptions {
        var result = self;
        result.verbose = true;
        return result;
    }

    pub fn withFailFast(self: TestRunnerOptions) TestRunnerOptions {
        var result = self;
        result.fail_fast = true;
        return result;
    }

    pub fn withTimeout(self: TestRunnerOptions, timeout: u32) TestRunnerOptions {
        var result = self;
        result.timeout_seconds = timeout;
        return result;
    }

    pub fn hasTimeout(self: TestRunnerOptions) bool {
        return self.timeout_seconds != null;
    }
};

test "test runner options" {
    const opts = TestRunnerOptions.init();
    try testing.expect(!opts.verbose);
    try testing.expect(opts.parallel);
    try testing.expect(!opts.hasTimeout());

    const verbose = opts.withVerbose().withFailFast().withTimeout(300);
    try testing.expect(verbose.verbose);
    try testing.expect(verbose.fail_fast);
    try testing.expect(verbose.hasTimeout());
}
// ANCHOR_END: test_runner_options

// ANCHOR: integration_test_config
// Integration test configuration
pub const IntegrationTestConfig = struct {
    name: []const u8,
    setup_required: bool,
    cleanup_required: bool,
    dependencies: []const []const u8,

    pub fn init(name: []const u8) IntegrationTestConfig {
        return .{
            .name = name,
            .setup_required = false,
            .cleanup_required = false,
            .dependencies = &[_][]const u8{},
        };
    }

    pub fn requiresSetup(self: IntegrationTestConfig) IntegrationTestConfig {
        var result = self;
        result.setup_required = true;
        return result;
    }

    pub fn requiresCleanup(self: IntegrationTestConfig) IntegrationTestConfig {
        var result = self;
        result.cleanup_required = true;
        return result;
    }

    pub fn withDependencies(self: IntegrationTestConfig, deps: []const []const u8) IntegrationTestConfig {
        var result = self;
        result.dependencies = deps;
        return result;
    }

    pub fn hasDependencies(self: IntegrationTestConfig) bool {
        return self.dependencies.len > 0;
    }
};

test "integration test config" {
    const config = IntegrationTestConfig.init("api-test");
    try testing.expect(!config.setup_required);
    try testing.expect(!config.hasDependencies());

    const deps = [_][]const u8{ "database", "redis" };
    const full = config.requiresSetup().requiresCleanup().withDependencies(&deps);
    try testing.expect(full.setup_required);
    try testing.expect(full.cleanup_required);
    try testing.expect(full.hasDependencies());
}
// ANCHOR_END: integration_test_config
```

### See Also

- Recipe 16.1: Basic build.zig setup
- Recipe 16.4: Custom build steps
- Recipe 16.6: Build options and configurations
- Recipe 14.1: Testing program output
- Recipe 14.3: Testing exceptional conditions

---
