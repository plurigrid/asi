# Zig Version Differences

## Table of Contents

1. [Overview](#overview)
2. [Major Version Changes](#major-version-changes)
3. [Detailed Migration Guides](#detailed-migration-guides)
   - [0.10.x → 0.11.x Migration](#010x--011x-migration)
   - [0.12.x → 0.13.x Migration](#012x--013x-migration)
   - [0.13.x → 0.14.x → 0.15.x Migration](#013x--014x--015x-migration)
4. [Breaking Changes Catalog](#breaking-changes-catalog)
5. [Standard Library API Changes](#standard-library-api-changes)
6. [Error Message Translations](#error-message-translations)
7. [Version Detection](#version-detection)
8. [Cross-Version Compatibility](#cross-version-compatibility)

## Overview

This document provides comprehensive guidance for migrating between Zig versions, with particular focus on breaking changes and their solutions. Use this reference when:

- Upgrading existing code to a newer Zig version
- Maintaining code that must work across multiple versions
- Understanding why code works in one version but not another
- Interpreting version-specific error messages

**Current stable:** Zig 0.15.2 (as of this documentation)

**Recommended versions for production:**
- **0.15.2** - Current stable, recommended for new projects
- **0.14.1** - Previous stable, still widely used
- **0.13.0** - Older stable with good ecosystem support

**Legacy versions:**
- **0.11.0-0.12.1** - Early modern Zig, major breaking changes from 0.10
- **0.9.1-0.10.1** - Last versions with async/await
- **0.2.0-0.8.1** - Early experimental versions, not recommended

## Major Version Changes

### 0.15.x (Current Stable)

**Release:** January 2025
**Status:** Current stable release

**Key Features:**
- Refined build system API (incremental improvements over 0.14)
- Enhanced error handling with better diagnostics
- Improved standard library consistency
- Better C interop support
- Enhanced comptime capabilities

**Breaking Changes from 0.14:**
- Minor standard library reorganization
- Some deprecated APIs removed
- Build system refinements (mostly backwards compatible)

**Code Compatibility:**
- ✅ Code from 0.14.x usually works with minor adjustments
- ⚠️ Some deprecated APIs require updates
- ❌ 0.10.x and earlier code requires significant migration

### 0.14.x

**Release:** October 2024
**Status:** Previous stable, still widely used

**Key Features:**
- Stable build API (no major changes from 0.13)
- Enhanced package manager support
- Improved error messages
- Better comptime diagnostics

**Breaking Changes from 0.13:**
- Minor standard library refinements
- Some build API improvements
- Error set improvements

### 0.13.x

**Release:** June 2024
**Status:** Significant for loop syntax changes

**Key Features:**
- **Major:** New for loop syntax with multiple captures
- Enhanced slice operations
- Improved type inference
- Better error handling

**Breaking Changes from 0.12:**
- **CRITICAL:** For loop syntax completely changed
- Multiple iteration variable captures now supported
- Index enumeration syntax changed

### 0.11.x - 0.12.x

**Release:** 0.11.0 (August 2023), 0.12.0 (December 2023)
**Status:** Major modernization releases

**Key Features:**
- **CRITICAL:** Async/await removed (being redesigned)
- **CRITICAL:** Complete build system API overhaul
- Modern error set syntax
- Improved standard library organization

**Breaking Changes from 0.10:**
- All async/await code must be rewritten
- All build.zig files must be updated
- Error set syntax modernized
- Many standard library reorganizations

### 0.9.x - 0.10.x

**Release:** 0.9.0 (August 2021), 0.10.0 (October 2021)
**Status:** Last versions with async/await

**Key Features:**
- Full async/await support
- Event loop built into runtime
- Coroutine-based concurrency
- Legacy build API

**Notable:**
- Most code from this era requires significant migration to 0.11+
- Async/await code cannot be automatically converted
- Build system completely different from 0.11+

### 0.2.x - 0.8.x

**Status:** Early experimental versions, not recommended

**Notable:**
- Significant syntax instability
- Limited standard library
- Many breaking changes between minor versions
- Migration from these versions requires complete rewrite

## Detailed Migration Guides

### 0.10.x → 0.11.x Migration

This is the **most significant breaking change** in recent Zig history. Plan for substantial work when migrating from 0.10.x to 0.11+.

#### 1. Async/Await Removal

**The Problem:** Async/await was completely removed in 0.11 for redesign.

**Before (0.10.x):**
```zig
const std = @import("std");

// Async function definition
fn fetchData() callconv(.Async) ![]const u8 {
    // Simulate async operation
    suspend;
    return "data";
}

pub fn main() !void {
    // Async call
    const frame = async fetchData();
    const result = await frame;
    std.debug.print("Result: {s}\n", .{result});
}
```

**After (0.11+):**
```zig
const std = @import("std");

// Use threads instead
fn fetchData() ![]const u8 {
    // Synchronous operation or use threads
    return "data";
}

pub fn main() !void {
    // Option 1: Direct synchronous call
    const result = try fetchData();
    std.debug.print("Result: {s}\n", .{result});

    // Option 2: Use threads for concurrency
    const thread = try std.Thread.spawn(.{}, fetchData, .{});
    const result2 = try thread.join();
    std.debug.print("Result: {s}\n", .{result2});
}
```

**Migration Strategy:**

1. **Simple Async Functions → Synchronous:**
   - Remove `callconv(.Async)`
   - Remove `await` calls
   - Remove `suspend` statements

2. **Concurrent Async → Threads:**
   ```zig
   // Before: Multiple async operations
   const frame1 = async operation1();
   const frame2 = async operation2();
   const result1 = await frame1;
   const result2 = await frame2;

   // After: Thread pool
   const thread1 = try std.Thread.spawn(.{}, operation1, .{});
   const thread2 = try std.Thread.spawn(.{}, operation2, .{});
   const result1 = try thread1.join();
   const result2 = try thread2.join();
   ```

3. **Event Loop Patterns → Custom Event Loop:**
   ```zig
   // You'll need to implement your own event loop using:
   // - std.Thread for concurrency
   // - std.os polling APIs (poll, epoll, kqueue)
   // - std.event.Loop (if available in your version)
   ```

4. **Frames and Allocations:**
   - Remove all `@Frame(func)` usages
   - Remove async frame allocations
   - Use regular allocators instead

#### 2. Build System API Complete Overhaul

**The Problem:** The entire build.zig API was redesigned in 0.11.

**Before (0.10.x):**
```zig
const std = @import("std");

pub fn build(b: *std.build.Builder) void {
    const target = b.standardTargetOptions(.{});
    const mode = b.standardReleaseOptions();

    const exe = b.addExecutable("myapp", "src/main.zig");
    exe.setTarget(target);
    exe.setBuildMode(mode);
    exe.install();

    const run_cmd = exe.run();
    run_cmd.step.dependOn(b.getInstallStep());
    const run_step = b.step("run", "Run the application");
    run_step.dependOn(&run_cmd.step);

    const test_step = b.step("test", "Run tests");
    const tests = b.addTest("src/main.zig");
    tests.setTarget(target);
    tests.setBuildMode(mode);
    test_step.dependOn(&tests.step);
}
```

**After (0.11+):**
```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe = b.addExecutable(.{
        .name = "myapp",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }
    const run_step = b.step("run", "Run the application");
    run_step.dependOn(&run_cmd.step);

    const tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    const run_tests = b.addRunArtifact(tests);
    const test_step = b.step("test", "Run tests");
    test_step.dependOn(&run_tests.step);
}
```

**Key Changes:**

| 0.10.x | 0.11+ | Notes |
|--------|-------|-------|
| `*std.build.Builder` | `*std.Build` | Type name changed |
| `standardReleaseOptions()` | `standardOptimizeOption(.{})` | Returns `OptimizeMode` |
| `addExecutable("name", "path")` | `addExecutable(.{ .name = "name", .root_source_file = b.path("path"), ... })` | Struct literal syntax |
| `exe.setTarget(target)` | Pass in `.target` field | No setter methods |
| `exe.setBuildMode(mode)` | Pass in `.optimize` field | No setter methods |
| `exe.install()` | `b.installArtifact(exe)` | Different method |
| `exe.run()` | `b.addRunArtifact(exe)` | Different method |
| `addTest("path")` | `addTest(.{ .root_source_file = b.path("path"), ... })` | Struct literal syntax |
| `"src/main.zig"` | `b.path("src/main.zig")` | Must use `b.path()` |

**Migration Checklist:**

- [ ] Change parameter type: `*std.build.Builder` → `*std.Build`
- [ ] Replace `standardReleaseOptions()` → `standardOptimizeOption(.{})`
- [ ] Convert all `addExecutable()` to struct literal syntax
- [ ] Convert all `addTest()` to struct literal syntax
- [ ] Wrap all file paths with `b.path()`
- [ ] Replace `exe.install()` → `b.installArtifact(exe)`
- [ ] Replace `exe.run()` → `b.addRunArtifact(exe)`
- [ ] Remove all `.setTarget()` and `.setBuildMode()` calls
- [ ] Add target and optimize fields to struct literals
- [ ] Test build configuration works

#### 3. Error Set Syntax Changes

**Before (0.10.x):**
```zig
// Union of error sets (older syntax)
const FileError = error.FileNotFound || error.AccessDenied;
const NetworkError = error.ConnectionRefused || error.Timeout;
const AllErrors = FileError || NetworkError;
```

**After (0.11+):**
```zig
// Modern error set syntax
const FileError = error{
    FileNotFound,
    AccessDenied,
};

const NetworkError = error{
    ConnectionRefused,
    Timeout,
};

// Union with ||
const AllErrors = FileError || NetworkError;

// Or define inline
const AllErrors2 = error{
    FileNotFound,
    AccessDenied,
    ConnectionRefused,
    Timeout,
};
```

**Migration:** Replace `error.Name` with `error{ Name }` in declarations.

#### 4. Standard Library Reorganization

Several standard library modules were reorganized in 0.11:

**Before (0.10.x):**
```zig
const std = @import("std");
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const StringHashMap = std.StringHashMap;
```

**After (0.11+):**
```zig
const std = @import("std");
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;  // Still works
const StringHashMap = std.StringHashMap;  // Still works

// But some imports changed:
const fs = std.fs;  // File system APIs more organized
const net = std.net;  // Network APIs reorganized
```

**Check these areas for changes:**
- File system APIs (`std.fs`)
- Network APIs (`std.net`)
- Threading APIs (`std.Thread`)
- Testing APIs (`std.testing`)

#### 5. Complete Migration Example: HTTP Server

**Before (0.10.x with async):**
```zig
const std = @import("std");

fn handleRequest() callconv(.Async) !void {
    // Async request handler
    const data = await fetchData();
    suspend;
    return data;
}

pub fn main() !void {
    var server = try std.net.StreamServer.init(.{});
    defer server.deinit();

    try server.listen(std.net.Address.parseIp("127.0.0.1", 8080) catch unreachable);

    while (true) {
        const conn = try server.accept();
        _ = async handleConnection(conn);
    }
}

fn handleConnection(conn: std.net.StreamServer.Connection) callconv(.Async) void {
    defer conn.stream.close();
    // Handle async
}
```

**After (0.11+ with threads):**
```zig
const std = @import("std");

fn handleRequest() !void {
    // Synchronous request handler
    const data = try fetchData();
    return data;
}

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const address = try std.net.Address.parseIp("127.0.0.1", 8080);
    var server = try address.listen(.{
        .reuse_address = true,
    });
    defer server.deinit();

    std.debug.print("Server listening on 127.0.0.1:8080\n", .{});

    while (true) {
        const conn = try server.accept();
        const thread = try std.Thread.spawn(.{}, handleConnection, .{conn});
        thread.detach();
    }
}

fn handleConnection(conn: std.net.Server.Connection) void {
    defer conn.stream.close();
    handleRequest() catch |err| {
        std.debug.print("Error handling request: {}\n", .{err});
    };
}
```

### 0.12.x → 0.13.x Migration

The primary breaking change in 0.13 is the **for loop syntax**. This affects nearly all code that iterates over collections.

#### For Loop Syntax Complete Overhaul

**The Problem:** For loop syntax changed to support multiple captures and inline indexing.

#### Pattern 1: Simple Iteration (No Changes)

**Before and After (Works in both):**
```zig
const items = [_]u32{ 1, 2, 3, 4, 5 };

for (items) |item| {
    std.debug.print("{}\n", .{item});
}
```

✅ This pattern works in both 0.12 and 0.13.

#### Pattern 2: Iteration with Index

**Before (0.12.x):**
```zig
const items = [_]u32{ 1, 2, 3, 4, 5 };

// Required separate index variable
var i: usize = 0;
for (items) |item| {
    std.debug.print("{}: {}\n", .{i, item});
    i += 1;
}

// Or use while loop
var i: usize = 0;
while (i < items.len) : (i += 1) {
    std.debug.print("{}: {}\n", .{i, items[i]});
}
```

**After (0.13+):**
```zig
const items = [_]u32{ 1, 2, 3, 4, 5 };

// Inline index enumeration with 0..
for (items, 0..) |item, i| {
    std.debug.print("{}: {}\n", .{i, item});
}

// Or start from different index
for (items, 5..) |item, i| {
    std.debug.print("{}: {}\n", .{i, item});  // i starts at 5
}
```

**Migration Steps:**

1. Find all for loops with separate index variables
2. Replace with inline index capture: `for (items, 0..) |item, i|`
3. Remove manual index increment (`i += 1`)
4. Test thoroughly - off-by-one errors common

#### Pattern 3: Iterating Multiple Arrays

**Before (0.12.x):**
```zig
const names = [_][]const u8{ "Alice", "Bob", "Charlie" };
const ages = [_]u32{ 25, 30, 35 };

// Required separate index or manual zip
var i: usize = 0;
for (names) |name| {
    std.debug.print("{s} is {} years old\n", .{name, ages[i]});
    i += 1;
}
```

**After (0.13+):**
```zig
const names = [_][]const u8{ "Alice", "Bob", "Charlie" };
const ages = [_]u32{ 25, 30, 35 };

// Direct multi-array iteration
for (names, ages) |name, age| {
    std.debug.print("{s} is {} years old\n", .{name, age});
}

// Can also add index
for (names, ages, 0..) |name, age, i| {
    std.debug.print("{}: {s} is {} years old\n", .{i, name, age});
}
```

**Requirements:**
- All arrays must have same length
- Runtime assertion if lengths differ
- More efficient than manual indexing

#### Pattern 4: Nested Loops with Indices

**Before (0.12.x):**
```zig
const matrix = [_][3]u32{
    [_]u32{ 1, 2, 3 },
    [_]u32{ 4, 5, 6 },
    [_]u32{ 7, 8, 9 },
};

var row_idx: usize = 0;
for (matrix) |row| {
    var col_idx: usize = 0;
    for (row) |cell| {
        std.debug.print("[{}][{}] = {}\n", .{row_idx, col_idx, cell});
        col_idx += 1;
    }
    row_idx += 1;
}
```

**After (0.13+):**
```zig
const matrix = [_][3]u32{
    [_]u32{ 1, 2, 3 },
    [_]u32{ 4, 5, 6 },
    [_]u32{ 7, 8, 9 },
};

for (matrix, 0..) |row, row_idx| {
    for (row, 0..) |cell, col_idx| {
        std.debug.print("[{}][{}] = {}\n", .{row_idx, col_idx, cell});
    }
}
```

#### Pattern 5: Slices and Ranges

**Before (0.12.x):**
```zig
const data = [_]u32{ 10, 20, 30, 40, 50 };
const slice = data[1..4];  // [20, 30, 40]

// Needed to calculate original index manually
var i: usize = 1;  // Start offset
for (slice) |value| {
    std.debug.print("data[{}] = {}\n", .{i, value});
    i += 1;
}
```

**After (0.13+):**
```zig
const data = [_]u32{ 10, 20, 30, 40, 50 };
const slice = data[1..4];  // [20, 30, 40]

// Index is relative to slice
for (slice, 0..) |value, i| {
    std.debug.print("slice[{}] = {}\n", .{i, value});  // i: 0, 1, 2
}

// Or start from original index
for (slice, 1..) |value, i| {
    std.debug.print("data[{}] = {}\n", .{i, value});  // i: 1, 2, 3
}
```

#### Pattern 6: Reverse Iteration

**Before (0.12.x):**
```zig
const items = [_]u32{ 1, 2, 3, 4, 5 };

// Manual reverse iteration
var i: usize = items.len;
while (i > 0) {
    i -= 1;
    std.debug.print("{}\n", .{items[i]});
}
```

**After (0.13+):**
```zig
const items = [_]u32{ 1, 2, 3, 4, 5 };

// Still need manual reverse (no built-in reverse iterator)
var i: usize = items.len;
while (i > 0) {
    i -= 1;
    std.debug.print("{}\n", .{items[i]});
}

// Or use std.mem.reverse first
const reversed = std.mem.reverse(u32, &items);
for (reversed) |item| {
    std.debug.print("{}\n", .{item});
}
```

Note: 0.13 doesn't add reverse iteration syntax, still need manual approach.

#### Error Messages When Using Old Syntax in 0.13+

**Common Error 1:**
```
error: for expects at most 2 capture groups, found 3
```
**Cause:** Trying to use old-style separate index variable or incorrect syntax
**Fix:** Use inline index: `for (items, 0..) |item, i|`

**Common Error 2:**
```
error: for loop index must be an integer range
```
**Cause:** Incorrect index syntax, forgot `..` after number
**Fix:** Change `for (items, 0)` to `for (items, 0..)`

#### Migration Checklist for 0.12 → 0.13

- [ ] Find all for loops with manual index variables
  - Search for: `var i: usize = 0;` followed by `for`
  - Search for: `i += 1` inside for loops
- [ ] Replace with inline index: `for (items, 0..) |item, i|`
- [ ] Find all parallel iteration patterns (separate index for multiple arrays)
- [ ] Replace with multi-array syntax: `for (array1, array2) |a, b|`
- [ ] Check nested loops with indices
- [ ] Test all iteration bounds carefully
- [ ] Watch for off-by-one errors
- [ ] Update any documentation/comments about iteration

### 0.13.x → 0.14.x → 0.15.x Migration

The 0.13 → 0.15 progression had relatively minor breaking changes compared to 0.10 → 0.11 or 0.12 → 0.13. Most changes were refinements and additions.

#### Standard Library Refinements

**Some APIs became more consistent:**

**0.13 → 0.14 Changes:**
```zig
// Error handling improvements
// More consistent error returns across stdlib

// Before (0.13): Some functions returned different error sets
const file = try std.fs.cwd().openFile("test.txt", .{});

// After (0.14): Error sets more consistent and documented
const file = try std.fs.cwd().openFile("test.txt", .{});
// Same API, better error documentation
```

**0.14 → 0.15 Changes:**
```zig
// Minor API refinements
// Better type inference in many cases

// Some deprecated functions removed
// Check compiler warnings in 0.14 for deprecated APIs
```

#### Build System Refinements

**Minor improvements to build API (0.13-0.15):**

```zig
// 0.13-0.14: Initial modern API
const exe = b.addExecutable(.{
    .name = "myapp",
    .root_source_file = b.path("src/main.zig"),
    .target = target,
    .optimize = optimize,
});

// 0.15: Same API, better error messages
// No significant breaking changes
const exe = b.addExecutable(.{
    .name = "myapp",
    .root_source_file = b.path("src/main.zig"),
    .target = target,
    .optimize = optimize,
});

// New additions in 0.15 (optional):
// - Better module system support
// - Enhanced dependency management
// - Improved cross-compilation options
```

#### Package Manager Enhancements

**Build.zig.zon improvements (0.14-0.15):**

```zig
// 0.13-0.14 build.zig.zon
.{
    .name = "myproject",
    .version = "0.1.0",
    .minimum_zig_version = "0.13.0",

    .dependencies = .{
        .somelib = .{
            .url = "https://example.com/lib.tar.gz",
            .hash = "1234...",
        },
    },
}

// 0.15 build.zig.zon (enhanced)
.{
    .name = "myproject",
    .version = "0.1.0",
    .minimum_zig_version = "0.15.0",

    .dependencies = .{
        .somelib = .{
            .url = "https://example.com/lib.tar.gz",
            .hash = "1234...",
        },
    },

    // Better path handling and error reporting
}
```

#### Migration Recommendations 0.13 → 0.15

**Quick Check:**
1. Update `minimum_zig_version` in build.zig.zon
2. Run `zig build` - check for deprecation warnings
3. Update any deprecated APIs found
4. Test thoroughly
5. Review standard library changes in release notes

**Most 0.13 code works in 0.14 and 0.15 with minimal changes.**

## Breaking Changes Catalog

### Async/Await (0.10 → 0.11)

| Feature | 0.10 and Earlier | 0.11+ | Status |
|---------|------------------|-------|--------|
| Async functions | `fn foo() callconv(.Async)` | Not available | Removed |
| Await keyword | `await frame` | Not available | Removed |
| Suspend keyword | `suspend` | Not available | Removed |
| @Frame builtin | `@Frame(funcName)` | Not available | Removed |
| Async frame allocation | Yes | No | Removed |
| Event loop | Built-in | Manual (threads) | Redesigned |
| Concurrency model | Async/await | Threads | Changed |

**Migration:** Use `std.Thread` for concurrency.

### Build System API (0.10 → 0.11)

| API | 0.10 | 0.11+ | Migration |
|-----|------|-------|-----------|
| Builder type | `*std.build.Builder` | `*std.Build` | Change type |
| Build mode | `standardReleaseOptions()` | `standardOptimizeOption(.{})` | Different method |
| Add executable | `addExecutable("name", "file")` | `addExecutable(.{ .name = "name", .root_source_file = b.path("file") })` | Struct literal |
| Add library | `addStaticLibrary("name", "file")` | `addStaticLibrary(.{ .name = "name", .root_source_file = b.path("file") })` | Struct literal |
| Add test | `addTest("file")` | `addTest(.{ .root_source_file = b.path("file") })` | Struct literal |
| Install artifact | `exe.install()` | `b.installArtifact(exe)` | Different method |
| Run artifact | `exe.run()` | `b.addRunArtifact(exe)` | Different method |
| File paths | `"src/main.zig"` | `b.path("src/main.zig")` | Must wrap |
| Set target | `exe.setTarget(target)` | Pass in `.target` field | No setters |
| Set mode | `exe.setBuildMode(mode)` | Pass in `.optimize` field | No setters |

### For Loop Syntax (0.12 → 0.13)

| Pattern | 0.12 | 0.13+ | Migration |
|---------|------|-------|-----------|
| Simple loop | `for (items) \|item\|` | `for (items) \|item\|` | No change |
| With index | Manual `i` variable | `for (items, 0..) \|item, i\|` | Use inline index |
| Multiple arrays | Manual index | `for (a, b) \|x, y\|` | Multi-capture |
| Index + multiple | Very manual | `for (a, b, 0..) \|x, y, i\|` | Multi-capture with index |
| Custom start index | `var i = 5;` | `for (items, 5..) \|item, i\|` | Inline with offset |

### Error Set Syntax (0.10 → 0.11)

| Syntax | 0.10 | 0.11+ | Notes |
|--------|------|-------|-------|
| Single error | `error.Name` | `error{ Name }` | Brace syntax |
| Error set | `error.A \|\| error.B` | `error{ A, B }` | Combined in braces |
| Union | `ErrorSetA \|\| ErrorSetB` | `ErrorSetA \|\| ErrorSetB` | No change |

## Standard Library API Changes

### File System APIs (0.10 → 0.11+)

**Opening Files:**

```zig
// 0.10
const file = try std.fs.cwd().openFile("test.txt", .{});

// 0.11+
const file = try std.fs.cwd().openFile("test.txt", .{
    .mode = .read_only,
});
// More explicit options
```

**Creating Directories:**

```zig
// 0.10
try std.fs.cwd().makeDir("newdir");

// 0.11+
try std.fs.cwd().makeDir("newdir");
// No change, but error handling improved
```

### Memory Allocation (0.10 → 0.11+)

**Allocator API:**

```zig
// 0.10
var gpa = std.heap.GeneralPurposeAllocator(.{}){};
defer _ = gpa.deinit();
const allocator = &gpa.allocator;

// 0.11+
var gpa = std.heap.GeneralPurposeAllocator(.{}){};
defer _ = gpa.deinit();
const allocator = gpa.allocator();
// Changed from field to method
```

### Testing API (0.10 → 0.11+)

**Test declarations:**

```zig
// Both 0.10 and 0.11+ (no change)
const std = @import("std");
const testing = std.testing;

test "basic test" {
    try testing.expectEqual(42, 42);
}
```

Testing API mostly stable across versions.

### Network APIs (0.10 → 0.11+)

**TCP Server:**

```zig
// 0.10
var server = try std.net.StreamServer.init(.{});
try server.listen(address);

// 0.11+
var server = try address.listen(.{
    .reuse_address = true,
});
// More direct API
```

### Thread APIs (0.11+)

**Thread creation:**

```zig
// 0.11+
const thread = try std.Thread.spawn(.{}, myFunction, .{arg1, arg2});
const result = try thread.join();

// Detached threads
const thread = try std.Thread.spawn(.{}, myFunction, .{});
thread.detach();
```

Threads are the primary concurrency mechanism in 0.11+ (replacing async/await).

## Error Message Translations

Understanding error messages across versions helps debug version-specific issues.

### Build System Errors

**Error:** `error: expected type '*std.Build', found '*std.build.Builder'`

**Meaning:** Using 0.10 build.zig with 0.11+ compiler

**Fix:**
```zig
// Change this (0.10):
pub fn build(b: *std.build.Builder) void {

// To this (0.11+):
pub fn build(b: *std.Build) void {
```

---

**Error:** `error: no field named 'install' in type '*Build.Step.Compile'`

**Meaning:** Using 0.10 install syntax with 0.11+ compiler

**Fix:**
```zig
// Change this (0.10):
exe.install();

// To this (0.11+):
b.installArtifact(exe);
```

---

**Error:** `error: expected struct literal, found string`

**Meaning:** Using 0.10 addExecutable syntax with 0.11+ compiler

**Fix:**
```zig
// Change this (0.10):
const exe = b.addExecutable("myapp", "src/main.zig");

// To this (0.11+):
const exe = b.addExecutable(.{
    .name = "myapp",
    .root_source_file = b.path("src/main.zig"),
    .target = target,
    .optimize = optimize,
});
```

---

**Error:** `error: no method named 'path' in type '*std.Build'`

**Meaning:** Using 0.11+ syntax with 0.10 compiler (backwards)

**Fix:** Upgrade to Zig 0.11+ or use older syntax

### For Loop Errors

**Error:** `error: for expects at most 2 capture groups, found 3`

**Meaning:** Using incorrect for loop syntax in 0.13+

**Fix:**
```zig
// This is wrong:
for (items) |item, i| {  // Only 2 captures but no index source

// This is right:
for (items, 0..) |item, i| {  // Index source provided
```

---

**Error:** `error: for loop index must be an integer range`

**Meaning:** Forgot `..` in index specification (0.13+)

**Fix:**
```zig
// Change this:
for (items, 0) |item, i| {

// To this:
for (items, 0..) |item, i| {
```

---

**Error:** `error: all for loop ranges must have the same length`

**Meaning:** Multiple arrays with different lengths in 0.13+ multi-array iteration

**Fix:**
```zig
// Ensure all arrays have same length
const a = [_]u32{ 1, 2, 3 };
const b = [_]u32{ 4, 5, 6 };  // Same length as a
const c = [_]u32{ 7, 8, 9 };  // Same length as a and b

for (a, b, c) |x, y, z| {
    // OK
}
```

### Async Errors (Using 0.10 code in 0.11+)

**Error:** `error: 'async' is not a valid keyword`

**Meaning:** Async/await not available in 0.11+

**Fix:** Rewrite using threads or synchronous code

---

**Error:** `error: 'await' is not a valid keyword`

**Meaning:** Async/await not available in 0.11+

**Fix:** Rewrite using threads or synchronous code

---

**Error:** `error: 'suspend' is not a valid keyword`

**Meaning:** Async/await not available in 0.11+

**Fix:** Rewrite using threads or synchronous code

### Type Errors

**Error:** `error: expected type '*Allocator', found 'std.mem.Allocator'`

**Meaning:** Allocator API changed (0.10 → 0.11)

**Fix:**
```zig
// Change this (0.10):
const allocator = &gpa.allocator;

// To this (0.11+):
const allocator = gpa.allocator();
```

---

**Error:** `error: container 'std.build' has no member named 'Builder'`

**Meaning:** Using 0.10 build API with 0.11+ compiler

**Fix:** Update entire build.zig to 0.11+ syntax

## Version Detection

### Detecting Zig Version at Compile Time

**Using builtin.zig_version:**

```zig
const std = @import("std");
const builtin = @import("builtin");

pub fn main() !void {
    const version = builtin.zig_version;
    std.debug.print("Zig version: {}.{}.{}\n", .{
        version.major,
        version.minor,
        version.patch,
    });

    // Conditional compilation based on version
    if (version.minor >= 11) {
        // Use 0.11+ features
        std.debug.print("Modern Zig (0.11+)\n", .{});
    } else {
        // Use older features
        std.debug.print("Legacy Zig (0.10 or earlier)\n", .{});
    }
}
```

### Detecting Features at Compile Time

**Using @hasDecl:**

```zig
const std = @import("std");

// Detect if modern build API is available
const has_modern_build = @hasDecl(std, "Build");

// Detect if async is available (0.9-0.10)
const has_async = @hasDecl(std, "event");

pub fn main() !void {
    if (has_modern_build) {
        std.debug.print("Modern build API available (0.11+)\n", .{});
    } else {
        std.debug.print("Legacy build API (0.10-)\n", .{});
    }

    if (has_async) {
        std.debug.print("Async/await available (0.9-0.10)\n", .{});
    } else {
        std.debug.print("No async/await (0.11+ or pre-0.9)\n", .{});
    }
}
```

### Version Detection in Build.zig

```zig
const std = @import("std");
const builtin = @import("builtin");

pub fn build(b: *std.Build) void {
    // Get Zig version
    const version = builtin.zig_version;

    // Version-specific build logic
    if (version.minor >= 15) {
        // 0.15+ specific options
        std.debug.print("Building with Zig 0.15+\n", .{});
    } else if (version.minor >= 13) {
        // 0.13-0.14 specific options
        std.debug.print("Building with Zig 0.13-0.14\n", .{});
    } else if (version.minor >= 11) {
        // 0.11-0.12 specific options
        std.debug.print("Building with Zig 0.11-0.12\n", .{});
    }

    // Rest of build logic...
}
```

### Version Detection Markers for Static Analysis

**Markers for tools to detect version:**

1. **Check build.zig.zon:**
   ```zig
   .minimum_zig_version = "0.15.0"
   ```

2. **Check build.zig API:**
   - Has `*std.Build` → 0.11+
   - Has `*std.build.Builder` → 0.10-
   - Uses `b.path()` → 0.11+

3. **Check source files:**
   - Has `for (items, 0..)` → 0.13+
   - Has `async`/`await` → 0.9-0.10
   - Has `callconv(.Async)` → 0.9-0.10

4. **Run zig version:**
   ```bash
   $ zig version
   0.15.2
   ```

### Decision Tree for Version Detection

```
1. Try to run `zig version` command
   ├─ Success → Parse output, this is the definitive version
   └─ Failed → Continue to static analysis

2. Check for build.zig.zon
   ├─ Exists → Read `minimum_zig_version` field
   │   └─ Use this as minimum version (actual might be higher)
   └─ Not exists → Continue

3. Check build.zig content
   ├─ Contains `*std.Build` → 0.11+
   │   └─ Check source files for for-loop syntax
   │       ├─ Has `for (items, 0..)` → 0.13+
   │       └─ No new syntax → 0.11-0.12
   ├─ Contains `*std.build.Builder` → 0.10-
   │   └─ Check for async keywords
   │       ├─ Has `async`/`await` → 0.9-0.10
   │       └─ No async → 0.2-0.8
   └─ No build.zig → Check source files

4. Scan source files
   ├─ Has `for (items, 0..)` → 0.13+
   ├─ Has `async`/`await` → 0.9-0.10
   ├─ Modern error sets → 0.11+
   └─ No clear markers → Ask user or default to latest (0.15.2)

5. If still uncertain
   ├─ Prompt user to specify version
   ├─ Or default to current stable (0.15.2)
   └─ Or run `zig version` in project directory
```

## Cross-Version Compatibility

### Writing Code That Works Across Versions

**Strategy 1: Version Detection with Conditional Compilation**

```zig
const std = @import("std");
const builtin = @import("builtin");

pub fn doSomething() !void {
    const version = builtin.zig_version;

    if (version.minor >= 13) {
        // Use modern for loop syntax
        const items = [_]u32{ 1, 2, 3 };
        for (items, 0..) |item, i| {
            std.debug.print("{}: {}\n", .{i, item});
        }
    } else {
        // Use older syntax
        const items = [_]u32{ 1, 2, 3 };
        var i: usize = 0;
        for (items) |item| {
            std.debug.print("{}: {}\n", .{i, item});
            i += 1;
        }
    }
}
```

**Strategy 2: Feature Detection**

```zig
const std = @import("std");

// Detect features, not versions
const has_modern_build = @hasDecl(std, "Build");
const has_async = @hasDecl(std, "event");

pub fn buildCompat(b: anytype) void {
    if (has_modern_build) {
        // Modern build API
        const exe = b.addExecutable(.{
            .name = "app",
            .root_source_file = b.path("src/main.zig"),
        });
    } else {
        // Legacy build API
        const exe = b.addExecutable("app", "src/main.zig");
    }
}
```

**Strategy 3: Abstraction Layer**

```zig
// compat.zig - compatibility layer
const std = @import("std");
const builtin = @import("builtin");

/// Iterate with index, works on all versions
pub fn forEachWithIndex(
    comptime T: type,
    items: []const T,
    context: anytype,
    comptime func: fn (@TypeOf(context), usize, T) void,
) void {
    const version = builtin.zig_version;

    if (version.minor >= 13) {
        for (items, 0..) |item, i| {
            func(context, i, item);
        }
    } else {
        var i: usize = 0;
        for (items) |item| {
            func(context, i, item);
            i += 1;
        }
    }
}

// Usage:
pub fn printItem(_: void, i: usize, item: u32) void {
    std.debug.print("{}: {}\n", .{i, item});
}

pub fn main() !void {
    const items = [_]u32{ 1, 2, 3 };
    forEachWithIndex(u32, &items, {}, printItem);
}
```

**Strategy 4: Document Version Requirements**

```zig
//! This module requires Zig 0.13+ for for-loop syntax
//!
//! Version compatibility:
//! - 0.15.x: Full support
//! - 0.14.x: Full support
//! - 0.13.x: Full support
//! - 0.12.x and earlier: Not supported (for loop syntax)
//!
//! To use with older versions, see compat.zig

const std = @import("std");

// Modern code using 0.13+ features...
```

### Maintaining Multi-Version Libraries

**Recommended approaches for library authors:**

1. **Target a minimum version and document it**
   ```zig
   // build.zig.zon
   .{
       .name = "mylib",
       .version = "1.0.0",
       .minimum_zig_version = "0.13.0",  // Be explicit
   }
   ```

2. **Use feature detection, not version detection**
   - Prefer `@hasDecl()` over version checks
   - More resilient to Zig evolution

3. **Provide compatibility shims when necessary**
   ```zig
   // lib/compat.zig
   // Compatibility utilities for older Zig versions
   ```

4. **Test on multiple versions**
   - CI with multiple Zig versions
   - Document which versions are tested

5. **Semantic versioning tied to Zig versions**
   - mylib 1.x.x → Zig 0.13+
   - mylib 2.x.x → Zig 0.15+
   - Different branches for major Zig versions

### Example: Cross-Version Build.zig

```zig
// build.zig that works on 0.11, 0.12, 0.13, 0.14, 0.15
const std = @import("std");

// Use anytype for maximum compatibility
pub fn build(b: anytype) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Detect if modern API is available
    const has_modern_api = @hasDecl(@TypeOf(b.*), "addExecutable");

    if (has_modern_api) {
        // 0.11+ API
        const exe = b.addExecutable(.{
            .name = "myapp",
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        });
        b.installArtifact(exe);

        const run_cmd = b.addRunArtifact(exe);
        const run_step = b.step("run", "Run the app");
        run_step.dependOn(&run_cmd.step);
    } else {
        // 0.10- API (legacy)
        @compileError("Zig 0.10 and earlier not supported. Please upgrade to Zig 0.11+");
    }
}
```

## Summary and Recommendations

### For Project Maintainers

**Upgrading existing projects:**

1. **Determine current version:** `zig version`
2. **Plan migration path:**
   - 0.10 → 0.11: Major work (async, build system)
   - 0.12 → 0.13: Moderate work (for loops)
   - 0.13 → 0.15: Minor work (refinements)
3. **Read relevant migration guides** in this document
4. **Test incrementally** after each change
5. **Update CI/CD** to use new version
6. **Update documentation** with new version requirement

**Staying up to date:**

- Follow Zig release notes
- Test beta versions before stable release
- Keep dependencies updated
- Monitor deprecation warnings
- Plan for breaking changes

### For Library Authors

**Best practices:**

1. **Declare minimum version** in build.zig.zon
2. **Use feature detection** over version checks
3. **Test on multiple versions** in CI
4. **Document version requirements** clearly
5. **Provide migration guides** for your users
6. **Use semantic versioning** tied to Zig versions

### For New Projects

**Recommendations:**

- **Use Zig 0.15.2** (current stable) for new projects
- Avoid async/await (not available in current versions)
- Use modern for loop syntax (0.13+)
- Follow current build system patterns
- Plan for future Zig evolution

### Quick Version Selection Guide

**Choose Zig 0.15.2 if:**
- Starting a new project
- Want latest features and fixes
- No compatibility constraints

**Choose Zig 0.14.1 if:**
- Need stability with slightly older dependencies
- Ecosystem dependencies target 0.14

**Choose Zig 0.13.0 if:**
- Dependencies specifically require 0.13
- Avoiding very latest changes

**Avoid Zig 0.10.x and earlier:**
- Significant breaking changes from modern Zig
- Missing modern features
- Migration path is costly

---

**Document Version:** 2.0
**Last Updated:** 2025-01-10
**Target Zig Versions:** 0.15.2 (primary), 0.14.1, 0.13.0, 0.11.0 (reference)
**Maintainer:** Zig Programming Skill

For questions or corrections, please refer to official Zig documentation at https://ziglang.org/documentation/
