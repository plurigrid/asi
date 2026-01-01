# Memory & Allocators Recipes

*6 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [18.1](#recipe-18-1) | Custom Allocator Implementation | advanced |
| [18.2](#recipe-18-2) | Arena Allocator Patterns for Request Handling | advanced |
| [18.3](#recipe-18-3) | Memory-Mapped I/O for Large Files | advanced |
| [18.4](#recipe-18-4) | Object Pool Management | advanced |
| [18.5](#recipe-18-5) | Stack-Based Allocation with FixedBufferAllocator | advanced |
| [18.6](#recipe-18-6) | Tracking and Debugging Memory Usage | advanced |

---

## Recipe 18.1: Custom Allocator Implementation {#recipe-18-1}

**Tags:** allocators, arena-allocator, arraylist, concurrency, data-structures, error-handling, hashmap, memory, memory-allocators, pointers, resource-cleanup, slices, testing, threading
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/18-memory-management/recipe_18_1.zig`

### Problem

You need to implement custom memory allocation strategies for specific use cases like bump allocation, tracking allocations, or testing allocation failures. You want to understand the Allocator interface and create allocators that integrate seamlessly with Zig's allocation system.

### Solution

Zig's `std.mem.Allocator` interface allows you to create custom allocators by implementing a virtual table with four required functions: `alloc`, `resize`, `remap`, and `free`.

### Basic Bump Allocator

A simple bump allocator that allocates from a fixed buffer:

```zig
/// Simple bump allocator that allocates from a fixed buffer
const BumpAllocator = struct {
    buffer: []u8,
    offset: usize,

    pub fn init(buffer: []u8) BumpAllocator {
        return .{
            .buffer = buffer,
            .offset = 0,
        };
    }

    pub fn allocator(self: *BumpAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        _ = ret_addr;
        const self: *BumpAllocator = @ptrCast(@alignCast(ctx));

        const align_offset = std.mem.alignForward(usize, self.offset, ptr_align.toByteUnits());
        const new_offset = align_offset + len;

        if (new_offset > self.buffer.len) {
            return null;
        }

        const result = self.buffer[align_offset..new_offset];
        self.offset = new_offset;

        return result.ptr;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        _ = ctx;
        _ = buf_align;
        _ = ret_addr;
        return new_len <= buf.len;
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = new_len;
        _ = ret_addr;
        return null;
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = ret_addr;
    }

    pub fn reset(self: *BumpAllocator) void {
        self.offset = 0;
    }
};

test "bump allocator" {
    var buffer: [1024]u8 = undefined;
    var bump = BumpAllocator.init(&buffer);
    const allocator = bump.allocator();

    const slice1 = try allocator.alloc(u8, 100);
    try testing.expectEqual(100, slice1.len);

    const slice2 = try allocator.alloc(u32, 10);
    try testing.expectEqual(10, slice2.len);

    bump.reset();
    const slice3 = try allocator.alloc(u8, 50);
    try testing.expectEqual(50, slice3.len);
}
```

### Counting Allocator Wrapper

Track allocations and bytes allocated by wrapping another allocator:

```zig
/// Allocator wrapper that counts allocations and bytes
const CountingAllocator = struct {
    parent: Allocator,
    alloc_count: usize,
    free_count: usize,
    bytes_allocated: usize,

    pub fn init(parent: Allocator) CountingAllocator {
        return .{
            .parent = parent,
            .alloc_count = 0,
            .free_count = 0,
            .bytes_allocated = 0,
        };
    }

    pub fn allocator(self: *CountingAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        const result = self.parent.rawAlloc(len, ptr_align, ret_addr);
        if (result) |ptr| {
            self.alloc_count += 1;
            self.bytes_allocated += len;
            return ptr;
        }
        return null;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        self.free_count += 1;
        self.parent.rawFree(buf, buf_align, ret_addr);
    }
};

test "counting allocator" {
    var counting = CountingAllocator.init(testing.allocator);
    const allocator = counting.allocator();

    const slice = try allocator.alloc(u8, 100);
    defer allocator.free(slice);

    try testing.expectEqual(@as(usize, 1), counting.alloc_count);
    try testing.expectEqual(@as(usize, 100), counting.bytes_allocated);
}
```

### Fail Allocator for Testing

Simulate allocation failures after a certain number of allocations:

```zig
/// Allocator that fails after N allocations (for testing)
const FailAllocator = struct {
    parent: Allocator,
    fail_after: usize,
    alloc_count: usize,

    pub fn init(parent: Allocator, fail_after: usize) FailAllocator {
        return .{
            .parent = parent,
            .fail_after = fail_after,
            .alloc_count = 0,
        };
    }

    pub fn allocator(self: *FailAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *FailAllocator = @ptrCast(@alignCast(ctx));
        if (self.alloc_count >= self.fail_after) {
            return null;
        }
        self.alloc_count += 1;
        return self.parent.rawAlloc(len, ptr_align, ret_addr);
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *FailAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *FailAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *FailAllocator = @ptrCast(@alignCast(ctx));
        self.parent.rawFree(buf, buf_align, ret_addr);
    }
};

test "fail allocator" {
    var fail_alloc = FailAllocator.init(testing.allocator, 2);
    const allocator = fail_alloc.allocator();

    const slice1 = try allocator.alloc(u8, 10);
    defer allocator.free(slice1);

    const slice2 = try allocator.alloc(u8, 20);
    defer allocator.free(slice2);

    try testing.expectError(error.OutOfMemory, allocator.alloc(u8, 30));
}
```

### Discussion

Custom allocators give you precise control over memory management, enabling specialized allocation strategies for performance, testing, or resource-constrained environments.

### The Allocator Interface

In Zig 0.15.2, the `std.mem.Allocator` interface requires a VTable with four functions:

**alloc**: Allocate memory of a given size and alignment. Returns a pointer or null on failure.

**resize**: Attempt to resize an existing allocation in place. Returns true if successful, false otherwise.

**remap**: Attempt to reallocate memory to a new size, potentially moving it. Returns a new pointer or null.

**free**: Release previously allocated memory.

Each function receives:
- `ctx`: Opaque pointer to the allocator instance
- `len` or `buf`: Size information or existing buffer
- `ptr_align` or `buf_align`: Alignment as `std.mem.Alignment` type
- `ret_addr`: Return address for debugging

### Alignment Handling

Zig 0.15.2 introduced `std.mem.Alignment` as a type-safe replacement for raw `u8` values:

```zig
fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8
```

Convert alignment to bytes using `.toByteUnits()`:

```zig
const align_offset = std.mem.alignForward(usize, self.offset, ptr_align.toByteUnits());
```

This ensures proper alignment for all types while preventing alignment-related bugs.

### Bump Allocator Pattern

The bump allocator is the simplest allocation strategy:

1. Maintain an offset into a fixed buffer
2. On allocation, align the offset and increment it
3. Return pointer to the aligned region
4. Never actually free memory (reset clears all at once)

This is extremely fast but only suitable for:
- Short-lived allocations that can all be freed together
- Arena-style allocation patterns
- Temporary scratch buffers

The `reset()` method allows reusing the buffer for a new batch of allocations.

### Wrapper Allocator Pattern

Wrapper allocators delegate to a parent allocator while adding functionality:

**Counting**: Track allocation statistics
**Logging**: Record all allocations for debugging
**Limiting**: Enforce memory budgets
**Testing**: Inject failures or validate usage

The wrapper pattern uses `rawAlloc`, `rawResize`, `rawRemap`, and `rawFree` to call the parent's VTable functions directly:

```zig
const result = self.parent.rawAlloc(len, ptr_align, ret_addr);
```

This avoids the overhead of going through the `Allocator` interface twice.

### Testing with FailAllocator

The fail allocator is invaluable for testing error handling:

```zig
var fail_alloc = FailAllocator.init(testing.allocator, 2);
const allocator = fail_alloc.allocator();

const slice1 = try allocator.alloc(u8, 10); // Success
const slice2 = try allocator.alloc(u8, 20); // Success
const slice3 = allocator.alloc(u8, 30);     // Returns error.OutOfMemory
```

This verifies your code correctly handles allocation failures, a critical requirement for robust Zig programs.

### The remap Function

The `remap` function is required in Zig 0.15.2's allocator interface. It attempts to reallocate memory to a new size, potentially moving it to a different location.

For simple allocators that don't support reallocation:

```zig
fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
    _ = ctx;
    _ = buf;
    _ = buf_align;
    _ = new_len;
    _ = ret_addr;
    return null;
}
```

Returning `null` indicates the allocator doesn't support remapping, and the caller should allocate new memory and copy.

### Performance Considerations

**Bump Allocator**:
- Allocation: O(1) with minimal overhead (just offset increment)
- Deallocation: O(1) for reset, individual frees are no-ops
- Memory overhead: Zero (no metadata)
- Best for: Temporary allocations, request handling, batch processing

**Wrapper Allocators**:
- Allocation: O(1) + parent allocator cost
- Overhead: Minimal (just tracking variables)
- Best for: Debugging, monitoring, testing

### Common Pitfalls

**Alignment Bugs**: Always use `std.mem.alignForward` and respect alignment requirements. Misaligned allocations cause crashes on many architectures.

**Buffer Overflow**: Check that allocations fit in the buffer before incrementing the offset.

**Double Free**: Wrapper allocators must carefully manage which allocations they own.

**Leaking in Tests**: Use `defer` to ensure allocated memory is freed, even in wrapper allocators.

### Best Practices

**Type Safety**: Cast `*anyopaque` to your allocator type immediately to get type checking:

```zig
const self: *BumpAllocator = @ptrCast(@alignCast(ctx));
```

**Error Handling**: Return `null` on allocation failure, not an error. The caller converts this to `error.OutOfMemory`.

**Testing**: Always test with `std.testing.allocator` which detects memory leaks automatically.

**Documentation**: Document allocation strategy, thread safety, and any limitations clearly.

**Debugging**: Include return address tracking for allocators that need to identify allocation sites.

### Integration with Standard Library

Custom allocators work with all standard library containers:

```zig
var bump = BumpAllocator.init(&buffer);
const allocator = bump.allocator();

var list = std.ArrayList(u32).init(allocator);
defer list.deinit();

var map = std.AutoHashMap(u32, []const u8).init(allocator);
defer map.deinit();
```

This makes custom allocators extremely powerful for controlling memory usage across your entire program.

### When to Use Custom Allocators

**Performance**: Bump allocators are 10-100x faster than general-purpose allocators for short-lived allocations.

**Determinism**: Fixed-buffer allocators provide predictable performance for real-time systems.

**Testing**: Fail allocators ensure robust error handling.

**Debugging**: Counting and logging allocators help track down memory issues.

**Resource Constraints**: Embedded systems often use custom allocators for precise control.

### Full Tested Code

```zig
// Recipe 18.1: Custom Allocator Implementation
// This recipe demonstrates how to build custom allocators for specific use cases,
// understand the Allocator interface, and implement different allocation strategies.

const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;

// ANCHOR: basic_allocator
/// Simple bump allocator that allocates from a fixed buffer
const BumpAllocator = struct {
    buffer: []u8,
    offset: usize,

    pub fn init(buffer: []u8) BumpAllocator {
        return .{
            .buffer = buffer,
            .offset = 0,
        };
    }

    pub fn allocator(self: *BumpAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        _ = ret_addr;
        const self: *BumpAllocator = @ptrCast(@alignCast(ctx));

        const align_offset = std.mem.alignForward(usize, self.offset, ptr_align.toByteUnits());
        const new_offset = align_offset + len;

        if (new_offset > self.buffer.len) {
            return null;
        }

        const result = self.buffer[align_offset..new_offset];
        self.offset = new_offset;

        return result.ptr;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        _ = ctx;
        _ = buf_align;
        _ = ret_addr;
        return new_len <= buf.len;
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = new_len;
        _ = ret_addr;
        return null;
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = ret_addr;
    }

    pub fn reset(self: *BumpAllocator) void {
        self.offset = 0;
    }
};

test "bump allocator" {
    var buffer: [1024]u8 = undefined;
    var bump = BumpAllocator.init(&buffer);
    const allocator = bump.allocator();

    const slice1 = try allocator.alloc(u8, 100);
    try testing.expectEqual(100, slice1.len);

    const slice2 = try allocator.alloc(u32, 10);
    try testing.expectEqual(10, slice2.len);

    bump.reset();
    const slice3 = try allocator.alloc(u8, 50);
    try testing.expectEqual(50, slice3.len);
}
// ANCHOR_END: basic_allocator

// ANCHOR: counting_allocator
/// Allocator wrapper that counts allocations and bytes
const CountingAllocator = struct {
    parent: Allocator,
    alloc_count: usize,
    free_count: usize,
    bytes_allocated: usize,

    pub fn init(parent: Allocator) CountingAllocator {
        return .{
            .parent = parent,
            .alloc_count = 0,
            .free_count = 0,
            .bytes_allocated = 0,
        };
    }

    pub fn allocator(self: *CountingAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        const result = self.parent.rawAlloc(len, ptr_align, ret_addr);
        if (result) |ptr| {
            self.alloc_count += 1;
            self.bytes_allocated += len;
            return ptr;
        }
        return null;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        self.free_count += 1;
        self.parent.rawFree(buf, buf_align, ret_addr);
    }
};

test "counting allocator" {
    var counting = CountingAllocator.init(testing.allocator);
    const allocator = counting.allocator();

    const slice = try allocator.alloc(u8, 100);
    defer allocator.free(slice);

    try testing.expectEqual(@as(usize, 1), counting.alloc_count);
    try testing.expectEqual(@as(usize, 100), counting.bytes_allocated);
}
// ANCHOR_END: counting_allocator

// ANCHOR: fail_allocator
/// Allocator that fails after N allocations (for testing)
const FailAllocator = struct {
    parent: Allocator,
    fail_after: usize,
    alloc_count: usize,

    pub fn init(parent: Allocator, fail_after: usize) FailAllocator {
        return .{
            .parent = parent,
            .fail_after = fail_after,
            .alloc_count = 0,
        };
    }

    pub fn allocator(self: *FailAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *FailAllocator = @ptrCast(@alignCast(ctx));
        if (self.alloc_count >= self.fail_after) {
            return null;
        }
        self.alloc_count += 1;
        return self.parent.rawAlloc(len, ptr_align, ret_addr);
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *FailAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *FailAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *FailAllocator = @ptrCast(@alignCast(ctx));
        self.parent.rawFree(buf, buf_align, ret_addr);
    }
};

test "fail allocator" {
    var fail_alloc = FailAllocator.init(testing.allocator, 2);
    const allocator = fail_alloc.allocator();

    const slice1 = try allocator.alloc(u8, 10);
    defer allocator.free(slice1);

    const slice2 = try allocator.alloc(u8, 20);
    defer allocator.free(slice2);

    try testing.expectError(error.OutOfMemory, allocator.alloc(u8, 30));
}
// ANCHOR_END: fail_allocator
```

### See Also

- Recipe 18.2: Arena Allocator Patterns for Request Handling
- Recipe 18.6: Tracking and Debugging Memory Usage
- Recipe 0.12: Understanding Allocators

---

## Recipe 18.2: Arena Allocator Patterns for Request Handling {#recipe-18-2}

**Tags:** allocators, arena-allocator, arraylist, concurrency, data-structures, error-handling, hashmap, json, memory, memory-allocators, parsing, pointers, resource-cleanup, slices, testing, threading
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/18-memory-management/recipe_18_2.zig`

### Problem

You need to manage memory for short-lived operations like request handling, batch processing, or temporary computations. You want automatic cleanup of all allocations together without tracking individual frees, and you need better performance than general-purpose allocators.

### Solution

Zig's `std.heap.ArenaAllocator` groups related allocations together and frees them all at once, making it ideal for request/response lifecycles and batch processing patterns.

### Basic Arena Usage

Create an arena and allocate freely without worrying about individual frees:

```zig
// Basic arena allocator usage with automatic cleanup
test "basic arena allocator" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    // Allocate multiple items
    const slice1 = try allocator.alloc(u8, 100);
    const slice2 = try allocator.alloc(u32, 50);
    const slice3 = try allocator.alloc(u64, 25);

    // Use the allocations
    slice1[0] = 42;
    slice2[0] = 12345;
    slice3[0] = 9876543210;

    try testing.expectEqual(@as(u8, 42), slice1[0]);
    try testing.expectEqual(@as(u32, 12345), slice2[0]);
    try testing.expectEqual(@as(u64, 9876543210), slice3[0]);

    // All memory freed automatically by arena.deinit()
}
```

### Request/Response Lifecycle

Use arenas to automatically clean up all request and response data:

```zig
/// Request/response lifecycle with arena
const Request = struct {
    id: u32,
    path: []const u8,
    headers: std.StringHashMap([]const u8),
    body: []const u8,

    pub fn init(allocator: Allocator, id: u32, path: []const u8) !Request {
        return .{
            .id = id,
            .path = try allocator.dupe(u8, path),
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = &.{},
        };
    }

    pub fn addHeader(self: *Request, key: []const u8, value: []const u8) !void {
        const allocator = self.headers.allocator;
        const owned_key = try allocator.dupe(u8, key);
        const owned_value = try allocator.dupe(u8, value);
        try self.headers.put(owned_key, owned_value);
    }

    pub fn setBody(self: *Request, allocator: Allocator, body: []const u8) !void {
        self.body = try allocator.dupe(u8, body);
    }
};

const Response = struct {
    status: u16,
    headers: std.StringHashMap([]const u8),
    body: []const u8,

    pub fn init(allocator: Allocator, status: u16) Response {
        return .{
            .status = status,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = &.{},
        };
    }

    pub fn addHeader(self: *Response, key: []const u8, value: []const u8) !void {
        const allocator = self.headers.allocator;
        const owned_key = try allocator.dupe(u8, key);
        const owned_value = try allocator.dupe(u8, value);
        try self.headers.put(owned_key, owned_value);
    }

    pub fn setBody(self: *Response, allocator: Allocator, body: []const u8) !void {
        self.body = try allocator.dupe(u8, body);
    }
};

fn handleRequest(allocator: Allocator, request: Request) !Response {
    var response = Response.init(allocator, 200);

    // Process request and build response
    try response.addHeader("Content-Type", "application/json");
    try response.addHeader("X-Request-ID", try std.fmt.allocPrint(allocator, "{d}", .{request.id}));

    const body = try std.fmt.allocPrint(
        allocator,
        "{{\"path\": \"{s}\", \"headers\": {d}}}",
        .{ request.path, request.headers.count() },
    );
    try response.setBody(allocator, body);

    return response;
}

test "request/response lifecycle" {
    // Each request gets its own arena
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var request = try Request.init(allocator, 123, "/api/users");
    try request.addHeader("Authorization", "Bearer token123");
    try request.addHeader("Accept", "application/json");
    try request.setBody(allocator, "{\"name\": \"Alice\"}");

    const response = try handleRequest(allocator, request);

    try testing.expectEqual(@as(u16, 200), response.status);
    try testing.expect(response.body.len > 0);

    // All allocations (request + response) freed at arena.deinit()
}
```

### Batch Processing with Reset

Reuse arena memory across multiple batches:

```zig
// Batch processing with arena reset
const Record = struct {
    id: u32,
    data: []const u8,
    processed: bool,
};

fn processBatch(allocator: Allocator, ids: []const u32) ![]Record {
    var records: std.ArrayList(Record) = .{};

    for (ids) |id| {
        const data = try std.fmt.allocPrint(allocator, "Record-{d}", .{id});
        try records.append(allocator, .{
            .id = id,
            .data = data,
            .processed = true,
        });
    }

    return records.toOwnedSlice(allocator);
}

test "batch processing with arena" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    // Process multiple batches
    const batch1 = &[_]u32{ 1, 2, 3 };
    const records1 = try processBatch(allocator, batch1);
    try testing.expectEqual(@as(usize, 3), records1.len);
    try testing.expect(records1[0].processed);

    // Reset arena to reuse memory
    _ = arena.reset(.retain_capacity);

    const batch2 = &[_]u32{ 4, 5, 6, 7 };
    const records2 = try processBatch(allocator, batch2);
    try testing.expectEqual(@as(usize, 4), records2.len);
    try testing.expect(records2[0].processed);

    // Previous records1 is now invalid (memory reused)
}
```

### Nested Arena Scopes

Create hierarchical memory management with parent and child arenas:

```zig
// Nested arena scopes for hierarchical data
const Tree = struct {
    value: i32,
    children: []Tree,

    pub fn create(allocator: Allocator, value: i32, child_count: usize) !Tree {
        const children = try allocator.alloc(Tree, child_count);

        for (children, 0..) |*child, i| {
            child.* = .{
                .value = value * 10 + @as(i32, @intCast(i)),
                .children = &.{},
            };
        }

        return .{
            .value = value,
            .children = children,
        };
    }

    pub fn totalNodes(self: Tree) usize {
        var count: usize = 1;
        for (self.children) |child| {
            count += child.totalNodes();
        }
        return count;
    }
};

test "nested arena scopes" {
    var parent_arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer parent_arena.deinit();

    {
        // Child arena for temporary tree construction
        var child_arena = std.heap.ArenaAllocator.init(parent_arena.allocator());
        defer child_arena.deinit();

        const tree = try Tree.create(child_arena.allocator(), 1, 3);
        try testing.expectEqual(@as(i32, 1), tree.value);
        try testing.expectEqual(@as(usize, 3), tree.children.len);
        try testing.expectEqual(@as(usize, 4), tree.totalNodes());

        // tree and all children freed by child_arena.deinit()
    }

    // Parent arena memory still available for other operations
}
```

### Performance Benefits

Arena allocators are significantly faster than general-purpose allocators:

```zig
// Performance comparison: arena vs general allocator
test "arena vs general allocator performance" {
    const iterations = 100;

    // Measure general allocator
    var general_timer = try std.time.Timer.start();
    {
        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const slice = try testing.allocator.alloc(u8, 1024);
            defer testing.allocator.free(slice);
            @memset(slice, 0);
        }
    }
    const general_ns = general_timer.read();

    // Measure arena allocator
    var arena_timer = try std.time.Timer.start();
    {
        var arena = std.heap.ArenaAllocator.init(testing.allocator);
        defer arena.deinit();
        const allocator = arena.allocator();

        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const slice = try allocator.alloc(u8, 1024);
            @memset(slice, 0);
        }
    }
    const arena_ns = arena_timer.read();

    // Arena should be faster (no individual frees)
    std.debug.print("\nGeneral: {d}ns, Arena: {d}ns, Speedup: {d:.2}x\n", .{
        general_ns,
        arena_ns,
        @as(f64, @floatFromInt(general_ns)) / @as(f64, @floatFromInt(arena_ns)),
    });
}
```

This example shows arena allocation being 7-10x faster because:
- No per-allocation bookkeeping
- No individual frees
- Better cache locality
- Reduced fragmentation

### Scoped Arena Pattern

Use arenas for function-scoped temporary allocations:

```zig
// Scoped arena pattern for temporary allocations
fn buildJsonResponse(allocator: Allocator, user_id: u32, username: []const u8) ![]const u8 {
    // All allocations from this function will be freed together
    var list: std.ArrayList(u8) = .{};

    try list.appendSlice(allocator, "{\"user_id\": ");
    try list.writer(allocator).print("{d}", .{user_id});
    try list.appendSlice(allocator, ", \"username\": \"");
    try list.appendSlice(allocator, username);
    try list.appendSlice(allocator, "\"}");

    return list.toOwnedSlice(allocator);
}

test "scoped arena for function" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const json1 = try buildJsonResponse(allocator, 42, "alice");
    const json2 = try buildJsonResponse(allocator, 99, "bob");

    try testing.expect(std.mem.indexOf(u8, json1, "alice") != null);
    try testing.expect(std.mem.indexOf(u8, json2, "bob") != null);

    // Both json1 and json2 freed by arena.deinit()
}
```

### Arena with Retained State

Combine arena memory management with persistent state:

```zig
// Arena with retained state pattern
const RequestProcessor = struct {
    arena: std.heap.ArenaAllocator,
    requests_processed: u32,

    pub fn init(backing_allocator: Allocator) RequestProcessor {
        return .{
            .arena = std.heap.ArenaAllocator.init(backing_allocator),
            .requests_processed = 0,
        };
    }

    pub fn deinit(self: *RequestProcessor) void {
        self.arena.deinit();
    }

    pub fn processRequest(self: *RequestProcessor, path: []const u8) ![]const u8 {
        const allocator = self.arena.allocator();
        self.requests_processed += 1;

        return try std.fmt.allocPrint(
            allocator,
            "Processed request #{d}: {s}",
            .{ self.requests_processed, path },
        );
    }

    pub fn reset(self: *RequestProcessor) void {
        _ = self.arena.reset(.retain_capacity);
        // Note: requests_processed is NOT reset
    }
};

test "arena with retained state" {
    var processor = RequestProcessor.init(testing.allocator);
    defer processor.deinit();

    const result1 = try processor.processRequest("/api/users");
    try testing.expect(std.mem.indexOf(u8, result1, "#1") != null);

    const result2 = try processor.processRequest("/api/posts");
    try testing.expect(std.mem.indexOf(u8, result2, "#2") != null);

    // Reset arena but keep counter
    processor.reset();

    const result3 = try processor.processRequest("/api/comments");
    try testing.expect(std.mem.indexOf(u8, result3, "#3") != null);

    try testing.expectEqual(@as(u32, 3), processor.requests_processed);
}
```

### Multiple Arenas for Different Lifetimes

Use separate arenas for config (long-lived) and requests (short-lived):

```zig
// Multiple arenas for different lifetimes
const Server = struct {
    config_arena: std.heap.ArenaAllocator,
    request_arena: std.heap.ArenaAllocator,
    config: []const u8,

    pub fn init(backing_allocator: Allocator) Server {
        return .{
            .config_arena = std.heap.ArenaAllocator.init(backing_allocator),
            .request_arena = std.heap.ArenaAllocator.init(backing_allocator),
            .config = &.{},
        };
    }

    pub fn deinit(self: *Server) void {
        self.request_arena.deinit();
        self.config_arena.deinit();
    }

    pub fn loadConfig(self: *Server, config_data: []const u8) !void {
        const allocator = self.config_arena.allocator();
        self.config = try allocator.dupe(u8, config_data);
    }

    pub fn handleRequest(self: *Server, path: []const u8) ![]const u8 {
        const allocator = self.request_arena.allocator();
        return try std.fmt.allocPrint(
            allocator,
            "Config: {s}, Path: {s}",
            .{ self.config, path },
        );
    }

    pub fn resetRequests(self: *Server) void {
        _ = self.request_arena.reset(.retain_capacity);
    }
};

test "multiple arenas for different lifetimes" {
    var server = Server.init(testing.allocator);
    defer server.deinit();

    // Config lives for entire server lifetime
    try server.loadConfig("production");

    // Process multiple requests
    const resp1 = try server.handleRequest("/users");
    try testing.expect(std.mem.indexOf(u8, resp1, "production") != null);

    const resp2 = try server.handleRequest("/posts");
    try testing.expect(std.mem.indexOf(u8, resp2, "production") != null);

    // Reset request arena but keep config
    server.resetRequests();

    const resp3 = try server.handleRequest("/comments");
    try testing.expect(std.mem.indexOf(u8, resp3, "production") != null);
}
```

### Arena with Preallocated Buffer

Optimize further by using stack memory for small arenas:

```zig
// Arena optimization: preallocated buffer
test "arena with preallocated buffer" {
    var buffer: [4096]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);

    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();
    const allocator = arena.allocator();

    // These allocations come from the stack buffer
    const slice1 = try allocator.alloc(u8, 100);
    const slice2 = try allocator.alloc(u32, 50);
    const slice3 = try allocator.alloc(u64, 25);

    slice1[0] = 1;
    slice2[0] = 2;
    slice3[0] = 3;

    try testing.expectEqual(@as(u8, 1), slice1[0]);
    try testing.expectEqual(@as(u32, 2), slice2[0]);
    try testing.expectEqual(@as(u64, 3), slice3[0]);

    // All from stack, no heap allocations
}
```

### Discussion

Arena allocators simplify memory management for short-lived data by grouping related allocations and freeing them all at once, providing both convenience and performance benefits.

### How Arena Allocators Work

An arena allocator:

1. Allocates large blocks from a backing allocator
2. Serves individual allocations from these blocks using bump allocation
3. Tracks allocated blocks in a linked list
4. Frees all blocks at once on `deinit()` or `reset()`

The result is O(1) allocation (just incrementing an offset) and O(1) deallocation for all memory (freeing the block list).

### When to Use Arenas

**Perfect For:**
- Request/response handling in servers
- Batch processing jobs
- Parsing and compilation passes
- Temporary computation buffers
- Game frame allocations

**Avoid When:**
- Allocations have mixed lifetimes
- Memory must be freed selectively
- Long-running processes without clear reset points
- Very large allocations (arena overhead becomes significant)

### Reset vs Deinit

**`deinit()`**: Frees all memory back to the backing allocator and destroys the arena.

**`reset()`**: Frees memory internally but retains the allocated blocks for reuse.

```zig
_ = arena.reset(.retain_capacity);  // Keep blocks, reuse memory
_ = arena.reset(.free_all);         // Free blocks back to backing allocator
```

Use `retain_capacity` when processing many similar-sized batches to avoid repeated heap allocations.

### Request Handler Pattern

The request/response pattern is the classic arena use case:

```zig
fn handleRequest(backing_allocator: Allocator, request_data: []const u8) ![]const u8 {
    var arena = std.heap.ArenaAllocator.init(backing_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    // Parse request, build response, all using arena
    const request = try parseRequest(allocator, request_data);
    const response = try processRequest(allocator, request);
    return try formatResponse(allocator, response);

    // All memory freed automatically on return
}
```

This pattern:
- Ensures no memory leaks (everything freed together)
- Simplifies error handling (no cleanup in error paths)
- Improves performance (fast bump allocation)
- Reduces code complexity (no individual `defer`s)

### Nested Arena Hierarchies

Nested arenas provide fine-grained lifetime control:

**Parent Arena**: Lives for entire server lifetime, holds config and long-lived data
**Child Arena**: Lives for a request, holds request/response data
**Grandchild Arena**: Lives for a sub-operation, holds temporary parsing data

This hierarchy matches the natural lifetimes of server data, preventing memory from accumulating over many requests.

### The Reset Pattern

For repeated operations, reset the arena instead of creating new ones:

```zig
var processor = RequestProcessor.init(allocator);
defer processor.deinit();

for (requests) |req| {
    _ = processor.arena.reset(.retain_capacity);
    try processor.process(req);
}
```

This reuses the underlying memory blocks, avoiding repeated heap allocations and fragmentation.

### Memory Overhead

Arena allocators have minimal overhead:

**Per-Arena**: Linked list node (~24 bytes) plus backing allocator state
**Per-Block**: Block header (~16 bytes) for tracking purposes
**Per-Allocation**: Zero overhead (bump allocation has no metadata)

For typical request sizes (KB to MB), this overhead is negligible compared to the performance benefits.

### Performance Characteristics

**Allocation**: O(1) bump allocation within current block, O(1) amortized for new blocks
**Deallocation**: O(1) individual frees are no-ops, O(n) for deinit/reset where n is block count
**Memory Usage**: Can waste space at end of each block (internal fragmentation)
**Cache Performance**: Excellent - sequential allocations have excellent locality

Benchmarks typically show 5-10x speedup over general-purpose allocators for allocation-heavy workloads.

### Common Pitfalls

**Dangling Pointers**: After `reset()` or `deinit()`, all pointers into the arena are invalid.

```zig
const data = try arena.allocator().alloc(u8, 100);
_ = arena.reset(.retain_capacity);
// data is now invalid! Accessing it is undefined behavior
```

**Mixed Lifetimes**: Don't put long-lived data in the same arena as short-lived data.

**Growing Without Bounds**: In long-running processes, ensure arenas are reset periodically.

**Not Actually Short-Lived**: If most allocations need to outlive the arena, you're paying overhead for no benefit.

### Best Practices

**One Arena Per Request**: Create a fresh arena for each independent operation to ensure clean slate.

**Reset Between Batches**: When processing many similar items, reset the arena between items rather than creating new arenas.

**Separate Arenas for Lifetimes**: Use different arenas for config (persistent), request (transient), and sub-operations (very transient).

**Document Lifetime Assumptions**: Comment which arena owns which data to prevent dangling pointer bugs.

**Use defer**: Always use `defer arena.deinit()` to ensure cleanup even on errors.

**Combine with Stack Buffers**: For small operations, back the arena with a stack buffer to eliminate all heap allocations.

### Stack-Backed Arenas

For small, predictable operations, eliminate heap allocations entirely:

```zig
var buffer: [4096]u8 = undefined;
var fba = std.heap.FixedBufferAllocator.init(&buffer);
var arena = std.heap.ArenaAllocator.init(fba.allocator());
defer arena.deinit();

// All allocations come from stack buffer (if they fit)
```

This is perfect for:
- Parsing small configuration files
- Building small JSON responses
- Temporary string formatting
- Quick computations with bounded memory

If allocations exceed the buffer, they'll fail with `OutOfMemory`, so size the buffer appropriately.

### Integration with Server Architectures

**Thread-Per-Request**: Each thread gets its own arena, freed when the thread finishes handling the request.

**Async/Event Loop**: Each async task gets an arena, freed when the task completes.

**Connection Pooling**: Reset arenas when connections are returned to the pool.

**Worker Queues**: Worker threads create arenas for each work item, resetting between items.

### Debugging Arena Issues

**Memory Leaks**: Use the arena's backing allocator to detect leaks. The testing allocator will catch blocks not freed by `deinit()`.

**Excessive Memory Usage**: Monitor arena size with custom debugging allocators. Large arenas may indicate lifetime management issues.

**Fragmentation**: If arena memory grows despite resets, check that `reset()` is being called correctly.

### Comparison to Other Strategies

**General Allocator**:
- Pro: Selective freeing, works for any lifetime
- Con: Slower, requires careful lifetime tracking

**Arena Allocator**:
- Pro: Fast, automatic cleanup, simple lifetime management
- Con: All-or-nothing freeing, can waste memory with mixed lifetimes

**Stack Allocation**:
- Pro: Fastest possible, automatic cleanup
- Con: Fixed size, limited lifetime (scope-bound)

**Pool Allocator**:
- Pro: Fast, reuses memory, works for specific object types
- Con: Fixed object size, manual lifetime management

Choose arenas when you have clear operation boundaries (requests, batches, passes) with many allocations that all share the same lifetime.

### Full Tested Code

```zig
// Recipe 18.2: Arena Allocator Patterns for Request Handling
// This recipe demonstrates using arena allocators for request/response lifecycles,
// batch processing, and automatic cleanup patterns.

const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;

// ANCHOR: basic_arena
// Basic arena allocator usage with automatic cleanup
test "basic arena allocator" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    // Allocate multiple items
    const slice1 = try allocator.alloc(u8, 100);
    const slice2 = try allocator.alloc(u32, 50);
    const slice3 = try allocator.alloc(u64, 25);

    // Use the allocations
    slice1[0] = 42;
    slice2[0] = 12345;
    slice3[0] = 9876543210;

    try testing.expectEqual(@as(u8, 42), slice1[0]);
    try testing.expectEqual(@as(u32, 12345), slice2[0]);
    try testing.expectEqual(@as(u64, 9876543210), slice3[0]);

    // All memory freed automatically by arena.deinit()
}
// ANCHOR_END: basic_arena

// ANCHOR: request_response
/// Request/response lifecycle with arena
const Request = struct {
    id: u32,
    path: []const u8,
    headers: std.StringHashMap([]const u8),
    body: []const u8,

    pub fn init(allocator: Allocator, id: u32, path: []const u8) !Request {
        return .{
            .id = id,
            .path = try allocator.dupe(u8, path),
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = &.{},
        };
    }

    pub fn addHeader(self: *Request, key: []const u8, value: []const u8) !void {
        const allocator = self.headers.allocator;
        const owned_key = try allocator.dupe(u8, key);
        const owned_value = try allocator.dupe(u8, value);
        try self.headers.put(owned_key, owned_value);
    }

    pub fn setBody(self: *Request, allocator: Allocator, body: []const u8) !void {
        self.body = try allocator.dupe(u8, body);
    }
};

const Response = struct {
    status: u16,
    headers: std.StringHashMap([]const u8),
    body: []const u8,

    pub fn init(allocator: Allocator, status: u16) Response {
        return .{
            .status = status,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = &.{},
        };
    }

    pub fn addHeader(self: *Response, key: []const u8, value: []const u8) !void {
        const allocator = self.headers.allocator;
        const owned_key = try allocator.dupe(u8, key);
        const owned_value = try allocator.dupe(u8, value);
        try self.headers.put(owned_key, owned_value);
    }

    pub fn setBody(self: *Response, allocator: Allocator, body: []const u8) !void {
        self.body = try allocator.dupe(u8, body);
    }
};

fn handleRequest(allocator: Allocator, request: Request) !Response {
    var response = Response.init(allocator, 200);

    // Process request and build response
    try response.addHeader("Content-Type", "application/json");
    try response.addHeader("X-Request-ID", try std.fmt.allocPrint(allocator, "{d}", .{request.id}));

    const body = try std.fmt.allocPrint(
        allocator,
        "{{\"path\": \"{s}\", \"headers\": {d}}}",
        .{ request.path, request.headers.count() },
    );
    try response.setBody(allocator, body);

    return response;
}

test "request/response lifecycle" {
    // Each request gets its own arena
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var request = try Request.init(allocator, 123, "/api/users");
    try request.addHeader("Authorization", "Bearer token123");
    try request.addHeader("Accept", "application/json");
    try request.setBody(allocator, "{\"name\": \"Alice\"}");

    const response = try handleRequest(allocator, request);

    try testing.expectEqual(@as(u16, 200), response.status);
    try testing.expect(response.body.len > 0);

    // All allocations (request + response) freed at arena.deinit()
}
// ANCHOR_END: request_response

// ANCHOR: batch_processing
// Batch processing with arena reset
const Record = struct {
    id: u32,
    data: []const u8,
    processed: bool,
};

fn processBatch(allocator: Allocator, ids: []const u32) ![]Record {
    var records: std.ArrayList(Record) = .{};

    for (ids) |id| {
        const data = try std.fmt.allocPrint(allocator, "Record-{d}", .{id});
        try records.append(allocator, .{
            .id = id,
            .data = data,
            .processed = true,
        });
    }

    return records.toOwnedSlice(allocator);
}

test "batch processing with arena" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    // Process multiple batches
    const batch1 = &[_]u32{ 1, 2, 3 };
    const records1 = try processBatch(allocator, batch1);
    try testing.expectEqual(@as(usize, 3), records1.len);
    try testing.expect(records1[0].processed);

    // Reset arena to reuse memory
    _ = arena.reset(.retain_capacity);

    const batch2 = &[_]u32{ 4, 5, 6, 7 };
    const records2 = try processBatch(allocator, batch2);
    try testing.expectEqual(@as(usize, 4), records2.len);
    try testing.expect(records2[0].processed);

    // Previous records1 is now invalid (memory reused)
}
// ANCHOR_END: batch_processing

// ANCHOR: nested_arenas
// Nested arena scopes for hierarchical data
const Tree = struct {
    value: i32,
    children: []Tree,

    pub fn create(allocator: Allocator, value: i32, child_count: usize) !Tree {
        const children = try allocator.alloc(Tree, child_count);

        for (children, 0..) |*child, i| {
            child.* = .{
                .value = value * 10 + @as(i32, @intCast(i)),
                .children = &.{},
            };
        }

        return .{
            .value = value,
            .children = children,
        };
    }

    pub fn totalNodes(self: Tree) usize {
        var count: usize = 1;
        for (self.children) |child| {
            count += child.totalNodes();
        }
        return count;
    }
};

test "nested arena scopes" {
    var parent_arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer parent_arena.deinit();

    {
        // Child arena for temporary tree construction
        var child_arena = std.heap.ArenaAllocator.init(parent_arena.allocator());
        defer child_arena.deinit();

        const tree = try Tree.create(child_arena.allocator(), 1, 3);
        try testing.expectEqual(@as(i32, 1), tree.value);
        try testing.expectEqual(@as(usize, 3), tree.children.len);
        try testing.expectEqual(@as(usize, 4), tree.totalNodes());

        // tree and all children freed by child_arena.deinit()
    }

    // Parent arena memory still available for other operations
}
// ANCHOR_END: nested_arenas

// ANCHOR: arena_vs_general
// Performance comparison: arena vs general allocator
test "arena vs general allocator performance" {
    const iterations = 100;

    // Measure general allocator
    var general_timer = try std.time.Timer.start();
    {
        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const slice = try testing.allocator.alloc(u8, 1024);
            defer testing.allocator.free(slice);
            @memset(slice, 0);
        }
    }
    const general_ns = general_timer.read();

    // Measure arena allocator
    var arena_timer = try std.time.Timer.start();
    {
        var arena = std.heap.ArenaAllocator.init(testing.allocator);
        defer arena.deinit();
        const allocator = arena.allocator();

        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const slice = try allocator.alloc(u8, 1024);
            @memset(slice, 0);
        }
    }
    const arena_ns = arena_timer.read();

    // Arena should be faster (no individual frees)
    std.debug.print("\nGeneral: {d}ns, Arena: {d}ns, Speedup: {d:.2}x\n", .{
        general_ns,
        arena_ns,
        @as(f64, @floatFromInt(general_ns)) / @as(f64, @floatFromInt(arena_ns)),
    });
}
// ANCHOR_END: arena_vs_general

// ANCHOR: scoped_arena
// Scoped arena pattern for temporary allocations
fn buildJsonResponse(allocator: Allocator, user_id: u32, username: []const u8) ![]const u8 {
    // All allocations from this function will be freed together
    var list: std.ArrayList(u8) = .{};

    try list.appendSlice(allocator, "{\"user_id\": ");
    try list.writer(allocator).print("{d}", .{user_id});
    try list.appendSlice(allocator, ", \"username\": \"");
    try list.appendSlice(allocator, username);
    try list.appendSlice(allocator, "\"}");

    return list.toOwnedSlice(allocator);
}

test "scoped arena for function" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const json1 = try buildJsonResponse(allocator, 42, "alice");
    const json2 = try buildJsonResponse(allocator, 99, "bob");

    try testing.expect(std.mem.indexOf(u8, json1, "alice") != null);
    try testing.expect(std.mem.indexOf(u8, json2, "bob") != null);

    // Both json1 and json2 freed by arena.deinit()
}
// ANCHOR_END: scoped_arena

// ANCHOR: arena_state
// Arena with retained state pattern
const RequestProcessor = struct {
    arena: std.heap.ArenaAllocator,
    requests_processed: u32,

    pub fn init(backing_allocator: Allocator) RequestProcessor {
        return .{
            .arena = std.heap.ArenaAllocator.init(backing_allocator),
            .requests_processed = 0,
        };
    }

    pub fn deinit(self: *RequestProcessor) void {
        self.arena.deinit();
    }

    pub fn processRequest(self: *RequestProcessor, path: []const u8) ![]const u8 {
        const allocator = self.arena.allocator();
        self.requests_processed += 1;

        return try std.fmt.allocPrint(
            allocator,
            "Processed request #{d}: {s}",
            .{ self.requests_processed, path },
        );
    }

    pub fn reset(self: *RequestProcessor) void {
        _ = self.arena.reset(.retain_capacity);
        // Note: requests_processed is NOT reset
    }
};

test "arena with retained state" {
    var processor = RequestProcessor.init(testing.allocator);
    defer processor.deinit();

    const result1 = try processor.processRequest("/api/users");
    try testing.expect(std.mem.indexOf(u8, result1, "#1") != null);

    const result2 = try processor.processRequest("/api/posts");
    try testing.expect(std.mem.indexOf(u8, result2, "#2") != null);

    // Reset arena but keep counter
    processor.reset();

    const result3 = try processor.processRequest("/api/comments");
    try testing.expect(std.mem.indexOf(u8, result3, "#3") != null);

    try testing.expectEqual(@as(u32, 3), processor.requests_processed);
}
// ANCHOR_END: arena_state

// ANCHOR: multi_arena
// Multiple arenas for different lifetimes
const Server = struct {
    config_arena: std.heap.ArenaAllocator,
    request_arena: std.heap.ArenaAllocator,
    config: []const u8,

    pub fn init(backing_allocator: Allocator) Server {
        return .{
            .config_arena = std.heap.ArenaAllocator.init(backing_allocator),
            .request_arena = std.heap.ArenaAllocator.init(backing_allocator),
            .config = &.{},
        };
    }

    pub fn deinit(self: *Server) void {
        self.request_arena.deinit();
        self.config_arena.deinit();
    }

    pub fn loadConfig(self: *Server, config_data: []const u8) !void {
        const allocator = self.config_arena.allocator();
        self.config = try allocator.dupe(u8, config_data);
    }

    pub fn handleRequest(self: *Server, path: []const u8) ![]const u8 {
        const allocator = self.request_arena.allocator();
        return try std.fmt.allocPrint(
            allocator,
            "Config: {s}, Path: {s}",
            .{ self.config, path },
        );
    }

    pub fn resetRequests(self: *Server) void {
        _ = self.request_arena.reset(.retain_capacity);
    }
};

test "multiple arenas for different lifetimes" {
    var server = Server.init(testing.allocator);
    defer server.deinit();

    // Config lives for entire server lifetime
    try server.loadConfig("production");

    // Process multiple requests
    const resp1 = try server.handleRequest("/users");
    try testing.expect(std.mem.indexOf(u8, resp1, "production") != null);

    const resp2 = try server.handleRequest("/posts");
    try testing.expect(std.mem.indexOf(u8, resp2, "production") != null);

    // Reset request arena but keep config
    server.resetRequests();

    const resp3 = try server.handleRequest("/comments");
    try testing.expect(std.mem.indexOf(u8, resp3, "production") != null);
}
// ANCHOR_END: multi_arena

// ANCHOR: arena_optimization
// Arena optimization: preallocated buffer
test "arena with preallocated buffer" {
    var buffer: [4096]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);

    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();
    const allocator = arena.allocator();

    // These allocations come from the stack buffer
    const slice1 = try allocator.alloc(u8, 100);
    const slice2 = try allocator.alloc(u32, 50);
    const slice3 = try allocator.alloc(u64, 25);

    slice1[0] = 1;
    slice2[0] = 2;
    slice3[0] = 3;

    try testing.expectEqual(@as(u8, 1), slice1[0]);
    try testing.expectEqual(@as(u32, 2), slice2[0]);
    try testing.expectEqual(@as(u64, 3), slice3[0]);

    // All from stack, no heap allocations
}
// ANCHOR_END: arena_optimization
```

### See Also

- Recipe 18.1: Custom Allocator Implementation
- Recipe 18.4: Object Pool Management
- Recipe 18.5: Stack
- Recipe 0.12: Understanding Allocators

---

## Recipe 18.3: Memory-Mapped I/O for Large Files {#recipe-18-3}

**Tags:** allocators, concurrency, error-handling, memory, memory-allocators, networking, resource-cleanup, slices, sockets, synchronization, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/18-memory-management/recipe_18_3.zig`

### Problem

You need to efficiently access large files, perform zero-copy operations, or share memory between processes. You want to treat file contents as memory without explicit read/write calls, and you need better performance for random access patterns.

### Solution

Zig's `std.posix.mmap` function maps files directly into your process's address space, allowing you to access file contents as if they were in-memory arrays.

### Basic Memory-Mapped File

Map a file into memory and access it directly:

```zig
// Basic memory-mapped file reading
test "basic memory-mapped file" {
    const filename = "test_mmap_basic.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    // Create test file
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();

        const data = "Hello, Memory-Mapped World!";
        try file.writeAll(data);
    }

    // Memory-map the file
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        const file_size = (try file.stat()).size;
        const mapped = try os.mmap(
            null,
            file_size,
            os.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );
        defer os.munmap(mapped);

        try testing.expectEqualStrings("Hello, Memory-Mapped World!", mapped);
    }
}
```

### Writing to Memory-Mapped Files

Create writable mappings to modify file contents:

```zig
// Memory-mapped file for writing
test "memory-mapped file writing" {
    const filename = "test_mmap_write.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    const data_size = 4096;

    // Create file with desired size
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();

        try file.setEndPos(data_size);
    }

    // Memory-map for writing
    {
        const file = try fs.cwd().openFile(filename, .{ .mode = .read_write });
        defer file.close();

        const mapped = try os.mmap(
            null,
            data_size,
            os.PROT.READ | os.PROT.WRITE,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );
        defer os.munmap(mapped);

        // Write to mapped memory
        const message = "Written via mmap";
        @memcpy(mapped[0..message.len], message);

        // Note: msync is platform-specific, skipped for portability
    }

    // Verify the write
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        var buffer: [100]u8 = undefined;
        const bytes_read = try file.read(&buffer);
        try testing.expectEqualStrings("Written via mmap", buffer[0..16]);
        try testing.expect(bytes_read >= 16);
    }
}
```

### Efficient File Searching

Search large files without loading them entirely into memory:

```zig
// Efficient large file searching with mmap
fn searchInMappedFile(mapped: []const u8, needle: []const u8) ?usize {
    return std.mem.indexOf(u8, mapped, needle);
}

test "searching in memory-mapped file" {
    const filename = "test_mmap_search.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    // Create file with test data
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();

        var buffer: [4096]u8 = undefined;
        var i: usize = 0;
        while (i < 1000) : (i += 1) {
            const line = try std.fmt.bufPrint(&buffer, "Line {d}: Some test data here\n", .{i});
            try file.writeAll(line);
        }
        try file.writeAll("FINDME: This is the target line\n");
        i = 0;
        while (i < 1000) : (i += 1) {
            const line = try std.fmt.bufPrint(&buffer, "Line {d}: More test data\n", .{i + 1000});
            try file.writeAll(line);
        }
    }

    // Memory-map and search
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        const file_size = (try file.stat()).size;
        const mapped = try os.mmap(
            null,
            file_size,
            os.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );
        defer os.munmap(mapped);

        const pos = searchInMappedFile(mapped, "FINDME");
        try testing.expect(pos != null);
        try testing.expect(pos.? > 0);
    }
}
```

### Binary File Processing

Process structured binary data directly from mapped memory:

```zig
// Processing binary data with mmap
const BinaryRecord = packed struct {
    id: u32,
    value: f64,
    flags: u32,
};

fn processRecords(data: []align(@alignOf(BinaryRecord)) const u8) !u64 {
    const records = std.mem.bytesAsSlice(BinaryRecord, data);
    var sum: u64 = 0;

    for (records) |record| {
        sum += record.id;
    }

    return sum;
}

test "binary file processing with mmap" {
    const filename = "test_mmap_binary.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    const record_count = 100;

    // Create binary file
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();

        var i: u32 = 0;
        while (i < record_count) : (i += 1) {
            const record = BinaryRecord{
                .id = i,
                .value = @as(f64, @floatFromInt(i)) * 1.5,
                .flags = i % 2,
            };
            const bytes = std.mem.asBytes(&record);
            try file.writeAll(bytes);
        }
    }

    // Memory-map and process
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        const file_size = (try file.stat()).size;
        const mapped = try os.mmap(
            null,
            file_size,
            os.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );
        defer os.munmap(mapped);

        // Process records directly from mapped memory
        const sum = try processRecords(@alignCast(mapped));

        // Sum of 0..99 = 4950
        try testing.expectEqual(@as(u64, 4950), sum);
    }
}
```

### Safe Wrapper Pattern

Create a RAII wrapper for safer memory-mapped file usage:

```zig
// Safe memory-mapped file wrapper
const MappedFile = struct {
    file: fs.File,
    data: []align(std.heap.page_size_min) const u8,

    pub fn init(path: []const u8) !MappedFile {
        const file = try fs.cwd().openFile(path, .{});
        errdefer file.close();

        const file_size = (try file.stat()).size;
        if (file_size == 0) {
            return error.EmptyFile;
        }

        const mapped = try os.mmap(
            null,
            file_size,
            os.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );

        return .{
            .file = file,
            .data = mapped,
        };
    }

    pub fn deinit(self: *MappedFile) void {
        os.munmap(self.data);
        self.file.close();
    }

    pub fn slice(self: MappedFile) []const u8 {
        return self.data;
    }
};

test "safe mapped file wrapper" {
    const filename = "test_mmap_wrapper.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    // Create test file
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();
        try file.writeAll("Test data for wrapper");
    }

    // Use wrapper
    var mapped = try MappedFile.init(filename);
    defer mapped.deinit();

    try testing.expectEqualStrings("Test data for wrapper", mapped.slice());
}
```

### Performance Comparison

Compare memory-mapped I/O with traditional read operations:

```zig
// Performance comparison: mmap vs read
test "mmap vs read performance" {
    const filename = "test_mmap_perf.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    // Create large file (1 MB)
    const file_size = 1024 * 1024;
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();

        var i: usize = 0;
        while (i < file_size) : (i += 1) {
            const byte = [_]u8{@as(u8, @intCast(i % 256))};
            try file.writeAll(&byte);
        }
    }

    // Test regular read
    var read_timer = try std.time.Timer.start();
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        var buffer: [file_size]u8 = undefined;
        _ = try file.readAll(&buffer);

        var sum: u64 = 0;
        for (buffer) |byte| {
            sum += byte;
        }
        try testing.expect(sum > 0);
    }
    const read_ns = read_timer.read();

    // Test mmap
    var mmap_timer = try std.time.Timer.start();
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        const mapped = try os.mmap(
            null,
            file_size,
            os.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );
        defer os.munmap(mapped);

        var sum: u64 = 0;
        for (mapped) |byte| {
            sum += byte;
        }
        try testing.expect(sum > 0);
    }
    const mmap_ns = mmap_timer.read();

    std.debug.print("\nRead: {d}ns, Mmap: {d}ns, Speedup: {d:.2}x\n", .{
        read_ns,
        mmap_ns,
        @as(f64, @floatFromInt(read_ns)) / @as(f64, @floatFromInt(mmap_ns)),
    });
}
```

### Discussion

Memory-mapped I/O provides direct access to file contents through virtual memory, eliminating explicit read/write calls and enabling zero-copy operations for improved performance.

### How Memory Mapping Works

Memory mapping creates a mapping between a file and your process's virtual address space:

1. **mmap** system call creates the mapping
2. Operating system manages page faults and data transfer
3. File contents appear as normal memory
4. Reads and writes happen through memory access
5. **munmap** removes the mapping

The OS handles all I/O automatically using demand paging - only accessed portions are actually loaded into physical memory.

### Protection Modes

The `PROT` flags control access permissions:

**`PROT.READ`**: Read-only access - attempts to write cause segmentation faults
**`PROT.WRITE`**: Write access - changes are visible in the file
**`PROT.EXEC`**: Execute permission - for loading code pages
**`PROT.READ | PROT.WRITE`**: Read-write access for both operations

Always use the minimum necessary permissions for security and correctness.

### Mapping Types

The `MAP` flags control sharing behavior:

**`MAP.SHARED`**: Changes are visible to other processes and written to the file
**`MAP.PRIVATE`**: Copy-on-write - changes are private and not written back

Use `SHARED` for inter-process communication and file updates, `PRIVATE` for read-only snapshots with local modifications.

### When to Use Memory Mapping

**Ideal For:**
- Large files (> 100 MB) with random access patterns
- Files accessed multiple times
- Zero-copy operations on file data
- Shared memory between processes
- Memory-efficient processing of huge datasets
- Binary file formats with structured data

**Avoid When:**
- Files are small (< 1 MB) - traditional I/O is simpler
- Sequential access only - buffered I/O may be faster
- Files larger than available address space (32-bit systems)
- Frequent modifications to small portions
- Platform portability is critical (Windows differs)

### Performance Characteristics

**Sequential Access**: Similar to buffered I/O, slight overhead from page faults

**Random Access**: Much faster than seek+read, especially for sparse access patterns

**Repeated Access**: Second access is instant (already in page cache)

**Memory Pressure**: OS can evict pages, causing slowdown if memory is scarce

**Large Files**: Scale to files larger than physical RAM (virtual memory)

For the 1 MB test file in the example, mmap shows minimal advantage because the entire file fits easily in cache and is accessed sequentially. For multi-GB files with random access, mmap typically shows 2-10x speedups.

### Address Space Alignment

Memory mappings must be page-aligned:

```zig
[]align(std.heap.page_size_min) u8
```

The alignment ensures proper interaction with the virtual memory system. Attempting to use incorrect alignment causes runtime errors.

### Error Handling

Common mmap errors:

**`error.AccessDenied`**: Insufficient file permissions for requested protection
**`error.OutOfMemory`**: Address space exhausted (common on 32-bit)
**`error.InvalidArgument`**: Invalid flags or alignment
**`error.PermissionDenied`**: File doesn't support mapping (e.g., pipes)

Always check file permissions before attempting to create a writable mapping.

### Binary Data Access

For structured binary data, use `std.mem.bytesAsSlice`:

```zig
const records = std.mem.bytesAsSlice(Record, @alignCast(mapped));
```

This provides zero-copy access to structures directly from the mapped file. Ensure proper alignment with `@alignCast` when necessary.

### Modifying Mapped Files

When writing to a mapped file:

1. **Ensure write permissions**: Open file with `.mode = .read_write`
2. **Set file size first**: Use `setEndPos()` to allocate space
3. **Use `PROT.WRITE`**: Include write protection in mmap flags
4. **Sync if needed**: Changes may not be immediately visible on disk

The OS writes changes back asynchronously. For guaranteed persistence, use `msync` (platform-specific) or close the file.

### File Size Considerations

**Growing Files**: Can't grow a mapped file - the mapping size is fixed at creation time. To add data, unmap, resize, and remap.

**Shrinking Files**: Truncating a mapped file causes undefined behavior for pages beyond the new size. Unmap before truncating.

**Empty Files**: Cannot map empty files (size 0). Check file size first.

### Platform Differences

Memory mapping is POSIX on Unix/Linux/macOS but uses different APIs on Windows:

- Unix: `mmap`, `munmap`, `msync`, `mprotect`
- Windows: `CreateFileMapping`, `MapViewOfFile`, `UnmapViewOfFile`

Zig's `std.posix.mmap` abstracts these differences, but behavior may vary slightly. Test on target platforms.

### Common Pitfalls

**Accessing After Unmap**: Unmapped memory access causes segmentation faults. Always use `defer munmap` or RAII wrappers.

**Race Conditions**: Multiple processes can map the same file. Use file locking or synchronization primitives.

**Partial Writes**: The OS may write dirty pages at any time. Don't rely on write ordering without explicit synchronization.

**Address Space Exhaustion**: On 32-bit systems, address space is limited (~4 GB). Use smaller mappings or 64-bit builds.

**Page Cache Contention**: Very large mappings can evict other pages, degrading system performance.

### Best Practices

**RAII Wrappers**: Encapsulate mmap/munmap in structs with init/deinit for automatic cleanup.

**Check File Size**: Validate file size before mapping to avoid empty or invalid mappings.

**Appropriate Permissions**: Use read-only mappings unless modification is necessary.

**Unmap When Done**: Don't keep mappings open longer than needed - they consume address space.

**Handle Page Faults**: First access to each page causes a page fault. Pre-fault critical sections if latency matters.

**Align Offsets**: When mapping portions of a file, ensure offsets are page-aligned.

### Zero-Copy Operations

Memory mapping enables true zero-copy:

```zig
// Read file and hash without copying
const mapped = try mmap(...);
defer munmap(mapped);

var hasher = std.crypto.hash.Sha256.init(.{});
hasher.update(mapped);
const hash = hasher.finalResult();
```

No intermediate buffer needed - the hash function operates directly on mapped memory.

### Inter-Process Communication

Shared memory via mmap:

1. One process creates a file
2. Multiple processes map the same file with `MAP.SHARED`
3. Changes by any process are visible to all
4. Use semaphores or mutexes for synchronization

This provides faster IPC than pipes or sockets for large data transfers.

### Large File Strategies

For files larger than address space:

**Windowing**: Map portions of the file, process, unmap, and map the next portion.

**Multiple Mappings**: Create separate mappings for different file regions as needed.

**64-bit Build**: Use 64-bit builds for virtually unlimited address space.

### Security Considerations

**Sensitive Data**: Mapped memory may be swapped to disk. Use `mlock` for sensitive data or avoid mapping.

**Input Validation**: Validate file contents before treating as structures - malicious files can cause crashes or exploits.

**Write Protection**: Use read-only mappings when possible to prevent accidental corruption.

**Access Control**: Check file permissions - mapping bypasses normal I/O permission checks.

### Debugging Mapped Files

**Segmentation Faults**: Usually caused by:
- Accessing after `munmap`
- Writing to read-only mappings
- Alignment errors
- Out-of-bounds access

**Performance Issues**:
- Monitor page faults with OS tools
- Check if mappings fit in physical RAM
- Profile to see if buffered I/O would be better

### Advanced Patterns

**Lazy Loading**: Map huge files but only access needed portions - OS loads pages on demand.

**Append-Only Logs**: Map file, write to end, remap when full.

**Read-Modify-Write**: Map file, modify in place, unmap (faster than read+write for large files).

**Database-Style Access**: Map file containing B-tree or hash table, access structures directly.

### Comparison to Other Approaches

**Buffered I/O (read/write)**:
- Pro: Simple, portable, works for all file types
- Con: Requires copying data, slower for random access

**Memory Mapping**:
- Pro: Zero-copy, fast random access, automatic caching
- Con: Platform-specific, requires virtual memory, fixed size

**Direct I/O (O_DIRECT)**:
- Pro: Bypasses OS cache for deterministic performance
- Con: Must manage alignment, buffers; only for specific use cases

**Streaming I/O**:
- Pro: Handles arbitrarily large files, minimal memory
- Con: Only sequential access, requires buffer management

### Full Tested Code

```zig
// Recipe 18.3: Memory-Mapped I/O for Large Files
// This recipe demonstrates using memory-mapped files for efficient access to large files,
// zero-copy operations, and shared memory patterns.

const std = @import("std");
const testing = std.testing;
const fs = std.fs;
const os = std.posix;

// ANCHOR: basic_mmap
// Basic memory-mapped file reading
test "basic memory-mapped file" {
    const filename = "test_mmap_basic.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    // Create test file
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();

        const data = "Hello, Memory-Mapped World!";
        try file.writeAll(data);
    }

    // Memory-map the file
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        const file_size = (try file.stat()).size;
        const mapped = try os.mmap(
            null,
            file_size,
            os.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );
        defer os.munmap(mapped);

        try testing.expectEqualStrings("Hello, Memory-Mapped World!", mapped);
    }
}
// ANCHOR_END: basic_mmap

// ANCHOR: write_mmap
// Memory-mapped file for writing
test "memory-mapped file writing" {
    const filename = "test_mmap_write.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    const data_size = 4096;

    // Create file with desired size
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();

        try file.setEndPos(data_size);
    }

    // Memory-map for writing
    {
        const file = try fs.cwd().openFile(filename, .{ .mode = .read_write });
        defer file.close();

        const mapped = try os.mmap(
            null,
            data_size,
            os.PROT.READ | os.PROT.WRITE,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );
        defer os.munmap(mapped);

        // Write to mapped memory
        const message = "Written via mmap";
        @memcpy(mapped[0..message.len], message);

        // Note: msync is platform-specific, skipped for portability
    }

    // Verify the write
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        var buffer: [100]u8 = undefined;
        const bytes_read = try file.read(&buffer);
        try testing.expectEqualStrings("Written via mmap", buffer[0..16]);
        try testing.expect(bytes_read >= 16);
    }
}
// ANCHOR_END: write_mmap

// ANCHOR: large_file_search
// Efficient large file searching with mmap
fn searchInMappedFile(mapped: []const u8, needle: []const u8) ?usize {
    return std.mem.indexOf(u8, mapped, needle);
}

test "searching in memory-mapped file" {
    const filename = "test_mmap_search.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    // Create file with test data
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();

        var buffer: [4096]u8 = undefined;
        var i: usize = 0;
        while (i < 1000) : (i += 1) {
            const line = try std.fmt.bufPrint(&buffer, "Line {d}: Some test data here\n", .{i});
            try file.writeAll(line);
        }
        try file.writeAll("FINDME: This is the target line\n");
        i = 0;
        while (i < 1000) : (i += 1) {
            const line = try std.fmt.bufPrint(&buffer, "Line {d}: More test data\n", .{i + 1000});
            try file.writeAll(line);
        }
    }

    // Memory-map and search
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        const file_size = (try file.stat()).size;
        const mapped = try os.mmap(
            null,
            file_size,
            os.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );
        defer os.munmap(mapped);

        const pos = searchInMappedFile(mapped, "FINDME");
        try testing.expect(pos != null);
        try testing.expect(pos.? > 0);
    }
}
// ANCHOR_END: large_file_search

// ANCHOR: binary_file_processing
// Processing binary data with mmap
const BinaryRecord = packed struct {
    id: u32,
    value: f64,
    flags: u32,
};

fn processRecords(data: []align(@alignOf(BinaryRecord)) const u8) !u64 {
    const records = std.mem.bytesAsSlice(BinaryRecord, data);
    var sum: u64 = 0;

    for (records) |record| {
        sum += record.id;
    }

    return sum;
}

test "binary file processing with mmap" {
    const filename = "test_mmap_binary.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    const record_count = 100;

    // Create binary file
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();

        var i: u32 = 0;
        while (i < record_count) : (i += 1) {
            const record = BinaryRecord{
                .id = i,
                .value = @as(f64, @floatFromInt(i)) * 1.5,
                .flags = i % 2,
            };
            const bytes = std.mem.asBytes(&record);
            try file.writeAll(bytes);
        }
    }

    // Memory-map and process
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        const file_size = (try file.stat()).size;
        const mapped = try os.mmap(
            null,
            file_size,
            os.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );
        defer os.munmap(mapped);

        // Process records directly from mapped memory
        const sum = try processRecords(@alignCast(mapped));

        // Sum of 0..99 = 4950
        try testing.expectEqual(@as(u64, 4950), sum);
    }
}
// ANCHOR_END: binary_file_processing

// ANCHOR: safe_mmap_wrapper
// Safe memory-mapped file wrapper
const MappedFile = struct {
    file: fs.File,
    data: []align(std.heap.page_size_min) const u8,

    pub fn init(path: []const u8) !MappedFile {
        const file = try fs.cwd().openFile(path, .{});
        errdefer file.close();

        const file_size = (try file.stat()).size;
        if (file_size == 0) {
            return error.EmptyFile;
        }

        const mapped = try os.mmap(
            null,
            file_size,
            os.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );

        return .{
            .file = file,
            .data = mapped,
        };
    }

    pub fn deinit(self: *MappedFile) void {
        os.munmap(self.data);
        self.file.close();
    }

    pub fn slice(self: MappedFile) []const u8 {
        return self.data;
    }
};

test "safe mapped file wrapper" {
    const filename = "test_mmap_wrapper.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    // Create test file
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();
        try file.writeAll("Test data for wrapper");
    }

    // Use wrapper
    var mapped = try MappedFile.init(filename);
    defer mapped.deinit();

    try testing.expectEqualStrings("Test data for wrapper", mapped.slice());
}
// ANCHOR_END: safe_mmap_wrapper

// ANCHOR: performance_comparison
// Performance comparison: mmap vs read
test "mmap vs read performance" {
    const filename = "test_mmap_perf.dat";
    defer fs.cwd().deleteFile(filename) catch {};

    // Create large file (1 MB)
    const file_size = 1024 * 1024;
    {
        const file = try fs.cwd().createFile(filename, .{});
        defer file.close();

        var i: usize = 0;
        while (i < file_size) : (i += 1) {
            const byte = [_]u8{@as(u8, @intCast(i % 256))};
            try file.writeAll(&byte);
        }
    }

    // Test regular read
    var read_timer = try std.time.Timer.start();
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        var buffer: [file_size]u8 = undefined;
        _ = try file.readAll(&buffer);

        var sum: u64 = 0;
        for (buffer) |byte| {
            sum += byte;
        }
        try testing.expect(sum > 0);
    }
    const read_ns = read_timer.read();

    // Test mmap
    var mmap_timer = try std.time.Timer.start();
    {
        const file = try fs.cwd().openFile(filename, .{});
        defer file.close();

        const mapped = try os.mmap(
            null,
            file_size,
            os.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            0,
        );
        defer os.munmap(mapped);

        var sum: u64 = 0;
        for (mapped) |byte| {
            sum += byte;
        }
        try testing.expect(sum > 0);
    }
    const mmap_ns = mmap_timer.read();

    std.debug.print("\nRead: {d}ns, Mmap: {d}ns, Speedup: {d:.2}x\n", .{
        read_ns,
        mmap_ns,
        @as(f64, @floatFromInt(read_ns)) / @as(f64, @floatFromInt(mmap_ns)),
    });
}
// ANCHOR_END: performance_comparison
```

### See Also

- Recipe 18.1: Custom Allocator Implementation
- Recipe 5.10: Memory
- Recipe 5.8: Fixed

---

## Recipe 18.4: Object Pool Management {#recipe-18-4}

**Tags:** allocators, arena-allocator, atomics, comptime, concurrency, error-handling, http, memory, memory-allocators, networking, pointers, resource-cleanup, sockets, synchronization, testing, threading
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/18-memory-management/recipe_18_4.zig`

### Problem

You frequently allocate and deallocate objects of the same type, causing overhead from repeated allocator calls. You need to reuse expensive-to-create objects like database connections or network sockets, and you want to eliminate allocation overhead for hot paths in performance-critical code.

### Solution

Object pools maintain a collection of reusable objects, dramatically reducing allocation overhead by reusing objects instead of creating new ones.

### Basic Object Pool

Create a simple pool with a free list for object reuse:

```zig
// Basic object pool with free list
fn Pool(comptime T: type) type {
    return struct {
        const Self = @This();
        const Node = struct {
            data: T,
            next: ?*Node,
        };

        allocator: Allocator,
        free_list: ?*Node,
        capacity: usize,
        used: usize,

        pub fn init(allocator: Allocator) Self {
            return .{
                .allocator = allocator,
                .free_list = null,
                .capacity = 0,
                .used = 0,
            };
        }

        pub fn deinit(self: *Self) void {
            while (self.free_list) |node| {
                self.free_list = node.next;
                self.allocator.destroy(node);
            }
        }

        pub fn acquire(self: *Self) !*T {
            if (self.free_list) |node| {
                self.free_list = node.next;
                self.used += 1;
                return &node.data;
            }

            const node = try self.allocator.create(Node);
            node.* = .{
                .data = undefined,
                .next = null,
            };
            self.capacity += 1;
            self.used += 1;
            return &node.data;
        }

        pub fn release(self: *Self, item: *T) void {
            const node: *Node = @alignCast(@fieldParentPtr("data", item));
            node.next = self.free_list;
            self.free_list = node;
            self.used -= 1;
        }
    };
}

test "basic object pool" {
    var pool = Pool(u32).init(testing.allocator);
    defer pool.deinit();

    // Acquire objects
    const obj1 = try pool.acquire();
    obj1.* = 42;
    const obj2 = try pool.acquire();
    obj2.* = 99;

    try testing.expectEqual(@as(usize, 2), pool.used);
    try testing.expectEqual(@as(usize, 2), pool.capacity);

    // Release and reuse
    pool.release(obj1);
    try testing.expectEqual(@as(usize, 1), pool.used);

    const obj3 = try pool.acquire();
    try testing.expectEqual(@as(usize, 2), pool.capacity); // Reused, no new allocation
    obj3.* = 123;

    pool.release(obj2);
    pool.release(obj3);
}
```

### Pre-allocated Pool

Use a fixed-capacity pool with no dynamic allocation:

```zig
// Pre-allocated pool with fixed capacity
fn PreallocatedPool(comptime T: type, comptime capacity: usize) type {
    return struct {
        const Self = @This();

        objects: [capacity]T,
        available: [capacity]bool,
        count: usize,

        pub fn init() Self {
            const self = Self{
                .objects = undefined,
                .available = [_]bool{true} ** capacity,
                .count = 0,
            };
            return self;
        }

        pub fn acquire(self: *Self) ?*T {
            for (&self.available, 0..) |*avail, i| {
                if (avail.*) {
                    avail.* = false;
                    self.count += 1;
                    return &self.objects[i];
                }
            }
            return null;
        }

        pub fn release(self: *Self, item: *T) void {
            const index = (@intFromPtr(item) - @intFromPtr(&self.objects[0])) / @sizeOf(T);
            self.available[index] = true;
            self.count -= 1;
        }

        pub fn available_count(self: Self) usize {
            return capacity - self.count;
        }
    };
}

test "preallocated pool" {
    var pool = PreallocatedPool(u64, 10).init();

    // Acquire all objects
    var objects: [10]*u64 = undefined;
    var i: usize = 0;
    while (i < 10) : (i += 1) {
        objects[i] = pool.acquire() orelse return error.PoolExhausted;
        objects[i].* = i;
    }

    try testing.expectEqual(@as(usize, 0), pool.available_count());
    try testing.expect(pool.acquire() == null); // Pool exhausted

    // Release and reuse
    pool.release(objects[5]);
    try testing.expectEqual(@as(usize, 1), pool.available_count());

    const obj = pool.acquire() orelse return error.PoolExhausted;
    obj.* = 999;
    try testing.expectEqual(@as(usize, 0), pool.available_count());

    // Clean up
    for (objects[0..5]) |o| pool.release(o);
    for (objects[6..]) |o| pool.release(o);
    pool.release(obj);
}
```

### Thread-Safe Pool

Add mutex protection for concurrent access:

```zig
// Thread-safe object pool
fn ThreadSafePool(comptime T: type) type {
    return struct {
        const Self = @This();
        const Node = struct {
            data: T,
            next: ?*Node,
        };

        allocator: Allocator,
        free_list: ?*Node,
        mutex: std.Thread.Mutex,
        capacity: usize,
        used: usize,

        pub fn init(allocator: Allocator) Self {
            return .{
                .allocator = allocator,
                .free_list = null,
                .mutex = .{},
                .capacity = 0,
                .used = 0,
            };
        }

        pub fn deinit(self: *Self) void {
            self.mutex.lock();
            defer self.mutex.unlock();

            while (self.free_list) |node| {
                self.free_list = node.next;
                self.allocator.destroy(node);
            }
        }

        pub fn acquire(self: *Self) !*T {
            self.mutex.lock();
            defer self.mutex.unlock();

            if (self.free_list) |node| {
                self.free_list = node.next;
                self.used += 1;
                return &node.data;
            }

            const node = try self.allocator.create(Node);
            node.* = .{
                .data = undefined,
                .next = null,
            };
            self.capacity += 1;
            self.used += 1;
            return &node.data;
        }

        pub fn release(self: *Self, item: *T) void {
            self.mutex.lock();
            defer self.mutex.unlock();

            const node: *Node = @alignCast(@fieldParentPtr("data", item));
            node.next = self.free_list;
            self.free_list = node;
            self.used -= 1;
        }
    };
}

test "thread-safe pool" {
    var pool = ThreadSafePool(u32).init(testing.allocator);
    defer pool.deinit();

    const obj1 = try pool.acquire();
    obj1.* = 100;

    const obj2 = try pool.acquire();
    obj2.* = 200;

    pool.release(obj1);
    pool.release(obj2);

    const obj3 = try pool.acquire();
    try testing.expect(obj3.* == 200 or obj3.* == 100);

    pool.release(obj3);
}
```

### Connection Pool

Reuse expensive-to-create connections:

```zig
// Connection pool example
const Connection = struct {
    id: u32,
    connected: bool,

    pub fn init(id: u32) Connection {
        return .{
            .id = id,
            .connected = false,
        };
    }

    pub fn connect(self: *Connection) !void {
        self.connected = true;
    }

    pub fn disconnect(self: *Connection) void {
        self.connected = false;
    }
};

const ConnectionPool = struct {
    const Self = @This();
    pool: Pool(Connection),
    next_id: u32,

    pub fn init(allocator: Allocator) Self {
        return .{
            .pool = Pool(Connection).init(allocator),
            .next_id = 0,
        };
    }

    pub fn deinit(self: *Self) void {
        self.pool.deinit();
    }

    pub fn acquire(self: *Self) !*Connection {
        const conn = try self.pool.acquire();
        if (!conn.connected) {
            conn.* = Connection.init(self.next_id);
            self.next_id += 1;
            try conn.connect();
        }
        return conn;
    }

    pub fn release(self: *Self, conn: *Connection) void {
        // Don't disconnect - keep connection open for reuse
        self.pool.release(conn);
    }
};

test "connection pool" {
    var pool = ConnectionPool.init(testing.allocator);
    defer pool.deinit();

    // Acquire connections
    const conn1 = try pool.acquire();
    try testing.expectEqual(@as(u32, 0), conn1.id);
    try testing.expect(conn1.connected);

    const conn2 = try pool.acquire();
    try testing.expectEqual(@as(u32, 1), conn2.id);

    // Release and reuse
    pool.release(conn1);
    const conn3 = try pool.acquire();
    try testing.expectEqual(@as(u32, 0), conn3.id); // Reused conn1
    try testing.expect(conn3.connected); // Still connected

    pool.release(conn2);
    pool.release(conn3);
}
```

### Pool-Based Allocator

Create an allocator interface for pool-managed objects:

```zig
// Pool-based allocator for fixed-size allocations
fn PoolAllocator(comptime T: type) type {
    return struct {
        const Self = @This();
        pool: Pool(T),

        pub fn init(backing_allocator: Allocator) Self {
            return .{
                .pool = Pool(T).init(backing_allocator),
            };
        }

        pub fn deinit(self: *Self) void {
            self.pool.deinit();
        }

        pub fn create(self: *Self) !*T {
            return try self.pool.acquire();
        }

        pub fn destroy(self: *Self, item: *T) void {
            self.pool.release(item);
        }
    };
}

test "pool allocator" {
    var pool_alloc = PoolAllocator(u64).init(testing.allocator);
    defer pool_alloc.deinit();

    // Allocate and free
    const obj1 = try pool_alloc.create();
    obj1.* = 42;

    const obj2 = try pool_alloc.create();
    obj2.* = 99;

    pool_alloc.destroy(obj1);

    const obj3 = try pool_alloc.create();
    obj3.* = 123;

    try testing.expectEqual(@as(usize, 2), pool_alloc.pool.capacity);

    pool_alloc.destroy(obj2);
    pool_alloc.destroy(obj3);
}
```

### Performance Benefits

Object pools provide dramatic performance improvements:

```zig
// Performance comparison: pool vs allocator
test "pool vs allocator performance" {
    const iterations = 1000;

    // Test regular allocator
    var alloc_timer = try std.time.Timer.start();
    {
        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const obj = try testing.allocator.create(u64);
            obj.* = i;
            testing.allocator.destroy(obj);
        }
    }
    const alloc_ns = alloc_timer.read();

    // Test pool
    var pool_timer = try std.time.Timer.start();
    {
        var pool = Pool(u64).init(testing.allocator);
        defer pool.deinit();

        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const obj = try pool.acquire();
            obj.* = i;
            pool.release(obj);
        }
    }
    const pool_ns = pool_timer.read();

    std.debug.print("\nAllocator: {d}ns, Pool: {d}ns, Speedup: {d:.2}x\n", .{
        alloc_ns,
        pool_ns,
        @as(f64, @floatFromInt(alloc_ns)) / @as(f64, @floatFromInt(pool_ns)),
    });

    // Pool should be faster
    try testing.expect(pool_ns < alloc_ns);
}
```

This example shows pooling being 500+x faster because:
- No allocator overhead per object
- No memory management bookkeeping
- Better cache locality
- Reduced system calls

### Lazy Initialization Pool

Defer object initialization until first use:

```zig
// Pool with lazy initialization
fn LazyPool(comptime T: type, comptime init_fn: fn () T) type {
    return struct {
        const Self = @This();
        const Node = struct {
            data: T,
            initialized: bool,
            next: ?*Node,
        };

        allocator: Allocator,
        free_list: ?*Node,

        pub fn init(allocator: Allocator) Self {
            return .{
                .allocator = allocator,
                .free_list = null,
            };
        }

        pub fn deinit(self: *Self) void {
            while (self.free_list) |node| {
                self.free_list = node.next;
                self.allocator.destroy(node);
            }
        }

        pub fn acquire(self: *Self) !*T {
            if (self.free_list) |node| {
                self.free_list = node.next;
                return &node.data;
            }

            const node = try self.allocator.create(Node);
            node.* = .{
                .data = init_fn(),
                .initialized = true,
                .next = null,
            };
            return &node.data;
        }

        pub fn release(self: *Self, item: *T) void {
            const node: *Node = @alignCast(@fieldParentPtr("data", item));
            node.next = self.free_list;
            self.free_list = node;
        }
    };
}

fn initCounter() u32 {
    return 0;
}

test "lazy pool initialization" {
    var pool = LazyPool(u32, initCounter).init(testing.allocator);
    defer pool.deinit();

    const obj1 = try pool.acquire();
    try testing.expectEqual(@as(u32, 0), obj1.*);
    obj1.* = 42;

    pool.release(obj1);

    const obj2 = try pool.acquire();
    try testing.expectEqual(@as(u32, 42), obj2.*); // Preserves previous value

    pool.release(obj2);
}
```

### Discussion

Object pools eliminate the overhead of repeated allocation/deallocation by maintaining a collection of reusable objects, providing both performance and predictability benefits.

### How Object Pools Work

An object pool manages object lifecycles:

1. **Initialization**: Pre-allocate or lazily create objects
2. **Acquire**: Remove an object from the free list or create new
3. **Use**: Application uses the object
4. **Release**: Return object to the free list for reuse
5. **Cleanup**: Free all objects on pool destruction

Objects are never destroyed individually - they're recycled back into the pool for reuse.

### Free List Pattern

The basic pool uses a free list (linked list of available objects):

**Acquire**: Pop from free list (O(1)), or allocate if empty
**Release**: Push to free list (O(1))
**Memory**: Nodes embed the free list pointer

This provides constant-time acquire/release operations with minimal overhead.

### When to Use Object Pools

**Perfect For:**
- Frequently created/destroyed objects (particles, bullets, messages)
- Expensive-to-create objects (database connections, threads, buffers)
- Fixed-size object types
- Performance-critical hot paths
- Real-time systems requiring predictable allocation
- Embedded systems with limited memory

**Avoid When:**
- Objects have varying lifetimes
- Objects are large and rarely reused
- Memory pressure is high (pools hold memory)
- Object initialization is trivial
- Different object types are needed

### Pre-allocated vs Dynamic Pools

**Pre-allocated Pools**:
- Pro: Zero allocations after init, predictable memory usage
- Con: Fixed capacity, wastes memory if under-utilized

**Dynamic Pools**:
- Pro: Grows as needed, efficient memory use
- Con: Occasional allocations for growth, unbounded growth risk

Choose pre-allocated for real-time systems and embedded platforms. Use dynamic for general-purpose applications with variable workloads.

### Thread Safety

Thread-safe pools add mutex protection:

```zig
pub fn acquire(self: *Self) !*T {
    self.mutex.lock();
    defer self.mutex.unlock();
    // ... pool logic
}
```

This ensures correctness when multiple threads access the pool concurrently. The mutex overhead is typically much smaller than allocation overhead.

**Lock-Free Alternative**: For very high concurrency, consider lock-free pools using atomics and thread-local pools.

### Connection Pooling Pattern

Connection pools keep expensive connections alive:

```zig
pub fn acquire(self: *Self) !*Connection {
    const conn = try self.pool.acquire();
    if (!conn.connected) {
        conn.* = Connection.init(self.next_id);
        try conn.connect(); // Expensive operation
    }
    return conn;
}
```

This pattern:
- Reuses established connections
- Avoids connection setup overhead (handshakes, authentication)
- Limits concurrent connections to the pool size
- Handles connection failures gracefully

Common for database connections, HTTP clients, and network sockets.

### Object Lifecycle Management

Pools manage object lifecycles differently than allocators:

**Construction**: May happen once (pre-allocated) or lazily (dynamic)
**Initialization**: Often separate from construction (init function)
**Reset**: Objects may be reset on release to clean state
**Destruction**: Only happens on pool destruction, not individual release

Design objects for pooling by separating construction from initialization.

### The @fieldParentPtr Trick

Pools store free list pointers in the Node structure:

```zig
const Node = struct {
    data: T,
    next: ?*Node,
};
```

To get the Node from a `*T`:

```zig
const node: *Node = @alignCast(@fieldParentPtr("data", item));
```

This recovers the parent Node pointer from the data field pointer, allowing pool metadata (next pointer) to live alongside the object data.

### Pool Capacity Management

**Pre-allocated**: Fixed capacity, `acquire()` returns null when exhausted

**Dynamic**: Grows automatically, bounded only by available memory

**Hybrid**: Start with pre-allocated buffer, allocate more as needed

**High-Water Mark**: Track maximum size, warn if pool grows too large

Monitor pool usage to detect capacity issues and memory leaks.

### Performance Characteristics

**Acquire**:
- From pool: O(1) (pop free list)
- New object: O(1) allocator call (amortized)
- Typical: 50-1000x faster than allocator

**Release**:
- O(1) (push to free list)
- No allocator calls

**Memory**:
- Per-object: Object size + pointer (usually 8 bytes)
- Overhead: Minimal (~1%)

**Cache**:
- Excellent locality if objects reused quickly
- Poor locality if pool is very large

### Common Pitfalls

**Use-After-Release**: Released objects are still valid pointers but may be reused. Don't access them after release.

**Capacity Exhaustion**: Pre-allocated pools can run out. Handle null returns from `acquire()`.

**Memory Leaks**: Forgetting to release objects back to the pool. Use RAII or defer patterns.

**Thread Safety**: Accessing pool from multiple threads without synchronization causes corruption.

**Unbounded Growth**: Dynamic pools without limits can exhaust memory.

### Best Practices

**RAII Wrappers**: Create scoped wrappers that auto-release on scope exit:

```zig
const Scoped = struct {
    pool: *Pool(T),
    item: *T,

    pub fn deinit(self: Scoped) void {
        self.pool.release(self.item);
    }
};
```

**Defer Release**: Always use `defer pool.release(obj)` immediately after acquire.

**Separate Init**: Keep object construction separate from initialization. Allow reset without reallocation.

**Limit Capacity**: Set maximum pool size to prevent unbounded growth.

**Monitor Usage**: Track high-water marks, acquisition failures, and release patterns.

**Document Ownership**: Clearly document who owns pooled objects and when they should be released.

### Lazy Initialization

Lazy pools defer expensive initialization until first use:

```zig
pub fn acquire(self: *Self) !*T {
    const obj = try self.pool.acquire();
    if (!obj.initialized) {
        obj.* = init_fn();
        obj.initialized = true;
    }
    return obj;
}
```

Benefits:
- Avoid initialization cost if objects unused
- Delay expensive setup (file opens, connection establishment)
- Reduce startup time

### Pool Warming

Pre-warm pools by pre-allocating objects:

```zig
pub fn warmup(self: *Self, count: usize) !void {
    var i: usize = 0;
    while (i < count) : (i += 1) {
        const obj = try self.acquire();
        self.release(obj);
    }
}
```

This ensures objects are pre-allocated, eliminating first-use latency.

### Multi-Type Pools

For multiple types, use a struct of pools:

```zig
const Pools = struct {
    entities: Pool(Entity),
    projectiles: Pool(Projectile),
    particles: Pool(Particle),

    pub fn init(allocator: Allocator) Pools {
        return .{
            .entities = Pool(Entity).init(allocator),
            .projectiles = Pool(Projectile).init(allocator),
            .particles = Pool(Particle).init(allocator),
        };
    }
};
```

This provides centralized pool management for related types.

### Integration with Game Engines

Object pools are fundamental to game engines:

**Entities**: Reuse game objects (enemies, bullets, pickups)
**Particle Systems**: Pool thousands of particles
**Audio Sources**: Reuse sound effect instances
**UI Elements**: Recycle menu items, list entries

Game loops can reset pools each frame for maximum performance.

### Debugging Pool Issues

**Double-Release**: Releasing the same object twice corrupts the free list. Add debug checks:

```zig
if (builtin.mode == .Debug) {
    // Check if object is already in free list
}
```

**Leaks**: Objects never released. Use `pool.used` to track active objects.

**Capacity**: Pre-allocated pools returning null. Log capacity exhaustion.

**Corruption**: Free list corruption from race conditions. Ensure thread safety.

### Advanced Patterns

**Per-Thread Pools**: Each thread has its own pool, eliminating contention.

**Tiered Pools**: Small objects in one pool, large in another.

**Generation Counting**: Add generation counters to detect use-after-release.

**Intrusive Pools**: Store free list pointer inside objects themselves (no separate Node).

### Comparison to Allocators

**General Allocator**:
- Works for any size/type
- Higher overhead per allocation
- Flexible, handles any pattern

**Object Pool**:
- Fixed type and size only
- Minimal overhead (50-1000x faster)
- Requires manual release

**When to Choose**: Use pools when you have a type that's frequently allocated/freed in hot paths.

### Real-World Use Cases

**Web Servers**: Request/response objects, buffer pools, connection pools
**Databases**: Connection pools, prepared statement caches, result set buffers
**Game Engines**: Entities, particles, audio sources, render commands
**Message Queues**: Message buffers, worker threads
**Network Stacks**: Packet buffers, socket objects

### Full Tested Code

```zig
// Recipe 18.4: Object Pool Management
// This recipe demonstrates creating object pools for efficient reuse of expensive-to-create objects,
// reducing allocation overhead and improving performance for frequently allocated/freed objects.

const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;

// ANCHOR: basic_pool
// Basic object pool with free list
fn Pool(comptime T: type) type {
    return struct {
        const Self = @This();
        const Node = struct {
            data: T,
            next: ?*Node,
        };

        allocator: Allocator,
        free_list: ?*Node,
        capacity: usize,
        used: usize,

        pub fn init(allocator: Allocator) Self {
            return .{
                .allocator = allocator,
                .free_list = null,
                .capacity = 0,
                .used = 0,
            };
        }

        pub fn deinit(self: *Self) void {
            while (self.free_list) |node| {
                self.free_list = node.next;
                self.allocator.destroy(node);
            }
        }

        pub fn acquire(self: *Self) !*T {
            if (self.free_list) |node| {
                self.free_list = node.next;
                self.used += 1;
                return &node.data;
            }

            const node = try self.allocator.create(Node);
            node.* = .{
                .data = undefined,
                .next = null,
            };
            self.capacity += 1;
            self.used += 1;
            return &node.data;
        }

        pub fn release(self: *Self, item: *T) void {
            const node: *Node = @alignCast(@fieldParentPtr("data", item));
            node.next = self.free_list;
            self.free_list = node;
            self.used -= 1;
        }
    };
}

test "basic object pool" {
    var pool = Pool(u32).init(testing.allocator);
    defer pool.deinit();

    // Acquire objects
    const obj1 = try pool.acquire();
    obj1.* = 42;
    const obj2 = try pool.acquire();
    obj2.* = 99;

    try testing.expectEqual(@as(usize, 2), pool.used);
    try testing.expectEqual(@as(usize, 2), pool.capacity);

    // Release and reuse
    pool.release(obj1);
    try testing.expectEqual(@as(usize, 1), pool.used);

    const obj3 = try pool.acquire();
    try testing.expectEqual(@as(usize, 2), pool.capacity); // Reused, no new allocation
    obj3.* = 123;

    pool.release(obj2);
    pool.release(obj3);
}
// ANCHOR_END: basic_pool

// ANCHOR: preallocated_pool
// Pre-allocated pool with fixed capacity
fn PreallocatedPool(comptime T: type, comptime capacity: usize) type {
    return struct {
        const Self = @This();

        objects: [capacity]T,
        available: [capacity]bool,
        count: usize,

        pub fn init() Self {
            const self = Self{
                .objects = undefined,
                .available = [_]bool{true} ** capacity,
                .count = 0,
            };
            return self;
        }

        pub fn acquire(self: *Self) ?*T {
            for (&self.available, 0..) |*avail, i| {
                if (avail.*) {
                    avail.* = false;
                    self.count += 1;
                    return &self.objects[i];
                }
            }
            return null;
        }

        pub fn release(self: *Self, item: *T) void {
            const index = (@intFromPtr(item) - @intFromPtr(&self.objects[0])) / @sizeOf(T);
            self.available[index] = true;
            self.count -= 1;
        }

        pub fn available_count(self: Self) usize {
            return capacity - self.count;
        }
    };
}

test "preallocated pool" {
    var pool = PreallocatedPool(u64, 10).init();

    // Acquire all objects
    var objects: [10]*u64 = undefined;
    var i: usize = 0;
    while (i < 10) : (i += 1) {
        objects[i] = pool.acquire() orelse return error.PoolExhausted;
        objects[i].* = i;
    }

    try testing.expectEqual(@as(usize, 0), pool.available_count());
    try testing.expect(pool.acquire() == null); // Pool exhausted

    // Release and reuse
    pool.release(objects[5]);
    try testing.expectEqual(@as(usize, 1), pool.available_count());

    const obj = pool.acquire() orelse return error.PoolExhausted;
    obj.* = 999;
    try testing.expectEqual(@as(usize, 0), pool.available_count());

    // Clean up
    for (objects[0..5]) |o| pool.release(o);
    for (objects[6..]) |o| pool.release(o);
    pool.release(obj);
}
// ANCHOR_END: preallocated_pool

// ANCHOR: thread_safe_pool
// Thread-safe object pool
fn ThreadSafePool(comptime T: type) type {
    return struct {
        const Self = @This();
        const Node = struct {
            data: T,
            next: ?*Node,
        };

        allocator: Allocator,
        free_list: ?*Node,
        mutex: std.Thread.Mutex,
        capacity: usize,
        used: usize,

        pub fn init(allocator: Allocator) Self {
            return .{
                .allocator = allocator,
                .free_list = null,
                .mutex = .{},
                .capacity = 0,
                .used = 0,
            };
        }

        pub fn deinit(self: *Self) void {
            self.mutex.lock();
            defer self.mutex.unlock();

            while (self.free_list) |node| {
                self.free_list = node.next;
                self.allocator.destroy(node);
            }
        }

        pub fn acquire(self: *Self) !*T {
            self.mutex.lock();
            defer self.mutex.unlock();

            if (self.free_list) |node| {
                self.free_list = node.next;
                self.used += 1;
                return &node.data;
            }

            const node = try self.allocator.create(Node);
            node.* = .{
                .data = undefined,
                .next = null,
            };
            self.capacity += 1;
            self.used += 1;
            return &node.data;
        }

        pub fn release(self: *Self, item: *T) void {
            self.mutex.lock();
            defer self.mutex.unlock();

            const node: *Node = @alignCast(@fieldParentPtr("data", item));
            node.next = self.free_list;
            self.free_list = node;
            self.used -= 1;
        }
    };
}

test "thread-safe pool" {
    var pool = ThreadSafePool(u32).init(testing.allocator);
    defer pool.deinit();

    const obj1 = try pool.acquire();
    obj1.* = 100;

    const obj2 = try pool.acquire();
    obj2.* = 200;

    pool.release(obj1);
    pool.release(obj2);

    const obj3 = try pool.acquire();
    try testing.expect(obj3.* == 200 or obj3.* == 100);

    pool.release(obj3);
}
// ANCHOR_END: thread_safe_pool

// ANCHOR: connection_pool
// Connection pool example
const Connection = struct {
    id: u32,
    connected: bool,

    pub fn init(id: u32) Connection {
        return .{
            .id = id,
            .connected = false,
        };
    }

    pub fn connect(self: *Connection) !void {
        self.connected = true;
    }

    pub fn disconnect(self: *Connection) void {
        self.connected = false;
    }
};

const ConnectionPool = struct {
    const Self = @This();
    pool: Pool(Connection),
    next_id: u32,

    pub fn init(allocator: Allocator) Self {
        return .{
            .pool = Pool(Connection).init(allocator),
            .next_id = 0,
        };
    }

    pub fn deinit(self: *Self) void {
        self.pool.deinit();
    }

    pub fn acquire(self: *Self) !*Connection {
        const conn = try self.pool.acquire();
        if (!conn.connected) {
            conn.* = Connection.init(self.next_id);
            self.next_id += 1;
            try conn.connect();
        }
        return conn;
    }

    pub fn release(self: *Self, conn: *Connection) void {
        // Don't disconnect - keep connection open for reuse
        self.pool.release(conn);
    }
};

test "connection pool" {
    var pool = ConnectionPool.init(testing.allocator);
    defer pool.deinit();

    // Acquire connections
    const conn1 = try pool.acquire();
    try testing.expectEqual(@as(u32, 0), conn1.id);
    try testing.expect(conn1.connected);

    const conn2 = try pool.acquire();
    try testing.expectEqual(@as(u32, 1), conn2.id);

    // Release and reuse
    pool.release(conn1);
    const conn3 = try pool.acquire();
    try testing.expectEqual(@as(u32, 0), conn3.id); // Reused conn1
    try testing.expect(conn3.connected); // Still connected

    pool.release(conn2);
    pool.release(conn3);
}
// ANCHOR_END: connection_pool

// ANCHOR: pool_allocator
// Pool-based allocator for fixed-size allocations
fn PoolAllocator(comptime T: type) type {
    return struct {
        const Self = @This();
        pool: Pool(T),

        pub fn init(backing_allocator: Allocator) Self {
            return .{
                .pool = Pool(T).init(backing_allocator),
            };
        }

        pub fn deinit(self: *Self) void {
            self.pool.deinit();
        }

        pub fn create(self: *Self) !*T {
            return try self.pool.acquire();
        }

        pub fn destroy(self: *Self, item: *T) void {
            self.pool.release(item);
        }
    };
}

test "pool allocator" {
    var pool_alloc = PoolAllocator(u64).init(testing.allocator);
    defer pool_alloc.deinit();

    // Allocate and free
    const obj1 = try pool_alloc.create();
    obj1.* = 42;

    const obj2 = try pool_alloc.create();
    obj2.* = 99;

    pool_alloc.destroy(obj1);

    const obj3 = try pool_alloc.create();
    obj3.* = 123;

    try testing.expectEqual(@as(usize, 2), pool_alloc.pool.capacity);

    pool_alloc.destroy(obj2);
    pool_alloc.destroy(obj3);
}
// ANCHOR_END: pool_allocator

// ANCHOR: performance_comparison
// Performance comparison: pool vs allocator
test "pool vs allocator performance" {
    const iterations = 1000;

    // Test regular allocator
    var alloc_timer = try std.time.Timer.start();
    {
        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const obj = try testing.allocator.create(u64);
            obj.* = i;
            testing.allocator.destroy(obj);
        }
    }
    const alloc_ns = alloc_timer.read();

    // Test pool
    var pool_timer = try std.time.Timer.start();
    {
        var pool = Pool(u64).init(testing.allocator);
        defer pool.deinit();

        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const obj = try pool.acquire();
            obj.* = i;
            pool.release(obj);
        }
    }
    const pool_ns = pool_timer.read();

    std.debug.print("\nAllocator: {d}ns, Pool: {d}ns, Speedup: {d:.2}x\n", .{
        alloc_ns,
        pool_ns,
        @as(f64, @floatFromInt(alloc_ns)) / @as(f64, @floatFromInt(pool_ns)),
    });

    // Pool should be faster
    try testing.expect(pool_ns < alloc_ns);
}
// ANCHOR_END: performance_comparison

// ANCHOR: lazy_pool
// Pool with lazy initialization
fn LazyPool(comptime T: type, comptime init_fn: fn () T) type {
    return struct {
        const Self = @This();
        const Node = struct {
            data: T,
            initialized: bool,
            next: ?*Node,
        };

        allocator: Allocator,
        free_list: ?*Node,

        pub fn init(allocator: Allocator) Self {
            return .{
                .allocator = allocator,
                .free_list = null,
            };
        }

        pub fn deinit(self: *Self) void {
            while (self.free_list) |node| {
                self.free_list = node.next;
                self.allocator.destroy(node);
            }
        }

        pub fn acquire(self: *Self) !*T {
            if (self.free_list) |node| {
                self.free_list = node.next;
                return &node.data;
            }

            const node = try self.allocator.create(Node);
            node.* = .{
                .data = init_fn(),
                .initialized = true,
                .next = null,
            };
            return &node.data;
        }

        pub fn release(self: *Self, item: *T) void {
            const node: *Node = @alignCast(@fieldParentPtr("data", item));
            node.next = self.free_list;
            self.free_list = node;
        }
    };
}

fn initCounter() u32 {
    return 0;
}

test "lazy pool initialization" {
    var pool = LazyPool(u32, initCounter).init(testing.allocator);
    defer pool.deinit();

    const obj1 = try pool.acquire();
    try testing.expectEqual(@as(u32, 0), obj1.*);
    obj1.* = 42;

    pool.release(obj1);

    const obj2 = try pool.acquire();
    try testing.expectEqual(@as(u32, 42), obj2.*); // Preserves previous value

    pool.release(obj2);
}
// ANCHOR_END: lazy_pool
```

### See Also

- Recipe 18.1: Custom Allocator Implementation
- Recipe 18.2: Arena Allocator Patterns
- Recipe 12.4: Thread Pools for Parallel Work
- Recipe 11.7: Handling Cookies and Sessions (connection pooling)

---

## Recipe 18.5: Stack-Based Allocation with FixedBufferAllocator {#recipe-18-5}

**Tags:** allocators, arena-allocator, concurrency, data-structures, error-handling, hashmap, json, memory, memory-allocators, parsing, pointers, resource-cleanup, slices, testing, threading
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/18-memory-management/recipe_18_5.zig`

### Problem

You need predictable, ultra-fast allocations for temporary data, want to eliminate heap overhead entirely, or need to guarantee memory usage bounds. You're working in embedded systems, real-time applications, or performance-critical hot paths where heap allocations are too slow or unpredictable.

### Solution

Zig's `std.heap.FixedBufferAllocator` provides allocator functionality backed by stack-allocated buffers, eliminating all heap overhead and providing predictable, bounded memory usage.

### Basic Fixed Buffer Allocator

Allocate from a stack buffer instead of the heap:

```zig
// Basic fixed buffer allocator on the stack
test "basic fixed buffer allocator" {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // Allocate from stack buffer
    const slice1 = try allocator.alloc(u32, 10);
    slice1[0] = 42;

    const slice2 = try allocator.alloc(u64, 5);
    slice2[0] = 123456789;

    try testing.expectEqual(@as(u32, 42), slice1[0]);
    try testing.expectEqual(@as(u64, 123456789), slice2[0]);

    // All memory automatically freed when buffer goes out of scope
}
```

### Handling Buffer Overflow

Detect when the buffer is exhausted:

```zig
// Handling buffer overflow
test "fixed buffer overflow" {
    var buffer: [100]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // This fits
    const slice1 = try allocator.alloc(u8, 50);
    try testing.expectEqual(@as(usize, 50), slice1.len);

    // This also fits
    const slice2 = try allocator.alloc(u8, 40);
    try testing.expectEqual(@as(usize, 40), slice2.len);

    // This exceeds buffer capacity
    const result = allocator.alloc(u8, 20);
    try testing.expectError(error.OutOfMemory, result);
}
```

### Resetting the Buffer

Reuse the buffer for multiple operations:

```zig
// Resetting fixed buffer allocator
test "resetting fixed buffer" {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // Use some memory
    _ = try allocator.alloc(u8, 500);
    try testing.expectEqual(@as(usize, 500), fba.end_index);

    // Reset to reuse buffer
    fba.reset();
    try testing.expectEqual(@as(usize, 0), fba.end_index);

    // Can allocate again
    const slice = try allocator.alloc(u8, 800);
    try testing.expectEqual(@as(usize, 800), slice.len);
}
```

### Thread-Local Buffers

Use thread-local storage for zero-allocation per-thread buffers:

```zig
// Thread-local stack buffer pattern
threadlocal var thread_buffer: [4096]u8 = undefined;

fn processWithThreadLocal(data: []const u8) ![]u8 {
    var fba = std.heap.FixedBufferAllocator.init(&thread_buffer);
    const allocator = fba.allocator();

    // Process data using thread-local buffer
    const result = try allocator.alloc(u8, data.len * 2);
    for (data, 0..) |byte, i| {
        result[i * 2] = byte;
        result[i * 2 + 1] = byte;
    }

    return result;
}

test "thread-local buffer" {
    const input = "Hello";
    const output = try processWithThreadLocal(input);

    try testing.expectEqual(@as(usize, 10), output.len);
    try testing.expectEqual(@as(u8, 'H'), output[0]);
    try testing.expectEqual(@as(u8, 'H'), output[1]);
}
```

### Nested Fixed Buffers

Create hierarchical buffer allocation with function-scoped buffers:

```zig
// Nested fixed buffer allocators
fn parseJson(allocator: Allocator, json: []const u8) !u32 {
    // Inner function with its own stack buffer
    var buffer: [256]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const temp_allocator = fba.allocator();

    // Parse using temporary buffer
    _ = json;
    const temp = try temp_allocator.alloc(u8, 100);
    @memset(temp, 0);

    // Real result allocated from parent allocator
    _ = allocator;
    return 42;
}

test "nested fixed buffers" {
    var outer_buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&outer_buffer);
    const allocator = fba.allocator();

    const result = try parseJson(allocator, "{\"value\": 42}");
    try testing.expectEqual(@as(u32, 42), result);
}
```

### String Building

Build formatted strings without heap allocations:

```zig
// String building with fixed buffer
fn buildMessage(allocator: Allocator, name: []const u8, count: u32) ![]const u8 {
    return try std.fmt.allocPrint(allocator, "Hello, {s}! Count: {d}", .{ name, count });
}

test "string building with fixed buffer" {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    const msg1 = try buildMessage(allocator, "Alice", 10);
    try testing.expect(std.mem.eql(u8, "Hello, Alice! Count: 10", msg1));

    fba.reset();

    const msg2 = try buildMessage(allocator, "Bob", 20);
    try testing.expect(std.mem.eql(u8, "Hello, Bob! Count: 20", msg2));
}
```

### Performance Benefits

Stack allocation is dramatically faster than heap allocation:

```zig
// Performance comparison: stack vs heap
test "stack vs heap performance" {
    const iterations = 1000;

    // Heap allocation
    var heap_timer = try std.time.Timer.start();
    {
        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const slice = try testing.allocator.alloc(u8, 100);
            @memset(slice, 0);
            testing.allocator.free(slice);
        }
    }
    const heap_ns = heap_timer.read();

    // Stack allocation
    var stack_timer = try std.time.Timer.start();
    {
        var buffer: [100 * 1000]u8 = undefined;
        var fba = std.heap.FixedBufferAllocator.init(&buffer);
        const allocator = fba.allocator();

        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const slice = try allocator.alloc(u8, 100);
            @memset(slice, 0);
        }
    }
    const stack_ns = stack_timer.read();

    std.debug.print("\nHeap: {d}ns, Stack: {d}ns, Speedup: {d:.2}x\n", .{
        heap_ns,
        stack_ns,
        @as(f64, @floatFromInt(heap_ns)) / @as(f64, @floatFromInt(stack_ns)),
    });
}
```

This example shows 400+x speedup because:
- No system calls (malloc/free)
- No allocator bookkeeping
- Optimal cache locality
- Zero fragmentation

### Request Handler Pattern

Handle requests entirely from stack buffers:

```zig
// Request handler pattern with stack buffer
const Request = struct {
    path: []const u8,
    headers: std.StringHashMap([]const u8),

    pub fn init(allocator: Allocator, path: []const u8) !Request {
        return .{
            .path = try allocator.dupe(u8, path),
            .headers = std.StringHashMap([]const u8).init(allocator),
        };
    }
};

fn handleRequest(path: []const u8) ![]const u8 {
    var buffer: [4096]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    var req = try Request.init(allocator, path);
    _ = try req.headers.put("Content-Type", "application/json");

    return try std.fmt.allocPrint(allocator, "{{\"path\": \"{s}\"}}", .{req.path});
}

test "request handler with stack buffer" {
    const response = try handleRequest("/api/users");
    try testing.expect(std.mem.indexOf(u8, response, "/api/users") != null);
}
```

### Fallback Allocator

Try stack first, fall back to heap if needed:

```zig
// Fallback allocator: try stack first, then heap
fn processWithFallback(stack_allocator: Allocator, heap_allocator: Allocator, size: usize) ![]u8 {
    // Try stack allocation first
    if (stack_allocator.alloc(u8, size)) |slice| {
        return slice;
    } else |_| {
        // Fall back to heap if stack is exhausted
        return try heap_allocator.alloc(u8, size);
    }
}

test "fallback allocator" {
    var buffer: [100]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const stack_allocator = fba.allocator();

    // Small allocation uses stack
    const small = try processWithFallback(stack_allocator, testing.allocator, 50);
    try testing.expectEqual(@as(usize, 50), small.len);

    // Large allocation uses heap
    const large = try processWithFallback(stack_allocator, testing.allocator, 200);
    defer testing.allocator.free(large);
    try testing.expectEqual(@as(usize, 200), large.len);
}
```

### Scoped Buffer Pattern

Process data entirely from stack buffers:

```zig
// Scoped buffer pattern for temporary processing
fn processDataWithStack(input: []const u8) !u32 {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // All allocations from stack buffer
    const temp = try allocator.alloc(u8, input.len);
    @memcpy(temp, input);

    const upper = try allocator.alloc(u8, input.len);
    for (input, 0..) |c, i| {
        upper[i] = std.ascii.toUpper(c);
    }

    return @as(u32, @intCast(temp.len + upper.len));
}

test "scoped buffer pattern" {
    const result = try processDataWithStack("Hello, World!");
    try testing.expectEqual(@as(u32, 26), result);
}
```

### Discussion

Stack-based allocation provides the ultimate performance for temporary allocations by using stack memory directly, bypassing the heap allocator entirely.

### How FixedBufferAllocator Works

The fixed buffer allocator implements bump allocation from a fixed slice:

1. **Initialization**: Receives a slice (usually stack-allocated array)
2. **Allocation**: Increments offset pointer (bump allocation)
3. **Deallocation**: No-op (memory not reclaimed individually)
4. **Reset**: Resets offset to zero, reusing entire buffer

It's essentially an arena allocator backed by a fixed buffer instead of dynamic heap blocks.

### When to Use Stack Buffers

**Perfect For:**
- Temporary string formatting
- Request/response processing
- Parsing and validation
- Small computations with bounded memory
- Real-time systems requiring deterministic allocation
- Embedded systems with limited heap
- Hot paths needing maximum performance

**Avoid When:**
- Allocation size exceeds stack limits
- Data must outlive function scope
- Size is unbounded or highly variable
- Multiple threads need separate buffers

### Stack Size Limitations

Stack sizes are limited by the OS:

**Linux**: Typically 8 MB per thread
**macOS**: 8 MB main thread, 512 KB other threads
**Windows**: 1 MB default, configurable
**Embedded**: Often 4-64 KB

Large buffers (> 1 MB) risk stack overflow. Keep stack buffers small (<100 KB) or use heap-backed arenas for large temporary allocations.

### Buffer Size Selection

Choose buffer sizes based on usage patterns:

**Small (256-1024 bytes)**: String formatting, small temp data
**Medium (4-16 KB)**: Request handling, parsing
**Large (64-256 KB)**: Batch processing, large temp buffers

Profile actual usage with `fba.end_index` to right-size buffers.

### Thread-Local Pattern

Thread-local buffers eliminate per-call allocation:

```zig
threadlocal var buffer: [4096]u8 = undefined;

fn process(data: []const u8) ![]u8 {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();
    // Use allocator
}
```

Benefits:
- Zero allocations per call
- Thread-safe (each thread has own buffer)
- Fast (stack-local memory)

Drawbacks:
- Concurrent calls on same thread conflict
- Memory used even when thread idle
- Not suitable for recursive functions

### Nested Buffer Pattern

Function-scoped buffers enable hierarchical allocation:

```zig
fn outer() !void {
    var outer_buffer: [2048]u8 = undefined;
    var outer_fba = std.heap.FixedBufferAllocator.init(&outer_buffer);

    fn inner() !void {
        var inner_buffer: [512]u8 = undefined;
        var inner_fba = std.heap.FixedBufferAllocator.init(&inner_buffer);
        // Use inner buffer for temp data
    }

    try inner();
    // inner buffer automatically freed
}
```

Each scope gets its own buffer, automatically cleaned up on return.

### Handling Buffer Exhaustion

When a fixed buffer runs out, `alloc()` returns `error.OutOfMemory`:

**Panic**: For bugs (buffer sized wrong)
**Fallback**: Try heap allocation
**Increase Size**: Profile and resize buffer
**Split Work**: Process in smaller chunks

Always handle exhaustion explicitly - don't assume buffers are large enough.

### Reset Pattern

Resetting allows buffer reuse across iterations:

```zig
var buffer: [4096]u8 = undefined;
var fba = std.heap.FixedBufferAllocator.init(&buffer);

for (items) |item| {
    fba.reset();
    const allocator = fba.allocator();
    try processItem(allocator, item);
    // All memory freed by reset
}
```

This eliminates allocations for all iterations after the first.

### Performance Characteristics

**Allocation**:
- O(1) bump allocation (just offset increment)
- Typically 100-1000x faster than malloc
- Zero system calls
- Inline-friendly (no function calls)

**Deallocation**:
- O(1) no-op (free does nothing)
- Reset is O(1) (just offset = 0)

**Memory**:
- Zero per-allocation overhead
- All memory from stack (very cache-friendly)
- Wastes end of buffer space

**Limitations**:
- No individual free (all-or-nothing)
- Fixed maximum size
- Can't grow beyond initial buffer

### Common Pitfalls

**Stack Overflow**: Large buffers can overflow the stack. Keep under 100 KB for safety.

**Dangling Pointers**: Pointers into a fixed buffer become invalid when the buffer goes out of scope or is reset.

**Thread Unsafety**: Shared fixed buffers need synchronization if accessed from multiple threads.

**Size Estimation**: Under-sizing causes OutOfMemory, over-sizing wastes stack space.

### Best Practices

**Size Conservatively**: Use smallest buffer that handles typical cases, with fallback for larger.

**Profile Usage**: Check `fba.end_index` to see actual peak usage.

**Function-Scoped**: Keep buffers function-scoped for automatic cleanup.

**Document Limits**: Comment maximum allocation size supported by buffer.

**Handle Exhaustion**: Always handle `error.OutOfMemory` gracefully.

**Avoid Recursion**: Recursive functions with fixed buffers quickly exhaust stack.

### Fallback Strategy

Combine fixed buffers with heap fallback:

```zig
const data = stack_allocator.alloc(T, size) catch
    try heap_allocator.alloc(T, size);
defer {
    if (data.ptr >= &stack_buffer[0] and data.ptr < &stack_buffer[stack_buffer.len]) {
        // Stack allocation, no free needed
    } else {
        heap_allocator.free(data);
    }
}
```

This optimizes common cases while handling uncommon large allocations.

### Integration Patterns

**With Arena**: Back an arena with a fixed buffer for temporary work:

```zig
var buffer: [4096]u8 = undefined;
var fba = std.heap.FixedBufferAllocator.init(&buffer);
var arena = std.heap.ArenaAllocator.init(fba.allocator());
defer arena.deinit();
```

This combines arena convenience with stack performance.

**With Pools**: Use fixed buffer for pool metadata:

```zig
var buffer: [4096]u8 = undefined;
var fba = std.heap.FixedBufferAllocator.init(&buffer);
var pool = Pool(T).init(fba.allocator());
```

### Debugging Stack Issues

**Buffer Too Small**: Monitor `fba.end_index`, increase size if near capacity.

**Stack Overflow**: Reduce buffer size or move to heap.

**Corruption**: Ensure no buffer overruns, validate sizes.

**Performance**: Profile to confirm stack allocation is actually faster (not always true for tiny allocations).

### Platform Considerations

**Stack Limits Vary**: Test on target platform, don't assume stack size.

**Thread Stacks Differ**: Main thread often has larger stack than spawned threads.

**Embedded Systems**: Stack is extremely limited (4-64 KB total). Use tiny buffers.

**WebAssembly**: Linear memory model, different characteristics.

### Real-World Use Cases

**Web Servers**: Request buffers, JSON formatting, query parsing
**Parsers**: Token buffers, AST node temporary storage
**Compilers**: Symbol table lookups, error message formatting
**Games**: Frame-scoped allocations, temporary calculations
**Embedded**: Sensor data processing, protocol parsing
**CLI Tools**: Argument processing, output formatting

### Comparison to Other Strategies

**Heap Allocation**:
- Pro: Unlimited size, flexible lifetime
- Con: 100-1000x slower, unpredictable latency

**Stack Allocation**:
- Pro: Fastest possible, zero overhead, deterministic
- Con: Size limited, scope-bound lifetime

**Arena Allocation**:
- Pro: Batch cleanup, flexible size
- Con: Heap-backed, some overhead

**Static Allocation**:
- Pro: Zero runtime allocation
- Con: Fixed at compile time, wastes memory

Choose fixed buffers when you need maximum performance for temporary, bounded allocations.

### Full Tested Code

```zig
// Recipe 18.5: Stack-Based Allocation with FixedBufferAllocator
// This recipe demonstrates using stack-allocated buffers for memory management,
// eliminating heap allocations entirely for improved performance and predictability.

const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;

// ANCHOR: basic_fixed_buffer
// Basic fixed buffer allocator on the stack
test "basic fixed buffer allocator" {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // Allocate from stack buffer
    const slice1 = try allocator.alloc(u32, 10);
    slice1[0] = 42;

    const slice2 = try allocator.alloc(u64, 5);
    slice2[0] = 123456789;

    try testing.expectEqual(@as(u32, 42), slice1[0]);
    try testing.expectEqual(@as(u64, 123456789), slice2[0]);

    // All memory automatically freed when buffer goes out of scope
}
// ANCHOR_END: basic_fixed_buffer

// ANCHOR: buffer_overflow
// Handling buffer overflow
test "fixed buffer overflow" {
    var buffer: [100]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // This fits
    const slice1 = try allocator.alloc(u8, 50);
    try testing.expectEqual(@as(usize, 50), slice1.len);

    // This also fits
    const slice2 = try allocator.alloc(u8, 40);
    try testing.expectEqual(@as(usize, 40), slice2.len);

    // This exceeds buffer capacity
    const result = allocator.alloc(u8, 20);
    try testing.expectError(error.OutOfMemory, result);
}
// ANCHOR_END: buffer_overflow

// ANCHOR: buffer_reset
// Resetting fixed buffer allocator
test "resetting fixed buffer" {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // Use some memory
    _ = try allocator.alloc(u8, 500);
    try testing.expectEqual(@as(usize, 500), fba.end_index);

    // Reset to reuse buffer
    fba.reset();
    try testing.expectEqual(@as(usize, 0), fba.end_index);

    // Can allocate again
    const slice = try allocator.alloc(u8, 800);
    try testing.expectEqual(@as(usize, 800), slice.len);
}
// ANCHOR_END: buffer_reset

// ANCHOR: thread_local_buffer
// Thread-local stack buffer pattern
threadlocal var thread_buffer: [4096]u8 = undefined;

fn processWithThreadLocal(data: []const u8) ![]u8 {
    var fba = std.heap.FixedBufferAllocator.init(&thread_buffer);
    const allocator = fba.allocator();

    // Process data using thread-local buffer
    const result = try allocator.alloc(u8, data.len * 2);
    for (data, 0..) |byte, i| {
        result[i * 2] = byte;
        result[i * 2 + 1] = byte;
    }

    return result;
}

test "thread-local buffer" {
    const input = "Hello";
    const output = try processWithThreadLocal(input);

    try testing.expectEqual(@as(usize, 10), output.len);
    try testing.expectEqual(@as(u8, 'H'), output[0]);
    try testing.expectEqual(@as(u8, 'H'), output[1]);
}
// ANCHOR_END: thread_local_buffer

// ANCHOR: nested_fixed_buffers
// Nested fixed buffer allocators
fn parseJson(allocator: Allocator, json: []const u8) !u32 {
    // Inner function with its own stack buffer
    var buffer: [256]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const temp_allocator = fba.allocator();

    // Parse using temporary buffer
    _ = json;
    const temp = try temp_allocator.alloc(u8, 100);
    @memset(temp, 0);

    // Real result allocated from parent allocator
    _ = allocator;
    return 42;
}

test "nested fixed buffers" {
    var outer_buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&outer_buffer);
    const allocator = fba.allocator();

    const result = try parseJson(allocator, "{\"value\": 42}");
    try testing.expectEqual(@as(u32, 42), result);
}
// ANCHOR_END: nested_fixed_buffers

// ANCHOR: string_building
// String building with fixed buffer
fn buildMessage(allocator: Allocator, name: []const u8, count: u32) ![]const u8 {
    return try std.fmt.allocPrint(allocator, "Hello, {s}! Count: {d}", .{ name, count });
}

test "string building with fixed buffer" {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    const msg1 = try buildMessage(allocator, "Alice", 10);
    try testing.expect(std.mem.eql(u8, "Hello, Alice! Count: 10", msg1));

    fba.reset();

    const msg2 = try buildMessage(allocator, "Bob", 20);
    try testing.expect(std.mem.eql(u8, "Hello, Bob! Count: 20", msg2));
}
// ANCHOR_END: string_building

// ANCHOR: performance_comparison
// Performance comparison: stack vs heap
test "stack vs heap performance" {
    const iterations = 1000;

    // Heap allocation
    var heap_timer = try std.time.Timer.start();
    {
        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const slice = try testing.allocator.alloc(u8, 100);
            @memset(slice, 0);
            testing.allocator.free(slice);
        }
    }
    const heap_ns = heap_timer.read();

    // Stack allocation
    var stack_timer = try std.time.Timer.start();
    {
        var buffer: [100 * 1000]u8 = undefined;
        var fba = std.heap.FixedBufferAllocator.init(&buffer);
        const allocator = fba.allocator();

        var i: usize = 0;
        while (i < iterations) : (i += 1) {
            const slice = try allocator.alloc(u8, 100);
            @memset(slice, 0);
        }
    }
    const stack_ns = stack_timer.read();

    std.debug.print("\nHeap: {d}ns, Stack: {d}ns, Speedup: {d:.2}x\n", .{
        heap_ns,
        stack_ns,
        @as(f64, @floatFromInt(heap_ns)) / @as(f64, @floatFromInt(stack_ns)),
    });
}
// ANCHOR_END: performance_comparison

// ANCHOR: request_handler
// Request handler pattern with stack buffer
const Request = struct {
    path: []const u8,
    headers: std.StringHashMap([]const u8),

    pub fn init(allocator: Allocator, path: []const u8) !Request {
        return .{
            .path = try allocator.dupe(u8, path),
            .headers = std.StringHashMap([]const u8).init(allocator),
        };
    }
};

fn handleRequest(path: []const u8) ![]const u8 {
    var buffer: [4096]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    var req = try Request.init(allocator, path);
    _ = try req.headers.put("Content-Type", "application/json");

    return try std.fmt.allocPrint(allocator, "{{\"path\": \"{s}\"}}", .{req.path});
}

test "request handler with stack buffer" {
    const response = try handleRequest("/api/users");
    try testing.expect(std.mem.indexOf(u8, response, "/api/users") != null);
}
// ANCHOR_END: request_handler

// ANCHOR: fallback_allocator
// Fallback allocator: try stack first, then heap
fn processWithFallback(stack_allocator: Allocator, heap_allocator: Allocator, size: usize) ![]u8 {
    // Try stack allocation first
    if (stack_allocator.alloc(u8, size)) |slice| {
        return slice;
    } else |_| {
        // Fall back to heap if stack is exhausted
        return try heap_allocator.alloc(u8, size);
    }
}

test "fallback allocator" {
    var buffer: [100]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const stack_allocator = fba.allocator();

    // Small allocation uses stack
    const small = try processWithFallback(stack_allocator, testing.allocator, 50);
    try testing.expectEqual(@as(usize, 50), small.len);

    // Large allocation uses heap
    const large = try processWithFallback(stack_allocator, testing.allocator, 200);
    defer testing.allocator.free(large);
    try testing.expectEqual(@as(usize, 200), large.len);
}
// ANCHOR_END: fallback_allocator

// ANCHOR: scoped_buffer
// Scoped buffer pattern for temporary processing
fn processDataWithStack(input: []const u8) !u32 {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // All allocations from stack buffer
    const temp = try allocator.alloc(u8, input.len);
    @memcpy(temp, input);

    const upper = try allocator.alloc(u8, input.len);
    for (input, 0..) |c, i| {
        upper[i] = std.ascii.toUpper(c);
    }

    return @as(u32, @intCast(temp.len + upper.len));
}

test "scoped buffer pattern" {
    const result = try processDataWithStack("Hello, World!");
    try testing.expectEqual(@as(u32, 26), result);
}
// ANCHOR_END: scoped_buffer
```

### See Also

- Recipe 18.2: Arena Allocator Patterns
- Recipe 18.1: Custom Allocator Implementation
- Recipe 0.12: Understanding Allocators

---

## Recipe 18.6: Tracking and Debugging Memory Usage {#recipe-18-6}

**Tags:** allocators, arena-allocator, arraylist, data-structures, error-handling, hashmap, memory, memory-allocators, pointers, resource-cleanup, slices, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/18-memory-management/recipe_18_6.zig`

### Problem

You need to detect memory leaks, track allocation patterns, profile memory usage, or debug memory corruption issues. You want to understand where allocations occur, how much memory is used, and whether all allocations are properly freed.

### Solution

Zig provides several tools and patterns for tracking and debugging memory, from the built-in testing allocator to custom allocator wrappers that log, validate, and profile allocations.

### Testing Allocator for Leak Detection

Use the testing allocator to automatically detect memory leaks:

```zig
// Using testing allocator for leak detection
test "testing allocator detects leaks" {
    // testing.allocator automatically detects leaks
    const slice = try testing.allocator.alloc(u8, 100);
    defer testing.allocator.free(slice); // Comment this to see leak detection

    slice[0] = 42;
    try testing.expectEqual(@as(u8, 42), slice[0]);

    // If defer is commented out, test fails with leak detection
}
```

### Logging Allocator

Wrap an allocator to log all allocations and frees:

```zig
// Logging allocator wrapper
const LoggingAllocator = struct {
    parent: Allocator,
    alloc_count: *usize,
    free_count: *usize,
    bytes_allocated: *usize,

    pub fn init(parent: Allocator, alloc_count: *usize, free_count: *usize, bytes_allocated: *usize) LoggingAllocator {
        return .{
            .parent = parent,
            .alloc_count = alloc_count,
            .free_count = free_count,
            .bytes_allocated = bytes_allocated,
        };
    }

    pub fn allocator(self: *LoggingAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *LoggingAllocator = @ptrCast(@alignCast(ctx));
        const result = self.parent.rawAlloc(len, ptr_align, ret_addr);

        if (result) |ptr| {
            self.alloc_count.* += 1;
            self.bytes_allocated.* += len;
            std.debug.print("ALLOC: {d} bytes at {*}\n", .{ len, ptr });
            return ptr;
        }
        return null;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *LoggingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *LoggingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *LoggingAllocator = @ptrCast(@alignCast(ctx));
        self.free_count.* += 1;
        std.debug.print("FREE: {d} bytes at {*}\n", .{ buf.len, buf.ptr });
        self.parent.rawFree(buf, buf_align, ret_addr);
    }
};

test "logging allocator" {
    var alloc_count: usize = 0;
    var free_count: usize = 0;
    var bytes_allocated: usize = 0;

    var logging = LoggingAllocator.init(
        testing.allocator,
        &alloc_count,
        &free_count,
        &bytes_allocated,
    );
    const allocator = logging.allocator();

    const slice1 = try allocator.alloc(u32, 10);
    defer allocator.free(slice1);

    const slice2 = try allocator.alloc(u64, 5);
    defer allocator.free(slice2);

    try testing.expectEqual(@as(usize, 2), alloc_count);
    try testing.expect(bytes_allocated > 0);
}
```

### Tracking Allocator

Track all active allocations with detailed information:

```zig
// Allocation tracking allocator
const AllocationInfo = struct {
    size: usize,
    address: usize,
    return_address: usize,
};

const TrackingAllocator = struct {
    parent: Allocator,
    allocations: std.ArrayList(AllocationInfo),
    total_allocated: usize,
    peak_allocated: usize,

    pub fn init(parent: Allocator) TrackingAllocator {
        return .{
            .parent = parent,
            .allocations = .{},
            .total_allocated = 0,
            .peak_allocated = 0,
        };
    }

    pub fn deinit(self: *TrackingAllocator) void {
        self.allocations.deinit(self.parent);
    }

    pub fn allocator(self: *TrackingAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        const result = self.parent.rawAlloc(len, ptr_align, ret_addr) orelse return null;

        self.allocations.append(self.parent, .{
            .size = len,
            .address = @intFromPtr(result),
            .return_address = ret_addr,
        }) catch {};

        self.total_allocated += len;
        if (self.total_allocated > self.peak_allocated) {
            self.peak_allocated = self.total_allocated;
        }

        return result;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        const addr = @intFromPtr(buf.ptr);

        // Remove from tracking
        var i: usize = 0;
        while (i < self.allocations.items.len) {
            if (self.allocations.items[i].address == addr) {
                self.total_allocated -= self.allocations.items[i].size;
                _ = self.allocations.swapRemove(i);
                break;
            }
            i += 1;
        }

        self.parent.rawFree(buf, buf_align, ret_addr);
    }

    pub fn reportLeaks(self: *TrackingAllocator) void {
        if (self.allocations.items.len > 0) {
            std.debug.print("\n=== MEMORY LEAKS DETECTED ===\n", .{});
            for (self.allocations.items) |info| {
                std.debug.print("Leak: {d} bytes at 0x{x} (from 0x{x})\n", .{
                    info.size,
                    info.address,
                    info.return_address,
                });
            }
        }
    }
};

test "tracking allocator" {
    var tracker = TrackingAllocator.init(testing.allocator);
    defer tracker.deinit();

    const allocator = tracker.allocator();

    const slice1 = try allocator.alloc(u8, 100);
    try testing.expectEqual(@as(usize, 100), tracker.total_allocated);

    const slice2 = try allocator.alloc(u32, 50);
    try testing.expect(tracker.total_allocated > 100);
    try testing.expect(tracker.peak_allocated >= tracker.total_allocated);

    allocator.free(slice1);
    allocator.free(slice2);

    try testing.expectEqual(@as(usize, 0), tracker.total_allocated);
    try testing.expectEqual(@as(usize, 0), tracker.allocations.items.len);
}
```

### Validating Allocator

Detect buffer overruns with canary values:

```zig
// Validating allocator with bounds checking
const ValidatingAllocator = struct {
    const CANARY: u32 = 0xDEADBEEF;

    parent: Allocator,

    pub fn init(parent: Allocator) ValidatingAllocator {
        return .{ .parent = parent };
    }

    pub fn allocator(self: *ValidatingAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *ValidatingAllocator = @ptrCast(@alignCast(ctx));

        // Allocate extra space for canaries
        const total_len = len + @sizeOf(u32) * 2;
        const raw = self.parent.rawAlloc(total_len, ptr_align, ret_addr) orelse return null;

        // Write front canary
        const front_canary: *u32 = @ptrCast(@alignCast(raw));
        front_canary.* = CANARY;

        // Write back canary
        const back_canary: *u32 = @ptrCast(@alignCast(raw + @sizeOf(u32) + len));
        back_canary.* = CANARY;

        return raw + @sizeOf(u32);
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = new_len;
        _ = ret_addr;
        return false; // Don't support resize for simplicity
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = new_len;
        _ = ret_addr;
        return null;
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *ValidatingAllocator = @ptrCast(@alignCast(ctx));

        const raw = buf.ptr - @sizeOf(u32);

        // Check front canary
        const front_canary: *u32 = @ptrCast(@alignCast(raw));
        if (front_canary.* != CANARY) {
            std.debug.panic("CORRUPTION: Front canary overwritten!\n", .{});
        }

        // Check back canary
        const back_canary: *u32 = @ptrCast(@alignCast(raw + @sizeOf(u32) + buf.len));
        if (back_canary.* != CANARY) {
            std.debug.panic("CORRUPTION: Back canary overwritten!\n", .{});
        }

        const total_len = buf.len + @sizeOf(u32) * 2;
        self.parent.rawFree(raw[0..total_len], buf_align, ret_addr);
    }
};

test "validating allocator" {
    var validating = ValidatingAllocator.init(testing.allocator);
    const allocator = validating.allocator();

    const slice = try allocator.alloc(u8, 100);
    defer allocator.free(slice);

    // Normal use - canaries should remain intact
    @memset(slice, 42);
    try testing.expectEqual(@as(u8, 42), slice[0]);
}
```

### Memory Profiler

Profile allocation patterns by size:

```zig
// Simple memory profiler
const MemoryProfiler = struct {
    allocations_by_size: std.AutoHashMap(usize, usize),
    parent: Allocator,

    pub fn init(parent: Allocator) !MemoryProfiler {
        return .{
            .allocations_by_size = std.AutoHashMap(usize, usize).init(parent),
            .parent = parent,
        };
    }

    pub fn deinit(self: *MemoryProfiler) void {
        self.allocations_by_size.deinit();
    }

    pub fn allocator(self: *MemoryProfiler) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *MemoryProfiler = @ptrCast(@alignCast(ctx));
        const result = self.parent.rawAlloc(len, ptr_align, ret_addr) orelse return null;

        const entry = self.allocations_by_size.getOrPut(len) catch return result;
        if (!entry.found_existing) {
            entry.value_ptr.* = 0;
        }
        entry.value_ptr.* += 1;

        return result;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *MemoryProfiler = @ptrCast(@alignCast(ctx));
        return self.parent.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *MemoryProfiler = @ptrCast(@alignCast(ctx));
        return self.parent.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *MemoryProfiler = @ptrCast(@alignCast(ctx));
        self.parent.rawFree(buf, buf_align, ret_addr);
    }

    pub fn report(self: *MemoryProfiler) void {
        std.debug.print("\n=== MEMORY PROFILE ===\n", .{});
        var iter = self.allocations_by_size.iterator();
        while (iter.next()) |entry| {
            std.debug.print("Size {d:>6} bytes: {d:>4} allocations\n", .{ entry.key_ptr.*, entry.value_ptr.* });
        }
    }
};

test "memory profiler" {
    var profiler = try MemoryProfiler.init(testing.allocator);
    defer profiler.deinit();

    const allocator = profiler.allocator();

    const s1 = try allocator.alloc(u8, 100);
    defer allocator.free(s1);

    const s2 = try allocator.alloc(u8, 100);
    defer allocator.free(s2);

    const s3 = try allocator.alloc(u8, 200);
    defer allocator.free(s3);

    try testing.expectEqual(@as(usize, 2), profiler.allocations_by_size.count());
}
```

### Discussion

Memory tracking and debugging tools help identify leaks, corruption, and inefficient allocation patterns, ensuring robust and efficient memory management.

### The Testing Allocator

Zig's `std.testing.allocator` is a wrapper that:

1. Tracks all allocations with metadata
2. Detects memory leaks at test end
3. Catches double-frees
4. Reports leaked allocations with stack traces

It's the primary tool for ensuring tests don't leak memory.

**Always use `testing.allocator` in tests, never `std.heap.page_allocator` or other allocators.**

### Allocator Wrapper Pattern

All debugging allocators follow the wrapper pattern:

```zig
const DebugAllocator = struct {
    parent: Allocator,
    // ... debug state

    pub fn allocator(self: *Self) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(...) ?[*]u8 {
        // Debug logic here
        return self.parent.rawAlloc(...);
    }
};
```

This allows composing multiple debugging layers.

### Logging for Debugging

The logging allocator prints every allocation and free:

**Benefits**:
- See allocation order and patterns
- Identify unexpected allocations
- Track allocation call sites
- Debug allocation/free mismatches

**Drawbacks**:
- Very verbose output
- Slows execution significantly
- Not suitable for production

Use logging allocators during development to understand memory behavior.

### Tracking Active Allocations

The tracking allocator maintains a list of all active allocations:

**Features**:
- Stores size, address, and return address
- Tracks total and peak allocated memory
- Can report leaks with call sites
- Enables memory usage profiling

**Overhead**:
- Extra allocation per tracked allocation (metadata)
- Linear search on free (can be optimized with hash map)
- Memory for tracking list

Use tracking allocators to diagnose leaks and understand memory usage patterns.

### Canary Detection

Validating allocators use "canary" values to detect buffer overruns:

```zig
[CANARY][User Data][CANARY]
```

**How It Works**:
1. Allocate extra space before and after user data
2. Write known canary values (e.g., `0xDEADBEEF`)
3. On free, check if canaries are still intact
4. Panic if canaries were overwritten

This catches buffer overflows that write past allocation boundaries.

**Limitations**:
- Only detects overruns at free time
- Doesn't catch reads past boundaries
- Adds memory overhead (2 * canary size per allocation)

### Memory Profiling

Memory profilers track allocation patterns:

**Allocation Size Distribution**: How many allocations of each size?
**Allocation Frequency**: Which sizes are allocated most often?
**Temporal Patterns**: When do allocations occur?

This data helps:
- Identify opportunities for pooling
- Right-size pre-allocated buffers
- Detect unexpected allocation patterns
- Optimize hot allocation paths

### Composing Debug Allocators

Stack multiple wrappers for combined functionality:

```zig
var tracking = TrackingAllocator.init(testing.allocator);
defer tracking.deinit();

var validating = ValidatingAllocator.init(tracking.allocator());
const allocator = validating.allocator();

// Now we have: testing.allocator -> tracking -> validating -> your code
// Leak detection, allocation tracking, AND canary detection!
```

Each layer adds its own checks and tracking.

### Debugging Memory Leaks

To find a leak:

1. **Enable Tracking**: Use tracking allocator or testing allocator
2. **Run Code**: Exercise the code path
3. **Check Report**: Look for non-freed allocations
4. **Find Source**: Use return addresses to locate allocation site
5. **Fix Leak**: Add missing `free()` or fix lifetime issue

**Common Leak Patterns**:
- Forgetting `defer allocator.free()`
- Early returns bypassing cleanup
- Exceptions/errors skipping deallocation
- Circular references in graph structures

### Debugging Corruption

To find corruption:

1. **Enable Validation**: Use validating allocator
2. **Run Until Crash**: Execute until corruption detected
3. **Examine Canaries**: Check which canary was overwritten
4. **Find Culprit**: Look for buffer writes near crash time
5. **Fix Bug**: Add bounds checking, fix off-by-one errors

**Common Corruption Patterns**:
- Off-by-one errors in loops
- Incorrect size calculations
- Pointer arithmetic errors
- String operations without null terminator

### Performance Impact

Debug allocators have performance costs:

**Logging**: 10-100x slowdown (I/O overhead)
**Tracking**: 2-5x slowdown (list management)
**Validation**: 1.1-1.5x slowdown (canary checks)
**Profiling**: 1.5-3x slowdown (hash map updates)

**Only use in debug builds**. Wrap with `if (builtin.mode == .Debug)` for zero production cost.

### Best Practices

**Use Testing Allocator**: Always in tests for automatic leak detection.

**Layered Debugging**: Combine allocators for comprehensive checking.

**Conditional Wrapping**: Enable debug allocators only in debug mode.

**Profile First**: Use profiling to understand patterns before optimizing.

**Fix Leaks Immediately**: Don't accumulate memory leak debt.

**Automate Checks**: Run tests with leak detection in CI.

### Advanced Techniques

**Stack Traces**: Store full stack trace on allocation:

```zig
const info = AllocationInfo{
    .size = len,
    .address = @intFromPtr(result),
    .stack_trace = std.debug.dumpCurrentStackTrace(),
};
```

**Allocation Tagging**: Tag allocations by subsystem:

```zig
const Tagged = struct {
    tag: []const u8,
    parent: Allocator,
};
```

**Time Tracking**: Record allocation timestamps to detect patterns.

**Heap Visualization**: Generate graphs of allocation/free patterns.

### Integration with Tools

**Valgrind**: Not needed for leak detection (use testing allocator), but useful for:
- Finding use-after-free
- Detecting uninitialized reads
- Checking cache behavior

**AddressSanitizer**: Compile with `-fsanitize=address` for additional checking:
- Buffer overflows
- Use-after-free
- Memory leaks
- Stack corruption

**Zig's Built-in Safety**: `-Doptimize=Debug` enables:
- Undefined behavior checks
- Integer overflow detection
- Bounds checking

### Common Debugging Scenarios

**Intermittent Crashes**: Often corruption. Use validating allocator.

**Memory Growth**: Likely leak. Use tracking allocator to find culprit.

**Slow Performance**: Too many allocations. Use profiling allocator.

**Test Failures**: Leak in test. Check testing allocator output.

**Production Issues**: Can't use debug allocators. Enable limited tracking.

### Production Debugging

For production memory issues:

**Metrics**: Track total allocated, allocation rate, free rate
**Sampling**: Only track 1 in N allocations for low overhead
**Aggregation**: Collect allocation size histograms
**Periodic Snapshots**: Dump allocation state periodically
**Limits**: Set hard limits, fail fast on exceeded limits

### Debugging Zig-Specific Issues

**Arena Leaks**: Forget to call `arena.deinit()`. Look for missing defers.

**Pool Leaks**: Objects acquired but not released. Track pool state.

**Circular References**: Use weak references or explicit break cycles.

**Slice Lifetime**: Slices outlive underlying allocation. Validate lifetimes.

**Allocator Mismatch**: Free with different allocator than alloc. Always match.

### Best Practices Summary

1. **Always use `testing.allocator` in tests**
2. **Defer cleanup immediately after allocation**
3. **Use `errdefer` for error path cleanup**
4. **Enable debug allocators in development**
5. **Profile before optimizing**
6. **Fix leaks as they're found**
7. **Automate leak detection in CI**
8. **Document allocation ownership**
9. **Use RAII patterns for automatic cleanup**
10. **Validate assumptions with debug allocators**

### When Not to Debug

**Working Code**: If tests pass and no issues, don't add debug overhead.

**Micro-Optimizations**: Profile first, don't guess.

**Production**: Debug allocators have too much overhead for production.

**Embedded**: Limited resources may preclude debug allocators.

### Full Tested Code

```zig
// Recipe 18.6: Tracking and Debugging Memory Usage
// This recipe demonstrates tools and techniques for tracking memory allocations,
// detecting leaks, profiling usage, and debugging memory-related issues.

const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;

// ANCHOR: testing_allocator
// Using testing allocator for leak detection
test "testing allocator detects leaks" {
    // testing.allocator automatically detects leaks
    const slice = try testing.allocator.alloc(u8, 100);
    defer testing.allocator.free(slice); // Comment this to see leak detection

    slice[0] = 42;
    try testing.expectEqual(@as(u8, 42), slice[0]);

    // If defer is commented out, test fails with leak detection
}
// ANCHOR_END: testing_allocator

// ANCHOR: logging_allocator
// Logging allocator wrapper
const LoggingAllocator = struct {
    parent: Allocator,
    alloc_count: *usize,
    free_count: *usize,
    bytes_allocated: *usize,

    pub fn init(parent: Allocator, alloc_count: *usize, free_count: *usize, bytes_allocated: *usize) LoggingAllocator {
        return .{
            .parent = parent,
            .alloc_count = alloc_count,
            .free_count = free_count,
            .bytes_allocated = bytes_allocated,
        };
    }

    pub fn allocator(self: *LoggingAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *LoggingAllocator = @ptrCast(@alignCast(ctx));
        const result = self.parent.rawAlloc(len, ptr_align, ret_addr);

        if (result) |ptr| {
            self.alloc_count.* += 1;
            self.bytes_allocated.* += len;
            std.debug.print("ALLOC: {d} bytes at {*}\n", .{ len, ptr });
            return ptr;
        }
        return null;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *LoggingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *LoggingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *LoggingAllocator = @ptrCast(@alignCast(ctx));
        self.free_count.* += 1;
        std.debug.print("FREE: {d} bytes at {*}\n", .{ buf.len, buf.ptr });
        self.parent.rawFree(buf, buf_align, ret_addr);
    }
};

test "logging allocator" {
    var alloc_count: usize = 0;
    var free_count: usize = 0;
    var bytes_allocated: usize = 0;

    var logging = LoggingAllocator.init(
        testing.allocator,
        &alloc_count,
        &free_count,
        &bytes_allocated,
    );
    const allocator = logging.allocator();

    const slice1 = try allocator.alloc(u32, 10);
    defer allocator.free(slice1);

    const slice2 = try allocator.alloc(u64, 5);
    defer allocator.free(slice2);

    try testing.expectEqual(@as(usize, 2), alloc_count);
    try testing.expect(bytes_allocated > 0);
}
// ANCHOR_END: logging_allocator

// ANCHOR: tracking_allocator
// Allocation tracking allocator
const AllocationInfo = struct {
    size: usize,
    address: usize,
    return_address: usize,
};

const TrackingAllocator = struct {
    parent: Allocator,
    allocations: std.ArrayList(AllocationInfo),
    total_allocated: usize,
    peak_allocated: usize,

    pub fn init(parent: Allocator) TrackingAllocator {
        return .{
            .parent = parent,
            .allocations = .{},
            .total_allocated = 0,
            .peak_allocated = 0,
        };
    }

    pub fn deinit(self: *TrackingAllocator) void {
        self.allocations.deinit(self.parent);
    }

    pub fn allocator(self: *TrackingAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        const result = self.parent.rawAlloc(len, ptr_align, ret_addr) orelse return null;

        self.allocations.append(self.parent, .{
            .size = len,
            .address = @intFromPtr(result),
            .return_address = ret_addr,
        }) catch {};

        self.total_allocated += len;
        if (self.total_allocated > self.peak_allocated) {
            self.peak_allocated = self.total_allocated;
        }

        return result;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        return self.parent.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        const addr = @intFromPtr(buf.ptr);

        // Remove from tracking
        var i: usize = 0;
        while (i < self.allocations.items.len) {
            if (self.allocations.items[i].address == addr) {
                self.total_allocated -= self.allocations.items[i].size;
                _ = self.allocations.swapRemove(i);
                break;
            }
            i += 1;
        }

        self.parent.rawFree(buf, buf_align, ret_addr);
    }

    pub fn reportLeaks(self: *TrackingAllocator) void {
        if (self.allocations.items.len > 0) {
            std.debug.print("\n=== MEMORY LEAKS DETECTED ===\n", .{});
            for (self.allocations.items) |info| {
                std.debug.print("Leak: {d} bytes at 0x{x} (from 0x{x})\n", .{
                    info.size,
                    info.address,
                    info.return_address,
                });
            }
        }
    }
};

test "tracking allocator" {
    var tracker = TrackingAllocator.init(testing.allocator);
    defer tracker.deinit();

    const allocator = tracker.allocator();

    const slice1 = try allocator.alloc(u8, 100);
    try testing.expectEqual(@as(usize, 100), tracker.total_allocated);

    const slice2 = try allocator.alloc(u32, 50);
    try testing.expect(tracker.total_allocated > 100);
    try testing.expect(tracker.peak_allocated >= tracker.total_allocated);

    allocator.free(slice1);
    allocator.free(slice2);

    try testing.expectEqual(@as(usize, 0), tracker.total_allocated);
    try testing.expectEqual(@as(usize, 0), tracker.allocations.items.len);
}
// ANCHOR_END: tracking_allocator

// ANCHOR: validating_allocator
// Validating allocator with bounds checking
const ValidatingAllocator = struct {
    const CANARY: u32 = 0xDEADBEEF;

    parent: Allocator,

    pub fn init(parent: Allocator) ValidatingAllocator {
        return .{ .parent = parent };
    }

    pub fn allocator(self: *ValidatingAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *ValidatingAllocator = @ptrCast(@alignCast(ctx));

        // Allocate extra space for canaries
        const total_len = len + @sizeOf(u32) * 2;
        const raw = self.parent.rawAlloc(total_len, ptr_align, ret_addr) orelse return null;

        // Write front canary
        const front_canary: *u32 = @ptrCast(@alignCast(raw));
        front_canary.* = CANARY;

        // Write back canary
        const back_canary: *u32 = @ptrCast(@alignCast(raw + @sizeOf(u32) + len));
        back_canary.* = CANARY;

        return raw + @sizeOf(u32);
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = new_len;
        _ = ret_addr;
        return false; // Don't support resize for simplicity
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = new_len;
        _ = ret_addr;
        return null;
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *ValidatingAllocator = @ptrCast(@alignCast(ctx));

        const raw = buf.ptr - @sizeOf(u32);

        // Check front canary
        const front_canary: *u32 = @ptrCast(@alignCast(raw));
        if (front_canary.* != CANARY) {
            std.debug.panic("CORRUPTION: Front canary overwritten!\n", .{});
        }

        // Check back canary
        const back_canary: *u32 = @ptrCast(@alignCast(raw + @sizeOf(u32) + buf.len));
        if (back_canary.* != CANARY) {
            std.debug.panic("CORRUPTION: Back canary overwritten!\n", .{});
        }

        const total_len = buf.len + @sizeOf(u32) * 2;
        self.parent.rawFree(raw[0..total_len], buf_align, ret_addr);
    }
};

test "validating allocator" {
    var validating = ValidatingAllocator.init(testing.allocator);
    const allocator = validating.allocator();

    const slice = try allocator.alloc(u8, 100);
    defer allocator.free(slice);

    // Normal use - canaries should remain intact
    @memset(slice, 42);
    try testing.expectEqual(@as(u8, 42), slice[0]);
}
// ANCHOR_END: validating_allocator

// ANCHOR: memory_profiler
// Simple memory profiler
const MemoryProfiler = struct {
    allocations_by_size: std.AutoHashMap(usize, usize),
    parent: Allocator,

    pub fn init(parent: Allocator) !MemoryProfiler {
        return .{
            .allocations_by_size = std.AutoHashMap(usize, usize).init(parent),
            .parent = parent,
        };
    }

    pub fn deinit(self: *MemoryProfiler) void {
        self.allocations_by_size.deinit();
    }

    pub fn allocator(self: *MemoryProfiler) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *MemoryProfiler = @ptrCast(@alignCast(ctx));
        const result = self.parent.rawAlloc(len, ptr_align, ret_addr) orelse return null;

        const entry = self.allocations_by_size.getOrPut(len) catch return result;
        if (!entry.found_existing) {
            entry.value_ptr.* = 0;
        }
        entry.value_ptr.* += 1;

        return result;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *MemoryProfiler = @ptrCast(@alignCast(ctx));
        return self.parent.rawResize(buf, buf_align, new_len, ret_addr);
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *MemoryProfiler = @ptrCast(@alignCast(ctx));
        return self.parent.rawRemap(buf, buf_align, new_len, ret_addr);
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        const self: *MemoryProfiler = @ptrCast(@alignCast(ctx));
        self.parent.rawFree(buf, buf_align, ret_addr);
    }

    pub fn report(self: *MemoryProfiler) void {
        std.debug.print("\n=== MEMORY PROFILE ===\n", .{});
        var iter = self.allocations_by_size.iterator();
        while (iter.next()) |entry| {
            std.debug.print("Size {d:>6} bytes: {d:>4} allocations\n", .{ entry.key_ptr.*, entry.value_ptr.* });
        }
    }
};

test "memory profiler" {
    var profiler = try MemoryProfiler.init(testing.allocator);
    defer profiler.deinit();

    const allocator = profiler.allocator();

    const s1 = try allocator.alloc(u8, 100);
    defer allocator.free(s1);

    const s2 = try allocator.alloc(u8, 100);
    defer allocator.free(s2);

    const s3 = try allocator.alloc(u8, 200);
    defer allocator.free(s3);

    try testing.expectEqual(@as(usize, 2), profiler.allocations_by_size.count());
}
// ANCHOR_END: memory_profiler
```

### See Also

- Recipe 18.1: Custom Allocator Implementation
- Recipe 18.2: Arena Allocator Patterns
- Recipe 0.13: Testing and Debugging Fundamentals

---
