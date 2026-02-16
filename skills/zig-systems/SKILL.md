---
name: zig-systems
description: Systems programming and performance optimization using Zig. Provides low-level abstractions, memory-safe compiled code, and performance benchmarking. Use for system-level operations, optimization, and interoperability with C/POSIX APIs.
license: MIT
compatibility: Requires Zig 0.11+. Compiles to native binaries with no runtime. POSIX-compatible (Linux, macOS, Windows). Can be called from Clojure, Go, and other languages via FFI.
metadata:
  version: 1.0.0
  author: Claude via Boxxy
  gf3-trit: 0
  trit-role: ERGODIC (Systems Coordinator)
  language: Zig
  zig-version: "0.11+"
  build-system: "zig build"
allowed-tools: "Bash(zig:*) Read"
---

# zig-systems - Systems Programming and Performance

## Overview

**zig-systems** provides low-level systems programming capabilities using Zig - a modern language for systems code with performance of C, memory safety guarantees, and cross-platform compilation.

**Role**: ERGODIC systems coordinator - bridges high-level skill orchestration (Clojure) with native performance code.

## Quick Start

### Install Zig

```bash
# macOS with Homebrew
brew install zig

# Or download from https://ziglang.org/download/
# Verify installation
zig version
```

### Basic Compilation

```bash
# Compile a Zig program
zig build-exe main.zig

# Run compiled binary
./main

# Compile with optimizations
zig build-exe -O ReleaseFast main.zig

# Compile to library (FFI)
zig build-lib main.zig
```

## Language Features

### Memory Safety Without GC

```zig
const std = @import("std");

pub fn main() void {
    // Stack-allocated, no garbage collection
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    const allocator = arena.allocator();

    // Explicit allocation
    var list = std.ArrayList(i32).init(allocator);
    defer list.deinit();

    // Type-safe operations
    try list.append(42);
}
```

### Comptime Metaprogramming

```zig
fn Matrix(comptime T: type, comptime rows: usize, comptime cols: usize) type {
    return struct {
        data: [rows * cols]T,

        fn get(self: @This(), r: usize, c: usize) T {
            return self.data[r * cols + c];
        }
    };
}

// Compile-time type generation
const IntMatrix = Matrix(i32, 3, 3);
```

### C Interoperability

```zig
// Direct C function calls
extern "c" fn malloc(size: usize) ?*anyopaque;
extern "c" fn free(ptr: ?*anyopaque) void;

// Export functions for C/other languages
export fn skill_invoke(input: [*]u8, len: usize) [*]u8 {
    // Process input, return output
}
```

## Project Structure

```
zig-systems/
├── SKILL.md
├── build.zig          # Build configuration
├── scripts/
│   ├── array_sort.zig
│   ├── compression.zig
│   ├── hash_table.zig
│   └── ffi.zig        # FFI/C interop
├── references/
│   ├── ZIG_SYNTAX.md
│   ├── MEMORY_MODEL.md
│   ├── PERFORMANCE.md
│   └── FFI_GUIDE.md
└── assets/
    └── build_template.zig
```

## Common Tasks

### 1. Efficient Sorting

```zig
const std = @import("std");

pub fn sort_i32(allocator: std.mem.Allocator, items: []i32) !void {
    var list = std.ArrayList(i32).init(allocator);
    defer list.deinit();

    try list.appendSlice(items);
    std.sort.sort(i32, list.items, {}, std.sort.asc(i32));
}
```

### 2. Hash Table Operations

```zig
const std = @import("std");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    var map = std.StringHashMap(i32).init(allocator);
    defer map.deinit();

    try map.put("foo", 42);
    if (map.get("foo")) |value| {
        std.debug.print("Found: {}\n", .{value});
    }
}
```

### 3. Compression Algorithm

```zig
pub fn compress(allocator: std.mem.Allocator, data: []const u8) ![]u8 {
    // Implement compression (e.g., DEFLATE, LZ4)
    var output = std.ArrayList(u8).init(allocator);
    defer output.deinit();

    // Compression logic here

    return output.toOwnedSlice();
}
```

### 4. Performance Benchmarking

```zig
const std = @import("std");

pub fn benchmark(comptime name: []const u8, func: fn() void) void {
    var timer = try std.time.Timer.start();
    defer {
        const elapsed = timer.read();
        std.debug.print("{s}: {d}ns\n", .{name, elapsed});
    }

    func();
}
```

## Performance Characteristics

### Compilation Speed
- **Incremental**: ~100ms for small modules
- **Full rebuild**: ~500ms - 2s
- **Release build**: ~1-5s with optimizations

### Runtime Performance
- **Memory usage**: Minimal (no GC overhead)
- **Binary size**: 1-10MB depending on features
- **Startup time**: <1ms for most programs
- **CPU efficiency**: Near-C performance

### Comparison

| Operation | Zig | Go | Java |
|-----------|-----|----|----|
| Array sort (10K items) | ~1ms | ~2ms | ~5ms |
| Hash table insert | ~50ns | ~100ns | ~200ns |
| Memory allocation | ~50ns | ~100ns | ~500ns |
| Binary size (hello) | 2KB | 1MB | 50MB |

## Building Zig Projects

### Simple build.zig

```zig
const std = @import("std");
const Builder = std.build.Builder;

pub fn build(b: *Builder) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe = b.addExecutable(.{
        .name = "my_skill",
        .root_source_file = .{ .path = "main.zig" },
        .target = target,
        .optimize = optimize,
    });

    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);
    const run_step = b.step("run", "Run the app");
    run_step.dependOn(&run_cmd.step);
}
```

### Build Commands

```bash
# Build debug binary
zig build

# Build with optimizations
zig build -Doptimize=ReleaseFast

# Install to prefix
zig build --prefix /usr/local install

# Run tests
zig build test
```

## Integration with Other Skills

### Calling from Clojure

```clojure
(defn call-zig-sort [data]
  "Invoke Zig sort via FFI."
  (shell/sh "zig-systems" "sort" (write-json data)))
```

### Calling from Go

```go
import "C"

//export SkillInvoke
func SkillInvoke(data *C.char) *C.char {
    // Call Zig compiled library
    result := C.zig_compress(data)
    return result
}
```

### Calling from Hy

```hy
(import subprocess)
(setv result (subprocess.run ["zig-systems" "compress" "input.dat"]
                            :capture-output True))
```

## When to Use

- **Performance-critical code**: Sorting, compression, hashing
- **System-level operations**: File I/O, memory management, POSIX APIs
- **Cross-platform binaries**: Compile once, run anywhere (Linux, macOS, Windows)
- **FFI requirements**: Need to call from other languages
- **Memory-constrained systems**: Embedded, IoT, serverless
- **Real-time systems**: Predictable performance, no GC pauses

## When NOT to Use

- High-level business logic (use Clojure)
- Quick prototyping (Hy/Python faster iteration)
- Dynamic typing requirements (Zig is statically typed)
- GC convenience preferred over control

## GF(3) Consideration

While zig-systems is a SINGLE language skill (not a triadic component itself), it coordinates with:

```
Validator (-1) + Coordinator (0) + Generator (+1) ≡ 0 (mod 3)
 [joker]        [zig-systems]    [hy-regime]
       OR
 [joker]      [jo-clojure]       [hy-regime]
```

Zig provides low-level system optimization that the triadic coordinator (jo-clojure or zig-systems) may invoke.

## Debugging

### Runtime Assertions

```zig
const std = @import("std");

pub fn divide(a: i32, b: i32) i32 {
    std.debug.assert(b != 0);  // Panics if false
    return a / b;
}
```

### Error Handling

```zig
const FileOpenError = error {
    FileNotFound,
    PermissionDenied,
};

pub fn open_file(path: []const u8) FileOpenError!*File {
    if (!file_exists(path)) {
        return FileOpenError.FileNotFound;
    }
    // ...
}
```

### Standard Library Utilities

```zig
const std = @import("std");

pub fn main() void {
    std.debug.print("Debug output: {any}\n", .{data});
    std.debug.assert(condition);
    var timer = std.time.Timer.start();
}
```

## Performance Optimization Tips

1. **Use ReleaseFast or ReleaseSmall** optimization levels
2. **Minimize allocations**: Preallocate where possible
3. **Use inline functions**: `inline` keyword for hot paths
4. **Leverage comptime**: Compute at compile time, not runtime
5. **Profile with perf**: `perf record ./binary` then `perf report`
6. **Consider SIMD**: `@Vector` type for parallel operations

## References

- [Zig Language Documentation](https://ziglang.org/documentation/master/)
- [Zig Standard Library](https://ziglang.org/api/)
- [Zig by Example](https://zigbyexample.com/)
- [Memory Model Guide](references/MEMORY_MODEL.md)
- [FFI Integration](references/FFI_GUIDE.md)
- [Performance Tuning](references/PERFORMANCE.md)

## Troubleshooting

**"zig: command not found"**
- Install Zig: `brew install zig`
- Verify: `zig version`
- Update PATH if needed

**Build errors with C libraries**
- Use `zig build-exe main.zig -lc` to link libc
- Declare C imports explicitly: `extern "c" fn malloc(...)`

**Memory leaks in debug mode**
- Use GeneralPurposeAllocator for testing
- Enable leak detection: `std.heap.GeneralPurposeAllocator(.{.safety = true})`

**Binary too large**
- Use ReleaseSmall optimization: `-O ReleaseSmall`
- Strip debug symbols: `strip ./binary`
