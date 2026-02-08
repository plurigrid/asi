---
name: zig
description: "zig skill"
model: inherit
tools: read-only
---

# zig

Zig ecosystem for systems programming without hidden control flow.

## Atomic Skills

| Skill | Commands | Domain |
|-------|----------|--------|
| zig build | build system | Compile, link, cross-compile |
| zig test | testing | Run test blocks |
| zig fmt | formatter | Canonical formatting |
| zls | LSP | Autocomplete, diagnostics |

## Quick Start

```bash
# New project
mkdir myproject && cd myproject
zig init

# Build and run
zig build run

# Test
zig build test

# Format
zig fmt src/

# Cross-compile to WASM
zig build -Dtarget=wasm32-freestanding
```

## build.zig (0.15.2)

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

    const run_step = b.step("run", "Run the application");
    run_step.dependOn(&run_cmd.step);

    const tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&b.addRunArtifact(tests).step);
}
```

## Core Patterns

### Explicit Allocators

```zig
const std = @import("std");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    var list = std.ArrayList(u8).init(allocator);
    defer list.deinit();

    try list.appendSlice("hello");
}
```

### Error Handling

```zig
fn readFile(path: []const u8) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    return file.readToEndAlloc(allocator, 1024 * 1024);
}

// Usage with catch
const dat