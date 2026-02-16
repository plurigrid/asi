# Fundamentals & Philosophy Recipes

*19 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [0.1](#recipe-0-1) | Understanding Zig's Philosophy | beginner |
| [0.2](#recipe-0-2) | Installing Zig and Verifying Your Toolchain | beginner |
| [0.3](#recipe-0-3) | Your First Zig Program | beginner |
| [0.4](#recipe-0-4) | Variables, Constants, and Type Inference | beginner |
| [0.5](#recipe-0-5) | Primitive Data and Basic Arrays | beginner |
| [0.6](#recipe-0-6) | Arrays, ArrayLists, and Slices | beginner |
| [0.7](#recipe-0-7) | Functions and the Standard Library | beginner |
| [0.8](#recipe-0-8) | Control Flow and Iteration | beginner |
| [0.9](#recipe-0-9) | Understanding Pointers and References | beginner |
| [0.10](#recipe-0-10) | Structs, Enums, and Simple Data Models | beginner |
| [0.11](#recipe-0-11) | Optionals, Errors, and Resource Cleanup | beginner |
| [0.12](#recipe-0-12) | Understanding Allocators | beginner |
| [0.13](#recipe-0-13) | Testing and Debugging Fundamentals | beginner |
| [0.14](#recipe-0-14) | Projects, Modules, and Dependencies | beginner |
| [1.1](#recipe-1-1) | Writing Idiomatic Zig Code | beginner |
| [1.2](#recipe-1-2) | Error Handling Patterns | beginner |
| [1.3](#recipe-1-3) | Testing Strategy | beginner |
| [1.4](#recipe-1-4) | When to Pass by Pointer vs Value | beginner |
| [1.5](#recipe-1-5) | Build Modes and Safety | beginner |

---

## Recipe 0.1: Understanding Zig's Philosophy {#recipe-0-1}

**Tags:** allocators, arena-allocator, arraylist, comptime, data-structures, error-handling, fundamentals, memory, pointers, resource-cleanup, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_1.zig`

### Problem

You've programmed in Python, JavaScript, Java, or C++ before. You're comfortable with those languages. So why learn Zig? What makes it different, and why should you care about those differences?

### Solution

Zig is built on four core principles that shape everything in the language:

1. **No hidden memory allocations** - You always know where memory comes from
2. **No hidden control flow** - No exceptions, no operator overloading
3. **Edge cases matter** - Out of memory, integer overflow, and null are explicit
4. **Compilation is code execution** - The compile-time/runtime boundary is fluid

Let's see what these mean in practice.

### Principle 1: No Hidden Memory Allocations

In Python, JavaScript, or Go, memory appears like magic:

```python
# Python - where does the memory come from?
numbers = [1, 2, 3]
numbers.append(4)  # What happens here?
```

In Zig, you must be explicit:

```zig
// Principle 1: No Hidden Memory Allocations
//
// In Python/JavaScript/Go, this is invisible:
//   numbers = [1, 2, 3]  # Where does the memory come from?
//   numbers.append(4)     # What happens here?
//
// In Zig, you must be explicit about where memory comes from:

test "explicit memory allocation" {
    // You must provide an allocator - no magic memory
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }

    const allocator = gpa.allocator();

    // Create a dynamic list - you see exactly where memory comes from
    var numbers = std.ArrayList(i32){};
    defer numbers.deinit(allocator); // You control when it's freed

    try numbers.append(allocator, 1);
    try numbers.append(allocator, 2);
    try numbers.append(allocator, 3);

    try testing.expectEqual(@as(usize, 3), numbers.items.len);
}

test "stack vs heap allocation" {
    // Fixed-size array on the stack - no allocator needed
    const stack_array = [3]i32{ 1, 2, 3 };
    // You can see it's fixed size just by looking at the type: [3]i32

    // For variable-size data, you must use an allocator
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }

    const allocator = gpa.allocator();
    const heap_array = try allocator.alloc(i32, 3);
    defer allocator.free(heap_array);

    heap_array[0] = 1;
    heap_array[1] = 2;
    heap_array[2] = 3;

    try testing.expectEqual(stack_array[0], heap_array[0]);
}
```

This looks like more work (and it is), but you gain:
- **Predictability**: No surprise allocations during performance-critical code
- **Control**: You choose the allocation strategy (arena, pool, stack, etc.)
- **Visibility**: Memory bugs are easier to track down

### Principle 2: No Hidden Control Flow

In Python, Java, or C++, exceptions can jump anywhere:

```python
# Python - might throw! You can't tell by looking
result = parse_number("abc")
process_result(result)  # This might never run
```

In Zig, errors are values and control flow is visible:

```zig
// Principle 2: No Hidden Control Flow
//
// In Python/Java/C++, exceptions can jump anywhere:
//   result = parseNumber("abc")  # Might throw! You can't tell by looking
//   processResult(result)        # This might never run
//
// In Zig, errors are values and control flow is explicit:

fn parseNumber(text: []const u8) !i32 {
    // The ! in the return type tells you this can fail
    return std.fmt.parseInt(i32, text, 10);
}

test "explicit error handling" {
    // Success case - you see the error handling
    const good = try parseNumber("42");
    try testing.expectEqual(@as(i32, 42), good);

    // Error case - no hidden throws, errors are values
    const bad = parseNumber("not a number");
    try testing.expectError(error.InvalidCharacter, bad);
}

test "no operator overloading" {
    // In C++, + might do anything (operator overloading)
    // In Zig, + always means numeric addition

    const a: i32 = 5;
    const b: i32 = 10;
    const sum = a + b; // Always addition, never hidden function calls

    try testing.expectEqual(@as(i32, 15), sum);

    // For complex operations, use explicit functions
    // This makes the cost visible:
    // const result = bigNumber.add(otherBigNumber);  // You see it's a call
}
```

The `!` in the return type (`!i32`) means "this returns an i32 or an error". When you see `try`, you know that line might fail and return early.

When you read Zig code, you can trust what you see. There are no invisible function calls hiding behind operators.

### Principle 3: Edge Cases Matter

Many languages treat edge cases as afterthoughts:

```java
// Java - what if size is negative? RuntimeException at 3am!
int[] array = new int[size];

// C - what if it overflows? Undefined behavior!
int x = a + b;

// Java - what if key doesn't exist? NullPointerException!
Object obj = map.get(key);
```

Zig forces you to think about these cases upfront:

```zig
// Principle 3: Edge Cases Matter
//
// In many languages, edge cases cause crashes:
//   int[] array = new int[size];  // What if size is negative? Crash!
//   int x = a + b;                 // What if it overflows? Undefined!
//   Object obj = map.get(key);     // What if key doesn't exist? Null!
//
// Zig forces you to handle edge cases explicitly:

test "out of memory is an error, not a crash" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }

    const allocator = gpa.allocator();

    // Allocation can fail - the ! forces you to handle it
    const array = allocator.alloc(i32, 100) catch {
        // Handle OOM explicitly
        return error.SkipZigTest; // In real code, you'd handle this
    };
    defer allocator.free(array);

    try testing.expect(array.len == 100);
}

test "integer overflow is checked in debug mode" {
    // In debug mode, overflow causes a panic (fail-fast)
    // In release mode, you choose: wrapping, saturating, or checked

    const a: i8 = 127; // Max for i8

    // This would panic in debug mode:
    // const overflow = a + 1;  // Overflow detected!

    // Make overflow behavior explicit:
    const wrapped = a +% 1; // Wrapping: 127 + 1 = -128

    // For saturating, use a conditional or saturating arithmetic
    const saturated: i8 = if (a == 127) 127 else a + 1;

    try testing.expectEqual(@as(i8, -128), wrapped);
    try testing.expectEqual(@as(i8, 127), saturated);
}

test "optionals handle absence explicitly" {
    // In Java/C++, null can cause crashes anywhere
    // In Zig, you must opt-in to nullable values with ?T

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    // Search returns an optional - might not find it
    const found: ?i32 = for (numbers) |n| {
        if (n == 3) break n;
    } else null;

    // You must handle the null case explicitly
    const result = found orelse 0; // Provide default
    try testing.expectEqual(@as(i32, 3), result);

    const not_found: ?i32 = for (numbers) |n| {
        if (n == 99) break n;
    } else null;

    try testing.expectEqual(@as(?i32, null), not_found);
}
```

### Principle 4: Compilation is Code Execution

Zig blurs the line between compile-time and runtime. Code that can run at compile time will run at compile time. This gives you metaprogramming without needing a separate macro language:

```zig
test "comptime: compilation is code execution" {
    // Principle 4: Comptime Philosophy
    //
    // Zig blurs the line between compile-time and runtime
    // Code that can run at compile-time will run at compile-time
    // This gives you metaprogramming without a separate macro language

    // This runs at compile time - zero runtime cost
    const array_size = comptime blk: {
        var size: u32 = 0;
        var i: u32 = 1;
        while (i <= 10) : (i += 1) {
            size += i;
        }
        break :blk size;
    };

    // array_size is computed at compile time
    try testing.expectEqual(@as(u32, 55), array_size);

    // You can create types at compile time
    const IntArray = [array_size]i32;
    const arr: IntArray = undefined;
    try testing.expectEqual(@as(usize, 55), arr.len);
}
```

The array size is calculated at compile time (1+2+3+...+10 = 55) and baked into the binary. Zero runtime cost.

### Discussion

### Why These Principles Matter

These principles might feel restrictive at first, especially if you're used to garbage-collected languages. But they exist for good reasons:

**No hidden allocations** means:
- Your performance is predictable
- No garbage collection pauses
- Memory bugs are local, not global

**No hidden control flow** means:
- You can read code top to bottom
- No invisible jumps from exceptions
- The cost of operations is visible

**Edge cases matter** means:
- Bugs are found at compile time or development
- Not at 3am in production
- Systems are more reliable

**Comptime** means:
- Zero-cost abstractions are real
- Generic programming without runtime overhead
- Type safety without sacrificing performance

### The Tradeoff

Yes, Zig requires more upfront thinking than Python or Go. You'll type more. You'll think harder about memory and errors.

But here's what you get:
- **No surprises**: What you see is what you get
- **Predictable performance**: No hidden costs
- **Catch bugs early**: Compile-time errors beat runtime crashes
- **Full control**: You decide how your program behaves

### Coming from Other Languages

**From Python/JavaScript/Go:**
- You'll miss garbage collection at first
- But you'll appreciate knowing exactly when allocations happen
- And you'll love that your programs start instantly (no GC setup)

**From C/C++:**
- You'll appreciate memory safety without a runtime
- And you'll love that undefined behavior is mostly eliminated
- But you'll need to unlearn some habits (explicit allocators, no malloc/free)

**From Rust:**
- You'll find Zig simpler (no borrow checker)
- But you'll need to be more careful (less compile-time safety)
- And you'll appreciate the simplicity of manual memory management

### Full Tested Code

```zig
// Recipe 0.1: Understanding Zig's Philosophy
// Target Zig Version: 0.15.2
//
// This recipe demonstrates the core principles that make Zig different from
// other languages. These examples show why Zig makes the choices it does.

const std = @import("std");
const testing = std.testing;

// ANCHOR: no_hidden_allocation
// Principle 1: No Hidden Memory Allocations
//
// In Python/JavaScript/Go, this is invisible:
//   numbers = [1, 2, 3]  # Where does the memory come from?
//   numbers.append(4)     # What happens here?
//
// In Zig, you must be explicit about where memory comes from:

test "explicit memory allocation" {
    // You must provide an allocator - no magic memory
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }

    const allocator = gpa.allocator();

    // Create a dynamic list - you see exactly where memory comes from
    var numbers = std.ArrayList(i32){};
    defer numbers.deinit(allocator); // You control when it's freed

    try numbers.append(allocator, 1);
    try numbers.append(allocator, 2);
    try numbers.append(allocator, 3);

    try testing.expectEqual(@as(usize, 3), numbers.items.len);
}

test "stack vs heap allocation" {
    // Fixed-size array on the stack - no allocator needed
    const stack_array = [3]i32{ 1, 2, 3 };
    // You can see it's fixed size just by looking at the type: [3]i32

    // For variable-size data, you must use an allocator
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }

    const allocator = gpa.allocator();
    const heap_array = try allocator.alloc(i32, 3);
    defer allocator.free(heap_array);

    heap_array[0] = 1;
    heap_array[1] = 2;
    heap_array[2] = 3;

    try testing.expectEqual(stack_array[0], heap_array[0]);
}
// ANCHOR_END: no_hidden_allocation

// ANCHOR: no_hidden_control_flow
// Principle 2: No Hidden Control Flow
//
// In Python/Java/C++, exceptions can jump anywhere:
//   result = parseNumber("abc")  # Might throw! You can't tell by looking
//   processResult(result)        # This might never run
//
// In Zig, errors are values and control flow is explicit:

fn parseNumber(text: []const u8) !i32 {
    // The ! in the return type tells you this can fail
    return std.fmt.parseInt(i32, text, 10);
}

test "explicit error handling" {
    // Success case - you see the error handling
    const good = try parseNumber("42");
    try testing.expectEqual(@as(i32, 42), good);

    // Error case - no hidden throws, errors are values
    const bad = parseNumber("not a number");
    try testing.expectError(error.InvalidCharacter, bad);
}

test "no operator overloading" {
    // In C++, + might do anything (operator overloading)
    // In Zig, + always means numeric addition

    const a: i32 = 5;
    const b: i32 = 10;
    const sum = a + b; // Always addition, never hidden function calls

    try testing.expectEqual(@as(i32, 15), sum);

    // For complex operations, use explicit functions
    // This makes the cost visible:
    // const result = bigNumber.add(otherBigNumber);  // You see it's a call
}
// ANCHOR_END: no_hidden_control_flow

// ANCHOR: edge_cases_matter
// Principle 3: Edge Cases Matter
//
// In many languages, edge cases cause crashes:
//   int[] array = new int[size];  // What if size is negative? Crash!
//   int x = a + b;                 // What if it overflows? Undefined!
//   Object obj = map.get(key);     // What if key doesn't exist? Null!
//
// Zig forces you to handle edge cases explicitly:

test "out of memory is an error, not a crash" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }

    const allocator = gpa.allocator();

    // Allocation can fail - the ! forces you to handle it
    const array = allocator.alloc(i32, 100) catch {
        // Handle OOM explicitly
        return error.SkipZigTest; // In real code, you'd handle this
    };
    defer allocator.free(array);

    try testing.expect(array.len == 100);
}

test "integer overflow is checked in debug mode" {
    // In debug mode, overflow causes a panic (fail-fast)
    // In release mode, you choose: wrapping, saturating, or checked

    const a: i8 = 127; // Max for i8

    // This would panic in debug mode:
    // const overflow = a + 1;  // Overflow detected!

    // Make overflow behavior explicit:
    const wrapped = a +% 1; // Wrapping: 127 + 1 = -128

    // For saturating, use a conditional or saturating arithmetic
    const saturated: i8 = if (a == 127) 127 else a + 1;

    try testing.expectEqual(@as(i8, -128), wrapped);
    try testing.expectEqual(@as(i8, 127), saturated);
}

test "optionals handle absence explicitly" {
    // In Java/C++, null can cause crashes anywhere
    // In Zig, you must opt-in to nullable values with ?T

    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    // Search returns an optional - might not find it
    const found: ?i32 = for (numbers) |n| {
        if (n == 3) break n;
    } else null;

    // You must handle the null case explicitly
    const result = found orelse 0; // Provide default
    try testing.expectEqual(@as(i32, 3), result);

    const not_found: ?i32 = for (numbers) |n| {
        if (n == 99) break n;
    } else null;

    try testing.expectEqual(@as(?i32, null), not_found);
}
// ANCHOR_END: edge_cases_matter

// ANCHOR: comptime_execution
test "comptime: compilation is code execution" {
    // Principle 4: Comptime Philosophy
    //
    // Zig blurs the line between compile-time and runtime
    // Code that can run at compile-time will run at compile-time
    // This gives you metaprogramming without a separate macro language

    // This runs at compile time - zero runtime cost
    const array_size = comptime blk: {
        var size: u32 = 0;
        var i: u32 = 1;
        while (i <= 10) : (i += 1) {
            size += i;
        }
        break :blk size;
    };

    // array_size is computed at compile time
    try testing.expectEqual(@as(u32, 55), array_size);

    // You can create types at compile time
    const IntArray = [array_size]i32;
    const arr: IntArray = undefined;
    try testing.expectEqual(@as(usize, 55), arr.len);
}
// ANCHOR_END: comptime_execution

// Summary:
// 1. No hidden allocations - you see where memory comes from
// 2. No hidden control flow - no exceptions, no operator overloading
// 3. Edge cases matter - OOM, overflow, null are explicit
// 4. Comptime - compile-time execution for zero-cost abstractions
//
// This philosophy means more typing upfront, but:
// - No surprises in production
// - Performance is predictable
// - Bugs are found at compile time, not 3am in production
```

### See Also

- Recipe 0.12: Understanding Allocators
- Recipe 0.11: Optionals, Errors, and Resource Cleanup
- Recipe 1.1: Idiomatic Zig

---

## Recipe 0.2: Installing Zig and Verifying Your Toolchain {#recipe-0-2}

**Tags:** error-handling, fundamentals, http, json, networking, parsing, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_2.zig`

### Problem

You want to start programming in Zig. You need to download it, install it, and make sure everything works before writing any code.

### Solution

There are two ways to install Zig: using a package manager (easiest) or downloading manually (for specific version control).

### Option A: Package Managers (Recommended)

The easiest way to install Zig is through your system's package manager. For a complete list of options, see the [official Zig package manager guide](https://github.com/ziglang/zig/wiki/Install-Zig-from-a-Package-Manager).

**macOS (Homebrew):**
```bash
brew install zig
```

**Linux (various):**
```bash
# Ubuntu/Debian (via snap)
snap install zig --classic --beta

# Arch Linux
pacman -S zig

# Fedora
dnf install zig

# Nix
nix-env -i zig
```

**Windows:**
```powershell
# Using winget
winget install zig.zig

# Using Scoop
scoop install zig

# Using Chocolatey
choco install zig
```

After installing via package manager, skip to **Step 3: Verify Installation**.

---

### Option B: Manual Download

If you need a specific version (like 0.15.2 for this cookbook) or your package manager doesn't have Zig, download it manually.

#### Step 1: Download Zig

Visit [https://ziglang.org/download/](https://ziglang.org/download/) and choose:

- **0.15.2** (stable - recommended for this cookbook)
- Or the latest development build if you want cutting-edge features

Download the archive for your platform:
- **macOS**: `zig-macos-aarch64-0.15.2.tar.xz` (Apple Silicon) or `zig-macos-x86_64-0.15.2.tar.xz` (Intel)
- **Linux**: `zig-linux-x86_64-0.15.2.tar.xz` or your architecture
- **Windows**: `zig-windows-x86_64-0.15.2.zip`

#### Step 2: Extract and Add to PATH

**macOS/Linux:**
```bash
# Extract
tar xf zig-macos-aarch64-0.15.2.tar.xz

# Move to a permanent location
sudo mv zig-macos-aarch64-0.15.2 /usr/local/zig

# Add to PATH (add this to your ~/.zshrc or ~/.bashrc)
export PATH="/usr/local/zig:$PATH"

# Reload your shell
source ~/.zshrc  # or ~/.bashrc
```

**Windows:**
1. Extract the ZIP file to `C:\zig\`
2. Add `C:\zig\` to your PATH environment variable
3. Restart your terminal

---

### Step 3: Verify Installation

Run these commands to verify Zig is installed correctly:

```bash
# Check version
zig version
# Should output: 0.15.2 (or your installed version)

# Check environment
zig env
# Shows paths and configuration
```

### Step 4: Test Your Installation

Create a simple test file to make sure everything works:

```zig
// Verifying Zig Installation
//
// After installing Zig, you should verify it's working correctly.
// This test confirms that the standard library is available and working.

test "verify standard library is available" {
    // If this test runs, Zig is installed and working
    const message = "Zig toolchain is working!";
    try testing.expect(message.len > 0);
}

test "check Zig version info" {
    // You can access version information through builtin
    const version = builtin.zig_version;

    // Verify we're using a reasonable version (not ancient)
    try testing.expect(version.major >= 0);
    try testing.expect(version.minor >= 11); // At least 0.11+

    // The version is available at compile time
    if (version.major == 0 and version.minor == 15) {
        // We're on 0.15.x
        try testing.expect(true);
    }
}
```

Run it:
```bash
zig test verify.zig
```

If you see "All 1 tests passed", you're ready to go!

### Discussion

### Understanding `zig version`

When you run `zig version`, you'll see output like:
```
0.15.2
```

This tells you exactly which version of Zig you're running. This matters because Zig is still evolving, and different versions have different features and APIs.

### Understanding `zig env`

The `zig env` command shows your environment configuration:

```json
{
  "zig_exe": "/usr/local/zig/zig",
  "lib_dir": "/usr/local/zig/lib",
  "std_dir": "/usr/local/zig/lib/std",
  "global_cache_dir": "/Users/you/.cache/zig",
  "version": "0.15.2"
}
```

This tells you:
- Where Zig is installed
- Where the standard library lives
- Where cached build artifacts go

You can check this information in code too:

```zig
// Understanding Your Zig Environment
//
// Zig provides information about the target environment through `builtin`.
// This is useful for cross-compilation and platform-specific code.

test "examine build environment" {
    // What platform are we building for?
    const os_tag = builtin.os.tag;
    const arch = builtin.cpu.arch;

    // Common OS tags: .macos, .linux, .windows
    switch (os_tag) {
        .macos, .linux, .windows => {
            // Major platforms
            try testing.expect(true);
        },
        else => {
            // Zig supports many platforms!
            try testing.expect(true);
        },
    }

    // Common architectures: .x86_64, .aarch64, .x86, .arm
    switch (arch) {
        .x86_64, .aarch64 => {
            // Modern 64-bit architectures
            try testing.expect(true);
        },
        else => {
            // Other architectures supported
            try testing.expect(true);
        },
    }
}
```

This is super useful for cross-compilation (we'll cover that later).

### Code Formatting with `zig fmt`

Zig includes an opinionated code formatter. You don't need to debate formatting styles - just use `zig fmt`:

```bash
# Format a single file
zig fmt myfile.zig

# Format all .zig files in current directory
zig fmt .

# Check if files are formatted (useful for CI)
zig fmt --check .
```

The formatter expects:
- 4-space indentation
- Opening braces on the same line
- Trailing commas in multi-line lists
- Consistent spacing

Example of properly formatted code:

```zig
// Code Formatting with `zig fmt`
//
// Zig has a built-in code formatter. This test verifies that code
// follows standard formatting conventions.

test "demonstrate zig fmt expectations" {
    // Zig fmt expects:
    // - 4-space indentation
    // - Opening braces on same line
    // - Trailing commas in multi-line lists
    // - Consistent spacing

    const array = [_]i32{
        1,
        2,
        3, // Trailing comma expected
    };

    try testing.expectEqual(@as(usize, 3), array.len);

    // Function calls with multiple arguments
    const result = add(
        10,
        20, // Trailing comma
    );

    try testing.expectEqual(@as(i32, 30), result);
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "zig fmt handles various constructs" {
    // Structs with multiple fields
    const Point = struct {
        x: i32,
        y: i32,
    };

    const p = Point{
        .x = 10,
        .y = 20, // Trailing comma
    };

    try testing.expectEqual(@as(i32, 10), p.x);
    try testing.expectEqual(@as(i32, 20), p.y);

    // String concatenation across lines is clear
    const long_string = "This is a long string that might " ++
        "be split across multiple lines " ++
        "for readability";

    try testing.expect(long_string.len > 0);
}
```

**Pro tip**: Set up your editor to run `zig fmt` on save. This keeps your code clean automatically.

### Build Modes

Zig has four build modes that you can check at compile time:

```zig
test "check optimization mode" {
    // Zig has different build modes
    const mode = builtin.mode;

    // Modes: .Debug, .ReleaseSafe, .ReleaseFast, .ReleaseSmall
    switch (mode) {
        .Debug => {
            // This is the default for `zig test`
            // Includes safety checks, slower but safer
            try testing.expect(true);
        },
        .ReleaseSafe => {
            // Safety checks enabled, but optimized
            try testing.expect(true);
        },
        .ReleaseFast => {
            // Maximum speed, some safety checks disabled
            try testing.expect(true);
        },
        .ReleaseSmall => {
            // Optimized for binary size
            try testing.expect(true);
        },
    }
}
```

- **Debug**: Default mode, all safety checks, easier debugging
- **ReleaseSafe**: Optimized but keeps safety checks
- **ReleaseFast**: Maximum speed, some safety disabled
- **ReleaseSmall**: Smallest binary size

For learning, stick with Debug mode (the default).

### Common Commands Quick Reference

```bash
# Version and environment
zig version              # Show Zig version
zig env                  # Show environment settings

# Code formatting
zig fmt file.zig         # Format a file
zig fmt .                # Format all files in current directory
zig fmt --check .        # Check formatting without modifying

# Compilation and running
zig run file.zig         # Compile and run a program
zig build-exe file.zig   # Compile to executable
zig build-lib file.zig   # Compile to library
zig test file.zig        # Run tests

# Build system
zig build                # Run build.zig script
zig init-exe             # Create a new executable project
zig init-lib             # Create a new library project
```

### Troubleshooting

**Problem**: `zig: command not found`
- **Solution**: Zig isn't in your PATH. Double-check Step 2 above.

**Problem**: `zig version` shows old version
- **Solution**: You have multiple Zig installations. Check `which zig` (Unix) or `where zig` (Windows) to see which one is being used.

**Problem**: Tests fail with weird errors
- **Solution**: Make sure you're using Zig 0.15.2. Earlier versions have different APIs.

**Problem**: Editor doesn't recognize Zig
- **Solution**: Install the Zig Language Server (ZLS) for your editor. See [zigtools.org](https://zigtools.org/) for setup.

### Full Tested Code

```zig
// Recipe 0.2: Installing Zig and Verifying Your Toolchain
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to verify your Zig installation and use
// basic toolchain commands. These examples assume Zig is already installed.
//
// Installation options:
//   - Package managers (easiest): brew, apt, pacman, winget, scoop, etc.
//   - Manual download from https://ziglang.org/download/
//   - See: https://github.com/ziglang/zig/wiki/Install-Zig-from-a-Package-Manager

const std = @import("std");
const testing = std.testing;
const builtin = @import("builtin");

// ANCHOR: verify_version
// Verifying Zig Installation
//
// After installing Zig, you should verify it's working correctly.
// This test confirms that the standard library is available and working.

test "verify standard library is available" {
    // If this test runs, Zig is installed and working
    const message = "Zig toolchain is working!";
    try testing.expect(message.len > 0);
}

test "check Zig version info" {
    // You can access version information through builtin
    const version = builtin.zig_version;

    // Verify we're using a reasonable version (not ancient)
    try testing.expect(version.major >= 0);
    try testing.expect(version.minor >= 11); // At least 0.11+

    // The version is available at compile time
    if (version.major == 0 and version.minor == 15) {
        // We're on 0.15.x
        try testing.expect(true);
    }
}
// ANCHOR_END: verify_version

// ANCHOR: environment_info
// Understanding Your Zig Environment
//
// Zig provides information about the target environment through `builtin`.
// This is useful for cross-compilation and platform-specific code.

test "examine build environment" {
    // What platform are we building for?
    const os_tag = builtin.os.tag;
    const arch = builtin.cpu.arch;

    // Common OS tags: .macos, .linux, .windows
    switch (os_tag) {
        .macos, .linux, .windows => {
            // Major platforms
            try testing.expect(true);
        },
        else => {
            // Zig supports many platforms!
            try testing.expect(true);
        },
    }

    // Common architectures: .x86_64, .aarch64, .x86, .arm
    switch (arch) {
        .x86_64, .aarch64 => {
            // Modern 64-bit architectures
            try testing.expect(true);
        },
        else => {
            // Other architectures supported
            try testing.expect(true);
        },
    }
}
// ANCHOR_END: environment_info

// ANCHOR: build_modes
test "check optimization mode" {
    // Zig has different build modes
    const mode = builtin.mode;

    // Modes: .Debug, .ReleaseSafe, .ReleaseFast, .ReleaseSmall
    switch (mode) {
        .Debug => {
            // This is the default for `zig test`
            // Includes safety checks, slower but safer
            try testing.expect(true);
        },
        .ReleaseSafe => {
            // Safety checks enabled, but optimized
            try testing.expect(true);
        },
        .ReleaseFast => {
            // Maximum speed, some safety checks disabled
            try testing.expect(true);
        },
        .ReleaseSmall => {
            // Optimized for binary size
            try testing.expect(true);
        },
    }
}
// ANCHOR_END: build_modes

// ANCHOR: format_check
// Code Formatting with `zig fmt`
//
// Zig has a built-in code formatter. This test verifies that code
// follows standard formatting conventions.

test "demonstrate zig fmt expectations" {
    // Zig fmt expects:
    // - 4-space indentation
    // - Opening braces on same line
    // - Trailing commas in multi-line lists
    // - Consistent spacing

    const array = [_]i32{
        1,
        2,
        3, // Trailing comma expected
    };

    try testing.expectEqual(@as(usize, 3), array.len);

    // Function calls with multiple arguments
    const result = add(
        10,
        20, // Trailing comma
    );

    try testing.expectEqual(@as(i32, 30), result);
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "zig fmt handles various constructs" {
    // Structs with multiple fields
    const Point = struct {
        x: i32,
        y: i32,
    };

    const p = Point{
        .x = 10,
        .y = 20, // Trailing comma
    };

    try testing.expectEqual(@as(i32, 10), p.x);
    try testing.expectEqual(@as(i32, 20), p.y);

    // String concatenation across lines is clear
    const long_string = "This is a long string that might " ++
        "be split across multiple lines " ++
        "for readability";

    try testing.expect(long_string.len > 0);
}
// ANCHOR_END: format_check

// Additional Notes:
//
// Common zig commands you should know:
//   zig version          - Show Zig version
//   zig env              - Show environment settings
//   zig fmt file.zig     - Format a file
//   zig fmt .            - Format all files in current directory
//   zig run file.zig     - Compile and run a program
//   zig build-exe file.zig - Compile to executable
//   zig test file.zig    - Run tests
//   zig build            - Run build.zig script
//
// Installation verification checklist:
//   1. Run `zig version` - should show version number
//   2. Run `zig env` - should show paths and settings
//   3. Run `zig fmt --check file.zig` - should check formatting
//   4. Run `zig test file.zig` - should run tests (like this file!)
```

### See Also

- Recipe 0.3: Your First Zig Program
- Recipe 0.14: Projects, Modules, and Dependencies

---

## Recipe 0.3: Your First Zig Program {#recipe-0-3}

**Tags:** allocators, error-handling, fundamentals, memory, resource-cleanup, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_3.zig`

### Problem

You have Zig installed and you're ready to write your first program. What's the minimal code to get something running? How do you structure a Zig program?

### Solution

Create a file called `hello.zig`:

```zig
// The Simplest Hello World
//
// In Zig, the entry point for an executable is `pub fn main()`.
// The `pub` keyword makes it visible outside this file (required for main).
// The `!void` return type means "returns nothing or an error".

pub fn main() !void {
    // Print to standard output
    const stdout = std.io.getStdOut().writer();
    try stdout.print("Hello, World!\n", .{});
}

// Note: This main() won't actually run when you `zig test` this file.
// Tests run in their own environment. But it will run if you:
//   zig build-exe recipe_0_3.zig
//   ./recipe_0_3

// For testing purposes, we can test the hello world logic separately:
test "hello world produces output" {
    // We can't easily test stdout, but we can test similar logic
    const message = "Hello, World!\n";
    try testing.expect(message.len > 0);
    try testing.expect(std.mem.eql(u8, message, "Hello, World!\n"));
}
```

Run it:
```bash
zig run hello.zig
```

You should see:
```
Hello, World!
```

That's it! You've written your first Zig program.

### Discussion

### Breaking Down the Code

Let's understand each part:

```zig
const std = @import("std");
```

This imports the standard library and binds it to the name `std`. The `@import` function is built into the compiler. You'll use `std` to access standard library features like printing, file I/O, and data structures.

```zig
pub fn main() !void {
```

This is the entry point for your program. Let's break it down:

- `pub` - Makes this function public (visible outside this file). The compiler looks for a public `main()`.
- `fn` - Declares a function
- `main` - The name of the function. This is special - it's where your program starts.
- `!void` - The return type. More on this below.

```zig
const stdout = std.io.getStdOut().writer();
```

This gets a writer for standard output. In Zig, you need to explicitly get handles to stdout/stderr/stdin. Nothing is magically available.

```zig
try stdout.print("Hello, World!\n", .{});
```

This prints to stdout. The `try` keyword means "if this fails, return the error from main()". The `.{}` is an empty tuple (we're not formatting any variables).

### Why `!void` and Not Just `void`?

The `!` in `!void` means this function returns "void or an error". This is called an error union type.

```zig
pub fn main() !void {
    // This can fail (printing might fail!)
    const stdout = std.io.getStdOut().writer();
    try stdout.print("Hello, World!\n", .{});
}
```

Why can printing fail? What if stdout is closed? What if the disk is full (when redirecting to a file)? Zig makes you think about these cases.

The `try` keyword is shorthand for:
```zig
stdout.print("Hello, World!\n", .{}) catch |err| return err;
```

If printing fails, `try` returns the error from `main()`, and your program exits.

Here's what different return types mean:

```zig
// Can't fail
pub fn main() void {}

// Can fail (most common for real programs)
pub fn main() !void {}

// Returns exit code
pub fn main() u8 {
    return 0; // Success
}

// Can fail AND return exit code
pub fn main() !u8 {}
```

For most programs, use `!void`. It's the convention.

### Understanding Error Handling

Errors in Zig are values, not exceptions. Let's see this in action:

```zig
// Understanding Return Types
//
// Why does main() return `!void` instead of just `void`?
// The `!` means the function can return an error.

fn mightFail() !void {
    // This function does nothing, but it could return an error
    // If it did fail, we'd use: return error.SomethingWrong;
}

test "understanding error return types" {
    // When you call a function that returns !T, you must handle potential errors
    // Option 1: Use `try` to propagate the error
    try mightFail();

    // Option 2: Use `catch` to handle the error
    mightFail() catch |err| {
        // Handle the error
        _ = err; // Suppress unused variable warning
        return;
    };

    // Option 3: Assert it won't fail (dangerous!)
    // mightFail() catch unreachable;  // Use only if you're 100% sure
}

fn parseAndDouble(text: []const u8) !i32 {
    // Parse text to integer, then double it
    const num = try std.fmt.parseInt(i32, text, 10);
    return num * 2;
}

test "errors must be handled" {
    // Success case
    const result = try parseAndDouble("21");
    try testing.expectEqual(@as(i32, 42), result);

    // Error case
    const err_result = parseAndDouble("not a number");
    try testing.expectError(error.InvalidCharacter, err_result);
}
```

The `!i32` return type means "returns an i32 or an error". When you call this function, you must handle the possibility of an error.

### Exit Codes

Programs can return exit codes to the shell. By convention:
- `0` = success
- Non-zero = error (1, 2, etc.)

```zig
// Working with Exit Codes
//
// Programs can return exit codes to indicate success or failure.
// By convention: 0 = success, non-zero = error

pub fn main_with_exit_code() u8 {
    // Return 0 for success
    return 0;
}

pub fn main_with_error() u8 {
    // Return non-zero for error
    return 1;
}

test "exit codes convention" {
    const success = main_with_exit_code();
    try testing.expectEqual(@as(u8, 0), success);

    const failure = main_with_error();
    try testing.expectEqual(@as(u8, 1), failure);
}

// In real programs, you might do:
pub fn main_real_example() u8 {
    const result = doSomething() catch {
        std.debug.print("Error occurred!\n", .{});
        return 1; // Return error code
    };

    std.debug.print("Success: {}\n", .{result});
    return 0; // Return success
}

fn doSomething() !i32 {
    // Simulate some work
    return 42;
}

test "main with error handling" {
    const exit_code = main_real_example();
    try testing.expectEqual(@as(u8, 0), exit_code);
}

// Different main() signatures you might see:
//
// pub fn main() void {}                    // Can't fail
// pub fn main() !void {}                   // Can fail (most common)
// pub fn main() u8 {}                      // Returns exit code
// pub fn main() !u8 {}                     // Can fail and return exit code
// pub fn main() anyerror!void {}           // Explicit error type
//
// For most programs, use: pub fn main() !void {}
```

You can check the exit code in your shell:
```bash
./myprogram
echo $?  # Shows the exit code
```

### Print Formatting

The `print()` function uses format strings:

```zig
// No arguments - just a plain string
try stdout.print("Hello!\n", .{});

// With arguments - use {} placeholders
const name = "Zig";
try stdout.print("Hello, {s}!\n", .{name});

// Multiple arguments
const lang = "Zig";
const version = "0.15.2";
try stdout.print("Language: {s}, Version: {s}\n", .{ lang, version });
```

Common format specifiers:
- `{s}` - String
- `{}` - Any type (auto-detect)
- `{d}` - Decimal integer
- `{x}` - Hexadecimal
- `{b}` - Binary
- `{.2}` - Float with 2 decimal places

### Building vs Running

Zig gives you multiple ways to work with your program:

```bash
# Compile and run immediately (for development)
zig run hello.zig

# Build an executable (for distribution)
zig build-exe hello.zig
./hello

# Build with optimization
zig build-exe -O ReleaseFast hello.zig

# Cross-compile for another platform
zig build-exe -target x86_64-windows hello.zig
```

For learning and quick iteration, use `zig run`. For production, use `zig build-exe` with optimization flags.

### Debug vs Release Printing

Zig has two main ways to print:

```zig
// For stdout/stderr (production)
const stdout = std.io.getStdOut().writer();
try stdout.print("Output: {}\n", .{value});

// For debugging (simpler, but not for production)
std.debug.print("Debug: {}\n", .{value});
```

`std.debug.print()` is easier (no `try` needed, no getting a writer), but it's meant for debugging. For real output, use `stdout.print()`.

### Common Beginner Mistakes

**Forgetting `pub` on main():**
```zig
fn main() !void {  // Missing pub!
    // ...
}
```
Error: "no entry point found"

**Forgetting `try` on fallible functions:**
```zig
pub fn main() !void {
    stdout.print("Hello!\n", .{});  // Missing try!
}
```
Error: "error is ignored"

**Wrong return type:**
```zig
pub fn main() void {  // Should be !void
    try stdout.print("Hello!\n", .{});  // Can't use try if main doesn't return !
}
```
Error: "`try` in function with non-error return type"

### Testing vs Running

When you write tests, they run in a test environment:

```zig
test "hello world produces output" {
    const message = "Hello, World!\n";
    try testing.expect(message.len > 0);
}
```

Run tests with:
```bash
zig test hello.zig
```

Tests don't execute `main()`. They run the test blocks instead. This is why we have separate test functions that check the logic.

### Full Tested Code

```zig
// Recipe 0.3: Your First Zig Program
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to write a basic Zig program with main(),
// understand return types, and work with exit codes.

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_hello
// The Simplest Hello World
//
// In Zig, the entry point for an executable is `pub fn main()`.
// The `pub` keyword makes it visible outside this file (required for main).
// The `!void` return type means "returns nothing or an error".

pub fn main() !void {
    // Print to standard output
    const stdout = std.io.getStdOut().writer();
    try stdout.print("Hello, World!\n", .{});
}

// Note: This main() won't actually run when you `zig test` this file.
// Tests run in their own environment. But it will run if you:
//   zig build-exe recipe_0_3.zig
//   ./recipe_0_3

// For testing purposes, we can test the hello world logic separately:
test "hello world produces output" {
    // We can't easily test stdout, but we can test similar logic
    const message = "Hello, World!\n";
    try testing.expect(message.len > 0);
    try testing.expect(std.mem.eql(u8, message, "Hello, World!\n"));
}
// ANCHOR_END: basic_hello

// ANCHOR: error_return
// Understanding Return Types
//
// Why does main() return `!void` instead of just `void`?
// The `!` means the function can return an error.

fn mightFail() !void {
    // This function does nothing, but it could return an error
    // If it did fail, we'd use: return error.SomethingWrong;
}

test "understanding error return types" {
    // When you call a function that returns !T, you must handle potential errors
    // Option 1: Use `try` to propagate the error
    try mightFail();

    // Option 2: Use `catch` to handle the error
    mightFail() catch |err| {
        // Handle the error
        _ = err; // Suppress unused variable warning
        return;
    };

    // Option 3: Assert it won't fail (dangerous!)
    // mightFail() catch unreachable;  // Use only if you're 100% sure
}

fn parseAndDouble(text: []const u8) !i32 {
    // Parse text to integer, then double it
    const num = try std.fmt.parseInt(i32, text, 10);
    return num * 2;
}

test "errors must be handled" {
    // Success case
    const result = try parseAndDouble("21");
    try testing.expectEqual(@as(i32, 42), result);

    // Error case
    const err_result = parseAndDouble("not a number");
    try testing.expectError(error.InvalidCharacter, err_result);
}
// ANCHOR_END: error_return

// ANCHOR: exit_codes
// Working with Exit Codes
//
// Programs can return exit codes to indicate success or failure.
// By convention: 0 = success, non-zero = error

pub fn main_with_exit_code() u8 {
    // Return 0 for success
    return 0;
}

pub fn main_with_error() u8 {
    // Return non-zero for error
    return 1;
}

test "exit codes convention" {
    const success = main_with_exit_code();
    try testing.expectEqual(@as(u8, 0), success);

    const failure = main_with_error();
    try testing.expectEqual(@as(u8, 1), failure);
}

// In real programs, you might do:
pub fn main_real_example() u8 {
    const result = doSomething() catch {
        std.debug.print("Error occurred!\n", .{});
        return 1; // Return error code
    };

    std.debug.print("Success: {}\n", .{result});
    return 0; // Return success
}

fn doSomething() !i32 {
    // Simulate some work
    return 42;
}

test "main with error handling" {
    const exit_code = main_real_example();
    try testing.expectEqual(@as(u8, 0), exit_code);
}

// Different main() signatures you might see:
//
// pub fn main() void {}                    // Can't fail
// pub fn main() !void {}                   // Can fail (most common)
// pub fn main() u8 {}                      // Returns exit code
// pub fn main() !u8 {}                     // Can fail and return exit code
// pub fn main() anyerror!void {}           // Explicit error type
//
// For most programs, use: pub fn main() !void {}
// ANCHOR_END: exit_codes

// Additional examples showing common main() patterns

test "understanding print formatting" {
    // The print function uses format strings
    // Empty .{} means no arguments
    const no_args = "Hello!\n";
    try testing.expect(no_args.len > 0);

    // With arguments, use {} placeholders
    const name = "Zig";
    const msg = std.fmt.allocPrint(
        testing.allocator,
        "Hello, {s}!\n",
        .{name},
    ) catch unreachable;
    defer testing.allocator.free(msg);

    try testing.expect(std.mem.eql(u8, msg, "Hello, Zig!\n"));
}

test "multiple print arguments" {
    // You can print multiple values
    const name = "Zig";
    const version = "0.15.2";

    const msg = std.fmt.allocPrint(
        testing.allocator,
        "Language: {s}, Version: {s}\n",
        .{ name, version },
    ) catch unreachable;
    defer testing.allocator.free(msg);

    try testing.expect(msg.len > 0);
}

// Summary:
// - Entry point is `pub fn main()`
// - Use `!void` return type to allow errors
// - Use `try` to propagate errors from main()
// - Print with stdout.print() or std.debug.print()
// - Format strings use {} for placeholders
// - Exit codes: 0 = success, non-zero = error
```

### See Also

- Recipe 0.4: Variables, Constants, and Type Inference
- Recipe 0.11: Optionals, Errors, and Resource Cleanup
- Recipe 0.2: Installing Zig

---

## Recipe 0.4: Variables, Constants, and Type Inference {#recipe-0-4}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, fundamentals, memory, pointers, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_4.zig`

### Problem

You need to store and manipulate data in your Zig programs. How do you declare values? What's the difference between `const` and `var`? When do you need to specify types explicitly?

### Solution

Zig has two keywords for declaring values:

- `const` - For values that never change (immutable)
- `var` - For values that can change (mutable)

The Zig philosophy: **use `const` by default, `var` only when needed**.

```zig
// Constants vs Variables
//
// Zig has two ways to declare values:
// - `const` for values that never change (immutable)
// - `var` for values that can change (mutable)
//
// The Zig philosophy: use `const` by default, `var` only when needed.

test "const values cannot be changed" {
    const x = 42;

    // This would cause a compile error:
    // x = 43;  // error: cannot assign to constant

    try testing.expectEqual(@as(i32, 42), x);
}

test "var values can be changed" {
    var x: i32 = 42;

    // This is allowed because x is var
    x = 43;

    try testing.expectEqual(@as(i32, 43), x);
}

test "const by default" {
    // Coming from other languages, you might think var is the default
    // In Zig, think const-first

    const name = "Alice"; // Won't change
    const age = 30; // Won't change
    var score: i32 = 0; // Will change

    score += 10;
    score += 5;

    try testing.expect(name.len > 0);
    try testing.expectEqual(@as(i32, 30), age);
    try testing.expectEqual(@as(i32, 15), score);
}

test "const pointers vs const values" {
    var value: i32 = 42;

    // Pointer to mutable value
    const ptr: *i32 = &value;
    ptr.* = 43; // Can modify through pointer
    try testing.expectEqual(@as(i32, 43), value);

    // Pointer to immutable value
    const const_value: i32 = 99;
    const const_ptr: *const i32 = &const_value;
    // const_ptr.* = 100;  // error: cannot assign to const

    try testing.expectEqual(@as(i32, 99), const_ptr.*);
}
```

### Discussion

Why prefer `const`?
- **Clarity**: When you see `const`, you know the value won't change
- **Safety**: The compiler prevents accidental modification
- **Optimization**: The compiler can make better decisions
- **Correctness**: Most values in programs don't actually need to change

### Const Pointers vs Const Values

This can be confusing: `const` on a pointer declaration means the pointer itself can't change, not necessarily what it points to:

```zig
test "const pointers vs const values" {
    var value: i32 = 42;

    // Pointer to mutable value
    const ptr: *i32 = &value;
    ptr.* = 43; // Can modify through pointer
    try testing.expectEqual(@as(i32, 43), value);

    // Pointer to immutable value
    const const_value: i32 = 99;
    const const_ptr: *const i32 = &const_value;
    // const_ptr.* = 100;  // error: cannot assign to const

    try testing.expectEqual(@as(i32, 99), const_ptr.*);
}
```

Key distinction:
- `const ptr: *i32` - The pointer address can't change, but the value it points to can
- `const ptr: *const i32` - The pointer AND the value are both immutable

### Type Inference

Zig can often figure out types automatically:

```zig
// Type Inference
//
// Zig can often figure out types automatically, but you can also
// specify them explicitly when needed.

test "type inference basics" {
    // Zig infers the type from the value
    const x = 42; // Inferred as comptime_int
    const y = 3.14; // Inferred as comptime_float
    const z = true; // Inferred as bool
    const s = "hello"; // Inferred as *const [5:0]u8

    // Comptime integers are flexible
    try testing.expectEqual(42, x);
    try testing.expectEqual(3.14, y);
    try testing.expectEqual(true, z);
    try testing.expect(s.len == 5);
}

test "explicit type annotations" {
    // Sometimes you need to be explicit
    const x: i32 = 42; // Explicitly i32
    const y: u64 = 100; // Explicitly u64
    const z: f64 = 3.14; // Explicitly f64

    try testing.expectEqual(@as(i32, 42), x);
    try testing.expectEqual(@as(u64, 100), y);
    try testing.expectEqual(@as(f64, 3.14), z);
}

test "when type inference needs help" {
    // Empty array needs type hint
    // const arr = [];  // error: unable to infer type

    const arr: [0]i32 = [_]i32{}; // Explicit type
    try testing.expectEqual(@as(usize, 0), arr.len);

    // Function calls sometimes need type hints
    const list = std.ArrayList(i32){}; // Type parameter required
    try testing.expectEqual(@as(usize, 0), list.items.len);
}

test "type inference with operations" {
    // When you mix types, you might need to be explicit
    const a: i32 = 10;
    const b: i64 = 20;

    // This won't compile:
    // const sum = a + b;  // error: mismatched types

    // Be explicit about the conversion:
    const sum: i64 = @as(i64, a) + b;
    try testing.expectEqual(@as(i64, 30), sum);
}
```

This is different from C or Python, where numeric types get automatically promoted. In Zig, you must be explicit.

### Type Casting and Conversion

Zig doesn't do implicit type conversions. Use these built-in functions:

```zig
// Type Casting and Conversion
//
// Zig doesn't do implicit type conversions. You must be explicit.

test "explicit type casting with @as" {
    // @as performs type casting
    const x: i32 = 42;
    const y: i64 = @as(i64, x); // Cast i32 to i64

    try testing.expectEqual(@as(i64, 42), y);
}

test "integer type conversions" {
    const small: i8 = 42;

    // Widening (safe)
    const big: i32 = @as(i32, small);
    try testing.expectEqual(@as(i32, 42), big);

    // Narrowing (potentially unsafe, checked in debug)
    const value: i32 = 127;
    const narrow: i8 = @intCast(value); // Checked cast
    try testing.expectEqual(@as(i8, 127), narrow);

    // This would panic in debug mode:
    // const too_big: i32 = 999;
    // const overflow: i8 = @intCast(too_big);  // panic!
}

test "float conversions" {
    const f32_val: f32 = 3.14;
    const f64_val: f64 = @as(f64, f32_val);

    // Float precision: f32 has less precision than f64
    // so we check the f64 value is close enough
    try testing.expect(@abs(f64_val - 3.14) < 0.01);

    // Float to int (truncates)
    const float: f32 = 3.99;
    const int: i32 = @intFromFloat(float);
    try testing.expectEqual(@as(i32, 3), int); // Truncated, not rounded
}

test "unsigned and signed conversions" {
    const unsigned: u32 = 42;
    const signed: i32 = @intCast(unsigned);

    try testing.expectEqual(@as(i32, 42), signed);

    // Use @bitCast for reinterpretation (advanced)
    const bits: u32 = @bitCast(signed);
    try testing.expectEqual(@as(u32, 42), bits);

    // Be careful with negative numbers and unsigned types
    // const neg: i32 = -5;
    // const wrong: u32 = @intCast(neg);  // Would panic in debug!
}

test "comptime_int to specific type" {
    // Literal integers are comptime_int by default
    const x = 42; // comptime_int

    // They automatically convert to compatible types
    const i8_val: i8 = x;
    const i32_val: i32 = x;
    const u64_val: u64 = x;

    try testing.expectEqual(@as(i8, 42), i8_val);
    try testing.expectEqual(@as(i32, 42), i32_val);
    try testing.expectEqual(@as(u64, 42), u64_val);

    // But only if the value fits
    // const too_big: i8 = 999;  // error: value doesn't fit
}
```

### Undefined and Uninitialized Values

You can delay initialization using `undefined`:

```zig
test "undefined and uninitialized values" {
    // You can declare without initializing using undefined
    var x: i32 = undefined;

    // But reading it before assignment is undefined behavior
    // try testing.expectEqual(0, x);  // DON'T DO THIS

    // Initialize before using
    x = 42;
    try testing.expectEqual(@as(i32, 42), x);
}
```

`undefined` is useful for:
- Arrays that will be filled later
- Temporary buffers
- Performance-critical code (skips initialization)

But be careful - reading `undefined` values is undefined behavior (might be any value, might crash).

### Multiple Declarations

Zig supports destructuring for multiple declarations:

```zig
test "multiple declarations" {
    // You can declare multiple values in one line with destructuring
    const a, const b, const c = .{ 1, 2, 3 };

    try testing.expectEqual(@as(i32, 1), a);
    try testing.expectEqual(@as(i32, 2), b);
    try testing.expectEqual(@as(i32, 3), c);
}
```

### Scope

Variables are scoped to their block:

```zig
test "scope and local declarations" {
    const x = 42;
    try testing.expectEqual(@as(i32, 42), x);

    {
        // Inner scope has its own declarations
        const y = 99;
        try testing.expectEqual(@as(i32, 99), y);
        // x from outer scope is also accessible here
        try testing.expectEqual(@as(i32, 42), x);
    }

    // y is not accessible here (out of scope)
    // Original x is still accessible
    try testing.expectEqual(@as(i32, 42), x);
}
```

### Common Beginner Mistakes

**Using var when const would work:**
```zig
var x = 42;  // Unnecessary var
const y = 42;  // Better - communicates intent
```

**Forgetting type annotations when needed:**
```zig
const arr = [_]i32{};  // error: can't infer empty array type
const arr: [0]i32 = [_]i32{};  // Fixed
```

**Trying to use implicit conversions:**
```zig
const x: i32 = 10;
const y: i64 = 20;
const sum = x + y;  // error: mismatched types!
const sum = @as(i64, x) + y;  // Fixed
```

**Reading undefined values:**
```zig
var x: i32 = undefined;
const y = x;  // Undefined behavior!
```

### Full Tested Code

```zig
// Recipe 0.4: Variables, Constants, and Type Inference
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to declare variables and constants,
// understand mutability, and work with type inference.

const std = @import("std");
const testing = std.testing;

// ANCHOR: const_vs_var
// Constants vs Variables
//
// Zig has two ways to declare values:
// - `const` for values that never change (immutable)
// - `var` for values that can change (mutable)
//
// The Zig philosophy: use `const` by default, `var` only when needed.

test "const values cannot be changed" {
    const x = 42;

    // This would cause a compile error:
    // x = 43;  // error: cannot assign to constant

    try testing.expectEqual(@as(i32, 42), x);
}

test "var values can be changed" {
    var x: i32 = 42;

    // This is allowed because x is var
    x = 43;

    try testing.expectEqual(@as(i32, 43), x);
}

test "const by default" {
    // Coming from other languages, you might think var is the default
    // In Zig, think const-first

    const name = "Alice"; // Won't change
    const age = 30; // Won't change
    var score: i32 = 0; // Will change

    score += 10;
    score += 5;

    try testing.expect(name.len > 0);
    try testing.expectEqual(@as(i32, 30), age);
    try testing.expectEqual(@as(i32, 15), score);
}

test "const pointers vs const values" {
    var value: i32 = 42;

    // Pointer to mutable value
    const ptr: *i32 = &value;
    ptr.* = 43; // Can modify through pointer
    try testing.expectEqual(@as(i32, 43), value);

    // Pointer to immutable value
    const const_value: i32 = 99;
    const const_ptr: *const i32 = &const_value;
    // const_ptr.* = 100;  // error: cannot assign to const

    try testing.expectEqual(@as(i32, 99), const_ptr.*);
}
// ANCHOR_END: const_vs_var

// ANCHOR: type_inference
// Type Inference
//
// Zig can often figure out types automatically, but you can also
// specify them explicitly when needed.

test "type inference basics" {
    // Zig infers the type from the value
    const x = 42; // Inferred as comptime_int
    const y = 3.14; // Inferred as comptime_float
    const z = true; // Inferred as bool
    const s = "hello"; // Inferred as *const [5:0]u8

    // Comptime integers are flexible
    try testing.expectEqual(42, x);
    try testing.expectEqual(3.14, y);
    try testing.expectEqual(true, z);
    try testing.expect(s.len == 5);
}

test "explicit type annotations" {
    // Sometimes you need to be explicit
    const x: i32 = 42; // Explicitly i32
    const y: u64 = 100; // Explicitly u64
    const z: f64 = 3.14; // Explicitly f64

    try testing.expectEqual(@as(i32, 42), x);
    try testing.expectEqual(@as(u64, 100), y);
    try testing.expectEqual(@as(f64, 3.14), z);
}

test "when type inference needs help" {
    // Empty array needs type hint
    // const arr = [];  // error: unable to infer type

    const arr: [0]i32 = [_]i32{}; // Explicit type
    try testing.expectEqual(@as(usize, 0), arr.len);

    // Function calls sometimes need type hints
    const list = std.ArrayList(i32){}; // Type parameter required
    try testing.expectEqual(@as(usize, 0), list.items.len);
}

test "type inference with operations" {
    // When you mix types, you might need to be explicit
    const a: i32 = 10;
    const b: i64 = 20;

    // This won't compile:
    // const sum = a + b;  // error: mismatched types

    // Be explicit about the conversion:
    const sum: i64 = @as(i64, a) + b;
    try testing.expectEqual(@as(i64, 30), sum);
}
// ANCHOR_END: type_inference

// ANCHOR: type_casting
// Type Casting and Conversion
//
// Zig doesn't do implicit type conversions. You must be explicit.

test "explicit type casting with @as" {
    // @as performs type casting
    const x: i32 = 42;
    const y: i64 = @as(i64, x); // Cast i32 to i64

    try testing.expectEqual(@as(i64, 42), y);
}

test "integer type conversions" {
    const small: i8 = 42;

    // Widening (safe)
    const big: i32 = @as(i32, small);
    try testing.expectEqual(@as(i32, 42), big);

    // Narrowing (potentially unsafe, checked in debug)
    const value: i32 = 127;
    const narrow: i8 = @intCast(value); // Checked cast
    try testing.expectEqual(@as(i8, 127), narrow);

    // This would panic in debug mode:
    // const too_big: i32 = 999;
    // const overflow: i8 = @intCast(too_big);  // panic!
}

test "float conversions" {
    const f32_val: f32 = 3.14;
    const f64_val: f64 = @as(f64, f32_val);

    // Float precision: f32 has less precision than f64
    // so we check the f64 value is close enough
    try testing.expect(@abs(f64_val - 3.14) < 0.01);

    // Float to int (truncates)
    const float: f32 = 3.99;
    const int: i32 = @intFromFloat(float);
    try testing.expectEqual(@as(i32, 3), int); // Truncated, not rounded
}

test "unsigned and signed conversions" {
    const unsigned: u32 = 42;
    const signed: i32 = @intCast(unsigned);

    try testing.expectEqual(@as(i32, 42), signed);

    // Use @bitCast for reinterpretation (advanced)
    const bits: u32 = @bitCast(signed);
    try testing.expectEqual(@as(u32, 42), bits);

    // Be careful with negative numbers and unsigned types
    // const neg: i32 = -5;
    // const wrong: u32 = @intCast(neg);  // Would panic in debug!
}

test "comptime_int to specific type" {
    // Literal integers are comptime_int by default
    const x = 42; // comptime_int

    // They automatically convert to compatible types
    const i8_val: i8 = x;
    const i32_val: i32 = x;
    const u64_val: u64 = x;

    try testing.expectEqual(@as(i8, 42), i8_val);
    try testing.expectEqual(@as(i32, 42), i32_val);
    try testing.expectEqual(@as(u64, 42), u64_val);

    // But only if the value fits
    // const too_big: i8 = 999;  // error: value doesn't fit
}
// ANCHOR_END: type_casting

// Additional examples

test "undefined and uninitialized values" {
    // You can declare without initializing using undefined
    var x: i32 = undefined;

    // But reading it before assignment is undefined behavior
    // try testing.expectEqual(0, x);  // DON'T DO THIS

    // Initialize before using
    x = 42;
    try testing.expectEqual(@as(i32, 42), x);
}

test "multiple declarations" {
    // You can declare multiple values in one line with destructuring
    const a, const b, const c = .{ 1, 2, 3 };

    try testing.expectEqual(@as(i32, 1), a);
    try testing.expectEqual(@as(i32, 2), b);
    try testing.expectEqual(@as(i32, 3), c);
}

test "scope and local declarations" {
    const x = 42;
    try testing.expectEqual(@as(i32, 42), x);

    {
        // Inner scope has its own declarations
        const y = 99;
        try testing.expectEqual(@as(i32, 99), y);
        // x from outer scope is also accessible here
        try testing.expectEqual(@as(i32, 42), x);
    }

    // y is not accessible here (out of scope)
    // Original x is still accessible
    try testing.expectEqual(@as(i32, 42), x);
}

// Summary:
// - Use `const` by default, `var` only when values change
// - Zig infers types when possible, but you can be explicit
// - No implicit type conversions - use @as, @intCast, @intFromFloat
// - Comptime integers are flexible until assigned to a specific type
// - Use `undefined` for delayed initialization, but assign before reading
```

### See Also

- Recipe 0.5: Primitive Data and Basic Arrays
- Recipe 0.9: Understanding Pointers and References
- Recipe 1.2: Standard Allocator Usage Patterns

---

## Recipe 0.5: Primitive Data and Basic Arrays {#recipe-0-5}

**Tags:** arraylist, data-structures, fundamentals, pointers, slices, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_5.zig`

### Problem

You need to work with different types of data in Zig. What integer types are available? How do floats work? How do you create and use arrays?

### Solution

Zig has explicit types for everything. Unlike C where `int` size varies by platform, Zig is completely explicit about sizes.

**Integers:**
- Signed: `i8`, `i16`, `i32`, `i64`, `i128`
- Unsigned: `u8`, `u16`, `u32`, `u64`, `u128`
- Platform-specific: `isize`, `usize` (pointer-sized)

**Floats:**
- `f32` - 32-bit float (single precision)
- `f64` - 64-bit float (double precision)

**Arrays:**
- Fixed-size: `[N]T` where N is the size and T is the type
- The size is part of the type!

### Discussion

### Integer Types

```zig
// Integer Types
//
// Zig has explicit integer types with specific sizes.
// Unlike C where `int` size varies by platform, Zig is explicit.
//
// Signed: i8, i16, i32, i64, i128
// Unsigned: u8, u16, u32, u64, u128
// Platform-specific: isize, usize (pointer-sized)

test "signed integers" {
    const tiny: i8 = -128; // 8-bit signed (-128 to 127)
    const small: i16 = -32_768; // 16-bit signed
    const medium: i32 = -2_147_483_648; // 32-bit signed
    const large: i64 = -9_223_372_036_854_775_808; // 64-bit signed

    try testing.expectEqual(@as(i8, -128), tiny);
    try testing.expectEqual(@as(i16, -32_768), small);
    try testing.expectEqual(@as(i32, -2_147_483_648), medium);
    try testing.expectEqual(@as(i64, -9_223_372_036_854_775_808), large);
}

test "unsigned integers" {
    const byte: u8 = 255; // 8-bit unsigned (0 to 255)
    const word: u16 = 65_535; // 16-bit unsigned
    const dword: u32 = 4_294_967_295; // 32-bit unsigned
    const qword: u64 = 18_446_744_073_709_551_615; // 64-bit unsigned

    try testing.expectEqual(@as(u8, 255), byte);
    try testing.expectEqual(@as(u16, 65_535), word);
    try testing.expectEqual(@as(u32, 4_294_967_295), dword);
    try testing.expectEqual(@as(u64, 18_446_744_073_709_551_615), qword);
}

test "pointer-sized integers" {
    // usize and isize are the size of a pointer on your platform
    // On 64-bit: usize = u64, isize = i64
    // On 32-bit: usize = u32, isize = i32

    const index: usize = 0; // Use for array indices
    const offset: isize = -5; // Use for pointer arithmetic

    try testing.expect(index == 0);
    try testing.expect(offset == -5);

    // usize is commonly used for lengths and indices
    const arr = [_]i32{ 1, 2, 3 };
    const len: usize = arr.len;
    try testing.expectEqual(@as(usize, 3), len);
}

test "arbitrary bit-width integers" {
    // Zig supports integers of any bit width
    const i3_val: i3 = -4; // 3-bit signed (-4 to 3)
    const u7_val: u7 = 127; // 7-bit unsigned (0 to 127)
    const i33_val: i33 = 0; // 33-bit signed

    try testing.expectEqual(@as(i3, -4), i3_val);
    try testing.expectEqual(@as(u7, 127), u7_val);
    try testing.expectEqual(@as(i33, 0), i33_val);
}

test "integer literals and underscores" {
    // Use underscores for readability (like commas in numbers)
    const million: i32 = 1_000_000;
    const byte_value: u8 = 0xFF; // Hexadecimal
    const binary: u8 = 0b1111_0000; // Binary
    const octal: u16 = 0o755; // Octal (755 in base 8 = 493 in base 10)

    try testing.expectEqual(@as(i32, 1_000_000), million);
    try testing.expectEqual(@as(u8, 255), byte_value);
    try testing.expectEqual(@as(u8, 240), binary);
    try testing.expectEqual(@as(u16, 493), octal);
}
```

### Floating Point Types

```zig
// Floating Point Types
//
// Zig has two float types: f32 and f64
// Plus f16 and f128 on some platforms

test "float types" {
    const small: f32 = 3.14; // 32-bit float (single precision)
    const large: f64 = 2.718281828; // 64-bit float (double precision)

    try testing.expect(small > 3.0 and small < 3.2);
    try testing.expect(large > 2.7 and large < 2.8);
}

test "float literals" {
    const scientific: f64 = 1.23e10; // Scientific notation
    const tiny: f64 = 1.23e-10;

    try testing.expect(scientific > 1e10);
    try testing.expect(tiny < 1e-9);
}

test "float operations" {
    const x: f32 = 10.5;
    const y: f32 = 2.5;

    const sum = x + y;
    const product = x * y;
    const quotient = x / y;

    try testing.expectEqual(@as(f32, 13.0), sum);
    try testing.expectEqual(@as(f32, 26.25), product);
    try testing.expectEqual(@as(f32, 4.2), quotient);
}

test "special float values" {
    // Infinity and NaN are available
    const inf = std.math.inf(f64);
    const neg_inf = -std.math.inf(f64);
    const nan = std.math.nan(f64);

    try testing.expect(std.math.isInf(inf));
    try testing.expect(std.math.isInf(neg_inf));
    try testing.expect(std.math.isNan(nan));
}
```

### Fixed-Size Arrays

```zig
// Fixed-Size Arrays
//
// Arrays in Zig have compile-time known size: [N]T
// The size is part of the type!

test "basic array declaration" {
    // Declare and initialize array
    const numbers = [5]i32{ 1, 2, 3, 4, 5 };

    try testing.expectEqual(@as(usize, 5), numbers.len);
    try testing.expectEqual(@as(i32, 1), numbers[0]);
    try testing.expectEqual(@as(i32, 5), numbers[4]);
}

test "array type inference" {
    // Use [_] to let Zig infer the size
    const inferred = [_]i32{ 10, 20, 30 };

    try testing.expectEqual(@as(usize, 3), inferred.len);
    try testing.expectEqual(@as(i32, 10), inferred[0]);
}

test "array initialization patterns" {
    // All zeros
    const zeros = [_]i32{0} ** 5; // [0, 0, 0, 0, 0]
    try testing.expectEqual(@as(i32, 0), zeros[0]);
    try testing.expectEqual(@as(i32, 0), zeros[4]);

    // Repeat a pattern
    const pattern = [_]i32{ 1, 2 } ** 3; // [1, 2, 1, 2, 1, 2]
    try testing.expectEqual(@as(usize, 6), pattern.len);
    try testing.expectEqual(@as(i32, 1), pattern[0]);
    try testing.expectEqual(@as(i32, 2), pattern[1]);
    try testing.expectEqual(@as(i32, 1), pattern[2]);
}

test "multidimensional arrays" {
    // Arrays of arrays
    const matrix = [3][3]i32{
        [_]i32{ 1, 2, 3 },
        [_]i32{ 4, 5, 6 },
        [_]i32{ 7, 8, 9 },
    };

    try testing.expectEqual(@as(i32, 1), matrix[0][0]);
    try testing.expectEqual(@as(i32, 5), matrix[1][1]);
    try testing.expectEqual(@as(i32, 9), matrix[2][2]);
}

test "modifying array elements" {
    var mutable = [_]i32{ 1, 2, 3 };

    // Can modify elements of var array
    mutable[0] = 10;
    mutable[1] = 20;

    try testing.expectEqual(@as(i32, 10), mutable[0]);
    try testing.expectEqual(@as(i32, 20), mutable[1]);
}

test "array iteration" {
    const values = [_]i32{ 10, 20, 30, 40, 50 };

    // Iterate with for loop
    var sum: i32 = 0;
    for (values) |value| {
        sum += value;
    }

    try testing.expectEqual(@as(i32, 150), sum);
}

test "array bounds are checked" {
    const arr = [_]i32{ 1, 2, 3 };

    // This is fine
    const first = arr[0];
    try testing.expectEqual(@as(i32, 1), first);

    // This would panic at runtime (in debug mode):
    // const oob = arr[10];  // Index out of bounds!
}

test "string literals are arrays" {
    // String literals are arrays of bytes with null terminator
    const hello: *const [5:0]u8 = "hello";
    // *const = pointer to const
    // [5:0] = array of 5 bytes with 0 terminator (sentinel)
    // u8 = unsigned 8-bit integer (byte)

    try testing.expectEqual(@as(usize, 5), hello.len);
    try testing.expectEqual(@as(u8, 'h'), hello[0]);
    try testing.expectEqual(@as(u8, 'o'), hello[4]);
}

test "boolean type" {
    const yes: bool = true;
    const no: bool = false;

    try testing.expect(yes);
    try testing.expect(!no);

    // Booleans in conditions
    const value: i32 = 10;
    const is_positive: bool = value > 0;
    try testing.expect(is_positive);
}

test "void type" {
    // void means "no value"
    // Functions that return nothing return void

    const nothing: void = {};
    _ = nothing; // Suppress unused variable warning

    // Common use: functions that perform actions but return nothing
    // fn doSomething() void { }
}
```

### Boolean Type

Zig has a proper boolean type:

```zig
test "boolean type" {
    const yes: bool = true;
    const no: bool = false;

    try testing.expect(yes);
    try testing.expect(!no);

    // Booleans in conditions
    const value: i32 = 10;
    const is_positive: bool = value > 0;
    try testing.expect(is_positive);
}
```

Unlike C where any non-zero value is "true", Zig only has `true` and `false`.

### Void Type

The `void` type represents "no value":

```zig
test "void type" {
    // void means "no value"
    // Functions that return nothing return void

    const nothing: void = {};
    _ = nothing; // Suppress unused variable warning

    // Common use: functions that perform actions but return nothing
    // fn doSomething() void { }
}
```

You'll rarely use `void` as a variable type, but you'll see it as return types for functions.

### Choosing the Right Type

**For integers:**
- Use `i32` or `u32` as your default
- Use `usize` for array indices and lengths
- Use `u8` for bytes and raw data
- Use `i64/u64` for timestamps and large values
- Use smaller types (`i8`, `i16`) only when you need to save space

**For floats:**
- Use `f64` as your default (more precision)
- Use `f32` when interfacing with graphics APIs or saving memory

**For arrays:**
- Use `[N]T` when size is known at compile time
- You'll learn about slices `[]T` in Recipe 0.6 (for runtime-sized data)

### Full Tested Code

```zig
// Recipe 0.5: Primitive Data and Basic Arrays
// Target Zig Version: 0.15.2
//
// This recipe demonstrates Zig's primitive types (integers, floats, booleans)
// and basic fixed-size arrays.

const std = @import("std");
const testing = std.testing;

// ANCHOR: integer_types
// Integer Types
//
// Zig has explicit integer types with specific sizes.
// Unlike C where `int` size varies by platform, Zig is explicit.
//
// Signed: i8, i16, i32, i64, i128
// Unsigned: u8, u16, u32, u64, u128
// Platform-specific: isize, usize (pointer-sized)

test "signed integers" {
    const tiny: i8 = -128; // 8-bit signed (-128 to 127)
    const small: i16 = -32_768; // 16-bit signed
    const medium: i32 = -2_147_483_648; // 32-bit signed
    const large: i64 = -9_223_372_036_854_775_808; // 64-bit signed

    try testing.expectEqual(@as(i8, -128), tiny);
    try testing.expectEqual(@as(i16, -32_768), small);
    try testing.expectEqual(@as(i32, -2_147_483_648), medium);
    try testing.expectEqual(@as(i64, -9_223_372_036_854_775_808), large);
}

test "unsigned integers" {
    const byte: u8 = 255; // 8-bit unsigned (0 to 255)
    const word: u16 = 65_535; // 16-bit unsigned
    const dword: u32 = 4_294_967_295; // 32-bit unsigned
    const qword: u64 = 18_446_744_073_709_551_615; // 64-bit unsigned

    try testing.expectEqual(@as(u8, 255), byte);
    try testing.expectEqual(@as(u16, 65_535), word);
    try testing.expectEqual(@as(u32, 4_294_967_295), dword);
    try testing.expectEqual(@as(u64, 18_446_744_073_709_551_615), qword);
}

test "pointer-sized integers" {
    // usize and isize are the size of a pointer on your platform
    // On 64-bit: usize = u64, isize = i64
    // On 32-bit: usize = u32, isize = i32

    const index: usize = 0; // Use for array indices
    const offset: isize = -5; // Use for pointer arithmetic

    try testing.expect(index == 0);
    try testing.expect(offset == -5);

    // usize is commonly used for lengths and indices
    const arr = [_]i32{ 1, 2, 3 };
    const len: usize = arr.len;
    try testing.expectEqual(@as(usize, 3), len);
}

test "arbitrary bit-width integers" {
    // Zig supports integers of any bit width
    const i3_val: i3 = -4; // 3-bit signed (-4 to 3)
    const u7_val: u7 = 127; // 7-bit unsigned (0 to 127)
    const i33_val: i33 = 0; // 33-bit signed

    try testing.expectEqual(@as(i3, -4), i3_val);
    try testing.expectEqual(@as(u7, 127), u7_val);
    try testing.expectEqual(@as(i33, 0), i33_val);
}

test "integer literals and underscores" {
    // Use underscores for readability (like commas in numbers)
    const million: i32 = 1_000_000;
    const byte_value: u8 = 0xFF; // Hexadecimal
    const binary: u8 = 0b1111_0000; // Binary
    const octal: u16 = 0o755; // Octal (755 in base 8 = 493 in base 10)

    try testing.expectEqual(@as(i32, 1_000_000), million);
    try testing.expectEqual(@as(u8, 255), byte_value);
    try testing.expectEqual(@as(u8, 240), binary);
    try testing.expectEqual(@as(u16, 493), octal);
}
// ANCHOR_END: integer_types

// ANCHOR: float_types
// Floating Point Types
//
// Zig has two float types: f32 and f64
// Plus f16 and f128 on some platforms

test "float types" {
    const small: f32 = 3.14; // 32-bit float (single precision)
    const large: f64 = 2.718281828; // 64-bit float (double precision)

    try testing.expect(small > 3.0 and small < 3.2);
    try testing.expect(large > 2.7 and large < 2.8);
}

test "float literals" {
    const scientific: f64 = 1.23e10; // Scientific notation
    const tiny: f64 = 1.23e-10;

    try testing.expect(scientific > 1e10);
    try testing.expect(tiny < 1e-9);
}

test "float operations" {
    const x: f32 = 10.5;
    const y: f32 = 2.5;

    const sum = x + y;
    const product = x * y;
    const quotient = x / y;

    try testing.expectEqual(@as(f32, 13.0), sum);
    try testing.expectEqual(@as(f32, 26.25), product);
    try testing.expectEqual(@as(f32, 4.2), quotient);
}

test "special float values" {
    // Infinity and NaN are available
    const inf = std.math.inf(f64);
    const neg_inf = -std.math.inf(f64);
    const nan = std.math.nan(f64);

    try testing.expect(std.math.isInf(inf));
    try testing.expect(std.math.isInf(neg_inf));
    try testing.expect(std.math.isNan(nan));
}
// ANCHOR_END: float_types

// ANCHOR: fixed_arrays
// Fixed-Size Arrays
//
// Arrays in Zig have compile-time known size: [N]T
// The size is part of the type!

test "basic array declaration" {
    // Declare and initialize array
    const numbers = [5]i32{ 1, 2, 3, 4, 5 };

    try testing.expectEqual(@as(usize, 5), numbers.len);
    try testing.expectEqual(@as(i32, 1), numbers[0]);
    try testing.expectEqual(@as(i32, 5), numbers[4]);
}

test "array type inference" {
    // Use [_] to let Zig infer the size
    const inferred = [_]i32{ 10, 20, 30 };

    try testing.expectEqual(@as(usize, 3), inferred.len);
    try testing.expectEqual(@as(i32, 10), inferred[0]);
}

test "array initialization patterns" {
    // All zeros
    const zeros = [_]i32{0} ** 5; // [0, 0, 0, 0, 0]
    try testing.expectEqual(@as(i32, 0), zeros[0]);
    try testing.expectEqual(@as(i32, 0), zeros[4]);

    // Repeat a pattern
    const pattern = [_]i32{ 1, 2 } ** 3; // [1, 2, 1, 2, 1, 2]
    try testing.expectEqual(@as(usize, 6), pattern.len);
    try testing.expectEqual(@as(i32, 1), pattern[0]);
    try testing.expectEqual(@as(i32, 2), pattern[1]);
    try testing.expectEqual(@as(i32, 1), pattern[2]);
}

test "multidimensional arrays" {
    // Arrays of arrays
    const matrix = [3][3]i32{
        [_]i32{ 1, 2, 3 },
        [_]i32{ 4, 5, 6 },
        [_]i32{ 7, 8, 9 },
    };

    try testing.expectEqual(@as(i32, 1), matrix[0][0]);
    try testing.expectEqual(@as(i32, 5), matrix[1][1]);
    try testing.expectEqual(@as(i32, 9), matrix[2][2]);
}

test "modifying array elements" {
    var mutable = [_]i32{ 1, 2, 3 };

    // Can modify elements of var array
    mutable[0] = 10;
    mutable[1] = 20;

    try testing.expectEqual(@as(i32, 10), mutable[0]);
    try testing.expectEqual(@as(i32, 20), mutable[1]);
}

test "array iteration" {
    const values = [_]i32{ 10, 20, 30, 40, 50 };

    // Iterate with for loop
    var sum: i32 = 0;
    for (values) |value| {
        sum += value;
    }

    try testing.expectEqual(@as(i32, 150), sum);
}

test "array bounds are checked" {
    const arr = [_]i32{ 1, 2, 3 };

    // This is fine
    const first = arr[0];
    try testing.expectEqual(@as(i32, 1), first);

    // This would panic at runtime (in debug mode):
    // const oob = arr[10];  // Index out of bounds!
}

test "string literals are arrays" {
    // String literals are arrays of bytes with null terminator
    const hello: *const [5:0]u8 = "hello";
    // *const = pointer to const
    // [5:0] = array of 5 bytes with 0 terminator (sentinel)
    // u8 = unsigned 8-bit integer (byte)

    try testing.expectEqual(@as(usize, 5), hello.len);
    try testing.expectEqual(@as(u8, 'h'), hello[0]);
    try testing.expectEqual(@as(u8, 'o'), hello[4]);
}

test "boolean type" {
    const yes: bool = true;
    const no: bool = false;

    try testing.expect(yes);
    try testing.expect(!no);

    // Booleans in conditions
    const value: i32 = 10;
    const is_positive: bool = value > 0;
    try testing.expect(is_positive);
}

test "void type" {
    // void means "no value"
    // Functions that return nothing return void

    const nothing: void = {};
    _ = nothing; // Suppress unused variable warning

    // Common use: functions that perform actions but return nothing
    // fn doSomething() void { }
}
// ANCHOR_END: fixed_arrays

// Summary:
// - Zig has explicit integer types: i8, i16, i32, i64, u8, u16, u32, u64
// - Use usize for array indices and lengths
// - Floats: f32 (single) and f64 (double precision)
// - Fixed arrays have compile-time size: [N]T
// - Array size is part of the type
// - Use [_] for size inference
// - Bounds checking happens in debug mode
// - String literals are sentinel-terminated byte arrays
```

### See Also

- Recipe 0.6: Arrays, ArrayLists, and Slices
- Recipe 0.4: Variables, Constants, and Type Inference
- Recipe 3.4: Working with Binary, Octal, and Hexadecimal

---

## Recipe 0.6: Arrays, ArrayLists, and Slices {#recipe-0-6}

**Tags:** allocators, arraylist, data-structures, error-handling, fundamentals, hashmap, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_6.zig`

### Full Tested Code

```zig
// Recipe 0.6: Arrays, ArrayLists, and Slices (CRITICAL)
// Target Zig Version: 0.15.2
//
// This is the #1 confusion point for Zig beginners!
// This recipe clarifies the three fundamental sequence types in Zig.

const std = @import("std");
const testing = std.testing;

// ANCHOR: fixed_arrays
// Part 1: Fixed Arrays [N]T
//
// Arrays have compile-time known size. The size is part of the type!
// [3]i32 and [5]i32 are completely different types.

test "fixed arrays have compile-time size" {
    // The size is in the type
    const arr1: [3]i32 = [_]i32{ 1, 2, 3 };
    const arr2: [5]i32 = [_]i32{ 1, 2, 3, 4, 5 };

    // These are different types!
    // const same: [3]i32 = arr2;  // error: type mismatch

    try testing.expectEqual(@as(usize, 3), arr1.len);
    try testing.expectEqual(@as(usize, 5), arr2.len);
}

test "arrays live on the stack" {
    // No allocator needed - arrays are value types
    const numbers = [_]i32{ 10, 20, 30, 40 };

    // You can pass arrays by value (they get copied)
    const sum = sumArray(numbers);

    try testing.expectEqual(@as(i32, 100), sum);
}

fn sumArray(arr: [4]i32) i32 {
    var total: i32 = 0;
    for (arr) |n| {
        total += n;
    }
    return total;
}

test "arrays cannot grow or shrink" {
    var arr = [_]i32{ 1, 2, 3 };

    // Can modify elements
    arr[0] = 10;
    try testing.expectEqual(@as(i32, 10), arr[0]);

    // But cannot change size
    // arr.append(4);  // No such method!
    // The size is fixed at compile time
}
// ANCHOR_END: fixed_arrays

// ANCHOR: slices_views
// Part 2: Slices []T
//
// Slices are "views" into arrays - pointer + length
// They're how you work with arrays when size isn't known at compile time

test "slices are views into arrays" {
    const array = [_]i32{ 1, 2, 3, 4, 5 };

    // Create a slice (view) of the array
    const slice: []const i32 = &array;

    // Slice knows its length at runtime
    try testing.expectEqual(@as(usize, 5), slice.len);
    try testing.expectEqual(@as(i32, 1), slice[0]);
}

test "slicing an array" {
    const array = [_]i32{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 };

    // Get a sub-slice [start..end]
    const middle: []const i32 = array[3..7]; // [3, 4, 5, 6]

    try testing.expectEqual(@as(usize, 4), middle.len);
    try testing.expectEqual(@as(i32, 3), middle[0]);
    try testing.expectEqual(@as(i32, 6), middle[3]);
}

test "slices can be passed to functions" {
    const array = [_]i32{ 10, 20, 30 };

    // Functions that take slices work with any array size
    const sum1 = sumSlice(&array);
    try testing.expectEqual(@as(i32, 60), sum1);

    const other = [_]i32{ 5, 15 };
    const sum2 = sumSlice(&other);
    try testing.expectEqual(@as(i32, 20), sum2);
}

fn sumSlice(slice: []const i32) i32 {
    var total: i32 = 0;
    for (slice) |n| {
        total += n;
    }
    return total;
}

test "mutable slices" {
    var array = [_]i32{ 1, 2, 3, 4, 5 };

    // Mutable slice - can modify through it
    const slice: []i32 = &array;
    slice[0] = 99;

    try testing.expectEqual(@as(i32, 99), array[0]);
}

test "slices don't own memory" {
    const array = [_]i32{ 1, 2, 3 };
    const slice: []const i32 = &array;

    // The slice is just a view - array owns the memory
    // When array goes out of scope, slice becomes invalid
    try testing.expectEqual(array.len, slice.len);
}
// ANCHOR_END: slices_views

// ANCHOR: arraylist_growable
// Part 3: ArrayList - Growable Arrays
//
// When you need to add/remove elements, use ArrayList
// This is like Python's list or Java's ArrayList

test "ArrayList needs an allocator" {
    // ArrayList requires an allocator to manage memory
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    // Can grow dynamically
    try list.append(testing.allocator, 1);
    try list.append(testing.allocator, 2);
    try list.append(testing.allocator, 3);

    try testing.expectEqual(@as(usize, 3), list.items.len);
    try testing.expectEqual(@as(i32, 1), list.items[0]);
}

test "ArrayList vs fixed array" {
    // Fixed array - size known at compile time
    const fixed = [_]i32{ 1, 2, 3 };
    _ = fixed;

    // ArrayList - size known at runtime, can grow
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    try list.append(testing.allocator, 1);
    try list.append(testing.allocator, 2);
    try list.append(testing.allocator, 3);

    // Can add more!
    try list.append(testing.allocator, 4);
    try testing.expectEqual(@as(usize, 4), list.items.len);
}

test "ArrayList operations" {
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    // Append items
    try list.append(testing.allocator, 10);
    try list.append(testing.allocator, 20);
    try list.append(testing.allocator, 30);

    try testing.expectEqual(@as(usize, 3), list.items.len);

    // Access items through .items slice
    try testing.expectEqual(@as(i32, 10), list.items[0]);
    try testing.expectEqual(@as(i32, 20), list.items[1]);

    // Pop removes last element
    const last = list.pop();
    try testing.expectEqual(@as(i32, 30), last);
    try testing.expectEqual(@as(usize, 2), list.items.len);
}

test "ArrayList .items is a slice" {
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    try list.append(testing.allocator, 5);
    try list.append(testing.allocator, 10);
    try list.append(testing.allocator, 15);

    // .items gives you a slice of the contents
    const slice: []i32 = list.items;

    // Can use slice operations
    try testing.expectEqual(@as(usize, 3), slice.len);

    // Can pass to functions expecting slices
    const sum = sumSlice(slice);
    try testing.expectEqual(@as(i32, 30), sum);
}
// ANCHOR_END: arraylist_growable

// String examples - strings are just byte arrays!

test "string literals are special arrays" {
    // String literal type: *const [N:0]u8
    // *const = pointer to const
    // [N:0]u8 = array of N bytes with null terminator
    const hello: *const [5:0]u8 = "hello";

    try testing.expectEqual(@as(usize, 5), hello.len);
    try testing.expectEqual(@as(u8, 'h'), hello[0]);
}

test "strings as slices" {
    const hello = "hello";

    // Can convert to slice
    const slice: []const u8 = hello;

    try testing.expectEqual(@as(usize, 5), slice.len);

    // Can slice strings
    const ello: []const u8 = hello[1..];
    try testing.expect(std.mem.eql(u8, ello, "ello"));
}

test "building strings with ArrayList" {
    // For dynamic strings, use ArrayList(u8)
    var string = std.ArrayList(u8){};
    defer string.deinit(testing.allocator);

    try string.appendSlice(testing.allocator, "Hello");
    try string.appendSlice(testing.allocator, ", ");
    try string.appendSlice(testing.allocator, "World!");

    try testing.expect(std.mem.eql(u8, string.items, "Hello, World!"));
}

// Comparison table

test "comparing the three types" {
    // 1. Fixed Array [N]T
    const fixed: [3]i32 = [_]i32{ 1, 2, 3 };
    // - Size known at compile time
    // - Lives on stack
    // - Cannot grow
    // - No allocator needed
    try testing.expectEqual(@as(usize, 3), fixed.len);

    // 2. Slice []T
    const slice_view: []const i32 = &fixed;
    // - View into array
    // - Size known at runtime
    // - Just pointer + length
    // - Doesn't own memory
    try testing.expectEqual(@as(usize, 3), slice_view.len);

    // 3. ArrayList
    var dynamic = std.ArrayList(i32){};
    defer dynamic.deinit(testing.allocator);
    try dynamic.append(testing.allocator, 1);
    try dynamic.append(testing.allocator, 2);
    try dynamic.append(testing.allocator, 3);
    // - Can grow and shrink
    // - Owns memory (needs allocator)
    // - .items gives you a slice
    // - Like Python list or Java ArrayList
    try testing.expectEqual(@as(usize, 3), dynamic.items.len);
}

// Summary:
// [N]T      - Fixed size, compile-time, stack, no allocator
// []T       - View/pointer, runtime size, doesn't own memory
// ArrayList - Growable, heap, needs allocator, owns memory
//
// When to use what:
// - Know size at compile time? Use [N]T
// - Passing arrays to functions? Use []T slice parameter
// - Need to grow/shrink? Use ArrayList
// - Working with strings? Usually []const u8 (slice)
```

### See Also

- Recipe 0.9: Understanding Pointers and References
- Recipe 0.12: Understanding Allocators
- Recipe 1.7: Ordered HashMap (more data structures)

---

## Recipe 0.7: Functions and the Standard Library {#recipe-0-7}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, fundamentals, hashmap, memory, resource-cleanup, slices, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_7.zig`

### Problem

You need to organize code into reusable functions, leverage Zig's standard library, and understand why some error messages mention "comptime". How do you define functions? What's in the standard library? What does `comptime` mean and why do generic functions need it?

### Solution

Zig provides:

1. **Explicit function definitions** - All parameter and return types must be declared
2. **Error returns with `!T`** - Built-in error handling mechanism
3. **Rich standard library** - Modules for strings, math, collections, I/O, and more
4. **Comptime for generics** - Write functions that work with any type using compile-time parameters

These features combine to create safe, reusable code without hidden behavior.

### Discussion

### Part 1: Basic Function Definition

```zig
// Part 1: Basic Function Definition
//
// Functions are defined with `fn`, must declare parameter types and return type

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "basic function definition" {
    const result = add(5, 3);
    try testing.expectEqual(@as(i32, 8), result);
}

fn greet(name: []const u8) void {
    // void means no return value
    std.debug.print("Hello, {s}!\n", .{name});
}

test "function with no return value" {
    // Functions returning void still get called normally
    greet("Zig");
    // Can't test print output easily, but this shows the pattern
}

// Functions can take multiple parameters of different types
fn formatMessage(count: usize, item: []const u8) void {
    std.debug.print("You have {d} {s}\n", .{ count, item });
}

test "function with multiple parameters" {
    formatMessage(5, "apples");
}
```

**Coming from Python/JavaScript:** There's no default parameter values, no keyword arguments, and all types must be explicit. Zig doesn't infer function signatures from usage.

### Part 2: Functions Returning Errors

```zig
// Part 2: Functions Returning Errors
//
// Use `!T` to return either an error or a value
// This is Zig's error handling mechanism

fn divide(a: i32, b: i32) !i32 {
    if (b == 0) {
        return error.DivisionByZero;
    }
    return @divTrunc(a, b);
}

test "function returning error union" {
    // Success case
    const result = try divide(10, 2);
    try testing.expectEqual(@as(i32, 5), result);

    // Error case
    const err_result = divide(10, 0);
    try testing.expectError(error.DivisionByZero, err_result);
}

// Can use `try` to propagate errors up the call stack
fn safeDivide(a: i32, b: i32) !i32 {
    // `try` returns on error, otherwise unwraps the value
    const result = try divide(a, b);
    return result * 2;
}

test "propagating errors with try" {
    const result = try safeDivide(10, 2);
    try testing.expectEqual(@as(i32, 10), result);

    // Error propagates up
    const err = safeDivide(10, 0);
    try testing.expectError(error.DivisionByZero, err);
}

// Can use `catch` to handle errors inline
fn divideOrDefault(a: i32, b: i32) i32 {
    return divide(a, b) catch 0;
}

test "handling errors with catch" {
    const result1 = divideOrDefault(10, 2);
    try testing.expectEqual(@as(i32, 5), result1);

    const result2 = divideOrDefault(10, 0);
    try testing.expectEqual(@as(i32, 0), result2);
}
```

**Coming from Java/C++:** Zig doesn't use exceptions. Errors are values returned from functions, making error paths explicit in the code.

### Part 3: Using the Standard Library

```zig
// Part 3: Using the Standard Library
//
// Import std and use its modules

test "using standard library for strings" {
    const str = "Hello, World!";

    // std.mem - memory operations
    try testing.expect(std.mem.startsWith(u8, str, "Hello"));
    try testing.expect(std.mem.endsWith(u8, str, "World!"));

    // Finding substrings
    const index = std.mem.indexOf(u8, str, "World");
    try testing.expect(index != null);
    try testing.expectEqual(@as(usize, 7), index.?);
}

test "using standard library for math" {
    // Builtin math operations
    const abs_val = @abs(@as(i32, -42));
    try testing.expectEqual(@as(i32, 42), abs_val);

    const min_val = @min(10, 20);
    try testing.expectEqual(@as(i32, 10), min_val);

    const max_val = @max(10, 20);
    try testing.expectEqual(@as(i32, 20), max_val);

    // std.math - Check for NaN, infinity
    const nan = std.math.nan(f32);
    try testing.expect(std.math.isNan(nan));

    const inf = std.math.inf(f32);
    try testing.expect(std.math.isInf(inf));
}

test "using standard library for collections" {
    // ArrayList - growable array
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    try list.append(testing.allocator, 1);
    try list.append(testing.allocator, 2);
    try list.append(testing.allocator, 3);

    try testing.expectEqual(@as(usize, 3), list.items.len);
    try testing.expectEqual(@as(i32, 2), list.items[1]);

    // HashMap - key-value mapping
    var map = std.StringHashMap(i32).init(testing.allocator);
    defer map.deinit();

    // Note: StringHashMap stores key references, not copies.
    // String literals like "answer" are safe because they have static lifetime.
    // For dynamic keys, see idiomatic_examples.zig Cache.put() for ownership patterns.
    try map.put("answer", 42);
    try map.put("year", 2025);

    const value = map.get("answer");
    try testing.expect(value != null);
    try testing.expectEqual(@as(i32, 42), value.?);
}

test "using std.debug.print for logging" {
    // std.debug.print outputs to stderr
    std.debug.print("\n[DEBUG] This is a debug message\n", .{});

    // Format specifiers:
    // {d} - decimal integer
    // {s} - string
    // {x} - hexadecimal
    // {b} - binary
    const num: i32 = 42;
    const name = "Zig";
    std.debug.print("[DEBUG] num={d}, name={s}\n", .{ num, name });
}
```

**Key std library modules:**
- `std.mem` - Memory operations (copy, compare, search)
- `std.math` - Mathematical functions
- `std.fmt` - Formatting and printing
- `std.ArrayList` - Growable arrays
- `std.HashMap` - Hash maps
- `std.fs` - File system operations
- `std.io` - Input/output
- `std.debug` - Debug utilities

### Part 4: Comptime Basics - Generic Functions

```zig
// Part 4: Comptime Basics - Generic Functions
//
// Use `comptime` to create generic functions that work with any type

fn maximum(comptime T: type, a: T, b: T) T {
    // T is determined at compile time
    // This function works with any type that supports comparison
    return if (a > b) a else b;
}

test "generic function with comptime type parameter" {
    // Works with integers
    const max_int = maximum(i32, 10, 20);
    try testing.expectEqual(@as(i32, 20), max_int);

    // Works with floats
    const max_float = maximum(f32, 3.14, 2.71);
    try testing.expect(@abs(max_float - 3.14) < 0.01);

    // Works with unsigned integers
    const max_uint = maximum(u8, 100, 200);
    try testing.expectEqual(@as(u8, 200), max_uint);
}

// Generic function that works with any array type
fn sum(comptime T: type, items: []const T) T {
    var total: T = 0;
    for (items) |item| {
        total += item;
    }
    return total;
}

test "generic sum function" {
    const ints = [_]i32{ 1, 2, 3, 4, 5 };
    const total = sum(i32, &ints);
    try testing.expectEqual(@as(i32, 15), total);

    const floats = [_]f32{ 1.0, 2.0, 3.0 };
    const float_sum = sum(f32, &floats);
    try testing.expect(@abs(float_sum - 6.0) < 0.01);
}

// Comptime parameters must be known at compile time
fn createArray(comptime size: usize, comptime T: type, value: T) [size]T {
    var arr: [size]T = undefined;
    for (0..size) |i| {
        arr[i] = value;
    }
    return arr;
}

test "comptime size parameter" {
    // Size must be compile-time known
    const arr = createArray(5, i32, 42);

    try testing.expectEqual(@as(usize, 5), arr.len);
    try testing.expectEqual(@as(i32, 42), arr[0]);
    try testing.expectEqual(@as(i32, 42), arr[4]);
}

// Why comptime is needed: Type information doesn't exist at runtime
fn typeInfo(comptime T: type) void {
    // @typeName returns the name of a type
    const name = @typeName(T);
    std.debug.print("Type: {s}\n", .{name});

    // @sizeOf returns size in bytes
    const size = @sizeOf(T);
    std.debug.print("Size: {d} bytes\n", .{size});
}

test "type introspection with comptime" {
    typeInfo(i32);
    typeInfo(f64);
    typeInfo([10]u8);
}

// Common comptime error: trying to use runtime value as comptime parameter
test "understanding comptime errors" {
    // This works - comptime known
    const size: usize = 5;
    var arr1: [size]i32 = undefined;
    _ = &arr1;

    // This would NOT work - runtime value:
    // var runtime_size: usize = 5;
    // var arr2: [runtime_size]i32 = undefined;  // error: unable to resolve comptime value

    // For runtime-sized collections, use ArrayList
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    const runtime_size: usize = 5;
    for (0..runtime_size) |_| {
        try list.append(testing.allocator, 0);
    }

    try testing.expectEqual(runtime_size, list.items.len);
}
```

The `comptime T: type` parameter tells Zig that `T` is a type known at compile time. This lets the function work with any type.

### Why Comptime is Needed

Type information doesn't exist at runtime in Zig. To work with types, you need `comptime`:

```zig
fn typeInfo(comptime T: type) void {
    const name = @typeName(T);
    std.debug.print("Type: {s}\n", .{name});

    const size = @sizeOf(T);
    std.debug.print("Size: {d} bytes\n", .{size});
}

test "type introspection with comptime" {
    typeInfo(i32);    // Type: i32, Size: 4 bytes
    typeInfo(f64);    // Type: f64, Size: 8 bytes
    typeInfo([10]u8); // Type: [10]u8, Size: 10 bytes
}
```

### Understanding Comptime Errors

The most common comptime error is trying to use a runtime value where a compile-time value is required:

```zig
test "understanding comptime errors" {
    // This works - comptime known
    const size: usize = 5;
    var arr1: [size]i32 = undefined;

    // This would NOT work - runtime value:
    // var runtime_size: usize = 5;
    // var arr2: [runtime_size]i32 = undefined;
    // error: unable to resolve comptime value

    // For runtime-sized collections, use ArrayList
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    const runtime_size: usize = 5;
    for (0..runtime_size) |_| {
        try list.append(testing.allocator, 0);
    }
}
```

**When you see "unable to resolve comptime value":**
- You're trying to use a runtime value in a place that requires compile-time information
- Common cases: array sizes, type parameters
- Solution: Use ArrayList or other runtime collections instead

### Putting It All Together

Here's a generic function that combines errors, comptime, and the standard library:

```zig
test "putting it all together" {
    const findMax = struct {
        fn call(comptime T: type, items: []const T) !T {
            if (items.len == 0) {
                return error.EmptySlice;
            }
            var max_val = items[0];
            for (items[1..]) |item| {
                if (item > max_val) {
                    max_val = item;
                }
            }
            return max_val;
        }
    }.call;

    const numbers = [_]i32{ 3, 7, 2, 9, 1 };
    const max_num = try findMax(i32, &numbers);
    try testing.expectEqual(@as(i32, 9), max_num);

    // Error case
    const empty: [0]i32 = .{};
    const err = findMax(i32, &empty);
    try testing.expectError(error.EmptySlice, err);
}
```

This function:
- Uses `comptime T: type` to work with any type
- Returns `!T` to handle errors (empty slice)
- Uses `try` for error handling
- Works with slices from the standard library

**Coming from C++:** Zig's comptime is like templates but runs actual Zig code at compile time. It's more powerful and easier to debug than text-based template metaprogramming.

**Coming from Java:** Think of comptime as generics, but resolved entirely at compile time with full type safety and no runtime overhead.

### Common Patterns

**Function returning errors:**
```zig
fn doSomething() !void {
    // Can return errors
    if (bad_condition) return error.SomethingWrong;
}
```

**Generic function:**
```zig
fn process(comptime T: type, value: T) T {
    // Works with any type
    return value;
}
```

**Using standard library:**
```zig
const std = @import("std");

// Use std modules
const result = std.mem.eql(u8, "hello", "hello");
```

### Common Mistakes

**Forgetting to handle errors:**
```zig
const result = divide(10, 0);  // error: expected type 'i32', found 'anyerror!i32'
const result = try divide(10, 0);  // fixed
```

**Using runtime value for comptime parameter:**
```zig
var size: usize = 5;
var arr: [size]i32 = undefined;  // error: unable to resolve comptime value

const size: usize = 5;  // fixed - const is comptime known
var arr: [size]i32 = undefined;
```

**Wrong format specifier:**
```zig
std.debug.print("{s}\n", .{42});  // error: {s} is for strings
std.debug.print("{d}\n", .{42});  // fixed - {d} for integers
```

### Full Tested Code

```zig
// Recipe 0.7: Functions and the Standard Library (EXPANDED)
// Target Zig Version: 0.15.2
//
// This recipe covers defining functions, working with the standard library,
// and introduces basic comptime parameters for generic functions.

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_function
// Part 1: Basic Function Definition
//
// Functions are defined with `fn`, must declare parameter types and return type

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "basic function definition" {
    const result = add(5, 3);
    try testing.expectEqual(@as(i32, 8), result);
}

fn greet(name: []const u8) void {
    // void means no return value
    std.debug.print("Hello, {s}!\n", .{name});
}

test "function with no return value" {
    // Functions returning void still get called normally
    greet("Zig");
    // Can't test print output easily, but this shows the pattern
}

// Functions can take multiple parameters of different types
fn formatMessage(count: usize, item: []const u8) void {
    std.debug.print("You have {d} {s}\n", .{ count, item });
}

test "function with multiple parameters" {
    formatMessage(5, "apples");
}
// ANCHOR_END: basic_function

// ANCHOR: error_return
// Part 2: Functions Returning Errors
//
// Use `!T` to return either an error or a value
// This is Zig's error handling mechanism

fn divide(a: i32, b: i32) !i32 {
    if (b == 0) {
        return error.DivisionByZero;
    }
    return @divTrunc(a, b);
}

test "function returning error union" {
    // Success case
    const result = try divide(10, 2);
    try testing.expectEqual(@as(i32, 5), result);

    // Error case
    const err_result = divide(10, 0);
    try testing.expectError(error.DivisionByZero, err_result);
}

// Can use `try` to propagate errors up the call stack
fn safeDivide(a: i32, b: i32) !i32 {
    // `try` returns on error, otherwise unwraps the value
    const result = try divide(a, b);
    return result * 2;
}

test "propagating errors with try" {
    const result = try safeDivide(10, 2);
    try testing.expectEqual(@as(i32, 10), result);

    // Error propagates up
    const err = safeDivide(10, 0);
    try testing.expectError(error.DivisionByZero, err);
}

// Can use `catch` to handle errors inline
fn divideOrDefault(a: i32, b: i32) i32 {
    return divide(a, b) catch 0;
}

test "handling errors with catch" {
    const result1 = divideOrDefault(10, 2);
    try testing.expectEqual(@as(i32, 5), result1);

    const result2 = divideOrDefault(10, 0);
    try testing.expectEqual(@as(i32, 0), result2);
}
// ANCHOR_END: error_return

// ANCHOR: stdlib_usage
// Part 3: Using the Standard Library
//
// Import std and use its modules

test "using standard library for strings" {
    const str = "Hello, World!";

    // std.mem - memory operations
    try testing.expect(std.mem.startsWith(u8, str, "Hello"));
    try testing.expect(std.mem.endsWith(u8, str, "World!"));

    // Finding substrings
    const index = std.mem.indexOf(u8, str, "World");
    try testing.expect(index != null);
    try testing.expectEqual(@as(usize, 7), index.?);
}

test "using standard library for math" {
    // Builtin math operations
    const abs_val = @abs(@as(i32, -42));
    try testing.expectEqual(@as(i32, 42), abs_val);

    const min_val = @min(10, 20);
    try testing.expectEqual(@as(i32, 10), min_val);

    const max_val = @max(10, 20);
    try testing.expectEqual(@as(i32, 20), max_val);

    // std.math - Check for NaN, infinity
    const nan = std.math.nan(f32);
    try testing.expect(std.math.isNan(nan));

    const inf = std.math.inf(f32);
    try testing.expect(std.math.isInf(inf));
}

test "using standard library for collections" {
    // ArrayList - growable array
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    try list.append(testing.allocator, 1);
    try list.append(testing.allocator, 2);
    try list.append(testing.allocator, 3);

    try testing.expectEqual(@as(usize, 3), list.items.len);
    try testing.expectEqual(@as(i32, 2), list.items[1]);

    // HashMap - key-value mapping
    var map = std.StringHashMap(i32).init(testing.allocator);
    defer map.deinit();

    // Note: StringHashMap stores key references, not copies.
    // String literals like "answer" are safe because they have static lifetime.
    // For dynamic keys, see idiomatic_examples.zig Cache.put() for ownership patterns.
    try map.put("answer", 42);
    try map.put("year", 2025);

    const value = map.get("answer");
    try testing.expect(value != null);
    try testing.expectEqual(@as(i32, 42), value.?);
}

test "using std.debug.print for logging" {
    // std.debug.print outputs to stderr
    std.debug.print("\n[DEBUG] This is a debug message\n", .{});

    // Format specifiers:
    // {d} - decimal integer
    // {s} - string
    // {x} - hexadecimal
    // {b} - binary
    const num: i32 = 42;
    const name = "Zig";
    std.debug.print("[DEBUG] num={d}, name={s}\n", .{ num, name });
}
// ANCHOR_END: stdlib_usage

// ANCHOR: comptime_basics
// Part 4: Comptime Basics - Generic Functions
//
// Use `comptime` to create generic functions that work with any type

fn maximum(comptime T: type, a: T, b: T) T {
    // T is determined at compile time
    // This function works with any type that supports comparison
    return if (a > b) a else b;
}

test "generic function with comptime type parameter" {
    // Works with integers
    const max_int = maximum(i32, 10, 20);
    try testing.expectEqual(@as(i32, 20), max_int);

    // Works with floats
    const max_float = maximum(f32, 3.14, 2.71);
    try testing.expect(@abs(max_float - 3.14) < 0.01);

    // Works with unsigned integers
    const max_uint = maximum(u8, 100, 200);
    try testing.expectEqual(@as(u8, 200), max_uint);
}

// Generic function that works with any array type
fn sum(comptime T: type, items: []const T) T {
    var total: T = 0;
    for (items) |item| {
        total += item;
    }
    return total;
}

test "generic sum function" {
    const ints = [_]i32{ 1, 2, 3, 4, 5 };
    const total = sum(i32, &ints);
    try testing.expectEqual(@as(i32, 15), total);

    const floats = [_]f32{ 1.0, 2.0, 3.0 };
    const float_sum = sum(f32, &floats);
    try testing.expect(@abs(float_sum - 6.0) < 0.01);
}

// Comptime parameters must be known at compile time
fn createArray(comptime size: usize, comptime T: type, value: T) [size]T {
    var arr: [size]T = undefined;
    for (0..size) |i| {
        arr[i] = value;
    }
    return arr;
}

test "comptime size parameter" {
    // Size must be compile-time known
    const arr = createArray(5, i32, 42);

    try testing.expectEqual(@as(usize, 5), arr.len);
    try testing.expectEqual(@as(i32, 42), arr[0]);
    try testing.expectEqual(@as(i32, 42), arr[4]);
}

// Why comptime is needed: Type information doesn't exist at runtime
fn typeInfo(comptime T: type) void {
    // @typeName returns the name of a type
    const name = @typeName(T);
    std.debug.print("Type: {s}\n", .{name});

    // @sizeOf returns size in bytes
    const size = @sizeOf(T);
    std.debug.print("Size: {d} bytes\n", .{size});
}

test "type introspection with comptime" {
    typeInfo(i32);
    typeInfo(f64);
    typeInfo([10]u8);
}

// Common comptime error: trying to use runtime value as comptime parameter
test "understanding comptime errors" {
    // This works - comptime known
    const size: usize = 5;
    var arr1: [size]i32 = undefined;
    _ = &arr1;

    // This would NOT work - runtime value:
    // var runtime_size: usize = 5;
    // var arr2: [runtime_size]i32 = undefined;  // error: unable to resolve comptime value

    // For runtime-sized collections, use ArrayList
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    const runtime_size: usize = 5;
    for (0..runtime_size) |_| {
        try list.append(testing.allocator, 0);
    }

    try testing.expectEqual(runtime_size, list.items.len);
}
// ANCHOR_END: comptime_basics

// Summary examples

test "putting it all together" {
    // Define a generic function that handles errors
    const findMax = struct {
        fn call(comptime T: type, items: []const T) !T {
            if (items.len == 0) {
                return error.EmptySlice;
            }
            var max_val = items[0];
            for (items[1..]) |item| {
                if (item > max_val) {
                    max_val = item;
                }
            }
            return max_val;
        }
    }.call;

    const numbers = [_]i32{ 3, 7, 2, 9, 1 };
    const max_num = try findMax(i32, &numbers);
    try testing.expectEqual(@as(i32, 9), max_num);

    // Error case
    const empty: [0]i32 = .{};
    const err = findMax(i32, &empty);
    try testing.expectError(error.EmptySlice, err);
}

// Summary:
// - Functions defined with `fn`, explicit types required
// - `!T` for error returns, use `try` or `catch` to handle
// - std library has modules: std.mem, std.math, std.debug, etc.
// - `comptime` creates generic functions that work with any type
// - comptime parameters must be compile-time known
// - Use ArrayList for runtime-sized collections
```

### See Also

- Recipe 0.11: Optionals, Errors, and Resource Cleanup
- Recipe 0.12: Understanding Allocators
- Recipe 0.13: Testing and Debugging Fundamentals

---

## Recipe 0.8: Control Flow and Iteration {#recipe-0-8}

**Tags:** arraylist, data-structures, error-handling, fundamentals, slices, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_8.zig`

### Problem

You need to make decisions and repeat operations in your Zig programs. How do if statements work? What about loops? How do you break out of nested loops?

### Solution

Zig has familiar control flow constructs with some unique twists:

- **if/else** - Conditions must be `bool` (no truthy/falsy)
- **switch** - Exhaustive pattern matching (as an expression)
- **while** - Loops with optional continue expressions
- **for** - Iterates over arrays, slices, and ranges
- **Labeled blocks** - Control nested loops precisely

All control flow in Zig is explicit and predictable - no hidden behavior.

### Discussion

### If/Else Statements

```zig
// If/Else Statements
//
// Zig's if statements are similar to other languages, but conditions must be bool
// (no truthy/falsy values like in C or JavaScript)

test "basic if statement" {
    const x: i32 = 10;

    if (x > 5) {
        try testing.expect(true);
    } else {
        try testing.expect(false);
    }
}

test "if expressions return values" {
    const x: i32 = 10;

    // if is an expression - it returns a value
    const result = if (x > 5) "big" else "small";

    try testing.expect(std.mem.eql(u8, result, "big"));
}

test "if with optional unwrapping" {
    const maybe_value: ?i32 = 42;

    // Unwrap optional with if
    if (maybe_value) |value| {
        try testing.expectEqual(@as(i32, 42), value);
    } else {
        try testing.expect(false); // This won't run
    }
}

test "if with error unwrapping" {
    const result: anyerror!i32 = 42;

    // Unwrap error union with if
    if (result) |value| {
        try testing.expectEqual(@as(i32, 42), value);
    } else |err| {
        _ = err;
        try testing.expect(false); // This won't run
    }
}

test "conditions must be bool" {
    const x: i32 = 1;

    // This works (explicit comparison)
    if (x != 0) {
        try testing.expect(true);
    }

    // This would NOT compile (no implicit conversion to bool):
    // if (x) { }  // error: expected bool, found i32
}
```

This might feel restrictive at first, but it prevents bugs. Your intent is clear.

### Switch Statements

```zig
// Switch Statements
//
// Zig's switch is powerful and used as an expression.
// All cases must be handled (exhaustive).

test "basic switch" {
    const x: i32 = 2;

    const result = switch (x) {
        1 => "one",
        2 => "two",
        3 => "three",
        else => "other",
    };

    try testing.expect(std.mem.eql(u8, result, "two"));
}

test "switch with multiple values" {
    const x: i32 = 5;

    const result = switch (x) {
        1, 2, 3 => "small",
        4, 5, 6 => "medium",
        7, 8, 9 => "large",
        else => "other",
    };

    try testing.expect(std.mem.eql(u8, result, "medium"));
}

test "switch with ranges" {
    const x: i32 = 15;

    const result = switch (x) {
        0...9 => "single digit",
        10...99 => "double digit",
        100...999 => "triple digit",
        else => "other",
    };

    try testing.expect(std.mem.eql(u8, result, "double digit"));
}

test "switch must be exhaustive" {
    const x: u2 = 2;

    // For small types, you can enumerate all cases
    const category = switch (x) {
        0 => "zero",
        1 => "one",
        2 => "two",
        3 => "three",
        // No else needed - all u2 values covered
    };

    try testing.expect(std.mem.eql(u8, category, "two"));
}

test "switch with blocks" {
    const x: i32 = 2;

    const result = switch (x) {
        1 => blk: {
            // Can use blocks for complex logic
            const val = x * 10;
            break :blk val;
        },
        2 => blk: {
            const val = x * 20;
            break :blk val;
        },
        else => 0,
    };

    try testing.expectEqual(@as(i32, 40), result);
}
```

The `...` syntax creates an inclusive range (0 through 9, not 0 to 8).

Use labeled blocks (`blk:`) when you need multiple statements in a case.

### While Loops

```zig
// While Loops
//
// Zig has while loops with optional continue expressions

test "basic while loop" {
    var i: i32 = 0;
    var sum: i32 = 0;

    while (i < 5) {
        sum += i;
        i += 1;
    }

    try testing.expectEqual(@as(i32, 10), sum);
}

test "while with continue expression" {
    var sum: i32 = 0;
    var i: i32 = 0;

    // The continue expression runs after each iteration
    while (i < 5) : (i += 1) {
        sum += i;
    }

    try testing.expectEqual(@as(i32, 10), sum);
}

test "while with break" {
    var i: i32 = 0;

    while (true) {
        if (i >= 5) break;
        i += 1;
    }

    try testing.expectEqual(@as(i32, 5), i);
}

test "while with continue" {
    var sum: i32 = 0;
    var i: i32 = 0;

    while (i < 10) : (i += 1) {
        // Skip even numbers
        if (@rem(i, 2) == 0) continue;
        sum += i;
    }

    // Sum of odd numbers: 1+3+5+7+9 = 25
    try testing.expectEqual(@as(i32, 25), sum);
}

test "while with optional unwrapping" {
    var maybe: ?i32 = 10;

    // Loop while optional has a value
    while (maybe) |value| {
        try testing.expectEqual(@as(i32, 10), value);
        maybe = null; // Exit loop
    }

    try testing.expectEqual(@as(?i32, null), maybe);
}
```

Note: Use `@rem` for remainder with signed integers (not `%`).

### For Loops

```zig
// For Loops
//
// Zig's for loops iterate over arrays, slices, and ranges

test "for loop over array" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    var sum: i32 = 0;

    for (numbers) |n| {
        sum += n;
    }

    try testing.expectEqual(@as(i32, 15), sum);
}

test "for loop with index" {
    const numbers = [_]i32{ 10, 20, 30 };

    // Modern Zig syntax for index
    for (numbers, 0..) |n, i| {
        try testing.expectEqual(numbers[i], n);
    }
}

test "for loop over range" {
    var sum: i32 = 0;

    // Loop from 0 to 4 (not including 5)
    for (0..5) |i| {
        sum += @intCast(i);
    }

    try testing.expectEqual(@as(i32, 10), sum);
}

test "for loop with break" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    var found = false;

    for (numbers) |n| {
        if (n == 3) {
            found = true;
            break;
        }
    }

    try testing.expect(found);
}

test "for loop with continue" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    var sum: i32 = 0;

    for (numbers) |n| {
        // Skip even numbers
        if (@rem(n, 2) == 0) continue;
        sum += n;
    }

    // Sum of odd numbers: 1+3+5 = 9
    try testing.expectEqual(@as(i32, 9), sum);
}

test "for loop as expression with else" {
    const numbers = [_]i32{ 2, 4, 6, 8 };

    // Find first odd number, or return 0
    const first_odd = for (numbers) |n| {
        if (@rem(n, 2) == 1) break n;
    } else 0;

    try testing.expectEqual(@as(i32, 0), first_odd);
}

test "iterating multiple arrays simultaneously" {
    const a = [_]i32{ 1, 2, 3 };
    const b = [_]i32{ 10, 20, 30 };
    var sum: i32 = 0;

    // Iterate both arrays together
    for (a, b) |x, y| {
        sum += x + y;
    }

    try testing.expectEqual(@as(i32, 66), sum);
}
```

The `0..` creates an infinite range, but it only iterates as far as the array.

The `else` branch runs if the loop completes without breaking.

### Labeled Blocks and Nested Loops

```zig
// Labeled Blocks and Nested Loops
//
// Use labels to break/continue outer loops from inner loops

test "labeled break in nested loops" {
    var count: i32 = 0;

    outer: for (0..3) |i| {
        for (0..3) |j| {
            count += 1;
            if (i == 1 and j == 1) {
                break :outer; // Break out of outer loop
            }
        }
    }

    // Iterations: (0,0), (0,1), (0,2), (1,0), (1,1) = 5
    try testing.expectEqual(@as(i32, 5), count);
}

test "labeled continue in nested loops" {
    var sum: i32 = 0;

    outer: for (0..3) |i| {
        for (0..3) |j| {
            if (j == 1) continue :outer; // Skip to next outer iteration
            sum += @as(i32, @intCast(i * 10 + j));
        }
    }

    // Only processes j=0 for each i: 00, 10, 20
    try testing.expectEqual(@as(i32, 30), sum);
}

test "labeled blocks for complex control flow" {
    const result = blk: {
        var i: i32 = 0;
        while (i < 10) : (i += 1) {
            if (i == 5) break :blk i * 2;
        }
        break :blk 0;
    };

    try testing.expectEqual(@as(i32, 10), result);
}

test "nested labeled blocks" {
    const result = outer: {
        const inner_result = inner: {
            break :inner 42;
        };
        break :outer inner_result * 2;
    };

    try testing.expectEqual(@as(i32, 84), result);
}
```

Labeled blocks let you return values from complex control flow.

### Combining Everything

Real code often combines multiple control flow constructs:

```zig
test "combining control flow" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    var result: i32 = 0;

    for (numbers) |n| {
        // Skip numbers less than 3
        if (n < 3) continue;

        // Stop at 8
        if (n > 8) break;

        // Add only odd numbers
        if (@rem(n, 2) == 0) continue;

        result += n;
    }

    // Sum of 3, 5, 7 = 15
    try testing.expectEqual(@as(i32, 15), result);
}
```

### Key Differences from Other Languages

**From JavaScript/Python:**
- No truthy/falsy values - conditions must be `bool`
- `switch` must be exhaustive (all cases handled)
- No `for...in` or `for...of` - use `for (array) |item|`

**From C:**
- Switch doesn't fall through (no `break` needed in each case)
- For loops don't use C-style `for (init; cond; inc)`
- Conditions must be `bool`, not any integer type

**From Rust:**
- Similar `if let` pattern for optional unwrapping
- Similar exhaustive `match` (Zig's `switch`)
- Labeled loops work the same way

### Common Beginner Mistakes

**Using non-bool in conditions:**
```zig
const x: i32 = 1;
if (x) { }  // error: expected bool, found i32
if (x != 0) { }  // fixed
```

**Forgetting else in switch:**
```zig
const x: i32 = 5;
const result = switch (x) {
    1 => "one",
    2 => "two",
    // Missing else!
};
// error: switch must handle all possibilities
```

**Using % with signed integers:**
```zig
if (x % 2 == 0) { }  // error
if (@rem(x, 2) == 0) { }  // fixed
```

**Wrong for loop syntax:**
```zig
// Old C-style (doesn't work)
for (var i = 0; i < 10; i++) { }

// Zig way
for (0..10) |i| { }
```

### Full Tested Code

```zig
// Recipe 0.8: Control Flow and Iteration
// Target Zig Version: 0.15.2
//
// This recipe demonstrates Zig's control flow constructs: if, switch, while, for,
// and how to use break, continue, and labeled blocks.

const std = @import("std");
const testing = std.testing;

// ANCHOR: if_else
// If/Else Statements
//
// Zig's if statements are similar to other languages, but conditions must be bool
// (no truthy/falsy values like in C or JavaScript)

test "basic if statement" {
    const x: i32 = 10;

    if (x > 5) {
        try testing.expect(true);
    } else {
        try testing.expect(false);
    }
}

test "if expressions return values" {
    const x: i32 = 10;

    // if is an expression - it returns a value
    const result = if (x > 5) "big" else "small";

    try testing.expect(std.mem.eql(u8, result, "big"));
}

test "if with optional unwrapping" {
    const maybe_value: ?i32 = 42;

    // Unwrap optional with if
    if (maybe_value) |value| {
        try testing.expectEqual(@as(i32, 42), value);
    } else {
        try testing.expect(false); // This won't run
    }
}

test "if with error unwrapping" {
    const result: anyerror!i32 = 42;

    // Unwrap error union with if
    if (result) |value| {
        try testing.expectEqual(@as(i32, 42), value);
    } else |err| {
        _ = err;
        try testing.expect(false); // This won't run
    }
}

test "conditions must be bool" {
    const x: i32 = 1;

    // This works (explicit comparison)
    if (x != 0) {
        try testing.expect(true);
    }

    // This would NOT compile (no implicit conversion to bool):
    // if (x) { }  // error: expected bool, found i32
}
// ANCHOR_END: if_else

// ANCHOR: switch_statement
// Switch Statements
//
// Zig's switch is powerful and used as an expression.
// All cases must be handled (exhaustive).

test "basic switch" {
    const x: i32 = 2;

    const result = switch (x) {
        1 => "one",
        2 => "two",
        3 => "three",
        else => "other",
    };

    try testing.expect(std.mem.eql(u8, result, "two"));
}

test "switch with multiple values" {
    const x: i32 = 5;

    const result = switch (x) {
        1, 2, 3 => "small",
        4, 5, 6 => "medium",
        7, 8, 9 => "large",
        else => "other",
    };

    try testing.expect(std.mem.eql(u8, result, "medium"));
}

test "switch with ranges" {
    const x: i32 = 15;

    const result = switch (x) {
        0...9 => "single digit",
        10...99 => "double digit",
        100...999 => "triple digit",
        else => "other",
    };

    try testing.expect(std.mem.eql(u8, result, "double digit"));
}

test "switch must be exhaustive" {
    const x: u2 = 2;

    // For small types, you can enumerate all cases
    const category = switch (x) {
        0 => "zero",
        1 => "one",
        2 => "two",
        3 => "three",
        // No else needed - all u2 values covered
    };

    try testing.expect(std.mem.eql(u8, category, "two"));
}

test "switch with blocks" {
    const x: i32 = 2;

    const result = switch (x) {
        1 => blk: {
            // Can use blocks for complex logic
            const val = x * 10;
            break :blk val;
        },
        2 => blk: {
            const val = x * 20;
            break :blk val;
        },
        else => 0,
    };

    try testing.expectEqual(@as(i32, 40), result);
}
// ANCHOR_END: switch_statement

// ANCHOR: while_loops
// While Loops
//
// Zig has while loops with optional continue expressions

test "basic while loop" {
    var i: i32 = 0;
    var sum: i32 = 0;

    while (i < 5) {
        sum += i;
        i += 1;
    }

    try testing.expectEqual(@as(i32, 10), sum);
}

test "while with continue expression" {
    var sum: i32 = 0;
    var i: i32 = 0;

    // The continue expression runs after each iteration
    while (i < 5) : (i += 1) {
        sum += i;
    }

    try testing.expectEqual(@as(i32, 10), sum);
}

test "while with break" {
    var i: i32 = 0;

    while (true) {
        if (i >= 5) break;
        i += 1;
    }

    try testing.expectEqual(@as(i32, 5), i);
}

test "while with continue" {
    var sum: i32 = 0;
    var i: i32 = 0;

    while (i < 10) : (i += 1) {
        // Skip even numbers
        if (@rem(i, 2) == 0) continue;
        sum += i;
    }

    // Sum of odd numbers: 1+3+5+7+9 = 25
    try testing.expectEqual(@as(i32, 25), sum);
}

test "while with optional unwrapping" {
    var maybe: ?i32 = 10;

    // Loop while optional has a value
    while (maybe) |value| {
        try testing.expectEqual(@as(i32, 10), value);
        maybe = null; // Exit loop
    }

    try testing.expectEqual(@as(?i32, null), maybe);
}
// ANCHOR_END: while_loops

// ANCHOR: for_loops
// For Loops
//
// Zig's for loops iterate over arrays, slices, and ranges

test "for loop over array" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    var sum: i32 = 0;

    for (numbers) |n| {
        sum += n;
    }

    try testing.expectEqual(@as(i32, 15), sum);
}

test "for loop with index" {
    const numbers = [_]i32{ 10, 20, 30 };

    // Modern Zig syntax for index
    for (numbers, 0..) |n, i| {
        try testing.expectEqual(numbers[i], n);
    }
}

test "for loop over range" {
    var sum: i32 = 0;

    // Loop from 0 to 4 (not including 5)
    for (0..5) |i| {
        sum += @intCast(i);
    }

    try testing.expectEqual(@as(i32, 10), sum);
}

test "for loop with break" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    var found = false;

    for (numbers) |n| {
        if (n == 3) {
            found = true;
            break;
        }
    }

    try testing.expect(found);
}

test "for loop with continue" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    var sum: i32 = 0;

    for (numbers) |n| {
        // Skip even numbers
        if (@rem(n, 2) == 0) continue;
        sum += n;
    }

    // Sum of odd numbers: 1+3+5 = 9
    try testing.expectEqual(@as(i32, 9), sum);
}

test "for loop as expression with else" {
    const numbers = [_]i32{ 2, 4, 6, 8 };

    // Find first odd number, or return 0
    const first_odd = for (numbers) |n| {
        if (@rem(n, 2) == 1) break n;
    } else 0;

    try testing.expectEqual(@as(i32, 0), first_odd);
}

test "iterating multiple arrays simultaneously" {
    const a = [_]i32{ 1, 2, 3 };
    const b = [_]i32{ 10, 20, 30 };
    var sum: i32 = 0;

    // Iterate both arrays together
    for (a, b) |x, y| {
        sum += x + y;
    }

    try testing.expectEqual(@as(i32, 66), sum);
}
// ANCHOR_END: for_loops

// ANCHOR: labeled_blocks
// Labeled Blocks and Nested Loops
//
// Use labels to break/continue outer loops from inner loops

test "labeled break in nested loops" {
    var count: i32 = 0;

    outer: for (0..3) |i| {
        for (0..3) |j| {
            count += 1;
            if (i == 1 and j == 1) {
                break :outer; // Break out of outer loop
            }
        }
    }

    // Iterations: (0,0), (0,1), (0,2), (1,0), (1,1) = 5
    try testing.expectEqual(@as(i32, 5), count);
}

test "labeled continue in nested loops" {
    var sum: i32 = 0;

    outer: for (0..3) |i| {
        for (0..3) |j| {
            if (j == 1) continue :outer; // Skip to next outer iteration
            sum += @as(i32, @intCast(i * 10 + j));
        }
    }

    // Only processes j=0 for each i: 00, 10, 20
    try testing.expectEqual(@as(i32, 30), sum);
}

test "labeled blocks for complex control flow" {
    const result = blk: {
        var i: i32 = 0;
        while (i < 10) : (i += 1) {
            if (i == 5) break :blk i * 2;
        }
        break :blk 0;
    };

    try testing.expectEqual(@as(i32, 10), result);
}

test "nested labeled blocks" {
    const result = outer: {
        const inner_result = inner: {
            break :inner 42;
        };
        break :outer inner_result * 2;
    };

    try testing.expectEqual(@as(i32, 84), result);
}
// ANCHOR_END: labeled_blocks

// Additional examples

test "inline for loops (compile-time iteration)" {
    const numbers = [_]i32{ 1, 2, 3 };

    // inline keyword unrolls loop at compile time
    var sum: i32 = 0;
    inline for (numbers) |n| {
        sum += n;
    }

    try testing.expectEqual(@as(i32, 6), sum);
}

test "combining control flow" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    var result: i32 = 0;

    for (numbers) |n| {
        // Skip numbers less than 3
        if (n < 3) continue;

        // Stop at 8
        if (n > 8) break;

        // Add only odd numbers
        if (@rem(n, 2) == 0) continue;

        result += n;
    }

    // Sum of 3, 5, 7 = 15
    try testing.expectEqual(@as(i32, 15), result);
}

// Summary:
// - if conditions must be bool (no truthy/falsy)
// - if is an expression (returns a value)
// - switch must be exhaustive (all cases covered)
// - switch is an expression (most common use)
// - while loops have optional continue expressions
// - for loops iterate arrays, slices, and ranges
// - Use labeled blocks for nested loop control
// - break exits loops, continue skips to next iteration
// - Labels let you break/continue outer loops from inner loops
```

### See Also

- Recipe 0.6: Arrays, ArrayLists, and Slices
- Recipe 0.11: Optionals, Errors, and Resource Cleanup
- Recipe 0.10: Structs, Enums, and Simple Data Models

---

## Recipe 0.9: Understanding Pointers and References {#recipe-0-9}

**Tags:** allocators, arraylist, data-structures, error-handling, fundamentals, memory, pointers, slices, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_9.zig`

### Problem

You're coming from Python, JavaScript, or Java where references are automatic and garbage collected. In Zig, you need to understand when and how to use pointers explicitly.

What's the difference between `*T`, `[*]T`, and `[]T`? When do you use `&` and `.*`? When should you pass by value vs pointer? This is essential knowledge that garbage-collected languages hide from you.

### Solution

Zig has three pointer types, each for different use cases:

1. **Single-item pointer `*T`** - Points to exactly one value
2. **Many-item pointer `[*]T`** - Points to unknown number of values (like C pointers)
3. **Slice `[]T`** - Pointer + length (safest, most common)

The key operations:
- Use `&` to take the address of a value
- Use `.*` to dereference a pointer
- Use `*const T` for read-only pointers
- Prefer slices over raw pointers

Understanding pointers is the bridge between high-level and systems programming.

### Discussion

### Part 1: Single-Item Pointers `*T`

```zig
// Part 1: Single-Item Pointers *T
//
// A single-item pointer points to exactly one value

test "basic single-item pointer" {
    var x: i32 = 42;

    // Take address with &
    const ptr: *i32 = &x;

    // Dereference with .*
    try testing.expectEqual(@as(i32, 42), ptr.*);

    // Can modify through pointer
    ptr.* = 100;
    try testing.expectEqual(@as(i32, 100), x);
}

test "const pointers" {
    var x: i32 = 42;

    // *const T - pointer to const value (can't modify)
    const const_ptr: *const i32 = &x;
    try testing.expectEqual(@as(i32, 42), const_ptr.*);

    // This would not compile:
    // const_ptr.* = 100;  // error: cannot assign to constant

    // *T - pointer to mutable value (can modify)
    const mut_ptr: *i32 = &x;
    mut_ptr.* = 100;
    try testing.expectEqual(@as(i32, 100), x);
}

test "pointers to structs" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    var p = Point{ .x = 10, .y = 20 };
    const ptr: *Point = &p;

    // Access fields through pointer (automatic dereferencing)
    try testing.expectEqual(@as(i32, 10), ptr.x);

    // Modify through pointer
    ptr.x = 30;
    try testing.expectEqual(@as(i32, 30), p.x);
}

fn increment(value: *i32) void {
    value.* += 1;
}

test "passing pointers to functions" {
    var x: i32 = 10;

    // Pass pointer to modify the value
    increment(&x);
    try testing.expectEqual(@as(i32, 11), x);

    increment(&x);
    try testing.expectEqual(@as(i32, 12), x);
}
```

**Coming from Python/JavaScript:** These languages hide all pointer operations. When you write `obj.field = value`, the language automatically handles the reference. In Zig, these operations are explicit.

**Coming from C++:** Zig's `*T` is like C++'s `T*`, and `.*` is like C++'s `*ptr`. But Zig auto-dereferences for struct field access.

### Part 2: Many-Item Pointers `[*]T` and Slices `[]T`

```zig
// Part 2: Many-Item Pointers [*]T and Slices []T
//
// Many-item pointers point to multiple values (unknown length)
// Slices are many-item pointers WITH a length

test "many-item pointers" {
    var array = [_]i32{ 1, 2, 3, 4, 5 };

    // Many-item pointer - no length information
    const many_ptr: [*]i32 = &array;

    // Access via indexing (like C pointers)
    try testing.expectEqual(@as(i32, 1), many_ptr[0]);
    try testing.expectEqual(@as(i32, 2), many_ptr[1]);

    // No bounds checking - YOU must track length!
    // many_ptr[100] would be undefined behavior
}

test "slices are better than many-item pointers" {
    var array = [_]i32{ 1, 2, 3, 4, 5 };

    // Slice - pointer + length
    const slice: []i32 = &array;

    // Has length
    try testing.expectEqual(@as(usize, 5), slice.len);

    // Bounds checking in debug builds
    try testing.expectEqual(@as(i32, 1), slice[0]);
    try testing.expectEqual(@as(i32, 5), slice[4]);
}

test "const slices" {
    const array = [_]i32{ 1, 2, 3, 4, 5 };

    // []const T - slice of const values
    const slice: []const i32 = &array;

    try testing.expectEqual(@as(i32, 1), slice[0]);

    // Cannot modify
    // slice[0] = 10;  // error: cannot assign to constant
}

test "slicing arrays" {
    const array = [_]i32{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 };

    // Create sub-slices with [start..end] syntax
    const middle: []const i32 = array[3..7];

    try testing.expectEqual(@as(usize, 4), middle.len);
    try testing.expectEqual(@as(i32, 3), middle[0]);
    try testing.expectEqual(@as(i32, 6), middle[3]);

    // [start..] - from start to end
    const tail: []const i32 = array[7..];
    try testing.expectEqual(@as(usize, 3), tail.len);

    // [0..end] - from beginning to end
    const head: []const i32 = array[0..5];
    try testing.expectEqual(@as(usize, 5), head.len);
}

fn sumSlice(values: []const i32) i32 {
    var total: i32 = 0;
    for (values) |v| {
        total += v;
    }
    return total;
}

test "passing slices to functions" {
    const array = [_]i32{ 1, 2, 3, 4, 5 };

    // Pass entire array as slice
    const total1 = sumSlice(&array);
    try testing.expectEqual(@as(i32, 15), total1);

    // Pass sub-slice
    const total2 = sumSlice(array[0..3]);
    try testing.expectEqual(@as(i32, 6), total2);
}
```

Functions that accept `[]const T` work with any array size - this is the idiomatic way to pass arrays in Zig.

### Part 3: When to Use Pointers vs Values

```zig
// Part 3: When to Use Pointers vs Values
//
// Zig passes small values efficiently, so you don't always need pointers

test "small values - just pass by value" {
    const Point = struct {
        x: i32,
        y: i32,

        fn distance(self: @This()) f32 {
            const dx = @as(f32, @floatFromInt(self.x));
            const dy = @as(f32, @floatFromInt(self.y));
            return @sqrt(dx * dx + dy * dy);
        }
    };

    const p = Point{ .x = 3, .y = 4 };

    // Pass by value - efficient for small structs
    const dist = p.distance();
    try testing.expect(@abs(dist - 5.0) < 0.01);
}

test "when to use pointers" {
    const BigStruct = struct {
        data: [1000]i32,

        fn sum(self: *const @This()) i32 {
            var total: i32 = 0;
            for (self.data) |val| {
                total += val;
            }
            return total;
        }
    };

    var big = BigStruct{ .data = [_]i32{1} ** 1000 };

    // Use pointer to avoid copying large struct
    const total = big.sum();
    try testing.expectEqual(@as(i32, 1000), total);
}

test "when you need to modify a value" {
    const Counter = struct {
        count: i32,

        fn increment(self: *@This()) void {
            self.count += 1;
        }

        fn reset(self: *@This()) void {
            self.count = 0;
        }
    };

    var counter = Counter{ .count = 0 };

    // Pass pointer to modify
    counter.increment();
    try testing.expectEqual(@as(i32, 1), counter.count);

    counter.increment();
    try testing.expectEqual(@as(i32, 2), counter.count);

    counter.reset();
    try testing.expectEqual(@as(i32, 0), counter.count);
}

test "optional pointers" {
    // ?*T - optional pointer (can be null)
    var x: i32 = 42;
    var maybe_ptr: ?*i32 = &x;

    // Check if not null
    if (maybe_ptr) |ptr| {
        try testing.expectEqual(@as(i32, 42), ptr.*);
    }

    // Set to null
    maybe_ptr = null;
    try testing.expectEqual(@as(?*i32, null), maybe_ptr);
}

test "pointer to array vs slice" {
    var array = [_]i32{ 1, 2, 3, 4, 5 };

    // Pointer to array - knows the size in the type
    const array_ptr: *[5]i32 = &array;
    try testing.expectEqual(@as(usize, 5), array_ptr.len);

    // Slice - size known at runtime
    const slice: []i32 = &array;
    try testing.expectEqual(@as(usize, 5), slice.len);

    // Both access the same data
    array_ptr[0] = 99;
    try testing.expectEqual(@as(i32, 99), slice[0]);
}
```

`*[5]i32` knows the size at compile time (it's part of the type). `[]i32` knows the size at runtime (it's a field in the slice).

### Advanced: Sentinel-Terminated Pointers

C strings use null termination. Zig represents this with `[*:0]u8`:

```zig
test "sentinel-terminated pointers" {
    // [*:0]u8 - many-item pointer terminated by 0 (for C strings)
    const c_string: [*:0]const u8 = "hello";

    // Can iterate until sentinel
    var len: usize = 0;
    while (c_string[len] != 0) : (len += 1) {}

    try testing.expectEqual(@as(usize, 5), len);

    // Better: use std.mem.span to convert to slice
    const slice = std.mem.span(c_string);
    try testing.expectEqual(@as(usize, 5), slice.len);
    try testing.expect(std.mem.eql(u8, slice, "hello"));
}
```

Use `std.mem.span` to convert C strings to slices.

### Comparing Pointers vs Values

```zig
test "comparing pointers vs comparing values" {
    var x: i32 = 42;
    var y: i32 = 42;

    const ptr_x: *i32 = &x;
    const ptr_y: *i32 = &y;

    // Different pointers (different addresses)
    try testing.expect(ptr_x != ptr_y);

    // Same values
    try testing.expectEqual(ptr_x.*, ptr_y.*);

    // Pointer to same location
    const also_ptr_x: *i32 = &x;
    try testing.expect(ptr_x == also_ptr_x);
}
```

Comparing pointers (`ptr_x == ptr_y`) checks if they point to the same address. Comparing values (`ptr_x.* == ptr_y.*`) checks if the values are equal.

### Avoiding Dangling Pointers

Never return a pointer to a local variable:

```zig
test "avoiding dangling pointers" {
    // This is BAD - don't do this!
    // fn getBadPointer() *i32 {
    //     var x: i32 = 42;
    //     return &x;  // x goes out of scope!
    // }

    // Instead, return the value
    const getGoodValue = struct {
        fn call() i32 {
            const x: i32 = 42;
            return x;
        }
    }.call;

    const value = getGoodValue();
    try testing.expectEqual(@as(i32, 42), value);
}
```

When a function returns, its local variables are freed. Returning a pointer to them creates a dangling pointer that points to invalid memory.

**Solutions:**
1. Return by value (for small data)
2. Use an allocator and return heap-allocated memory
3. Have the caller provide the memory

### Decision Tree

**Should I use a pointer?**

- Need to modify the value? → Use `*T`
- Struct is large (> 64 bytes)? → Use `*const T` for read-only
- Working with arrays/strings? → Use `[]T` (slice)
- C interop? → Might need `[*]T` or `[*:0]T`
- Otherwise → Pass by value

**Which pointer type?**

- Single value, known at compile time → `*T` or `*const T`
- Array without length tracking → `[*]T` (rare, prefer slices)
- Array with length → `[]T` (slice - most common)
- Nullable pointer → `?*T`

### Common Mistakes

**Returning pointer to local variable:**
```zig
fn bad() *i32 {
    var x: i32 = 42;
    return &x;  // BAD: x is freed when function returns
}
```

**Forgetting to dereference:**
```zig
var x: i32 = 42;
const ptr: *i32 = &x;
const value = ptr;  // error: ptr is *i32, not i32
const value = ptr.*;  // fixed
```

**Using many-item pointer when you need a slice:**
```zig
fn process(ptr: [*]i32) void {
    // How many elements? You don't know!
}

fn process(slice: []i32) void {
    // Much better - you have slice.len
}
```

**Modifying through const pointer:**
```zig
var x: i32 = 42;
const ptr: *const i32 = &x;
ptr.* = 100;  // error: cannot assign to constant
```

### Full Tested Code

```zig
// Recipe 0.9: Understanding Pointers and References (CRITICAL)
// Target Zig Version: 0.15.2
//
// This is essential for beginners from garbage-collected languages.
// Understand when and how to use pointers in Zig.

const std = @import("std");
const testing = std.testing;

// ANCHOR: single_item_pointer
// Part 1: Single-Item Pointers *T
//
// A single-item pointer points to exactly one value

test "basic single-item pointer" {
    var x: i32 = 42;

    // Take address with &
    const ptr: *i32 = &x;

    // Dereference with .*
    try testing.expectEqual(@as(i32, 42), ptr.*);

    // Can modify through pointer
    ptr.* = 100;
    try testing.expectEqual(@as(i32, 100), x);
}

test "const pointers" {
    var x: i32 = 42;

    // *const T - pointer to const value (can't modify)
    const const_ptr: *const i32 = &x;
    try testing.expectEqual(@as(i32, 42), const_ptr.*);

    // This would not compile:
    // const_ptr.* = 100;  // error: cannot assign to constant

    // *T - pointer to mutable value (can modify)
    const mut_ptr: *i32 = &x;
    mut_ptr.* = 100;
    try testing.expectEqual(@as(i32, 100), x);
}

test "pointers to structs" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    var p = Point{ .x = 10, .y = 20 };
    const ptr: *Point = &p;

    // Access fields through pointer (automatic dereferencing)
    try testing.expectEqual(@as(i32, 10), ptr.x);

    // Modify through pointer
    ptr.x = 30;
    try testing.expectEqual(@as(i32, 30), p.x);
}

fn increment(value: *i32) void {
    value.* += 1;
}

test "passing pointers to functions" {
    var x: i32 = 10;

    // Pass pointer to modify the value
    increment(&x);
    try testing.expectEqual(@as(i32, 11), x);

    increment(&x);
    try testing.expectEqual(@as(i32, 12), x);
}
// ANCHOR_END: single_item_pointer

// ANCHOR: many_item_pointer
// Part 2: Many-Item Pointers [*]T and Slices []T
//
// Many-item pointers point to multiple values (unknown length)
// Slices are many-item pointers WITH a length

test "many-item pointers" {
    var array = [_]i32{ 1, 2, 3, 4, 5 };

    // Many-item pointer - no length information
    const many_ptr: [*]i32 = &array;

    // Access via indexing (like C pointers)
    try testing.expectEqual(@as(i32, 1), many_ptr[0]);
    try testing.expectEqual(@as(i32, 2), many_ptr[1]);

    // No bounds checking - YOU must track length!
    // many_ptr[100] would be undefined behavior
}

test "slices are better than many-item pointers" {
    var array = [_]i32{ 1, 2, 3, 4, 5 };

    // Slice - pointer + length
    const slice: []i32 = &array;

    // Has length
    try testing.expectEqual(@as(usize, 5), slice.len);

    // Bounds checking in debug builds
    try testing.expectEqual(@as(i32, 1), slice[0]);
    try testing.expectEqual(@as(i32, 5), slice[4]);
}

test "const slices" {
    const array = [_]i32{ 1, 2, 3, 4, 5 };

    // []const T - slice of const values
    const slice: []const i32 = &array;

    try testing.expectEqual(@as(i32, 1), slice[0]);

    // Cannot modify
    // slice[0] = 10;  // error: cannot assign to constant
}

test "slicing arrays" {
    const array = [_]i32{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 };

    // Create sub-slices with [start..end] syntax
    const middle: []const i32 = array[3..7];

    try testing.expectEqual(@as(usize, 4), middle.len);
    try testing.expectEqual(@as(i32, 3), middle[0]);
    try testing.expectEqual(@as(i32, 6), middle[3]);

    // [start..] - from start to end
    const tail: []const i32 = array[7..];
    try testing.expectEqual(@as(usize, 3), tail.len);

    // [0..end] - from beginning to end
    const head: []const i32 = array[0..5];
    try testing.expectEqual(@as(usize, 5), head.len);
}

fn sumSlice(values: []const i32) i32 {
    var total: i32 = 0;
    for (values) |v| {
        total += v;
    }
    return total;
}

test "passing slices to functions" {
    const array = [_]i32{ 1, 2, 3, 4, 5 };

    // Pass entire array as slice
    const total1 = sumSlice(&array);
    try testing.expectEqual(@as(i32, 15), total1);

    // Pass sub-slice
    const total2 = sumSlice(array[0..3]);
    try testing.expectEqual(@as(i32, 6), total2);
}
// ANCHOR_END: many_item_pointer

// ANCHOR: when_to_use_pointers
// Part 3: When to Use Pointers vs Values
//
// Zig passes small values efficiently, so you don't always need pointers

test "small values - just pass by value" {
    const Point = struct {
        x: i32,
        y: i32,

        fn distance(self: @This()) f32 {
            const dx = @as(f32, @floatFromInt(self.x));
            const dy = @as(f32, @floatFromInt(self.y));
            return @sqrt(dx * dx + dy * dy);
        }
    };

    const p = Point{ .x = 3, .y = 4 };

    // Pass by value - efficient for small structs
    const dist = p.distance();
    try testing.expect(@abs(dist - 5.0) < 0.01);
}

test "when to use pointers" {
    const BigStruct = struct {
        data: [1000]i32,

        fn sum(self: *const @This()) i32 {
            var total: i32 = 0;
            for (self.data) |val| {
                total += val;
            }
            return total;
        }
    };

    var big = BigStruct{ .data = [_]i32{1} ** 1000 };

    // Use pointer to avoid copying large struct
    const total = big.sum();
    try testing.expectEqual(@as(i32, 1000), total);
}

test "when you need to modify a value" {
    const Counter = struct {
        count: i32,

        fn increment(self: *@This()) void {
            self.count += 1;
        }

        fn reset(self: *@This()) void {
            self.count = 0;
        }
    };

    var counter = Counter{ .count = 0 };

    // Pass pointer to modify
    counter.increment();
    try testing.expectEqual(@as(i32, 1), counter.count);

    counter.increment();
    try testing.expectEqual(@as(i32, 2), counter.count);

    counter.reset();
    try testing.expectEqual(@as(i32, 0), counter.count);
}

test "optional pointers" {
    // ?*T - optional pointer (can be null)
    var x: i32 = 42;
    var maybe_ptr: ?*i32 = &x;

    // Check if not null
    if (maybe_ptr) |ptr| {
        try testing.expectEqual(@as(i32, 42), ptr.*);
    }

    // Set to null
    maybe_ptr = null;
    try testing.expectEqual(@as(?*i32, null), maybe_ptr);
}

test "pointer to array vs slice" {
    var array = [_]i32{ 1, 2, 3, 4, 5 };

    // Pointer to array - knows the size in the type
    const array_ptr: *[5]i32 = &array;
    try testing.expectEqual(@as(usize, 5), array_ptr.len);

    // Slice - size known at runtime
    const slice: []i32 = &array;
    try testing.expectEqual(@as(usize, 5), slice.len);

    // Both access the same data
    array_ptr[0] = 99;
    try testing.expectEqual(@as(i32, 99), slice[0]);
}
// ANCHOR_END: when_to_use_pointers

// Additional examples

test "pointer arithmetic with many-item pointers" {
    var array = [_]i32{ 10, 20, 30, 40, 50 };

    const ptr: [*]i32 = &array;

    // Can do pointer arithmetic (like C)
    const offset_ptr = ptr + 2;
    try testing.expectEqual(@as(i32, 30), offset_ptr[0]);

    // But slices are safer and easier
    const slice: []i32 = array[2..];
    try testing.expectEqual(@as(i32, 30), slice[0]);
}

test "sentinel-terminated pointers" {
    // [*:0]u8 - many-item pointer terminated by 0 (for C strings)
    const c_string: [*:0]const u8 = "hello";

    // Can iterate until sentinel
    var len: usize = 0;
    while (c_string[len] != 0) : (len += 1) {}

    try testing.expectEqual(@as(usize, 5), len);

    // Better: use std.mem.span to convert to slice
    const slice = std.mem.span(c_string);
    try testing.expectEqual(@as(usize, 5), slice.len);
    try testing.expect(std.mem.eql(u8, slice, "hello"));
}

test "comparing pointers vs comparing values" {
    var x: i32 = 42;
    var y: i32 = 42;

    const ptr_x: *i32 = &x;
    const ptr_y: *i32 = &y;

    // Different pointers (different addresses)
    try testing.expect(ptr_x != ptr_y);

    // Same values
    try testing.expectEqual(ptr_x.*, ptr_y.*);

    // Pointer to same location
    const also_ptr_x: *i32 = &x;
    try testing.expect(ptr_x == also_ptr_x);
}

test "avoiding dangling pointers" {
    // Example of what NOT to do (would cause undefined behavior)
    _ = struct {
        fn call() *i32 {
            var x: i32 = 42;
            return &x; // BAD: x goes out of scope!
        }
    };

    // This would be undefined behavior:
    // const bad_ptr = getBadPointer();
    // const value = bad_ptr.*;  // Reading freed memory!

    // Instead, return the value or use an allocator
    const getGoodValue = struct {
        fn call() i32 {
            const x: i32 = 42;
            return x; // Good: return by value
        }
    }.call;

    const value = getGoodValue();
    try testing.expectEqual(@as(i32, 42), value);
}

// Summary:
// - *T: single-item pointer (points to one value)
// - [*]T: many-item pointer (no length, like C pointers)
// - []T: slice (pointer + length, safer and more common)
// - Use & to get address, .* to dereference
// - *const T vs *T: const vs mutable pointer
// - Pass by value for small structs, pointer for large ones
// - Use pointers when you need to modify or avoid copying
// - Slices are almost always better than many-item pointers
```

### See Also

- Recipe 0.6: Arrays, ArrayLists, and Slices
- Recipe 0.10: Structs, Enums, and Simple Data Models
- Recipe 0.12: Understanding Allocators

---

## Recipe 0.10: Structs, Enums, and Simple Data Models {#recipe-0-10}

**Tags:** comptime, error-handling, fundamentals, pointers, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_10.zig`

### Problem

You need to group related data and create custom types for your program. How do you define structs? How do enums work? What are tagged unions, and how do they differ from structs?

Coming from object-oriented languages, you might be looking for classes with inheritance. Zig takes a different approach focused on composition and explicit data modeling.

### Solution

Zig provides three main ways to create custom types:

1. **Structs** - Group related data with optional methods
2. **Enums** - Define a set of named constants
3. **Tagged Unions** - Store different types in the same variable (variant types)

These combine to create expressive data models without complex inheritance hierarchies.

### Discussion

### Part 1: Basic Structs

```zig
// Part 1: Basic Structs
//
// Structs group related data together

test "defining and using structs" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    // Create an instance
    const p1 = Point{ .x = 10, .y = 20 };

    try testing.expectEqual(@as(i32, 10), p1.x);
    try testing.expectEqual(@as(i32, 20), p1.y);

    // Mutable instance
    var p2 = Point{ .x = 5, .y = 15 };
    p2.x = 100;
    try testing.expectEqual(@as(i32, 100), p2.x);
}

test "struct with default field values" {
    const Config = struct {
        host: []const u8 = "localhost",
        port: u16 = 8080,
        debug: bool = false,
    };

    // Use defaults
    const config1 = Config{};
    try testing.expect(std.mem.eql(u8, config1.host, "localhost"));
    try testing.expectEqual(@as(u16, 8080), config1.port);
    try testing.expectEqual(false, config1.debug);

    // Override some defaults
    const config2 = Config{ .port = 3000, .debug = true };
    try testing.expect(std.mem.eql(u8, config2.host, "localhost"));
    try testing.expectEqual(@as(u16, 3000), config2.port);
    try testing.expectEqual(true, config2.debug);
}

test "struct methods" {
    const Rectangle = struct {
        width: i32,
        height: i32,

        fn area(self: @This()) i32 {
            return self.width * self.height;
        }

        fn perimeter(self: @This()) i32 {
            return 2 * (self.width + self.height);
        }

        fn scale(self: *@This(), factor: i32) void {
            self.width *= factor;
            self.height *= factor;
        }
    };

    var rect = Rectangle{ .width = 10, .height = 5 };

    try testing.expectEqual(@as(i32, 50), rect.area());
    try testing.expectEqual(@as(i32, 30), rect.perimeter());

    rect.scale(2);
    try testing.expectEqual(@as(i32, 20), rect.width);
    try testing.expectEqual(@as(i32, 10), rect.height);
}

test "constructor patterns" {
    const Person = struct {
        name: []const u8,
        age: u8,

        fn init(name: []const u8, age: u8) @This() {
            return .{
                .name = name,
                .age = age,
            };
        }

        fn describe(self: @This()) void {
            std.debug.print("{s} is {d} years old\n", .{ self.name, self.age });
        }
    };

    const person = Person.init("Alice", 30);
    try testing.expect(std.mem.eql(u8, person.name, "Alice"));
    try testing.expectEqual(@as(u8, 30), person.age);

    person.describe();
}
```

**Coming from OOP:** Zig doesn't have classes or inheritance. Structs are pure data with optional functions. There's no `this` keyword - you explicitly pass `self`.

### Part 2: Enums

```zig
// Part 2: Enums
//
// Enums define a set of named values

test "basic enums" {
    const Color = enum {
        red,
        green,
        blue,
    };

    const c1: Color = .red;
    const c2: Color = .green;

    try testing.expect(c1 == .red);
    try testing.expect(c2 == .green);
    try testing.expect(c1 != c2);
}

test "enums with explicit values" {
    const StatusCode = enum(u16) {
        ok = 200,
        not_found = 404,
        server_error = 500,
    };

    const code: StatusCode = .ok;

    // Convert to integer
    const value = @intFromEnum(code);
    try testing.expectEqual(@as(u16, 200), value);

    // Convert from integer
    const from_int = @as(StatusCode, @enumFromInt(404));
    try testing.expect(from_int == .not_found);
}

test "switch on enums" {
    const Direction = enum {
        north,
        south,
        east,
        west,
    };

    const dir: Direction = .north;

    const result = switch (dir) {
        .north => "Going up",
        .south => "Going down",
        .east => "Going right",
        .west => "Going left",
    };

    try testing.expect(std.mem.eql(u8, result, "Going up"));
}

test "enum methods" {
    const LogLevel = enum {
        debug,
        info,
        warning,
        err,

        fn toString(self: @This()) []const u8 {
            return switch (self) {
                .debug => "DEBUG",
                .info => "INFO",
                .warning => "WARNING",
                .err => "ERROR",
            };
        }

        fn isError(self: @This()) bool {
            return self == .err;
        }
    };

    const level: LogLevel = .warning;
    try testing.expect(std.mem.eql(u8, level.toString(), "WARNING"));
    try testing.expectEqual(false, level.isError());

    const error_level: LogLevel = .err;
    try testing.expectEqual(true, error_level.isError());
}
```

Enums can have methods like structs.

### Part 3: Tagged Unions - Variant Types

```zig
// Part 3: Tagged Unions - Variant Types
//
// Tagged unions let you store different types in the same variable

test "basic tagged unions" {
    const Value = union(enum) {
        int: i32,
        float: f32,
        boolean: bool,
    };

    // Create different variants
    const v1 = Value{ .int = 42 };
    const v2 = Value{ .float = 3.14 };
    const v3 = Value{ .boolean = true };

    // Access with switch
    switch (v1) {
        .int => |val| try testing.expectEqual(@as(i32, 42), val),
        .float => unreachable,
        .boolean => unreachable,
    }

    switch (v2) {
        .int => unreachable,
        .float => |val| try testing.expect(@abs(val - 3.14) < 0.01),
        .boolean => unreachable,
    }

    switch (v3) {
        .int => unreachable,
        .float => unreachable,
        .boolean => |val| try testing.expectEqual(true, val),
    }
}

test "tagged union with methods" {
    const Shape = union(enum) {
        circle: struct { radius: f32 },
        rectangle: struct { width: f32, height: f32 },
        triangle: struct { base: f32, height: f32 },

        fn area(self: @This()) f32 {
            return switch (self) {
                .circle => |c| std.math.pi * c.radius * c.radius,
                .rectangle => |r| r.width * r.height,
                .triangle => |t| 0.5 * t.base * t.height,
            };
        }
    };

    const circle = Shape{ .circle = .{ .radius = 5.0 } };
    const rect = Shape{ .rectangle = .{ .width = 10.0, .height = 5.0 } };
    const tri = Shape{ .triangle = .{ .base = 8.0, .height = 6.0 } };

    try testing.expect(@abs(circle.area() - 78.54) < 0.1);
    try testing.expect(@abs(rect.area() - 50.0) < 0.01);
    try testing.expect(@abs(tri.area() - 24.0) < 0.01);
}

test "tagged union pattern matching" {
    const Result = union(enum) {
        ok: i32,
        err: []const u8,

        fn isOk(self: @This()) bool {
            return switch (self) {
                .ok => true,
                .err => false,
            };
        }

        fn unwrap(self: @This()) !i32 {
            return switch (self) {
                .ok => |val| val,
                .err => |msg| {
                    std.debug.print("Error: {s}\n", .{msg});
                    return error.Failed;
                },
            };
        }
    };

    const success = Result{ .ok = 42 };
    try testing.expectEqual(true, success.isOk());
    const value = try success.unwrap();
    try testing.expectEqual(@as(i32, 42), value);

    const failure = Result{ .err = "Something went wrong" };
    try testing.expectEqual(false, failure.isOk());
    const err = failure.unwrap();
    try testing.expectError(error.Failed, err);
}
```

**Coming from TypeScript:** Tagged unions are like discriminated unions. The tag tells you which variant is active.

**Coming from Rust:** `union(enum)` is like Rust's `enum`. Zig calls it a tagged union because it combines a union with an enum tag.

### Public vs Private

Use `pub` to expose members outside the file:

```zig
test "public vs private members" {
    const Counter = struct {
        // Private field (default)
        count: i32 = 0,

        // Public function
        pub fn increment(self: *@This()) void {
            self.count += 1;
        }

        pub fn get(self: @This()) i32 {
            return self.count;
        }

        // Private function
        fn reset(self: *@This()) void {
            self.count = 0;
        }

        pub fn resetPublic(self: *@This()) void {
            self.reset();
        }
    };

    var counter = Counter{};
    counter.increment();
    try testing.expectEqual(@as(i32, 1), counter.get());
}
```

Without `pub`, members are private to the file. This provides encapsulation without access modifiers like `private`/`protected`/`public`.

### Nested Structs

Keep related types together:

```zig
test "nested structs" {
    const Company = struct {
        const Employee = struct {
            name: []const u8,
            salary: u32,
        };

        name: []const u8,
        employees: []const Employee,

        fn totalSalary(self: @This()) u32 {
            var total: u32 = 0;
            for (self.employees) |emp| {
                total += emp.salary;
            }
            return total;
        }
    };

    const employees = [_]Company.Employee{
        .{ .name = "Alice", .salary = 50000 },
        .{ .name = "Bob", .salary = 60000 },
    };

    const company = Company{
        .name = "Acme Corp",
        .employees = &employees,
    };

    try testing.expectEqual(@as(u32, 110000), company.totalSalary());
}
```

`Company.Employee` is a nested type, namespaced under `Company`.

### Putting It All Together

Here's a complete example combining structs, enums, and methods:

```zig
test "putting it all together" {
    const User = struct {
        const Role = enum {
            admin,
            moderator,
            user,

            fn canDelete(self: @This()) bool {
                return switch (self) {
                    .admin, .moderator => true,
                    .user => false,
                };
            }
        };

        id: u32,
        name: []const u8,
        role: Role,

        fn init(id: u32, name: []const u8, role: Role) @This() {
            return .{
                .id = id,
                .name = name,
                .role = role,
            };
        }

        fn describe(self: @This()) void {
            const role_str = switch (self.role) {
                .admin => "Admin",
                .moderator => "Moderator",
                .user => "User",
            };
            std.debug.print("User #{d}: {s} ({s})\n", .{ self.id, self.name, role_str });
        }
    };

    const admin = User.init(1, "Alice", .admin);
    const user = User.init(2, "Bob", .user);

    try testing.expectEqual(true, admin.role.canDelete());
    try testing.expectEqual(false, user.role.canDelete());
}
```

This pattern is idiomatic Zig: nested types, explicit initialization, methods that operate on data.

### Design Patterns

**Instead of inheritance, use composition:**
```zig
const Engine = struct { horsepower: u32 };
const Car = struct {
    engine: Engine,
    brand: []const u8
};
```

**Instead of interfaces, use function pointers or generic functions:**
```zig
fn processAny(comptime T: type, thing: T) void {
    thing.process(); // Works if T has a process() method
}
```

**Instead of null objects, use optionals:**
```zig
const maybe_user: ?User = null;
```

### Common Patterns

**Factory functions:**
```zig
fn create() @This() {
    return .{ .field = default_value };
}
```

**Builder pattern with default values:**
```zig
const Config = struct {
    host: []const u8 = "localhost",
    port: u16 = 8080,
};

const config = Config{ .port = 3000 }; // Override only what you need
```

**State machines with tagged unions:**
```zig
const State = union(enum) {
    idle,
    running: struct { progress: f32 },
    error: []const u8,
};
```

### Common Mistakes

**Forgetting field names:**
```zig
const p = Point{ 10, 20 };  // error
const p = Point{ .x = 10, .y = 20 };  // fixed
```

**Using wrong self parameter:**
```zig
fn modify(self: @This()) void {  // Can't modify - passed by value
    self.field = 10;  // error
}

fn modify(self: *@This()) void {  // Fixed - use pointer
    self.field = 10;
}
```

**Not handling all enum cases:**
```zig
switch (color) {
    .red => ...,
    .green => ...,
    // Missing .blue - compiler error!
}
```

**Accessing wrong union variant:**
```zig
const val = Value{ .int = 42 };
const f = val.float;  // Undefined behavior!

// Use switch instead:
switch (val) {
    .int => |i| ...,
    .float => |f| ...,
}
```

### Full Tested Code

```zig
// Recipe 0.10: Structs, Enums, and Simple Data Models
// Target Zig Version: 0.15.2
//
// This recipe covers creating custom types with structs, enums,
// and tagged unions for simple data modeling.

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_structs
// Part 1: Basic Structs
//
// Structs group related data together

test "defining and using structs" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    // Create an instance
    const p1 = Point{ .x = 10, .y = 20 };

    try testing.expectEqual(@as(i32, 10), p1.x);
    try testing.expectEqual(@as(i32, 20), p1.y);

    // Mutable instance
    var p2 = Point{ .x = 5, .y = 15 };
    p2.x = 100;
    try testing.expectEqual(@as(i32, 100), p2.x);
}

test "struct with default field values" {
    const Config = struct {
        host: []const u8 = "localhost",
        port: u16 = 8080,
        debug: bool = false,
    };

    // Use defaults
    const config1 = Config{};
    try testing.expect(std.mem.eql(u8, config1.host, "localhost"));
    try testing.expectEqual(@as(u16, 8080), config1.port);
    try testing.expectEqual(false, config1.debug);

    // Override some defaults
    const config2 = Config{ .port = 3000, .debug = true };
    try testing.expect(std.mem.eql(u8, config2.host, "localhost"));
    try testing.expectEqual(@as(u16, 3000), config2.port);
    try testing.expectEqual(true, config2.debug);
}

test "struct methods" {
    const Rectangle = struct {
        width: i32,
        height: i32,

        fn area(self: @This()) i32 {
            return self.width * self.height;
        }

        fn perimeter(self: @This()) i32 {
            return 2 * (self.width + self.height);
        }

        fn scale(self: *@This(), factor: i32) void {
            self.width *= factor;
            self.height *= factor;
        }
    };

    var rect = Rectangle{ .width = 10, .height = 5 };

    try testing.expectEqual(@as(i32, 50), rect.area());
    try testing.expectEqual(@as(i32, 30), rect.perimeter());

    rect.scale(2);
    try testing.expectEqual(@as(i32, 20), rect.width);
    try testing.expectEqual(@as(i32, 10), rect.height);
}

test "constructor patterns" {
    const Person = struct {
        name: []const u8,
        age: u8,

        fn init(name: []const u8, age: u8) @This() {
            return .{
                .name = name,
                .age = age,
            };
        }

        fn describe(self: @This()) void {
            std.debug.print("{s} is {d} years old\n", .{ self.name, self.age });
        }
    };

    const person = Person.init("Alice", 30);
    try testing.expect(std.mem.eql(u8, person.name, "Alice"));
    try testing.expectEqual(@as(u8, 30), person.age);

    person.describe();
}
// ANCHOR_END: basic_structs

// ANCHOR: enums
// Part 2: Enums
//
// Enums define a set of named values

test "basic enums" {
    const Color = enum {
        red,
        green,
        blue,
    };

    const c1: Color = .red;
    const c2: Color = .green;

    try testing.expect(c1 == .red);
    try testing.expect(c2 == .green);
    try testing.expect(c1 != c2);
}

test "enums with explicit values" {
    const StatusCode = enum(u16) {
        ok = 200,
        not_found = 404,
        server_error = 500,
    };

    const code: StatusCode = .ok;

    // Convert to integer
    const value = @intFromEnum(code);
    try testing.expectEqual(@as(u16, 200), value);

    // Convert from integer
    const from_int = @as(StatusCode, @enumFromInt(404));
    try testing.expect(from_int == .not_found);
}

test "switch on enums" {
    const Direction = enum {
        north,
        south,
        east,
        west,
    };

    const dir: Direction = .north;

    const result = switch (dir) {
        .north => "Going up",
        .south => "Going down",
        .east => "Going right",
        .west => "Going left",
    };

    try testing.expect(std.mem.eql(u8, result, "Going up"));
}

test "enum methods" {
    const LogLevel = enum {
        debug,
        info,
        warning,
        err,

        fn toString(self: @This()) []const u8 {
            return switch (self) {
                .debug => "DEBUG",
                .info => "INFO",
                .warning => "WARNING",
                .err => "ERROR",
            };
        }

        fn isError(self: @This()) bool {
            return self == .err;
        }
    };

    const level: LogLevel = .warning;
    try testing.expect(std.mem.eql(u8, level.toString(), "WARNING"));
    try testing.expectEqual(false, level.isError());

    const error_level: LogLevel = .err;
    try testing.expectEqual(true, error_level.isError());
}
// ANCHOR_END: enums

// ANCHOR: tagged_unions
// Part 3: Tagged Unions - Variant Types
//
// Tagged unions let you store different types in the same variable

test "basic tagged unions" {
    const Value = union(enum) {
        int: i32,
        float: f32,
        boolean: bool,
    };

    // Create different variants
    const v1 = Value{ .int = 42 };
    const v2 = Value{ .float = 3.14 };
    const v3 = Value{ .boolean = true };

    // Access with switch
    switch (v1) {
        .int => |val| try testing.expectEqual(@as(i32, 42), val),
        .float => unreachable,
        .boolean => unreachable,
    }

    switch (v2) {
        .int => unreachable,
        .float => |val| try testing.expect(@abs(val - 3.14) < 0.01),
        .boolean => unreachable,
    }

    switch (v3) {
        .int => unreachable,
        .float => unreachable,
        .boolean => |val| try testing.expectEqual(true, val),
    }
}

test "tagged union with methods" {
    const Shape = union(enum) {
        circle: struct { radius: f32 },
        rectangle: struct { width: f32, height: f32 },
        triangle: struct { base: f32, height: f32 },

        fn area(self: @This()) f32 {
            return switch (self) {
                .circle => |c| std.math.pi * c.radius * c.radius,
                .rectangle => |r| r.width * r.height,
                .triangle => |t| 0.5 * t.base * t.height,
            };
        }
    };

    const circle = Shape{ .circle = .{ .radius = 5.0 } };
    const rect = Shape{ .rectangle = .{ .width = 10.0, .height = 5.0 } };
    const tri = Shape{ .triangle = .{ .base = 8.0, .height = 6.0 } };

    try testing.expect(@abs(circle.area() - 78.54) < 0.1);
    try testing.expect(@abs(rect.area() - 50.0) < 0.01);
    try testing.expect(@abs(tri.area() - 24.0) < 0.01);
}

test "tagged union pattern matching" {
    const Result = union(enum) {
        ok: i32,
        err: []const u8,

        fn isOk(self: @This()) bool {
            return switch (self) {
                .ok => true,
                .err => false,
            };
        }

        fn unwrap(self: @This()) !i32 {
            return switch (self) {
                .ok => |val| val,
                .err => |msg| {
                    std.debug.print("Error: {s}\n", .{msg});
                    return error.Failed;
                },
            };
        }
    };

    const success = Result{ .ok = 42 };
    try testing.expectEqual(true, success.isOk());
    const value = try success.unwrap();
    try testing.expectEqual(@as(i32, 42), value);

    const failure = Result{ .err = "Something went wrong" };
    try testing.expectEqual(false, failure.isOk());
    const err = failure.unwrap();
    try testing.expectError(error.Failed, err);
}
// ANCHOR_END: tagged_unions

// Public vs Private

test "public vs private members" {
    const Counter = struct {
        // Private field (default)
        count: i32 = 0,

        // Public function
        pub fn increment(self: *@This()) void {
            self.count += 1;
        }

        pub fn get(self: @This()) i32 {
            return self.count;
        }

        // Private function
        fn reset(self: *@This()) void {
            self.count = 0;
        }

        pub fn resetPublic(self: *@This()) void {
            self.reset();
        }
    };

    var counter = Counter{};
    counter.increment();
    try testing.expectEqual(@as(i32, 1), counter.get());

    counter.resetPublic();
    try testing.expectEqual(@as(i32, 0), counter.get());
}

// Nested structs

test "nested structs" {
    const Company = struct {
        const Employee = struct {
            name: []const u8,
            salary: u32,
        };

        name: []const u8,
        employees: []const Employee,

        fn totalSalary(self: @This()) u32 {
            var total: u32 = 0;
            for (self.employees) |emp| {
                total += emp.salary;
            }
            return total;
        }
    };

    const employees = [_]Company.Employee{
        .{ .name = "Alice", .salary = 50000 },
        .{ .name = "Bob", .salary = 60000 },
    };

    const company = Company{
        .name = "Acme Corp",
        .employees = &employees,
    };

    try testing.expectEqual(@as(u32, 110000), company.totalSalary());
}

// Complete example

test "putting it all together" {
    const User = struct {
        const Role = enum {
            admin,
            moderator,
            user,

            fn canDelete(self: @This()) bool {
                return switch (self) {
                    .admin, .moderator => true,
                    .user => false,
                };
            }
        };

        id: u32,
        name: []const u8,
        role: Role,

        fn init(id: u32, name: []const u8, role: Role) @This() {
            return .{
                .id = id,
                .name = name,
                .role = role,
            };
        }

        fn describe(self: @This()) void {
            const role_str = switch (self.role) {
                .admin => "Admin",
                .moderator => "Moderator",
                .user => "User",
            };
            std.debug.print("User #{d}: {s} ({s})\n", .{ self.id, self.name, role_str });
        }
    };

    const admin = User.init(1, "Alice", .admin);
    const user = User.init(2, "Bob", .user);

    try testing.expectEqual(true, admin.role.canDelete());
    try testing.expectEqual(false, user.role.canDelete());

    admin.describe();
    user.describe();
}

// Summary:
// - Structs group related data with optional default values
// - Methods use `self: @This()` or `self: *@This()` for modification
// - Enums define a set of named constants
// - Tagged unions (union(enum)) store different types
// - Use switch to handle tagged union variants
// - `pub` makes members visible outside the file
// - Nested types keep related definitions together
```

### See Also

- Recipe 0.9: Understanding Pointers
- Recipe 0.7: Functions and Standard Library
- Recipe 2.13: Creating Data Processing Pipelines

---

## Recipe 0.11: Optionals, Errors, and Resource Cleanup {#recipe-0-11}

**Tags:** allocators, arraylist, data-structures, error-handling, fundamentals, memory, pointers, resource-cleanup, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_11.zig`

### Problem

You need to handle values that might be null, operations that might fail, and resources that need cleanup. How do you represent optional values? How do you handle errors without exceptions? How do you ensure cleanup code runs even when errors occur?

Coming from languages with null pointers and exceptions, Zig's approach is different but safer.

### Solution

Zig provides three powerful features for safe programming:

1. **Optionals `?T`** - Explicitly mark values that might be null
2. **Error unions `!T`** - Return errors as values, not exceptions
3. **defer/errdefer** - Automatic cleanup when scope exits

These eliminate entire classes of bugs: null pointer dereferences, unchecked exceptions, and resource leaks.

### Discussion

### Part 1: Optionals (?T)

```zig
// Part 1: Optionals (?T)
//
// Optionals represent values that might be null

test "basic optionals" {
    // ?T means "optional T" - can be a value or null
    var maybe_num: ?i32 = 42;
    try testing.expect(maybe_num != null);

    // Set to null
    maybe_num = null;
    try testing.expect(maybe_num == null);

    // Create optional with value
    const some_value: ?i32 = 100;
    try testing.expect(some_value != null);
}

test "unwrapping optionals with if" {
    const maybe_value: ?i32 = 42;

    // Unwrap with if - safe way to access the value
    if (maybe_value) |value| {
        try testing.expectEqual(@as(i32, 42), value);
    } else {
        try testing.expect(false); // Won't run
    }

    // Null case
    const no_value: ?i32 = null;
    if (no_value) |_| {
        try testing.expect(false); // Won't run
    } else {
        try testing.expect(true); // This runs
    }
}

test "unwrapping with orelse" {
    const maybe_value: ?i32 = 42;

    // Use orelse to provide a default
    const value1 = maybe_value orelse 0;
    try testing.expectEqual(@as(i32, 42), value1);

    const no_value: ?i32 = null;
    const value2 = no_value orelse 100;
    try testing.expectEqual(@as(i32, 100), value2);
}

test "optional pointers" {
    var x: i32 = 42;
    var ptr: ?*i32 = &x;

    // Unwrap optional pointer
    if (ptr) |p| {
        try testing.expectEqual(@as(i32, 42), p.*);
    }

    ptr = null;
    try testing.expect(ptr == null);
}

fn findInArray(arr: []const i32, target: i32) ?usize {
    for (arr, 0..) |val, i| {
        if (val == target) return i;
    }
    return null;
}

test "functions returning optionals" {
    const numbers = [_]i32{ 10, 20, 30, 40, 50 };

    const index1 = findInArray(&numbers, 30);
    try testing.expect(index1 != null);
    try testing.expectEqual(@as(usize, 2), index1.?);

    const index2 = findInArray(&numbers, 99);
    try testing.expect(index2 == null);
}
```

**Coming from Java/C++:** `?T` is like `Optional<T>` or `std::optional<T>`, but built into the language. Unlike C/C++ pointers, you can't accidentally dereference null.

### Part 2: Error Unions (!T)

```zig
// Part 2: Error Unions (!T)
//
// Error unions represent operations that can fail

test "basic error unions" {
    // !T means "error union T" - can be a value or an error
    const success: anyerror!i32 = 42;
    const failure: anyerror!i32 = error.Failed;

    // Check for errors
    if (success) |val| {
        try testing.expectEqual(@as(i32, 42), val);
    } else |_| {
        try testing.expect(false);
    }

    if (failure) |_| {
        try testing.expect(false);
    } else |err| {
        try testing.expectEqual(error.Failed, err);
    }
}

const MathError = error{
    DivisionByZero,
    Overflow,
};

fn divide(a: i32, b: i32) MathError!i32 {
    if (b == 0) return error.DivisionByZero;
    if (a == std.math.minInt(i32) and b == -1) return error.Overflow;
    return @divTrunc(a, b);
}

test "custom error sets" {
    const result1 = try divide(10, 2);
    try testing.expectEqual(@as(i32, 5), result1);

    const result2 = divide(10, 0);
    try testing.expectError(error.DivisionByZero, result2);

    const result3 = divide(std.math.minInt(i32), -1);
    try testing.expectError(error.Overflow, result3);
}

test "propagating errors with try" {
    const safeDivide = struct {
        fn call(a: i32, b: i32) MathError!i32 {
            // try propagates the error up
            const result = try divide(a, b);
            return result * 2;
        }
    }.call;

    const result1 = try safeDivide(10, 2);
    try testing.expectEqual(@as(i32, 10), result1);

    const result2 = safeDivide(10, 0);
    try testing.expectError(error.DivisionByZero, result2);
}

test "handling errors with catch" {
    const divideOrZero = struct {
        fn call(a: i32, b: i32) i32 {
            return divide(a, b) catch 0;
        }
    }.call;

    const result1 = divideOrZero(10, 2);
    try testing.expectEqual(@as(i32, 5), result1);

    const result2 = divideOrZero(10, 0);
    try testing.expectEqual(@as(i32, 0), result2);
}

test "catch with error value" {
    const handleError = struct {
        fn call(a: i32, b: i32) i32 {
            return divide(a, b) catch |err| {
                std.debug.print("Error occurred: {}\n", .{err});
                return -1;
            };
        }
    }.call;

    const result = handleError(10, 0);
    try testing.expectEqual(@as(i32, -1), result);
}
```

**Coming from Java/Python:** Errors are return values, not exceptions. There's no try/catch blocks or stack unwinding. Error handling is explicit and visible in the code.

### Part 3: Resource Cleanup with defer and errdefer

```zig
// Part 3: Resource Cleanup with defer and errdefer
//
// defer runs when scope exits, errdefer runs only on error

test "basic defer" {
    var counter: i32 = 0;

    {
        defer counter += 1;
        try testing.expectEqual(@as(i32, 0), counter);
    } // defer runs here

    try testing.expectEqual(@as(i32, 1), counter);
}

test "multiple defers run in reverse order" {
    var counter: i32 = 0;

    {
        defer counter += 1; // Runs third (last)
        defer counter += 10; // Runs second
        defer counter += 100; // Runs first

        try testing.expectEqual(@as(i32, 0), counter);
    } // defers run in reverse order: 100, then 10, then 1

    try testing.expectEqual(@as(i32, 111), counter);
}

fn allocateResource(allocator: std.mem.Allocator) ![]u8 {
    const data = try allocator.alloc(u8, 100);
    errdefer allocator.free(data); // Only runs if error occurs after this point

    // Simulate initialization that might fail
    if (data.len < 50) return error.TooSmall; // Won't happen, but demonstrates errdefer

    return data;
}

test "defer for resource cleanup" {
    const data = try allocateResource(testing.allocator);
    defer testing.allocator.free(data);

    // Use data
    try testing.expectEqual(@as(usize, 100), data.len);
}

fn createList(allocator: std.mem.Allocator, fail: bool) !std.ArrayList(i32) {
    var list = std.ArrayList(i32){};
    errdefer list.deinit(allocator); // Clean up if initialization fails

    try list.append(allocator, 1);
    try list.append(allocator, 2);

    if (fail) {
        return error.InitFailed; // errdefer will run
    }

    return list; // errdefer won't run
}

test "errdefer for error cleanup" {
    // Success case - errdefer doesn't run
    var list1 = try createList(testing.allocator, false);
    defer list1.deinit(testing.allocator);
    try testing.expectEqual(@as(usize, 2), list1.items.len);

    // Error case - errdefer runs and cleans up
    const result = createList(testing.allocator, true);
    try testing.expectError(error.InitFailed, result);
    // If errdefer didn't run, we'd have a memory leak
}

test "defer vs errdefer" {
    var regular_cleanup = false;
    var error_cleanup = false;

    const testFunc = struct {
        fn call(should_fail: bool, reg: *bool, err_clean: *bool) !void {
            defer reg.* = true; // Always runs
            errdefer err_clean.* = true; // Only runs on error

            if (should_fail) {
                return error.Failed;
            }
        }
    }.call;

    // Success case
    try testFunc(false, &regular_cleanup, &error_cleanup);
    try testing.expectEqual(true, regular_cleanup);
    try testing.expectEqual(false, error_cleanup);

    // Reset
    regular_cleanup = false;
    error_cleanup = false;

    // Error case
    const result = testFunc(true, &regular_cleanup, &error_cleanup);
    try testing.expectError(error.Failed, result);
    try testing.expectEqual(true, regular_cleanup); // defer ran
    try testing.expectEqual(true, error_cleanup); // errdefer also ran
}

fn initializeResource(allocator: std.mem.Allocator, stage: u8) !*std.ArrayList(i32) {
    const list = try allocator.create(std.ArrayList(i32));
    errdefer allocator.destroy(list);

    list.* = std.ArrayList(i32){};
    errdefer list.deinit(allocator);

    try list.append(allocator, 1);

    if (stage == 1) return error.StageFailed;

    try list.append(allocator, 2);

    if (stage == 2) return error.StageFailed;

    return list;
}

test "multiple errdefers for staged cleanup" {
    // Success
    const resource = try initializeResource(testing.allocator, 0);
    defer {
        resource.deinit(testing.allocator);
        testing.allocator.destroy(resource);
    }
    try testing.expectEqual(@as(usize, 2), resource.items.len);

    // Fail at stage 1 - both errdefers run
    const result1 = initializeResource(testing.allocator, 1);
    try testing.expectError(error.StageFailed, result1);

    // Fail at stage 2 - both errdefers run
    const result2 = initializeResource(testing.allocator, 2);
    try testing.expectError(error.StageFailed, result2);
}
```

Each `errdefer` handles cleanup for what was allocated before it. If initialization fails at any stage, all relevant cleanup runs.

### Combining Optionals and Errors

Sometimes you need both:

```zig
test "optional error unions" {
    const parseNumber = struct {
        fn call(str: []const u8) !?i32 {
            if (str.len == 0) return null;
            if (str[0] == 'x') return error.InvalidFormat;
            return 42;
        }
    }.call;

    // Success
    const result1 = try parseNumber("123");
    try testing.expectEqual(@as(?i32, 42), result1);

    // Null (not an error)
    const result2 = try parseNumber("");
    try testing.expectEqual(@as(?i32, null), result2);

    // Error
    const result3 = parseNumber("x");
    try testing.expectError(error.InvalidFormat, result3);
}
```

The type `!?T` means "either an error, or an optional T". This distinguishes:
- Success with value
- Success with no value (null)
- Failure (error)

### Practical Example

Here's a complete example combining all three features:

```zig
test "practical example: safe file operations" {
    const FileOps = struct {
        fn open(name: []const u8) !?*u32 {
            if (std.mem.eql(u8, name, "")) return null;
            if (std.mem.eql(u8, name, "bad")) return error.AccessDenied;

            const handle = try testing.allocator.create(u32);
            handle.* = 42;
            return handle;
        }

        fn close(handle: *u32, allocator: std.mem.Allocator) void {
            allocator.destroy(handle);
        }
    };

    // Successful open and close
    if (try FileOps.open("good.txt")) |handle| {
        defer FileOps.close(handle, testing.allocator);
        try testing.expectEqual(@as(u32, 42), handle.*);
    }

    // File doesn't exist (null, not error)
    const no_file = try FileOps.open("");
    try testing.expectEqual(@as(?*u32, null), no_file);

    // Access denied (error)
    const denied = FileOps.open("bad");
    try testing.expectError(error.AccessDenied, denied);
}
```

This pattern ensures:
- Resources are always cleaned up (defer)
- Errors are explicit and handled
- Null is distinct from error

### Decision Tree

**Should I use optional or error?**
- Value might not exist (but that's OK) → Use `?T`
- Operation might fail (that's an error) → Use `!T`
- Both possible → Use `!?T`

**Should I use defer or errdefer?**
- Cleanup always needed → Use `defer`
- Cleanup only on error → Use `errdefer`
- Both needed → Use both!

### Common Patterns

**Resource acquisition:**
```zig
const resource = try allocate();
defer free(resource);
```

**Error path cleanup:**
```zig
var resource = try init();
errdefer deinit(resource);
```

**Unwrapping with default:**
```zig
const value = optional orelse default_value;
const value = try_operation() catch default_value;
```

### Common Mistakes

**Forgetting defer:**
```zig
const data = try allocator.alloc(u8, 100);
// ... use data ...
// Memory leak! Need: defer allocator.free(data);
```

**Using .? on null:**
```zig
const maybe: ?i32 = null;
const value = maybe.?;  // Panic! Use if (maybe) |val| instead
```

**Not handling all error cases:**
```zig
const result = try riskyOperation();
// If riskyOperation returns error, function exits here
// Use catch if you want to handle it
```

**Wrong order of defer/errdefer:**
```zig
errdefer allocator.free(data);
const data = try allocator.alloc(u8, 100);  // Wrong! errdefer runs before allocation
```

Fix: Put errdefer after the allocation.

### Full Tested Code

```zig
// Recipe 0.11: Optionals, Errors, and Resource Cleanup (EXPANDED)
// Target Zig Version: 0.15.2
//
// This recipe covers optionals (?T), error unions (!T), and resource cleanup
// with defer and errdefer.

const std = @import("std");
const testing = std.testing;

// ANCHOR: optionals
// Part 1: Optionals (?T)
//
// Optionals represent values that might be null

test "basic optionals" {
    // ?T means "optional T" - can be a value or null
    var maybe_num: ?i32 = 42;
    try testing.expect(maybe_num != null);

    // Set to null
    maybe_num = null;
    try testing.expect(maybe_num == null);

    // Create optional with value
    const some_value: ?i32 = 100;
    try testing.expect(some_value != null);
}

test "unwrapping optionals with if" {
    const maybe_value: ?i32 = 42;

    // Unwrap with if - safe way to access the value
    if (maybe_value) |value| {
        try testing.expectEqual(@as(i32, 42), value);
    } else {
        try testing.expect(false); // Won't run
    }

    // Null case
    const no_value: ?i32 = null;
    if (no_value) |_| {
        try testing.expect(false); // Won't run
    } else {
        try testing.expect(true); // This runs
    }
}

test "unwrapping with orelse" {
    const maybe_value: ?i32 = 42;

    // Use orelse to provide a default
    const value1 = maybe_value orelse 0;
    try testing.expectEqual(@as(i32, 42), value1);

    const no_value: ?i32 = null;
    const value2 = no_value orelse 100;
    try testing.expectEqual(@as(i32, 100), value2);
}

test "optional pointers" {
    var x: i32 = 42;
    var ptr: ?*i32 = &x;

    // Unwrap optional pointer
    if (ptr) |p| {
        try testing.expectEqual(@as(i32, 42), p.*);
    }

    ptr = null;
    try testing.expect(ptr == null);
}

fn findInArray(arr: []const i32, target: i32) ?usize {
    for (arr, 0..) |val, i| {
        if (val == target) return i;
    }
    return null;
}

test "functions returning optionals" {
    const numbers = [_]i32{ 10, 20, 30, 40, 50 };

    const index1 = findInArray(&numbers, 30);
    try testing.expect(index1 != null);
    try testing.expectEqual(@as(usize, 2), index1.?);

    const index2 = findInArray(&numbers, 99);
    try testing.expect(index2 == null);
}
// ANCHOR_END: optionals

// ANCHOR: error_unions
// Part 2: Error Unions (!T)
//
// Error unions represent operations that can fail

test "basic error unions" {
    // !T means "error union T" - can be a value or an error
    const success: anyerror!i32 = 42;
    const failure: anyerror!i32 = error.Failed;

    // Check for errors
    if (success) |val| {
        try testing.expectEqual(@as(i32, 42), val);
    } else |_| {
        try testing.expect(false);
    }

    if (failure) |_| {
        try testing.expect(false);
    } else |err| {
        try testing.expectEqual(error.Failed, err);
    }
}

const MathError = error{
    DivisionByZero,
    Overflow,
};

fn divide(a: i32, b: i32) MathError!i32 {
    if (b == 0) return error.DivisionByZero;
    if (a == std.math.minInt(i32) and b == -1) return error.Overflow;
    return @divTrunc(a, b);
}

test "custom error sets" {
    const result1 = try divide(10, 2);
    try testing.expectEqual(@as(i32, 5), result1);

    const result2 = divide(10, 0);
    try testing.expectError(error.DivisionByZero, result2);

    const result3 = divide(std.math.minInt(i32), -1);
    try testing.expectError(error.Overflow, result3);
}

test "propagating errors with try" {
    const safeDivide = struct {
        fn call(a: i32, b: i32) MathError!i32 {
            // try propagates the error up
            const result = try divide(a, b);
            return result * 2;
        }
    }.call;

    const result1 = try safeDivide(10, 2);
    try testing.expectEqual(@as(i32, 10), result1);

    const result2 = safeDivide(10, 0);
    try testing.expectError(error.DivisionByZero, result2);
}

test "handling errors with catch" {
    const divideOrZero = struct {
        fn call(a: i32, b: i32) i32 {
            return divide(a, b) catch 0;
        }
    }.call;

    const result1 = divideOrZero(10, 2);
    try testing.expectEqual(@as(i32, 5), result1);

    const result2 = divideOrZero(10, 0);
    try testing.expectEqual(@as(i32, 0), result2);
}

test "catch with error value" {
    const handleError = struct {
        fn call(a: i32, b: i32) i32 {
            return divide(a, b) catch |err| {
                std.debug.print("Error occurred: {}\n", .{err});
                return -1;
            };
        }
    }.call;

    const result = handleError(10, 0);
    try testing.expectEqual(@as(i32, -1), result);
}
// ANCHOR_END: error_unions

// ANCHOR: defer_errdefer
// Part 3: Resource Cleanup with defer and errdefer
//
// defer runs when scope exits, errdefer runs only on error

test "basic defer" {
    var counter: i32 = 0;

    {
        defer counter += 1;
        try testing.expectEqual(@as(i32, 0), counter);
    } // defer runs here

    try testing.expectEqual(@as(i32, 1), counter);
}

test "multiple defers run in reverse order" {
    var counter: i32 = 0;

    {
        defer counter += 1; // Runs third (last)
        defer counter += 10; // Runs second
        defer counter += 100; // Runs first

        try testing.expectEqual(@as(i32, 0), counter);
    } // defers run in reverse order: 100, then 10, then 1

    try testing.expectEqual(@as(i32, 111), counter);
}

fn allocateResource(allocator: std.mem.Allocator) ![]u8 {
    const data = try allocator.alloc(u8, 100);
    errdefer allocator.free(data); // Only runs if error occurs after this point

    // Simulate initialization that might fail
    if (data.len < 50) return error.TooSmall; // Won't happen, but demonstrates errdefer

    return data;
}

test "defer for resource cleanup" {
    const data = try allocateResource(testing.allocator);
    defer testing.allocator.free(data);

    // Use data
    try testing.expectEqual(@as(usize, 100), data.len);
}

fn createList(allocator: std.mem.Allocator, fail: bool) !std.ArrayList(i32) {
    var list = std.ArrayList(i32){};
    errdefer list.deinit(allocator); // Clean up if initialization fails

    try list.append(allocator, 1);
    try list.append(allocator, 2);

    if (fail) {
        return error.InitFailed; // errdefer will run
    }

    return list; // errdefer won't run
}

test "errdefer for error cleanup" {
    // Success case - errdefer doesn't run
    var list1 = try createList(testing.allocator, false);
    defer list1.deinit(testing.allocator);
    try testing.expectEqual(@as(usize, 2), list1.items.len);

    // Error case - errdefer runs and cleans up
    const result = createList(testing.allocator, true);
    try testing.expectError(error.InitFailed, result);
    // If errdefer didn't run, we'd have a memory leak
}

test "defer vs errdefer" {
    var regular_cleanup = false;
    var error_cleanup = false;

    const testFunc = struct {
        fn call(should_fail: bool, reg: *bool, err_clean: *bool) !void {
            defer reg.* = true; // Always runs
            errdefer err_clean.* = true; // Only runs on error

            if (should_fail) {
                return error.Failed;
            }
        }
    }.call;

    // Success case
    try testFunc(false, &regular_cleanup, &error_cleanup);
    try testing.expectEqual(true, regular_cleanup);
    try testing.expectEqual(false, error_cleanup);

    // Reset
    regular_cleanup = false;
    error_cleanup = false;

    // Error case
    const result = testFunc(true, &regular_cleanup, &error_cleanup);
    try testing.expectError(error.Failed, result);
    try testing.expectEqual(true, regular_cleanup); // defer ran
    try testing.expectEqual(true, error_cleanup); // errdefer also ran
}

fn initializeResource(allocator: std.mem.Allocator, stage: u8) !*std.ArrayList(i32) {
    const list = try allocator.create(std.ArrayList(i32));
    errdefer allocator.destroy(list);

    list.* = std.ArrayList(i32){};
    errdefer list.deinit(allocator);

    try list.append(allocator, 1);

    if (stage == 1) return error.StageFailed;

    try list.append(allocator, 2);

    if (stage == 2) return error.StageFailed;

    return list;
}

test "multiple errdefers for staged cleanup" {
    // Success
    const resource = try initializeResource(testing.allocator, 0);
    defer {
        resource.deinit(testing.allocator);
        testing.allocator.destroy(resource);
    }
    try testing.expectEqual(@as(usize, 2), resource.items.len);

    // Fail at stage 1 - both errdefers run
    const result1 = initializeResource(testing.allocator, 1);
    try testing.expectError(error.StageFailed, result1);

    // Fail at stage 2 - both errdefers run
    const result2 = initializeResource(testing.allocator, 2);
    try testing.expectError(error.StageFailed, result2);
}
// ANCHOR_END: defer_errdefer

// Combining optionals and errors

test "optional error unions" {
    const parseNumber = struct {
        fn call(str: []const u8) !?i32 {
            if (str.len == 0) return null;
            if (str[0] == 'x') return error.InvalidFormat;
            return 42;
        }
    }.call;

    // Success
    const result1 = try parseNumber("123");
    try testing.expectEqual(@as(?i32, 42), result1);

    // Null (not an error)
    const result2 = try parseNumber("");
    try testing.expectEqual(@as(?i32, null), result2);

    // Error
    const result3 = parseNumber("x");
    try testing.expectError(error.InvalidFormat, result3);
}

test "practical example: safe file operations" {
    // Simulate file operations with error handling
    const FileOps = struct {
        fn open(name: []const u8) !?*u32 {
            if (std.mem.eql(u8, name, "")) return null;
            if (std.mem.eql(u8, name, "bad")) return error.AccessDenied;

            const handle = try testing.allocator.create(u32);
            handle.* = 42;
            return handle;
        }

        fn close(handle: *u32, allocator: std.mem.Allocator) void {
            allocator.destroy(handle);
        }
    };

    // Successful open and close
    if (try FileOps.open("good.txt")) |handle| {
        defer FileOps.close(handle, testing.allocator);
        try testing.expectEqual(@as(u32, 42), handle.*);
    }

    // File doesn't exist (null, not error)
    const no_file = try FileOps.open("");
    try testing.expectEqual(@as(?*u32, null), no_file);

    // Access denied (error)
    const denied = FileOps.open("bad");
    try testing.expectError(error.AccessDenied, denied);
}

// Summary:
// - ?T: optional values (can be null)
// - !T: error unions (can be error or value)
// - Use if (val) |v| to unwrap optionals
// - Use if (val) |v| else |err| to unwrap errors
// - Use orelse for optional defaults
// - Use catch for error defaults
// - defer: always runs when scope exits
// - errdefer: only runs when scope exits due to error
// - Use errdefer for resource cleanup in error paths
```

### See Also

- Recipe 0.12: Understanding Allocators
- Recipe 0.7: Functions and Standard Library
- Recipe 0.13: Testing and Debugging

---

## Recipe 0.12: Understanding Allocators {#recipe-0-12}

**Tags:** allocators, arena-allocator, arraylist, data-structures, error-handling, fundamentals, hashmap, memory, resource-cleanup, slices, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_12.zig`

### Problem

You're coming from Python, JavaScript, or Java where memory allocation is automatic and invisible. In Zig, there's no `new` keyword, no `malloc()` function you can call directly, and no default allocator.

How do you allocate memory? What's an `Allocator` parameter? Why do ArrayList and HashMap need an allocator argument? This is uniquely Zig and must be understood before writing any real code.

### Solution

Zig requires **explicit memory allocation** - you must choose where memory comes from:

1. **No default allocator** - Functions that allocate memory take an `Allocator` parameter
2. **Allocator interface** - All allocators implement `std.mem.Allocator`
3. **Different allocators for different use cases** - Choose based on lifetime and performance needs

Common allocators:
- `FixedBufferAllocator` - Stack memory, no malloc
- `GeneralPurposeAllocator` - Safe malloc with leak detection
- `ArenaAllocator` - Batch allocate, free all at once
- `testing.allocator` - For tests, detects leaks automatically

This explicit approach eliminates hidden allocations and makes memory usage predictable.

### Discussion

### Part 1: Why Zig Needs Allocators

```zig
// Part 1: Why Zig Needs Allocators
//
// Unlike Python/Java/JavaScript, Zig has NO default allocator
// You must explicitly choose where memory comes from

test "no default allocator" {
    // This would NOT compile in Zig:
    // var list = std.ArrayList(i32).init();  // error: missing allocator parameter

    // You MUST provide an allocator:
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    try list.append(testing.allocator, 1);
    try list.append(testing.allocator, 2);

    try testing.expectEqual(@as(usize, 2), list.items.len);
}

test "allocator interface" {
    // std.mem.Allocator is an interface
    // All allocators implement the same interface:
    // - alloc(T, n) - allocate n items of type T
    // - free(memory) - free memory
    // - create(T) - allocate one T
    // - destroy(T) - free one T

    const allocator = testing.allocator;

    // Allocate a slice of 10 integers
    const numbers = try allocator.alloc(i32, 10);
    defer allocator.free(numbers);

    numbers[0] = 42;
    try testing.expectEqual(@as(i32, 42), numbers[0]);
    try testing.expectEqual(@as(usize, 10), numbers.len);

    // Allocate a single struct
    const Point = struct {
        x: i32,
        y: i32,
    };

    const point = try allocator.create(Point);
    defer allocator.destroy(point);

    point.* = .{ .x = 10, .y = 20 };
    try testing.expectEqual(@as(i32, 10), point.x);
}
```

**Coming from C:** Zig's allocators are like passing a custom `malloc`/`free` implementation, but type-safe and standardized.

**Coming from Java/Python:** Every `new` or `[]` allocation you write in those languages is hidden. Zig makes it explicit so you know exactly when and where memory is allocated.

### Part 2: Common Allocator Types

```zig
// Part 2: Common Allocator Types
//
// Zig provides several allocators for different use cases

test "FixedBufferAllocator - stack memory" {
    // Fixed buffer - uses stack memory, no malloc
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // Allocate from the fixed buffer
    const numbers = try allocator.alloc(i32, 10);
    // No free needed - buffer is on stack

    numbers[0] = 100;
    try testing.expectEqual(@as(i32, 100), numbers[0]);

    // If you run out of buffer space, alloc returns error.OutOfMemory
    const result = allocator.alloc(i32, 1000);
    try testing.expectError(error.OutOfMemory, result);
}

test "GeneralPurposeAllocator - safe malloc" {
    // GPA is like malloc but with leak detection
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }

    const allocator = gpa.allocator();

    // Allocate on heap
    const numbers = try allocator.alloc(i32, 100);
    defer allocator.free(numbers);

    numbers[50] = 42;
    try testing.expectEqual(@as(i32, 42), numbers[50]);

    // GPA checks for leaks when deinit() is called
}

test "ArenaAllocator - batch cleanup" {
    // Arena allocates many items, frees all at once
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit(); // Frees ALL allocations

    const allocator = arena.allocator();

    // Allocate many things
    const slice1 = try allocator.alloc(i32, 10);
    const slice2 = try allocator.alloc(i32, 20);
    const slice3 = try allocator.alloc(i32, 30);

    // No individual free calls needed!
    slice1[0] = 1;
    slice2[0] = 2;
    slice3[0] = 3;

    try testing.expectEqual(@as(i32, 1), slice1[0]);
    try testing.expectEqual(@as(i32, 2), slice2[0]);
    try testing.expectEqual(@as(i32, 3), slice3[0]);

    // arena.deinit() frees everything at once
}

test "testing.allocator - for tests" {
    // testing.allocator is a GPA configured for testing
    // It detects memory leaks automatically

    const allocator = testing.allocator;

    const numbers = try allocator.alloc(i32, 50);
    defer allocator.free(numbers);

    // If you forget the defer, test will fail with leak detection
    numbers[0] = 99;
    try testing.expectEqual(@as(i32, 99), numbers[0]);
}
```

Always use `testing.allocator` in tests - it automatically detects and reports memory leaks.

### Part 3: Common Allocator Patterns

```zig
// Part 3: Common Allocator Patterns
//
// How to use allocators in real code

test "passing allocators to functions" {
    // Convention: allocator is first parameter
    const createList = struct {
        fn call(allocator: std.mem.Allocator, size: usize) ![]i32 {
            const list = try allocator.alloc(i32, size);
            for (list, 0..) |*item, i| {
                item.* = @intCast(i);
            }
            return list;
        }
    }.call;

    const list = try createList(testing.allocator, 5);
    defer testing.allocator.free(list);

    try testing.expectEqual(@as(i32, 0), list[0]);
    try testing.expectEqual(@as(i32, 4), list[4]);
}

test "struct with allocator field" {
    // Structs that allocate keep a reference to allocator
    const Buffer = struct {
        data: []u8,
        allocator: std.mem.Allocator,

        fn init(allocator: std.mem.Allocator, size: usize) !@This() {
            const data = try allocator.alloc(u8, size);
            return .{
                .data = data,
                .allocator = allocator,
            };
        }

        fn deinit(self: *@This()) void {
            self.allocator.free(self.data);
        }
    };

    var buffer = try Buffer.init(testing.allocator, 100);
    defer buffer.deinit();

    buffer.data[0] = 42;
    try testing.expectEqual(@as(u8, 42), buffer.data[0]);
}

test "arena for temporary allocations" {
    // Use arena for request-scoped lifetimes
    const processRequest = struct {
        fn call(parent_allocator: std.mem.Allocator) !i32 {
            var arena = std.heap.ArenaAllocator.init(parent_allocator);
            defer arena.deinit(); // Cleanup all at end

            const allocator = arena.allocator();

            // Allocate many temporary things
            const temp1 = try allocator.alloc(i32, 10);
            const temp2 = try allocator.alloc(i32, 20);

            // Do work...
            temp1[0] = 10;
            temp2[0] = 20;

            return temp1[0] + temp2[0];
        }
    }.call;

    const result = try processRequest(testing.allocator);
    try testing.expectEqual(@as(i32, 30), result);
    // All arena allocations freed automatically
}

test "choosing the right allocator" {
    // For small, known-size allocations - FixedBufferAllocator
    var buffer: [256]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const small_alloc = fba.allocator();

    const small_data = try small_alloc.alloc(u8, 10);
    small_data[0] = 1;
    try testing.expectEqual(@as(u8, 1), small_data[0]);

    // For temporary allocations - ArenaAllocator
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const temp_alloc = arena.allocator();

    const temp_data = try temp_alloc.alloc(i32, 100);
    temp_data[0] = 2;
    try testing.expectEqual(@as(i32, 2), temp_data[0]);

    // For general use - GeneralPurposeAllocator
    // (or testing.allocator in tests)
    const general_alloc = testing.allocator;
    const general_data = try general_alloc.alloc(f32, 50);
    defer general_alloc.free(general_data);

    general_data[0] = 3.0;
    try testing.expect(@abs(general_data[0] - 3.0) < 0.01);
}
```

### Handling Allocation Failures

Allocations can fail - always be prepared:

```zig
test "handling allocation failures" {
    const tryAllocate = struct {
        fn call(allocator: std.mem.Allocator, size: usize) ![]u8 {
            const data = allocator.alloc(u8, size) catch |err| {
                std.debug.print("Allocation failed: {}\n", .{err});
                return err;
            };
            return data;
        }
    }.call;

    // This will likely succeed
    const data = try tryAllocate(testing.allocator, 100);
    defer testing.allocator.free(data);

    // FixedBufferAllocator can run out of space
    var buffer: [10]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);

    const result = tryAllocate(fba.allocator(), 1000);
    try testing.expectError(error.OutOfMemory, result);
}
```

Unlike garbage-collected languages, running out of memory is a recoverable error in Zig.

### Combining with errdefer

Use `errdefer` to clean up on allocation failure:

```zig
test "allocator with errdefer" {
    const createAndInit = struct {
        fn call(allocator: std.mem.Allocator, should_fail: bool) ![]i32 {
            const data = try allocator.alloc(i32, 10);
            errdefer allocator.free(data); // Free if initialization fails

            // Initialize
            for (data, 0..) |*item, i| {
                item.* = @intCast(i);
            }

            if (should_fail) {
                return error.InitFailed; // errdefer runs
            }

            return data; // errdefer doesn't run
        }
    }.call;

    // Success case
    const data = try createAndInit(testing.allocator, false);
    defer testing.allocator.free(data);
    try testing.expectEqual(@as(i32, 5), data[5]);

    // Failure case - errdefer prevents leak
    const result = createAndInit(testing.allocator, true);
    try testing.expectError(error.InitFailed, result);
}
```

### Practical Example

Building a dynamic data structure:

```zig
test "building a dynamic data structure" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    const allocator = arena.allocator();

    var names = std.ArrayList([]const u8){};
    defer names.deinit(allocator);

    // Add strings to list
    try names.append(allocator, "Alice");
    try names.append(allocator, "Bob");
    try names.append(allocator, "Charlie");

    // Create a copy of a string
    const name_copy = try allocator.dupe(u8, "David");
    try names.append(allocator, name_copy);

    try testing.expectEqual(@as(usize, 4), names.items.len);
    try testing.expect(std.mem.eql(u8, names.items[0], "Alice"));

    // arena.deinit() frees everything
}
```

### Decision Tree

**Which allocator should I use?**

- Writing tests? → `testing.allocator`
- Small, temporary, stack allocation? → `FixedBufferAllocator`
- Many allocations, free all at once? → `ArenaAllocator`
- General purpose, long-lived? → `GeneralPurposeAllocator`

**Should I store the allocator in my struct?**

- Struct allocates memory in `init`? → Yes, store it for `deinit`
- Struct only receives allocated memory? → No, caller handles it

### Common Patterns

**Init/deinit pattern:**
```zig
fn init(allocator: std.mem.Allocator) !@This() {
    const data = try allocator.alloc(u8, size);
    return .{ .data = data, .allocator = allocator };
}

fn deinit(self: *@This()) void {
    self.allocator.free(self.data);
}
```

**Arena for scoped lifetime:**
```zig
var arena = std.heap.ArenaAllocator.init(parent_allocator);
defer arena.deinit();
// ... use arena.allocator() ...
```

**Passing allocator through call chain:**
```zig
fn topLevel(allocator: std.mem.Allocator) !void {
    try middleLevel(allocator);
}

fn middleLevel(allocator: std.mem.Allocator) !void {
    const data = try bottomLevel(allocator);
    defer allocator.free(data);
}
```

### Common Mistakes

**Forgetting to pass allocator:**
```zig
var list = std.ArrayList(i32){};
list.append(1);  // error: no allocator provided
// Fixed:
try list.append(allocator, 1);
```

**Forgetting defer:**
```zig
const data = try allocator.alloc(u8, 100);
// Memory leak! Need: defer allocator.free(data);
```

**Using wrong allocator for deinit:**
```zig
const data = try allocator1.alloc(u8, 100);
allocator2.free(data);  // Wrong! Must use same allocator
```

**Not handling OutOfMemory:**
```zig
const data = allocator.alloc(u8, huge_size);
// Should be:
const data = try allocator.alloc(u8, huge_size);
```

### Full Tested Code

```zig
// Recipe 0.12: Understanding Allocators (CRITICAL)
// Target Zig Version: 0.15.2
//
// This is critical for beginners from garbage-collected languages.
// Zig requires explicit memory allocation - no hidden allocations.

const std = @import("std");
const testing = std.testing;

// ANCHOR: why_allocators
// Part 1: Why Zig Needs Allocators
//
// Unlike Python/Java/JavaScript, Zig has NO default allocator
// You must explicitly choose where memory comes from

test "no default allocator" {
    // This would NOT compile in Zig:
    // var list = std.ArrayList(i32).init();  // error: missing allocator parameter

    // You MUST provide an allocator:
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    try list.append(testing.allocator, 1);
    try list.append(testing.allocator, 2);

    try testing.expectEqual(@as(usize, 2), list.items.len);
}

test "allocator interface" {
    // std.mem.Allocator is an interface
    // All allocators implement the same interface:
    // - alloc(T, n) - allocate n items of type T
    // - free(memory) - free memory
    // - create(T) - allocate one T
    // - destroy(T) - free one T

    const allocator = testing.allocator;

    // Allocate a slice of 10 integers
    const numbers = try allocator.alloc(i32, 10);
    defer allocator.free(numbers);

    numbers[0] = 42;
    try testing.expectEqual(@as(i32, 42), numbers[0]);
    try testing.expectEqual(@as(usize, 10), numbers.len);

    // Allocate a single struct
    const Point = struct {
        x: i32,
        y: i32,
    };

    const point = try allocator.create(Point);
    defer allocator.destroy(point);

    point.* = .{ .x = 10, .y = 20 };
    try testing.expectEqual(@as(i32, 10), point.x);
}
// ANCHOR_END: why_allocators

// ANCHOR: allocator_types
// Part 2: Common Allocator Types
//
// Zig provides several allocators for different use cases

test "FixedBufferAllocator - stack memory" {
    // Fixed buffer - uses stack memory, no malloc
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // Allocate from the fixed buffer
    const numbers = try allocator.alloc(i32, 10);
    // No free needed - buffer is on stack

    numbers[0] = 100;
    try testing.expectEqual(@as(i32, 100), numbers[0]);

    // If you run out of buffer space, alloc returns error.OutOfMemory
    const result = allocator.alloc(i32, 1000);
    try testing.expectError(error.OutOfMemory, result);
}

test "GeneralPurposeAllocator - safe malloc" {
    // GPA is like malloc but with leak detection
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        const leaked = gpa.deinit();
        if (leaked == .leak) {
            @panic("Memory leak detected!");
        }
    }

    const allocator = gpa.allocator();

    // Allocate on heap
    const numbers = try allocator.alloc(i32, 100);
    defer allocator.free(numbers);

    numbers[50] = 42;
    try testing.expectEqual(@as(i32, 42), numbers[50]);

    // GPA checks for leaks when deinit() is called
}

test "ArenaAllocator - batch cleanup" {
    // Arena allocates many items, frees all at once
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit(); // Frees ALL allocations

    const allocator = arena.allocator();

    // Allocate many things
    const slice1 = try allocator.alloc(i32, 10);
    const slice2 = try allocator.alloc(i32, 20);
    const slice3 = try allocator.alloc(i32, 30);

    // No individual free calls needed!
    slice1[0] = 1;
    slice2[0] = 2;
    slice3[0] = 3;

    try testing.expectEqual(@as(i32, 1), slice1[0]);
    try testing.expectEqual(@as(i32, 2), slice2[0]);
    try testing.expectEqual(@as(i32, 3), slice3[0]);

    // arena.deinit() frees everything at once
}

test "testing.allocator - for tests" {
    // testing.allocator is a GPA configured for testing
    // It detects memory leaks automatically

    const allocator = testing.allocator;

    const numbers = try allocator.alloc(i32, 50);
    defer allocator.free(numbers);

    // If you forget the defer, test will fail with leak detection
    numbers[0] = 99;
    try testing.expectEqual(@as(i32, 99), numbers[0]);
}
// ANCHOR_END: allocator_types

// ANCHOR: allocator_patterns
// Part 3: Common Allocator Patterns
//
// How to use allocators in real code

test "passing allocators to functions" {
    // Convention: allocator is first parameter
    const createList = struct {
        fn call(allocator: std.mem.Allocator, size: usize) ![]i32 {
            const list = try allocator.alloc(i32, size);
            for (list, 0..) |*item, i| {
                item.* = @intCast(i);
            }
            return list;
        }
    }.call;

    const list = try createList(testing.allocator, 5);
    defer testing.allocator.free(list);

    try testing.expectEqual(@as(i32, 0), list[0]);
    try testing.expectEqual(@as(i32, 4), list[4]);
}

test "struct with allocator field" {
    // Structs that allocate keep a reference to allocator
    const Buffer = struct {
        data: []u8,
        allocator: std.mem.Allocator,

        fn init(allocator: std.mem.Allocator, size: usize) !@This() {
            const data = try allocator.alloc(u8, size);
            return .{
                .data = data,
                .allocator = allocator,
            };
        }

        fn deinit(self: *@This()) void {
            self.allocator.free(self.data);
        }
    };

    var buffer = try Buffer.init(testing.allocator, 100);
    defer buffer.deinit();

    buffer.data[0] = 42;
    try testing.expectEqual(@as(u8, 42), buffer.data[0]);
}

test "arena for temporary allocations" {
    // Use arena for request-scoped lifetimes
    const processRequest = struct {
        fn call(parent_allocator: std.mem.Allocator) !i32 {
            var arena = std.heap.ArenaAllocator.init(parent_allocator);
            defer arena.deinit(); // Cleanup all at end

            const allocator = arena.allocator();

            // Allocate many temporary things
            const temp1 = try allocator.alloc(i32, 10);
            const temp2 = try allocator.alloc(i32, 20);

            // Do work...
            temp1[0] = 10;
            temp2[0] = 20;

            return temp1[0] + temp2[0];
        }
    }.call;

    const result = try processRequest(testing.allocator);
    try testing.expectEqual(@as(i32, 30), result);
    // All arena allocations freed automatically
}

test "choosing the right allocator" {
    // For small, known-size allocations - FixedBufferAllocator
    var buffer: [256]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const small_alloc = fba.allocator();

    const small_data = try small_alloc.alloc(u8, 10);
    small_data[0] = 1;
    try testing.expectEqual(@as(u8, 1), small_data[0]);

    // For temporary allocations - ArenaAllocator
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const temp_alloc = arena.allocator();

    const temp_data = try temp_alloc.alloc(i32, 100);
    temp_data[0] = 2;
    try testing.expectEqual(@as(i32, 2), temp_data[0]);

    // For general use - GeneralPurposeAllocator
    // (or testing.allocator in tests)
    const general_alloc = testing.allocator;
    const general_data = try general_alloc.alloc(f32, 50);
    defer general_alloc.free(general_data);

    general_data[0] = 3.0;
    try testing.expect(@abs(general_data[0] - 3.0) < 0.01);
}
// ANCHOR_END: allocator_patterns

// Handling out-of-memory errors

test "handling allocation failures" {
    // Allocations can fail - plan for it
    const tryAllocate = struct {
        fn call(allocator: std.mem.Allocator, size: usize) ![]u8 {
            const data = allocator.alloc(u8, size) catch |err| {
                std.debug.print("Allocation failed: {}\n", .{err});
                return err;
            };
            return data;
        }
    }.call;

    // This will likely succeed
    const data = try tryAllocate(testing.allocator, 100);
    defer testing.allocator.free(data);

    try testing.expectEqual(@as(usize, 100), data.len);

    // FixedBufferAllocator can run out of space
    var buffer: [10]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);

    const result = tryAllocate(fba.allocator(), 1000);
    try testing.expectError(error.OutOfMemory, result);
}

// Complex example

test "building a dynamic data structure" {
    // Realistic example: building a list of strings
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    const allocator = arena.allocator();

    var names = std.ArrayList([]const u8){};
    defer names.deinit(allocator);

    // Add strings to list
    try names.append(allocator, "Alice");
    try names.append(allocator, "Bob");
    try names.append(allocator, "Charlie");

    // Create a copy of a string
    const name_copy = try allocator.dupe(u8, "David");
    try names.append(allocator, name_copy);

    try testing.expectEqual(@as(usize, 4), names.items.len);
    try testing.expect(std.mem.eql(u8, names.items[0], "Alice"));
    try testing.expect(std.mem.eql(u8, names.items[3], "David"));

    // arena.deinit() frees everything
}

test "allocator with errdefer" {
    const createAndInit = struct {
        fn call(allocator: std.mem.Allocator, should_fail: bool) ![]i32 {
            const data = try allocator.alloc(i32, 10);
            errdefer allocator.free(data); // Free if initialization fails

            // Initialize
            for (data, 0..) |*item, i| {
                item.* = @intCast(i);
            }

            if (should_fail) {
                return error.InitFailed; // errdefer runs
            }

            return data; // errdefer doesn't run
        }
    }.call;

    // Success case
    const data = try createAndInit(testing.allocator, false);
    defer testing.allocator.free(data);
    try testing.expectEqual(@as(i32, 5), data[5]);

    // Failure case - errdefer prevents leak
    const result = createAndInit(testing.allocator, true);
    try testing.expectError(error.InitFailed, result);
}

// Summary:
// - Zig has NO default allocator - you must provide one
// - std.mem.Allocator is the interface all allocators implement
// - FixedBufferAllocator: stack memory, no malloc
// - GeneralPurposeAllocator: safe malloc with leak detection
// - ArenaAllocator: batch allocate, free all at once
// - testing.allocator: for tests, detects leaks
// - Convention: allocator is first function parameter
// - Always use defer/errdefer to prevent leaks
// - Handle allocation failures with try/catch
```

### See Also

- Recipe 0.11: Optionals, Errors, and Resource Cleanup
- Recipe 0.6: Arrays, ArrayLists, and Slices
- Recipe 0.13: Testing and Debugging

---

## Recipe 0.13: Testing and Debugging Fundamentals {#recipe-0-13}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, fundamentals, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_13.zig`

### Problem

You need to verify your code works correctly and debug issues when they arise. How do you write tests in Zig? What testing functions are available? How do you print debug output? How do you investigate bugs?

### Solution

Zig has testing built into the language:

1. **test blocks** - First-class test support with the `test` keyword
2. **std.testing** - Rich assertion library for verification
3. **std.debug** - Debugging utilities and formatted printing
4. **std.log** - Structured logging for production code

Run tests with `zig test filename.zig`. All tests run automatically, with automatic memory leak detection.

### Discussion

### Part 1: Basic Testing with std.testing

```zig
// Part 1: Basic Testing with std.testing
//
// Tests are first-class citizens in Zig

test "basic test example" {
    // Test blocks start with 'test' keyword
    // They run when you execute `zig test filename.zig`

    const x: i32 = 42;
    const y: i32 = 42;

    // expect: assert a boolean condition
    try testing.expect(x == y);
}

test "testing equality" {
    // expectEqual: check two values are equal
    const result = 2 + 2;
    try testing.expectEqual(@as(i32, 4), result);

    // Type must match exactly
    const a: u8 = 10;
    const b: u8 = 10;
    try testing.expectEqual(a, b);
}

test "testing strings" {
    const str1 = "hello";
    const str2 = "hello";

    // For strings, use std.mem.eql
    try testing.expect(std.mem.eql(u8, str1, str2));

    // This would NOT work:
    // try testing.expectEqual(str1, str2);  // Compares pointers, not content
}

test "testing errors" {
    const divide = struct {
        fn call(a: i32, b: i32) !i32 {
            if (b == 0) return error.DivisionByZero;
            return @divTrunc(a, b);
        }
    }.call;

    // expectError: check a specific error is returned
    const result = divide(10, 0);
    try testing.expectError(error.DivisionByZero, result);

    // Successful case
    const success = try divide(10, 2);
    try testing.expectEqual(@as(i32, 5), success);
}

test "testing floating point" {
    const pi: f32 = 3.14159;

    // For floats, use epsilon comparison
    try testing.expect(@abs(pi - 3.14159) < 0.00001);

    // Or use expectApproxEqAbs
    try testing.expectApproxEqAbs(@as(f32, 3.14159), pi, 0.00001);
}
```

Never use exact equality for floats - use epsilon comparisons or `expectApproxEqAbs`.

### Part 2: Advanced Testing Patterns

```zig
// Part 2: Advanced Testing Patterns
//
// More sophisticated testing techniques

test "testing with allocators" {
    // Always use testing.allocator in tests
    // It detects memory leaks automatically

    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    try list.append(testing.allocator, 1);
    try list.append(testing.allocator, 2);
    try list.append(testing.allocator, 3);

    try testing.expectEqual(@as(usize, 3), list.items.len);
    try testing.expectEqual(@as(i32, 2), list.items[1]);

    // If you forget defer, test fails with memory leak error
}

test "testing slices" {
    const expected = [_]i32{ 1, 2, 3, 4, 5 };
    const actual = [_]i32{ 1, 2, 3, 4, 5 };

    // expectEqualSlices: compare entire slices
    try testing.expectEqualSlices(i32, &expected, &actual);

    // Works with strings too
    const str = "hello";
    try testing.expectEqualSlices(u8, "hello", str);
}

test "testing optional values" {
    const maybe_value: ?i32 = 42;
    const no_value: ?i32 = null;

    // Check if optional has value
    try testing.expect(maybe_value != null);
    try testing.expect(no_value == null);

    // Unwrap and check value
    if (maybe_value) |value| {
        try testing.expectEqual(@as(i32, 42), value);
    } else {
        try testing.expect(false); // Should not reach here
    }
}

test "testing panics" {
    const willPanic = struct {
        fn call() void {
            @panic("This is a panic!");
        }
    }.call;

    // Can't directly test for panics in tests
    // But you can test conditions that would cause them

    const safe_optional: ?i32 = 42;
    if (safe_optional) |val| {
        try testing.expectEqual(@as(i32, 42), val);
    }

    // Using .? would panic if null - avoid in tests unless intended
    _ = willPanic; // Acknowledged but not called
}

fn fibonacci(n: u32) u32 {
    if (n <= 1) return n;
    return fibonacci(n - 1) + fibonacci(n - 2);
}

test "testing a function with multiple cases" {
    try testing.expectEqual(@as(u32, 0), fibonacci(0));
    try testing.expectEqual(@as(u32, 1), fibonacci(1));
    try testing.expectEqual(@as(u32, 1), fibonacci(2));
    try testing.expectEqual(@as(u32, 2), fibonacci(3));
    try testing.expectEqual(@as(u32, 3), fibonacci(4));
    try testing.expectEqual(@as(u32, 5), fibonacci(5));
    try testing.expectEqual(@as(u32, 8), fibonacci(6));
}
```

Test edge cases and multiple inputs to ensure correctness.

### Part 3: Debugging Techniques

```zig
// Part 3: Debugging Techniques
//
// Tools and patterns for debugging Zig code

test "debug printing" {
    // std.debug.print outputs to stderr
    std.debug.print("\n[TEST] Starting debug print test\n", .{});

    const x: i32 = 42;
    const name = "Zig";

    // Format specifiers:
    // {d} - decimal
    // {s} - string
    // {x} - hexadecimal
    // {b} - binary
    // {} - default format for type
    std.debug.print("x={d}, name={s}\n", .{ x, name });
    std.debug.print("x in hex={x}, binary={b}\n", .{ x, x });

    // Print with default formatter
    std.debug.print("Value: {}\n", .{x});
}

test "printing arrays and slices" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    std.debug.print("\nArray: ", .{});
    for (numbers) |n| {
        std.debug.print("{d} ", .{n});
    }
    std.debug.print("\n", .{});

    // Print with array formatter
    std.debug.print("Numbers: {any}\n", .{numbers});
}

test "printing structs" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    const p = Point{ .x = 10, .y = 20 };

    // {any} prints the struct with field names
    std.debug.print("\nPoint: {any}\n", .{p});

    // Manual printing
    std.debug.print("Point {{ x={d}, y={d} }}\n", .{ p.x, p.y });
}

test "conditional debug output" {
    const debug_mode = true;

    if (debug_mode) {
        std.debug.print("\n[DEBUG] This only prints in debug mode\n", .{});
    }

    // Use comptime to completely remove debug code in release builds
    const comptime_debug = struct {
        fn log(comptime fmt: []const u8, args: anytype) void {
            if (@import("builtin").mode == .Debug) {
                std.debug.print(fmt, args);
            }
        }
    }.log;

    comptime_debug("\n[COMPTIME DEBUG] This is removed in release\n", .{});
}

test "assertions" {
    const x: i32 = 42;

    // std.debug.assert panics if condition is false
    // Only in Debug/ReleaseSafe builds - removed in ReleaseFast/ReleaseSmall
    std.debug.assert(x == 42);

    // Always runs, even in release:
    if (x != 42) {
        @panic("x must be 42!");
    }
}

test "logging levels" {
    // std.log provides structured logging
    std.log.debug("This is a debug message", .{});
    std.log.info("This is an info message", .{});
    std.log.warn("This is a warning", .{});
    std.log.err("This is an error", .{});

    // Log with context
    const value: i32 = 100;
    std.log.info("Value is {d}", .{value});
}

fn debugHelper(x: i32) void {
    std.debug.print("debugHelper called with {d}\n", .{x});
    std.debug.print("Stack trace:\n", .{});
    std.debug.dumpCurrentStackTrace(@returnAddress());
}

test "stack traces" {
    // Stack traces help find where errors occur
    std.debug.print("\n[TEST] Stack trace example:\n", .{});
    debugHelper(42);
}
```

### Test Organization

**Tests Near Code:**

```zig
test "test organization" {
    const MyStruct = struct {
        value: i32,

        fn init(val: i32) @This() {
            return .{ .value = val };
        }

        fn double(self: @This()) i32 {
            return self.value * 2;
        }

        // Tests can be inside structs too
        test "MyStruct.double" {
            const s = init(21);
            try testing.expectEqual(@as(i32, 42), s.double());
        }
    };

    const s = MyStruct.init(10);
    try testing.expectEqual(@as(i32, 20), s.double());
}
```

Tests can be:
- At file level
- Inside structs (near the code they test)
- In separate test files

### Common std.testing Functions

- `expect(condition)` - Assert boolean condition
- `expectEqual(expected, actual)` - Assert values are equal
- `expectError(error, result)` - Assert specific error returned
- `expectEqualSlices(T, expected, actual)` - Assert slices are equal
- `expectApproxEqAbs(expected, actual, epsilon)` - Float comparison
- `expectEqualStrings(expected, actual)` - String comparison

### Running Tests

```bash
# Run all tests in a file
zig test file.zig

# Run tests with specific build mode
zig test -O ReleaseSafe file.zig

# Run tests for entire project
zig build test
```

### Best Practices

**Write tests as you code:**
```zig
fn processData(data: []const u8) !void {
    // Implementation
}

test "processData with empty input" {
    try processData("");
}

test "processData with valid input" {
    try processData("test");
}
```

**Use testing.allocator:**
```zig
test "always use testing allocator" {
    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator); // Automatic leak detection
    // ...
}
```

**Test edge cases:**
```zig
test "edge cases matter" {
    try testing.expectEqual(0, fibonacci(0)); // Zero
    try testing.expectEqual(1, fibonacci(1)); // One
    try testing.expectEqual(55, fibonacci(10)); // Larger value
}
```

### Common Mistakes

**Comparing strings with ==:**
```zig
const str1 = "hello";
const str2 = "hello";
try testing.expect(str1 == str2);  // Wrong - compares pointers!
try testing.expect(std.mem.eql(u8, str1, str2));  // Correct
```

**Forgetting defer with allocator:**
```zig
var list = std.ArrayList(i32){};
try list.append(testing.allocator, 1);
// Missing: defer list.deinit(testing.allocator);
// Test will fail with memory leak!
```

**Using exact equality for floats:**
```zig
const f: f32 = 0.1 + 0.2;
try testing.expectEqual(0.3, f);  // May fail due to precision!
try testing.expectApproxEqAbs(0.3, f, 0.0001);  // Correct
```

### Full Tested Code

```zig
// Recipe 0.13: Testing and Debugging Fundamentals
// Target Zig Version: 0.15.2
//
// This recipe covers creating tests, using std.testing, and debugging techniques.

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_testing
// Part 1: Basic Testing with std.testing
//
// Tests are first-class citizens in Zig

test "basic test example" {
    // Test blocks start with 'test' keyword
    // They run when you execute `zig test filename.zig`

    const x: i32 = 42;
    const y: i32 = 42;

    // expect: assert a boolean condition
    try testing.expect(x == y);
}

test "testing equality" {
    // expectEqual: check two values are equal
    const result = 2 + 2;
    try testing.expectEqual(@as(i32, 4), result);

    // Type must match exactly
    const a: u8 = 10;
    const b: u8 = 10;
    try testing.expectEqual(a, b);
}

test "testing strings" {
    const str1 = "hello";
    const str2 = "hello";

    // For strings, use std.mem.eql
    try testing.expect(std.mem.eql(u8, str1, str2));

    // This would NOT work:
    // try testing.expectEqual(str1, str2);  // Compares pointers, not content
}

test "testing errors" {
    const divide = struct {
        fn call(a: i32, b: i32) !i32 {
            if (b == 0) return error.DivisionByZero;
            return @divTrunc(a, b);
        }
    }.call;

    // expectError: check a specific error is returned
    const result = divide(10, 0);
    try testing.expectError(error.DivisionByZero, result);

    // Successful case
    const success = try divide(10, 2);
    try testing.expectEqual(@as(i32, 5), success);
}

test "testing floating point" {
    const pi: f32 = 3.14159;

    // For floats, use epsilon comparison
    try testing.expect(@abs(pi - 3.14159) < 0.00001);

    // Or use expectApproxEqAbs
    try testing.expectApproxEqAbs(@as(f32, 3.14159), pi, 0.00001);
}
// ANCHOR_END: basic_testing

// ANCHOR: advanced_testing
// Part 2: Advanced Testing Patterns
//
// More sophisticated testing techniques

test "testing with allocators" {
    // Always use testing.allocator in tests
    // It detects memory leaks automatically

    var list = std.ArrayList(i32){};
    defer list.deinit(testing.allocator);

    try list.append(testing.allocator, 1);
    try list.append(testing.allocator, 2);
    try list.append(testing.allocator, 3);

    try testing.expectEqual(@as(usize, 3), list.items.len);
    try testing.expectEqual(@as(i32, 2), list.items[1]);

    // If you forget defer, test fails with memory leak error
}

test "testing slices" {
    const expected = [_]i32{ 1, 2, 3, 4, 5 };
    const actual = [_]i32{ 1, 2, 3, 4, 5 };

    // expectEqualSlices: compare entire slices
    try testing.expectEqualSlices(i32, &expected, &actual);

    // Works with strings too
    const str = "hello";
    try testing.expectEqualSlices(u8, "hello", str);
}

test "testing optional values" {
    const maybe_value: ?i32 = 42;
    const no_value: ?i32 = null;

    // Check if optional has value
    try testing.expect(maybe_value != null);
    try testing.expect(no_value == null);

    // Unwrap and check value
    if (maybe_value) |value| {
        try testing.expectEqual(@as(i32, 42), value);
    } else {
        try testing.expect(false); // Should not reach here
    }
}

test "testing panics" {
    const willPanic = struct {
        fn call() void {
            @panic("This is a panic!");
        }
    }.call;

    // Can't directly test for panics in tests
    // But you can test conditions that would cause them

    const safe_optional: ?i32 = 42;
    if (safe_optional) |val| {
        try testing.expectEqual(@as(i32, 42), val);
    }

    // Using .? would panic if null - avoid in tests unless intended
    _ = willPanic; // Acknowledged but not called
}

fn fibonacci(n: u32) u32 {
    if (n <= 1) return n;
    return fibonacci(n - 1) + fibonacci(n - 2);
}

test "testing a function with multiple cases" {
    try testing.expectEqual(@as(u32, 0), fibonacci(0));
    try testing.expectEqual(@as(u32, 1), fibonacci(1));
    try testing.expectEqual(@as(u32, 1), fibonacci(2));
    try testing.expectEqual(@as(u32, 2), fibonacci(3));
    try testing.expectEqual(@as(u32, 3), fibonacci(4));
    try testing.expectEqual(@as(u32, 5), fibonacci(5));
    try testing.expectEqual(@as(u32, 8), fibonacci(6));
}
// ANCHOR_END: advanced_testing

// ANCHOR: debugging
// Part 3: Debugging Techniques
//
// Tools and patterns for debugging Zig code

test "debug printing" {
    // std.debug.print outputs to stderr
    std.debug.print("\n[TEST] Starting debug print test\n", .{});

    const x: i32 = 42;
    const name = "Zig";

    // Format specifiers:
    // {d} - decimal
    // {s} - string
    // {x} - hexadecimal
    // {b} - binary
    // {} - default format for type
    std.debug.print("x={d}, name={s}\n", .{ x, name });
    std.debug.print("x in hex={x}, binary={b}\n", .{ x, x });

    // Print with default formatter
    std.debug.print("Value: {}\n", .{x});
}

test "printing arrays and slices" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };

    std.debug.print("\nArray: ", .{});
    for (numbers) |n| {
        std.debug.print("{d} ", .{n});
    }
    std.debug.print("\n", .{});

    // Print with array formatter
    std.debug.print("Numbers: {any}\n", .{numbers});
}

test "printing structs" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    const p = Point{ .x = 10, .y = 20 };

    // {any} prints the struct with field names
    std.debug.print("\nPoint: {any}\n", .{p});

    // Manual printing
    std.debug.print("Point {{ x={d}, y={d} }}\n", .{ p.x, p.y });
}

test "conditional debug output" {
    const debug_mode = true;

    if (debug_mode) {
        std.debug.print("\n[DEBUG] This only prints in debug mode\n", .{});
    }

    // Use comptime to completely remove debug code in release builds
    const comptime_debug = struct {
        fn log(comptime fmt: []const u8, args: anytype) void {
            if (@import("builtin").mode == .Debug) {
                std.debug.print(fmt, args);
            }
        }
    }.log;

    comptime_debug("\n[COMPTIME DEBUG] This is removed in release\n", .{});
}

test "assertions" {
    const x: i32 = 42;

    // std.debug.assert panics if condition is false
    // Only in Debug/ReleaseSafe builds - removed in ReleaseFast/ReleaseSmall
    std.debug.assert(x == 42);

    // Always runs, even in release:
    if (x != 42) {
        @panic("x must be 42!");
    }
}

test "logging levels" {
    // std.log provides structured logging
    std.log.debug("This is a debug message", .{});
    std.log.info("This is an info message", .{});
    std.log.warn("This is a warning", .{});
    std.log.err("This is an error", .{});

    // Log with context
    const value: i32 = 100;
    std.log.info("Value is {d}", .{value});
}

fn debugHelper(x: i32) void {
    std.debug.print("debugHelper called with {d}\n", .{x});
    std.debug.print("Stack trace:\n", .{});
    std.debug.dumpCurrentStackTrace(@returnAddress());
}

test "stack traces" {
    // Stack traces help find where errors occur
    std.debug.print("\n[TEST] Stack trace example:\n", .{});
    debugHelper(42);
}
// ANCHOR_END: debugging

// Organizing tests

test "test organization" {
    // Tests are typically organized near the code they test
    // Or in the same file

    const MyStruct = struct {
        value: i32,

        fn init(val: i32) @This() {
            return .{ .value = val };
        }

        fn double(self: @This()) i32 {
            return self.value * 2;
        }

        // Tests can be inside structs too
        test "MyStruct.double" {
            const s = init(21);
            try testing.expectEqual(@as(i32, 42), s.double());
        }
    };

    const s = MyStruct.init(10);
    try testing.expectEqual(@as(i32, 20), s.double());
}

test "test names can be descriptive" {
    // Test names are strings, so they can be very descriptive
    // This helps when tests fail

    const add = struct {
        fn call(a: i32, b: i32) i32 {
            return a + b;
        }
    }.call;

    try testing.expectEqual(@as(i32, 5), add(2, 3));
}

// Summary:
// - Use `test` blocks for testing
// - std.testing provides assertion functions
// - testing.allocator detects memory leaks
// - Use std.debug.print for debugging output
// - Use {any} formatter to print complex types
// - std.log provides structured logging
// - Tests run with `zig test filename.zig`
// - Tests are first-class - write them alongside code
```

### See Also

- Recipe 0.12: Understanding Allocators
- Recipe 0.11: Optionals, Errors, and Resource Cleanup
- Recipe 0.14: Projects, Modules, and Dependencies

---

## Recipe 0.14: Projects, Modules, and Dependencies {#recipe-0-14}

**Tags:** allocators, arraylist, data-structures, error-handling, fundamentals, hashmap, http, memory, networking, resource-cleanup, testing
**Difficulty:** beginner
**Code:** `code/00-bootcamp/recipe_0_14.zig`

### Problem

You've been writing small single-file Zig programs. Now you need to organize code across multiple files, import modules, structure a project, and manage dependencies. How does Zig's module system work? What are the standard project layouts? How do you use the build system?

### Solution

Zig provides a straightforward module and build system:

1. **Modules are just structs** - Use `pub` to export functionality
2. **@import loads modules** - Import the standard library or your own files
3. **build.zig configures projects** - Standard build script pattern
4. **build.zig.zon manages dependencies** - Package manifest file

The module system is simple: files are modules, structs are namespaces, and `pub` controls visibility.

### Discussion

### Part 1: Modules and @import

```zig
// Part 1: Modules and @import
//
// Zig uses @import to load code from other files

test "importing std library" {
    // @import("std") loads the standard library
    // It returns a struct containing all std modules

    // Access modules through the std namespace
    _ = std.ArrayList;
    _ = std.HashMap;
    _ = std.mem;
    _ = std.testing;
    _ = std.io;
}

test "module structure" {
    // Modules are just structs
    // They can contain:
    // - Functions
    // - Types (structs, enums, unions)
    // - Constants
    // - Other modules (nested)

    const MyModule = struct {
        // Public function
        pub fn greet(name: []const u8) void {
            std.debug.print("Hello, {s}!\n", .{name});
        }

        // Public type
        pub const Config = struct {
            debug: bool = false,
        };

        // Public constant
        pub const VERSION = "1.0.0";

        // Nested module
        pub const utils = struct {
            pub fn add(a: i32, b: i32) i32 {
                return a + b;
            }
        };
    };

    // Use the module
    MyModule.greet("Zig");
    const config = MyModule.Config{};
    try testing.expectEqual(false, config.debug);
    try testing.expect(std.mem.eql(u8, MyModule.VERSION, "1.0.0"));
    try testing.expectEqual(@as(i32, 5), MyModule.utils.add(2, 3));
}

test "public vs private in modules" {
    const MyModule = struct {
        // Public - visible when imported
        pub fn publicFunction() i32 {
            return 42;
        }

        // Private - only visible within this module
        fn privateHelper() i32 {
            return 10;
        }

        pub fn usesPrivate() i32 {
            return privateHelper() * 2;
        }
    };

    // Can call public functions
    try testing.expectEqual(@as(i32, 42), MyModule.publicFunction());
    try testing.expectEqual(@as(i32, 20), MyModule.usesPrivate());

    // Cannot call private functions from outside:
    // const x = MyModule.privateHelper();  // error
}
```

### Part 2: Project Structure and Organization

```zig
// Part 2: Project Structure and Organization
//
// Typical Zig project layout

test "typical project structure" {
    // A typical Zig project looks like:
    //
    // my-project/
    //   build.zig          - Build configuration
    //   build.zig.zon      - Package dependencies
    //   src/
    //     main.zig         - Entry point
    //     lib.zig          - Library root (optional)
    //     module1.zig      - Module files
    //     module2.zig
    //   tests/
    //     tests.zig        - Integration tests

    // Files are modules - use @import to load them
    // @import("./module.zig") loads a file
    // @import("module") loads from build.zig modules

    try testing.expect(true); // This test just documents structure
}

test "file organization patterns" {
    // Pattern 1: Monolithic - everything in one file
    // Good for: Small projects, prototypes

    // Pattern 2: Modular - split by functionality
    // src/
    //   parser.zig
    //   lexer.zig
    //   ast.zig
    //   main.zig

    // Pattern 3: Hierarchical - nested modules
    // src/
    //   frontend/
    //     lexer.zig
    //     parser.zig
    //   backend/
    //     codegen.zig
    //     optimizer.zig

    // Import from subdirectories:
    // const lexer = @import("frontend/lexer.zig");

    try testing.expect(true); // Documentation test
}
```

### Part 3: Build System Basics

```zig
// Part 3: Build System Basics
//
// Understanding build.zig

test "build system concepts" {
    // build.zig is a Zig program that builds your project
    // It runs at build time (before compiling your code)

    // Key concepts:
    // - Build steps: compile, test, run, install
    // - Dependencies: link libraries, add modules
    // - Options: build configurations
    // - Cross-compilation: different targets

    // Common build.zig pattern:
    // pub fn build(b: *std.Build) void {
    //     const target = b.standardTargetOptions(.{});
    //     const optimize = b.standardOptimizeOption(.{});
    //
    //     const exe = b.addExecutable(.{
    //         .name = "my-app",
    //         .root_source_file = b.path("src/main.zig"),
    //         .target = target,
    //         .optimize = optimize,
    //     });
    //
    //     b.installArtifact(exe);
    // }

    try testing.expect(true); // Documentation test
}

test "common build commands" {
    // zig init-exe          - Create executable project
    // zig init-lib          - Create library project
    // zig build             - Build the project
    // zig build run         - Build and run
    // zig build test        - Run tests
    // zig build install     - Install to zig-out/
    // zig build -Doptimize=ReleaseFast  - Release build

    try testing.expect(true); // Documentation test
}

test "dependency management" {
    // build.zig.zon - Package manifest file
    // .{
    //     .name = "my-project",
    //     .version = "0.1.0",
    //     .dependencies = .{
    //         .some_lib = .{
    //             .url = "https://github.com/user/lib/archive/v1.0.tar.gz",
    //             .hash = "1220...",
    //         },
    //     },
    // }

    // zig fetch - Download and cache dependency

    // In build.zig, add the dependency:
    // const some_lib = b.dependency("some_lib", .{});
    // exe.root_module.addImport("some_lib", some_lib.module("some_lib"));

    // In your code:
    // const some_lib = @import("some_lib");

    try testing.expect(true); // Documentation test
}
```

### Practical Examples

**Example Module Pattern:**

```zig
test "example module pattern" {
    // A typical module exports a focused API
    const StringUtils = struct {
        pub fn reverse(allocator: std.mem.Allocator, s: []const u8) ![]u8 {
            const result = try allocator.alloc(u8, s.len);
            var i: usize = 0;
            while (i < s.len) : (i += 1) {
                result[i] = s[s.len - 1 - i];
            }
            return result;
        }

        pub fn toUpper(allocator: std.mem.Allocator, s: []const u8) ![]u8 {
            const result = try allocator.dupe(u8, s);
            for (result) |*c| {
                if (c.* >= 'a' and c.* <= 'z') {
                    c.* -= 32;
                }
            }
            return result;
        }
    };

    const reversed = try StringUtils.reverse(testing.allocator, "hello");
    defer testing.allocator.free(reversed);
    try testing.expect(std.mem.eql(u8, "olleh", reversed));

    const upper = try StringUtils.toUpper(testing.allocator, "hello");
    defer testing.allocator.free(upper);
    try testing.expect(std.mem.eql(u8, "HELLO", upper));
}
```

This module provides string utilities with clear, focused functionality.

**Multi-File Project Simulation:**

```zig
test "multi-file project simulation" {
    // Simulate what multiple files would look like

    // File: math.zig
    const Math = struct {
        pub fn add(a: i32, b: i32) i32 {
            return a + b;
        }

        pub fn multiply(a: i32, b: i32) i32 {
            return a * b;
        }
    };

    // File: utils.zig
    const Utils = struct {
        pub fn max(a: i32, b: i32) i32 {
            return if (a > b) a else b;
        }
    };

    // File: main.zig would import these:
    // const math = @import("math.zig");
    // const utils = @import("utils.zig");

    // Using them:
    const sum = Math.add(5, 3);
    const product = Math.multiply(sum, 2);
    const result = Utils.max(product, 100);

    try testing.expectEqual(@as(i32, 100), result);
}
```

**Namespace Organization:**

```zig
test "namespace organization" {
    // Good practice: organize related functionality
    const App = struct {
        pub const models = struct {
            pub const User = struct {
                id: u32,
                name: []const u8,
            };

            pub const Post = struct {
                id: u32,
                title: []const u8,
            };
        };

        pub const services = struct {
            pub fn createUser(id: u32, name: []const u8) models.User {
                return .{ .id = id, .name = name };
            }
        };
    };

    // Clean, hierarchical access:
    const user = App.services.createUser(1, "Alice");
    try testing.expectEqual(@as(u32, 1), user.id);
    try testing.expect(std.mem.eql(u8, "Alice", user.name));
}
```

Nested namespaces create clean, self-documenting code organization.

**Conditional Imports:**

```zig
test "conditional imports" {
    // Can conditionally import based on platform
    const os_module = if (@import("builtin").os.tag == .windows)
        struct {
            pub fn getPath() []const u8 {
                return "C:\\path";
            }
        }
    else
        struct {
            pub fn getPath() []const u8 {
                return "/path";
            }
        };

    const path = os_module.getPath();
    try testing.expect(path.len > 0);
}
```

Use `@import("builtin")` to conditionally select platform-specific code.

### Getting Started with Projects

**Create a new executable project:**
```bash
zig init-exe
```

This generates:
- `build.zig` - Build configuration
- `build.zig.zon` - Package manifest
- `src/main.zig` - Entry point with `pub fn main() !void`

**Create a new library project:**
```bash
zig init-lib
```

This generates:
- `build.zig` - Library build configuration
- `src/root.zig` - Library root module

**Build and run:**
```bash
zig build run
```

**Run tests:**
```bash
zig build test
```

### Common Patterns

**Init pattern for modules:**
```zig
const MyModule = struct {
    data: []const u8,

    pub fn init(data: []const u8) MyModule {
        return .{ .data = data };
    }
};
```

**Exporting library interface:**
```zig
// In src/lib.zig
pub const Parser = @import("parser.zig").Parser;
pub const Lexer = @import("lexer.zig").Lexer;
pub const version = "1.0.0";
```

**Cross-compilation:**
```bash
zig build -Dtarget=x86_64-windows
zig build -Dtarget=aarch64-linux
```

### Full Tested Code

```zig
// Recipe 0.14: Projects, Modules, and Dependencies
// Target Zig Version: 0.15.2
//
// This recipe covers project structure, modules, and the build system.

const std = @import("std");
const testing = std.testing;

// ANCHOR: modules
// Part 1: Modules and @import
//
// Zig uses @import to load code from other files

test "importing std library" {
    // @import("std") loads the standard library
    // It returns a struct containing all std modules

    // Access modules through the std namespace
    _ = std.ArrayList;
    _ = std.HashMap;
    _ = std.mem;
    _ = std.testing;
    _ = std.io;
}

test "module structure" {
    // Modules are just structs
    // They can contain:
    // - Functions
    // - Types (structs, enums, unions)
    // - Constants
    // - Other modules (nested)

    const MyModule = struct {
        // Public function
        pub fn greet(name: []const u8) void {
            std.debug.print("Hello, {s}!\n", .{name});
        }

        // Public type
        pub const Config = struct {
            debug: bool = false,
        };

        // Public constant
        pub const VERSION = "1.0.0";

        // Nested module
        pub const utils = struct {
            pub fn add(a: i32, b: i32) i32 {
                return a + b;
            }
        };
    };

    // Use the module
    MyModule.greet("Zig");
    const config = MyModule.Config{};
    try testing.expectEqual(false, config.debug);
    try testing.expect(std.mem.eql(u8, MyModule.VERSION, "1.0.0"));
    try testing.expectEqual(@as(i32, 5), MyModule.utils.add(2, 3));
}

test "public vs private in modules" {
    const MyModule = struct {
        // Public - visible when imported
        pub fn publicFunction() i32 {
            return 42;
        }

        // Private - only visible within this module
        fn privateHelper() i32 {
            return 10;
        }

        pub fn usesPrivate() i32 {
            return privateHelper() * 2;
        }
    };

    // Can call public functions
    try testing.expectEqual(@as(i32, 42), MyModule.publicFunction());
    try testing.expectEqual(@as(i32, 20), MyModule.usesPrivate());

    // Cannot call private functions from outside:
    // const x = MyModule.privateHelper();  // error
}
// ANCHOR_END: modules

// ANCHOR: project_structure
// Part 2: Project Structure and Organization
//
// Typical Zig project layout

test "typical project structure" {
    // A typical Zig project looks like:
    //
    // my-project/
    //   build.zig          - Build configuration
    //   build.zig.zon      - Package dependencies
    //   src/
    //     main.zig         - Entry point
    //     lib.zig          - Library root (optional)
    //     module1.zig      - Module files
    //     module2.zig
    //   tests/
    //     tests.zig        - Integration tests

    // Files are modules - use @import to load them
    // @import("./module.zig") loads a file
    // @import("module") loads from build.zig modules

    try testing.expect(true); // This test just documents structure
}

test "file organization patterns" {
    // Pattern 1: Monolithic - everything in one file
    // Good for: Small projects, prototypes

    // Pattern 2: Modular - split by functionality
    // src/
    //   parser.zig
    //   lexer.zig
    //   ast.zig
    //   main.zig

    // Pattern 3: Hierarchical - nested modules
    // src/
    //   frontend/
    //     lexer.zig
    //     parser.zig
    //   backend/
    //     codegen.zig
    //     optimizer.zig

    // Import from subdirectories:
    // const lexer = @import("frontend/lexer.zig");

    try testing.expect(true); // Documentation test
}
// ANCHOR_END: project_structure

// ANCHOR: build_system
// Part 3: Build System Basics
//
// Understanding build.zig

test "build system concepts" {
    // build.zig is a Zig program that builds your project
    // It runs at build time (before compiling your code)

    // Key concepts:
    // - Build steps: compile, test, run, install
    // - Dependencies: link libraries, add modules
    // - Options: build configurations
    // - Cross-compilation: different targets

    // Common build.zig pattern:
    // pub fn build(b: *std.Build) void {
    //     const target = b.standardTargetOptions(.{});
    //     const optimize = b.standardOptimizeOption(.{});
    //
    //     const exe = b.addExecutable(.{
    //         .name = "my-app",
    //         .root_source_file = b.path("src/main.zig"),
    //         .target = target,
    //         .optimize = optimize,
    //     });
    //
    //     b.installArtifact(exe);
    // }

    try testing.expect(true); // Documentation test
}

test "common build commands" {
    // zig init-exe          - Create executable project
    // zig init-lib          - Create library project
    // zig build             - Build the project
    // zig build run         - Build and run
    // zig build test        - Run tests
    // zig build install     - Install to zig-out/
    // zig build -Doptimize=ReleaseFast  - Release build

    try testing.expect(true); // Documentation test
}

test "dependency management" {
    // build.zig.zon - Package manifest file
    // .{
    //     .name = "my-project",
    //     .version = "0.1.0",
    //     .dependencies = .{
    //         .some_lib = .{
    //             .url = "https://github.com/user/lib/archive/v1.0.tar.gz",
    //             .hash = "1220...",
    //         },
    //     },
    // }

    // zig fetch - Download and cache dependency

    // In build.zig, add the dependency:
    // const some_lib = b.dependency("some_lib", .{});
    // exe.root_module.addImport("some_lib", some_lib.module("some_lib"));

    // In your code:
    // const some_lib = @import("some_lib");

    try testing.expect(true); // Documentation test
}
// ANCHOR_END: build_system

// Practical examples

test "example module pattern" {
    // A typical module exports a focused API
    const StringUtils = struct {
        pub fn reverse(allocator: std.mem.Allocator, s: []const u8) ![]u8 {
            const result = try allocator.alloc(u8, s.len);
            var i: usize = 0;
            while (i < s.len) : (i += 1) {
                result[i] = s[s.len - 1 - i];
            }
            return result;
        }

        pub fn toUpper(allocator: std.mem.Allocator, s: []const u8) ![]u8 {
            const result = try allocator.dupe(u8, s);
            for (result) |*c| {
                if (c.* >= 'a' and c.* <= 'z') {
                    c.* -= 32;
                }
            }
            return result;
        }
    };

    const reversed = try StringUtils.reverse(testing.allocator, "hello");
    defer testing.allocator.free(reversed);
    try testing.expect(std.mem.eql(u8, "olleh", reversed));

    const upper = try StringUtils.toUpper(testing.allocator, "hello");
    defer testing.allocator.free(upper);
    try testing.expect(std.mem.eql(u8, "HELLO", upper));
}

test "multi-file project simulation" {
    // Simulate what multiple files would look like

    // File: math.zig
    const Math = struct {
        pub fn add(a: i32, b: i32) i32 {
            return a + b;
        }

        pub fn multiply(a: i32, b: i32) i32 {
            return a * b;
        }
    };

    // File: utils.zig
    const Utils = struct {
        pub fn max(a: i32, b: i32) i32 {
            return if (a > b) a else b;
        }
    };

    // File: main.zig would import these:
    // const math = @import("math.zig");
    // const utils = @import("utils.zig");

    // Using them:
    const sum = Math.add(5, 3);
    const product = Math.multiply(sum, 2);
    const result = Utils.max(product, 100);

    try testing.expectEqual(@as(i32, 100), result);
}

test "namespace organization" {
    // Good practice: organize related functionality
    const App = struct {
        pub const models = struct {
            pub const User = struct {
                id: u32,
                name: []const u8,
            };

            pub const Post = struct {
                id: u32,
                title: []const u8,
            };
        };

        pub const services = struct {
            pub fn createUser(id: u32, name: []const u8) models.User {
                return .{ .id = id, .name = name };
            }
        };
    };

    // Clean, hierarchical access:
    const user = App.services.createUser(1, "Alice");
    try testing.expectEqual(@as(u32, 1), user.id);
    try testing.expect(std.mem.eql(u8, "Alice", user.name));
}

test "conditional imports" {
    // Can conditionally import based on platform
    const os_module = if (@import("builtin").os.tag == .windows)
        struct {
            pub fn getPath() []const u8 {
                return "C:\\path";
            }
        }
    else
        struct {
            pub fn getPath() []const u8 {
                return "/path";
            }
        };

    const path = os_module.getPath();
    try testing.expect(path.len > 0);
}

// Summary:
// - @import loads modules (std library or your files)
// - Modules are structs with pub members
// - Use pub to export from modules
// - Organize code in src/ directory
// - build.zig configures your project
// - build.zig.zon manages dependencies
// - zig build compiles everything
// - zig fetch downloads dependencies
// - Split code into logical modules
// - Use hierarchical namespaces
```

### See Also

- Recipe 0.7: Functions and the Standard Library
- Recipe 0.10: Structs, Enums, and Simple Data Models
- Recipe 0.12: Understanding Allocators

---

## Recipe 1.1: Writing Idiomatic Zig Code {#recipe-1-1}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, fundamentals, hashmap, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** beginner
**Code:** `code/01-foundation/recipe_0_1.zig`

---

## Recipe 1.2: Error Handling Patterns {#recipe-1-2}

**Tags:** allocators, error-handling, fundamentals, memory, resource-cleanup
**Difficulty:** beginner
**Code:** `code/01-foundation/recipe_0_2.zig`

---

## Recipe 1.3: Testing Strategy {#recipe-1-3}

**Tags:** allocators, arraylist, c-interop, data-structures, error-handling, fundamentals, memory, resource-cleanup, slices, testing
**Difficulty:** beginner
**Code:** `code/01-foundation/recipe_0_3.zig`

---

## Recipe 1.4: When to Pass by Pointer vs Value {#recipe-1-4}

**Tags:** fundamentals, pointers, slices
**Difficulty:** beginner
**Code:** `code/01-foundation/recipe_0_4.zig`

### Problem

You need to decide whether to pass function arguments by value or by pointer. Passing by value is simple but can be inefficient for large types. Passing by pointer is efficient but requires understanding mutability, aliasing, and lifetime rules.

### Solution

Zig gives you explicit control over how data flows through your program. Follow these guidelines:

- **Small types** (primitives, small structs): Pass by value
- **Need to modify**: Pass by mutable pointer (`*T`)
- **Large types, read-only**: Pass by const pointer (`*const T`)
- **Slices**: Already pointers, don't double-pointer
- **Returning data**: Return by value for small types, use caller-allocated pattern for large types

### Small Types: Pass by Value

Primitives and small structs are cheap to copy:

```zig
// Small types: pass by value (cheap to copy)
fn incrementByValue(x: i32) i32 {
    return x + 1;
}

fn addPoints(a: Point2D, b: Point2D) Point2D {
    return .{
        .x = a.x + b.x,
        .y = a.y + b.y,
    };
}

const Point2D = struct {
    x: f32,
    y: f32,
};

test "small types by value" {
    const result = incrementByValue(5);
    try testing.expectEqual(@as(i32, 6), result);

    const p1 = Point2D{ .x = 1.0, .y = 2.0 };
    const p2 = Point2D{ .x = 3.0, .y = 4.0 };
    const sum = addPoints(p1, p2);

    try testing.expectEqual(@as(f32, 4.0), sum.x);
    try testing.expectEqual(@as(f32, 6.0), sum.y);
}
```

Types under 16-32 bytes are generally passed by value. Copying a few bytes is faster than dereferencing a pointer.

### Mutation Requires Pointers

If a function needs to modify its argument, pass a mutable pointer:

```zig
// Mutation: pass by pointer when you need to modify
fn incrementByPointer(x: *i32) void {
    x.* += 1;
}

fn scalePoint(point: *Point2D, factor: f32) void {
    point.x *= factor;
    point.y *= factor;
}

test "mutation requires pointer" {
    var value: i32 = 5;
    incrementByPointer(&value);
    try testing.expectEqual(@as(i32, 6), value);

    var point = Point2D{ .x = 2.0, .y = 3.0 };
    scalePoint(&point, 2.0);

    try testing.expectEqual(@as(f32, 4.0), point.x);
    try testing.expectEqual(@as(f32, 6.0), point.y);
}
```

The `&` operator takes the address of a variable. The `.*` syntax dereferences the pointer to access or modify the value.

### Discussion

### Large Types: Use Const Pointers

For large structs, pass by const pointer to avoid copying:

```zig
// Large types: pass by const pointer to avoid copies
const LargeStruct = struct {
    data: [1024]u8,
    metadata: [256]u8,

    pub fn init() LargeStruct {
        return .{
            .data = [_]u8{0} ** 1024,
            .metadata = [_]u8{0} ** 256,
        };
    }
};

// Inefficient: copies 1280 bytes
fn processLargeByValue(large: LargeStruct) usize {
    var sum: usize = 0;
    for (large.data) |byte| {
        sum += byte;
    }
    return sum;
}

// Efficient: passes 8-byte pointer
fn processLargeByConstPointer(large: *const LargeStruct) usize {
    var sum: usize = 0;
    for (large.data) |byte| {
        sum += byte;
    }
    return sum;
}

test "large types use const pointer" {
    const large = LargeStruct.init();

    // Both work, but const pointer is more efficient
    const result1 = processLargeByValue(large);
    const result2 = processLargeByConstPointer(&large);

    try testing.expectEqual(result1, result2);
    try testing.expectEqual(@as(usize, 0), result1);
}
```

The `*const` syntax creates a read-only pointer. This avoids the copy while preventing accidental modification.

### Const Pointers Prevent Mutation

The type system enforces immutability for const pointers:

```zig
// Const pointers prevent mutation
fn tryToModify(point: *const Point2D) f32 {
    // point.x = 10.0;  // Compile error: cannot assign to const
    return point.x + point.y;
}

fn mustModify(point: *Point2D) void {
    point.x = 10.0; // OK: mutable pointer
}

test "const pointer prevents modification" {
    var point = Point2D{ .x = 1.0, .y = 2.0 };

    const sum = tryToModify(&point);
    try testing.expectEqual(@as(f32, 3.0), sum);

    mustModify(&point);
    try testing.expectEqual(@as(f32, 10.0), point.x);
}
```

Use `*const T` when you only need read access. This communicates intent and catches bugs at compile time.

### Slices Are Already Pointers

Slices are fat pointers (pointer + length). Never take a pointer to a slice:

```zig
// Slices are already pointers - don't double-pointer
fn sumSlice(items: []const i32) i32 {
    var total: i32 = 0;
    for (items) |item| {
        total += item;
    }
    return total;
}

// Don't do this - slice is already a reference
// fn sumSliceWrong(items: *const []const i32) i32 { ... }

test "slices are already pointers" {
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    const total = sumSlice(&numbers);
    try testing.expectEqual(@as(i32, 15), total);
}
```

A slice already contains a pointer to the data, so passing by value is efficient.

### Returning Values

Return small types by value:

```zig
// Return by value for small types and stack allocation
fn createPoint(x: f32, y: f32) Point2D {
    return .{ .x = x, .y = y };
}

fn createArray() [4]i32 {
    return .{ 1, 2, 3, 4 };
}

test "return by value for small types" {
    const point = createPoint(5.0, 10.0);
    try testing.expectEqual(@as(f32, 5.0), point.x);

    const array = createArray();
    try testing.expectEqual(@as(i32, 1), array[0]);
    try testing.expectEqual(@as(i32, 4), array[3]);
}
```

Returning by value is clear and safe. The compiler handles the memory efficiently.

### Caller-Allocated Pattern

For large types, use the caller-allocated pattern:

```zig
// Caller-allocated: pass pointer to receive large result
fn fillLargeStruct(result: *LargeStruct) void {
    result.data = [_]u8{42} ** 1024;
    result.metadata = [_]u8{1} ** 256;
}

test "caller-allocated pattern" {
    var large = LargeStruct.init();
    fillLargeStruct(&large);

    try testing.expectEqual(@as(u8, 42), large.data[0]);
    try testing.expectEqual(@as(u8, 1), large.metadata[0]);
}
```

The caller allocates the memory, and the function fills it in. This avoids copying large objects on return.

### Struct Method Conventions

Struct methods follow a consistent pattern for `self`:

```zig
// Struct methods: self convention
const Counter = struct {
    value: i32,

    pub fn init() Counter {
        return .{ .value = 0 };
    }

    // Method that reads: const pointer
    pub fn getValue(self: *const Counter) i32 {
        return self.value;
    }

    // Method that mutates: mutable pointer
    pub fn increment(self: *Counter) void {
        self.value += 1;
    }

    // Method that consumes: by value
    pub fn consume(self: Counter) i32 {
        return self.value;
    }
};

test "struct method self conventions" {
    var counter = Counter.init();

    try testing.expectEqual(@as(i32, 0), counter.getValue());

    counter.increment();
    try testing.expectEqual(@as(i32, 1), counter.getValue());

    const final = counter.consume();
    try testing.expectEqual(@as(i32, 1), final);
}
```

Use `*const Self` for read-only methods, `*Self` for mutating methods, and `Self` for consuming methods.

### Optional Pointers

Use optional pointers to return references that might not exist:

```zig
// Optional pointers for optional references
fn findMax(items: []const i32) ?*const i32 {
    if (items.len == 0) return null;

    var max_idx: usize = 0;
    for (items[1..], 1..) |val, i| {
        if (val > items[max_idx]) {
            max_idx = i;
        }
    }
    return &items[max_idx];
}

test "optional pointers" {
    const numbers = [_]i32{ 3, 7, 2, 9, 1 };
    const max = findMax(&numbers);

    try testing.expect(max != null);
    try testing.expectEqual(@as(i32, 9), max.?.*);

    const empty: []const i32 = &.{};
    const no_max = findMax(empty);
    try testing.expect(no_max == null);
}
```

The `?*const T` type represents an optional pointer. Return `null` when there's no valid reference.

### Pointer Size Awareness

Pointers are always 8 bytes on 64-bit systems, regardless of what they point to:

```zig
// Size awareness: primitives vs structs
test "pointer size is always constant" {
    // Pointers are always 8 bytes on 64-bit (regardless of what they point to)
    try testing.expectEqual(@as(usize, 8), @sizeOf(*i32));
    try testing.expectEqual(@as(usize, 8), @sizeOf(*LargeStruct));
    try testing.expectEqual(@as(usize, 8), @sizeOf(*Point2D));

    // Values vary in size
    try testing.expectEqual(@as(usize, 4), @sizeOf(i32));
    try testing.expectEqual(@as(usize, 1280), @sizeOf(LargeStruct));
    try testing.expectEqual(@as(usize, 8), @sizeOf(Point2D));
}
```

When the value is larger than a pointer (typically 8 bytes), consider passing by pointer.

### Multiple Return Values

Return multiple values using a struct, not out-parameters:

```zig
// Multiple return values: use struct, not pointer out-params
const DivResult = struct {
    quotient: i32,
    remainder: i32,
};

fn divmod(a: i32, b: i32) DivResult {
    return .{
        .quotient = @divTrunc(a, b),
        .remainder = @rem(a, b),
    };
}

test "multi return with struct" {
    const result = divmod(17, 5);

    try testing.expectEqual(@as(i32, 3), result.quotient);
    try testing.expectEqual(@as(i32, 2), result.remainder);
}
```

Returning a struct is clearer and safer than using pointer out-parameters.

### Pointer Aliasing

Be aware that two pointers can refer to the same memory:

```zig
// Be aware of pointer aliasing
fn addToEach(a: *i32, b: *i32, value: i32) void {
    a.* += value;
    b.* += value;
}

test "pointer aliasing" {
    var x: i32 = 10;
    var y: i32 = 20;

    // Different pointers: works as expected
    addToEach(&x, &y, 5);
    try testing.expectEqual(@as(i32, 15), x);
    try testing.expectEqual(@as(i32, 25), y);

    // Same pointer: adds twice (aliasing)
    var z: i32 = 10;
    addToEach(&z, &z, 5);
    try testing.expectEqual(@as(i32, 20), z); // 10 + 5 + 5
}
```

When `a` and `b` point to the same location, both assignments affect the same value.

### Performance Considerations

The performance difference becomes significant for types larger than about 16-32 bytes:

- **Small types (≤16 bytes)**: Pass by value (simple and fast)
- **Medium types (16-100 bytes)**: Consider const pointer if frequently passed
- **Large types (>100 bytes)**: Always use const pointer

For actual benchmarking, use `std.time.Timer` and run operations in a loop. The compiler optimizes aggressively, so always measure in realistic scenarios.

### Decision Tree

Use this decision tree when choosing how to pass arguments:

1. **Need to modify the argument?**
   - Yes → Use `*T` (mutable pointer)
   - No → Continue

2. **Is it a slice or array-like type?**
   - Yes → Use `[]T` or `[]const T` (already a pointer)
   - No → Continue

3. **Is the type large (>16 bytes)?**
   - Yes → Use `*const T` (const pointer)
   - No → Continue

4. **Default: Pass by value** (`T`)

### Common Patterns

**Read-only large data:**
```zig
fn process(data: *const LargeStruct) Result
```

**Mutating argument:**
```zig
fn modify(data: *LargeStruct) void
```

**Slice (read-only):**
```zig
fn sum(items: []const i32) i32
```

**Slice (mutable):**
```zig
fn fill(items: []i32, value: i32) void
```

**Optional reference:**
```zig
fn find(items: []const Item) ?*const Item
```

**Multiple returns:**
```zig
fn parse(input: []const u8) struct { result: T, remaining: []const u8 }
```

### Memory Safety

Zig's pointer rules ensure memory safety:

- Pointers must point to valid memory
- Const pointers cannot be used to modify data
- Dangling pointers are prevented by the compiler when possible
- Lifetime analysis catches many use-after-free bugs

The type system guides you toward safe patterns while giving you low-level control when needed.

### See Also

- Recipe 0.9: Understanding Pointers and References
- Recipe 1.1: Writing Idiomatic Zig Code
- Recipe 2.6: Implementing a custom container

---

## Recipe 1.5: Build Modes and Safety {#recipe-1-5}

**Tags:** error-handling, fundamentals, pointers, testing
**Difficulty:** beginner
**Code:** `code/01-foundation/recipe_0_5.zig`

### Problem

You need to understand when and how Zig's safety features protect your code, and when to disable them for performance. You want to catch bugs during development without paying for safety checks in production, and you need to handle edge cases like integer overflow, division by zero, and null pointers safely.

### Solution

Zig provides four build modes that balance safety and performance:

- **Debug**: Full safety checks, no optimizations (development)
- **ReleaseSafe**: Full safety checks, optimized code (production default)
- **ReleaseFast**: No safety checks, maximum speed (performance-critical)
- **ReleaseSmall**: No safety checks, minimum binary size (embedded systems)

Use compile-time detection to adapt behavior, and leverage explicit operators for overflow handling.

### Detecting Build Mode

Check the current build mode at compile time:

```zig
// Detect current build mode at compile time
fn getCurrentBuildMode() []const u8 {
    return switch (builtin.mode) {
        .Debug => "Debug",
        .ReleaseSafe => "ReleaseSafe",
        .ReleaseFast => "ReleaseFast",
        .ReleaseSmall => "ReleaseSmall",
    };
}

test "detect build mode" {
    const mode = getCurrentBuildMode();
    std.debug.print("\nCurrent build mode: {s}\n", .{mode});

    // In tests, usually run in Debug mode
    // But can be overridden with -Doptimize=ReleaseSafe etc.
    try testing.expect(mode.len > 0);
}
```

The `builtin.mode` constant is available at compile time, allowing code to adapt to the build configuration.

### Integer Overflow Detection

In Debug and ReleaseSafe modes, integer overflow causes a panic:

```zig
// Integer overflow is caught in Debug and ReleaseSafe
fn wouldOverflowInSafeMode() bool {
    // In Debug/ReleaseSafe: would panic with "integer overflow"
    // In ReleaseFast/ReleaseSmall: would wrap to 0
    // We don't actually trigger overflow in tests (it would panic)
    return builtin.mode == .Debug or builtin.mode == .ReleaseSafe;
}

test "integer overflow detection" {
    const has_checks = wouldOverflowInSafeMode();

    if (has_checks) {
        // In these modes, x + 1 where x = 255 would panic
        std.debug.print("\nOverflow checking is enabled\n", .{});
    } else {
        // In release modes without safety, overflow wraps
        std.debug.print("\nOverflow checking is disabled (wraps)\n", .{});
    }

    try testing.expect(true);
}
```

In Debug and ReleaseSafe, operations like `x + 1` on a maxed-out integer will panic. In ReleaseFast and ReleaseSmall, the value wraps around (undefined behavior).

### Discussion

### Intentional Wrapping with Special Operators

When overflow is intentional, use wrapping operators:

```zig
// Use wrapping operators when overflow is intentional
fn intentionalWrapping() u8 {
    var x: u8 = 255;
    x +%= 1; // Wrapping add: always wraps, never panics
    return x;
}

fn wrappingMultiply(a: u16, b: u16) u16 {
    return a *% b; // Wrapping multiply
}

test "intentional wrapping" {
    const wrapped = intentionalWrapping();
    try testing.expectEqual(@as(u8, 0), wrapped);

    const product = wrappingMultiply(300, 300);
    // 300 * 300 = 90000, wraps to 24464 for u16 (max 65535)
    try testing.expectEqual(@as(u16, 24464), product);
}
```

Wrapping operators (`+%`, `-%`, `*%`, `+%=`) wrap in all build modes, making the behavior explicit and predictable.

### Saturating Arithmetic

Saturating operators clamp to minimum or maximum values instead of wrapping:

```zig
// Saturating arithmetic clamps to min/max instead of wrapping
fn saturatingAdd(a: u8, b: u8) u8 {
    return a +| b; // Saturating add
}

fn saturatingSubtract(a: u8, b: u8) u8 {
    return a -| b; // Saturating subtract
}

test "saturating arithmetic" {
    try testing.expectEqual(@as(u8, 255), saturatingAdd(200, 100));
    try testing.expectEqual(@as(u8, 255), saturatingAdd(255, 1));

    try testing.expectEqual(@as(u8, 0), saturatingSubtract(10, 20));
    try testing.expectEqual(@as(u8, 0), saturatingSubtract(0, 1));
}
```

Use saturating operators (`+|`, `-|`) when you want to prevent overflow without wrapping or panicking.

### Array Bounds Checking

Array access is bounds-checked in Debug and ReleaseSafe:

```zig
// Array bounds checking is active in Debug and ReleaseSafe
fn accessArray(index: usize) !i32 {
    const array = [_]i32{ 1, 2, 3, 4, 5 };

    // Bounds check happens at runtime in Debug/ReleaseSafe
    // Skipped in ReleaseFast/ReleaseSmall for performance
    if (index >= array.len) {
        return error.OutOfBounds;
    }

    return array[index];
}

test "bounds checking" {
    const valid = try accessArray(2);
    try testing.expectEqual(@as(i32, 3), valid);

    const invalid = accessArray(10);
    try testing.expectError(error.OutOfBounds, invalid);
}
```

Accessing an array out of bounds panics in safe modes. Return an error instead for explicit handling.

### Null Pointer Safety

Optionals prevent null pointer dereference:

```zig
// Null pointer dereference is caught in Debug/ReleaseSafe
fn dereferenceOptional(ptr: ?*i32) !i32 {
    // Using orelse handles null safely
    const value = ptr orelse return error.NullPointer;
    return value.*;
}

test "null pointer safety" {
    var value: i32 = 42;
    const valid = try dereferenceOptional(&value);
    try testing.expectEqual(@as(i32, 42), valid);

    const invalid = dereferenceOptional(null);
    try testing.expectError(error.NullPointer, invalid);
}
```

The `?*T` type represents an optional pointer. Use `orelse` to handle the null case explicitly.

### Unreachable Code Paths

Mark code paths that should never execute:

```zig
// Mark code paths that should never execute
fn dividePositive(a: u32, b: u32) u32 {
    if (b == 0) {
        unreachable; // Tells compiler this never happens
    }
    return a / b;
}

fn getSign(x: i32) []const u8 {
    if (x > 0) return "positive";
    if (x < 0) return "negative";
    if (x == 0) return "zero";
    unreachable; // All cases covered
}

test "unreachable marker" {
    try testing.expectEqual(@as(u32, 5), dividePositive(10, 2));

    try testing.expectEqualStrings("positive", getSign(10));
    try testing.expectEqualStrings("negative", getSign(-5));
    try testing.expectEqualStrings("zero", getSign(0));
}
```

The `unreachable` keyword tells the compiler a code path is impossible. In Debug and ReleaseSafe, hitting `unreachable` panics. In release modes, it's undefined behavior (but enables optimizations).

### Fine-Grained Runtime Safety Control

Use `@setRuntimeSafety` for scoped control:

```zig
// Control safety checks with @setRuntimeSafety
fn unsafeButFast(arr: []i32) i32 {
    // Disable safety checks for this scope
    @setRuntimeSafety(false);

    var sum: i32 = 0;
    for (arr) |val| {
        sum += val; // No overflow check
    }
    return sum;
}

fn safeVersion(arr: []i32) i32 {
    @setRuntimeSafety(true);

    var sum: i32 = 0;
    for (arr) |val| {
        sum += val; // Overflow checked even in release modes
    }
    return sum;
}

test "runtime safety control" {
    var numbers = [_]i32{ 1, 2, 3, 4, 5 };

    const unsafe_sum = unsafeButFast(&numbers);
    const safe_sum = safeVersion(&numbers);

    try testing.expectEqual(unsafe_sum, safe_sum);
    try testing.expectEqual(@as(i32, 15), safe_sum);
}
```

Use `@setRuntimeSafety(false)` in performance-critical hot loops after validation. Use `@setRuntimeSafety(true)` to enforce checks even in release builds.

### Debug Assertions

Use `std.debug.assert` for development-only checks:

```zig
// Use std.debug.assert for development-time checks
fn processValidInput(value: i32) i32 {
    // Active in Debug, stripped in all release modes
    std.debug.assert(value >= 0);
    std.debug.assert(value < 1000);

    return value * 2;
}

test "assertion checks" {
    const result = processValidInput(10);
    try testing.expectEqual(@as(i32, 20), result);

    // In Debug mode, this would panic:
    // processValidInput(-5);  // assertion failure
    // In release modes, assertions are compiled out
}
```

Debug assertions are completely removed from release builds, making them zero-cost for invariant checking during development.

### Explicit Overflow Detection

Use `@addWithOverflow` and `@mulWithOverflow` for explicit handling:

```zig
// Use @addWithOverflow and friends for explicit overflow handling
fn addWithOverflowCheck(a: u32, b: u32) !u32 {
    const result = @addWithOverflow(a, b);

    if (result[1] != 0) {
        return error.Overflow;
    }

    return result[0];
}

fn multiplyChecked(a: u16, b: u16) !u16 {
    const result = @mulWithOverflow(a, b);

    if (result[1] != 0) {
        return error.Overflow;
    }

    return result[0];
}

test "checked arithmetic" {
    const sum = try addWithOverflowCheck(100, 200);
    try testing.expectEqual(@as(u32, 300), sum);

    const overflow = addWithOverflowCheck(4_000_000_000, 1_000_000_000);
    try testing.expectError(error.Overflow, overflow);

    const product = try multiplyChecked(100, 200);
    try testing.expectEqual(@as(u16, 20000), product);

    const mul_overflow = multiplyChecked(300, 300);
    try testing.expectError(error.Overflow, mul_overflow);
}
```

These builtins return a tuple `[2]T` where `[0]` is the result and `[1]` is 1 if overflow occurred, 0 otherwise.

### Division by Zero

Division by zero is caught in Debug and ReleaseSafe:

```zig
// Division by zero is caught in Debug/ReleaseSafe
fn safeDivide(a: i32, b: i32) !i32 {
    if (b == 0) {
        return error.DivisionByZero;
    }
    return @divTrunc(a, b);
}

test "division by zero protection" {
    const result = try safeDivide(10, 2);
    try testing.expectEqual(@as(i32, 5), result);

    const div_error = safeDivide(10, 0);
    try testing.expectError(error.DivisionByZero, div_error);
}
```

Always check for division by zero explicitly. In ReleaseFast and ReleaseSmall, dividing by zero is undefined behavior.

### Build Mode Characteristics

Each build mode optimizes for different goals:

| Mode | Safety Checks | Optimized | Size Optimized | Use Case |
|------|--------------|-----------|----------------|----------|
| **Debug** | Yes | No | No | Development, debugging |
| **ReleaseSafe** | Yes | Yes | No | Production default |
| **ReleaseFast** | No | Yes | No | Performance-critical |
| **ReleaseSmall** | No | Yes | Yes | Embedded systems |

**Debug**: Maximum safety, slow execution, large binaries
**ReleaseSafe**: Best default for production (safety + speed)
**ReleaseFast**: Maximum speed, no safety guarantees
**ReleaseSmall**: Minimum size, no safety guarantees

### When to Use Each Mode

**Development and Testing:**
- Use **Debug** for development and initial testing
- Catches bugs early with full safety checks
- Slower execution helps identify performance issues

**Production:**
- Use **ReleaseSafe** as the default for production
- Maintains safety checks with optimized code
- Best balance for most applications

**Performance-Critical:**
- Use **ReleaseFast** for hot paths after thorough testing
- Games, scientific computing, high-frequency trading
- Only after profiling shows safety checks are bottlenecks

**Resource-Constrained:**
- Use **ReleaseSmall** for embedded systems
- Microcontrollers, bootloaders, minimal environments
- When binary size matters more than speed

### Optimization Impact

Different modes produce different code:

```zig
// Different build modes optimize differently
fn computeHeavy() u64 {
    var result: u64 = 1;
    var i: u64 = 1;
    while (i <= 10) : (i += 1) {
        result *= i;
    }
    return result;
}

test "optimization behavior" {
    const factorial = computeHeavy();
    try testing.expectEqual(@as(u64, 3628800), factorial);

    // Debug: No optimizations, full safety
    // ReleaseSafe: Optimized, full safety
    // ReleaseFast: Optimized, safety disabled (fastest)
    // ReleaseSmall: Size-optimized, safety disabled (smallest)
}
```

In Debug, the loop executes as written. In release modes, the compiler may unroll the loop, inline functions, or compute the factorial at compile time.

### Safety Recommendations

Follow these guidelines for safe code:

1. **Default to ReleaseSafe** for production builds
2. **Use explicit operators** for wrapping (`+%`) and saturating (`+|`) arithmetic
3. **Check for errors** instead of relying on panics (division by zero, bounds)
4. **Use debug assertions** for development-time invariants
5. **Profile before disabling safety** - only use ReleaseFast when proven necessary
6. **Use @setRuntimeSafety sparingly** - only in validated hot paths
7. **Mark impossible paths** with `unreachable` for optimization hints

### Testing Across Build Modes

Test your code in multiple build modes:

```bash
# Debug mode (default for zig test)
zig test recipe_1_5.zig

# ReleaseSafe mode
zig test recipe_1_5.zig -Doptimize=ReleaseSafe

# ReleaseFast mode
zig test recipe_1_5.zig -Doptimize=ReleaseFast

# ReleaseSmall mode
zig test recipe_1_5.zig -Doptimize=ReleaseSmall
```

Run tests in both Debug and ReleaseSafe to catch bugs that only appear with optimizations.

### Common Pitfalls

**Relying on panics in production:**
```zig
// Don't do this in production code:
fn badDivide(a: i32, b: i32) i32 {
    return a / b;  // Panics on b == 0 in safe modes
}

// Do this instead:
fn goodDivide(a: i32, b: i32) !i32 {
    if (b == 0) return error.DivisionByZero;
    return @divTrunc(a, b);
}
```

**Disabling safety prematurely:**
```zig
// Don't disable safety without profiling:
@setRuntimeSafety(false);  // Did you measure this?

// Profile first, then optimize hot paths only
```

**Assuming overflow wraps:**
```zig
// Wrong: assumes wrapping behavior
var x: u8 = 255;
x += 1;  // Panics in Debug/ReleaseSafe

// Right: explicit wrapping
var x: u8 = 255;
x +%= 1;  // Always wraps to 0
```

### Memory Safety

Zig's safety features extend beyond arithmetic:

- **No use-after-free**: Compile-time lifetime analysis
- **No double-free**: Single ownership or explicit reference counting
- **No null dereferences**: Optional types enforce handling
- **No buffer overflows**: Bounds checking in safe modes
- **No uninitialized reads**: Compiler enforces initialization

These guarantees make Zig suitable for systems programming without sacrificing safety.

### See Also

- Recipe 0.11: Optionals, Errors, and Resource Cleanup
- Recipe 1.1: Writing Idiomatic Zig Code
- Recipe 14.2: Using different build modes

---
