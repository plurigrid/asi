# C Interoperability Recipes

*7 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [15.1](#recipe-15-1) | Accessing C code from Zig | intermediate |
| [15.2](#recipe-15-2) | Writing a Zig library callable from C | intermediate |
| [15.3](#recipe-15-3) | Passing arrays between C and Zig | intermediate |
| [15.4](#recipe-15-4) | Managing opaque types in C extensions | intermediate |
| [15.5](#recipe-15-5) | Wrapping existing C libraries | intermediate |
| [15.6](#recipe-15-6) | Passing NULL-terminated strings to C functions | intermediate |
| [15.7](#recipe-15-7) | Calling C functions with variadic arguments | intermediate |

---

## Recipe 15.1: Accessing C code from Zig {#recipe-15-1}

**Tags:** allocators, c-interop, error-handling, memory, pointers, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/15-c-interoperability/recipe_15_1.zig`

### Problem

You need to call C library functions from your Zig code, such as using standard C library functions like `printf`, `sqrt`, or `strlen`.

### Solution

Zig provides `@cImport` to import C headers directly. This builtin function translates C declarations into Zig code at compile time, allowing you to call C functions naturally.

Here's how to import C headers:

```zig
// Import C standard library headers
const c = @cImport({
    @cInclude("stdio.h");
    @cInclude("math.h");
    @cInclude("string.h");
});
```

Once imported, you can call C functions directly:

```zig
test "calling C printf" {
    const result = c.printf("Hello from Zig via C printf!\n");
    try testing.expect(result > 0);
}
```

### Discussion

### Basic C Import

The `@cImport` function takes a compile-time expression that can include multiple `@cInclude` directives. Each directive imports a C header file, making its functions, types, and constants available to your Zig code.

When you compile code that uses `@cImport`, you need to link with the C library using the `-lc` flag:

```bash
zig test recipe_15_1.zig -lc
```

### Using C Math Functions

C standard library functions work seamlessly:

```zig
test "calling C math functions" {
    const result = c.sqrt(16.0);
    try testing.expectApproxEqAbs(4.0, result, 0.001);

    const power = c.pow(2.0, 8.0);
    try testing.expectApproxEqAbs(256.0, power, 0.001);

    const sine = c.sin(0.0);
    try testing.expectApproxEqAbs(0.0, sine, 0.001);
}
```

### C Type Primitives

Zig provides C-compatible types that guarantee the correct ABI:

```zig
test "using C type primitives" {
    const x: c_int = 42;
    const y: c_long = 1234567890;
    const z: c_char = 'A';

    try testing.expectEqual(@as(c_int, 42), x);
    try testing.expectEqual(@as(c_long, 1234567890), y);
    try testing.expectEqual(@as(c_char, 'A'), z);
}
```

Available C types include:
- `c_char`, `c_short`, `c_int`, `c_long`, `c_longlong`
- `c_ushort`, `c_uint`, `c_ulong`, `c_ulonglong`
- `c_longdouble`

For C's `void*`, use `?*anyopaque` in Zig.

### Working with C Strings

C functions that take strings work with Zig's string pointers:

```zig
test "calling C strlen" {
    const str = "Hello, World!";
    const len = c.strlen(str.ptr);
    try testing.expectEqual(@as(usize, 13), len);
}
```

### Using Preprocessor Defines

You can set C preprocessor macros using `@cDefine`:

```zig
// Using @cDefine to set preprocessor macros
const c_with_defines = @cImport({
    @cDefine("_GNU_SOURCE", "1");
    @cInclude("stdio.h");
});

test "using @cDefine" {
    // The define affects how headers are processed
    _ = c_with_defines.printf("Testing with defines\n");
}
```

### Conditional Imports

Import different headers based on compile-time conditions:

```zig
// Conditional imports based on compile-time conditions
const builtin = @import("builtin");

const c_platform = @cImport({
    if (builtin.os.tag == .windows) {
        @cInclude("windows.h");
    } else {
        @cInclude("unistd.h");
    }
    @cInclude("stdlib.h");
});

test "conditional C imports" {
    // Test that platform-specific imports work
    _ = c_platform;
}
```

This is useful for cross-platform code where different operating systems require different headers.

### Accessing C Constants

C preprocessor constants and definitions are available:

```zig
test "using C constants" {
    // Access C preprocessor constants
    const eof = c.EOF;
    try testing.expect(eof < 0);

    // Many C constants are available
    const null_char = c.NULL;
    try testing.expectEqual(@as(?*anyopaque, null), null_char);
}
```

### Working with C Buffers

You can pass Zig buffers to C functions that write data:

```zig
test "using Zig allocator with C functions" {
    var buffer: [100]u8 = undefined;

    // sprintf is a C function that writes to a buffer
    const result = c.sprintf(&buffer, "Number: %d, String: %s", @as(c_int, 42), "test");
    try testing.expect(result > 0);

    // Verify the output
    const output = buffer[0..@as(usize, @intCast(result))];
    try testing.expect(std.mem.eql(u8, output, "Number: 42, String: test"));
}
```

Note that variadic C functions require explicit type casts for literals.

### Multiple Related Headers

Import multiple headers in a single `@cImport` block:

```zig
// Import multiple related headers
const c_time = @cImport({
    @cInclude("time.h");
    @cInclude("stdlib.h");
});

test "working with C time functions" {
    const timestamp = c_time.time(null);
    try testing.expect(timestamp > 0);

    // C functions can be called naturally from Zig
    const tm_ptr = c_time.localtime(&timestamp);
    try testing.expect(tm_ptr != null);
}
```

### Error Handling

C functions often use return codes or NULL pointers to indicate errors. Handle these explicitly in Zig:

```zig
test "error handling with C functions" {
    // C functions that can fail often return error codes or NULL
    // We need to handle these cases explicitly in Zig

    const invalid_ptr: ?*c.FILE = null;
    try testing.expectEqual(@as(?*c.FILE, null), invalid_ptr);

    // Many C functions return -1 or NULL on error
    // Zig's type system helps us handle these cases safely
}
```

### Void Pointers

C's `void*` maps to `?*anyopaque` in Zig:

```zig
test "working with C void pointers" {
    // C void* is represented as ?*anyopaque in Zig
    var value: c_int = 42;
    const void_ptr: ?*anyopaque = @ptrCast(&value);

    // Cast back to the original type
    const int_ptr: *c_int = @ptrCast(@alignCast(void_ptr.?));
    try testing.expectEqual(@as(c_int, 42), int_ptr.*);
}
```

### Important Considerations

1. **Linking**: Always use `-lc` when compiling code that uses C library functions
2. **Type Safety**: Use C type primitives (`c_int`, `c_long`, etc.) for ABI compatibility
3. **Variadic Functions**: Cast integer and float literals explicitly when calling variadic C functions
4. **Null Safety**: C pointers are nullable; handle NULL cases explicitly
5. **Translation Caching**: Zig caches C translations for faster subsequent builds

### Alternative: zig translate-c

For more control, you can use the `zig translate-c` CLI tool to generate Zig bindings from C headers, then edit the generated code manually.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_cimport
// Import C standard library headers
const c = @cImport({
    @cInclude("stdio.h");
    @cInclude("math.h");
    @cInclude("string.h");
});
// ANCHOR_END: basic_cimport

// ANCHOR: calling_printf
test "calling C printf" {
    const result = c.printf("Hello from Zig via C printf!\n");
    try testing.expect(result > 0);
}
// ANCHOR_END: calling_printf

// ANCHOR: calling_math
test "calling C math functions" {
    const result = c.sqrt(16.0);
    try testing.expectApproxEqAbs(4.0, result, 0.001);

    const power = c.pow(2.0, 8.0);
    try testing.expectApproxEqAbs(256.0, power, 0.001);

    const sine = c.sin(0.0);
    try testing.expectApproxEqAbs(0.0, sine, 0.001);
}
// ANCHOR_END: calling_math

// ANCHOR: c_types
test "using C type primitives" {
    const x: c_int = 42;
    const y: c_long = 1234567890;
    const z: c_char = 'A';

    try testing.expectEqual(@as(c_int, 42), x);
    try testing.expectEqual(@as(c_long, 1234567890), y);
    try testing.expectEqual(@as(c_char, 'A'), z);
}
// ANCHOR_END: c_types

// ANCHOR: strlen_example
test "calling C strlen" {
    const str = "Hello, World!";
    const len = c.strlen(str.ptr);
    try testing.expectEqual(@as(usize, 13), len);
}
// ANCHOR_END: strlen_example

// ANCHOR: cdefine_example
// Using @cDefine to set preprocessor macros
const c_with_defines = @cImport({
    @cDefine("_GNU_SOURCE", "1");
    @cInclude("stdio.h");
});

test "using @cDefine" {
    // The define affects how headers are processed
    _ = c_with_defines.printf("Testing with defines\n");
}
// ANCHOR_END: cdefine_example

// ANCHOR: conditional_import
// Conditional imports based on compile-time conditions
const builtin = @import("builtin");

const c_platform = @cImport({
    if (builtin.os.tag == .windows) {
        @cInclude("windows.h");
    } else {
        @cInclude("unistd.h");
    }
    @cInclude("stdlib.h");
});

test "conditional C imports" {
    // Test that platform-specific imports work
    _ = c_platform;
}
// ANCHOR_END: conditional_import

// ANCHOR: c_constants
test "using C constants" {
    // Access C preprocessor constants
    const eof = c.EOF;
    try testing.expect(eof < 0);

    // Many C constants are available
    const null_char = c.NULL;
    try testing.expectEqual(@as(?*anyopaque, null), null_char);
}
// ANCHOR_END: c_constants

// ANCHOR: allocator_with_c
test "using Zig allocator with C functions" {
    var buffer: [100]u8 = undefined;

    // sprintf is a C function that writes to a buffer
    const result = c.sprintf(&buffer, "Number: %d, String: %s", @as(c_int, 42), "test");
    try testing.expect(result > 0);

    // Verify the output
    const output = buffer[0..@as(usize, @intCast(result))];
    try testing.expect(std.mem.eql(u8, output, "Number: 42, String: test"));
}
// ANCHOR_END: allocator_with_c

// ANCHOR: multiple_headers
// Import multiple related headers
const c_time = @cImport({
    @cInclude("time.h");
    @cInclude("stdlib.h");
});

test "working with C time functions" {
    const timestamp = c_time.time(null);
    try testing.expect(timestamp > 0);

    // C functions can be called naturally from Zig
    const tm_ptr = c_time.localtime(&timestamp);
    try testing.expect(tm_ptr != null);
}
// ANCHOR_END: multiple_headers

// ANCHOR: error_handling
test "error handling with C functions" {
    // C functions that can fail often return error codes or NULL
    // We need to handle these cases explicitly in Zig

    const invalid_ptr: ?*c.FILE = null;
    try testing.expectEqual(@as(?*c.FILE, null), invalid_ptr);

    // Many C functions return -1 or NULL on error
    // Zig's type system helps us handle these cases safely
}
// ANCHOR_END: error_handling

// ANCHOR: c_void_pointer
test "working with C void pointers" {
    // C void* is represented as ?*anyopaque in Zig
    var value: c_int = 42;
    const void_ptr: ?*anyopaque = @ptrCast(&value);

    // Cast back to the original type
    const int_ptr: *c_int = @ptrCast(@alignCast(void_ptr.?));
    try testing.expectEqual(@as(c_int, 42), int_ptr.*);
}
// ANCHOR_END: c_void_pointer
```

### See Also

- Recipe 15.2: Writing a Zig Library Callable from C
- Recipe 15.5: Wrapping Existing C Libraries
- Recipe 15.8: Passing NULL
- Recipe 15.10: Calling C Functions with Variadic Arguments

---

## Recipe 15.2: Writing a Zig library callable from C {#recipe-15-2}

**Tags:** allocators, c-interop, concurrency, error-handling, memory, pointers, testing, threading
**Difficulty:** intermediate
**Code:** `code/04-specialized/15-c-interoperability/recipe_15_2.zig`

### Problem

You want to create a library in Zig that can be called from C code, exposing Zig functions through a C-compatible API.

### Solution

Use the `export` keyword to make Zig functions accessible from C. Exported functions follow the C ABI and can be called from any language that supports C linkage.

Here's a basic exported function:

```zig
// Export a simple function callable from C
export fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "basic exported function" {
    const result = add(5, 7);
    try testing.expectEqual(@as(i32, 12), result);
}
```

Build as a library:

```bash
zig build-lib recipe_15_2.zig        # Static library
zig build-lib recipe_15_2.zig -dynamic   # Shared library
```

### Discussion

### Exporting Functions

The `export` keyword makes a function part of the library's public API with C linkage. The function follows the C calling convention and can be called from C code.

For better C compatibility, use C types:

```zig
// Use C types for better compatibility
export fn multiply(a: c_int, b: c_int) c_int {
    return a * b;
}

test "exported function with C types" {
    const result = multiply(6, 7);
    try testing.expectEqual(@as(c_int, 42), result);
}
```

### Exporting Struct-Based APIs

Create structs with C-compatible layout using `extern struct`:

```zig
// Struct with C ABI for use in exported functions
pub const Point = extern struct {
    x: c_int,
    y: c_int,
};

export fn create_point(x: c_int, y: c_int) Point {
    return Point{ .x = x, .y = y };
}

export fn point_distance_squared(p: Point) c_int {
    return p.x * p.x + p.y * p.y;
}

test "exported struct operations" {
    const p = create_point(3, 4);
    try testing.expectEqual(@as(c_int, 3), p.x);
    try testing.expectEqual(@as(c_int, 4), p.y);

    const dist_sq = point_distance_squared(p);
    try testing.expectEqual(@as(c_int, 25), dist_sq);
}
```

The `extern struct` keyword ensures the struct uses C memory layout, making it safe to pass across the C/Zig boundary.

### Array Operations

Export functions that work with array pointers for C compatibility:

```zig
// Export function that works with array pointers
export fn sum_array(arr: [*]const c_int, len: usize) c_int {
    var total: c_int = 0;
    for (0..len) |i| {
        total += arr[i];
    }
    return total;
}

test "exported array operation" {
    const numbers = [_]c_int{ 1, 2, 3, 4, 5 };
    const result = sum_array(&numbers, numbers.len);
    try testing.expectEqual(@as(c_int, 15), result);
}
```

Use `[*]T` for many-item pointers and pass the length separately, as C does not track array sizes.

### String Operations

Work with C-style NULL-terminated strings using `[*:0]const u8`:

```zig
// Export function that works with C strings
export fn string_length(str: [*:0]const u8) usize {
    var len: usize = 0;
    while (str[len] != 0) {
        len += 1;
    }
    return len;
}

test "exported string operation" {
    const text = "Hello, World!";
    const len = string_length(text.ptr);
    try testing.expectEqual(@as(usize, 13), len);
}
```

The `:0` sentinel in the type indicates a NULL-terminated string.

### Error Handling

Since Zig's error unions don't translate to C, use return codes:

```zig
// Export function that returns error codes
export fn safe_divide(a: c_int, b: c_int, result: *c_int) c_int {
    if (b == 0) {
        return -1; // Error code
    }
    result.* = @divTrunc(a, b);
    return 0; // Success
}

test "exported function with error handling" {
    var result: c_int = 0;

    // Successful division
    var status = safe_divide(10, 2, &result);
    try testing.expectEqual(@as(c_int, 0), status);
    try testing.expectEqual(@as(c_int, 5), result);

    // Division by zero
    status = safe_divide(10, 0, &result);
    try testing.expectEqual(@as(c_int, -1), status);
}
```

Common patterns:
- Return 0 for success, negative values for errors
- Use output parameters for return values
- Document error codes clearly

### Opaque Types for Encapsulation

Hide implementation details using opaque pointers:

```zig
// Export opaque type for encapsulation
const Counter = struct {
    value: c_int,
};

export fn counter_create() ?*Counter {
    const allocator = std.heap.c_allocator;
    const counter = allocator.create(Counter) catch return null;
    counter.* = Counter{ .value = 0 };
    return counter;
}

export fn counter_increment(counter: ?*Counter) void {
    if (counter) |c| {
        c.value += 1;
    }
}

export fn counter_get_value(counter: ?*const Counter) c_int {
    if (counter) |c| {
        return c.value;
    }
    return -1;
}

export fn counter_destroy(counter: ?*Counter) void {
    if (counter) |c| {
        const allocator = std.heap.c_allocator;
        allocator.destroy(c);
    }
}

test "exported opaque type" {
    const counter = counter_create();
    try testing.expect(counter != null);

    try testing.expectEqual(@as(c_int, 0), counter_get_value(counter));

    counter_increment(counter);
    counter_increment(counter);
    try testing.expectEqual(@as(c_int, 2), counter_get_value(counter));

    counter_destroy(counter);
}
```

This pattern provides:
- Encapsulation of internal state
- Memory safety through controlled allocation/deallocation
- ABI stability (C code doesn't depend on struct layout)

### Callback Functions

Accept function pointers from C code:

```zig
// Export function that takes a callback
const CallbackFn = *const fn (c_int) callconv(.c) void;

var callback_result: c_int = 0;

export fn process_with_callback(value: c_int, callback: CallbackFn) void {
    callback(value * 2);
}

fn test_callback(value: c_int) callconv(.c) void {
    callback_result = value;
}

test "exported function with callback" {
    callback_result = 0;
    process_with_callback(21, test_callback);
    try testing.expectEqual(@as(c_int, 42), callback_result);
}
```

The `callconv(.c)` specifies C calling convention for the callback.

### Buffer Modifications

Export functions that modify buffers in place:

```zig
// Export function that modifies a buffer
export fn to_uppercase(buffer: [*]u8, len: usize) void {
    for (0..len) |i| {
        if (buffer[i] >= 'a' and buffer[i] <= 'z') {
            buffer[i] -= 32;
        }
    }
}

test "exported buffer modification" {
    var text = "hello world".*;
    to_uppercase(&text, text.len);
    try testing.expect(std.mem.eql(u8, &text, "HELLO WORLD"));
}
```

### Exporting Global Variables

Variables can also be exported:

```zig
// Export global variables
export var global_counter: c_int = 0;

export fn increment_global() c_int {
    global_counter += 1;
    return global_counter;
}

test "exported global variable" {
    global_counter = 0;

    const v1 = increment_global();
    try testing.expectEqual(@as(c_int, 1), v1);

    const v2 = increment_global();
    try testing.expectEqual(@as(c_int, 2), v2);

    try testing.expectEqual(@as(c_int, 2), global_counter);
}
```

Be cautious with global state in multi-threaded environments.

### Building and Using the Library

To build a static library:

```bash
zig build-lib mylib.zig
```

This creates `libmylib.a` (or `mylib.lib` on Windows).

To build a shared/dynamic library:

```bash
zig build-lib mylib.zig -dynamic
```

This creates `libmylib.so` (Linux), `libmylib.dylib` (macOS), or `mylib.dll` (Windows).

### Using from C

From C code, declare the functions:

```c
// mylib.h
#include <stdint.h>

int32_t add(int32_t a, int32_t b);
int32_t multiply(int32_t a, int32_t b);
```

Then compile and link:

```bash
gcc main.c -L. -lmylib -o main
```

### Important Considerations

1. **C ABI Compatibility**: Use C types (`c_int`, `c_long`, etc.) for guaranteed compatibility
2. **Memory Management**: Document who owns and frees memory
3. **NULL Safety**: Always check for NULL pointers from C code
4. **Thread Safety**: Make exported functions thread-safe if they'll be called from multiple threads
5. **Error Handling**: Use return codes, not Zig error unions
6. **Struct Layout**: Use `extern struct` for C-compatible layout
7. **String Handling**: Use sentinel-terminated pointers `[*:0]u8` for C strings

### Header Generation

Zig can generate C headers automatically. In your build.zig:

```zig
const lib = b.addLibrary(.{
    .name = "mylib",
    .root_source_file = b.path("mylib.zig"),
});
lib.emit_h = true;  // Generate header file
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_export
// Export a simple function callable from C
export fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "basic exported function" {
    const result = add(5, 7);
    try testing.expectEqual(@as(i32, 12), result);
}
// ANCHOR_END: basic_export

// ANCHOR: export_with_c_types
// Use C types for better compatibility
export fn multiply(a: c_int, b: c_int) c_int {
    return a * b;
}

test "exported function with C types" {
    const result = multiply(6, 7);
    try testing.expectEqual(@as(c_int, 42), result);
}
// ANCHOR_END: export_with_c_types

// ANCHOR: export_struct
// Struct with C ABI for use in exported functions
pub const Point = extern struct {
    x: c_int,
    y: c_int,
};

export fn create_point(x: c_int, y: c_int) Point {
    return Point{ .x = x, .y = y };
}

export fn point_distance_squared(p: Point) c_int {
    return p.x * p.x + p.y * p.y;
}

test "exported struct operations" {
    const p = create_point(3, 4);
    try testing.expectEqual(@as(c_int, 3), p.x);
    try testing.expectEqual(@as(c_int, 4), p.y);

    const dist_sq = point_distance_squared(p);
    try testing.expectEqual(@as(c_int, 25), dist_sq);
}
// ANCHOR_END: export_struct

// ANCHOR: export_array_operations
// Export function that works with array pointers
export fn sum_array(arr: [*]const c_int, len: usize) c_int {
    var total: c_int = 0;
    for (0..len) |i| {
        total += arr[i];
    }
    return total;
}

test "exported array operation" {
    const numbers = [_]c_int{ 1, 2, 3, 4, 5 };
    const result = sum_array(&numbers, numbers.len);
    try testing.expectEqual(@as(c_int, 15), result);
}
// ANCHOR_END: export_array_operations

// ANCHOR: export_string_operations
// Export function that works with C strings
export fn string_length(str: [*:0]const u8) usize {
    var len: usize = 0;
    while (str[len] != 0) {
        len += 1;
    }
    return len;
}

test "exported string operation" {
    const text = "Hello, World!";
    const len = string_length(text.ptr);
    try testing.expectEqual(@as(usize, 13), len);
}
// ANCHOR_END: export_string_operations

// ANCHOR: export_error_handling
// Export function that returns error codes
export fn safe_divide(a: c_int, b: c_int, result: *c_int) c_int {
    if (b == 0) {
        return -1; // Error code
    }
    result.* = @divTrunc(a, b);
    return 0; // Success
}

test "exported function with error handling" {
    var result: c_int = 0;

    // Successful division
    var status = safe_divide(10, 2, &result);
    try testing.expectEqual(@as(c_int, 0), status);
    try testing.expectEqual(@as(c_int, 5), result);

    // Division by zero
    status = safe_divide(10, 0, &result);
    try testing.expectEqual(@as(c_int, -1), status);
}
// ANCHOR_END: export_error_handling

// ANCHOR: export_opaque_type
// Export opaque type for encapsulation
const Counter = struct {
    value: c_int,
};

export fn counter_create() ?*Counter {
    const allocator = std.heap.c_allocator;
    const counter = allocator.create(Counter) catch return null;
    counter.* = Counter{ .value = 0 };
    return counter;
}

export fn counter_increment(counter: ?*Counter) void {
    if (counter) |c| {
        c.value += 1;
    }
}

export fn counter_get_value(counter: ?*const Counter) c_int {
    if (counter) |c| {
        return c.value;
    }
    return -1;
}

export fn counter_destroy(counter: ?*Counter) void {
    if (counter) |c| {
        const allocator = std.heap.c_allocator;
        allocator.destroy(c);
    }
}

test "exported opaque type" {
    const counter = counter_create();
    try testing.expect(counter != null);

    try testing.expectEqual(@as(c_int, 0), counter_get_value(counter));

    counter_increment(counter);
    counter_increment(counter);
    try testing.expectEqual(@as(c_int, 2), counter_get_value(counter));

    counter_destroy(counter);
}
// ANCHOR_END: export_opaque_type

// ANCHOR: export_callback
// Export function that takes a callback
const CallbackFn = *const fn (c_int) callconv(.c) void;

var callback_result: c_int = 0;

export fn process_with_callback(value: c_int, callback: CallbackFn) void {
    callback(value * 2);
}

fn test_callback(value: c_int) callconv(.c) void {
    callback_result = value;
}

test "exported function with callback" {
    callback_result = 0;
    process_with_callback(21, test_callback);
    try testing.expectEqual(@as(c_int, 42), callback_result);
}
// ANCHOR_END: export_callback

// ANCHOR: export_buffer_operations
// Export function that modifies a buffer
export fn to_uppercase(buffer: [*]u8, len: usize) void {
    for (0..len) |i| {
        if (buffer[i] >= 'a' and buffer[i] <= 'z') {
            buffer[i] -= 32;
        }
    }
}

test "exported buffer modification" {
    var text = "hello world".*;
    to_uppercase(&text, text.len);
    try testing.expect(std.mem.eql(u8, &text, "HELLO WORLD"));
}
// ANCHOR_END: export_buffer_operations

// ANCHOR: export_variable
// Export global variables
export var global_counter: c_int = 0;

export fn increment_global() c_int {
    global_counter += 1;
    return global_counter;
}

test "exported global variable" {
    global_counter = 0;

    const v1 = increment_global();
    try testing.expectEqual(@as(c_int, 1), v1);

    const v2 = increment_global();
    try testing.expectEqual(@as(c_int, 2), v2);

    try testing.expectEqual(@as(c_int, 2), global_counter);
}
// ANCHOR_END: export_variable
```

### See Also

- Recipe 15.1: Accessing C Code from Zig
- Recipe 15.3: Passing Arrays Between C and Zig
- Recipe 15.6: Calling Zig Functions from C
- Recipe 15.7: Managing Memory Across the C/Zig Boundary

---

## Recipe 15.3: Passing arrays between C and Zig {#recipe-15-3}

**Tags:** allocators, c-interop, memory, pointers, slices, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/15-c-interoperability/recipe_15_3.zig`

### Problem

You need to pass arrays between C and Zig code, handling the differences in how each language represents arrays and pointers.

### Solution

Use many-item pointers (`[*]T`) combined with a length parameter to pass arrays between C and Zig. This matches C's convention of passing arrays as pointers with separate length tracking.

```zig
// Zig function accepting a C array as many-item pointer
export fn sum_integers(arr: [*]const c_int, len: usize) c_int {
    var total: c_int = 0;
    for (0..len) |i| {
        total += arr[i];
    }
    return total;
}

test "passing array to Zig from C" {
    const numbers = [_]c_int{ 10, 20, 30, 40, 50 };
    const result = sum_integers(&numbers, numbers.len);
    try testing.expectEqual(@as(c_int, 150), result);
}
```

### Discussion

### Understanding Pointer Types

Zig has several pointer types for C interop:

- `[*]T` - Many-item pointer (preferred for C arrays)
- `[*c]T` - C pointer (auto-generated from `@cImport`, allows NULL)
- `*T` - Single-item pointer
- `[*:0]T` - Sentinel-terminated pointer (for C strings)

### Modifying C Arrays

Zig functions can modify C arrays in place:

```zig
// Zig function that modifies a C array in place
export fn double_values(arr: [*]c_int, len: usize) void {
    for (0..len) |i| {
        arr[i] *= 2;
    }
}

test "modifying C array from Zig" {
    var numbers = [_]c_int{ 1, 2, 3, 4, 5 };
    double_values(&numbers, numbers.len);

    try testing.expectEqual(@as(c_int, 2), numbers[0]);
    try testing.expectEqual(@as(c_int, 4), numbers[1]);
    try testing.expectEqual(@as(c_int, 6), numbers[2]);
    try testing.expectEqual(@as(c_int, 8), numbers[3]);
    try testing.expectEqual(@as(c_int, 10), numbers[4]);
}
```

### Returning Arrays to C

Use output parameters to return array data to C callers:

```zig
// Allocate and return an array to C
export fn create_range(start: c_int, count: usize, out_arr: [*]c_int) void {
    for (0..count) |i| {
        out_arr[i] = start + @as(c_int, @intCast(i));
    }
}

test "returning array to C" {
    var result: [5]c_int = undefined;
    create_range(10, 5, &result);

    try testing.expectEqual(@as(c_int, 10), result[0]);
    try testing.expectEqual(@as(c_int, 11), result[1]);
    try testing.expectEqual(@as(c_int, 12), result[2]);
    try testing.expectEqual(@as(c_int, 13), result[3]);
    try testing.expectEqual(@as(c_int, 14), result[4]);
}
```

This pattern is safer than returning a pointer, as the caller manages the memory.

### Working with C Pointers

When working with auto-generated bindings, you'll encounter `[*c]T` pointers:

```zig
// Using C pointers ([*c]T) for maximum compatibility
const c = @cImport({
    @cInclude("stdlib.h");
});

export fn process_c_array(arr: [*c]c_int, len: usize) c_int {
    if (arr == null) return -1;

    var max: c_int = arr[0];
    for (1..len) |i| {
        if (arr[i] > max) {
            max = arr[i];
        }
    }
    return max;
}

test "working with C pointers" {
    var numbers = [_]c_int{ 15, 42, 8, 23, 16 };
    const result = process_c_array(&numbers, numbers.len);
    try testing.expectEqual(@as(c_int, 42), result);

    // Test NULL handling
    const null_result = process_c_array(null, 0);
    try testing.expectEqual(@as(c_int, -1), null_result);
}
```

C pointers support NULL checking and coerce to other pointer types.

### Multidimensional Arrays

Handle 2D arrays as arrays of pointers:

```zig
// Working with 2D arrays (arrays of pointers)
export fn sum_2d_array(rows: [*]const [*]const c_int, num_rows: usize, cols_per_row: usize) c_int {
    var total: c_int = 0;
    for (0..num_rows) |i| {
        for (0..cols_per_row) |j| {
            total += rows[i][j];
        }
    }
    return total;
}

test "2D array operations" {
    const row1 = [_]c_int{ 1, 2, 3 };
    const row2 = [_]c_int{ 4, 5, 6 };
    const row3 = [_]c_int{ 7, 8, 9 };

    const rows = [_][*]const c_int{ &row1, &row2, &row3 };
    const result = sum_2d_array(&rows, 3, 3);
    try testing.expectEqual(@as(c_int, 45), result);
}
```

This matches C's convention where a 2D array is an array of row pointers.

### Arrays of Structs

Pass arrays of C-compatible structs using `extern struct`:

```zig
// Passing arrays of structs
pub const Point2D = extern struct {
    x: c_int,
    y: c_int,
};

export fn compute_bounding_box(points: [*]const Point2D, count: usize, min_x: *c_int, min_y: *c_int, max_x: *c_int, max_y: *c_int) void {
    if (count == 0) return;

    min_x.* = points[0].x;
    min_y.* = points[0].y;
    max_x.* = points[0].x;
    max_y.* = points[0].y;

    for (1..count) |i| {
        if (points[i].x < min_x.*) min_x.* = points[i].x;
        if (points[i].y < min_y.*) min_y.* = points[i].y;
        if (points[i].x > max_x.*) max_x.* = points[i].x;
        if (points[i].y > max_y.*) max_y.* = points[i].y;
    }
}

test "array of structs" {
    const points = [_]Point2D{
        .{ .x = 5, .y = 3 },
        .{ .x = 1, .y = 7 },
        .{ .x = 9, .y = 2 },
        .{ .x = 3, .y = 8 },
    };

    var min_x: c_int = undefined;
    var min_y: c_int = undefined;
    var max_x: c_int = undefined;
    var max_y: c_int = undefined;

    compute_bounding_box(&points, points.len, &min_x, &min_y, &max_x, &max_y);

    try testing.expectEqual(@as(c_int, 1), min_x);
    try testing.expectEqual(@as(c_int, 2), min_y);
    try testing.expectEqual(@as(c_int, 9), max_x);
    try testing.expectEqual(@as(c_int, 8), max_y);
}
```

### Converting Slices to C Arrays

Zig slices have `.ptr` and `.len` fields that map naturally to C conventions:

```zig
// Converting Zig slices to C arrays
export fn average_slice(slice_ptr: [*]const c_int, slice_len: usize) f64 {
    if (slice_len == 0) return 0.0;

    var sum: c_int = 0;
    for (0..slice_len) |i| {
        sum += slice_ptr[i];
    }

    return @as(f64, @floatFromInt(sum)) / @as(f64, @floatFromInt(slice_len));
}

test "converting slice to C array" {
    const numbers = [_]c_int{ 10, 20, 30, 40, 50 };
    const slice: []const c_int = &numbers;

    const result = average_slice(slice.ptr, slice.len);
    try testing.expectApproxEqAbs(30.0, result, 0.001);
}
```

### Dynamic Array Allocation

Allocate arrays that C code will use:

```zig
// Allocating arrays for C callers
export fn create_fibonacci(n: usize) ?[*]c_int {
    if (n == 0) return null;

    const allocator = std.heap.c_allocator;
    const arr = allocator.alloc(c_int, n) catch return null;

    if (n >= 1) arr[0] = 0;
    if (n >= 2) arr[1] = 1;

    for (2..n) |i| {
        arr[i] = arr[i - 1] + arr[i - 2];
    }

    return arr.ptr;
}

export fn free_array(arr: ?[*]c_int, len: usize) void {
    if (arr) |a| {
        const allocator = std.heap.c_allocator;
        const slice = a[0..len];
        allocator.free(slice);
    }
}

test "dynamic array allocation" {
    const arr = create_fibonacci(10);
    try testing.expect(arr != null);

    if (arr) |a| {
        try testing.expectEqual(@as(c_int, 0), a[0]);
        try testing.expectEqual(@as(c_int, 1), a[1]);
        try testing.expectEqual(@as(c_int, 1), a[2]);
        try testing.expectEqual(@as(c_int, 2), a[3]);
        try testing.expectEqual(@as(c_int, 3), a[4]);
        try testing.expectEqual(@as(c_int, 5), a[5]);
        try testing.expectEqual(@as(c_int, 8), a[6]);
        try testing.expectEqual(@as(c_int, 13), a[7]);
        try testing.expectEqual(@as(c_int, 21), a[8]);
        try testing.expectEqual(@as(c_int, 34), a[9]);

        free_array(arr, 10);
    }
}
```

Key points:
- Use `std.heap.c_allocator` for C-compatible allocation
- Return the pointer (`arr.ptr`) to C
- Provide a `free` function for C to deallocate
- Always check for allocation failures

### Byte Array Operations

Byte arrays (`[*]u8`) are common for buffers and binary data:

```zig
// Working with byte arrays (useful for buffers)
export fn reverse_bytes(data: [*]u8, len: usize) void {
    var left: usize = 0;
    var right: usize = len - 1;

    while (left < right) {
        const temp = data[left];
        data[left] = data[right];
        data[right] = temp;
        left += 1;
        right -= 1;
    }
}

test "byte array manipulation" {
    var data = "Hello".*;
    reverse_bytes(&data, data.len);
    try testing.expect(std.mem.eql(u8, &data, "olleH"));
}
```

### Safe Array Access

Add bounds checking for safer C APIs:

```zig
// Safe array access with bounds checking
export fn safe_get_element(arr: [*]const c_int, len: usize, index: usize, out_value: *c_int) bool {
    if (index >= len) {
        return false;
    }
    out_value.* = arr[index];
    return true;
}

test "safe array access" {
    const numbers = [_]c_int{ 100, 200, 300, 400 };
    var value: c_int = undefined;

    // Valid access
    const success = safe_get_element(&numbers, numbers.len, 2, &value);
    try testing.expect(success);
    try testing.expectEqual(@as(c_int, 300), value);

    // Out of bounds access
    const failure = safe_get_element(&numbers, numbers.len, 10, &value);
    try testing.expect(!failure);
}
```

Return a boolean to indicate success/failure instead of potentially accessing invalid memory.

### Best Practices

1. **Always pass length**: C doesn't track array sizes, so pass the length explicitly
2. **Use many-item pointers**: Prefer `[*]T` over `[*c]T` when you control the interface
3. **Document ownership**: Clearly specify who allocates and frees memory
4. **Check for NULL**: Always validate pointers from C before dereferencing
5. **Bounds checking**: Add safety checks when accessing array elements
6. **Use const**: Mark arrays as `const` when they shouldn't be modified
7. **extern struct**: Use `extern struct` for C-compatible struct layout
8. **Sentinel pointers**: Use `[*:0]T` for NULL-terminated arrays (especially strings)

### Common Patterns

**Reading from C array:**
```zig
export fn process(arr: [*]const c_int, len: usize) c_int {
    for (0..len) |i| {
        // Process arr[i]
    }
}
```

**Modifying C array:**
```zig
export fn transform(arr: [*]c_int, len: usize) void {
    for (0..len) |i| {
        arr[i] = /* transformation */;
    }
}
```

**Output parameter:**
```zig
export fn fill_array(out: [*]c_int, len: usize, value: c_int) void {
    for (0..len) |i| {
        out[i] = value;
    }
}
```

### Memory Safety

When allocating arrays for C:
- Use `std.heap.c_allocator` (compatible with C's `malloc/free`)
- Provide a corresponding `free` function
- Return NULL on allocation failure
- Document ownership clearly

When accepting arrays from C:
- Validate pointers are not NULL
- Trust but verify the length parameter
- Don't assume array lifetime extends beyond the call
- Consider copying data if you need to retain it

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: many_item_pointer
// Zig function accepting a C array as many-item pointer
export fn sum_integers(arr: [*]const c_int, len: usize) c_int {
    var total: c_int = 0;
    for (0..len) |i| {
        total += arr[i];
    }
    return total;
}

test "passing array to Zig from C" {
    const numbers = [_]c_int{ 10, 20, 30, 40, 50 };
    const result = sum_integers(&numbers, numbers.len);
    try testing.expectEqual(@as(c_int, 150), result);
}
// ANCHOR_END: many_item_pointer

// ANCHOR: modifying_array
// Zig function that modifies a C array in place
export fn double_values(arr: [*]c_int, len: usize) void {
    for (0..len) |i| {
        arr[i] *= 2;
    }
}

test "modifying C array from Zig" {
    var numbers = [_]c_int{ 1, 2, 3, 4, 5 };
    double_values(&numbers, numbers.len);

    try testing.expectEqual(@as(c_int, 2), numbers[0]);
    try testing.expectEqual(@as(c_int, 4), numbers[1]);
    try testing.expectEqual(@as(c_int, 6), numbers[2]);
    try testing.expectEqual(@as(c_int, 8), numbers[3]);
    try testing.expectEqual(@as(c_int, 10), numbers[4]);
}
// ANCHOR_END: modifying_array

// ANCHOR: returning_array
// Allocate and return an array to C
export fn create_range(start: c_int, count: usize, out_arr: [*]c_int) void {
    for (0..count) |i| {
        out_arr[i] = start + @as(c_int, @intCast(i));
    }
}

test "returning array to C" {
    var result: [5]c_int = undefined;
    create_range(10, 5, &result);

    try testing.expectEqual(@as(c_int, 10), result[0]);
    try testing.expectEqual(@as(c_int, 11), result[1]);
    try testing.expectEqual(@as(c_int, 12), result[2]);
    try testing.expectEqual(@as(c_int, 13), result[3]);
    try testing.expectEqual(@as(c_int, 14), result[4]);
}
// ANCHOR_END: returning_array

// ANCHOR: c_pointer_conversion
// Using C pointers ([*c]T) for maximum compatibility
const c = @cImport({
    @cInclude("stdlib.h");
});

export fn process_c_array(arr: [*c]c_int, len: usize) c_int {
    if (arr == null) return -1;

    var max: c_int = arr[0];
    for (1..len) |i| {
        if (arr[i] > max) {
            max = arr[i];
        }
    }
    return max;
}

test "working with C pointers" {
    var numbers = [_]c_int{ 15, 42, 8, 23, 16 };
    const result = process_c_array(&numbers, numbers.len);
    try testing.expectEqual(@as(c_int, 42), result);

    // Test NULL handling
    const null_result = process_c_array(null, 0);
    try testing.expectEqual(@as(c_int, -1), null_result);
}
// ANCHOR_END: c_pointer_conversion

// ANCHOR: multidimensional_arrays
// Working with 2D arrays (arrays of pointers)
export fn sum_2d_array(rows: [*]const [*]const c_int, num_rows: usize, cols_per_row: usize) c_int {
    var total: c_int = 0;
    for (0..num_rows) |i| {
        for (0..cols_per_row) |j| {
            total += rows[i][j];
        }
    }
    return total;
}

test "2D array operations" {
    const row1 = [_]c_int{ 1, 2, 3 };
    const row2 = [_]c_int{ 4, 5, 6 };
    const row3 = [_]c_int{ 7, 8, 9 };

    const rows = [_][*]const c_int{ &row1, &row2, &row3 };
    const result = sum_2d_array(&rows, 3, 3);
    try testing.expectEqual(@as(c_int, 45), result);
}
// ANCHOR_END: multidimensional_arrays

// ANCHOR: struct_array
// Passing arrays of structs
pub const Point2D = extern struct {
    x: c_int,
    y: c_int,
};

export fn compute_bounding_box(points: [*]const Point2D, count: usize, min_x: *c_int, min_y: *c_int, max_x: *c_int, max_y: *c_int) void {
    if (count == 0) return;

    min_x.* = points[0].x;
    min_y.* = points[0].y;
    max_x.* = points[0].x;
    max_y.* = points[0].y;

    for (1..count) |i| {
        if (points[i].x < min_x.*) min_x.* = points[i].x;
        if (points[i].y < min_y.*) min_y.* = points[i].y;
        if (points[i].x > max_x.*) max_x.* = points[i].x;
        if (points[i].y > max_y.*) max_y.* = points[i].y;
    }
}

test "array of structs" {
    const points = [_]Point2D{
        .{ .x = 5, .y = 3 },
        .{ .x = 1, .y = 7 },
        .{ .x = 9, .y = 2 },
        .{ .x = 3, .y = 8 },
    };

    var min_x: c_int = undefined;
    var min_y: c_int = undefined;
    var max_x: c_int = undefined;
    var max_y: c_int = undefined;

    compute_bounding_box(&points, points.len, &min_x, &min_y, &max_x, &max_y);

    try testing.expectEqual(@as(c_int, 1), min_x);
    try testing.expectEqual(@as(c_int, 2), min_y);
    try testing.expectEqual(@as(c_int, 9), max_x);
    try testing.expectEqual(@as(c_int, 8), max_y);
}
// ANCHOR_END: struct_array

// ANCHOR: slice_to_c_array
// Converting Zig slices to C arrays
export fn average_slice(slice_ptr: [*]const c_int, slice_len: usize) f64 {
    if (slice_len == 0) return 0.0;

    var sum: c_int = 0;
    for (0..slice_len) |i| {
        sum += slice_ptr[i];
    }

    return @as(f64, @floatFromInt(sum)) / @as(f64, @floatFromInt(slice_len));
}

test "converting slice to C array" {
    const numbers = [_]c_int{ 10, 20, 30, 40, 50 };
    const slice: []const c_int = &numbers;

    const result = average_slice(slice.ptr, slice.len);
    try testing.expectApproxEqAbs(30.0, result, 0.001);
}
// ANCHOR_END: slice_to_c_array

// ANCHOR: dynamic_array_allocation
// Allocating arrays for C callers
export fn create_fibonacci(n: usize) ?[*]c_int {
    if (n == 0) return null;

    const allocator = std.heap.c_allocator;
    const arr = allocator.alloc(c_int, n) catch return null;

    if (n >= 1) arr[0] = 0;
    if (n >= 2) arr[1] = 1;

    for (2..n) |i| {
        arr[i] = arr[i - 1] + arr[i - 2];
    }

    return arr.ptr;
}

export fn free_array(arr: ?[*]c_int, len: usize) void {
    if (arr) |a| {
        const allocator = std.heap.c_allocator;
        const slice = a[0..len];
        allocator.free(slice);
    }
}

test "dynamic array allocation" {
    const arr = create_fibonacci(10);
    try testing.expect(arr != null);

    if (arr) |a| {
        try testing.expectEqual(@as(c_int, 0), a[0]);
        try testing.expectEqual(@as(c_int, 1), a[1]);
        try testing.expectEqual(@as(c_int, 1), a[2]);
        try testing.expectEqual(@as(c_int, 2), a[3]);
        try testing.expectEqual(@as(c_int, 3), a[4]);
        try testing.expectEqual(@as(c_int, 5), a[5]);
        try testing.expectEqual(@as(c_int, 8), a[6]);
        try testing.expectEqual(@as(c_int, 13), a[7]);
        try testing.expectEqual(@as(c_int, 21), a[8]);
        try testing.expectEqual(@as(c_int, 34), a[9]);

        free_array(arr, 10);
    }
}
// ANCHOR_END: dynamic_array_allocation

// ANCHOR: byte_array_operations
// Working with byte arrays (useful for buffers)
export fn reverse_bytes(data: [*]u8, len: usize) void {
    var left: usize = 0;
    var right: usize = len - 1;

    while (left < right) {
        const temp = data[left];
        data[left] = data[right];
        data[right] = temp;
        left += 1;
        right -= 1;
    }
}

test "byte array manipulation" {
    var data = "Hello".*;
    reverse_bytes(&data, data.len);
    try testing.expect(std.mem.eql(u8, &data, "olleH"));
}
// ANCHOR_END: byte_array_operations

// ANCHOR: array_bounds_safety
// Safe array access with bounds checking
export fn safe_get_element(arr: [*]const c_int, len: usize, index: usize, out_value: *c_int) bool {
    if (index >= len) {
        return false;
    }
    out_value.* = arr[index];
    return true;
}

test "safe array access" {
    const numbers = [_]c_int{ 100, 200, 300, 400 };
    var value: c_int = undefined;

    // Valid access
    const success = safe_get_element(&numbers, numbers.len, 2, &value);
    try testing.expect(success);
    try testing.expectEqual(@as(c_int, 300), value);

    // Out of bounds access
    const failure = safe_get_element(&numbers, numbers.len, 10, &value);
    try testing.expect(!failure);
}
// ANCHOR_END: array_bounds_safety
```

### See Also

- Recipe 15.1: Accessing C Code from Zig
- Recipe 15.2: Writing a Zig Library Callable from C
- Recipe 15.7: Managing Memory Across the C/Zig Boundary
- Recipe 15.8: Passing NULL

---

## Recipe 15.4: Managing opaque types in C extensions {#recipe-15-4}

**Tags:** allocators, arraylist, c-interop, concurrency, data-structures, error-handling, memory, pointers, slices, testing, threading
**Difficulty:** intermediate
**Code:** `code/04-specialized/15-c-interoperability/recipe_15_4.zig`

### Problem

You want to hide implementation details from C code while providing a clean API, preventing C callers from depending on internal structure layout.

### Solution

Use Zig's `opaque` type to create handles that hide implementation details. This provides encapsulation and ABI stability.

```zig
// Define an opaque handle type for C
pub const Database = opaque {};

// Internal implementation (not visible to C)
const DatabaseImpl = struct {
    name: []const u8,
    connection_count: usize,
    allocator: std.mem.Allocator,
};

export fn database_create(name: [*:0]const u8) ?*Database {
    const allocator = std.heap.c_allocator;

    // Convert C string to Zig slice
    const name_len = std.mem.len(name);
    const name_copy = allocator.dupe(u8, name[0..name_len]) catch return null;

    const impl = allocator.create(DatabaseImpl) catch {
        allocator.free(name_copy);
        return null;
    };

    impl.* = DatabaseImpl{
        .name = name_copy,
        .connection_count = 0,
        .allocator = allocator,
    };

    return @ptrCast(impl);
}

export fn database_connect(db: ?*Database) bool {
    const impl: *DatabaseImpl = @ptrCast(@alignCast(db orelse return false));
    impl.connection_count += 1;
    return true;
}

export fn database_get_connections(db: ?*const Database) usize {
    const impl: *const DatabaseImpl = @ptrCast(@alignCast(db orelse return 0));
    return impl.connection_count;
}

export fn database_destroy(db: ?*Database) void {
    if (db) |handle| {
        const impl: *DatabaseImpl = @ptrCast(@alignCast(handle));
        impl.allocator.free(impl.name);
        impl.allocator.destroy(impl);
    }
}

test "basic opaque handle" {
    const db = database_create("test_db");
    try testing.expect(db != null);

    try testing.expect(database_connect(db));
    try testing.expect(database_connect(db));
    try testing.expectEqual(@as(usize, 2), database_get_connections(db));

    database_destroy(db);
}
```

### Discussion

### Why Opaque Types?

Opaque types provide several benefits:
- **Encapsulation**: Hide implementation details from C callers
- **ABI Stability**: Change internal structure without breaking C code
- **Type Safety**: Handles are type-checked, preventing misuse
- **Memory Safety**: Control all allocation and deallocation

### Basic Pattern

The standard pattern for opaque handles:

1. Declare an opaque type for C
2. Define an internal implementation struct
3. Cast between the types in exported functions
4. Provide create/destroy functions for lifecycle management

### File Handle Example

A more complete example with state management:

```zig
// More complex opaque type with multiple operations
pub const FileHandle = opaque {};

const FileHandleImpl = struct {
    path: []const u8,
    is_open: bool,
    read_count: usize,
    write_count: usize,
    allocator: std.mem.Allocator,
};

export fn file_open(path: [*:0]const u8) ?*FileHandle {
    const allocator = std.heap.c_allocator;
    const path_len = std.mem.len(path);
    const path_copy = allocator.dupe(u8, path[0..path_len]) catch return null;

    const impl = allocator.create(FileHandleImpl) catch {
        allocator.free(path_copy);
        return null;
    };

    impl.* = FileHandleImpl{
        .path = path_copy,
        .is_open = true,
        .read_count = 0,
        .write_count = 0,
        .allocator = allocator,
    };

    return @ptrCast(impl);
}

export fn file_read(handle: ?*FileHandle) bool {
    const impl: *FileHandleImpl = @ptrCast(@alignCast(handle orelse return false));
    if (!impl.is_open) return false;
    impl.read_count += 1;
    return true;
}

export fn file_write(handle: ?*FileHandle) bool {
    const impl: *FileHandleImpl = @ptrCast(@alignCast(handle orelse return false));
    if (!impl.is_open) return false;
    impl.write_count += 1;
    return true;
}

export fn file_get_stats(handle: ?*const FileHandle, reads: *usize, writes: *usize) bool {
    const impl: *const FileHandleImpl = @ptrCast(@alignCast(handle orelse return false));
    reads.* = impl.read_count;
    writes.* = impl.write_count;
    return true;
}

export fn file_close(handle: ?*FileHandle) void {
    if (handle) |h| {
        const impl: *FileHandleImpl = @ptrCast(@alignCast(h));
        impl.is_open = false;
        impl.allocator.free(impl.path);
        impl.allocator.destroy(impl);
    }
}

test "opaque file handle with state" {
    const handle = file_open("test.txt");
    try testing.expect(handle != null);

    try testing.expect(file_read(handle));
    try testing.expect(file_read(handle));
    try testing.expect(file_write(handle));

    var reads: usize = 0;
    var writes: usize = 0;
    try testing.expect(file_get_stats(handle, &reads, &writes));
    try testing.expectEqual(@as(usize, 2), reads);
    try testing.expectEqual(@as(usize, 1), writes);

    file_close(handle);
}
```

### Iterator Pattern

Opaque types work well for iterators:

```zig
// Iterator pattern using opaque types
pub const Iterator = opaque {};

const IteratorImpl = struct {
    data: []const c_int,
    current: usize,
    allocator: std.mem.Allocator,
};

export fn iterator_create(data: [*]const c_int, len: usize) ?*Iterator {
    const allocator = std.heap.c_allocator;
    const data_copy = allocator.dupe(c_int, data[0..len]) catch return null;

    const impl = allocator.create(IteratorImpl) catch {
        allocator.free(data_copy);
        return null;
    };

    impl.* = IteratorImpl{
        .data = data_copy,
        .current = 0,
        .allocator = allocator,
    };

    return @ptrCast(impl);
}

export fn iterator_has_next(iter: ?*const Iterator) bool {
    const impl: *const IteratorImpl = @ptrCast(@alignCast(iter orelse return false));
    return impl.current < impl.data.len;
}

export fn iterator_next(iter: ?*Iterator, out_value: *c_int) bool {
    const impl: *IteratorImpl = @ptrCast(@alignCast(iter orelse return false));
    if (impl.current >= impl.data.len) return false;

    out_value.* = impl.data[impl.current];
    impl.current += 1;
    return true;
}

export fn iterator_reset(iter: ?*Iterator) void {
    if (iter) |it| {
        const impl: *IteratorImpl = @ptrCast(@alignCast(it));
        impl.current = 0;
    }
}

export fn iterator_destroy(iter: ?*Iterator) void {
    if (iter) |it| {
        const impl: *IteratorImpl = @ptrCast(@alignCast(it));
        impl.allocator.free(impl.data);
        impl.allocator.destroy(impl);
    }
}

test "opaque iterator pattern" {
    const data = [_]c_int{ 10, 20, 30, 40 };
    const iter = iterator_create(&data, data.len);
    try testing.expect(iter != null);

    var value: c_int = 0;
    var count: usize = 0;

    while (iterator_has_next(iter)) {
        try testing.expect(iterator_next(iter, &value));
        count += 1;
    }
    try testing.expectEqual(@as(usize, 4), count);

    // Reset and iterate again
    iterator_reset(iter);
    try testing.expect(iterator_next(iter, &value));
    try testing.expectEqual(@as(c_int, 10), value);

    iterator_destroy(iter);
}
```

This pattern provides:
- Clean iteration API for C
- Hidden state management
- Safe cleanup

### Collection Types

Build collection data structures with opaque handles:

```zig
// Collection type with opaque internals
pub const Stack = opaque {};

const StackImpl = struct {
    items: std.ArrayList(c_int),
    max_size: usize,
    allocator: std.mem.Allocator,
};

export fn stack_create(max_size: usize) ?*Stack {
    const allocator = std.heap.c_allocator;
    const impl = allocator.create(StackImpl) catch return null;

    impl.* = StackImpl{
        .items = .{},
        .max_size = max_size,
        .allocator = allocator,
    };

    return @ptrCast(impl);
}

export fn stack_push(stack: ?*Stack, value: c_int) bool {
    const impl: *StackImpl = @ptrCast(@alignCast(stack orelse return false));
    if (impl.items.items.len >= impl.max_size) return false;

    impl.items.append(impl.allocator, value) catch return false;
    return true;
}

export fn stack_pop(stack: ?*Stack, out_value: *c_int) bool {
    const impl: *StackImpl = @ptrCast(@alignCast(stack orelse return false));
    if (impl.items.items.len == 0) return false;

    out_value.* = impl.items.pop() orelse return false;
    return true;
}

export fn stack_peek(stack: ?*const Stack, out_value: *c_int) bool {
    const impl: *const StackImpl = @ptrCast(@alignCast(stack orelse return false));
    if (impl.items.items.len == 0) return false;

    out_value.* = impl.items.items[impl.items.items.len - 1];
    return true;
}

export fn stack_size(stack: ?*const Stack) usize {
    const impl: *const StackImpl = @ptrCast(@alignCast(stack orelse return 0));
    return impl.items.items.len;
}

export fn stack_is_empty(stack: ?*const Stack) bool {
    const impl: *const StackImpl = @ptrCast(@alignCast(stack orelse return true));
    return impl.items.items.len == 0;
}

export fn stack_clear(stack: ?*Stack) void {
    if (stack) |s| {
        const impl: *StackImpl = @ptrCast(@alignCast(s));
        impl.items.clearRetainingCapacity();
    }
}

export fn stack_destroy(stack: ?*Stack) void {
    if (stack) |s| {
        const impl: *StackImpl = @ptrCast(@alignCast(s));
        impl.items.deinit(impl.allocator);
        impl.allocator.destroy(impl);
    }
}

test "opaque stack collection" {
    const stack = stack_create(5);
    try testing.expect(stack != null);
    try testing.expect(stack_is_empty(stack));

    try testing.expect(stack_push(stack, 10));
    try testing.expect(stack_push(stack, 20));
    try testing.expect(stack_push(stack, 30));
    try testing.expectEqual(@as(usize, 3), stack_size(stack));

    var value: c_int = 0;
    try testing.expect(stack_peek(stack, &value));
    try testing.expectEqual(@as(c_int, 30), value);
    try testing.expectEqual(@as(usize, 3), stack_size(stack));

    try testing.expect(stack_pop(stack, &value));
    try testing.expectEqual(@as(c_int, 30), value);
    try testing.expectEqual(@as(usize, 2), stack_size(stack));

    stack_clear(stack);
    try testing.expect(stack_is_empty(stack));

    stack_destroy(stack);
}
```

### Resource Management

Manage pools of resources using opaque types:

```zig
// Resource manager with opaque handle
pub const ResourcePool = opaque {};

const Resource = struct {
    id: usize,
    in_use: bool,
};

const ResourcePoolImpl = struct {
    resources: std.ArrayList(Resource),
    next_id: usize,
    allocator: std.mem.Allocator,
};

export fn resource_pool_create(initial_capacity: usize) ?*ResourcePool {
    const allocator = std.heap.c_allocator;
    const impl = allocator.create(ResourcePoolImpl) catch return null;

    impl.* = ResourcePoolImpl{
        .resources = .{},
        .next_id = 0,
        .allocator = allocator,
    };

    // Pre-allocate resources
    for (0..initial_capacity) |_| {
        const resource = Resource{ .id = impl.next_id, .in_use = false };
        impl.next_id += 1;
        impl.resources.append(allocator, resource) catch {
            impl.resources.deinit(allocator);
            allocator.destroy(impl);
            return null;
        };
    }

    return @ptrCast(impl);
}

export fn resource_pool_acquire(pool: ?*ResourcePool) isize {
    const impl: *ResourcePoolImpl = @ptrCast(@alignCast(pool orelse return -1));

    for (impl.resources.items) |*resource| {
        if (!resource.in_use) {
            resource.in_use = true;
            return @intCast(resource.id);
        }
    }

    return -1; // No available resources
}

export fn resource_pool_release(pool: ?*ResourcePool, resource_id: usize) bool {
    const impl: *ResourcePoolImpl = @ptrCast(@alignCast(pool orelse return false));

    for (impl.resources.items) |*resource| {
        if (resource.id == resource_id and resource.in_use) {
            resource.in_use = false;
            return true;
        }
    }

    return false;
}

export fn resource_pool_available_count(pool: ?*const ResourcePool) usize {
    const impl: *const ResourcePoolImpl = @ptrCast(@alignCast(pool orelse return 0));
    var count: usize = 0;

    for (impl.resources.items) |resource| {
        if (!resource.in_use) count += 1;
    }

    return count;
}

export fn resource_pool_destroy(pool: ?*ResourcePool) void {
    if (pool) |p| {
        const impl: *ResourcePoolImpl = @ptrCast(@alignCast(p));
        impl.resources.deinit(impl.allocator);
        impl.allocator.destroy(impl);
    }
}

test "opaque resource pool" {
    const pool = resource_pool_create(3);
    try testing.expect(pool != null);
    try testing.expectEqual(@as(usize, 3), resource_pool_available_count(pool));

    const r1 = resource_pool_acquire(pool);
    const r2 = resource_pool_acquire(pool);
    try testing.expect(r1 >= 0);
    try testing.expect(r2 >= 0);
    try testing.expectEqual(@as(usize, 1), resource_pool_available_count(pool));

    try testing.expect(resource_pool_release(pool, @intCast(r1)));
    try testing.expectEqual(@as(usize, 2), resource_pool_available_count(pool));

    resource_pool_destroy(pool);
}
```

### Design Patterns

**Factory Pattern:**
```zig
export fn thing_create(params...) ?*Thing {
    // Allocate and initialize
    return @ptrCast(impl);
}
```

**Destructor Pattern:**
```zig
export fn thing_destroy(thing: ?*Thing) void {
    if (thing) |t| {
        // Cleanup and deallocate
    }
}
```

**Accessor Pattern:**
```zig
export fn thing_get_value(thing: ?*const Thing) ReturnType {
    const impl: *const ThingImpl = @ptrCast(@alignCast(thing orelse return default));
    return impl.value;
}
```

**Mutator Pattern:**
```zig
export fn thing_set_value(thing: ?*Thing, value: ValueType) bool {
    const impl: *ThingImpl = @ptrCast(@alignCast(thing orelse return false));
    impl.value = value;
    return true;
}
```

### Memory Management

Always use `std.heap.c_allocator` for opaque types:

```zig
const allocator = std.heap.c_allocator;
const impl = allocator.create(ThingImpl) catch return null;
// ...later...
allocator.destroy(impl);
```

This ensures memory allocated in Zig can be safely freed, and matches C's expectations.

### NULL Safety

Always check for NULL before dereferencing:

```zig
export fn thing_process(thing: ?*Thing) bool {
    const impl: *ThingImpl = @ptrCast(@alignCast(thing orelse return false));
    // Safe to use impl here
}
```

### Type Casting

The standard casting pattern:

```zig
// Mutable access
const impl: *ThingImpl = @ptrCast(@alignCast(opaque_ptr));

// Const access
const impl: *const ThingImpl = @ptrCast(@alignCast(opaque_ptr));
```

### Error Handling

Since opaque types are used with C, follow C conventions:

```zig
// Return NULL on creation failure
export fn thing_create() ?*Thing {
    const impl = allocator.create(ThingImpl) catch return null;
    // ...
}

// Return bool for success/failure
export fn thing_operation(thing: ?*Thing) bool {
    const impl: *ThingImpl = @ptrCast(@alignCast(thing orelse return false));
    // ... operation ...
    return true;  // or false on error
}

// Return error codes
export fn thing_process(thing: ?*Thing) c_int {
    if (thing == null) return -1;
    // ...
    return 0;  // Success
}
```

### Best Practices

1. **Always Validate**: Check for NULL before casting
2. **Clear Ownership**: Document who creates and destroys handles
3. **Consistent Naming**: Use `create`/`destroy` naming convention
4. **Return NULL on Failure**: Creation functions should return NULL when they fail
5. **Use Const**: Mark read-only operations with `const` pointers
6. **Document Lifecycle**: Clearly specify object lifetime expectations
7. **Thread Safety**: Document if handles are thread-safe
8. **Resource Cleanup**: Always provide a destroy function

### Common Pitfalls

**Double Free:**
```zig
// BAD: Don't let C code free memory directly
// GOOD: Provide a destroy function
export fn thing_destroy(thing: ?*Thing) void {
    // Handle cleanup properly
}
```

**Dangling Pointers:**
```zig
// BAD: Returning pointers to stack memory
// GOOD: Allocate on heap, return handle
```

**Missing NULL Checks:**
```zig
// BAD: Assuming pointer is valid
// GOOD: Always check for NULL
const impl: *ThingImpl = @ptrCast(@alignCast(thing orelse return false));
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_opaque
// Define an opaque handle type for C
pub const Database = opaque {};

// Internal implementation (not visible to C)
const DatabaseImpl = struct {
    name: []const u8,
    connection_count: usize,
    allocator: std.mem.Allocator,
};

export fn database_create(name: [*:0]const u8) ?*Database {
    const allocator = std.heap.c_allocator;

    // Convert C string to Zig slice
    const name_len = std.mem.len(name);
    const name_copy = allocator.dupe(u8, name[0..name_len]) catch return null;

    const impl = allocator.create(DatabaseImpl) catch {
        allocator.free(name_copy);
        return null;
    };

    impl.* = DatabaseImpl{
        .name = name_copy,
        .connection_count = 0,
        .allocator = allocator,
    };

    return @ptrCast(impl);
}

export fn database_connect(db: ?*Database) bool {
    const impl: *DatabaseImpl = @ptrCast(@alignCast(db orelse return false));
    impl.connection_count += 1;
    return true;
}

export fn database_get_connections(db: ?*const Database) usize {
    const impl: *const DatabaseImpl = @ptrCast(@alignCast(db orelse return 0));
    return impl.connection_count;
}

export fn database_destroy(db: ?*Database) void {
    if (db) |handle| {
        const impl: *DatabaseImpl = @ptrCast(@alignCast(handle));
        impl.allocator.free(impl.name);
        impl.allocator.destroy(impl);
    }
}

test "basic opaque handle" {
    const db = database_create("test_db");
    try testing.expect(db != null);

    try testing.expect(database_connect(db));
    try testing.expect(database_connect(db));
    try testing.expectEqual(@as(usize, 2), database_get_connections(db));

    database_destroy(db);
}
// ANCHOR_END: basic_opaque

// ANCHOR: opaque_with_state
// More complex opaque type with multiple operations
pub const FileHandle = opaque {};

const FileHandleImpl = struct {
    path: []const u8,
    is_open: bool,
    read_count: usize,
    write_count: usize,
    allocator: std.mem.Allocator,
};

export fn file_open(path: [*:0]const u8) ?*FileHandle {
    const allocator = std.heap.c_allocator;
    const path_len = std.mem.len(path);
    const path_copy = allocator.dupe(u8, path[0..path_len]) catch return null;

    const impl = allocator.create(FileHandleImpl) catch {
        allocator.free(path_copy);
        return null;
    };

    impl.* = FileHandleImpl{
        .path = path_copy,
        .is_open = true,
        .read_count = 0,
        .write_count = 0,
        .allocator = allocator,
    };

    return @ptrCast(impl);
}

export fn file_read(handle: ?*FileHandle) bool {
    const impl: *FileHandleImpl = @ptrCast(@alignCast(handle orelse return false));
    if (!impl.is_open) return false;
    impl.read_count += 1;
    return true;
}

export fn file_write(handle: ?*FileHandle) bool {
    const impl: *FileHandleImpl = @ptrCast(@alignCast(handle orelse return false));
    if (!impl.is_open) return false;
    impl.write_count += 1;
    return true;
}

export fn file_get_stats(handle: ?*const FileHandle, reads: *usize, writes: *usize) bool {
    const impl: *const FileHandleImpl = @ptrCast(@alignCast(handle orelse return false));
    reads.* = impl.read_count;
    writes.* = impl.write_count;
    return true;
}

export fn file_close(handle: ?*FileHandle) void {
    if (handle) |h| {
        const impl: *FileHandleImpl = @ptrCast(@alignCast(h));
        impl.is_open = false;
        impl.allocator.free(impl.path);
        impl.allocator.destroy(impl);
    }
}

test "opaque file handle with state" {
    const handle = file_open("test.txt");
    try testing.expect(handle != null);

    try testing.expect(file_read(handle));
    try testing.expect(file_read(handle));
    try testing.expect(file_write(handle));

    var reads: usize = 0;
    var writes: usize = 0;
    try testing.expect(file_get_stats(handle, &reads, &writes));
    try testing.expectEqual(@as(usize, 2), reads);
    try testing.expectEqual(@as(usize, 1), writes);

    file_close(handle);
}
// ANCHOR_END: opaque_with_state

// ANCHOR: opaque_iterator
// Iterator pattern using opaque types
pub const Iterator = opaque {};

const IteratorImpl = struct {
    data: []const c_int,
    current: usize,
    allocator: std.mem.Allocator,
};

export fn iterator_create(data: [*]const c_int, len: usize) ?*Iterator {
    const allocator = std.heap.c_allocator;
    const data_copy = allocator.dupe(c_int, data[0..len]) catch return null;

    const impl = allocator.create(IteratorImpl) catch {
        allocator.free(data_copy);
        return null;
    };

    impl.* = IteratorImpl{
        .data = data_copy,
        .current = 0,
        .allocator = allocator,
    };

    return @ptrCast(impl);
}

export fn iterator_has_next(iter: ?*const Iterator) bool {
    const impl: *const IteratorImpl = @ptrCast(@alignCast(iter orelse return false));
    return impl.current < impl.data.len;
}

export fn iterator_next(iter: ?*Iterator, out_value: *c_int) bool {
    const impl: *IteratorImpl = @ptrCast(@alignCast(iter orelse return false));
    if (impl.current >= impl.data.len) return false;

    out_value.* = impl.data[impl.current];
    impl.current += 1;
    return true;
}

export fn iterator_reset(iter: ?*Iterator) void {
    if (iter) |it| {
        const impl: *IteratorImpl = @ptrCast(@alignCast(it));
        impl.current = 0;
    }
}

export fn iterator_destroy(iter: ?*Iterator) void {
    if (iter) |it| {
        const impl: *IteratorImpl = @ptrCast(@alignCast(it));
        impl.allocator.free(impl.data);
        impl.allocator.destroy(impl);
    }
}

test "opaque iterator pattern" {
    const data = [_]c_int{ 10, 20, 30, 40 };
    const iter = iterator_create(&data, data.len);
    try testing.expect(iter != null);

    var value: c_int = 0;
    var count: usize = 0;

    while (iterator_has_next(iter)) {
        try testing.expect(iterator_next(iter, &value));
        count += 1;
    }
    try testing.expectEqual(@as(usize, 4), count);

    // Reset and iterate again
    iterator_reset(iter);
    try testing.expect(iterator_next(iter, &value));
    try testing.expectEqual(@as(c_int, 10), value);

    iterator_destroy(iter);
}
// ANCHOR_END: opaque_iterator

// ANCHOR: opaque_collection
// Collection type with opaque internals
pub const Stack = opaque {};

const StackImpl = struct {
    items: std.ArrayList(c_int),
    max_size: usize,
    allocator: std.mem.Allocator,
};

export fn stack_create(max_size: usize) ?*Stack {
    const allocator = std.heap.c_allocator;
    const impl = allocator.create(StackImpl) catch return null;

    impl.* = StackImpl{
        .items = .{},
        .max_size = max_size,
        .allocator = allocator,
    };

    return @ptrCast(impl);
}

export fn stack_push(stack: ?*Stack, value: c_int) bool {
    const impl: *StackImpl = @ptrCast(@alignCast(stack orelse return false));
    if (impl.items.items.len >= impl.max_size) return false;

    impl.items.append(impl.allocator, value) catch return false;
    return true;
}

export fn stack_pop(stack: ?*Stack, out_value: *c_int) bool {
    const impl: *StackImpl = @ptrCast(@alignCast(stack orelse return false));
    if (impl.items.items.len == 0) return false;

    out_value.* = impl.items.pop() orelse return false;
    return true;
}

export fn stack_peek(stack: ?*const Stack, out_value: *c_int) bool {
    const impl: *const StackImpl = @ptrCast(@alignCast(stack orelse return false));
    if (impl.items.items.len == 0) return false;

    out_value.* = impl.items.items[impl.items.items.len - 1];
    return true;
}

export fn stack_size(stack: ?*const Stack) usize {
    const impl: *const StackImpl = @ptrCast(@alignCast(stack orelse return 0));
    return impl.items.items.len;
}

export fn stack_is_empty(stack: ?*const Stack) bool {
    const impl: *const StackImpl = @ptrCast(@alignCast(stack orelse return true));
    return impl.items.items.len == 0;
}

export fn stack_clear(stack: ?*Stack) void {
    if (stack) |s| {
        const impl: *StackImpl = @ptrCast(@alignCast(s));
        impl.items.clearRetainingCapacity();
    }
}

export fn stack_destroy(stack: ?*Stack) void {
    if (stack) |s| {
        const impl: *StackImpl = @ptrCast(@alignCast(s));
        impl.items.deinit(impl.allocator);
        impl.allocator.destroy(impl);
    }
}

test "opaque stack collection" {
    const stack = stack_create(5);
    try testing.expect(stack != null);
    try testing.expect(stack_is_empty(stack));

    try testing.expect(stack_push(stack, 10));
    try testing.expect(stack_push(stack, 20));
    try testing.expect(stack_push(stack, 30));
    try testing.expectEqual(@as(usize, 3), stack_size(stack));

    var value: c_int = 0;
    try testing.expect(stack_peek(stack, &value));
    try testing.expectEqual(@as(c_int, 30), value);
    try testing.expectEqual(@as(usize, 3), stack_size(stack));

    try testing.expect(stack_pop(stack, &value));
    try testing.expectEqual(@as(c_int, 30), value);
    try testing.expectEqual(@as(usize, 2), stack_size(stack));

    stack_clear(stack);
    try testing.expect(stack_is_empty(stack));

    stack_destroy(stack);
}
// ANCHOR_END: opaque_collection

// ANCHOR: opaque_resource_manager
// Resource manager with opaque handle
pub const ResourcePool = opaque {};

const Resource = struct {
    id: usize,
    in_use: bool,
};

const ResourcePoolImpl = struct {
    resources: std.ArrayList(Resource),
    next_id: usize,
    allocator: std.mem.Allocator,
};

export fn resource_pool_create(initial_capacity: usize) ?*ResourcePool {
    const allocator = std.heap.c_allocator;
    const impl = allocator.create(ResourcePoolImpl) catch return null;

    impl.* = ResourcePoolImpl{
        .resources = .{},
        .next_id = 0,
        .allocator = allocator,
    };

    // Pre-allocate resources
    for (0..initial_capacity) |_| {
        const resource = Resource{ .id = impl.next_id, .in_use = false };
        impl.next_id += 1;
        impl.resources.append(allocator, resource) catch {
            impl.resources.deinit(allocator);
            allocator.destroy(impl);
            return null;
        };
    }

    return @ptrCast(impl);
}

export fn resource_pool_acquire(pool: ?*ResourcePool) isize {
    const impl: *ResourcePoolImpl = @ptrCast(@alignCast(pool orelse return -1));

    for (impl.resources.items) |*resource| {
        if (!resource.in_use) {
            resource.in_use = true;
            return @intCast(resource.id);
        }
    }

    return -1; // No available resources
}

export fn resource_pool_release(pool: ?*ResourcePool, resource_id: usize) bool {
    const impl: *ResourcePoolImpl = @ptrCast(@alignCast(pool orelse return false));

    for (impl.resources.items) |*resource| {
        if (resource.id == resource_id and resource.in_use) {
            resource.in_use = false;
            return true;
        }
    }

    return false;
}

export fn resource_pool_available_count(pool: ?*const ResourcePool) usize {
    const impl: *const ResourcePoolImpl = @ptrCast(@alignCast(pool orelse return 0));
    var count: usize = 0;

    for (impl.resources.items) |resource| {
        if (!resource.in_use) count += 1;
    }

    return count;
}

export fn resource_pool_destroy(pool: ?*ResourcePool) void {
    if (pool) |p| {
        const impl: *ResourcePoolImpl = @ptrCast(@alignCast(p));
        impl.resources.deinit(impl.allocator);
        impl.allocator.destroy(impl);
    }
}

test "opaque resource pool" {
    const pool = resource_pool_create(3);
    try testing.expect(pool != null);
    try testing.expectEqual(@as(usize, 3), resource_pool_available_count(pool));

    const r1 = resource_pool_acquire(pool);
    const r2 = resource_pool_acquire(pool);
    try testing.expect(r1 >= 0);
    try testing.expect(r2 >= 0);
    try testing.expectEqual(@as(usize, 1), resource_pool_available_count(pool));

    try testing.expect(resource_pool_release(pool, @intCast(r1)));
    try testing.expectEqual(@as(usize, 2), resource_pool_available_count(pool));

    resource_pool_destroy(pool);
}
// ANCHOR_END: opaque_resource_manager
```

### See Also

- Recipe 15.2: Writing a Zig Library Callable from C
- Recipe 15.3: Passing Arrays Between C and Zig
- Recipe 15.7: Managing Memory Across the C/Zig Boundary

---

## Recipe 15.5: Wrapping existing C libraries {#recipe-15-5}

**Tags:** allocators, c-interop, comptime, error-handling, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/15-c-interoperability/recipe_15_5.zig`

### Problem

You want to create idiomatic Zig wrappers around existing C library functions to provide better type safety, error handling, and a more Zig-friendly API.

### Solution

Import C headers with `@cImport` and create wrapper functions that translate between C and Zig conventions.

```zig
// Anchor 'c_library_import' not found in ../../../code/04-specialized/15-c-interoperability/recipe_15_5.zig
```

### Discussion

### Basic Memory Function Wrappers

Wrap C's `malloc`/`free` with Zig-friendly types:

```zig
// Wrapper for C malloc/free with Zig types
pub const CMemory = struct {
    pub fn alloc(size: usize) ?[*]u8 {
        const ptr = c.malloc(size);
        return @ptrCast(ptr);
    }

    pub fn free(ptr: ?[*]u8) void {
        c.free(ptr);
    }

    pub fn realloc(ptr: ?[*]u8, new_size: usize) ?[*]u8 {
        const new_ptr = c.realloc(ptr, new_size);
        return @ptrCast(new_ptr);
    }
};

test "wrapping C memory functions" {
    const ptr = CMemory.alloc(100);
    try testing.expect(ptr != null);

    if (ptr) |p| {
        p[0] = 42;
        try testing.expectEqual(@as(u8, 42), p[0]);

        const new_ptr = CMemory.realloc(p, 200);
        try testing.expect(new_ptr != null);

        if (new_ptr) |np| {
            try testing.expectEqual(@as(u8, 42), np[0]);
            CMemory.free(np);
        }
    }
}
```

### Error Handling Wrappers

Convert C error conventions to Zig error unions:

```zig
// Wrap C functions with Zig error handling
pub const MathError = error{
    InvalidInput,
    DomainError,
    RangeError,
};

pub const SafeMath = struct {
    pub fn sqrt(x: f64) MathError!f64 {
        if (x < 0) return error.DomainError;
        return c.sqrt(x);
    }

    pub fn log(x: f64) MathError!f64 {
        if (x <= 0) return error.DomainError;
        return c.log(x);
    }

    pub fn pow(base: f64, exp: f64) MathError!f64 {
        const result = c.pow(base, exp);
        if (std.math.isNan(result)) return error.DomainError;
        if (std.math.isInf(result)) return error.RangeError;
        return result;
    }
};

test "error handling wrapper" {
    const result1 = try SafeMath.sqrt(16.0);
    try testing.expectApproxEqAbs(4.0, result1, 0.001);

    const result2 = SafeMath.sqrt(-1.0);
    try testing.expectError(error.DomainError, result2);

    const result3 = try SafeMath.log(std.math.e);
    try testing.expectApproxEqAbs(1.0, result3, 0.001);
}
```

This wrapper:
- Returns Zig error types instead of relying on C conventions
- Validates input before calling C functions
- Checks results for error conditions (NaN, infinity)

### String Function Wrappers

Wrap C string functions with Zig slices:

```zig
// Wrap C string functions with Zig slices
pub const CString = struct {
    pub fn length(str: [*:0]const u8) usize {
        return c.strlen(str);
    }

    pub fn compare(s1: [*:0]const u8, s2: [*:0]const u8) i32 {
        return c.strcmp(s1, s2);
    }

    pub fn copy(dest: [*]u8, src: [*:0]const u8, max_len: usize) [*]u8 {
        _ = c.strncpy(dest, src, max_len);
        return dest;
    }

    pub fn duplicate(allocator: std.mem.Allocator, str: [*:0]const u8) ![]u8 {
        const len = length(str);
        const buf = try allocator.alloc(u8, len);
        @memcpy(buf, str[0..len]);
        return buf;
    }
};

test "C string wrapper" {
    const str1 = "hello";
    const str2 = "world";

    const len = CString.length(str1.ptr);
    try testing.expectEqual(@as(usize, 5), len);

    var buffer: [20]u8 = undefined;
    _ = CString.copy(&buffer, str1.ptr, buffer.len);

    const allocator = testing.allocator;
    const dup = try CString.duplicate(allocator, str2.ptr);
    defer allocator.free(dup);
    try testing.expect(std.mem.eql(u8, dup, "world"));
}
```

### RAII-Style Resource Wrappers

Create structs that manage C resources automatically:

```zig
// RAII-style wrapper for C resources
pub const CFile = struct {
    handle: ?*c.FILE,

    pub fn open(path: [*:0]const u8, mode: [*:0]const u8) !CFile {
        const handle = c.fopen(path, mode);
        if (handle == null) return error.OpenFailed;
        return CFile{ .handle = handle };
    }

    pub fn close(self: *CFile) void {
        if (self.handle) |h| {
            _ = c.fclose(h);
            self.handle = null;
        }
    }

    pub fn write(self: *CFile, data: []const u8) !usize {
        const h = self.handle orelse return error.FileClosed;
        const written = c.fwrite(data.ptr, 1, data.len, h);
        if (written < data.len) return error.WriteFailed;
        return written;
    }

    pub fn read(self: *CFile, buffer: []u8) !usize {
        const h = self.handle orelse return error.FileClosed;
        const bytes_read = c.fread(buffer.ptr, 1, buffer.len, h);
        return bytes_read;
    }
};

test "RAII C file wrapper" {
    // Test file operations (in-memory for testing)
    const filename = "/tmp/test_zig_c_wrapper.txt";
    var file = try CFile.open(filename, "w");
    defer file.close();

    const data = "Hello from Zig!";
    _ = try file.write(data);
}
```

This pattern:
- Wraps C file handle in a Zig struct
- Provides idiomatic methods
- Uses `defer` for cleanup
- Returns errors instead of error codes

### Type-Safe Allocator Wrappers

Add compile-time type safety to C allocations:

```zig
// Type-safe wrapper for C functions
pub const Allocator = struct {
    pub fn create(comptime T: type) !*T {
        const ptr = c.malloc(@sizeOf(T));
        if (ptr == null) return error.OutOfMemory;
        return @ptrCast(@alignCast(ptr.?));
    }

    pub fn destroy(comptime T: type, ptr: *T) void {
        c.free(ptr);
    }

    pub fn createArray(comptime T: type, count: usize) ![]T {
        const ptr = c.malloc(@sizeOf(T) * count);
        if (ptr == null) return error.OutOfMemory;
        const typed_ptr: [*]T = @ptrCast(@alignCast(ptr.?));
        return typed_ptr[0..count];
    }

    pub fn destroyArray(comptime T: type, slice: []T) void {
        c.free(slice.ptr);
    }
};

test "type-safe allocator wrapper" {
    const Point = struct { x: i32, y: i32 };

    const point = try Allocator.create(Point);
    point.* = .{ .x = 10, .y = 20 };
    try testing.expectEqual(@as(i32, 10), point.x);
    Allocator.destroy(Point, point);

    const points = try Allocator.createArray(Point, 3);
    points[0] = .{ .x = 1, .y = 2 };
    points[1] = .{ .x = 3, .y = 4 };
    points[2] = .{ .x = 5, .y = 6 };
    try testing.expectEqual(@as(i32, 3), points[1].x);
    Allocator.destroyArray(Point, points);
}
```

### Callback Wrappers

Wrap C functions that accept callbacks:

```zig
// Wrapper for C callbacks
pub const Comparator = struct {
    pub const CompareFunc = *const fn (a: ?*const anyopaque, b: ?*const anyopaque) callconv(.c) c_int;

    pub fn qsort(comptime T: type, slice: []T, compare_fn: CompareFunc) void {
        c.qsort(slice.ptr, slice.len, @sizeOf(T), compare_fn);
    }
};

fn compareInts(a: ?*const anyopaque, b: ?*const anyopaque) callconv(.c) c_int {
    const ia: *const c_int = @ptrCast(@alignCast(a.?));
    const ib: *const c_int = @ptrCast(@alignCast(b.?));
    if (ia.* < ib.*) return -1;
    if (ia.* > ib.*) return 1;
    return 0;
}

test "callback wrapper for qsort" {
    var numbers = [_]c_int{ 5, 2, 8, 1, 9, 3 };
    Comparator.qsort(c_int, &numbers, compareInts);

    try testing.expectEqual(@as(c_int, 1), numbers[0]);
    try testing.expectEqual(@as(c_int, 2), numbers[1]);
    try testing.expectEqual(@as(c_int, 3), numbers[2]);
    try testing.expectEqual(@as(c_int, 5), numbers[3]);
    try testing.expectEqual(@as(c_int, 8), numbers[4]);
    try testing.expectEqual(@as(c_int, 9), numbers[5]);
}
```

### Const-Correct Wrappers

Enforce const correctness in wrapped functions:

```zig
// Wrapper that enforces const correctness
pub const ConstString = struct {
    pub fn find(haystack: []const u8, needle: []const u8) ?usize {
        if (haystack.len == 0 or needle.len == 0) return null;

        const result = c.strstr(haystack.ptr, needle.ptr);
        if (result == null) return null;

        const ptr_val: usize = @intFromPtr(result);
        const base_val: usize = @intFromPtr(haystack.ptr);
        return ptr_val - base_val;
    }

    pub fn findChar(str: []const u8, ch: u8) ?usize {
        const result = c.strchr(str.ptr, ch);
        if (result == null) return null;

        const ptr_val: usize = @intFromPtr(result);
        const base_val: usize = @intFromPtr(str.ptr);
        return ptr_val - base_val;
    }
};

test "const-correct string wrapper" {
    const text = "Hello, World!";

    const pos1 = ConstString.find(text, "World");
    try testing.expectEqual(@as(?usize, 7), pos1);

    const pos2 = ConstString.find(text, "Zig");
    try testing.expectEqual(@as(?usize, null), pos2);

    const pos3 = ConstString.findChar(text, 'W');
    try testing.expectEqual(@as(?usize, 7), pos3);
}
```

### Best Practices

1. **Error Handling**: Convert C error codes to Zig error types
2. **Memory Safety**: Add NULL checks and bounds validation
3. **Type Safety**: Use specific Zig types instead of raw pointers
4. **Resource Management**: Use RAII patterns with structs and `defer`
5. **Const Correctness**: Mark read-only parameters as `const`
6. **Documentation**: Document ownership and lifetime expectations
7. **Testing**: Write comprehensive tests for wrapped functions

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

//ANCHOR: c_library_import
// Import C standard library functions
const c = @cImport({
    @cInclude("stdlib.h");
    @cInclude("string.h");
    @cInclude("math.h");
    @cInclude("stdio.h");
});
// ANCHOR_END: c_library_import

// ANCHOR: basic_wrapper
// Wrapper for C malloc/free with Zig types
pub const CMemory = struct {
    pub fn alloc(size: usize) ?[*]u8 {
        const ptr = c.malloc(size);
        return @ptrCast(ptr);
    }

    pub fn free(ptr: ?[*]u8) void {
        c.free(ptr);
    }

    pub fn realloc(ptr: ?[*]u8, new_size: usize) ?[*]u8 {
        const new_ptr = c.realloc(ptr, new_size);
        return @ptrCast(new_ptr);
    }
};

test "wrapping C memory functions" {
    const ptr = CMemory.alloc(100);
    try testing.expect(ptr != null);

    if (ptr) |p| {
        p[0] = 42;
        try testing.expectEqual(@as(u8, 42), p[0]);

        const new_ptr = CMemory.realloc(p, 200);
        try testing.expect(new_ptr != null);

        if (new_ptr) |np| {
            try testing.expectEqual(@as(u8, 42), np[0]);
            CMemory.free(np);
        }
    }
}
// ANCHOR_END: basic_wrapper

// ANCHOR: error_handling_wrapper
// Wrap C functions with Zig error handling
pub const MathError = error{
    InvalidInput,
    DomainError,
    RangeError,
};

pub const SafeMath = struct {
    pub fn sqrt(x: f64) MathError!f64 {
        if (x < 0) return error.DomainError;
        return c.sqrt(x);
    }

    pub fn log(x: f64) MathError!f64 {
        if (x <= 0) return error.DomainError;
        return c.log(x);
    }

    pub fn pow(base: f64, exp: f64) MathError!f64 {
        const result = c.pow(base, exp);
        if (std.math.isNan(result)) return error.DomainError;
        if (std.math.isInf(result)) return error.RangeError;
        return result;
    }
};

test "error handling wrapper" {
    const result1 = try SafeMath.sqrt(16.0);
    try testing.expectApproxEqAbs(4.0, result1, 0.001);

    const result2 = SafeMath.sqrt(-1.0);
    try testing.expectError(error.DomainError, result2);

    const result3 = try SafeMath.log(std.math.e);
    try testing.expectApproxEqAbs(1.0, result3, 0.001);
}
// ANCHOR_END: error_handling_wrapper

// ANCHOR: string_wrapper
// Wrap C string functions with Zig slices
pub const CString = struct {
    pub fn length(str: [*:0]const u8) usize {
        return c.strlen(str);
    }

    pub fn compare(s1: [*:0]const u8, s2: [*:0]const u8) i32 {
        return c.strcmp(s1, s2);
    }

    pub fn copy(dest: [*]u8, src: [*:0]const u8, max_len: usize) [*]u8 {
        _ = c.strncpy(dest, src, max_len);
        return dest;
    }

    pub fn duplicate(allocator: std.mem.Allocator, str: [*:0]const u8) ![]u8 {
        const len = length(str);
        const buf = try allocator.alloc(u8, len);
        @memcpy(buf, str[0..len]);
        return buf;
    }
};

test "C string wrapper" {
    const str1 = "hello";
    const str2 = "world";

    const len = CString.length(str1.ptr);
    try testing.expectEqual(@as(usize, 5), len);

    var buffer: [20]u8 = undefined;
    _ = CString.copy(&buffer, str1.ptr, buffer.len);

    const allocator = testing.allocator;
    const dup = try CString.duplicate(allocator, str2.ptr);
    defer allocator.free(dup);
    try testing.expect(std.mem.eql(u8, dup, "world"));
}
// ANCHOR_END: string_wrapper

// ANCHOR: resource_wrapper
// RAII-style wrapper for C resources
pub const CFile = struct {
    handle: ?*c.FILE,

    pub fn open(path: [*:0]const u8, mode: [*:0]const u8) !CFile {
        const handle = c.fopen(path, mode);
        if (handle == null) return error.OpenFailed;
        return CFile{ .handle = handle };
    }

    pub fn close(self: *CFile) void {
        if (self.handle) |h| {
            _ = c.fclose(h);
            self.handle = null;
        }
    }

    pub fn write(self: *CFile, data: []const u8) !usize {
        const h = self.handle orelse return error.FileClosed;
        const written = c.fwrite(data.ptr, 1, data.len, h);
        if (written < data.len) return error.WriteFailed;
        return written;
    }

    pub fn read(self: *CFile, buffer: []u8) !usize {
        const h = self.handle orelse return error.FileClosed;
        const bytes_read = c.fread(buffer.ptr, 1, buffer.len, h);
        return bytes_read;
    }
};

test "RAII C file wrapper" {
    // Test file operations (in-memory for testing)
    const filename = "/tmp/test_zig_c_wrapper.txt";
    var file = try CFile.open(filename, "w");
    defer file.close();

    const data = "Hello from Zig!";
    _ = try file.write(data);
}
// ANCHOR_END: resource_wrapper

// ANCHOR: type_safe_wrapper
// Type-safe wrapper for C functions
pub const Allocator = struct {
    pub fn create(comptime T: type) !*T {
        const ptr = c.malloc(@sizeOf(T));
        if (ptr == null) return error.OutOfMemory;
        return @ptrCast(@alignCast(ptr.?));
    }

    pub fn destroy(comptime T: type, ptr: *T) void {
        c.free(ptr);
    }

    pub fn createArray(comptime T: type, count: usize) ![]T {
        const ptr = c.malloc(@sizeOf(T) * count);
        if (ptr == null) return error.OutOfMemory;
        const typed_ptr: [*]T = @ptrCast(@alignCast(ptr.?));
        return typed_ptr[0..count];
    }

    pub fn destroyArray(comptime T: type, slice: []T) void {
        c.free(slice.ptr);
    }
};

test "type-safe allocator wrapper" {
    const Point = struct { x: i32, y: i32 };

    const point = try Allocator.create(Point);
    point.* = .{ .x = 10, .y = 20 };
    try testing.expectEqual(@as(i32, 10), point.x);
    Allocator.destroy(Point, point);

    const points = try Allocator.createArray(Point, 3);
    points[0] = .{ .x = 1, .y = 2 };
    points[1] = .{ .x = 3, .y = 4 };
    points[2] = .{ .x = 5, .y = 6 };
    try testing.expectEqual(@as(i32, 3), points[1].x);
    Allocator.destroyArray(Point, points);
}
// ANCHOR_END: type_safe_wrapper

// ANCHOR: callback_wrapper
// Wrapper for C callbacks
pub const Comparator = struct {
    pub const CompareFunc = *const fn (a: ?*const anyopaque, b: ?*const anyopaque) callconv(.c) c_int;

    pub fn qsort(comptime T: type, slice: []T, compare_fn: CompareFunc) void {
        c.qsort(slice.ptr, slice.len, @sizeOf(T), compare_fn);
    }
};

fn compareInts(a: ?*const anyopaque, b: ?*const anyopaque) callconv(.c) c_int {
    const ia: *const c_int = @ptrCast(@alignCast(a.?));
    const ib: *const c_int = @ptrCast(@alignCast(b.?));
    if (ia.* < ib.*) return -1;
    if (ia.* > ib.*) return 1;
    return 0;
}

test "callback wrapper for qsort" {
    var numbers = [_]c_int{ 5, 2, 8, 1, 9, 3 };
    Comparator.qsort(c_int, &numbers, compareInts);

    try testing.expectEqual(@as(c_int, 1), numbers[0]);
    try testing.expectEqual(@as(c_int, 2), numbers[1]);
    try testing.expectEqual(@as(c_int, 3), numbers[2]);
    try testing.expectEqual(@as(c_int, 5), numbers[3]);
    try testing.expectEqual(@as(c_int, 8), numbers[4]);
    try testing.expectEqual(@as(c_int, 9), numbers[5]);
}
// ANCHOR_END: callback_wrapper

// ANCHOR: const_wrapper
// Wrapper that enforces const correctness
pub const ConstString = struct {
    pub fn find(haystack: []const u8, needle: []const u8) ?usize {
        if (haystack.len == 0 or needle.len == 0) return null;

        const result = c.strstr(haystack.ptr, needle.ptr);
        if (result == null) return null;

        const ptr_val: usize = @intFromPtr(result);
        const base_val: usize = @intFromPtr(haystack.ptr);
        return ptr_val - base_val;
    }

    pub fn findChar(str: []const u8, ch: u8) ?usize {
        const result = c.strchr(str.ptr, ch);
        if (result == null) return null;

        const ptr_val: usize = @intFromPtr(result);
        const base_val: usize = @intFromPtr(str.ptr);
        return ptr_val - base_val;
    }
};

test "const-correct string wrapper" {
    const text = "Hello, World!";

    const pos1 = ConstString.find(text, "World");
    try testing.expectEqual(@as(?usize, 7), pos1);

    const pos2 = ConstString.find(text, "Zig");
    try testing.expectEqual(@as(?usize, null), pos2);

    const pos3 = ConstString.findChar(text, 'W');
    try testing.expectEqual(@as(?usize, 7), pos3);
}
// ANCHOR_END: const_wrapper
```

### See Also

- Recipe 15.1: Accessing C Code from Zig
- Recipe 15.2: Writing a Zig Library Callable from C
- Recipe 15.7: Managing Memory Across the C/Zig Boundary

---

## Recipe 15.6: Passing NULL-terminated strings to C functions {#recipe-15-6}

**Tags:** allocators, c-interop, comptime, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/15-c-interoperability/recipe_15_6.zig`

### Problem

You need to work with C strings (NULL-terminated character arrays) from Zig code, handling conversions between Zig slices and C string conventions.

### Solution

Use Zig's sentinel-terminated pointer type `[*:0]const u8` for C strings:

```zig
// Using sentinel-terminated pointers for C strings
export fn get_string_length(str: [*:0]const u8) usize {
    return c.strlen(str);
}

test "sentinel-terminated pointers" {
    const text = "Hello, World!";
    const len = get_string_length(text.ptr);
    try testing.expectEqual(@as(usize, 13), len);
}
```

### Discussion

### Sentinel-Terminated Pointers

The `:0` in `[*:0]const u8` indicates a NULL-terminated pointer, matching C's string convention.

```zig
// Convert Zig string to C string
export fn process_zig_string(str: [*:0]const u8) c_int {
    var len: c_int = 0;
    while (str[@as(usize, @intCast(len))] != 0) {
        len += 1;
    }
    return len;
}

test "passing Zig strings to C" {
    const message = "Zig string";
    const result = process_zig_string(message.ptr);
    try testing.expectEqual(@as(c_int, 10), result);
}
```

### Allocating C Strings

Create NULL-terminated strings dynamically:

```zig
// Allocate NULL-terminated string for C
pub fn createCString(allocator: std.mem.Allocator, str: []const u8) ![*:0]u8 {
    const result = try allocator.allocSentinel(u8, str.len, 0);
    @memcpy(result, str);
    return result;
}

pub fn freeCString(allocator: std.mem.Allocator, str: [*:0]u8) void {
    const len = c.strlen(str);
    const slice = str[0 .. len + 1];
    allocator.free(slice);
}

test "allocating C strings" {
    const allocator = testing.allocator;
    const c_str = try createCString(allocator, "test string");
    defer freeCString(allocator, c_str);

    const len = c.strlen(c_str);
    try testing.expectEqual(@as(usize, 11), len);
}
```

Use `allocSentinel` to ensure the NULL terminator is included.

### String Conversion Utilities

Convert between Zig and C string representations:

```zig
// Convert between Zig and C strings
pub const StringConv = struct {
    pub fn fromC(str: [*:0]const u8) []const u8 {
        const len = c.strlen(str);
        return str[0..len];
    }

    pub fn toC(allocator: std.mem.Allocator, str: []const u8) ![*:0]u8 {
        return try allocator.dupeZ(u8, str);
    }

    pub fn freeC(allocator: std.mem.Allocator, str: [*:0]u8) void {
        const len = c.strlen(str);
        allocator.free(str[0 .. len + 1]);
    }
};

test "string conversion utilities" {
    const allocator = testing.allocator;

    // Zig to C
    const zig_str = "Hello from Zig";
    const c_str = try StringConv.toC(allocator, zig_str);
    defer StringConv.freeC(allocator, c_str);

    // C to Zig
    const back_to_zig = StringConv.fromC(c_str);
    try testing.expect(std.mem.eql(u8, back_to_zig, zig_str));
}
```

Helper methods:
- `fromC`: Convert C string to Zig slice
- `toC`: Allocate C string from Zig slice
- `freeC`: Free allocated C string properly

### Arrays of C Strings

Pass multiple strings to C:

```zig
// Working with arrays of C strings
export fn count_strings(strings: [*]const [*:0]const u8, count: usize) usize {
    var total_length: usize = 0;
    for (0..count) |i| {
        total_length += c.strlen(strings[i]);
    }
    return total_length;
}

test "array of C strings" {
    const str1 = "hello";
    const str2 = "world";
    const str3 = "test";

    const strings = [_][*:0]const u8{ str1.ptr, str2.ptr, str3.ptr };
    const total = count_strings(&strings, 3);
    try testing.expectEqual(@as(usize, 14), total);
}
```

### String Concatenation

Combine C strings safely:

```zig
// Concatenate C strings
pub fn concatenateCStrings(allocator: std.mem.Allocator, s1: [*:0]const u8, s2: [*:0]const u8) ![*:0]u8 {
    const len1 = c.strlen(s1);
    const len2 = c.strlen(s2);
    const result = try allocator.allocSentinel(u8, len1 + len2, 0);

    @memcpy(result[0..len1], s1[0..len1]);
    @memcpy(result[len1 .. len1 + len2], s2[0..len2]);

    return result;
}

test "concatenating C strings" {
    const allocator = testing.allocator;
    const s1 = "Hello, ";
    const s2 = "World!";

    const result = try concatenateCStrings(allocator, s1.ptr, s2.ptr);
    defer {
        const len = c.strlen(result);
        allocator.free(result[0 .. len + 1]);
    }

    const as_slice = StringConv.fromC(result);
    try testing.expect(std.mem.eql(u8, as_slice, "Hello, World!"));
}
```

### String Comparison

Use C comparison functions:

```zig
// String comparison with C functions
export fn compare_strings(s1: [*:0]const u8, s2: [*:0]const u8) c_int {
    return c.strcmp(s1, s2);
}

export fn compare_strings_n(s1: [*:0]const u8, s2: [*:0]const u8, n: usize) c_int {
    return c.strncmp(s1, s2, n);
}

test "string comparison" {
    const s1 = "apple";
    const s2 = "banana";
    const s3 = "apple";

    const cmp1 = compare_strings(s1.ptr, s2.ptr);
    try testing.expect(cmp1 < 0);

    const cmp2 = compare_strings(s1.ptr, s3.ptr);
    try testing.expectEqual(@as(c_int, 0), cmp2);

    const cmp3 = compare_strings_n(s1.ptr, s2.ptr, 1);
    try testing.expect(cmp3 < 0);
}
```

### String Search Operations

Find substrings and characters:

```zig
// Search operations on C strings
pub const StringSearch = struct {
    pub fn find(haystack: [*:0]const u8, needle: [*:0]const u8) ?[*:0]const u8 {
        const result = c.strstr(haystack, needle);
        return result;
    }

    pub fn findChar(str: [*:0]const u8, ch: c_int) ?[*:0]const u8 {
        const result = c.strchr(str, ch);
        return result;
    }

    pub fn findLastChar(str: [*:0]const u8, ch: c_int) ?[*:0]const u8 {
        const result = c.strrchr(str, ch);
        return result;
    }
};

test "string search operations" {
    const text = "Hello, World! Hello!";

    const found = StringSearch.find(text.ptr, "World");
    try testing.expect(found != null);

    const char_pos = StringSearch.findChar(text.ptr, 'W');
    try testing.expect(char_pos != null);

    const last_h = StringSearch.findLastChar(text.ptr, 'H');
    try testing.expect(last_h != null);
}
```

### String Manipulation

Modify strings in place or create copies:

```zig
// String manipulation with C functions
export fn to_uppercase_c(str: [*]u8, len: usize) void {
    for (0..len) |i| {
        if (str[i] >= 'a' and str[i] <= 'z') {
            str[i] -= 32;
        }
    }
}

export fn copy_string(dest: [*]u8, src: [*:0]const u8, max_len: usize) void {
    _ = c.strncpy(dest, src, max_len);
}

test "string manipulation" {
    var buffer: [20]u8 = undefined;

    // Copy string
    const source = "hello";
    copy_string(&buffer, source.ptr, buffer.len);

    // Convert to uppercase
    to_uppercase_c(&buffer, 5);

    try testing.expect(buffer[0] == 'H');
    try testing.expect(buffer[1] == 'E');
    try testing.expect(buffer[2] == 'L');
    try testing.expect(buffer[3] == 'L');
    try testing.expect(buffer[4] == 'O');
}
```

### Formatting C Strings

Format strings for C consumption:

```zig
// Format strings for C (similar to sprintf)
pub fn formatCString(allocator: std.mem.Allocator, comptime fmt: []const u8, args: anytype) ![*:0]u8 {
    const result = try std.fmt.allocPrint(allocator, fmt, args);
    defer allocator.free(result);
    return try allocator.dupeZ(u8, result);
}

test "formatting C strings" {
    const allocator = testing.allocator;

    const formatted = try formatCString(allocator, "Number: {d}, String: {s}", .{ 42, "test" });
    defer {
        const len = c.strlen(formatted);
        allocator.free(formatted[0 .. len + 1]);
    }

    const as_slice = StringConv.fromC(formatted);
    try testing.expect(std.mem.eql(u8, as_slice, "Number: 42, String: test"));
}
```

### Best Practices

1. **Use Sentinel Types**: Always use `[*:0]const u8` for C strings
2. **Allocate with Sentinel**: Use `allocSentinel` or `dupeZ` for allocations
3. **Free Correctly**: Remember to include the NULL terminator in the free size
4. **Check for NULL**: Validate pointers before dereferencing
5. **Prefer Slices**: Convert to Zig slices for safer manipulation
6. **Document Ownership**: Clearly specify who allocates and frees strings
7. **Use `.ptr`**: Access the pointer from string literals with `.ptr`

### Common Patterns

**Passing literal string to C:**
```zig
c_function("literal string".ptr);
```

**Converting C string to Zig:**
```zig
const zig_slice = c_str[0..std.mem.len(c_str)];
```

**Allocating C string:**
```zig
const c_str = try allocator.dupeZ(u8, zig_slice);
defer allocator.free(c_str[0..c_str.len + 1]);
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

const c = @cImport({
    @cInclude("string.h");
    @cInclude("stdlib.h");
});

// ANCHOR: sentinel_pointer
// Using sentinel-terminated pointers for C strings
export fn get_string_length(str: [*:0]const u8) usize {
    return c.strlen(str);
}

test "sentinel-terminated pointers" {
    const text = "Hello, World!";
    const len = get_string_length(text.ptr);
    try testing.expectEqual(@as(usize, 13), len);
}
// ANCHOR_END: sentinel_pointer

// ANCHOR: zig_to_c_string
// Convert Zig string to C string
export fn process_zig_string(str: [*:0]const u8) c_int {
    var len: c_int = 0;
    while (str[@as(usize, @intCast(len))] != 0) {
        len += 1;
    }
    return len;
}

test "passing Zig strings to C" {
    const message = "Zig string";
    const result = process_zig_string(message.ptr);
    try testing.expectEqual(@as(c_int, 10), result);
}
// ANCHOR_END: zig_to_c_string

// ANCHOR: allocate_c_string
// Allocate NULL-terminated string for C
pub fn createCString(allocator: std.mem.Allocator, str: []const u8) ![*:0]u8 {
    const result = try allocator.allocSentinel(u8, str.len, 0);
    @memcpy(result, str);
    return result;
}

pub fn freeCString(allocator: std.mem.Allocator, str: [*:0]u8) void {
    const len = c.strlen(str);
    const slice = str[0 .. len + 1];
    allocator.free(slice);
}

test "allocating C strings" {
    const allocator = testing.allocator;
    const c_str = try createCString(allocator, "test string");
    defer freeCString(allocator, c_str);

    const len = c.strlen(c_str);
    try testing.expectEqual(@as(usize, 11), len);
}
// ANCHOR_END: allocate_c_string

// ANCHOR: string_conversion
// Convert between Zig and C strings
pub const StringConv = struct {
    pub fn fromC(str: [*:0]const u8) []const u8 {
        const len = c.strlen(str);
        return str[0..len];
    }

    pub fn toC(allocator: std.mem.Allocator, str: []const u8) ![*:0]u8 {
        return try allocator.dupeZ(u8, str);
    }

    pub fn freeC(allocator: std.mem.Allocator, str: [*:0]u8) void {
        const len = c.strlen(str);
        allocator.free(str[0 .. len + 1]);
    }
};

test "string conversion utilities" {
    const allocator = testing.allocator;

    // Zig to C
    const zig_str = "Hello from Zig";
    const c_str = try StringConv.toC(allocator, zig_str);
    defer StringConv.freeC(allocator, c_str);

    // C to Zig
    const back_to_zig = StringConv.fromC(c_str);
    try testing.expect(std.mem.eql(u8, back_to_zig, zig_str));
}
// ANCHOR_END: string_conversion

// ANCHOR: string_array
// Working with arrays of C strings
export fn count_strings(strings: [*]const [*:0]const u8, count: usize) usize {
    var total_length: usize = 0;
    for (0..count) |i| {
        total_length += c.strlen(strings[i]);
    }
    return total_length;
}

test "array of C strings" {
    const str1 = "hello";
    const str2 = "world";
    const str3 = "test";

    const strings = [_][*:0]const u8{ str1.ptr, str2.ptr, str3.ptr };
    const total = count_strings(&strings, 3);
    try testing.expectEqual(@as(usize, 14), total);
}
// ANCHOR_END: string_array

// ANCHOR: string_concatenation
// Concatenate C strings
pub fn concatenateCStrings(allocator: std.mem.Allocator, s1: [*:0]const u8, s2: [*:0]const u8) ![*:0]u8 {
    const len1 = c.strlen(s1);
    const len2 = c.strlen(s2);
    const result = try allocator.allocSentinel(u8, len1 + len2, 0);

    @memcpy(result[0..len1], s1[0..len1]);
    @memcpy(result[len1 .. len1 + len2], s2[0..len2]);

    return result;
}

test "concatenating C strings" {
    const allocator = testing.allocator;
    const s1 = "Hello, ";
    const s2 = "World!";

    const result = try concatenateCStrings(allocator, s1.ptr, s2.ptr);
    defer {
        const len = c.strlen(result);
        allocator.free(result[0 .. len + 1]);
    }

    const as_slice = StringConv.fromC(result);
    try testing.expect(std.mem.eql(u8, as_slice, "Hello, World!"));
}
// ANCHOR_END: string_concatenation

// ANCHOR: string_comparison
// String comparison with C functions
export fn compare_strings(s1: [*:0]const u8, s2: [*:0]const u8) c_int {
    return c.strcmp(s1, s2);
}

export fn compare_strings_n(s1: [*:0]const u8, s2: [*:0]const u8, n: usize) c_int {
    return c.strncmp(s1, s2, n);
}

test "string comparison" {
    const s1 = "apple";
    const s2 = "banana";
    const s3 = "apple";

    const cmp1 = compare_strings(s1.ptr, s2.ptr);
    try testing.expect(cmp1 < 0);

    const cmp2 = compare_strings(s1.ptr, s3.ptr);
    try testing.expectEqual(@as(c_int, 0), cmp2);

    const cmp3 = compare_strings_n(s1.ptr, s2.ptr, 1);
    try testing.expect(cmp3 < 0);
}
// ANCHOR_END: string_comparison

// ANCHOR: string_search
// Search operations on C strings
pub const StringSearch = struct {
    pub fn find(haystack: [*:0]const u8, needle: [*:0]const u8) ?[*:0]const u8 {
        const result = c.strstr(haystack, needle);
        return result;
    }

    pub fn findChar(str: [*:0]const u8, ch: c_int) ?[*:0]const u8 {
        const result = c.strchr(str, ch);
        return result;
    }

    pub fn findLastChar(str: [*:0]const u8, ch: c_int) ?[*:0]const u8 {
        const result = c.strrchr(str, ch);
        return result;
    }
};

test "string search operations" {
    const text = "Hello, World! Hello!";

    const found = StringSearch.find(text.ptr, "World");
    try testing.expect(found != null);

    const char_pos = StringSearch.findChar(text.ptr, 'W');
    try testing.expect(char_pos != null);

    const last_h = StringSearch.findLastChar(text.ptr, 'H');
    try testing.expect(last_h != null);
}
// ANCHOR_END: string_search

// ANCHOR: string_manipulation
// String manipulation with C functions
export fn to_uppercase_c(str: [*]u8, len: usize) void {
    for (0..len) |i| {
        if (str[i] >= 'a' and str[i] <= 'z') {
            str[i] -= 32;
        }
    }
}

export fn copy_string(dest: [*]u8, src: [*:0]const u8, max_len: usize) void {
    _ = c.strncpy(dest, src, max_len);
}

test "string manipulation" {
    var buffer: [20]u8 = undefined;

    // Copy string
    const source = "hello";
    copy_string(&buffer, source.ptr, buffer.len);

    // Convert to uppercase
    to_uppercase_c(&buffer, 5);

    try testing.expect(buffer[0] == 'H');
    try testing.expect(buffer[1] == 'E');
    try testing.expect(buffer[2] == 'L');
    try testing.expect(buffer[3] == 'L');
    try testing.expect(buffer[4] == 'O');
}
// ANCHOR_END: string_manipulation

// ANCHOR: format_string
// Format strings for C (similar to sprintf)
pub fn formatCString(allocator: std.mem.Allocator, comptime fmt: []const u8, args: anytype) ![*:0]u8 {
    const result = try std.fmt.allocPrint(allocator, fmt, args);
    defer allocator.free(result);
    return try allocator.dupeZ(u8, result);
}

test "formatting C strings" {
    const allocator = testing.allocator;

    const formatted = try formatCString(allocator, "Number: {d}, String: {s}", .{ 42, "test" });
    defer {
        const len = c.strlen(formatted);
        allocator.free(formatted[0 .. len + 1]);
    }

    const as_slice = StringConv.fromC(formatted);
    try testing.expect(std.mem.eql(u8, as_slice, "Number: 42, String: test"));
}
// ANCHOR_END: format_string
```

### See Also

- Recipe 15.1: Accessing C Code from Zig
- Recipe 15.3: Passing Arrays Between C and Zig

---

## Recipe 15.7: Calling C functions with variadic arguments {#recipe-15-7}

**Tags:** allocators, c-interop, comptime, error-handling, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/15-c-interoperability/recipe_15_7.zig`

### Problem

You need to call C functions that accept a variable number of arguments (`printf`, `sprintf`, etc.) or create your own variadic functions for C interop.

### Solution

When calling C variadic functions, explicitly cast all literals to fixed-size types. For defining variadic functions, use `@cVaStart`, `@cVaArg`, and `@cVaEnd`.

```zig
// Calling C variadic functions (printf)
pub extern "c" fn printf(format: [*:0]const u8, ...) c_int;

test "calling printf" {
    // Must cast literals for variadic functions
    const result = printf("Number: %d, String: %s\n", @as(c_int, 42), "test");
    try testing.expect(result > 0);
}
```

### Discussion

### Calling C Variadic Functions

C's most common variadic function is `printf`:

```zig
// Using sprintf with variadic arguments
pub extern "c" fn sprintf(buf: [*]u8, format: [*:0]const u8, ...) c_int;

test "calling sprintf" {
    var buffer: [100]u8 = undefined;

    const written = sprintf(&buffer, "x=%d, y=%d", @as(c_int, 10), @as(c_int, 20));
    try testing.expect(written > 0);

    const result = buffer[0..@as(usize, @intCast(written))];
    try testing.expect(std.mem.eql(u8, result, "x=10, y=20"));
}
```

Key requirement: **All integer and float literals must be explicitly cast** to fixed-size types (`c_int`, `f64`, etc.) when passed to variadic functions.

### Defining Variadic Functions

Create your own variadic functions using special builtins:

```zig
// Define a variadic function in Zig
fn sum_integers(count: c_int, ...) callconv(.c) c_int {
    var ap = @cVaStart();
    defer @cVaEnd(&ap);

    var total: c_int = 0;
    var i: c_int = 0;
    while (i < count) : (i += 1) {
        total += @cVaArg(&ap, c_int);
    }

    return total;
}

test "defining variadic function" {
    // Skip on platforms with known issues
    if (builtin.cpu.arch == .aarch64 and builtin.os.tag != .macos) {
        return error.SkipZigTest;
    }
    if (builtin.cpu.arch == .x86_64 and builtin.os.tag == .windows) {
        return error.SkipZigTest;
    }

    try testing.expectEqual(@as(c_int, 0), sum_integers(0));
    try testing.expectEqual(@as(c_int, 5), sum_integers(1, @as(c_int, 5)));
    try testing.expectEqual(@as(c_int, 15), sum_integers(3, @as(c_int, 3), @as(c_int, 5), @as(c_int, 7)));
}
```

Builtins for variadic functions:
- `@cVaStart()` - Initialize argument list
- `@cVaArg(&ap, Type)` - Get next argument of Type
- `@cVaEnd(&ap)` - Clean up argument list

### Variadic Wrappers

Wrap C variadic functions with type-safe Zig interfaces:

```zig
// Wrapper for C variadic function
pub const Printf = struct {
    pub fn print(comptime fmt: []const u8, args: anytype) !void {
        // Build format string with proper specifiers
        var buffer: [1024]u8 = undefined;
        const result = try std.fmt.bufPrint(&buffer, fmt, args);

        _ = printf("%s", result.ptr);
    }

    pub fn printInt(value: i32) void {
        _ = printf("%d\n", @as(c_int, value));
    }

    pub fn printFloat(value: f64) void {
        _ = printf("%f\n", value);
    }

    pub fn printString(str: []const u8) void {
        _ = printf("%.*s\n", @as(c_int, @intCast(str.len)), str.ptr);
    }
};

test "variadic wrapper functions" {
    Printf.printInt(42);
    Printf.printFloat(3.14159);
    Printf.printString("Hello from wrapper");
}
```

### Type-Safe Alternatives

Instead of variadic functions, use explicit parameter lists when possible:

```zig
// Type-safe variadic wrapper
export fn print_values(format: [*:0]const u8, int_count: c_int, ints: [*]const c_int, str_count: c_int, strs: [*]const [*:0]const u8) c_int {
    // This is safer than true variadic functions
    // We know exactly what types and how many args we have
    _ = format;
    _ = int_count;
    _ = ints;
    _ = str_count;
    _ = strs;

    return 0;
}

test "type-safe variadic alternative" {
    const ints = [_]c_int{ 1, 2, 3 };
    const strs = [_][*:0]const u8{ "hello".ptr, "world".ptr };

    _ = print_values("fmt", 3, &ints, 2, &strs);
}
```

This approach:
- Provides type safety at compile time
- Eliminates runtime type confusion
- Is easier to debug and maintain

### Forwarding Variadic Arguments

Note that forwarding `va_list` between functions is limited in Zig:

```zig
// Forwarding variadic arguments
export fn log_message(level: c_int, format: [*:0]const u8, ...) c_int {
    // Prepend log level
    const level_str = switch (level) {
        0 => "DEBUG",
        1 => "INFO",
        2 => "WARN",
        3 => "ERROR",
        else => "UNKNOWN",
    };

    _ = printf("[%s] ", level_str.ptr);

    // Note: We can't easily forward va_list in Zig
    // Better to reconstruct the call
    _ = format;

    return 0;
}

test "forwarding variadic arguments" {
    _ = log_message(1, "Test message: %d\n", @as(c_int, 42));
}
```

### Mixed Type Arguments

Handle different types in a variadic function:

```zig
// Variadic function with mixed types
fn print_mixed(count: c_int, ...) callconv(.c) void {
    var ap = @cVaStart();
    defer @cVaEnd(&ap);

    var i: c_int = 0;
    while (i < count) : (i += 1) {
        // First arg is type indicator
        const type_id = @cVaArg(&ap, c_int);

        switch (type_id) {
            0 => { // int
                const value = @cVaArg(&ap, c_int);
                _ = printf("int: %d\n", value);
            },
            1 => { // double
                const value = @cVaArg(&ap, f64);
                _ = printf("double: %f\n", value);
            },
            2 => { // string
                const value = @cVaArg(&ap, [*:0]const u8);
                _ = printf("string: %s\n", value);
            },
            else => {},
        }
    }
}

test "mixed type variadic" {
    if (builtin.cpu.arch == .aarch64 and builtin.os.tag != .macos) {
        return error.SkipZigTest;
    }
    if (builtin.cpu.arch == .x86_64 and builtin.os.tag == .windows) {
        return error.SkipZigTest;
    }

    print_mixed(
        3,
        @as(c_int, 0),
        @as(c_int, 42), // int
        @as(c_int, 1),
        @as(f64, 3.14), // double
        @as(c_int, 2),
        "hello".ptr, // string
    );
}
```

This pattern uses type tags to identify argument types at runtime.

### Safer Alternatives

Use Zig's compile-time features instead of runtime variadic functions:

```zig
// Safer alternative to variadic functions using tuples
pub fn printFormatted(comptime fmt: []const u8, args: anytype) void {
    const result = std.fmt.allocPrint(std.heap.c_allocator, fmt, args) catch return;
    defer std.heap.c_allocator.free(result);

    _ = printf("%s", result.ptr);
}

test "safer tuple-based alternative" {
    printFormatted("Values: {d}, {s}, {d:.2}\n", .{ 42, "test", 3.14159 });
}
```

Benefits:
- Compile-time type checking
- No casting required
- Better error messages
- More idiomatic Zig

### Examining Arguments

Process variadic arguments in a loop:

```zig
// Examining variadic arguments
export fn count_non_zero(count: c_int, ...) c_int {
    var ap = @cVaStart();
    defer @cVaEnd(&ap);

    var non_zero: c_int = 0;
    var i: c_int = 0;

    while (i < count) : (i += 1) {
        const value = @cVaArg(&ap, c_int);
        if (value != 0) {
            non_zero += 1;
        }
    }

    return non_zero;
}

test "examining variadic arguments" {
    if (builtin.cpu.arch == .aarch64 and builtin.os.tag != .macos) {
        return error.SkipZigTest;
    }
    if (builtin.cpu.arch == .x86_64 and builtin.os.tag == .windows) {
        return error.SkipZigTest;
    }

    const result = count_non_zero(5, @as(c_int, 1), @as(c_int, 0), @as(c_int, 3), @as(c_int, 0), @as(c_int, 5));
    try testing.expectEqual(@as(c_int, 3), result);
}
```

### Best Practices

1. **Cast Literals**: Always cast integer/float literals to fixed-size types
2. **Prefer Tuples**: Use tuples (`anytype`) over variadic functions in Zig
3. **Type Tags**: Use type indicators when mixing types
4. **Limit Scope**: Keep variadic functions at the C boundary
5. **Document Types**: Clearly document expected argument types
6. **Error Handling**: Validate argument counts and types when possible
7. **Platform Testing**: Test on multiple platforms (varargs are platform-specific)

### Platform Limitations

Some platforms have limitations with variadic functions:
- **ARM64 (non-macOS)**: May skip tests due to ABI issues
- **Windows x86_64**: May skip tests due to calling convention differences

Always test variadic code on target platforms.

### Common Pitfalls

**Wrong: Missing casts**
```zig
printf("%d", 42);  // Error: must cast literal
```

**Right: Explicit casts**
```zig
printf("%d", @as(c_int, 42));  // Correct
```

**Wrong: Forgetting @cVaEnd**
```zig
fn bad(...) callconv(.c) void {
    var ap = @cVaStart();
    // Missing @cVaEnd(&ap)
}
```

**Right: Always cleanup**
```zig
fn good(...) callconv(.c) void {
    var ap = @cVaStart();
    defer @cVaEnd(&ap);  // Ensures cleanup
}
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;
const builtin = @import("builtin");

const c = @cImport({
    @cInclude("stdio.h");
    @cInclude("stdarg.h");
});

// ANCHOR: calling_printf
// Calling C variadic functions (printf)
pub extern "c" fn printf(format: [*:0]const u8, ...) c_int;

test "calling printf" {
    // Must cast literals for variadic functions
    const result = printf("Number: %d, String: %s\n", @as(c_int, 42), "test");
    try testing.expect(result > 0);
}
// ANCHOR_END: calling_printf

// ANCHOR: calling_sprintf
// Using sprintf with variadic arguments
pub extern "c" fn sprintf(buf: [*]u8, format: [*:0]const u8, ...) c_int;

test "calling sprintf" {
    var buffer: [100]u8 = undefined;

    const written = sprintf(&buffer, "x=%d, y=%d", @as(c_int, 10), @as(c_int, 20));
    try testing.expect(written > 0);

    const result = buffer[0..@as(usize, @intCast(written))];
    try testing.expect(std.mem.eql(u8, result, "x=10, y=20"));
}
// ANCHOR_END: calling_sprintf

// ANCHOR: defining_variadic
// Define a variadic function in Zig
fn sum_integers(count: c_int, ...) callconv(.c) c_int {
    var ap = @cVaStart();
    defer @cVaEnd(&ap);

    var total: c_int = 0;
    var i: c_int = 0;
    while (i < count) : (i += 1) {
        total += @cVaArg(&ap, c_int);
    }

    return total;
}

test "defining variadic function" {
    // Skip on platforms with known issues
    if (builtin.cpu.arch == .aarch64 and builtin.os.tag != .macos) {
        return error.SkipZigTest;
    }
    if (builtin.cpu.arch == .x86_64 and builtin.os.tag == .windows) {
        return error.SkipZigTest;
    }

    try testing.expectEqual(@as(c_int, 0), sum_integers(0));
    try testing.expectEqual(@as(c_int, 5), sum_integers(1, @as(c_int, 5)));
    try testing.expectEqual(@as(c_int, 15), sum_integers(3, @as(c_int, 3), @as(c_int, 5), @as(c_int, 7)));
}
// ANCHOR_END: defining_variadic

// ANCHOR: variadic_wrapper
// Wrapper for C variadic function
pub const Printf = struct {
    pub fn print(comptime fmt: []const u8, args: anytype) !void {
        // Build format string with proper specifiers
        var buffer: [1024]u8 = undefined;
        const result = try std.fmt.bufPrint(&buffer, fmt, args);

        _ = printf("%s", result.ptr);
    }

    pub fn printInt(value: i32) void {
        _ = printf("%d\n", @as(c_int, value));
    }

    pub fn printFloat(value: f64) void {
        _ = printf("%f\n", value);
    }

    pub fn printString(str: []const u8) void {
        _ = printf("%.*s\n", @as(c_int, @intCast(str.len)), str.ptr);
    }
};

test "variadic wrapper functions" {
    Printf.printInt(42);
    Printf.printFloat(3.14159);
    Printf.printString("Hello from wrapper");
}
// ANCHOR_END: variadic_wrapper

// ANCHOR: type_checking
// Type-safe variadic wrapper
export fn print_values(format: [*:0]const u8, int_count: c_int, ints: [*]const c_int, str_count: c_int, strs: [*]const [*:0]const u8) c_int {
    // This is safer than true variadic functions
    // We know exactly what types and how many args we have
    _ = format;
    _ = int_count;
    _ = ints;
    _ = str_count;
    _ = strs;

    return 0;
}

test "type-safe variadic alternative" {
    const ints = [_]c_int{ 1, 2, 3 };
    const strs = [_][*:0]const u8{ "hello".ptr, "world".ptr };

    _ = print_values("fmt", 3, &ints, 2, &strs);
}
// ANCHOR_END: type_checking

// ANCHOR: forwarding_varargs
// Forwarding variadic arguments
export fn log_message(level: c_int, format: [*:0]const u8, ...) c_int {
    // Prepend log level
    const level_str = switch (level) {
        0 => "DEBUG",
        1 => "INFO",
        2 => "WARN",
        3 => "ERROR",
        else => "UNKNOWN",
    };

    _ = printf("[%s] ", level_str.ptr);

    // Note: We can't easily forward va_list in Zig
    // Better to reconstruct the call
    _ = format;

    return 0;
}

test "forwarding variadic arguments" {
    _ = log_message(1, "Test message: %d\n", @as(c_int, 42));
}
// ANCHOR_END: forwarding_varargs

// ANCHOR: mixed_types
// Variadic function with mixed types
fn print_mixed(count: c_int, ...) callconv(.c) void {
    var ap = @cVaStart();
    defer @cVaEnd(&ap);

    var i: c_int = 0;
    while (i < count) : (i += 1) {
        // First arg is type indicator
        const type_id = @cVaArg(&ap, c_int);

        switch (type_id) {
            0 => { // int
                const value = @cVaArg(&ap, c_int);
                _ = printf("int: %d\n", value);
            },
            1 => { // double
                const value = @cVaArg(&ap, f64);
                _ = printf("double: %f\n", value);
            },
            2 => { // string
                const value = @cVaArg(&ap, [*:0]const u8);
                _ = printf("string: %s\n", value);
            },
            else => {},
        }
    }
}

test "mixed type variadic" {
    if (builtin.cpu.arch == .aarch64 and builtin.os.tag != .macos) {
        return error.SkipZigTest;
    }
    if (builtin.cpu.arch == .x86_64 and builtin.os.tag == .windows) {
        return error.SkipZigTest;
    }

    print_mixed(
        3,
        @as(c_int, 0),
        @as(c_int, 42), // int
        @as(c_int, 1),
        @as(f64, 3.14), // double
        @as(c_int, 2),
        "hello".ptr, // string
    );
}
// ANCHOR_END: mixed_types

// ANCHOR: safer_alternative
// Safer alternative to variadic functions using tuples
pub fn printFormatted(comptime fmt: []const u8, args: anytype) void {
    const result = std.fmt.allocPrint(std.heap.c_allocator, fmt, args) catch return;
    defer std.heap.c_allocator.free(result);

    _ = printf("%s", result.ptr);
}

test "safer tuple-based alternative" {
    printFormatted("Values: {d}, {s}, {d:.2}\n", .{ 42, "test", 3.14159 });
}
// ANCHOR_END: safer_alternative

// ANCHOR: examining_varargs
// Examining variadic arguments
export fn count_non_zero(count: c_int, ...) c_int {
    var ap = @cVaStart();
    defer @cVaEnd(&ap);

    var non_zero: c_int = 0;
    var i: c_int = 0;

    while (i < count) : (i += 1) {
        const value = @cVaArg(&ap, c_int);
        if (value != 0) {
            non_zero += 1;
        }
    }

    return non_zero;
}

test "examining variadic arguments" {
    if (builtin.cpu.arch == .aarch64 and builtin.os.tag != .macos) {
        return error.SkipZigTest;
    }
    if (builtin.cpu.arch == .x86_64 and builtin.os.tag == .windows) {
        return error.SkipZigTest;
    }

    const result = count_non_zero(5, @as(c_int, 1), @as(c_int, 0), @as(c_int, 3), @as(c_int, 0), @as(c_int, 5));
    try testing.expectEqual(@as(c_int, 3), result);
}
// ANCHOR_END: examining_varargs
```

### See Also

- Recipe 15.1: Accessing C Code from Zig
- Recipe 15.6: Passing NULL

---
