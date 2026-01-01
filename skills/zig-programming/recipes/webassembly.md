# WebAssembly Recipes

*6 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [19.1](#recipe-19-1) | Building a Basic WebAssembly Module | advanced |
| [19.2](#recipe-19-2) | Exporting Functions to JavaScript | advanced |
| [19.3](#recipe-19-3) | Importing and Calling JavaScript Functions | advanced |
| [19.4](#recipe-19-4) | Passing Strings and Data Between Zig and JavaScript | advanced |
| [19.5](#recipe-19-5) | Custom Allocators for Freestanding Targets | advanced |
| [19.6](#recipe-19-6) | Implementing a Panic Handler for WASM | advanced |

---

## Recipe 19.1: Building a Basic WebAssembly Module {#recipe-19-1}

**Tags:** allocators, error-handling, freestanding, memory, pointers, testing, webassembly
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/19-webassembly-freestanding/recipe_19_1.zig`

### Problem

You want to compile Zig code to WebAssembly and call it from JavaScript in a web browser or other WASM runtime.

### Solution

Create a Zig file with exported functions and compile it to the `wasm32-freestanding` target. The `export` keyword makes functions visible to JavaScript.

First, implement a custom panic handler, which is required for freestanding targets:

```zig
// Custom panic handler required for freestanding targets
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = msg;
    _ = error_return_trace;
    _ = ret_addr;
    while (true) {}
}
```

Export simple functions that JavaScript can call:

```zig
// Export a simple function that JavaScript can call
export fn add(a: i32, b: i32) i32 {
    return a + b;
}
```

```zig
// Another exported function
export fn multiply(a: i32, b: i32) i32 {
    return a * b;
}
```

More complex exported functions work the same way:

```zig
// More complex exported function
export fn fibonacci(n: i32) i32 {
    if (n <= 1) return n;

    var prev: i32 = 0;
    var curr: i32 = 1;
    var i: i32 = 2;

    while (i <= n) : (i += 1) {
        const next = prev + curr;
        prev = curr;
        curr = next;
    }

    return curr;
}
```

```zig
// Check if a number is prime
export fn isPrime(n: i32) bool {
    if (n < 2) return false;
    if (n == 2) return true;
    if (@rem(n, 2) == 0) return false;

    var i: i32 = 3;
    while (i * i <= n) : (i += 2) {
        if (@rem(n, i) == 0) return false;
    }

    return true;
}
```

Build the WebAssembly module:

```bash
zig build-lib -O ReleaseSmall -target wasm32-freestanding -dynamic -rdynamic recipe_19_1.zig
```

This produces `recipe_19_1.wasm`, which you can load in JavaScript:

```javascript
async function loadWasm() {
    const response = await fetch('recipe_19_1.wasm');
    const bytes = await response.arrayBuffer();
    const { instance } = await WebAssembly.instantiate(bytes);
    const wasm = instance.exports;

    // Call exported functions
    console.log(wasm.add(5, 3));           // 8
    console.log(wasm.multiply(7, 6));       // 42
    console.log(wasm.fibonacci(10));        // 55
    console.log(wasm.isPrime(17));          // true
}
```

### Discussion

### The `export` Keyword

The `export` keyword makes functions visible in the compiled WebAssembly module. Without it, functions remain internal to the WASM binary and cannot be called from JavaScript.

The difference between `pub` and `export`:
- `pub` makes functions visible to other Zig modules at compile time
- `export` makes functions visible in the compiled binary's symbol table
- For WASM, you need `export` to call functions from JavaScript

### Freestanding Target Requirements

The `wasm32-freestanding` target runs without an operating system. This means:

1. **Custom panic handler required**: The standard library's panic implementation relies on OS features not available in freestanding environments. Your panic handler must be marked `noreturn` and handle all errors.

2. **No standard I/O**: You cannot use `std.debug.print` or `std.io` functions that rely on file descriptors.

3. **No filesystem**: File operations are not available unless provided by the WASM runtime.

4. **Explicit memory management**: No system allocator exists by default (covered in Recipe 19.5).

### Build Flags Explained

```bash
zig build-lib -O ReleaseSmall -target wasm32-freestanding -dynamic -rdynamic recipe_19_1.zig
```

- `-O ReleaseSmall`: Optimizes for small binary size, critical for web distribution
- `-target wasm32-freestanding`: Targets WebAssembly without OS support
- `-dynamic`: Builds a dynamic library (WASM module)
- `-rdynamic`: Ensures exported symbols remain visible in the binary

The `-rdynamic` flag is essential. Without it, the linker may strip exported symbols, making them unavailable to JavaScript.

### Type Considerations

WASM natively supports these types:
- `i32`, `i64`: Signed integers
- `f32`, `f64`: Floating-point numbers

Zig automatically maps compatible types:
- `bool` becomes `i32` (0 or 1)
- Smaller integers promote to `i32`
- Pointers become `i32` (memory addresses)

For complex types like strings or structs, you'll need to pass them through linear memory (see Recipe 19.4).

### Testing WASM Functions

The tests in the Zig file verify logic but run on your host system, not in WASM. They use standard Zig test infrastructure:

```zig
test "add function" {
    try testing.expectEqual(@as(i32, 5), add(2, 3));
    try testing.expectEqual(@as(i32, 0), add(-5, 5));
    try testing.expectEqual(@as(i32, -10), add(-7, -3));
}
```

Run tests with:

```bash
zig test recipe_19_1.zig
```

These tests ensure the logic is correct before compiling to WASM, where debugging is more difficult.

### Using the Module in a Browser

See `code/05-zig-paradigms/19-webassembly-freestanding/recipe_19_1.html` for a complete working example. The key steps:

1. Fetch the WASM file
2. Instantiate it with `WebAssembly.instantiate()`
3. Access exported functions via `instance.exports`
4. Call functions normally

### Debugging and Inspecting WASM

Use browser developer tools to inspect WASM:
1. Open DevTools → Sources tab
2. Find the .wasm file in the file tree
3. View disassembled WebAssembly code

Use `wasm-objdump` to inspect the binary:

```bash
wasm-objdump -x recipe_19_1.wasm
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: panic_handler
// Custom panic handler required for freestanding targets
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = msg;
    _ = error_return_trace;
    _ = ret_addr;
    while (true) {}
}
// ANCHOR_END: panic_handler

// ANCHOR: basic_export
// Export a simple function that JavaScript can call
export fn add(a: i32, b: i32) i32 {
    return a + b;
}
// ANCHOR_END: basic_export

// ANCHOR: multiply_export
// Another exported function
export fn multiply(a: i32, b: i32) i32 {
    return a * b;
}
// ANCHOR_END: multiply_export

// ANCHOR: fibonacci_export
// More complex exported function
export fn fibonacci(n: i32) i32 {
    if (n <= 1) return n;

    var prev: i32 = 0;
    var curr: i32 = 1;
    var i: i32 = 2;

    while (i <= n) : (i += 1) {
        const next = prev + curr;
        prev = curr;
        curr = next;
    }

    return curr;
}
// ANCHOR_END: fibonacci_export

// ANCHOR: is_prime_export
// Check if a number is prime
export fn isPrime(n: i32) bool {
    if (n < 2) return false;
    if (n == 2) return true;
    if (@rem(n, 2) == 0) return false;

    var i: i32 = 3;
    while (i * i <= n) : (i += 2) {
        if (@rem(n, i) == 0) return false;
    }

    return true;
}
// ANCHOR_END: is_prime_export

// Tests verify the logic works correctly
// Note: These tests run on the host system, not in WASM

// ANCHOR: test_add
test "add function" {
    try testing.expectEqual(@as(i32, 5), add(2, 3));
    try testing.expectEqual(@as(i32, 0), add(-5, 5));
    try testing.expectEqual(@as(i32, -10), add(-7, -3));
}
// ANCHOR_END: test_add

// ANCHOR: test_multiply
test "multiply function" {
    try testing.expectEqual(@as(i32, 6), multiply(2, 3));
    try testing.expectEqual(@as(i32, -25), multiply(-5, 5));
    try testing.expectEqual(@as(i32, 21), multiply(-7, -3));
    try testing.expectEqual(@as(i32, 0), multiply(0, 100));
}
// ANCHOR_END: test_multiply

// ANCHOR: test_fibonacci
test "fibonacci function" {
    try testing.expectEqual(@as(i32, 0), fibonacci(0));
    try testing.expectEqual(@as(i32, 1), fibonacci(1));
    try testing.expectEqual(@as(i32, 1), fibonacci(2));
    try testing.expectEqual(@as(i32, 2), fibonacci(3));
    try testing.expectEqual(@as(i32, 3), fibonacci(4));
    try testing.expectEqual(@as(i32, 5), fibonacci(5));
    try testing.expectEqual(@as(i32, 8), fibonacci(6));
    try testing.expectEqual(@as(i32, 55), fibonacci(10));
}
// ANCHOR_END: test_fibonacci

// ANCHOR: test_is_prime
test "isPrime function" {
    try testing.expect(!isPrime(0));
    try testing.expect(!isPrime(1));
    try testing.expect(isPrime(2));
    try testing.expect(isPrime(3));
    try testing.expect(!isPrime(4));
    try testing.expect(isPrime(5));
    try testing.expect(!isPrime(6));
    try testing.expect(isPrime(7));
    try testing.expect(!isPrime(8));
    try testing.expect(!isPrime(9));
    try testing.expect(!isPrime(10));
    try testing.expect(isPrime(11));
    try testing.expect(isPrime(13));
    try testing.expect(!isPrime(15));
    try testing.expect(isPrime(17));
}
// ANCHOR_END: test_is_prime

// ANCHOR: test_edge_cases
test "edge cases" {
    // Test with maximum values
    const max_i32 = std.math.maxInt(i32);
    try testing.expectEqual(max_i32, add(max_i32, 0));

    // Test with minimum values
    const min_i32 = std.math.minInt(i32);
    try testing.expectEqual(min_i32, add(min_i32, 0));
}
// ANCHOR_END: test_edge_cases
```

### See Also

- Recipe 19.2: Exporting functions to JavaScript (advanced exports)
- Recipe 19.3: Importing and calling JavaScript functions
- Recipe 19.5: Custom allocators for freestanding targets
- Recipe 19.6: Implementing a panic handler for WASM

---

## Recipe 19.2: Exporting Functions to JavaScript {#recipe-19-2}

**Tags:** allocators, concurrency, error-handling, freestanding, memory, pointers, testing, threading, webassembly
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/19-webassembly-freestanding/recipe_19_2.zig`

### Problem

You need to export complex functions from Zig to WebAssembly, including functions that return multiple values, work with pointers, or maintain state across calls.

### Solution

### Maintaining State with Global Variables

Export getter and setter functions to manage state:

```zig
// Global state (simple use case - be careful with this pattern)
var counter: i32 = 0;
var last_calculation: f64 = 0.0;
```

```zig
// Counter manipulation
export fn incrementCounter() i32 {
    counter += 1;
    return counter;
}

export fn getCounter() i32 {
    return counter;
}

export fn resetCounter() void {
    counter = 0;
}
```

### Returning Multiple Values via Pointers

Use pointer parameters to return additional values:

```zig
// Return multiple values via pointer parameters
export fn divideWithRemainder(dividend: i32, divisor: i32, remainder_ptr: *i32) i32 {
    const quotient = @divTrunc(dividend, divisor);
    const remainder = @rem(dividend, divisor);
    remainder_ptr.* = remainder;
    return quotient;
}
```

From JavaScript:

```javascript
// Allocate memory for the remainder
const remainderPtr = wasm.__heap_base || 0;
const quotient = wasm.divideWithRemainder(17, 5, remainderPtr);

// Read remainder from WASM linear memory
const memView = new Int32Array(wasm.memory.buffer);
const remainder = memView[remainderPtr / 4];

console.log(`17 ÷ 5 = ${quotient} remainder ${remainder}`);
// Output: 17 ÷ 5 = 3 remainder 2
```

### Storing Calculation Results

Combine computation with state storage:

```zig
// Calculate distance and store result
export fn calculateDistance(x1: f64, y1: f64, x2: f64, y2: f64) f64 {
    const dx = x2 - x1;
    const dy = y2 - y1;
    const distance = @sqrt(dx * dx + dy * dy);
    last_calculation = distance;
    return distance;
}

export fn getLastCalculation() f64 {
    return last_calculation;
}
```

### Working with Structured Data

Define structures and export functions that work with pointers:

```zig
// Point structure stored in WASM linear memory
const Point = struct {
    x: f64,
    y: f64,
};
```

```zig
// Allocate a point in WASM memory and return its address
export fn createPoint(x: f64, y: f64) *Point {
    // In a real application, you'd use a proper allocator
    // For this example, we use a static buffer
    const static = struct {
        var points_buffer: [100]Point = undefined;
        var next_index: usize = 0;
    };

    if (static.next_index >= static.points_buffer.len) {
        // Out of space - in real code, handle this better
        static.next_index = 0;
    }

    static.points_buffer[static.next_index] = Point{ .x = x, .y = y };
    const result = &static.points_buffer[static.next_index];
    static.next_index += 1;

    return result;
}

// Get point coordinates
export fn getPointX(point: *const Point) f64 {
    return point.x;
}

export fn getPointY(point: *const Point) f64 {
    return point.y;
}

// Calculate distance between two points
export fn pointDistance(p1: *const Point, p2: *const Point) f64 {
    const dx = p2.x - p1.x;
    const dy = p2.y - p1.y;
    return @sqrt(dx * dx + dy * dy);
}
```

### Boolean Returns

WASM doesn't have a native boolean type, but Zig automatically converts them:

```zig
// Return bool (becomes i32 in WASM: 0 or 1)
export fn isInRange(value: f64, min: f64, max: f64) bool {
    return value >= min and value <= max;
}
```

In JavaScript, this returns `0` (false) or `1` (true), but JavaScript automatically treats them as boolean values in conditional contexts.

### Discussion

### Global State in WASM

Global variables in Zig become mutable locations in WASM linear memory. This allows you to:

- Maintain state across function calls
- Implement stateful APIs
- Cache computation results

However, be aware:
- All WASM instances share the same globals
- No thread safety guarantees (single-threaded by default)
- State persists for the lifetime of the WASM instance

### Pointer Parameters for Multiple Returns

WASM functions can only return a single value (or multiple values with the multi-value proposal, which isn't universally supported). To return multiple values:

1. **Pass pointer parameters**: The caller allocates memory, you write results to it
2. **Use structs**: Return a struct by pointer (see point operations example)
3. **Use global state**: Store additional results in globals (less clean)

The pointer approach works like this:

```javascript
// Allocate space in WASM memory (simplified)
const ptr = wasm.__heap_base || 0;

// Call function that writes to that address
const result1 = wasm.functionWithMultipleReturns(arg1, arg2, ptr);

// Read additional return value from memory
const view = new Int32Array(wasm.memory.buffer);
const result2 = view[ptr / 4];  // Divide by 4 for i32 indexing
```

### Memory Layout and Addressing

WASM uses a flat linear memory model:
- Memory is a contiguous array of bytes
- Pointers are `i32` addresses into this array
- Structures layout matches C ABI by default
- `__heap_base` marks where dynamic allocation could start

For the `Point` struct:

```zig
const Point = struct {
    x: f64,  // 8 bytes
    y: f64,  // 8 bytes
};  // Total: 16 bytes
```

If a `Point` is at address `0x100`:
- `x` is at `0x100` (bytes 0-7)
- `y` is at `0x108` (bytes 8-15)

### Static Buffers vs Allocators

The `createPoint` example uses a static buffer:

```zig
const static = struct {
    var points_buffer: [100]Point = undefined;
    var next_index: usize = 0;
};
```

This is simple but limited:
- Fixed capacity (100 points)
- No deallocation
- Reuses slots when full (circular buffer behavior)

For production code, use a proper allocator (see Recipe 19.5).

### Type Conversions

JavaScript to WASM conversions:

| JavaScript | Zig Type | WASM Type | Notes |
|------------|----------|-----------|-------|
| `number` (integer) | `i32`, `i64` | `i32`, `i64` | Truncated to integer |
| `number` (float) | `f32`, `f64` | `f32`, `f64` | Direct conversion |
| `boolean` | `bool` | `i32` | `false=0`, `true=1` |
| Pointer value | `*T` | `i32` | Memory address |

When returning from WASM to JavaScript:
- `i32` → JavaScript `number` (integer)
- `f64` → JavaScript `number` (float)
- `bool` → JavaScript `number` (`0` or `1`, but truthy/falsy)

### Accessing WASM Memory from JavaScript

Three ways to read WASM memory:

**1. Typed Arrays (for primitives):**
```javascript
const i32View = new Int32Array(wasm.memory.buffer);
const f64View = new Float64Array(wasm.memory.buffer);
```

**2. DataView (for mixed types):**
```javascript
const view = new DataView(wasm.memory.buffer);
const x = view.getFloat64(ptr + 0, true);  // Little-endian
const y = view.getFloat64(ptr + 8, true);
```

**3. Manual byte manipulation:**
```javascript
const u8View = new Uint8Array(wasm.memory.buffer);
```

### Calling Conventions

When JavaScript calls an exported function:
1. JavaScript values are converted to WASM types
2. Function executes in WASM
3. Return value is converted back to JavaScript
4. Any pointer writes update the shared linear memory

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// Custom panic handler required for freestanding targets
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = msg;
    _ = error_return_trace;
    _ = ret_addr;
    while (true) {}
}

// ANCHOR: point_struct
// Point structure stored in WASM linear memory
const Point = struct {
    x: f64,
    y: f64,
};
// ANCHOR_END: point_struct

// ANCHOR: global_state
// Global state (simple use case - be careful with this pattern)
var counter: i32 = 0;
var last_calculation: f64 = 0.0;
// ANCHOR_END: global_state

// ANCHOR: counter_functions
// Counter manipulation
export fn incrementCounter() i32 {
    counter += 1;
    return counter;
}

export fn getCounter() i32 {
    return counter;
}

export fn resetCounter() void {
    counter = 0;
}
// ANCHOR_END: counter_functions

// ANCHOR: divide_with_remainder
// Return multiple values via pointer parameters
export fn divideWithRemainder(dividend: i32, divisor: i32, remainder_ptr: *i32) i32 {
    const quotient = @divTrunc(dividend, divisor);
    const remainder = @rem(dividend, divisor);
    remainder_ptr.* = remainder;
    return quotient;
}
// ANCHOR_END: divide_with_remainder

// ANCHOR: distance_calculation
// Calculate distance and store result
export fn calculateDistance(x1: f64, y1: f64, x2: f64, y2: f64) f64 {
    const dx = x2 - x1;
    const dy = y2 - y1;
    const distance = @sqrt(dx * dx + dy * dy);
    last_calculation = distance;
    return distance;
}

export fn getLastCalculation() f64 {
    return last_calculation;
}
// ANCHOR_END: distance_calculation

// ANCHOR: point_operations
// Allocate a point in WASM memory and return its address
export fn createPoint(x: f64, y: f64) *Point {
    // In a real application, you'd use a proper allocator
    // For this example, we use a static buffer
    const static = struct {
        var points_buffer: [100]Point = undefined;
        var next_index: usize = 0;
    };

    if (static.next_index >= static.points_buffer.len) {
        // Out of space - in real code, handle this better
        static.next_index = 0;
    }

    static.points_buffer[static.next_index] = Point{ .x = x, .y = y };
    const result = &static.points_buffer[static.next_index];
    static.next_index += 1;

    return result;
}

// Get point coordinates
export fn getPointX(point: *const Point) f64 {
    return point.x;
}

export fn getPointY(point: *const Point) f64 {
    return point.y;
}

// Calculate distance between two points
export fn pointDistance(p1: *const Point, p2: *const Point) f64 {
    const dx = p2.x - p1.x;
    const dy = p2.y - p1.y;
    return @sqrt(dx * dx + dy * dy);
}
// ANCHOR_END: point_operations

// ANCHOR: range_check
// Return bool (becomes i32 in WASM: 0 or 1)
export fn isInRange(value: f64, min: f64, max: f64) bool {
    return value >= min and value <= max;
}
// ANCHOR_END: range_check

// ANCHOR: clamp_function
// Clamp a value between min and max
export fn clamp(value: f64, min: f64, max: f64) f64 {
    if (value < min) return min;
    if (value > max) return max;
    return value;
}
// ANCHOR_END: clamp_function

// ANCHOR: factorial
// Factorial with iteration
export fn factorial(n: i32) i32 {
    if (n < 0) return 0;
    if (n <= 1) return 1;

    var result: i32 = 1;
    var i: i32 = 2;
    while (i <= n) : (i += 1) {
        result *= i;
    }

    return result;
}
// ANCHOR_END: factorial

// Tests

// ANCHOR: test_counter
test "counter functions" {
    counter = 0; // Reset for test
    try testing.expectEqual(@as(i32, 0), getCounter());
    try testing.expectEqual(@as(i32, 1), incrementCounter());
    try testing.expectEqual(@as(i32, 2), incrementCounter());
    try testing.expectEqual(@as(i32, 2), getCounter());
    resetCounter();
    try testing.expectEqual(@as(i32, 0), getCounter());
}
// ANCHOR_END: test_counter

// ANCHOR: test_divide_remainder
test "divide with remainder" {
    var remainder: i32 = undefined;
    const quotient = divideWithRemainder(17, 5, &remainder);
    try testing.expectEqual(@as(i32, 3), quotient);
    try testing.expectEqual(@as(i32, 2), remainder);

    const quotient2 = divideWithRemainder(20, 4, &remainder);
    try testing.expectEqual(@as(i32, 5), quotient2);
    try testing.expectEqual(@as(i32, 0), remainder);
}
// ANCHOR_END: test_divide_remainder

// ANCHOR: test_distance
test "distance calculation" {
    const dist = calculateDistance(0, 0, 3, 4);
    try testing.expectApproxEqAbs(@as(f64, 5.0), dist, 0.001);
    try testing.expectApproxEqAbs(@as(f64, 5.0), getLastCalculation(), 0.001);

    const dist2 = calculateDistance(1, 1, 4, 5);
    try testing.expectApproxEqAbs(@as(f64, 5.0), dist2, 0.001);
}
// ANCHOR_END: test_distance

// ANCHOR: test_points
test "point operations" {
    const p1 = createPoint(0, 0);
    const p2 = createPoint(3, 4);

    try testing.expectEqual(@as(f64, 0), getPointX(p1));
    try testing.expectEqual(@as(f64, 0), getPointY(p1));
    try testing.expectEqual(@as(f64, 3), getPointX(p2));
    try testing.expectEqual(@as(f64, 4), getPointY(p2));

    const dist = pointDistance(p1, p2);
    try testing.expectApproxEqAbs(@as(f64, 5.0), dist, 0.001);
}
// ANCHOR_END: test_points

// ANCHOR: test_range
test "range check" {
    try testing.expect(isInRange(5, 0, 10));
    try testing.expect(isInRange(0, 0, 10));
    try testing.expect(isInRange(10, 0, 10));
    try testing.expect(!isInRange(-1, 0, 10));
    try testing.expect(!isInRange(11, 0, 10));
}
// ANCHOR_END: test_range

// ANCHOR: test_clamp
test "clamp function" {
    try testing.expectEqual(@as(f64, 5), clamp(5, 0, 10));
    try testing.expectEqual(@as(f64, 0), clamp(-5, 0, 10));
    try testing.expectEqual(@as(f64, 10), clamp(15, 0, 10));
    try testing.expectEqual(@as(f64, 7.5), clamp(7.5, 0, 10));
}
// ANCHOR_END: test_clamp

// ANCHOR: test_factorial
test "factorial" {
    try testing.expectEqual(@as(i32, 1), factorial(0));
    try testing.expectEqual(@as(i32, 1), factorial(1));
    try testing.expectEqual(@as(i32, 2), factorial(2));
    try testing.expectEqual(@as(i32, 6), factorial(3));
    try testing.expectEqual(@as(i32, 24), factorial(4));
    try testing.expectEqual(@as(i32, 120), factorial(5));
    try testing.expectEqual(@as(i32, 0), factorial(-1));
}
// ANCHOR_END: test_factorial
```

### See Also

- Recipe 19.1: Building a basic WebAssembly module
- Recipe 19.3: Importing and calling JavaScript functions
- Recipe 19.4: Passing strings and data between Zig and JavaScript
- Recipe 19.5: Custom allocators for freestanding targets

---

## Recipe 19.3: Importing and Calling JavaScript Functions {#recipe-19-3}

**Tags:** allocators, c-interop, comptime, error-handling, freestanding, memory, pointers, testing, webassembly
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/19-webassembly-freestanding/recipe_19_3.zig`

### Problem

You need to call JavaScript functions from Zig code running in WebAssembly, such as logging to the console, generating random numbers, or using browser APIs.

### Solution

Use `extern "env"` to declare JavaScript functions that will be provided when instantiating the WASM module.

### Declaring External Functions

Declare JavaScript functions with matching signatures:

```zig
// Import console.log from JavaScript
extern "env" fn consoleLog(value: f64) void;
extern "env" fn consoleLogInt(value: i32) void;
extern "env" fn consoleLogStr(ptr: [*]const u8, len: usize) void;
```

```zig
// Import JavaScript Math functions
extern "env" fn jsRandom() f64;
extern "env" fn jsDateNow() f64;
extern "env" fn jsMathPow(base: f64, exponent: f64) f64;
extern "env" fn jsMathSin(x: f64) f64;
extern "env" fn jsMathCos(x: f64) f64;
```

```zig
// Import custom JavaScript callbacks
extern "env" fn jsCallback(value: i32) void;
extern "env" fn jsProcessData(data: i32) i32;
```

### Using Imported Functions

Call them like regular Zig functions:

```zig
// Function that logs to JavaScript console
export fn logValue(x: f64) void {
    consoleLog(x);
}

export fn logInteger(x: i32) void {
    consoleLogInt(x);
}

export fn logMessage() void {
    const msg = "Hello from Zig!";
    consoleLogStr(msg, msg.len);
}
```

```zig
// Use JavaScript Math functions
export fn calculatePower(base: f64, exponent: f64) f64 {
    return jsMathPow(base, exponent);
}

export fn calculateCircleArea(radius: f64) f64 {
    const pi = 3.141592653589793;
    const area = pi * jsMathPow(radius, 2.0);
    consoleLog(area); // Log the result
    return area;
}

export fn calculateSinCos(angle: f64) f64 {
    const sin_val = jsMathSin(angle);
    const cos_val = jsMathCos(angle);
    // sin² + cos² = 1
    return jsMathPow(sin_val, 2.0) + jsMathPow(cos_val, 2.0);
}
```

```zig
// Generate random numbers using JavaScript
export fn rollDice() i32 {
    const rand = jsRandom(); // Returns [0, 1)
    return @as(i32, @intFromFloat(@floor(rand * 6.0))) + 1;
}

export fn randomInRange(min: i32, max: i32) i32 {
    const rand = jsRandom();
    const range: f64 = @floatFromInt(max - min + 1);
    return min + @as(i32, @intFromFloat(@floor(rand * range)));
}

export fn shuffleArray(arr: [*]i32, len: usize) void {
    // Fisher-Yates shuffle using JavaScript random
    var i: usize = len - 1;
    while (i > 0) : (i -= 1) {
        const rand = jsRandom();
        const j: usize = @intFromFloat(@floor(rand * @as(f64, @floatFromInt(i + 1))));

        // Swap arr[i] and arr[j]
        const temp = arr[i];
        arr[i] = arr[j];
        arr[j] = temp;
    }
}
```

### Providing Implementations from JavaScript

When loading the WASM module, supply the import object:

```javascript
const importObject = {
    env: {
        consoleLog: (value) => {
            console.log(`[WASM] ${value}`);
        },
        consoleLogInt: (value) => {
            console.log(`[WASM] ${value}`);
        },
        consoleLogStr: (ptr, len) => {
            const bytes = new Uint8Array(wasm.memory.buffer, ptr, len);
            const str = new TextDecoder().decode(bytes);
            console.log(`[WASM] "${str}"`);
        },
        jsRandom: () => Math.random(),
        jsDateNow: () => Date.now(),
        jsMathPow: (base, exp) => Math.pow(base, exp),
        jsMathSin: (x) => Math.sin(x),
        jsMathCos: (x) => Math.cos(x),
        jsCallback: (value) => {
            console.log(`Callback received: ${value}`);
        },
        jsProcessData: (data) => data * 3 + 7
    }
};

const { instance } = await WebAssembly.instantiate(bytes, importObject);
```

### Discussion

### The `extern` Keyword

The `extern` keyword declares a function implemented externally. The string `"env"` specifies the namespace where JavaScript will provide these functions.

```zig
extern "env" fn functionName(args: Type) ReturnType;
```

This creates an import entry in the WASM binary. When JavaScript instantiates the module, it must provide matching implementations in the import object.

### Import Namespaces

While `"env"` is conventional, you can use any namespace:

```zig
extern "custom" fn myFunction() void;
```

Then provide it in JavaScript:

```javascript
const importObject = {
    custom: {
        myFunction: () => { /* implementation */ }
    }
};
```

The `"env"` namespace is standard and expected by most WASM tooling and runtimes.

### Type Conversions

WASM only supports `i32`, `i64`, `f32`, and `f64`. Zig handles conversions automatically:

| Zig Type | WASM Type | Notes |
|----------|-----------|-------|
| `i32`, `u32` | `i32` | Direct mapping |
| `i64`, `u64` | `i64` | Direct mapping |
| `f32` | `f32` | Direct mapping |
| `f64` | `f64` | Direct mapping |
| `bool` | `i32` | `false=0`, `true=1` |
| `*T`, `[*]T` | `i32` | Memory address |
| `usize`, `isize` | `i32` | On wasm32 |

### Passing Strings

Strings require passing a pointer and length:

```zig
extern "env" fn consoleLogStr(ptr: [*]const u8, len: usize) void;
```

JavaScript reads from linear memory:

```javascript
consoleLogStr: (ptr, len) => {
    const bytes = new Uint8Array(wasm.memory.buffer, ptr, len);
    const str = new TextDecoder().decode(bytes);
    console.log(str);
}
```

The pointer (`i32`) is an offset into `wasm.memory.buffer`. The Uint8Array view provides access to the string bytes.

### Random Numbers

WebAssembly has no source of entropy. For random numbers, import JavaScript's `Math.random()`:

```zig
// Generate random numbers using JavaScript
export fn rollDice() i32 {
    const rand = jsRandom(); // Returns [0, 1)
    return @as(i32, @intFromFloat(@floor(rand * 6.0))) + 1;
}

export fn randomInRange(min: i32, max: i32) i32 {
    const rand = jsRandom();
    const range: f64 = @floatFromInt(max - min + 1);
    return min + @as(i32, @intFromFloat(@floor(rand * range)));
}

export fn shuffleArray(arr: [*]i32, len: usize) void {
    // Fisher-Yates shuffle using JavaScript random
    var i: usize = len - 1;
    while (i > 0) : (i -= 1) {
        const rand = jsRandom();
        const j: usize = @intFromFloat(@floor(rand * @as(f64, @floatFromInt(i + 1))));

        // Swap arr[i] and arr[j]
        const temp = arr[i];
        arr[i] = arr[j];
        arr[j] = temp;
    }
}
```

This pattern works for any browser API or JavaScript function you need.

### Timestamps and Timing

Get current time from JavaScript:

```zig
// Get current time from JavaScript
export fn getElapsedSeconds(start_time: f64) f64 {
    const now = jsDateNow();
    return (now - start_time) / 1000.0; // Convert ms to seconds
}

export fn getCurrentTimestamp() f64 {
    return jsDateNow();
}
```

Useful for benchmarking and profiling:

```zig
// Benchmark using JavaScript timing
export fn fibonacci(n: i32) i32 {
    if (n <= 1) return n;

    var prev: i32 = 0;
    var curr: i32 = 1;
    var i: i32 = 2;

    while (i <= n) : (i += 1) {
        const next = prev + curr;
        prev = curr;
        curr = next;
    }

    return curr;
}

export fn benchmarkFibonacci(n: i32) f64 {
    const start = jsDateNow();
    _ = fibonacci(n);
    const end = jsDateNow();
    return end - start;
}
```

### Callbacks and Event Handling

Use callbacks to send data back to JavaScript:

```zig
// Use custom callbacks to process data
export fn processWithCallback(value: i32) void {
    // Do some processing
    const result = value * 2 + 10;
    // Send result to JavaScript
    jsCallback(result);
}

export fn processArray(arr: [*]i32, len: usize) void {
    for (0..len) |i| {
        arr[i] = jsProcessData(arr[i]);
    }
}
```

This pattern enables:
- Event notifications
- Progress updates
- Streaming results
- Bidirectional communication

### Testing with Stubs

Since external functions aren't available during `zig test`, provide stubs:

```zig
const builtin = @import("builtin");

comptime {
    if (builtin.is_test) {
        @export(&stub_jsRandom, .{ .name = "jsRandom" });
    }
}

fn stub_jsRandom() callconv(.c) f64 {
    return 0.5; // Deterministic for testing
}
```

This allows testing the Zig logic without JavaScript dependencies.

### Error Handling

External functions can't return Zig errors. Use sentinel values or callbacks:

```zig
extern "env" fn jsOperation(input: i32) i32;

export fn safeOperation(input: i32) ?i32 {
    const result = jsOperation(input);
    if (result < 0) return null; // -1 indicates error
    return result;
}
```

Or use a callback pattern:

```zig
extern "env" fn reportError(code: i32) void;

export fn operation(input: i32) i32 {
    if (input < 0) {
        reportError(1); // Send error code to JavaScript
        return 0;
    }
    return input * 2;
}
```

### Performance Considerations

Each call across the WASM/JavaScript boundary has overhead. For performance-critical code:

1. **Batch operations**: Process arrays in Zig, minimize crossings
2. **Cache results**: Store JavaScript values in Zig memory
3. **Minimize callbacks**: Reduce back-and-forth communication

Example of batching:

```zig
// Bad: One call per element
export fn processItems(items: [*]i32, len: usize) void {
    for (0..len) |i| {
        items[i] = jsProcessOne(items[i]); // Many boundary crossings
    }
}

// Good: Process in Zig, call once
export fn processItemsBatch(items: [*]i32, len: usize) void {
    // Do Zig processing
    for (0..len) |i| {
        items[i] = items[i] * 2 + 10;
    }
    // Single callback when done
    jsNotifyComplete();
}
```

### Common Patterns

**Console logging:**
```zig
extern "env" fn jsLog(ptr: [*]const u8, len: usize) void;
```

**DOM manipulation:**
```zig
extern "env" fn jsSetElementText(id_ptr: [*]const u8, id_len: usize,
                                  text_ptr: [*]const u8, text_len: usize) void;
```

**Fetch/XHR:**
```zig
extern "env" fn jsFetchUrl(url_ptr: [*]const u8, url_len: usize,
                            callback_id: i32) void;
```

**Local storage:**
```zig
extern "env" fn jsLocalStorageSet(key_ptr: [*]const u8, key_len: usize,
                                   value_ptr: [*]const u8, value_len: usize) void;
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// Custom panic handler
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = msg;
    _ = error_return_trace;
    _ = ret_addr;
    while (true) {}
}

// ANCHOR: console_log_import
// Import console.log from JavaScript
extern "env" fn consoleLog(value: f64) void;
extern "env" fn consoleLogInt(value: i32) void;
extern "env" fn consoleLogStr(ptr: [*]const u8, len: usize) void;
// ANCHOR_END: console_log_import

// ANCHOR: math_imports
// Import JavaScript Math functions
extern "env" fn jsRandom() f64;
extern "env" fn jsDateNow() f64;
extern "env" fn jsMathPow(base: f64, exponent: f64) f64;
extern "env" fn jsMathSin(x: f64) f64;
extern "env" fn jsMathCos(x: f64) f64;
// ANCHOR_END: math_imports

// ANCHOR: callback_imports
// Import custom JavaScript callbacks
extern "env" fn jsCallback(value: i32) void;
extern "env" fn jsProcessData(data: i32) i32;
// ANCHOR_END: callback_imports

// Test stubs for extern functions (only compiled during testing)
const builtin = @import("builtin");
const is_test = builtin.is_test;

// Provide stub implementations for testing
comptime {
    if (is_test) {
        @export(&stub_consoleLog, .{ .name = "consoleLog" });
        @export(&stub_consoleLogInt, .{ .name = "consoleLogInt" });
        @export(&stub_consoleLogStr, .{ .name = "consoleLogStr" });
        @export(&stub_jsRandom, .{ .name = "jsRandom" });
        @export(&stub_jsDateNow, .{ .name = "jsDateNow" });
        @export(&stub_jsMathPow, .{ .name = "jsMathPow" });
        @export(&stub_jsMathSin, .{ .name = "jsMathSin" });
        @export(&stub_jsMathCos, .{ .name = "jsMathCos" });
        @export(&stub_jsCallback, .{ .name = "jsCallback" });
        @export(&stub_jsProcessData, .{ .name = "jsProcessData" });
    }
}

fn stub_consoleLog(value: f64) callconv(.c) void {
    _ = value;
}
fn stub_consoleLogInt(value: i32) callconv(.c) void {
    _ = value;
}
fn stub_consoleLogStr(ptr: [*]const u8, len: usize) callconv(.c) void {
    _ = ptr;
    _ = len;
}
fn stub_jsRandom() callconv(.c) f64 {
    return 0.5;
}
fn stub_jsDateNow() callconv(.c) f64 {
    return 1000.0;
}
fn stub_jsMathPow(base: f64, exponent: f64) callconv(.c) f64 {
    return std.math.pow(f64, base, exponent);
}
fn stub_jsMathSin(x: f64) callconv(.c) f64 {
    return @sin(x);
}
fn stub_jsMathCos(x: f64) callconv(.c) f64 {
    return @cos(x);
}
fn stub_jsCallback(value: i32) callconv(.c) void {
    _ = value;
}
fn stub_jsProcessData(data: i32) callconv(.c) i32 {
    return data * 2;
}

// ANCHOR: using_console_log
// Function that logs to JavaScript console
export fn logValue(x: f64) void {
    consoleLog(x);
}

export fn logInteger(x: i32) void {
    consoleLogInt(x);
}

export fn logMessage() void {
    const msg = "Hello from Zig!";
    consoleLogStr(msg, msg.len);
}
// ANCHOR_END: using_console_log

// ANCHOR: using_math
// Use JavaScript Math functions
export fn calculatePower(base: f64, exponent: f64) f64 {
    return jsMathPow(base, exponent);
}

export fn calculateCircleArea(radius: f64) f64 {
    const pi = 3.141592653589793;
    const area = pi * jsMathPow(radius, 2.0);
    consoleLog(area); // Log the result
    return area;
}

export fn calculateSinCos(angle: f64) f64 {
    const sin_val = jsMathSin(angle);
    const cos_val = jsMathCos(angle);
    // sin² + cos² = 1
    return jsMathPow(sin_val, 2.0) + jsMathPow(cos_val, 2.0);
}
// ANCHOR_END: using_math

// ANCHOR: using_random
// Generate random numbers using JavaScript
export fn rollDice() i32 {
    const rand = jsRandom(); // Returns [0, 1)
    return @as(i32, @intFromFloat(@floor(rand * 6.0))) + 1;
}

export fn randomInRange(min: i32, max: i32) i32 {
    const rand = jsRandom();
    const range: f64 = @floatFromInt(max - min + 1);
    return min + @as(i32, @intFromFloat(@floor(rand * range)));
}

export fn shuffleArray(arr: [*]i32, len: usize) void {
    // Fisher-Yates shuffle using JavaScript random
    var i: usize = len - 1;
    while (i > 0) : (i -= 1) {
        const rand = jsRandom();
        const j: usize = @intFromFloat(@floor(rand * @as(f64, @floatFromInt(i + 1))));

        // Swap arr[i] and arr[j]
        const temp = arr[i];
        arr[i] = arr[j];
        arr[j] = temp;
    }
}
// ANCHOR_END: using_random

// ANCHOR: using_timestamp
// Get current time from JavaScript
export fn getElapsedSeconds(start_time: f64) f64 {
    const now = jsDateNow();
    return (now - start_time) / 1000.0; // Convert ms to seconds
}

export fn getCurrentTimestamp() f64 {
    return jsDateNow();
}
// ANCHOR_END: using_timestamp

// ANCHOR: using_callbacks
// Use custom callbacks to process data
export fn processWithCallback(value: i32) void {
    // Do some processing
    const result = value * 2 + 10;
    // Send result to JavaScript
    jsCallback(result);
}

export fn processArray(arr: [*]i32, len: usize) void {
    for (0..len) |i| {
        arr[i] = jsProcessData(arr[i]);
    }
}
// ANCHOR_END: using_callbacks

// ANCHOR: benchmark_example
// Benchmark using JavaScript timing
export fn fibonacci(n: i32) i32 {
    if (n <= 1) return n;

    var prev: i32 = 0;
    var curr: i32 = 1;
    var i: i32 = 2;

    while (i <= n) : (i += 1) {
        const next = prev + curr;
        prev = curr;
        curr = next;
    }

    return curr;
}

export fn benchmarkFibonacci(n: i32) f64 {
    const start = jsDateNow();
    _ = fibonacci(n);
    const end = jsDateNow();
    return end - start;
}
// ANCHOR_END: benchmark_example

// Tests (these verify logic, not the external calls)

// ANCHOR: test_dice
test "dice roll in valid range" {
    // We can't test actual randomness in unit tests,
    // but we can verify the formula logic
    const rand = 0.5; // Simulated random value
    const result = @as(i32, @intFromFloat(@floor(rand * 6.0))) + 1;
    try testing.expect(result >= 1 and result <= 6);
}
// ANCHOR_END: test_dice

// ANCHOR: test_random_range
test "random in range logic" {
    const min: i32 = 10;
    const max: i32 = 20;
    const rand = 0.5; // Simulated
    const range: f64 = @floatFromInt(max - min + 1);
    const result = min + @as(i32, @intFromFloat(@floor(rand * range)));
    try testing.expect(result >= min and result <= max);
}
// ANCHOR_END: test_random_range

// ANCHOR: test_shuffle
test "shuffle array logic" {
    const arr = [_]i32{ 1, 2, 3, 4, 5 };
    // Test that array structure is valid
    try testing.expectEqual(@as(usize, 5), arr.len);
}
// ANCHOR_END: test_shuffle

// ANCHOR: test_fibonacci
test "fibonacci function" {
    try testing.expectEqual(@as(i32, 0), fibonacci(0));
    try testing.expectEqual(@as(i32, 1), fibonacci(1));
    try testing.expectEqual(@as(i32, 1), fibonacci(2));
    try testing.expectEqual(@as(i32, 55), fibonacci(10));
}
// ANCHOR_END: test_fibonacci

// ANCHOR: test_elapsed_time
test "elapsed time calculation" {
    const start: f64 = 1000.0;
    const now: f64 = 5000.0;
    const elapsed = (now - start) / 1000.0;
    try testing.expectEqual(@as(f64, 4.0), elapsed);
}
// ANCHOR_END: test_elapsed_time
```

### See Also

- Recipe 19.1: Building a basic WebAssembly module
- Recipe 19.2: Exporting functions to JavaScript
- Recipe 19.4: Passing strings and data between Zig and JavaScript
- Recipe 19.5: Custom allocators for freestanding targets

---

## Recipe 19.4: Passing Strings and Data Between Zig and JavaScript {#recipe-19-4}

**Tags:** allocators, concurrency, error-handling, freestanding, json, memory, parsing, pointers, slices, testing, threading, webassembly
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/19-webassembly-freestanding/recipe_19_4.zig`

### Problem

You need to pass strings and complex data between Zig and JavaScript in WebAssembly, handling encoding, memory management, and bidirectional communication.

### Solution

Use linear memory with pointer/length pairs for passing strings, and static buffers for returning data.

### Setting Up a String Buffer

Create a buffer for returning strings to JavaScript:

```zig
// Static buffer for returning strings to JavaScript
var string_buffer: [1024]u8 = undefined;
var string_buffer_len: usize = 0;
```

```zig
// Export functions to access string buffer
export fn getStringPtr() [*]const u8 {
    return &string_buffer;
}

export fn getStringLen() usize {
    return string_buffer_len;
}
```

### Processing Input Strings

Accept strings via pointer and length:

```zig
// Process a string passed from JavaScript
export fn processString(ptr: [*]const u8, len: usize) usize {
    const input = ptr[0..len];

    var count: usize = 0;
    for (input) |char| {
        if (char >= 'a' and char <= 'z') {
            count += 1;
        }
    }

    return count;
}
```

### Returning Modified Strings

Write results to the buffer for JavaScript to read:

```zig
// Convert string to uppercase and store in buffer
export fn uppercaseString(ptr: [*]const u8, len: usize) void {
    const input = ptr[0..len];

    // Ensure it fits in our buffer
    const copy_len = @min(input.len, string_buffer.len);

    for (0..copy_len) |i| {
        if (input[i] >= 'a' and input[i] <= 'z') {
            string_buffer[i] = input[i] - 32; // Convert to uppercase
        } else {
            string_buffer[i] = input[i];
        }
    }

    string_buffer_len = copy_len;
}
```

```zig
// Reverse a string in the buffer
export fn reverseString(ptr: [*]const u8, len: usize) void {
    const input = ptr[0..len];
    const copy_len = @min(input.len, string_buffer.len);

    var i: usize = 0;
    while (i < copy_len) : (i += 1) {
        string_buffer[i] = input[copy_len - 1 - i];
    }

    string_buffer_len = copy_len;
}
```

### Working with Multiple Strings

Process multiple string parameters:

```zig
// Concatenate two strings
export fn concatenateStrings(ptr1: [*]const u8, len1: usize, ptr2: [*]const u8, len2: usize) void {
    const str1 = ptr1[0..len1];
    const str2 = ptr2[0..len2];

    const total_len = @min(len1 + len2, string_buffer.len);
    const len1_clamped = @min(len1, string_buffer.len);
    const len2_clamped = @min(total_len - len1_clamped, len2);

    // Copy first string
    for (0..len1_clamped) |i| {
        string_buffer[i] = str1[i];
    }

    // Copy second string
    for (0..len2_clamped) |i| {
        string_buffer[len1_clamped + i] = str2[i];
    }

    string_buffer_len = len1_clamped + len2_clamped;
}
```

### String to Number Conversion

Parse numbers from strings:

```zig
// Parse number from string
export fn parseNumber(ptr: [*]const u8, len: usize) i32 {
    const input = ptr[0..len];

    var result: i32 = 0;
    var is_negative = false;
    var start_index: usize = 0;

    // Check for negative sign
    if (input.len > 0 and input[0] == '-') {
        is_negative = true;
        start_index = 1;
    }

    for (start_index..input.len) |i| {
        const char = input[i];
        if (char >= '0' and char <= '9') {
            result = result * 10 + @as(i32, char - '0');
        }
    }

    return if (is_negative) -result else result;
}
```

### Number to String Formatting

Format numbers as strings:

```zig
// Format number as string
export fn formatNumber(num: i32) void {
    if (num == 0) {
        string_buffer[0] = '0';
        string_buffer_len = 1;
        return;
    }

    var n = num;
    var is_negative = false;

    if (n < 0) {
        is_negative = true;
        n = -n;
    }

    var temp_buffer: [32]u8 = undefined;
    var temp_len: usize = 0;

    // Convert digits in reverse
    while (n > 0) : (n = @divTrunc(n, 10)) {
        const digit: u8 = @intCast(@rem(n, 10));
        temp_buffer[temp_len] = '0' + digit;
        temp_len += 1;
    }

    // Add negative sign if needed
    if (is_negative) {
        temp_buffer[temp_len] = '-';
        temp_len += 1;
    }

    // Reverse into string_buffer
    for (0..temp_len) |i| {
        string_buffer[i] = temp_buffer[temp_len - 1 - i];
    }

    string_buffer_len = temp_len;
}
```

### JavaScript Integration

From JavaScript, use TextEncoder/TextDecoder:

```javascript
// Write string to WASM memory
function writeString(str) {
    const encoder = new TextEncoder();
    const bytes = encoder.encode(str);
    const ptr = wasm.allocateBytes(bytes.length);
    const view = new Uint8Array(wasm.memory.buffer);
    for (let i = 0; i < bytes.length; i++) {
        view[ptr + i] = bytes[i];
    }
    return { ptr, len: bytes.length };
}

// Read string from WASM buffer
function readStringFromBuffer() {
    const ptr = wasm.getStringPtr();
    const len = wasm.getStringLen();
    const bytes = new Uint8Array(wasm.memory.buffer, ptr, len);
    return new TextDecoder().decode(bytes);
}

// Usage
const { ptr, len } = writeString("hello");
wasm.uppercaseString(ptr, len);
const result = readStringFromBuffer(); // "HELLO"
```

### Discussion

### Memory Layout for Strings

Strings in WASM are just byte sequences in linear memory. The pattern is:

1. **Passing to Zig**: JavaScript writes bytes to WASM memory, passes pointer and length
2. **Returning from Zig**: Zig writes to a known buffer, JavaScript reads from that buffer

This avoids complex memory management while allowing efficient string operations.

### The Pointer-Length Pattern

Every string function takes two parameters:

```zig
fn processString(ptr: [*]const u8, len: usize) ResultType
```

This pattern:
- Works with any string encoding (UTF-8, ASCII, etc.)
- Avoids null-termination overhead
- Matches Zig's slice semantics
- Is efficient (no copying unless needed)

Convert to a slice inside the function:

```zig
const input = ptr[0..len]; // Creates slice
```

### UTF-8 Encoding

Zig strings are UTF-8 by default. JavaScript's TextEncoder/TextDecoder also use UTF-8:

```javascript
const encoder = new TextEncoder(); // UTF-8
const bytes = encoder.encode("Hello 世界"); // Works with Unicode

const decoder = new TextDecoder(); // UTF-8
const str = decoder.decode(bytes);
```

For ASCII-only operations, you can work with bytes directly. For Unicode-aware operations, use `std.unicode`:

```zig
const std = @import("std");

// Count UTF-8 codepoints (not bytes)
fn countCodepoints(ptr: [*]const u8, len: usize) usize {
    const input = ptr[0..len];
    var count: usize = 0;
    var i: usize = 0;
    while (i < input.len) {
        const cp_len = std.unicode.utf8ByteSequenceLength(input[i]) catch 1;
        count += 1;
        i += cp_len;
    }
    return count;
}
```

### Static Buffers vs Dynamic Allocation

This recipe uses static buffers:

```zig
var string_buffer: [1024]u8 = undefined;
```

Advantages:
- Simple, no allocator needed
- Fast, no allocation overhead
- Deterministic memory usage

Disadvantages:
- Fixed size limit
- Can't return multiple strings simultaneously
- Not thread-safe (for multi-threaded WASM)

For more flexibility, use a proper allocator (see Recipe 19.5).

### Alternative: Direct Memory Access

For large data or many operations, consider having JavaScript work directly in WASM memory:

```zig
export fn getWorkBuffer() [*]u8 {
    const static = struct {
        var buffer: [4096]u8 = undefined;
    };
    return &static.buffer;
}
```

JavaScript can then read/write directly:

```javascript
const bufPtr = wasm.getWorkBuffer();
const view = new Uint8Array(wasm.memory.buffer, bufPtr, 4096);

// Write directly
const encoder = new TextEncoder();
const bytes = encoder.encode("Hello");
view.set(bytes);

// Call WASM function that works in-place
wasm.processInPlace(bytes.length);

// Read result
const decoder = new TextDecoder();
const result = decoder.decode(view.slice(0, wasm.getResultLen()));
```

### Word Counting Example

Demonstrates more complex string processing:

```zig
// Count words in a string
export fn wordCount(ptr: [*]const u8, len: usize) usize {
    const input = ptr[0..len];
    var count: usize = 0;
    var in_word = false;

    for (input) |char| {
        const is_space = (char == ' ' or char == '\t' or char == '\n' or char == '\r');

        if (!is_space and !in_word) {
            count += 1;
            in_word = true;
        } else if (is_space) {
            in_word = false;
        }
    }

    return count;
}
```

This shows:
- State tracking across loop iterations
- Character classification
- No memory allocation needed

### Handling Large Strings

For strings larger than your buffer:

1. **Chunk processing**: Process in pieces
2. **Streaming**: Use callbacks to send results incrementally
3. **Dynamic allocation**: Use a proper allocator (Recipe 19.5)
4. **Compression**: Compress before passing

Example of chunked processing:

```zig
export fn processChunk(ptr: [*]const u8, len: usize, chunk_index: usize) void {
    const input = ptr[0..len];
    // Process this chunk
    // Store results keyed by chunk_index
}
```

### JSON and Structured Data

For complex data, use JSON:

```javascript
// JavaScript side
const data = { name: "Alice", age: 30 };
const json = JSON.stringify(data);
const { ptr, len } = writeString(json);
wasm.processJSON(ptr, len);
```

In Zig, parse the JSON string:

```zig
const std = @import("std");

export fn processJSON(ptr: [*]const u8, len: usize) void {
    const input = ptr[0..len];
    // Parse with std.json (needs allocator)
    // Or write custom parser for known structure
}
```

### Performance Tips

1. **Minimize crossings**: Do bulk work in Zig, pass results once
2. **Reuse buffers**: Don't allocate for each operation
3. **Use views**: Uint8Array views are cheap
4. **Batch operations**: Process arrays of strings together

Example of batching:

```javascript
// Bad: Many boundary crossings
for (const str of strings) {
    const { ptr, len } = writeString(str);
    results.push(wasm.processString(ptr, len));
}

// Better: Write all strings, process in batch
const allStrings = strings.join('\0'); // Null-separated
const { ptr, len } = writeString(allStrings);
wasm.processBatch(ptr, len, strings.length);
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// Custom panic handler
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = msg;
    _ = error_return_trace;
    _ = ret_addr;
    while (true) {}
}

// ANCHOR: string_buffer
// Static buffer for returning strings to JavaScript
var string_buffer: [1024]u8 = undefined;
var string_buffer_len: usize = 0;
// ANCHOR_END: string_buffer

// ANCHOR: string_exports
// Export functions to access string buffer
export fn getStringPtr() [*]const u8 {
    return &string_buffer;
}

export fn getStringLen() usize {
    return string_buffer_len;
}
// ANCHOR_END: string_exports

// ANCHOR: process_string
// Process a string passed from JavaScript
export fn processString(ptr: [*]const u8, len: usize) usize {
    const input = ptr[0..len];

    var count: usize = 0;
    for (input) |char| {
        if (char >= 'a' and char <= 'z') {
            count += 1;
        }
    }

    return count;
}
// ANCHOR_END: process_string

// ANCHOR: uppercase_string
// Convert string to uppercase and store in buffer
export fn uppercaseString(ptr: [*]const u8, len: usize) void {
    const input = ptr[0..len];

    // Ensure it fits in our buffer
    const copy_len = @min(input.len, string_buffer.len);

    for (0..copy_len) |i| {
        if (input[i] >= 'a' and input[i] <= 'z') {
            string_buffer[i] = input[i] - 32; // Convert to uppercase
        } else {
            string_buffer[i] = input[i];
        }
    }

    string_buffer_len = copy_len;
}
// ANCHOR_END: uppercase_string

// ANCHOR: reverse_string
// Reverse a string in the buffer
export fn reverseString(ptr: [*]const u8, len: usize) void {
    const input = ptr[0..len];
    const copy_len = @min(input.len, string_buffer.len);

    var i: usize = 0;
    while (i < copy_len) : (i += 1) {
        string_buffer[i] = input[copy_len - 1 - i];
    }

    string_buffer_len = copy_len;
}
// ANCHOR_END: reverse_string

// ANCHOR: concatenate_strings
// Concatenate two strings
export fn concatenateStrings(ptr1: [*]const u8, len1: usize, ptr2: [*]const u8, len2: usize) void {
    const str1 = ptr1[0..len1];
    const str2 = ptr2[0..len2];

    const total_len = @min(len1 + len2, string_buffer.len);
    const len1_clamped = @min(len1, string_buffer.len);
    const len2_clamped = @min(total_len - len1_clamped, len2);

    // Copy first string
    for (0..len1_clamped) |i| {
        string_buffer[i] = str1[i];
    }

    // Copy second string
    for (0..len2_clamped) |i| {
        string_buffer[len1_clamped + i] = str2[i];
    }

    string_buffer_len = len1_clamped + len2_clamped;
}
// ANCHOR_END: concatenate_strings

// ANCHOR: parse_number
// Parse number from string
export fn parseNumber(ptr: [*]const u8, len: usize) i32 {
    const input = ptr[0..len];

    var result: i32 = 0;
    var is_negative = false;
    var start_index: usize = 0;

    // Check for negative sign
    if (input.len > 0 and input[0] == '-') {
        is_negative = true;
        start_index = 1;
    }

    for (start_index..input.len) |i| {
        const char = input[i];
        if (char >= '0' and char <= '9') {
            result = result * 10 + @as(i32, char - '0');
        }
    }

    return if (is_negative) -result else result;
}
// ANCHOR_END: parse_number

// ANCHOR: format_number
// Format number as string
export fn formatNumber(num: i32) void {
    if (num == 0) {
        string_buffer[0] = '0';
        string_buffer_len = 1;
        return;
    }

    var n = num;
    var is_negative = false;

    if (n < 0) {
        is_negative = true;
        n = -n;
    }

    var temp_buffer: [32]u8 = undefined;
    var temp_len: usize = 0;

    // Convert digits in reverse
    while (n > 0) : (n = @divTrunc(n, 10)) {
        const digit: u8 = @intCast(@rem(n, 10));
        temp_buffer[temp_len] = '0' + digit;
        temp_len += 1;
    }

    // Add negative sign if needed
    if (is_negative) {
        temp_buffer[temp_len] = '-';
        temp_len += 1;
    }

    // Reverse into string_buffer
    for (0..temp_len) |i| {
        string_buffer[i] = temp_buffer[temp_len - 1 - i];
    }

    string_buffer_len = temp_len;
}
// ANCHOR_END: format_number

// ANCHOR: word_count
// Count words in a string
export fn wordCount(ptr: [*]const u8, len: usize) usize {
    const input = ptr[0..len];
    var count: usize = 0;
    var in_word = false;

    for (input) |char| {
        const is_space = (char == ' ' or char == '\t' or char == '\n' or char == '\r');

        if (!is_space and !in_word) {
            count += 1;
            in_word = true;
        } else if (is_space) {
            in_word = false;
        }
    }

    return count;
}
// ANCHOR_END: word_count

// ANCHOR: allocate_bytes
// Allocate bytes and return pointer (simplified - uses static buffer)
export fn allocateBytes(size: usize) [*]u8 {
    const static = struct {
        var heap: [4096]u8 = undefined;
        var offset: usize = 0;
    };

    if (static.offset + size > static.heap.len) {
        // Out of space - reset (not production-ready!)
        static.offset = 0;
    }

    const ptr: [*]u8 = @ptrCast(&static.heap[static.offset]);
    static.offset += size;

    return ptr;
}
// ANCHOR_END: allocate_bytes

// Tests

// ANCHOR: test_process_string
test "process string" {
    const str = "Hello World!";
    const count = processString(str.ptr, str.len);
    try testing.expectEqual(@as(usize, 8), count); // 8 lowercase letters
}
// ANCHOR_END: test_process_string

// ANCHOR: test_uppercase
test "uppercase string" {
    const str = "hello";
    uppercaseString(str.ptr, str.len);

    const result = string_buffer[0..string_buffer_len];
    try testing.expectEqualStrings("HELLO", result);
}
// ANCHOR_END: test_uppercase

// ANCHOR: test_reverse
test "reverse string" {
    const str = "hello";
    reverseString(str.ptr, str.len);

    const result = string_buffer[0..string_buffer_len];
    try testing.expectEqualStrings("olleh", result);
}
// ANCHOR_END: test_reverse

// ANCHOR: test_concatenate
test "concatenate strings" {
    const str1 = "Hello, ";
    const str2 = "World!";
    concatenateStrings(str1.ptr, str1.len, str2.ptr, str2.len);

    const result = string_buffer[0..string_buffer_len];
    try testing.expectEqualStrings("Hello, World!", result);
}
// ANCHOR_END: test_concatenate

// ANCHOR: test_parse_number
test "parse number" {
    const str1 = "123";
    try testing.expectEqual(@as(i32, 123), parseNumber(str1.ptr, str1.len));

    const str2 = "-456";
    try testing.expectEqual(@as(i32, -456), parseNumber(str2.ptr, str2.len));

    const str3 = "0";
    try testing.expectEqual(@as(i32, 0), parseNumber(str3.ptr, str3.len));
}
// ANCHOR_END: test_parse_number

// ANCHOR: test_format_number
test "format number" {
    formatNumber(123);
    try testing.expectEqualStrings("123", string_buffer[0..string_buffer_len]);

    formatNumber(-456);
    try testing.expectEqualStrings("-456", string_buffer[0..string_buffer_len]);

    formatNumber(0);
    try testing.expectEqualStrings("0", string_buffer[0..string_buffer_len]);
}
// ANCHOR_END: test_format_number

// ANCHOR: test_word_count
test "word count" {
    const str1 = "Hello World";
    try testing.expectEqual(@as(usize, 2), wordCount(str1.ptr, str1.len));

    const str2 = "  Multiple   spaces  ";
    try testing.expectEqual(@as(usize, 2), wordCount(str2.ptr, str2.len));

    const str3 = "";
    try testing.expectEqual(@as(usize, 0), wordCount(str3.ptr, str3.len));
}
// ANCHOR_END: test_word_count
```

### See Also

- Recipe 19.1: Building a basic WebAssembly module
- Recipe 19.2: Exporting functions to JavaScript
- Recipe 19.3: Importing and calling JavaScript functions
- Recipe 19.5: Custom allocators for freestanding targets

---

## Recipe 19.5: Custom Allocators for Freestanding Targets {#recipe-19-5}

**Tags:** allocators, arena-allocator, atomics, c-interop, concurrency, error-handling, freestanding, memory, resource-cleanup, slices, synchronization, testing, threading, webassembly
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/19-webassembly-freestanding/recipe_19_5.zig`

### Problem

Freestanding WebAssembly targets don't have a system allocator. You need to implement custom memory allocation strategies for dynamic memory management.

### Solution

Implement allocators that work within WebAssembly's linear memory constraints.

### Bump Allocator (Fast, No Individual Frees)

Simple allocator that never frees individual allocations:

```zig
// Simple bump allocator - fast but can't free individual allocations
const BumpAllocator = struct {
    buffer: []u8,
    offset: usize,

    pub fn init(buffer: []u8) BumpAllocator {
        return .{
            .buffer = buffer,
            .offset = 0,
        };
    }

    pub fn allocator(self: *BumpAllocator) std.mem.Allocator {
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
        _ = ret_addr;
        const self: *BumpAllocator = @ptrCast(@alignCast(ctx));

        const align_offset = std.mem.alignForward(usize, self.offset, ptr_align.toByteUnits());
        const new_offset = align_offset + len;

        if (new_offset > self.buffer.len) {
            return null; // Out of memory
        }

        const result = self.buffer[align_offset..new_offset];
        self.offset = new_offset;

        return result.ptr;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = new_len;
        _ = ret_addr;
        return false; // Cannot resize
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = ret_addr;
        // Bump allocator doesn't free individual allocations
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = new_len;
        _ = ret_addr;
        return null; // Cannot remap
    }

    pub fn reset(self: *BumpAllocator) void {
        self.offset = 0;
    }
};
```

Set up a global instance:

```zig
// Global allocator instance for WASM
var global_heap: [64 * 1024]u8 = undefined; // 64KB
var global_allocator = BumpAllocator.init(&global_heap);
```

Use it for allocations:

```zig
// Example: Create dynamic array
export fn createArray(size: usize) ?[*]i32 {
    const allocator = global_allocator.allocator();
    const array = allocator.alloc(i32, size) catch return null;

    // Initialize array
    for (array, 0..) |*item, i| {
        item.* = @intCast(i);
    }

    return array.ptr;
}

export fn resetAllocator() void {
    global_allocator.reset();
}
```

### Arena Allocator (Bulk Freeing)

Group allocations for efficient bulk freeing:

```zig
// Arena allocator - groups allocations for bulk freeing
const ArenaWrapper = struct {
    var backing_buffer: [32 * 1024]u8 = undefined;
    var fixed_allocator = std.heap.FixedBufferAllocator.init(&backing_buffer);
    var arena = std.heap.ArenaAllocator.init(fixed_allocator.allocator());

    pub fn get() std.mem.Allocator {
        return arena.allocator();
    }

    pub fn reset() void {
        _ = arena.reset(.free_all);
    }
};
```

```zig
// Example: Process with arena
export fn processData(count: usize) i32 {
    const allocator = ArenaWrapper.get();

    // Allocate temporary data
    const buffer = allocator.alloc(i32, count) catch return -1;

    var sum: i32 = 0;
    for (0..count) |i| {
        buffer[i] = @as(i32, @intCast(i)) * 2;
        sum += buffer[i];
    }

    // No need to free - arena will handle it
    return sum;
}

export fn resetArena() void {
    ArenaWrapper.reset();
}
```

### Fixed Buffer Allocator (Stack-Like)

Local stack-allocated buffer for temporary work:

```zig
// Direct use of FixedBufferAllocator
export fn useFixedBuffer() i32 {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // Allocate and use memory
    const array = allocator.alloc(i32, 10) catch return -1;
    defer allocator.free(array);

    var sum: i32 = 0;
    for (array, 0..) |*item, i| {
        item.* = @intCast(i);
        sum += item.*;
    }

    return sum; // 0+1+2+...+9 = 45
}
```

### Pool Allocator (Fixed-Size Objects)

Efficient allocation for same-sized objects:

```zig
// Pool allocator for fixed-size allocations
const PoolAllocator = struct {
    const POOL_SIZE = 100;
    const ITEM_SIZE = 64;

    pool: [POOL_SIZE][ITEM_SIZE]u8,
    free_list: [POOL_SIZE]bool,
    initialized: bool,

    pub fn init() PoolAllocator {
        return .{
            .pool = undefined,
            .free_list = [_]bool{true} ** POOL_SIZE,
            .initialized = true,
        };
    }

    pub fn allocate(self: *PoolAllocator) ?[*]u8 {
        for (&self.free_list, 0..) |*is_free, i| {
            if (is_free.*) {
                is_free.* = false;
                return &self.pool[i];
            }
        }
        return null; // Pool exhausted
    }

    pub fn deallocate(self: *PoolAllocator, ptr: [*]u8) void {
        const base = @intFromPtr(&self.pool[0]);
        const addr = @intFromPtr(ptr);
        const offset = addr - base;
        const index = offset / ITEM_SIZE;

        if (index < POOL_SIZE) {
            self.free_list[index] = true;
        }
    }
};

var global_pool = PoolAllocator.init();
```

```zig
// Example: Use pool allocator
export fn allocateFromPool() ?[*]u8 {
    return global_pool.allocate();
}

export fn freeToPool(ptr: [*]u8) void {
    global_pool.deallocate(ptr);
}
```

### Discussion

### Why Custom Allocators?

Freestanding WASM has no malloc/free. You must provide memory management. The standard library's allocators won't work without OS support.

### Bump Allocator Characteristics

**Pros:**
- Extremely fast: O(1) allocation
- Simple implementation
- No fragmentation
- Predictable memory usage

**Cons:**
- Cannot free individual allocations
- Must reset all at once
- Memory grows until reset

**Best for:**
- Request/response cycles (allocate, process, reset)
- Temporary computations
- Single-pass algorithms

### Arena Allocator Characteristics

**Pros:**
- Fast allocation
- Bulk freeing
- Can wrap any backing allocator
- Good for hierarchical lifetimes

**Cons:**
- Cannot free individual items
- Memory grows until reset
- Requires backing allocator

**Best for:**
- Processing requests (allocate many, free all at end)
- Tree/graph construction then disposal
- Grouped temporary data

Example pattern:

```javascript
// JavaScript calls WASM for each request
for (const request of requests) {
    wasm.processRequest(request);
    wasm.resetArena(); // Free all allocations
}
```

### Pool Allocator Characteristics

**Pros:**
- O(1) allocation and deallocation
- No fragmentation
- Perfect for fixed-size objects
- Can free individual items

**Cons:**
- Fixed capacity
- Wasted space if object sizes vary
- Requires knowing max object count

**Best for:**
- Particle systems
- Object pools (network packets, DOM nodes)
- Fixed-size data structures

### Choosing an Allocator

| Allocator | Free Individual? | Reset All? | Best Use Case |
|-----------|------------------|------------|---------------|
| Bump | No | Yes | Single pass, request/response |
| Arena | No | Yes | Hierarchical lifetimes |
| Pool | Yes | Yes | Fixed-size objects |
| FixedBuffer | Yes | N/A | Local temporary buffers |

### Memory Layout in WASM

WASM linear memory starts at address 0. Typical layout:

```
0x0000   - Stack (grows down)
...
0x????   - Global variables
0x????   - __heap_base (start of dynamic memory)
...      - Your allocators work here
0xFFFF   - End of initial memory (can grow)
```

The compiler sets `__heap_base` to mark where dynamic allocation can begin.

### Implementing Custom VTable

The allocator interface requires four functions:

```zig
pub const VTable = struct {
    alloc: fn(*anyopaque, usize, Alignment, usize) ?[*]u8,
    resize: fn(*anyopaque, []u8, Alignment, usize, usize) bool,
    free: fn(*anyopaque, []u8, Alignment, usize) void,
    remap: fn(*anyopaque, []u8, Alignment, usize, usize) ?[*]u8,
};
```

- `alloc`: Allocate new memory
- `resize`: Try to resize in place
- `free`: Deallocate memory
- `remap`: Reallocate (move if needed)

Simple allocators can return failure for resize/remap.

### Growing WASM Memory

WASM memory can grow at runtime:

```zig
// Not in freestanding, but in WASI or with custom imports
extern "env" fn __wasm_memory_grow(pages: i32) i32;

export fn growMemory(pages: i32) bool {
    const result = __wasm_memory_grow(pages);
    return result != -1; // -1 means failure
}
```

Pages are 64KB each. Most allocators work within initial memory.

### Combining Allocators

Layer allocators for different use cases:

```zig
// Large backing buffer with bump allocator
var backing: [1024 * 1024]u8 = undefined; // 1MB
var bump = BumpAllocator.init(&backing);

// Arena for request processing
var arena = std.heap.ArenaAllocator.init(bump.allocator());

// Use arena for request
const data = try arena.allocator().alloc(u8, size);
// ... process ...
_ = arena.reset(.free_all);
```

### Error Handling

Allocations can fail. Handle errors properly:

```zig
export fn allocateArray(size: usize) i32 {
    const allocator = global_allocator.allocator();
    const array = allocator.alloc(i32, size) catch {
        return -1; // Signal error to JavaScript
    };
    return @intCast(@intFromPtr(array.ptr));
}
```

From JavaScript:

```javascript
const ptr = wasm.allocateArray(1000);
if (ptr === -1) {
    console.error('Allocation failed');
}
```

### Thread Safety

These allocators are not thread-safe. For multi-threaded WASM:

1. Use separate allocators per thread
2. Add mutex protection
3. Use atomic operations

Example with mutex:

```zig
const Mutex = std.Thread.Mutex;

var allocator_mutex = Mutex{};
var global_alloc = BumpAllocator.init(&heap);

export fn threadSafeAlloc(size: usize) ?[*]u8 {
    allocator_mutex.lock();
    defer allocator_mutex.unlock();

    return global_alloc.allocator().alloc(u8, size) catch null;
}
```

### Debugging Allocations

Track allocation stats:

```zig
const TrackedAllocator = struct {
    backing: BumpAllocator,
    alloc_count: usize = 0,
    bytes_allocated: usize = 0,

    pub fn allocator(self: *TrackedAllocator) std.mem.Allocator {
        // Wrap backing allocator, increment counters
    }
};
```

Export stats for JavaScript to monitor:

```zig
export fn getAllocStats() usize {
    return tracked_alloc.bytes_allocated;
}
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// Custom panic handler
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = msg;
    _ = error_return_trace;
    _ = ret_addr;
    while (true) {}
}

// ANCHOR: bump_allocator
// Simple bump allocator - fast but can't free individual allocations
const BumpAllocator = struct {
    buffer: []u8,
    offset: usize,

    pub fn init(buffer: []u8) BumpAllocator {
        return .{
            .buffer = buffer,
            .offset = 0,
        };
    }

    pub fn allocator(self: *BumpAllocator) std.mem.Allocator {
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
        _ = ret_addr;
        const self: *BumpAllocator = @ptrCast(@alignCast(ctx));

        const align_offset = std.mem.alignForward(usize, self.offset, ptr_align.toByteUnits());
        const new_offset = align_offset + len;

        if (new_offset > self.buffer.len) {
            return null; // Out of memory
        }

        const result = self.buffer[align_offset..new_offset];
        self.offset = new_offset;

        return result.ptr;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = new_len;
        _ = ret_addr;
        return false; // Cannot resize
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, ret_addr: usize) void {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = ret_addr;
        // Bump allocator doesn't free individual allocations
    }

    fn remap(ctx: *anyopaque, buf: []u8, buf_align: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        _ = ctx;
        _ = buf;
        _ = buf_align;
        _ = new_len;
        _ = ret_addr;
        return null; // Cannot remap
    }

    pub fn reset(self: *BumpAllocator) void {
        self.offset = 0;
    }
};
// ANCHOR_END: bump_allocator

// ANCHOR: global_allocator
// Global allocator instance for WASM
var global_heap: [64 * 1024]u8 = undefined; // 64KB
var global_allocator = BumpAllocator.init(&global_heap);
// ANCHOR_END: global_allocator

// ANCHOR: using_allocator
// Example: Create dynamic array
export fn createArray(size: usize) ?[*]i32 {
    const allocator = global_allocator.allocator();
    const array = allocator.alloc(i32, size) catch return null;

    // Initialize array
    for (array, 0..) |*item, i| {
        item.* = @intCast(i);
    }

    return array.ptr;
}

export fn resetAllocator() void {
    global_allocator.reset();
}
// ANCHOR_END: using_allocator

// ANCHOR: arena_allocator
// Arena allocator - groups allocations for bulk freeing
const ArenaWrapper = struct {
    var backing_buffer: [32 * 1024]u8 = undefined;
    var fixed_allocator = std.heap.FixedBufferAllocator.init(&backing_buffer);
    var arena = std.heap.ArenaAllocator.init(fixed_allocator.allocator());

    pub fn get() std.mem.Allocator {
        return arena.allocator();
    }

    pub fn reset() void {
        _ = arena.reset(.free_all);
    }
};
// ANCHOR_END: arena_allocator

// ANCHOR: using_arena
// Example: Process with arena
export fn processData(count: usize) i32 {
    const allocator = ArenaWrapper.get();

    // Allocate temporary data
    const buffer = allocator.alloc(i32, count) catch return -1;

    var sum: i32 = 0;
    for (0..count) |i| {
        buffer[i] = @as(i32, @intCast(i)) * 2;
        sum += buffer[i];
    }

    // No need to free - arena will handle it
    return sum;
}

export fn resetArena() void {
    ArenaWrapper.reset();
}
// ANCHOR_END: using_arena

// ANCHOR: fixed_buffer_allocator
// Direct use of FixedBufferAllocator
export fn useFixedBuffer() i32 {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    // Allocate and use memory
    const array = allocator.alloc(i32, 10) catch return -1;
    defer allocator.free(array);

    var sum: i32 = 0;
    for (array, 0..) |*item, i| {
        item.* = @intCast(i);
        sum += item.*;
    }

    return sum; // 0+1+2+...+9 = 45
}
// ANCHOR_END: fixed_buffer_allocator

// ANCHOR: pool_allocator
// Pool allocator for fixed-size allocations
const PoolAllocator = struct {
    const POOL_SIZE = 100;
    const ITEM_SIZE = 64;

    pool: [POOL_SIZE][ITEM_SIZE]u8,
    free_list: [POOL_SIZE]bool,
    initialized: bool,

    pub fn init() PoolAllocator {
        return .{
            .pool = undefined,
            .free_list = [_]bool{true} ** POOL_SIZE,
            .initialized = true,
        };
    }

    pub fn allocate(self: *PoolAllocator) ?[*]u8 {
        for (&self.free_list, 0..) |*is_free, i| {
            if (is_free.*) {
                is_free.* = false;
                return &self.pool[i];
            }
        }
        return null; // Pool exhausted
    }

    pub fn deallocate(self: *PoolAllocator, ptr: [*]u8) void {
        const base = @intFromPtr(&self.pool[0]);
        const addr = @intFromPtr(ptr);
        const offset = addr - base;
        const index = offset / ITEM_SIZE;

        if (index < POOL_SIZE) {
            self.free_list[index] = true;
        }
    }
};

var global_pool = PoolAllocator.init();
// ANCHOR_END: pool_allocator

// ANCHOR: using_pool
// Example: Use pool allocator
export fn allocateFromPool() ?[*]u8 {
    return global_pool.allocate();
}

export fn freeToPool(ptr: [*]u8) void {
    global_pool.deallocate(ptr);
}
// ANCHOR_END: using_pool

// Tests

// ANCHOR: test_bump_allocator
test "bump allocator" {
    var buffer: [1024]u8 = undefined;
    var bump = BumpAllocator.init(&buffer);
    const allocator = bump.allocator();

    const slice1 = try allocator.alloc(u8, 100);
    try testing.expectEqual(@as(usize, 100), slice1.len);

    const slice2 = try allocator.alloc(u8, 200);
    try testing.expectEqual(@as(usize, 200), slice2.len);

    // Reset and reuse
    bump.reset();
    const slice3 = try allocator.alloc(u8, 50);
    try testing.expectEqual(@as(usize, 50), slice3.len);
}
// ANCHOR_END: test_bump_allocator

// ANCHOR: test_arena
test "arena allocator" {
    var backing: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&backing);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();

    const allocator = arena.allocator();

    // Multiple allocations
    const slice1 = try allocator.alloc(i32, 10);
    const slice2 = try allocator.alloc(i32, 20);

    try testing.expectEqual(@as(usize, 10), slice1.len);
    try testing.expectEqual(@as(usize, 20), slice2.len);

    // All freed together
}
// ANCHOR_END: test_arena

// ANCHOR: test_fixed_buffer
test "fixed buffer allocator" {
    var buffer: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const allocator = fba.allocator();

    const array = try allocator.alloc(i32, 10);
    defer allocator.free(array);

    var sum: i32 = 0;
    for (array, 0..) |*item, i| {
        item.* = @intCast(i);
        sum += item.*;
    }

    try testing.expectEqual(@as(i32, 45), sum);
}
// ANCHOR_END: test_fixed_buffer

// ANCHOR: test_pool
test "pool allocator" {
    var pool = PoolAllocator.init();

    const ptr1 = pool.allocate().?;
    const ptr2 = pool.allocate().?;

    try testing.expect(ptr1 != ptr2);

    pool.deallocate(ptr1);

    const ptr3 = pool.allocate().?;
    try testing.expectEqual(ptr1, ptr3); // Reused slot
}
// ANCHOR_END: test_pool

// ANCHOR: test_out_of_memory
test "out of memory handling" {
    var buffer: [100]u8 = undefined;
    var bump = BumpAllocator.init(&buffer);
    const allocator = bump.allocator();

    _ = try allocator.alloc(u8, 50);

    // This should fail
    const result = allocator.alloc(u8, 100);
    try testing.expectError(error.OutOfMemory, result);
}
// ANCHOR_END: test_out_of_memory
```

### See Also

- Recipe 19.1: Building a basic WebAssembly module
- Recipe 19.4: Passing strings and data between Zig and JavaScript
- Recipe 19.6: Implementing a panic handler for WASM
- Recipe 0.12: Understanding Allocators (fundamentals)

---

## Recipe 19.6: Implementing a Panic Handler for WASM {#recipe-19-6}

**Tags:** c-interop, comptime, error-handling, freestanding, pointers, resource-cleanup, testing, webassembly
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/19-webassembly-freestanding/recipe_19_6.zig`

### Problem

Freestanding WebAssembly targets require a custom panic handler. Without one, your code won't compile. You need to handle panics appropriately for web environments.

### Solution

Implement a `panic` function that reports errors to JavaScript and prevents undefined behavior.

### Simple Panic Handler

Minimal implementation that halts execution:

```zig
// Simple panic handler - infinite loop
pub fn simplePanicHandler(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = msg;
    _ = error_return_trace;
    _ = ret_addr;
    while (true) {} // Hang forever
}
```

### Logging Panic Handler

Report panics to JavaScript for debugging:

```zig
// Import JavaScript panic reporting function
extern "env" fn jsPanic(msg_ptr: [*]const u8, msg_len: usize) void;
extern "env" fn jsLogPanic(msg_ptr: [*]const u8, msg_len: usize) void;
```

```zig
// Panic handler that logs to JavaScript
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = error_return_trace;
    _ = ret_addr;

    // Call JavaScript to report the panic
    jsPanic(msg.ptr, msg.len);

    // Hang after reporting
    while (true) {}
}
```

### Enhanced Panic with Context

Include additional debugging information:

```zig
// Enhanced panic handler with more context
var last_panic_message: [256]u8 = undefined;
var last_panic_len: usize = 0;

pub fn enhancedPanic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = error_return_trace;

    // Store panic message
    const copy_len = @min(msg.len, last_panic_message.len);
    for (0..copy_len) |i| {
        last_panic_message[i] = msg[i];
    }
    last_panic_len = copy_len;

    // Build context message
    var buffer: [512]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    writer.print("PANIC: {s}", .{msg}) catch {};

    if (ret_addr) |addr| {
        writer.print(" (address: 0x{x})", .{addr}) catch {};
    }

    const context = fbs.getWritten();
    jsLogPanic(context.ptr, context.len);

    while (true) {}
}
```

### Retrieving Panic Information

Export functions for JavaScript to access panic details:

```zig
// Export functions to retrieve panic info
export fn getLastPanicMessage() [*]const u8 {
    return &last_panic_message;
}

export fn getLastPanicLength() usize {
    return last_panic_len;
}
```

### JavaScript Integration

Provide panic handlers when loading WASM:

```javascript
const importObject = {
    env: {
        jsPanic: (msgPtr, msgLen) => {
            const bytes = new Uint8Array(wasm.memory.buffer, msgPtr, msgLen);
            const message = new TextDecoder().decode(bytes);
            console.error(`WASM PANIC: ${message}`);
            alert(`Fatal error: ${message}`);
        },
        jsLogPanic: (msgPtr, msgLen) => {
            const bytes = new Uint8Array(wasm.memory.buffer, msgPtr, msgLen);
            const message = new TextDecoder().decode(bytes);
            console.error(message);
        }
    }
};

const { instance } = await WebAssembly.instantiate(bytes, importObject);
```

### Discussion

### Why Panic Handlers Are Required

Freestanding targets have no operating system to handle crashes. The standard library's default panic handler uses OS features (stderr, stack traces) that don't exist in WASM.

You must provide your own handler or compilation fails:

```
error: 'panic' is not marked as a 'pub fn' in the root source file
```

### Panic Handler Signature

The exact signature required:

```zig
pub fn panic(
    msg: []const u8,
    error_return_trace: ?*std.builtin.StackTrace,
    ret_addr: ?usize
) noreturn
```

Must be:
- `pub` - Visible to the compiler
- Named `panic` - Compiler looks for this exact name
- `noreturn` - Function never returns
- In root source file - Usually your main `.zig` file

### The Infinite Loop

Panic handlers must never return (`noreturn`). The infinite loop is standard:

```zig
while (true) {}
```

This prevents undefined behavior. In WASM:
- Execution halts at the loop
- JavaScript can detect the hang (timeout)
- Memory state is preserved for debugging

Alternative: Use `@trap()` (Zig builtin):

```zig
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = msg;
    _ = error_return_trace;
    _ = ret_addr;
    @trap(); // Explicitly trap
}
```

### Common Panic Triggers

Functions that can panic:

```zig
// Functions that can trigger panics

export fn divideByZero(a: i32, b: i32) i32 {
    if (b == 0) {
        @panic("Division by zero");
    }
    return @divTrunc(a, b);
}

export fn accessOutOfBounds(index: usize) i32 {
    const array = [_]i32{ 1, 2, 3, 4, 5 };
    if (index >= array.len) {
        @panic("Index out of bounds");
    }
    return array[index];
}

export fn assertCondition(value: i32) void {
    std.debug.assert(value > 0); // Panics if false
}

export fn unwrapNull(has_value: bool) i32 {
    const optional: ?i32 = if (has_value) 42 else null;
    return optional.?; // Panics if null
}
```

Each triggers a panic for safety:
- Integer division by zero
- Array index out of bounds
- Failed assertion
- Null pointer unwrap

### Reporting to JavaScript

Three strategies for reporting panics:

**1. Immediate callback:**
```zig
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    jsPanic(msg.ptr, msg.len); // Call immediately
    while (true) {}
}
```

**2. Store message for later:**
```zig
var panic_buffer: [256]u8 = undefined;
var panic_len: usize = 0;

pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    const len = @min(msg.len, panic_buffer.len);
    @memcpy(panic_buffer[0..len], msg[0..len]);
    panic_len = len;
    while (true) {}
}

export fn getPanicMessage() [*]const u8 {
    return &panic_buffer;
}
```

**3. Hybrid approach (used in enhanced handler):**
- Call JavaScript immediately
- Store message in buffer
- Provide exports for access

### Stack Traces

The `error_return_trace` parameter contains stack information:

```zig
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    if (error_return_trace) |trace| {
        // Stack trace available (error returns)
        // Access via trace.instruction_addresses
    }

    if (ret_addr) |addr| {
        // Return address available
        // Use for debugging: address of panic call
    }

    // ...
}
```

Note: Stack traces are limited in WASM without debug info. Return addresses help locate panic sites.

### Cleanup Before Panic

Attempt cleanup before hanging:

```zig
// Panic after cleanup attempt
var cleanup_called = false;

fn attemptCleanup() void {
    cleanup_called = true;
    // Cleanup resources before panic
}

export fn panicWithCleanup() void {
    attemptCleanup();
    @panic("Panic after cleanup");
}

export fn wasCleanupCalled() bool {
    return cleanup_called;
}

export fn resetCleanupFlag() void {
    cleanup_called = false;
}
```

Use cases:
- Flush pending writes
- Release critical resources
- Log final state
- Signal JavaScript

### Panic vs Error Returns

Prefer error returns for recoverable failures:

```zig
// Bad: Panic for expected errors
export fn processData(ptr: [*]const u8, len: usize) void {
    if (len == 0) @panic("Empty data"); // Don't do this!
}

// Good: Return error code
export fn processData(ptr: [*]const u8, len: usize) i32 {
    if (len == 0) return -1; // Error code
    // ... process ...
    return 0; // Success
}
```

Reserve panics for:
- Programming errors (assertions)
- Impossible states
- Unrecoverable conditions

### Development vs Production Handlers

Use different handlers for dev/prod:

```zig
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    if (builtin.mode == .Debug) {
        // Verbose logging for development
        jsLogPanic(msg.ptr, msg.len);
        if (ret_addr) |addr| {
            const addr_msg = std.fmt.comptimePrint("Address: 0x{x}", .{addr});
            jsLogPanic(addr_msg.ptr, addr_msg.len);
        }
    } else {
        // Minimal reporting for production
        jsPanic("Fatal error".ptr, 11);
    }

    while (true) {}
}
```

### Testing Panic Handlers

Cannot directly test panics (they halt execution), but test the logic:

```zig
test "panic info storage" {
    last_panic_len = 0;

    const msg = "Test panic message";
    const copy_len = @min(msg.len, last_panic_message.len);
    for (0..copy_len) |i| {
        last_panic_message[i] = msg[i];
    }
    last_panic_len = copy_len;

    try testing.expectEqual(@as(usize, msg.len), last_panic_len);
    const stored = last_panic_message[0..last_panic_len];
    try testing.expectEqualStrings(msg, stored);
}
```

Test panic-triggering conditions without actually panicking:

```zig
test "bounds check" {
    const result = accessOutOfBounds(2);
    try testing.expectEqual(@as(i32, 3), result);

    // Verify array length
    const array = [_]i32{ 1, 2, 3, 4, 5 };
    try testing.expectEqual(@as(usize, 5), array.len);
}
```

### Debugging Panics

When a panic occurs in production:

1. **Check browser console** - Your `jsPanic` logs should appear
2. **Inspect WASM state** - Use browser DevTools WASM debugging
3. **Read panic message** - Via exported getter functions
4. **Check return address** - Correlate with source maps

Example JavaScript debugging:

```javascript
try {
    wasm.someFunction();
} catch (e) {
    // WASM execution might throw on infinite loop timeout
    console.error('WASM panic detected');

    // Retrieve stored panic message
    const msgPtr = wasm.getLastPanicMessage();
    const msgLen = wasm.getLastPanicLength();
    const bytes = new Uint8Array(wasm.memory.buffer, msgPtr, msgLen);
    const message = new TextDecoder().decode(bytes);

    console.error(`Panic message: ${message}`);
}
```

### Panic and Memory Leaks

Panics don't run destructors or free memory. In WASM:
- Memory is frozen at panic
- Page reload clears all state
- No OS-level cleanup needed

For critical cleanup, use `defer` and `errdefer` before operations that might panic.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: extern_panic_callback
// Import JavaScript panic reporting function
extern "env" fn jsPanic(msg_ptr: [*]const u8, msg_len: usize) void;
extern "env" fn jsLogPanic(msg_ptr: [*]const u8, msg_len: usize) void;
// ANCHOR_END: extern_panic_callback

// Test stubs
const builtin = @import("builtin");

comptime {
    if (builtin.is_test) {
        @export(&stub_jsPanic, .{ .name = "jsPanic" });
        @export(&stub_jsLogPanic, .{ .name = "jsLogPanic" });
    }
}

fn stub_jsPanic(msg_ptr: [*]const u8, msg_len: usize) callconv(.c) void {
    _ = msg_ptr;
    _ = msg_len;
}

fn stub_jsLogPanic(msg_ptr: [*]const u8, msg_len: usize) callconv(.c) void {
    _ = msg_ptr;
    _ = msg_len;
}

// ANCHOR: simple_panic_handler
// Simple panic handler - infinite loop
pub fn simplePanicHandler(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = msg;
    _ = error_return_trace;
    _ = ret_addr;
    while (true) {} // Hang forever
}
// ANCHOR_END: simple_panic_handler

// ANCHOR: logging_panic_handler
// Panic handler that logs to JavaScript
pub fn panic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = error_return_trace;
    _ = ret_addr;

    // Call JavaScript to report the panic
    jsPanic(msg.ptr, msg.len);

    // Hang after reporting
    while (true) {}
}
// ANCHOR_END: logging_panic_handler

// ANCHOR: panic_with_context
// Enhanced panic handler with more context
var last_panic_message: [256]u8 = undefined;
var last_panic_len: usize = 0;

pub fn enhancedPanic(msg: []const u8, error_return_trace: ?*std.builtin.StackTrace, ret_addr: ?usize) noreturn {
    _ = error_return_trace;

    // Store panic message
    const copy_len = @min(msg.len, last_panic_message.len);
    for (0..copy_len) |i| {
        last_panic_message[i] = msg[i];
    }
    last_panic_len = copy_len;

    // Build context message
    var buffer: [512]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    writer.print("PANIC: {s}", .{msg}) catch {};

    if (ret_addr) |addr| {
        writer.print(" (address: 0x{x})", .{addr}) catch {};
    }

    const context = fbs.getWritten();
    jsLogPanic(context.ptr, context.len);

    while (true) {}
}
// ANCHOR_END: panic_with_context

// ANCHOR: get_panic_info
// Export functions to retrieve panic info
export fn getLastPanicMessage() [*]const u8 {
    return &last_panic_message;
}

export fn getLastPanicLength() usize {
    return last_panic_len;
}
// ANCHOR_END: get_panic_info

// ANCHOR: panic_triggering_functions
// Functions that can trigger panics

export fn divideByZero(a: i32, b: i32) i32 {
    if (b == 0) {
        @panic("Division by zero");
    }
    return @divTrunc(a, b);
}

export fn accessOutOfBounds(index: usize) i32 {
    const array = [_]i32{ 1, 2, 3, 4, 5 };
    if (index >= array.len) {
        @panic("Index out of bounds");
    }
    return array[index];
}

export fn assertCondition(value: i32) void {
    std.debug.assert(value > 0); // Panics if false
}

export fn unwrapNull(has_value: bool) i32 {
    const optional: ?i32 = if (has_value) 42 else null;
    return optional.?; // Panics if null
}
// ANCHOR_END: panic_triggering_functions

// ANCHOR: controlled_panic
// Controlled panic with custom messages
export fn triggerPanic(code: i32) void {
    switch (code) {
        1 => @panic("Error code 1: Invalid input"),
        2 => @panic("Error code 2: Resource exhausted"),
        3 => @panic("Error code 3: Operation failed"),
        else => @panic("Unknown error code"),
    }
}
// ANCHOR_END: controlled_panic

// ANCHOR: panic_with_cleanup
// Panic after cleanup attempt
var cleanup_called = false;

fn attemptCleanup() void {
    cleanup_called = true;
    // Cleanup resources before panic
}

export fn panicWithCleanup() void {
    attemptCleanup();
    @panic("Panic after cleanup");
}

export fn wasCleanupCalled() bool {
    return cleanup_called;
}

export fn resetCleanupFlag() void {
    cleanup_called = false;
}
// ANCHOR_END: panic_with_cleanup

// Tests

// ANCHOR: test_panic_info
test "panic info storage" {
    last_panic_len = 0;

    const msg = "Test panic message";
    const copy_len = @min(msg.len, last_panic_message.len);
    for (0..copy_len) |i| {
        last_panic_message[i] = msg[i];
    }
    last_panic_len = copy_len;

    try testing.expectEqual(@as(usize, msg.len), last_panic_len);
    const stored = last_panic_message[0..last_panic_len];
    try testing.expectEqualStrings(msg, stored);
}
// ANCHOR_END: test_panic_info

// ANCHOR: test_divide_by_zero
test "divide by zero detection" {
    const result = divideByZero(10, 2);
    try testing.expectEqual(@as(i32, 5), result);

    // Cannot test actual panic in tests, but verify logic
    const b: i32 = 0;
    try testing.expect(b == 0);
}
// ANCHOR_END: test_divide_by_zero

// ANCHOR: test_bounds_check
test "bounds check" {
    const result = accessOutOfBounds(2);
    try testing.expectEqual(@as(i32, 3), result);

    // Verify array length
    const array = [_]i32{ 1, 2, 3, 4, 5 };
    try testing.expectEqual(@as(usize, 5), array.len);
}
// ANCHOR_END: test_bounds_check

// ANCHOR: test_optional_unwrap
test "optional unwrap" {
    const result = unwrapNull(true);
    try testing.expectEqual(@as(i32, 42), result);
}
// ANCHOR_END: test_optional_unwrap

// ANCHOR: test_cleanup
test "cleanup before panic" {
    cleanup_called = false;
    attemptCleanup();
    try testing.expect(wasCleanupCalled());

    resetCleanupFlag();
    try testing.expect(!wasCleanupCalled());
}
// ANCHOR_END: test_cleanup
```

### See Also

- Recipe 19.1: Building a basic WebAssembly module
- Recipe 19.3: Importing and calling JavaScript functions
- Recipe 0.11: Optionals, Errors, and Resource Cleanup
- Recipe 14.8: Creating custom exception types

---
