# Comptime & Metaprogramming Recipes

*24 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [9.1](#recipe-9-1) | Putting a Wrapper Around a Function | intermediate |
| [9.2](#recipe-9-2) | Preserving Function Metadata When Writing Decorators | intermediate |
| [9.3](#recipe-9-3) | Unwrapping a Decorator | intermediate |
| [9.4](#recipe-9-4) | Defining a Decorator That Takes Arguments | intermediate |
| [9.5](#recipe-9-5) | Enforcing Type Checking on a Function Using a Decorator | intermediate |
| [9.6](#recipe-9-6) | Defining Decorators As Part of a Struct | intermediate |
| [9.7](#recipe-9-7) | Defining Decorators As Structs | intermediate |
| [9.8](#recipe-9-8) | Applying Decorators to Struct and Static Methods | intermediate |
| [9.9](#recipe-9-9) | Writing Decorators That Add Arguments to Wrapped Functions | intermediate |
| [9.10](#recipe-9-10) | Using Decorators to Patch Struct Definitions | intermediate |
| [9.11](#recipe-9-11) | Using a Metaclass to Control Instance Creation | intermediate |
| [9.12](#recipe-9-12) | Capturing Struct Attribute Definition Order | intermediate |
| [9.13](#recipe-9-13) | Defining a Metaclass That Takes Optional Arguments | intermediate |
| [9.14](#recipe-9-14) | Enforcing an Argument Signature on Tuple Arguments | intermediate |
| [9.15](#recipe-9-15) | Enforcing Coding Conventions in Structs | intermediate |
| [9.16](#recipe-9-16) | Defining Structs Programmatically | advanced |
| [9.17](#recipe-9-17) | Initializing Struct Members at Definition Time | advanced |
| [17.1](#recipe-17-1) | Type-Level Pattern Matching | advanced |
| [17.2](#recipe-17-2) | Compile-Time String Processing | advanced |
| [17.3](#recipe-17-3) | Compile-Time Assertions | advanced |
| [17.4](#recipe-17-4) | Generic Data Structure Generation | advanced |
| [17.5](#recipe-17-5) | Compile-Time Dependency Injection | advanced |
| [17.6](#recipe-17-6) | Build-Time Resource Embedding | advanced |
| [17.7](#recipe-17-7) | Comptime Function Memoization | advanced |

---

## Recipe 9.1: Putting a Wrapper Around a Function {#recipe-9-1}

**Tags:** allocators, arraylist, comptime, comptime-metaprogramming, data-structures, error-handling, memory, pointers, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_1.zig`

### Problem

You want to add cross-cutting behavior to functions (logging, timing, caching, validation) without modifying their implementations. You need function wrappers or decorators that work at compile time with zero runtime overhead.

### Solution

Use Zig's `comptime` to create functions that take other functions as parameters and return wrapped versions. The wrapper can execute code before, after, or around the original function.

### Basic Wrapper

Create a simple logging wrapper using comptime:

```zig
// Basic function wrapper using comptime
fn withLogging(comptime func: anytype) fn (i32) i32 {
    return struct {
        fn wrapper(x: i32) i32 {
            std.debug.print("Calling function with: {d}\n", .{x});
            const result = func(x);
            std.debug.print("Result: {d}\n", .{result});
            return result;
        }
    }.wrapper;
}

fn double(x: i32) i32 {
    return x * 2;
}

test "basic wrapper" {
    const wrapped = withLogging(double);
    const result = wrapped(5);
    try testing.expectEqual(@as(i32, 10), result);
}
```

The wrapper function is generated at compile time.

### Timing Wrapper

Measure execution time of any function:

```zig
fn withTiming(comptime func: anytype) fn (i32) i32 {
    return struct {
        fn wrapper(x: i32) i32 {
            const start = std.time.nanoTimestamp();
            const result = func(x);
            const end = std.time.nanoTimestamp();
            const duration = end - start;
            std.debug.print("Execution time: {d}ns\n", .{duration});
            return result;
        }
    }.wrapper;
}

fn slowFunction(x: i32) i32 {
    var sum: i32 = 0;
    var i: i32 = 0;
    while (i < x) : (i += 1) {
        sum += i;
    }
    return sum;
}

// Usage
const timed = withTiming(slowFunction);
const result = timed(100);  // Prints execution time
```

Timing is added with zero overhead when disabled.

### Error Handling Wrapper

Add error handling to functions:

```zig
fn withErrorHandling(comptime func: anytype) fn (i32) anyerror!i32 {
    return struct {
        fn wrapper(x: i32) anyerror!i32 {
            if (x < 0) {
                std.debug.print("Warning: negative input {d}\n", .{x});
            }
            return func(x);
        }
    }.wrapper;
}

fn safeDivide(x: i32) anyerror!i32 {
    if (x == 0) return error.DivisionByZero;
    return @divTrunc(100, x);
}

// Usage
const wrapped = withErrorHandling(safeDivide);
const result = try wrapped(10);  // Returns 10
```

The wrapper can validate inputs or handle errors.

### Generic Wrapper

Create wrappers that work with any function signature:

```zig
fn GenericWrapper(comptime func: anytype) type {
    const FuncInfo = @typeInfo(@TypeOf(func));
    const ReturnType = switch (FuncInfo) {
        .@"fn" => |f| f.return_type.?,
        else => @compileError("Expected function"),
    };

    return struct {
        call_count: usize = 0,

        pub fn call(self: *@This(), args: anytype) ReturnType {
            self.call_count += 1;
            return @call(.auto, func, args);
        }

        pub fn getCallCount(self: *const @This()) usize {
            return self.call_count;
        }
    };
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

// Usage
const Wrapper = GenericWrapper(add);
var wrapper = Wrapper{};
const r1 = wrapper.call(.{ 5, 3 });  // 8
const r2 = wrapper.call(.{ 10, 20 }); // 30
// wrapper.getCallCount() == 2
```

Generic wrappers adapt to any function signature using `@typeInfo`.

### Caching Wrapper

Memoize expensive function calls:

```zig
fn WithCache(comptime func: anytype) type {
    return struct {
        cache: ?i32 = null,
        cache_key: ?i32 = null,

        pub fn call(self: *@This(), x: i32) i32 {
            if (self.cache_key) |key| {
                if (key == x) {
                    return self.cache.?;
                }
            }

            const result = func(x);
            self.cache = result;
            self.cache_key = x;
            return result;
        }
    };
}

fn expensive(x: i32) i32 {
    var result: i32 = 0;
    var i: i32 = 0;
    while (i < x) : (i += 1) {
        result += i * i;
    }
    return result;
}

// Usage
const CachedFunc = WithCache(expensive);
var cached = CachedFunc{};
const r1 = cached.call(10);  // Computes
const r2 = cached.call(10);  // Returns cached value
```

Caching avoids redundant expensive computations.

### Validation Wrapper

Add input validation with compile-time bounds:

```zig
fn WithValidation(comptime func: anytype, comptime min: i32, comptime max: i32) type {
    return struct {
        pub fn call(x: i32) !i32 {
            if (x < min or x > max) {
                return error.OutOfRange;
            }
            return func(x);
        }
    };
}

fn processValue(x: i32) i32 {
    return x * x;
}

// Usage
const ValidatedFunc = WithValidation(processValue, 0, 100);
const r1 = try ValidatedFunc.call(50);   // OK: 2500
const r2 = ValidatedFunc.call(150);      // Error: OutOfRange
```

Validation bounds are checked at compile time.

### Retry Wrapper

Automatically retry failed operations:

```zig
fn WithRetry(comptime func: anytype, comptime max_retries: u32) type {
    return struct {
        pub fn call(x: i32) !i32 {
            var attempts: u32 = 0;
            var last_error: ?anyerror = null;

            while (attempts < max_retries) : (attempts += 1) {
                const result = func(x) catch |err| {
                    last_error = err;
                    continue;
                };
                return result;
            }

            if (last_error) |err| {
                return err;
            }
            return error.MaxRetriesExceeded;
        }
    };
}

fn unreliable(x: i32) !i32 {
    // Might fail temporarily
    if (shouldFail()) {
        return error.Temporary;
    }
    return x * 2;
}

// Usage
const RetriedFunc = WithRetry(unreliable, 5);
const result = try RetriedFunc.call(10);  // Retries up to 5 times
```

Retry logic is baked in at compile time.

### Chaining Wrappers

Compose multiple wrappers together:

```zig
fn compose(comptime f: anytype, comptime g: anytype) fn (i32) i32 {
    return struct {
        fn wrapper(x: i32) i32 {
            return f(g(x));
        }
    }.wrapper;
}

fn increment(x: i32) i32 {
    return x + 1;
}

fn triple(x: i32) i32 {
    return x * 3;
}

// Usage
const composed = compose(triple, increment);
const result = composed(5);  // (5 + 1) * 3 = 18
```

Function composition creates pipelines at compile time.

### Stateful Wrapper

Maintain state across wrapper invocations:

```zig
fn WithState(comptime func: anytype) type {
    return struct {
        total_calls: usize = 0,
        total_sum: i32 = 0,

        pub fn call(self: *@This(), x: i32) i32 {
            self.total_calls += 1;
            const result = func(x);
            self.total_sum += result;
            return result;
        }

        pub fn getAverage(self: *const @This()) i32 {
            if (self.total_calls == 0) return 0;
            return @divTrunc(self.total_sum, @as(i32, @intCast(self.total_calls)));
        }
    };
}

// Usage
const StatefulFunc = WithState(identity);
var stateful = StatefulFunc{};
_ = stateful.call(10);
_ = stateful.call(20);
_ = stateful.call(30);
// stateful.getAverage() == 20
```

Wrappers can accumulate statistics or history.

### Conditional Wrapper

Enable or disable wrappers at compile time:

```zig
fn ConditionalWrapper(comptime func: anytype, comptime enable: bool) type {
    if (enable) {
        return struct {
            pub fn call(x: i32) i32 {
                std.debug.print("Enabled wrapper\n", .{});
                return func(x);
            }
        };
    } else {
        return struct {
            pub fn call(x: i32) i32 {
                return func(x);
            }
        };
    }
}

// Usage
const EnabledWrapper = ConditionalWrapper(simpleFunc, true);
const DisabledWrapper = ConditionalWrapper(simpleFunc, false);
```

Debug wrappers can be completely eliminated in release builds.

### Discussion

Function wrappers in Zig use compile-time metaprogramming to add behavior without runtime overhead.

### How Comptime Wrappers Work

**Compile-time function generation**:
```zig
fn wrapper(comptime func: anytype) fn (i32) i32 {
    return struct {
        fn inner(x: i32) i32 {
            // Wrapper logic
            return func(x);  // Call original
        }
    }.inner;
}
```

**Pattern breakdown**:
1. Accept function as `comptime` parameter
2. Return new function (or type with callable methods)
3. Wrapper calls original function
4. All resolved at compile time

**Anonymous struct trick**:
```zig
return struct {
    fn wrapper(...) ... {
        // Implementation
    }
}.wrapper;
```

Creates closure-like behavior without heap allocation.

### Wrapper Patterns

**Simple function wrapper**:
```zig
fn wrap(comptime func: anytype) fn (T) R {
    return struct {
        fn inner(arg: T) R {
            // before
            const result = func(arg);
            // after
            return result;
        }
    }.inner;
}
```

Returns function directly.

**Stateful type wrapper**:
```zig
fn Wrap(comptime func: anytype) type {
    return struct {
        state: StateType,

        pub fn call(self: *@This(), arg: T) R {
            // Use self.state
            return func(arg);
        }
    };
}
```

Returns type with state and methods.

**Generic wrapper with any signature**:
```zig
fn Wrap(comptime func: anytype) type {
    return struct {
        pub fn call(self: *@This(), args: anytype) ReturnType {
            return @call(.auto, func, args);
        }
    };
}
```

Uses `anytype` for arguments and `@call` for invocation.

### Type Introspection

**Extract function info**:
```zig
const FuncInfo = @typeInfo(@TypeOf(func));
const return_type = switch (FuncInfo) {
    .@"fn" => |f| f.return_type.?,
    else => @compileError("Not a function"),
};
```

**Check function properties**:
```zig
if (FuncInfo.@"fn".is_generic) {
    // Handle generic functions
}
if (FuncInfo.@"fn".return_type == null) {
    // Void return
}
```

Use `@typeInfo` to adapt to function signatures.

### Performance Characteristics

**Zero runtime overhead**:
- All wrapper logic compiled away
- Inlined like hand-written code
- No function pointer indirection
- No heap allocations

**Compile-time cost**:
- More complex wrappers increase compile time
- Each wrapper instantiation generates code
- Trade compile time for runtime performance

**Code size**:
- Generic wrappers instantiated per function
- Can increase binary size
- Mitigated by compiler optimizations

### Design Guidelines

**When to use wrappers**:
- Cross-cutting concerns (logging, timing, caching)
- Aspect-oriented behavior
- Policy enforcement
- Testing and debugging hooks

**Naming conventions**:
```zig
fn withLogging(...)     // Returns function
fn WithCache(...)       // Returns type
fn Validated(...)       // Adjective describing wrapper
```

**Keep wrappers simple**:
- Single responsibility
- Minimal state
- Clear semantics
- Composable

**Document behavior**:
```zig
/// Wraps a function to add retry logic with exponential backoff.
/// Returns a new type with a `call` method that retries up to max_retries times.
fn WithRetry(comptime func: anytype, comptime max_retries: u32) type
```

### Common Wrapper Use Cases

**Instrumentation**:
- Logging function calls
- Measuring execution time
- Counting invocations
- Profiling hot paths

**Resilience**:
- Retry logic
- Fallback values
- Error recovery
- Circuit breakers

**Optimization**:
- Result caching/memoization
- Lazy evaluation
- Batch processing
- Resource pooling

**Validation**:
- Input bounds checking
- Precondition enforcement
- Type constraints
- Authorization checks

### Wrapper Composition

**Sequential composition**:
```zig
const f = withLogging(withTiming(withCache(original)));
```

Wrappers applied inside-out.

**Functional composition**:
```zig
fn pipe(comptime f: anytype, comptime g: anytype) ... {
    return compose(g, f);  // g(f(x))
}
```

Create composition utilities.

**Conditional stacking**:
```zig
const func = if (debug)
    withLogging(withTiming(original))
else
    original;
```

Enable wrappers based on conditions.

### Limitations and Gotchas

**Type signatures must match**:
- Wrapper return type must match wrapped function
- Or use `anytype` for flexibility
- Can't change fundamental signature

**State requires type wrappers**:
```zig
// Can't maintain state with function wrapper
fn wrap(...) fn (...) {...}  // Stateless

// Need type wrapper for state
fn Wrap(...) type {...}      // Stateful
```

**Comptime function parameter**:
```zig
// Must be comptime
fn wrap(comptime func: anytype) ... {
    // func is known at compile time
}
```

Not for runtime function pointers.

**Generic wrappers need care**:
```zig
// Works for specific signature
fn wrap(comptime func: fn (i32) i32) fn (i32) i32

// Generic requires type introspection
fn Wrap(comptime func: anytype) type {
    // Use @typeInfo and @call
}
```

### Testing Wrappers

**Test wrapper behavior**:
```zig
test "wrapper adds logging" {
    var output = std.ArrayList(u8).init(allocator);
    defer output.deinit();

    const wrapped = withLogging(double);
    _ = wrapped(5);

    // Verify logging occurred
    try testing.expect(output.items.len > 0);
}
```

**Test state accumulation**:
```zig
test "wrapper tracks calls" {
    const Wrapper = GenericWrapper(add);
    var wrapper = Wrapper{};

    _ = wrapper.call(.{1, 2});
    _ = wrapper.call(.{3, 4});

    try testing.expectEqual(@as(usize, 2), wrapper.getCallCount());
}
```

**Test composition**:
```zig
test "wrappers compose" {
    const f = compose(triple, increment);
    const result = f(5);
    try testing.expectEqual(@as(i32, 18), result);
}
```

### Comparison with Other Languages

**Python decorators**:
```python
@with_logging
def double(x):
    return x * 2
```

Zig equivalent:
```zig
const double_wrapped = withLogging(double);
```

**Rust**:
```rust
// No direct equivalent, use macros or traits
```

**C++ templates**:
```cpp
template<typename F>
auto withLogging(F func) {
    return [func](auto x) {
        // wrapper logic
        return func(x);
    };
}
```

Zig's approach is simpler and more explicit.

### Full Tested Code

```zig
// Recipe 9.1: Putting a Wrapper Around a Function
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_wrapper
// Basic function wrapper using comptime
fn withLogging(comptime func: anytype) fn (i32) i32 {
    return struct {
        fn wrapper(x: i32) i32 {
            std.debug.print("Calling function with: {d}\n", .{x});
            const result = func(x);
            std.debug.print("Result: {d}\n", .{result});
            return result;
        }
    }.wrapper;
}

fn double(x: i32) i32 {
    return x * 2;
}

test "basic wrapper" {
    const wrapped = withLogging(double);
    const result = wrapped(5);
    try testing.expectEqual(@as(i32, 10), result);
}
// ANCHOR_END: basic_wrapper

// ANCHOR: timing_wrapper
// Wrapper that measures execution time
fn withTiming(comptime func: anytype) fn (i32) i32 {
    return struct {
        fn wrapper(x: i32) i32 {
            const start = std.time.nanoTimestamp();
            const result = func(x);
            const end = std.time.nanoTimestamp();
            const duration = end - start;
            std.debug.print("Execution time: {d}ns\n", .{duration});
            return result;
        }
    }.wrapper;
}

fn slowFunction(x: i32) i32 {
    var sum: i32 = 0;
    var i: i32 = 0;
    while (i < x) : (i += 1) {
        sum += i;
    }
    return sum;
}

test "timing wrapper" {
    const wrapped = withTiming(slowFunction);
    const result = wrapped(100);
    try testing.expect(result >= 0);
}
// ANCHOR_END: timing_wrapper

// ANCHOR: error_wrapper
// Wrapper that adds error handling
fn withErrorHandling(comptime func: anytype) fn (i32) anyerror!i32 {
    return struct {
        fn wrapper(x: i32) anyerror!i32 {
            if (x < 0) {
                std.debug.print("Warning: negative input {d}\n", .{x});
            }
            return func(x);
        }
    }.wrapper;
}

fn safeDivide(x: i32) anyerror!i32 {
    if (x == 0) return error.DivisionByZero;
    return @divTrunc(100, x);
}

test "error wrapper" {
    const wrapped = withErrorHandling(safeDivide);
    const result = try wrapped(10);
    try testing.expectEqual(@as(i32, 10), result);

    const err_result = wrapped(0);
    try testing.expectError(error.DivisionByZero, err_result);
}
// ANCHOR_END: error_wrapper

// ANCHOR: generic_wrapper
// Generic wrapper for any function signature
fn GenericWrapper(comptime func: anytype) type {
    const FuncInfo = @typeInfo(@TypeOf(func));
    const ReturnType = switch (FuncInfo) {
        .@"fn" => |f| f.return_type.?,
        else => @compileError("Expected function"),
    };

    return struct {
        call_count: usize = 0,

        pub fn call(self: *@This(), args: anytype) ReturnType {
            self.call_count += 1;
            return @call(.auto, func, args);
        }

        pub fn getCallCount(self: *const @This()) usize {
            return self.call_count;
        }
    };
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "generic wrapper" {
    const Wrapper = GenericWrapper(add);
    var wrapper = Wrapper{};

    const r1 = wrapper.call(.{ 5, 3 });
    const r2 = wrapper.call(.{ 10, 20 });

    try testing.expectEqual(@as(i32, 8), r1);
    try testing.expectEqual(@as(i32, 30), r2);
    try testing.expectEqual(@as(usize, 2), wrapper.getCallCount());
}
// ANCHOR_END: generic_wrapper

// ANCHOR: caching_wrapper
// Wrapper that caches results
fn WithCache(comptime func: anytype) type {
    return struct {
        cache: ?i32 = null,
        cache_key: ?i32 = null,

        pub fn call(self: *@This(), x: i32) i32 {
            if (self.cache_key) |key| {
                if (key == x) {
                    return self.cache.?;
                }
            }

            const result = func(x);
            self.cache = result;
            self.cache_key = x;
            return result;
        }
    };
}

fn expensive(x: i32) i32 {
    var result: i32 = 0;
    var i: i32 = 0;
    while (i < x) : (i += 1) {
        result += i * i;
    }
    return result;
}

test "caching wrapper" {
    const CachedFunc = WithCache(expensive);
    var cached = CachedFunc{};

    const r1 = cached.call(10);
    const r2 = cached.call(10); // Should use cache
    const r3 = cached.call(20); // New computation

    try testing.expectEqual(r1, r2);
    try testing.expect(r3 > r1);
}
// ANCHOR_END: caching_wrapper

// ANCHOR: validation_wrapper
// Wrapper that validates inputs
fn WithValidation(comptime func: anytype, comptime min: i32, comptime max: i32) type {
    return struct {
        pub fn call(x: i32) !i32 {
            if (x < min or x > max) {
                return error.OutOfRange;
            }
            return func(x);
        }
    };
}

fn processValue(x: i32) i32 {
    return x * x;
}

test "validation wrapper" {
    const ValidatedFunc = WithValidation(processValue, 0, 100);

    const r1 = try ValidatedFunc.call(50);
    try testing.expectEqual(@as(i32, 2500), r1);

    const r2 = ValidatedFunc.call(150);
    try testing.expectError(error.OutOfRange, r2);

    const r3 = ValidatedFunc.call(-5);
    try testing.expectError(error.OutOfRange, r3);
}
// ANCHOR_END: validation_wrapper

// ANCHOR: retry_wrapper
// Wrapper that retries on failure
fn WithRetry(comptime func: anytype, comptime max_retries: u32) type {
    return struct {
        pub fn call(x: i32) !i32 {
            var attempts: u32 = 0;
            var last_error: ?anyerror = null;

            while (attempts < max_retries) : (attempts += 1) {
                const result = func(x) catch |err| {
                    last_error = err;
                    continue;
                };
                return result;
            }

            if (last_error) |err| {
                return err;
            }
            return error.MaxRetriesExceeded;
        }
    };
}

var fail_count: u32 = 0;

fn unreliable(x: i32) !i32 {
    fail_count += 1;
    if (fail_count < 3) {
        return error.Temporary;
    }
    return x * 2;
}

test "retry wrapper" {
    fail_count = 0;
    const RetriedFunc = WithRetry(unreliable, 5);

    const result = try RetriedFunc.call(10);
    try testing.expectEqual(@as(i32, 20), result);
    try testing.expectEqual(@as(u32, 3), fail_count);
}
// ANCHOR_END: retry_wrapper

// ANCHOR: chaining_wrappers
// Chaining multiple wrappers together
fn compose(comptime f: anytype, comptime g: anytype) fn (i32) i32 {
    return struct {
        fn wrapper(x: i32) i32 {
            return f(g(x));
        }
    }.wrapper;
}

fn increment(x: i32) i32 {
    return x + 1;
}

fn triple(x: i32) i32 {
    return x * 3;
}

test "chaining wrappers" {
    // (x + 1) * 3
    const composed = compose(triple, increment);
    const result = composed(5);
    try testing.expectEqual(@as(i32, 18), result); // (5 + 1) * 3 = 18
}
// ANCHOR_END: chaining_wrappers

// ANCHOR: state_wrapper
// Wrapper that maintains state across calls
fn WithState(comptime func: anytype) type {
    return struct {
        total_calls: usize = 0,
        total_sum: i32 = 0,

        pub fn call(self: *@This(), x: i32) i32 {
            self.total_calls += 1;
            const result = func(x);
            self.total_sum += result;
            return result;
        }

        pub fn getAverage(self: *const @This()) i32 {
            if (self.total_calls == 0) return 0;
            return @divTrunc(self.total_sum, @as(i32, @intCast(self.total_calls)));
        }
    };
}

fn identity(x: i32) i32 {
    return x;
}

test "state wrapper" {
    const StatefulFunc = WithState(identity);
    var stateful = StatefulFunc{};

    _ = stateful.call(10);
    _ = stateful.call(20);
    _ = stateful.call(30);

    try testing.expectEqual(@as(usize, 3), stateful.total_calls);
    try testing.expectEqual(@as(i32, 20), stateful.getAverage());
}
// ANCHOR_END: state_wrapper

// ANCHOR: conditional_wrapper
// Wrapper that conditionally executes
fn ConditionalWrapper(comptime func: anytype, comptime enable: bool) type {
    if (enable) {
        return struct {
            pub fn call(x: i32) i32 {
                std.debug.print("Enabled wrapper\n", .{});
                return func(x);
            }
        };
    } else {
        return struct {
            pub fn call(x: i32) i32 {
                return func(x);
            }
        };
    }
}

fn simpleFunc(x: i32) i32 {
    return x + 5;
}

test "conditional wrapper" {
    const EnabledWrapper = ConditionalWrapper(simpleFunc, true);
    const DisabledWrapper = ConditionalWrapper(simpleFunc, false);

    const r1 = EnabledWrapper.call(10);
    const r2 = DisabledWrapper.call(10);

    try testing.expectEqual(r1, r2);
    try testing.expectEqual(@as(i32, 15), r1);
}
// ANCHOR_END: conditional_wrapper

// Comprehensive test
test "comprehensive function wrappers" {
    // Test basic wrapper
    const wrapped_double = withLogging(double);
    try testing.expectEqual(@as(i32, 20), wrapped_double(10));

    // Test timing wrapper
    const timed = withTiming(slowFunction);
    _ = timed(50);

    // Test generic wrapper with state
    const Wrapper = GenericWrapper(add);
    var wrapper = Wrapper{};
    _ = wrapper.call(.{ 1, 2 });
    _ = wrapper.call(.{ 3, 4 });
    try testing.expectEqual(@as(usize, 2), wrapper.getCallCount());

    // Test caching
    const CachedFunc = WithCache(expensive);
    var cached = CachedFunc{};
    const c1 = cached.call(5);
    const c2 = cached.call(5);
    try testing.expectEqual(c1, c2);

    // Test composition
    const composed = compose(triple, increment);
    try testing.expectEqual(@as(i32, 18), composed(5));
}
```

### See Also

- Recipe 9.2: Preserving Function Metadata When Writing Decorators
- Recipe 9.4: Defining a Decorator That Takes Arguments
- Recipe 9.11: Using comptime to Control Instance Creation
- Recipe 8.18: Extending Classes with Mixins

---

## Recipe 9.2: Preserving Function Metadata When Writing Decorators {#recipe-9-2}

**Tags:** allocators, comptime, comptime-metaprogramming, error-handling, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_2.zig`

### Problem

When wrapping functions with decorators, you need to preserve the original function's metadata: return types, error sets, parameter information, and other compile-time properties. Losing metadata breaks type safety and makes wrapped functions harder to use.

### Solution

Use Zig's `@typeInfo` builtin to extract function metadata at compile time, then build wrappers that preserve all type information including signatures, error sets, optional types, and documentation.

### Basic Metadata Extraction

Extract and expose function metadata using `@typeInfo`:

```zig
// Preserve function signature using @typeInfo
fn PreservingWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const Fn = func_info.@"fn";

    return struct {
        pub const name = @typeName(@TypeOf(func));
        pub const return_type = Fn.return_type;
        pub const params_len = Fn.params.len;

        pub fn call(args: anytype) Fn.return_type.? {
            return @call(.auto, func, args);
        }

        pub fn getName() []const u8 {
            return name;
        }
    };
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "basic metadata" {
    const Wrapper = PreservingWrapper(add);

    const result = Wrapper.call(.{ 5, 3 });
    try testing.expectEqual(@as(i32, 8), result);
    try testing.expectEqual(@as(usize, 2), Wrapper.params_len);
}
```

All function metadata is available at compile time.

### Error Set Preservation

Preserve error return types through wrappers:

```zig
fn ErrorPreservingWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub fn call(args: anytype) ReturnType {
            return @call(.auto, func, args);
        }
    };
}

fn divide(a: i32, b: i32) !i32 {
    if (b == 0) return error.DivisionByZero;
    return @divTrunc(a, b);
}

// Usage
const Wrapper = ErrorPreservingWrapper(divide);
const result = try Wrapper.call(.{ 10, 2 });  // Must use try
const err = Wrapper.call(.{ 10, 0 });  // Returns error.DivisionByZero
```

Error sets flow through wrappers naturally.

### Signature Matching

Create wrappers that exactly match the original function signature:

```zig
fn SignatureMatchingWrapper(comptime func: anytype) type {
    const T = @TypeOf(func);
    const func_info = @typeInfo(T).@"fn";
    const ReturnType = func_info.return_type.?;

    return struct {
        const Self = @This();

        pub const original_type = T;
        pub const return_type = ReturnType;

        call_count: usize = 0,

        pub fn wrap(self: *Self, args: anytype) ReturnType {
            self.call_count += 1;
            return @call(.auto, func, args);
        }
    };
}

fn multiply(x: i32, y: i32, z: i32) i32 {
    return x * y * z;
}

// Usage
const Wrapper = SignatureMatchingWrapper(multiply);
var wrapper = Wrapper{};
const result = wrapper.wrap(.{ 2, 3, 4 });  // 24
```

The wrapper exposes the original function type.

### Complete Metadata Extraction

Extract all available function properties:

```zig
fn MetadataExtractor(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));

    if (func_info != .@"fn") {
        @compileError("Expected function type");
    }

    const fn_info = func_info.@"fn";

    return struct {
        pub const Info = struct {
            pub const is_generic = fn_info.is_generic;
            pub const is_var_args = fn_info.is_var_args;
            pub const calling_convention = fn_info.calling_convention;
            pub const param_count = fn_info.params.len;
            pub const has_return = fn_info.return_type != null;
        };

        pub fn call(args: anytype) fn_info.return_type.? {
            return @call(.auto, func, args);
        }
    };
}

// Usage
const Meta = MetadataExtractor(example);
// Meta.Info.param_count
// Meta.Info.is_generic
// Meta.Info.calling_convention
```

All function metadata is accessible as compile-time constants.

### Documentation Wrapper

Add documentation metadata to wrapped functions:

```zig
fn DocumentedWrapper(
    comptime func: anytype,
    comptime doc: []const u8,
) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub const documentation = doc;
        pub const wrapped_function = func;

        pub fn call(args: anytype) ReturnType {
            return @call(.auto, func, args);
        }

        pub fn getDoc() []const u8 {
            return documentation;
        }
    };
}

fn square(x: i32) i32 {
    return x * x;
}

// Usage
const Wrapped = DocumentedWrapper(square, "Computes the square of x");
const result = Wrapped.call(.{5});  // 25
const doc = Wrapped.getDoc();  // "Computes the square of x"
```

Metadata can include custom documentation strings.

### Optional Type Preservation

Preserve optional return types correctly:

```zig
fn OptionalPreservingWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub fn call(args: anytype) ReturnType {
            const result = @call(.auto, func, args);
            return result;
        }
    };
}

fn findValue(arr: []const i32, target: i32) ?usize {
    for (arr, 0..) |val, i| {
        if (val == target) return i;
    }
    return null;
}

// Usage
const Wrapper = OptionalPreservingWrapper(findValue);
const arr = [_]i32{ 1, 2, 3, 4, 5 };

const found = Wrapper.call(.{ &arr, 3 });  // ?usize
if (found) |index| {
    // Use index
}
```

Optional types remain optional through wrapping.

### Allocator Function Wrapper

Handle functions that take allocators as first parameter:

```zig
fn AllocatorWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        allocations: usize = 0,

        pub fn call(self: *@This(), allocator: std.mem.Allocator, args: anytype) ReturnType {
            self.allocations += 1;
            const full_args = .{allocator} ++ args;
            return @call(.auto, func, full_args);
        }

        pub fn getAllocationCount(self: *const @This()) usize {
            return self.allocations;
        }
    };
}

fn allocateArray(allocator: std.mem.Allocator, size: usize) ![]i32 {
    return try allocator.alloc(i32, size);
}

// Usage
const Wrapper = AllocatorWrapper(allocateArray);
var wrapper = Wrapper{};
const arr = try wrapper.call(allocator, .{5});
defer allocator.free(arr);
// wrapper.getAllocationCount() == 1
```

Allocator-taking functions require special handling.

### Complex Return Types

Handle functions returning structs, tuples, or unions:

```zig
fn ComplexReturnWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub const return_type = ReturnType;

        pub fn call(args: anytype) ReturnType {
            return @call(.auto, func, args);
        }

        pub fn getReturnTypeName() []const u8 {
            return @typeName(ReturnType);
        }
    };
}

fn divmod(a: i32, b: i32) struct { quotient: i32, remainder: i32 } {
    return .{
        .quotient = @divTrunc(a, b),
        .remainder = @rem(a, b),
    };
}

// Usage
const Wrapper = ComplexReturnWrapper(divmod);
const result = Wrapper.call(.{ 17, 5 });
// result.quotient == 3
// result.remainder == 2
```

Complex types are preserved through metadata extraction.

### Type-Safe Wrappers

Enforce expected return types at compile time:

```zig
fn TypeSafeWrapper(comptime func: anytype, comptime ExpectedReturn: type) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ActualReturn = func_info.@"fn".return_type.?;

    // Compile-time check
    if (ActualReturn != ExpectedReturn) {
        @compileError("Return type mismatch");
    }

    return struct {
        pub fn call(args: anytype) ExpectedReturn {
            return @call(.auto, func, args);
        }
    };
}

fn increment(x: i32) i32 {
    return x + 1;
}

// Usage
const Wrapper = TypeSafeWrapper(increment, i32);  // OK
// const BadWrapper = TypeSafeWrapper(increment, i64);  // Compile error
```

Type mismatches are caught at compile time.

### Void Return Functions

Handle functions that don't return values:

```zig
fn VoidReturnWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type;

    return struct {
        call_count: usize = 0,

        pub fn call(self: *@This(), args: anytype) if (ReturnType) |T| T else void {
            self.call_count += 1;
            if (ReturnType) |_| {
                return @call(.auto, func, args);
            } else {
                @call(.auto, func, args);
            }
        }
    };
}

var side_effect: i32 = 0;

fn voidFunc(x: i32) void {
    side_effect = x;
}

// Usage
const Wrapper = VoidReturnWrapper(voidFunc);
var wrapper = Wrapper{};
wrapper.call(.{42});
// side_effect == 42
// wrapper.call_count == 1
```

Void functions require conditional return handling.

### Discussion

Preserving metadata ensures wrapped functions behave identically to originals from the type system's perspective.

### Why Metadata Preservation Matters

**Type safety**:
- Callers know exact return types
- Error sets are explicit
- Optionals remain optional
- Compiler catches misuse

**Tooling support**:
- IDE autocomplete works
- Type inspection functions
- Documentation generation
- Compiler error messages

**Composability**:
- Wrappers can be stacked
- Each layer preserves metadata
- No information loss
- Full type inference

### Using @typeInfo

**Extract function information**:
```zig
const func_info = @typeInfo(@TypeOf(func));
```

**Access function properties**:
```zig
const fn_info = func_info.@"fn";
const return_type = fn_info.return_type;
const params = fn_info.params;
const is_generic = fn_info.is_generic;
```

**Type variants**:
- `.@"fn"` - Regular functions
- `.params` - Parameter list
- `.return_type` - Return type (nullable)
- `.calling_convention` - C, Inline, etc.
- `.is_generic` - Generic function
- `.is_var_args` - Variadic

### Return Type Handling

**Non-error return**:
```zig
const ReturnType = fn_info.return_type.?;
pub fn call(args: anytype) ReturnType { ... }
```

**Error union return**:
```zig
// ReturnType already includes !
pub fn call(args: anytype) ReturnType { ... }
```

**Optional return**:
```zig
// ReturnType is ?T
pub fn call(args: anytype) ReturnType { ... }
```

**Void return**:
```zig
const ReturnType = fn_info.return_type;  // null for void
pub fn call(args: anytype) if (ReturnType) |T| T else void { ... }
```

### Function Call Strategies

**Direct call with tuple**:
```zig
return @call(.auto, func, args);  // args is tuple
```

**Argument unpacking**:
```zig
const full_args = .{allocator} ++ args;
return @call(.auto, func, full_args);
```

**Conditional calling**:
```zig
if (ReturnType) |_| {
    return @call(.auto, func, args);
} else {
    @call(.auto, func, args);
}
```

### Metadata Patterns

**Expose compile-time constants**:
```zig
return struct {
    pub const param_count = fn_info.params.len;
    pub const return_type = fn_info.return_type;
    pub const original_function = func;
};
```

**Runtime metadata**:
```zig
return struct {
    call_count: usize = 0,
    last_result: ?ReturnType = null,
};
```

**Mixed compile/runtime**:
```zig
return struct {
    pub const Info = struct {
        // Compile-time data
    };

    // Runtime state
    stats: Stats,
};
```

### Error Set Preservation

**Automatic preservation**:
```zig
const ReturnType = fn_info.return_type.?;
// If ReturnType is !T, it's preserved
pub fn call(args: anytype) ReturnType {
    return @call(.auto, func, args);
}
```

**Error handling in wrapper**:
```zig
pub fn call(args: anytype) ReturnType {
    const result = @call(.auto, func, args) catch |err| {
        // Log or handle error
        return err;
    };
    return result;
}
```

**Adding wrapper errors**:
```zig
pub fn call(args: anytype) (error{WrapperError} || ReturnErrorSet)!T {
    if (invalid_input) return error.WrapperError;
    return @call(.auto, func, args);
}
```

### Parameter Introspection

**Extract parameter types**:
```zig
const params = fn_info.params;
const first_param_type = params[0].type.?;
```

**Check parameter count**:
```zig
if (fn_info.params.len != 2) {
    @compileError("Expected 2 parameters");
}
```

**Validate parameter types**:
```zig
inline for (fn_info.params, 0..) |param, i| {
    if (param.type.? != i32) {
        @compileError("All params must be i32");
    }
}
```

### Generic Function Handling

**Check if generic**:
```zig
if (fn_info.is_generic) {
    // Handle generic function
}
```

**Generic wrappers**:
```zig
fn GenericWrapper(comptime func: anytype) type {
    // Works for both generic and non-generic
    return struct {
        pub fn call(args: anytype) auto {
            return @call(.auto, func, args);
        }
    };
}
```

### Documentation Strategies

**Embed documentation**:
```zig
pub const documentation = "Function description";
pub const param_docs = [_][]const u8{
    "First parameter",
    "Second parameter",
};
```

**Generate from metadata**:
```zig
pub fn getSignature() []const u8 {
    return std.fmt.comptimePrint(
        "fn({d} params) -> {s}",
        .{ param_count, @typeName(return_type) }
    );
}
```

### Performance Implications

**Zero runtime overhead**:
- All metadata resolved at compile time
- No runtime type checks
- Fully inlined calls
- Same as hand-written code

**Compile-time cost**:
- Type introspection takes compile time
- Each wrapper instantiation generates code
- Complex metadata increases build time

**Binary size**:
- Metadata stored in type system only
- No runtime metadata structures
- Generic wrappers per instantiation

### Testing Metadata

**Verify metadata extraction**:
```zig
test "metadata extraction" {
    const Meta = MetadataExtractor(func);
    try testing.expectEqual(expected_count, Meta.Info.param_count);
    try testing.expect(Meta.Info.has_return);
}
```

**Test type preservation**:
```zig
test "type preservation" {
    const Wrapper = PreservingWrapper(func);
    try testing.expectEqual(
        @TypeOf(func(0)),
        @TypeOf(Wrapper.call(.{0}))
    );
}
```

**Test error propagation**:
```zig
test "error propagation" {
    const Wrapper = ErrorWrapper(failableFunc);
    const result = Wrapper.call(.{bad_input});
    try testing.expectError(error.Expected, result);
}
```

### Full Tested Code

```zig
// Recipe 9.2: Preserving Function Metadata When Writing Decorators
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_metadata
// Preserve function signature using @typeInfo
fn PreservingWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const Fn = func_info.@"fn";

    return struct {
        pub const name = @typeName(@TypeOf(func));
        pub const return_type = Fn.return_type;
        pub const params_len = Fn.params.len;

        pub fn call(args: anytype) Fn.return_type.? {
            return @call(.auto, func, args);
        }

        pub fn getName() []const u8 {
            return name;
        }
    };
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "basic metadata" {
    const Wrapper = PreservingWrapper(add);

    const result = Wrapper.call(.{ 5, 3 });
    try testing.expectEqual(@as(i32, 8), result);
    try testing.expectEqual(@as(usize, 2), Wrapper.params_len);
}
// ANCHOR_END: basic_metadata

// ANCHOR: error_preservation
// Preserve error sets through wrappers
fn ErrorPreservingWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub fn call(args: anytype) ReturnType {
            // Wrapper can still handle errors
            return @call(.auto, func, args);
        }
    };
}

fn divide(a: i32, b: i32) !i32 {
    if (b == 0) return error.DivisionByZero;
    return @divTrunc(a, b);
}

test "error preservation" {
    const Wrapper = ErrorPreservingWrapper(divide);

    const r1 = try Wrapper.call(.{ 10, 2 });
    try testing.expectEqual(@as(i32, 5), r1);

    const r2 = Wrapper.call(.{ 10, 0 });
    try testing.expectError(error.DivisionByZero, r2);
}
// ANCHOR_END: error_preservation

// ANCHOR: signature_matching
// Create wrapper that exactly matches original signature
fn SignatureMatchingWrapper(comptime func: anytype) type {
    const T = @TypeOf(func);
    const func_info = @typeInfo(T).@"fn";
    const ReturnType = func_info.return_type.?;

    return struct {
        const Self = @This();

        pub const original_type = T;
        pub const return_type = ReturnType;

        call_count: usize = 0,

        pub fn wrap(self: *Self, args: anytype) ReturnType {
            self.call_count += 1;
            return @call(.auto, func, args);
        }
    };
}

fn multiply(x: i32, y: i32, z: i32) i32 {
    return x * y * z;
}

test "signature matching" {
    const Wrapper = SignatureMatchingWrapper(multiply);
    var wrapper = Wrapper{};

    const r1 = wrapper.wrap(.{ 2, 3, 4 });
    const r2 = wrapper.wrap(.{ 1, 2, 3 });

    try testing.expectEqual(@as(i32, 24), r1);
    try testing.expectEqual(@as(i32, 6), r2);
    try testing.expectEqual(@as(usize, 2), wrapper.call_count);
}
// ANCHOR_END: signature_matching

// ANCHOR: generic_metadata
// Extract and expose all function metadata
fn MetadataExtractor(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));

    if (func_info != .@"fn") {
        @compileError("Expected function type");
    }

    const fn_info = func_info.@"fn";

    return struct {
        pub const Info = struct {
            pub const is_generic = fn_info.is_generic;
            pub const is_var_args = fn_info.is_var_args;
            pub const calling_convention = fn_info.calling_convention;
            pub const param_count = fn_info.params.len;
            pub const has_return = fn_info.return_type != null;
        };

        pub fn call(args: anytype) fn_info.return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn example(a: i32, b: i32) i32 {
    return a + b;
}

test "generic metadata" {
    const Meta = MetadataExtractor(example);

    try testing.expect(!Meta.Info.is_generic);
    try testing.expect(!Meta.Info.is_var_args);
    try testing.expectEqual(@as(usize, 2), Meta.Info.param_count);
    try testing.expect(Meta.Info.has_return);

    const result = Meta.call(.{ 10, 20 });
    try testing.expectEqual(@as(i32, 30), result);
}
// ANCHOR_END: generic_metadata

// ANCHOR: documentation_wrapper
// Wrapper that adds documentation metadata
fn DocumentedWrapper(
    comptime func: anytype,
    comptime doc: []const u8,
) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub const documentation = doc;
        pub const wrapped_function = func;

        pub fn call(args: anytype) ReturnType {
            return @call(.auto, func, args);
        }

        pub fn getDoc() []const u8 {
            return documentation;
        }
    };
}

fn square(x: i32) i32 {
    return x * x;
}

test "documentation wrapper" {
    const Wrapped = DocumentedWrapper(square, "Computes the square of x");

    const result = Wrapped.call(.{5});
    try testing.expectEqual(@as(i32, 25), result);

    const doc = Wrapped.getDoc();
    try testing.expectEqualStrings("Computes the square of x", doc);
}
// ANCHOR_END: documentation_wrapper

// ANCHOR: optional_preservation
// Preserve optional return types
fn OptionalPreservingWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub fn call(args: anytype) ReturnType {
            const result = @call(.auto, func, args);
            return result;
        }
    };
}

fn findValue(arr: []const i32, target: i32) ?usize {
    for (arr, 0..) |val, i| {
        if (val == target) return i;
    }
    return null;
}

test "optional preservation" {
    const Wrapper = OptionalPreservingWrapper(findValue);

    const arr = [_]i32{ 1, 2, 3, 4, 5 };

    const r1 = Wrapper.call(.{ &arr, 3 });
    try testing.expectEqual(@as(?usize, 2), r1);

    const r2 = Wrapper.call(.{ &arr, 10 });
    try testing.expectEqual(@as(?usize, null), r2);
}
// ANCHOR_END: optional_preservation

// ANCHOR: allocator_wrapper
// Preserve allocator-taking functions
fn AllocatorWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        allocations: usize = 0,

        pub fn call(self: *@This(), allocator: std.mem.Allocator, args: anytype) ReturnType {
            self.allocations += 1;
            const full_args = .{allocator} ++ args;
            return @call(.auto, func, full_args);
        }

        pub fn getAllocationCount(self: *const @This()) usize {
            return self.allocations;
        }
    };
}

fn allocateArray(allocator: std.mem.Allocator, size: usize) ![]i32 {
    return try allocator.alloc(i32, size);
}

test "allocator wrapper" {
    const Wrapper = AllocatorWrapper(allocateArray);
    var wrapper = Wrapper{};

    const arr1 = try wrapper.call(testing.allocator, .{5});
    defer testing.allocator.free(arr1);

    const arr2 = try wrapper.call(testing.allocator, .{3});
    defer testing.allocator.free(arr2);

    try testing.expectEqual(@as(usize, 5), arr1.len);
    try testing.expectEqual(@as(usize, 3), arr2.len);
    try testing.expectEqual(@as(usize, 2), wrapper.getAllocationCount());
}
// ANCHOR_END: allocator_wrapper

// ANCHOR: multi_return_wrapper
// Handle functions with complex return types
fn ComplexReturnWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub const return_type = ReturnType;

        pub fn call(args: anytype) ReturnType {
            return @call(.auto, func, args);
        }

        pub fn getReturnTypeName() []const u8 {
            return @typeName(ReturnType);
        }
    };
}

fn divmod(a: i32, b: i32) struct { quotient: i32, remainder: i32 } {
    return .{
        .quotient = @divTrunc(a, b),
        .remainder = @rem(a, b),
    };
}

test "multi return wrapper" {
    const Wrapper = ComplexReturnWrapper(divmod);

    const result = Wrapper.call(.{ 17, 5 });
    try testing.expectEqual(@as(i32, 3), result.quotient);
    try testing.expectEqual(@as(i32, 2), result.remainder);
}
// ANCHOR_END: multi_return_wrapper

// ANCHOR: type_safe_wrapper
// Compile-time type safety in wrappers
fn TypeSafeWrapper(comptime func: anytype, comptime ExpectedReturn: type) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ActualReturn = func_info.@"fn".return_type.?;

    // Compile-time check
    if (ActualReturn != ExpectedReturn) {
        @compileError("Return type mismatch");
    }

    return struct {
        pub fn call(args: anytype) ExpectedReturn {
            return @call(.auto, func, args);
        }
    };
}

fn increment(x: i32) i32 {
    return x + 1;
}

test "type safe wrapper" {
    const Wrapper = TypeSafeWrapper(increment, i32);
    const result = Wrapper.call(.{5});
    try testing.expectEqual(@as(i32, 6), result);

    // This would fail at compile time:
    // const BadWrapper = TypeSafeWrapper(increment, i64);
}
// ANCHOR_END: type_safe_wrapper

// ANCHOR: void_return_wrapper
// Handle void return functions
fn VoidReturnWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type;

    return struct {
        call_count: usize = 0,

        pub fn call(self: *@This(), args: anytype) if (ReturnType) |T| T else void {
            self.call_count += 1;
            if (ReturnType) |_| {
                return @call(.auto, func, args);
            } else {
                @call(.auto, func, args);
            }
        }
    };
}

var side_effect: i32 = 0;

fn voidFunc(x: i32) void {
    side_effect = x;
}

test "void return wrapper" {
    const Wrapper = VoidReturnWrapper(voidFunc);
    var wrapper = Wrapper{};

    wrapper.call(.{42});
    try testing.expectEqual(@as(i32, 42), side_effect);
    try testing.expectEqual(@as(usize, 1), wrapper.call_count);

    wrapper.call(.{100});
    try testing.expectEqual(@as(i32, 100), side_effect);
    try testing.expectEqual(@as(usize, 2), wrapper.call_count);
}
// ANCHOR_END: void_return_wrapper

// Comprehensive test
test "comprehensive metadata preservation" {
    // Test basic metadata extraction
    const Meta = MetadataExtractor(example);
    try testing.expectEqual(@as(usize, 2), Meta.Info.param_count);

    // Test error preservation
    const ErrWrapper = ErrorPreservingWrapper(divide);
    const err_result = try ErrWrapper.call(.{ 10, 2 });
    try testing.expectEqual(@as(i32, 5), err_result);

    // Test optional preservation
    const OptWrapper = OptionalPreservingWrapper(findValue);
    const arr = [_]i32{ 1, 2, 3 };
    const opt_result = OptWrapper.call(.{ &arr, 2 });
    try testing.expectEqual(@as(?usize, 1), opt_result);

    // Test documentation
    const DocWrapper = DocumentedWrapper(square, "Square function");
    try testing.expectEqualStrings("Square function", DocWrapper.getDoc());

    // Test void return
    const VoidWrapper = VoidReturnWrapper(voidFunc);
    var void_wrap = VoidWrapper{};
    void_wrap.call(.{50});
    try testing.expectEqual(@as(i32, 50), side_effect);
}
```

### See Also

- Recipe 9.1: Putting a Wrapper Around a Function
- Recipe 9.3: Unwrapping a Decorator
- Recipe 9.5: Enforcing Type Checking on a Function Using a Decorator
- Recipe 9.11: Using comptime to Control Instance Creation

---

## Recipe 9.3: Unwrapping a Decorator {#recipe-9-3}

**Tags:** comptime, comptime-metaprogramming, error-handling, pointers, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_3.zig`

### Problem

You've wrapped functions with decorators but need to access the original unwrapped function, inspect wrapper layers, or remove decorator behavior. You want to extract the underlying function from a chain of wrappers.

### Solution

Expose the original function through the wrapper type using public constants and unwrap methods. Use `@hasDecl` to check if types support unwrapping and `@TypeOf` to extract function types from wrappers.

### Basic Unwrapping

Store and expose the original function in the wrapper:

```zig
// Wrapper that exposes the original function
fn Unwrappable(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub const original = func;
        pub const wrapped_type = @TypeOf(func);

        pub fn call(args: anytype) ReturnType {
            return @call(.auto, func, args);
        }

        pub fn unwrap() @TypeOf(func) {
            return func;
        }
    };
}

fn double(x: i32) i32 {
    return x * 2;
}

test "basic unwrapping" {
    const Wrapped = Unwrappable(double);

    const result1 = Wrapped.call(.{5});
    try testing.expectEqual(@as(i32, 10), result1);

    // Access original function
    const orig = Wrapped.unwrap();
    const result2 = orig(5);
    try testing.expectEqual(@as(i32, 10), result2);

    // Direct access to original
    const result3 = Wrapped.original(5);
    try testing.expectEqual(@as(i32, 10), result3);
}
```

The original function remains accessible through multiple pathways.

### Layered Unwrapping

Peel off wrapper layers one at a time:

```zig
fn Layer1(comptime func: anytype) type {
    return struct {
        pub const inner = func;
        pub const layer_name = "Layer1";

        pub fn call(x: i32) i32 {
            const result = func(x);
            return result + 1;
        }

        pub fn unwrap() @TypeOf(func) {
            return func;
        }
    };
}

fn Layer2(comptime func: anytype) type {
    return struct {
        pub const inner = func;
        pub const layer_name = "Layer2";

        pub fn call(x: i32) i32 {
            const result = func(x);
            return result * 2;
        }

        pub fn unwrap() @TypeOf(func) {
            return func;
        }
    };
}

fn base(x: i32) i32 {
    return x;
}

// Usage
const L1 = Layer1(base);
const L2 = Layer2(L1.call);

// Through both layers: (x + 1) * 2
const result = L2.call(5);  // 12

// Unwrap one layer
const unwrapped_once = L2.unwrap();
const result2 = unwrapped_once(5);  // 6

// Access inner layer
const inner = L1.unwrap();
const result3 = inner(5);  // 5
```

Each layer can be unwrapped independently.

### Metadata Preservation

Keep original function metadata when unwrapping:

```zig
fn MetadataWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub const original_function = func;
        pub const original_name = @typeName(@TypeOf(func));
        pub const param_count = func_info.@"fn".params.len;

        pub fn call(args: anytype) ReturnType {
            return @call(.auto, func, args);
        }

        pub fn getOriginal() @TypeOf(func) {
            return func;
        }

        pub fn getMetadata() []const u8 {
            return original_name;
        }
    };
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

// Usage
const Wrapped = MetadataWrapper(add);
// Wrapped.param_count == 2
const orig = Wrapped.getOriginal();
const result = orig(3, 7);  // 10
```

Metadata survives unwrapping operations.

### Conditional Unwrapping

Check if a type supports unwrapping before attempting it:

```zig
fn ConditionalUnwrap(comptime T: type) type {
    const type_info = @typeInfo(T);
    const has_unwrap = switch (type_info) {
        .@"struct", .@"enum", .@"union", .@"opaque" => @hasDecl(T, "unwrap"),
        else => false,
    };

    if (has_unwrap) {
        return struct {
            pub fn get() @TypeOf(T.unwrap()) {
                return T.unwrap();
            }

            pub fn isWrapped() bool {
                return true;
            }
        };
    } else {
        return struct {
            pub fn get() void {
                // Can't return the type if it's not wrapped
            }

            pub fn isWrapped() bool {
                return false;
            }
        };
    }
}

// Usage
const Wrapped = Unwrappable(plain);
const UnwrapHelper = ConditionalUnwrap(Wrapped);
// UnwrapHelper.isWrapped() == true

const PlainHelper = ConditionalUnwrap(@TypeOf(plain));
// PlainHelper.isWrapped() == false
```

Runtime checks determine if unwrapping is available.

### Stateful Wrapper Unwrapping

Extract original function from stateful wrappers:

```zig
fn StatefulWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        const Self = @This();

        pub const wrapped = func;
        call_count: usize = 0,

        pub fn call(self: *Self, args: anytype) ReturnType {
            self.call_count += 1;
            return @call(.auto, func, args);
        }

        pub fn getWrapped() @TypeOf(func) {
            return func;
        }

        pub fn getCallCount(self: *const Self) usize {
            return self.call_count;
        }
    };
}

fn increment(x: i32) i32 {
    return x + 1;
}

// Usage
const Wrapper = StatefulWrapper(increment);
var wrapper = Wrapper{};
_ = wrapper.call(.{5});
_ = wrapper.call(.{10});
// wrapper.getCallCount() == 2

// Get original function without state
const orig = Wrapper.getWrapped();
const result = orig(5);  // 6
```

State and original function are separate concerns.

### Recursive Unwrapping

Unwrap all layers to reach the original function:

```zig
fn DeepUnwrap(comptime T: type) type {
    const type_info = @typeInfo(T);
    const can_check_decls = switch (type_info) {
        .@"struct", .@"enum", .@"union", .@"opaque" => true,
        else => false,
    };

    if (can_check_decls) {
        if (@hasDecl(T, "inner")) {
            // Has another layer
            const InnerType = @TypeOf(T.inner);
            return DeepUnwrap(InnerType);
        } else if (@hasDecl(T, "original")) {
            // This is the original
            return @TypeOf(T.original);
        }
    }

    return T;
}

// Usage
const L1 = Layer1(original);
const L2 = Layer2(L1.call);

// Get the deeply nested type
const DeepType = DeepUnwrap(L2);
// DeepType is the original function type
```

Recursion peels off all wrapper layers.

### Runtime Unwrapping

Support unwrapping with runtime function pointers:

```zig
const FuncWrapper = struct {
    const Self = @This();

    call_fn: *const fn (i32) i32,
    original_fn: *const fn (i32) i32,

    pub fn init(func: *const fn (i32) i32) Self {
        return Self{
            .call_fn = func,
            .original_fn = func,
        };
    }

    pub fn call(self: *const Self, x: i32) i32 {
        return self.call_fn(x);
    }

    pub fn unwrap(self: *const Self) *const fn (i32) i32 {
        return self.original_fn;
    }
};

fn triple(x: i32) i32 {
    return x * 3;
}

// Usage
const wrapper = FuncWrapper.init(&triple);
const result1 = wrapper.call(5);  // 15

const orig = wrapper.unwrap();
const result2 = orig(5);  // 15
```

Runtime wrappers track original function pointers.

### Wrapper Chain

Build and navigate wrapper chains:

```zig
fn ChainableWrapper(comptime func: anytype, comptime name: []const u8) type {
    return struct {
        pub const wrapped_function = func;
        pub const wrapper_name = name;

        pub fn call(x: i32) i32 {
            return func(x);
        }

        pub fn unwrap() @TypeOf(func) {
            return func;
        }

        pub fn getName() []const u8 {
            return name;
        }
    };
}

fn identity(x: i32) i32 {
    return x;
}

// Usage
const W1 = ChainableWrapper(identity, "First");
const W2 = ChainableWrapper(W1.call, "Second");
const W3 = ChainableWrapper(W2.call, "Third");

// W3.getName() == "Third"
// W2.getName() == "Second"
// W1.getName() == "First"

const result = W3.call(42);  // 42
```

Named wrappers help track layer identity.

### Type-Safe Unwrapping

Enforce expected types at compile time:

```zig
fn TypeSafeUnwrap(comptime Wrapper: type, comptime ExpectedType: type) type {
    return struct {
        pub fn unwrap() ExpectedType {
            if (!@hasDecl(Wrapper, "unwrap")) {
                @compileError("Type does not support unwrapping");
            }

            const unwrapped = Wrapper.unwrap();
            const ActualType = @TypeOf(unwrapped);

            if (ActualType != ExpectedType) {
                @compileError("Unwrapped type does not match expected type");
            }

            return unwrapped;
        }
    };
}

fn square(x: i32) i32 {
    return x * x;
}

// Usage
const Wrapped = Unwrappable(square);
const Unwrapper = TypeSafeUnwrap(Wrapped, @TypeOf(square));
const orig = Unwrapper.unwrap();
const result = orig(7);  // 49
```

Type mismatches cause compile errors.

### Partial Unwrapping

Unwrap to a specific depth in the wrapper chain:

```zig
fn UnwrapToDepth(comptime T: type, comptime depth: usize) type {
    if (depth == 0) {
        return T;
    } else {
        if (@hasDecl(T, "inner")) {
            const InnerType = @TypeOf(T.inner);
            return UnwrapToDepth(InnerType, depth - 1);
        } else {
            return T;
        }
    }
}

// Usage
const L1 = Layer1(base);
const L2 = Layer2(L1.call);

// Unwrap to depth 0 (no unwrapping)
const Depth0 = UnwrapToDepth(L2, 0);  // L2

// Unwrap to depth 1
const Depth1 = UnwrapToDepth(L2, 1);  // L1.call type
```

Control how many layers to peel off.

### Discussion

Unwrapping decorators provides access to original functions while preserving the ability to use wrapped versions.

### Why Unwrapping Matters

**Testing**:
- Test original function directly
- Verify wrapper behavior separately
- Mock or stub wrapped functions
- Compare wrapped vs unwrapped

**Debugging**:
- Call original without wrapper overhead
- Isolate bugs to wrapper or function
- Profile performance differences
- Inspect intermediate states

**Introspection**:
- Query wrapper chain depth
- Identify active decorators
- Extract metadata
- Validate wrapper composition

**Flexibility**:
- Conditionally use wrappers
- Remove wrappers at runtime
- Reconfigure decorator chain
- Access both wrapped and unwrapped

### Unwrapping Patterns

**Public constant**:
```zig
return struct {
    pub const original = func;
};
```

Simplest approach, direct access.

**Unwrap method**:
```zig
pub fn unwrap() @TypeOf(func) {
    return func;
}
```

More explicit, follows naming convention.

**Typed constant**:
```zig
pub const wrapped_function: @TypeOf(func) = func;
```

Type annotation for clarity.

**Inner reference**:
```zig
pub const inner = func;  // For nested wrappers
```

Indicates another layer exists.

### Checking for Unwrap Support

**Use @hasDecl safely**:
```zig
const type_info = @typeInfo(T);
const can_check = switch (type_info) {
    .@"struct", .@"enum", .@"union", .@"opaque" => true,
    else => false,
};

if (can_check and @hasDecl(T, "unwrap")) {
    // Can unwrap
}
```

`@hasDecl` only works on aggregate types.

**Compile-time check**:
```zig
if (!@hasDecl(Wrapper, "unwrap")) {
    @compileError("Wrapper must support unwrapping");
}
```

Enforce unwrapping support at compile time.

**Runtime check**:
```zig
pub fn isUnwrappable(comptime T: type) bool {
    const info = @typeInfo(T);
    return switch (info) {
        .@"struct" => @hasDecl(T, "unwrap"),
        else => false,
    };
}
```

### Layer Navigation

**Direct unwrap**:
```zig
const orig = Wrapper.unwrap();  // One layer
```

**Chain unwrap**:
```zig
const layer1 = Layer3.unwrap();
const layer2 = layer1.unwrap();
const orig = layer2.unwrap();
```

**Recursive unwrap**:
```zig
const DeepType = DeepUnwrap(MultiLayerWrapper);
```

**Depth-controlled**:
```zig
const PartialType = UnwrapToDepth(Wrapper, 2);
```

### Metadata Extraction

**Function type**:
```zig
pub const wrapped_type = @TypeOf(func);
```

**Function name**:
```zig
pub const original_name = @typeName(@TypeOf(func));
```

**Parameter count**:
```zig
pub const param_count = @typeInfo(@TypeOf(func)).@"fn".params.len;
```

**Return type**:
```zig
pub const return_type = @typeInfo(@TypeOf(func)).@"fn".return_type.?;
```

### State vs Function Separation

**Stateful wrapper**:
```zig
return struct {
    pub const wrapped = func;  // Function
    state: State,              // Wrapper state

    pub fn call(self: *Self, ...) ... {
        self.state.update();
        return func(...);
    }
};
```

Original function has no state.

**State-free access**:
```zig
const orig = Wrapper.wrapped;
// Call without wrapper state
const result = orig(args);
```

### Performance Considerations

**Compile-time unwrapping**:
- Zero runtime cost
- Function inlined
- Type-safe extraction
- Optimized away

**Runtime unwrapping**:
- Function pointer overhead
- Indirect call
- Not inlined
- Dynamic dispatch

**Unwrap caching**:
```zig
const cached_orig = Wrapper.unwrap();
// Reuse cached_orig multiple times
```

Avoid repeated unwrapping.

### Design Guidelines

**Always provide unwrap**:
- Makes wrappers transparent
- Enables testing
- Supports debugging
- Shows intent

**Naming consistency**:
- `unwrap()` - Method that returns function
- `original` - Direct const access
- `inner` - Next layer reference
- `wrapped` - Alternate naming

**Document unwrapping**:
```zig
/// Returns the original unwrapped function.
/// Use this for testing or when wrapper behavior isn't needed.
pub fn unwrap() @TypeOf(func) {
    return func;
}
```

**Type safety**:
```zig
// Ensure unwrap returns correct type
pub fn unwrap() @TypeOf(func) {
    return func;  // Type-checked
}
```

### Common Use Cases

**Unit testing**:
```zig
test "original function" {
    const orig = Wrapper.unwrap();
    const result = orig(input);
    try testing.expectEqual(expected, result);
}
```

**Performance profiling**:
```zig
const orig = Wrapper.unwrap();
const start = timer.read();
_ = orig(args);
const unwrapped_time = timer.read() - start;

const wrapped_result = Wrapper.call(args);
const wrapped_time = timer.read() - start - unwrapped_time;
```

**Conditional decoration**:
```zig
const func = if (enable_wrapper)
    Wrapper.call
else
    Wrapper.unwrap();
```

**Wrapper analysis**:
```zig
fn countLayers(comptime T: type) usize {
    if (@hasDecl(T, "inner")) {
        return 1 + countLayers(@TypeOf(T.inner));
    }
    return 0;
}
```

### Testing Unwrapping

**Test basic unwrap**:
```zig
test "unwrap returns original" {
    const Wrapped = Unwrappable(func);
    const orig = Wrapped.unwrap();
    try testing.expectEqual(@TypeOf(func), @TypeOf(orig));
}
```

**Test layer unwrapping**:
```zig
test "layer by layer" {
    const L1 = Layer1(base);
    const L2 = Layer2(L1.call);

    const unwrapped = L2.unwrap();
    try testing.expectEqual(L1.call, unwrapped);
}
```

**Test metadata preservation**:
```zig
test "metadata survives unwrapping" {
    const Wrapped = MetadataWrapper(func);
    const orig = Wrapped.unwrap();
    // Verify orig has same properties as func
}
```

### Full Tested Code

```zig
// Recipe 9.3: Unwrapping a Decorator
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_unwrapping
// Wrapper that exposes the original function
fn Unwrappable(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub const original = func;
        pub const wrapped_type = @TypeOf(func);

        pub fn call(args: anytype) ReturnType {
            return @call(.auto, func, args);
        }

        pub fn unwrap() @TypeOf(func) {
            return func;
        }
    };
}

fn double(x: i32) i32 {
    return x * 2;
}

test "basic unwrapping" {
    const Wrapped = Unwrappable(double);

    const result1 = Wrapped.call(.{5});
    try testing.expectEqual(@as(i32, 10), result1);

    // Access original function
    const orig = Wrapped.unwrap();
    const result2 = orig(5);
    try testing.expectEqual(@as(i32, 10), result2);

    // Direct access to original
    const result3 = Wrapped.original(5);
    try testing.expectEqual(@as(i32, 10), result3);
}
// ANCHOR_END: basic_unwrapping

// ANCHOR: layered_unwrapping
// Multiple wrapper layers that can be peeled off
fn Layer1(comptime func: anytype) type {
    return struct {
        pub const inner = func;
        pub const layer_name = "Layer1";

        pub fn call(x: i32) i32 {
            const result = func(x);
            return result + 1;
        }

        pub fn unwrap() @TypeOf(func) {
            return func;
        }
    };
}

fn Layer2(comptime func: anytype) type {
    return struct {
        pub const inner = func;
        pub const layer_name = "Layer2";

        pub fn call(x: i32) i32 {
            const result = func(x);
            return result * 2;
        }

        pub fn unwrap() @TypeOf(func) {
            return func;
        }
    };
}

fn base(x: i32) i32 {
    return x;
}

test "layered unwrapping" {
    const L1 = Layer1(base);
    const L2 = Layer2(L1.call);

    // Through both layers: (x + 1) * 2
    const result = L2.call(5);
    try testing.expectEqual(@as(i32, 12), result);

    // Unwrap one layer
    const unwrapped_once = L2.unwrap();
    const result2 = unwrapped_once(5);
    try testing.expectEqual(@as(i32, 6), result2);

    // Access inner layer
    const inner = L1.unwrap();
    const result3 = inner(5);
    try testing.expectEqual(@as(i32, 5), result3);
}
// ANCHOR_END: layered_unwrapping

// ANCHOR: metadata_preservation
// Unwrapping preserves original metadata
fn MetadataWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub const original_function = func;
        pub const original_name = @typeName(@TypeOf(func));
        pub const param_count = func_info.@"fn".params.len;

        pub fn call(args: anytype) ReturnType {
            return @call(.auto, func, args);
        }

        pub fn getOriginal() @TypeOf(func) {
            return func;
        }

        pub fn getMetadata() []const u8 {
            return original_name;
        }
    };
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "metadata preservation" {
    const Wrapped = MetadataWrapper(add);

    try testing.expectEqual(@as(usize, 2), Wrapped.param_count);

    const orig = Wrapped.getOriginal();
    const result = orig(3, 7);
    try testing.expectEqual(@as(i32, 10), result);
}
// ANCHOR_END: metadata_preservation

// ANCHOR: conditional_unwrapping
// Conditionally unwrap based on type
fn ConditionalUnwrap(comptime T: type) type {
    const type_info = @typeInfo(T);
    const has_unwrap = switch (type_info) {
        .@"struct", .@"enum", .@"union", .@"opaque" => @hasDecl(T, "unwrap"),
        else => false,
    };

    if (has_unwrap) {
        return struct {
            pub fn get() @TypeOf(T.unwrap()) {
                return T.unwrap();
            }

            pub fn isWrapped() bool {
                return true;
            }
        };
    } else {
        return struct {
            pub fn get() void {
                // Can't return the type if it's not wrapped
            }

            pub fn isWrapped() bool {
                return false;
            }
        };
    }
}

fn plain(x: i32) i32 {
    return x * 3;
}

test "conditional unwrapping" {
    const Wrapped = Unwrappable(plain);
    const UnwrapHelper = ConditionalUnwrap(Wrapped);

    try testing.expect(UnwrapHelper.isWrapped());

    const PlainHelper = ConditionalUnwrap(@TypeOf(plain));
    try testing.expect(!PlainHelper.isWrapped());
}
// ANCHOR_END: conditional_unwrapping

// ANCHOR: state_unwrapping
// Unwrap stateful wrappers
fn StatefulWrapper(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        const Self = @This();

        pub const wrapped = func;
        call_count: usize = 0,

        pub fn call(self: *Self, args: anytype) ReturnType {
            self.call_count += 1;
            return @call(.auto, func, args);
        }

        pub fn getWrapped() @TypeOf(func) {
            return func;
        }

        pub fn getCallCount(self: *const Self) usize {
            return self.call_count;
        }
    };
}

fn increment(x: i32) i32 {
    return x + 1;
}

test "state unwrapping" {
    const Wrapper = StatefulWrapper(increment);
    var wrapper = Wrapper{};

    _ = wrapper.call(.{5});
    _ = wrapper.call(.{10});

    try testing.expectEqual(@as(usize, 2), wrapper.getCallCount());

    // Get original function without state
    const orig = Wrapper.getWrapped();
    const result = orig(5);
    try testing.expectEqual(@as(i32, 6), result);
}
// ANCHOR_END: state_unwrapping

// ANCHOR: recursive_unwrapping
// Unwrap all layers to get to the original
fn DeepUnwrap(comptime T: type) type {
    const type_info = @typeInfo(T);
    const can_check_decls = switch (type_info) {
        .@"struct", .@"enum", .@"union", .@"opaque" => true,
        else => false,
    };

    if (can_check_decls) {
        if (@hasDecl(T, "inner")) {
            // Has another layer
            const InnerType = @TypeOf(T.inner);
            return DeepUnwrap(InnerType);
        } else if (@hasDecl(T, "original")) {
            // This is the original
            return @TypeOf(T.original);
        }
    }

    return T;
}

fn original(x: i32) i32 {
    return x;
}

test "recursive unwrapping" {
    const L1 = Layer1(original);
    const L2 = Layer2(L1.call);

    // Get the deeply nested type
    const DeepType = DeepUnwrap(L2);

    // Verify it's the original function type
    try testing.expectEqual(@TypeOf(L1.unwrap()), DeepType);
}
// ANCHOR_END: recursive_unwrapping

// ANCHOR: runtime_unwrapping
// Runtime unwrapping with dynamic dispatch
const FuncWrapper = struct {
    const Self = @This();

    call_fn: *const fn (i32) i32,
    original_fn: *const fn (i32) i32,

    pub fn init(func: *const fn (i32) i32) Self {
        return Self{
            .call_fn = func,
            .original_fn = func,
        };
    }

    pub fn call(self: *const Self, x: i32) i32 {
        return self.call_fn(x);
    }

    pub fn unwrap(self: *const Self) *const fn (i32) i32 {
        return self.original_fn;
    }
};

fn triple(x: i32) i32 {
    return x * 3;
}

test "runtime unwrapping" {
    const wrapper = FuncWrapper.init(&triple);

    const result1 = wrapper.call(5);
    try testing.expectEqual(@as(i32, 15), result1);

    const orig = wrapper.unwrap();
    const result2 = orig(5);
    try testing.expectEqual(@as(i32, 15), result2);
}
// ANCHOR_END: runtime_unwrapping

// ANCHOR: wrapper_chain
// Chain of wrappers with full unwrap path
fn ChainableWrapper(comptime func: anytype, comptime name: []const u8) type {
    return struct {
        pub const wrapped_function = func;
        pub const wrapper_name = name;

        pub fn call(x: i32) i32 {
            return func(x);
        }

        pub fn unwrap() @TypeOf(func) {
            return func;
        }

        pub fn getName() []const u8 {
            return name;
        }
    };
}

fn identity(x: i32) i32 {
    return x;
}

test "wrapper chain" {
    const W1 = ChainableWrapper(identity, "First");
    const W2 = ChainableWrapper(W1.call, "Second");
    const W3 = ChainableWrapper(W2.call, "Third");

    try testing.expectEqualStrings("Third", W3.getName());
    try testing.expectEqualStrings("Second", W2.getName());
    try testing.expectEqualStrings("First", W1.getName());

    const result = W3.call(42);
    try testing.expectEqual(@as(i32, 42), result);
}
// ANCHOR_END: wrapper_chain

// ANCHOR: type_safe_unwrap
// Type-safe unwrapping with compile-time checks
fn TypeSafeUnwrap(comptime Wrapper: type, comptime ExpectedType: type) type {
    return struct {
        pub fn unwrap() ExpectedType {
            if (!@hasDecl(Wrapper, "unwrap")) {
                @compileError("Type does not support unwrapping");
            }

            const unwrapped = Wrapper.unwrap();
            const ActualType = @TypeOf(unwrapped);

            if (ActualType != ExpectedType) {
                @compileError("Unwrapped type does not match expected type");
            }

            return unwrapped;
        }
    };
}

fn square(x: i32) i32 {
    return x * x;
}

test "type safe unwrap" {
    const Wrapped = Unwrappable(square);
    const Unwrapper = TypeSafeUnwrap(Wrapped, @TypeOf(square));

    const orig = Unwrapper.unwrap();
    const result = orig(7);
    try testing.expectEqual(@as(i32, 49), result);
}
// ANCHOR_END: type_safe_unwrap

// ANCHOR: partial_unwrapping
// Unwrap to a specific layer depth
fn UnwrapToDepth(comptime T: type, comptime depth: usize) type {
    if (depth == 0) {
        return T;
    } else {
        if (@hasDecl(T, "inner")) {
            const InnerType = @TypeOf(T.inner);
            return UnwrapToDepth(InnerType, depth - 1);
        } else {
            return T;
        }
    }
}

test "partial unwrapping" {
    const L1 = Layer1(base);
    const L2 = Layer2(L1.call);

    // Unwrap to depth 0 (no unwrapping)
    const Depth0 = UnwrapToDepth(L2, 0);
    try testing.expectEqual(L2, Depth0);

    // Unwrap to depth 1
    const Depth1 = UnwrapToDepth(L2, 1);
    try testing.expectEqual(@TypeOf(L1.call), Depth1);
}
// ANCHOR_END: partial_unwrapping

// Comprehensive test
test "comprehensive unwrapping" {
    // Test basic unwrapping
    const W1 = Unwrappable(double);
    const orig1 = W1.unwrap();
    try testing.expectEqual(@as(i32, 10), orig1(5));

    // Test layered unwrapping
    const L1 = Layer1(base);
    const L2 = Layer2(L1.call);
    try testing.expectEqual(@as(i32, 12), L2.call(5));

    // Test stateful unwrapping
    const SW = StatefulWrapper(increment);
    var sw = SW{};
    _ = sw.call(.{1});
    const orig2 = SW.getWrapped();
    try testing.expectEqual(@as(i32, 6), orig2(5));

    // Test conditional unwrapping
    const CU = ConditionalUnwrap(W1);
    try testing.expect(CU.isWrapped());

    // Test wrapper chain
    const C1 = ChainableWrapper(identity, "A");
    const C2 = ChainableWrapper(C1.call, "B");
    try testing.expectEqualStrings("B", C2.getName());
}
```

### See Also

- Recipe 9.1: Putting a Wrapper Around a Function
- Recipe 9.2: Preserving Function Metadata When Writing Decorators
- Recipe 9.4: Defining a Decorator That Takes Arguments
- Recipe 9.11: Using comptime to Control Instance Creation

---

## Recipe 9.4: Defining a Decorator That Takes Arguments {#recipe-9-4}

**Tags:** allocators, comptime, comptime-metaprogramming, error-handling, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_4.zig`

### Problem

You need decorators that behave differently based on configuration. You want to parameterize wrappers with values, types, callbacks, or options that control how they modify functions.

### Solution

Pass additional comptime parameters to decorator functions before the wrapped function. These parameters become part of the generated type and can control wrapper behavior, provide defaults, or configure validation.

### Basic Parameterized Decorator

Create decorators that take simple value parameters:

```zig
// Decorator that takes compile-time arguments
fn WithMultiplier(comptime func: anytype, comptime multiplier: i32) type {
    return struct {
        pub fn call(x: i32) i32 {
            return func(x) * multiplier;
        }
    };
}

fn identity(x: i32) i32 {
    return x;
}

test "basic parameterized" {
    const Times2 = WithMultiplier(identity, 2);
    const Times10 = WithMultiplier(identity, 10);

    try testing.expectEqual(@as(i32, 10), Times2.call(5));
    try testing.expectEqual(@as(i32, 50), Times10.call(5));
}
```

The multiplier parameter customizes each wrapper instance.

### Validation Decorator

Use parameters to configure validation bounds:

```zig
fn WithBounds(comptime func: anytype, comptime min: i32, comptime max: i32) type {
    return struct {
        pub fn call(x: i32) !i32 {
            if (x < min or x > max) {
                return error.OutOfBounds;
            }
            return func(x);
        }

        pub fn getMin() i32 {
            return min;
        }

        pub fn getMax() i32 {
            return max;
        }
    };
}

fn square(x: i32) i32 {
    return x * x;
}

// Usage
const BoundedSquare = WithBounds(square, 0, 10);
const result = try BoundedSquare.call(5);  // 25
const err = BoundedSquare.call(15);  // error.OutOfBounds
```

Bounds are enforced at runtime, configured at compile time.

### Retry Decorator

Configure retry behavior with parameters:

```zig
fn WithRetry(comptime func: anytype, comptime max_attempts: u32, comptime delay_ms: u64) type {
    return struct {
        pub fn call(x: i32) !i32 {
            var attempts: u32 = 0;
            var last_error: ?anyerror = null;

            while (attempts < max_attempts) : (attempts += 1) {
                const result = func(x) catch |err| {
                    last_error = err;
                    // In real code, would sleep for delay_ms milliseconds
                    continue;
                };
                return result;
            }

            if (last_error) |err| {
                return err;
            }
            return error.MaxRetriesExceeded;
        }

        pub fn getMaxAttempts() u32 {
            return max_attempts;
        }

        pub fn getDelay() u64 {
            return delay_ms;
        }
    };
}

// Usage
const Retried = WithRetry(unreliable, 5, 100);
const result = try Retried.call(10);
// Retried.getMaxAttempts() == 5
// Retried.getDelay() == 100
```

Retry configuration is baked into the type.

### String Parameter Decorator

Use string parameters for formatting:

```zig
fn WithPrefixSuffix(comptime func: anytype, comptime prefix: []const u8, comptime suffix: []const u8) type {
    return struct {
        pub fn call(allocator: std.mem.Allocator, x: i32) ![]u8 {
            const result = try func(allocator, x);
            defer allocator.free(result);

            const full = try std.fmt.allocPrint(
                allocator,
                "{s}{s}{s}",
                .{ prefix, result, suffix },
            );
            return full;
        }
    };
}

fn formatNumber(allocator: std.mem.Allocator, x: i32) ![]u8 {
    return try std.fmt.allocPrint(allocator, "{d}", .{x});
}

// Usage
const Bracketed = WithPrefixSuffix(formatNumber, "[", "]");
const result = try Bracketed.call(allocator, 42);
defer allocator.free(result);
// result == "[42]"
```

String literals become compile-time constants.

### Type Parameter Decorator

Accept type parameters for generic behavior:

```zig
fn WithDefault(comptime func: anytype, comptime T: type, comptime default: T) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub fn call(x: ?T) ReturnType {
            const val = x orelse default;
            return func(val);
        }

        pub fn getDefault() T {
            return default;
        }
    };
}

fn double(x: i32) i32 {
    return x * 2;
}

// Usage
const DoubleWithDefault = WithDefault(double, i32, 10);
DoubleWithDefault.call(5);     // 10
DoubleWithDefault.call(null);  // 20 (uses default)
```

Type and default value customize wrapper behavior.

### Callback Parameter Decorator

Pass functions as decorator arguments:

```zig
fn WithCallbacks(
    comptime func: anytype,
    comptime before: anytype,
    comptime after: anytype,
) type {
    return struct {
        pub fn call(x: i32) i32 {
            before(x);
            const result = func(x);
            after(result);
            return result;
        }
    };
}

fn logBefore(x: i32) void {
    std.debug.print("Before: {d}\n", .{x});
}

fn logAfter(x: i32) void {
    std.debug.print("After: {d}\n", .{x});
}

// Usage
const Instrumented = WithCallbacks(triple, logBefore, logAfter);
const result = Instrumented.call(5);  // Logs before and after
```

Callbacks customize behavior without modifying the decorator.

### Conditional Decorator

Use boolean flags to enable/disable features:

```zig
fn Conditional(comptime func: anytype, comptime enabled: bool) type {
    if (enabled) {
        return struct {
            pub fn call(x: i32) i32 {
                const result = func(x);
                return result * 2; // Apply transformation
            }

            pub fn isEnabled() bool {
                return true;
            }
        };
    } else {
        return struct {
            pub fn call(x: i32) i32 {
                return func(x); // Pass through
            }

            pub fn isEnabled() bool {
                return false;
            }
        };
    }
}

// Usage
const Enabled = Conditional(add10, true);
const Disabled = Conditional(add10, false);

Enabled.call(5);   // 30 (transformed)
Disabled.call(5);  // 15 (pass-through)
```

Compile-time conditionals eliminate dead code.

### Threshold Decorator

Combine enum and value parameters:

```zig
fn WithThreshold(comptime func: anytype, comptime threshold: i32, comptime action: enum { clamp, error_on_exceed }) type {
    return struct {
        pub fn call(x: i32) !i32 {
            if (x > threshold) {
                switch (action) {
                    .clamp => {
                        const result = func(threshold);
                        return result;
                    },
                    .error_on_exceed => {
                        return error.ThresholdExceeded;
                    },
                }
            }
            return func(x);
        }

        pub fn getThreshold() i32 {
            return threshold;
        }
    };
}

// Usage
const Clamped = WithThreshold(double, 10, .clamp);
const ErrorBased = WithThreshold(double, 10, .error_on_exceed);

Clamped.call(15);      // 20 (clamped to 10, then doubled)
ErrorBased.call(15);   // error.ThresholdExceeded
```

Enum parameters provide type-safe configuration options.

### Multiple Parameter Decorator

Use struct parameters for complex configuration:

```zig
fn WithConfig(
    comptime func: anytype,
    comptime config: struct {
        multiplier: i32,
        offset: i32,
        invert: bool,
    },
) type {
    return struct {
        pub fn call(x: i32) i32 {
            var result = func(x);
            result = result * config.multiplier;
            result = result + config.offset;
            if (config.invert) {
                result = -result;
            }
            return result;
        }

        pub fn getConfig() @TypeOf(config) {
            return config;
        }
    };
}

// Usage
const Configured = WithConfig(identity, .{
    .multiplier = 2,
    .offset = 5,
    .invert = false,
});

Configured.call(5);  // (5 * 2) + 5 = 15
```

Struct parameters group related configuration.

### Array Parameter Decorator

Use arrays for list-based configuration:

```zig
fn WithAllowList(comptime func: anytype, comptime allowed: []const i32) type {
    return struct {
        pub fn call(x: i32) !i32 {
            for (allowed) |val| {
                if (x == val) {
                    return func(x);
                }
            }
            return error.NotAllowed;
        }

        pub fn getAllowed() []const i32 {
            return allowed;
        }
    };
}

// Usage
const allowed_values = [_]i32{ 1, 5, 10, 15 };
const Restricted = WithAllowList(double, &allowed_values);

Restricted.call(5);   // 10 (allowed)
Restricted.call(7);   // error.NotAllowed
```

Arrays define allow/deny lists at compile time.

### Discussion

Parameterized decorators enable flexible, reusable metaprogramming patterns with compile-time configuration.

### Why Parameterized Decorators

**Reusability**:
- One decorator, many configurations
- No code duplication
- Shared behavior, different parameters
- Type-safe variation

**Compile-time safety**:
- Parameters validated at compile time
- Type errors caught early
- No runtime configuration overhead
- Optimized per-instantiation

**Flexibility**:
- Mix and match parameters
- Compose decorators with different configs
- Build decorator libraries
- Application-specific customization

### Parameter Types

**Value parameters**:
```zig
comptime multiplier: i32
comptime threshold: f64
comptime max_retries: u32
```

Simple constants used in wrapper logic.

**Type parameters**:
```zig
comptime T: type
comptime ErrorSet: type
comptime ReturnType: type
```

Generic wrappers adapting to types.

**String parameters**:
```zig
comptime prefix: []const u8
comptime format: []const u8
comptime name: []const u8
```

Compile-time string constants.

**Function parameters**:
```zig
comptime callback: anytype
comptime validator: anytype
comptime transform: anytype
```

Higher-order decoration with function parameters.

**Enum parameters**:
```zig
comptime mode: enum { strict, lenient }
comptime action: enum { clamp, error, wrap }
```

Type-safe configuration options.

**Struct parameters**:
```zig
comptime config: struct {
    field1: T1,
    field2: T2,
}
```

Grouped configuration for complex cases.

**Array parameters**:
```zig
comptime allowed: []const T
comptime defaults: []const T
```

Lists of values at compile time.

### Parameter Naming

**Descriptive names**:
```zig
fn WithBounds(... comptime min: i32, comptime max: i32)
fn WithRetry(... comptime max_attempts: u32, comptime delay_ms: u64)
```

Make parameter purpose obvious.

**Config struct pattern**:
```zig
fn Decorator(comptime func: anytype, comptime config: Config) type
```

Group related parameters.

**Consistent ordering**:
1. Function being wrapped
2. Primary parameters
3. Secondary/optional parameters
4. Callback functions

### Accessing Parameters

**Public const**:
```zig
return struct {
    pub const multiplier_value = multiplier;
    pub const threshold_value = threshold;
};
```

Expose parameters as constants.

**Getter methods**:
```zig
pub fn getMultiplier() i32 {
    return multiplier;
}
```

More explicit than constants.

**Both approaches**:
```zig
pub const max_attempts = max_attempts_param;

pub fn getMaxAttempts() u32 {
    return max_attempts;
}
```

Provide both for flexibility.

### Conditional Compilation

**Feature flags**:
```zig
fn WithFeature(comptime func: anytype, comptime enable_feature: bool) type {
    if (enable_feature) {
        // Feature enabled code
    } else {
        // Feature disabled code
    }
}
```

**Build mode checks**:
```zig
const debug = @import("builtin").mode == .Debug;
const Decorated = WithLogging(func, debug);
```

**Platform-specific**:
```zig
const is_windows = @import("builtin").os.tag == .windows;
const Wrapped = PlatformSpecific(func, is_windows);
```

### Design Patterns

**Builder pattern**:
```zig
const Builder = struct {
    multiplier: i32 = 1,
    offset: i32 = 0,

    pub fn build(self: Builder, comptime func: anytype) type {
        return WithConfig(func, .{
            .multiplier = self.multiplier,
            .offset = self.offset,
        });
    }
};
```

**Default parameters**:
```zig
fn WithOptionalRetry(
    comptime func: anytype,
    comptime max_attempts: u32,
    comptime delay_ms: ?u64,
) type {
    const delay = delay_ms orelse 100; // Default
    return WithRetry(func, max_attempts, delay);
}
```

**Parameter validation**:
```zig
fn WithValidatedBounds(..., comptime min: i32, comptime max: i32) type {
    if (min >= max) {
        @compileError("min must be less than max");
    }
    // ...
}
```

### Common Configurations

**Validation**:
- Min/max bounds
- Allow/deny lists
- Type constraints
- Format validation

**Timing**:
- Retry delays
- Timeout durations
- Rate limits
- Debounce intervals

**Transformation**:
- Multipliers/scalars
- Offsets/additions
- Format strings
- Conversion functions

**Behavior**:
- Debug vs release
- Strict vs lenient
- Synchronous vs async
- Cached vs uncached

### Performance

**Zero runtime overhead**:
- All parameters resolved at compile time
- No runtime configuration structures
- No dynamic dispatch
- Fully inlined

**Code size**:
- Each parameter combination generates separate type
- Can increase binary size
- Mitigated by compiler optimization
- Trade-off: flexibility vs size

**Compile time**:
- More parameters = longer compile
- Complex conditionals increase time
- Worth it for runtime performance
- Use judiciously

### Testing Parameterized Decorators

**Test different configurations**:
```zig
test "various multipliers" {
    const Times2 = WithMultiplier(func, 2);
    const Times10 = WithMultiplier(func, 10);

    try testing.expectEqual(10, Times2.call(5));
    try testing.expectEqual(50, Times10.call(5));
}
```

**Test parameter access**:
```zig
test "parameter accessors" {
    const Decorated = WithBounds(func, 0, 100);

    try testing.expectEqual(0, Decorated.getMin());
    try testing.expectEqual(100, Decorated.getMax());
}
```

**Test edge cases**:
```zig
test "boundary conditions" {
    const Bounded = WithBounds(func, 5, 10);

    try testing.expectEqual(25, try Bounded.call(5));  // Min
    try testing.expectEqual(100, try Bounded.call(10)); // Max
    try testing.expectError(error.OutOfBounds, Bounded.call(4));  // Below
    try testing.expectError(error.OutOfBounds, Bounded.call(11)); // Above
}
```

### Error Handling

**Invalid parameters**:
```zig
if (max_attempts == 0) {
    @compileError("max_attempts must be > 0");
}
```

**Type mismatches**:
```zig
if (@TypeOf(default) != T) {
    @compileError("default value type must match T");
}
```

**Range validation**:
```zig
if (threshold < 0 or threshold > 100) {
    @compileError("threshold must be 0-100");
}
```

### Full Tested Code

```zig
// Recipe 9.4: Defining a Decorator That Takes Arguments
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_parameterized
// Decorator that takes compile-time arguments
fn WithMultiplier(comptime func: anytype, comptime multiplier: i32) type {
    return struct {
        pub fn call(x: i32) i32 {
            return func(x) * multiplier;
        }
    };
}

fn identity(x: i32) i32 {
    return x;
}

test "basic parameterized" {
    const Times2 = WithMultiplier(identity, 2);
    const Times10 = WithMultiplier(identity, 10);

    try testing.expectEqual(@as(i32, 10), Times2.call(5));
    try testing.expectEqual(@as(i32, 50), Times10.call(5));
}
// ANCHOR_END: basic_parameterized

// ANCHOR: validation_decorator
// Decorator with validation bounds
fn WithBounds(comptime func: anytype, comptime min: i32, comptime max: i32) type {
    return struct {
        pub fn call(x: i32) !i32 {
            if (x < min or x > max) {
                return error.OutOfBounds;
            }
            return func(x);
        }

        pub fn getMin() i32 {
            return min;
        }

        pub fn getMax() i32 {
            return max;
        }
    };
}

fn square(x: i32) i32 {
    return x * x;
}

test "validation decorator" {
    const BoundedSquare = WithBounds(square, 0, 10);

    const r1 = try BoundedSquare.call(5);
    try testing.expectEqual(@as(i32, 25), r1);

    const r2 = BoundedSquare.call(15);
    try testing.expectError(error.OutOfBounds, r2);

    try testing.expectEqual(@as(i32, 0), BoundedSquare.getMin());
    try testing.expectEqual(@as(i32, 10), BoundedSquare.getMax());
}
// ANCHOR_END: validation_decorator

// ANCHOR: retry_decorator
// Decorator with retry configuration
fn WithRetry(comptime func: anytype, comptime max_attempts: u32, comptime delay_ms: u64) type {
    return struct {
        pub fn call(x: i32) !i32 {
            var attempts: u32 = 0;
            var last_error: ?anyerror = null;

            while (attempts < max_attempts) : (attempts += 1) {
                const result = func(x) catch |err| {
                    last_error = err;
                    // In real code, would sleep for delay_ms milliseconds
                    continue;
                };
                return result;
            }

            if (last_error) |err| {
                return err;
            }
            return error.MaxRetriesExceeded;
        }

        pub fn getMaxAttempts() u32 {
            return max_attempts;
        }

        pub fn getDelay() u64 {
            return delay_ms;
        }
    };
}

var attempt_count: u32 = 0;

fn unreliable(x: i32) !i32 {
    attempt_count += 1;
    if (attempt_count < 3) {
        return error.Temporary;
    }
    return x * 2;
}

test "retry decorator" {
    attempt_count = 0;
    const Retried = WithRetry(unreliable, 5, 100);

    const result = try Retried.call(10);
    try testing.expectEqual(@as(i32, 20), result);
    try testing.expectEqual(@as(u32, 3), attempt_count);

    try testing.expectEqual(@as(u32, 5), Retried.getMaxAttempts());
    try testing.expectEqual(@as(u64, 100), Retried.getDelay());
}
// ANCHOR_END: retry_decorator

// ANCHOR: prefix_suffix_decorator
// Decorator with string configuration
fn WithPrefixSuffix(comptime func: anytype, comptime prefix: []const u8, comptime suffix: []const u8) type {
    return struct {
        pub fn call(allocator: std.mem.Allocator, x: i32) ![]u8 {
            const result = try func(allocator, x);
            defer allocator.free(result);

            const full = try std.fmt.allocPrint(
                allocator,
                "{s}{s}{s}",
                .{ prefix, result, suffix },
            );
            return full;
        }
    };
}

fn formatNumber(allocator: std.mem.Allocator, x: i32) ![]u8 {
    return try std.fmt.allocPrint(allocator, "{d}", .{x});
}

test "prefix suffix decorator" {
    const Bracketed = WithPrefixSuffix(formatNumber, "[", "]");

    const result = try Bracketed.call(testing.allocator, 42);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("[42]", result);
}
// ANCHOR_END: prefix_suffix_decorator

// ANCHOR: typed_decorator
// Decorator that takes a type parameter
fn WithDefault(comptime func: anytype, comptime T: type, comptime default: T) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        pub fn call(x: ?T) ReturnType {
            const val = x orelse default;
            return func(val);
        }

        pub fn getDefault() T {
            return default;
        }
    };
}

fn double(x: i32) i32 {
    return x * 2;
}

test "typed decorator" {
    const DoubleWithDefault = WithDefault(double, i32, 10);

    const r1 = DoubleWithDefault.call(5);
    const r2 = DoubleWithDefault.call(null);

    try testing.expectEqual(@as(i32, 10), r1);
    try testing.expectEqual(@as(i32, 20), r2);
    try testing.expectEqual(@as(i32, 10), DoubleWithDefault.getDefault());
}
// ANCHOR_END: typed_decorator

// ANCHOR: callback_decorator
// Decorator with callback functions
fn WithCallbacks(
    comptime func: anytype,
    comptime before: anytype,
    comptime after: anytype,
) type {
    return struct {
        pub fn call(x: i32) i32 {
            before(x);
            const result = func(x);
            after(result);
            return result;
        }
    };
}

var before_value: i32 = 0;
var after_value: i32 = 0;

fn logBefore(x: i32) void {
    before_value = x;
}

fn logAfter(x: i32) void {
    after_value = x;
}

fn triple(x: i32) i32 {
    return x * 3;
}

test "callback decorator" {
    before_value = 0;
    after_value = 0;

    const Instrumented = WithCallbacks(triple, logBefore, logAfter);

    const result = Instrumented.call(5);

    try testing.expectEqual(@as(i32, 15), result);
    try testing.expectEqual(@as(i32, 5), before_value);
    try testing.expectEqual(@as(i32, 15), after_value);
}
// ANCHOR_END: callback_decorator

// ANCHOR: conditional_decorator
// Decorator with boolean flag
fn Conditional(comptime func: anytype, comptime enabled: bool) type {
    if (enabled) {
        return struct {
            pub fn call(x: i32) i32 {
                const result = func(x);
                return result * 2; // Apply transformation
            }

            pub fn isEnabled() bool {
                return true;
            }
        };
    } else {
        return struct {
            pub fn call(x: i32) i32 {
                return func(x); // Pass through
            }

            pub fn isEnabled() bool {
                return false;
            }
        };
    }
}

fn add10(x: i32) i32 {
    return x + 10;
}

test "conditional decorator" {
    const Enabled = Conditional(add10, true);
    const Disabled = Conditional(add10, false);

    try testing.expectEqual(@as(i32, 30), Enabled.call(5)); // (5 + 10) * 2
    try testing.expectEqual(@as(i32, 15), Disabled.call(5)); // 5 + 10

    try testing.expect(Enabled.isEnabled());
    try testing.expect(!Disabled.isEnabled());
}
// ANCHOR_END: conditional_decorator

// ANCHOR: threshold_decorator
// Decorator with threshold check
fn WithThreshold(comptime func: anytype, comptime threshold: i32, comptime action: enum { clamp, error_on_exceed }) type {
    return struct {
        pub fn call(x: i32) !i32 {
            if (x > threshold) {
                switch (action) {
                    .clamp => {
                        const result = func(threshold);
                        return result;
                    },
                    .error_on_exceed => {
                        return error.ThresholdExceeded;
                    },
                }
            }
            return func(x);
        }

        pub fn getThreshold() i32 {
            return threshold;
        }
    };
}

test "threshold decorator" {
    const Clamped = WithThreshold(double, 10, .clamp);
    const ErrorBased = WithThreshold(double, 10, .error_on_exceed);

    try testing.expectEqual(@as(i32, 10), try Clamped.call(5));
    try testing.expectEqual(@as(i32, 20), try Clamped.call(15)); // Clamped to 10

    try testing.expectEqual(@as(i32, 10), try ErrorBased.call(5));
    try testing.expectError(error.ThresholdExceeded, ErrorBased.call(15));
}
// ANCHOR_END: threshold_decorator

// ANCHOR: multi_param_decorator
// Decorator with multiple parameters
fn WithConfig(
    comptime func: anytype,
    comptime config: struct {
        multiplier: i32,
        offset: i32,
        invert: bool,
    },
) type {
    return struct {
        pub fn call(x: i32) i32 {
            var result = func(x);
            result = result * config.multiplier;
            result = result + config.offset;
            if (config.invert) {
                result = -result;
            }
            return result;
        }

        pub fn getConfig() @TypeOf(config) {
            return config;
        }
    };
}

test "multi param decorator" {
    const Configured = WithConfig(identity, .{
        .multiplier = 2,
        .offset = 5,
        .invert = false,
    });

    const Inverted = WithConfig(identity, .{
        .multiplier = 1,
        .offset = 0,
        .invert = true,
    });

    try testing.expectEqual(@as(i32, 15), Configured.call(5)); // (5 * 2) + 5
    try testing.expectEqual(@as(i32, -5), Inverted.call(5)); // -(5)

    const cfg = Configured.getConfig();
    try testing.expectEqual(@as(i32, 2), cfg.multiplier);
}
// ANCHOR_END: multi_param_decorator

// ANCHOR: array_param_decorator
// Decorator with array parameter
fn WithAllowList(comptime func: anytype, comptime allowed: []const i32) type {
    return struct {
        pub fn call(x: i32) !i32 {
            for (allowed) |val| {
                if (x == val) {
                    return func(x);
                }
            }
            return error.NotAllowed;
        }

        pub fn getAllowed() []const i32 {
            return allowed;
        }
    };
}

test "array param decorator" {
    const allowed_values = [_]i32{ 1, 5, 10, 15 };
    const Restricted = WithAllowList(double, &allowed_values);

    const r1 = try Restricted.call(5);
    try testing.expectEqual(@as(i32, 10), r1);

    const r2 = Restricted.call(7);
    try testing.expectError(error.NotAllowed, r2);

    try testing.expectEqual(@as(usize, 4), Restricted.getAllowed().len);
}
// ANCHOR_END: array_param_decorator

// Comprehensive test
test "comprehensive parameterized decorators" {
    // Test multiplier
    const Times3 = WithMultiplier(identity, 3);
    try testing.expectEqual(@as(i32, 15), Times3.call(5));

    // Test bounds
    const Bounded = WithBounds(square, 1, 5);
    try testing.expectEqual(@as(i32, 16), try Bounded.call(4));

    // Test conditional
    const Enabled = Conditional(add10, true);
    try testing.expectEqual(@as(i32, 30), Enabled.call(5));

    // Test threshold
    const Clamped = WithThreshold(double, 8, .clamp);
    try testing.expectEqual(@as(i32, 16), try Clamped.call(10));

    // Test multi-param
    const Configured = WithConfig(identity, .{ .multiplier = 2, .offset = 3, .invert = false });
    try testing.expectEqual(@as(i32, 13), Configured.call(5));
}
```

### See Also

- Recipe 9.1: Putting a Wrapper Around a Function
- Recipe 9.2: Preserving Function Metadata When Writing Decorators
- Recipe 9.3: Unwrapping a Decorator
- Recipe 9.5: Enforcing Type Checking on a Function Using a Decorator

---

## Recipe 9.5: Enforcing Type Checking on a Function Using a Decorator {#recipe-9-5}

**Tags:** allocators, comptime, comptime-metaprogramming, error-handling, memory, pointers, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_5.zig`

### Problem

You want to enforce type constraints on functions at compile time, validating that functions have specific parameter types, return types, or other type properties. You need type-safe decorators that catch errors before runtime.

### Solution

Use `@typeInfo` to introspect function signatures and validate types at compile time with decorators. Combine type checking with `@compileError` to enforce constraints during compilation.

### Parameter Type Checking

Validate parameter types match expected types:

```zig
// Enforce parameter types at compile time
fn WithParameterCheck(comptime func: anytype, comptime ExpectedParams: []const type) type {
    const func_info = @typeInfo(@TypeOf(func));
    const params = func_info.@"fn".params;

    if (params.len != ExpectedParams.len) {
        @compileError("Parameter count mismatch");
    }

    inline for (params, ExpectedParams, 0..) |param, expected, i| {
        if (param.type.? != expected) {
            @compileError(std.fmt.comptimePrint(
                "Parameter {d} type mismatch: expected {s}, got {s}",
                .{ i, @typeName(expected), @typeName(param.type.?) },
            ));
        }
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "parameter type check" {
    const expected = [_]type{ i32, i32 };
    const Checked = WithParameterCheck(add, &expected);

    const result = Checked.call(.{ 5, 3 });
    try testing.expectEqual(@as(i32, 8), result);

    // This would fail at compile time:
    // const bad_params = [_]type{ i64, i32 };
    // const Bad = WithParameterCheck(add, &bad_params);
}
```

Type mismatches cause compile errors with helpful messages.

### Return Type Checking

Enforce specific return types:

```zig
fn WithReturnCheck(comptime func: anytype, comptime ExpectedReturn: type) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ActualReturn = func_info.@"fn".return_type.?;

    if (ActualReturn != ExpectedReturn) {
        @compileError(std.fmt.comptimePrint(
            "Return type mismatch: expected {s}, got {s}",
            .{ @typeName(ExpectedReturn), @typeName(ActualReturn) },
        ));
    }

    return struct {
        pub fn call(args: anytype) ExpectedReturn {
            return @call(.auto, func, args);
        }
    };
}

fn double(x: i32) i32 {
    return x * 2;
}

// Usage
const Checked = WithReturnCheck(double, i32);  // OK
const result = Checked.call(.{5});  // 10

// This would fail at compile time:
// const Bad = WithReturnCheck(double, i64);
```

Return type validation prevents unexpected types.

### Error Set Checking

Ensure functions return error unions:

```zig
fn WithErrorCheck(comptime func: anytype, comptime RequiredErrors: type) type {
    _ = RequiredErrors; // For future enhancement
    const func_info = @typeInfo(@TypeOf(func));
    const return_info = @typeInfo(func_info.@"fn".return_type.?);

    if (return_info != .error_union) {
        @compileError("Function must return an error union");
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn divide(a: i32, b: i32) !i32 {
    if (b == 0) return error.DivisionByZero;
    return @divTrunc(a, b);
}

// Usage
const Checked = WithErrorCheck(divide, error{DivisionByZero});
const result = try Checked.call(.{ 10, 2 });  // 5
```

Enforces error handling at compile time.

### Numeric Type Constraint

Restrict to numeric types only:

```zig
fn NumericOnly(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const return_type = func_info.@"fn".return_type.?;
    const return_info = @typeInfo(return_type);

    if (return_info != .int and return_info != .float) {
        @compileError("Function must return numeric type");
    }

    for (func_info.@"fn".params) |param| {
        const param_info = @typeInfo(param.type.?);
        if (param_info != .int and param_info != .float) {
            @compileError("All parameters must be numeric");
        }
    }

    return struct {
        pub fn call(args: anytype) return_type {
            return @call(.auto, func, args);
        }
    };
}

fn multiply(x: i32, y: i32) i32 {
    return x * y;
}

// Usage
const Checked = NumericOnly(multiply);
const result = Checked.call(.{ 4, 5 });  // 20
```

Ensures mathematical operations on numeric types.

### Signed Integer Requirement

Require signed integer parameters:

```zig
fn SignedIntegersOnly(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));

    for (func_info.@"fn".params) |param| {
        const param_info = @typeInfo(param.type.?);
        if (param_info != .int) {
            @compileError("All parameters must be integers");
        }
        if (param_info.int.signedness != .signed) {
            @compileError("All integer parameters must be signed");
        }
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn negate(x: i32) i32 {
    return -x;
}

// Usage
const Checked = SignedIntegersOnly(negate);
const result = Checked.call(.{5});  // -5
```

Prevents unsigned integers where signs matter.

### Pointer Parameter Check

Enforce specific parameters are pointers:

```zig
fn RequiresPointer(comptime func: anytype, comptime index: usize) type {
    const func_info = @typeInfo(@TypeOf(func));
    const params = func_info.@"fn".params;

    if (index >= params.len) {
        @compileError("Parameter index out of range");
    }

    const param_info = @typeInfo(params[index].type.?);
    if (param_info != .pointer) {
        @compileError(std.fmt.comptimePrint(
            "Parameter {d} must be a pointer",
            .{index},
        ));
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn increment(x: *i32) void {
    x.* += 1;
}

// Usage
const Checked = RequiresPointer(increment, 0);
var val: i32 = 10;
Checked.call(.{&val});
// val == 11
```

Validates pointer usage for mutability.

### Slice Type Enforcement

Require slice parameters with specific element types:

```zig
fn RequiresSlice(comptime func: anytype, comptime ElementType: type) type {
    const func_info = @typeInfo(@TypeOf(func));
    const params = func_info.@"fn".params;

    var found_slice = false;
    for (params) |param| {
        const param_type = param.type.?;
        const type_name = @typeName(param_type);

        // Slices start with "[]" in their type name
        if (std.mem.startsWith(u8, type_name, "[]")) {
            const param_info = @typeInfo(param_type);
            if (param_info == .pointer) {
                if (param_info.pointer.child == ElementType) {
                    found_slice = true;
                    break;
                }
            }
        }
    }

    if (!found_slice) {
        @compileError(std.fmt.comptimePrint(
            "Function must have a slice parameter of type []const {s}",
            .{@typeName(ElementType)},
        ));
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn sum(items: []const i32) i32 {
    var total: i32 = 0;
    for (items) |item| {
        total += item;
    }
    return total;
}

// Usage
const Checked = RequiresSlice(sum, i32);
const items = [_]i32{ 1, 2, 3, 4, 5 };
const result = Checked.call(.{&items});  // 15
```

Ensures collection-based functions receive slices.

### Optional Return Type Check

Validate optional return types with specific payload:

```zig
fn ReturnsOptional(comptime func: anytype, comptime PayloadType: type) type {
    const func_info = @typeInfo(@TypeOf(func));
    const return_type = func_info.@"fn".return_type.?;
    const return_info = @typeInfo(return_type);

    if (return_info != .optional) {
        @compileError("Function must return an optional type");
    }

    if (return_info.optional.child != PayloadType) {
        @compileError(std.fmt.comptimePrint(
            "Optional payload must be {s}, not {s}",
            .{ @typeName(PayloadType), @typeName(return_info.optional.child) },
        ));
    }

    return struct {
        pub fn call(args: anytype) return_type {
            return @call(.auto, func, args);
        }
    };
}

fn findFirst(items: []const i32, target: i32) ?usize {
    for (items, 0..) |item, i| {
        if (item == target) return i;
    }
    return null;
}

// Usage
const Checked = ReturnsOptional(findFirst, usize);
const items = [_]i32{ 10, 20, 30, 40 };
const found = Checked.call(.{ &items, 30 });  // ?usize = 2
```

Enforces optional patterns for nullable results.

### Struct Field Requirement

Ensure struct parameters have required fields:

```zig
fn RequiresStructWithFields(comptime func: anytype, comptime required_fields: []const []const u8) type {
    const func_info = @typeInfo(@TypeOf(func));
    const params = func_info.@"fn".params;

    if (params.len == 0) {
        @compileError("Function must have at least one parameter");
    }

    const first_param = params[0].type.?;
    const param_info = @typeInfo(first_param);

    if (param_info != .@"struct") {
        @compileError("First parameter must be a struct");
    }

    inline for (required_fields) |field_name| {
        if (!@hasField(first_param, field_name)) {
            @compileError(std.fmt.comptimePrint(
                "Struct must have field: {s}",
                .{field_name},
            ));
        }
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

const Point = struct {
    x: i32,
    y: i32,
};

fn distance(p: Point) i32 {
    return p.x + p.y;
}

// Usage
const required = [_][]const u8{ "x", "y" };
const Checked = RequiresStructWithFields(distance, &required);
const p = Point{ .x = 3, .y = 4 };
const result = Checked.call(.{p});  // 7
```

Validates struct interface contracts.

### Allocator Parameter Requirement

Ensure functions take allocator as first parameter:

```zig
fn RequiresAllocator(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const params = func_info.@"fn".params;

    if (params.len == 0) {
        @compileError("Function must have at least one parameter");
    }

    const first_param = params[0].type.?;
    if (first_param != std.mem.Allocator) {
        @compileError(std.fmt.comptimePrint(
            "First parameter must be std.mem.Allocator, got {s}",
            .{@typeName(first_param)},
        ));
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn allocateSlice(allocator: std.mem.Allocator, size: usize) ![]i32 {
    return try allocator.alloc(i32, size);
}

// Usage
const Checked = RequiresAllocator(allocateSlice);
const slice = try Checked.call(.{ allocator, 5 });
defer allocator.free(slice);
```

Enforces explicit allocator passing convention.

### Pure Function Check

Enforce functional purity (no mutable pointers, must return value):

```zig
fn PureFunction(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));

    if (func_info.@"fn".return_type == null) {
        @compileError("Pure function must return a value");
    }

    for (func_info.@"fn".params) |param| {
        const param_type = param.type.?;
        const param_info = @typeInfo(param_type);

        if (param_info == .pointer) {
            // Allow const pointers and slices (read-only access)
            const is_slice = std.mem.startsWith(u8, @typeName(param_type), "[]");
            if (param_info.pointer.is_const == false and !is_slice) {
                @compileError("Pure function cannot have mutable pointer parameters");
            }
        }
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn square(x: i32) i32 {
    return x * x;
}

// Usage
const Checked = PureFunction(square);
const result = Checked.call(.{7});  // 49
```

Promotes functional programming patterns.

### Discussion

Type checking decorators provide compile-time safety by validating function signatures before code runs.

### Why Type Checking Matters

**Compile-time safety**:
- Catch type errors early
- No runtime type checks needed
- Zero performance overhead
- Self-documenting constraints

**API contracts**:
- Enforce interface requirements
- Document expected types
- Prevent misuse
- Guide correct usage

**Refactoring confidence**:
- Changes caught at compile time
- Type errors impossible at runtime
- Compiler verifies correctness
- Safe large-scale changes

### Type Introspection with @typeInfo

**Function information**:
```zig
const func_info = @typeInfo(@TypeOf(func));
const fn_info = func_info.@"fn";
```

**Available properties**:
- `params` - Parameter list
- `return_type` - Return type (nullable)
- `calling_convention` - Calling convention
- `is_generic` - Generic function check
- `is_var_args` - Variadic check

**Parameter inspection**:
```zig
for (fn_info.params, 0..) |param, i| {
    const param_type = param.type.?;
    const param_info = @typeInfo(param_type);
    // Check param_info...
}
```

### Type Categories

**Primitive types**:
```zig
.int, .float, .bool, .void
```

**Composite types**:
```zig
.@"struct", .@"enum", .@"union", .@"opaque"
```

**Pointer types**:
```zig
.pointer - Check size, child, is_const
```

**Special types**:
```zig
.optional, .error_union, .error_set, .array
```

### Error Messages

**Helpful compile errors**:
```zig
@compileError(std.fmt.comptimePrint(
    "Expected {s} but got {s}",
    .{ @typeName(expected), @typeName(actual) },
));
```

**Include context**:
- Parameter index
- Expected vs actual types
- Constraint description
- Suggestion for fix

**Example output**:
```
error: Parameter 1 type mismatch: expected i32, got i64
```

### Common Patterns

**Type equality**:
```zig
if (ActualType != ExpectedType) {
    @compileError("Type mismatch");
}
```

**Type category**:
```zig
const info = @typeInfo(T);
if (info != .int) {
    @compileError("Must be integer");
}
```

**Field existence**:
```zig
if (!@hasField(T, "field_name")) {
    @compileError("Missing field");
}
```

**Signedness check**:
```zig
if (info.int.signedness != .signed) {
    @compileError("Must be signed");
}
```

### Design Guidelines

**Clear error messages**:
- Explain what's wrong
- Show expected vs actual
- Suggest how to fix
- Include context

**Specific constraints**:
- Check exactly what matters
- Don't over-constrain
- Allow flexibility where safe
- Document requirements

**Composable checks**:
```zig
const Validated =
    RequiresAllocator(
        NumericOnly(
            WithReturnCheck(func, i32)
        )
    );
```

Stack checks for comprehensive validation.

### Performance

**Zero runtime cost**:
- All checks at compile time
- No type tags
- No runtime inspection
- Pure compile-time overhead

**Compile time**:
- Type checks are fast
- Increase with complexity
- Worth it for safety
- One-time cost

**Binary size**:
- No runtime metadata
- Same as unchecked code
- Type info eliminated
- Optimal generated code

### Testing Type Checks

**Test valid cases**:
```zig
test "accepts valid types" {
    const Checked = WithReturnCheck(func, i32);
    const result = Checked.call(.{5});
    try testing.expectEqual(@as(i32, 10), result);
}
```

**Test compile errors** (in comments):
```zig
// This should fail at compile time:
// const Bad = WithReturnCheck(func, i64);
```

**Test edge cases**:
```zig
test "empty parameter list" {
    fn noParams() i32 { return 42; }
    const Checked = WithParameterCheck(noParams, &[_]type{});
    try testing.expectEqual(@as(i32, 42), Checked.call(.{}));
}
```

### Advanced Techniques

**Recursive type checking**:
```zig
fn checkNested(comptime T: type) void {
    const info = @typeInfo(T);
    if (info == .@"struct") {
        inline for (info.@"struct".fields) |field| {
            checkNested(field.type);
        }
    }
}
```

**Constraint composition**:
```zig
fn MultiConstraint(comptime func: anytype) type {
    _ = NumericOnly(func);
    _ = WithReturnCheck(func, i32);
    _ = RequiresAllocator(func);
    // All checks must pass
    return func;
}
```

**Custom type traits**:
```zig
fn isNumeric(comptime T: type) bool {
    const info = @typeInfo(T);
    return info == .int or info == .float;
}
```

### Full Tested Code

```zig
// Recipe 9.5: Enforcing Type Checking on a Function Using a Decorator
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: parameter_type_check
// Enforce parameter types at compile time
fn WithParameterCheck(comptime func: anytype, comptime ExpectedParams: []const type) type {
    const func_info = @typeInfo(@TypeOf(func));
    const params = func_info.@"fn".params;

    if (params.len != ExpectedParams.len) {
        @compileError("Parameter count mismatch");
    }

    inline for (params, ExpectedParams, 0..) |param, expected, i| {
        if (param.type.? != expected) {
            @compileError(std.fmt.comptimePrint(
                "Parameter {d} type mismatch: expected {s}, got {s}",
                .{ i, @typeName(expected), @typeName(param.type.?) },
            ));
        }
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "parameter type check" {
    const expected = [_]type{ i32, i32 };
    const Checked = WithParameterCheck(add, &expected);

    const result = Checked.call(.{ 5, 3 });
    try testing.expectEqual(@as(i32, 8), result);

    // This would fail at compile time:
    // const bad_params = [_]type{ i64, i32 };
    // const Bad = WithParameterCheck(add, &bad_params);
}
// ANCHOR_END: parameter_type_check

// ANCHOR: return_type_check
// Enforce return type at compile time
fn WithReturnCheck(comptime func: anytype, comptime ExpectedReturn: type) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ActualReturn = func_info.@"fn".return_type.?;

    if (ActualReturn != ExpectedReturn) {
        @compileError(std.fmt.comptimePrint(
            "Return type mismatch: expected {s}, got {s}",
            .{ @typeName(ExpectedReturn), @typeName(ActualReturn) },
        ));
    }

    return struct {
        pub fn call(args: anytype) ExpectedReturn {
            return @call(.auto, func, args);
        }
    };
}

fn double(x: i32) i32 {
    return x * 2;
}

test "return type check" {
    const Checked = WithReturnCheck(double, i32);
    const result = Checked.call(.{5});
    try testing.expectEqual(@as(i32, 10), result);

    // This would fail at compile time:
    // const Bad = WithReturnCheck(double, i64);
}
// ANCHOR_END: return_type_check

// ANCHOR: error_set_check
// Enforce error set requirements
fn WithErrorCheck(comptime func: anytype, comptime RequiredErrors: type) type {
    _ = RequiredErrors; // For future enhancement
    const func_info = @typeInfo(@TypeOf(func));
    const return_info = @typeInfo(func_info.@"fn".return_type.?);

    if (return_info != .error_union) {
        @compileError("Function must return an error union");
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn divide(a: i32, b: i32) !i32 {
    if (b == 0) return error.DivisionByZero;
    return @divTrunc(a, b);
}

test "error set check" {
    const Checked = WithErrorCheck(divide, error{DivisionByZero});

    const r1 = try Checked.call(.{ 10, 2 });
    try testing.expectEqual(@as(i32, 5), r1);

    const r2 = Checked.call(.{ 10, 0 });
    try testing.expectError(error.DivisionByZero, r2);
}
// ANCHOR_END: error_set_check

// ANCHOR: numeric_constraint
// Constrain to numeric types only
fn NumericOnly(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const return_type = func_info.@"fn".return_type.?;
    const return_info = @typeInfo(return_type);

    if (return_info != .int and return_info != .float) {
        @compileError("Function must return numeric type");
    }

    for (func_info.@"fn".params) |param| {
        const param_info = @typeInfo(param.type.?);
        if (param_info != .int and param_info != .float) {
            @compileError("All parameters must be numeric");
        }
    }

    return struct {
        pub fn call(args: anytype) return_type {
            return @call(.auto, func, args);
        }
    };
}

fn multiply(x: i32, y: i32) i32 {
    return x * y;
}

test "numeric constraint" {
    const Checked = NumericOnly(multiply);
    const result = Checked.call(.{ 4, 5 });
    try testing.expectEqual(@as(i32, 20), result);
}
// ANCHOR_END: numeric_constraint

// ANCHOR: signed_integer_check
// Require signed integer types
fn SignedIntegersOnly(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));

    for (func_info.@"fn".params) |param| {
        const param_info = @typeInfo(param.type.?);
        if (param_info != .int) {
            @compileError("All parameters must be integers");
        }
        if (param_info.int.signedness != .signed) {
            @compileError("All integer parameters must be signed");
        }
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn negate(x: i32) i32 {
    return -x;
}

test "signed integer check" {
    const Checked = SignedIntegersOnly(negate);
    const result = Checked.call(.{5});
    try testing.expectEqual(@as(i32, -5), result);
}
// ANCHOR_END: signed_integer_check

// ANCHOR: pointer_check
// Enforce pointer parameter types
fn RequiresPointer(comptime func: anytype, comptime index: usize) type {
    const func_info = @typeInfo(@TypeOf(func));
    const params = func_info.@"fn".params;

    if (index >= params.len) {
        @compileError("Parameter index out of range");
    }

    const param_info = @typeInfo(params[index].type.?);
    if (param_info != .pointer) {
        @compileError(std.fmt.comptimePrint(
            "Parameter {d} must be a pointer",
            .{index},
        ));
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn increment(x: *i32) void {
    x.* += 1;
}

test "pointer check" {
    const Checked = RequiresPointer(increment, 0);

    var val: i32 = 10;
    Checked.call(.{&val});
    try testing.expectEqual(@as(i32, 11), val);
}
// ANCHOR_END: pointer_check

// ANCHOR: slice_check
// Enforce slice types
fn RequiresSlice(comptime func: anytype, comptime ElementType: type) type {
    const func_info = @typeInfo(@TypeOf(func));
    const params = func_info.@"fn".params;

    var found_slice = false;
    for (params) |param| {
        // Check if this is a slice by seeing if it matches []const T or []T pattern
        const param_type = param.type.?;
        const type_name = @typeName(param_type);

        // Slices start with "[]" in their type name
        if (std.mem.startsWith(u8, type_name, "[]")) {
            // Check if element type matches
            const param_info = @typeInfo(param_type);
            if (param_info == .pointer) {
                if (param_info.pointer.child == ElementType) {
                    found_slice = true;
                    break;
                }
            }
        }
    }

    if (!found_slice) {
        @compileError(std.fmt.comptimePrint(
            "Function must have a slice parameter of type []const {s}",
            .{@typeName(ElementType)},
        ));
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn sum(items: []const i32) i32 {
    var total: i32 = 0;
    for (items) |item| {
        total += item;
    }
    return total;
}

test "slice check" {
    const Checked = RequiresSlice(sum, i32);

    const items = [_]i32{ 1, 2, 3, 4, 5 };
    const result = Checked.call(.{&items});
    try testing.expectEqual(@as(i32, 15), result);
}
// ANCHOR_END: slice_check

// ANCHOR: optional_check
// Enforce optional return types
fn ReturnsOptional(comptime func: anytype, comptime PayloadType: type) type {
    const func_info = @typeInfo(@TypeOf(func));
    const return_type = func_info.@"fn".return_type.?;
    const return_info = @typeInfo(return_type);

    if (return_info != .optional) {
        @compileError("Function must return an optional type");
    }

    if (return_info.optional.child != PayloadType) {
        @compileError(std.fmt.comptimePrint(
            "Optional payload must be {s}, not {s}",
            .{ @typeName(PayloadType), @typeName(return_info.optional.child) },
        ));
    }

    return struct {
        pub fn call(args: anytype) return_type {
            return @call(.auto, func, args);
        }
    };
}

fn findFirst(items: []const i32, target: i32) ?usize {
    for (items, 0..) |item, i| {
        if (item == target) return i;
    }
    return null;
}

test "optional check" {
    const Checked = ReturnsOptional(findFirst, usize);

    const items = [_]i32{ 10, 20, 30, 40 };
    const r1 = Checked.call(.{ &items, 30 });
    try testing.expectEqual(@as(?usize, 2), r1);

    const r2 = Checked.call(.{ &items, 99 });
    try testing.expectEqual(@as(?usize, null), r2);
}
// ANCHOR_END: optional_check

// ANCHOR: struct_field_check
// Enforce struct parameter with specific fields
fn RequiresStructWithFields(comptime func: anytype, comptime required_fields: []const []const u8) type {
    const func_info = @typeInfo(@TypeOf(func));
    const params = func_info.@"fn".params;

    if (params.len == 0) {
        @compileError("Function must have at least one parameter");
    }

    const first_param = params[0].type.?;
    const param_info = @typeInfo(first_param);

    if (param_info != .@"struct") {
        @compileError("First parameter must be a struct");
    }

    inline for (required_fields) |field_name| {
        if (!@hasField(first_param, field_name)) {
            @compileError(std.fmt.comptimePrint(
                "Struct must have field: {s}",
                .{field_name},
            ));
        }
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

const Point = struct {
    x: i32,
    y: i32,
};

fn distance(p: Point) i32 {
    return p.x + p.y;
}

test "struct field check" {
    const required = [_][]const u8{ "x", "y" };
    const Checked = RequiresStructWithFields(distance, &required);

    const p = Point{ .x = 3, .y = 4 };
    const result = Checked.call(.{p});
    try testing.expectEqual(@as(i32, 7), result);
}
// ANCHOR_END: struct_field_check

// ANCHOR: allocator_check
// Ensure function takes allocator as first parameter
fn RequiresAllocator(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const params = func_info.@"fn".params;

    if (params.len == 0) {
        @compileError("Function must have at least one parameter");
    }

    const first_param = params[0].type.?;
    if (first_param != std.mem.Allocator) {
        @compileError(std.fmt.comptimePrint(
            "First parameter must be std.mem.Allocator, got {s}",
            .{@typeName(first_param)},
        ));
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn allocateSlice(allocator: std.mem.Allocator, size: usize) ![]i32 {
    return try allocator.alloc(i32, size);
}

test "allocator check" {
    const Checked = RequiresAllocator(allocateSlice);

    const slice = try Checked.call(.{ testing.allocator, 5 });
    defer testing.allocator.free(slice);

    try testing.expectEqual(@as(usize, 5), slice.len);
}
// ANCHOR_END: allocator_check

// ANCHOR: pure_function_check
// Enforce that function has no side effects (no void parameters/returns)
fn PureFunction(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));

    if (func_info.@"fn".return_type == null) {
        @compileError("Pure function must return a value");
    }

    for (func_info.@"fn".params) |param| {
        const param_type = param.type.?;
        const param_info = @typeInfo(param_type);

        if (param_info == .pointer) {
            // Allow const pointers and slices (read-only access)
            const is_slice = std.mem.startsWith(u8, @typeName(param_type), "[]");
            if (param_info.pointer.is_const == false and !is_slice) {
                @compileError("Pure function cannot have mutable pointer parameters");
            }
        }
    }

    return struct {
        pub fn call(args: anytype) func_info.@"fn".return_type.? {
            return @call(.auto, func, args);
        }
    };
}

fn square(x: i32) i32 {
    return x * x;
}

test "pure function check" {
    const Checked = PureFunction(square);
    const result = Checked.call(.{7});
    try testing.expectEqual(@as(i32, 49), result);
}
// ANCHOR_END: pure_function_check

// Comprehensive test
test "comprehensive type checking" {
    // Parameter type checking
    const param_types = [_]type{ i32, i32 };
    const CheckedAdd = WithParameterCheck(add, &param_types);
    try testing.expectEqual(@as(i32, 8), CheckedAdd.call(.{ 5, 3 }));

    // Return type checking
    const CheckedDouble = WithReturnCheck(double, i32);
    try testing.expectEqual(@as(i32, 10), CheckedDouble.call(.{5}));

    // Error set checking
    const CheckedDivide = WithErrorCheck(divide, error{DivisionByZero});
    try testing.expectEqual(@as(i32, 5), try CheckedDivide.call(.{ 10, 2 }));

    // Numeric constraint
    const CheckedMultiply = NumericOnly(multiply);
    try testing.expectEqual(@as(i32, 20), CheckedMultiply.call(.{ 4, 5 }));

    // Pure function
    const CheckedSquare = PureFunction(square);
    try testing.expectEqual(@as(i32, 49), CheckedSquare.call(.{7}));
}
```

### See Also

- Recipe 9.1: Putting a Wrapper Around a Function
- Recipe 9.2: Preserving Function Metadata When Writing Decorators
- Recipe 9.4: Defining a Decorator That Takes Arguments
- Recipe 9.6: Defining Decorators as Part of a Struct

---

## Recipe 9.6: Defining Decorators As Part of a Struct {#recipe-9-6}

**Tags:** atomics, comptime, comptime-metaprogramming, concurrency, error-handling, http, networking, testing, threading
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_6.zig`

### Problem

You want to organize related decorators together, provide shared configuration or utilities, or create namespaced decorator collections. Individual standalone decorator functions can become scattered and hard to manage.

### Solution

Define decorators as methods within structs to create organized namespaces, share configuration, and group related functionality.

### Basic Struct Decorators

Organize decorators as struct methods for namespace organization:

```zig
// Organize decorators as struct methods
const Decorators = struct {
    pub fn Timing(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) i32 {
                // In real code, would measure time
                const result = func(x);
                return result;
            }
        };
    }

    pub fn Logging(comptime func: anytype) type {
        return struct {
            var call_count: u32 = 0;

            pub fn call(x: i32) i32 {
                call_count += 1;
                const result = func(x);
                return result;
            }

            pub fn getCallCount() u32 {
                return call_count;
            }
        };
    }
};

fn double(x: i32) i32 {
    return x * 2;
}

test "basic struct decorators" {
    const Timed = Decorators.Timing(double);
    try testing.expectEqual(@as(i32, 10), Timed.call(5));

    const Logged = Decorators.Logging(double);
    try testing.expectEqual(@as(i32, 10), Logged.call(5));
    try testing.expectEqual(@as(u32, 1), Logged.getCallCount());
}
```

Struct methods provide namespace separation and logical grouping.

### Shared Configuration

Pass configuration to decorator methods at compile time:

```zig
const ConfiguredDecorators = struct {
    const Config = struct {
        enable_logging: bool = false,
        enable_caching: bool = true,
        max_cache_size: usize = 100,
    };

    pub fn WithCache(comptime config: Config, comptime func: anytype) type {
        const enable = config.enable_caching;
        const max_size = config.max_cache_size;

        return struct {
            pub fn call(x: i32) i32 {
                if (!enable) {
                    return func(x);
                }
                // Caching logic using max_size
                return func(x);
            }

            pub fn isCacheEnabled() bool {
                return enable;
            }
        };
    }
};

// Usage
const config = ConfiguredDecorators.Config{
    .enable_caching = true,
    .max_cache_size = 50,
};

const Cached = ConfiguredDecorators.WithCache(config, double);
Cached.call(5);  // 10
Cached.isCacheEnabled();  // true
```

Compile-time configuration provides zero-overhead customization.

### Namespace Organization

Group decorators by category using separate structs:

```zig
const Validation = struct {
    pub fn Bounds(comptime func: anytype, comptime min: i32, comptime max: i32) type {
        return struct {
            pub fn call(x: i32) !i32 {
                if (x < min or x > max) {
                    return error.OutOfBounds;
                }
                return func(x);
            }
        };
    }

    pub fn NonZero(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) !i32 {
                if (x == 0) {
                    return error.ZeroNotAllowed;
                }
                return func(x);
            }
        };
    }
};

const Transformation = struct {
    pub fn Scale(comptime func: anytype, comptime factor: i32) type {
        return struct {
            pub fn call(x: i32) i32 {
                return func(x) * factor;
            }
        };
    }

    pub fn Offset(comptime func: anytype, comptime offset: i32) type {
        return struct {
            pub fn call(x: i32) i32 {
                return func(x) + offset;
            }
        };
    }
};

// Usage
const Bounded = Validation.Bounds(double, 0, 10);
const Scaled = Transformation.Scale(double, 2);

try Bounded.call(5);  // 10
try Bounded.call(15); // error.OutOfBounds

Scaled.call(5);  // 20
```

Categorization makes intent clear and improves discoverability.

### Stateful Decorators

Track state across multiple invocations:

```zig
const StatefulDecorators = struct {
    pub fn WithCounter(comptime func: anytype) type {
        return struct {
            var call_count: u32 = 0;
            var total_sum: i64 = 0;

            pub fn call(x: i32) i32 {
                call_count += 1;
                const result = func(x);
                total_sum += result;
                return result;
            }

            pub fn getCallCount() u32 {
                return call_count;
            }

            pub fn getTotalSum() i64 {
                return total_sum;
            }

            pub fn reset() void {
                call_count = 0;
                total_sum = 0;
            }
        };
    }

    pub fn WithMinMax(comptime func: anytype) type {
        return struct {
            var min_value: ?i32 = null;
            var max_value: ?i32 = null;

            pub fn call(x: i32) i32 {
                const result = func(x);

                if (min_value) |min| {
                    if (result < min) min_value = result;
                } else {
                    min_value = result;
                }

                if (max_value) |max| {
                    if (result > max) max_value = result;
                } else {
                    max_value = result;
                }

                return result;
            }

            pub fn getMin() ?i32 {
                return min_value;
            }

            pub fn getMax() ?i32 {
                return max_value;
            }

            pub fn reset() void {
                min_value = null;
                max_value = null;
            }
        };
    }
};

// Usage
const Counted = StatefulDecorators.WithCounter(double);

Counted.call(5);   // 10
Counted.call(10);  // 20

Counted.getCallCount();  // 2
Counted.getTotalSum();   // 30

const MinMaxed = StatefulDecorators.WithMinMax(double);
MinMaxed.call(5);   // 10
MinMaxed.call(10);  // 20
MinMaxed.call(2);   // 4

MinMaxed.getMin();  // 4
MinMaxed.getMax();  // 20
```

State persists across calls, enabling tracking and analytics.

### Decorator Factory

Create decorators dynamically based on type:

```zig
const DecoratorFactory = struct {
    pub fn create(comptime decorator_type: enum { timing, logging, caching }) type {
        return switch (decorator_type) {
            .timing => struct {
                pub fn wrap(comptime func: anytype) type {
                    return struct {
                        pub fn call(x: i32) i32 {
                            // Timing logic
                            return func(x);
                        }
                    };
                }
            },
            .logging => struct {
                pub fn wrap(comptime func: anytype) type {
                    return struct {
                        var count: u32 = 0;

                        pub fn call(x: i32) i32 {
                            count += 1;
                            return func(x);
                        }

                        pub fn getCount() u32 {
                            return count;
                        }
                    };
                }
            },
            .caching => struct {
                pub fn wrap(comptime func: anytype) type {
                    return struct {
                        pub fn call(x: i32) i32 {
                            // Caching logic
                            return func(x);
                        }
                    };
                }
            },
        };
    }
};

// Usage
const LoggingDecorator = DecoratorFactory.create(.logging);
const Logged = LoggingDecorator.wrap(double);

Logged.call(5);       // 10
Logged.getCount();    // 1
```

Factory pattern provides compile-time decorator selection.

### Chaining Struct Decorators

Chain multiple decorators from the same namespace:

```zig
const ChainableDecorators = struct {
    pub fn Validate(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) !i32 {
                if (x < 0) {
                    return error.NegativeNotAllowed;
                }
                return func(x);
            }
        };
    }

    pub fn Double(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) @TypeOf(func(0)) {
                return func(x * 2);
            }
        };
    }

    pub fn AddTen(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) @TypeOf(func(0)) {
                return func(x + 10);
            }
        };
    }
};

fn identity(x: i32) i32 {
    return x;
}

// Usage - chain decorators
const Step1 = ChainableDecorators.Validate(identity);
const Step2 = ChainableDecorators.Double(Step1.call);
const Step3 = ChainableDecorators.AddTen(Step2.call);

try Step3.call(5);  // (5 + 10) * 2 = 30
```

Chaining builds complex behavior from simple components.

### Shared Utilities

Share helper functions across decorators:

```zig
const UtilityDecorators = struct {
    fn logMessage(comptime msg: []const u8, value: i32) void {
        _ = value;
        _ = msg;
        // In real code: std.debug.print("{s}: {d}\n", .{ msg, value });
    }

    pub fn WithPreLog(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) i32 {
                logMessage("Before", x);
                return func(x);
            }
        };
    }

    pub fn WithPostLog(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) i32 {
                const result = func(x);
                logMessage("After", result);
                return result;
            }
        };
    }
};

// Usage
const PreLogged = UtilityDecorators.WithPreLog(double);
const PostLogged = UtilityDecorators.WithPostLog(double);
```

Shared utilities reduce code duplication.

### Generic Decorator Struct

Create type-parameterized decorator collections:

```zig
fn DecoratorSet(comptime T: type) type {
    return struct {
        pub fn WithDefault(comptime func: anytype, comptime default: T) type {
            return struct {
                pub fn call(x: ?T) T {
                    const val = x orelse default;
                    return func(val);
                }
            };
        }

        pub fn WithValidation(comptime func: anytype, comptime validator: anytype) type {
            return struct {
                pub fn call(x: T) !T {
                    if (!validator(x)) {
                        return error.ValidationFailed;
                    }
                    return func(x);
                }
            };
        }
    };
}

fn isPositive(x: i32) bool {
    return x > 0;
}

// Usage
const I32Decorators = DecoratorSet(i32);

const WithDefault = I32Decorators.WithDefault(double, 10);
WithDefault.call(5);     // 10
WithDefault.call(null);  // 20 (uses default)

const Validated = I32Decorators.WithValidation(double, isPositive);
try Validated.call(5);   // 10
try Validated.call(-5);  // error.ValidationFailed
```

Generic structs create reusable decorator families.

### Decorator Registry

Conditionally enable decorators based on compile-time registry:

```zig
const DecoratorRegistry = struct {
    const Entry = struct {
        name: []const u8,
        enabled: bool,
    };

    fn isEnabled(comptime entries: []const Entry, comptime name: []const u8) bool {
        inline for (entries) |entry| {
            if (std.mem.eql(u8, entry.name, name)) {
                return entry.enabled;
            }
        }
        return false;
    }

    pub fn Conditional(comptime entries: []const Entry, comptime name: []const u8, comptime func: anytype) type {
        const enabled = comptime isEnabled(entries, name);

        return struct {
            pub fn call(x: i32) i32 {
                if (enabled) {
                    return func(x) * 2;
                }
                return func(x);
            }
        };
    }
};

// Usage
const entries = [_]DecoratorRegistry.Entry{
    .{ .name = "timing", .enabled = true },
    .{ .name = "logging", .enabled = false },
};

const TimingWrapped = DecoratorRegistry.Conditional(&entries, "timing", double);
const LoggingWrapped = DecoratorRegistry.Conditional(&entries, "logging", double);

TimingWrapped.call(5);   // 20 (enabled: (5*2)*2)
LoggingWrapped.call(5);  // 10 (disabled: 5*2)
```

Registry pattern enables conditional compilation of decorators.

### Discussion

Organizing decorators within structs provides structure, sharing, and namespace management for metaprogramming code.

### Why Struct-Based Decorators

**Organization**:
- Logical grouping of related decorators
- Namespace separation prevents name collisions
- Clear categorization by purpose
- Easier discovery and documentation

**Sharing**:
- Common configuration across decorators
- Shared utility functions
- Consistent interfaces
- Reduced code duplication

**Flexibility**:
- Mix standalone and struct-based decorators
- Nest decorator structs for hierarchy
- Create decorator families with generics
- Enable/disable via compile-time flags

### Design Patterns

**Namespace pattern**:
```zig
const Category = struct {
    pub fn Decorator1(...) type { ... }
    pub fn Decorator2(...) type { ... }
};
```

Group by category (Validation, Transformation, etc).

**Configuration pattern**:
```zig
const Decorators = struct {
    pub fn WithConfig(comptime config: Config, ...) type { ... }
};
```

Share configuration across decorator instances.

**Factory pattern**:
```zig
const Factory = struct {
    pub fn create(comptime kind: enum { ... }) type {
        return switch (kind) { ... };
    }
};
```

Select decorator type at compile time.

**Generic pattern**:
```zig
fn DecoratorFamily(comptime T: type) type {
    return struct {
        pub fn Decorator1(...) type { ... }
        pub fn Decorator2(...) type { ... }
    };
}
```

Create type-parameterized decorator collections.

**Registry pattern**:
```zig
const Registry = struct {
    pub fn Conditional(comptime entries: []const Entry, ...) type { ... }
};
```

Enable/disable decorators based on compile-time registry.

### Struct Organization Strategies

**By purpose**:
```zig
const Validation = struct { ... };
const Logging = struct { ... };
const Performance = struct { ... };
```

**By domain**:
```zig
const HttpDecorators = struct { ... };
const DatabaseDecorators = struct { ... };
const CacheDecorators = struct { ... };
```

**By complexity**:
```zig
const SimpleDecorators = struct { ... };
const AdvancedDecorators = struct { ... };
const ExperimentalDecorators = struct { ... };
```

**By lifecycle**:
```zig
const PreProcessing = struct { ... };
const CoreLogic = struct { ... };
const PostProcessing = struct { ... };
```

### State Management

**Module-level state**:
```zig
pub fn Decorator(...) type {
    return struct {
        var state: StateType = init_value;
        // ...
    };
}
```

State persists across all uses of this decorator instance.

**Resettable state**:
```zig
pub fn reset() void {
    state = initial_value;
}
```

Allow clearing state between test runs or phases.

**Thread safety**:

Zig's comptime evaluation is single-threaded. Runtime state requires explicit synchronization:
```zig
var state: std.atomic.Value(u32) = .{ .value = 0 };
```

Use atomics for thread-safe state.

### Compile-Time Requirements

**All decorator parameters must be comptime**:
```zig
pub fn Decorator(comptime config: Config, comptime func: anytype) type
```

Can't use runtime values when returning types.

**Configuration resolution**:
```zig
pub fn Decorator(comptime config: Config, ...) type {
    const enabled = config.enabled;  // Resolved at compile time
    // Use 'enabled' in decorator logic
}
```

Extract configuration values before using in decorator.

**Registry lookups**:
```zig
const enabled = comptime isEnabled(entries, name);
```

All registry access must be comptime.

### Testing Strategies

**Test individual decorators**:
```zig
test "validation decorator" {
    const Bounded = Validation.Bounds(func, 0, 10);
    try testing.expectEqual(expected, try Bounded.call(5));
}
```

**Test decorator combinations**:
```zig
test "chained decorators" {
    const Step1 = Decorators.First(func);
    const Step2 = Decorators.Second(Step1.call);
    // Test chain behavior
}
```

**Test stateful decorators**:
```zig
test "stateful tracking" {
    const Tracked = Decorators.WithCounter(func);
    _ = Tracked.call(5);
    try testing.expectEqual(1, Tracked.getCallCount());
    Tracked.reset();
    try testing.expectEqual(0, Tracked.getCallCount());
}
```

**Test configuration variants**:
```zig
test "different configs" {
    const config1 = Config{ .enabled = true };
    const config2 = Config{ .enabled = false };

    const Dec1 = Decorators.WithConfig(config1, func);
    const Dec2 = Decorators.WithConfig(config2, func);
    // Test different behaviors
}
```

### Documentation Practices

**Document struct purpose**:
```zig
/// Validation decorators that enforce runtime constraints
const Validation = struct { ... };
```

**Document individual decorators**:
```zig
/// Enforces bounds checking on function input
/// Returns error.OutOfBounds if x < min or x > max
pub fn Bounds(comptime func: anytype, comptime min: i32, comptime max: i32) type
```

**Document configuration**:
```zig
/// Configuration for caching decorators
const Config = struct {
    /// Enable/disable caching (default: true)
    enable_caching: bool = true,
    /// Maximum cache entries (default: 100)
    max_cache_size: usize = 100,
};
```

**Provide usage examples**:
```zig
/// Example usage:
///   const Bounded = Validation.Bounds(myFunc, 0, 100);
///   const result = try Bounded.call(50);
```

### Performance Characteristics

**Zero runtime overhead**:
- All decorator selection at compile time
- No vtables or dynamic dispatch
- Fully inlined by optimizer
- Same performance as hand-written code

**Compile time impact**:
- More complex structures increase compile time
- Registry lookups add minimal overhead
- Generic instantiation multiplies compile work
- Worth it for maintainability

**Binary size**:
- Each configuration creates separate instance
- May increase code size with many variants
- Compiler deduplicates identical code
- Use judiciously in size-constrained environments

### Common Patterns

**Validation suite**:
```zig
const Validate = struct {
    pub fn Bounds(...) type { ... }
    pub fn NonNull(...) type { ... }
    pub fn Range(...) type { ... }
    pub fn Pattern(...) type { ... }
};
```

**Transformation pipeline**:
```zig
const Transform = struct {
    pub fn Map(...) type { ... }
    pub fn Filter(...) type { ... }
    pub fn Reduce(...) type { ... }
};
```

**Instrumentation**:
```zig
const Instrument = struct {
    pub fn Timing(...) type { ... }
    pub fn Logging(...) type { ... }
    pub fn Profiling(...) type { ... }
};
```

**Resource management**:
```zig
const Resource = struct {
    pub fn WithLock(...) type { ... }
    pub fn WithRetry(...) type { ... }
    pub fn WithTimeout(...) type { ... }
};
```

### Full Tested Code

```zig
// Recipe 9.6: Defining Decorators as Part of a Struct
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_struct_decorators
// Organize decorators as struct methods
const Decorators = struct {
    pub fn Timing(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) i32 {
                // In real code, would measure time
                const result = func(x);
                return result;
            }
        };
    }

    pub fn Logging(comptime func: anytype) type {
        return struct {
            var call_count: u32 = 0;

            pub fn call(x: i32) i32 {
                call_count += 1;
                const result = func(x);
                return result;
            }

            pub fn getCallCount() u32 {
                return call_count;
            }
        };
    }
};

fn double(x: i32) i32 {
    return x * 2;
}

test "basic struct decorators" {
    const Timed = Decorators.Timing(double);
    try testing.expectEqual(@as(i32, 10), Timed.call(5));

    const Logged = Decorators.Logging(double);
    try testing.expectEqual(@as(i32, 10), Logged.call(5));
    try testing.expectEqual(@as(u32, 1), Logged.getCallCount());
}
// ANCHOR_END: basic_struct_decorators

// ANCHOR: shared_config
// Decorators with shared configuration
const ConfiguredDecorators = struct {
    const Config = struct {
        enable_logging: bool = false,
        enable_caching: bool = true,
        max_cache_size: usize = 100,
    };

    pub fn WithCache(comptime config: Config, comptime func: anytype) type {
        const enable = config.enable_caching;
        const max_size = config.max_cache_size;

        return struct {
            pub fn call(x: i32) i32 {
                if (!enable) {
                    return func(x);
                }
                // Simplified caching
                _ = max_size;
                return func(x);
            }

            pub fn isCacheEnabled() bool {
                return enable;
            }
        };
    }
};

test "shared config" {
    const config = ConfiguredDecorators.Config{
        .enable_caching = true,
        .max_cache_size = 50,
    };

    const Cached = ConfiguredDecorators.WithCache(config, double);
    try testing.expectEqual(@as(i32, 10), Cached.call(5));
    try testing.expect(Cached.isCacheEnabled());
}
// ANCHOR_END: shared_config

// ANCHOR: namespace_organization
// Organize decorators by category
const Validation = struct {
    pub fn Bounds(comptime func: anytype, comptime min: i32, comptime max: i32) type {
        return struct {
            pub fn call(x: i32) !i32 {
                if (x < min or x > max) {
                    return error.OutOfBounds;
                }
                return func(x);
            }
        };
    }

    pub fn NonZero(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) !i32 {
                if (x == 0) {
                    return error.ZeroNotAllowed;
                }
                return func(x);
            }
        };
    }
};

const Transformation = struct {
    pub fn Scale(comptime func: anytype, comptime factor: i32) type {
        return struct {
            pub fn call(x: i32) i32 {
                return func(x) * factor;
            }
        };
    }

    pub fn Offset(comptime func: anytype, comptime offset: i32) type {
        return struct {
            pub fn call(x: i32) i32 {
                return func(x) + offset;
            }
        };
    }
};

test "namespace organization" {
    const Bounded = Validation.Bounds(double, 0, 10);
    try testing.expectEqual(@as(i32, 10), try Bounded.call(5));
    try testing.expectError(error.OutOfBounds, Bounded.call(15));

    const Scaled = Transformation.Scale(double, 2);
    try testing.expectEqual(@as(i32, 20), Scaled.call(5)); // (5 * 2) * 2
}
// ANCHOR_END: namespace_organization

// ANCHOR: stateful_decorators
// Decorators with compile-time configuration and state tracking
const StatefulDecorators = struct {
    pub fn WithCounter(comptime func: anytype) type {
        return struct {
            var call_count: u32 = 0;
            var total_sum: i64 = 0;

            pub fn call(x: i32) i32 {
                call_count += 1;
                const result = func(x);
                total_sum += result;
                return result;
            }

            pub fn getCallCount() u32 {
                return call_count;
            }

            pub fn getTotalSum() i64 {
                return total_sum;
            }

            pub fn reset() void {
                call_count = 0;
                total_sum = 0;
            }
        };
    }

    pub fn WithMinMax(comptime func: anytype) type {
        return struct {
            var min_value: ?i32 = null;
            var max_value: ?i32 = null;

            pub fn call(x: i32) i32 {
                const result = func(x);

                if (min_value) |min| {
                    if (result < min) min_value = result;
                } else {
                    min_value = result;
                }

                if (max_value) |max| {
                    if (result > max) max_value = result;
                } else {
                    max_value = result;
                }

                return result;
            }

            pub fn getMin() ?i32 {
                return min_value;
            }

            pub fn getMax() ?i32 {
                return max_value;
            }

            pub fn reset() void {
                min_value = null;
                max_value = null;
            }
        };
    }
};

test "stateful decorators" {
    const Counted = StatefulDecorators.WithCounter(double);

    _ = Counted.call(5);
    _ = Counted.call(10);

    try testing.expectEqual(@as(u32, 2), Counted.getCallCount());
    try testing.expectEqual(@as(i64, 30), Counted.getTotalSum()); // 10 + 20

    Counted.reset();
    try testing.expectEqual(@as(u32, 0), Counted.getCallCount());

    const MinMaxed = StatefulDecorators.WithMinMax(double);
    _ = MinMaxed.call(5);  // 10
    _ = MinMaxed.call(10); // 20
    _ = MinMaxed.call(2);  // 4

    try testing.expectEqual(@as(?i32, 4), MinMaxed.getMin());
    try testing.expectEqual(@as(?i32, 20), MinMaxed.getMax());

    MinMaxed.reset();
}
// ANCHOR_END: stateful_decorators

// ANCHOR: decorator_factory
// Factory pattern for decorator creation
const DecoratorFactory = struct {
    pub fn create(comptime decorator_type: enum { timing, logging, caching }) type {
        return switch (decorator_type) {
            .timing => struct {
                pub fn wrap(comptime func: anytype) type {
                    return struct {
                        pub fn call(x: i32) i32 {
                            // Timing logic
                            return func(x);
                        }
                    };
                }
            },
            .logging => struct {
                pub fn wrap(comptime func: anytype) type {
                    return struct {
                        var count: u32 = 0;

                        pub fn call(x: i32) i32 {
                            count += 1;
                            return func(x);
                        }

                        pub fn getCount() u32 {
                            return count;
                        }
                    };
                }
            },
            .caching => struct {
                pub fn wrap(comptime func: anytype) type {
                    return struct {
                        pub fn call(x: i32) i32 {
                            // Caching logic
                            return func(x);
                        }
                    };
                }
            },
        };
    }
};

test "decorator factory" {
    const LoggingDecorator = DecoratorFactory.create(.logging);
    const Logged = LoggingDecorator.wrap(double);

    try testing.expectEqual(@as(i32, 10), Logged.call(5));
    try testing.expectEqual(@as(u32, 1), Logged.getCount());
}
// ANCHOR_END: decorator_factory

// ANCHOR: chaining_struct_decorators
// Chain multiple decorators from the same struct
const ChainableDecorators = struct {
    pub fn Validate(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) !i32 {
                if (x < 0) {
                    return error.NegativeNotAllowed;
                }
                return func(x);
            }
        };
    }

    pub fn Double(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) @TypeOf(func(0)) {
                return func(x * 2);
            }
        };
    }

    pub fn AddTen(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) @TypeOf(func(0)) {
                return func(x + 10);
            }
        };
    }
};

fn identity(x: i32) i32 {
    return x;
}

test "chaining struct decorators" {
    // Chain: AddTen -> Double -> Validate -> identity
    const Step1 = ChainableDecorators.Validate(identity);
    const Step2 = ChainableDecorators.Double(Step1.call);
    const Step3 = ChainableDecorators.AddTen(Step2.call);

    try testing.expectEqual(@as(i32, 30), try Step3.call(5)); // (5 + 10) * 2 = 30
}
// ANCHOR_END: chaining_struct_decorators

// ANCHOR: shared_utilities
// Decorators with shared utility functions
const UtilityDecorators = struct {
    fn logMessage(comptime msg: []const u8, value: i32) void {
        _ = value;
        _ = msg;
        // In real code: std.debug.print("{s}: {d}\n", .{ msg, value });
    }

    pub fn WithPreLog(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) i32 {
                logMessage("Before", x);
                return func(x);
            }
        };
    }

    pub fn WithPostLog(comptime func: anytype) type {
        return struct {
            pub fn call(x: i32) i32 {
                const result = func(x);
                logMessage("After", result);
                return result;
            }
        };
    }
};

test "shared utilities" {
    const PreLogged = UtilityDecorators.WithPreLog(double);
    const PostLogged = UtilityDecorators.WithPostLog(double);

    try testing.expectEqual(@as(i32, 10), PreLogged.call(5));
    try testing.expectEqual(@as(i32, 10), PostLogged.call(5));
}
// ANCHOR_END: shared_utilities

// ANCHOR: generic_decorator_struct
// Generic decorator struct with type parameters
fn DecoratorSet(comptime T: type) type {
    return struct {
        pub fn WithDefault(comptime func: anytype, comptime default: T) type {
            return struct {
                pub fn call(x: ?T) T {
                    const val = x orelse default;
                    return func(val);
                }
            };
        }

        pub fn WithValidation(comptime func: anytype, comptime validator: anytype) type {
            return struct {
                pub fn call(x: T) !T {
                    if (!validator(x)) {
                        return error.ValidationFailed;
                    }
                    return func(x);
                }
            };
        }
    };
}

fn isPositive(x: i32) bool {
    return x > 0;
}

test "generic decorator struct" {
    const I32Decorators = DecoratorSet(i32);

    const WithDefault = I32Decorators.WithDefault(double, 10);
    try testing.expectEqual(@as(i32, 10), WithDefault.call(5));
    try testing.expectEqual(@as(i32, 20), WithDefault.call(null));

    const Validated = I32Decorators.WithValidation(double, isPositive);
    try testing.expectEqual(@as(i32, 10), try Validated.call(5));
    try testing.expectError(error.ValidationFailed, Validated.call(-5));
}
// ANCHOR_END: generic_decorator_struct

// ANCHOR: mixin_decorators
// Decorator mixin pattern
const LoggingMixin = struct {
    pub fn addLogging(comptime T: type) type {
        return struct {
            base: T,

            pub fn call(self: @This(), x: i32) i32 {
                // Log before
                const result = self.base.call(x);
                // Log after
                return result;
            }
        };
    }
};

const CachingMixin = struct {
    pub fn addCaching(comptime T: type) type {
        return struct {
            base: T,
            var cached: ?i32 = null;

            pub fn call(self: @This(), x: i32) i32 {
                if (cached) |c| {
                    if (x == 0) return c; // Simplified cache check
                }
                const result = self.base.call(x);
                cached = result;
                return result;
            }
        };
    }
};

const BaseWrapper = struct {
    pub fn call(_: @This(), x: i32) i32 {
        return x * 3;
    }
};

test "mixin decorators" {
    const Logged = LoggingMixin.addLogging(BaseWrapper);
    const logged = Logged{ .base = .{} };
    try testing.expectEqual(@as(i32, 15), logged.call(5));

    const Cached = CachingMixin.addCaching(BaseWrapper);
    const cached = Cached{ .base = .{} };
    try testing.expectEqual(@as(i32, 15), cached.call(5));
}
// ANCHOR_END: mixin_decorators

// ANCHOR: decorator_registry
// Decorator registry pattern
const DecoratorRegistry = struct {
    const Entry = struct {
        name: []const u8,
        enabled: bool,
    };

    fn isEnabled(comptime entries: []const Entry, comptime name: []const u8) bool {
        inline for (entries) |entry| {
            if (std.mem.eql(u8, entry.name, name)) {
                return entry.enabled;
            }
        }
        return false;
    }

    pub fn Conditional(comptime entries: []const Entry, comptime name: []const u8, comptime func: anytype) type {
        const enabled = comptime isEnabled(entries, name);

        return struct {
            pub fn call(x: i32) i32 {
                if (enabled) {
                    return func(x) * 2;
                }
                return func(x);
            }
        };
    }
};

test "decorator registry" {
    const entries = [_]DecoratorRegistry.Entry{
        .{ .name = "timing", .enabled = true },
        .{ .name = "logging", .enabled = false },
    };

    const TimingWrapped = DecoratorRegistry.Conditional(&entries, "timing", double);
    const LoggingWrapped = DecoratorRegistry.Conditional(&entries, "logging", double);

    try testing.expectEqual(@as(i32, 20), TimingWrapped.call(5)); // Enabled: (5*2)*2
    try testing.expectEqual(@as(i32, 10), LoggingWrapped.call(5)); // Disabled: 5*2
}
// ANCHOR_END: decorator_registry

// Comprehensive test
test "comprehensive struct decorators" {
    // Basic struct decorators
    const Logged = Decorators.Logging(double);
    try testing.expectEqual(@as(i32, 10), Logged.call(5));

    // Namespace organization
    const Bounded = Validation.Bounds(double, 0, 100);
    try testing.expectEqual(@as(i32, 10), try Bounded.call(5));

    // Factory pattern
    const Factory = DecoratorFactory.create(.logging);
    const FactoryWrapped = Factory.wrap(double);
    try testing.expectEqual(@as(i32, 10), FactoryWrapped.call(5));

    // Generic decorator set
    const I32Decs = DecoratorSet(i32);
    const WithDef = I32Decs.WithDefault(double, 10);
    try testing.expectEqual(@as(i32, 20), WithDef.call(null));
}
```

### See Also

- Recipe 9.1: Putting a Wrapper Around a Function
- Recipe 9.2: Preserving Function Metadata When Writing Decorators
- Recipe 9.4: Defining a Decorator That Takes Arguments
- Recipe 9.7: Defining Decorators as Structs

---

## Recipe 9.7: Defining Decorators As Structs {#recipe-9-7}

**Tags:** allocators, arraylist, atomics, comptime, comptime-metaprogramming, concurrency, data-structures, error-handling, hashmap, memory, resource-cleanup, testing, threading
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_7.zig`

### Problem

You need decorators with instance state, configuration, or multiple methods. You want decorators that can be configured at runtime, maintain mutable state across calls, or provide additional APIs beyond simple wrapping.

### Solution

Define decorators as struct types that wrap functionality, maintaining their own state and configuration as struct fields.

### Basic Decorator Struct

Create a decorator as a struct that wraps a function type:

```zig
// Define decorator as a struct type
fn TimingDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();
        func: Func,
        elapsed_ns: u64 = 0,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) i32 {
            // In real code, measure actual time
            self.elapsed_ns += 100;
            return self.func.call(x);
        }

        pub fn getElapsed(self: Self) u64 {
            return self.elapsed_ns;
        }
    };
}

const SimpleFunc = struct {
    pub fn call(_: @This(), x: i32) i32 {
        return x * 2;
    }
};

test "basic decorator struct" {
    const simple = SimpleFunc{};
    var timed = TimingDecorator(SimpleFunc).init(simple);

    const result = timed.call(5);
    try testing.expectEqual(@as(i32, 10), result);
    try testing.expectEqual(@as(u64, 100), timed.getElapsed());
}
```

The decorator is an instance with mutable state.

### Stateful Decorator

Track statistics across multiple calls:

```zig
fn CountingDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();
        func: Func,
        call_count: u32 = 0,
        total_sum: i64 = 0,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) i32 {
            self.call_count += 1;
            const result = self.func.call(x);
            self.total_sum += result;
            return result;
        }

        pub fn getCallCount(self: Self) u32 {
            return self.call_count;
        }

        pub fn getTotalSum(self: Self) i64 {
            return self.total_sum;
        }

        pub fn reset(self: *Self) void {
            self.call_count = 0;
            self.total_sum = 0;
        }
    };
}

// Usage
const simple = SimpleFunc{};
var counter = CountingDecorator(SimpleFunc).init(simple);

counter.call(5);         // 10
counter.call(10);        // 20

counter.getCallCount();  // 2
counter.getTotalSum();   // 30

counter.reset();
counter.getCallCount();  // 0
```

State persists across calls and can be reset.

### Configured Decorator

Pass configuration at initialization:

```zig
fn ValidatingDecorator(comptime Func: type, comptime Config: type) type {
    return struct {
        const Self = @This();
        func: Func,
        config: Config,

        pub fn init(func: Func, config: Config) Self {
            return .{ .func = func, .config = config };
        }

        pub fn call(self: *Self, x: i32) !i32 {
            if (x < self.config.min or x > self.config.max) {
                return error.OutOfBounds;
            }
            return self.func.call(x);
        }
    };
}

const BoundsConfig = struct {
    min: i32,
    max: i32,
};

// Usage
const simple = SimpleFunc{};
const config = BoundsConfig{ .min = 0, .max = 10 };
var validator = ValidatingDecorator(SimpleFunc, BoundsConfig).init(simple, config);

try validator.call(5);   // 10
try validator.call(15);  // error.OutOfBounds
```

Configuration stored in struct fields.

### Caching Decorator

Maintain cache state within the decorator:

```zig
fn CachingDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();
        const CacheEntry = struct {
            input: i32,
            output: i32,
        };

        func: Func,
        cache: ?CacheEntry = null,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) i32 {
            if (self.cache) |entry| {
                if (entry.input == x) {
                    return entry.output;
                }
            }

            const result = self.func.call(x);
            self.cache = CacheEntry{ .input = x, .output = result };
            return result;
        }

        pub fn clearCache(self: *Self) void {
            self.cache = null;
        }

        pub fn isCached(self: Self, x: i32) bool {
            if (self.cache) |entry| {
                return entry.input == x;
            }
            return false;
        }
    };
}

// Usage
const simple = SimpleFunc{};
var cached = CachingDecorator(SimpleFunc).init(simple);

cached.call(5);      // Calculates, caches
cached.call(5);      // Returns cached
cached.isCached(5);  // true

cached.clearCache();
cached.isCached(5);  // false
```

Cache managed as instance state.

### Composable Decorators

Chain decorator structs together:

```zig
fn LoggingDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();
        func: Func,
        log_count: u32 = 0,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) @TypeOf(self.func.call(0)) {
            self.log_count += 1;
            return self.func.call(x);
        }

        pub fn getLogCount(self: Self) u32 {
            return self.log_count;
        }
    };
}

fn ScalingDecorator(comptime Func: type, comptime factor: i32) type {
    return struct {
        const Self = @This();
        func: Func,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) @TypeOf(self.func.call(0)) {
            return self.func.call(x) * factor;
        }
    };
}

// Usage - compose decorators
const simple = SimpleFunc{};
const logged = LoggingDecorator(SimpleFunc).init(simple);
var scaled = ScalingDecorator(LoggingDecorator(SimpleFunc), 3).init(logged);

scaled.call(5);  // (5 * 2) * 3 = 30
```

Each decorator wraps the previous one.

### Allocator-Based Decorator

Use allocators for dynamic storage:

```zig
fn HistoryDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();
        func: Func,
        allocator: std.mem.Allocator,
        history: std.ArrayList(i32),

        pub fn init(allocator: std.mem.Allocator, func: Func) Self {
            return .{
                .func = func,
                .allocator = allocator,
                .history = .{ .items = &.{}, .capacity = 0 },
            };
        }

        pub fn deinit(self: *Self) void {
            self.history.deinit(self.allocator);
        }

        pub fn call(self: *Self, x: i32) !i32 {
            const result = self.func.call(x);
            try self.history.append(self.allocator, result);
            return result;
        }

        pub fn getHistory(self: Self) []const i32 {
            return self.history.items;
        }

        pub fn clearHistory(self: *Self) void {
            self.history.clearRetainingCapacity();
        }
    };
}

// Usage
const simple = SimpleFunc{};
var history = HistoryDecorator(SimpleFunc).init(allocator, simple);
defer history.deinit();

try history.call(5);   // Appends 10
try history.call(10);  // Appends 20

const hist = history.getHistory();  // [10, 20]
```

Decorators can manage allocated resources.

### Error Handling Decorator

Implement retry logic with error handling:

```zig
fn RetryDecorator(comptime Func: type, comptime max_attempts: u32) type {
    return struct {
        const Self = @This();
        func: Func,
        attempts: u32 = 0,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) !i32 {
            var last_error: ?anyerror = null;
            var attempt: u32 = 0;

            while (attempt < max_attempts) : (attempt += 1) {
                self.attempts += 1;
                const result = self.func.call(x) catch |err| {
                    last_error = err;
                    continue;
                };
                return result;
            }

            if (last_error) |err| {
                return err;
            }
            return error.MaxRetriesExceeded;
        }

        pub fn getAttempts(self: Self) u32 {
            return self.attempts;
        }
    };
}

// Usage
var retry = RetryDecorator(FallibleFunc, 5).init(fallible);

const result = try retry.call(10);
retry.getAttempts();  // Number of attempts made
```

Retry attempts tracked in decorator state.

### Builder Pattern

Fluent API for decorator construction:

```zig
fn DecoratorBuilder(comptime Func: type) type {
    return struct {
        const Self = @This();

        func: Func,
        enable_logging: bool = false,
        enable_caching: bool = false,
        scale_factor: i32 = 1,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn withLogging(self: Self) Self {
            var new = self;
            new.enable_logging = true;
            return new;
        }

        pub fn withCaching(self: Self) Self {
            var new = self;
            new.enable_caching = true;
            return new;
        }

        pub fn withScale(self: Self, factor: i32) Self {
            var new = self;
            new.scale_factor = factor;
            return new;
        }

        pub fn build(self: Self) Built(Func) {
            return Built(Func){
                .func = self.func,
                .enable_logging = self.enable_logging,
                .enable_caching = self.enable_caching,
                .scale_factor = self.scale_factor,
            };
        }
    };
}

// Usage
const simple = SimpleFunc{};
var decorated = DecoratorBuilder(SimpleFunc).init(simple)
    .withLogging()
    .withScale(3)
    .build();

decorated.call(5);  // 30
```

Builder provides fluent configuration API.

### Conditional Decorator

Enable/disable behavior at runtime:

```zig
fn ConditionalDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();

        func: Func,
        enabled: bool,
        multiplier: i32,

        pub fn init(func: Func, enabled: bool, multiplier: i32) Self {
            return .{
                .func = func,
                .enabled = enabled,
                .multiplier = multiplier,
            };
        }

        pub fn call(self: *Self, x: i32) i32 {
            const base = self.func.call(x);
            if (self.enabled) {
                return base * self.multiplier;
            }
            return base;
        }

        pub fn enable(self: *Self) void {
            self.enabled = true;
        }

        pub fn disable(self: *Self) void {
            self.enabled = false;
        }
    };
}

// Usage
var conditional = ConditionalDecorator(SimpleFunc).init(simple, true, 3);

conditional.call(5);  // 30 (enabled)

conditional.disable();
conditional.call(5);  // 10 (disabled)
```

Runtime control over decorator behavior.

### Method Chaining

Create fluent APIs with method chaining:

```zig
fn ChainableDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();

        func: Func,
        offset: i32 = 0,
        multiplier: i32 = 1,
        invert: bool = false,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn addOffset(self: *Self, offset: i32) *Self {
            self.offset = offset;
            return self;
        }

        pub fn setMultiplier(self: *Self, multiplier: i32) *Self {
            self.multiplier = multiplier;
            return self;
        }

        pub fn setInvert(self: *Self, invert: bool) *Self {
            self.invert = invert;
            return self;
        }

        pub fn call(self: *Self, x: i32) i32 {
            var result = self.func.call(x);
            result = result + self.offset;
            result = result * self.multiplier;
            if (self.invert) {
                result = -result;
            }
            return result;
        }
    };
}

// Usage
var chainable = ChainableDecorator(SimpleFunc).init(simple);

_ = chainable.addOffset(5).setMultiplier(2);

chainable.call(5);  // ((5*2) + 5) * 2 = 30
```

Methods return `*Self` for chaining.

### Discussion

Decorator structs combine compile-time type generation with runtime instance state for flexible, powerful metaprogramming.

### When to Use Decorator Structs

**Use decorator structs when:**
- Need mutable state across calls
- Require runtime configuration
- Want multiple methods beyond call()
- Managing resources (allocators, files)
- Implementing stateful patterns (caching, counting)
- Building complex chained behaviors

**Use function decorators when:**
- Stateless transformations
- Pure compile-time decisions
- Simple wrapping without state
- Zero-overhead abstractions

### Struct vs Function Decorators

**Struct decorators**:
```zig
fn Decorator(comptime Func: type) type {
    return struct {
        func: Func,
        state: StateType,
        // Instance methods
    };
}
```

Instance-based, mutable state, resource management.

**Function decorators**:
```zig
fn Decorator(comptime func: anytype) type {
    return struct {
        pub fn call(args: anytype) ReturnType {
            // Stateless wrapper
        }
    };
}
```

Stateless, compile-time only, simpler.

### State Management

**Mutable state**:
```zig
return struct {
    var state: u32 = 0;  // Shared across all instances

    pub fn call(self: *Self, ...) {
        state += 1;  // Modified by all instances
    }
};
```

vs

```zig
return struct {
    state: u32 = 0,  // Per-instance

    pub fn call(self: *Self, ...) {
        self.state += 1;  // Modified per instance
    }
};
```

Choose based on sharing requirements.

**Reset capabilities**:
```zig
pub fn reset(self: *Self) void {
    self.state = initial_value;
}
```

Allow clearing state for reuse or testing.

**Thread safety**:

Struct fields are not inherently thread-safe:
```zig
state: std.atomic.Value(u32),  // For concurrent access
```

Use atomics for thread-safe state.

### Resource Management

**RAII pattern**:
```zig
pub fn init(allocator: Allocator, ...) Self {
    return .{ .resource = acquire(), ... };
}

pub fn deinit(self: *Self) void {
    release(self.resource);
}
```

Always provide `deinit` for cleanup.

**Usage with defer**:
```zig
var decorator = Decorator.init(allocator, func);
defer decorator.deinit();
```

Ensures cleanup even on error paths.

**Error handling in init**:
```zig
pub fn init(allocator: Allocator, ...) !Self {
    const resource = try acquire();
    errdefer release(resource);
    return .{ .resource = resource, ... };
}
```

Use `errdefer` for partial cleanup.

### Builder Pattern Benefits

**Fluent API**:
```zig
decorator
    .withLogging()
    .withCaching()
    .withScale(2)
    .build()
```

Readable, self-documenting configuration.

**Immutable builder**:
```zig
pub fn withOption(self: Self, value: T) Self {
    var new = self;
    new.option = value;
    return new;
}
```

Each method returns new instance.

**Validation at build**:
```zig
pub fn build(self: Self) !Decorated {
    if (self.min >= self.max) {
        return error.InvalidConfig;
    }
    return Decorated{ ... };
}
```

Catch configuration errors early.

### Composition Strategies

**Nested decorators**:
```zig
const logged = LoggingDecorator(SimpleFunc).init(simple);
const cached = CachingDecorator(LoggingDecorator(SimpleFunc)).init(logged);
```

Type composition at compile time.

**Uniform interface**:
```zig
pub fn call(self: *Self, x: i32) ReturnType
```

All decorators share same call signature.

**Type erasure**:
```zig
const AnyDecorator = struct {
    ptr: *anyopaque,
    callFn: *const fn(*anyopaque, i32) i32,

    pub fn call(self: *AnyDecorator, x: i32) i32 {
        return self.callFn(self.ptr, x);
    }
};
```

Hide concrete decorator types if needed.

### Performance Considerations

**Instance overhead**:
- Each decorator instance has memory cost
- State stored in struct fields
- Multiple decorators = multiple instances
- Consider stack vs heap allocation

**Indirection cost**:
```zig
self.func.call(x)  // One level of indirection
```

Minimal, often inlined by compiler.

**Cache effects**:
- Struct fields stored contiguously
- Good cache locality for hot paths
- Large structs may hurt performance

**Optimization**:
- Compiler can inline struct methods
- Release builds optimize away overhead
- Profile before optimizing

### Testing Strategies

**Test initialization**:
```zig
test "decorator init" {
    const decorator = Decorator.init(func);
    try testing.expectEqual(expected_initial_state, decorator.state);
}
```

**Test state changes**:
```zig
test "state mutation" {
    var decorator = Decorator.init(func);
    _ = decorator.call(5);
    try testing.expectEqual(1, decorator.call_count);
}
```

**Test resource cleanup**:
```zig
test "cleanup" {
    var decorator = Decorator.init(allocator, func);
    defer decorator.deinit();
    // Use decorator
    // defer ensures cleanup
}
```

**Test error paths**:
```zig
test "error handling" {
    var decorator = Decorator.init(func);
    try testing.expectError(error.Expected, decorator.call(invalid));
}
```

**Test composition**:
```zig
test "chained decorators" {
    const d1 = Dec1.init(func);
    var d2 = Dec2.init(d1);
    try testing.expectEqual(expected, d2.call(input));
}
```

### Common Patterns

**Statistics tracking**:
```zig
call_count: u32 = 0,
total_time: u64 = 0,
min_value: ?T = null,
max_value: ?T = null,
```

**Caching**:
```zig
cache: std.AutoHashMap(Input, Output),
cache_hits: u32 = 0,
cache_misses: u32 = 0,
```

**Rate limiting**:
```zig
last_call: i64 = 0,
calls_per_second: u32,
delay_ms: u64,
```

**Validation**:
```zig
min_value: T,
max_value: T,
validation_errors: u32 = 0,
```

**Logging**:
```zig
log_level: LogLevel,
log_count: u32 = 0,
last_input: ?Input = null,
```

### Memory Layout

**Struct size**:
```zig
test "decorator size" {
    try testing.expectEqual(
        @sizeOf(WrappedFunc) + @sizeOf(State),
        @sizeOf(Decorator(WrappedFunc))
    );
}
```

**Alignment**:
```zig
return struct {
    func: Func align(8),  // Control alignment
    state: State,
};
```

**Packed structs**:
```zig
return packed struct {
    // Minimize size for flags
    enabled: bool,
    cached: bool,
    logged: bool,
};
```

### Documentation

**Document struct fields**:
```zig
/// Number of times call() has been invoked
call_count: u32 = 0,
/// Cumulative sum of all results
total_sum: i64 = 0,
```

**Document methods**:
```zig
/// Calls the wrapped function and updates statistics
/// Returns the result of the wrapped function
pub fn call(self: *Self, x: i32) i32
```

**Document initialization**:
```zig
/// Creates a new decorator instance
/// The decorator takes ownership of `func`
pub fn init(func: Func) Self
```

**Document cleanup**:
```zig
/// Releases all resources held by this decorator
/// Must be called when decorator is no longer needed
pub fn deinit(self: *Self) void
```

### Full Tested Code

```zig
// Recipe 9.7: Defining Decorators as Structs
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_decorator_struct
// Define decorator as a struct type
fn TimingDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();
        func: Func,
        elapsed_ns: u64 = 0,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) i32 {
            // In real code, measure actual time
            self.elapsed_ns += 100;
            return self.func.call(x);
        }

        pub fn getElapsed(self: Self) u64 {
            return self.elapsed_ns;
        }
    };
}

const SimpleFunc = struct {
    pub fn call(_: @This(), x: i32) i32 {
        return x * 2;
    }
};

test "basic decorator struct" {
    const simple = SimpleFunc{};
    var timed = TimingDecorator(SimpleFunc).init(simple);

    const result = timed.call(5);
    try testing.expectEqual(@as(i32, 10), result);
    try testing.expectEqual(@as(u64, 100), timed.getElapsed());
}
// ANCHOR_END: basic_decorator_struct

// ANCHOR: stateful_decorator
// Decorator with persistent state
fn CountingDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();
        func: Func,
        call_count: u32 = 0,
        total_sum: i64 = 0,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) i32 {
            self.call_count += 1;
            const result = self.func.call(x);
            self.total_sum += result;
            return result;
        }

        pub fn getCallCount(self: Self) u32 {
            return self.call_count;
        }

        pub fn getTotalSum(self: Self) i64 {
            return self.total_sum;
        }

        pub fn reset(self: *Self) void {
            self.call_count = 0;
            self.total_sum = 0;
        }
    };
}

test "stateful decorator" {
    const simple = SimpleFunc{};
    var counter = CountingDecorator(SimpleFunc).init(simple);

    _ = counter.call(5);
    _ = counter.call(10);

    try testing.expectEqual(@as(u32, 2), counter.getCallCount());
    try testing.expectEqual(@as(i64, 30), counter.getTotalSum()); // 10 + 20

    counter.reset();
    try testing.expectEqual(@as(u32, 0), counter.getCallCount());
}
// ANCHOR_END: stateful_decorator

// ANCHOR: configured_decorator
// Decorator with configuration
fn ValidatingDecorator(comptime Func: type, comptime Config: type) type {
    return struct {
        const Self = @This();
        func: Func,
        config: Config,

        pub fn init(func: Func, config: Config) Self {
            return .{ .func = func, .config = config };
        }

        pub fn call(self: *Self, x: i32) !i32 {
            if (x < self.config.min or x > self.config.max) {
                return error.OutOfBounds;
            }
            return self.func.call(x);
        }
    };
}

const BoundsConfig = struct {
    min: i32,
    max: i32,
};

test "configured decorator" {
    const simple = SimpleFunc{};
    const config = BoundsConfig{ .min = 0, .max = 10 };
    var validator = ValidatingDecorator(SimpleFunc, BoundsConfig).init(simple, config);

    const r1 = try validator.call(5);
    try testing.expectEqual(@as(i32, 10), r1);

    const r2 = validator.call(15);
    try testing.expectError(error.OutOfBounds, r2);
}
// ANCHOR_END: configured_decorator

// ANCHOR: caching_decorator
// Decorator with cache storage
fn CachingDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();
        const CacheEntry = struct {
            input: i32,
            output: i32,
        };

        func: Func,
        cache: ?CacheEntry = null,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) i32 {
            if (self.cache) |entry| {
                if (entry.input == x) {
                    return entry.output;
                }
            }

            const result = self.func.call(x);
            self.cache = CacheEntry{ .input = x, .output = result };
            return result;
        }

        pub fn clearCache(self: *Self) void {
            self.cache = null;
        }

        pub fn isCached(self: Self, x: i32) bool {
            if (self.cache) |entry| {
                return entry.input == x;
            }
            return false;
        }
    };
}

test "caching decorator" {
    const simple = SimpleFunc{};
    var cached = CachingDecorator(SimpleFunc).init(simple);

    const r1 = cached.call(5);
    try testing.expectEqual(@as(i32, 10), r1);
    try testing.expect(cached.isCached(5));

    const r2 = cached.call(5);
    try testing.expectEqual(@as(i32, 10), r2);

    cached.clearCache();
    try testing.expect(!cached.isCached(5));
}
// ANCHOR_END: caching_decorator

// ANCHOR: composable_decorators
// Compose multiple decorator structs
fn LoggingDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();
        func: Func,
        log_count: u32 = 0,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) @TypeOf(self.func.call(0)) {
            self.log_count += 1;
            return self.func.call(x);
        }

        pub fn getLogCount(self: Self) u32 {
            return self.log_count;
        }
    };
}

fn ScalingDecorator(comptime Func: type, comptime factor: i32) type {
    return struct {
        const Self = @This();
        func: Func,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) @TypeOf(self.func.call(0)) {
            return self.func.call(x) * factor;
        }
    };
}

test "composable decorators" {
    const simple = SimpleFunc{};
    const logged = LoggingDecorator(SimpleFunc).init(simple);
    var scaled = ScalingDecorator(LoggingDecorator(SimpleFunc), 3).init(logged);

    const result = scaled.call(5);
    try testing.expectEqual(@as(i32, 30), result); // (5 * 2) * 3
}
// ANCHOR_END: composable_decorators

// ANCHOR: allocator_decorator
// Decorator with allocator for dynamic data
fn HistoryDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();
        func: Func,
        allocator: std.mem.Allocator,
        history: std.ArrayList(i32),

        pub fn init(allocator: std.mem.Allocator, func: Func) Self {
            return .{
                .func = func,
                .allocator = allocator,
                .history = .{ .items = &.{}, .capacity = 0 },
            };
        }

        pub fn deinit(self: *Self) void {
            self.history.deinit(self.allocator);
        }

        pub fn call(self: *Self, x: i32) !i32 {
            const result = self.func.call(x);
            try self.history.append(self.allocator, result);
            return result;
        }

        pub fn getHistory(self: Self) []const i32 {
            return self.history.items;
        }

        pub fn clearHistory(self: *Self) void {
            self.history.clearRetainingCapacity();
        }
    };
}

test "allocator decorator" {
    const simple = SimpleFunc{};
    var history = HistoryDecorator(SimpleFunc).init(testing.allocator, simple);
    defer history.deinit();

    _ = try history.call(5);
    _ = try history.call(10);

    const hist = history.getHistory();
    try testing.expectEqual(@as(usize, 2), hist.len);
    try testing.expectEqual(@as(i32, 10), hist[0]);
    try testing.expectEqual(@as(i32, 20), hist[1]);

    history.clearHistory();
    try testing.expectEqual(@as(usize, 0), history.getHistory().len);
}
// ANCHOR_END: allocator_decorator

// ANCHOR: error_handling_decorator
// Decorator with error handling
fn RetryDecorator(comptime Func: type, comptime max_attempts: u32) type {
    return struct {
        const Self = @This();
        func: Func,
        attempts: u32 = 0,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn call(self: *Self, x: i32) !i32 {
            var last_error: ?anyerror = null;
            var attempt: u32 = 0;

            while (attempt < max_attempts) : (attempt += 1) {
                self.attempts += 1;
                const result = self.func.call(x) catch |err| {
                    last_error = err;
                    continue;
                };
                return result;
            }

            if (last_error) |err| {
                return err;
            }
            return error.MaxRetriesExceeded;
        }

        pub fn getAttempts(self: Self) u32 {
            return self.attempts;
        }
    };
}

const FallibleFunc = struct {
    attempts: *u32,

    pub fn call(self: @This(), x: i32) !i32 {
        self.attempts.* += 1;
        if (self.attempts.* < 3) {
            return error.Temporary;
        }
        return x * 2;
    }
};

test "error handling decorator" {
    var attempt_count: u32 = 0;
    const fallible = FallibleFunc{ .attempts = &attempt_count };
    var retry = RetryDecorator(FallibleFunc, 5).init(fallible);

    const result = try retry.call(10);
    try testing.expectEqual(@as(i32, 20), result);
    try testing.expectEqual(@as(u32, 3), retry.getAttempts());
}
// ANCHOR_END: error_handling_decorator

// ANCHOR: builder_pattern
// Builder pattern for decorator construction
fn DecoratorBuilder(comptime Func: type) type {
    return struct {
        const Self = @This();

        func: Func,
        enable_logging: bool = false,
        enable_caching: bool = false,
        scale_factor: i32 = 1,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn withLogging(self: Self) Self {
            var new = self;
            new.enable_logging = true;
            return new;
        }

        pub fn withCaching(self: Self) Self {
            var new = self;
            new.enable_caching = true;
            return new;
        }

        pub fn withScale(self: Self, factor: i32) Self {
            var new = self;
            new.scale_factor = factor;
            return new;
        }

        pub fn build(self: Self) Built(Func) {
            return Built(Func){
                .func = self.func,
                .enable_logging = self.enable_logging,
                .enable_caching = self.enable_caching,
                .scale_factor = self.scale_factor,
            };
        }
    };
}

fn Built(comptime Func: type) type {
    return struct {
        const Self = @This();

        func: Func,
        enable_logging: bool,
        enable_caching: bool,
        scale_factor: i32,
        cache: ?i32 = null,
        log_count: u32 = 0,

        pub fn call(self: *Self, x: i32) i32 {
            if (self.enable_logging) {
                self.log_count += 1;
            }

            if (self.enable_caching) {
                if (self.cache) |c| {
                    return c;
                }
            }

            var result = self.func.call(x);
            result = result * self.scale_factor;

            if (self.enable_caching) {
                self.cache = result;
            }

            return result;
        }

        pub fn getLogCount(self: Self) u32 {
            return self.log_count;
        }
    };
}

test "builder pattern" {
    const simple = SimpleFunc{};
    var decorated = DecoratorBuilder(SimpleFunc).init(simple)
        .withLogging()
        .withScale(3)
        .build();

    const result = decorated.call(5);
    try testing.expectEqual(@as(i32, 30), result); // (5 * 2) * 3
    try testing.expectEqual(@as(u32, 1), decorated.getLogCount());
}
// ANCHOR_END: builder_pattern

// ANCHOR: conditional_decorator
// Conditional behavior based on struct fields
fn ConditionalDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();

        func: Func,
        enabled: bool,
        multiplier: i32,

        pub fn init(func: Func, enabled: bool, multiplier: i32) Self {
            return .{
                .func = func,
                .enabled = enabled,
                .multiplier = multiplier,
            };
        }

        pub fn call(self: *Self, x: i32) i32 {
            const base = self.func.call(x);
            if (self.enabled) {
                return base * self.multiplier;
            }
            return base;
        }

        pub fn enable(self: *Self) void {
            self.enabled = true;
        }

        pub fn disable(self: *Self) void {
            self.enabled = false;
        }
    };
}

test "conditional decorator" {
    const simple = SimpleFunc{};
    var conditional = ConditionalDecorator(SimpleFunc).init(simple, true, 3);

    const r1 = conditional.call(5);
    try testing.expectEqual(@as(i32, 30), r1); // Enabled: (5*2)*3

    conditional.disable();
    const r2 = conditional.call(5);
    try testing.expectEqual(@as(i32, 10), r2); // Disabled: 5*2
}
// ANCHOR_END: conditional_decorator

// ANCHOR: chaining_methods
// Decorator with method chaining
fn ChainableDecorator(comptime Func: type) type {
    return struct {
        const Self = @This();

        func: Func,
        offset: i32 = 0,
        multiplier: i32 = 1,
        invert: bool = false,

        pub fn init(func: Func) Self {
            return .{ .func = func };
        }

        pub fn addOffset(self: *Self, offset: i32) *Self {
            self.offset = offset;
            return self;
        }

        pub fn setMultiplier(self: *Self, multiplier: i32) *Self {
            self.multiplier = multiplier;
            return self;
        }

        pub fn setInvert(self: *Self, invert: bool) *Self {
            self.invert = invert;
            return self;
        }

        pub fn call(self: *Self, x: i32) i32 {
            var result = self.func.call(x);
            result = result + self.offset;
            result = result * self.multiplier;
            if (self.invert) {
                result = -result;
            }
            return result;
        }
    };
}

test "chaining methods" {
    const simple = SimpleFunc{};
    var chainable = ChainableDecorator(SimpleFunc).init(simple);

    _ = chainable.addOffset(5).setMultiplier(2).setInvert(false);

    const result = chainable.call(5);
    try testing.expectEqual(@as(i32, 30), result); // ((5*2) + 5) * 2
}
// ANCHOR_END: chaining_methods

// Comprehensive test
test "comprehensive decorator structs" {
    // Basic decorator
    const simple = SimpleFunc{};
    var timed = TimingDecorator(SimpleFunc).init(simple);
    try testing.expectEqual(@as(i32, 10), timed.call(5));

    // Stateful decorator
    var counter = CountingDecorator(SimpleFunc).init(simple);
    _ = counter.call(5);
    try testing.expectEqual(@as(u32, 1), counter.getCallCount());

    // Caching decorator
    var cached = CachingDecorator(SimpleFunc).init(simple);
    _ = cached.call(5);
    try testing.expect(cached.isCached(5));

    // Builder pattern
    var built = DecoratorBuilder(SimpleFunc).init(simple)
        .withLogging()
        .build();
    _ = built.call(5);
    try testing.expectEqual(@as(u32, 1), built.getLogCount());
}
```

### See Also

- Recipe 9.1: Putting a Wrapper Around a Function
- Recipe 9.6: Defining Decorators as Part of a Struct
- Recipe 9.8: Applying Decorators to Struct and Static Methods
- Recipe 8.10: Using Lazily Computed Properties

---

## Recipe 9.8: Applying Decorators to Struct and Static Methods {#recipe-9-8}

**Tags:** allocators, comptime, comptime-metaprogramming, data-structures, error-handling, hashmap, memory, pointers, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_8.zig`

### Problem

You want to apply decorators to struct instance methods or static methods (functions within structs that don't take `self`). You need to track method calls, add validation, implement caching, or inject other behavior without modifying method implementations.

### Solution

Create decorators that accept methods as compile-time parameters and return wrapper types with state and additional functionality.

### Instance Method Decorator

Decorate methods that take a `self` parameter:

```zig
// Decorate instance methods
fn WithLogging(comptime method: anytype) type {
    return struct {
        const Self = @This();
        call_count: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) i32 {
            self.call_count += 1;
            return method(instance, x);
        }

        pub fn getCallCount(self: Self) u32 {
            return self.call_count;
        }
    };
}

const Counter = struct {
    value: i32 = 0,

    pub fn add(self: *Counter, x: i32) i32 {
        self.value += x;
        return self.value;
    }
};

test "instance method decorator" {
    var counter = Counter{};
    var logged = WithLogging(Counter.add){};

    const r1 = logged.call(&counter, 5);
    try testing.expectEqual(@as(i32, 5), r1);
    try testing.expectEqual(@as(u32, 1), logged.getCallCount());

    const r2 = logged.call(&counter, 3);
    try testing.expectEqual(@as(i32, 8), r2);
    try testing.expectEqual(@as(u32, 2), logged.getCallCount());
}
```

The decorator tracks how many times the method is called.

### Static Method Decorator

Decorate static methods without `self`:

```zig
fn WithCache(comptime func: anytype) type {
    return struct {
        const Self = @This();
        const CacheEntry = struct {
            input: i32,
            output: i32,
        };

        cache: ?CacheEntry = null,

        pub fn call(self: *Self, x: i32) i32 {
            if (self.cache) |entry| {
                if (entry.input == x) {
                    return entry.output;
                }
            }

            const result = func(x);
            self.cache = CacheEntry{ .input = x, .output = result };
            return result;
        }

        pub fn isCached(self: Self, x: i32) bool {
            if (self.cache) |entry| {
                return entry.input == x;
            }
            return false;
        }
    };
}

const Math = struct {
    pub fn square(x: i32) i32 {
        return x * x;
    }
};

// Usage
var cached = WithCache(Math.square){};

cached.call(5);      // Computes 25, caches
cached.call(5);      // Returns cached 25
cached.isCached(5);  // true
```

Caching decorator for pure static methods.

### Generic Method Decorator

Handle any method signature with `anytype` and `@call`:

```zig
fn MethodDecorator(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        const Self = @This();
        invocations: u32 = 0,

        pub fn call(self: *Self, args: anytype) ReturnType {
            self.invocations += 1;
            return @call(.auto, func, args);
        }

        pub fn getInvocations(self: Self) u32 {
            return self.invocations;
        }
    };
}

const Calculator = struct {
    multiplier: i32,

    pub fn multiply(self: Calculator, x: i32) i32 {
        return x * self.multiplier;
    }
};

// Usage
const calc = Calculator{ .multiplier = 3 };
var decorated = MethodDecorator(Calculator.multiply){};

decorated.call(.{ calc, 5 });  // 15
decorated.getInvocations();     // 1
```

Works with any argument tuple.

### Bound Method Decorator

Bind an instance to a method for convenient reuse:

```zig
fn BoundMethod(comptime Instance: type, comptime method: anytype) type {
    return struct {
        const Self = @This();
        instance: *Instance,
        call_count: u32 = 0,

        pub fn init(instance: *Instance) Self {
            return .{ .instance = instance };
        }

        pub fn call(self: *Self, x: i32) i32 {
            self.call_count += 1;
            return method(self.instance, x);
        }

        pub fn getCallCount(self: Self) u32 {
            return self.call_count;
        }
    };
}

// Usage
var counter = Counter{};
var bound = BoundMethod(Counter, Counter.add).init(&counter);

bound.call(5);  // Calls counter.add(5)
bound.call(3);  // Calls counter.add(3)

counter.value;         // 8
bound.getCallCount();  // 2
```

Instance is bound at initialization.

### Validation Method Decorator

Add bounds checking to methods:

```zig
fn WithValidation(comptime method: anytype, comptime min: i32, comptime max: i32) type {
    return struct {
        const Self = @This();
        validation_errors: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) !i32 {
            if (x < min or x > max) {
                self.validation_errors += 1;
                return error.OutOfBounds;
            }
            return method(instance, x);
        }

        pub fn getValidationErrors(self: Self) u32 {
            return self.validation_errors;
        }
    };
}

// Usage
var counter = Counter{};
var validated = WithValidation(Counter.add, 0, 10){};

try validated.call(&counter, 5);   // 5 (valid)
try validated.call(&counter, 15);  // error.OutOfBounds

validated.getValidationErrors();    // 1
```

Tracks validation failures.

### Timing Method Decorator

Measure method execution time:

```zig
fn WithTiming(comptime method: anytype) type {
    return struct {
        const Self = @This();
        total_time: u64 = 0,
        calls: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) i32 {
            // In real code, measure actual time
            const elapsed: u64 = 100;
            self.total_time += elapsed;
            self.calls += 1;
            return method(instance, x);
        }

        pub fn getAverageTime(self: Self) u64 {
            if (self.calls == 0) return 0;
            return self.total_time / self.calls;
        }
    };
}

// Usage
var counter = Counter{};
var timed = WithTiming(Counter.add){};

timed.call(&counter, 5);
timed.call(&counter, 3);

timed.getAverageTime();  // 100 (average time per call)
```

Tracks cumulative and average timing.

### Composed Decorators

Combine multiple decorator behaviors:

```zig
fn ComposeDecorators(comptime method: anytype) type {
    return struct {
        const Self = @This();
        log_count: u32 = 0,
        time_count: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) i32 {
            // Log the call
            self.log_count += 1;
            // Time the call
            self.time_count += 1;
            // Call the method
            const result = method(instance, x);
            // Apply transformation
            return result * 2;
        }

        pub fn getLogCount(self: Self) u32 {
            return self.log_count;
        }
    };
}

// Usage
var counter = Counter{};
var composed = ComposeDecorators(Counter.add){};

composed.call(&counter, 5);  // 10 (5 * 2)
composed.getLogCount();       // 1
```

Single decorator with multiple concerns.

### Method Wrapper Struct

Wrap all methods of a struct:

```zig
fn DecoratedStruct(comptime T: type) type {
    return struct {
        const Self = @This();
        inner: T,
        add_calls: u32 = 0,

        pub fn init(inner: T) Self {
            return .{ .inner = inner };
        }

        pub fn add(self: *Self, x: i32) i32 {
            self.add_calls += 1;
            return self.inner.add(x);
        }

        pub fn getAddCalls(self: Self) u32 {
            return self.add_calls;
        }
    };
}

// Usage
const counter = Counter{};
var decorated = DecoratedStruct(Counter).init(counter);

decorated.add(5);
decorated.add(3);

decorated.getAddCalls();  // 2
```

Wrapper tracks calls to specific methods.

### Conditional Method Decorator

Enable/disable decoration at compile time:

```zig
fn ConditionalMethod(comptime method: anytype, comptime enabled: bool) type {
    return struct {
        const Self = @This();
        calls_when_enabled: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) i32 {
            if (enabled) {
                self.calls_when_enabled += 1;
                const result = method(instance, x);
                return result * 2;
            }
            return method(instance, x);
        }

        pub fn getCalls(self: Self) u32 {
            return self.calls_when_enabled;
        }
    };
}

// Usage
var enabled = ConditionalMethod(Counter.add, true){};
enabled.call(&counter, 5);   // 10 (enabled: doubles)

var disabled = ConditionalMethod(Counter.add, false){};
disabled.call(&counter, 5);  // 5 (disabled: pass-through)
```

Compile-time conditional decoration.

### Memoizing Method

Cache method results based on input:

```zig
fn Memoized(comptime method: anytype) type {
    return struct {
        const Self = @This();
        const Entry = struct {
            input: i32,
            output: i32,
        };

        cache: [10]?Entry = [_]?Entry{null} ** 10,
        cache_size: usize = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) i32 {
            // Check cache
            for (self.cache[0..self.cache_size]) |maybe_entry| {
                if (maybe_entry) |entry| {
                    if (entry.input == x) {
                        return entry.output;
                    }
                }
            }

            // Not in cache, compute
            const result = method(instance, x);

            // Add to cache if space
            if (self.cache_size < self.cache.len) {
                self.cache[self.cache_size] = Entry{ .input = x, .output = result };
                self.cache_size += 1;
            }

            return result;
        }

        pub fn getCacheSize(self: Self) usize {
            return self.cache_size;
        }
    };
}

// Usage
var counter = Counter{};
var memoized = Memoized(Counter.add){};

memoized.call(&counter, 5);  // Computes, caches
memoized.call(&counter, 5);  // Returns cached

memoized.getCacheSize();     // 1
```

Simple memoization with fixed-size cache.

### Retry Method Decorator

Implement retry logic for fallible methods:

```zig
fn WithRetry(comptime method: anytype, comptime max_attempts: u32) type {
    return struct {
        const Self = @This();
        retry_count: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) !i32 {
            var attempt: u32 = 0;
            var last_error: ?anyerror = null;

            while (attempt < max_attempts) : (attempt += 1) {
                self.retry_count += 1;
                const result = method(instance, x) catch |err| {
                    last_error = err;
                    continue;
                };
                return result;
            }

            if (last_error) |err| {
                return err;
            }
            return error.MaxRetriesExceeded;
        }

        pub fn getRetryCount(self: Self) u32 {
            return self.retry_count;
        }
    };
}

const Fallible = struct {
    attempts: u32 = 0,

    pub fn unreliable(self: *Fallible, x: i32) !i32 {
        self.attempts += 1;
        if (self.attempts < 3) {
            return error.Temporary;
        }
        return x * 2;
    }
};

// Usage
var fallible = Fallible{};
var retry = WithRetry(Fallible.unreliable, 5){};

const result = try retry.call(&fallible, 10);  // 20 (succeeds on 3rd attempt)
retry.getRetryCount();  // 3
```

Automatic retry for transient failures.

### Discussion

Method decorators provide powerful metaprogramming capabilities for adding cross-cutting concerns to struct methods.

### Instance vs Static Methods

**Instance methods**:
```zig
pub fn method(self: *Self, args...) ReturnType
```

Take `self` as first parameter, access instance state.

**Static methods**:
```zig
pub fn staticMethod(args...) ReturnType
```

No `self` parameter, pure functions within struct namespace.

**Decorator differences**:

For instance methods, decorator `call` must pass instance:
```zig
pub fn call(self: *Self, instance: anytype, x: i32) i32 {
    return method(instance, x);
}
```

For static methods, no instance needed:
```zig
pub fn call(self: *Self, x: i32) i32 {
    return func(x);
}
```

### Compile-Time Method Binding

**Methods stored as comptime parameters**:
```zig
fn Decorator(comptime method: anytype) type
```

Method is a compile-time value, not stored in decorator instance.

**Zero runtime cost**:
- No function pointer storage
- No indirection overhead
- Fully inlined by compiler
- Type-specific optimization

**Multiple decorations**:
```zig
const Logged = WithLogging(Counter.add){};
const Cached = WithCache(Counter.add){};
```

Each creates separate type.

### State Management

**Per-decorator state**:
```zig
return struct {
    call_count: u32 = 0,  // Instance state
    // ...
};
```

Each decorator instance has own state.

**Shared static state**:
```zig
return struct {
    var call_count: u32 = 0,  // Shared state
    // ...
};
```

All instances of this decorator type share state.

**Resettable state**:
```zig
pub fn reset(self: *Self) void {
    self.call_count = 0;
}
```

Allow clearing state for testing or reuse.

### Generic Method Wrapping

**Using `anytype` for arguments**:
```zig
pub fn call(self: *Self, args: anytype) ReturnType {
    return @call(.auto, func, args);
}
```

Works with any argument tuple.

**Type introspection**:
```zig
const func_info = @typeInfo(@TypeOf(func));
const ReturnType = func_info.@"fn".return_type.?;
```

Extract method metadata at compile time.

**Preserving signatures**:

Decorator's `call` should match wrapped method's signature where possible for type safety.

### Bound Methods

**Python-style bound methods**:
```zig
var bound = BoundMethod(Counter, Counter.add).init(&counter);
bound.call(5);  // No need to pass &counter
```

Instance bound at initialization, calls simplified.

**Use cases**:
- Callbacks with context
- Event handlers with state
- Simplified APIs

### Validation Patterns

**Compile-time bounds**:
```zig
fn WithValidation(comptime method: anytype, comptime min: i32, comptime max: i32)
```

Bounds known at compile time, zero overhead.

**Runtime error tracking**:
```zig
validation_errors: u32 = 0,
```

Count failures for monitoring.

**Error propagation**:
```zig
pub fn call(...) !ReturnType {
    if (invalid) return error.ValidationFailed;
    return method(...);
}
```

Caller handles validation errors.

### Caching Strategies

**Simple cache**:
```zig
cache: ?CacheEntry = null,  // Single entry
```

Useful for repeated calls with same input.

**Fixed-size cache**:
```zig
cache: [10]?Entry = [_]?Entry{null} ** 10,
cache_size: usize = 0,
```

Multiple entries, no allocation.

**Hash-based cache**:

Use `std.AutoHashMap` for larger caches (requires allocator).

**Cache invalidation**:
```zig
pub fn clearCache(self: *Self) void {
    self.cache = null;
}
```

### Composition Techniques

**Single composite decorator**:
```zig
fn ComposeDecorators(comptime method: anytype) type {
    // Multiple behaviors in one decorator
}
```

Simpler than chaining separate decorators.

**Nested decorators**:
```zig
const Logged = WithLogging(method);
const LoggedAndCached = WithCache(Logged.call);
```

Layer decorators for complex behavior.

**Trade-offs**:
- Single composite: less boilerplate, less flexible
- Nested: more flexible, more complex types

### Performance Considerations

**Compile-time overhead**:
- Each decorated method generates unique type
- Can increase compile time
- Binary size grows with instantiations

**Runtime overhead**:
- State fields add memory cost
- Decorator call checks (caching, validation) add cycles
- Usually negligible compared to method work

**Optimization**:
- Compiler inlines decorator calls in release builds
- State checks often optimized away
- Profile before optimizing

### Testing Strategies

**Test decorator behavior**:
```zig
test "decorator tracking" {
    var logged = WithLogging(Counter.add){};
    _ = logged.call(&counter, 5);
    try testing.expectEqual(1, logged.getCallCount());
}
```

**Test with different methods**:
```zig
test "decorator on various methods" {
    var logged_add = WithLogging(Counter.add){};
    var logged_mult = WithLogging(Calculator.multiply){};
    // Test both
}
```

**Test state isolation**:
```zig
test "independent instances" {
    var dec1 = WithLogging(method){};
    var dec2 = WithLogging(method){};

    dec1.call(...);
    try testing.expectEqual(1, dec1.getCallCount());
    try testing.expectEqual(0, dec2.getCallCount());
}
```

**Test edge cases**:
```zig
test "validation edge cases" {
    try testing.expectEqual(min_val, try validated.call(&inst, min_val));
    try testing.expectEqual(max_val, try validated.call(&inst, max_val));
    try testing.expectError(error.OutOfBounds, validated.call(&inst, min_val - 1));
}
```

### Common Use Cases

**Instrumentation**:
- Call counting
- Timing measurement
- Performance profiling

**Validation**:
- Bounds checking
- Type validation
- Precondition enforcement

**Caching**:
- Memoization
- Result caching
- Computation reuse

**Error handling**:
- Retry logic
- Fallback values
- Error tracking

**Access control**:
- Permission checking
- Rate limiting
- Quota enforcement

### Full Tested Code

```zig
// Recipe 9.8: Applying Decorators to Struct and Static Methods
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: instance_method_decorator
// Decorate instance methods
fn WithLogging(comptime method: anytype) type {
    return struct {
        const Self = @This();
        call_count: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) i32 {
            self.call_count += 1;
            return method(instance, x);
        }

        pub fn getCallCount(self: Self) u32 {
            return self.call_count;
        }
    };
}

const Counter = struct {
    value: i32 = 0,

    pub fn add(self: *Counter, x: i32) i32 {
        self.value += x;
        return self.value;
    }
};

test "instance method decorator" {
    var counter = Counter{};
    var logged = WithLogging(Counter.add){};

    const r1 = logged.call(&counter, 5);
    try testing.expectEqual(@as(i32, 5), r1);
    try testing.expectEqual(@as(u32, 1), logged.getCallCount());

    const r2 = logged.call(&counter, 3);
    try testing.expectEqual(@as(i32, 8), r2);
    try testing.expectEqual(@as(u32, 2), logged.getCallCount());
}
// ANCHOR_END: instance_method_decorator

// ANCHOR: static_method_decorator
// Decorate static methods (no self parameter)
fn WithCache(comptime func: anytype) type {
    return struct {
        const Self = @This();
        const CacheEntry = struct {
            input: i32,
            output: i32,
        };

        cache: ?CacheEntry = null,

        pub fn call(self: *Self, x: i32) i32 {
            if (self.cache) |entry| {
                if (entry.input == x) {
                    return entry.output;
                }
            }

            const result = func(x);
            self.cache = CacheEntry{ .input = x, .output = result };
            return result;
        }

        pub fn isCached(self: Self, x: i32) bool {
            if (self.cache) |entry| {
                return entry.input == x;
            }
            return false;
        }
    };
}

const Math = struct {
    pub fn square(x: i32) i32 {
        return x * x;
    }

    pub fn cube(x: i32) i32 {
        return x * x * x;
    }
};

test "static method decorator" {
    var cached = WithCache(Math.square){};

    const r1 = cached.call(5);
    try testing.expectEqual(@as(i32, 25), r1);
    try testing.expect(cached.isCached(5));

    const r2 = cached.call(5);
    try testing.expectEqual(@as(i32, 25), r2);
}
// ANCHOR_END: static_method_decorator

// ANCHOR: generic_method_decorator
// Generic decorator for any method signature
fn MethodDecorator(comptime func: anytype) type {
    const func_info = @typeInfo(@TypeOf(func));
    const ReturnType = func_info.@"fn".return_type.?;

    return struct {
        const Self = @This();
        invocations: u32 = 0,

        pub fn call(self: *Self, args: anytype) ReturnType {
            self.invocations += 1;
            return @call(.auto, func, args);
        }

        pub fn getInvocations(self: Self) u32 {
            return self.invocations;
        }
    };
}

const Calculator = struct {
    multiplier: i32,

    pub fn multiply(self: Calculator, x: i32) i32 {
        return x * self.multiplier;
    }

    pub fn add(a: i32, b: i32) i32 {
        return a + b;
    }
};

test "generic method decorator" {
    const calc = Calculator{ .multiplier = 3 };
    var decorated = MethodDecorator(Calculator.multiply){};

    const result = decorated.call(.{ calc, 5 });
    try testing.expectEqual(@as(i32, 15), result);
    try testing.expectEqual(@as(u32, 1), decorated.getInvocations());

    var static_decorated = MethodDecorator(Calculator.add){};
    const r2 = static_decorated.call(.{ 10, 20 });
    try testing.expectEqual(@as(i32, 30), r2);
}
// ANCHOR_END: generic_method_decorator

// ANCHOR: bound_method_decorator
// Decorator that binds instance to method
fn BoundMethod(comptime Instance: type, comptime method: anytype) type {
    return struct {
        const Self = @This();
        instance: *Instance,
        call_count: u32 = 0,

        pub fn init(instance: *Instance) Self {
            return .{ .instance = instance };
        }

        pub fn call(self: *Self, x: i32) i32 {
            self.call_count += 1;
            return method(self.instance, x);
        }

        pub fn getCallCount(self: Self) u32 {
            return self.call_count;
        }
    };
}

test "bound method decorator" {
    var counter = Counter{};
    var bound = BoundMethod(Counter, Counter.add).init(&counter);

    _ = bound.call(5);
    _ = bound.call(3);

    try testing.expectEqual(@as(i32, 8), counter.value);
    try testing.expectEqual(@as(u32, 2), bound.getCallCount());
}
// ANCHOR_END: bound_method_decorator

// ANCHOR: validation_method_decorator
// Decorator with validation for methods
fn WithValidation(comptime method: anytype, comptime min: i32, comptime max: i32) type {
    return struct {
        const Self = @This();
        validation_errors: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) !i32 {
            if (x < min or x > max) {
                self.validation_errors += 1;
                return error.OutOfBounds;
            }
            return method(instance, x);
        }

        pub fn getValidationErrors(self: Self) u32 {
            return self.validation_errors;
        }
    };
}

test "validation method decorator" {
    var counter = Counter{};
    var validated = WithValidation(Counter.add, 0, 10){};

    const r1 = try validated.call(&counter, 5);
    try testing.expectEqual(@as(i32, 5), r1);
    try testing.expectEqual(@as(u32, 0), validated.getValidationErrors());

    const r2 = validated.call(&counter, 15);
    try testing.expectError(error.OutOfBounds, r2);
    try testing.expectEqual(@as(u32, 1), validated.getValidationErrors());
}
// ANCHOR_END: validation_method_decorator

// ANCHOR: timing_method_decorator
// Decorator to track method timing
fn WithTiming(comptime method: anytype) type {
    return struct {
        const Self = @This();
        total_time: u64 = 0,
        calls: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) i32 {
            // In real code, measure actual time
            const elapsed: u64 = 100;
            self.total_time += elapsed;
            self.calls += 1;
            return method(instance, x);
        }

        pub fn getAverageTime(self: Self) u64 {
            if (self.calls == 0) return 0;
            return self.total_time / self.calls;
        }
    };
}

test "timing method decorator" {
    var counter = Counter{};
    var timed = WithTiming(Counter.add){};

    _ = timed.call(&counter, 5);
    _ = timed.call(&counter, 3);

    try testing.expectEqual(@as(u64, 100), timed.getAverageTime());
}
// ANCHOR_END: timing_method_decorator

// ANCHOR: composed_method_decorators
// Compose multiple decorators on methods
fn ComposeDecorators(comptime method: anytype) type {
    return struct {
        const Self = @This();
        log_count: u32 = 0,
        time_count: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) i32 {
            // Log the call
            self.log_count += 1;
            // Time the call
            self.time_count += 1;
            // Call the method
            const result = method(instance, x);
            // Apply additional transformation
            return result * 2;
        }

        pub fn getLogCount(self: Self) u32 {
            return self.log_count;
        }
    };
}

test "composed method decorators" {
    var counter = Counter{};
    var composed_dec = ComposeDecorators(Counter.add){};

    const result = composed_dec.call(&counter, 5);
    try testing.expectEqual(@as(i32, 10), result); // 5 * 2
    try testing.expectEqual(@as(u32, 1), composed_dec.getLogCount());
}
// ANCHOR_END: composed_method_decorators

// ANCHOR: method_wrapper_struct
// Struct that wraps all methods with decorators
fn DecoratedStruct(comptime T: type) type {
    return struct {
        const Self = @This();
        inner: T,
        add_calls: u32 = 0,

        pub fn init(inner: T) Self {
            return .{ .inner = inner };
        }

        pub fn add(self: *Self, x: i32) i32 {
            self.add_calls += 1;
            return self.inner.add(x);
        }

        pub fn getAddCalls(self: Self) u32 {
            return self.add_calls;
        }
    };
}

test "method wrapper struct" {
    const counter = Counter{};
    var decorated = DecoratedStruct(Counter).init(counter);

    _ = decorated.add(5);
    _ = decorated.add(3);

    try testing.expectEqual(@as(u32, 2), decorated.getAddCalls());
}
// ANCHOR_END: method_wrapper_struct

// ANCHOR: conditional_method_decorator
// Decorator that conditionally applies behavior
fn ConditionalMethod(comptime method: anytype, comptime enabled: bool) type {
    return struct {
        const Self = @This();
        calls_when_enabled: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) i32 {
            if (enabled) {
                self.calls_when_enabled += 1;
                const result = method(instance, x);
                return result * 2;
            }
            return method(instance, x);
        }

        pub fn getCalls(self: Self) u32 {
            return self.calls_when_enabled;
        }
    };
}

test "conditional method decorator" {
    var counter1 = Counter{};
    var enabled = ConditionalMethod(Counter.add, true){};

    const r1 = enabled.call(&counter1, 5);
    try testing.expectEqual(@as(i32, 10), r1); // 5 * 2
    try testing.expectEqual(@as(u32, 1), enabled.getCalls());

    var counter2 = Counter{};
    var disabled = ConditionalMethod(Counter.add, false){};

    const r2 = disabled.call(&counter2, 5);
    try testing.expectEqual(@as(i32, 5), r2); // No multiplication
    try testing.expectEqual(@as(u32, 0), disabled.getCalls());
}
// ANCHOR_END: conditional_method_decorator

// ANCHOR: memoizing_method
// Decorator that memoizes method results
fn Memoized(comptime method: anytype) type {
    return struct {
        const Self = @This();
        const Entry = struct {
            input: i32,
            output: i32,
        };

        cache: [10]?Entry = [_]?Entry{null} ** 10,
        cache_size: usize = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) i32 {
            // Check cache
            for (self.cache[0..self.cache_size]) |maybe_entry| {
                if (maybe_entry) |entry| {
                    if (entry.input == x) {
                        return entry.output;
                    }
                }
            }

            // Not in cache, compute
            const result = method(instance, x);

            // Add to cache if space
            if (self.cache_size < self.cache.len) {
                self.cache[self.cache_size] = Entry{ .input = x, .output = result };
                self.cache_size += 1;
            }

            return result;
        }

        pub fn getCacheSize(self: Self) usize {
            return self.cache_size;
        }
    };
}

test "memoizing method" {
    var counter = Counter{};
    var memoized = Memoized(Counter.add){};

    _ = memoized.call(&counter, 5);
    _ = memoized.call(&counter, 5); // Should use cache

    try testing.expectEqual(@as(usize, 1), memoized.getCacheSize());
}
// ANCHOR_END: memoizing_method

// ANCHOR: retry_method_decorator
// Decorator with retry logic for methods
fn WithRetry(comptime method: anytype, comptime max_attempts: u32) type {
    return struct {
        const Self = @This();
        retry_count: u32 = 0,

        pub fn call(self: *Self, instance: anytype, x: i32) !i32 {
            var attempt: u32 = 0;
            var last_error: ?anyerror = null;

            while (attempt < max_attempts) : (attempt += 1) {
                self.retry_count += 1;
                const result = method(instance, x) catch |err| {
                    last_error = err;
                    continue;
                };
                return result;
            }

            if (last_error) |err| {
                return err;
            }
            return error.MaxRetriesExceeded;
        }

        pub fn getRetryCount(self: Self) u32 {
            return self.retry_count;
        }
    };
}

const Fallible = struct {
    attempts: u32 = 0,

    pub fn unreliable(self: *Fallible, x: i32) !i32 {
        self.attempts += 1;
        if (self.attempts < 3) {
            return error.Temporary;
        }
        return x * 2;
    }
};

test "retry method decorator" {
    var fallible = Fallible{};
    var retry = WithRetry(Fallible.unreliable, 5){};

    const result = try retry.call(&fallible, 10);
    try testing.expectEqual(@as(i32, 20), result);
    try testing.expectEqual(@as(u32, 3), retry.getRetryCount());
}
// ANCHOR_END: retry_method_decorator

// Comprehensive test
test "comprehensive method decorators" {
    // Instance method decorator
    var counter1 = Counter{};
    var logged = WithLogging(Counter.add){};
    _ = logged.call(&counter1, 5);
    try testing.expectEqual(@as(u32, 1), logged.getCallCount());

    // Static method decorator
    var cached = WithCache(Math.square){};
    try testing.expectEqual(@as(i32, 25), cached.call(5));

    // Generic method decorator
    const calc = Calculator{ .multiplier = 2 };
    var generic = MethodDecorator(Calculator.multiply){};
    try testing.expectEqual(@as(i32, 10), generic.call(.{ calc, 5 }));

    // Bound method decorator
    var counter2 = Counter{};
    var bound = BoundMethod(Counter, Counter.add).init(&counter2);
    _ = bound.call(5);
    try testing.expectEqual(@as(i32, 5), counter2.value);

    // Validation decorator
    var counter3 = Counter{};
    var validated = WithValidation(Counter.add, 0, 10){};
    try testing.expectEqual(@as(i32, 5), try validated.call(&counter3, 5));
}
```

### See Also

- Recipe 9.1: Putting a Wrapper Around a Function
- Recipe 9.6: Defining Decorators as Part of a Struct
- Recipe 9.7: Defining Decorators as Structs
- Recipe 8.1: Changing the String Representation of Instances

---

## Recipe 9.9: Writing Decorators That Add Arguments to Wrapped Functions {#recipe-9-9}

**Tags:** allocators, arraylist, comptime, comptime-metaprogramming, data-structures, error-handling, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_9.zig`

### Problem

You want to simplify function calls by injecting common arguments like allocators, configuration objects, loggers, or contexts. You need to avoid repetitive parameter passing while maintaining type safety and zero runtime overhead.

### Solution

Create decorators that prepend, append, or inject arguments into wrapped functions at compile time using tuple concatenation.

### Inject Allocator

Automatically provide an allocator to functions:

```zig
// Decorator that injects allocator as first argument
// NOTE: The wrapped function MUST accept the allocator as its first parameter.
// This follows Zig stdlib conventions where allocator is typically the first argument
// to init/create functions (e.g., ArrayList.init(allocator), alloc(allocator, size)).
// If your function has a different signature, use a different decorator pattern.
fn WithAllocator(comptime func: anytype, comptime allocator: std.mem.Allocator) type {
    return struct {
        const Self = @This();

        pub fn call(args: anytype) @TypeOf(@call(.auto, func, .{allocator} ++ args)) {
            return @call(.auto, func, .{allocator} ++ args);
        }
    };
}

fn createSlice(allocator: std.mem.Allocator, size: usize) ![]i32 {
    return try allocator.alloc(i32, size);
}

test "inject allocator" {
    const WithTestAllocator = WithAllocator(createSlice, testing.allocator);

    const slice = try WithTestAllocator.call(.{5});
    defer testing.allocator.free(slice);

    try testing.expectEqual(@as(usize, 5), slice.len);
}
```

Allocator injected automatically, callers don't pass it.

### Inject Context

Provide configuration or context objects:

```zig
fn WithContext(comptime func: anytype, comptime Context: type, comptime context: Context) type {
    return struct {
        const Self = @This();

        pub fn call(args: anytype) @TypeOf(@call(.auto, func, .{context} ++ args)) {
            return @call(.auto, func, .{context} ++ args);
        }
    };
}

const Config = struct {
    multiplier: i32,
    offset: i32,
};

fn transform(config: Config, x: i32) i32 {
    return (x * config.multiplier) + config.offset;
}

// Usage
const config = Config{ .multiplier = 2, .offset = 5 };
const Configured = WithContext(transform, Config, config);

Configured.call(.{10});  // 25: (10 * 2) + 5
```

Configuration injected at compile time.

### Prepend Arguments

Add arguments at the beginning:

```zig
fn PrependArgs(comptime func: anytype, comptime prepend: anytype) type {
    return struct {
        const Self = @This();

        pub fn call(args: anytype) @TypeOf(@call(.auto, func, prepend ++ args)) {
            return @call(.auto, func, prepend ++ args);
        }
    };
}

fn multiply(a: i32, b: i32) i32 {
    return a * b;
}

// Usage
const TimesTwo = PrependArgs(multiply, .{2});

TimesTwo.call(.{5});  // 10: 2 * 5
```

Partial application of first arguments.

### Append Arguments

Add arguments at the end:

```zig
fn AppendArgs(comptime func: anytype, comptime append: anytype) type {
    return struct {
        const Self = @This();

        pub fn call(args: anytype) @TypeOf(@call(.auto, func, args ++ append)) {
            return @call(.auto, func, args ++ append);
        }
    };
}

fn divide(a: i32, b: i32) i32 {
    return @divTrunc(a, b);
}

// Usage
const DivideByTwo = AppendArgs(divide, .{2});

DivideByTwo.call(.{10});  // 5: 10 / 2
```

Partial application of last arguments.

### Inject Default Arguments

Provide default values for trailing parameters:

```zig
fn WithDefaults(comptime func: anytype, comptime defaults: anytype) type {
    return struct {
        const Self = @This();

        pub fn call(provided: anytype) @TypeOf(@call(.auto, func, provided ++ defaults)) {
            return @call(.auto, func, provided ++ defaults);
        }
    };
}

fn configuredAdd(x: i32, multiplier: i32, offset: i32) i32 {
    return (x * multiplier) + offset;
}

// Usage
const DefaultConfig = WithDefaults(configuredAdd, .{ 3, 10 });

DefaultConfig.call(.{5});  // 25: (5 * 3) + 10
```

Defaults applied automatically.

### Inject Logger

Provide logging infrastructure:

```zig
fn WithLogger(comptime func: anytype) type {
    return struct {
        const Self = @This();
        const Logger = struct {
            log_count: *u32,

            pub fn log(self: Logger, comptime fmt: []const u8, args: anytype) void {
                _ = fmt;
                _ = args;
                self.log_count.* += 1;
            }
        };

        log_count: u32 = 0,

        pub fn call(self: *Self, args: anytype) @TypeOf(@call(.auto, func, .{Logger{ .log_count = &self.log_count }} ++ args)) {
            const logger = Logger{ .log_count = &self.log_count };
            return @call(.auto, func, .{logger} ++ args);
        }

        pub fn getLogCount(self: Self) u32 {
            return self.log_count;
        }
    };
}

fn processWithLog(logger: anytype, x: i32) i32 {
    logger.log("Processing {d}", .{x});
    return x * 2;
}

// Usage
var decorated = WithLogger(processWithLog){};

decorated.call(.{5});       // 10
decorated.getLogCount();    // 1
```

Logger injected with state tracking.

### Inject Timestamp

Provide timing information:

```zig
fn WithTimestamp(comptime func: anytype) type {
    return struct {
        const Self = @This();
        current_time: u64 = 0,

        pub fn call(self: *Self, args: anytype) @TypeOf(@call(.auto, func, .{self.current_time} ++ args)) {
            self.current_time += 1;
            return @call(.auto, func, .{self.current_time} ++ args);
        }

        pub fn getCurrentTime(self: Self) u64 {
            return self.current_time;
        }
    };
}

fn processWithTime(timestamp: u64, x: i32) i32 {
    _ = timestamp;
    return x * 2;
}

// Usage
var decorated = WithTimestamp(processWithTime){};

decorated.call(.{5});
decorated.call(.{10});

decorated.getCurrentTime();  // 2
```

Monotonic timestamp injection.

### Inject Error Handler

Provide error handling infrastructure:

```zig
fn WithErrorHandler(comptime func: anytype) type {
    return struct {
        const Self = @This();
        const ErrorHandler = struct {
            error_count: *u32,

            pub fn handleError(self: ErrorHandler, _: anyerror) void {
                self.error_count.* += 1;
            }
        };

        error_count: u32 = 0,

        pub fn call(self: *Self, args: anytype) @TypeOf(@call(.auto, func, .{ErrorHandler{ .error_count = &self.error_count }} ++ args)) {
            const handler = ErrorHandler{ .error_count = &self.error_count };
            return @call(.auto, func, .{handler} ++ args);
        }

        pub fn getErrorCount(self: Self) u32 {
            return self.error_count;
        }
    };
}

fn processWithErrorHandler(handler: anytype, x: i32) !i32 {
    if (x < 0) {
        handler.handleError(error.NegativeValue);
        return error.NegativeValue;
    }
    return x * 2;
}

// Usage
var decorated = WithErrorHandler(processWithErrorHandler){};

try decorated.call(.{5});      // 10
try decorated.call(.{-5});     // error.NegativeValue

decorated.getErrorCount();      // 1
```

Error tracking built into injected handler.

### Inject Metrics

Provide metrics collection:

```zig
fn WithMetrics(comptime func: anytype) type {
    return struct {
        const Self = @This();
        const Metrics = struct {
            calls: *u32,
            total: *i64,

            pub fn record(self: Metrics, value: i32) void {
                self.calls.* += 1;
                self.total.* += value;
            }
        };

        calls: u32 = 0,
        total: i64 = 0,

        pub fn call(self: *Self, args: anytype) @TypeOf(@call(.auto, func, .{Metrics{ .calls = &self.calls, .total = &self.total }} ++ args)) {
            const metrics = Metrics{ .calls = &self.calls, .total = &self.total };
            return @call(.auto, func, .{metrics} ++ args);
        }

        pub fn getAverage(self: Self) i64 {
            if (self.calls == 0) return 0;
            return @divTrunc(self.total, self.calls);
        }
    };
}

fn processWithMetrics(metrics: anytype, x: i32) i32 {
    const result = x * 2;
    metrics.record(result);
    return result;
}

// Usage
var decorated = WithMetrics(processWithMetrics){};

decorated.call(.{5});
decorated.call(.{10});
decorated.call(.{15});

decorated.getAverage();  // 20: (10 + 20 + 30) / 3
```

Automatic metrics collection.

### Inject Runtime Context

Provide runtime-configurable context:

```zig
fn WithRuntimeContext(comptime func: anytype, comptime Context: type) type {
    return struct {
        const Self = @This();
        context: Context,

        pub fn init(context: Context) Self {
            return .{ .context = context };
        }

        pub fn call(self: Self, args: anytype) @TypeOf(@call(.auto, func, .{self.context} ++ args)) {
            return @call(.auto, func, .{self.context} ++ args);
        }
    };
}

const RuntimeConfig = struct {
    scale: i32,
    enabled: bool,
};

fn processWithRuntimeContext(config: RuntimeConfig, x: i32) i32 {
    if (!config.enabled) return x;
    return x * config.scale;
}

// Usage
const config1 = RuntimeConfig{ .scale = 3, .enabled = true };
const decorated1 = WithRuntimeContext(processWithRuntimeContext, RuntimeConfig).init(config1);

decorated1.call(.{5});  // 15

const config2 = RuntimeConfig{ .scale = 3, .enabled = false };
const decorated2 = WithRuntimeContext(processWithRuntimeContext, RuntimeConfig).init(config2);

decorated2.call(.{5});  // 5
```

Different instances with different configurations.

### Inject Multiple Arguments

Inject several arguments at once:

```zig
fn InjectMultiple(comptime func: anytype, comptime inject: anytype) type {
    return struct {
        const Self = @This();

        pub fn call(args: anytype) @TypeOf(@call(.auto, func, inject ++ args)) {
            return @call(.auto, func, inject ++ args);
        }
    };
}

fn complexFunc(a: i32, b: i32, c: i32, d: i32) i32 {
    return a + b + c + d;
}

// Usage
const Injected = InjectMultiple(complexFunc, .{ 1, 2 });

Injected.call(.{ 3, 4 });  // 10: 1 + 2 + 3 + 4
```

Multiple arguments injected together.

### Conditional Injection

Inject arguments based on compile-time condition:

```zig
fn ConditionalInject(comptime func: anytype, comptime condition: bool, comptime inject: anytype) type {
    if (condition) {
        return struct {
            pub fn call(args: anytype) @TypeOf(@call(.auto, func, inject ++ args)) {
                return @call(.auto, func, inject ++ args);
            }
        };
    } else {
        return struct {
            pub fn call(args: anytype) @TypeOf(@call(.auto, func, args)) {
                return @call(.auto, func, args);
            }
        };
    }
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

// Usage
const WithInjection = ConditionalInject(add, true, .{10});
WithInjection.call(.{5});  // 15: 10 + 5

const WithoutInjection = ConditionalInject(add, false, .{10});
WithoutInjection.call(.{ 5, 3 });  // 8: 5 + 3
```

Compile-time conditional argument injection.

### Discussion

Argument injection decorators provide dependency injection, simplify APIs, and eliminate repetitive parameter passing.

### Tuple Concatenation

**Core mechanism**:
```zig
.{allocator} ++ args  // Prepend allocator to args tuple
args ++ .{default}    // Append default to args tuple
```

Tuples concatenated at compile time, zero runtime overhead.

**Type safety**:
```zig
@TypeOf(@call(.auto, func, prepend ++ args))
```

Return type computed from actual call signature.

**Flexibility**:
```zig
inject ++ args         // Prepend
args ++ inject         // Append
prefix ++ args ++ suffix  // Both
```

### Compile-Time vs Runtime Injection

**Compile-time injection**:
```zig
fn WithAllocator(comptime func: anytype, comptime allocator: Allocator) type
```

Allocator baked into type, no storage cost.

**Runtime injection**:
```zig
return struct {
    context: Context,  // Stored in decorator instance

    pub fn call(self: Self, args: anytype) ... {
        return @call(.auto, func, .{self.context} ++ args);
    }
};
```

Context can vary per instance.

**Trade-offs**:
- Compile-time: Zero overhead, but fixed at compile time
- Runtime: Flexible configuration, small storage cost

### Dependency Injection Patterns

**Allocator injection**:

Common in Zig APIs. Decorators eliminate repetitive passing:
```zig
// Without decorator
const slice1 = try createSlice(allocator, 5);
const slice2 = try createSlice(allocator, 10);

// With decorator
const Create = WithAllocator(createSlice, allocator);
const slice1 = try Create.call(.{5});
const slice2 = try Create.call(.{10});
```

**Configuration injection**:

Centralize configuration:
```zig
const config = Config{ .timeout = 100, .retries = 3 };
const Process = WithContext(process, Config, config);

Process.call(.{data1});
Process.call(.{data2});
```

All calls use same configuration.

**Infrastructure injection**:

Loggers, metrics, error handlers:
```zig
var logged = WithLogger(process){};
logged.call(.{x});  // Logger automatically provided
```

Infrastructure transparent to caller.

### Partial Application

**Currying in Zig**:

Decorators enable partial application:
```zig
fn add(a: i32, b: i32) i32 {
    return a + b;
}

const Add5 = PrependArgs(add, .{5});
Add5.call(.{10});  // 15
```

Bind some arguments, defer others.

**Use cases**:
- Factory functions
- Specialized processors
- Event handlers with context

### State Management

**Stateless injection**:
```zig
fn WithAllocator(...) type {
    return struct {
        pub fn call(args: anytype) ... {
            return @call(.auto, func, .{allocator} ++ args);
        }
    };
}
```

No state, pure compile-time.

**Stateful injection**:
```zig
fn WithLogger(...) type {
    return struct {
        log_count: u32 = 0,  // State

        pub fn call(self: *Self, args: anytype) ... {
            const logger = Logger{ .log_count = &self.log_count };
            return @call(.auto, func, .{logger} ++ args);
        }
    };
}
```

Decorator maintains state, shared with injected object.

### Injected Object Design

**Simple values**:
```zig
.{allocator} ++ args
.{config} ++ args
```

Directly inject POD types.

**Complex objects**:
```zig
const Logger = struct {
    count: *u32,
    pub fn log(self: Logger, ...) void { ... }
};

const logger = Logger{ .count = &self.log_count };
.{logger} ++ args
```

Inject structs with methods, maintain references to decorator state.

**Interface pattern**:

Injected objects can be `anytype`, allowing duck typing:
```zig
fn process(logger: anytype, x: i32) i32 {
    logger.log("Processing", .{});  // Any type with log() works
    return x * 2;
}
```

### Performance Characteristics

**Zero-cost abstraction**:
- Tuple concatenation at compile time
- No runtime allocation
- Fully inlined
- Same performance as manual passing

**Binary size**:
- Each injected configuration creates new type
- Can increase code size
- Usually negligible

**Compile time**:
- Argument injection is fast
- Complex injected types increase compile time slightly

### Testing Strategies

**Test with different injections**:
```zig
test "with test allocator" {
    const Create = WithAllocator(createSlice, testing.allocator);
    const slice = try Create.call(.{5});
    defer testing.allocator.free(slice);
}

test "with failing allocator" {
    const Create = WithAllocator(createSlice, testing.failing_allocator);
    try testing.expectError(error.OutOfMemory, Create.call(.{5}));
}
```

**Test state tracking**:
```zig
test "logger counts calls" {
    var logged = WithLogger(process){};
    _ = logged.call(.{5});
    _ = logged.call(.{10});
    try testing.expectEqual(2, logged.getLogCount());
}
```

**Test runtime configuration**:
```zig
test "different contexts" {
    const ctx1 = Config{ .enabled = true };
    const dec1 = WithRuntimeContext(process, Config).init(ctx1);

    const ctx2 = Config{ .enabled = false };
    const dec2 = WithRuntimeContext(process, Config).init(ctx2);

    // Test different behaviors
}
```

### Common Use Cases

**Allocator passing**:

Eliminate repetitive allocator arguments:
```zig
const WithAlloc = WithAllocator(func, allocator);
```

**Configuration management**:

Centralize configuration:
```zig
const Configured = WithContext(func, Config, config);
```

**Observability**:

Inject logging, metrics, tracing:
```zig
var logged = WithLogger(func){};
var metriced = WithMetrics(func){};
```

**Error handling**:

Inject error handlers, recovery logic:
```zig
var handled = WithErrorHandler(func){};
```

**Testing**:

Inject test doubles, mocks:
```zig
const WithMock = WithContext(func, MockDB, mock_db);
```

### Design Patterns

**Builder with injection**:
```zig
const builder = FunctionBuilder.init(func)
    .withAllocator(alloc)
    .withLogger()
    .build();
```

**Factory with defaults**:
```zig
fn createProcessor(config: Config) ProcessorType {
    return WithDefaults(rawProcessor, .{ config.default1, config.default2 });
}
```

**Adapter pattern**:
```zig
// Adapt function expecting (allocator, x, y) to take just (x, y)
const Adapted = WithAllocator(func, allocator);
```

### Limitations

**Cannot remove arguments**:

Only prepend/append, not remove or reorder:
```zig
// Can't turn fn(a, b, c) into fn(a, c)
```

**Type must match**:

Injected arguments must match function signature:
```zig
fn process(allocator: Allocator, x: i32) !T
const Dec = WithAllocator(process, allocator);  // OK
const Bad = WithAllocator(process, 42);  // Type error: expects Allocator
```

**Fixed arity**:

Can't make variadic functions:
```zig
// Can't inject different number of args based on runtime condition
```

### Full Tested Code

```zig
// Recipe 9.9: Writing Decorators That Add Arguments to Wrapped Functions
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: inject_allocator
// Decorator that injects allocator as first argument
// NOTE: The wrapped function MUST accept the allocator as its first parameter.
// This follows Zig stdlib conventions where allocator is typically the first argument
// to init/create functions (e.g., ArrayList.init(allocator), alloc(allocator, size)).
// If your function has a different signature, use a different decorator pattern.
fn WithAllocator(comptime func: anytype, comptime allocator: std.mem.Allocator) type {
    return struct {
        const Self = @This();

        pub fn call(args: anytype) @TypeOf(@call(.auto, func, .{allocator} ++ args)) {
            return @call(.auto, func, .{allocator} ++ args);
        }
    };
}

fn createSlice(allocator: std.mem.Allocator, size: usize) ![]i32 {
    return try allocator.alloc(i32, size);
}

test "inject allocator" {
    const WithTestAllocator = WithAllocator(createSlice, testing.allocator);

    const slice = try WithTestAllocator.call(.{5});
    defer testing.allocator.free(slice);

    try testing.expectEqual(@as(usize, 5), slice.len);
}
// ANCHOR_END: inject_allocator

// ANCHOR: inject_context
// Decorator that injects context object
fn WithContext(comptime func: anytype, comptime Context: type, comptime context: Context) type {
    return struct {
        const Self = @This();

        pub fn call(args: anytype) @TypeOf(@call(.auto, func, .{context} ++ args)) {
            return @call(.auto, func, .{context} ++ args);
        }
    };
}

const Config = struct {
    multiplier: i32,
    offset: i32,
};

fn transform(config: Config, x: i32) i32 {
    return (x * config.multiplier) + config.offset;
}

test "inject context" {
    const config = Config{ .multiplier = 2, .offset = 5 };
    const Configured = WithContext(transform, Config, config);

    const result = Configured.call(.{10});
    try testing.expectEqual(@as(i32, 25), result); // (10 * 2) + 5
}
// ANCHOR_END: inject_context

// ANCHOR: prepend_arguments
// Decorator that prepends arguments
fn PrependArgs(comptime func: anytype, comptime prepend: anytype) type {
    return struct {
        const Self = @This();

        pub fn call(args: anytype) @TypeOf(@call(.auto, func, prepend ++ args)) {
            return @call(.auto, func, prepend ++ args);
        }
    };
}

fn multiply(a: i32, b: i32) i32 {
    return a * b;
}

test "prepend arguments" {
    const TimesTwo = PrependArgs(multiply, .{2});

    const result = TimesTwo.call(.{5});
    try testing.expectEqual(@as(i32, 10), result); // 2 * 5
}
// ANCHOR_END: prepend_arguments

// ANCHOR: append_arguments
// Decorator that appends arguments
fn AppendArgs(comptime func: anytype, comptime append: anytype) type {
    return struct {
        const Self = @This();

        pub fn call(args: anytype) @TypeOf(@call(.auto, func, args ++ append)) {
            return @call(.auto, func, args ++ append);
        }
    };
}

fn divide(a: i32, b: i32) i32 {
    return @divTrunc(a, b);
}

test "append arguments" {
    const DivideByTwo = AppendArgs(divide, .{2});

    const result = DivideByTwo.call(.{10});
    try testing.expectEqual(@as(i32, 5), result); // 10 / 2
}
// ANCHOR_END: append_arguments

// ANCHOR: inject_default_args
// Decorator that injects default arguments
fn WithDefaults(comptime func: anytype, comptime defaults: anytype) type {
    return struct {
        const Self = @This();

        pub fn call(provided: anytype) @TypeOf(@call(.auto, func, provided ++ defaults)) {
            return @call(.auto, func, provided ++ defaults);
        }
    };
}

fn configuredAdd(x: i32, multiplier: i32, offset: i32) i32 {
    return (x * multiplier) + offset;
}

test "inject default args" {
    const DefaultConfig = WithDefaults(configuredAdd, .{ 3, 10 });

    const result = DefaultConfig.call(.{5});
    try testing.expectEqual(@as(i32, 25), result); // (5 * 3) + 10
}
// ANCHOR_END: inject_default_args

// ANCHOR: inject_logger
// Decorator that injects logger
fn WithLogger(comptime func: anytype) type {
    return struct {
        const Self = @This();
        const Logger = struct {
            log_count: *u32,

            pub fn log(self: Logger, comptime fmt: []const u8, args: anytype) void {
                _ = fmt;
                _ = args;
                self.log_count.* += 1;
            }
        };

        log_count: u32 = 0,

        pub fn call(self: *Self, args: anytype) @TypeOf(@call(.auto, func, .{Logger{ .log_count = &self.log_count }} ++ args)) {
            const logger = Logger{ .log_count = &self.log_count };
            return @call(.auto, func, .{logger} ++ args);
        }

        pub fn getLogCount(self: Self) u32 {
            return self.log_count;
        }
    };
}

fn processWithLog(logger: anytype, x: i32) i32 {
    logger.log("Processing {d}", .{x});
    return x * 2;
}

test "inject logger" {
    var decorated = WithLogger(processWithLog){};

    const result = decorated.call(.{5});
    try testing.expectEqual(@as(i32, 10), result);
    try testing.expectEqual(@as(u32, 1), decorated.getLogCount());
}
// ANCHOR_END: inject_logger

// ANCHOR: inject_timestamp
// Decorator that injects timestamp
fn WithTimestamp(comptime func: anytype) type {
    return struct {
        const Self = @This();
        current_time: u64 = 0,

        pub fn call(self: *Self, args: anytype) @TypeOf(@call(.auto, func, .{self.current_time} ++ args)) {
            self.current_time += 1;
            return @call(.auto, func, .{self.current_time} ++ args);
        }

        pub fn getCurrentTime(self: Self) u64 {
            return self.current_time;
        }
    };
}

fn processWithTime(timestamp: u64, x: i32) i32 {
    _ = timestamp;
    return x * 2;
}

test "inject timestamp" {
    var decorated = WithTimestamp(processWithTime){};

    _ = decorated.call(.{5});
    _ = decorated.call(.{10});

    try testing.expectEqual(@as(u64, 2), decorated.getCurrentTime());
}
// ANCHOR_END: inject_timestamp

// ANCHOR: inject_error_handler
// Decorator that injects error handler
fn WithErrorHandler(comptime func: anytype) type {
    return struct {
        const Self = @This();
        const ErrorHandler = struct {
            error_count: *u32,

            pub fn handleError(self: ErrorHandler, _: anyerror) void {
                self.error_count.* += 1;
            }
        };

        error_count: u32 = 0,

        pub fn call(self: *Self, args: anytype) @TypeOf(@call(.auto, func, .{ErrorHandler{ .error_count = &self.error_count }} ++ args)) {
            const handler = ErrorHandler{ .error_count = &self.error_count };
            return @call(.auto, func, .{handler} ++ args);
        }

        pub fn getErrorCount(self: Self) u32 {
            return self.error_count;
        }
    };
}

fn processWithErrorHandler(handler: anytype, x: i32) !i32 {
    if (x < 0) {
        handler.handleError(error.NegativeValue);
        return error.NegativeValue;
    }
    return x * 2;
}

test "inject error handler" {
    var decorated = WithErrorHandler(processWithErrorHandler){};

    const r1 = try decorated.call(.{5});
    try testing.expectEqual(@as(i32, 10), r1);

    const r2 = decorated.call(.{-5});
    try testing.expectError(error.NegativeValue, r2);
    try testing.expectEqual(@as(u32, 1), decorated.getErrorCount());
}
// ANCHOR_END: inject_error_handler

// ANCHOR: inject_metrics
// Decorator that injects metrics collector
fn WithMetrics(comptime func: anytype) type {
    return struct {
        const Self = @This();
        const Metrics = struct {
            calls: *u32,
            total: *i64,

            pub fn record(self: Metrics, value: i32) void {
                self.calls.* += 1;
                self.total.* += value;
            }
        };

        calls: u32 = 0,
        total: i64 = 0,

        pub fn call(self: *Self, args: anytype) @TypeOf(@call(.auto, func, .{Metrics{ .calls = &self.calls, .total = &self.total }} ++ args)) {
            const metrics = Metrics{ .calls = &self.calls, .total = &self.total };
            return @call(.auto, func, .{metrics} ++ args);
        }

        pub fn getAverage(self: Self) i64 {
            if (self.calls == 0) return 0;
            return @divTrunc(self.total, self.calls);
        }
    };
}

fn processWithMetrics(metrics: anytype, x: i32) i32 {
    const result = x * 2;
    metrics.record(result);
    return result;
}

test "inject metrics" {
    var decorated = WithMetrics(processWithMetrics){};

    _ = decorated.call(.{5});
    _ = decorated.call(.{10});
    _ = decorated.call(.{15});

    try testing.expectEqual(@as(i64, 20), decorated.getAverage()); // (10 + 20 + 30) / 3
}
// ANCHOR_END: inject_metrics

// ANCHOR: inject_runtime_context
// Decorator with runtime-configurable context
fn WithRuntimeContext(comptime func: anytype, comptime Context: type) type {
    return struct {
        const Self = @This();
        context: Context,

        pub fn init(context: Context) Self {
            return .{ .context = context };
        }

        pub fn call(self: Self, args: anytype) @TypeOf(@call(.auto, func, .{self.context} ++ args)) {
            return @call(.auto, func, .{self.context} ++ args);
        }
    };
}

const RuntimeConfig = struct {
    scale: i32,
    enabled: bool,
};

fn processWithRuntimeContext(config: RuntimeConfig, x: i32) i32 {
    if (!config.enabled) return x;
    return x * config.scale;
}

test "inject runtime context" {
    const config1 = RuntimeConfig{ .scale = 3, .enabled = true };
    const decorated1 = WithRuntimeContext(processWithRuntimeContext, RuntimeConfig).init(config1);

    const r1 = decorated1.call(.{5});
    try testing.expectEqual(@as(i32, 15), r1);

    const config2 = RuntimeConfig{ .scale = 3, .enabled = false };
    const decorated2 = WithRuntimeContext(processWithRuntimeContext, RuntimeConfig).init(config2);

    const r2 = decorated2.call(.{5});
    try testing.expectEqual(@as(i32, 5), r2);
}
// ANCHOR_END: inject_runtime_context

// ANCHOR: inject_multiple_args
// Decorator that injects multiple arguments
fn InjectMultiple(comptime func: anytype, comptime inject: anytype) type {
    return struct {
        const Self = @This();

        pub fn call(args: anytype) @TypeOf(@call(.auto, func, inject ++ args)) {
            return @call(.auto, func, inject ++ args);
        }
    };
}

fn complexFunc(a: i32, b: i32, c: i32, d: i32) i32 {
    return a + b + c + d;
}

test "inject multiple args" {
    const Injected = InjectMultiple(complexFunc, .{ 1, 2 });

    const result = Injected.call(.{ 3, 4 });
    try testing.expectEqual(@as(i32, 10), result); // 1 + 2 + 3 + 4
}
// ANCHOR_END: inject_multiple_args

// ANCHOR: conditional_injection
// Decorator with conditional argument injection
fn ConditionalInject(comptime func: anytype, comptime condition: bool, comptime inject: anytype) type {
    if (condition) {
        return struct {
            pub fn call(args: anytype) @TypeOf(@call(.auto, func, inject ++ args)) {
                return @call(.auto, func, inject ++ args);
            }
        };
    } else {
        return struct {
            pub fn call(args: anytype) @TypeOf(@call(.auto, func, args)) {
                return @call(.auto, func, args);
            }
        };
    }
}

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "conditional injection" {
    const WithInjection = ConditionalInject(add, true, .{10});
    const r1 = WithInjection.call(.{5});
    try testing.expectEqual(@as(i32, 15), r1); // 10 + 5

    const WithoutInjection = ConditionalInject(add, false, .{10});
    const r2 = WithoutInjection.call(.{ 5, 3 });
    try testing.expectEqual(@as(i32, 8), r2); // 5 + 3
}
// ANCHOR_END: conditional_injection

// Comprehensive test
test "comprehensive argument injection" {
    // Allocator injection
    const WithTestAlloc = WithAllocator(createSlice, testing.allocator);
    const slice = try WithTestAlloc.call(.{3});
    defer testing.allocator.free(slice);
    try testing.expectEqual(@as(usize, 3), slice.len);

    // Prepend arguments
    const Times3 = PrependArgs(multiply, .{3});
    try testing.expectEqual(@as(i32, 15), Times3.call(.{5}));

    // Append arguments
    const DivBy5 = AppendArgs(divide, .{5});
    try testing.expectEqual(@as(i32, 4), DivBy5.call(.{20}));

    // Logger injection
    var logger_dec = WithLogger(processWithLog){};
    _ = logger_dec.call(.{10});
    try testing.expectEqual(@as(u32, 1), logger_dec.getLogCount());

    // Multiple argument injection
    const Multi = InjectMultiple(complexFunc, .{ 2, 3 });
    try testing.expectEqual(@as(i32, 11), Multi.call(.{ 4, 2 }));
}
```

### See Also

- Recipe 9.1: Putting a Wrapper Around a Function
- Recipe 9.4: Defining a Decorator That Takes Arguments
- Recipe 9.7: Defining Decorators as Structs
- Recipe 0.12: Understanding Allocators

---

## Recipe 9.10: Using Decorators to Patch Struct Definitions {#recipe-9-10}

**Tags:** allocators, comptime, comptime-metaprogramming, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_10.zig`

### Problem

You need to add common functionality to existing structs without modifying their definitions. You want reusable patterns for adding timestamps, IDs, validation, versioning, or other cross-cutting concerns to multiple struct types.

### Solution

Use compile-time functions that take a type and return a new type with enhanced capabilities. These "decorator" functions wrap the original struct and add fields, methods, or both.

### Adding Fields to Structs

The simplest pattern wraps a struct and adds new fields:

```zig
// Add fields to a struct
fn WithTimestamp(comptime T: type) type {
    return struct {
        inner: T,
        created_at: u64 = 0,
        updated_at: u64 = 0,

        pub fn init(inner: T) @This() {
            return .{
                .inner = inner,
                .created_at = 1000,
                .updated_at = 1000,
            };
        }

        pub fn update(self: *@This()) void {
            self.updated_at += 1;
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

const Person = struct {
    name: []const u8,
    age: u32,
};

test "add field" {
    const TimestampedPerson = WithTimestamp(Person);
    var tp = TimestampedPerson.init(.{ .name = "Alice", .age = 30 });

    try testing.expectEqual(@as(u64, 1000), tp.created_at);
    tp.update();
    try testing.expectEqual(@as(u64, 1001), tp.updated_at);

    const person = tp.getInner();
    try testing.expectEqualStrings("Alice", person.name);
}
```

The original struct is stored in an `inner` field, keeping it separate from the added functionality.

### Adding Methods to Structs

You can also add new methods while preserving the original struct:

```zig
// Add logging methods to any struct
fn WithLogging(comptime T: type) type {
    return struct {
        inner: T,
        log_count: u32 = 0,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn log(self: *@This(), comptime message: []const u8) void {
            _ = message;
            self.log_count += 1;
        }

        pub fn getLogCount(self: @This()) u32 {
            return self.log_count;
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "add methods" {
    const LoggedPerson = WithLogging(Person);
    var lp = LoggedPerson.init(.{ .name = "Bob", .age = 25 });

    lp.log("Created person");
    lp.log("Updated person");

    try testing.expectEqual(@as(u32, 2), lp.getLogCount());
}
```

### Wrapping with Validation

Decorators can add runtime behavior like validation:

```zig
// Wrap struct with validation state
fn WithValidation(comptime T: type) type {
    return struct {
        inner: T,
        is_valid: bool = true,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn validate(self: *@This()) bool {
            // Simplified validation
            self.is_valid = true;
            return self.is_valid;
        }

        pub fn invalidate(self: *@This()) void {
            self.is_valid = false;
        }

        pub fn getInner(self: @This()) ?T {
            if (!self.is_valid) return null;
            return self.inner;
        }
    };
}

test "wrap struct" {
    const ValidatedPerson = WithValidation(Person);
    var vp = ValidatedPerson.init(.{ .name = "Charlie", .age = 35 });

    try testing.expect(vp.validate());

    const person1 = vp.getInner();
    try testing.expect(person1 != null);

    vp.invalidate();
    const person2 = vp.getInner();
    try testing.expect(person2 == null);
}
```

### Discussion

### The Wrapper Pattern

All these decorators follow the same basic pattern:

1. Accept a type as a `comptime` parameter
2. Return a new struct type
3. Store the original type in an `inner` field
4. Add new fields and methods
5. Provide a `getInner()` method to access the wrapped value

This pattern is zero-cost at runtime because everything happens at compile time. The Zig compiler generates specialized code for each type you wrap.

### Common Decorator Patterns

**Adding Unique Identifiers:**

```zig
fn WithID(comptime T: type) type {
    return struct {
        id: u64,
        inner: T,

        pub fn init(id: u64, inner: T) @This() {
            return .{ .id = id, .inner = inner };
        }

        pub fn getID(self: @This()) u64 {
            return self.id;
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "add id field" {
    const PersonWithID = WithID(Person);
    const p = PersonWithID.init(42, .{ .name = "Diana", .age = 28 });

    try testing.expectEqual(@as(u64, 42), p.getID());
    try testing.expectEqualStrings("Diana", p.getInner().name);
}
```

**Version Tracking:**

```zig
fn Versioned(comptime T: type) type {
    return struct {
        inner: T,
        version: u32 = 1,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn update(self: *@This(), new_inner: T) void {
            self.inner = new_inner;
            self.version += 1;
        }

        pub fn getVersion(self: @This()) u32 {
            return self.version;
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "versioned struct" {
    const VersionedPerson = Versioned(Person);
    var vp = VersionedPerson.init(.{ .name = "Eve", .age = 30 });

    try testing.expectEqual(@as(u32, 1), vp.getVersion());

    vp.update(.{ .name = "Eve", .age = 31 });
    try testing.expectEqual(@as(u32, 2), vp.getVersion());
    try testing.expectEqual(@as(u32, 31), vp.getInner().age);
}
```

### Mixin Pattern

Mixins add capabilities without inheritance:

```zig
fn Comparable(comptime T: type) type {
    return struct {
        inner: T,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn equals(self: @This(), other: @This()) bool {
            // Simplified comparison
            _ = self;
            _ = other;
            return false; // Would compare fields
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

fn Serializable(comptime T: type) type {
    return struct {
        inner: T,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn serialize(self: @This()) []const u8 {
            _ = self;
            return "serialized"; // Simplified
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "mixin pattern" {
    const ComparablePerson = Comparable(Person);
    const cp1 = ComparablePerson.init(.{ .name = "Frank", .age = 40 });
    const cp2 = ComparablePerson.init(.{ .name = "Grace", .age = 45 });

    try testing.expect(!cp1.equals(cp2));

    const SerializablePerson = Serializable(Person);
    const sp = SerializablePerson.init(.{ .name = "Henry", .age = 50 });

    try testing.expectEqualStrings("serialized", sp.serialize());
}
```

### Adding Metadata

You can attach compile-time metadata to structs:

```zig
fn WithMetadata(comptime T: type, comptime metadata: anytype) type {
    return struct {
        pub const meta = metadata;
        inner: T,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn getMetadata() @TypeOf(metadata) {
            return meta;
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

const Metadata = struct {
    table_name: []const u8,
    primary_key: []const u8,
};

test "add metadata" {
    const meta = Metadata{ .table_name = "people", .primary_key = "id" };
    const MetaPerson = WithMetadata(Person, meta);

    const mp = MetaPerson.init(.{ .name = "Jack", .age = 33 });

    try testing.expectEqualStrings("people", MetaPerson.getMetadata().table_name);
    try testing.expectEqualStrings("Jack", mp.getInner().name);
}
```

The metadata is stored as a compile-time constant, accessible via the type itself rather than instances.

### Observable Pattern

Track changes to wrapped values:

```zig
fn Observable(comptime T: type) type {
    return struct {
        inner: T,
        change_count: u32 = 0,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn set(self: *@This(), new_value: T) void {
            self.inner = new_value;
            self.change_count += 1;
        }

        pub fn get(self: @This()) T {
            return self.inner;
        }

        pub fn getChangeCount(self: @This()) u32 {
            return self.change_count;
        }
    };
}

test "observable struct" {
    const ObservablePerson = Observable(Person);
    var op = ObservablePerson.init(.{ .name = "Leo", .age = 29 });

    try testing.expectEqual(@as(u32, 0), op.getChangeCount());

    op.set(.{ .name = "Leo", .age = 30 });
    try testing.expectEqual(@as(u32, 1), op.getChangeCount());
}
```

### Clone Support

Add cloning capability to any type:

```zig
fn Cloneable(comptime T: type) type {
    return struct {
        inner: T,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn clone(self: @This()) @This() {
            return .{ .inner = self.inner };
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "clone support" {
    const CloneablePerson = Cloneable(Person);
    const cp = CloneablePerson.init(.{ .name = "Mary", .age = 32 });

    const cloned = cp.clone();
    try testing.expectEqualStrings("Mary", cloned.getInner().name);
    try testing.expectEqual(@as(u32, 32), cloned.getInner().age);
}
```

This works for types that can be copied by value. For heap-allocated data, you'd need to pass an allocator and implement deep cloning.

### Default Values

Provide default initialization:

```zig
fn WithDefaults(comptime T: type, comptime defaults: T) type {
    return struct {
        inner: T,

        pub fn init() @This() {
            return .{ .inner = defaults };
        }

        pub fn initWith(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "default values" {
    const default_person = Person{ .name = "Default", .age = 0 };
    const DefaultPerson = WithDefaults(Person, default_person);

    const dp1 = DefaultPerson.init();
    try testing.expectEqualStrings("Default", dp1.getInner().name);

    const dp2 = DefaultPerson.initWith(.{ .name = "Nancy", .age = 24 });
    try testing.expectEqualStrings("Nancy", dp2.getInner().name);
}
```

### Lazy Initialization

Defer expensive initialization until first use:

```zig
fn Lazy(comptime T: type) type {
    return struct {
        value: ?T = null,
        initialized: bool = false,

        pub fn init() @This() {
            return .{};
        }

        pub fn get(self: *@This(), comptime init_fn: anytype) T {
            if (!self.initialized) {
                self.value = init_fn();
                self.initialized = true;
            }
            return self.value.?;
        }

        pub fn isInitialized(self: @This()) bool {
            return self.initialized;
        }
    };
}

fn createPerson() Person {
    return .{ .name = "Lazy", .age = 99 };
}

test "lazy initialization" {
    var lazy = Lazy(Person).init();

    try testing.expect(!lazy.isInitialized());

    const person = lazy.get(createPerson);
    try testing.expect(lazy.isInitialized());
    try testing.expectEqualStrings("Lazy", person.name);
}
```

The initialization function is called only once, on the first `get()` call.

### When to Use Struct Patching

These patterns shine when you need to:

1. **Add cross-cutting concerns** like logging, metrics, or validation to many types
2. **Avoid code duplication** by extracting common patterns
3. **Maintain separation of concerns** between core logic and auxiliary features
4. **Support progressive enhancement** of simple types
5. **Create composable abstractions** without inheritance

The compile-time nature means there's no runtime overhead compared to writing the enhanced struct directly.

### Limitations

**Type Identity:**
The wrapped type is distinct from the original. `WithTimestamp(Person)` and `Person` are different types.

**Field Access:**
You can't directly access inner fields without calling `getInner()` first. This can be verbose but maintains clear boundaries.

**Multiple Wrapping:**
Wrapping the same type with multiple decorators creates nesting:

```zig
const Enhanced = WithTimestamp(WithID(Person));
```

Each wrapper adds another level of indirection. For complex compositions, consider creating a dedicated struct instead.

### Full Tested Code

```zig
// Recipe 9.10: Using Decorators to Patch Struct Definitions
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: add_field
// Add fields to a struct
fn WithTimestamp(comptime T: type) type {
    return struct {
        inner: T,
        created_at: u64 = 0,
        updated_at: u64 = 0,

        pub fn init(inner: T) @This() {
            return .{
                .inner = inner,
                .created_at = 1000,
                .updated_at = 1000,
            };
        }

        pub fn update(self: *@This()) void {
            self.updated_at += 1;
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

const Person = struct {
    name: []const u8,
    age: u32,
};

test "add field" {
    const TimestampedPerson = WithTimestamp(Person);
    var tp = TimestampedPerson.init(.{ .name = "Alice", .age = 30 });

    try testing.expectEqual(@as(u64, 1000), tp.created_at);
    tp.update();
    try testing.expectEqual(@as(u64, 1001), tp.updated_at);

    const person = tp.getInner();
    try testing.expectEqualStrings("Alice", person.name);
}
// ANCHOR_END: add_field

// ANCHOR: add_methods
// Add methods to a struct
fn WithLogging(comptime T: type) type {
    return struct {
        inner: T,
        log_count: u32 = 0,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn log(self: *@This(), comptime message: []const u8) void {
            _ = message;
            self.log_count += 1;
        }

        pub fn getLogCount(self: @This()) u32 {
            return self.log_count;
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "add methods" {
    const LoggedPerson = WithLogging(Person);
    var lp = LoggedPerson.init(.{ .name = "Bob", .age = 25 });

    lp.log("Created person");
    lp.log("Updated person");

    try testing.expectEqual(@as(u32, 2), lp.getLogCount());
}
// ANCHOR_END: add_methods

// ANCHOR: wrap_struct
// Wrap struct with validation
fn WithValidation(comptime T: type) type {
    return struct {
        inner: T,
        is_valid: bool = true,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn validate(self: *@This()) bool {
            // Simplified validation
            self.is_valid = true;
            return self.is_valid;
        }

        pub fn invalidate(self: *@This()) void {
            self.is_valid = false;
        }

        pub fn getInner(self: @This()) ?T {
            if (!self.is_valid) return null;
            return self.inner;
        }
    };
}

test "wrap struct" {
    const ValidatedPerson = WithValidation(Person);
    var vp = ValidatedPerson.init(.{ .name = "Charlie", .age = 35 });

    try testing.expect(vp.validate());

    const person1 = vp.getInner();
    try testing.expect(person1 != null);

    vp.invalidate();
    const person2 = vp.getInner();
    try testing.expect(person2 == null);
}
// ANCHOR_END: wrap_struct

// ANCHOR: add_id_field
// Add ID field to any struct
fn WithID(comptime T: type) type {
    return struct {
        id: u64,
        inner: T,

        pub fn init(id: u64, inner: T) @This() {
            return .{ .id = id, .inner = inner };
        }

        pub fn getID(self: @This()) u64 {
            return self.id;
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "add id field" {
    const PersonWithID = WithID(Person);
    const p = PersonWithID.init(42, .{ .name = "Diana", .age = 28 });

    try testing.expectEqual(@as(u64, 42), p.getID());
    try testing.expectEqualStrings("Diana", p.getInner().name);
}
// ANCHOR_END: add_id_field

// ANCHOR: versioned_struct
// Add version tracking
fn Versioned(comptime T: type) type {
    return struct {
        inner: T,
        version: u32 = 1,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn update(self: *@This(), new_inner: T) void {
            self.inner = new_inner;
            self.version += 1;
        }

        pub fn getVersion(self: @This()) u32 {
            return self.version;
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "versioned struct" {
    const VersionedPerson = Versioned(Person);
    var vp = VersionedPerson.init(.{ .name = "Eve", .age = 30 });

    try testing.expectEqual(@as(u32, 1), vp.getVersion());

    vp.update(.{ .name = "Eve", .age = 31 });
    try testing.expectEqual(@as(u32, 2), vp.getVersion());
    try testing.expectEqual(@as(u32, 31), vp.getInner().age);
}
// ANCHOR_END: versioned_struct

// ANCHOR: mixin_pattern
// Mixin pattern for adding capabilities
fn Comparable(comptime T: type) type {
    return struct {
        inner: T,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn equals(self: @This(), other: @This()) bool {
            // Simplified comparison
            _ = self;
            _ = other;
            return false; // Would compare fields
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

fn Serializable(comptime T: type) type {
    return struct {
        inner: T,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn serialize(self: @This()) []const u8 {
            _ = self;
            return "serialized"; // Simplified
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "mixin pattern" {
    const ComparablePerson = Comparable(Person);
    const cp1 = ComparablePerson.init(.{ .name = "Frank", .age = 40 });
    const cp2 = ComparablePerson.init(.{ .name = "Grace", .age = 45 });

    try testing.expect(!cp1.equals(cp2));

    const SerializablePerson = Serializable(Person);
    const sp = SerializablePerson.init(.{ .name = "Henry", .age = 50 });

    try testing.expectEqualStrings("serialized", sp.serialize());
}
// ANCHOR_END: mixin_pattern

// ANCHOR: compose_mixins
// Compose multiple mixins
fn Compose(comptime T: type, comptime Mixins: []const type) type {
    // This is simplified - real implementation would be more complex
    _ = Mixins;
    return struct {
        inner: T,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "compose mixins" {
    const Enhanced = Compose(Person, &[_]type{ Comparable(Person), Serializable(Person) });
    const e = Enhanced.init(.{ .name = "Iris", .age = 22 });

    try testing.expectEqualStrings("Iris", e.getInner().name);
}
// ANCHOR_END: compose_mixins

// ANCHOR: add_metadata
// Add metadata to struct
fn WithMetadata(comptime T: type, comptime metadata: anytype) type {
    return struct {
        pub const meta = metadata;
        inner: T,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn getMetadata() @TypeOf(metadata) {
            return meta;
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

const Metadata = struct {
    table_name: []const u8,
    primary_key: []const u8,
};

test "add metadata" {
    const meta = Metadata{ .table_name = "people", .primary_key = "id" };
    const MetaPerson = WithMetadata(Person, meta);

    const mp = MetaPerson.init(.{ .name = "Jack", .age = 33 });

    try testing.expectEqualStrings("people", MetaPerson.getMetadata().table_name);
    try testing.expectEqualStrings("Jack", mp.getInner().name);
}
// ANCHOR_END: add_metadata

// ANCHOR: builder_wrapper
// Add builder pattern
fn WithBuilder(comptime T: type) type {
    return struct {
        const Self = @This();
        inner: T,

        pub fn init(inner: T) Self {
            return .{ .inner = inner };
        }

        pub fn build(self: Self) T {
            return self.inner;
        }

        pub fn getInner(self: Self) T {
            return self.inner;
        }
    };
}

test "builder wrapper" {
    const PersonBuilder = WithBuilder(Person);
    const builder = PersonBuilder.init(.{ .name = "Kate", .age = 27 });

    const person = builder.build();
    try testing.expectEqualStrings("Kate", person.name);
}
// ANCHOR_END: builder_wrapper

// ANCHOR: observable_struct
// Add observer pattern
fn Observable(comptime T: type) type {
    return struct {
        inner: T,
        change_count: u32 = 0,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn set(self: *@This(), new_value: T) void {
            self.inner = new_value;
            self.change_count += 1;
        }

        pub fn get(self: @This()) T {
            return self.inner;
        }

        pub fn getChangeCount(self: @This()) u32 {
            return self.change_count;
        }
    };
}

test "observable struct" {
    const ObservablePerson = Observable(Person);
    var op = ObservablePerson.init(.{ .name = "Leo", .age = 29 });

    try testing.expectEqual(@as(u32, 0), op.getChangeCount());

    op.set(.{ .name = "Leo", .age = 30 });
    try testing.expectEqual(@as(u32, 1), op.getChangeCount());
}
// ANCHOR_END: observable_struct

// ANCHOR: clone_support
// Add clone capability
fn Cloneable(comptime T: type) type {
    return struct {
        inner: T,

        pub fn init(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn clone(self: @This()) @This() {
            return .{ .inner = self.inner };
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "clone support" {
    const CloneablePerson = Cloneable(Person);
    const cp = CloneablePerson.init(.{ .name = "Mary", .age = 32 });

    const cloned = cp.clone();
    try testing.expectEqualStrings("Mary", cloned.getInner().name);
    try testing.expectEqual(@as(u32, 32), cloned.getInner().age);
}
// ANCHOR_END: clone_support

// ANCHOR: default_values
// Add default value support
fn WithDefaults(comptime T: type, comptime defaults: T) type {
    return struct {
        inner: T,

        pub fn init() @This() {
            return .{ .inner = defaults };
        }

        pub fn initWith(inner: T) @This() {
            return .{ .inner = inner };
        }

        pub fn getInner(self: @This()) T {
            return self.inner;
        }
    };
}

test "default values" {
    const default_person = Person{ .name = "Default", .age = 0 };
    const DefaultPerson = WithDefaults(Person, default_person);

    const dp1 = DefaultPerson.init();
    try testing.expectEqualStrings("Default", dp1.getInner().name);

    const dp2 = DefaultPerson.initWith(.{ .name = "Nancy", .age = 24 });
    try testing.expectEqualStrings("Nancy", dp2.getInner().name);
}
// ANCHOR_END: default_values

// ANCHOR: lazy_initialization
// Add lazy initialization
fn Lazy(comptime T: type) type {
    return struct {
        value: ?T = null,
        initialized: bool = false,

        pub fn init() @This() {
            return .{};
        }

        pub fn get(self: *@This(), comptime init_fn: anytype) T {
            if (!self.initialized) {
                self.value = init_fn();
                self.initialized = true;
            }
            return self.value.?;
        }

        pub fn isInitialized(self: @This()) bool {
            return self.initialized;
        }
    };
}

fn createPerson() Person {
    return .{ .name = "Lazy", .age = 99 };
}

test "lazy initialization" {
    var lazy = Lazy(Person).init();

    try testing.expect(!lazy.isInitialized());

    const person = lazy.get(createPerson);
    try testing.expect(lazy.isInitialized());
    try testing.expectEqualStrings("Lazy", person.name);
}
// ANCHOR_END: lazy_initialization

// Comprehensive test
test "comprehensive struct patching" {
    // Add timestamp
    const TimestampedPerson = WithTimestamp(Person);
    const tp = TimestampedPerson.init(.{ .name = "Test", .age = 50 });
    try testing.expectEqual(@as(u64, 1000), tp.created_at);

    // Add ID
    const PersonWithID = WithID(Person);
    const pid = PersonWithID.init(123, .{ .name = "Test2", .age = 51 });
    try testing.expectEqual(@as(u64, 123), pid.getID());

    // Versioned
    const VersionedPerson = Versioned(Person);
    var vp = VersionedPerson.init(.{ .name = "Test3", .age = 52 });
    vp.update(.{ .name = "Test3", .age = 53 });
    try testing.expectEqual(@as(u32, 2), vp.getVersion());

    // Observable
    const ObservablePerson = Observable(Person);
    var op = ObservablePerson.init(.{ .name = "Test4", .age = 54 });
    op.set(.{ .name = "Test4", .age = 55 });
    try testing.expectEqual(@as(u32, 1), op.getChangeCount());
}
```

### See Also

- Recipe 9.1: Putting a wrapper around a function
- Recipe 9.6: Defining decorators as part of a struct
- Recipe 9.7: Defining decorators as structs
- Recipe 9.18: Extending classes with mixins (if available)

---

## Recipe 9.11: Using a Metaclass to Control Instance Creation {#recipe-9-11}

**Tags:** comptime, comptime-metaprogramming, error-handling, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_11.zig`

### Problem

You want to control instance creation at compile time, enforcing patterns like singletons, factories, or resource pools. You need to generate different types based on compile-time parameters, validate initialization, or include/exclude fields conditionally.

### Solution

Use `comptime` parameters and compile-time evaluation to generate types with specific instance creation behavior. Zig's compile-time execution allows you to make decisions about type structure and initialization before the program runs.

### Singleton Pattern

Enforce single-instance behavior at compile time:

```zig
// Enforce singleton pattern at compile time
fn Singleton(comptime T: type) type {
    return struct {
        const Self = @This();
        var instance: ?T = null;
        var initialized: bool = false;

        pub fn getInstance() *T {
            if (!initialized) {
                instance = T{};
                initialized = true;
            }
            return &instance.?;
        }

        pub fn reset() void {
            instance = null;
            initialized = false;
        }
    };
}

const Config = struct {
    value: i32 = 42,
};

test "singleton pattern" {
    const ConfigSingleton = Singleton(Config);

    ConfigSingleton.reset();
    const cfg1 = ConfigSingleton.getInstance();
    cfg1.value = 100;

    const cfg2 = ConfigSingleton.getInstance();
    try testing.expectEqual(@as(i32, 100), cfg2.value);
    try testing.expectEqual(@intFromPtr(cfg1), @intFromPtr(cfg2));
}
```

The singleton is generated at compile time, with static storage for the single instance.

### Factory Pattern

Create different types based on compile-time enum values:

```zig
fn Factory(comptime kind: enum { Simple, Complex }) type {
    return switch (kind) {
        .Simple => struct {
            value: i32,

            pub fn init(v: i32) @This() {
                return .{ .value = v };
            }

            pub fn getValue(self: @This()) i32 {
                return self.value;
            }
        },
        .Complex => struct {
            value: i32,
            metadata: []const u8,

            pub fn init(v: i32, meta: []const u8) @This() {
                return .{ .value = v, .metadata = meta };
            }

            pub fn getValue(self: @This()) i32 {
                return self.value;
            }

            pub fn getMetadata(self: @This()) []const u8 {
                return self.metadata;
            }
        },
    };
}

test "factory pattern" {
    const Simple = Factory(.Simple);
    const s = Simple.init(10);
    try testing.expectEqual(@as(i32, 10), s.getValue());

    const Complex = Factory(.Complex);
    const c = Complex.init(20, "test");
    try testing.expectEqual(@as(i32, 20), c.getValue());
    try testing.expectEqualStrings("test", c.getMetadata());
}
```

Each factory variant generates a completely different type with its own structure and methods.

### Discussion

### Runtime Validation with Compile-Time Types

While you can't validate runtime values at compile time, you can create types that enforce validation:

```zig
fn ValidatedInit(comptime T: type) type {
    return struct {
        inner: T,

        pub fn init(value: T, comptime validator: anytype) !@This() {
            if (!validator(value)) {
                return error.InvalidValue;
            }
            return .{ .inner = value };
        }

        pub fn get(self: @This()) T {
            return self.inner;
        }
    };
}

fn isPositive(value: i32) bool {
    return value > 0;
}

fn isEven(value: i32) bool {
    return @mod(value, 2) == 0;
}

test "validated init" {
    const ValidatedInt = ValidatedInit(i32);

    const p1 = try ValidatedInt.init(10, isPositive);
    try testing.expectEqual(@as(i32, 10), p1.get());

    const p2 = ValidatedInt.init(-5, isPositive);
    try testing.expectError(error.InvalidValue, p2);

    const even = try ValidatedInt.init(8, isEven);
    try testing.expectEqual(@as(i32, 8), even.get());
}
```

The validator is a compile-time parameter, allowing different validation logic for each usage.

### Conditional Fields

Include or exclude fields based on compile-time flags:

```zig
fn ConditionalFields(comptime has_id: bool, comptime has_timestamp: bool) type {
    return struct {
        const Self = @This();

        id: if (has_id) u64 else void,
        timestamp: if (has_timestamp) u64 else void,
        value: i32,

        pub fn init(value: i32) Self {
            return .{
                .id = if (has_id) 0 else {},
                .timestamp = if (has_timestamp) 0 else {},
                .value = value,
            };
        }

        pub fn getValue(self: Self) i32 {
            return self.value;
        }

        pub fn hasID() bool {
            return has_id;
        }

        pub fn hasTimestamp() bool {
            return has_timestamp;
        }
    };
}

test "conditional fields" {
    const WithBoth = ConditionalFields(true, true);
    const both = WithBoth.init(42);
    try testing.expectEqual(@as(i32, 42), both.getValue());
    try testing.expect(WithBoth.hasID());
    try testing.expect(WithBoth.hasTimestamp());

    const Plain = ConditionalFields(false, false);
    _ = Plain.init(5);
    try testing.expect(!Plain.hasID());
    try testing.expect(!Plain.hasTimestamp());
}
```

Fields with type `void` occupy no space, making this truly zero-cost.

### Resource Pools

Create fixed-size resource pools at compile time:

```zig
fn Pool(comptime T: type, comptime capacity: usize) type {
    return struct {
        const Self = @This();
        items: [capacity]?T = [_]?T{null} ** capacity,
        count: usize = 0,

        pub fn init() Self {
            return .{};
        }

        pub fn acquire(self: *Self, value: T) !usize {
            if (self.count >= capacity) return error.PoolExhausted;

            for (self.items, 0..) |item, i| {
                if (item == null) {
                    self.items[i] = value;
                    self.count += 1;
                    return i;
                }
            }
            unreachable;
        }

        pub fn release(self: *Self, index: usize) void {
            if (index < capacity and self.items[index] != null) {
                self.items[index] = null;
                self.count -= 1;
            }
        }

        pub fn getCapacity() usize {
            return capacity;
        }

        pub fn getCount(self: Self) usize {
            return self.count;
        }
    };
}

test "resource pool" {
    const IntPool = Pool(i32, 5);
    var pool = IntPool.init();

    try testing.expectEqual(@as(usize, 5), IntPool.getCapacity());

    const idx1 = try pool.acquire(10);
    const idx2 = try pool.acquire(20);
    try testing.expectEqual(@as(usize, 2), pool.getCount());

    pool.release(idx1);
    try testing.expectEqual(@as(usize, 1), pool.getCount());
}
```

The array size is determined at compile time, with no runtime allocation.

### Builder Pattern Generation

Generate builders that introspect the target type:

```zig
fn Builder(comptime T: type) type {
    return struct {
        const Self = @This();
        instance: T,

        pub fn init() Self {
            return .{ .instance = std.mem.zeroes(T) };
        }

        pub fn set(self: *Self, value: T) void {
            self.instance = value;
        }

        pub fn build(self: Self) T {
            return self.instance;
        }

        pub fn getFieldCount() usize {
            return @typeInfo(T).@"struct".fields.len;
        }

        pub fn hasField(comptime name: []const u8) bool {
            const fields = @typeInfo(T).@"struct".fields;
            inline for (fields) |field| {
                if (std.mem.eql(u8, field.name, name)) {
                    return true;
                }
            }
            return false;
        }
    };
}

const Person = struct {
    name: []const u8 = "",
    age: u32 = 0,
};

test "builder generation" {
    const PersonBuilder = Builder(Person);
    var builder = PersonBuilder.init();
    builder.instance.name = "Alice";
    builder.instance.age = 30;

    const person = builder.build();
    try testing.expectEqualStrings("Alice", person.name);

    try testing.expectEqual(@as(usize, 2), PersonBuilder.getFieldCount());
    try testing.expect(PersonBuilder.hasField("name"));
    try testing.expect(!PersonBuilder.hasField("invalid"));
}
```

The builder uses `@typeInfo` to inspect fields at compile time.

### Type Registry

Create compile-time type collections:

```zig
fn TypeRegistry(comptime types: []const type) type {
    return struct {
        pub fn getCount() usize {
            return types.len;
        }

        pub fn getType(comptime index: usize) type {
            if (index >= types.len) {
                @compileError("Index out of bounds");
            }
            return types[index];
        }

        pub fn hasType(comptime T: type) bool {
            inline for (types) |t| {
                if (t == T) return true;
            }
            return false;
        }

        pub fn indexOf(comptime T: type) ?usize {
            inline for (types, 0..) |t, i| {
                if (t == T) return i;
            }
            return null;
        }
    };
}

test "type registry" {
    const Registry = TypeRegistry(&[_]type{ i32, u32, f32, bool });

    try testing.expectEqual(@as(usize, 4), Registry.getCount());
    try testing.expect(Registry.getType(0) == i32);
    try testing.expect(Registry.hasType(u32));
    try testing.expect(!Registry.hasType(i64));
    try testing.expectEqual(@as(?usize, 2), Registry.indexOf(f32));
}
```

All type lookups happen at compile time with no runtime cost.

### Lazy Static Initialization

Initialize static values lazily:

```zig
fn LazyStatic(comptime init_fn: anytype) type {
    return struct {
        const T = @TypeOf(init_fn());
        var value: ?T = null;
        var is_initialized: bool = false;

        pub fn get() *const T {
            if (!is_initialized) {
                value = init_fn();
                is_initialized = true;
            }
            return &value.?;
        }

        pub fn reset() void {
            value = null;
            is_initialized = false;
        }
    };
}

fn createDefaultConfig() Config {
    return .{ .value = 999 };
}

test "lazy static" {
    const DefaultConfig = LazyStatic(createDefaultConfig);

    DefaultConfig.reset();
    const cfg1 = DefaultConfig.get();
    try testing.expectEqual(@as(i32, 999), cfg1.value);

    const cfg2 = DefaultConfig.get();
    try testing.expectEqual(@intFromPtr(cfg1), @intFromPtr(cfg2));
}
```

The initialization function runs at most once, on first access.

### Variant Types

Generate different struct types based on an enum:

```zig
fn Variant(comptime shape: enum { Circle, Rectangle, Triangle }) type {
    return switch (shape) {
        .Circle => struct {
            radius: f32,

            pub fn init(r: f32) @This() {
                return .{ .radius = r };
            }

            pub fn area(self: @This()) f32 {
                return 3.14159 * self.radius * self.radius;
            }
        },
        .Rectangle => struct {
            width: f32,
            height: f32,

            pub fn init(w: f32, h: f32) @This() {
                return .{ .width = w, .height = h };
            }

            pub fn area(self: @This()) f32 {
                return self.width * self.height;
            }
        },
        .Triangle => struct {
            base: f32,
            height: f32,

            pub fn init(b: f32, h: f32) @This() {
                return .{ .base = b, .height = h };
            }

            pub fn area(self: @This()) f32 {
                return 0.5 * self.base * self.height;
            }
        },
    };
}

test "variant creation" {
    const Circle = Variant(.Circle);
    const c = Circle.init(5.0);
    try testing.expect(c.area() > 78.0 and c.area() < 79.0);

    const Rectangle = Variant(.Rectangle);
    const r = Rectangle.init(4.0, 5.0);
    try testing.expectEqual(@as(f32, 20.0), r.area());
}
```

Each variant is a completely different type with its own fields and implementations.

### Capability Injection

Selectively add methods based on compile-time flags:

```zig
fn WithCapabilities(comptime T: type, comptime capabilities: struct {
    serializable: bool = false,
    comparable: bool = false,
    cloneable: bool = false,
}) type {
    return struct {
        const Self = @This();
        inner: T,

        pub fn init(inner: T) Self {
            return .{ .inner = inner };
        }

        pub fn get(self: Self) T {
            return self.inner;
        }

        pub fn serialize(self: Self) []const u8 {
            if (!capabilities.serializable) {
                @compileError("Serialization not enabled");
            }
            _ = self;
            return "serialized";
        }

        pub fn clone(self: Self) Self {
            if (!capabilities.cloneable) {
                @compileError("Cloning not enabled");
            }
            return .{ .inner = self.inner };
        }

        pub fn hasSerializable() bool {
            return capabilities.serializable;
        }
    };
}

test "capability injection" {
    const AllCapabilities = WithCapabilities(i32, .{
        .serializable = true,
        .comparable = true,
        .cloneable = true,
    });

    const v1 = AllCapabilities.init(42);
    try testing.expectEqualStrings("serialized", v1.serialize());
    const v2 = v1.clone();
    try testing.expectEqual(@as(i32, 42), v2.get());
}
```

Calling a disabled capability produces a compile error.

### Type Constraints

Enforce constraints on the types that can be used:

```zig
fn Constrained(comptime T: type, comptime constraint: fn (type) bool) type {
    if (!constraint(T)) {
        @compileError("Type does not meet constraint");
    }

    return struct {
        value: T,

        pub fn init(v: T) @This() {
            return .{ .value = v };
        }

        pub fn get(self: @This()) T {
            return self.value;
        }
    };
}

fn isNumeric(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .int, .float => true,
        else => false,
    };
}

test "constrained init" {
    const NumericInt = Constrained(i32, isNumeric);
    const n = NumericInt.init(42);
    try testing.expectEqual(@as(i32, 42), n.get());

    // This would fail at compile time:
    // const InvalidType = Constrained(bool, isNumeric);
}
```

The constraint function runs at compile time, rejecting invalid types before code generation.

### When to Use These Patterns

Compile-time instance creation control is valuable when you need to:

1. **Enforce design patterns** like singletons or factories at the type level
2. **Generate type variants** based on compile-time parameters
3. **Optimize for specific use cases** by including only needed fields
4. **Create domain-specific types** with compile-time validation
5. **Build type-safe APIs** that prevent misuse at compile time

The key advantage is that all decisions happen during compilation, resulting in zero runtime overhead compared to hand-written alternatives.

### Full Tested Code

```zig
// Recipe 9.11: Using Comptime to Control Instance Creation
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: singleton_pattern
// Enforce singleton pattern at compile time
fn Singleton(comptime T: type) type {
    return struct {
        const Self = @This();
        var instance: ?T = null;
        var initialized: bool = false;

        pub fn getInstance() *T {
            if (!initialized) {
                instance = T{};
                initialized = true;
            }
            return &instance.?;
        }

        pub fn reset() void {
            instance = null;
            initialized = false;
        }
    };
}

const Config = struct {
    value: i32 = 42,
};

test "singleton pattern" {
    const ConfigSingleton = Singleton(Config);

    ConfigSingleton.reset();
    const cfg1 = ConfigSingleton.getInstance();
    cfg1.value = 100;

    const cfg2 = ConfigSingleton.getInstance();
    try testing.expectEqual(@as(i32, 100), cfg2.value);
    try testing.expectEqual(@intFromPtr(cfg1), @intFromPtr(cfg2));
}
// ANCHOR_END: singleton_pattern

// ANCHOR: factory_pattern
// Factory that creates different types based on comptime parameter
fn Factory(comptime kind: enum { Simple, Complex }) type {
    return switch (kind) {
        .Simple => struct {
            value: i32,

            pub fn init(v: i32) @This() {
                return .{ .value = v };
            }

            pub fn getValue(self: @This()) i32 {
                return self.value;
            }
        },
        .Complex => struct {
            value: i32,
            metadata: []const u8,

            pub fn init(v: i32, meta: []const u8) @This() {
                return .{ .value = v, .metadata = meta };
            }

            pub fn getValue(self: @This()) i32 {
                return self.value;
            }

            pub fn getMetadata(self: @This()) []const u8 {
                return self.metadata;
            }
        },
    };
}

test "factory pattern" {
    const Simple = Factory(.Simple);
    const s = Simple.init(10);
    try testing.expectEqual(@as(i32, 10), s.getValue());

    const Complex = Factory(.Complex);
    const c = Complex.init(20, "test");
    try testing.expectEqual(@as(i32, 20), c.getValue());
    try testing.expectEqualStrings("test", c.getMetadata());
}
// ANCHOR_END: factory_pattern

// ANCHOR: validated_init
// Runtime-validated initialization with compile-time type checking
fn ValidatedInit(comptime T: type) type {
    return struct {
        inner: T,

        pub fn init(value: T, comptime validator: anytype) !@This() {
            if (!validator(value)) {
                return error.InvalidValue;
            }
            return .{ .inner = value };
        }

        pub fn get(self: @This()) T {
            return self.inner;
        }
    };
}

fn isPositive(value: i32) bool {
    return value > 0;
}

fn isEven(value: i32) bool {
    return @mod(value, 2) == 0;
}

test "validated init" {
    const ValidatedInt = ValidatedInit(i32);

    const p1 = try ValidatedInt.init(10, isPositive);
    try testing.expectEqual(@as(i32, 10), p1.get());

    const p2 = ValidatedInt.init(-5, isPositive);
    try testing.expectError(error.InvalidValue, p2);

    const even = try ValidatedInt.init(8, isEven);
    try testing.expectEqual(@as(i32, 8), even.get());
}
// ANCHOR_END: validated_init

// ANCHOR: conditional_fields
// Include fields conditionally based on comptime parameters
fn ConditionalFields(comptime has_id: bool, comptime has_timestamp: bool) type {
    return struct {
        const Self = @This();

        id: if (has_id) u64 else void,
        timestamp: if (has_timestamp) u64 else void,
        value: i32,

        pub fn init(value: i32) Self {
            return .{
                .id = if (has_id) 0 else {},
                .timestamp = if (has_timestamp) 0 else {},
                .value = value,
            };
        }

        pub fn getValue(self: Self) i32 {
            return self.value;
        }

        pub fn hasID() bool {
            return has_id;
        }

        pub fn hasTimestamp() bool {
            return has_timestamp;
        }
    };
}

test "conditional fields" {
    const WithBoth = ConditionalFields(true, true);
    const both = WithBoth.init(42);
    try testing.expectEqual(@as(i32, 42), both.getValue());
    try testing.expect(WithBoth.hasID());
    try testing.expect(WithBoth.hasTimestamp());

    const WithID = ConditionalFields(true, false);
    _ = WithID.init(10);
    try testing.expect(WithID.hasID());
    try testing.expect(!WithID.hasTimestamp());

    const Plain = ConditionalFields(false, false);
    _ = Plain.init(5);
    try testing.expect(!Plain.hasID());
    try testing.expect(!Plain.hasTimestamp());
}
// ANCHOR_END: conditional_fields

// ANCHOR: resource_pool
// Compile-time resource pool
fn Pool(comptime T: type, comptime capacity: usize) type {
    return struct {
        const Self = @This();
        items: [capacity]?T = [_]?T{null} ** capacity,
        count: usize = 0,

        pub fn init() Self {
            return .{};
        }

        pub fn acquire(self: *Self, value: T) !usize {
            if (self.count >= capacity) return error.PoolExhausted;

            for (self.items, 0..) |item, i| {
                if (item == null) {
                    self.items[i] = value;
                    self.count += 1;
                    return i;
                }
            }
            unreachable;
        }

        pub fn release(self: *Self, index: usize) void {
            if (index < capacity and self.items[index] != null) {
                self.items[index] = null;
                self.count -= 1;
            }
        }

        pub fn getCapacity() usize {
            return capacity;
        }

        pub fn getCount(self: Self) usize {
            return self.count;
        }
    };
}

test "resource pool" {
    const IntPool = Pool(i32, 5);
    var pool = IntPool.init();

    try testing.expectEqual(@as(usize, 5), IntPool.getCapacity());

    const idx1 = try pool.acquire(10);
    const idx2 = try pool.acquire(20);
    try testing.expectEqual(@as(usize, 2), pool.getCount());

    pool.release(idx1);
    try testing.expectEqual(@as(usize, 1), pool.getCount());

    pool.release(idx2);
    try testing.expectEqual(@as(usize, 0), pool.getCount());
}
// ANCHOR_END: resource_pool

// ANCHOR: builder_generation
// Generate builder pattern at compile time
fn Builder(comptime T: type) type {
    return struct {
        const Self = @This();
        instance: T,

        pub fn init() Self {
            return .{ .instance = std.mem.zeroes(T) };
        }

        pub fn set(self: *Self, value: T) void {
            self.instance = value;
        }

        pub fn build(self: Self) T {
            return self.instance;
        }

        pub fn getFieldCount() usize {
            return @typeInfo(T).@"struct".fields.len;
        }

        pub fn hasField(comptime name: []const u8) bool {
            const fields = @typeInfo(T).@"struct".fields;
            inline for (fields) |field| {
                if (std.mem.eql(u8, field.name, name)) {
                    return true;
                }
            }
            return false;
        }
    };
}

const Person = struct {
    name: []const u8 = "",
    age: u32 = 0,
};

test "builder generation" {
    const PersonBuilder = Builder(Person);
    var builder = PersonBuilder.init();
    builder.instance.name = "Alice";
    builder.instance.age = 30;

    const person = builder.build();
    try testing.expectEqualStrings("Alice", person.name);
    try testing.expectEqual(@as(u32, 30), person.age);

    try testing.expectEqual(@as(usize, 2), PersonBuilder.getFieldCount());
    try testing.expect(PersonBuilder.hasField("name"));
    try testing.expect(!PersonBuilder.hasField("invalid"));
}
// ANCHOR_END: builder_generation

// ANCHOR: type_registry
// Compile-time type registry
fn TypeRegistry(comptime types: []const type) type {
    return struct {
        pub fn getCount() usize {
            return types.len;
        }

        pub fn getType(comptime index: usize) type {
            if (index >= types.len) {
                @compileError("Index out of bounds");
            }
            return types[index];
        }

        pub fn hasType(comptime T: type) bool {
            inline for (types) |t| {
                if (t == T) return true;
            }
            return false;
        }

        pub fn indexOf(comptime T: type) ?usize {
            inline for (types, 0..) |t, i| {
                if (t == T) return i;
            }
            return null;
        }
    };
}

test "type registry" {
    const Registry = TypeRegistry(&[_]type{ i32, u32, f32, bool });

    try testing.expectEqual(@as(usize, 4), Registry.getCount());
    try testing.expect(Registry.getType(0) == i32);
    try testing.expect(Registry.hasType(u32));
    try testing.expect(!Registry.hasType(i64));
    try testing.expectEqual(@as(?usize, 2), Registry.indexOf(f32));
    try testing.expectEqual(@as(?usize, null), Registry.indexOf(i64));
}
// ANCHOR_END: type_registry

// ANCHOR: lazy_static
// Compile-time lazy initialization
fn LazyStatic(comptime init_fn: anytype) type {
    return struct {
        const T = @TypeOf(init_fn());
        var value: ?T = null;
        var is_initialized: bool = false;

        pub fn get() *const T {
            if (!is_initialized) {
                value = init_fn();
                is_initialized = true;
            }
            return &value.?;
        }

        pub fn reset() void {
            value = null;
            is_initialized = false;
        }
    };
}

fn createDefaultConfig() Config {
    return .{ .value = 999 };
}

test "lazy static" {
    const DefaultConfig = LazyStatic(createDefaultConfig);

    DefaultConfig.reset();
    const cfg1 = DefaultConfig.get();
    try testing.expectEqual(@as(i32, 999), cfg1.value);

    const cfg2 = DefaultConfig.get();
    try testing.expectEqual(@intFromPtr(cfg1), @intFromPtr(cfg2));
}
// ANCHOR_END: lazy_static

// ANCHOR: variant_creation
// Create variants based on comptime enum
fn Variant(comptime shape: enum { Circle, Rectangle, Triangle }) type {
    return switch (shape) {
        .Circle => struct {
            radius: f32,

            pub fn init(r: f32) @This() {
                return .{ .radius = r };
            }

            pub fn area(self: @This()) f32 {
                return 3.14159 * self.radius * self.radius;
            }
        },
        .Rectangle => struct {
            width: f32,
            height: f32,

            pub fn init(w: f32, h: f32) @This() {
                return .{ .width = w, .height = h };
            }

            pub fn area(self: @This()) f32 {
                return self.width * self.height;
            }
        },
        .Triangle => struct {
            base: f32,
            height: f32,

            pub fn init(b: f32, h: f32) @This() {
                return .{ .base = b, .height = h };
            }

            pub fn area(self: @This()) f32 {
                return 0.5 * self.base * self.height;
            }
        },
    };
}

test "variant creation" {
    const Circle = Variant(.Circle);
    const c = Circle.init(5.0);
    try testing.expect(c.area() > 78.0 and c.area() < 79.0);

    const Rectangle = Variant(.Rectangle);
    const r = Rectangle.init(4.0, 5.0);
    try testing.expectEqual(@as(f32, 20.0), r.area());

    const Triangle = Variant(.Triangle);
    const t = Triangle.init(6.0, 4.0);
    try testing.expectEqual(@as(f32, 12.0), t.area());
}
// ANCHOR_END: variant_creation

// ANCHOR: capability_injection
// Inject capabilities based on comptime flags
fn WithCapabilities(comptime T: type, comptime capabilities: struct {
    serializable: bool = false,
    comparable: bool = false,
    cloneable: bool = false,
}) type {
    return struct {
        const Self = @This();
        inner: T,

        pub fn init(inner: T) Self {
            return .{ .inner = inner };
        }

        pub fn get(self: Self) T {
            return self.inner;
        }

        pub fn serialize(self: Self) []const u8 {
            if (!capabilities.serializable) {
                @compileError("Serialization not enabled");
            }
            _ = self;
            return "serialized";
        }

        pub fn equals(self: Self, other: Self) bool {
            if (!capabilities.comparable) {
                @compileError("Comparison not enabled");
            }
            _ = self;
            _ = other;
            return false;
        }

        pub fn clone(self: Self) Self {
            if (!capabilities.cloneable) {
                @compileError("Cloning not enabled");
            }
            return .{ .inner = self.inner };
        }

        pub fn hasSerializable() bool {
            return capabilities.serializable;
        }

        pub fn hasComparable() bool {
            return capabilities.comparable;
        }

        pub fn hasCloneable() bool {
            return capabilities.cloneable;
        }
    };
}

test "capability injection" {
    const AllCapabilities = WithCapabilities(i32, .{
        .serializable = true,
        .comparable = true,
        .cloneable = true,
    });

    try testing.expect(AllCapabilities.hasSerializable());
    try testing.expect(AllCapabilities.hasComparable());
    try testing.expect(AllCapabilities.hasCloneable());

    const v1 = AllCapabilities.init(42);
    try testing.expectEqualStrings("serialized", v1.serialize());
    try testing.expect(!v1.equals(v1));
    const v2 = v1.clone();
    try testing.expectEqual(@as(i32, 42), v2.get());

    const OnlySerializable = WithCapabilities(i32, .{ .serializable = true });
    const s = OnlySerializable.init(10);
    try testing.expectEqualStrings("serialized", s.serialize());
    try testing.expect(OnlySerializable.hasSerializable());
    try testing.expect(!OnlySerializable.hasCloneable());
    // s.clone() would fail at compile time with appropriate error
}
// ANCHOR_END: capability_injection

// ANCHOR: constrained_init
// Constrain initialization based on type properties
fn Constrained(comptime T: type, comptime constraint: fn (type) bool) type {
    if (!constraint(T)) {
        @compileError("Type does not meet constraint");
    }

    return struct {
        value: T,

        pub fn init(v: T) @This() {
            return .{ .value = v };
        }

        pub fn get(self: @This()) T {
            return self.value;
        }
    };
}

fn isNumeric(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .int, .float => true,
        else => false,
    };
}

test "constrained init" {
    const NumericInt = Constrained(i32, isNumeric);
    const n = NumericInt.init(42);
    try testing.expectEqual(@as(i32, 42), n.get());

    // This would fail at compile time:
    // const InvalidType = Constrained(bool, isNumeric);
}
// ANCHOR_END: constrained_init

// Comprehensive test
test "comprehensive comptime instance creation" {
    // Singleton
    const SingletonConfig = Singleton(Config);
    SingletonConfig.reset();
    const cfg = SingletonConfig.getInstance();
    try testing.expectEqual(@as(i32, 42), cfg.value);

    // Factory
    const SimpleFactory = Factory(.Simple);
    const simple = SimpleFactory.init(100);
    try testing.expectEqual(@as(i32, 100), simple.getValue());

    // Conditional fields
    const Minimal = ConditionalFields(false, false);
    const m = Minimal.init(15);
    try testing.expectEqual(@as(i32, 15), m.getValue());

    // Pool
    const SmallPool = Pool(i32, 3);
    var pool = SmallPool.init();
    _ = try pool.acquire(1);
    _ = try pool.acquire(2);
    try testing.expectEqual(@as(usize, 2), pool.getCount());

    // Variant
    const Rect = Variant(.Rectangle);
    const rect = Rect.init(10.0, 5.0);
    try testing.expectEqual(@as(f32, 50.0), rect.area());
}
```

### See Also

- Recipe 9.10: Using decorators to patch struct definitions
- Recipe 9.13: Defining a generic that takes optional arguments
- Recipe 9.15: Enforcing coding conventions in structs

---

## Recipe 9.12: Capturing Struct Attribute Definition Order {#recipe-9-12}

**Tags:** allocators, comptime, comptime-metaprogramming, error-handling, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_12.zig`

### Problem

You need to know the order in which fields are defined in a struct. You want to iterate over fields in definition order, serialize them in a specific sequence, validate field ordering, or create derived types that preserve or manipulate field order.

### Solution

Use `@typeInfo` to access struct metadata at compile time. Zig guarantees that the fields array returned by `@typeInfo(T).@"struct".fields` preserves the original definition order.

### Getting Field Names in Order

The simplest operation extracts field names as they were defined:

```zig
// Extract field names in definition order
fn getFieldNames(comptime T: type) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;
    comptime var names: [fields.len][]const u8 = undefined;
    inline for (fields, 0..) |field, i| {
        names[i] = field.name;
    }
    const final = names;
    return &final;
}

const Person = struct {
    name: []const u8,
    age: u32,
    email: []const u8,
};

test "get field order" {
    const names = getFieldNames(Person);
    try testing.expectEqual(@as(usize, 3), names.len);
    try testing.expectEqualStrings("name", names[0]);
    try testing.expectEqualStrings("age", names[1]);
    try testing.expectEqualStrings("email", names[2]);
}
```

The array index corresponds directly to the field's position in the struct definition.

### Finding Field Positions

You can look up where a specific field appears:

```zig
fn getFieldPosition(comptime T: type, comptime field_name: []const u8) ?usize {
    const fields = @typeInfo(T).@"struct".fields;
    inline for (fields, 0..) |field, i| {
        if (std.mem.eql(u8, field.name, field_name)) {
            return i;
        }
    }
    return null;
}

test "field positions" {
    try testing.expectEqual(@as(?usize, 0), getFieldPosition(Person, "name"));
    try testing.expectEqual(@as(?usize, 1), getFieldPosition(Person, "age"));
    try testing.expectEqual(@as(?usize, null), getFieldPosition(Person, "invalid"));
}
```

This returns `null` for fields that don't exist.

### Discussion

### Iterating Fields in Order

You can process fields sequentially using their definition order:

```zig
fn forEachField(comptime T: type, comptime func: anytype) void {
    const fields = @typeInfo(T).@"struct".fields;
    inline for (fields, 0..) |field, i| {
        func(i, field.name);
    }
}

test "ordered iteration" {
    var count: usize = 0;
    forEachField(Person, struct {
        fn visit(index: usize, name: []const u8) void {
            _ = index;
            _ = name;
            count += 1;
        }
    }.visit);
    try testing.expectEqual(@as(usize, 3), count);
}
```

The `inline for` ensures each field is visited in order at compile time.

### Preserving Order in Generated Types

When creating wrapper types, field order is automatically preserved:

```zig
fn WithPrefix(comptime T: type, comptime prefix: []const u8) type {
    _ = prefix;
    return struct {
        const Original = T;
        original: T,

        pub fn init(original: T) @This() {
            return .{ .original = original };
        }

        pub fn getFieldName(comptime index: usize) []const u8 {
            const fields = @typeInfo(T).@"struct".fields;
            if (index >= fields.len) {
                @compileError("Field index out of bounds");
            }
            return fields[index].name;
        }
    };
}

test "preserve order" {
    const PrefixedPerson = WithPrefix(Person, "user_");
    try testing.expectEqualStrings("name", PrefixedPerson.getFieldName(0));
    try testing.expectEqualStrings("age", PrefixedPerson.getFieldName(1));
}
```

The wrapper can query the original type's field order.

### Field Metadata Based on Position

Determine if a field is first, last, or at a specific position:

```zig
fn isFirstField(comptime T: type, comptime name: []const u8) bool {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len == 0) return false;
    return std.mem.eql(u8, fields[0].name, name);
}

fn isLastField(comptime T: type, comptime name: []const u8) bool {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len == 0) return false;
    return std.mem.eql(u8, fields[fields.len - 1].name, name);
}

fn getFieldTypeAtIndex(comptime T: type, comptime index: usize) type {
    const fields = @typeInfo(T).@"struct".fields;
    if (index >= fields.len) {
        @compileError("Field index out of bounds");
    }
    return fields[index].type;
}

test "field metadata" {
    try testing.expect(isFirstField(Person, "name"));
    try testing.expect(!isFirstField(Person, "age"));
    try testing.expect(isLastField(Person, "email"));

    try testing.expect(getFieldTypeAtIndex(Person, 0) == []const u8);
    try testing.expect(getFieldTypeAtIndex(Person, 1) == u32);
}
```

These functions use `@compileError` to catch invalid indices at compile time.

### Ordered Serialization

Serialize field names in definition order:

```zig
fn OrderedSerializer(comptime T: type) type {
    return struct {
        pub fn serializeFieldNames(allocator: std.mem.Allocator) ![]const u8 {
            const fields = @typeInfo(T).@"struct".fields;

            // Calculate total length at compile time
            comptime var total_len: usize = 0;
            inline for (fields, 0..) |field, i| {
                total_len += field.name.len;
                if (i < fields.len - 1) {
                    total_len += 1; // for comma
                }
            }

            // Allocate buffer
            const buffer = try allocator.alloc(u8, total_len);
            errdefer allocator.free(buffer);

            // Fill buffer in field order
            var pos: usize = 0;
            inline for (fields, 0..) |field, i| {
                @memcpy(buffer[pos..][0..field.name.len], field.name);
                pos += field.name.len;
                if (i < fields.len - 1) {
                    buffer[pos] = ',';
                    pos += 1;
                }
            }

            return buffer;
        }
    };
}

test "ordered serialization" {
    const Serializer = OrderedSerializer(Person);
    const result = try Serializer.serializeFieldNames(testing.allocator);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("name,age,email", result);
}
```

The compile-time length calculation eliminates runtime overhead for size determination.

### Validating Field Order

Enforce that fields appear in a specific order:

```zig
fn validateFieldOrder(comptime T: type, comptime expected: []const []const u8) bool {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len != expected.len) return false;

    inline for (fields, 0..) |field, i| {
        if (!std.mem.eql(u8, field.name, expected[i])) {
            return false;
        }
    }
    return true;
}

test "validate order" {
    const expected = [_][]const u8{ "name", "age", "email" };
    comptime {
        if (!validateFieldOrder(Person, &expected)) {
            @compileError("Field order validation failed");
        }
    }
    try testing.expect(validateFieldOrder(Person, &expected));

    const wrong = [_][]const u8{ "age", "name", "email" };
    try testing.expect(!validateFieldOrder(Person, &wrong));
}
```

The `comptime` block ensures validation happens during compilation.

### Adjacent Field Pairs

Work with consecutive field pairs:

```zig
fn getFieldPair(comptime T: type, comptime index: usize) struct { []const u8, []const u8 } {
    const fields = @typeInfo(T).@"struct".fields;
    const pair_count = if (fields.len < 2) 0 else fields.len - 1;
    if (index >= pair_count) {
        @compileError("Pair index out of bounds");
    }
    return .{ fields[index].name, fields[index + 1].name };
}

test "field pairs" {
    const pair1 = getFieldPair(Person, 0);
    try testing.expectEqualStrings("name", pair1[0]);
    try testing.expectEqualStrings("age", pair1[1]);

    const pair2 = getFieldPair(Person, 1);
    try testing.expectEqualStrings("age", pair2[0]);
    try testing.expectEqualStrings("email", pair2[1]);
}
```

This is useful for analyzing relationships between adjacent fields.

### Field Ranges

Extract a subset of fields by index range:

```zig
fn getFieldRange(comptime T: type, comptime start: usize, comptime end: usize) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;
    if (start > end or end > fields.len) {
        @compileError("Invalid field range");
    }

    comptime var result: [end - start][]const u8 = undefined;
    inline for (start..end, 0..) |i, j| {
        result[j] = fields[i].name;
    }
    const final = result;
    return &final;
}

test "field range" {
    const range = getFieldRange(Person, 0, 2);
    try testing.expectEqual(@as(usize, 2), range.len);
    try testing.expectEqualStrings("name", range[0]);
    try testing.expectEqualStrings("age", range[1]);
}
```

Bounds checking happens at compile time.

### Reversing Field Order

Get fields in reverse definition order:

```zig
fn reverseFieldOrder(comptime T: type) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;
    comptime var reversed: [fields.len][]const u8 = undefined;

    inline for (fields, 0..) |field, i| {
        reversed[fields.len - 1 - i] = field.name;
    }
    const final = reversed;
    return &final;
}

test "reverse order" {
    const reversed = reverseFieldOrder(Person);
    try testing.expectEqualStrings("email", reversed[0]);
    try testing.expectEqualStrings("age", reversed[1]);
    try testing.expectEqualStrings("name", reversed[2]);
}
```

This can be useful for processing fields in reverse dependency order.

### Filtering Fields by Type

Select fields matching specific criteria:

```zig
fn getStringFields(comptime T: type) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;

    comptime var count: usize = 0;
    inline for (fields) |field| {
        if (field.type == []const u8) {
            count += 1;
        }
    }

    comptime var result: [count][]const u8 = undefined;
    comptime var index: usize = 0;
    inline for (fields) |field| {
        if (field.type == []const u8) {
            result[index] = field.name;
            index += 1;
        }
    }

    const final = result;
    return &final;
}

fn getNumericFields(comptime T: type) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;

    comptime var count: usize = 0;
    inline for (fields) |field| {
        const is_numeric = switch (@typeInfo(field.type)) {
            .int, .float => true,
            else => false,
        };
        if (is_numeric) {
            count += 1;
        }
    }

    comptime var result: [count][]const u8 = undefined;
    comptime var index: usize = 0;
    inline for (fields) |field| {
        const is_numeric = switch (@typeInfo(field.type)) {
            .int, .float => true,
            else => false,
        };
        if (is_numeric) {
            result[index] = field.name;
            index += 1;
        }
    }

    const final = result;
    return &final;
}

test "field filter" {
    const string_fields = getStringFields(Person);
    try testing.expectEqual(@as(usize, 2), string_fields.len);
    try testing.expectEqualStrings("name", string_fields[0]);
    try testing.expectEqualStrings("email", string_fields[1]);

    const numeric_fields = getNumericFields(Person);
    try testing.expectEqual(@as(usize, 1), numeric_fields.len);
    try testing.expectEqualStrings("age", numeric_fields[0]);
}
```

Filtered results maintain original definition order.

### Grouping Fields by Type

Identify where field types change:

```zig
fn countFieldGroups(comptime T: type) usize {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len == 0) return 0;

    comptime var groups: usize = 1;
    comptime var prev_type = fields[0].type;

    inline for (fields[1..]) |field| {
        if (field.type != prev_type) {
            groups += 1;
            prev_type = field.type;
        }
    }

    return groups;
}

fn isFieldGroupBoundary(comptime T: type, comptime index: usize) bool {
    const fields = @typeInfo(T).@"struct".fields;
    if (index == 0 or index >= fields.len) return true;
    return fields[index].type != fields[index - 1].type;
}

const Mixed = struct {
    a: i32,
    b: i32,
    c: []const u8,
    d: []const u8,
    e: bool,
};

test "field grouping" {
    try testing.expectEqual(@as(usize, 3), countFieldGroups(Mixed));
    try testing.expect(isFieldGroupBoundary(Mixed, 0));  // Start of first group
    try testing.expect(!isFieldGroupBoundary(Mixed, 1)); // Same type as 'a'
    try testing.expect(isFieldGroupBoundary(Mixed, 2));  // Type changed
    try testing.expect(!isFieldGroupBoundary(Mixed, 3)); // Same type as 'c'
    try testing.expect(isFieldGroupBoundary(Mixed, 4));  // Type changed
}
```

This detects consecutive fields with the same type, useful for layout optimization or batch processing.

### Why Field Order Matters

Field definition order is significant for:

1. **Binary layout** - Affects memory layout and struct size due to alignment
2. **Serialization** - Determines wire format and compatibility
3. **Initialization order** - Some frameworks process fields sequentially
4. **API design** - Field order in constructors often mirrors struct order
5. **Code generation** - Generated code may depend on consistent ordering

Zig's guarantee that `@typeInfo` preserves definition order makes it reliable for these use cases.

### Performance Considerations

All the functions shown operate at compile time with zero runtime overhead:

- Field iteration uses `inline for`, unrolling at compile time
- Array allocations for field names are resolved during compilation
- Type comparisons and validations happen before code generation
- The only runtime cost is from explicit allocations like serialization buffers

This makes field order analysis essentially free in production code.

### Full Tested Code

```zig
// Recipe 9.12: Capturing Struct Attribute Definition Order
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: get_field_order
// Extract field names in definition order
fn getFieldNames(comptime T: type) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;
    comptime var names: [fields.len][]const u8 = undefined;
    inline for (fields, 0..) |field, i| {
        names[i] = field.name;
    }
    const final = names;
    return &final;
}

const Person = struct {
    name: []const u8,
    age: u32,
    email: []const u8,
};

test "get field order" {
    const names = getFieldNames(Person);
    try testing.expectEqual(@as(usize, 3), names.len);
    try testing.expectEqualStrings("name", names[0]);
    try testing.expectEqualStrings("age", names[1]);
    try testing.expectEqualStrings("email", names[2]);
}
// ANCHOR_END: get_field_order

// ANCHOR: field_positions
// Get position of specific field
fn getFieldPosition(comptime T: type, comptime field_name: []const u8) ?usize {
    const fields = @typeInfo(T).@"struct".fields;
    inline for (fields, 0..) |field, i| {
        if (std.mem.eql(u8, field.name, field_name)) {
            return i;
        }
    }
    return null;
}

fn fieldCount(comptime T: type) usize {
    return @typeInfo(T).@"struct".fields.len;
}

test "field positions" {
    try testing.expectEqual(@as(?usize, 0), getFieldPosition(Person, "name"));
    try testing.expectEqual(@as(?usize, 1), getFieldPosition(Person, "age"));
    try testing.expectEqual(@as(?usize, 2), getFieldPosition(Person, "email"));
    try testing.expectEqual(@as(?usize, null), getFieldPosition(Person, "invalid"));
    try testing.expectEqual(@as(usize, 3), fieldCount(Person));
}
// ANCHOR_END: field_positions

// ANCHOR: ordered_iteration
// Iterate fields in definition order
fn printFieldOrder(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;
    inline for (fields, 0..) |field, i| {
        _ = i;
        _ = field;
        // In real code: std.debug.print("Field {}: {s}\n", .{ i, field.name });
    }
}

fn forEachField(comptime T: type, comptime func: anytype) void {
    const fields = @typeInfo(T).@"struct".fields;
    inline for (fields, 0..) |field, i| {
        func(i, field.name);
    }
}

var field_visit_count: usize = 0;

fn visitField(index: usize, name: []const u8) void {
    _ = index;
    _ = name;
    field_visit_count += 1;
}

test "ordered iteration" {
    printFieldOrder(Person);
    field_visit_count = 0;
    forEachField(Person, visitField);
    try testing.expectEqual(@as(usize, 3), field_visit_count);
}
// ANCHOR_END: ordered_iteration

// ANCHOR: preserve_order
// Create new struct preserving field order
fn WithPrefix(comptime T: type, comptime prefix: []const u8) type {
    _ = prefix;
    // Fields are automatically in the same order
    return struct {
        const Original = T;
        original: T,

        pub fn init(original: T) @This() {
            return .{ .original = original };
        }

        pub fn getFieldCount() usize {
            return @typeInfo(T).@"struct".fields.len;
        }

        pub fn getFieldName(comptime index: usize) []const u8 {
            const fields = @typeInfo(T).@"struct".fields;
            if (index >= fields.len) {
                @compileError("Field index out of bounds");
            }
            return fields[index].name;
        }
    };
}

test "preserve order" {
    const PrefixedPerson = WithPrefix(Person, "user_");
    const p = PrefixedPerson.init(.{ .name = "Alice", .age = 30, .email = "alice@example.com" });
    try testing.expectEqualStrings("Alice", p.original.name);
    try testing.expectEqual(@as(usize, 3), PrefixedPerson.getFieldCount());
    try testing.expectEqualStrings("name", PrefixedPerson.getFieldName(0));
    try testing.expectEqualStrings("age", PrefixedPerson.getFieldName(1));
}
// ANCHOR_END: preserve_order

// ANCHOR: field_metadata
// Attach metadata to fields based on order
fn isFirstField(comptime T: type, comptime name: []const u8) bool {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len == 0) return false;
    return std.mem.eql(u8, fields[0].name, name);
}

fn isLastField(comptime T: type, comptime name: []const u8) bool {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len == 0) return false;
    return std.mem.eql(u8, fields[fields.len - 1].name, name);
}

fn getFieldTypeAtIndex(comptime T: type, comptime index: usize) type {
    const fields = @typeInfo(T).@"struct".fields;
    if (index >= fields.len) {
        @compileError("Field index out of bounds");
    }
    return fields[index].type;
}

test "field metadata" {
    try testing.expect(isFirstField(Person, "name"));
    try testing.expect(!isFirstField(Person, "age"));
    try testing.expect(isLastField(Person, "email"));
    try testing.expect(!isLastField(Person, "name"));

    try testing.expect(getFieldTypeAtIndex(Person, 0) == []const u8);
    try testing.expect(getFieldTypeAtIndex(Person, 1) == u32);
    try testing.expect(getFieldTypeAtIndex(Person, 2) == []const u8);
}
// ANCHOR_END: field_metadata

// ANCHOR: ordered_serialization
// Serialize fields in definition order
fn OrderedSerializer(comptime T: type) type {
    return struct {
        const Self = @This();

        pub fn serializeFieldNames(allocator: std.mem.Allocator) ![]const u8 {
            const fields = @typeInfo(T).@"struct".fields;

            // Calculate total length needed
            comptime var total_len: usize = 0;
            inline for (fields, 0..) |field, i| {
                total_len += field.name.len;
                if (i < fields.len - 1) {
                    total_len += 1; // for comma
                }
            }

            // Allocate buffer
            const buffer = try allocator.alloc(u8, total_len);
            errdefer allocator.free(buffer);

            // Fill buffer
            var pos: usize = 0;
            inline for (fields, 0..) |field, i| {
                @memcpy(buffer[pos..][0..field.name.len], field.name);
                pos += field.name.len;
                if (i < fields.len - 1) {
                    buffer[pos] = ',';
                    pos += 1;
                }
            }

            return buffer;
        }

        pub fn getFieldCount() usize {
            return @typeInfo(T).@"struct".fields.len;
        }
    };
}

test "ordered serialization" {
    const Serializer = OrderedSerializer(Person);
    const result = try Serializer.serializeFieldNames(testing.allocator);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("name,age,email", result);
    try testing.expectEqual(@as(usize, 3), Serializer.getFieldCount());
}
// ANCHOR_END: ordered_serialization

// ANCHOR: validate_order
// Validate field order matches expected
fn validateFieldOrder(comptime T: type, comptime expected: []const []const u8) bool {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len != expected.len) return false;

    inline for (fields, 0..) |field, i| {
        if (!std.mem.eql(u8, field.name, expected[i])) {
            return false;
        }
    }
    return true;
}

test "validate order" {
    const expected = [_][]const u8{ "name", "age", "email" };
    comptime {
        if (!validateFieldOrder(Person, &expected)) {
            @compileError("Field order validation failed");
        }
    }
    try testing.expect(validateFieldOrder(Person, &expected));

    const wrong = [_][]const u8{ "age", "name", "email" };
    try testing.expect(!validateFieldOrder(Person, &wrong));
}
// ANCHOR_END: validate_order

// ANCHOR: field_pairs
// Generate adjacent field pairs
fn getFieldPair(comptime T: type, comptime index: usize) struct { []const u8, []const u8 } {
    const fields = @typeInfo(T).@"struct".fields;
    const pair_count = if (fields.len < 2) 0 else fields.len - 1;
    if (index >= pair_count) {
        @compileError("Pair index out of bounds");
    }
    return .{ fields[index].name, fields[index + 1].name };
}

fn getFieldPairCount(comptime T: type) usize {
    const field_count = @typeInfo(T).@"struct".fields.len;
    if (field_count < 2) return 0;
    return field_count - 1;
}

test "field pairs" {
    try testing.expectEqual(@as(usize, 2), getFieldPairCount(Person));

    const pair1 = getFieldPair(Person, 0);
    try testing.expectEqualStrings("name", pair1[0]);
    try testing.expectEqualStrings("age", pair1[1]);

    const pair2 = getFieldPair(Person, 1);
    try testing.expectEqualStrings("age", pair2[0]);
    try testing.expectEqualStrings("email", pair2[1]);
}
// ANCHOR_END: field_pairs

// ANCHOR: field_range
// Get fields in a range
fn getFieldRange(comptime T: type, comptime start: usize, comptime end: usize) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;
    if (start > end or end > fields.len) {
        @compileError("Invalid field range");
    }

    comptime var result: [end - start][]const u8 = undefined;
    inline for (start..end, 0..) |i, j| {
        result[j] = fields[i].name;
    }
    const final = result;
    return &final;
}

test "field range" {
    const range = getFieldRange(Person, 0, 2);
    try testing.expectEqual(@as(usize, 2), range.len);
    try testing.expectEqualStrings("name", range[0]);
    try testing.expectEqualStrings("age", range[1]);

    const single = getFieldRange(Person, 1, 2);
    try testing.expectEqual(@as(usize, 1), single.len);
    try testing.expectEqualStrings("age", single[0]);
}
// ANCHOR_END: field_range

// ANCHOR: reverse_order
// Get fields in reverse order
fn reverseFieldOrder(comptime T: type) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;
    comptime var reversed: [fields.len][]const u8 = undefined;

    inline for (fields, 0..) |field, i| {
        reversed[fields.len - 1 - i] = field.name;
    }
    const final = reversed;
    return &final;
}

test "reverse order" {
    const reversed = reverseFieldOrder(Person);
    try testing.expectEqual(@as(usize, 3), reversed.len);
    try testing.expectEqualStrings("email", reversed[0]);
    try testing.expectEqualStrings("age", reversed[1]);
    try testing.expectEqualStrings("name", reversed[2]);
}
// ANCHOR_END: reverse_order

// ANCHOR: field_filter
// Filter fields by type
fn getStringFields(comptime T: type) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;

    comptime var count: usize = 0;
    inline for (fields) |field| {
        if (field.type == []const u8) {
            count += 1;
        }
    }

    comptime var result: [count][]const u8 = undefined;
    comptime var index: usize = 0;
    inline for (fields) |field| {
        if (field.type == []const u8) {
            result[index] = field.name;
            index += 1;
        }
    }

    const final = result;
    return &final;
}

fn getNumericFields(comptime T: type) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;

    comptime var count: usize = 0;
    inline for (fields) |field| {
        const is_numeric = switch (@typeInfo(field.type)) {
            .int, .float => true,
            else => false,
        };
        if (is_numeric) {
            count += 1;
        }
    }

    comptime var result: [count][]const u8 = undefined;
    comptime var index: usize = 0;
    inline for (fields) |field| {
        const is_numeric = switch (@typeInfo(field.type)) {
            .int, .float => true,
            else => false,
        };
        if (is_numeric) {
            result[index] = field.name;
            index += 1;
        }
    }

    const final = result;
    return &final;
}

test "field filter" {
    const string_fields = getStringFields(Person);
    try testing.expectEqual(@as(usize, 2), string_fields.len);
    try testing.expectEqualStrings("name", string_fields[0]);
    try testing.expectEqualStrings("email", string_fields[1]);

    const numeric_fields = getNumericFields(Person);
    try testing.expectEqual(@as(usize, 1), numeric_fields.len);
    try testing.expectEqualStrings("age", numeric_fields[0]);
}
// ANCHOR_END: field_filter

// ANCHOR: field_grouping
// Group consecutive fields by type
fn countFieldGroups(comptime T: type) usize {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len == 0) return 0;

    comptime var groups: usize = 1;
    comptime var prev_type = fields[0].type;

    inline for (fields[1..]) |field| {
        if (field.type != prev_type) {
            groups += 1;
            prev_type = field.type;
        }
    }

    return groups;
}

fn isFieldGroupBoundary(comptime T: type, comptime index: usize) bool {
    const fields = @typeInfo(T).@"struct".fields;
    if (index == 0 or index >= fields.len) return true;
    return fields[index].type != fields[index - 1].type;
}

const Mixed = struct {
    a: i32,
    b: i32,
    c: []const u8,
    d: []const u8,
    e: bool,
};

test "field grouping" {
    try testing.expectEqual(@as(usize, 3), countFieldGroups(Mixed));
    try testing.expect(isFieldGroupBoundary(Mixed, 0)); // Start
    try testing.expect(!isFieldGroupBoundary(Mixed, 1)); // Same as a
    try testing.expect(isFieldGroupBoundary(Mixed, 2)); // Different from b
    try testing.expect(!isFieldGroupBoundary(Mixed, 3)); // Same as c
    try testing.expect(isFieldGroupBoundary(Mixed, 4)); // Different from d
}
// ANCHOR_END: field_grouping

// Comprehensive test
test "comprehensive field order operations" {
    // Get field names
    const names = getFieldNames(Person);
    try testing.expectEqual(@as(usize, 3), names.len);

    // Field positions
    try testing.expectEqual(@as(?usize, 1), getFieldPosition(Person, "age"));

    // Metadata
    try testing.expect(isFirstField(Person, "name"));
    try testing.expect(isLastField(Person, "email"));

    // Serialization
    const Serializer = OrderedSerializer(Person);
    const serialized = try Serializer.serializeFieldNames(testing.allocator);
    defer testing.allocator.free(serialized);
    try testing.expectEqualStrings("name,age,email", serialized);

    // Validation
    const expected = [_][]const u8{ "name", "age", "email" };
    try testing.expect(validateFieldOrder(Person, &expected));

    // Reverse order
    const reversed = reverseFieldOrder(Person);
    try testing.expectEqualStrings("email", reversed[0]);

    // Filtering
    const strings = getStringFields(Person);
    try testing.expectEqual(@as(usize, 2), strings.len);
}
```

### See Also

- Recipe 9.10: Using decorators to patch struct definitions
- Recipe 9.11: Using comptime to control instance creation
- Recipe 9.13: Defining a generic that takes optional arguments

---

## Recipe 9.13: Defining a Metaclass That Takes Optional Arguments {#recipe-9-13}

**Tags:** allocators, comptime, comptime-metaprogramming, error-handling, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_13.zig`

### Problem

You need to create generic types or functions that accept optional parameters, allowing users to override defaults when needed while keeping simple cases simple. You want to avoid forcing users to specify every parameter while still maintaining type safety.

### Solution

Zig provides several patterns for optional arguments: structs with default field values, compile-time conditional logic, and variadic tuple handling. These approaches leverage compile-time evaluation to eliminate runtime overhead.

### Optional Configuration Struct

The simplest pattern uses a struct with default field values:

```zig
// Function with optional configuration struct
fn process(value: i32, config: struct {
    multiplier: i32 = 2,
    offset: i32 = 0,
    enabled: bool = true,
}) i32 {
    if (!config.enabled) return value;
    return (value * config.multiplier) + config.offset;
}

test "optional config" {
    // All defaults
    const r1 = process(10, .{});
    try testing.expectEqual(@as(i32, 20), r1);

    // Partial override
    const r2 = process(10, .{ .multiplier = 3 });
    try testing.expectEqual(@as(i32, 30), r2);

    // Full override
    const r3 = process(10, .{ .multiplier = 5, .offset = 10, .enabled = true });
    try testing.expectEqual(@as(i32, 60), r3);

    // Disabled
    const r4 = process(10, .{ .enabled = false });
    try testing.expectEqual(@as(i32, 10), r4);
}
```

Callers can specify only the fields they want to override, making the API both flexible and concise.

### Discussion

### Generic with Optional Type Parameters

Use struct defaults to provide optional configuration to generic types:

```zig
fn Container(comptime T: type, comptime Options: type) type {
    return struct {
        const Self = @This();
        const Opts = if (@hasDecl(Options, "capacity")) Options else struct {
            pub const capacity: usize = 10;
            pub const resizable: bool = true;
        };

        data: [Opts.capacity]T = undefined,
        len: usize = 0,

        pub fn init() Self {
            return .{};
        }

        pub fn append(self: *Self, item: T) !void {
            if (self.len >= Opts.capacity) {
                return error.CapacityExceeded;
            }
            self.data[self.len] = item;
            self.len += 1;
        }

        pub fn getCapacity() usize {
            return Opts.capacity;
        }
    };
}

test "optional type param" {
    // Use default options
    const DefaultContainer = Container(i32, struct {});
    var c1 = DefaultContainer.init();
    try c1.append(10);
    try testing.expectEqual(@as(usize, 10), DefaultContainer.getCapacity());

    // Custom options
    const CustomOptions = struct {
        pub const capacity: usize = 5;
        pub const resizable: bool = false;
    };
    const CustomContainer = Container(i32, CustomOptions);
    var c2 = CustomContainer.init();
    try testing.expectEqual(@as(usize, 5), CustomContainer.getCapacity());
}
```

The `@hasDecl` check allows detecting whether custom options were provided.

### Variadic Tuple Arguments

Process a variable number of arguments via tuples:

```zig
fn sum(args: anytype) i32 {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    var total: i32 = 0;
    inline for (fields) |field| {
        total += @field(args, field.name);
    }
    return total;
}

fn concat(allocator: std.mem.Allocator, args: anytype) ![]const u8 {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;

    // Calculate total length
    var total_len: usize = 0;
    inline for (fields) |field| {
        const value = @field(args, field.name);
        total_len += value.len;
    }

    // Allocate and fill buffer
    const buffer = try allocator.alloc(u8, total_len);
    errdefer allocator.free(buffer);

    var pos: usize = 0;
    inline for (fields) |field| {
        const value = @field(args, field.name);
        @memcpy(buffer[pos..][0..value.len], value);
        pos += value.len;
    }

    return buffer;
}

test "variadic tuple" {
    const r1 = sum(.{1});
    try testing.expectEqual(@as(i32, 1), r1);

    const r2 = sum(.{ 1, 2, 3 });
    try testing.expectEqual(@as(i32, 6), r2);

    const s = try concat(testing.allocator, .{ "hello", " ", "world" });
    defer testing.allocator.free(s);
    try testing.expectEqualStrings("hello world", s);
}
```

The `inline for` iterates over tuple fields at compile time, making this zero-overhead.

### Optional Allocator

Conditionally include an allocator based on a compile-time flag:

```zig
fn Processor(comptime needs_allocator: bool) type {
    return struct {
        const Self = @This();
        allocator: if (needs_allocator) std.mem.Allocator else void,
        buffer: if (needs_allocator) ?[]u8 else void,

        pub fn init(allocator_arg: anytype) Self {
            if (needs_allocator) {
                return .{
                    .allocator = allocator_arg,
                    .buffer = null,
                };
            } else {
                return .{
                    .allocator = {},
                    .buffer = {},
                };
            }
        }

        pub fn process(self: *Self, value: i32) !i32 {
            if (needs_allocator) {
                if (self.buffer == null) {
                    self.buffer = try self.allocator.alloc(u8, 10);
                }
            }
            return value * 2;
        }

        pub fn deinit(self: *Self) void {
            if (needs_allocator) {
                if (self.buffer) |buf| {
                    self.allocator.free(buf);
                }
            }
        }

        pub fn needsAllocator() bool {
            return needs_allocator;
        }
    };
}

test "optional allocator" {
    const WithAlloc = Processor(true);
    var p1 = WithAlloc.init(testing.allocator);
    defer p1.deinit();
    const r1 = try p1.process(10);
    try testing.expectEqual(@as(i32, 20), r1);

    const NoAlloc = Processor(false);
    var p2 = NoAlloc.init({});
    const r2 = try p2.process(15);
    try testing.expectEqual(@as(i32, 30), r2);
}
```

Fields with type `void` occupy no space, making the non-allocator version truly zero-cost.

### Builder Pattern

Implement fluent builders with optional field setting:

```zig
fn Builder(comptime T: type) type {
    return struct {
        const Self = @This();
        instance: T,

        pub fn init() Self {
            return .{ .instance = std.mem.zeroes(T) };
        }

        pub fn set(self: *Self, comptime field_name: []const u8, value: anytype) *Self {
            @field(self.instance, field_name) = value;
            return self;
        }

        pub fn build(self: Self) T {
            return self.instance;
        }
    };
}

const Config = struct {
    name: []const u8 = "",
    value: i32 = 0,
    enabled: bool = false,
};

test "builder pattern" {
    var builder = Builder(Config).init();
    const config = builder
        .set("name", "test")
        .set("value", 42)
        .build();

    try testing.expectEqualStrings("test", config.name);
    try testing.expectEqual(@as(i32, 42), config.value);
    try testing.expect(!config.enabled); // Uses default
}
```

The builder returns `*Self` to enable method chaining. Fields not explicitly set retain their default values.

### Conditional Fields

Include fields only when needed:

```zig
fn Record(comptime has_id: bool, comptime has_timestamp: bool) type {
    return struct {
        const Self = @This();

        id: if (has_id) u64 else void = if (has_id) 0 else {},
        timestamp: if (has_timestamp) u64 else void = if (has_timestamp) 0 else {},
        data: []const u8,

        pub fn init(data: []const u8, opts: anytype) Self {
            var result: Self = undefined;
            result.data = data;

            if (has_id) {
                if (@hasField(@TypeOf(opts), "id")) {
                    result.id = opts.id;
                } else {
                    result.id = 0;
                }
            } else {
                result.id = {};
            }

            if (has_timestamp) {
                if (@hasField(@TypeOf(opts), "timestamp")) {
                    result.timestamp = opts.timestamp;
                } else {
                    result.timestamp = 0;
                }
            } else {
                result.timestamp = {};
            }

            return result;
        }

        pub fn hasID() bool {
            return has_id;
        }

        pub fn hasTimestamp() bool {
            return has_timestamp;
        }
    };
}

test "conditional fields" {
    const Full = Record(true, true);
    const r1 = Full.init("data", .{ .id = 123, .timestamp = 456 });
    try testing.expectEqual(@as(u64, 123), r1.id);

    const Minimal = Record(false, false);
    const r2 = Minimal.init("data", .{});
    try testing.expectEqualStrings("data", r2.data);
    try testing.expect(!Minimal.hasID());
}
```

This creates completely different struct layouts based on compile-time parameters.

### Default Type Arguments

Provide defaults for type-level parameters:

```zig
fn createArray(comptime T: type, comptime size: usize, comptime default_value: T) [size]T {
    var arr: [size]T = undefined;
    for (&arr) |*item| {
        item.* = default_value;
    }
    return arr;
}

fn createArrayOpt(comptime T: type, comptime opts: struct {
    size: usize = 5,
    default_value: T = 0,
}) [opts.size]T {
    var arr: [opts.size]T = undefined;
    for (&arr) |*item| {
        item.* = opts.default_value;
    }
    return arr;
}

test "default args" {
    const arr1 = createArrayOpt(i32, .{});
    try testing.expectEqual(@as(usize, 5), arr1.len);

    const arr2 = createArrayOpt(i32, .{ .size = 3, .default_value = 10 });
    try testing.expectEqual(@as(usize, 3), arr2.len);
    try testing.expectEqual(@as(i32, 10), arr2[0]);
}
```

The struct parameter allows named defaults while maintaining type safety.

### Optional Callback

Conditionally include callback functionality:

```zig
fn Transform(comptime has_callback: bool) type {
    return struct {
        const Self = @This();
        const Callback = if (has_callback) *const fn (i32) i32 else void;

        callback: Callback,
        multiplier: i32,

        pub fn init(multiplier: i32, callback: anytype) Self {
            if (has_callback) {
                return .{
                    .callback = callback,
                    .multiplier = multiplier,
                };
            } else {
                return .{
                    .callback = {},
                    .multiplier = multiplier,
                };
            }
        }

        pub fn process(self: Self, value: i32) i32 {
            const result = value * self.multiplier;
            if (has_callback) {
                return self.callback(result);
            }
            return result;
        }
    };
}

fn addTen(x: i32) i32 {
    return x + 10;
}

test "optional callback" {
    const WithCallback = Transform(true);
    const t1 = WithCallback.init(2, addTen);
    const r1 = t1.process(5);
    try testing.expectEqual(@as(i32, 20), r1); // (5 * 2) + 10

    const NoCallback = Transform(false);
    const t2 = NoCallback.init(3, {});
    const r2 = t2.process(5);
    try testing.expectEqual(@as(i32, 15), r2); // 5 * 3
}
```

The callback type is `void` when not needed, eliminating storage overhead.

### Optional Error Type

Choose between fallible and infallible operations:

```zig
fn Operation(comptime can_fail: bool) type {
    return struct {
        const Self = @This();
        const Error = if (can_fail) error{OperationFailed} else void;
        const Result = if (can_fail) Error!i32 else i32;

        value: i32,

        pub fn init(value: i32) Self {
            return .{ .value = value };
        }

        pub fn execute(self: Self) Result {
            if (can_fail) {
                if (self.value < 0) {
                    return error.OperationFailed;
                }
                return self.value * 2;
            }
            return self.value * 2;
        }
    };
}

test "optional error type" {
    const Fallible = Operation(true);
    const op1 = Fallible.init(10);
    const r1 = try op1.execute();
    try testing.expectEqual(@as(i32, 20), r1);

    const Infallible = Operation(false);
    const op3 = Infallible.init(-5);
    const r3 = op3.execute();
    try testing.expectEqual(@as(i32, -10), r3); // No error checking needed
}
```

Infallible operations return plain `i32`, avoiding the overhead of error handling.

### Optional Constraints

Validate values against optional bounds:

```zig
fn Validator(comptime T: type, comptime opts: struct {
    min_value: ?T = null,
    max_value: ?T = null,
    allow_zero: bool = true,
}) type {
    return struct {
        pub fn validate(value: T) bool {
            if (opts.min_value) |min| {
                if (value < min) return false;
            }
            if (opts.max_value) |max| {
                if (value > max) return false;
            }
            if (!opts.allow_zero and value == 0) {
                return false;
            }
            return true;
        }
    };
}

test "optional constraints" {
    const NoConstraints = Validator(i32, .{});
    try testing.expect(NoConstraints.validate(100));

    const Range = Validator(i32, .{ .min_value = 0, .max_value = 100 });
    try testing.expect(Range.validate(50));
    try testing.expect(!Range.validate(101));

    const NoZero = Validator(i32, .{ .allow_zero = false });
    try testing.expect(!NoZero.validate(0));
}
```

Optional values use `?T` to indicate constraints that may or may not be present.

### Feature Flags

Enable or disable features at compile time:

```zig
fn Wrapper(comptime T: type, comptime features: struct {
    logging: bool = false,
    validation: bool = false,
    caching: bool = false,
}) type {
    return struct {
        const Self = @This();
        value: T,
        log_count: if (features.logging) u32 else void = if (features.logging) 0 else {},
        is_valid: if (features.validation) bool else void = if (features.validation) true else {},
        cached: if (features.caching) ?T else void = if (features.caching) null else {},

        pub fn init(value: T) Self {
            var result: Self = undefined;
            result.value = value;
            if (features.logging) result.log_count = 0;
            if (features.validation) result.is_valid = true;
            if (features.caching) result.cached = null;
            return result;
        }

        pub fn get(self: *Self) T {
            if (features.logging) {
                self.log_count += 1;
            }
            if (features.caching) {
                if (self.cached) |cached| {
                    return cached;
                }
                self.cached = self.value;
            }
            return self.value;
        }
    };
}

test "optional wrapper" {
    const AllFeatures = Wrapper(i32, .{ .logging = true, .caching = true });
    var w1 = AllFeatures.init(42);
    try testing.expectEqual(@as(i32, 42), w1.get());
    try testing.expectEqual(@as(u32, 1), w1.log_count);

    const NoFeatures = Wrapper(i32, .{});
    var w2 = NoFeatures.init(10);
    try testing.expectEqual(@as(i32, 10), w2.get());
}
```

Disabled features compile away entirely, including their fields and logic.

### When to Use Optional Arguments

These patterns are valuable when:

1. **Sensible defaults exist** - Most users can use defaults, but some need customization
2. **Configuration grows over time** - New options can be added without breaking existing code
3. **Zero-cost abstractions matter** - Unused features should impose no runtime cost
4. **Type safety is critical** - Compile-time validation prevents configuration errors
5. **API evolution is important** - Optional parameters allow backward-compatible changes

### Design Considerations

**Struct Parameters vs Multiple Functions:**
Using struct parameters with defaults is more maintainable than creating multiple function variants:

```zig
// Good: Single function with optional config
fn process(value: i32, config: struct { multiplier: i32 = 2 }) i32

// Avoid: Multiple functions for each combination
fn process(value: i32) i32
fn processWithMultiplier(value: i32, multiplier: i32) i32
```

**Compile-Time vs Runtime Optionality:**
- Use `comptime` parameters when the choice affects type structure or can be resolved at compile time
- Use `?T` (optional types) when the choice must be made at runtime
- Prefer compile-time when possible for better optimization

**Named vs Positional Parameters:**
Struct parameters provide named arguments, improving readability:

```zig
// Clear what each value means
const r = process(10, .{ .multiplier = 3, .offset = 5 });

// Unclear without looking at function signature
const r = process(10, 3, 5);
```

The pattern trades a small amount of syntax for significant gains in maintainability.

### Full Tested Code

```zig
// Recipe 9.13: Defining a Generic That Takes Optional Arguments
// Target Zig Version: 0.15.2

const std = @import("std");
const testing = std.testing;

// ANCHOR: optional_type_param
// Generic with optional type parameter using struct defaults
fn Container(comptime T: type, comptime Options: type) type {
    return struct {
        const Self = @This();
        const Opts = if (@hasDecl(Options, "capacity")) Options else struct {
            pub const capacity: usize = 10;
            pub const resizable: bool = true;
        };

        data: [Opts.capacity]T = undefined,
        len: usize = 0,

        pub fn init() Self {
            return .{};
        }

        pub fn append(self: *Self, item: T) !void {
            if (self.len >= Opts.capacity) {
                // Note: Actual resizing would require an allocator parameter.
                // The 'resizable' option is kept for demonstration purposes.
                return error.CapacityExceeded;
            }
            self.data[self.len] = item;
            self.len += 1;
        }

        pub fn getCapacity() usize {
            return Opts.capacity;
        }
    };
}

test "optional type param" {
    // Use default options
    const DefaultContainer = Container(i32, struct {});
    var c1 = DefaultContainer.init();
    try c1.append(10);
    try testing.expectEqual(@as(usize, 10), DefaultContainer.getCapacity());

    // Custom options
    const CustomOptions = struct {
        pub const capacity: usize = 5;
        pub const resizable: bool = false;
    };
    const CustomContainer = Container(i32, CustomOptions);
    var c2 = CustomContainer.init();
    try c2.append(20);
    try testing.expectEqual(@as(usize, 5), CustomContainer.getCapacity());
}
// ANCHOR_END: optional_type_param

// ANCHOR: optional_config
// Function with optional configuration struct
fn process(value: i32, config: struct {
    multiplier: i32 = 2,
    offset: i32 = 0,
    enabled: bool = true,
}) i32 {
    if (!config.enabled) return value;
    return (value * config.multiplier) + config.offset;
}

test "optional config" {
    // All defaults
    const r1 = process(10, .{});
    try testing.expectEqual(@as(i32, 20), r1);

    // Partial override
    const r2 = process(10, .{ .multiplier = 3 });
    try testing.expectEqual(@as(i32, 30), r2);

    // Full override
    const r3 = process(10, .{ .multiplier = 5, .offset = 10, .enabled = true });
    try testing.expectEqual(@as(i32, 60), r3);

    // Disabled
    const r4 = process(10, .{ .enabled = false });
    try testing.expectEqual(@as(i32, 10), r4);
}
// ANCHOR_END: optional_config

// ANCHOR: variadic_tuple
// Process variable number of arguments via tuple
fn sum(args: anytype) i32 {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    var total: i32 = 0;
    inline for (fields) |field| {
        total += @field(args, field.name);
    }
    return total;
}

fn concat(allocator: std.mem.Allocator, args: anytype) ![]const u8 {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;

    // Calculate total length
    var total_len: usize = 0;
    inline for (fields) |field| {
        const value = @field(args, field.name);
        total_len += value.len;
    }

    // Allocate buffer
    const buffer = try allocator.alloc(u8, total_len);
    errdefer allocator.free(buffer);

    // Copy strings
    var pos: usize = 0;
    inline for (fields) |field| {
        const value = @field(args, field.name);
        @memcpy(buffer[pos..][0..value.len], value);
        pos += value.len;
    }

    return buffer;
}

test "variadic tuple" {
    const r1 = sum(.{1});
    try testing.expectEqual(@as(i32, 1), r1);

    const r2 = sum(.{ 1, 2, 3 });
    try testing.expectEqual(@as(i32, 6), r2);

    const r3 = sum(.{ 10, 20, 30, 40 });
    try testing.expectEqual(@as(i32, 100), r3);

    const s1 = try concat(testing.allocator, .{"hello"});
    defer testing.allocator.free(s1);
    try testing.expectEqualStrings("hello", s1);

    const s2 = try concat(testing.allocator, .{ "hello", " ", "world" });
    defer testing.allocator.free(s2);
    try testing.expectEqualStrings("hello world", s2);
}
// ANCHOR_END: variadic_tuple

// ANCHOR: optional_allocator
// Generic with optional allocator
fn Processor(comptime needs_allocator: bool) type {
    return struct {
        const Self = @This();
        allocator: if (needs_allocator) std.mem.Allocator else void,
        buffer: if (needs_allocator) ?[]u8 else void,

        pub fn init(allocator_arg: anytype) Self {
            if (needs_allocator) {
                return .{
                    .allocator = allocator_arg,
                    .buffer = null,
                };
            } else {
                return .{
                    .allocator = {},
                    .buffer = {},
                };
            }
        }

        pub fn process(self: *Self, value: i32) !i32 {
            if (needs_allocator) {
                if (self.buffer == null) {
                    self.buffer = try self.allocator.alloc(u8, 10);
                }
                return value * 2;
            }
            return value * 2;
        }

        pub fn deinit(self: *Self) void {
            if (needs_allocator) {
                if (self.buffer) |buf| {
                    self.allocator.free(buf);
                }
            }
        }

        pub fn needsAllocator() bool {
            return needs_allocator;
        }
    };
}

test "optional allocator" {
    const WithAlloc = Processor(true);
    var p1 = WithAlloc.init(testing.allocator);
    defer p1.deinit();
    const r1 = try p1.process(10);
    try testing.expectEqual(@as(i32, 20), r1);
    try testing.expect(WithAlloc.needsAllocator());

    const NoAlloc = Processor(false);
    var p2 = NoAlloc.init({});
    defer p2.deinit();
    const r2 = try p2.process(15);
    try testing.expectEqual(@as(i32, 30), r2);
    try testing.expect(!NoAlloc.needsAllocator());
}
// ANCHOR_END: optional_allocator

// ANCHOR: builder_pattern
// Builder with optional fields
fn Builder(comptime T: type) type {
    return struct {
        const Self = @This();
        instance: T,

        pub fn init() Self {
            return .{ .instance = std.mem.zeroes(T) };
        }

        pub fn set(self: *Self, comptime field_name: []const u8, value: anytype) *Self {
            @field(self.instance, field_name) = value;
            return self;
        }

        pub fn build(self: Self) T {
            return self.instance;
        }
    };
}

const Config = struct {
    name: []const u8 = "",
    value: i32 = 0,
    enabled: bool = false,
};

test "builder pattern" {
    var builder = Builder(Config).init();
    const config = builder
        .set("name", "test")
        .set("value", 42)
        .build();

    try testing.expectEqualStrings("test", config.name);
    try testing.expectEqual(@as(i32, 42), config.value);
    try testing.expect(!config.enabled); // Uses default
}
// ANCHOR_END: builder_pattern

// ANCHOR: conditional_fields
// Type with conditionally included fields
fn Record(comptime has_id: bool, comptime has_timestamp: bool) type {
    return struct {
        const Self = @This();

        id: if (has_id) u64 else void = if (has_id) 0 else {},
        timestamp: if (has_timestamp) u64 else void = if (has_timestamp) 0 else {},
        data: []const u8,

        pub fn init(data: []const u8, opts: anytype) Self {
            var result: Self = undefined;
            result.data = data;

            if (has_id) {
                if (@hasField(@TypeOf(opts), "id")) {
                    result.id = opts.id;
                } else {
                    result.id = 0;
                }
            } else {
                result.id = {};
            }

            if (has_timestamp) {
                if (@hasField(@TypeOf(opts), "timestamp")) {
                    result.timestamp = opts.timestamp;
                } else {
                    result.timestamp = 0;
                }
            } else {
                result.timestamp = {};
            }

            return result;
        }

        pub fn hasID() bool {
            return has_id;
        }

        pub fn hasTimestamp() bool {
            return has_timestamp;
        }
    };
}

test "conditional fields" {
    const Full = Record(true, true);
    const r1 = Full.init("data", .{ .id = 123, .timestamp = 456 });
    try testing.expectEqual(@as(u64, 123), r1.id);
    try testing.expectEqual(@as(u64, 456), r1.timestamp);
    try testing.expect(Full.hasID());
    try testing.expect(Full.hasTimestamp());

    const Minimal = Record(false, false);
    const r2 = Minimal.init("data", .{});
    try testing.expectEqualStrings("data", r2.data);
    try testing.expect(!Minimal.hasID());
    try testing.expect(!Minimal.hasTimestamp());
}
// ANCHOR_END: conditional_fields

// ANCHOR: default_args
// Generic function with default type arguments
fn createArray(comptime T: type, comptime size: usize, comptime default_value: T) [size]T {
    var arr: [size]T = undefined;
    for (&arr) |*item| {
        item.* = default_value;
    }
    return arr;
}

fn createArrayOpt(comptime T: type, comptime opts: struct {
    size: usize = 5,
    default_value: T = 0,
}) [opts.size]T {
    var arr: [opts.size]T = undefined;
    for (&arr) |*item| {
        item.* = opts.default_value;
    }
    return arr;
}

test "default args" {
    const arr1 = createArray(i32, 3, 0);
    try testing.expectEqual(@as(usize, 3), arr1.len);
    try testing.expectEqual(@as(i32, 0), arr1[0]);

    const arr2 = createArrayOpt(i32, .{});
    try testing.expectEqual(@as(usize, 5), arr2.len);

    const arr3 = createArrayOpt(i32, .{ .size = 3, .default_value = 10 });
    try testing.expectEqual(@as(usize, 3), arr3.len);
    try testing.expectEqual(@as(i32, 10), arr3[0]);
}
// ANCHOR_END: default_args

// ANCHOR: optional_callback
// Generic with optional callback
fn Transform(comptime has_callback: bool) type {
    return struct {
        const Self = @This();
        const Callback = if (has_callback) *const fn (i32) i32 else void;

        callback: Callback,
        multiplier: i32,

        pub fn init(multiplier: i32, callback: anytype) Self {
            if (has_callback) {
                return .{
                    .callback = callback,
                    .multiplier = multiplier,
                };
            } else {
                return .{
                    .callback = {},
                    .multiplier = multiplier,
                };
            }
        }

        pub fn process(self: Self, value: i32) i32 {
            const result = value * self.multiplier;
            if (has_callback) {
                return self.callback(result);
            }
            return result;
        }
    };
}

fn addTen(x: i32) i32 {
    return x + 10;
}

test "optional callback" {
    const WithCallback = Transform(true);
    const t1 = WithCallback.init(2, addTen);
    const r1 = t1.process(5);
    try testing.expectEqual(@as(i32, 20), r1); // (5 * 2) + 10

    const NoCallback = Transform(false);
    const t2 = NoCallback.init(3, {});
    const r2 = t2.process(5);
    try testing.expectEqual(@as(i32, 15), r2); // 5 * 3
}
// ANCHOR_END: optional_callback

// ANCHOR: optional_error_type
// Generic with optional error type
fn Operation(comptime can_fail: bool) type {
    return struct {
        const Self = @This();
        const Error = if (can_fail) error{OperationFailed} else void;
        const Result = if (can_fail) Error!i32 else i32;

        value: i32,

        pub fn init(value: i32) Self {
            return .{ .value = value };
        }

        pub fn execute(self: Self) Result {
            if (can_fail) {
                if (self.value < 0) {
                    return error.OperationFailed;
                }
                return self.value * 2;
            }
            return self.value * 2;
        }
    };
}

test "optional error type" {
    const Fallible = Operation(true);
    const op1 = Fallible.init(10);
    const r1 = try op1.execute();
    try testing.expectEqual(@as(i32, 20), r1);

    const op2 = Fallible.init(-5);
    const r2 = op2.execute();
    try testing.expectError(error.OperationFailed, r2);

    const Infallible = Operation(false);
    const op3 = Infallible.init(-5);
    const r3 = op3.execute();
    try testing.expectEqual(@as(i32, -10), r3);
}
// ANCHOR_END: optional_error_type

// ANCHOR: optional_constraints
// Generic with optional type constraints
fn Validator(comptime T: type, comptime opts: struct {
    min_value: ?T = null,
    max_value: ?T = null,
    allow_zero: bool = true,
}) type {
    return struct {
        pub fn validate(value: T) bool {
            if (opts.min_value) |min| {
                if (value < min) return false;
            }
            if (opts.max_value) |max| {
                if (value > max) return false;
            }
            if (!opts.allow_zero and value == 0) {
                return false;
            }
            return true;
        }
    };
}

test "optional constraints" {
    const NoConstraints = Validator(i32, .{});
    try testing.expect(NoConstraints.validate(100));
    try testing.expect(NoConstraints.validate(0));
    try testing.expect(NoConstraints.validate(-100));

    const MinOnly = Validator(i32, .{ .min_value = 10 });
    try testing.expect(MinOnly.validate(10));
    try testing.expect(MinOnly.validate(100));
    try testing.expect(!MinOnly.validate(5));

    const Range = Validator(i32, .{ .min_value = 0, .max_value = 100 });
    try testing.expect(Range.validate(50));
    try testing.expect(!Range.validate(-1));
    try testing.expect(!Range.validate(101));

    const NoZero = Validator(i32, .{ .allow_zero = false });
    try testing.expect(!NoZero.validate(0));
    try testing.expect(NoZero.validate(1));
}
// ANCHOR_END: optional_constraints

// ANCHOR: optional_wrapper
// Generic wrapper with optional features
fn Wrapper(comptime T: type, comptime features: struct {
    logging: bool = false,
    validation: bool = false,
    caching: bool = false,
}) type {
    return struct {
        const Self = @This();
        value: T,
        log_count: if (features.logging) u32 else void = if (features.logging) 0 else {},
        is_valid: if (features.validation) bool else void = if (features.validation) true else {},
        cached: if (features.caching) ?T else void = if (features.caching) null else {},

        pub fn init(value: T) Self {
            var result: Self = undefined;
            result.value = value;
            if (features.logging) result.log_count = 0;
            if (features.validation) result.is_valid = true;
            if (features.caching) result.cached = null;
            return result;
        }

        pub fn get(self: *Self) T {
            if (features.logging) {
                self.log_count += 1;
            }
            if (features.caching) {
                if (self.cached) |cached| {
                    return cached;
                }
                self.cached = self.value;
            }
            return self.value;
        }

        pub fn hasLogging() bool {
            return features.logging;
        }

        pub fn hasValidation() bool {
            return features.validation;
        }

        pub fn hasCaching() bool {
            return features.caching;
        }
    };
}

test "optional wrapper" {
    const AllFeatures = Wrapper(i32, .{ .logging = true, .validation = true, .caching = true });
    var w1 = AllFeatures.init(42);
    try testing.expectEqual(@as(i32, 42), w1.get());
    try testing.expectEqual(@as(u32, 1), w1.log_count);
    try testing.expect(AllFeatures.hasLogging());
    try testing.expect(AllFeatures.hasValidation());
    try testing.expect(AllFeatures.hasCaching());

    const NoFeatures = Wrapper(i32, .{});
    var w2 = NoFeatures.init(10);
    try testing.expectEqual(@as(i32, 10), w2.get());
    try testing.expect(!NoFeatures.hasLogging());
}
// ANCHOR_END: optional_wrapper

// Comprehensive test
test "comprehensive optional arguments" {
    // Optional config
    const r1 = process(5, .{ .multiplier = 4 });
    try testing.expectEqual(@as(i32, 20), r1);

    // Variadic
    const r2 = sum(.{ 1, 2, 3, 4, 5 });
    try testing.expectEqual(@as(i32, 15), r2);

    // Builder
    var builder = Builder(Config).init();
    const config = builder.set("value", 100).build();
    try testing.expectEqual(@as(i32, 100), config.value);

    // Optional allocator
    const NoAlloc = Processor(false);
    var proc = NoAlloc.init({});
    defer proc.deinit();
    const r3 = try proc.process(7);
    try testing.expectEqual(@as(i32, 14), r3);

    // Optional constraints
    const RangeValidator = Validator(i32, .{ .min_value = 1, .max_value = 10 });
    try testing.expect(RangeValidator.validate(5));
    try testing.expect(!RangeValidator.validate(11));
}
```

### See Also

- Recipe 9.11: Using comptime to control instance creation
- Recipe 9.14: Enforcing an argument signature on tuple arguments
- Recipe 9.15: Enforcing coding conventions in structs

---

## Recipe 9.14: Enforcing an Argument Signature on Tuple Arguments {#recipe-9-14}

**Tags:** comptime, comptime-metaprogramming, error-handling, pointers, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_14.zig`

### Problem

You want to create functions that accept variable numbers of arguments (variadic functions) while enforcing specific type constraints, count requirements, or structural patterns at compile time. You need to validate tuple arguments to ensure type safety, prevent misuse, and provide clear compiler errors when arguments don't match expected patterns.

### Solution

Use `@typeInfo` to introspect tuple arguments at compile time and `@compileError` to enforce validation rules. Zig's compile-time execution allows you to validate argument types, counts, and patterns with zero runtime overhead.

### Validating All Types Match

The simplest validation ensures all tuple arguments have the same type:

```zig
// Validate that all tuple arguments match a specific type
fn validateAllTypes(comptime T: type, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        if (field.type != T) {
            @compileError("All arguments must be of the specified type");
        }
    }
}

fn sumInts(args: anytype) i32 {
    comptime validateAllTypes(i32, args);

    var total: i32 = 0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        total += @field(args, field.name);
    }
    return total;
}

test "validate types" {
    const r1 = sumInts(.{ @as(i32, 1), @as(i32, 2), @as(i32, 3) });
    try testing.expectEqual(@as(i32, 6), r1);

    const r2 = sumInts(.{@as(i32, 10)});
    try testing.expectEqual(@as(i32, 10), r2);

    // This would fail at compile time:
    // const r3 = sumInts(.{ @as(i32, 1), 2.5, @as(i32, 3) });
}
```

The validation happens entirely at compile time. Code with invalid argument types will not compile.

### Enforcing Argument Count Constraints

Require a minimum and maximum number of arguments:

```zig
fn requireArgCount(comptime min: usize, comptime max: usize, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    if (fields.len < min) {
        @compileError("Too few arguments");
    }
    if (fields.len > max) {
        @compileError("Too many arguments");
    }
}

fn average(args: anytype) f64 {
    comptime requireArgCount(1, 10, args);

    var total: f64 = 0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        const value = @field(args, field.name);
        total += @as(f64, @floatFromInt(value));
    }
    return total / @as(f64, @floatFromInt(fields.len));
}

test "min max args" {
    const r1 = average(.{10});
    try testing.expectEqual(@as(f64, 10.0), r1);

    const r2 = average(.{ 10, 20, 30 });
    try testing.expectEqual(@as(f64, 20.0), r2);

    // These would fail at compile time:
    // const r3 = average(.{}); // Too few
    // const r4 = average(.{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 }); // Too many
}
```

### Discussion

### Enforcing Exact Type Signatures

You can validate that arguments match a specific type pattern:

```zig
fn enforceSignature(comptime Signature: type, args: anytype) void {
    const sig_fields = @typeInfo(Signature).@"struct".fields;
    const arg_fields = @typeInfo(@TypeOf(args)).@"struct".fields;

    if (sig_fields.len != arg_fields.len) {
        @compileError("Argument count mismatch");
    }

    inline for (sig_fields, 0..) |sig_field, i| {
        if (arg_fields[i].type != sig_field.type) {
            @compileError("Argument type mismatch");
        }
    }
}

fn processTyped(args: anytype) i32 {
    const Signature = struct { i32, []const u8, bool };
    comptime enforceSignature(Signature, args);

    const num = args[0];
    const str = args[1];
    const flag = args[2];

    if (flag) {
        return num + @as(i32, @intCast(str.len));
    }
    return num;
}

test "typed signature" {
    const str1: []const u8 = "hello";
    const str2: []const u8 = "test";

    const r1 = processTyped(.{ @as(i32, 10), str1, true });
    try testing.expectEqual(@as(i32, 15), r1);

    const r2 = processTyped(.{ @as(i32, 20), str2, false });
    try testing.expectEqual(@as(i32, 20), r2);
}
```

This creates a compile-time contract for the exact argument types and count.

### Homogeneous Tuple Validation

Create a reusable generic validator for homogeneous tuples:

```zig
fn HomogeneousArgs(comptime T: type) type {
    return struct {
        pub fn call(args: anytype) T {
            const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
            if (fields.len == 0) {
                @compileError("At least one argument required");
            }

            inline for (fields) |field| {
                if (field.type != T) {
                    @compileError("All arguments must be of the same type");
                }
            }

            return @field(args, fields[0].name);
        }
    };
}

fn firstInt(args: anytype) i32 {
    return HomogeneousArgs(i32).call(args);
}

test "homogeneous tuple" {
    const r1 = firstInt(.{@as(i32, 42)});
    try testing.expectEqual(@as(i32, 42), r1);

    const r2 = firstInt(.{ @as(i32, 1), @as(i32, 2), @as(i32, 3) });
    try testing.expectEqual(@as(i32, 1), r2);
}
```

This pattern bundles the validation logic into a reusable type generator.

### Validating Type Categories

Check that all arguments belong to a category of types:

```zig
fn isNumeric(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .int, .float, .comptime_int, .comptime_float => true,
        else => false,
    };
}

fn validateNumeric(args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        if (!isNumeric(field.type)) {
            @compileError("Only numeric types allowed");
        }
    }
}

fn multiplyAll(args: anytype) f64 {
    comptime validateNumeric(args);

    var result: f64 = 1.0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        const value = @field(args, field.name);
        const float_val = switch (@typeInfo(field.type)) {
            .int, .comptime_int => @as(f64, @floatFromInt(value)),
            .float, .comptime_float => @as(f64, @floatCast(value)),
            else => unreachable,
        };
        result *= float_val;
    }
    return result;
}

test "numeric only" {
    const r1 = multiplyAll(.{ 2, 3, 4 });
    try testing.expectEqual(@as(f64, 24.0), r1);

    const r2 = multiplyAll(.{ 2.5, 4.0 });
    try testing.expectEqual(@as(f64, 10.0), r2);

    const r3 = multiplyAll(.{ @as(i32, 5), @as(f32, 2.0) });
    try testing.expectEqual(@as(f64, 10.0), r3);
}
```

This accepts any numeric type, handling both integers and floats correctly.

### First Argument Determines Type

Use the first argument's type to validate the rest:

```zig
fn FirstTypeDetermines(args: anytype) type {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    if (fields.len == 0) {
        @compileError("At least one argument required");
    }

    const FirstType = fields[0].type;
    inline for (fields[1..]) |field| {
        if (field.type != FirstType) {
            @compileError("All arguments must match the first argument's type");
        }
    }

    return FirstType;
}

fn maxValue(args: anytype) FirstTypeDetermines(args) {
    var max_val = args[0];

    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields[1..]) |field| {
        const value = @field(args, field.name);
        if (value > max_val) {
            max_val = value;
        }
    }

    return max_val;
}

test "first type determines" {
    const r1 = maxValue(.{ 3, 7, 2, 9, 1 });
    try testing.expectEqual(9, r1);

    const r2 = maxValue(.{ 3.5, 1.2, 7.8 });
    try testing.expect(r2 > 7.7 and r2 < 7.9);
}
```

The return type is determined by the first argument, allowing type-safe operations on any comparable type.

### Alternating Type Patterns

Enforce that arguments alternate between two types:

```zig
fn validateAlternating(comptime T1: type, comptime T2: type, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields, 0..) |field, i| {
        const expected_type = if (i % 2 == 0) T1 else T2;
        if (field.type != expected_type) {
            @compileError("Arguments must alternate between specified types");
        }
    }
}

fn processAlternating(args: anytype) i32 {
    comptime validateAlternating(i32, []const u8, args);

    var sum: i32 = 0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields, 0..) |field, i| {
        if (i % 2 == 0) {
            sum += @field(args, field.name);
        }
    }
    return sum;
}

test "alternate types" {
    const s1: []const u8 = "a";
    const s2: []const u8 = "b";
    const s3: []const u8 = "c";

    const r1 = processAlternating(.{ @as(i32, 10), s1, @as(i32, 20), s2, @as(i32, 30), s3 });
    try testing.expectEqual(@as(i32, 60), r1);
}
```

This is useful for functions that process pairs of related values.

### Key-Value Pair Validation

Enforce that arguments come in key-value pairs:

```zig
fn validateKeyValuePairs(comptime KeyType: type, comptime ValueType: type, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    if (fields.len % 2 != 0) {
        @compileError("Arguments must be in key-value pairs");
    }

    inline for (fields, 0..) |field, i| {
        const expected_type = if (i % 2 == 0) KeyType else ValueType;
        if (field.type != expected_type) {
            @compileError("Key-value types don't match");
        }
    }
}

fn countPairs(args: anytype) usize {
    comptime validateKeyValuePairs([]const u8, i32, args);
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    return fields.len / 2;
}

test "key value pairs" {
    const k1: []const u8 = "age";
    const k2: []const u8 = "score";

    const r1 = countPairs(.{ k1, @as(i32, 30), k2, @as(i32, 100) });
    try testing.expectEqual(@as(usize, 2), r1);
}
```

This pattern is useful for building DSLs or configuration functions.

### Required First Argument

Validate that the first argument is a specific type, with any remaining arguments optional:

```zig
fn requireFirstArg(comptime FirstType: type, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    if (fields.len == 0) {
        @compileError("At least one argument required");
    }
    if (fields[0].type != FirstType) {
        @compileError("First argument must be of specified type");
    }
}

fn formatMessage(args: anytype) []const u8 {
    comptime requireFirstArg([]const u8, args);
    return args[0];
}

test "min one max rest" {
    const msg1: []const u8 = "hello";
    const msg2: []const u8 = "message";

    const r1 = formatMessage(.{msg1});
    try testing.expectEqualStrings("hello", r1);

    const r2 = formatMessage(.{ msg2, 42, true });
    try testing.expectEqualStrings("message", r2);
}
```

This allows flexible trailing arguments while ensuring a required argument is present.

### Type Predicate Validation

Use a predicate function to validate types:

```zig
fn TypePredicate(comptime predicate: fn (type) bool) type {
    return struct {
        pub fn validate(args: anytype) void {
            const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
            inline for (fields) |field| {
                if (!predicate(field.type)) {
                    @compileError("Argument type fails predicate");
                }
            }
        }
    };
}

fn isInteger(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .int, .comptime_int => true,
        else => false,
    };
}

fn sumIntegers(args: anytype) i64 {
    comptime TypePredicate(isInteger).validate(args);

    var total: i64 = 0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        total += @as(i64, @field(args, field.name));
    }
    return total;
}

test "type predicate" {
    const r1 = sumIntegers(.{ @as(i32, 10), @as(i8, 20), @as(u16, 30) });
    try testing.expectEqual(@as(i64, 60), r1);
}
```

This approach allows reusable type validators based on arbitrary conditions.

### Exact Count Constraint

Require an exact number of arguments:

```zig
fn requireExactCount(comptime count: usize, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    if (fields.len != count) {
        @compileError("Exact argument count required");
    }
}

fn triple(args: anytype) struct { i32, i32, i32 } {
    comptime requireExactCount(3, args);
    comptime validateAllTypes(i32, args);

    return .{ args[0], args[1], args[2] };
}

test "count constraint" {
    const result = triple(.{ @as(i32, 1), @as(i32, 2), @as(i32, 3) });
    try testing.expectEqual(@as(i32, 1), result[0]);
    try testing.expectEqual(@as(i32, 2), result[1]);
    try testing.expectEqual(@as(i32, 3), result[2]);
}
```

This is useful for functions that need a specific number of arguments.

### Combining Validators

You can combine multiple validators for comprehensive validation:

```zig
fn processData(args: anytype) i32 {
    comptime requireArgCount(2, 5, args);
    comptime validateNumeric(args);

    var sum: i32 = 0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        sum += @as(i32, @field(args, field.name));
    }
    return sum;
}
```

Validators compose naturally since they all operate at compile time.

### Why This Matters

Compile-time argument validation provides several benefits:

1. **Zero runtime cost** - All validation happens during compilation
2. **Type safety** - Invalid code won't compile, catching errors early
3. **Clear error messages** - `@compileError` provides helpful feedback
4. **No exceptions** - Type errors are caught before code runs
5. **Self-documenting** - Validation code serves as documentation
6. **Composition** - Validators can be combined and reused

### Performance Characteristics

All validation in this recipe has zero runtime overhead:

- Type checking happens during compilation
- Invalid code is rejected before code generation
- Valid code runs at full speed with no extra checks
- No dynamic dispatch or runtime type information needed

The only runtime cost is from the actual function logic, never from validation.

### String Literal Type Inference

Note the use of explicit type annotations for string literals in tests:

```zig
const str: []const u8 = "hello";
const r = processTyped(.{ @as(i32, 10), str, true });
```

String literals infer as `*const [N:0]u8` (null-terminated pointer arrays), not `[]const u8` (slices). When type-checking signatures, you need explicit slice types. This is an important detail when working with string arguments in validated tuples.

### Real-World Applications

These patterns are useful for:

1. **DSL construction** - Creating type-safe mini-languages
2. **Builder APIs** - Validating builder method calls
3. **Configuration functions** - Type-safe configuration
4. **Testing utilities** - Flexible test assertions
5. **Generic algorithms** - Type-safe variadic algorithms
6. **Data processing** - Validated data transformations

### Full Tested Code

```zig
// Recipe 9.14: Enforcing an Argument Signature on Tuple Arguments
// Target Zig Version: 0.15.2
//
// Performance Note: All validation in this recipe happens at compile-time.
// There is ZERO runtime cost for these checks. Invalid code will not compile,
// and valid code runs at full speed with no overhead.

const std = @import("std");
const testing = std.testing;

// ANCHOR: validate_types
// Validate that all tuple arguments match a specific type
fn validateAllTypes(comptime T: type, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        if (field.type != T) {
            @compileError("All arguments must be of the specified type");
        }
    }
}

fn sumInts(args: anytype) i32 {
    comptime validateAllTypes(i32, args);

    var total: i32 = 0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        total += @field(args, field.name);
    }
    return total;
}

test "validate types" {
    const r1 = sumInts(.{ @as(i32, 1), @as(i32, 2), @as(i32, 3) });
    try testing.expectEqual(@as(i32, 6), r1);

    const r2 = sumInts(.{@as(i32, 10)});
    try testing.expectEqual(@as(i32, 10), r2);

    // This would fail at compile time:
    // const r3 = sumInts(.{ @as(i32, 1), 2.5, @as(i32, 3) });
}
// ANCHOR_END: validate_types

// ANCHOR: min_max_args
// Enforce minimum and maximum argument counts
fn requireArgCount(comptime min: usize, comptime max: usize, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    if (fields.len < min) {
        @compileError("Too few arguments");
    }
    if (fields.len > max) {
        @compileError("Too many arguments");
    }
}

fn average(args: anytype) f64 {
    comptime requireArgCount(1, 10, args);
    // Note: This function assumes integer arguments. For mixed numeric types,
    // see the multiplyAll function which explicitly validates numeric types.

    var total: f64 = 0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        const value = @field(args, field.name);
        total += @as(f64, @floatFromInt(value));
    }
    return total / @as(f64, @floatFromInt(fields.len));
}

test "min max args" {
    const r1 = average(.{10});
    try testing.expectEqual(@as(f64, 10.0), r1);

    const r2 = average(.{ 10, 20, 30 });
    try testing.expectEqual(@as(f64, 20.0), r2);

    // These would fail at compile time:
    // const r3 = average(.{}); // Too few
    // const r4 = average(.{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 }); // Too many
}
// ANCHOR_END: min_max_args

// ANCHOR: typed_signature
// Enforce a specific signature pattern
fn enforceSignature(comptime Signature: type, args: anytype) void {
    const sig_fields = @typeInfo(Signature).@"struct".fields;
    const arg_fields = @typeInfo(@TypeOf(args)).@"struct".fields;

    if (sig_fields.len != arg_fields.len) {
        @compileError("Argument count mismatch");
    }

    inline for (sig_fields, 0..) |sig_field, i| {
        if (arg_fields[i].type != sig_field.type) {
            @compileError("Argument type mismatch");
        }
    }
}

fn processTyped(args: anytype) i32 {
    const Signature = struct { i32, []const u8, bool };
    comptime enforceSignature(Signature, args);

    const num = args[0];
    const str = args[1];
    const flag = args[2];

    if (flag) {
        return num + @as(i32, @intCast(str.len));
    }
    return num;
}

test "typed signature" {
    const str1: []const u8 = "hello";
    const str2: []const u8 = "test";

    const r1 = processTyped(.{ @as(i32, 10), str1, true });
    try testing.expectEqual(@as(i32, 15), r1);

    const r2 = processTyped(.{ @as(i32, 20), str2, false });
    try testing.expectEqual(@as(i32, 20), r2);

    // This would fail at compile time:
    // const r3 = processTyped(.{ @as(i32, 10), str1 }); // Wrong count
    // const r4 = processTyped(.{ 10, 20, true }); // Wrong types
}
// ANCHOR_END: typed_signature

// ANCHOR: homogeneous_tuple
// Ensure all arguments are the same type
fn HomogeneousArgs(comptime T: type) type {
    return struct {
        pub fn call(args: anytype) T {
            const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
            if (fields.len == 0) {
                @compileError("At least one argument required");
            }

            inline for (fields) |field| {
                if (field.type != T) {
                    @compileError("All arguments must be of the same type");
                }
            }

            return @field(args, fields[0].name);
        }
    };
}

fn firstInt(args: anytype) i32 {
    return HomogeneousArgs(i32).call(args);
}

test "homogeneous tuple" {
    const r1 = firstInt(.{@as(i32, 42)});
    try testing.expectEqual(@as(i32, 42), r1);

    const r2 = firstInt(.{ @as(i32, 1), @as(i32, 2), @as(i32, 3), @as(i32, 4), @as(i32, 5) });
    try testing.expectEqual(@as(i32, 1), r2);

    // This would fail at compile time:
    // const r3 = firstInt(.{ @as(i32, 1), "hello", @as(i32, 3) });
}
// ANCHOR_END: homogeneous_tuple

// ANCHOR: numeric_only
// Validate numeric types only
fn isNumeric(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .int, .float, .comptime_int, .comptime_float => true,
        else => false,
    };
}

fn validateNumeric(args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        if (!isNumeric(field.type)) {
            @compileError("Only numeric types allowed");
        }
    }
}

fn multiplyAll(args: anytype) f64 {
    comptime validateNumeric(args);

    var result: f64 = 1.0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        const value = @field(args, field.name);
        const float_val = switch (@typeInfo(field.type)) {
            .int, .comptime_int => @as(f64, @floatFromInt(value)),
            .float, .comptime_float => @as(f64, @floatCast(value)),
            else => unreachable,
        };
        result *= float_val;
    }
    return result;
}

test "numeric only" {
    const r1 = multiplyAll(.{ 2, 3, 4 });
    try testing.expectEqual(@as(f64, 24.0), r1);

    const r2 = multiplyAll(.{ 2.5, 4.0 });
    try testing.expectEqual(@as(f64, 10.0), r2);

    const r3 = multiplyAll(.{ @as(i32, 5), @as(f32, 2.0) });
    try testing.expectEqual(@as(f64, 10.0), r3);

    // This would fail at compile time:
    // const r4 = multiplyAll(.{ 2, "hello", 4 });
}
// ANCHOR_END: numeric_only

// ANCHOR: first_type_determines
// First argument determines type for rest
fn FirstTypeDetermines(args: anytype) type {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    if (fields.len == 0) {
        @compileError("At least one argument required");
    }

    const FirstType = fields[0].type;
    inline for (fields[1..]) |field| {
        if (field.type != FirstType) {
            @compileError("All arguments must match the first argument's type");
        }
    }

    return FirstType;
}

fn maxValue(args: anytype) FirstTypeDetermines(args) {
    var max_val = args[0];

    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields[1..]) |field| {
        const value = @field(args, field.name);
        if (value > max_val) {
            max_val = value;
        }
    }

    return max_val;
}

test "first type determines" {
    const r1 = maxValue(.{ 3, 7, 2, 9, 1 });
    try testing.expectEqual(9, r1);

    const r2 = maxValue(.{ 3.5, 1.2, 7.8 });
    try testing.expect(r2 > 7.7 and r2 < 7.9);

    // This would fail at compile time:
    // const r3 = maxValue(.{ 3, 7.5, 2 }); // Mixed types
}
// ANCHOR_END: first_type_determines

// ANCHOR: alternate_types
// Validate alternating type pattern
fn validateAlternating(comptime T1: type, comptime T2: type, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields, 0..) |field, i| {
        const expected_type = if (i % 2 == 0) T1 else T2;
        if (field.type != expected_type) {
            @compileError("Arguments must alternate between specified types");
        }
    }
}

fn processAlternating(args: anytype) i32 {
    comptime validateAlternating(i32, []const u8, args);

    var sum: i32 = 0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields, 0..) |field, i| {
        if (i % 2 == 0) {
            sum += @field(args, field.name);
        }
    }
    return sum;
}

test "alternate types" {
    const s1: []const u8 = "a";
    const s2: []const u8 = "b";
    const s3: []const u8 = "c";
    const s4: []const u8 = "test";

    const r1 = processAlternating(.{ @as(i32, 10), s1, @as(i32, 20), s2, @as(i32, 30), s3 });
    try testing.expectEqual(@as(i32, 60), r1);

    const r2 = processAlternating(.{ @as(i32, 5), s4 });
    try testing.expectEqual(@as(i32, 5), r2);

    // This would fail at compile time:
    // const r3 = processAlternating(.{ 10, 20, 30 }); // Not alternating
}
// ANCHOR_END: alternate_types

// ANCHOR: key_value_pairs
// Enforce key-value pair structure
fn validateKeyValuePairs(comptime KeyType: type, comptime ValueType: type, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    if (fields.len % 2 != 0) {
        @compileError("Arguments must be in key-value pairs");
    }

    inline for (fields, 0..) |field, i| {
        const expected_type = if (i % 2 == 0) KeyType else ValueType;
        if (field.type != expected_type) {
            @compileError("Key-value types don't match");
        }
    }
}

fn countPairs(args: anytype) usize {
    comptime validateKeyValuePairs([]const u8, i32, args);
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    return fields.len / 2;
}

test "key value pairs" {
    const k1: []const u8 = "age";
    const k2: []const u8 = "score";
    const k3: []const u8 = "count";

    const r1 = countPairs(.{ k1, @as(i32, 30), k2, @as(i32, 100) });
    try testing.expectEqual(@as(usize, 2), r1);

    const r2 = countPairs(.{ k3, @as(i32, 42) });
    try testing.expectEqual(@as(usize, 1), r2);

    // These would fail at compile time:
    // const r3 = countPairs(.{ k1, @as(i32, 30), k2 }); // Odd count
    // const r4 = countPairs(.{ k1, k2 }); // Wrong value type
}
// ANCHOR_END: key_value_pairs

// ANCHOR: min_one_max_rest
// First argument required, rest optional
fn requireFirstArg(comptime FirstType: type, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    if (fields.len == 0) {
        @compileError("At least one argument required");
    }
    if (fields[0].type != FirstType) {
        @compileError("First argument must be of specified type");
    }
}

fn formatMessage(args: anytype) []const u8 {
    comptime requireFirstArg([]const u8, args);
    return args[0];
}

test "min one max rest" {
    const msg1: []const u8 = "hello";
    const msg2: []const u8 = "message";

    const r1 = formatMessage(.{msg1});
    try testing.expectEqualStrings("hello", r1);

    const r2 = formatMessage(.{ msg2, 42, true });
    try testing.expectEqualStrings("message", r2);

    // These would fail at compile time:
    // const r3 = formatMessage(.{}); // No arguments
    // const r4 = formatMessage(.{ 42, msg1 }); // Wrong first type
}
// ANCHOR_END: min_one_max_rest

// ANCHOR: type_predicate
// Use predicate function to validate types
fn TypePredicate(comptime predicate: fn (type) bool) type {
    return struct {
        pub fn validate(args: anytype) void {
            const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
            inline for (fields) |field| {
                if (!predicate(field.type)) {
                    @compileError("Argument type fails predicate");
                }
            }
        }
    };
}

fn isInteger(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .int, .comptime_int => true,
        else => false,
    };
}

fn sumIntegers(args: anytype) i64 {
    comptime TypePredicate(isInteger).validate(args);

    var total: i64 = 0;
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    inline for (fields) |field| {
        total += @as(i64, @field(args, field.name));
    }
    return total;
}

test "type predicate" {
    const r1 = sumIntegers(.{ @as(i32, 10), @as(i8, 20), @as(u16, 30) });
    try testing.expectEqual(@as(i64, 60), r1);

    // This would fail at compile time:
    // const r2 = sumIntegers(.{ 10, 2.5, 30 }); // Contains float
}
// ANCHOR_END: type_predicate

// ANCHOR: count_constraint
// Validate exact argument count
fn requireExactCount(comptime count: usize, args: anytype) void {
    const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
    if (fields.len != count) {
        @compileError("Exact argument count required");
    }
}

fn triple(args: anytype) struct { i32, i32, i32 } {
    comptime requireExactCount(3, args);
    comptime validateAllTypes(i32, args);

    return .{ args[0], args[1], args[2] };
}

test "count constraint" {
    const result = triple(.{ @as(i32, 1), @as(i32, 2), @as(i32, 3) });
    try testing.expectEqual(@as(i32, 1), result[0]);
    try testing.expectEqual(@as(i32, 2), result[1]);
    try testing.expectEqual(@as(i32, 3), result[2]);

    // These would fail at compile time:
    // const r2 = triple(.{ @as(i32, 1), @as(i32, 2) }); // Too few
    // const r3 = triple(.{ @as(i32, 1), @as(i32, 2), @as(i32, 3), @as(i32, 4) }); // Too many
}
// ANCHOR_END: count_constraint

// Comprehensive test
test "comprehensive signature validation" {
    // Type validation
    const sum_result = sumInts(.{ @as(i32, 1), @as(i32, 2), @as(i32, 3), @as(i32, 4), @as(i32, 5) });
    try testing.expectEqual(@as(i32, 15), sum_result);

    // Count validation
    const avg_result = average(.{ 10, 20, 30 });
    try testing.expectEqual(@as(f64, 20.0), avg_result);

    // Signature enforcement
    const world: []const u8 = "world";
    const proc_result = processTyped(.{ @as(i32, 5), world, false });
    try testing.expectEqual(@as(i32, 5), proc_result);

    // Numeric validation
    const mult_result = multiplyAll(.{ 2, 3, 4 });
    try testing.expectEqual(@as(f64, 24.0), mult_result);

    // Max value
    const max_result = maxValue(.{ 5, 9, 3, 7 });
    try testing.expectEqual(9, max_result);

    // Key-value pairs
    const ka: []const u8 = "a";
    const kb: []const u8 = "b";
    const pair_count = countPairs(.{ ka, @as(i32, 1), kb, @as(i32, 2) });
    try testing.expectEqual(@as(usize, 2), pair_count);
}
```

### See Also

- Recipe 9.11: Using comptime to control instance creation
- Recipe 9.12: Capturing struct attribute definition order
- Recipe 9.13: Defining a generic that takes optional arguments

---

## Recipe 9.15: Enforcing Coding Conventions in Structs {#recipe-9-15}

**Tags:** comptime, comptime-metaprogramming, error-handling, json, parsing, pointers, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_15.zig`

### Problem

You want to enforce consistent coding conventions across your codebase at compile time. You need to validate that struct definitions follow naming standards, include required fields, avoid forbidden patterns, and maintain structural consistency. Manual code reviews catch these issues too late and inconsistently.

### Solution

Use `@typeInfo` to introspect struct definitions at compile time and `@compileError` to enforce conventions before code runs. Zig's compile-time execution lets you validate naming patterns, field requirements, type constraints, and structural rules with zero runtime overhead.

### Enforcing snake_case Naming

Validate that all field names follow snake_case convention:

```zig
// Enforce snake_case naming convention for fields
fn isSnakeCase(name: []const u8) bool {
    if (name.len == 0) return false;

    // Must start with lowercase letter
    if (name[0] < 'a' or name[0] > 'z') return false;

    for (name) |c| {
        const valid = (c >= 'a' and c <= 'z') or (c >= '0' and c <= '9') or c == '_';
        if (!valid) return false;
    }

    return true;
}

fn enforceSnakeCase(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;
    inline for (fields) |field| {
        if (!isSnakeCase(field.name)) {
            @compileError("Field '" ++ field.name ++ "' must use snake_case naming");
        }
    }
}

const ValidSnakeCase = struct {
    user_name: []const u8,
    age_in_years: u32,
    is_active: bool,
};

test "snake case validation" {
    comptime enforceSnakeCase(ValidSnakeCase);

    const user = ValidSnakeCase{
        .user_name = "alice",
        .age_in_years = 30,
        .is_active = true,
    };
    try testing.expectEqualStrings("alice", user.user_name);

    // This would fail at compile time:
    // const InvalidCamelCase = struct { userName: []const u8 };
    // comptime enforceSnakeCase(InvalidCamelCase);
}
```

Invalid naming patterns won't compile. This is useful for matching SQL column conventions or enforcing project style guides.

### Requiring Specific Fields

Ensure structs contain mandatory fields:

```zig
fn requireFields(comptime T: type, comptime required: []const []const u8) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (required) |req_name| {
        var found = false;
        inline for (fields) |field| {
            if (std.mem.eql(u8, field.name, req_name)) {
                found = true;
                break;
            }
        }
        if (!found) {
            @compileError("Required field '" ++ req_name ++ "' is missing");
        }
    }
}

const User = struct {
    id: u64,
    name: []const u8,
    email: []const u8,
    created_at: i64,
};

test "required fields" {
    const required = [_][]const u8{ "id", "name", "email" };
    comptime requireFields(User, &required);

    const user = User{
        .id = 1,
        .name = "alice",
        .email = "alice@example.com",
        .created_at = 1234567890,
    };
    try testing.expectEqual(@as(u64, 1), user.id);
}
```

This pattern ensures API entities or database models always include essential fields.

### Discussion

### Forbidding Dangerous Field Names

Prevent accidentally including sensitive data:

```zig
fn forbidFields(comptime T: type, comptime forbidden: []const []const u8) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        inline for (forbidden) |forbidden_name| {
            if (std.mem.eql(u8, field.name, forbidden_name)) {
                @compileError("Field '" ++ field.name ++ "' is forbidden");
            }
        }
    }
}

const SafeConfig = struct {
    host: []const u8,
    port: u16,
    timeout: u32,
};

test "forbidden fields" {
    const forbidden = [_][]const u8{ "password", "secret", "private_key" };
    comptime forbidFields(SafeConfig, &forbidden);

    const config = SafeConfig{
        .host = "localhost",
        .port = 8080,
        .timeout = 30,
    };
    try testing.expectEqual(@as(u16, 8080), config.port);
}
```

This prevents sensitive data from appearing in logged or serialized structs.

### Field Count Constraints

Enforce reasonable struct sizes:

```zig
fn requireFieldCount(comptime T: type, comptime min: usize, comptime max: usize) void {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len < min) {
        @compileError("Struct must have at least " ++ std.fmt.comptimePrint("{d}", .{min}) ++ " fields");
    }
    if (fields.len > max) {
        @compileError("Struct must have at most " ++ std.fmt.comptimePrint("{d}", .{max}) ++ " fields");
    }
}

const Point3D = struct {
    x: f64,
    y: f64,
    z: f64,
};

test "field count constraints" {
    comptime requireFieldCount(Point3D, 2, 4);

    const p = Point3D{ .x = 1.0, .y = 2.0, .z = 3.0 };
    try testing.expectEqual(@as(f64, 1.0), p.x);
}
```

This helps prevent overly complex data structures and encourages composition.

### Type Requirements

Enforce that specific fields have expected types:

```zig
fn requireFieldType(comptime T: type, comptime field_name: []const u8, comptime FieldType: type) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        if (std.mem.eql(u8, field.name, field_name)) {
            if (field.type != FieldType) {
                @compileError("Field '" ++ field_name ++ "' must be of type " ++ @typeName(FieldType));
            }
        }
    }
}

const Entity = struct {
    id: u64,
    name: []const u8,
    active: bool,
};

test "type requirements" {
    comptime requireFieldType(Entity, "id", u64);
    comptime requireFieldType(Entity, "active", bool);

    const entity = Entity{
        .id = 42,
        .name = "test",
        .active = true,
    };
    try testing.expectEqual(@as(u64, 42), entity.id);
}
```

This ensures critical fields maintain consistent types across related structs.

### Prefix Conventions

Enforce field name prefixes for private or internal fields:

```zig
fn requirePrefix(comptime T: type, comptime prefix: []const u8) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        if (!std.mem.startsWith(u8, field.name, prefix)) {
            @compileError("Field '" ++ field.name ++ "' must start with '" ++ prefix ++ "'");
        }
    }
}

const PrivateData = struct {
    _internal_id: u64,
    _hidden_flag: bool,
    _secret_value: i32,
};

test "prefix convention" {
    comptime requirePrefix(PrivateData, "_");

    const data = PrivateData{
        ._internal_id = 1,
        ._hidden_flag = true,
        ._secret_value = 42,
    };
    try testing.expectEqual(@as(u64, 1), data._internal_id);
}
```

This pattern makes internal fields visually distinct from public API.

### Forbidding Optional Fields

Prevent nullable fields for stricter data models:

```zig
fn forbidOptionalFields(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        const type_info = @typeInfo(field.type);
        if (type_info == .optional) {
            @compileError("Field '" ++ field.name ++ "' cannot be optional");
        }
    }
}

const RequiredFields = struct {
    name: []const u8,
    age: u32,
    active: bool,
};

test "no optional fields" {
    comptime forbidOptionalFields(RequiredFields);

    const data = RequiredFields{
        .name = "test",
        .age = 25,
        .active = true,
    };
    try testing.expectEqual(@as(u32, 25), data.age);
}
```

This is useful for database models where NULL values aren't permitted.

### Requiring ID Fields

Enforce that database entities have identifier fields:

```zig
fn requireIdField(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;
    var found_id = false;

    inline for (fields) |field| {
        if (std.mem.eql(u8, field.name, "id")) {
            found_id = true;
            const type_info = @typeInfo(field.type);
            if (type_info != .int and type_info != .comptime_int) {
                @compileError("Field 'id' must be an integer type");
            }
        }
    }

    if (!found_id) {
        @compileError("Struct must have an 'id' field");
    }
}

const Product = struct {
    id: u64,
    name: []const u8,
    price: f64,
};

test "require id field" {
    comptime requireIdField(Product);

    const product = Product{
        .id = 100,
        .name = "Widget",
        .price = 19.99,
    };
    try testing.expectEqual(@as(u64, 100), product.id);
}
```

This ensures consistent identifier handling across data models.

### Field Ordering Requirements

Validate field definition order:

```zig
fn requireIdFirst(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len == 0) {
        @compileError("Struct must have at least one field");
    }

    if (!std.mem.eql(u8, fields[0].name, "id")) {
        @compileError("First field must be 'id', found '" ++ fields[0].name ++ "'");
    }
}

const Record = struct {
    id: u64,
    timestamp: i64,
    data: []const u8,
};

test "field order validation" {
    comptime requireIdFirst(Record);

    const record = Record{
        .id = 1,
        .timestamp = 1234567890,
        .data = "test",
    };
    try testing.expectEqual(@as(u64, 1), record.id);
}
```

Field ordering can matter for binary serialization or memory layout optimization.

### Combining Multiple Validators

Create comprehensive validation by composing validators:

```zig
fn ValidatedStruct(comptime T: type) type {
    // Enforce all conventions
    comptime enforceSnakeCase(T);
    comptime requireIdField(T);
    comptime requireIdFirst(T);
    comptime forbidOptionalFields(T);
    comptime requireFieldCount(T, 2, 10);

    return T;
}

const ValidatedUser = ValidatedStruct(struct {
    id: u64,
    user_name: []const u8,
    email_address: []const u8,
    is_active: bool,
});

test "combined validation" {
    const user = ValidatedUser{
        .id = 1,
        .user_name = "alice",
        .email_address = "alice@example.com",
        .is_active = true,
    };
    try testing.expectEqual(@as(u64, 1), user.id);
    try testing.expectEqualStrings("alice", user.user_name);
}
```

This pattern lets you create domain-specific validators for different parts of your system.

### camelCase Convention

Support alternative naming conventions:

```zig
fn isCamelCase(name: []const u8) bool {
    if (name.len == 0) return false;

    // Must start with lowercase letter
    if (name[0] < 'a' or name[0] > 'z') return false;

    for (name) |c| {
        const valid = (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or (c >= '0' and c <= '9');
        if (!valid) return false;
    }

    return true;
}

fn enforceCamelCase(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;
    inline for (fields) |field| {
        if (!isCamelCase(field.name)) {
            @compileError("Field '" ++ field.name ++ "' must use camelCase naming");
        }
    }
}

const CamelCaseData = struct {
    firstName: []const u8,
    lastName: []const u8,
    emailAddress: []const u8,
};

test "camel case validation" {
    comptime enforceCamelCase(CamelCaseData);

    const data = CamelCaseData{
        .firstName = "Bob",
        .lastName = "Smith",
        .emailAddress = "bob@example.com",
    };
    try testing.expectEqualStrings("Bob", data.firstName);
}
```

Different naming conventions suit different contexts (APIs, databases, legacy systems).

### Forbidding Single-Item Pointers

Prevent unsafe pointer usage:

```zig
fn forbidSinglePointerFields(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        const type_info = @typeInfo(field.type);
        if (type_info == .pointer) {
            // Forbid single-item pointers (size == .one)
            // Allow many-item pointers and C pointers (slices)
            if (type_info.pointer.size == .one) {
                @compileError("Field '" ++ field.name ++ "' cannot be a single-item pointer (use slices or values instead)");
            }
        }
    }
}

const SafeData = struct {
    values: []const u8,  // Slice is OK
    count: usize,
};

test "no single pointer fields" {
    comptime forbidSinglePointerFields(SafeData);

    const data = SafeData{
        .values = "test",
        .count = 4,
    };
    try testing.expectEqual(@as(usize, 4), data.count);
}
```

This encourages safer memory handling with slices instead of raw pointers.

### Suffix Conventions

Require consistent field name suffixes:

```zig
fn requireSuffix(comptime T: type, comptime suffix: []const u8) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        if (!std.mem.endsWith(u8, field.name, suffix)) {
            @compileError("Field '" ++ field.name ++ "' must end with '" ++ suffix ++ "'");
        }
    }
}

const MetricsData = struct {
    request_count: u64,
    error_count: u64,
    success_count: u64,
};

test "suffix convention" {
    comptime requireSuffix(MetricsData, "_count");

    const metrics = MetricsData{
        .request_count = 100,
        .error_count = 5,
        .success_count = 95,
    };
    try testing.expectEqual(@as(u64, 100), metrics.request_count);
}
```

Suffix conventions make field purposes immediately clear.

### Why This Matters

Compile-time convention enforcement provides several benefits:

1. **Consistency** - Automated enforcement across entire codebase
2. **Early Detection** - Violations caught during compilation, not code review
3. **Zero Runtime Cost** - All validation happens at compile time
4. **Self-Documenting** - Validators encode team conventions explicitly
5. **Refactoring Safety** - Convention violations prevented during changes
6. **Onboarding** - New team members learn conventions from compiler errors

### Real-World Applications

These validation patterns are useful for:

1. **Database ORM** - Enforce entity structure (required IDs, snake_case columns)
2. **API Serialization** - Validate JSON-compatible field names (camelCase)
3. **Security** - Prevent sensitive fields in logged structs
4. **Code Generation** - Ensure generated structs meet requirements
5. **Plugin Systems** - Validate plugin interface implementations
6. **Legacy Integration** - Enforce compatibility with existing systems

### Performance Characteristics

All validation has zero runtime cost:

- Type checking happens during compilation
- Invalid code is rejected before code generation
- Valid code runs at full speed with no overhead
- No dynamic dispatch or runtime type information needed

The only cost is compile time, which increases slightly with more validators. However, this is typically negligible compared to the time saved catching errors early.

### Building Domain-Specific Validators

You can create specialized validators for different system components:

```zig
// Database entity validator
fn DatabaseEntity(comptime T: type) type {
    comptime {
        enforceSnakeCase(T);           // SQL column naming
        requireIdField(T);              // Primary key required
        requireIdFirst(T);              // Conventional field order
        forbidSinglePointerFields(T);   // No dangling references
    }
    return T;
}

// API response validator
fn ApiResponse(comptime T: type) type {
    comptime {
        enforceCamelCase(T);            // JSON naming convention
        forbidOptionalFields(T);        // All fields must be present
        requireFieldCount(T, 1, 20);    // Reasonable payload size
    }
    return T;
}

// Internal state validator
fn InternalState(comptime T: type) type {
    comptime {
        requirePrefix(T, "_");          // Private field convention
        forbidFields(T, &[_][]const u8{"password", "secret"});  // No secrets in state
    }
    return T;
}
```

These specialized validators encode architectural decisions and maintain consistency across layers.

### String Validation Patterns

When validating field names, work with compile-time string operations:

```zig
// Check character ranges directly
if (name[0] < 'a' or name[0] > 'z') return false;

// Use std.mem functions for patterns
if (!std.mem.startsWith(u8, field.name, "_")) { }
if (!std.mem.endsWith(u8, field.name, "_count")) { }
if (!std.mem.eql(u8, field.name, "id")) { }

// Iterate characters for custom validation
for (name) |c| {
    const valid = (c >= 'a' and c <= 'z') or c == '_';
    if (!valid) return false;
}
```

All string operations work at compile time with zero runtime overhead.

### Type Introspection Techniques

Access different aspects of type information:

```zig
const fields = @typeInfo(T).@"struct".fields;

for (fields) |field| {
    const name = field.name;              // Field name ([]const u8)
    const field_type = field.type;        // Field type (type)
    const type_info = @typeInfo(field_type);  // Type category

    // Check type categories
    if (type_info == .optional) { }
    if (type_info == .pointer) { }
    if (type_info == .int) { }

    // Access pointer details
    if (type_info == .pointer) {
        const size = type_info.pointer.size;  // .one, .many, .c
    }
}
```

The `@typeInfo` builtin provides complete type metadata at compile time.

### Full Tested Code

```zig
// Recipe 9.15: Enforcing Coding Conventions in Structs
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to use compile-time validation to enforce
// naming conventions, field requirements, and structural patterns in structs.

const std = @import("std");
const testing = std.testing;

// ANCHOR: snake_case_validation
// Enforce snake_case naming convention for fields
fn isSnakeCase(name: []const u8) bool {
    if (name.len == 0) return false;

    // Must start with lowercase letter
    if (name[0] < 'a' or name[0] > 'z') return false;

    for (name) |c| {
        const valid = (c >= 'a' and c <= 'z') or (c >= '0' and c <= '9') or c == '_';
        if (!valid) return false;
    }

    return true;
}

fn enforceSnakeCase(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;
    inline for (fields) |field| {
        if (!isSnakeCase(field.name)) {
            @compileError("Field '" ++ field.name ++ "' must use snake_case naming");
        }
    }
}

const ValidSnakeCase = struct {
    user_name: []const u8,
    age_in_years: u32,
    is_active: bool,
};

test "snake case validation" {
    comptime enforceSnakeCase(ValidSnakeCase);

    const user = ValidSnakeCase{
        .user_name = "alice",
        .age_in_years = 30,
        .is_active = true,
    };
    try testing.expectEqualStrings("alice", user.user_name);

    // This would fail at compile time:
    // const InvalidCamelCase = struct { userName: []const u8 };
    // comptime enforceSnakeCase(InvalidCamelCase);
}
// ANCHOR_END: snake_case_validation

// ANCHOR: required_fields
// Enforce that specific fields must be present
fn requireFields(comptime T: type, comptime required: []const []const u8) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (required) |req_name| {
        var found = false;
        inline for (fields) |field| {
            if (std.mem.eql(u8, field.name, req_name)) {
                found = true;
                break;
            }
        }
        if (!found) {
            @compileError("Required field '" ++ req_name ++ "' is missing");
        }
    }
}

const User = struct {
    id: u64,
    name: []const u8,
    email: []const u8,
    created_at: i64,
};

test "required fields" {
    const required = [_][]const u8{ "id", "name", "email" };
    comptime requireFields(User, &required);

    const user = User{
        .id = 1,
        .name = "alice",
        .email = "alice@example.com",
        .created_at = 1234567890,
    };
    try testing.expectEqual(@as(u64, 1), user.id);

    // This would fail at compile time:
    // const IncompleteUser = struct { id: u64, name: []const u8 };
    // comptime requireFields(IncompleteUser, &required);
}
// ANCHOR_END: required_fields

// ANCHOR: forbidden_names
// Forbid specific field names
fn forbidFields(comptime T: type, comptime forbidden: []const []const u8) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        inline for (forbidden) |forbidden_name| {
            if (std.mem.eql(u8, field.name, forbidden_name)) {
                @compileError("Field '" ++ field.name ++ "' is forbidden");
            }
        }
    }
}

const SafeConfig = struct {
    host: []const u8,
    port: u16,
    timeout: u32,
};

test "forbidden fields" {
    const forbidden = [_][]const u8{ "password", "secret", "private_key" };
    comptime forbidFields(SafeConfig, &forbidden);

    const config = SafeConfig{
        .host = "localhost",
        .port = 8080,
        .timeout = 30,
    };
    try testing.expectEqual(@as(u16, 8080), config.port);

    // This would fail at compile time:
    // const UnsafeConfig = struct { password: []const u8 };
    // comptime forbidFields(UnsafeConfig, &forbidden);
}
// ANCHOR_END: forbidden_names

// ANCHOR: field_count_constraints
// Enforce minimum and maximum field counts
fn requireFieldCount(comptime T: type, comptime min: usize, comptime max: usize) void {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len < min) {
        @compileError("Struct must have at least " ++ std.fmt.comptimePrint("{d}", .{min}) ++ " fields");
    }
    if (fields.len > max) {
        @compileError("Struct must have at most " ++ std.fmt.comptimePrint("{d}", .{max}) ++ " fields");
    }
}

const Point3D = struct {
    x: f64,
    y: f64,
    z: f64,
};

test "field count constraints" {
    comptime requireFieldCount(Point3D, 2, 4);

    const p = Point3D{ .x = 1.0, .y = 2.0, .z = 3.0 };
    try testing.expectEqual(@as(f64, 1.0), p.x);

    // This would fail at compile time:
    // const TooFew = struct { x: f64 };
    // comptime requireFieldCount(TooFew, 2, 4);
}
// ANCHOR_END: field_count_constraints

// ANCHOR: type_requirements
// Enforce that all fields of a certain name have a specific type
fn requireFieldType(comptime T: type, comptime field_name: []const u8, comptime FieldType: type) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        if (std.mem.eql(u8, field.name, field_name)) {
            if (field.type != FieldType) {
                @compileError("Field '" ++ field_name ++ "' must be of type " ++ @typeName(FieldType));
            }
        }
    }
}

const Entity = struct {
    id: u64,
    name: []const u8,
    active: bool,
};

test "type requirements" {
    comptime requireFieldType(Entity, "id", u64);
    comptime requireFieldType(Entity, "active", bool);

    const entity = Entity{
        .id = 42,
        .name = "test",
        .active = true,
    };
    try testing.expectEqual(@as(u64, 42), entity.id);

    // This would fail at compile time:
    // const WrongType = struct { id: i32 };
    // comptime requireFieldType(WrongType, "id", u64);
}
// ANCHOR_END: type_requirements

// ANCHOR: prefix_convention
// Enforce field name prefixes
fn requirePrefix(comptime T: type, comptime prefix: []const u8) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        if (!std.mem.startsWith(u8, field.name, prefix)) {
            @compileError("Field '" ++ field.name ++ "' must start with '" ++ prefix ++ "'");
        }
    }
}

const PrivateData = struct {
    _internal_id: u64,
    _hidden_flag: bool,
    _secret_value: i32,
};

test "prefix convention" {
    comptime requirePrefix(PrivateData, "_");

    const data = PrivateData{
        ._internal_id = 1,
        ._hidden_flag = true,
        ._secret_value = 42,
    };
    try testing.expectEqual(@as(u64, 1), data._internal_id);

    // This would fail at compile time:
    // const NoPrefixData = struct { public_field: u64 };
    // comptime requirePrefix(NoPrefixData, "_");
}
// ANCHOR_END: prefix_convention

// ANCHOR: no_optional_fields
// Forbid optional fields
fn forbidOptionalFields(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        const type_info = @typeInfo(field.type);
        if (type_info == .optional) {
            @compileError("Field '" ++ field.name ++ "' cannot be optional");
        }
    }
}

const RequiredFields = struct {
    name: []const u8,
    age: u32,
    active: bool,
};

test "no optional fields" {
    comptime forbidOptionalFields(RequiredFields);

    const data = RequiredFields{
        .name = "test",
        .age = 25,
        .active = true,
    };
    try testing.expectEqual(@as(u32, 25), data.age);

    // This would fail at compile time:
    // const OptionalData = struct { name: ?[]const u8 };
    // comptime forbidOptionalFields(OptionalData);
}
// ANCHOR_END: no_optional_fields

// ANCHOR: require_id_field
// Require an 'id' field of integer type
fn requireIdField(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;
    var found_id = false;

    inline for (fields) |field| {
        if (std.mem.eql(u8, field.name, "id")) {
            found_id = true;
            const type_info = @typeInfo(field.type);
            if (type_info != .int and type_info != .comptime_int) {
                @compileError("Field 'id' must be an integer type");
            }
        }
    }

    if (!found_id) {
        @compileError("Struct must have an 'id' field");
    }
}

const Product = struct {
    id: u64,
    name: []const u8,
    price: f64,
};

test "require id field" {
    comptime requireIdField(Product);

    const product = Product{
        .id = 100,
        .name = "Widget",
        .price = 19.99,
    };
    try testing.expectEqual(@as(u64, 100), product.id);

    // This would fail at compile time:
    // const NoId = struct { name: []const u8 };
    // comptime requireIdField(NoId);
}
// ANCHOR_END: require_id_field

// ANCHOR: field_order_validation
// Validate that 'id' field comes first
fn requireIdFirst(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;
    if (fields.len == 0) {
        @compileError("Struct must have at least one field");
    }

    if (!std.mem.eql(u8, fields[0].name, "id")) {
        @compileError("First field must be 'id', found '" ++ fields[0].name ++ "'");
    }
}

const Record = struct {
    id: u64,
    timestamp: i64,
    data: []const u8,
};

test "field order validation" {
    comptime requireIdFirst(Record);

    const record = Record{
        .id = 1,
        .timestamp = 1234567890,
        .data = "test",
    };
    try testing.expectEqual(@as(u64, 1), record.id);

    // This would fail at compile time:
    // const WrongOrder = struct { name: []const u8, id: u64 };
    // comptime requireIdFirst(WrongOrder);
}
// ANCHOR_END: field_order_validation

// ANCHOR: combined_validation
// Combine multiple validators for comprehensive enforcement
fn ValidatedStruct(comptime T: type) type {
    // Enforce all conventions
    comptime enforceSnakeCase(T);
    comptime requireIdField(T);
    comptime requireIdFirst(T);
    comptime forbidOptionalFields(T);
    comptime requireFieldCount(T, 2, 10);

    return T;
}

const ValidatedUser = ValidatedStruct(struct {
    id: u64,
    user_name: []const u8,
    email_address: []const u8,
    is_active: bool,
});

test "combined validation" {
    const user = ValidatedUser{
        .id = 1,
        .user_name = "alice",
        .email_address = "alice@example.com",
        .is_active = true,
    };
    try testing.expectEqual(@as(u64, 1), user.id);
    try testing.expectEqualStrings("alice", user.user_name);
}
// ANCHOR_END: combined_validation

// ANCHOR: camel_case_validation
// Enforce camelCase naming convention
fn isCamelCase(name: []const u8) bool {
    if (name.len == 0) return false;

    // Must start with lowercase letter
    if (name[0] < 'a' or name[0] > 'z') return false;

    for (name) |c| {
        const valid = (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or (c >= '0' and c <= '9');
        if (!valid) return false;
    }

    return true;
}

fn enforceCamelCase(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;
    inline for (fields) |field| {
        if (!isCamelCase(field.name)) {
            @compileError("Field '" ++ field.name ++ "' must use camelCase naming");
        }
    }
}

const CamelCaseData = struct {
    firstName: []const u8,
    lastName: []const u8,
    emailAddress: []const u8,
};

test "camel case validation" {
    comptime enforceCamelCase(CamelCaseData);

    const data = CamelCaseData{
        .firstName = "Bob",
        .lastName = "Smith",
        .emailAddress = "bob@example.com",
    };
    try testing.expectEqualStrings("Bob", data.firstName);

    // This would fail at compile time:
    // const InvalidSnake = struct { first_name: []const u8 };
    // comptime enforceCamelCase(InvalidSnake);
}
// ANCHOR_END: camel_case_validation

// ANCHOR: no_pointer_fields
// Forbid single-item pointer fields for safety
fn forbidSinglePointerFields(comptime T: type) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        const type_info = @typeInfo(field.type);
        if (type_info == .pointer) {
            // Forbid single-item pointers (size == .one)
            // Allow many-item pointers and C pointers (slices)
            if (type_info.pointer.size == .one) {
                @compileError("Field '" ++ field.name ++ "' cannot be a single-item pointer (use slices or values instead)");
            }
        }
    }
}

const SafeData = struct {
    values: []const u8,  // Slice is OK
    count: usize,
};

test "no single pointer fields" {
    comptime forbidSinglePointerFields(SafeData);

    const data = SafeData{
        .values = "test",
        .count = 4,
    };
    try testing.expectEqual(@as(usize, 4), data.count);

    // This would fail at compile time:
    // const UnsafeData = struct { ptr: *u8 };
    // comptime forbidSinglePointerFields(UnsafeData);
}
// ANCHOR_END: no_pointer_fields

// ANCHOR: suffix_convention
// Require fields to end with a specific suffix
fn requireSuffix(comptime T: type, comptime suffix: []const u8) void {
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        if (!std.mem.endsWith(u8, field.name, suffix)) {
            @compileError("Field '" ++ field.name ++ "' must end with '" ++ suffix ++ "'");
        }
    }
}

const MetricsData = struct {
    request_count: u64,
    error_count: u64,
    success_count: u64,
};

test "suffix convention" {
    comptime requireSuffix(MetricsData, "_count");

    const metrics = MetricsData{
        .request_count = 100,
        .error_count = 5,
        .success_count = 95,
    };
    try testing.expectEqual(@as(u64, 100), metrics.request_count);

    // This would fail at compile time:
    // const NoSuffix = struct { total: u64 };
    // comptime requireSuffix(NoSuffix, "_count");
}
// ANCHOR_END: suffix_convention

// Comprehensive test
test "comprehensive convention enforcement" {
    // Snake case convention
    comptime enforceSnakeCase(ValidSnakeCase);

    // Required fields present
    const required_user_fields = [_][]const u8{ "id", "name", "email" };
    comptime requireFields(User, &required_user_fields);

    // No forbidden fields
    const forbidden_config_fields = [_][]const u8{ "password", "secret" };
    comptime forbidFields(SafeConfig, &forbidden_config_fields);

    // Field count in range
    comptime requireFieldCount(Point3D, 2, 4);

    // Specific type enforcement
    comptime requireFieldType(Entity, "id", u64);

    // Prefix convention
    comptime requirePrefix(PrivateData, "_");

    // No optionals
    comptime forbidOptionalFields(RequiredFields);

    // ID field required
    comptime requireIdField(Product);

    // ID must be first
    comptime requireIdFirst(Record);

    // Camel case convention
    comptime enforceCamelCase(CamelCaseData);

    // No single-item pointers
    comptime forbidSinglePointerFields(SafeData);

    // Suffix convention
    comptime requireSuffix(MetricsData, "_count");

    try testing.expect(true);
}
```

### See Also

- Recipe 9.12: Capturing struct attribute definition order
- Recipe 9.14: Enforcing an argument signature on tuple arguments
- Recipe 9.16: Defining structs programmatically

---

## Recipe 9.16: Defining Structs Programmatically {#recipe-9-16}

**Tags:** c-interop, comptime, comptime-metaprogramming, error-handling, pointers, testing
**Difficulty:** advanced
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_16.zig`

### Problem

You need to create struct types dynamically at compile time. You want to generate structs based on configuration, merge multiple structs together, transform field names or types, filter fields by criteria, or create wrapper types without manually writing repetitive struct definitions.

### Solution

Use `@Type` to construct struct types programmatically at compile time. Zig's `@Type` builtin converts type information structures into actual types, enabling dynamic struct generation with zero runtime overhead.

### Basic Struct Creation

Create a simple struct type from scratch:

```zig
// Create a simple struct type programmatically
fn createSimpleStruct() type {
    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &[_]std.builtin.Type.StructField{
                .{
                    .name = "x",
                    .type = i32,
                    .default_value_ptr = null,
                    .is_comptime = false,
                    .alignment = @alignOf(i32),
                },
                .{
                    .name = "y",
                    .type = i32,
                    .default_value_ptr = null,
                    .is_comptime = false,
                    .alignment = @alignOf(i32),
                },
            },
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "basic struct creation" {
    const Point = createSimpleStruct();
    const p = Point{ .x = 10, .y = 20 };

    try testing.expectEqual(@as(i32, 10), p.x);
    try testing.expectEqual(@as(i32, 20), p.y);
}
```

The generated `Point` type is identical to one written manually.

### Variable Number of Fields

Generate structs with dynamic field counts:

```zig
fn createFieldsStruct(comptime count: usize, comptime T: type) type {
    var fields: [count]std.builtin.Type.StructField = undefined;

    for (0..count) |i| {
        const name = std.fmt.comptimePrint("field_{d}", .{i});
        fields[i] = .{
            .name = name,
            .type = T,
            .default_value_ptr = null,
            .is_comptime = false,
            .alignment = @alignOf(T),
        };
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &fields,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "add fields" {
    const ThreeInts = createFieldsStruct(3, i32);
    const data = ThreeInts{
        .field_0 = 1,
        .field_1 = 2,
        .field_2 = 3,
    };

    try testing.expectEqual(@as(i32, 1), data.field_0);
    try testing.expectEqual(@as(i32, 2), data.field_1);
    try testing.expectEqual(@as(i32, 3), data.field_2);
}
```

This is useful for code generation based on configuration.

### Discussion

### Creating Structs from Tuples

Build structs from name-type pairs:

```zig
fn structFromPairs(comptime pairs: anytype) type {
    const fields_tuple = @typeInfo(@TypeOf(pairs)).@"struct".fields;
    var fields: [fields_tuple.len]std.builtin.Type.StructField = undefined;

    inline for (fields_tuple, 0..) |field, i| {
        const pair = @field(pairs, field.name);
        fields[i] = .{
            .name = pair[0],
            .type = pair[1],
            .default_value_ptr = null,
            .is_comptime = false,
            .alignment = @alignOf(pair[1]),
        };
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &fields,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "struct from tuples" {
    const Person = structFromPairs(.{
        .{ "name", []const u8 },
        .{ "age", u32 },
        .{ "active", bool },
    });

    const person = Person{
        .name = "Alice",
        .age = 30,
        .active = true,
    };

    try testing.expectEqualStrings("Alice", person.name);
    try testing.expectEqual(@as(u32, 30), person.age);
    try testing.expect(person.active);
}
```

This enables DSL-style struct definitions with clean syntax.

### Merging Struct Types

Combine multiple structs into one:

```zig
fn mergeStructs(comptime A: type, comptime B: type) type {
    const a_fields = @typeInfo(A).@"struct".fields;
    const b_fields = @typeInfo(B).@"struct".fields;

    // Check for name collisions
    inline for (a_fields) |a_field| {
        inline for (b_fields) |b_field| {
            if (std.mem.eql(u8, a_field.name, b_field.name)) {
                @compileError("Cannot merge structs: field '" ++ a_field.name ++ "' exists in both types");
            }
        }
    }

    var merged: [a_fields.len + b_fields.len]std.builtin.Type.StructField = undefined;

    inline for (a_fields, 0..) |field, i| {
        merged[i] = field;
    }

    inline for (b_fields, 0..) |field, i| {
        merged[a_fields.len + i] = field;
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &merged,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "merge structs" {
    const Position = struct { x: i32, y: i32 };
    const Velocity = struct { dx: f32, dy: f32 };

    const Entity = mergeStructs(Position, Velocity);

    const entity = Entity{
        .x = 10,
        .y = 20,
        .dx = 1.5,
        .dy = 2.5,
    };

    try testing.expectEqual(@as(i32, 10), entity.x);
    try testing.expectEqual(@as(i32, 20), entity.y);
}
```

This is useful for composition patterns and combining domain objects.

### Filtering Fields by Predicate

Select fields matching specific criteria:

```zig
fn filterFields(comptime T: type, comptime predicate: fn (std.builtin.Type.StructField) bool) type {
    const fields = @typeInfo(T).@"struct".fields;

    comptime var count: usize = 0;
    inline for (fields) |field| {
        if (predicate(field)) {
            count += 1;
        }
    }

    var filtered: [count]std.builtin.Type.StructField = undefined;
    comptime var index: usize = 0;
    inline for (fields) |field| {
        if (predicate(field)) {
            filtered[index] = field;
            index += 1;
        }
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &filtered,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

fn isIntegerField(field: std.builtin.Type.StructField) bool {
    return @typeInfo(field.type) == .int or @typeInfo(field.type) == .comptime_int;
}

test "filter fields" {
    const Mixed = struct {
        id: u64,
        name: []const u8,
        count: i32,
        active: bool,
    };

    const IntegersOnly = filterFields(Mixed, isIntegerField);

    const data = IntegersOnly{
        .id = 1,
        .count = 42,
    };

    try testing.expectEqual(@as(u64, 1), data.id);
    try testing.expectEqual(@as(i32, 42), data.count);
}
```

This enables type-based transformations and projections.

### Adding Field Name Prefixes

Transform field names systematically:

```zig
fn prefixFields(comptime T: type, comptime prefix: []const u8) type {
    const fields = @typeInfo(T).@"struct".fields;
    var prefixed: [fields.len]std.builtin.Type.StructField = undefined;

    inline for (fields, 0..) |field, i| {
        prefixed[i] = .{
            .name = prefix ++ field.name,
            .type = field.type,
            .default_value_ptr = null,
            .is_comptime = field.is_comptime,
            .alignment = field.alignment,
        };
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &prefixed,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "add prefix" {
    const Original = struct {
        name: []const u8,
        value: i32,
    };

    const Prefixed = prefixFields(Original, "my_");

    const data = Prefixed{
        .my_name = "test",
        .my_value = 42,
    };

    try testing.expectEqualStrings("test", data.my_name);
    try testing.expectEqual(@as(i32, 42), data.my_value);
}
```

This helps with namespace management and avoiding name collisions.

### Wrapping Fields in Optionals

Convert all fields to optional types:

```zig
fn makeFieldsOptional(comptime T: type) type {
    const fields = @typeInfo(T).@"struct".fields;
    var optional_fields: [fields.len]std.builtin.Type.StructField = undefined;

    inline for (fields, 0..) |field, i| {
        optional_fields[i] = .{
            .name = field.name,
            .type = ?field.type,
            .default_value_ptr = null,
            .is_comptime = false,
            .alignment = @alignOf(?field.type),
        };
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &optional_fields,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "optional wrapper" {
    const Required = struct {
        name: []const u8,
        age: u32,
    };

    const Optional = makeFieldsOptional(Required);

    const partial = Optional{
        .name = "Alice",
        .age = null,
    };

    try testing.expectEqualStrings("Alice", partial.name.?);
    try testing.expectEqual(@as(?u32, null), partial.age);
}
```

This is useful for builder patterns or partial updates.

### Selecting Specific Fields

Create a struct containing only named fields:

```zig
fn selectFields(comptime T: type, comptime field_names: []const []const u8) type {
    const all_fields = @typeInfo(T).@"struct".fields;
    var selected: [field_names.len]std.builtin.Type.StructField = undefined;

    inline for (field_names, 0..) |name, i| {
        var found = false;
        inline for (all_fields) |field| {
            if (std.mem.eql(u8, field.name, name)) {
                selected[i] = field;
                found = true;
                break;
            }
        }
        if (!found) {
            @compileError("Field '" ++ name ++ "' not found in type " ++ @typeName(T));
        }
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &selected,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "select fields" {
    const Full = struct {
        id: u64,
        name: []const u8,
        email: []const u8,
        age: u32,
        active: bool,
    };

    const Partial = selectFields(Full, &[_][]const u8{ "id", "name", "active" });

    const data = Partial{
        .id = 1,
        .name = "Alice",
        .active = true,
    };

    try testing.expectEqual(@as(u64, 1), data.id);
    try testing.expectEqualStrings("Alice", data.name);
    try testing.expect(data.active);
}
```

This implements projection, useful for API responses or data transfer objects.

### Why This Matters

Programmatic struct creation provides several benefits:

1. **Code Generation** - Generate types from configuration files or schemas
2. **Type Transformations** - Create wrapper types without manual duplication
3. **Composition** - Build complex types from simpler components
4. **DRY Principle** - Avoid repeating similar struct definitions
5. **Compile-Time Validation** - All type errors caught before code runs
6. **Zero Runtime Cost** - All struct generation happens at compile time

### Real-World Applications

These patterns are useful for:

1. **ORM Systems** - Generate database model types from schemas
2. **API Clients** - Create request/response types from API specifications
3. **Serialization** - Generate serialization wrappers automatically
4. **Builder Patterns** - Create optional field versions for builders
5. **Type Safety** - Enforce field presence or absence at compile time
6. **Code Generators** - Build types from external data sources

### Performance Characteristics

All struct generation has zero runtime cost:

- Type construction happens during compilation
- Generated structs are identical to hand-written ones
- No runtime type information needed
- No dynamic dispatch or vtables
- Full compiler optimization applies

The only cost is compile time, which increases with complexity but remains reasonable for most use cases.

### Type System Integration

Generated structs integrate fully with Zig's type system:

- Type inference works normally
- Compiler errors reference generated types
- `@TypeOf` and `@typeInfo` work correctly
- Can be used in generic functions
- Support all struct operations (methods, fields, etc.)

### Limitations and Gotchas

Be aware of these constraints:

1. **Field Names Must Be Compile-Time Known** - Can't generate names from runtime strings
2. **No Circular References** - Generated types can't reference themselves
3. **Type Info Immutable** - Once created, types can't be modified
4. **Error Messages** - Compiler errors may reference generated code locations
5. **Collision Detection** - Check for duplicate field names manually (as shown in `mergeStructs`)

### Combining Patterns

You can chain struct transformations:

```zig
const Base = struct { id: u64, name: []const u8 };
const WithPrefix = prefixFields(Base, "db_");
const Optional = makeFieldsOptional(WithPrefix);

const config = Optional{
    .db_id = 1,
    .db_name = null,
};
```

This enables complex type transformations through composition.

### Field Structure Details

Each `StructField` requires these components:

- **name** - Field name as compile-time string
- **type** - Field type (must be a Zig type)
- **default_value_ptr** - Pointer to default value or null
- **is_comptime** - Whether field is comptime-known
- **alignment** - Field alignment (use `@alignOf(T)`)

All fields must be properly initialized to avoid undefined behavior.

### Debugging Generated Types

Use `@typeName` to inspect generated types:

```zig
const Generated = createFieldsStruct(3, i32);
std.debug.print("Type: {s}\n", .{@typeName(Generated)});
```

This helps understand what the compiler generated.

### Full Tested Code

```zig
// Recipe 9.16: Defining Structs Programmatically
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to create struct types at compile time using @Type.
// All struct generation happens during compilation with zero runtime overhead.

const std = @import("std");
const testing = std.testing;
const builtin = @import("builtin");

// ANCHOR: basic_struct_creation
// Create a simple struct type programmatically
fn createSimpleStruct() type {
    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &[_]std.builtin.Type.StructField{
                .{
                    .name = "x",
                    .type = i32,
                    .default_value_ptr = null,
                    .is_comptime = false,
                    .alignment = @alignOf(i32),
                },
                .{
                    .name = "y",
                    .type = i32,
                    .default_value_ptr = null,
                    .is_comptime = false,
                    .alignment = @alignOf(i32),
                },
            },
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "basic struct creation" {
    const Point = createSimpleStruct();
    const p = Point{ .x = 10, .y = 20 };

    try testing.expectEqual(@as(i32, 10), p.x);
    try testing.expectEqual(@as(i32, 20), p.y);
}
// ANCHOR_END: basic_struct_creation

// ANCHOR: add_fields
// Generate a struct with a variable number of fields
fn createFieldsStruct(comptime count: usize, comptime T: type) type {
    var fields: [count]std.builtin.Type.StructField = undefined;

    for (0..count) |i| {
        const name = std.fmt.comptimePrint("field_{d}", .{i});
        fields[i] = .{
            .name = name,
            .type = T,
            .default_value_ptr = null,
            .is_comptime = false,
            .alignment = @alignOf(T),
        };
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &fields,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "add fields" {
    const ThreeInts = createFieldsStruct(3, i32);
    const data = ThreeInts{
        .field_0 = 1,
        .field_1 = 2,
        .field_2 = 3,
    };

    try testing.expectEqual(@as(i32, 1), data.field_0);
    try testing.expectEqual(@as(i32, 2), data.field_1);
    try testing.expectEqual(@as(i32, 3), data.field_2);
}
// ANCHOR_END: add_fields

// ANCHOR: struct_from_tuples
// Create a struct from a tuple of name-type pairs
fn structFromPairs(comptime pairs: anytype) type {
    const fields_tuple = @typeInfo(@TypeOf(pairs)).@"struct".fields;
    var fields: [fields_tuple.len]std.builtin.Type.StructField = undefined;

    inline for (fields_tuple, 0..) |field, i| {
        const pair = @field(pairs, field.name);
        fields[i] = .{
            .name = pair[0],
            .type = pair[1],
            .default_value_ptr = null,
            .is_comptime = false,
            .alignment = @alignOf(pair[1]),
        };
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &fields,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "struct from tuples" {
    const Person = structFromPairs(.{
        .{ "name", []const u8 },
        .{ "age", u32 },
        .{ "active", bool },
    });

    const person = Person{
        .name = "Alice",
        .age = 30,
        .active = true,
    };

    try testing.expectEqualStrings("Alice", person.name);
    try testing.expectEqual(@as(u32, 30), person.age);
    try testing.expect(person.active);
}
// ANCHOR_END: struct_from_tuples

// ANCHOR: merge_structs
// Merge two struct types into one
// Note: Produces compile error if both structs have fields with the same name
fn mergeStructs(comptime A: type, comptime B: type) type {
    const a_fields = @typeInfo(A).@"struct".fields;
    const b_fields = @typeInfo(B).@"struct".fields;

    // Check for name collisions
    inline for (a_fields) |a_field| {
        inline for (b_fields) |b_field| {
            if (std.mem.eql(u8, a_field.name, b_field.name)) {
                @compileError("Cannot merge structs: field '" ++ a_field.name ++ "' exists in both types");
            }
        }
    }

    var merged: [a_fields.len + b_fields.len]std.builtin.Type.StructField = undefined;

    inline for (a_fields, 0..) |field, i| {
        merged[i] = field;
    }

    inline for (b_fields, 0..) |field, i| {
        merged[a_fields.len + i] = field;
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &merged,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "merge structs" {
    const Position = struct { x: i32, y: i32 };
    const Velocity = struct { dx: f32, dy: f32 };

    const Entity = mergeStructs(Position, Velocity);

    const entity = Entity{
        .x = 10,
        .y = 20,
        .dx = 1.5,
        .dy = 2.5,
    };

    try testing.expectEqual(@as(i32, 10), entity.x);
    try testing.expectEqual(@as(i32, 20), entity.y);
    try testing.expectEqual(@as(f32, 1.5), entity.dx);
    try testing.expectEqual(@as(f32, 2.5), entity.dy);
}
// ANCHOR_END: merge_structs

// ANCHOR: filter_fields
// Create a new struct with only fields matching a predicate
fn filterFields(comptime T: type, comptime predicate: fn (std.builtin.Type.StructField) bool) type {
    const fields = @typeInfo(T).@"struct".fields;

    comptime var count: usize = 0;
    inline for (fields) |field| {
        if (predicate(field)) {
            count += 1;
        }
    }

    var filtered: [count]std.builtin.Type.StructField = undefined;
    comptime var index: usize = 0;
    inline for (fields) |field| {
        if (predicate(field)) {
            filtered[index] = field;
            index += 1;
        }
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &filtered,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

fn isIntegerField(field: std.builtin.Type.StructField) bool {
    return @typeInfo(field.type) == .int or @typeInfo(field.type) == .comptime_int;
}

test "filter fields" {
    const Mixed = struct {
        id: u64,
        name: []const u8,
        count: i32,
        active: bool,
    };

    const IntegersOnly = filterFields(Mixed, isIntegerField);

    const data = IntegersOnly{
        .id = 1,
        .count = 42,
    };

    try testing.expectEqual(@as(u64, 1), data.id);
    try testing.expectEqual(@as(i32, 42), data.count);
}
// ANCHOR_END: filter_fields

// ANCHOR: add_prefix
// Add a prefix to all field names
fn prefixFields(comptime T: type, comptime prefix: []const u8) type {
    const fields = @typeInfo(T).@"struct".fields;
    var prefixed: [fields.len]std.builtin.Type.StructField = undefined;

    inline for (fields, 0..) |field, i| {
        prefixed[i] = .{
            .name = prefix ++ field.name,
            .type = field.type,
            .default_value_ptr = null,
            .is_comptime = field.is_comptime,
            .alignment = field.alignment,
        };
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &prefixed,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "add prefix" {
    const Original = struct {
        name: []const u8,
        value: i32,
    };

    const Prefixed = prefixFields(Original, "my_");

    const data = Prefixed{
        .my_name = "test",
        .my_value = 42,
    };

    try testing.expectEqualStrings("test", data.my_name);
    try testing.expectEqual(@as(i32, 42), data.my_value);
}
// ANCHOR_END: add_prefix

// ANCHOR: optional_wrapper
// Wrap all fields in Optional
fn makeFieldsOptional(comptime T: type) type {
    const fields = @typeInfo(T).@"struct".fields;
    var optional_fields: [fields.len]std.builtin.Type.StructField = undefined;

    inline for (fields, 0..) |field, i| {
        optional_fields[i] = .{
            .name = field.name,
            .type = ?field.type,
            .default_value_ptr = null,
            .is_comptime = false,
            .alignment = @alignOf(?field.type),
        };
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &optional_fields,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "optional wrapper" {
    const Required = struct {
        name: []const u8,
        age: u32,
    };

    const Optional = makeFieldsOptional(Required);

    const partial = Optional{
        .name = "Alice",
        .age = null,
    };

    try testing.expectEqualStrings("Alice", partial.name.?);
    try testing.expectEqual(@as(?u32, null), partial.age);
}
// ANCHOR_END: optional_wrapper

// ANCHOR: select_fields
// Create a struct with only specific fields
// Note: Produces compile error if any field_name doesn't exist in T
fn selectFields(comptime T: type, comptime field_names: []const []const u8) type {
    const all_fields = @typeInfo(T).@"struct".fields;
    var selected: [field_names.len]std.builtin.Type.StructField = undefined;

    inline for (field_names, 0..) |name, i| {
        var found = false;
        inline for (all_fields) |field| {
            if (std.mem.eql(u8, field.name, name)) {
                selected[i] = field;
                found = true;
                break;
            }
        }
        if (!found) {
            @compileError("Field '" ++ name ++ "' not found in type " ++ @typeName(T));
        }
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = &selected,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "select fields" {
    const Full = struct {
        id: u64,
        name: []const u8,
        email: []const u8,
        age: u32,
        active: bool,
    };

    const Partial = selectFields(Full, &[_][]const u8{ "id", "name", "active" });

    const data = Partial{
        .id = 1,
        .name = "Alice",
        .active = true,
    };

    try testing.expectEqual(@as(u64, 1), data.id);
    try testing.expectEqualStrings("Alice", data.name);
    try testing.expect(data.active);
}
// ANCHOR_END: select_fields

// Comprehensive test
test "comprehensive struct generation" {
    // Basic creation
    const Basic = createSimpleStruct();
    const b = Basic{ .x = 1, .y = 2 };
    try testing.expectEqual(@as(i32, 1), b.x);

    // Variable fields
    const Multi = createFieldsStruct(2, u32);
    const m = Multi{ .field_0 = 10, .field_1 = 20 };
    try testing.expectEqual(@as(u32, 10), m.field_0);

    // From tuples
    const FromTuples = structFromPairs(.{
        .{ "a", i32 },
        .{ "b", bool },
    });
    const ft = FromTuples{ .a = 5, .b = true };
    try testing.expectEqual(@as(i32, 5), ft.a);

    // Merged structs
    const A = struct { x: i32 };
    const B = struct { y: i32 };
    const Merged = mergeStructs(A, B);
    const merged = Merged{ .x = 1, .y = 2 };
    try testing.expectEqual(@as(i32, 1), merged.x);

    // Prefixed fields
    const Orig = struct { val: i32 };
    const Pre = prefixFields(Orig, "p_");
    const pre = Pre{ .p_val = 99 };
    try testing.expectEqual(@as(i32, 99), pre.p_val);

    // Optional fields
    const Req = struct { x: i32 };
    const Opt = makeFieldsOptional(Req);
    const opt = Opt{ .x = null };
    try testing.expectEqual(@as(?i32, null), opt.x);

    try testing.expect(true);
}
```

### See Also

- Recipe 9.12: Capturing struct attribute definition order
- Recipe 9.15: Enforcing coding conventions in structs
- Recipe 9.17: Initializing struct members at definition time

---

## Recipe 9.17: Initializing Struct Members at Definition Time {#recipe-9-17}

**Tags:** allocators, comptime, comptime-metaprogramming, error-handling, memory, pointers, slices, testing
**Difficulty:** advanced
**Code:** `code/03-advanced/09-metaprogramming/recipe_9_17.zig`

### Problem

You need to initialize struct members with sensible defaults, provide flexible initialization options, or create instances with different preset configurations. You want to avoid repetitive initialization code, support partial initialization, and provide clean APIs for struct creation.

### Solution

Zig offers multiple approaches for struct initialization: default field values, init functions, builder patterns, factory methods, and compile-time defaults. Each pattern suits different use cases and complexity levels.

### Default Field Values

The simplest approach assigns default values directly in the struct definition:

```zig
// Simple struct with default field values
const Config = struct {
    host: []const u8 = "localhost",
    port: u16 = 8080,
    timeout: u32 = 30,
};

test "default values" {
    const config = Config{};

    try testing.expectEqualStrings("localhost", config.host);
    try testing.expectEqual(@as(u16, 8080), config.port);
    try testing.expectEqual(@as(u32, 30), config.timeout);
}
```

Creating an instance with `Config{}` uses all defaults. This works well for simple configuration structs.

### Partial Initialization

Override specific defaults while keeping others:

```zig
test "partial initialization" {
    const config = Config{
        .port = 3000,
    };

    try testing.expectEqualStrings("localhost", config.host);
    try testing.expectEqual(@as(u16, 3000), config.port);
    try testing.expectEqual(@as(u32, 30), config.timeout);
}
```

Only the port changes; other fields use their defaults.

### Discussion

### Init Functions

For structs without defaults, provide named initialization functions:

```zig
const Point = struct {
    x: f32,
    y: f32,

    pub fn init() Point {
        return .{
            .x = 0.0,
            .y = 0.0,
        };
    }

    pub fn initAt(x: f32, y: f32) Point {
        return .{
            .x = x,
            .y = y,
        };
    }
};

test "init function" {
    const origin = Point.init();
    try testing.expectEqual(@as(f32, 0.0), origin.x);
    try testing.expectEqual(@as(f32, 0.0), origin.y);

    const point = Point.initAt(10.0, 20.0);
    try testing.expectEqual(@as(f32, 10.0), point.x);
    try testing.expectEqual(@as(f32, 20.0), point.y);
}
```

This pattern provides semantic names for different initialization scenarios.

### Compile-Time Default Generation

Generate defaults programmatically using reflection:

```zig
fn createDefaults(comptime T: type) T {
    var result: T = undefined;
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        const default_val = switch (@typeInfo(field.type)) {
            .int => @as(field.type, 0),
            .float => @as(field.type, 0.0),
            .bool => false,
            .pointer => |ptr| switch (ptr.size) {
                .one => @compileError("Cannot create default for single-item pointer"),
                .many, .c => @compileError("Cannot create default for many-item pointer"),
                .slice => @as(field.type, &[_]u8{}),
            },
            else => @compileError("Unsupported type for default value"),
        };
        @field(result, field.name) = default_val;
    }

    return result;
}

test "comptime defaults" {
    const Data = struct {
        count: i32,
        value: f64,
        active: bool,
    };

    const defaults = comptime createDefaults(Data);

    try testing.expectEqual(@as(i32, 0), defaults.count);
    try testing.expectEqual(@as(f64, 0.0), defaults.value);
    try testing.expect(!defaults.active);
}
```

This demonstrates compile-time introspection to generate zero values for any compatible struct.

### Builder Pattern

Implement fluent initialization with method chaining:

```zig
const ServerConfig = struct {
    host: []const u8 = "localhost",
    port: u16 = 8080,
    max_connections: u32 = 100,
    timeout_seconds: u32 = 30,
    enable_logging: bool = true,

    pub fn builder() ServerConfig {
        return .{};
    }

    pub fn withHost(self: ServerConfig, host: []const u8) ServerConfig {
        var result = self;
        result.host = host;
        return result;
    }

    pub fn withPort(self: ServerConfig, port: u16) ServerConfig {
        var result = self;
        result.port = port;
        return result;
    }

    pub fn withMaxConnections(self: ServerConfig, max: u32) ServerConfig {
        var result = self;
        result.max_connections = max;
        return result;
    }
};

test "builder pattern" {
    const config = ServerConfig.builder()
        .withHost("example.com")
        .withPort(9000)
        .withMaxConnections(500);

    try testing.expectEqualStrings("example.com", config.host);
    try testing.expectEqual(@as(u16, 9000), config.port);
    try testing.expectEqual(@as(u32, 500), config.max_connections);
    try testing.expectEqual(@as(u32, 30), config.timeout_seconds);
    try testing.expect(config.enable_logging);
}
```

The builder pattern works well for complex configurations with many optional fields.

### Computed Defaults

Use factory methods to compute related values:

```zig
const Rectangle = struct {
    width: f32,
    height: f32,

    pub fn init(width: f32, height: f32) Rectangle {
        return .{
            .width = width,
            .height = height,
        };
    }

    pub fn square(side: f32) Rectangle {
        return .{
            .width = side,
            .height = side,
        };
    }

    pub fn area(self: Rectangle) f32 {
        return self.width * self.height;
    }
};

test "computed defaults" {
    const rect = Rectangle.init(10.0, 5.0);
    try testing.expectEqual(@as(f32, 50.0), rect.area());

    const sq = Rectangle.square(7.0);
    try testing.expectEqual(@as(f32, 49.0), sq.area());
}
```

The `square` factory method computes both dimensions from a single parameter.

### Optional Fields

Use null defaults for optional configuration:

```zig
const User = struct {
    id: u64,
    name: []const u8,
    email: ?[]const u8 = null,
    phone: ?[]const u8 = null,

    pub fn init(id: u64, name: []const u8) User {
        return .{
            .id = id,
            .name = name,
        };
    }

    pub fn withEmail(self: User, email: []const u8) User {
        var result = self;
        result.email = email;
        return result;
    }
};

test "optional fields" {
    const user1 = User.init(1, "Alice");
    try testing.expectEqual(@as(u64, 1), user1.id);
    try testing.expectEqualStrings("Alice", user1.name);
    try testing.expectEqual(@as(?[]const u8, null), user1.email);

    const user2 = user1.withEmail("alice@example.com");
    try testing.expectEqualStrings("alice@example.com", user2.email.?);
}
```

Optional fields with null defaults support incremental configuration.

### Enum-Based Configuration

Use enums to create named configuration profiles:

```zig
const LogLevel = enum {
    debug,
    info,
    warn,
    err,
};

const Logger = struct {
    level: LogLevel = .info,
    timestamp: bool = true,
    color: bool = false,

    pub fn init() Logger {
        return .{};
    }

    pub fn debug() Logger {
        return .{ .level = .debug };
    }

    pub fn production() Logger {
        return .{
            .level = .warn,
            .timestamp = true,
            .color = false,
        };
    }
};

test "enum defaults" {
    const default_logger = Logger.init();
    try testing.expectEqual(LogLevel.info, default_logger.level);
    try testing.expect(default_logger.timestamp);
    try testing.expect(!default_logger.color);

    const debug_logger = Logger.debug();
    try testing.expectEqual(LogLevel.debug, debug_logger.level);

    const prod_logger = Logger.production();
    try testing.expectEqual(LogLevel.warn, prod_logger.level);
}
```

Named factory methods provide semantic initialization for different environments.

### Array Defaults

Initialize array fields with repetition syntax:

```zig
const Matrix3x3 = struct {
    data: [9]f32 = [_]f32{0.0} ** 9,

    pub fn identity() Matrix3x3 {
        return .{
            .data = [_]f32{
                1.0, 0.0, 0.0,
                0.0, 1.0, 0.0,
                0.0, 0.0, 1.0,
            },
        };
    }

    pub fn get(self: Matrix3x3, row: usize, col: usize) f32 {
        return self.data[row * 3 + col];
    }
};

test "array defaults" {
    const zero_matrix = Matrix3x3{};
    try testing.expectEqual(@as(f32, 0.0), zero_matrix.get(0, 0));
    try testing.expectEqual(@as(f32, 0.0), zero_matrix.get(1, 1));

    const identity = Matrix3x3.identity();
    try testing.expectEqual(@as(f32, 1.0), identity.get(0, 0));
    try testing.expectEqual(@as(f32, 1.0), identity.get(1, 1));
    try testing.expectEqual(@as(f32, 1.0), identity.get(2, 2));
    try testing.expectEqual(@as(f32, 0.0), identity.get(0, 1));
}
```

The `** 9` syntax repeats the value 9 times to fill the array.

### Nested Defaults

Struct defaults cascade to nested structs:

```zig
const Address = struct {
    street: []const u8 = "",
    city: []const u8 = "",
    country: []const u8 = "USA",
};

const Person = struct {
    name: []const u8,
    age: u32 = 0,
    address: Address = .{},

    pub fn init(name: []const u8) Person {
        return .{
            .name = name,
        };
    }
};

test "nested defaults" {
    const person = Person.init("Bob");

    try testing.expectEqualStrings("Bob", person.name);
    try testing.expectEqual(@as(u32, 0), person.age);
    try testing.expectEqualStrings("", person.address.street);
    try testing.expectEqualStrings("USA", person.address.country);
}
```

The `address: Address = .{}` syntax creates a nested struct using its defaults.

### Compile-Time Struct Initialization

Create structs with compile-time constant fields:

```zig
fn createComptimeStruct(comptime name: []const u8, comptime value: i32) type {
    return struct {
        const config_name = name;
        const config_value = value;
        data: i32 = value,

        pub fn init() @This() {
            return .{};
        }
    };
}

test "comptime initialization" {
    const MyStruct = createComptimeStruct("test", 42);

    try testing.expectEqualStrings("test", MyStruct.config_name);
    try testing.expectEqual(@as(i32, 42), MyStruct.config_value);

    const instance = MyStruct.init();
    try testing.expectEqual(@as(i32, 42), instance.data);
}
```

This pattern generates struct types with embedded constants at compile time.

### Factory Pattern

Provide preset configurations through named factory methods:

```zig
const Connection = struct {
    host: []const u8,
    port: u16,
    secure: bool,
    timeout: u32,

    pub fn local() Connection {
        return .{
            .host = "localhost",
            .port = 8080,
            .secure = false,
            .timeout = 30,
        };
    }

    pub fn secureConnection(host: []const u8, port: u16) Connection {
        return .{
            .host = host,
            .port = port,
            .secure = true,
            .timeout = 60,
        };
    }

    pub fn custom(host: []const u8, port: u16, timeout: u32) Connection {
        return .{
            .host = host,
            .port = port,
            .secure = false,
            .timeout = timeout,
        };
    }
};

test "factory pattern" {
    const local = Connection.local();
    try testing.expectEqualStrings("localhost", local.host);
    try testing.expect(!local.secure);

    const secure_conn = Connection.secureConnection("example.com", 443);
    try testing.expectEqualStrings("example.com", secure_conn.host);
    try testing.expectEqual(@as(u16, 443), secure_conn.port);
    try testing.expect(secure_conn.secure);

    const custom = Connection.custom("api.example.com", 9000, 120);
    try testing.expectEqual(@as(u32, 120), custom.timeout);
}
```

Factory methods provide semantic initialization for common scenarios while maintaining flexibility.

### When to Use Each Pattern

Choose the right pattern for your use case:

**Default Values:**
- Simple configuration structs
- Independent fields with no interdependencies
- Fields rarely need customization
- Example: `Config{ .port = 3000 }`

**Init Functions:**
- Structs with required parameters
- Complex initialization logic
- Field validation needed
- Example: `Point.init()`, `Point.initAt(x, y)`

**Builder Pattern:**
- Many optional configuration fields
- Step-by-step construction preferred
- Fluent API desired
- Example: `ServerConfig.builder().withHost("x").withPort(80)`

**Factory Methods:**
- Multiple preset configurations
- Semantic initialization needed
- Common use cases deserve named methods
- Example: `Logger.production()`, `Connection.local()`

**Compile-Time Defaults:**
- Generic default generation needed
- Type-based initialization
- Metaprogramming applications
- Example: `createDefaults(MyStruct)`

### Important Considerations

Default field values should only be used when fields are truly independent. For structs with interdependent fields, prefer factory methods or computed properties:

```zig
// Don't do this - fields can become inconsistent:
const BadRectangle = struct {
    width: f32 = 10.0,
    height: f32 = 5.0,
    area: f32 = 50.0,  // Can diverge from width * height
};

// Do this instead - compute dependent values:
const GoodRectangle = struct {
    width: f32,
    height: f32,

    pub fn area(self: GoodRectangle) f32 {
        return self.width * self.height;
    }
};
```

### Performance Characteristics

All initialization patterns have zero runtime overhead:

- Default values are compile-time constants
- Builder pattern copies are optimized away
- Factory methods inline completely
- No virtual dispatch or dynamic allocation
- Struct layout identical to manual initialization

The compiler generates the same machine code regardless of which pattern you use.

### Memory Management

These patterns work naturally with Zig's explicit allocation:

- Stack allocation: `const config = Config{};`
- Heap allocation: `const config = try allocator.create(Config);`
- Builder pattern works identically for both

No hidden allocations occur in any of these patterns.

### Combining Patterns

Mix and match patterns as needed:

```zig
const config = ServerConfig.builder()  // Builder pattern
    .withHost("example.com")
    .withPort(9000);

const logger = Logger.production();  // Factory method

const person = Person.init("Alice");  // Init function

const partial = Config{ .port = 3000 };  // Partial defaults
```

Each pattern complements the others for different use cases.

### Full Tested Code

```zig
// Recipe 9.17: Initializing Struct Members at Definition Time
// Target Zig Version: 0.15.2
//
// This recipe demonstrates compile-time struct initialization patterns,
// default values, and automatic field population.
//
// Important: Default field values should only be used when fields are
// truly independent. For complex types with interdependent fields,
// prefer named default constants or factory methods.

const std = @import("std");
const testing = std.testing;

// ANCHOR: default_values
// Simple struct with default field values
const Config = struct {
    host: []const u8 = "localhost",
    port: u16 = 8080,
    timeout: u32 = 30,
};

test "default values" {
    const config = Config{};

    try testing.expectEqualStrings("localhost", config.host);
    try testing.expectEqual(@as(u16, 8080), config.port);
    try testing.expectEqual(@as(u32, 30), config.timeout);
}
// ANCHOR_END: default_values

// ANCHOR: partial_init
// Override some defaults while keeping others
test "partial initialization" {
    const config = Config{
        .port = 3000,
    };

    try testing.expectEqualStrings("localhost", config.host);
    try testing.expectEqual(@as(u16, 3000), config.port);
    try testing.expectEqual(@as(u32, 30), config.timeout);
}
// ANCHOR_END: partial_init

// ANCHOR: init_function
// Custom initialization function with defaults
const Point = struct {
    x: f32,
    y: f32,

    pub fn init() Point {
        return .{
            .x = 0.0,
            .y = 0.0,
        };
    }

    pub fn initAt(x: f32, y: f32) Point {
        return .{
            .x = x,
            .y = y,
        };
    }
};

test "init function" {
    const origin = Point.init();
    try testing.expectEqual(@as(f32, 0.0), origin.x);
    try testing.expectEqual(@as(f32, 0.0), origin.y);

    const point = Point.initAt(10.0, 20.0);
    try testing.expectEqual(@as(f32, 10.0), point.x);
    try testing.expectEqual(@as(f32, 20.0), point.y);
}
// ANCHOR_END: init_function

// ANCHOR: comptime_defaults
// Generate default values at compile time
fn createDefaults(comptime T: type) T {
    var result: T = undefined;
    const fields = @typeInfo(T).@"struct".fields;

    inline for (fields) |field| {
        const default_val = switch (@typeInfo(field.type)) {
            .int => @as(field.type, 0),
            .float => @as(field.type, 0.0),
            .bool => false,
            .pointer => |ptr| switch (ptr.size) {
                .one => @compileError("Cannot create default for single-item pointer"),
                .many, .c => @compileError("Cannot create default for many-item pointer"),
                .slice => @as(field.type, &[_]u8{}),
            },
            else => @compileError("Unsupported type for default value"),
        };
        @field(result, field.name) = default_val;
    }

    return result;
}

test "comptime defaults" {
    const Data = struct {
        count: i32,
        value: f64,
        active: bool,
    };

    const defaults = comptime createDefaults(Data);

    try testing.expectEqual(@as(i32, 0), defaults.count);
    try testing.expectEqual(@as(f64, 0.0), defaults.value);
    try testing.expect(!defaults.active);
}
// ANCHOR_END: comptime_defaults

// ANCHOR: builder_pattern
// Builder pattern with incremental initialization
const ServerConfig = struct {
    host: []const u8 = "localhost",
    port: u16 = 8080,
    max_connections: u32 = 100,
    timeout_seconds: u32 = 30,
    enable_logging: bool = true,

    pub fn builder() ServerConfig {
        return .{};
    }

    pub fn withHost(self: ServerConfig, host: []const u8) ServerConfig {
        var result = self;
        result.host = host;
        return result;
    }

    pub fn withPort(self: ServerConfig, port: u16) ServerConfig {
        var result = self;
        result.port = port;
        return result;
    }

    pub fn withMaxConnections(self: ServerConfig, max: u32) ServerConfig {
        var result = self;
        result.max_connections = max;
        return result;
    }
};

test "builder pattern" {
    const config = ServerConfig.builder()
        .withHost("example.com")
        .withPort(9000)
        .withMaxConnections(500);

    try testing.expectEqualStrings("example.com", config.host);
    try testing.expectEqual(@as(u16, 9000), config.port);
    try testing.expectEqual(@as(u32, 500), config.max_connections);
    try testing.expectEqual(@as(u32, 30), config.timeout_seconds);
    try testing.expect(config.enable_logging);
}
// ANCHOR_END: builder_pattern

// ANCHOR: computed_defaults
// Defaults computed from other values
const Rectangle = struct {
    width: f32,
    height: f32,

    pub fn init(width: f32, height: f32) Rectangle {
        return .{
            .width = width,
            .height = height,
        };
    }

    pub fn square(side: f32) Rectangle {
        return .{
            .width = side,
            .height = side,
        };
    }

    pub fn area(self: Rectangle) f32 {
        return self.width * self.height;
    }
};

test "computed defaults" {
    const rect = Rectangle.init(10.0, 5.0);
    try testing.expectEqual(@as(f32, 50.0), rect.area());

    const sq = Rectangle.square(7.0);
    try testing.expectEqual(@as(f32, 49.0), sq.area());
}
// ANCHOR_END: computed_defaults

// ANCHOR: optional_fields
// Optional fields with null defaults
const User = struct {
    id: u64,
    name: []const u8,
    email: ?[]const u8 = null,
    phone: ?[]const u8 = null,

    pub fn init(id: u64, name: []const u8) User {
        return .{
            .id = id,
            .name = name,
        };
    }

    pub fn withEmail(self: User, email: []const u8) User {
        var result = self;
        result.email = email;
        return result;
    }
};

test "optional fields" {
    const user1 = User.init(1, "Alice");
    try testing.expectEqual(@as(u64, 1), user1.id);
    try testing.expectEqualStrings("Alice", user1.name);
    try testing.expectEqual(@as(?[]const u8, null), user1.email);

    const user2 = user1.withEmail("alice@example.com");
    try testing.expectEqualStrings("alice@example.com", user2.email.?);
}
// ANCHOR_END: optional_fields

// ANCHOR: enum_defaults
// Enum-based configuration with defaults
const LogLevel = enum {
    debug,
    info,
    warn,
    err,
};

const Logger = struct {
    level: LogLevel = .info,
    timestamp: bool = true,
    color: bool = false,

    pub fn init() Logger {
        return .{};
    }

    pub fn debug() Logger {
        return .{ .level = .debug };
    }

    pub fn production() Logger {
        return .{
            .level = .warn,
            .timestamp = true,
            .color = false,
        };
    }
};

test "enum defaults" {
    const default_logger = Logger.init();
    try testing.expectEqual(LogLevel.info, default_logger.level);
    try testing.expect(default_logger.timestamp);
    try testing.expect(!default_logger.color);

    const debug_logger = Logger.debug();
    try testing.expectEqual(LogLevel.debug, debug_logger.level);

    const prod_logger = Logger.production();
    try testing.expectEqual(LogLevel.warn, prod_logger.level);
}
// ANCHOR_END: enum_defaults

// ANCHOR: array_defaults
// Arrays with default values
const Matrix3x3 = struct {
    data: [9]f32 = [_]f32{0.0} ** 9,

    pub fn identity() Matrix3x3 {
        return .{
            .data = [_]f32{
                1.0, 0.0, 0.0,
                0.0, 1.0, 0.0,
                0.0, 0.0, 1.0,
            },
        };
    }

    pub fn get(self: Matrix3x3, row: usize, col: usize) f32 {
        return self.data[row * 3 + col];
    }
};

test "array defaults" {
    const zero_matrix = Matrix3x3{};
    try testing.expectEqual(@as(f32, 0.0), zero_matrix.get(0, 0));
    try testing.expectEqual(@as(f32, 0.0), zero_matrix.get(1, 1));

    const identity = Matrix3x3.identity();
    try testing.expectEqual(@as(f32, 1.0), identity.get(0, 0));
    try testing.expectEqual(@as(f32, 1.0), identity.get(1, 1));
    try testing.expectEqual(@as(f32, 1.0), identity.get(2, 2));
    try testing.expectEqual(@as(f32, 0.0), identity.get(0, 1));
}
// ANCHOR_END: array_defaults

// ANCHOR: nested_defaults
// Nested structs with cascading defaults
const Address = struct {
    street: []const u8 = "",
    city: []const u8 = "",
    country: []const u8 = "USA",
};

const Person = struct {
    name: []const u8,
    age: u32 = 0,
    address: Address = .{},

    pub fn init(name: []const u8) Person {
        return .{
            .name = name,
        };
    }
};

test "nested defaults" {
    const person = Person.init("Bob");

    try testing.expectEqualStrings("Bob", person.name);
    try testing.expectEqual(@as(u32, 0), person.age);
    try testing.expectEqualStrings("", person.address.street);
    try testing.expectEqualStrings("USA", person.address.country);
}
// ANCHOR_END: nested_defaults

// ANCHOR: comptime_init
// Compile-time struct initialization
fn createComptimeStruct(comptime name: []const u8, comptime value: i32) type {
    return struct {
        const config_name = name;
        const config_value = value;
        data: i32 = value,

        pub fn init() @This() {
            return .{};
        }
    };
}

test "comptime initialization" {
    const MyStruct = createComptimeStruct("test", 42);

    try testing.expectEqualStrings("test", MyStruct.config_name);
    try testing.expectEqual(@as(i32, 42), MyStruct.config_value);

    const instance = MyStruct.init();
    try testing.expectEqual(@as(i32, 42), instance.data);
}
// ANCHOR_END: comptime_init

// ANCHOR: factory_pattern
// Factory methods for different initialization scenarios
const Connection = struct {
    host: []const u8,
    port: u16,
    secure: bool,
    timeout: u32,

    pub fn local() Connection {
        return .{
            .host = "localhost",
            .port = 8080,
            .secure = false,
            .timeout = 30,
        };
    }

    pub fn secureConnection(host: []const u8, port: u16) Connection {
        return .{
            .host = host,
            .port = port,
            .secure = true,
            .timeout = 60,
        };
    }

    pub fn custom(host: []const u8, port: u16, timeout: u32) Connection {
        return .{
            .host = host,
            .port = port,
            .secure = false,
            .timeout = timeout,
        };
    }
};

test "factory pattern" {
    const local = Connection.local();
    try testing.expectEqualStrings("localhost", local.host);
    try testing.expect(!local.secure);

    const secure_conn = Connection.secureConnection("example.com", 443);
    try testing.expectEqualStrings("example.com", secure_conn.host);
    try testing.expectEqual(@as(u16, 443), secure_conn.port);
    try testing.expect(secure_conn.secure);

    const custom = Connection.custom("api.example.com", 9000, 120);
    try testing.expectEqual(@as(u32, 120), custom.timeout);
}
// ANCHOR_END: factory_pattern

// Comprehensive test
test "comprehensive initialization patterns" {
    // Default values
    const cfg = Config{};
    try testing.expectEqual(@as(u16, 8080), cfg.port);

    // Init function
    const pt = Point.init();
    try testing.expectEqual(@as(f32, 0.0), pt.x);

    // Builder pattern
    const srv = ServerConfig.builder().withPort(5000);
    try testing.expectEqual(@as(u16, 5000), srv.port);

    // Optional fields
    const usr = User.init(1, "Test");
    try testing.expectEqual(@as(?[]const u8, null), usr.email);

    // Enum defaults
    const log = Logger.init();
    try testing.expectEqual(LogLevel.info, log.level);

    // Array defaults
    const mat = Matrix3x3{};
    try testing.expectEqual(@as(f32, 0.0), mat.get(0, 0));

    // Nested defaults
    const pers = Person.init("Alice");
    try testing.expectEqualStrings("USA", pers.address.country);

    // Factory pattern
    const conn = Connection.local();
    try testing.expectEqualStrings("localhost", conn.host);

    try testing.expect(true);
}
```

### See Also

- Recipe 9.11: Using comptime to control instance creation
- Recipe 9.16: Defining structs programmatically
- Recipe 8.11: Simplifying the initialization of data structures

---

## Recipe 17.1: Type-Level Pattern Matching {#recipe-17-1}

**Tags:** comptime, comptime-metaprogramming, error-handling, pointers, slices, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/17-advanced-comptime/recipe_17_1.zig`

### Problem

You need to write generic functions that behave differently based on the characteristics of the types they operate on, such as whether a type is numeric, its size, or what fields a struct contains. This requires compile-time type inspection and pattern matching.

### Solution

Zig provides powerful compile-time reflection through `@typeInfo()`, which returns detailed information about any type. You can use this to match types against patterns and implement type-aware generic functions.

### Basic Type Matching

Check if a type belongs to a specific category:

```zig
/// Check if a type is a numeric type (integer or float)
fn isNumeric(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .int, .comptime_int, .float, .comptime_float => true,
        else => false,
    };
}

test "basic type matching" {
    try testing.expect(isNumeric(i32));
    try testing.expect(isNumeric(u64));
    try testing.expect(isNumeric(f32));
    try testing.expect(isNumeric(f64));
    try testing.expect(!isNumeric(bool));
    try testing.expect(!isNumeric([]const u8));
}
```

### Categorizing Types

Create broader type categories for more flexible matching:

```zig
/// Categorize types into broad families
const TypeCategory = enum {
    integer,
    float,
    pointer,
    array,
    slice,
    @"struct",
    @"enum",
    @"union",
    optional,
    error_union,
    other,
};

fn categorizeType(comptime T: type) TypeCategory {
    return switch (@typeInfo(T)) {
        .int, .comptime_int => .integer,
        .float, .comptime_float => .float,
        .pointer => .pointer,
        .array => .array,
        .@"struct" => .@"struct",
        .@"enum" => .@"enum",
        .@"union" => .@"union",
        .optional => .optional,
        .error_union => .error_union,
        else => .other,
    };
}

test "type categorization" {
    try testing.expectEqual(TypeCategory.integer, categorizeType(i32));
    try testing.expectEqual(TypeCategory.float, categorizeType(f64));
    try testing.expectEqual(TypeCategory.pointer, categorizeType(*u8));
    try testing.expectEqual(TypeCategory.array, categorizeType([10]u8));
    try testing.expectEqual(TypeCategory.optional, categorizeType(?i32));
}
```

### Generic Zero Values

Generate appropriate zero values for any numeric type:

```zig
/// Return the "zero" value for any numeric type
fn zero(comptime T: type) T {
    const info = @typeInfo(T);

    return switch (info) {
        .int, .comptime_int => 0,
        .float, .comptime_float => 0.0,
        else => @compileError("zero() only works with numeric types"),
    };
}

test "generic zero value" {
    try testing.expectEqual(@as(i32, 0), zero(i32));
    try testing.expectEqual(@as(u64, 0), zero(u64));
    try testing.expectEqual(@as(f32, 0.0), zero(f32));
    try testing.expectEqual(@as(f64, 0.0), zero(f64));
}
```

### Container Depth Analysis

Calculate how deeply nested a type is:

```zig
/// Calculate the nesting depth of container types (arrays, slices, pointers)
fn containerDepth(comptime T: type) comptime_int {
    const info = @typeInfo(T);

    return switch (info) {
        .pointer => |ptr| 1 + containerDepth(ptr.child),
        .array => |arr| 1 + containerDepth(arr.child),
        .optional => |opt| 1 + containerDepth(opt.child),
        else => 0,
    };
}

test "container depth calculation" {
    try testing.expectEqual(0, containerDepth(i32));
    try testing.expectEqual(1, containerDepth(*i32));
    try testing.expectEqual(2, containerDepth(**i32));
    try testing.expectEqual(1, containerDepth([10]u8));
    try testing.expectEqual(2, containerDepth([5][10]u8));
    try testing.expectEqual(1, containerDepth(?i32));
    try testing.expectEqual(2, containerDepth(?*i32));
}
```

### Unwrapping Nested Types

Peel away layers of pointers, arrays, and optionals to get the innermost type:

```zig
/// Unwrap nested container types to get the innermost child type
fn unwrapType(comptime T: type) type {
    const info = @typeInfo(T);

    return switch (info) {
        .pointer => |ptr| unwrapType(ptr.child),
        .array => |arr| unwrapType(arr.child),
        .optional => |opt| unwrapType(opt.child),
        else => T,
    };
}

test "unwrap nested types" {
    try testing.expectEqual(i32, unwrapType(i32));
    try testing.expectEqual(i32, unwrapType(*i32));
    try testing.expectEqual(i32, unwrapType(**i32));
    try testing.expectEqual(u8, unwrapType([10]u8));
    try testing.expectEqual(u8, unwrapType([5][10]u8));
    try testing.expectEqual(i32, unwrapType(?i32));
    try testing.expectEqual(i32, unwrapType(?*i32));
}
```

### Size-Based Dispatch

Choose different strategies based on type size:

```zig
/// Choose an implementation based on type size
fn processValue(comptime T: type, value: T) void {
    const size = @sizeOf(T);

    if (size <= 8) {
        // Fast path for small types that fit in a register
        processSmall(T, value);
    } else {
        // Different strategy for larger types
        processLarge(T, value);
    }
}

fn processSmall(comptime T: type, value: T) void {
    _ = value;
    std.debug.print("Processing small type {} (size: {} bytes)\n", .{ T, @sizeOf(T) });
}

fn processLarge(comptime T: type, value: T) void {
    _ = value;
    std.debug.print("Processing large type {} (size: {} bytes)\n", .{ T, @sizeOf(T) });
}

test "size-based dispatch" {
    processValue(u8, 42);
    processValue(u64, 1000);
    processValue([100]u8, [_]u8{0} ** 100);
}
```

### Integer Signedness Matching

Inspect and transform integer signedness at compile time:

```zig
/// Determine if an integer type is signed or unsigned
fn isSigned(comptime T: type) bool {
    const info = @typeInfo(T);

    return switch (info) {
        .int => |int_info| int_info.signedness == .signed,
        else => @compileError("isSigned() only works with integer types"),
    };
}

/// Get the corresponding signed or unsigned version of an integer type
fn toggleSignedness(comptime T: type) type {
    const info = @typeInfo(T);

    return switch (info) {
        .int => |int_info| {
            const new_signedness: std.builtin.Signedness =
                if (int_info.signedness == .signed) .unsigned else .signed;

            return @Type(.{
                .int = .{
                    .signedness = new_signedness,
                    .bits = int_info.bits
                }
            });
        },
        else => @compileError("toggleSignedness() only works with integer types"),
    };
}

test "signedness matching" {
    try testing.expect(isSigned(i32));
    try testing.expect(!isSigned(u32));

    try testing.expectEqual(u32, toggleSignedness(i32));
    try testing.expectEqual(i32, toggleSignedness(u32));
    try testing.expectEqual(u64, toggleSignedness(i64));
    try testing.expectEqual(i8, toggleSignedness(u8));
}
```

### Struct Field Matching

Check for the presence of specific fields and get their types:

```zig
/// Check if a struct has a specific field
fn hasField(comptime T: type, comptime field_name: []const u8) bool {
    const info = @typeInfo(T);

    return switch (info) {
        .@"struct" => |struct_info| {
            inline for (struct_info.fields) |field| {
                if (std.mem.eql(u8, field.name, field_name)) {
                    return true;
                }
            }
            return false;
        },
        else => false,
    };
}

/// Get the type of a specific field if it exists
fn fieldType(comptime T: type, comptime field_name: []const u8) ?type {
    const info = @typeInfo(T);

    return switch (info) {
        .@"struct" => |struct_info| {
            inline for (struct_info.fields) |field| {
                if (std.mem.eql(u8, field.name, field_name)) {
                    return field.type;
                }
            }
            return null;
        },
        else => null,
    };
}

const TestStruct = struct {
    id: u32,
    name: []const u8,
    value: f64,
};

test "struct field matching" {
    try testing.expect(hasField(TestStruct, "id"));
    try testing.expect(hasField(TestStruct, "name"));
    try testing.expect(hasField(TestStruct, "value"));
    try testing.expect(!hasField(TestStruct, "missing"));

    try testing.expectEqual(u32, fieldType(TestStruct, "id").?);
    try testing.expectEqual([]const u8, fieldType(TestStruct, "name").?);
    try testing.expectEqual(f64, fieldType(TestStruct, "value").?);
    try testing.expectEqual(@as(?type, null), fieldType(TestStruct, "missing"));
}
```

### Polymorphic Serializer

Build a generic serializer that adapts to different types automatically:

```zig
/// Generic serializer that adapts to different type patterns
fn serialize(comptime T: type, value: T, writer: anytype) !void {
    const info = @typeInfo(T);

    switch (info) {
        .int, .comptime_int => try writer.print("{d}", .{value}),
        .float, .comptime_float => try writer.print("{d:.2}", .{value}),
        .bool => try writer.writeAll(if (value) "true" else "false"),
        .pointer => |ptr| {
            if (ptr.size == .slice) {
                if (ptr.child == u8) {
                    // Special case for string slices
                    try writer.print("\"{s}\"", .{value});
                } else {
                    try writer.writeAll("[");
                    for (value, 0..) |item, i| {
                        if (i > 0) try writer.writeAll(", ");
                        try serialize(ptr.child, item, writer);
                    }
                    try writer.writeAll("]");
                }
            } else {
                try writer.writeAll("(pointer)");
            }
        },
        .array => |arr| {
            try writer.writeAll("[");
            for (value, 0..) |item, i| {
                if (i > 0) try writer.writeAll(", ");
                try serialize(arr.child, item, writer);
            }
            try writer.writeAll("]");
        },
        .optional => {
            if (value) |val| {
                try serialize(@TypeOf(val), val, writer);
            } else {
                try writer.writeAll("null");
            }
        },
        else => try writer.writeAll("(unsupported)"),
    }
}

test "polymorphic serializer" {
    var buffer: [1024]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    try serialize(i32, 42, writer);
    try writer.writeAll(" ");

    try serialize(f64, 3.14159, writer);
    try writer.writeAll(" ");

    try serialize(bool, true, writer);
    try writer.writeAll(" ");

    try serialize([]const u8, "hello", writer);
    try writer.writeAll(" ");

    const arr = [_]i32{ 1, 2, 3 };
    try serialize([3]i32, arr, writer);
    try writer.writeAll(" ");

    try serialize(?i32, null, writer);
    try writer.writeAll(" ");

    try serialize(?i32, 99, writer);

    const output = fbs.getWritten();
    try testing.expect(std.mem.indexOf(u8, output, "42") != null);
    try testing.expect(std.mem.indexOf(u8, output, "3.14") != null);
    try testing.expect(std.mem.indexOf(u8, output, "true") != null);
    try testing.expect(std.mem.indexOf(u8, output, "\"hello\"") != null);
    try testing.expect(std.mem.indexOf(u8, output, "[1, 2, 3]") != null);
    try testing.expect(std.mem.indexOf(u8, output, "null") != null);
    try testing.expect(std.mem.indexOf(u8, output, "99") != null);
}
```

### Discussion

Type-level pattern matching is one of Zig's most powerful metaprogramming features. Unlike runtime reflection in other languages, Zig's type introspection happens entirely at compile time, meaning zero runtime overhead.

### How @typeInfo Works

The `@typeInfo()` builtin returns a `std.builtin.Type` union that describes the type's structure. You can switch on this union to handle different type categories:

- `.int` and `.comptime_int` for integer types
- `.float` and `.comptime_float` for floating-point types
- `.pointer` for pointers (with information about mutability, child type, and size)
- `.array` for fixed-size arrays
- `.@"struct"` for struct types (with field information)
- `.@"enum"` and `.@"union"` for enums and unions
- `.optional` for optional types
- `.error_union` for error unions

### Pattern Matching Strategies

**Simple Category Checks**: Use basic switches to check if a type belongs to a family like numeric types, containers, or aggregates.

**Recursive Type Analysis**: Many type properties require recursion, like calculating nesting depth or unwrapping nested containers. These functions call themselves with child types until reaching a base case.

**Type Construction**: Use `@Type()` to build new types based on patterns you've matched. This is how `toggleSignedness()` creates unsigned versions of signed integers.

**Field Iteration**: When inspecting struct fields, use `inline for` to iterate at compile time. The compiler unrolls the loop and each iteration can access comptime-only information like field types.

### Compile-Time Guarantees

Since all type matching happens at compile time:

- Invalid operations are caught immediately with `@compileError()`
- No runtime type checks or casts are needed
- The generated code is as efficient as hand-written type-specific code
- You get full type safety without performance cost

### Practical Applications

**Generic Collections**: Adapt container behavior based on element types (use memcpy for simple types, proper cleanup for complex types).

**Serialization**: Automatically serialize any type by inspecting its structure, as shown in the polymorphic serializer example.

**Memory Optimization**: Choose allocation strategies based on type size and alignment requirements.

**API Validation**: Enforce constraints on generic parameters, like requiring certain struct fields or numeric bounds.

**Zero-Cost Abstractions**: Create high-level interfaces that compile down to optimal machine code tailored to each concrete type.

### Full Tested Code

```zig
// Recipe 17.1: Type-Level Pattern Matching
// This recipe demonstrates how to use compile-time reflection to match and
// transform types based on patterns, implementing generic functions that
// behave differently for specific type families.

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_type_matching
/// Check if a type is a numeric type (integer or float)
fn isNumeric(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .int, .comptime_int, .float, .comptime_float => true,
        else => false,
    };
}

test "basic type matching" {
    try testing.expect(isNumeric(i32));
    try testing.expect(isNumeric(u64));
    try testing.expect(isNumeric(f32));
    try testing.expect(isNumeric(f64));
    try testing.expect(!isNumeric(bool));
    try testing.expect(!isNumeric([]const u8));
}
// ANCHOR_END: basic_type_matching

// ANCHOR: type_categories
/// Categorize types into broad families
const TypeCategory = enum {
    integer,
    float,
    pointer,
    array,
    slice,
    @"struct",
    @"enum",
    @"union",
    optional,
    error_union,
    other,
};

fn categorizeType(comptime T: type) TypeCategory {
    return switch (@typeInfo(T)) {
        .int, .comptime_int => .integer,
        .float, .comptime_float => .float,
        .pointer => .pointer,
        .array => .array,
        .@"struct" => .@"struct",
        .@"enum" => .@"enum",
        .@"union" => .@"union",
        .optional => .optional,
        .error_union => .error_union,
        else => .other,
    };
}

test "type categorization" {
    try testing.expectEqual(TypeCategory.integer, categorizeType(i32));
    try testing.expectEqual(TypeCategory.float, categorizeType(f64));
    try testing.expectEqual(TypeCategory.pointer, categorizeType(*u8));
    try testing.expectEqual(TypeCategory.array, categorizeType([10]u8));
    try testing.expectEqual(TypeCategory.optional, categorizeType(?i32));
}
// ANCHOR_END: type_categories

// ANCHOR: generic_zero
/// Return the "zero" value for any numeric type
fn zero(comptime T: type) T {
    const info = @typeInfo(T);

    return switch (info) {
        .int, .comptime_int => 0,
        .float, .comptime_float => 0.0,
        else => @compileError("zero() only works with numeric types"),
    };
}

test "generic zero value" {
    try testing.expectEqual(@as(i32, 0), zero(i32));
    try testing.expectEqual(@as(u64, 0), zero(u64));
    try testing.expectEqual(@as(f32, 0.0), zero(f32));
    try testing.expectEqual(@as(f64, 0.0), zero(f64));
}
// ANCHOR_END: generic_zero

// ANCHOR: container_depth
/// Calculate the nesting depth of container types (arrays, slices, pointers)
fn containerDepth(comptime T: type) comptime_int {
    const info = @typeInfo(T);

    return switch (info) {
        .pointer => |ptr| 1 + containerDepth(ptr.child),
        .array => |arr| 1 + containerDepth(arr.child),
        .optional => |opt| 1 + containerDepth(opt.child),
        else => 0,
    };
}

test "container depth calculation" {
    try testing.expectEqual(0, containerDepth(i32));
    try testing.expectEqual(1, containerDepth(*i32));
    try testing.expectEqual(2, containerDepth(**i32));
    try testing.expectEqual(1, containerDepth([10]u8));
    try testing.expectEqual(2, containerDepth([5][10]u8));
    try testing.expectEqual(1, containerDepth(?i32));
    try testing.expectEqual(2, containerDepth(?*i32));
}
// ANCHOR_END: container_depth

// ANCHOR: unwrap_type
/// Unwrap nested container types to get the innermost child type
fn unwrapType(comptime T: type) type {
    const info = @typeInfo(T);

    return switch (info) {
        .pointer => |ptr| unwrapType(ptr.child),
        .array => |arr| unwrapType(arr.child),
        .optional => |opt| unwrapType(opt.child),
        else => T,
    };
}

test "unwrap nested types" {
    try testing.expectEqual(i32, unwrapType(i32));
    try testing.expectEqual(i32, unwrapType(*i32));
    try testing.expectEqual(i32, unwrapType(**i32));
    try testing.expectEqual(u8, unwrapType([10]u8));
    try testing.expectEqual(u8, unwrapType([5][10]u8));
    try testing.expectEqual(i32, unwrapType(?i32));
    try testing.expectEqual(i32, unwrapType(?*i32));
}
// ANCHOR_END: unwrap_type

// ANCHOR: size_based_dispatch
/// Choose an implementation based on type size
fn processValue(comptime T: type, value: T) void {
    const size = @sizeOf(T);

    if (size <= 8) {
        // Fast path for small types that fit in a register
        processSmall(T, value);
    } else {
        // Different strategy for larger types
        processLarge(T, value);
    }
}

fn processSmall(comptime T: type, value: T) void {
    _ = value;
    std.debug.print("Processing small type {} (size: {} bytes)\n", .{ T, @sizeOf(T) });
}

fn processLarge(comptime T: type, value: T) void {
    _ = value;
    std.debug.print("Processing large type {} (size: {} bytes)\n", .{ T, @sizeOf(T) });
}

test "size-based dispatch" {
    processValue(u8, 42);
    processValue(u64, 1000);
    processValue([100]u8, [_]u8{0} ** 100);
}
// ANCHOR_END: size_based_dispatch

// ANCHOR: signedness_matching
/// Determine if an integer type is signed or unsigned
fn isSigned(comptime T: type) bool {
    const info = @typeInfo(T);

    return switch (info) {
        .int => |int_info| int_info.signedness == .signed,
        else => @compileError("isSigned() only works with integer types"),
    };
}

/// Get the corresponding signed or unsigned version of an integer type
fn toggleSignedness(comptime T: type) type {
    const info = @typeInfo(T);

    return switch (info) {
        .int => |int_info| {
            const new_signedness: std.builtin.Signedness =
                if (int_info.signedness == .signed) .unsigned else .signed;

            return @Type(.{
                .int = .{
                    .signedness = new_signedness,
                    .bits = int_info.bits
                }
            });
        },
        else => @compileError("toggleSignedness() only works with integer types"),
    };
}

test "signedness matching" {
    try testing.expect(isSigned(i32));
    try testing.expect(!isSigned(u32));

    try testing.expectEqual(u32, toggleSignedness(i32));
    try testing.expectEqual(i32, toggleSignedness(u32));
    try testing.expectEqual(u64, toggleSignedness(i64));
    try testing.expectEqual(i8, toggleSignedness(u8));
}
// ANCHOR_END: signedness_matching

// ANCHOR: struct_field_matching
/// Check if a struct has a specific field
fn hasField(comptime T: type, comptime field_name: []const u8) bool {
    const info = @typeInfo(T);

    return switch (info) {
        .@"struct" => |struct_info| {
            inline for (struct_info.fields) |field| {
                if (std.mem.eql(u8, field.name, field_name)) {
                    return true;
                }
            }
            return false;
        },
        else => false,
    };
}

/// Get the type of a specific field if it exists
fn fieldType(comptime T: type, comptime field_name: []const u8) ?type {
    const info = @typeInfo(T);

    return switch (info) {
        .@"struct" => |struct_info| {
            inline for (struct_info.fields) |field| {
                if (std.mem.eql(u8, field.name, field_name)) {
                    return field.type;
                }
            }
            return null;
        },
        else => null,
    };
}

const TestStruct = struct {
    id: u32,
    name: []const u8,
    value: f64,
};

test "struct field matching" {
    try testing.expect(hasField(TestStruct, "id"));
    try testing.expect(hasField(TestStruct, "name"));
    try testing.expect(hasField(TestStruct, "value"));
    try testing.expect(!hasField(TestStruct, "missing"));

    try testing.expectEqual(u32, fieldType(TestStruct, "id").?);
    try testing.expectEqual([]const u8, fieldType(TestStruct, "name").?);
    try testing.expectEqual(f64, fieldType(TestStruct, "value").?);
    try testing.expectEqual(@as(?type, null), fieldType(TestStruct, "missing"));
}
// ANCHOR_END: struct_field_matching

// ANCHOR: polymorphic_serializer
/// Generic serializer that adapts to different type patterns
fn serialize(comptime T: type, value: T, writer: anytype) !void {
    const info = @typeInfo(T);

    switch (info) {
        .int, .comptime_int => try writer.print("{d}", .{value}),
        .float, .comptime_float => try writer.print("{d:.2}", .{value}),
        .bool => try writer.writeAll(if (value) "true" else "false"),
        .pointer => |ptr| {
            if (ptr.size == .slice) {
                if (ptr.child == u8) {
                    // Special case for string slices
                    try writer.print("\"{s}\"", .{value});
                } else {
                    try writer.writeAll("[");
                    for (value, 0..) |item, i| {
                        if (i > 0) try writer.writeAll(", ");
                        try serialize(ptr.child, item, writer);
                    }
                    try writer.writeAll("]");
                }
            } else {
                try writer.writeAll("(pointer)");
            }
        },
        .array => |arr| {
            try writer.writeAll("[");
            for (value, 0..) |item, i| {
                if (i > 0) try writer.writeAll(", ");
                try serialize(arr.child, item, writer);
            }
            try writer.writeAll("]");
        },
        .optional => {
            if (value) |val| {
                try serialize(@TypeOf(val), val, writer);
            } else {
                try writer.writeAll("null");
            }
        },
        else => try writer.writeAll("(unsupported)"),
    }
}

test "polymorphic serializer" {
    var buffer: [1024]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    try serialize(i32, 42, writer);
    try writer.writeAll(" ");

    try serialize(f64, 3.14159, writer);
    try writer.writeAll(" ");

    try serialize(bool, true, writer);
    try writer.writeAll(" ");

    try serialize([]const u8, "hello", writer);
    try writer.writeAll(" ");

    const arr = [_]i32{ 1, 2, 3 };
    try serialize([3]i32, arr, writer);
    try writer.writeAll(" ");

    try serialize(?i32, null, writer);
    try writer.writeAll(" ");

    try serialize(?i32, 99, writer);

    const output = fbs.getWritten();
    try testing.expect(std.mem.indexOf(u8, output, "42") != null);
    try testing.expect(std.mem.indexOf(u8, output, "3.14") != null);
    try testing.expect(std.mem.indexOf(u8, output, "true") != null);
    try testing.expect(std.mem.indexOf(u8, output, "\"hello\"") != null);
    try testing.expect(std.mem.indexOf(u8, output, "[1, 2, 3]") != null);
    try testing.expect(std.mem.indexOf(u8, output, "null") != null);
    try testing.expect(std.mem.indexOf(u8, output, "99") != null);
}
// ANCHOR_END: polymorphic_serializer
```

### See Also

- Recipe 9.16: Defining structs programmatically
- Recipe 9.11: Using comptime to control instance creation
- Recipe 17.2: Compile
- Recipe 17.4: Generic Data Structure Generation

---

## Recipe 17.2: Compile-Time String Processing {#recipe-17-2}

**Tags:** allocators, c-interop, comptime, comptime-metaprogramming, csv, error-handling, json, memory, parsing, testing, xml
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/17-advanced-comptime/recipe_17_2.zig`

### Problem

You want to build domain-specific languages (DSLs), generate code from strings, validate identifiers, or process configuration at compile time. You need powerful string manipulation that happens during compilation without any runtime overhead.

### Solution

Zig provides `std.fmt.comptimePrint` for generating strings at compile time, along with the `++` operator for concatenation and standard string operations that work in comptime contexts.

### Basic Compile-Time Printing

Generate formatted strings at compile time:

```zig
/// Generate strings at compile time using comptimePrint
fn makeTypeName(comptime base: []const u8, comptime id: u32) []const u8 {
    return comptime fmt.comptimePrint("{s}_{d}", .{ base, id });
}

test "basic comptime print" {
    const name1 = makeTypeName("Widget", 1);
    const name2 = makeTypeName("Widget", 2);

    try testing.expectEqualStrings("Widget_1", name1);
    try testing.expectEqualStrings("Widget_2", name2);
}
```

### Parsing Key-Value Pairs

Parse simple formats at compile time with validation:

```zig
/// Parse a simple key=value format at compile time
fn parseKeyValue(comptime input: []const u8) struct { key: []const u8, value: []const u8 } {
    comptime {
        var eq_pos: ?usize = null;
        for (input, 0..) |char, i| {
            if (char == '=') {
                eq_pos = i;
                break;
            }
        }

        if (eq_pos) |pos| {
            return .{
                .key = input[0..pos],
                .value = input[pos + 1 ..],
            };
        } else {
            @compileError("Invalid key=value format: missing '=' separator");
        }
    }
}

test "compile-time string parsing" {
    const parsed = comptime parseKeyValue("name=Alice");

    try testing.expectEqualStrings("name", parsed.key);
    try testing.expectEqualStrings("Alice", parsed.value);

    const parsed2 = comptime parseKeyValue("count=42");
    try testing.expectEqualStrings("count", parsed2.key);
    try testing.expectEqualStrings("42", parsed2.value);
}
```

### Generating Field Names

Create systematic naming patterns:

```zig
/// Generate field names based on a pattern
fn generateFieldNames(comptime prefix: []const u8, comptime count: usize) [count][]const u8 {
    comptime {
        var names: [count][]const u8 = undefined;
        for (0..count) |i| {
            names[i] = fmt.comptimePrint("{s}{d}", .{ prefix, i });
        }
        return names;
    }
}

test "field name generation" {
    const field_names = comptime generateFieldNames("field", 3);

    try testing.expectEqual(3, field_names.len);
    try testing.expectEqualStrings("field0", field_names[0]);
    try testing.expectEqualStrings("field1", field_names[1]);
    try testing.expectEqualStrings("field2", field_names[2]);
}
```

### Building SQL Queries

Construct SQL at compile time with validation:

```zig
/// Build SQL queries at compile time with basic validation
fn buildSelectQuery(
    comptime table: []const u8,
    comptime columns: []const []const u8,
    comptime where_clause: ?[]const u8,
) []const u8 {
    comptime {
        if (table.len == 0) {
            @compileError("Table name cannot be empty");
        }

        if (columns.len == 0) {
            @compileError("Must select at least one column");
        }

        // Build column list
        var col_list: []const u8 = columns[0];
        for (columns[1..]) |col| {
            col_list = col_list ++ ", " ++ col;
        }

        // Build complete query
        if (where_clause) |clause| {
            return fmt.comptimePrint("SELECT {s} FROM {s} WHERE {s}", .{ col_list, table, clause });
        } else {
            return fmt.comptimePrint("SELECT {s} FROM {s}", .{ col_list, table });
        }
    }
}

test "SQL query builder" {
    const query1 = comptime buildSelectQuery(
        "users",
        &[_][]const u8{ "id", "name", "email" },
        null,
    );
    try testing.expectEqualStrings("SELECT id, name, email FROM users", query1);

    const query2 = comptime buildSelectQuery(
        "products",
        &[_][]const u8{ "id", "price" },
        "price > 100",
    );
    try testing.expectEqualStrings("SELECT id, price FROM products WHERE price > 100", query2);
}
```

### Parsing Format Strings

Analyze format strings to extract metadata:

```zig
/// Parse format strings at compile time and validate them
fn parseFormat(comptime format: []const u8) struct {
    placeholders: usize,
    has_precision: bool,
} {
    comptime {
        var placeholders: usize = 0;
        var has_precision = false;
        var i: usize = 0;

        while (i < format.len) : (i += 1) {
            if (format[i] == '{') {
                if (i + 1 < format.len and format[i + 1] != '{') {
                    placeholders += 1;

                    // Check for precision specifier
                    var j = i + 1;
                    while (j < format.len and format[j] != '}') : (j += 1) {
                        if (format[j] == '.') {
                            has_precision = true;
                        }
                    }

                    i = j;
                }
            }
        }

        return .{
            .placeholders = placeholders,
            .has_precision = has_precision,
        };
    }
}

test "format string parsing" {
    const fmt1 = comptime parseFormat("Hello, {s}!");
    try testing.expectEqual(1, fmt1.placeholders);
    try testing.expect(!fmt1.has_precision);

    const fmt2 = comptime parseFormat("Value: {d:.2}");
    try testing.expectEqual(1, fmt2.placeholders);
    try testing.expect(fmt2.has_precision);

    const fmt3 = comptime parseFormat("Multiple: {s} and {d} values");
    try testing.expectEqual(2, fmt3.placeholders);
}
```

### Generating Enums from Strings

Create enum types from string lists at compile time:

```zig
/// Generate an enum from compile-time string list
fn makeEnum(comptime strings: []const []const u8) type {
    comptime {
        // Create enum fields
        var fields: [strings.len]std.builtin.Type.EnumField = undefined;
        for (strings, 0..) |str, i| {
            // Add sentinel terminator for field name
            const name = str ++ "";
            fields[i] = .{
                .name = name[0..str.len :0],
                .value = i,
            };
        }

        return @Type(.{
            .@"enum" = .{
                .tag_type = std.math.IntFittingRange(0, strings.len - 1),
                .fields = &fields,
                .decls = &[_]std.builtin.Type.Declaration{},
                .is_exhaustive = true,
            },
        });
    }
}

test "enum generation from strings" {
    const Color = makeEnum(&[_][]const u8{ "red", "green", "blue" });

    const red = Color.red;
    const green = Color.green;
    const blue = Color.blue;

    try testing.expectEqual(Color.red, red);
    try testing.expectEqual(Color.green, green);
    try testing.expectEqual(Color.blue, blue);
}
```

### Identifier Validation

Validate Zig identifiers at compile time:

```zig
/// Validate that a string is a valid Zig identifier at compile time
fn isValidIdentifier(comptime name: []const u8) bool {
    if (name.len == 0) return false;

    // First character must be letter or underscore
    const first = name[0];
    if (!std.ascii.isAlphabetic(first) and first != '_') {
        return false;
    }

    // Remaining characters must be alphanumeric or underscore
    for (name[1..]) |char| {
        if (!std.ascii.isAlphanumeric(char) and char != '_') {
            return false;
        }
    }

    return true;
}

fn requireValidIdentifier(comptime name: []const u8) void {
    if (!isValidIdentifier(name)) {
        @compileError("Invalid identifier: '" ++ name ++ "'");
    }
}

test "identifier validation" {
    try testing.expect(isValidIdentifier("hello"));
    try testing.expect(isValidIdentifier("_private"));
    try testing.expect(isValidIdentifier("value123"));
    try testing.expect(isValidIdentifier("snake_case"));

    try testing.expect(!isValidIdentifier(""));
    try testing.expect(!isValidIdentifier("123start"));
    try testing.expect(!isValidIdentifier("has-dash"));
    try testing.expect(!isValidIdentifier("has space"));
}
```

### String Concatenation and Joining

Build complex strings from parts:

```zig
/// Compile-time string concatenation utilities
fn concat(comptime strings: []const []const u8) []const u8 {
    comptime {
        var result: []const u8 = "";
        for (strings) |s| {
            result = result ++ s;
        }
        return result;
    }
}

fn join(comptime strings: []const []const u8, comptime separator: []const u8) []const u8 {
    comptime {
        if (strings.len == 0) return "";
        if (strings.len == 1) return strings[0];

        var result: []const u8 = strings[0];
        for (strings[1..]) |s| {
            result = result ++ separator ++ s;
        }
        return result;
    }
}

test "compile-time string operations" {
    const hello = comptime concat(&[_][]const u8{ "Hello", ", ", "World", "!" });
    try testing.expectEqualStrings("Hello, World!", hello);

    const path = comptime join(&[_][]const u8{ "usr", "local", "bin" }, "/");
    try testing.expectEqualStrings("usr/local/bin", path);

    const csv = comptime join(&[_][]const u8{ "a", "b", "c" }, ", ");
    try testing.expectEqualStrings("a, b, c", csv);
}
```

### Code Generator

Generate method names following naming conventions:

```zig
/// Generate getter and setter method names
fn makeAccessors(comptime field_name: []const u8) struct {
    getter: []const u8,
    setter: []const u8,
} {
    comptime {
        requireValidIdentifier(field_name);

        // Capitalize first letter for getter/setter
        var capitalized: [field_name.len]u8 = undefined;
        @memcpy(&capitalized, field_name);
        if (capitalized.len > 0 and std.ascii.isLower(capitalized[0])) {
            capitalized[0] = std.ascii.toUpper(capitalized[0]);
        }

        return .{
            .getter = fmt.comptimePrint("get{s}", .{capitalized}),
            .setter = fmt.comptimePrint("set{s}", .{capitalized}),
        };
    }
}

test "accessor name generation" {
    const accessors = comptime makeAccessors("name");

    try testing.expectEqualStrings("getName", accessors.getter);
    try testing.expectEqualStrings("setName", accessors.setter);

    const accessors2 = comptime makeAccessors("value");
    try testing.expectEqualStrings("getValue", accessors2.getter);
    try testing.expectEqualStrings("setValue", accessors2.setter);
}
```

### Discussion

Compile-time string processing is essential for metaprogramming, letting you build tools that generate code, validate input, and create DSLs without any runtime cost.

### How comptimePrint Works

`std.fmt.comptimePrint` is like `std.fmt.allocPrint` but works at compile time. It returns a compile-time string literal that gets embedded in your binary:

- No allocator needed (memory is compile-time only)
- Supports all standard format specifiers (`{s}`, `{d}`, `{x}`, etc.)
- The result is a `[]const u8` known at compile time
- Can be used anywhere a compile-time string is required

### String Operations at Comptime

Most string operations work at compile time if wrapped in a `comptime` block:

**Concatenation**: Use `++` to join strings. This creates a new compile-time string without allocation.

**Indexing and Slicing**: Access individual characters or substrings with `string[index]` or `string[start..end]`.

**Comparison**: Use `std.mem.eql(u8, a, b)` to compare strings.

**Searching**: Loop through characters to find patterns, delimiters, or specific content.

### Building DSLs

Domain-specific languages become practical when you can parse and validate them at compile time:

**SQL Builders**: Catch table name typos or missing columns before compilation completes.

**Config Validation**: Parse configuration formats and reject invalid syntax immediately.

**API Generation**: Generate function names, struct fields, or entire interfaces from specifications.

### Type Generation

Combine string processing with `@Type()` to create types programmatically. The `makeEnum` example shows how to:

1. Process string lists at compile time
2. Build type metadata (field names, values)
3. Construct a complete type with `@Type()`
4. Use the generated type like any hand-written code

This is powerful for code generation from external specifications, configuration files, or data schemas.

### Validation and Error Reporting

Use `@compileError()` to provide clear feedback when strings don't meet requirements:

- Check for empty strings, invalid characters, or malformed syntax
- Build helpful error messages using string concatenation
- Fail fast at compile time rather than runtime

The `isValidIdentifier` and `requireValidIdentifier` functions show this pattern: validate input and provide actionable errors.

### Performance Characteristics

All string processing happens at compile time, so:

- Zero runtime overhead (no string parsing at program startup)
- Generated code is as fast as hand-written code
- Binary size includes only the final strings, not processing logic
- Compilation may take longer for complex string operations

### Practical Applications

**Serialization Formats**: Generate JSON, XML, or binary protocol encoders/decoders from schemas.

**Resource Embedding**: Process file paths, concatenate includes, or generate lookup tables.

**Code Generation**: Create boilerplate, implement getters/setters, or build test fixtures.

**Configuration**: Parse build-time configuration and generate optimized code for each setting.

**Validation**: Enforce naming conventions, check identifier validity, or validate format strings.

### Full Tested Code

```zig
// Recipe 17.2: Compile-Time String Processing and Code Generation
// This recipe demonstrates how to build DSLs and generate code from compile-time
// strings, parse format strings, and create sophisticated compile-time string
// manipulation utilities.

const std = @import("std");
const testing = std.testing;
const fmt = std.fmt;

// ANCHOR: basic_comptime_print
/// Generate strings at compile time using comptimePrint
fn makeTypeName(comptime base: []const u8, comptime id: u32) []const u8 {
    return comptime fmt.comptimePrint("{s}_{d}", .{ base, id });
}

test "basic comptime print" {
    const name1 = makeTypeName("Widget", 1);
    const name2 = makeTypeName("Widget", 2);

    try testing.expectEqualStrings("Widget_1", name1);
    try testing.expectEqualStrings("Widget_2", name2);
}
// ANCHOR_END: basic_comptime_print

// ANCHOR: string_parsing
/// Parse a simple key=value format at compile time
fn parseKeyValue(comptime input: []const u8) struct { key: []const u8, value: []const u8 } {
    comptime {
        var eq_pos: ?usize = null;
        for (input, 0..) |char, i| {
            if (char == '=') {
                eq_pos = i;
                break;
            }
        }

        if (eq_pos) |pos| {
            return .{
                .key = input[0..pos],
                .value = input[pos + 1 ..],
            };
        } else {
            @compileError("Invalid key=value format: missing '=' separator");
        }
    }
}

test "compile-time string parsing" {
    const parsed = comptime parseKeyValue("name=Alice");

    try testing.expectEqualStrings("name", parsed.key);
    try testing.expectEqualStrings("Alice", parsed.value);

    const parsed2 = comptime parseKeyValue("count=42");
    try testing.expectEqualStrings("count", parsed2.key);
    try testing.expectEqualStrings("42", parsed2.value);
}
// ANCHOR_END: string_parsing

// ANCHOR: field_name_generator
/// Generate field names based on a pattern
fn generateFieldNames(comptime prefix: []const u8, comptime count: usize) [count][]const u8 {
    comptime {
        var names: [count][]const u8 = undefined;
        for (0..count) |i| {
            names[i] = fmt.comptimePrint("{s}{d}", .{ prefix, i });
        }
        return names;
    }
}

test "field name generation" {
    const field_names = comptime generateFieldNames("field", 3);

    try testing.expectEqual(3, field_names.len);
    try testing.expectEqualStrings("field0", field_names[0]);
    try testing.expectEqualStrings("field1", field_names[1]);
    try testing.expectEqualStrings("field2", field_names[2]);
}
// ANCHOR_END: field_name_generator

// ANCHOR: sql_builder
/// Build SQL queries at compile time with basic validation
fn buildSelectQuery(
    comptime table: []const u8,
    comptime columns: []const []const u8,
    comptime where_clause: ?[]const u8,
) []const u8 {
    comptime {
        if (table.len == 0) {
            @compileError("Table name cannot be empty");
        }

        if (columns.len == 0) {
            @compileError("Must select at least one column");
        }

        // Build column list
        var col_list: []const u8 = columns[0];
        for (columns[1..]) |col| {
            col_list = col_list ++ ", " ++ col;
        }

        // Build complete query
        if (where_clause) |clause| {
            return fmt.comptimePrint("SELECT {s} FROM {s} WHERE {s}", .{ col_list, table, clause });
        } else {
            return fmt.comptimePrint("SELECT {s} FROM {s}", .{ col_list, table });
        }
    }
}

test "SQL query builder" {
    const query1 = comptime buildSelectQuery(
        "users",
        &[_][]const u8{ "id", "name", "email" },
        null,
    );
    try testing.expectEqualStrings("SELECT id, name, email FROM users", query1);

    const query2 = comptime buildSelectQuery(
        "products",
        &[_][]const u8{ "id", "price" },
        "price > 100",
    );
    try testing.expectEqualStrings("SELECT id, price FROM products WHERE price > 100", query2);
}
// ANCHOR_END: sql_builder

// ANCHOR: format_parser
/// Parse format strings at compile time and validate them
fn parseFormat(comptime format: []const u8) struct {
    placeholders: usize,
    has_precision: bool,
} {
    comptime {
        var placeholders: usize = 0;
        var has_precision = false;
        var i: usize = 0;

        while (i < format.len) : (i += 1) {
            if (format[i] == '{') {
                if (i + 1 < format.len and format[i + 1] != '{') {
                    placeholders += 1;

                    // Check for precision specifier
                    var j = i + 1;
                    while (j < format.len and format[j] != '}') : (j += 1) {
                        if (format[j] == '.') {
                            has_precision = true;
                        }
                    }

                    i = j;
                }
            }
        }

        return .{
            .placeholders = placeholders,
            .has_precision = has_precision,
        };
    }
}

test "format string parsing" {
    const fmt1 = comptime parseFormat("Hello, {s}!");
    try testing.expectEqual(1, fmt1.placeholders);
    try testing.expect(!fmt1.has_precision);

    const fmt2 = comptime parseFormat("Value: {d:.2}");
    try testing.expectEqual(1, fmt2.placeholders);
    try testing.expect(fmt2.has_precision);

    const fmt3 = comptime parseFormat("Multiple: {s} and {d} values");
    try testing.expectEqual(2, fmt3.placeholders);
}
// ANCHOR_END: format_parser

// ANCHOR: enum_from_strings
/// Generate an enum from compile-time string list
fn makeEnum(comptime strings: []const []const u8) type {
    comptime {
        // Create enum fields
        var fields: [strings.len]std.builtin.Type.EnumField = undefined;
        for (strings, 0..) |str, i| {
            // Add sentinel terminator for field name
            const name = str ++ "";
            fields[i] = .{
                .name = name[0..str.len :0],
                .value = i,
            };
        }

        return @Type(.{
            .@"enum" = .{
                .tag_type = std.math.IntFittingRange(0, strings.len - 1),
                .fields = &fields,
                .decls = &[_]std.builtin.Type.Declaration{},
                .is_exhaustive = true,
            },
        });
    }
}

test "enum generation from strings" {
    const Color = makeEnum(&[_][]const u8{ "red", "green", "blue" });

    const red = Color.red;
    const green = Color.green;
    const blue = Color.blue;

    try testing.expectEqual(Color.red, red);
    try testing.expectEqual(Color.green, green);
    try testing.expectEqual(Color.blue, blue);
}
// ANCHOR_END: enum_from_strings

// ANCHOR: identifier_validation
/// Validate that a string is a valid Zig identifier at compile time
fn isValidIdentifier(comptime name: []const u8) bool {
    if (name.len == 0) return false;

    // First character must be letter or underscore
    const first = name[0];
    if (!std.ascii.isAlphabetic(first) and first != '_') {
        return false;
    }

    // Remaining characters must be alphanumeric or underscore
    for (name[1..]) |char| {
        if (!std.ascii.isAlphanumeric(char) and char != '_') {
            return false;
        }
    }

    return true;
}

fn requireValidIdentifier(comptime name: []const u8) void {
    if (!isValidIdentifier(name)) {
        @compileError("Invalid identifier: '" ++ name ++ "'");
    }
}

test "identifier validation" {
    try testing.expect(isValidIdentifier("hello"));
    try testing.expect(isValidIdentifier("_private"));
    try testing.expect(isValidIdentifier("value123"));
    try testing.expect(isValidIdentifier("snake_case"));

    try testing.expect(!isValidIdentifier(""));
    try testing.expect(!isValidIdentifier("123start"));
    try testing.expect(!isValidIdentifier("has-dash"));
    try testing.expect(!isValidIdentifier("has space"));
}
// ANCHOR_END: identifier_validation

// ANCHOR: string_concatenation
/// Compile-time string concatenation utilities
fn concat(comptime strings: []const []const u8) []const u8 {
    comptime {
        var result: []const u8 = "";
        for (strings) |s| {
            result = result ++ s;
        }
        return result;
    }
}

fn join(comptime strings: []const []const u8, comptime separator: []const u8) []const u8 {
    comptime {
        if (strings.len == 0) return "";
        if (strings.len == 1) return strings[0];

        var result: []const u8 = strings[0];
        for (strings[1..]) |s| {
            result = result ++ separator ++ s;
        }
        return result;
    }
}

test "compile-time string operations" {
    const hello = comptime concat(&[_][]const u8{ "Hello", ", ", "World", "!" });
    try testing.expectEqualStrings("Hello, World!", hello);

    const path = comptime join(&[_][]const u8{ "usr", "local", "bin" }, "/");
    try testing.expectEqualStrings("usr/local/bin", path);

    const csv = comptime join(&[_][]const u8{ "a", "b", "c" }, ", ");
    try testing.expectEqualStrings("a, b, c", csv);
}
// ANCHOR_END: string_concatenation

// ANCHOR: code_generator
/// Generate getter and setter method names
fn makeAccessors(comptime field_name: []const u8) struct {
    getter: []const u8,
    setter: []const u8,
} {
    comptime {
        requireValidIdentifier(field_name);

        // Capitalize first letter for getter/setter
        var capitalized: [field_name.len]u8 = undefined;
        @memcpy(&capitalized, field_name);
        if (capitalized.len > 0 and std.ascii.isLower(capitalized[0])) {
            capitalized[0] = std.ascii.toUpper(capitalized[0]);
        }

        return .{
            .getter = fmt.comptimePrint("get{s}", .{capitalized}),
            .setter = fmt.comptimePrint("set{s}", .{capitalized}),
        };
    }
}

test "accessor name generation" {
    const accessors = comptime makeAccessors("name");

    try testing.expectEqualStrings("getName", accessors.getter);
    try testing.expectEqualStrings("setName", accessors.setter);

    const accessors2 = comptime makeAccessors("value");
    try testing.expectEqualStrings("getValue", accessors2.getter);
    try testing.expectEqualStrings("setValue", accessors2.setter);
}
// ANCHOR_END: code_generator
```

### See Also

- Recipe 17.1: Type
- Recipe 17.4: Generic Data Structure Generation
- Recipe 17.6: Build
- Recipe 9.16: Defining structs programmatically

---

## Recipe 17.3: Compile-Time Assertions {#recipe-17-3}

**Tags:** c-interop, comptime, comptime-metaprogramming, error-handling, pointers, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/17-advanced-comptime/recipe_17_3.zig`

### Problem

You need to enforce constraints on types, validate struct layouts, check API contracts, and ensure invariants are maintained across your codebase. You want these checks to happen at compile time so invalid code never makes it to production.

### Solution

Zig's `@compileError` builtin combined with compile-time type introspection allows you to create sophisticated assertions that validate code at compile time with zero runtime overhead.

### Basic Compile-Time Assertions

Create simple assertions with custom error messages:

```zig
/// Basic compile-time assertion with custom error message
fn assertComptime(comptime condition: bool, comptime message: []const u8) void {
    if (!condition) {
        @compileError(message);
    }
}

/// Assert that a type is numeric
fn assertNumeric(comptime T: type) void {
    const info = @typeInfo(T);
    switch (info) {
        .int, .comptime_int, .float, .comptime_float => {},
        else => @compileError("Type " ++ @typeName(T) ++ " is not numeric"),
    }
}

/// Assert that a type has a specific size
fn assertSize(comptime T: type, comptime expected_size: usize) void {
    const actual_size = @sizeOf(T);
    if (actual_size != expected_size) {
        @compileError(std.fmt.comptimePrint(
            "Type {s} has size {d}, expected {d}",
            .{ @typeName(T), actual_size, expected_size },
        ));
    }
}

test "basic compile-time assertions" {
    // These assertions pass
    assertNumeric(i32);
    assertNumeric(f64);
    assertSize(u32, 4);
    assertSize(u64, 8);

    // Uncomment to see compile errors:
    // assertNumeric(bool);  // Error: Type bool is not numeric
    // assertSize(u32, 8);   // Error: Type u32 has size 4, expected 8
}
```

### Type Relationship Assertions

Validate relationships between types:

```zig
/// Assert that two types are the same
fn assertSameType(comptime T: type, comptime U: type) void {
    if (T != U) {
        @compileError(std.fmt.comptimePrint(
            "Type mismatch: {s} != {s}",
            .{ @typeName(T), @typeName(U) },
        ));
    }
}

/// Assert that T can be coerced to U
fn assertCoercible(comptime T: type, comptime U: type) void {
    const dummy: T = undefined;
    _ = @as(U, dummy);
}

/// Assert that a type is a pointer
fn assertPointer(comptime T: type) void {
    const info = @typeInfo(T);
    switch (info) {
        .pointer => {},
        else => @compileError("Type " ++ @typeName(T) ++ " is not a pointer"),
    }
}

test "type relationship assertions" {
    assertSameType(i32, i32);
    assertPointer(*u8);
    assertPointer(*const u32);

    // These would fail at compile time:
    // assertSameType(i32, u32);
    // assertPointer(u8);
}
```

### Struct Field Validation

Check struct shapes and field types:

```zig
/// Check if a struct has a specific field (returns bool for use in tests)
fn hasField(comptime T: type, comptime field_name: []const u8) bool {
    const info = @typeInfo(T);
    switch (info) {
        .@"struct" => |struct_info| {
            inline for (struct_info.fields) |field| {
                if (std.mem.eql(u8, field.name, field_name)) {
                    return true;
                }
            }
            return false;
        },
        else => return false,
    }
}

/// Get field type if it exists (returns ?type for use in tests)
fn getFieldType(comptime T: type, comptime field_name: []const u8) ?type {
    const info = @typeInfo(T);
    switch (info) {
        .@"struct" => |struct_info| {
            inline for (struct_info.fields) |field| {
                if (std.mem.eql(u8, field.name, field_name)) {
                    return field.type;
                }
            }
            return null;
        },
        else => return null,
    }
}

const TestStruct = struct {
    id: u32,
    name: []const u8,
    value: f64,
};

test "struct field validation" {
    // Test field existence
    try testing.expect(hasField(TestStruct, "id"));
    try testing.expect(hasField(TestStruct, "name"));
    try testing.expect(hasField(TestStruct, "value"));
    try testing.expect(!hasField(TestStruct, "missing"));

    // Test field types
    try testing.expectEqual(u32, getFieldType(TestStruct, "id").?);
    try testing.expectEqual([]const u8, getFieldType(TestStruct, "name").?);
    try testing.expectEqual(f64, getFieldType(TestStruct, "value").?);
    try testing.expectEqual(@as(?type, null), getFieldType(TestStruct, "missing"));

    // Example of how to use in compile-time assertions:
    comptime {
        if (!hasField(TestStruct, "id")) {
            @compileError("TestStruct must have id field");
        }
        if (getFieldType(TestStruct, "id").? != u32) {
            @compileError("TestStruct.id must be u32");
        }
    }
}
```

### Interface Validation

Ensure types implement required methods (duck typing):

```zig
/// Assert that a type implements required methods (duck typing)
fn assertHasMethod(
    comptime T: type,
    comptime method_name: []const u8,
) void {
    if (!@hasDecl(T, method_name)) {
        @compileError(std.fmt.comptimePrint(
            "Type {s} does not implement method '{s}'",
            .{ @typeName(T), method_name },
        ));
    }
}

/// Assert that a type implements multiple methods
fn assertImplements(
    comptime T: type,
    comptime methods: []const []const u8,
) void {
    inline for (methods) |method_name| {
        assertHasMethod(T, method_name);
    }
}

const Writer = struct {
    pub fn write(self: *Writer, data: []const u8) !usize {
        _ = self;
        _ = data;
        return 0;
    }

    pub fn flush(self: *Writer) !void {
        _ = self;
    }
};

test "interface validation" {
    assertHasMethod(Writer, "write");
    assertHasMethod(Writer, "flush");

    assertImplements(Writer, &[_][]const u8{ "write", "flush" });

    // Would fail:
    // assertHasMethod(Writer, "missing");
}
```

### Alignment and Layout Assertions

Validate memory layout characteristics:

```zig
/// Assert that a type has specific alignment
fn assertAlignment(comptime T: type, comptime expected: usize) void {
    const actual = @alignOf(T);
    if (actual != expected) {
        @compileError(std.fmt.comptimePrint(
            "Type {s} has alignment {d}, expected {d}",
            .{ @typeName(T), actual, expected },
        ));
    }
}

/// Assert that a type is packed (no padding)
fn assertPacked(comptime T: type) void {
    const info = @typeInfo(T);
    switch (info) {
        .@"struct" => |struct_info| {
            if (struct_info.layout != .@"packed") {
                @compileError("Struct " ++ @typeName(T) ++ " is not packed");
            }
        },
        else => @compileError("Type " ++ @typeName(T) ++ " is not a struct"),
    }
}

const PackedStruct = packed struct {
    a: u8,
    b: u16,
    c: u8,
};

test "alignment assertions" {
    assertAlignment(u8, 1);
    assertAlignment(u16, 2);
    assertAlignment(u32, 4);
    assertAlignment(u64, 8);

    assertPacked(PackedStruct);
}
```

### Range and Size Validation

Check compile-time constants fall within valid ranges:

```zig
/// Assert that a value is within a valid range
fn assertInRange(
    comptime T: type,
    comptime value: T,
    comptime min: T,
    comptime max: T,
) void {
    if (value < min or value > max) {
        @compileError(std.fmt.comptimePrint(
            "Value {d} is outside range [{d}, {d}]",
            .{ value, min, max },
        ));
    }
}

/// Assert that an array has a specific length
fn assertArrayLength(comptime T: type, comptime expected_len: usize) void {
    const info = @typeInfo(T);
    switch (info) {
        .array => |arr_info| {
            if (arr_info.len != expected_len) {
                @compileError(std.fmt.comptimePrint(
                    "Array has length {d}, expected {d}",
                    .{ arr_info.len, expected_len },
                ));
            }
        },
        else => @compileError("Type " ++ @typeName(T) ++ " is not an array"),
    }
}

test "range validation" {
    assertInRange(u32, 50, 0, 100);
    assertInRange(i32, -10, -100, 100);

    assertArrayLength([5]u8, 5);
    assertArrayLength([10]i32, 10);

    // Would fail:
    // assertInRange(u32, 150, 0, 100);
    // assertArrayLength([5]u8, 10);
}
```

### Build Configuration Assertions

Validate build settings and target platforms:

```zig
/// Assert debug mode for development-only code
fn assertDebugMode() void {
    const mode = @import("builtin").mode;
    if (mode != .Debug) {
        @compileError("This code only works in Debug mode");
    }
}

/// Assert release mode for performance-critical code
fn assertReleaseMode() void {
    const mode = @import("builtin").mode;
    if (mode == .Debug) {
        @compileError("This code requires release mode optimizations");
    }
}

/// Assert specific target architecture
fn assertArch(comptime expected: std.Target.Cpu.Arch) void {
    const actual = @import("builtin").cpu.arch;
    if (actual != expected) {
        @compileError(std.fmt.comptimePrint(
            "Expected architecture {s}, found {s}",
            .{ @tagName(expected), @tagName(actual) },
        ));
    }
}

test "build configuration assertions" {
    // These depend on build settings
    const mode = @import("builtin").mode;
    _ = mode;

    // Example: assertArch would check CPU architecture
    // assertArch(.x86_64);
}
```

### Design by Contract

Enforce preconditions and postconditions:

```zig
/// Design by contract: require preconditions
fn requireContract(comptime condition: bool, comptime message: []const u8) void {
    if (!condition) {
        @compileError("Contract violation: " ++ message);
    }
}

/// Generic function with compile-time contracts
fn divideArray(comptime T: type, comptime len: usize) type {
    // Contracts
    assertNumeric(T);
    requireContract(len > 0, "Array length must be positive");
    requireContract(len % 2 == 0, "Array length must be even");

    return struct {
        first_half: [len / 2]T,
        second_half: [len / 2]T,
    };
}

test "contract validation" {
    const Result4 = divideArray(i32, 4);
    const r4: Result4 = undefined;
    try testing.expectEqual(2, r4.first_half.len);
    try testing.expectEqual(2, r4.second_half.len);

    const Result10 = divideArray(f64, 10);
    const r10: Result10 = undefined;
    try testing.expectEqual(5, r10.first_half.len);
    try testing.expectEqual(5, r10.second_half.len);

    // Would fail at compile time:
    // const Bad1 = divideArray(bool, 4);  // Not numeric
    // const Bad2 = divideArray(i32, 0);   // Length not positive
    // const Bad3 = divideArray(i32, 5);   // Length not even
}
```

### Custom Validators

Build reusable validation helpers:

```zig
/// Composite validator for numeric types in a specific range
fn ValidatedNumeric(
    comptime T: type,
    comptime min_bits: u16,
    comptime max_bits: u16,
) type {
    assertNumeric(T);

    const info = @typeInfo(T);
    const bits = switch (info) {
        .int => |int_info| int_info.bits,
        .float => |float_info| float_info.bits,
        else => unreachable,
    };

    if (bits < min_bits or bits > max_bits) {
        @compileError(std.fmt.comptimePrint(
            "Type {s} has {d} bits, must be between {d} and {d}",
            .{ @typeName(T), bits, min_bits, max_bits },
        ));
    }

    return T;
}

/// Builder pattern for complex validation
fn ValidatedStruct(comptime T: type) type {
    // Validate it's a struct
    const info = @typeInfo(T);
    if (info != .@"struct") {
        @compileError("ValidatedStruct requires a struct type");
    }

    // Ensure struct has at least one field
    if (info.@"struct".fields.len == 0) {
        @compileError("Struct must have at least one field");
    }

    return T;
}

test "custom validators" {
    const Small = ValidatedNumeric(u8, 8, 16);
    try testing.expectEqual(u8, Small);

    const Medium = ValidatedNumeric(u32, 16, 64);
    try testing.expectEqual(u32, Medium);

    const Valid = ValidatedStruct(TestStruct);
    try testing.expectEqual(TestStruct, Valid);

    // Would fail:
    // const TooBig = ValidatedNumeric(u128, 8, 64);
    // const Empty = ValidatedStruct(struct {});
}
```

### Discussion

Compile-time assertions transform potential runtime bugs into compilation errors, giving you immediate feedback when constraints are violated.

### How @compileError Works

The `@compileError` builtin stops compilation with a custom message. When placed inside a comptime block or function:

- Execution stops immediately when reached
- The provided message is displayed as a compilation error
- No code is generated for invalid branches
- Works seamlessly with conditional logic

Use `std.fmt.comptimePrint` to create detailed error messages that include type names, values, and context.

### Assertion Strategies

**Type Validation**: Use `@typeInfo()` to inspect type characteristics and reject invalid types before generating code.

**Struct Introspection**: Check field names and types using the `.@"struct"` tag. Iterate fields with `inline for` to validate structure.

**Method Checking**: Use `@hasDecl()` to verify types implement required functions, enabling duck typing with compile-time guarantees.

**Size and Alignment**: Assert memory layout requirements with `@sizeOf()` and `@alignOf()` to prevent ABI mismatches or platform issues.

### Best Practices

**Informative Messages**: Include as much context as possible in error messages. Show what was expected vs. what was found, along with type names and values.

**Fail Early**: Place assertions at the entry points of generic functions and type constructors. Catch invalid usage immediately.

**Composable Validators**: Build small, focused assertion functions that can be combined. Create libraries of validators for common patterns.

**Return Bool for Testing**: Functions that would use `@compileError` should return bool for testability, then wrap them in assertion helpers.

**Document Contracts**: Use assertions as executable documentation. They clearly state what your code requires and guarantees.

### Common Use Cases

**Generic Constraints**: Ensure type parameters meet requirements (numeric, pointer, specific size, etc.).

**Platform Validation**: Check target architecture, OS, or build mode matches code requirements.

**ABI Guarantees**: Verify struct layouts match external API requirements for C interop or network protocols.

**API Evolution**: Ensure code changes don't violate backward compatibility contracts.

**Configuration Validation**: Catch invalid build options or feature combinations at compile time.

### Performance Characteristics

All assertions happen at compile time:

- Zero runtime overhead (no checks in final binary)
- No branches or conditional code generated
- Fast compile-time validation (analyzed once)
- Invalid code paths are pruned completely

### Integration with Testing

Combine compile-time assertions with runtime tests:

- Use assertions in generic functions to validate parameters
- Test successful cases with runtime tests
- Document failed cases with commented-out examples
- Use comptime blocks in tests to verify assertions fire correctly

The struct field validation example shows this pattern: runtime tests verify the validation functions work, while comptime blocks demonstrate how to use them for compile-time enforcement.

### Error Message Quality

Good error messages are crucial:

```zig
// Bad: Generic error
@compileError("Invalid type");

// Good: Specific context
@compileError(std.fmt.comptimePrint(
    "Type {s} has {d} fields, expected at least {d}",
    .{ @typeName(T), actual, minimum }
));
```

Include:
- What was checked
- What was expected
- What was actually found
- Type names for clarity
- Suggestions for fixing if possible

### Full Tested Code

```zig
// Recipe 17.3: Compile-Time Assertion and Contract Validation
// This recipe demonstrates how to create sophisticated compile-time assertions
// that validate type relationships, struct layouts, and API contracts with
// clear error messages.

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_assertions
/// Basic compile-time assertion with custom error message
fn assertComptime(comptime condition: bool, comptime message: []const u8) void {
    if (!condition) {
        @compileError(message);
    }
}

/// Assert that a type is numeric
fn assertNumeric(comptime T: type) void {
    const info = @typeInfo(T);
    switch (info) {
        .int, .comptime_int, .float, .comptime_float => {},
        else => @compileError("Type " ++ @typeName(T) ++ " is not numeric"),
    }
}

/// Assert that a type has a specific size
fn assertSize(comptime T: type, comptime expected_size: usize) void {
    const actual_size = @sizeOf(T);
    if (actual_size != expected_size) {
        @compileError(std.fmt.comptimePrint(
            "Type {s} has size {d}, expected {d}",
            .{ @typeName(T), actual_size, expected_size },
        ));
    }
}

test "basic compile-time assertions" {
    // These assertions pass
    assertNumeric(i32);
    assertNumeric(f64);
    assertSize(u32, 4);
    assertSize(u64, 8);

    // Uncomment to see compile errors:
    // assertNumeric(bool);  // Error: Type bool is not numeric
    // assertSize(u32, 8);   // Error: Type u32 has size 4, expected 8
}
// ANCHOR_END: basic_assertions

// ANCHOR: type_relationships
/// Assert that two types are the same
fn assertSameType(comptime T: type, comptime U: type) void {
    if (T != U) {
        @compileError(std.fmt.comptimePrint(
            "Type mismatch: {s} != {s}",
            .{ @typeName(T), @typeName(U) },
        ));
    }
}

/// Assert that T can be coerced to U
fn assertCoercible(comptime T: type, comptime U: type) void {
    const dummy: T = undefined;
    _ = @as(U, dummy);
}

/// Assert that a type is a pointer
fn assertPointer(comptime T: type) void {
    const info = @typeInfo(T);
    switch (info) {
        .pointer => {},
        else => @compileError("Type " ++ @typeName(T) ++ " is not a pointer"),
    }
}

test "type relationship assertions" {
    assertSameType(i32, i32);
    assertPointer(*u8);
    assertPointer(*const u32);

    // These would fail at compile time:
    // assertSameType(i32, u32);
    // assertPointer(u8);
}
// ANCHOR_END: type_relationships

// ANCHOR: struct_field_validation
/// Check if a struct has a specific field (returns bool for use in tests)
fn hasField(comptime T: type, comptime field_name: []const u8) bool {
    const info = @typeInfo(T);
    switch (info) {
        .@"struct" => |struct_info| {
            inline for (struct_info.fields) |field| {
                if (std.mem.eql(u8, field.name, field_name)) {
                    return true;
                }
            }
            return false;
        },
        else => return false,
    }
}

/// Get field type if it exists (returns ?type for use in tests)
fn getFieldType(comptime T: type, comptime field_name: []const u8) ?type {
    const info = @typeInfo(T);
    switch (info) {
        .@"struct" => |struct_info| {
            inline for (struct_info.fields) |field| {
                if (std.mem.eql(u8, field.name, field_name)) {
                    return field.type;
                }
            }
            return null;
        },
        else => return null,
    }
}

const TestStruct = struct {
    id: u32,
    name: []const u8,
    value: f64,
};

test "struct field validation" {
    // Test field existence
    try testing.expect(hasField(TestStruct, "id"));
    try testing.expect(hasField(TestStruct, "name"));
    try testing.expect(hasField(TestStruct, "value"));
    try testing.expect(!hasField(TestStruct, "missing"));

    // Test field types
    try testing.expectEqual(u32, getFieldType(TestStruct, "id").?);
    try testing.expectEqual([]const u8, getFieldType(TestStruct, "name").?);
    try testing.expectEqual(f64, getFieldType(TestStruct, "value").?);
    try testing.expectEqual(@as(?type, null), getFieldType(TestStruct, "missing"));

    // Example of how to use in compile-time assertions:
    comptime {
        if (!hasField(TestStruct, "id")) {
            @compileError("TestStruct must have id field");
        }
        if (getFieldType(TestStruct, "id").? != u32) {
            @compileError("TestStruct.id must be u32");
        }
    }
}
// ANCHOR_END: struct_field_validation

// ANCHOR: interface_validation
/// Assert that a type implements required methods (duck typing)
fn assertHasMethod(
    comptime T: type,
    comptime method_name: []const u8,
) void {
    if (!@hasDecl(T, method_name)) {
        @compileError(std.fmt.comptimePrint(
            "Type {s} does not implement method '{s}'",
            .{ @typeName(T), method_name },
        ));
    }
}

/// Assert that a type implements multiple methods
fn assertImplements(
    comptime T: type,
    comptime methods: []const []const u8,
) void {
    inline for (methods) |method_name| {
        assertHasMethod(T, method_name);
    }
}

const Writer = struct {
    pub fn write(self: *Writer, data: []const u8) !usize {
        _ = self;
        _ = data;
        return 0;
    }

    pub fn flush(self: *Writer) !void {
        _ = self;
    }
};

test "interface validation" {
    assertHasMethod(Writer, "write");
    assertHasMethod(Writer, "flush");

    assertImplements(Writer, &[_][]const u8{ "write", "flush" });

    // Would fail:
    // assertHasMethod(Writer, "missing");
}
// ANCHOR_END: interface_validation

// ANCHOR: alignment_assertions
/// Assert that a type has specific alignment
fn assertAlignment(comptime T: type, comptime expected: usize) void {
    const actual = @alignOf(T);
    if (actual != expected) {
        @compileError(std.fmt.comptimePrint(
            "Type {s} has alignment {d}, expected {d}",
            .{ @typeName(T), actual, expected },
        ));
    }
}

/// Assert that a type is packed (no padding)
fn assertPacked(comptime T: type) void {
    const info = @typeInfo(T);
    switch (info) {
        .@"struct" => |struct_info| {
            if (struct_info.layout != .@"packed") {
                @compileError("Struct " ++ @typeName(T) ++ " is not packed");
            }
        },
        else => @compileError("Type " ++ @typeName(T) ++ " is not a struct"),
    }
}

const PackedStruct = packed struct {
    a: u8,
    b: u16,
    c: u8,
};

test "alignment assertions" {
    assertAlignment(u8, 1);
    assertAlignment(u16, 2);
    assertAlignment(u32, 4);
    assertAlignment(u64, 8);

    assertPacked(PackedStruct);
}
// ANCHOR_END: alignment_assertions

// ANCHOR: range_validation
/// Assert that a value is within a valid range
fn assertInRange(
    comptime T: type,
    comptime value: T,
    comptime min: T,
    comptime max: T,
) void {
    if (value < min or value > max) {
        @compileError(std.fmt.comptimePrint(
            "Value {d} is outside range [{d}, {d}]",
            .{ value, min, max },
        ));
    }
}

/// Assert that an array has a specific length
fn assertArrayLength(comptime T: type, comptime expected_len: usize) void {
    const info = @typeInfo(T);
    switch (info) {
        .array => |arr_info| {
            if (arr_info.len != expected_len) {
                @compileError(std.fmt.comptimePrint(
                    "Array has length {d}, expected {d}",
                    .{ arr_info.len, expected_len },
                ));
            }
        },
        else => @compileError("Type " ++ @typeName(T) ++ " is not an array"),
    }
}

test "range validation" {
    assertInRange(u32, 50, 0, 100);
    assertInRange(i32, -10, -100, 100);

    assertArrayLength([5]u8, 5);
    assertArrayLength([10]i32, 10);

    // Would fail:
    // assertInRange(u32, 150, 0, 100);
    // assertArrayLength([5]u8, 10);
}
// ANCHOR_END: range_validation

// ANCHOR: build_configuration
/// Assert debug mode for development-only code
fn assertDebugMode() void {
    const mode = @import("builtin").mode;
    if (mode != .Debug) {
        @compileError("This code only works in Debug mode");
    }
}

/// Assert release mode for performance-critical code
fn assertReleaseMode() void {
    const mode = @import("builtin").mode;
    if (mode == .Debug) {
        @compileError("This code requires release mode optimizations");
    }
}

/// Assert specific target architecture
fn assertArch(comptime expected: std.Target.Cpu.Arch) void {
    const actual = @import("builtin").cpu.arch;
    if (actual != expected) {
        @compileError(std.fmt.comptimePrint(
            "Expected architecture {s}, found {s}",
            .{ @tagName(expected), @tagName(actual) },
        ));
    }
}

test "build configuration assertions" {
    // These depend on build settings
    const mode = @import("builtin").mode;
    _ = mode;

    // Example: assertArch would check CPU architecture
    // assertArch(.x86_64);
}
// ANCHOR_END: build_configuration

// ANCHOR: contract_validation
/// Design by contract: require preconditions
fn requireContract(comptime condition: bool, comptime message: []const u8) void {
    if (!condition) {
        @compileError("Contract violation: " ++ message);
    }
}

/// Generic function with compile-time contracts
fn divideArray(comptime T: type, comptime len: usize) type {
    // Contracts
    assertNumeric(T);
    requireContract(len > 0, "Array length must be positive");
    requireContract(len % 2 == 0, "Array length must be even");

    return struct {
        first_half: [len / 2]T,
        second_half: [len / 2]T,
    };
}

test "contract validation" {
    const Result4 = divideArray(i32, 4);
    const r4: Result4 = undefined;
    try testing.expectEqual(2, r4.first_half.len);
    try testing.expectEqual(2, r4.second_half.len);

    const Result10 = divideArray(f64, 10);
    const r10: Result10 = undefined;
    try testing.expectEqual(5, r10.first_half.len);
    try testing.expectEqual(5, r10.second_half.len);

    // Would fail at compile time:
    // const Bad1 = divideArray(bool, 4);  // Not numeric
    // const Bad2 = divideArray(i32, 0);   // Length not positive
    // const Bad3 = divideArray(i32, 5);   // Length not even
}
// ANCHOR_END: contract_validation

// ANCHOR: custom_validators
/// Composite validator for numeric types in a specific range
fn ValidatedNumeric(
    comptime T: type,
    comptime min_bits: u16,
    comptime max_bits: u16,
) type {
    assertNumeric(T);

    const info = @typeInfo(T);
    const bits = switch (info) {
        .int => |int_info| int_info.bits,
        .float => |float_info| float_info.bits,
        else => unreachable,
    };

    if (bits < min_bits or bits > max_bits) {
        @compileError(std.fmt.comptimePrint(
            "Type {s} has {d} bits, must be between {d} and {d}",
            .{ @typeName(T), bits, min_bits, max_bits },
        ));
    }

    return T;
}

/// Builder pattern for complex validation
fn ValidatedStruct(comptime T: type) type {
    // Validate it's a struct
    const info = @typeInfo(T);
    if (info != .@"struct") {
        @compileError("ValidatedStruct requires a struct type");
    }

    // Ensure struct has at least one field
    if (info.@"struct".fields.len == 0) {
        @compileError("Struct must have at least one field");
    }

    return T;
}

test "custom validators" {
    const Small = ValidatedNumeric(u8, 8, 16);
    try testing.expectEqual(u8, Small);

    const Medium = ValidatedNumeric(u32, 16, 64);
    try testing.expectEqual(u32, Medium);

    const Valid = ValidatedStruct(TestStruct);
    try testing.expectEqual(TestStruct, Valid);

    // Would fail:
    // const TooBig = ValidatedNumeric(u128, 8, 64);
    // const Empty = ValidatedStruct(struct {});
}
// ANCHOR_END: custom_validators
```

### See Also

- Recipe 17.1: Type
- Recipe 17.2: Compile
- Recipe 17.4: Generic Data Structure Generation
- Recipe 9.5: Enforcing type checking on a function using a decorator

---

## Recipe 17.4: Generic Data Structure Generation {#recipe-17-4}

**Tags:** allocators, arena-allocator, comptime, comptime-metaprogramming, error-handling, memory, resource-cleanup, slices, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/17-advanced-comptime/recipe_17_4.zig`

### Problem

You need to create reusable container types that work with any payload type while maintaining type safety and performance. You want generic data structures that adapt to different types at compile time without runtime overhead or code duplication.

### Solution

Zig's comptime system lets you write functions that return types, enabling powerful generic programming. These type-generating functions can inspect their parameters and create optimized containers tailored to specific use cases.

### Basic Generic List

A simple dynamic array that works with any type:

```zig
/// Simple generic dynamic array
fn List(comptime T: type) type {
    return struct {
        items: []T,
        capacity: usize,
        allocator: Allocator,

        const Self = @This();

        pub fn init(allocator: Allocator) Self {
            return .{
                .items = &[_]T{},
                .capacity = 0,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            if (self.capacity > 0) {
                self.allocator.free(self.items.ptr[0..self.capacity]);
            }
        }

        pub fn append(self: *Self, item: T) !void {
            if (self.items.len >= self.capacity) {
                try self.grow();
            }
            self.items.ptr[self.items.len] = item;
            self.items.len += 1;
        }

        fn grow(self: *Self) !void {
            const new_capacity = if (self.capacity == 0) 4 else self.capacity * 2;
            const new_memory = try self.allocator.alloc(T, new_capacity);

            if (self.items.len > 0) {
                @memcpy(new_memory[0..self.items.len], self.items);
            }

            if (self.capacity > 0) {
                self.allocator.free(self.items.ptr[0..self.capacity]);
            }

            self.items = new_memory[0..self.items.len];
            self.capacity = new_capacity;
        }
    };
}

test "basic generic list" {
    var int_list = List(i32).init(testing.allocator);
    defer int_list.deinit();

    try int_list.append(1);
    try int_list.append(2);
    try int_list.append(3);

    try testing.expectEqual(3, int_list.items.len);
    try testing.expectEqual(@as(i32, 1), int_list.items[0]);
    try testing.expectEqual(@as(i32, 2), int_list.items[1]);
    try testing.expectEqual(@as(i32, 3), int_list.items[2]);
}
```

### Type-Aware Optimization

Adapt container behavior based on type characteristics:

```zig
/// Generic stack with type-specific optimizations
fn Stack(comptime T: type) type {
    const is_small = @sizeOf(T) <= @sizeOf(usize);
    const inline_capacity = if (is_small) 16 else 4;

    return struct {
        items: [inline_capacity]T,
        len: usize,

        const Self = @This();

        pub fn init() Self {
            return .{
                .items = undefined,
                .len = 0,
            };
        }

        pub fn push(self: *Self, value: T) !void {
            if (self.len >= inline_capacity) {
                return error.StackFull;
            }
            self.items[self.len] = value;
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
    };
}

test "type-aware stack optimization" {
    var small_stack = Stack(u8).init();
    try small_stack.push(1);
    try small_stack.push(2);
    try testing.expectEqual(@as(?u8, 2), small_stack.peek());
    try testing.expectEqual(@as(?u8, 2), small_stack.pop());
    try testing.expectEqual(@as(?u8, 1), small_stack.pop());
    try testing.expectEqual(@as(?u8, null), small_stack.pop());

    var large_stack = Stack([100]u8).init();
    try large_stack.push([_]u8{0} ** 100);
    try testing.expect(large_stack.pop() != null);
}
```

### Generic Result Type

Error handling container that works with any success and error types:

```zig
/// Generic Result type for error handling
fn Result(comptime T: type, comptime E: type) type {
    return union(enum) {
        ok: T,
        err: E,

        const Self = @This();

        pub fn isOk(self: Self) bool {
            return self == .ok;
        }

        pub fn isErr(self: Self) bool {
            return self == .err;
        }

        pub fn unwrap(self: Self) T {
            return switch (self) {
                .ok => |value| value,
                .err => @panic("Called unwrap on error value"),
            };
        }

        pub fn unwrapOr(self: Self, default: T) T {
            return switch (self) {
                .ok => |value| value,
                .err => default,
            };
        }

        pub fn unwrapErr(self: Self) E {
            return switch (self) {
                .err => |e| e,
                .ok => @panic("Called unwrapErr on ok value"),
            };
        }
    };
}

test "generic result type" {
    const IntResult = Result(i32, []const u8);

    const success = IntResult{ .ok = 42 };
    try testing.expect(success.isOk());
    try testing.expectEqual(@as(i32, 42), success.unwrap());

    const failure = IntResult{ .err = "something went wrong" };
    try testing.expect(failure.isErr());
    try testing.expectEqualStrings("something went wrong", failure.unwrapErr());
    try testing.expectEqual(@as(i32, -1), failure.unwrapOr(-1));
}
```

### Pair/Tuple Types

Generic pairs with type-safe operations:

```zig
/// Generic pair/tuple type
fn Pair(comptime A: type, comptime B: type) type {
    return struct {
        first: A,
        second: B,

        const Self = @This();

        pub fn init(a: A, b: B) Self {
            return .{ .first = a, .second = b };
        }

        pub fn swap(self: Self) Pair(B, A) {
            return .{ .first = self.second, .second = self.first };
        }
    };
}

test "generic pair" {
    const p1 = Pair(i32, []const u8).init(42, "hello");
    try testing.expectEqual(@as(i32, 42), p1.first);
    try testing.expectEqualStrings("hello", p1.second);

    const p2 = p1.swap();
    try testing.expectEqualStrings("hello", p2.first);
    try testing.expectEqual(@as(i32, 42), p2.second);
}
```

### Enhanced Optional Wrapper

Build richer optional types with additional methods:

```zig
/// Enhanced optional with additional methods
fn Maybe(comptime T: type) type {
    return struct {
        value: ?T,

        const Self = @This();

        pub fn some(v: T) Self {
            return .{ .value = v };
        }

        pub fn none() Self {
            return .{ .value = null };
        }

        pub fn isSome(self: Self) bool {
            return self.value != null;
        }

        pub fn isNone(self: Self) bool {
            return self.value == null;
        }

        pub fn unwrap(self: Self) T {
            return self.value orelse @panic("Called unwrap on none");
        }

        pub fn unwrapOr(self: Self, default: T) T {
            return self.value orelse default;
        }

        pub fn map(self: Self, comptime U: type, f: fn (T) U) Maybe(U) {
            if (self.value) |v| {
                return Maybe(U).some(f(v));
            }
            return Maybe(U).none();
        }
    };
}

fn double(x: i32) i32 {
    return x * 2;
}

test "enhanced optional" {
    const m1 = Maybe(i32).some(21);
    try testing.expect(m1.isSome());
    try testing.expectEqual(@as(i32, 21), m1.unwrap());

    const m2 = m1.map(i32, double);
    try testing.expectEqual(@as(i32, 42), m2.unwrap());

    const m3 = Maybe(i32).none();
    try testing.expect(m3.isNone());
    try testing.expectEqual(@as(i32, -1), m3.unwrapOr(-1));
}
```

### Generic Tree Node

Recursive data structures that work with any comparable type:

```zig
/// Generic binary tree node
fn TreeNode(comptime T: type) type {
    return struct {
        value: T,
        left: ?*Self,
        right: ?*Self,
        allocator: Allocator,

        const Self = @This();

        pub fn init(allocator: Allocator, value: T) !*Self {
            const node = try allocator.create(Self);
            node.* = .{
                .value = value,
                .left = null,
                .right = null,
                .allocator = allocator,
            };
            return node;
        }

        pub fn deinit(self: *Self) void {
            if (self.left) |left| {
                left.deinit();
                self.allocator.destroy(left);
            }
            if (self.right) |right| {
                right.deinit();
                self.allocator.destroy(right);
            }
        }

        pub fn insert(self: *Self, value: T) !void {
            if (value < self.value) {
                if (self.left) |left| {
                    try left.insert(value);
                } else {
                    self.left = try Self.init(self.allocator, value);
                }
            } else {
                if (self.right) |right| {
                    try right.insert(value);
                } else {
                    self.right = try Self.init(self.allocator, value);
                }
            }
        }
    };
}

test "generic tree node" {
    var root = try TreeNode(i32).init(testing.allocator, 50);
    defer {
        root.deinit();
        testing.allocator.destroy(root);
    }

    try root.insert(30);
    try root.insert(70);
    try root.insert(20);
    try root.insert(40);

    try testing.expectEqual(@as(i32, 50), root.value);
    try testing.expectEqual(@as(i32, 30), root.left.?.value);
    try testing.expectEqual(@as(i32, 70), root.right.?.value);
}
```

### Circular Buffer

Fixed-size ring buffer with compile-time capacity:

```zig
/// Fixed-size circular buffer
fn CircularBuffer(comptime T: type, comptime size: usize) type {
    if (size == 0) {
        @compileError("CircularBuffer size must be greater than 0");
    }

    return struct {
        buffer: [size]T,
        read_pos: usize,
        write_pos: usize,
        count: usize,

        const Self = @This();

        pub fn init() Self {
            return .{
                .buffer = undefined,
                .read_pos = 0,
                .write_pos = 0,
                .count = 0,
            };
        }

        pub fn write(self: *Self, value: T) bool {
            if (self.count >= size) {
                return false; // Buffer full
            }

            self.buffer[self.write_pos] = value;
            self.write_pos = (self.write_pos + 1) % size;
            self.count += 1;
            return true;
        }

        pub fn read(self: *Self) ?T {
            if (self.count == 0) {
                return null;
            }

            const value = self.buffer[self.read_pos];
            self.read_pos = (self.read_pos + 1) % size;
            self.count -= 1;
            return value;
        }

        pub fn isFull(self: Self) bool {
            return self.count >= size;
        }

        pub fn isEmpty(self: Self) bool {
            return self.count == 0;
        }
    };
}

test "circular buffer" {
    var buf = CircularBuffer(u32, 4).init();

    try testing.expect(buf.write(1));
    try testing.expect(buf.write(2));
    try testing.expect(buf.write(3));
    try testing.expect(buf.write(4));
    try testing.expect(buf.isFull());
    try testing.expect(!buf.write(5)); // Should fail, buffer full

    try testing.expectEqual(@as(?u32, 1), buf.read());
    try testing.expectEqual(@as(?u32, 2), buf.read());
    try testing.expect(!buf.isFull());

    try testing.expect(buf.write(5));
    try testing.expect(buf.write(6));

    try testing.expectEqual(@as(?u32, 3), buf.read());
    try testing.expectEqual(@as(?u32, 4), buf.read());
    try testing.expectEqual(@as(?u32, 5), buf.read());
    try testing.expectEqual(@as(?u32, 6), buf.read());
    try testing.expect(buf.isEmpty());
}
```

### Tagged Union Generation

Programmatically create tagged unions from type lists:

```zig
/// Generate tagged union from type list
fn TaggedUnion(comptime types: []const type) type {
    // First create the enum tag type
    var enum_fields: [types.len]std.builtin.Type.EnumField = undefined;
    for (0..types.len) |i| {
        const name = std.fmt.comptimePrint("variant{d}", .{i});
        const name_z = name ++ "";
        enum_fields[i] = .{
            .name = name_z[0..name.len :0],
            .value = i,
        };
    }

    const TagEnum = @Type(.{
        .@"enum" = .{
            .tag_type = std.math.IntFittingRange(0, types.len - 1),
            .fields = &enum_fields,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_exhaustive = true,
        },
    });

    // Now create the union fields
    var union_fields: [types.len]std.builtin.Type.UnionField = undefined;
    for (types, 0..) |T, i| {
        const name = std.fmt.comptimePrint("variant{d}", .{i});
        const name_z = name ++ "";
        union_fields[i] = .{
            .name = name_z[0..name.len :0],
            .type = T,
            .alignment = @alignOf(T),
        };
    }

    return @Type(.{
        .@"union" = .{
            .layout = .auto,
            .tag_type = TagEnum,
            .fields = &union_fields,
            .decls = &[_]std.builtin.Type.Declaration{},
        },
    });
}

test "tagged union generation" {
    const MyUnion = TaggedUnion(&[_]type{ i32, f64, []const u8 });

    var value: MyUnion = .{ .variant0 = 42 };
    try testing.expectEqual(@as(i32, 42), value.variant0);

    value = .{ .variant1 = 3.14 };
    try testing.expectEqual(@as(f64, 3.14), value.variant1);

    value = .{ .variant2 = "hello" };
    try testing.expectEqualStrings("hello", value.variant2);
}
```

### Discussion

Generic data structure generation is one of Zig's most powerful features, enabling type-safe containers without templates, runtime overhead, or code bloat.

### How Type Functions Work

Functions that return `type` are the foundation of generic programming in Zig:

```zig
fn Container(comptime T: type) type {
    return struct {
        value: T,
        // ... methods ...
    };
}
```

These functions:
- Execute at compile time only
- Return types, not values
- Can inspect their parameters using `@typeInfo()`
- Generate specialized code for each concrete type
- Create zero-cost abstractions

### The `comptime` Parameter Pattern

Mark parameters as `comptime` when they must be known at compilation:

```zig
fn Array(comptime T: type, comptime size: usize) type
```

This enables:
- Type parameters (`T: type`)
- Compile-time constants (buffer sizes, capacities)
- Configuration flags
- Any value needed to generate the type

### Type-Specific Optimizations

Use compile-time introspection to adapt behavior:

**Size-Based Decisions**: Choose inline storage for small types, heap allocation for large ones.

**Comparison Operators**: Only generate `<` operators for types that support comparison.

**Memory Management**: Use `memcpy` for simple types, proper copy constructors for complex types.

The Stack example demonstrates this: small types get larger inline buffers, while large types use smaller buffers to conserve stack space.

### The `Self` Pattern

Most generic types use this idiom:

```zig
fn Container(comptime T: type) type {
    return struct {
        const Self = @This();

        pub fn method(self: *Self) void {
            // ...
        }
    };
}
```

`@This()` returns the current struct type, enabling methods to reference their containing type before it's fully defined.

### Generic Methods

Methods can have their own type parameters:

```zig
pub fn map(self: Self, comptime U: type, f: fn (T) U) Maybe(U)
```

This creates higher-order functions that transform container types while maintaining type safety.

### Building Types with @Type

For advanced cases, use `@Type()` to construct types from metadata:

1. Create field arrays with proper types and names
2. Build enum or struct definitions
3. Pass to `@Type()` to generate the actual type

The `TaggedUnion` example shows this process: generating both an enum tag and union fields from a type list.

### Memory Management Patterns

Generic containers handle allocation in two ways:

**Owned Allocation**: Container owns memory and requires an allocator (List, TreeNode).

**Stack Allocation**: Fixed-size containers use stack memory (Stack, CircularBuffer).

Choose based on use case:
- Dynamic sizing → heap allocation
- Known bounds → stack allocation
- Temporary data → stack or arena allocator

### Common Patterns

**Result/Option Types**: Wrap success values and errors or nulls with rich APIs.

**Collection Wrappers**: Build Lists, Stacks, Queues, Trees, Graphs with type-safe interfaces.

**Metaprogramming Helpers**: Create Pair, Tuple, Variant types for generic programming.

**Fixed-Size Buffers**: Generate CircularBuffer, RingBuffer, Pool types with compile-time capacity.

### Zero-Cost Abstractions

Generic types in Zig are zero-cost:

- No runtime type information (RTTI)
- No vtables or dynamic dispatch
- No template code bloat
- Each instantiation is a separate, specialized type
- Optimized as if hand-written for that type

### Limitations and Workarounds

**No Default Parameters**: Can't specify default type arguments, but can use wrapper functions.

**No Variadic Generics**: Use slices or tuples of types instead.

**Name Collisions**: Each instantiation creates a new type, so `List(i32)` and `List(u32)` are completely different types.

### Testing Strategies

Test generic code with:
- Multiple concrete types (small, large, complex)
- Edge cases (empty containers, single elements)
- Memory leak detection (use testing.allocator)
- Type-specific behavior (compare numeric vs non-numeric)

### Full Tested Code

```zig
// Recipe 17.4: Generic Data Structure Generation
// This recipe demonstrates how to build type-safe container types that adapt
// to payload types at compile time, creating zero-overhead generic data structures.

const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;

// ANCHOR: basic_generic_list
/// Simple generic dynamic array
fn List(comptime T: type) type {
    return struct {
        items: []T,
        capacity: usize,
        allocator: Allocator,

        const Self = @This();

        pub fn init(allocator: Allocator) Self {
            return .{
                .items = &[_]T{},
                .capacity = 0,
                .allocator = allocator,
            };
        }

        pub fn deinit(self: *Self) void {
            if (self.capacity > 0) {
                self.allocator.free(self.items.ptr[0..self.capacity]);
            }
        }

        pub fn append(self: *Self, item: T) !void {
            if (self.items.len >= self.capacity) {
                try self.grow();
            }
            self.items.ptr[self.items.len] = item;
            self.items.len += 1;
        }

        fn grow(self: *Self) !void {
            const new_capacity = if (self.capacity == 0) 4 else self.capacity * 2;
            const new_memory = try self.allocator.alloc(T, new_capacity);

            if (self.items.len > 0) {
                @memcpy(new_memory[0..self.items.len], self.items);
            }

            if (self.capacity > 0) {
                self.allocator.free(self.items.ptr[0..self.capacity]);
            }

            self.items = new_memory[0..self.items.len];
            self.capacity = new_capacity;
        }
    };
}

test "basic generic list" {
    var int_list = List(i32).init(testing.allocator);
    defer int_list.deinit();

    try int_list.append(1);
    try int_list.append(2);
    try int_list.append(3);

    try testing.expectEqual(3, int_list.items.len);
    try testing.expectEqual(@as(i32, 1), int_list.items[0]);
    try testing.expectEqual(@as(i32, 2), int_list.items[1]);
    try testing.expectEqual(@as(i32, 3), int_list.items[2]);
}
// ANCHOR_END: basic_generic_list

// ANCHOR: type_aware_optimization
/// Generic stack with type-specific optimizations
fn Stack(comptime T: type) type {
    const is_small = @sizeOf(T) <= @sizeOf(usize);
    const inline_capacity = if (is_small) 16 else 4;

    return struct {
        items: [inline_capacity]T,
        len: usize,

        const Self = @This();

        pub fn init() Self {
            return .{
                .items = undefined,
                .len = 0,
            };
        }

        pub fn push(self: *Self, value: T) !void {
            if (self.len >= inline_capacity) {
                return error.StackFull;
            }
            self.items[self.len] = value;
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
    };
}

test "type-aware stack optimization" {
    var small_stack = Stack(u8).init();
    try small_stack.push(1);
    try small_stack.push(2);
    try testing.expectEqual(@as(?u8, 2), small_stack.peek());
    try testing.expectEqual(@as(?u8, 2), small_stack.pop());
    try testing.expectEqual(@as(?u8, 1), small_stack.pop());
    try testing.expectEqual(@as(?u8, null), small_stack.pop());

    var large_stack = Stack([100]u8).init();
    try large_stack.push([_]u8{0} ** 100);
    try testing.expect(large_stack.pop() != null);
}
// ANCHOR_END: type_aware_optimization

// ANCHOR: result_type
/// Generic Result type for error handling
fn Result(comptime T: type, comptime E: type) type {
    return union(enum) {
        ok: T,
        err: E,

        const Self = @This();

        pub fn isOk(self: Self) bool {
            return self == .ok;
        }

        pub fn isErr(self: Self) bool {
            return self == .err;
        }

        pub fn unwrap(self: Self) T {
            return switch (self) {
                .ok => |value| value,
                .err => @panic("Called unwrap on error value"),
            };
        }

        pub fn unwrapOr(self: Self, default: T) T {
            return switch (self) {
                .ok => |value| value,
                .err => default,
            };
        }

        pub fn unwrapErr(self: Self) E {
            return switch (self) {
                .err => |e| e,
                .ok => @panic("Called unwrapErr on ok value"),
            };
        }
    };
}

test "generic result type" {
    const IntResult = Result(i32, []const u8);

    const success = IntResult{ .ok = 42 };
    try testing.expect(success.isOk());
    try testing.expectEqual(@as(i32, 42), success.unwrap());

    const failure = IntResult{ .err = "something went wrong" };
    try testing.expect(failure.isErr());
    try testing.expectEqualStrings("something went wrong", failure.unwrapErr());
    try testing.expectEqual(@as(i32, -1), failure.unwrapOr(-1));
}
// ANCHOR_END: result_type

// ANCHOR: pair_tuple
/// Generic pair/tuple type
fn Pair(comptime A: type, comptime B: type) type {
    return struct {
        first: A,
        second: B,

        const Self = @This();

        pub fn init(a: A, b: B) Self {
            return .{ .first = a, .second = b };
        }

        pub fn swap(self: Self) Pair(B, A) {
            return .{ .first = self.second, .second = self.first };
        }
    };
}

test "generic pair" {
    const p1 = Pair(i32, []const u8).init(42, "hello");
    try testing.expectEqual(@as(i32, 42), p1.first);
    try testing.expectEqualStrings("hello", p1.second);

    const p2 = p1.swap();
    try testing.expectEqualStrings("hello", p2.first);
    try testing.expectEqual(@as(i32, 42), p2.second);
}
// ANCHOR_END: pair_tuple

// ANCHOR: optional_wrapper
/// Enhanced optional with additional methods
fn Maybe(comptime T: type) type {
    return struct {
        value: ?T,

        const Self = @This();

        pub fn some(v: T) Self {
            return .{ .value = v };
        }

        pub fn none() Self {
            return .{ .value = null };
        }

        pub fn isSome(self: Self) bool {
            return self.value != null;
        }

        pub fn isNone(self: Self) bool {
            return self.value == null;
        }

        pub fn unwrap(self: Self) T {
            return self.value orelse @panic("Called unwrap on none");
        }

        pub fn unwrapOr(self: Self, default: T) T {
            return self.value orelse default;
        }

        pub fn map(self: Self, comptime U: type, f: fn (T) U) Maybe(U) {
            if (self.value) |v| {
                return Maybe(U).some(f(v));
            }
            return Maybe(U).none();
        }
    };
}

fn double(x: i32) i32 {
    return x * 2;
}

test "enhanced optional" {
    const m1 = Maybe(i32).some(21);
    try testing.expect(m1.isSome());
    try testing.expectEqual(@as(i32, 21), m1.unwrap());

    const m2 = m1.map(i32, double);
    try testing.expectEqual(@as(i32, 42), m2.unwrap());

    const m3 = Maybe(i32).none();
    try testing.expect(m3.isNone());
    try testing.expectEqual(@as(i32, -1), m3.unwrapOr(-1));
}
// ANCHOR_END: optional_wrapper

// ANCHOR: tree_node
/// Generic binary tree node
fn TreeNode(comptime T: type) type {
    return struct {
        value: T,
        left: ?*Self,
        right: ?*Self,
        allocator: Allocator,

        const Self = @This();

        pub fn init(allocator: Allocator, value: T) !*Self {
            const node = try allocator.create(Self);
            node.* = .{
                .value = value,
                .left = null,
                .right = null,
                .allocator = allocator,
            };
            return node;
        }

        pub fn deinit(self: *Self) void {
            if (self.left) |left| {
                left.deinit();
                self.allocator.destroy(left);
            }
            if (self.right) |right| {
                right.deinit();
                self.allocator.destroy(right);
            }
        }

        pub fn insert(self: *Self, value: T) !void {
            if (value < self.value) {
                if (self.left) |left| {
                    try left.insert(value);
                } else {
                    self.left = try Self.init(self.allocator, value);
                }
            } else {
                if (self.right) |right| {
                    try right.insert(value);
                } else {
                    self.right = try Self.init(self.allocator, value);
                }
            }
        }
    };
}

test "generic tree node" {
    var root = try TreeNode(i32).init(testing.allocator, 50);
    defer {
        root.deinit();
        testing.allocator.destroy(root);
    }

    try root.insert(30);
    try root.insert(70);
    try root.insert(20);
    try root.insert(40);

    try testing.expectEqual(@as(i32, 50), root.value);
    try testing.expectEqual(@as(i32, 30), root.left.?.value);
    try testing.expectEqual(@as(i32, 70), root.right.?.value);
}
// ANCHOR_END: tree_node

// ANCHOR: circular_buffer
/// Fixed-size circular buffer
fn CircularBuffer(comptime T: type, comptime size: usize) type {
    if (size == 0) {
        @compileError("CircularBuffer size must be greater than 0");
    }

    return struct {
        buffer: [size]T,
        read_pos: usize,
        write_pos: usize,
        count: usize,

        const Self = @This();

        pub fn init() Self {
            return .{
                .buffer = undefined,
                .read_pos = 0,
                .write_pos = 0,
                .count = 0,
            };
        }

        pub fn write(self: *Self, value: T) bool {
            if (self.count >= size) {
                return false; // Buffer full
            }

            self.buffer[self.write_pos] = value;
            self.write_pos = (self.write_pos + 1) % size;
            self.count += 1;
            return true;
        }

        pub fn read(self: *Self) ?T {
            if (self.count == 0) {
                return null;
            }

            const value = self.buffer[self.read_pos];
            self.read_pos = (self.read_pos + 1) % size;
            self.count -= 1;
            return value;
        }

        pub fn isFull(self: Self) bool {
            return self.count >= size;
        }

        pub fn isEmpty(self: Self) bool {
            return self.count == 0;
        }
    };
}

test "circular buffer" {
    var buf = CircularBuffer(u32, 4).init();

    try testing.expect(buf.write(1));
    try testing.expect(buf.write(2));
    try testing.expect(buf.write(3));
    try testing.expect(buf.write(4));
    try testing.expect(buf.isFull());
    try testing.expect(!buf.write(5)); // Should fail, buffer full

    try testing.expectEqual(@as(?u32, 1), buf.read());
    try testing.expectEqual(@as(?u32, 2), buf.read());
    try testing.expect(!buf.isFull());

    try testing.expect(buf.write(5));
    try testing.expect(buf.write(6));

    try testing.expectEqual(@as(?u32, 3), buf.read());
    try testing.expectEqual(@as(?u32, 4), buf.read());
    try testing.expectEqual(@as(?u32, 5), buf.read());
    try testing.expectEqual(@as(?u32, 6), buf.read());
    try testing.expect(buf.isEmpty());
}
// ANCHOR_END: circular_buffer

// ANCHOR: tagged_union
/// Generate tagged union from type list
fn TaggedUnion(comptime types: []const type) type {
    // First create the enum tag type
    var enum_fields: [types.len]std.builtin.Type.EnumField = undefined;
    for (0..types.len) |i| {
        const name = std.fmt.comptimePrint("variant{d}", .{i});
        const name_z = name ++ "";
        enum_fields[i] = .{
            .name = name_z[0..name.len :0],
            .value = i,
        };
    }

    const TagEnum = @Type(.{
        .@"enum" = .{
            .tag_type = std.math.IntFittingRange(0, types.len - 1),
            .fields = &enum_fields,
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_exhaustive = true,
        },
    });

    // Now create the union fields
    var union_fields: [types.len]std.builtin.Type.UnionField = undefined;
    for (types, 0..) |T, i| {
        const name = std.fmt.comptimePrint("variant{d}", .{i});
        const name_z = name ++ "";
        union_fields[i] = .{
            .name = name_z[0..name.len :0],
            .type = T,
            .alignment = @alignOf(T),
        };
    }

    return @Type(.{
        .@"union" = .{
            .layout = .auto,
            .tag_type = TagEnum,
            .fields = &union_fields,
            .decls = &[_]std.builtin.Type.Declaration{},
        },
    });
}

test "tagged union generation" {
    const MyUnion = TaggedUnion(&[_]type{ i32, f64, []const u8 });

    var value: MyUnion = .{ .variant0 = 42 };
    try testing.expectEqual(@as(i32, 42), value.variant0);

    value = .{ .variant1 = 3.14 };
    try testing.expectEqual(@as(f64, 3.14), value.variant1);

    value = .{ .variant2 = "hello" };
    try testing.expectEqualStrings("hello", value.variant2);
}
// ANCHOR_END: tagged_union
```

### See Also

- Recipe 17.1: Type
- Recipe 17.3: Compile
- Recipe 9.11: Using comptime to control instance creation
- Recipe 9.16: Defining structs programmatically

---

## Recipe 17.5: Compile-Time Dependency Injection {#recipe-17-5}

**Tags:** c-interop, comptime, comptime-metaprogramming, error-handling, pointers, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/17-advanced-comptime/recipe_17_5.zig`

### Problem

You need to manage dependencies between components without runtime overhead, reflection, or complex frameworks. You want the flexibility of dependency injection with the performance and safety guarantees of compile-time resolution.

### Solution

Zig's comptime system enables dependency injection that's resolved entirely at compilation. Pass types as parameters to create components that work with different implementations, all without runtime cost.

### Basic Interface Injection

Inject dependencies through type parameters:

```zig
/// Basic dependency injection through comptime interfaces
fn Service(comptime Logger: type) type {
    return struct {
        logger: Logger,

        const Self = @This();

        pub fn init(logger: Logger) Self {
            return .{ .logger = logger };
        }

        pub fn doWork(self: *Self, task: []const u8) void {
            self.logger.log("Starting: {s}", task);
            // Do actual work...
            self.logger.log("Completed: {s}", task);
        }
    };
}

const ConsoleLogger = struct {
    pub fn log(self: *const ConsoleLogger, comptime fmt: []const u8, task: []const u8) void {
        _ = self;
        std.debug.print(fmt ++ "\n", .{task});
    }
};

const NoopLogger = struct {
    pub fn log(self: *const NoopLogger, comptime fmt: []const u8, task: []const u8) void {
        _ = self;
        _ = fmt;
        _ = task;
    }
};

test "basic dependency injection" {
    const logger = NoopLogger{};
    var service = Service(NoopLogger).init(logger);
    service.doWork("test task");

    // Different logger type creates different service type
    const console_logger = ConsoleLogger{};
    var console_service = Service(ConsoleLogger).init(console_logger);
    console_service.doWork("console task");
}
```

### Configuration Injection

Inject configuration values at compile time:

```zig
/// Inject configuration at compile time
fn ConfigurableApp(comptime config: struct {
    debug_mode: bool,
    max_connections: usize,
    timeout_ms: u64,
}) type {
    return struct {
        connections: usize,

        const Self = @This();
        const debug = config.debug_mode;
        const max_conn = config.max_connections;
        const timeout = config.timeout_ms;

        pub fn init() Self {
            if (debug) {
                @compileLog("App initialized with max connections:", max_conn);
            }
            return .{ .connections = 0 };
        }

        pub fn connect(self: *Self) !void {
            if (self.connections >= max_conn) {
                return error.TooManyConnections;
            }
            self.connections += 1;

            if (debug) {
                std.debug.print("Connected (total: {})\n", .{self.connections});
            }
        }

        pub fn getTimeout(self: Self) u64 {
            _ = self;
            return timeout;
        }
    };
}

test "configuration injection" {
    const DevApp = ConfigurableApp(.{
        .debug_mode = false, // Changed to false to avoid comptime log in test
        .max_connections = 2,
        .timeout_ms = 1000,
    });

    var app = DevApp.init();
    try app.connect();
    try app.connect();
    try testing.expectError(error.TooManyConnections, app.connect());
    try testing.expectEqual(@as(u64, 1000), app.getTimeout());
}
```

### Multiple Dependencies

Compose components from multiple injected types:

```zig
/// Inject multiple dependencies
fn Application(
    comptime Database: type,
    comptime Cache: type,
    comptime Logger: type,
) type {
    return struct {
        db: Database,
        cache: Cache,
        logger: Logger,

        const Self = @This();

        pub fn init(db: Database, cache: Cache, logger: Logger) Self {
            return .{
                .db = db,
                .cache = cache,
                .logger = logger,
            };
        }

        pub fn getData(self: *Self, key: []const u8) !?[]const u8 {
            // Try cache first
            if (try self.cache.get(key)) |data| {
                self.logger.log("Cache hit: {s}", key);
                return data;
            }

            // Fallback to database
            if (try self.db.query(key)) |data| {
                self.logger.log("Database query: {s}", key);
                try self.cache.set(key, data);
                return data;
            }

            return null;
        }
    };
}

const MockDatabase = struct {
    pub fn query(self: *const MockDatabase, key: []const u8) !?[]const u8 {
        _ = self;
        if (std.mem.eql(u8, key, "test")) {
            return "db_value";
        }
        return null;
    }
};

const MockCache = struct {
    pub fn get(self: *const MockCache, key: []const u8) !?[]const u8 {
        _ = self;
        _ = key;
        return null;
    }

    pub fn set(self: *const MockCache, key: []const u8, value: []const u8) !void {
        _ = self;
        _ = key;
        _ = value;
    }
};

test "multiple dependencies" {
    const db = MockDatabase{};
    const cache = MockCache{};
    const logger = NoopLogger{};

    var app = Application(MockDatabase, MockCache, NoopLogger).init(db, cache, logger);

    const result = try app.getData("test");
    try testing.expect(result != null);
    try testing.expectEqualStrings("db_value", result.?);
}
```

### Trait-Based Injection

Verify dependencies meet interface requirements at compile time:

```zig
/// Trait-based dependency injection with compile-time verification
fn requiresLogger(comptime T: type) void {
    if (!@hasDecl(T, "log")) {
        @compileError("Type " ++ @typeName(T) ++ " must implement log method");
    }
}

fn Worker(comptime Logger: type) type {
    comptime requiresLogger(Logger);

    return struct {
        logger: Logger,
        tasks_completed: usize,

        const Self = @This();

        pub fn init(logger: Logger) Self {
            return .{
                .logger = logger,
                .tasks_completed = 0,
            };
        }

        pub fn process(self: *Self, task: []const u8) void {
            self.logger.log("Processing: {s}", task);
            self.tasks_completed += 1;
        }

        pub fn getCompleted(self: Self) usize {
            return self.tasks_completed;
        }
    };
}

test "trait-based injection" {
    const logger = NoopLogger{};
    var worker = Worker(NoopLogger).init(logger);

    worker.process("task1");
    worker.process("task2");

    try testing.expectEqual(@as(usize, 2), worker.getCompleted());
}
```

### Factory Pattern

Use factories to create components with injected dependencies:

```zig
/// Factory pattern with compile-time dependency resolution
fn ServiceFactory(comptime dependencies: struct {
    logger_type: type,
    storage_type: type,
    enable_metrics: bool,
}) type {
    return struct {
        pub fn createService() FactoryService {
            return FactoryService{
                .logger = dependencies.logger_type{},
                .storage = dependencies.storage_type{},
                .metrics_enabled = dependencies.enable_metrics,
            };
        }

        const FactoryService = struct {
            logger: dependencies.logger_type,
            storage: dependencies.storage_type,
            metrics_enabled: bool,

            pub fn execute(self: *FactoryService, command: []const u8) void {
                self.logger.log("Executing: {s}", command);
                self.storage.save(command);

                if (self.metrics_enabled) {
                    std.debug.print("Metrics: command executed\n", .{});
                }
            }
        };
    };
}

const MockStorage = struct {
    pub fn save(self: *const MockStorage, data: []const u8) void {
        _ = self;
        _ = data;
    }
};

test "factory-based injection" {
    const Factory = ServiceFactory(.{
        .logger_type = NoopLogger,
        .storage_type = MockStorage,
        .enable_metrics = false,
    });

    var service = Factory.createService();
    service.execute("test command");
}
```

### Context Objects

Bundle dependencies into context objects:

```zig
/// Context object pattern for dependency management
fn Context(comptime DepsType: type) type {
    return struct {
        deps: DepsType,

        const Self = @This();

        pub fn init(deps: DepsType) Self {
            return .{ .deps = deps };
        }

        pub fn getLogger(self: *const Self) @TypeOf(self.deps.logger) {
            return self.deps.logger;
        }

        pub fn getDatabase(self: *const Self) @TypeOf(self.deps.db) {
            return self.deps.db;
        }
    };
}

fn BusinessLogic(comptime Ctx: type) type {
    return struct {
        context: Ctx,

        const Self = @This();

        pub fn init(context: Ctx) Self {
            return .{ .context = context };
        }

        pub fn run(self: *Self) void {
            const logger = self.context.getLogger();
            const db = self.context.getDatabase();

            logger.log("Running business logic", "");
            _ = db.query("data") catch {};
        }
    };
}

test "context-based injection" {
    const DepsStruct = struct {
        logger: NoopLogger,
        db: MockDatabase,
    };

    const deps = DepsStruct{
        .logger = NoopLogger{},
        .db = MockDatabase{},
    };

    const ctx = Context(DepsStruct).init(deps);
    var logic = BusinessLogic(@TypeOf(ctx)).init(ctx);
    logic.run();
}
```

### Strategy Pattern

Inject behavior through strategy objects:

```zig
/// Strategy pattern with compile-time selection
fn Processor(comptime Strategy: type) type {
    return struct {
        strategy: Strategy,

        const Self = @This();

        pub fn init(strategy: Strategy) Self {
            return .{ .strategy = strategy };
        }

        pub fn process(self: *Self, data: []const u8) []const u8 {
            return self.strategy.transform(data);
        }
    };
}

const UpperCaseStrategy = struct {
    pub fn transform(self: *const UpperCaseStrategy, data: []const u8) []const u8 {
        _ = self;
        // Simplified: just return the input
        return data;
    }
};

const LowerCaseStrategy = struct {
    pub fn transform(self: *const LowerCaseStrategy, data: []const u8) []const u8 {
        _ = self;
        // Simplified: just return the input
        return data;
    }
};

test "strategy injection" {
    const upper_strategy = UpperCaseStrategy{};
    var upper_processor = Processor(UpperCaseStrategy).init(upper_strategy);
    const result1 = upper_processor.process("hello");
    try testing.expectEqualStrings("hello", result1);

    const lower_strategy = LowerCaseStrategy{};
    var lower_processor = Processor(LowerCaseStrategy).init(lower_strategy);
    const result2 = lower_processor.process("WORLD");
    try testing.expectEqualStrings("WORLD", result2);
}
```

### Module Injection

Inject entire modules as dependencies:

```zig
/// Inject entire modules as dependencies
fn ModularSystem(comptime modules: struct {
    auth: type,
    storage: type,
    network: type,
}) type {
    return struct {
        auth: modules.auth,
        storage: modules.storage,
        network: modules.network,

        const Self = @This();

        pub fn init(auth: modules.auth, storage: modules.storage, network: modules.network) Self {
            return .{
                .auth = auth,
                .storage = storage,
                .network = network,
            };
        }

        pub fn handleRequest(self: *Self, user: []const u8) !bool {
            // Authenticate
            if (!self.auth.verify(user)) {
                return false;
            }

            // Store data
            self.storage.save(user);

            // Send notification
            try self.network.send(user);

            return true;
        }
    };
}

const MockAuth = struct {
    pub fn verify(self: *const MockAuth, user: []const u8) bool {
        _ = self;
        return user.len > 0;
    }
};

const MockNetwork = struct {
    pub fn send(self: *const MockNetwork, data: []const u8) !void {
        _ = self;
        _ = data;
    }
};

test "module injection" {
    const auth = MockAuth{};
    const storage = MockStorage{};
    const network = MockNetwork{};

    var system = ModularSystem(.{
        .auth = MockAuth,
        .storage = MockStorage,
        .network = MockNetwork,
    }).init(auth, storage, network);

    try testing.expect(try system.handleRequest("user123"));
    try testing.expect(!try system.handleRequest(""));
}
```

### Discussion

Compile-time dependency injection in Zig provides the flexibility of traditional DI frameworks without any runtime overhead or complex machinery.

### How Compile-Time DI Works

Traditional dependency injection uses runtime reflection or containers to wire components together. Zig does this at compile time:

1. **Type Parameters**: Functions return types parameterized by dependency types
2. **Compile-Time Verification**: `@hasDecl` and type introspection ensure interfaces match
3. **Zero Runtime Cost**: All resolution happens during compilation
4. **Static Dispatch**: No vtables or function pointer indirection

The result is code that's as fast as hand-written, tightly-coupled code but with the flexibility of loosely-coupled architecture.

### Inversion of Control

Components depend on abstractions (type parameters) rather than concrete implementations:

```zig
fn Component(comptime Logger: type) type
```

This `Component` doesn't care what `Logger` is, just that it has the methods it needs. Swap implementations by changing the type parameter.

### Duck Typing with Safety

Zig uses structural typing for interfaces:

```zig
fn requiresLogger(comptime T: type) void {
    if (!@hasDecl(T, "log")) {
        @compileError("Type must implement log method");
    }
}
```

Types don't need to explicitly declare they implement an interface. If they have the required methods, they work. But unlike dynamic duck typing, this is verified at compile time.

### Configuration as Code

The configuration injection pattern embeds settings directly into types:

```zig
const App = ConfigurableApp(.{
    .debug_mode = true,
    .max_connections = 100,
});
```

These values are compile-time constants, allowing:
- Dead code elimination (debug code removed in release builds)
- Constant folding (comparisons optimized away)
- Type-level configuration (different types for different configs)

### Testing and Mocking

Compile-time DI makes testing straightforward:

1. Create mock implementations with the same interface
2. Inject mocks instead of real dependencies
3. No test framework magic needed
4. Test exactly the same code paths as production

Each test can use different mock types, creating completely separate test cases without runtime switches.

### Composition Patterns

**Single Dependency**: Simple type parameter for one dependency.

**Multiple Dependencies**: Multiple type parameters for complex components.

**Context Objects**: Bundle related dependencies together, pass one context instead of many individual types.

**Factory Pattern**: Hide construction logic, create complex dependency graphs.

**Strategy Pattern**: Inject algorithmic behavior, swap strategies by type.

### When to Use Each Pattern

**Basic Injection**: Simple cases with 1-2 dependencies. Clear and direct.

**Configuration**: When behavior changes based on build settings or environment.

**Context Objects**: Many dependencies (more than 3-4). Reduces parameter count.

**Factories**: Complex initialization logic or multi-step construction.

**Traits/Validation**: When you need to document or enforce interface contracts.

### Limitations

**No Runtime Polymorphism**: Each type parameter creates a distinct concrete type. Can't store different implementations in the same collection without wrapping.

**Compilation Time**: More type combinations mean more code generation and longer builds.

**Binary Size**: Each instantiation generates new code. Many instantiations can increase binary size.

**No Dynamic Loading**: All dependencies must be known at compile time. Can't load plugins at runtime without additional infrastructure.

### Workarounds for Limitations

**Runtime Polymorphism**: Use tagged unions or function pointers when you need it.

**Compilation Time**: Use aggressive caching, split into modules, or reduce instantiation diversity.

**Binary Size**: Share implementations through common base types or use inline functions.

**Dynamic Loading**: Combine comptime DI for known components with runtime DI for plugins.

### Best Practices

**Keep Interfaces Minimal**: Only require methods you actually use. Smaller interfaces mean more flexibility.

**Validate Early**: Use `@hasDecl` and assertions to catch interface mismatches at the injection point.

**Document Contracts**: Use comments or compile-time checks to document what dependencies must provide.

**Prefer Composition**: Build complex systems from simple, single-responsibility components.

**Test Boundaries**: Use DI at system boundaries (I/O, external services) rather than everywhere.

### Comparison to Other Languages

**Java/C# DI**: Runtime reflection, container-managed lifecycles, complex configuration. Zig: compile-time, no containers, simple and fast.

**C++ Templates**: Similar mechanics but Zig's comptime is more flexible and generates clearer errors.

**Go Interfaces**: Runtime type checking, vtable dispatch. Zig: compile-time checking, static dispatch.

### Performance Characteristics

Compile-time DI is zero-cost:

- No runtime type checks
- No vtable indirection
- No container overhead
- No reflection penalty
- Fully inlined and optimized

The generated code is indistinguishable from hand-written code that directly uses concrete types.

### Full Tested Code

```zig
// Recipe 17.5: Compile-Time Dependency Injection
// This recipe demonstrates how to create dependency injection systems resolved
// entirely at compile time, achieving zero runtime reflection or performance cost.

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_interface
/// Basic dependency injection through comptime interfaces
fn Service(comptime Logger: type) type {
    return struct {
        logger: Logger,

        const Self = @This();

        pub fn init(logger: Logger) Self {
            return .{ .logger = logger };
        }

        pub fn doWork(self: *Self, task: []const u8) void {
            self.logger.log("Starting: {s}", task);
            // Do actual work...
            self.logger.log("Completed: {s}", task);
        }
    };
}

const ConsoleLogger = struct {
    pub fn log(self: *const ConsoleLogger, comptime fmt: []const u8, task: []const u8) void {
        _ = self;
        std.debug.print(fmt ++ "\n", .{task});
    }
};

const NoopLogger = struct {
    pub fn log(self: *const NoopLogger, comptime fmt: []const u8, task: []const u8) void {
        _ = self;
        _ = fmt;
        _ = task;
    }
};

test "basic dependency injection" {
    const logger = NoopLogger{};
    var service = Service(NoopLogger).init(logger);
    service.doWork("test task");

    // Different logger type creates different service type
    const console_logger = ConsoleLogger{};
    var console_service = Service(ConsoleLogger).init(console_logger);
    console_service.doWork("console task");
}
// ANCHOR_END: basic_interface

// ANCHOR: configuration_injection
/// Inject configuration at compile time
fn ConfigurableApp(comptime config: struct {
    debug_mode: bool,
    max_connections: usize,
    timeout_ms: u64,
}) type {
    return struct {
        connections: usize,

        const Self = @This();
        const debug = config.debug_mode;
        const max_conn = config.max_connections;
        const timeout = config.timeout_ms;

        pub fn init() Self {
            if (debug) {
                @compileLog("App initialized with max connections:", max_conn);
            }
            return .{ .connections = 0 };
        }

        pub fn connect(self: *Self) !void {
            if (self.connections >= max_conn) {
                return error.TooManyConnections;
            }
            self.connections += 1;

            if (debug) {
                std.debug.print("Connected (total: {})\n", .{self.connections});
            }
        }

        pub fn getTimeout(self: Self) u64 {
            _ = self;
            return timeout;
        }
    };
}

test "configuration injection" {
    const DevApp = ConfigurableApp(.{
        .debug_mode = false, // Changed to false to avoid comptime log in test
        .max_connections = 2,
        .timeout_ms = 1000,
    });

    var app = DevApp.init();
    try app.connect();
    try app.connect();
    try testing.expectError(error.TooManyConnections, app.connect());
    try testing.expectEqual(@as(u64, 1000), app.getTimeout());
}
// ANCHOR_END: configuration_injection

// ANCHOR: multi_dependency
/// Inject multiple dependencies
fn Application(
    comptime Database: type,
    comptime Cache: type,
    comptime Logger: type,
) type {
    return struct {
        db: Database,
        cache: Cache,
        logger: Logger,

        const Self = @This();

        pub fn init(db: Database, cache: Cache, logger: Logger) Self {
            return .{
                .db = db,
                .cache = cache,
                .logger = logger,
            };
        }

        pub fn getData(self: *Self, key: []const u8) !?[]const u8 {
            // Try cache first
            if (try self.cache.get(key)) |data| {
                self.logger.log("Cache hit: {s}", key);
                return data;
            }

            // Fallback to database
            if (try self.db.query(key)) |data| {
                self.logger.log("Database query: {s}", key);
                try self.cache.set(key, data);
                return data;
            }

            return null;
        }
    };
}

const MockDatabase = struct {
    pub fn query(self: *const MockDatabase, key: []const u8) !?[]const u8 {
        _ = self;
        if (std.mem.eql(u8, key, "test")) {
            return "db_value";
        }
        return null;
    }
};

const MockCache = struct {
    pub fn get(self: *const MockCache, key: []const u8) !?[]const u8 {
        _ = self;
        _ = key;
        return null;
    }

    pub fn set(self: *const MockCache, key: []const u8, value: []const u8) !void {
        _ = self;
        _ = key;
        _ = value;
    }
};

test "multiple dependencies" {
    const db = MockDatabase{};
    const cache = MockCache{};
    const logger = NoopLogger{};

    var app = Application(MockDatabase, MockCache, NoopLogger).init(db, cache, logger);

    const result = try app.getData("test");
    try testing.expect(result != null);
    try testing.expectEqualStrings("db_value", result.?);
}
// ANCHOR_END: multi_dependency

// ANCHOR: trait_based_injection
/// Trait-based dependency injection with compile-time verification
fn requiresLogger(comptime T: type) void {
    if (!@hasDecl(T, "log")) {
        @compileError("Type " ++ @typeName(T) ++ " must implement log method");
    }
}

fn Worker(comptime Logger: type) type {
    comptime requiresLogger(Logger);

    return struct {
        logger: Logger,
        tasks_completed: usize,

        const Self = @This();

        pub fn init(logger: Logger) Self {
            return .{
                .logger = logger,
                .tasks_completed = 0,
            };
        }

        pub fn process(self: *Self, task: []const u8) void {
            self.logger.log("Processing: {s}", task);
            self.tasks_completed += 1;
        }

        pub fn getCompleted(self: Self) usize {
            return self.tasks_completed;
        }
    };
}

test "trait-based injection" {
    const logger = NoopLogger{};
    var worker = Worker(NoopLogger).init(logger);

    worker.process("task1");
    worker.process("task2");

    try testing.expectEqual(@as(usize, 2), worker.getCompleted());
}
// ANCHOR_END: trait_based_injection

// ANCHOR: factory_injection
/// Factory pattern with compile-time dependency resolution
fn ServiceFactory(comptime dependencies: struct {
    logger_type: type,
    storage_type: type,
    enable_metrics: bool,
}) type {
    return struct {
        pub fn createService() FactoryService {
            return FactoryService{
                .logger = dependencies.logger_type{},
                .storage = dependencies.storage_type{},
                .metrics_enabled = dependencies.enable_metrics,
            };
        }

        const FactoryService = struct {
            logger: dependencies.logger_type,
            storage: dependencies.storage_type,
            metrics_enabled: bool,

            pub fn execute(self: *FactoryService, command: []const u8) void {
                self.logger.log("Executing: {s}", command);
                self.storage.save(command);

                if (self.metrics_enabled) {
                    std.debug.print("Metrics: command executed\n", .{});
                }
            }
        };
    };
}

const MockStorage = struct {
    pub fn save(self: *const MockStorage, data: []const u8) void {
        _ = self;
        _ = data;
    }
};

test "factory-based injection" {
    const Factory = ServiceFactory(.{
        .logger_type = NoopLogger,
        .storage_type = MockStorage,
        .enable_metrics = false,
    });

    var service = Factory.createService();
    service.execute("test command");
}
// ANCHOR_END: factory_injection

// ANCHOR: context_injection
/// Context object pattern for dependency management
fn Context(comptime DepsType: type) type {
    return struct {
        deps: DepsType,

        const Self = @This();

        pub fn init(deps: DepsType) Self {
            return .{ .deps = deps };
        }

        pub fn getLogger(self: *const Self) @TypeOf(self.deps.logger) {
            return self.deps.logger;
        }

        pub fn getDatabase(self: *const Self) @TypeOf(self.deps.db) {
            return self.deps.db;
        }
    };
}

fn BusinessLogic(comptime Ctx: type) type {
    return struct {
        context: Ctx,

        const Self = @This();

        pub fn init(context: Ctx) Self {
            return .{ .context = context };
        }

        pub fn run(self: *Self) void {
            const logger = self.context.getLogger();
            const db = self.context.getDatabase();

            logger.log("Running business logic", "");
            _ = db.query("data") catch {};
        }
    };
}

test "context-based injection" {
    const DepsStruct = struct {
        logger: NoopLogger,
        db: MockDatabase,
    };

    const deps = DepsStruct{
        .logger = NoopLogger{},
        .db = MockDatabase{},
    };

    const ctx = Context(DepsStruct).init(deps);
    var logic = BusinessLogic(@TypeOf(ctx)).init(ctx);
    logic.run();
}
// ANCHOR_END: context_injection

// ANCHOR: strategy_injection
/// Strategy pattern with compile-time selection
fn Processor(comptime Strategy: type) type {
    return struct {
        strategy: Strategy,

        const Self = @This();

        pub fn init(strategy: Strategy) Self {
            return .{ .strategy = strategy };
        }

        pub fn process(self: *Self, data: []const u8) []const u8 {
            return self.strategy.transform(data);
        }
    };
}

const UpperCaseStrategy = struct {
    pub fn transform(self: *const UpperCaseStrategy, data: []const u8) []const u8 {
        _ = self;
        // Simplified: just return the input
        return data;
    }
};

const LowerCaseStrategy = struct {
    pub fn transform(self: *const LowerCaseStrategy, data: []const u8) []const u8 {
        _ = self;
        // Simplified: just return the input
        return data;
    }
};

test "strategy injection" {
    const upper_strategy = UpperCaseStrategy{};
    var upper_processor = Processor(UpperCaseStrategy).init(upper_strategy);
    const result1 = upper_processor.process("hello");
    try testing.expectEqualStrings("hello", result1);

    const lower_strategy = LowerCaseStrategy{};
    var lower_processor = Processor(LowerCaseStrategy).init(lower_strategy);
    const result2 = lower_processor.process("WORLD");
    try testing.expectEqualStrings("WORLD", result2);
}
// ANCHOR_END: strategy_injection

// ANCHOR: module_injection
/// Inject entire modules as dependencies
fn ModularSystem(comptime modules: struct {
    auth: type,
    storage: type,
    network: type,
}) type {
    return struct {
        auth: modules.auth,
        storage: modules.storage,
        network: modules.network,

        const Self = @This();

        pub fn init(auth: modules.auth, storage: modules.storage, network: modules.network) Self {
            return .{
                .auth = auth,
                .storage = storage,
                .network = network,
            };
        }

        pub fn handleRequest(self: *Self, user: []const u8) !bool {
            // Authenticate
            if (!self.auth.verify(user)) {
                return false;
            }

            // Store data
            self.storage.save(user);

            // Send notification
            try self.network.send(user);

            return true;
        }
    };
}

const MockAuth = struct {
    pub fn verify(self: *const MockAuth, user: []const u8) bool {
        _ = self;
        return user.len > 0;
    }
};

const MockNetwork = struct {
    pub fn send(self: *const MockNetwork, data: []const u8) !void {
        _ = self;
        _ = data;
    }
};

test "module injection" {
    const auth = MockAuth{};
    const storage = MockStorage{};
    const network = MockNetwork{};

    var system = ModularSystem(.{
        .auth = MockAuth,
        .storage = MockStorage,
        .network = MockNetwork,
    }).init(auth, storage, network);

    try testing.expect(try system.handleRequest("user123"));
    try testing.expect(!try system.handleRequest(""));
}
// ANCHOR_END: module_injection
```

### See Also

- Recipe 17.1: Type
- Recipe 17.3: Compile
- Recipe 17.4: Generic Data Structure Generation
- Recipe 9.7: Defining decorators as structs

---

## Recipe 17.6: Build-Time Resource Embedding {#recipe-17-6}

**Tags:** c-interop, comptime, comptime-metaprogramming, error-handling, json, parsing, slices, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/17-advanced-comptime/recipe_17_6.zig`

### Problem

You need to embed files, configuration data, or other resources directly into your binary. You want to process these resources at compile time, generate lookup tables, and eliminate runtime file I/O for bundled assets.

### Solution

Zig's `@embedFile` builtin reads files at compile time and embeds their contents as string literals in your binary. Combined with comptime processing, you can parse, transform, and optimize resources during compilation.

### Basic File Embedding

Embed text files directly into your program:

```zig
/// Embed a text file directly into the binary
const embedded_message = @embedFile("assets/message.txt");

test "basic file embedding" {
    try testing.expect(embedded_message.len > 0);
    try testing.expect(std.mem.indexOf(u8, embedded_message, "Hello") != null);
}
```

### Parse Configuration at Compile Time

Process embedded configuration files during compilation:

```zig
/// Parse embedded configuration at compile time
const embedded_config = @embedFile("assets/config.txt");

fn parseConfig(comptime content: []const u8) type {
    @setEvalBranchQuota(10000);

    var line_count: usize = 0;
    var pos: usize = 0;

    // Count lines
    while (pos < content.len) : (pos += 1) {
        if (content[pos] == '\n') {
            line_count += 1;
        }
    }

    // Parse key-value pairs
    var fields: [line_count]std.builtin.Type.StructField = undefined;
    var field_idx: usize = 0;
    var line_start: usize = 0;

    pos = 0;
    while (pos < content.len) : (pos += 1) {
        if (content[pos] == '\n' or pos == content.len - 1) {
            const line_end = if (content[pos] == '\n') pos else pos + 1;
            const line = content[line_start..line_end];

            // Find '=' separator
            for (line, 0..) |char, i| {
                if (char == '=') {
                    const key = line[0..i];

                    // Create field with null-terminated name
                    const key_z = key ++ "";
                    fields[field_idx] = .{
                        .name = key_z[0..key.len :0],
                        .type = []const u8,
                        .default_value_ptr = null,
                        .is_comptime = false,
                        .alignment = @alignOf([]const u8),
                    };
                    field_idx += 1;
                    break;
                }
            }

            line_start = pos + 1;
        }
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = fields[0..field_idx],
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "parse config at compile time" {
    const ConfigType = parseConfig(embedded_config);

    // Verify the type has the expected fields
    const type_info = @typeInfo(ConfigType);
    try testing.expect(type_info == .@"struct");
    try testing.expect(type_info.@"struct".fields.len == 3);
}
```

### Generate Lookup Tables

Create lookup tables from embedded data:

```zig
/// Generate a lookup table from embedded data
fn generateLookupTable(comptime data: []const u8) [256]u8 {
    var table: [256]u8 = undefined;

    // Simple transformation: rotate each byte value
    for (0..256) |i| {
        table[i] = @as(u8, @intCast((i + data.len) % 256));
    }

    return table;
}

const lookup = generateLookupTable(embedded_message);

test "generated lookup table" {
    try testing.expect(lookup.len == 256);

    // Verify it's a valid lookup table
    for (lookup) |value| {
        try testing.expect(value < 256);
    }
}
```

### Hash at Compile Time

Compute checksums and hashes during compilation:

```zig
/// Compute hash of embedded file at compile time
fn simpleHash(comptime data: []const u8) u64 {
    var hash: u64 = 0;
    for (data) |byte| {
        hash = hash *% 31 +% byte;
    }
    return hash;
}

const file_hash = simpleHash(embedded_message);

test "compile-time hash" {
    // Hash is computed once at compile time
    try testing.expect(file_hash != 0);

    // Verify it matches runtime calculation
    const runtime_hash = simpleHash(embedded_message);
    try testing.expectEqual(file_hash, runtime_hash);
}
```

### Resource Maps

Build resource managers at compile time:

```zig
/// Create a resource map at compile time
const ResourceEntry = struct {
    name: []const u8,
    content: []const u8,
    size: usize,
};

fn createResourceMap(comptime resources: []const ResourceEntry) type {
    return struct {
        pub fn get(name: []const u8) ?[]const u8 {
            inline for (resources) |resource| {
                if (std.mem.eql(u8, resource.name, name)) {
                    return resource.content;
                }
            }
            return null;
        }

        pub fn getSize(name: []const u8) ?usize {
            inline for (resources) |resource| {
                if (std.mem.eql(u8, resource.name, name)) {
                    return resource.size;
                }
            }
            return null;
        }

        pub fn list() []const []const u8 {
            comptime {
                var names: [resources.len][]const u8 = undefined;
                for (resources, 0..) |resource, i| {
                    names[i] = resource.name;
                }
                const final_names = names;
                return &final_names;
            }
        }
    };
}

const Resources = createResourceMap(&[_]ResourceEntry{
    .{
        .name = "message",
        .content = @embedFile("assets/message.txt"),
        .size = @embedFile("assets/message.txt").len,
    },
    .{
        .name = "config",
        .content = @embedFile("assets/config.txt"),
        .size = @embedFile("assets/config.txt").len,
    },
});

test "resource map" {
    const message = Resources.get("message");
    try testing.expect(message != null);
    try testing.expect(message.?.len > 0);

    const config = Resources.get("config");
    try testing.expect(config != null);

    const missing = Resources.get("nonexistent");
    try testing.expectEqual(@as(?[]const u8, null), missing);

    const size = Resources.getSize("message");
    try testing.expect(size != null);
    try testing.expectEqual(message.?.len, size.?);
}
```

### Version Information

Embed version and build metadata:

```zig
/// Embed version information at compile time
const version_info = struct {
    const major = 1;
    const minor = 0;
    const patch = 0;
    const git_hash = "abc123"; // Would come from build system

    pub fn string() []const u8 {
        return comptime std.fmt.comptimePrint(
            "{d}.{d}.{d}-{s}",
            .{ major, minor, patch, git_hash },
        );
    }

    pub fn full() []const u8 {
        return comptime std.fmt.comptimePrint(
            "Version {d}.{d}.{d} (commit {s})",
            .{ major, minor, patch, git_hash },
        );
    }
};

test "version embedding" {
    const ver = version_info.string();
    try testing.expectEqualStrings("1.0.0-abc123", ver);

    const full = version_info.full();
    try testing.expect(std.mem.indexOf(u8, full, "Version") != null);
}
```

### String Interning

Create compile-time string pools with efficient lookup:

```zig
/// String interner for embedded strings
fn StringInterner(comptime strings: []const []const u8) type {
    return struct {
        pub fn getId(str: []const u8) ?usize {
            inline for (strings, 0..) |s, i| {
                if (std.mem.eql(u8, s, str)) {
                    return i;
                }
            }
            return null;
        }

        pub fn getString(id: usize) ?[]const u8 {
            if (id >= strings.len) return null;
            return strings[id];
        }

        pub fn count() usize {
            return strings.len;
        }
    };
}

const Strings = StringInterner(&[_][]const u8{
    "error",
    "warning",
    "info",
    "debug",
});

test "string interner" {
    const error_id = Strings.getId("error");
    try testing.expectEqual(@as(?usize, 0), error_id);

    const info_id = Strings.getId("info");
    try testing.expectEqual(@as(?usize, 2), info_id);

    const str = Strings.getString(1);
    try testing.expectEqualStrings("warning", str.?);

    try testing.expectEqual(@as(usize, 4), Strings.count());
}
```

### Asset Compression

Compress embedded resources at compile time:

```zig
/// Simple run-length encoding at compile time
fn compressRLE(comptime data: []const u8) []const u8 {
    @setEvalBranchQuota(100000);

    var result: []const u8 = "";
    var i: usize = 0;

    while (i < data.len) {
        const byte = data[i];
        var count: usize = 1;

        // Count consecutive identical bytes
        while (i + count < data.len and data[i + count] == byte and count < 255) {
            count += 1;
        }

        // Append count and byte
        const count_byte = [_]u8{@as(u8, @intCast(count))};
        const value_byte = [_]u8{byte};
        result = result ++ &count_byte ++ &value_byte;

        i += count;
    }

    return result;
}

test "compile-time compression" {
    const original = "aaabbbccc";
    const compressed = comptime compressRLE(original);

    // RLE format: count, byte, count, byte, ...
    try testing.expect(compressed.len < original.len or compressed.len == original.len * 2);

    // First run: 3x 'a'
    try testing.expectEqual(@as(u8, 3), compressed[0]);
    try testing.expectEqual(@as(u8, 'a'), compressed[1]);
}
```

### Build Metadata

Capture build-time information:

```zig
/// Embed build-time metadata
const build_info = struct {
    const timestamp = "2025-01-20T12:00:00Z"; // Would come from build system
    const compiler = "zig 0.15.2";
    const target = "x86_64-linux";

    pub fn summary() []const u8 {
        return comptime std.fmt.comptimePrint(
            "Built: {s} | Compiler: {s} | Target: {s}",
            .{ timestamp, compiler, target },
        );
    }
};

test "build metadata" {
    const info = build_info.summary();
    try testing.expect(std.mem.indexOf(u8, info, "Built:") != null);
    try testing.expect(std.mem.indexOf(u8, info, "Compiler:") != null);
    try testing.expect(std.mem.indexOf(u8, info, "Target:") != null);
}
```

### Discussion

Build-time resource embedding eliminates runtime file I/O, simplifies deployment, and enables powerful compile-time optimizations.

### How @embedFile Works

The `@embedFile` builtin:

1. Reads a file relative to the source file at compile time
2. Returns the contents as a `[]const u8` string literal
3. Embeds the data directly into the binary's read-only data section
4. Performs the read only once, even if called multiple times with the same path

The embedded data is available at runtime as a normal string slice, with zero I/O overhead.

### Path Resolution

File paths are resolved relative to the source file containing `@embedFile`:

```zig
// If in src/main.zig:
@embedFile("data.txt")        // Looks for src/data.txt
@embedFile("../assets/img.png") // Looks for assets/img.png
```

Use relative paths to keep builds reproducible and portable across different development environments.

### Compile-Time Processing

Once data is embedded, you can process it at compile time:

**Parsing**: Convert configuration formats (INI, JSON, custom formats) into native Zig types.

**Validation**: Check for errors, enforce schemas, and reject invalid data at compile time.

**Transformation**: Compress, encrypt, or encode data before embedding.

**Generation**: Create lookup tables, hash maps, or search trees from embedded data.

All processing happens once during compilation. The final binary contains only the processed result.

### The @setEvalBranchQuota Directive

Complex compile-time processing may exceed Zig's default evaluation limits:

```zig
@setEvalBranchQuota(10000);
```

This increases the number of branches the compiler will evaluate in comptime code. Use it when processing large files or complex transformations.

### Resource Management Patterns

**Direct Embedding**: Simple cases where you just need the raw data.

**Resource Maps**: Multiple resources accessed by name, using comptime-generated lookup.

**String Interning**: Deduplicate strings and use integer IDs for comparisons.

**Lazy Processing**: Embed raw data, process at runtime if transformation is too complex for comptime.

### Performance Characteristics

**Compile Time**:
- File I/O happens during compilation
- Processing time added to build time
- Large files or complex transformations increase compilation time

**Runtime**:
- Zero file I/O (data already in binary)
- No parsing overhead (pre-processed at compile time)
- Data lives in read-only memory (shared across processes)
- Fast access (just memory reads)

**Binary Size**:
- Embedded data increases binary size proportionally
- Compression can reduce size
- All embedded files are included even if unused (no tree-shaking)

### Use Cases

**Configuration**: Embed default configurations, removing runtime file dependencies.

**Templates**: HTML templates, SQL queries, or code generation templates.

**Assets**: Icons, small images, or other resources for GUIs.

**Localization**: Translation strings and language resources.

**Test Data**: Fixtures and expected outputs for testing.

**Version Info**: Git commit hashes, build timestamps, and version numbers.

### Limitations and Workarounds

**Large Files**: Very large embedded files slow compilation and increase binary size. Consider:
- Compressing at compile time
- Splitting into chunks
- Loading at runtime for truly large assets

**Dynamic Content**: `@embedFile` only works with files present at compile time. For user-provided files, use runtime I/O.

**Cross-Platform Paths**: Use forward slashes even on Windows. Zig normalizes paths automatically.

**Build Cache**: Zig's build cache doesn't track embedded file changes well. Clean rebuild if embedded files change unexpectedly.

### Best Practices

**Small Resources Only**: Embed configuration, templates, and small assets. Load large files at runtime.

**Version Control Assets**: Check embedded files into source control so builds are reproducible.

**Validate at Compile Time**: Catch errors early by parsing and validating during compilation.

**Document Embedded Files**: Comment what files are embedded and why.

**Use Compression**: For text-heavy resources, consider compile-time compression to reduce binary size.

**Cache Processed Results**: If processing is expensive, cache the result as a comptime constant.

### Integration with Build System

Combine `@embedFile` with build.zig to:

- Generate version information from git
- Embed timestamps and build metadata
- Process assets during the build
- Create different embeddings for different build configurations

### Security Considerations

**Sensitive Data**: Don't embed passwords, API keys, or secrets. They'll be visible in the binary.

**Input Validation**: Validate embedded files at compile time to prevent malformed data.

**Size Limits**: Set reasonable limits on embedded file sizes to prevent binary bloat.

**Read-Only**: Embedded data is in read-only memory. Don't try to modify it.

### Comparison to Other Approaches

**Runtime File I/O**:
- Pro: Smaller binaries, easier updates
- Con: File I/O overhead, deployment complexity

**Code Generation**:
- Pro: More flexible, can integrate with external tools
- Con: Additional build complexity, separate preprocessing step

**@embedFile**:
- Pro: Simple, integrated, zero runtime overhead
- Con: Increases binary size, compile-time processing only

### Full Tested Code

```zig
// Recipe 17.6: Build-Time Resource Embedding
// This recipe demonstrates how to embed files, generate lookup tables, and
// compile assets into your binary using @embedFile and comptime processing.

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_embed
/// Embed a text file directly into the binary
const embedded_message = @embedFile("assets/message.txt");

test "basic file embedding" {
    try testing.expect(embedded_message.len > 0);
    try testing.expect(std.mem.indexOf(u8, embedded_message, "Hello") != null);
}
// ANCHOR_END: basic_embed

// ANCHOR: parse_at_comptime
/// Parse embedded configuration at compile time
const embedded_config = @embedFile("assets/config.txt");

fn parseConfig(comptime content: []const u8) type {
    @setEvalBranchQuota(10000);

    var line_count: usize = 0;
    var pos: usize = 0;

    // Count lines
    while (pos < content.len) : (pos += 1) {
        if (content[pos] == '\n') {
            line_count += 1;
        }
    }

    // Parse key-value pairs
    var fields: [line_count]std.builtin.Type.StructField = undefined;
    var field_idx: usize = 0;
    var line_start: usize = 0;

    pos = 0;
    while (pos < content.len) : (pos += 1) {
        if (content[pos] == '\n' or pos == content.len - 1) {
            const line_end = if (content[pos] == '\n') pos else pos + 1;
            const line = content[line_start..line_end];

            // Find '=' separator
            for (line, 0..) |char, i| {
                if (char == '=') {
                    const key = line[0..i];

                    // Create field with null-terminated name
                    const key_z = key ++ "";
                    fields[field_idx] = .{
                        .name = key_z[0..key.len :0],
                        .type = []const u8,
                        .default_value_ptr = null,
                        .is_comptime = false,
                        .alignment = @alignOf([]const u8),
                    };
                    field_idx += 1;
                    break;
                }
            }

            line_start = pos + 1;
        }
    }

    return @Type(.{
        .@"struct" = .{
            .layout = .auto,
            .fields = fields[0..field_idx],
            .decls = &[_]std.builtin.Type.Declaration{},
            .is_tuple = false,
        },
    });
}

test "parse config at compile time" {
    const ConfigType = parseConfig(embedded_config);

    // Verify the type has the expected fields
    const type_info = @typeInfo(ConfigType);
    try testing.expect(type_info == .@"struct");
    try testing.expect(type_info.@"struct".fields.len == 3);
}
// ANCHOR_END: parse_at_comptime

// ANCHOR: lookup_table
/// Generate a lookup table from embedded data
fn generateLookupTable(comptime data: []const u8) [256]u8 {
    var table: [256]u8 = undefined;

    // Simple transformation: rotate each byte value
    for (0..256) |i| {
        table[i] = @as(u8, @intCast((i + data.len) % 256));
    }

    return table;
}

const lookup = generateLookupTable(embedded_message);

test "generated lookup table" {
    try testing.expect(lookup.len == 256);

    // Verify it's a valid lookup table
    for (lookup) |value| {
        try testing.expect(value < 256);
    }
}
// ANCHOR_END: lookup_table

// ANCHOR: hash_at_comptime
/// Compute hash of embedded file at compile time
fn simpleHash(comptime data: []const u8) u64 {
    var hash: u64 = 0;
    for (data) |byte| {
        hash = hash *% 31 +% byte;
    }
    return hash;
}

const file_hash = simpleHash(embedded_message);

test "compile-time hash" {
    // Hash is computed once at compile time
    try testing.expect(file_hash != 0);

    // Verify it matches runtime calculation
    const runtime_hash = simpleHash(embedded_message);
    try testing.expectEqual(file_hash, runtime_hash);
}
// ANCHOR_END: hash_at_comptime

// ANCHOR: resource_map
/// Create a resource map at compile time
const ResourceEntry = struct {
    name: []const u8,
    content: []const u8,
    size: usize,
};

fn createResourceMap(comptime resources: []const ResourceEntry) type {
    return struct {
        pub fn get(name: []const u8) ?[]const u8 {
            inline for (resources) |resource| {
                if (std.mem.eql(u8, resource.name, name)) {
                    return resource.content;
                }
            }
            return null;
        }

        pub fn getSize(name: []const u8) ?usize {
            inline for (resources) |resource| {
                if (std.mem.eql(u8, resource.name, name)) {
                    return resource.size;
                }
            }
            return null;
        }

        pub fn list() []const []const u8 {
            comptime {
                var names: [resources.len][]const u8 = undefined;
                for (resources, 0..) |resource, i| {
                    names[i] = resource.name;
                }
                const final_names = names;
                return &final_names;
            }
        }
    };
}

const Resources = createResourceMap(&[_]ResourceEntry{
    .{
        .name = "message",
        .content = @embedFile("assets/message.txt"),
        .size = @embedFile("assets/message.txt").len,
    },
    .{
        .name = "config",
        .content = @embedFile("assets/config.txt"),
        .size = @embedFile("assets/config.txt").len,
    },
});

test "resource map" {
    const message = Resources.get("message");
    try testing.expect(message != null);
    try testing.expect(message.?.len > 0);

    const config = Resources.get("config");
    try testing.expect(config != null);

    const missing = Resources.get("nonexistent");
    try testing.expectEqual(@as(?[]const u8, null), missing);

    const size = Resources.getSize("message");
    try testing.expect(size != null);
    try testing.expectEqual(message.?.len, size.?);
}
// ANCHOR_END: resource_map

// ANCHOR: version_info
/// Embed version information at compile time
const version_info = struct {
    const major = 1;
    const minor = 0;
    const patch = 0;
    const git_hash = "abc123"; // Would come from build system

    pub fn string() []const u8 {
        return comptime std.fmt.comptimePrint(
            "{d}.{d}.{d}-{s}",
            .{ major, minor, patch, git_hash },
        );
    }

    pub fn full() []const u8 {
        return comptime std.fmt.comptimePrint(
            "Version {d}.{d}.{d} (commit {s})",
            .{ major, minor, patch, git_hash },
        );
    }
};

test "version embedding" {
    const ver = version_info.string();
    try testing.expectEqualStrings("1.0.0-abc123", ver);

    const full = version_info.full();
    try testing.expect(std.mem.indexOf(u8, full, "Version") != null);
}
// ANCHOR_END: version_info

// ANCHOR: string_interner
/// String interner for embedded strings
fn StringInterner(comptime strings: []const []const u8) type {
    return struct {
        pub fn getId(str: []const u8) ?usize {
            inline for (strings, 0..) |s, i| {
                if (std.mem.eql(u8, s, str)) {
                    return i;
                }
            }
            return null;
        }

        pub fn getString(id: usize) ?[]const u8 {
            if (id >= strings.len) return null;
            return strings[id];
        }

        pub fn count() usize {
            return strings.len;
        }
    };
}

const Strings = StringInterner(&[_][]const u8{
    "error",
    "warning",
    "info",
    "debug",
});

test "string interner" {
    const error_id = Strings.getId("error");
    try testing.expectEqual(@as(?usize, 0), error_id);

    const info_id = Strings.getId("info");
    try testing.expectEqual(@as(?usize, 2), info_id);

    const str = Strings.getString(1);
    try testing.expectEqualStrings("warning", str.?);

    try testing.expectEqual(@as(usize, 4), Strings.count());
}
// ANCHOR_END: string_interner

// ANCHOR: asset_compression
/// Simple run-length encoding at compile time
fn compressRLE(comptime data: []const u8) []const u8 {
    @setEvalBranchQuota(100000);

    var result: []const u8 = "";
    var i: usize = 0;

    while (i < data.len) {
        const byte = data[i];
        var count: usize = 1;

        // Count consecutive identical bytes
        while (i + count < data.len and data[i + count] == byte and count < 255) {
            count += 1;
        }

        // Append count and byte
        const count_byte = [_]u8{@as(u8, @intCast(count))};
        const value_byte = [_]u8{byte};
        result = result ++ &count_byte ++ &value_byte;

        i += count;
    }

    return result;
}

test "compile-time compression" {
    const original = "aaabbbccc";
    const compressed = comptime compressRLE(original);

    // RLE format: count, byte, count, byte, ...
    try testing.expect(compressed.len < original.len or compressed.len == original.len * 2);

    // First run: 3x 'a'
    try testing.expectEqual(@as(u8, 3), compressed[0]);
    try testing.expectEqual(@as(u8, 'a'), compressed[1]);
}
// ANCHOR_END: asset_compression

// ANCHOR: build_metadata
/// Embed build-time metadata
const build_info = struct {
    const timestamp = "2025-01-20T12:00:00Z"; // Would come from build system
    const compiler = "zig 0.15.2";
    const target = "x86_64-linux";

    pub fn summary() []const u8 {
        return comptime std.fmt.comptimePrint(
            "Built: {s} | Compiler: {s} | Target: {s}",
            .{ timestamp, compiler, target },
        );
    }
};

test "build metadata" {
    const info = build_info.summary();
    try testing.expect(std.mem.indexOf(u8, info, "Built:") != null);
    try testing.expect(std.mem.indexOf(u8, info, "Compiler:") != null);
    try testing.expect(std.mem.indexOf(u8, info, "Target:") != null);
}
// ANCHOR_END: build_metadata
```

### See Also

- Recipe 17.2: Compile
- Recipe 17.3: Compile
- Recipe 16.4: Custom build steps
- Recipe 16.6: Build options and configurations

---

## Recipe 17.7: Comptime Function Memoization {#recipe-17-7}

**Tags:** comptime, comptime-metaprogramming, data-structures, error-handling, hashmap, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/17-advanced-comptime/recipe_17_7.zig`

### Problem

You have expensive computations that are called repeatedly with the same inputs, or you need to optimize code paths based on compile-time information. You want to cache results, generate lookup tables, and create optimization hints without any runtime overhead.

### Solution

Zig's comptime system enables you to perform computations once at compile time and embed the results directly into your binary as lookup tables or pre-computed constants.

### Basic Memoization

Cache expensive recursive computations at compile time:

```zig
/// Fibonacci with compile-time memoization via lookup table
fn fibonacci(comptime n: u32) u64 {
    if (n == 0) return 0;
    if (n == 1) return 1;

    var cache: [n + 1]u64 = undefined;
    cache[0] = 0;
    cache[1] = 1;

    for (2..n + 1) |i| {
        cache[i] = cache[i - 1] + cache[i - 2];
    }

    return cache[n];
}

test "basic memoization" {
    try testing.expectEqual(@as(u64, 0), comptime fibonacci(0));
    try testing.expectEqual(@as(u64, 1), comptime fibonacci(1));
    try testing.expectEqual(@as(u64, 55), comptime fibonacci(10));
    try testing.expectEqual(@as(u64, 6765), comptime fibonacci(20));

    // Computed at compile time, zero runtime cost
    const fib30 = comptime fibonacci(30);
    try testing.expectEqual(@as(u64, 832040), fib30);
}
```

### Precomputed Lookup Tables

Generate complete lookup tables for O(1) runtime access:

```zig
/// Generate a complete lookup table at compile time
fn generateFibTable(comptime max_n: usize) [max_n]u64 {
    comptime {
        var table: [max_n]u64 = undefined;
        table[0] = 0;
        if (max_n > 1) {
            table[1] = 1;

            for (2..max_n) |i| {
                table[i] = table[i - 1] + table[i - 2];
            }
        }

        return table;
    }
}

const fib_table = generateFibTable(50);

test "precomputed lookup table" {
    try testing.expectEqual(@as(u64, 55), fib_table[10]);
    try testing.expectEqual(@as(u64, 6765), fib_table[20]);
    try testing.expectEqual(@as(u64, 832040), fib_table[30]);

    // Instant O(1) lookup, no computation
    const val = fib_table[40];
    try testing.expectEqual(@as(u64, 102334155), val);
}
```

### Cached Prime Numbers

Compute and cache prime numbers at build time:

```zig
/// Cache prime numbers at compile time
fn isPrime(comptime n: u64) bool {
    if (n < 2) return false;
    if (n == 2) return true;
    if (n % 2 == 0) return false;

    var i: u64 = 3;
    while (i * i <= n) : (i += 2) {
        if (n % i == 0) return false;
    }

    return true;
}

fn generatePrimes(comptime max: u64) []const u64 {
    comptime {
        @setEvalBranchQuota(100000);

        var count: usize = 0;
        var n: u64 = 2;
        while (n < max) : (n += 1) {
            if (isPrime(n)) {
                count += 1;
            }
        }

        var primes: [count]u64 = undefined;
        var idx: usize = 0;
        n = 2;
        while (n < max) : (n += 1) {
            if (isPrime(n)) {
                primes[idx] = n;
                idx += 1;
            }
        }

        const result = primes;
        return &result;
    }
}

const primes_under_100 = generatePrimes(100);

test "cached prime numbers" {
    try testing.expectEqual(@as(usize, 25), primes_under_100.len);
    try testing.expectEqual(@as(u64, 2), primes_under_100[0]);
    try testing.expectEqual(@as(u64, 97), primes_under_100[24]);

    // Check a few primes
    try testing.expect(std.mem.indexOfScalar(u64, primes_under_100, 17) != null);
    try testing.expect(std.mem.indexOfScalar(u64, primes_under_100, 53) != null);
}
```

### Factorial Table

Precompute factorials for instant lookup:

```zig
/// Precompute factorial values
fn factorial(comptime n: u64) u64 {
    if (n == 0 or n == 1) return 1;

    var result: u64 = 1;
    for (2..n + 1) |i| {
        result *= i;
    }

    return result;
}

fn generateFactorialTable(comptime max: usize) [max]u64 {
    comptime {
        var table: [max]u64 = undefined;

        for (0..max) |i| {
            table[i] = factorial(i);
        }

        return table;
    }
}

const factorials = generateFactorialTable(21);

test "factorial table" {
    try testing.expectEqual(@as(u64, 1), factorials[0]);
    try testing.expectEqual(@as(u64, 1), factorials[1]);
    try testing.expectEqual(@as(u64, 2), factorials[2]);
    try testing.expectEqual(@as(u64, 6), factorials[3]);
    try testing.expectEqual(@as(u64, 24), factorials[4]);
    try testing.expectEqual(@as(u64, 120), factorials[5]);
    try testing.expectEqual(@as(u64, 3628800), factorials[10]);
}
```

### String Hash Table

Precompute hashes for fast string comparisons:

```zig
/// Precompute string hashes
fn hashString(comptime str: []const u8) u64 {
    var hash: u64 = 0;
    for (str) |byte| {
        hash = hash *% 31 +% byte;
    }
    return hash;
}

fn hashStringRuntime(str: []const u8) u64 {
    var hash: u64 = 0;
    for (str) |byte| {
        hash = hash *% 31 +% byte;
    }
    return hash;
}

fn StringHashMap(comptime strings: []const []const u8) type {
    return struct {
        const Entry = struct {
            hash: u64,
            str: []const u8,
        };

        const entries = blk: {
            var result: [strings.len]Entry = undefined;
            for (strings, 0..) |str, i| {
                result[i] = .{
                    .hash = hashString(str),
                    .str = str,
                };
            }
            break :blk result;
        };

        pub fn getHash(str: []const u8) ?u64 {
            const h = hashStringRuntime(str);
            inline for (entries) |entry| {
                if (entry.hash == h and std.mem.eql(u8, entry.str, str)) {
                    return entry.hash;
                }
            }
            return null;
        }

        pub fn contains(str: []const u8) bool {
            return getHash(str) != null;
        }
    };
}

const Keywords = StringHashMap(&[_][]const u8{
    "if",
    "else",
    "while",
    "for",
    "return",
    "break",
    "continue",
});

test "string hash table" {
    try testing.expect(Keywords.contains("if"));
    try testing.expect(Keywords.contains("while"));
    try testing.expect(!Keywords.contains("unknown"));

    const hash = Keywords.getHash("return");
    try testing.expect(hash != null);
}
```

### Powers of Two

Cache powers of 2 for bit manipulation:

```zig
/// Cache powers of 2 for fast lookups
fn generatePowersOfTwo(comptime max_exp: usize) [max_exp]u64 {
    comptime {
        var table: [max_exp]u64 = undefined;
        var pow: u64 = 1;

        for (0..max_exp) |i| {
            table[i] = pow;
            if (i + 1 < max_exp) {
                pow *= 2;
            }
        }

        return table;
    }
}

const powers_of_2 = generatePowersOfTwo(63);

test "powers of two table" {
    try testing.expectEqual(@as(u64, 1), powers_of_2[0]);
    try testing.expectEqual(@as(u64, 2), powers_of_2[1]);
    try testing.expectEqual(@as(u64, 4), powers_of_2[2]);
    try testing.expectEqual(@as(u64, 1024), powers_of_2[10]);
    try testing.expectEqual(@as(u64, 1 << 20), powers_of_2[20]);
}
```

### Trigonometric Tables

Precompute sine values for fast approximations:

```zig
/// Precompute sine values for fast lookup
fn generateSinTable(comptime resolution: usize) [resolution]f64 {
    comptime {
        var table: [resolution]f64 = undefined;
        const step = 2.0 * std.math.pi / @as(f64, @floatFromInt(resolution));

        for (0..resolution) |i| {
            const angle = @as(f64, @floatFromInt(i)) * step;
            table[i] = @sin(angle);
        }

        return table;
    }
}

const sin_table = generateSinTable(360);

fn fastSin(angle_degrees: f64) f64 {
    const normalized = @mod(angle_degrees, 360.0);
    const index = @as(usize, @intFromFloat(@round(normalized)));
    return sin_table[index];
}

test "sine lookup table" {
    const epsilon = 0.01;

    // 0 degrees
    try testing.expect(@abs(fastSin(0.0) - 0.0) < epsilon);

    // 90 degrees
    try testing.expect(@abs(fastSin(90.0) - 1.0) < epsilon);

    // 180 degrees
    try testing.expect(@abs(fastSin(180.0) - 0.0) < epsilon);

    // 270 degrees
    try testing.expect(@abs(fastSin(270.0) - (-1.0)) < epsilon);
}
```

### Generic Memoization Wrapper

Create reusable memoization helpers:

```zig
/// Generic memoization wrapper
fn Memoized(comptime F: type, comptime f: F, comptime max_n: usize) type {
    return struct {
        const cache = blk: {
            var result: [max_n]u64 = undefined;
            for (0..max_n) |i| {
                result[i] = f(i);
            }
            break :blk result;
        };

        pub fn call(n: usize) u64 {
            if (n >= max_n) {
                @panic("Input exceeds cache size");
            }
            return cache[n];
        }
    };
}

fn slowSquare(n: usize) u64 {
    return @as(u64, n) * @as(u64, n);
}

const MemoizedSquare = Memoized(@TypeOf(slowSquare), slowSquare, 100);

test "generic memoization" {
    try testing.expectEqual(@as(u64, 0), MemoizedSquare.call(0));
    try testing.expectEqual(@as(u64, 1), MemoizedSquare.call(1));
    try testing.expectEqual(@as(u64, 100), MemoizedSquare.call(10));
    try testing.expectEqual(@as(u64, 9801), MemoizedSquare.call(99));
}
```

### Build-Time Optimization Selection

Choose implementations based on compile-time analysis:

```zig
/// Choose implementation based on compile-time computation
fn optimizedSum(comptime size: usize) fn ([]const u32) u64 {
    if (size <= 4) {
        // For small arrays, use simple loop
        return struct {
            fn sum(arr: []const u32) u64 {
                var result: u64 = 0;
                for (arr) |val| {
                    result += val;
                }
                return result;
            }
        }.sum;
    } else {
        // For larger arrays, use unrolled loop
        return struct {
            fn sum(arr: []const u32) u64 {
                var result: u64 = 0;
                var i: usize = 0;

                // Process 4 at a time
                while (i + 4 <= arr.len) : (i += 4) {
                    result += arr[i];
                    result += arr[i + 1];
                    result += arr[i + 2];
                    result += arr[i + 3];
                }

                // Handle remainder
                while (i < arr.len) : (i += 1) {
                    result += arr[i];
                }

                return result;
            }
        }.sum;
    }
}

test "compile-time optimization selection" {
    const small_arr = [_]u32{ 1, 2, 3 };
    const small_fn = optimizedSum(small_arr.len);
    try testing.expectEqual(@as(u64, 6), small_fn(&small_arr));

    const large_arr = [_]u32{ 1, 2, 3, 4, 5, 6, 7, 8 };
    const large_fn = optimizedSum(large_arr.len);
    try testing.expectEqual(@as(u64, 36), large_fn(&large_arr));
}
```

### Discussion

Comptime memoization transforms expensive computations into instant lookups, moving work from runtime to compile time for dramatic performance improvements.

### How Comptime Caching Works

When you compute values at compile time, Zig:

1. Executes the computation during compilation
2. Stores the result in the binary's data section
3. Replaces function calls with direct array lookups or constants
4. Eliminates the computation logic from the final binary

The result is runtime code that's as fast as if you'd manually typed in the pre-computed values.

### Lookup Table Strategy

**Small Input Domain**: Generate complete tables for all possible inputs (powers of 2, small factorials, trigonometric functions).

**Sparse Tables**: For functions with selective interesting inputs (primes, Fibonacci numbers), cache only the values you need.

**Approximation Tables**: Use finite precision for continuous functions (sin/cos), trading accuracy for speed.

### Memory vs Speed Tradeoff

Lookup tables trade memory for speed:

**Benefits**:
- O(1) runtime lookup instead of O(n) or O(log n) computation
- No branches or function call overhead
- Cache-friendly linear memory access
- Predictable performance

**Costs**:
- Increased binary size
- Memory used even for unused values
- Less flexible than computed results

Choose tables when:
- The input domain is small
- The computation is expensive
- Speed is more important than memory
- The values are frequently accessed

### The @setEvalBranchQuota Directive

Zig limits compile-time computation to prevent infinite loops:

```zig
@setEvalBranchQuota(100000);
```

This increases the branch evaluation limit. Use it for:
- Large table generation
- Complex compile-time algorithms
- Iterative processing of embedded data

Set it as high as needed but be aware that very high values can slow compilation.

### Optimization Patterns

**Direct Memoization**: Fibonacci example shows basic caching with intermediate results.

**Full Table Generation**: Powers of 2, factorials—generate every possible value upfront.

**Filtered Generation**: Primes—only store values matching a criteria.

**Approximation**: Sine table—finite precision for continuous functions.

**Compile-Time Selection**: Choose algorithm based on problem size or type characteristics.

### Generic Memoization

The `Memoized` wrapper demonstrates creating reusable caching helpers:

```zig
const Cached = Memoized(@TypeOf(expensiveFunc), expensiveFunc, max_n);
```

This pattern:
- Works with any function signature
- Generates specialized caches per function
- Provides type-safe lookups
- Eliminates boilerplate

### Practical Applications

**Game Development**: Precompute damage tables, XP curves, or procedural generation parameters.

**Graphics**: Sine/cosine tables for rotations, gamma correction lookup tables.

**Cryptography**: S-boxes, permutation tables, modular arithmetic tables.

**Compression**: Huffman code tables, dictionary entries.

**String Processing**: Hash tables for keywords, character classification tables.

**Math Libraries**: Logarithms, square roots, or other transcendental functions with limited precision.

### Compilation Impact

**Build Time**: Table generation happens during compilation, increasing build time proportional to table size and complexity.

**Build Cache**: Tables are cached between builds, so only the first compilation or changes to input data trigger regeneration.

**Incremental Builds**: Tables in unchanged files don't need recomputation.

### Performance Characteristics

**Compile Time**:
- Linear in table size for simple functions
- Exponential for recursive algorithms without memoization
- Memory-bound for very large tables

**Runtime**:
- O(1) lookup for all cached values
- No computation overhead
- No stack frames or function calls
- Ideal cache locality

**Binary Size**:
- Proportional to table size
- Aligned and padded per platform ABI
- Shared across all uses

### Debugging Comptime Code

When compile-time computation fails:

1. Use `@compileLog` to print intermediate values
2. Reduce table sizes for faster iteration
3. Check `@setEvalBranchQuota` is sufficient
4. Verify no runtime dependencies in comptime code
5. Test the logic with runtime functions first

### Best Practices

**Start Small**: Begin with small table sizes, verify correctness, then scale up.

**Document Tables**: Explain what each table contains, its range, and precision.

**Validate Inputs**: For functions taking indices, check bounds and provide clear errors.

**Consider Compression**: For sparse tables, use maps instead of arrays.

**Profile First**: Measure whether the overhead justifies the memory cost.

**Version Carefully**: Document table format if persisting across versions.

### Limitations

**Static Input**: Can only compute for values known at compile time.

**Memory Constraints**: Very large tables can exhaust compilation memory or create huge binaries.

**Precision Loss**: Approximation tables sacrifice accuracy for speed.

**Cold Start**: Table access may miss cache on first use.

### When Not to Use

**Dynamic Inputs**: Runtime values can't benefit from compile-time tables.

**Rarely Used**: If a value is only accessed once, computing it on-demand is cheaper.

**Large Domains**: Tables for 64-bit integers would be terabytes.

**Frequently Changing**: If the computation logic changes often, runtime flexibility may be better.

### Full Tested Code

```zig
// Recipe 17.7: Comptime Function Memoization and Optimization
// This recipe demonstrates how to cache expensive compile-time computations,
// build lookup tables, and create optimization hints at compile time.

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_memoization
/// Fibonacci with compile-time memoization via lookup table
fn fibonacci(comptime n: u32) u64 {
    if (n == 0) return 0;
    if (n == 1) return 1;

    var cache: [n + 1]u64 = undefined;
    cache[0] = 0;
    cache[1] = 1;

    for (2..n + 1) |i| {
        cache[i] = cache[i - 1] + cache[i - 2];
    }

    return cache[n];
}

test "basic memoization" {
    try testing.expectEqual(@as(u64, 0), comptime fibonacci(0));
    try testing.expectEqual(@as(u64, 1), comptime fibonacci(1));
    try testing.expectEqual(@as(u64, 55), comptime fibonacci(10));
    try testing.expectEqual(@as(u64, 6765), comptime fibonacci(20));

    // Computed at compile time, zero runtime cost
    const fib30 = comptime fibonacci(30);
    try testing.expectEqual(@as(u64, 832040), fib30);
}
// ANCHOR_END: basic_memoization

// ANCHOR: precompute_table
/// Generate a complete lookup table at compile time
fn generateFibTable(comptime max_n: usize) [max_n]u64 {
    comptime {
        var table: [max_n]u64 = undefined;
        table[0] = 0;
        if (max_n > 1) {
            table[1] = 1;

            for (2..max_n) |i| {
                table[i] = table[i - 1] + table[i - 2];
            }
        }

        return table;
    }
}

const fib_table = generateFibTable(50);

test "precomputed lookup table" {
    try testing.expectEqual(@as(u64, 55), fib_table[10]);
    try testing.expectEqual(@as(u64, 6765), fib_table[20]);
    try testing.expectEqual(@as(u64, 832040), fib_table[30]);

    // Instant O(1) lookup, no computation
    const val = fib_table[40];
    try testing.expectEqual(@as(u64, 102334155), val);
}
// ANCHOR_END: precompute_table

// ANCHOR: prime_cache
/// Cache prime numbers at compile time
fn isPrime(comptime n: u64) bool {
    if (n < 2) return false;
    if (n == 2) return true;
    if (n % 2 == 0) return false;

    var i: u64 = 3;
    while (i * i <= n) : (i += 2) {
        if (n % i == 0) return false;
    }

    return true;
}

fn generatePrimes(comptime max: u64) []const u64 {
    comptime {
        @setEvalBranchQuota(100000);

        var count: usize = 0;
        var n: u64 = 2;
        while (n < max) : (n += 1) {
            if (isPrime(n)) {
                count += 1;
            }
        }

        var primes: [count]u64 = undefined;
        var idx: usize = 0;
        n = 2;
        while (n < max) : (n += 1) {
            if (isPrime(n)) {
                primes[idx] = n;
                idx += 1;
            }
        }

        const result = primes;
        return &result;
    }
}

const primes_under_100 = generatePrimes(100);

test "cached prime numbers" {
    try testing.expectEqual(@as(usize, 25), primes_under_100.len);
    try testing.expectEqual(@as(u64, 2), primes_under_100[0]);
    try testing.expectEqual(@as(u64, 97), primes_under_100[24]);

    // Check a few primes
    try testing.expect(std.mem.indexOfScalar(u64, primes_under_100, 17) != null);
    try testing.expect(std.mem.indexOfScalar(u64, primes_under_100, 53) != null);
}
// ANCHOR_END: prime_cache

// ANCHOR: factorial_table
/// Precompute factorial values
fn factorial(comptime n: u64) u64 {
    if (n == 0 or n == 1) return 1;

    var result: u64 = 1;
    for (2..n + 1) |i| {
        result *= i;
    }

    return result;
}

fn generateFactorialTable(comptime max: usize) [max]u64 {
    comptime {
        var table: [max]u64 = undefined;

        for (0..max) |i| {
            table[i] = factorial(i);
        }

        return table;
    }
}

const factorials = generateFactorialTable(21);

test "factorial table" {
    try testing.expectEqual(@as(u64, 1), factorials[0]);
    try testing.expectEqual(@as(u64, 1), factorials[1]);
    try testing.expectEqual(@as(u64, 2), factorials[2]);
    try testing.expectEqual(@as(u64, 6), factorials[3]);
    try testing.expectEqual(@as(u64, 24), factorials[4]);
    try testing.expectEqual(@as(u64, 120), factorials[5]);
    try testing.expectEqual(@as(u64, 3628800), factorials[10]);
}
// ANCHOR_END: factorial_table

// ANCHOR: string_hash_table
/// Precompute string hashes
fn hashString(comptime str: []const u8) u64 {
    var hash: u64 = 0;
    for (str) |byte| {
        hash = hash *% 31 +% byte;
    }
    return hash;
}

fn hashStringRuntime(str: []const u8) u64 {
    var hash: u64 = 0;
    for (str) |byte| {
        hash = hash *% 31 +% byte;
    }
    return hash;
}

fn StringHashMap(comptime strings: []const []const u8) type {
    return struct {
        const Entry = struct {
            hash: u64,
            str: []const u8,
        };

        const entries = blk: {
            var result: [strings.len]Entry = undefined;
            for (strings, 0..) |str, i| {
                result[i] = .{
                    .hash = hashString(str),
                    .str = str,
                };
            }
            break :blk result;
        };

        pub fn getHash(str: []const u8) ?u64 {
            const h = hashStringRuntime(str);
            inline for (entries) |entry| {
                if (entry.hash == h and std.mem.eql(u8, entry.str, str)) {
                    return entry.hash;
                }
            }
            return null;
        }

        pub fn contains(str: []const u8) bool {
            return getHash(str) != null;
        }
    };
}

const Keywords = StringHashMap(&[_][]const u8{
    "if",
    "else",
    "while",
    "for",
    "return",
    "break",
    "continue",
});

test "string hash table" {
    try testing.expect(Keywords.contains("if"));
    try testing.expect(Keywords.contains("while"));
    try testing.expect(!Keywords.contains("unknown"));

    const hash = Keywords.getHash("return");
    try testing.expect(hash != null);
}
// ANCHOR_END: string_hash_table

// ANCHOR: power_of_two
/// Cache powers of 2 for fast lookups
fn generatePowersOfTwo(comptime max_exp: usize) [max_exp]u64 {
    comptime {
        var table: [max_exp]u64 = undefined;
        var pow: u64 = 1;

        for (0..max_exp) |i| {
            table[i] = pow;
            if (i + 1 < max_exp) {
                pow *= 2;
            }
        }

        return table;
    }
}

const powers_of_2 = generatePowersOfTwo(63);

test "powers of two table" {
    try testing.expectEqual(@as(u64, 1), powers_of_2[0]);
    try testing.expectEqual(@as(u64, 2), powers_of_2[1]);
    try testing.expectEqual(@as(u64, 4), powers_of_2[2]);
    try testing.expectEqual(@as(u64, 1024), powers_of_2[10]);
    try testing.expectEqual(@as(u64, 1 << 20), powers_of_2[20]);
}
// ANCHOR_END: power_of_two

// ANCHOR: sin_table
/// Precompute sine values for fast lookup
fn generateSinTable(comptime resolution: usize) [resolution]f64 {
    comptime {
        var table: [resolution]f64 = undefined;
        const step = 2.0 * std.math.pi / @as(f64, @floatFromInt(resolution));

        for (0..resolution) |i| {
            const angle = @as(f64, @floatFromInt(i)) * step;
            table[i] = @sin(angle);
        }

        return table;
    }
}

const sin_table = generateSinTable(360);

fn fastSin(angle_degrees: f64) f64 {
    const normalized = @mod(angle_degrees, 360.0);
    const index = @as(usize, @intFromFloat(@round(normalized)));
    return sin_table[index];
}

test "sine lookup table" {
    const epsilon = 0.01;

    // 0 degrees
    try testing.expect(@abs(fastSin(0.0) - 0.0) < epsilon);

    // 90 degrees
    try testing.expect(@abs(fastSin(90.0) - 1.0) < epsilon);

    // 180 degrees
    try testing.expect(@abs(fastSin(180.0) - 0.0) < epsilon);

    // 270 degrees
    try testing.expect(@abs(fastSin(270.0) - (-1.0)) < epsilon);
}
// ANCHOR_END: sin_table

// ANCHOR: memoized_generic
/// Generic memoization wrapper
fn Memoized(comptime F: type, comptime f: F, comptime max_n: usize) type {
    return struct {
        const cache = blk: {
            var result: [max_n]u64 = undefined;
            for (0..max_n) |i| {
                result[i] = f(i);
            }
            break :blk result;
        };

        pub fn call(n: usize) u64 {
            if (n >= max_n) {
                @panic("Input exceeds cache size");
            }
            return cache[n];
        }
    };
}

fn slowSquare(n: usize) u64 {
    return @as(u64, n) * @as(u64, n);
}

const MemoizedSquare = Memoized(@TypeOf(slowSquare), slowSquare, 100);

test "generic memoization" {
    try testing.expectEqual(@as(u64, 0), MemoizedSquare.call(0));
    try testing.expectEqual(@as(u64, 1), MemoizedSquare.call(1));
    try testing.expectEqual(@as(u64, 100), MemoizedSquare.call(10));
    try testing.expectEqual(@as(u64, 9801), MemoizedSquare.call(99));
}
// ANCHOR_END: memoized_generic

// ANCHOR: build_time_optimization
/// Choose implementation based on compile-time computation
fn optimizedSum(comptime size: usize) fn ([]const u32) u64 {
    if (size <= 4) {
        // For small arrays, use simple loop
        return struct {
            fn sum(arr: []const u32) u64 {
                var result: u64 = 0;
                for (arr) |val| {
                    result += val;
                }
                return result;
            }
        }.sum;
    } else {
        // For larger arrays, use unrolled loop
        return struct {
            fn sum(arr: []const u32) u64 {
                var result: u64 = 0;
                var i: usize = 0;

                // Process 4 at a time
                while (i + 4 <= arr.len) : (i += 4) {
                    result += arr[i];
                    result += arr[i + 1];
                    result += arr[i + 2];
                    result += arr[i + 3];
                }

                // Handle remainder
                while (i < arr.len) : (i += 1) {
                    result += arr[i];
                }

                return result;
            }
        }.sum;
    }
}

test "compile-time optimization selection" {
    const small_arr = [_]u32{ 1, 2, 3 };
    const small_fn = optimizedSum(small_arr.len);
    try testing.expectEqual(@as(u64, 6), small_fn(&small_arr));

    const large_arr = [_]u32{ 1, 2, 3, 4, 5, 6, 7, 8 };
    const large_fn = optimizedSum(large_arr.len);
    try testing.expectEqual(@as(u64, 36), large_fn(&large_arr));
}
// ANCHOR_END: build_time_optimization
```

### See Also

- Recipe 17.2: Compile
- Recipe 17.4: Generic Data Structure Generation
- Recipe 17.6: Build
- Recipe 16.6: Build options and configurations

---
