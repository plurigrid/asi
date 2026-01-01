# Multi-File Zig Project Example

This example demonstrates a complete multi-file Zig project with:
- Module organization
- Build system configuration
- Cross-module imports
- Comprehensive testing
- Library creation

## Project Structure

```
build_example/
├── build.zig              # Build configuration
├── README.md              # This file
└── src/
    ├── main.zig           # Main entry point
    ├── math_utils.zig     # Math operations module
    └── string_utils.zig   # String operations module
```

## Modules

### math_utils.zig
Provides mathematical operations:
- Basic arithmetic (add, subtract, multiply, divide)
- Factorial calculation
- Prime number checking
- Greatest common divisor (GCD)

### string_utils.zig
Provides string operations:
- Character counting
- Prefix/suffix checking
- Case conversion (upper/lower)
- String reversal
- Trimming whitespace
- Numeric and palindrome checking

### main.zig
Demonstrates using both modules together with practical examples.

## Building and Running

### Build the executable
```bash
zig build
```

### Build and run
```bash
zig build run
```

### Run all tests
```bash
zig build test
```

### Build the math library
```bash
zig build lib
```

## Build System Features

The `build.zig` file demonstrates:

1. **Executable creation** - Compiles src/main.zig into an executable
2. **Test targets** - Creates test executables for each module
3. **Library creation** - Builds a static library from math_utils
4. **Custom build steps** - Defines `run`, `test`, and `lib` steps
5. **Target and optimization** - Configurable cross-compilation and optimization

## Key Concepts Demonstrated

### Module Imports
```zig
const math = @import("math_utils.zig");
const strings = @import("string_utils.zig");
```

### Public API Design
All public functions use `pub fn` to export them to other modules.

### Testing Strategy
- Each module has its own unit tests
- Main module includes integration tests
- All tests run with `zig build test`

### Memory Management
Functions that allocate memory:
- Accept an `Allocator` parameter
- Caller is responsible for freeing
- Use `defer` for cleanup

### Error Handling
Functions that can fail return error unions (`!T`).

## Learning Path

1. **Start with modules** - Read `math_utils.zig` and `string_utils.zig`
2. **Understand imports** - See how `main.zig` imports and uses modules
3. **Study build.zig** - Learn build system configuration
4. **Run tests** - Execute `zig build test` to see testing in action
5. **Modify and extend** - Add new functions or modules

## Common Patterns

### Creating a new module

1. Create a new .zig file in `src/`
2. Define public functions with `pub fn`
3. Import in main.zig: `const mymod = @import("mymod.zig");`
4. Add test target in build.zig

### Adding tests

```zig
const testing = std.testing;

test "description" {
    try testing.expectEqual(expected, actual);
}
```

### Exporting functionality

```zig
pub fn myFunction(param: Type) ReturnType {
    // Implementation
}
```

## Output Example

When you run `zig build run`, you'll see:

```
=== Multi-File Zig Project Example ===

=== Math Utilities ===
5 + 3 = 8
5 - 3 = 2
5 * 3 = 15
15 / 3 = 5
Factorial of 5 = 120
Is 17 prime? true
GCD of 12 and 18 = 6

=== String Utilities ===
Test string: 'Hello, Zig!'
Count of 'l': 2
Starts with 'Hello': true
Ends with 'Zig!': true
Uppercase: HELLO, ZIG!
Lowercase: hello, zig!
Reversed: !giZ ,olleH
...
```

## Next Steps

- Add more modules for different functionality
- Implement a CLI with argument parsing
- Create a library that can be used by other projects
- Add benchmarks for performance testing
- Integrate with external C libraries
