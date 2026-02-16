# Files & I/O Recipes

*19 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [5.1](#recipe-5-1) | Reading and Writing Text Data | intermediate |
| [5.2](#recipe-5-2) | Printing to a File | intermediate |
| [5.3](#recipe-5-3) | Printing with a Different Separator or Line Ending | intermediate |
| [5.4](#recipe-5-4) | Reading and Writing Binary Data | intermediate |
| [5.5](#recipe-5-5) | Writing to a File That Doesn't Already Exist | intermediate |
| [5.6](#recipe-5-6) | Performing I/O Operations on a String | intermediate |
| [5.7](#recipe-5-7) | Reading and Writing Compressed Datafiles | intermediate |
| [5.8](#recipe-5-8) | Iterating Over Fixed-Sized Records | intermediate |
| [5.9](#recipe-5-9) | Reading Binary Data into a Mutable Buffer | intermediate |
| [5.10](#recipe-5-10) | Memory Mapping Binary Files | intermediate |
| [5.11](#recipe-5-11) | Manipulating Pathnames | intermediate |
| [5.12](#recipe-5-12) | Testing for the Existence of a File | intermediate |
| [5.13](#recipe-5-13) | Getting a Directory Listing | intermediate |
| [5.14](#recipe-5-14) | Bypassing Filename Encoding | intermediate |
| [5.15](#recipe-5-15) | Printing Bad Filenames | intermediate |
| [5.16](#recipe-5-16) | Adding or Changing the Encoding of an Already Open File | advanced |
| [5.17](#recipe-5-17) | Writing Bytes to a Text File | advanced |
| [5.18](#recipe-5-18) | Communicating with Serial Ports | advanced |
| [5.19](#recipe-5-19) | Serializing Zig Objects | advanced |

---

## Recipe 5.1: Reading and Writing Text Data {#recipe-5-1}

**Tags:** allocators, arena-allocator, arraylist, data-structures, error-handling, files-io, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_1.zig`

### Problem

You need to read text from a file or write text to a file efficiently, handling line-by-line processing or bulk data operations.

### Solution

### Writing and Reading Text

```zig
/// Write text content to a file using buffered I/O
pub fn writeTextFile(path: []const u8, content: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.writeAll(content);
    try writer.flush();
}

/// Read entire text file into memory
pub fn readTextFile(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const file_size = (try file.stat()).size;
    const buffer = try allocator.alloc(u8, file_size);

    const bytes_read = try file.readAll(buffer);
    return buffer[0..bytes_read];
}
```

### Line Processing

```zig
/// Process a file line by line and collect lines into an array
pub fn readLinesIntoList(
    allocator: std.mem.Allocator,
    path: []const u8,
) !std.array_list.Managed([]u8) {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    var read_buf: [4096]u8 = undefined;
    var file_reader = file.reader(&read_buf);
    const reader = &file_reader.interface;

    var lines = std.array_list.Managed([]u8).init(allocator);
    errdefer {
        for (lines.items) |line| {
            allocator.free(line);
        }
        lines.deinit();
    }

    var line_writer = std.Io.Writer.Allocating.init(allocator);
    defer line_writer.deinit();

    while (true) {
        _ = reader.streamDelimiter(&line_writer.writer, '\n') catch |err| {
            if (err == error.EndOfStream) break else return err;
        };
        _ = reader.toss(1); // Skip the newline delimiter

        const line_copy = try allocator.dupe(u8, line_writer.written());
        try lines.append(line_copy);
        line_writer.clearRetainingCapacity();
    }

    // Handle last line if no trailing newline
    if (line_writer.written().len > 0) {
        const line_copy = try allocator.dupe(u8, line_writer.written());
        try lines.append(line_copy);
    }

    return lines;
}
```

### Stream Transform

```zig
/// Write formatted lines to a file
pub fn writeFormattedLines(
    path: []const u8,
    data: []const i32,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (data, 0..) |value, i| {
        try writer.print("Item {}: {}\n", .{ i, value });
    }

    try writer.flush();
}

/// Read from one file and write to another, transforming content
pub fn processLargeFile(
    allocator: std.mem.Allocator,
    input_path: []const u8,
    output_path: []const u8,
) !usize {
    const input = try std.fs.cwd().openFile(input_path, .{});
    defer input.close();

    const output = try std.fs.cwd().createFile(output_path, .{});
    defer output.close();

    var read_buf: [4096]u8 = undefined;
    var write_buf: [4096]u8 = undefined;

    var input_reader = input.reader(&read_buf);
    var output_writer = output.writer(&write_buf);

    const reader = &input_reader.interface;
    const writer = &output_writer.interface;

    var line_count: usize = 0;
    var line_writer = std.Io.Writer.Allocating.init(allocator);
    defer line_writer.deinit();

    while (true) {
        _ = reader.streamDelimiter(&line_writer.writer, '\n') catch |err| {
            if (err == error.EndOfStream) break else return err;
        };
        _ = reader.toss(1); // Skip newline

        line_count += 1;

        // Transform: convert to uppercase
        const line = line_writer.written();
        for (line) |c| {
            const upper = if (c >= 'a' and c <= 'z') c - 32 else c;
            try writer.writeByte(upper);
        }
        try writer.writeByte('\n');
        line_writer.clearRetainingCapacity();
    }

    // Handle last line if no trailing newline
    if (line_writer.written().len > 0) {
        line_count += 1;
        const line = line_writer.written();
        for (line) |c| {
            const upper = if (c >= 'a' and c <= 'z') c - 32 else c;
            try writer.writeByte(upper);
        }
        try writer.writeByte('\n');
    }

    try writer.flush();
    return line_count;
}
```

### Discussion

### Zig 0.15.2 I/O API

Starting with Zig 0.15.1, the I/O system was redesigned with buffered I/O as the default. Key changes:

- **Explicit buffers required**: Pass a buffer to `file.reader(&buffer)` and `file.writer(&buffer)`
- **Access via interface**: Get the reader/writer interface with `&file_reader.interface`
- **Manual flushing**: Always call `.flush()` on writers to ensure data is written
- **New line reading**: Use `reader.streamDelimiter()` instead of `readUntilDelimiter()`
- **ArrayList changes**: Use `std.array_list.Managed(T)` instead of `std.ArrayList(T)`

These changes provide better performance but require explicit buffer management and flush calls.

### Buffered I/O Benefits

Buffered readers and writers significantly improve performance by reducing the number of system calls. Instead of reading or writing one byte at a time, they work with larger chunks of data.

**Without buffering:**
- Each `readByte()` or `writeByte()` call triggers a system call
- Extremely slow for large files
- High overhead

**With buffering:**
- Data is read/written in blocks (typically 4KB)
- Dramatically reduces system calls
- Much better performance

### Buffer Sizes

The standard library uses reasonable default buffer sizes (4096 bytes). You can customize buffer sizes if needed:

```zig
var buffer: [8192]u8 = undefined;
var buffered = std.io.bufferedReaderSize(4096, file.reader());
```

### Error Handling

File operations can fail for many reasons:

- File doesn't exist (`error.FileNotFound`)
- Permission denied (`error.AccessDenied`)
- Disk full (`error.NoSpaceLeft`)
- I/O errors (`error.InputOutput`)

Always handle errors explicitly with `try`, `catch`, or proper error propagation:

```zig
const file = std.fs.cwd().openFile(path, .{}) catch |err| {
    std.debug.print("Failed to open {s}: {}\n", .{ path, err });
    return err;
};
```

### Memory Management

When reading entire files into memory:

1. Always free allocated memory with `defer allocator.free(content)`
2. Be aware of file sizes before allocating
3. Consider streaming for very large files
4. Use `ArenaAllocator` for batch processing

```zig
var arena = std.heap.ArenaAllocator.init(allocator);
defer arena.deinit();
const arena_alloc = arena.allocator();

// All allocations cleaned up together
const content1 = try readTextFile(arena_alloc, "file1.txt");
const content2 = try readTextFile(arena_alloc, "file2.txt");
// No individual frees needed
```

### Line Endings

Zig treats `\n` as the line delimiter. For cross-platform text files:

- Unix/Linux/macOS: `\n` (LF)
- Windows: `\r\n` (CRLF)
- Old Mac: `\r` (CR)

To handle Windows-style line endings:

```zig
const trimmed = std.mem.trimRight(u8, line, "\r");
```

### File Modes

When creating files, specify the mode:

```zig
// Truncate existing file (default)
const file = try std.fs.cwd().createFile(path, .{});

// Append to existing file
const file = try std.fs.cwd().openFile(path, .{
    .mode = .write_only,
});
try file.seekFromEnd(0);

// Create only if doesn't exist
const file = try std.fs.cwd().createFile(path, .{
    .exclusive = true,
});
```

### Reading Strategies

Choose the right strategy based on your needs:

**Full file read** - Good for small to medium files:
```zig
const content = try file.readToEndAlloc(allocator, max_size);
```

**Line by line** - Best for large files or when processing sequentially:
```zig
while (try reader.readUntilDelimiterOrEof(&buffer, '\n')) |line| {
    // Process line
}
```

**Fixed chunks** - For binary data or custom processing:
```zig
const bytes_read = try reader.read(buffer);
```

### Performance Considerations

The generic Reader interface used in these examples prioritizes simplicity, portability, and correctness. For most applications, this provides excellent performance with proper buffering.

**When performance matters most:**
- The generic `streamDelimiter()` reads byte-by-byte through the Reader interface
- For high-performance scenarios (processing many large files), direct BufferedReader access with SIMD-optimized `std.mem.indexOfScalar()` can be 2-15x faster
- This advanced optimization trades simplicity for speed and is covered in advanced recipes

For the vast majority of use cases, the patterns shown here are the right choice.

### Comparison with Other Languages

**Python:**
```python
# Read entire file
with open('file.txt', 'r') as f:
    content = f.read()

# Line by line
with open('file.txt', 'r') as f:
    for line in f:
        print(line)
```

**Zig's approach** requires explicit resource management (`defer file.close()`) and explicit error handling, but provides more control and no hidden allocations.

### Full Tested Code

```zig
// Recipe 5.1: Reading and writing text data
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to efficiently read and write text files using
// buffered I/O operations, handle line-by-line processing, and manage file resources.

const std = @import("std");
const testing = std.testing;

// ANCHOR: write_read_text
/// Write text content to a file using buffered I/O
pub fn writeTextFile(path: []const u8, content: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.writeAll(content);
    try writer.flush();
}

/// Read entire text file into memory
pub fn readTextFile(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const file_size = (try file.stat()).size;
    const buffer = try allocator.alloc(u8, file_size);

    const bytes_read = try file.readAll(buffer);
    return buffer[0..bytes_read];
}
// ANCHOR_END: write_read_text

// ANCHOR: line_processing
/// Process a file line by line and collect lines into an array
pub fn readLinesIntoList(
    allocator: std.mem.Allocator,
    path: []const u8,
) !std.array_list.Managed([]u8) {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    var read_buf: [4096]u8 = undefined;
    var file_reader = file.reader(&read_buf);
    const reader = &file_reader.interface;

    var lines = std.array_list.Managed([]u8).init(allocator);
    errdefer {
        for (lines.items) |line| {
            allocator.free(line);
        }
        lines.deinit();
    }

    var line_writer = std.Io.Writer.Allocating.init(allocator);
    defer line_writer.deinit();

    while (true) {
        _ = reader.streamDelimiter(&line_writer.writer, '\n') catch |err| {
            if (err == error.EndOfStream) break else return err;
        };
        _ = reader.toss(1); // Skip the newline delimiter

        const line_copy = try allocator.dupe(u8, line_writer.written());
        try lines.append(line_copy);
        line_writer.clearRetainingCapacity();
    }

    // Handle last line if no trailing newline
    if (line_writer.written().len > 0) {
        const line_copy = try allocator.dupe(u8, line_writer.written());
        try lines.append(line_copy);
    }

    return lines;
}
// ANCHOR_END: line_processing

// ANCHOR: stream_transform
/// Write formatted lines to a file
pub fn writeFormattedLines(
    path: []const u8,
    data: []const i32,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (data, 0..) |value, i| {
        try writer.print("Item {}: {}\n", .{ i, value });
    }

    try writer.flush();
}

/// Read from one file and write to another, transforming content
pub fn processLargeFile(
    allocator: std.mem.Allocator,
    input_path: []const u8,
    output_path: []const u8,
) !usize {
    const input = try std.fs.cwd().openFile(input_path, .{});
    defer input.close();

    const output = try std.fs.cwd().createFile(output_path, .{});
    defer output.close();

    var read_buf: [4096]u8 = undefined;
    var write_buf: [4096]u8 = undefined;

    var input_reader = input.reader(&read_buf);
    var output_writer = output.writer(&write_buf);

    const reader = &input_reader.interface;
    const writer = &output_writer.interface;

    var line_count: usize = 0;
    var line_writer = std.Io.Writer.Allocating.init(allocator);
    defer line_writer.deinit();

    while (true) {
        _ = reader.streamDelimiter(&line_writer.writer, '\n') catch |err| {
            if (err == error.EndOfStream) break else return err;
        };
        _ = reader.toss(1); // Skip newline

        line_count += 1;

        // Transform: convert to uppercase
        const line = line_writer.written();
        for (line) |c| {
            const upper = if (c >= 'a' and c <= 'z') c - 32 else c;
            try writer.writeByte(upper);
        }
        try writer.writeByte('\n');
        line_writer.clearRetainingCapacity();
    }

    // Handle last line if no trailing newline
    if (line_writer.written().len > 0) {
        line_count += 1;
        const line = line_writer.written();
        for (line) |c| {
            const upper = if (c >= 'a' and c <= 'z') c - 32 else c;
            try writer.writeByte(upper);
        }
        try writer.writeByte('\n');
    }

    try writer.flush();
    return line_count;
}
// ANCHOR_END: stream_transform

/// Append text to an existing file
pub fn appendToFile(path: []const u8, content: []const u8) !void {
    const file = try std.fs.cwd().openFile(path, .{
        .mode = .read_write,
    });
    defer file.close();

    const end_pos = try file.getEndPos();
    try file.seekTo(end_pos);

    // Use unbuffered write for append to avoid issues with file positioning
    _ = try file.write(content);
}

/// Count lines in a file without loading entire file into memory
pub fn countLines(allocator: std.mem.Allocator, path: []const u8) !usize {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    var read_buf: [4096]u8 = undefined;
    var file_reader = file.reader(&read_buf);
    const reader = &file_reader.interface;

    var count: usize = 0;
    var line_writer = std.Io.Writer.Allocating.init(allocator);
    defer line_writer.deinit();

    while (true) {
        _ = reader.streamDelimiter(&line_writer.writer, '\n') catch |err| {
            if (err == error.EndOfStream) break else return err;
        };
        _ = reader.toss(1); // Skip newline
        count += 1;
        line_writer.clearRetainingCapacity();
    }

    // Handle last line if no trailing newline
    if (line_writer.written().len > 0) {
        count += 1;
    }

    return count;
}

// Tests

test "write and read text file" {
    const allocator = testing.allocator;
    const test_path = "test_write_read.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const content = "Hello, Zig!\nThis is a test file.\nWith multiple lines.";

    // Write file
    try writeTextFile(test_path, content);

    // Read file
    const read_content = try readTextFile(allocator, test_path);
    defer allocator.free(read_content);

    try testing.expectEqualStrings(content, read_content);
}

test "read lines into list" {
    const allocator = testing.allocator;
    const test_path = "test_lines.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const content = "Line 1\nLine 2\nLine 3";
    try writeTextFile(test_path, content);

    var lines = try readLinesIntoList(allocator, test_path);
    defer {
        for (lines.items) |line| {
            allocator.free(line);
        }
        lines.deinit();
    }

    try testing.expectEqual(@as(usize, 3), lines.items.len);
    try testing.expectEqualStrings("Line 1", lines.items[0]);
    try testing.expectEqualStrings("Line 2", lines.items[1]);
    try testing.expectEqualStrings("Line 3", lines.items[2]);
}

test "write formatted lines" {
    const allocator = testing.allocator;
    const test_path = "test_formatted.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const data = [_]i32{ 10, 20, 30, 40, 50 };
    try writeFormattedLines(test_path, &data);

    const content = try readTextFile(allocator, test_path);
    defer allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Item 0: 10") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Item 4: 50") != null);
}

test "process large file with transformation" {
    const allocator = testing.allocator;
    const input_path = "test_input.txt";
    const output_path = "test_output.txt";
    defer std.fs.cwd().deleteFile(input_path) catch {};
    defer std.fs.cwd().deleteFile(output_path) catch {};

    const content = "hello world\nzig is awesome\nfile io test";
    try writeTextFile(input_path, content);

    const line_count = try processLargeFile(allocator, input_path, output_path);
    try testing.expectEqual(@as(usize, 3), line_count);

    const output_content = try readTextFile(allocator, output_path);
    defer allocator.free(output_content);

    try testing.expect(std.mem.indexOf(u8, output_content, "HELLO WORLD") != null);
    try testing.expect(std.mem.indexOf(u8, output_content, "ZIG IS AWESOME") != null);
}

test "append to file" {
    const allocator = testing.allocator;
    const test_path = "test_append.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write initial content
    try writeTextFile(test_path, "First line\n");

    // Append more content
    try appendToFile(test_path, "Second line\n");
    try appendToFile(test_path, "Third line\n");

    const content = try readTextFile(allocator, test_path);
    defer allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "First line") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Second line") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Third line") != null);
}

test "count lines" {
    const allocator = testing.allocator;
    const test_path = "test_count.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const content = "Line 1\nLine 2\nLine 3\nLine 4\nLine 5";
    try writeTextFile(test_path, content);

    const count = try countLines(allocator, test_path);
    try testing.expectEqual(@as(usize, 5), count);
}

test "handle empty file" {
    const allocator = testing.allocator;
    const test_path = "test_empty.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    try writeTextFile(test_path, "");

    const content = try readTextFile(allocator, test_path);
    defer allocator.free(content);

    try testing.expectEqual(@as(usize, 0), content.len);

    const count = try countLines(allocator, test_path);
    try testing.expectEqual(@as(usize, 0), count);
}

test "handle file with single line no newline" {
    const allocator = testing.allocator;
    const test_path = "test_single.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    try writeTextFile(test_path, "Single line");

    const content = try readTextFile(allocator, test_path);
    defer allocator.free(content);

    try testing.expectEqualStrings("Single line", content);

    const count = try countLines(allocator, test_path);
    try testing.expectEqual(@as(usize, 1), count);
}

test "handle windows line endings" {
    const allocator = testing.allocator;
    const test_path = "test_crlf.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const content = "Line 1\r\nLine 2\r\nLine 3\r\n";
    try writeTextFile(test_path, content);

    var lines = try readLinesIntoList(allocator, test_path);
    defer {
        for (lines.items) |line| {
            allocator.free(line);
        }
        lines.deinit();
    }

    try testing.expectEqual(@as(usize, 3), lines.items.len);

    // Note: lines will have \r at the end, need to trim
    const line1 = std.mem.trimRight(u8, lines.items[0], "\r");
    try testing.expectEqualStrings("Line 1", line1);
}

test "memory safety with arena allocator" {
    const test_path = "test_arena.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const content = "Line 1\nLine 2\nLine 3\nLine 4\nLine 5\n";
    try writeTextFile(test_path, content);

    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    // Read file multiple times - all allocations cleaned up together
    const read1 = try readTextFile(arena_alloc, test_path);
    const read2 = try readTextFile(arena_alloc, test_path);

    try testing.expectEqualStrings(content, read1);
    try testing.expectEqualStrings(content, read2);
    // No individual frees needed - arena.deinit() handles everything
}
```

### See Also

- Recipe 5.2: Printing to a file
- Recipe 5.4: Reading and writing binary data
- Recipe 5.6: Performing I/O operations on a string

---

## Recipe 5.2: Printing to a File {#recipe-5-2}

**Tags:** allocators, error-handling, files-io, memory, pointers, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_2.zig`

### Problem

You need to write formatted data to a file, similar to how `std.debug.print` works for stdout, but directed to a file instead.

### Solution

### Basic Printing

```zig
/// Print formatted data to a file using the writer interface
pub fn printToFile(path: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.print("Hello, {s}!\n", .{"World"});
    try writer.print("The answer is: {}\n", .{42});
    try writer.print("Pi: {d:.2}\n", .{3.14159});

    try writer.flush();
}

/// Demonstrate printing various data types with different format specifiers
pub fn printMixedData(path: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    // Integers with different bases
    try writer.print("Decimal: {}\n", .{255});
    try writer.print("Hexadecimal: {x}\n", .{255});
    try writer.print("Binary: {b}\n", .{255});
    try writer.print("Octal: {o}\n", .{255});

    // Floating point with precision
    try writer.print("Default float: {}\n", .{3.14159});
    try writer.print("Two decimals: {d:.2}\n", .{3.14159});
    try writer.print("Scientific: {e}\n", .{1234.5});

    // Boolean and strings
    try writer.print("Boolean: {}\n", .{true});
    try writer.print("String: {s}\n", .{"Hello"});

    try writer.flush();
}
```

### Structured Printing

```zig
const Person = struct {
    name: []const u8,
    age: u32,
    height: f32,
};

/// Print structured data (array of structs) to a file
pub fn printStructData(path: []const u8, people: []const Person) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.print("People Database\n", .{});
    try writer.print("{s}\n", .{"=" ** 50});

    for (people, 0..) |person, i| {
        try writer.print("{}: {s}, Age: {}, Height: {d:.1}m\n", .{
            i + 1,
            person.name,
            person.age,
            person.height,
        });
    }

    try writer.flush();
}

/// Print a formatted table with headers and data rows
pub fn printTable(
    path: []const u8,
    headers: []const []const u8,
    data: []const []const []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    // Print headers
    for (headers) |header| {
        try writer.print("{s:<15} ", .{header});
    }
    try writer.print("\n", .{});

    // Print separator
    for (headers) |_| {
        try writer.print("{s:<15} ", .{"-" ** 15});
    }
    try writer.print("\n", .{});

    // Print data rows
    for (data) |row| {
        for (row) |cell| {
            try writer.print("{s:<15} ", .{cell});
        }
        try writer.print("\n", .{});
    }

    try writer.flush();
}
```

### Conditional Logging

```zig
/// Print only values that meet a condition, return count
pub fn printWithConditions(
    path: []const u8,
    values: []const i32,
    threshold: i32,
) !usize {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    var count: usize = 0;

    try writer.print("Values greater than {}:\n", .{threshold});

    for (values) |value| {
        if (value > threshold) {
            try writer.print("  {}\n", .{value});
            count += 1;
        }
    }

    try writer.print("\nTotal: {} values\n", .{count});
    try writer.flush();

    return count;
}

/// Append a log entry with timestamp to a log file
pub fn printLog(
    path: []const u8,
    level: []const u8,
    message: []const u8,
) !void {
    // Open file for appending by using OpenFlags
    const file = try std.fs.cwd().openFile(path, .{
        .mode = .write_only,
    });
    defer file.close();

    // Seek to end for appending
    try file.seekFromEnd(0);

    const timestamp = std.time.timestamp();

    // Format the message
    var buf: [512]u8 = undefined;
    const log_line = try std.fmt.bufPrint(&buf, "[{}] {s}: {s}\n", .{ timestamp, level, message });

    // Write directly without buffering to avoid issues
    _ = try file.write(log_line);
}

/// Print a report with error handling for data generation
pub fn printReport(
    path: []const u8,
    allocator: std.mem.Allocator,
    generate_data: *const fn (std.mem.Allocator) anyerror![]const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.print("=== Report ===\n\n", .{});

    const data = generate_data(allocator) catch |err| {
        try writer.print("Error generating data: {}\n", .{err});
        try writer.flush();
        return err;
    };
    defer allocator.free(data);

    try writer.print("Data:\n{s}\n", .{data});
    try writer.flush();
}

/// Print numbers with various alignment options
pub fn printAlignedNumbers(path: []const u8, numbers: []const i32) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.print("Left aligned:   ", .{});
    for (numbers) |num| {
        try writer.print("{:<8}", .{num});
    }
    try writer.print("\n", .{});

    try writer.print("Right aligned:  ", .{});
    for (numbers) |num| {
        try writer.print("{:>8}", .{num});
    }
    try writer.print("\n", .{});

    try writer.print("Center aligned: ", .{});
    for (numbers) |num| {
        try writer.print("{:^8}", .{num});
    }
    try writer.print("\n", .{});

    try writer.flush();
}

/// Print statistics summary
pub fn printStatistics(
    path: []const u8,
    values: []const f64,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    var sum: f64 = 0;
    var min: f64 = values[0];
    var max: f64 = values[0];

    for (values) |v| {
        sum += v;
        if (v < min) min = v;
        if (v > max) max = v;
    }

    const mean = sum / @as(f64, @floatFromInt(values.len));
```

### Discussion

### Writer Interface

The `.print()` method on writers provides type-safe formatted output similar to `std.debug.print` or `std.fmt.format`. It uses compile-time format string parsing to ensure type safety.

**Format specifiers:**
- `{}` - Default formatting for the type
- `{s}` - String (required for `[]const u8`)
- `{d}` - Decimal formatting for numbers
- `{x}` - Hexadecimal (lowercase)
- `{X}` - Hexadecimal (uppercase)
- `{b}` - Binary
- `{o}` - Octal
- `{e}` - Scientific notation
- `{c}` - Character
- `{*}` - Pointer address

**Formatting options:**
- `{d:.2}` - Precision (2 decimal places)
- `{s:<10}` - Left-align with width 10
- `{s:>10}` - Right-align with width 10
- `{s:^10}` - Center-align with width 10

### Memory Usage

The `.print()` method formats directly into the writer's buffer, avoiding intermediate allocations. This makes it very efficient for file output.

```zig
// No allocations needed
try writer.print("Value: {}\n", .{42});

// Compare to building strings:
const str = try std.fmt.allocPrint(allocator, "Value: {}\n", .{42});
defer allocator.free(str);
try writer.writeAll(str);  // Less efficient
```

### Flushing

Always remember to flush the writer when you're done:

```zig
try writer.flush();
```

Without flushing, data may remain in the buffer and not be written to disk. This is especially important for:
- Log files where immediate visibility matters
- Critical data that must be persisted
- Before closing the file (though `defer file.close()` helps here)

### Error Handling

Printing to a file can fail for several reasons:
- Disk full (`error.NoSpaceLeft`)
- File system errors (`error.InputOutput`)
- Broken pipe if file handle becomes invalid
- Permission issues

Always propagate or handle these errors appropriately:

```zig
writer.print("Data: {}\n", .{value}) catch |err| {
    std.log.err("Failed to write: {}", .{err});
    return err;
};
```

### Performance Considerations

**Buffered writing is automatic** with the new Zig 0.15.2 API. The buffer you provide to `file.writer(&buffer)` is used for batching write operations.

**Buffer size matters:**
- Smaller buffers (1KB-4KB): More frequent flushes, good for logs
- Larger buffers (8KB-64KB): Fewer syscalls, better for bulk data
- Default 4KB is good for most cases

**For maximum performance:**
```zig
var write_buf: [8192]u8 = undefined;  // Larger buffer
var file_writer = file.writer(&write_buf);
const writer = &file_writer.interface;

// Batch many print calls
for (many_items) |item| {
    try writer.print("{}\n", .{item});
}

// Single flush at the end
try writer.flush();
```

### Comparison with writeAll

**Use `.print()` when:**
- You need formatting
- Working with multiple data types
- Building output dynamically
- Creating human-readable output

**Use `.writeAll()` when:**
- You already have formatted strings
- Writing raw binary data
- Maximum performance is critical
- No formatting needed

```zig
// With formatting - use print
try writer.print("Count: {}\n", .{count});

// Pre-formatted - use writeAll
try writer.writeAll("Static string\n");
```

### Comparison with Other Languages

**Python:**
```python
with open('output.txt', 'w') as f:
    print(f"Hello, {name}!", file=f)
    print(f"Value: {value}", file=f)
```

**C:**
```c
FILE *f = fopen("output.txt", "w");
fprintf(f, "Hello, %s!\n", name);
fprintf(f, "Value: %d\n", value);
fclose(f);
```

**Zig's approach** combines type safety of format strings (compile-time checked) with explicit error handling and no hidden allocations.

### Full Tested Code

```zig
// Recipe 5.2: Printing to a file
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to use formatted printing to write data to files,
// similar to how std.debug.print works for stdout but directed to file handles.

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_printing
/// Print formatted data to a file using the writer interface
pub fn printToFile(path: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.print("Hello, {s}!\n", .{"World"});
    try writer.print("The answer is: {}\n", .{42});
    try writer.print("Pi: {d:.2}\n", .{3.14159});

    try writer.flush();
}

/// Demonstrate printing various data types with different format specifiers
pub fn printMixedData(path: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    // Integers with different bases
    try writer.print("Decimal: {}\n", .{255});
    try writer.print("Hexadecimal: {x}\n", .{255});
    try writer.print("Binary: {b}\n", .{255});
    try writer.print("Octal: {o}\n", .{255});

    // Floating point with precision
    try writer.print("Default float: {}\n", .{3.14159});
    try writer.print("Two decimals: {d:.2}\n", .{3.14159});
    try writer.print("Scientific: {e}\n", .{1234.5});

    // Boolean and strings
    try writer.print("Boolean: {}\n", .{true});
    try writer.print("String: {s}\n", .{"Hello"});

    try writer.flush();
}
// ANCHOR_END: basic_printing

// ANCHOR: structured_printing
const Person = struct {
    name: []const u8,
    age: u32,
    height: f32,
};

/// Print structured data (array of structs) to a file
pub fn printStructData(path: []const u8, people: []const Person) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.print("People Database\n", .{});
    try writer.print("{s}\n", .{"=" ** 50});

    for (people, 0..) |person, i| {
        try writer.print("{}: {s}, Age: {}, Height: {d:.1}m\n", .{
            i + 1,
            person.name,
            person.age,
            person.height,
        });
    }

    try writer.flush();
}

/// Print a formatted table with headers and data rows
pub fn printTable(
    path: []const u8,
    headers: []const []const u8,
    data: []const []const []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    // Print headers
    for (headers) |header| {
        try writer.print("{s:<15} ", .{header});
    }
    try writer.print("\n", .{});

    // Print separator
    for (headers) |_| {
        try writer.print("{s:<15} ", .{"-" ** 15});
    }
    try writer.print("\n", .{});

    // Print data rows
    for (data) |row| {
        for (row) |cell| {
            try writer.print("{s:<15} ", .{cell});
        }
        try writer.print("\n", .{});
    }

    try writer.flush();
}
// ANCHOR_END: structured_printing

// ANCHOR: conditional_logging
/// Print only values that meet a condition, return count
pub fn printWithConditions(
    path: []const u8,
    values: []const i32,
    threshold: i32,
) !usize {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    var count: usize = 0;

    try writer.print("Values greater than {}:\n", .{threshold});

    for (values) |value| {
        if (value > threshold) {
            try writer.print("  {}\n", .{value});
            count += 1;
        }
    }

    try writer.print("\nTotal: {} values\n", .{count});
    try writer.flush();

    return count;
}

/// Append a log entry with timestamp to a log file
pub fn printLog(
    path: []const u8,
    level: []const u8,
    message: []const u8,
) !void {
    // Open file for appending by using OpenFlags
    const file = try std.fs.cwd().openFile(path, .{
        .mode = .write_only,
    });
    defer file.close();

    // Seek to end for appending
    try file.seekFromEnd(0);

    const timestamp = std.time.timestamp();

    // Format the message
    var buf: [512]u8 = undefined;
    const log_line = try std.fmt.bufPrint(&buf, "[{}] {s}: {s}\n", .{ timestamp, level, message });

    // Write directly without buffering to avoid issues
    _ = try file.write(log_line);
}

/// Print a report with error handling for data generation
pub fn printReport(
    path: []const u8,
    allocator: std.mem.Allocator,
    generate_data: *const fn (std.mem.Allocator) anyerror![]const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.print("=== Report ===\n\n", .{});

    const data = generate_data(allocator) catch |err| {
        try writer.print("Error generating data: {}\n", .{err});
        try writer.flush();
        return err;
    };
    defer allocator.free(data);

    try writer.print("Data:\n{s}\n", .{data});
    try writer.flush();
}

/// Print numbers with various alignment options
pub fn printAlignedNumbers(path: []const u8, numbers: []const i32) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.print("Left aligned:   ", .{});
    for (numbers) |num| {
        try writer.print("{:<8}", .{num});
    }
    try writer.print("\n", .{});

    try writer.print("Right aligned:  ", .{});
    for (numbers) |num| {
        try writer.print("{:>8}", .{num});
    }
    try writer.print("\n", .{});

    try writer.print("Center aligned: ", .{});
    for (numbers) |num| {
        try writer.print("{:^8}", .{num});
    }
    try writer.print("\n", .{});

    try writer.flush();
}

/// Print statistics summary
pub fn printStatistics(
    path: []const u8,
    values: []const f64,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    var sum: f64 = 0;
    var min: f64 = values[0];
    var max: f64 = values[0];

    for (values) |v| {
        sum += v;
        if (v < min) min = v;
        if (v > max) max = v;
    }

    const mean = sum / @as(f64, @floatFromInt(values.len));
// ANCHOR_END: conditional_logging

    try writer.print("Statistics Summary\n", .{});
    try writer.print("{s}\n", .{"=" ** 20});
    try writer.print("Count:   {}\n", .{values.len});
    try writer.print("Sum:     {d:.2}\n", .{sum});
    try writer.print("Mean:    {d:.2}\n", .{mean});
    try writer.print("Min:     {d:.2}\n", .{min});
    try writer.print("Max:     {d:.2}\n", .{max});

    try writer.flush();
}

// Tests

test "basic printing to file" {
    const test_path = "test_print_basic.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    try printToFile(test_path);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Hello, World!") != null);
    try testing.expect(std.mem.indexOf(u8, content, "42") != null);
    try testing.expect(std.mem.indexOf(u8, content, "3.14") != null);
}

test "print mixed data types" {
    const test_path = "test_print_mixed.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    try printMixedData(test_path);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 2048);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Decimal: 255") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Hexadecimal: ff") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Binary: 11111111") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Boolean: true") != null);
}

test "print structured data" {
    const test_path = "test_print_struct.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const people = [_]Person{
        .{ .name = "Alice", .age = 30, .height = 1.65 },
        .{ .name = "Bob", .age = 25, .height = 1.80 },
        .{ .name = "Charlie", .age = 35, .height = 1.75 },
    };

    try printStructData(test_path, &people);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 2048);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Alice") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Bob") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Charlie") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Age: 30") != null);
}

test "print table" {
    const test_path = "test_print_table.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const headers = [_][]const u8{ "Name", "Age", "City" };
    const row1 = [_][]const u8{ "Alice", "30", "NYC" };
    const row2 = [_][]const u8{ "Bob", "25", "LA" };
    const row3 = [_][]const u8{ "Charlie", "35", "Chicago" };
    const data = [_][]const []const u8{ &row1, &row2, &row3 };

    try printTable(test_path, &headers, &data);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 2048);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Name") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Alice") != null);
    try testing.expect(std.mem.indexOf(u8, content, "NYC") != null);
}

test "print with conditions" {
    const test_path = "test_print_conditions.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const values = [_]i32{ 10, 25, 30, 5, 50, 15, 40 };
    const count = try printWithConditions(test_path, &values, 20);

    try testing.expectEqual(@as(usize, 4), count);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "25") != null);
    try testing.expect(std.mem.indexOf(u8, content, "30") != null);
    try testing.expect(std.mem.indexOf(u8, content, "50") != null);
    try testing.expect(std.mem.indexOf(u8, content, "40") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Total: 4") != null);
}

test "print log entries" {
    const test_path = "test_print_log.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create initial file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
    }

    // Append log entries
    try printLog(test_path, "INFO", "Application started");
    try printLog(test_path, "WARN", "Low memory warning");
    try printLog(test_path, "ERROR", "Connection failed");

    // Read and verify
    const content = blk: {
        const file = try std.fs.cwd().openFile(test_path, .{});
        defer file.close();
        break :blk try file.readToEndAlloc(testing.allocator, 2048);
    };
    defer testing.allocator.free(content);

    // Verify content is not empty
    try testing.expect(content.len > 0);

    // Verify each log level appears - indexOf returns the index or null
    _ = std.mem.indexOf(u8, content, "INFO") orelse {
        std.debug.print("Content: {s}\n", .{content});
        return error.TestFailed;
    };
    _ = std.mem.indexOf(u8, content, "WARN") orelse return error.TestFailed;
    _ = std.mem.indexOf(u8, content, "ERROR") orelse return error.TestFailed;
    _ = std.mem.indexOf(u8, content, "Application started") orelse return error.TestFailed;
}

fn generateTestData(allocator: std.mem.Allocator) ![]const u8 {
    return try allocator.dupe(u8, "Sample data from generator");
}

fn generateErrorData(_: std.mem.Allocator) ![]const u8 {
    return error.TestError;
}

test "print report with success" {
    const test_path = "test_print_report.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    try printReport(test_path, testing.allocator, generateTestData);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "=== Report ===") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Sample data") != null);
}

test "print report with error" {
    const test_path = "test_print_report_error.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const result = printReport(test_path, testing.allocator, generateErrorData);
    try testing.expectError(error.TestError, result);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Error generating data") != null);
}

test "print aligned numbers" {
    const test_path = "test_print_aligned.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const numbers = [_]i32{ 1, 42, 999, 12345 };
    try printAlignedNumbers(test_path, &numbers);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Left aligned") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Right aligned") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Center aligned") != null);
}

test "print statistics" {
    const test_path = "test_print_stats.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const values = [_]f64{ 10.5, 20.3, 15.7, 8.2, 30.1 };
    try printStatistics(test_path, &values);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expect(std.mem.indexOf(u8, content, "Statistics Summary") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Count:   5") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Min:") != null);
    try testing.expect(std.mem.indexOf(u8, content, "Max:") != null);
}

test "memory safety check - no allocations" {
    const test_path = "test_memory_safe.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // All these operations should not allocate
    try printToFile(test_path);
    try printMixedData(test_path);

    const numbers = [_]i32{ 1, 2, 3 };
    try printAlignedNumbers(test_path, &numbers);

    // If we reach here without allocation errors, the test passes
}
```

### See Also

- Recipe 5.1: Reading and writing text data
- Recipe 5.3: Printing with a different separator or line ending
- Recipe 3.3: Formatting numbers for output

---

## Recipe 5.3: Printing with a Different Separator or Line Ending {#recipe-5-3}

**Tags:** allocators, csv, error-handling, files-io, json, memory, parsing, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_3.zig`

### Problem

You want to print data to a file with custom separators between values (like tabs, commas, or pipes) or use different line endings (like Windows CRLF or no line endings at all).

### Solution

### Delimited Output

```zig
/// Print rows with tab separators
pub fn printTabDelimited(
    path: []const u8,
    rows: []const []const []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (rows) |row| {
        for (row, 0..) |cell, i| {
            try writer.writeAll(cell);
            if (i < row.len - 1) {
                try writer.writeAll("\t");
            }
        }
        try writer.writeAll("\n");
    }

    try writer.flush();
}

/// Print CSV with proper escaping
pub fn printCsv(
    path: []const u8,
    rows: []const []const []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (rows) |row| {
        for (row, 0..) |cell, i| {
            // Escape cells containing commas or quotes
            if (std.mem.indexOf(u8, cell, ",") != null or
                std.mem.indexOf(u8, cell, "\"") != null)
            {
                try writer.writeAll("\"");
                // Escape internal quotes by doubling them
                for (cell) |c| {
                    if (c == '"') {
                        try writer.writeAll("\"\"");
                    } else {
                        try writer.writeByte(c);
                    }
                }
                try writer.writeAll("\"");
            } else {
                try writer.writeAll(cell);
            }

            if (i < row.len - 1) {
                try writer.writeAll(",");
            }
        }
        try writer.writeAll("\n");
    }

    try writer.flush();
}

/// Print values with a custom separator
pub fn printWithSeparator(
    path: []const u8,
    values: []const []const u8,
    separator: []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (values, 0..) |value, i| {
        try writer.writeAll(value);
        if (i < values.len - 1) {
            try writer.writeAll(separator);
        }
    }

    try writer.flush();
}
```

### Line Endings

```zig
/// Print lines with Windows CRLF line endings
pub fn printWithCrlf(
    path: []const u8,
    lines: []const []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (lines) |line| {
        try writer.writeAll(line);
        try writer.writeAll("\r\n");
    }

    try writer.flush();
}

/// Print numbers with custom separator and precision
pub fn printNumbersWithFormat(
    path: []const u8,
    numbers: []const f64,
    separator: []const u8,
    precision: usize,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (numbers, 0..) |num, i| {
        switch (precision) {
            0 => try writer.print("{d:.0}", .{num}),
            1 => try writer.print("{d:.1}", .{num}),
            2 => try writer.print("{d:.2}", .{num}),
            3 => try writer.print("{d:.3}", .{num}),
            else => try writer.print("{d:.4}", .{num}),
        }

        if (i < numbers.len - 1) {
            try writer.writeAll(separator);
        }
    }

    try writer.flush();
}

/// Print chunks concatenated with no line endings
pub fn printConcatenated(
    path: []const u8,
    chunks: []const []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (chunks) |chunk| {
        try writer.writeAll(chunk);
    }

    try writer.flush();
}

/// Line ending styles
pub const LineEnding = enum {
    lf,    // Unix: \n
    crlf,  // Windows: \r\n
    cr,    // Old Mac: \r
};

/// Print lines with configurable line endings
pub fn printWithLineEnding(
    path: []const u8,
    lines: []const []const u8,
    ending: LineEnding,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    const line_end = switch (ending) {
        .lf => "\n",
        .crlf => "\r\n",
        .cr => "\r",
    };

    for (lines) |line| {
        try writer.writeAll(line);
        try writer.writeAll(line_end);
    }

    try writer.flush();
}
```

### Format Variations

```zig
/// Print JSON array with optional indentation
pub fn printJsonArray(
    path: []const u8,
    values: []const []const u8,
    indent: bool,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.writeAll("[");
    if (indent) try writer.writeAll("\n");

    for (values, 0..) |value, i| {
        if (indent) try writer.writeAll("  ");
        try writer.print("\"{s}\"", .{value});
        if (i < values.len - 1) {
            try writer.writeAll(",");
        }
        if (indent) try writer.writeAll("\n");
    }

    try writer.writeAll("]");
    if (indent) try writer.writeAll("\n");

    try writer.flush();
}

/// Key-value pair type
pub const KeyValue = struct {
    key: []const u8,
    value: []const u8,
};

/// Print key-value pairs with custom format
pub fn printKeyValuePairs(
    path: []const u8,
    pairs: []const KeyValue,
    pair_separator: []const u8,
    kv_separator: []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (pairs, 0..) |pair, i| {
        try writer.writeAll(pair.key);
        try writer.writeAll(kv_separator);
        try writer.writeAll(pair.value);
        if (i < pairs.len - 1) {
            try writer.writeAll(pair_separator);
        }
    }

    try writer.flush();
}
```

### Discussion

### Separator Strategies

When printing tabular or structured data, choosing the right separator is important:

**Tab-separated (\t):**
- Good for terminal display with aligned columns
- Easy to parse
- Works well with spreadsheet applications
- Not great for data containing actual tabs

**Comma-separated (,):**
- Standard CSV format
- Widely supported
- Requires escaping commas in data
- Need to handle quoted fields

**Pipe-separated (|):**
- Less common in data
- Easy to visually parse
- Good for log files
- Still need escaping if data contains pipes

**Custom separators:**
- Use unique strings like `::` or `|||`
- Reduce collision risk
- May be harder to parse with standard tools

### CSV Escaping Rules

Proper CSV formatting requires careful escaping:

1. **Quoted fields:** If a field contains a comma, newline, or quote, wrap it in quotes
2. **Escaped quotes:** Double any quote marks inside quoted fields: `"He said ""Hi"""`
3. **Newlines:** Can be preserved inside quoted fields
4. **Leading/trailing spaces:** May need quoting depending on implementation

Our simple implementation handles basic cases. For production CSV writing, consider using a dedicated library.

### Line Endings

Different platforms use different line endings:

**Unix/Linux/macOS (LF):** `\n`
- Single character
- Modern standard
- Used by most modern tools

**Windows (CRLF):** `\r\n`
- Two characters
- Required by some Windows applications
- Notepad, older Windows tools

**Old Mac (CR):** `\r`
- Single character
- Rarely seen today
- Pre-OS X Macintosh systems

**Best practices:**
- Default to LF (`\n`) for cross-platform compatibility
- Use CRLF only when targeting Windows-specific tools
- Be consistent within a file
- Modern editors handle any line ending

### Performance Considerations

**Buffered writes are crucial:** The examples use buffered writers which batch multiple small writes into larger syscalls. This is much faster than writing one character at a time.

**Separator choice affects performance:**
- Single-character separators (`\t`, `,`) are fastest
- Multi-character separators require more write calls
- Complex escaping (CSV) adds overhead

**For maximum throughput:**
```zig
// Use larger buffer for bulk data
var write_buf: [16384]u8 = undefined;  // 16KB buffer
var file_writer = file.writer(&write_buf);
const writer = &file_writer.interface;

// Batch many writes before flushing
for (many_rows) |row| {
    // ... write row ...
}
try writer.flush();  // Single flush at end
```

### Cross-Platform Considerations

When writing files that will be used on different platforms:

1. **Document your format:** Specify line endings and encoding in comments/docs
2. **Be consistent:** Don't mix line endings within a file
3. **Test on target platforms:** Windows text mode can auto-convert `\n` to `\r\n`
4. **Consider binary mode:** For precise control, use binary mode and explicit line endings

### Comparison with Other Languages

**Python:**
```python
# Custom separator
print(*values, sep="|", file=f)

# Custom line ending
print("line", end="\r\n", file=f)

# CSV module
import csv
writer = csv.writer(f, delimiter='\t')
writer.writerow(row)
```

**Zig's approach** requires more explicit code but gives you complete control over formatting, buffering, and error handling with no hidden behavior.

### Full Tested Code

```zig
// Recipe 5.3: Printing with different separators and line endings
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to customize output formatting with different
// separators, delimiters, and line endings for various file formats.

const std = @import("std");
const testing = std.testing;

// ANCHOR: delimited_output
/// Print rows with tab separators
pub fn printTabDelimited(
    path: []const u8,
    rows: []const []const []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (rows) |row| {
        for (row, 0..) |cell, i| {
            try writer.writeAll(cell);
            if (i < row.len - 1) {
                try writer.writeAll("\t");
            }
        }
        try writer.writeAll("\n");
    }

    try writer.flush();
}

/// Print CSV with proper escaping
pub fn printCsv(
    path: []const u8,
    rows: []const []const []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (rows) |row| {
        for (row, 0..) |cell, i| {
            // Escape cells containing commas or quotes
            if (std.mem.indexOf(u8, cell, ",") != null or
                std.mem.indexOf(u8, cell, "\"") != null)
            {
                try writer.writeAll("\"");
                // Escape internal quotes by doubling them
                for (cell) |c| {
                    if (c == '"') {
                        try writer.writeAll("\"\"");
                    } else {
                        try writer.writeByte(c);
                    }
                }
                try writer.writeAll("\"");
            } else {
                try writer.writeAll(cell);
            }

            if (i < row.len - 1) {
                try writer.writeAll(",");
            }
        }
        try writer.writeAll("\n");
    }

    try writer.flush();
}

/// Print values with a custom separator
pub fn printWithSeparator(
    path: []const u8,
    values: []const []const u8,
    separator: []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (values, 0..) |value, i| {
        try writer.writeAll(value);
        if (i < values.len - 1) {
            try writer.writeAll(separator);
        }
    }

    try writer.flush();
}
// ANCHOR_END: delimited_output

// ANCHOR: line_endings
/// Print lines with Windows CRLF line endings
pub fn printWithCrlf(
    path: []const u8,
    lines: []const []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (lines) |line| {
        try writer.writeAll(line);
        try writer.writeAll("\r\n");
    }

    try writer.flush();
}

/// Print numbers with custom separator and precision
pub fn printNumbersWithFormat(
    path: []const u8,
    numbers: []const f64,
    separator: []const u8,
    precision: usize,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (numbers, 0..) |num, i| {
        switch (precision) {
            0 => try writer.print("{d:.0}", .{num}),
            1 => try writer.print("{d:.1}", .{num}),
            2 => try writer.print("{d:.2}", .{num}),
            3 => try writer.print("{d:.3}", .{num}),
            else => try writer.print("{d:.4}", .{num}),
        }

        if (i < numbers.len - 1) {
            try writer.writeAll(separator);
        }
    }

    try writer.flush();
}

/// Print chunks concatenated with no line endings
pub fn printConcatenated(
    path: []const u8,
    chunks: []const []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (chunks) |chunk| {
        try writer.writeAll(chunk);
    }

    try writer.flush();
}

/// Line ending styles
pub const LineEnding = enum {
    lf,    // Unix: \n
    crlf,  // Windows: \r\n
    cr,    // Old Mac: \r
};

/// Print lines with configurable line endings
pub fn printWithLineEnding(
    path: []const u8,
    lines: []const []const u8,
    ending: LineEnding,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    const line_end = switch (ending) {
        .lf => "\n",
        .crlf => "\r\n",
        .cr => "\r",
    };

    for (lines) |line| {
        try writer.writeAll(line);
        try writer.writeAll(line_end);
    }

    try writer.flush();
}
// ANCHOR_END: line_endings

// ANCHOR: format_variations
/// Print JSON array with optional indentation
pub fn printJsonArray(
    path: []const u8,
    values: []const []const u8,
    indent: bool,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writer.writeAll("[");
    if (indent) try writer.writeAll("\n");

    for (values, 0..) |value, i| {
        if (indent) try writer.writeAll("  ");
        try writer.print("\"{s}\"", .{value});
        if (i < values.len - 1) {
            try writer.writeAll(",");
        }
        if (indent) try writer.writeAll("\n");
    }

    try writer.writeAll("]");
    if (indent) try writer.writeAll("\n");

    try writer.flush();
}

/// Key-value pair type
pub const KeyValue = struct {
    key: []const u8,
    value: []const u8,
};

/// Print key-value pairs with custom format
pub fn printKeyValuePairs(
    path: []const u8,
    pairs: []const KeyValue,
    pair_separator: []const u8,
    kv_separator: []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (pairs, 0..) |pair, i| {
        try writer.writeAll(pair.key);
        try writer.writeAll(kv_separator);
        try writer.writeAll(pair.value);
        if (i < pairs.len - 1) {
            try writer.writeAll(pair_separator);
        }
    }

    try writer.flush();
}
// ANCHOR_END: format_variations

// Tests

test "print tab delimited" {
    const test_path = "test_tab_delimited.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const row1 = [_][]const u8{ "Name", "Age", "City" };
    const row2 = [_][]const u8{ "Alice", "30", "NYC" };
    const row3 = [_][]const u8{ "Bob", "25", "LA" };
    const rows = [_][]const []const u8{ &row1, &row2, &row3 };

    try printTabDelimited(test_path, &rows);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    _ = std.mem.indexOf(u8, content, "Name\tAge\tCity") orelse return error.TestFailed;
    _ = std.mem.indexOf(u8, content, "Alice\t30\tNYC") orelse return error.TestFailed;
}

test "print csv with escaping" {
    const test_path = "test_csv.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const row1 = [_][]const u8{ "Name", "Description", "Price" };
    const row2 = [_][]const u8{ "Widget", "A nice, useful widget", "$10" };
    const row3 = [_][]const u8{ "Gadget", "Has \"quotes\"", "$20" };
    const rows = [_][]const []const u8{ &row1, &row2, &row3 };

    try printCsv(test_path, &rows);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    // Check for proper escaping
    _ = std.mem.indexOf(u8, content, "\"A nice, useful widget\"") orelse return error.TestFailed;
    _ = std.mem.indexOf(u8, content, "\"Has \"\"quotes\"\"\"") orelse return error.TestFailed;
}

test "print with custom separator" {
    const test_path = "test_custom_sep.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const values = [_][]const u8{ "apple", "banana", "cherry", "date" };
    try printWithSeparator(test_path, &values, " | ");

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expectEqualStrings("apple | banana | cherry | date", content);
}

test "print with CRLF line endings" {
    const test_path = "test_crlf.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const lines = [_][]const u8{ "Line 1", "Line 2", "Line 3" };
    try printWithCrlf(test_path, &lines);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expectEqualStrings("Line 1\r\nLine 2\r\nLine 3\r\n", content);
}

test "print numbers with format" {
    const test_path = "test_numbers_format.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const numbers = [_]f64{ 3.14159, 2.71828, 1.41421 };
    try printNumbersWithFormat(test_path, &numbers, ", ", 2);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    _ = std.mem.indexOf(u8, content, "3.14") orelse return error.TestFailed;
    _ = std.mem.indexOf(u8, content, "2.72") orelse return error.TestFailed;
    _ = std.mem.indexOf(u8, content, "1.41") orelse return error.TestFailed;
}

test "print concatenated without line endings" {
    const test_path = "test_concatenated.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const chunks = [_][]const u8{ "Hello", " ", "World", "!" };
    try printConcatenated(test_path, &chunks);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expectEqualStrings("Hello World!", content);
}

test "print with different line endings" {
    const allocator = testing.allocator;

    const lines = [_][]const u8{ "Line 1", "Line 2", "Line 3" };

    // Test LF (Unix)
    {
        const test_path = "test_lf.txt";
        defer std.fs.cwd().deleteFile(test_path) catch {};

        try printWithLineEnding(test_path, &lines, .lf);

        const file = try std.fs.cwd().openFile(test_path, .{});
        defer file.close();

        const content = try file.readToEndAlloc(allocator, 1024);
        defer allocator.free(content);

        try testing.expectEqualStrings("Line 1\nLine 2\nLine 3\n", content);
    }

    // Test CRLF (Windows)
    {
        const test_path = "test_crlf2.txt";
        defer std.fs.cwd().deleteFile(test_path) catch {};

        try printWithLineEnding(test_path, &lines, .crlf);

        const file = try std.fs.cwd().openFile(test_path, .{});
        defer file.close();

        const content = try file.readToEndAlloc(allocator, 1024);
        defer allocator.free(content);

        try testing.expectEqualStrings("Line 1\r\nLine 2\r\nLine 3\r\n", content);
    }

    // Test CR (Old Mac)
    {
        const test_path = "test_cr.txt";
        defer std.fs.cwd().deleteFile(test_path) catch {};

        try printWithLineEnding(test_path, &lines, .cr);

        const file = try std.fs.cwd().openFile(test_path, .{});
        defer file.close();

        const content = try file.readToEndAlloc(allocator, 1024);
        defer allocator.free(content);

        try testing.expectEqualStrings("Line 1\rLine 2\rLine 3\r", content);
    }
}

test "print json array" {
    const allocator = testing.allocator;

    const values = [_][]const u8{ "apple", "banana", "cherry" };

    // Test without indentation
    {
        const test_path = "test_json_compact.txt";
        defer std.fs.cwd().deleteFile(test_path) catch {};

        try printJsonArray(test_path, &values, false);

        const file = try std.fs.cwd().openFile(test_path, .{});
        defer file.close();

        const content = try file.readToEndAlloc(allocator, 1024);
        defer allocator.free(content);

        try testing.expectEqualStrings("[\"apple\",\"banana\",\"cherry\"]", content);
    }

    // Test with indentation
    {
        const test_path = "test_json_indent.txt";
        defer std.fs.cwd().deleteFile(test_path) catch {};

        try printJsonArray(test_path, &values, true);

        const file = try std.fs.cwd().openFile(test_path, .{});
        defer file.close();

        const content = try file.readToEndAlloc(allocator, 1024);
        defer allocator.free(content);

        _ = std.mem.indexOf(u8, content, "[\n  \"apple\",\n") orelse return error.TestFailed;
    }
}

test "print key-value pairs" {
    const test_path = "test_kvpairs.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const pairs = [_]KeyValue{
        .{ .key = "name", .value = "Alice" },
        .{ .key = "age", .value = "30" },
        .{ .key = "city", .value = "NYC" },
    };

    try printKeyValuePairs(test_path, &pairs, "; ", "=");

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expectEqualStrings("name=Alice; age=30; city=NYC", content);
}

test "empty input handling" {
    const test_path = "test_empty.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const empty: []const []const u8 = &[_][]const u8{};
    try printWithSeparator(test_path, empty, ",");

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expectEqual(@as(usize, 0), content.len);
}

test "single value no separator" {
    const test_path = "test_single.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const values = [_][]const u8{"single"};
    try printWithSeparator(test_path, &values, ",");

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(testing.allocator, 1024);
    defer testing.allocator.free(content);

    try testing.expectEqualStrings("single", content);
}
```

### See Also

- Recipe 5.2: Printing to a file
- Recipe 5.1: Reading and writing text data
- Recipe 6.1: Reading and writing CSV data

---

## Recipe 5.4: Reading and Writing Binary Data {#recipe-5-4}

**Tags:** allocators, comptime, error-handling, files-io, memory, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_4.zig`

### Problem

You need to read or write binary data to a file, such as integers, floats, or packed structures, with control over byte order and data layout.

### Solution

### Binary Integers

```zig
/// Helper to write an integer to a writer using a buffer
fn writeIntToWriter(writer: anytype, comptime T: type, value: T, endian: std.builtin.Endian) !void {
    var buf: [@sizeOf(T)]u8 = undefined;
    std.mem.writeInt(T, &buf, value, endian);
    try writer.writeAll(&buf);
}

/// Helper to read an integer by reading raw bytes
fn readIntFromFile(file: std.fs.File, comptime T: type, endian: std.builtin.Endian) !T {
    var buf: [@sizeOf(T)]u8 = undefined;
    const bytes_read = try file.read(&buf);
    if (bytes_read != @sizeOf(T)) return error.UnexpectedEndOfFile;
    return std.mem.readInt(T, &buf, endian);
}

/// Write various integer types to a binary file
pub fn writeIntegers(path: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    // Write unsigned integers
    try writeIntToWriter(writer, u8, 255, .little);
    try writeIntToWriter(writer, u16, 65535, .little);
    try writeIntToWriter(writer, u32, 4294967295, .little);
    try writeIntToWriter(writer, u64, 123456789012345, .little);

    // Write signed integers
    try writeIntToWriter(writer, i8, -128, .little);
    try writeIntToWriter(writer, i16, -32768, .little);
    try writeIntToWriter(writer, i32, -2147483648, .little);

    try writer.flush();
}

/// Read integers from a binary file
pub fn readIntegers(path: []const u8) ![7]i64 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    var results: [7]i64 = undefined;
    results[0] = try readIntFromFile(file, u8, .little);
    results[1] = try readIntFromFile(file, u16, .little);
    results[2] = try readIntFromFile(file, u32, .little);
    results[3] = @intCast(try readIntFromFile(file, u64, .little));
    results[4] = try readIntFromFile(file, i8, .little);
    results[5] = try readIntFromFile(file, i16, .little);
    results[6] = try readIntFromFile(file, i32, .little);

    return results;
}
```

### Binary Structs

```zig
/// Write floating point numbers as binary
pub fn writeBinaryFloats(path: []const u8, values: []const f64) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (values) |value| {
        const bits: u64 = @bitCast(value);
        try writeIntToWriter(writer, u64, bits, .little);
    }

    try writer.flush();
}

/// Read floating point numbers from binary file
pub fn readBinaryFloats(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]f64 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const file_size = (try file.stat()).size;
    const count = file_size / @sizeOf(f64);

    const values = try allocator.alloc(f64, count);
    errdefer allocator.free(values);

    for (values) |*value| {
        const bits = try readIntFromFile(file, u64, .little);
        value.* = @bitCast(bits);
    }

    return values;
}

/// Binary file header structure
pub const BinaryHeader = packed struct {
    magic: u32,
    version: u16,
    flags: u16,
    data_size: u64,
};

/// Write a binary header to file
pub fn writeStructHeader(path: []const u8, header: BinaryHeader) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writeIntToWriter(writer, u32, header.magic, .little);
    try writeIntToWriter(writer, u16, header.version, .little);
    try writeIntToWriter(writer, u16, header.flags, .little);
    try writeIntToWriter(writer, u64, header.data_size, .little);

    try writer.flush();
}

/// Read a binary header from file
pub fn readStructHeader(path: []const u8) !BinaryHeader {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    return BinaryHeader{
        .magic = try readIntFromFile(file, u32, .little),
        .version = try readIntFromFile(file, u16, .little),
        .flags = try readIntFromFile(file, u16, .little),
        .data_size = try readIntFromFile(file, u64, .little),
    };
}

/// Write raw bytes with length prefix
pub fn writeRawBytes(path: []const u8, data: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writeIntToWriter(writer, u64, data.len, .little);
    try writer.writeAll(data);
    try writer.flush();
}

/// Read raw bytes with length prefix
pub fn readRawBytes(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const length = try readIntFromFile(file, u64, .little);
    const data = try allocator.alloc(u8, length);
    errdefer allocator.free(data);

    const bytes_read = try file.read(data);
    if (bytes_read != length) return error.UnexpectedEndOfFile;

    return data;
}

/// 3D point structure with binary I/O
pub const Point3D = struct {
    x: f32,
    y: f32,
    z: f32,

    pub fn write(self: Point3D, writer: anytype) !void {
        try writeIntToWriter(writer, u32, @bitCast(self.x), .little);
        try writeIntToWriter(writer, u32, @bitCast(self.y), .little);
        try writeIntToWriter(writer, u32, @bitCast(self.z), .little);
    }

    pub fn read(file: std.fs.File) !Point3D {
        return Point3D{
            .x = @bitCast(try readIntFromFile(file, u32, .little)),
            .y = @bitCast(try readIntFromFile(file, u32, .little)),
            .z = @bitCast(try readIntFromFile(file, u32, .little)),
        };
    }
};

/// Write an array of 3D points to file
pub fn writeMesh(path: []const u8, points: []const Point3D) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writeIntToWriter(writer, u64, points.len, .little);

    for (points) |point| {
        try point.write(writer);
    }

    try writer.flush();
}

/// Read an array of 3D points from file
pub fn readMesh(allocator: std.mem.Allocator, path: []const u8) ![]Point3D {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const count = try readIntFromFile(file, u64, .little);
    const points = try allocator.alloc(Point3D, count);
    errdefer allocator.free(points);

    for (points) |*point| {
        point.* = try Point3D.read(file);
    }

    return points;
}
```

### Endianness Validation

```zig
/// Write with big-endian byte order
pub fn writeWithBigEndian(path: []const u8, value: u32) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writeIntToWriter(writer, u32, value, .big);
    try writer.flush();
}

/// Read with specified endianness
pub fn readWithEndianness(path: []const u8, endian: std.builtin.Endian) !u32 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    return try readIntFromFile(file, u32, endian);
}

/// Write mixed binary data (header + payload)
pub fn writeCompleteFile(
    path: []const u8,
    magic: u32,
    data: []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    const header = BinaryHeader{
        .magic = magic,
        .version = 1,
        .flags = 0,
        .data_size = data.len,
    };

    try writeIntToWriter(writer, u32, header.magic, .little);
    try writeIntToWriter(writer, u16, header.version, .little);
    try writeIntToWriter(writer, u16, header.flags, .little);
    try writeIntToWriter(writer, u64, header.data_size, .little);
    try writer.writeAll(data);

    try writer.flush();
}

/// Read and validate complete binary file
pub fn readCompleteFile(
    allocator: std.mem.Allocator,
    path: []const u8,
    expected_magic: u32,
) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const header = BinaryHeader{
        .magic = try readIntFromFile(file, u32, .little),
        .version = try readIntFromFile(file, u16, .little),
        .flags = try readIntFromFile(file, u16, .little),
        .data_size = try readIntFromFile(file, u64, .little),
    };

    if (header.magic != expected_magic) return error.InvalidMagicNumber;
    if (header.data_size > 100_000_000) return error.SizeTooLarge;

    const data = try allocator.alloc(u8, header.data_size);
    errdefer allocator.free(data);

    const bytes_read = try file.read(data);
    if (bytes_read != header.data_size) return error.UnexpectedEndOfFile;

    return data;
}
```

### Discussion

### Endianness

Endianness determines the byte order when storing multi-byte values:

**Little-endian (.little):**
- Least significant byte first
- Used by x86, x86-64, ARM (usually)
- Example: `0x12345678` stored as `78 56 34 12`

**Big-endian (.big):**
- Most significant byte first
- Network byte order (TCP/IP)
- Some RISC processors
- Example: `0x12345678` stored as `12 34 56 78`

**Best practices:**
- Always specify endianness explicitly with `writeInt()` and `readInt()`
- Use `.little` for local files on modern systems
- Use `.big` for network protocols (matches network byte order)
- Document the endianness in file format specifications
- Use `@byteSwap()` to convert between endiannesses if needed

### Binary File Structure

Well-designed binary files typically include:

1. **Magic number** - Identifies file type (e.g., `0x89504E47` for PNG)
2. **Version** - Allows format evolution
3. **Header** - Metadata about the file contents
4. **Data sections** - The actual payload
5. **Checksums** - Verify data integrity

```zig
const FileHeader = packed struct {
    magic: u32,      // File type identifier
    version: u16,    // Format version
    flags: u16,      // Feature flags
    data_size: u64,  // Payload size in bytes
};
```

### Packed vs Regular Structs

**Packed structs:**
- Guarantee no padding between fields
- Fields stored in declaration order
- Exact memory layout control
- Good for binary file formats
- May be slower to access

**Regular structs:**
- Compiler can reorder and pad fields
- Better performance
- Not suitable for binary I/O
- Use for in-memory data

For binary files, always use explicit field-by-field reading/writing or carefully designed packed structs.

### Type Punning with @bitCast

To write floats as binary data, use `@bitCast` to reinterpret the bits:

```zig
const float_value: f32 = 3.14;
const int_bits: u32 = @bitCast(float_value);
try writer.writeInt(u32, int_bits, .little);

// Reading back
const read_bits = try reader.readInt(u32, .little);
const float_back: f32 = @bitCast(read_bits);
```

This preserves the exact binary representation without conversion.

### Error Handling

Binary I/O can fail in specific ways:

- `error.EndOfStream` - Unexpected end of file
- `error.UnexpectedEndOfFile` - Read fewer bytes than expected
- `error.InvalidFormat` - Wrong magic number or version
- `error.Overflow` - Size field too large

Always validate:
- Magic numbers match expected values
- Version numbers are supported
- Size fields are reasonable
- Checksums are correct

### Performance Tips

**Buffering is crucial:**
```zig
// Good - buffered
var buf: [8192]u8 = undefined;
var buffered_reader = file.reader(&buf);
const reader = &buffered_reader.interface;

// Reading many small values is efficient
for (0..1000) |_| {
    const val = try reader.readInt(u32, .little);
}
```

**Avoid byte-by-byte reads:**
```zig
// Slow - many syscalls
for (buffer) |*byte| {
    byte.* = try reader.readByte();
}

// Fast - single read
_ = try reader.readAll(buffer);
```

**Use readAll for known-size data:**
```zig
var buffer: [1024]u8 = undefined;
const bytes_read = try reader.readAll(&buffer);
if (bytes_read != buffer.len) return error.UnexpectedEndOfFile;
```

### Memory Safety

When reading binary data:

1. **Validate sizes before allocation:**
```zig
const size = try reader.readInt(u64, .little);
if (size > 100_000_000) return error.SizeTooLarge;
const data = try allocator.alloc(u8, size);
```

2. **Use errdefer for cleanup:**
```zig
const data = try allocator.alloc(u8, size);
errdefer allocator.free(data);
// ... reading can fail ...
```

3. **Check read lengths:**
```zig
const bytes_read = try reader.readAll(data);
if (bytes_read != data.len) return error.UnexpectedEndOfFile;
```

### Comparison with Other Languages

**Python:**
```python
import struct
# Write binary
with open('data.bin', 'wb') as f:
    f.write(struct.pack('<I', 42))  # Little-endian u32

# Read binary
with open('data.bin', 'rb') as f:
    value = struct.unpack('<I', f.read(4))[0]
```

**C:**
```c
FILE *f = fopen("data.bin", "wb");
uint32_t value = 42;
fwrite(&value, sizeof(value), 1, f);
fclose(f);
```

**Zig's approach** provides explicit control over endianness, clear error handling, and compile-time size checking without the risks of C or the performance overhead of Python.

### Full Tested Code

```zig
// Recipe 5.4: Reading and writing binary data
// Target Zig Version: 0.15.2
//
// This recipe demonstrates reading and writing binary data to files, including
// integers, floats, packed structs, and handling endianness for cross-platform files.

const std = @import("std");
const testing = std.testing;

// ANCHOR: binary_integers
/// Helper to write an integer to a writer using a buffer
fn writeIntToWriter(writer: anytype, comptime T: type, value: T, endian: std.builtin.Endian) !void {
    var buf: [@sizeOf(T)]u8 = undefined;
    std.mem.writeInt(T, &buf, value, endian);
    try writer.writeAll(&buf);
}

/// Helper to read an integer by reading raw bytes
fn readIntFromFile(file: std.fs.File, comptime T: type, endian: std.builtin.Endian) !T {
    var buf: [@sizeOf(T)]u8 = undefined;
    const bytes_read = try file.read(&buf);
    if (bytes_read != @sizeOf(T)) return error.UnexpectedEndOfFile;
    return std.mem.readInt(T, &buf, endian);
}

/// Write various integer types to a binary file
pub fn writeIntegers(path: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    // Write unsigned integers
    try writeIntToWriter(writer, u8, 255, .little);
    try writeIntToWriter(writer, u16, 65535, .little);
    try writeIntToWriter(writer, u32, 4294967295, .little);
    try writeIntToWriter(writer, u64, 123456789012345, .little);

    // Write signed integers
    try writeIntToWriter(writer, i8, -128, .little);
    try writeIntToWriter(writer, i16, -32768, .little);
    try writeIntToWriter(writer, i32, -2147483648, .little);

    try writer.flush();
}

/// Read integers from a binary file
pub fn readIntegers(path: []const u8) ![7]i64 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    var results: [7]i64 = undefined;
    results[0] = try readIntFromFile(file, u8, .little);
    results[1] = try readIntFromFile(file, u16, .little);
    results[2] = try readIntFromFile(file, u32, .little);
    results[3] = @intCast(try readIntFromFile(file, u64, .little));
    results[4] = try readIntFromFile(file, i8, .little);
    results[5] = try readIntFromFile(file, i16, .little);
    results[6] = try readIntFromFile(file, i32, .little);

    return results;
}
// ANCHOR_END: binary_integers

// ANCHOR: binary_structs
/// Write floating point numbers as binary
pub fn writeBinaryFloats(path: []const u8, values: []const f64) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    for (values) |value| {
        const bits: u64 = @bitCast(value);
        try writeIntToWriter(writer, u64, bits, .little);
    }

    try writer.flush();
}

/// Read floating point numbers from binary file
pub fn readBinaryFloats(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]f64 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const file_size = (try file.stat()).size;
    const count = file_size / @sizeOf(f64);

    const values = try allocator.alloc(f64, count);
    errdefer allocator.free(values);

    for (values) |*value| {
        const bits = try readIntFromFile(file, u64, .little);
        value.* = @bitCast(bits);
    }

    return values;
}

/// Binary file header structure
pub const BinaryHeader = packed struct {
    magic: u32,
    version: u16,
    flags: u16,
    data_size: u64,
};

/// Write a binary header to file
pub fn writeStructHeader(path: []const u8, header: BinaryHeader) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writeIntToWriter(writer, u32, header.magic, .little);
    try writeIntToWriter(writer, u16, header.version, .little);
    try writeIntToWriter(writer, u16, header.flags, .little);
    try writeIntToWriter(writer, u64, header.data_size, .little);

    try writer.flush();
}

/// Read a binary header from file
pub fn readStructHeader(path: []const u8) !BinaryHeader {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    return BinaryHeader{
        .magic = try readIntFromFile(file, u32, .little),
        .version = try readIntFromFile(file, u16, .little),
        .flags = try readIntFromFile(file, u16, .little),
        .data_size = try readIntFromFile(file, u64, .little),
    };
}

/// Write raw bytes with length prefix
pub fn writeRawBytes(path: []const u8, data: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writeIntToWriter(writer, u64, data.len, .little);
    try writer.writeAll(data);
    try writer.flush();
}

/// Read raw bytes with length prefix
pub fn readRawBytes(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const length = try readIntFromFile(file, u64, .little);
    const data = try allocator.alloc(u8, length);
    errdefer allocator.free(data);

    const bytes_read = try file.read(data);
    if (bytes_read != length) return error.UnexpectedEndOfFile;

    return data;
}

/// 3D point structure with binary I/O
pub const Point3D = struct {
    x: f32,
    y: f32,
    z: f32,

    pub fn write(self: Point3D, writer: anytype) !void {
        try writeIntToWriter(writer, u32, @bitCast(self.x), .little);
        try writeIntToWriter(writer, u32, @bitCast(self.y), .little);
        try writeIntToWriter(writer, u32, @bitCast(self.z), .little);
    }

    pub fn read(file: std.fs.File) !Point3D {
        return Point3D{
            .x = @bitCast(try readIntFromFile(file, u32, .little)),
            .y = @bitCast(try readIntFromFile(file, u32, .little)),
            .z = @bitCast(try readIntFromFile(file, u32, .little)),
        };
    }
};

/// Write an array of 3D points to file
pub fn writeMesh(path: []const u8, points: []const Point3D) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writeIntToWriter(writer, u64, points.len, .little);

    for (points) |point| {
        try point.write(writer);
    }

    try writer.flush();
}

/// Read an array of 3D points from file
pub fn readMesh(allocator: std.mem.Allocator, path: []const u8) ![]Point3D {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const count = try readIntFromFile(file, u64, .little);
    const points = try allocator.alloc(Point3D, count);
    errdefer allocator.free(points);

    for (points) |*point| {
        point.* = try Point3D.read(file);
    }

    return points;
}
// ANCHOR_END: binary_structs

// ANCHOR: endianness_validation
/// Write with big-endian byte order
pub fn writeWithBigEndian(path: []const u8, value: u32) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    try writeIntToWriter(writer, u32, value, .big);
    try writer.flush();
}

/// Read with specified endianness
pub fn readWithEndianness(path: []const u8, endian: std.builtin.Endian) !u32 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    return try readIntFromFile(file, u32, endian);
}

/// Write mixed binary data (header + payload)
pub fn writeCompleteFile(
    path: []const u8,
    magic: u32,
    data: []const u8,
) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    const header = BinaryHeader{
        .magic = magic,
        .version = 1,
        .flags = 0,
        .data_size = data.len,
    };

    try writeIntToWriter(writer, u32, header.magic, .little);
    try writeIntToWriter(writer, u16, header.version, .little);
    try writeIntToWriter(writer, u16, header.flags, .little);
    try writeIntToWriter(writer, u64, header.data_size, .little);
    try writer.writeAll(data);

    try writer.flush();
}

/// Read and validate complete binary file
pub fn readCompleteFile(
    allocator: std.mem.Allocator,
    path: []const u8,
    expected_magic: u32,
) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const header = BinaryHeader{
        .magic = try readIntFromFile(file, u32, .little),
        .version = try readIntFromFile(file, u16, .little),
        .flags = try readIntFromFile(file, u16, .little),
        .data_size = try readIntFromFile(file, u64, .little),
    };

    if (header.magic != expected_magic) return error.InvalidMagicNumber;
    if (header.data_size > 100_000_000) return error.SizeTooLarge;

    const data = try allocator.alloc(u8, header.data_size);
    errdefer allocator.free(data);

    const bytes_read = try file.read(data);
    if (bytes_read != header.data_size) return error.UnexpectedEndOfFile;

    return data;
}
// ANCHOR_END: endianness_validation

// Tests

test "write and read integers" {
    const test_path = "test_integers.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    try writeIntegers(test_path);
    const results = try readIntegers(test_path);

    try testing.expectEqual(@as(i64, 255), results[0]);
    try testing.expectEqual(@as(i64, 65535), results[1]);
    try testing.expectEqual(@as(i64, 4294967295), results[2]);
    try testing.expectEqual(@as(i64, 123456789012345), results[3]);
    try testing.expectEqual(@as(i64, -128), results[4]);
    try testing.expectEqual(@as(i64, -32768), results[5]);
    try testing.expectEqual(@as(i64, -2147483648), results[6]);
}

test "write and read floats" {
    const allocator = testing.allocator;
    const test_path = "test_floats.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const input = [_]f64{ 3.14159, 2.71828, 1.41421, -273.15 };
    try writeBinaryFloats(test_path, &input);

    const output = try readBinaryFloats(allocator, test_path);
    defer allocator.free(output);

    try testing.expectEqual(@as(usize, 4), output.len);
    try testing.expectApproxEqAbs(3.14159, output[0], 0.00001);
    try testing.expectApproxEqAbs(2.71828, output[1], 0.00001);
    try testing.expectApproxEqAbs(1.41421, output[2], 0.00001);
    try testing.expectApproxEqAbs(-273.15, output[3], 0.00001);
}

test "write and read struct header" {
    const test_path = "test_header.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const header = BinaryHeader{
        .magic = 0x12345678,
        .version = 1,
        .flags = 0x00FF,
        .data_size = 1024,
    };

    try writeStructHeader(test_path, header);
    const read_header = try readStructHeader(test_path);

    try testing.expectEqual(header.magic, read_header.magic);
    try testing.expectEqual(header.version, read_header.version);
    try testing.expectEqual(header.flags, read_header.flags);
    try testing.expectEqual(header.data_size, read_header.data_size);
}

test "write and read raw bytes" {
    const allocator = testing.allocator;
    const test_path = "test_raw_bytes.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const input = "Hello, Binary World!";
    try writeRawBytes(test_path, input);

    const output = try readRawBytes(allocator, test_path);
    defer allocator.free(output);

    try testing.expectEqualStrings(input, output);
}

test "write and read mesh" {
    const allocator = testing.allocator;
    const test_path = "test_mesh.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const input_points = [_]Point3D{
        .{ .x = 1.0, .y = 2.0, .z = 3.0 },
        .{ .x = 4.0, .y = 5.0, .z = 6.0 },
        .{ .x = 7.0, .y = 8.0, .z = 9.0 },
    };

    try writeMesh(test_path, &input_points);

    const output_points = try readMesh(allocator, test_path);
    defer allocator.free(output_points);

    try testing.expectEqual(@as(usize, 3), output_points.len);
    try testing.expectApproxEqAbs(1.0, output_points[0].x, 0.0001);
    try testing.expectApproxEqAbs(2.0, output_points[0].y, 0.0001);
    try testing.expectApproxEqAbs(3.0, output_points[0].z, 0.0001);
    try testing.expectApproxEqAbs(7.0, output_points[2].x, 0.0001);
    try testing.expectApproxEqAbs(8.0, output_points[2].y, 0.0001);
    try testing.expectApproxEqAbs(9.0, output_points[2].z, 0.0001);
}

test "big-endian vs little-endian" {
    const test_path = "test_endian.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const value: u32 = 0x12345678;
    try writeWithBigEndian(test_path, value);

    const big_result = try readWithEndianness(test_path, .big);
    try testing.expectEqual(value, big_result);

    // Reading with wrong endianness gives swapped bytes
    const little_result = try readWithEndianness(test_path, .little);
    try testing.expectEqual(@as(u32, 0x78563412), little_result);
}

test "complete file with validation" {
    const allocator = testing.allocator;
    const test_path = "test_complete.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const magic: u32 = 0xDEADBEEF;
    const data = "Test payload data";

    try writeCompleteFile(test_path, magic, data);

    const output = try readCompleteFile(allocator, test_path, magic);
    defer allocator.free(output);

    try testing.expectEqualStrings(data, output);
}

test "invalid magic number" {
    const allocator = testing.allocator;
    const test_path = "test_bad_magic.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    try writeCompleteFile(test_path, 0x12345678, "data");

    const result = readCompleteFile(allocator, test_path, 0xABCDEF00);
    try testing.expectError(error.InvalidMagicNumber, result);
}

test "empty binary data" {
    const allocator = testing.allocator;
    const test_path = "test_empty.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    try writeRawBytes(test_path, "");

    const output = try readRawBytes(allocator, test_path);
    defer allocator.free(output);

    try testing.expectEqual(@as(usize, 0), output.len);
}

test "large binary array" {
    const allocator = testing.allocator;
    const test_path = "test_large.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create array of 1000 floats
    const input = try allocator.alloc(f64, 1000);
    defer allocator.free(input);

    for (input, 0..) |*val, i| {
        val.* = @as(f64, @floatFromInt(i)) * 1.5;
    }

    try writeBinaryFloats(test_path, input);

    const output = try readBinaryFloats(allocator, test_path);
    defer allocator.free(output);

    try testing.expectEqual(input.len, output.len);
    for (input, output) |in, out| {
        try testing.expectApproxEqAbs(in, out, 0.0001);
    }
}

test "memory safety with errdefer" {
    const allocator = testing.allocator;
    const test_path = "test_truncated.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write incomplete file
    const file = try std.fs.cwd().createFile(test_path, .{});
    defer file.close();

    var write_buf: [4096]u8 = undefined;
    var file_writer = file.writer(&write_buf);
    const writer = &file_writer.interface;

    // Write length but no data
    try writeIntToWriter(writer, u64, 100, .little);
    try writer.flush();

    // This should fail and not leak memory
    const result = readRawBytes(allocator, test_path);
    try testing.expectError(error.UnexpectedEndOfFile, result);
}

test "binary file size calculation" {
    const test_path = "test_size.bin";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const values = [_]f64{ 1.0, 2.0, 3.0, 4.0, 5.0 };
    try writeBinaryFloats(test_path, &values);

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const file_size = (try file.stat()).size;
    const expected_size = values.len * @sizeOf(f64);

    try testing.expectEqual(expected_size, file_size);
}
```

### See Also

- Recipe 5.1: Reading and writing text data
- Recipe 3.5: Packing/unpacking large integers from bytes
- Recipe 6.9: Reading and writing binary arrays of structures

---

## Recipe 5.5: Writing to a File That Doesn't Already Exist {#recipe-5-5}

**Tags:** allocators, atomics, concurrency, error-handling, files-io, json, memory, parsing, resource-cleanup, testing, threading
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_5.zig`

### Problem

You want to create and write to a file only if it doesn't already exist, preventing accidental overwrites of existing data.

### Solution

### Exclusive Creation

```zig
/// Create a file exclusively (fails if file already exists)
pub fn createExclusive(path: []const u8, data: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{
        .exclusive = true,
    });
    defer file.close();

    try file.writeAll(data);
}

/// Acquire a lock file (fails if lock already held)
pub fn acquireLock(lock_path: []const u8) !std.fs.File {
    return std.fs.cwd().createFile(lock_path, .{
        .exclusive = true,
    });
}

/// Release a lock file
pub fn releaseLock(lock: std.fs.File, lock_path: []const u8) void {
    lock.close();
    std.fs.cwd().deleteFile(lock_path) catch {};
}

/// Create a unique temporary file with random suffix
pub fn createUniqueFile(allocator: std.mem.Allocator, prefix: []const u8) !struct { path: []const u8, file: std.fs.File } {
    var prng = std.Random.DefaultPrng.init(@intCast(std.time.timestamp()));
    const random = prng.random();

    var attempts: usize = 0;
    while (attempts < 100) : (attempts += 1) {
        const suffix = random.int(u32);
        const path = try std.fmt.allocPrint(allocator, "{s}_{d}.tmp", .{ prefix, suffix });
        errdefer allocator.free(path);

        const file = std.fs.cwd().createFile(path, .{
            .exclusive = true,
        }) catch |err| {
            if (err == error.PathAlreadyExists) {
                allocator.free(path);
                continue;
            }
            return err;
        };

        return .{ .path = path, .file = file };
    }

    return error.TooManyAttempts;
}
```

### Atomic Operations

```zig
/// Safely update a configuration file using atomic rename
pub fn safeUpdateConfig(config_path: []const u8, new_content: []const u8, allocator: std.mem.Allocator) !void {
    // Create unique temp file
    const temp_path = try std.fmt.allocPrint(allocator, "{s}.tmp", .{config_path});
    defer allocator.free(temp_path);

    // Write to temp file with exclusive creation
    {
        const file = try std.fs.cwd().createFile(temp_path, .{
            .exclusive = true,
        });
        defer file.close();
        try file.writeAll(new_content);
    }

    // Atomically replace original file
    try std.fs.cwd().rename(temp_path, config_path);
}

/// Write exclusively with error cleanup
pub fn writeExclusiveWithCleanup(path: []const u8, data: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{
        .exclusive = true,
    });
    errdefer {
        file.close();
        // Clean up partial file on error
        std.fs.cwd().deleteFile(path) catch {};
    }
    defer file.close();

    try file.writeAll(data);
}
```

### Discussion

### Exclusive Creation Flags

The `exclusive` flag in `CreateFlags` ensures that file creation is atomic and fails if the file already exists. This is equivalent to the POSIX `O_EXCL | O_CREAT` flags.

Without `exclusive = true`, `createFile` will truncate existing files:

```zig
// This WILL overwrite existing files (default behavior)
const file = try std.fs.cwd().createFile("data.txt", .{});

// This will NOT overwrite - fails with PathAlreadyExists
const file = try std.fs.cwd().createFile("data.txt", .{
    .exclusive = true,
});
```

### Error Handling

When a file already exists, the operation returns `error.PathAlreadyExists`:

```zig
const result = std.fs.cwd().createFile(path, .{ .exclusive = true });
if (result) |file| {
    defer file.close();
    // File created successfully, write data
    try file.writeAll(data);
} else |err| switch (err) {
    error.PathAlreadyExists => {
        // File exists - decide what to do
        std.debug.print("File already exists: {s}\n", .{path});
        return err;
    },
    else => return err,
}
```

### Use Cases

**Lock Files**: Prevent multiple processes from running simultaneously:

```zig
pub fn acquireLock(lock_path: []const u8) !std.fs.File {
    return std.fs.cwd().createFile(lock_path, .{
        .exclusive = true,
    });
}

pub fn releaseLock(lock: std.fs.File, lock_path: []const u8) void {
    lock.close();
    std.fs.cwd().deleteFile(lock_path) catch {};
}
```

**Unique Temporary Files**: Generate unique filenames until creation succeeds:

```zig
pub fn createUniqueFile(allocator: std.mem.Allocator, prefix: []const u8) !struct { path: []const u8, file: std.fs.File } {
    var prng = std.Random.DefaultPrng.init(@intCast(std.time.timestamp()));
    const random = prng.random();

    var attempts: usize = 0;
    while (attempts < 100) : (attempts += 1) {
        const suffix = random.int(u32);
        const path = try std.fmt.allocPrint(allocator, "{s}_{d}.tmp", .{ prefix, suffix });
        errdefer allocator.free(path);

        const file = std.fs.cwd().createFile(path, .{
            .exclusive = true,
        }) catch |err| {
            if (err == error.PathAlreadyExists) {
                allocator.free(path);
                continue;
            }
            return err;
        };

        return .{ .path = path, .file = file };
    }

    return error.TooManyAttempts;
}
```

**Safe Configuration File Updates**: Write to temporary file, then atomically rename:

```zig
pub fn safeUpdateConfig(config_path: []const u8, new_content: []const u8, allocator: std.mem.Allocator) !void {
    // Create unique temp file
    const temp_path = try std.fmt.allocPrint(allocator, "{s}.tmp", .{config_path});
    defer allocator.free(temp_path);

    // Write to temp file with exclusive creation
    {
        const file = try std.fs.cwd().createFile(temp_path, .{
            .exclusive = true,
        });
        defer file.close();
        try file.writeAll(new_content);
    }

    // Atomically replace original file
    try std.fs.cwd().rename(temp_path, config_path);
}
```

### Platform Considerations

Exclusive file creation is atomic on all platforms Zig supports:

- **Linux/macOS**: Uses `O_EXCL | O_CREAT` flags
- **Windows**: Uses `CREATE_NEW` disposition
- **WASI**: Implements atomic file creation

The operation is thread-safe and process-safe, making it suitable for inter-process synchronization.

### Related Functions

- `std.fs.Dir.createFile()` - Create file with options
- `std.fs.Dir.openFile()` - Open existing file
- `std.fs.Dir.atomicFile()` - Create temporary file for atomic updates
- `std.fs.Dir.rename()` - Atomically replace file

### Memory Safety

Always use `defer` to ensure files are closed, and `errdefer` to clean up on errors:

```zig
pub fn writeExclusiveWithCleanup(path: []const u8, data: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{
        .exclusive = true,
    });
    errdefer {
        file.close();
        // Clean up partial file on error
        std.fs.cwd().deleteFile(path) catch {};
    }
    defer file.close();

    try file.writeAll(data);
}
```

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: exclusive_creation
/// Create a file exclusively (fails if file already exists)
pub fn createExclusive(path: []const u8, data: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{
        .exclusive = true,
    });
    defer file.close();

    try file.writeAll(data);
}

/// Acquire a lock file (fails if lock already held)
pub fn acquireLock(lock_path: []const u8) !std.fs.File {
    return std.fs.cwd().createFile(lock_path, .{
        .exclusive = true,
    });
}

/// Release a lock file
pub fn releaseLock(lock: std.fs.File, lock_path: []const u8) void {
    lock.close();
    std.fs.cwd().deleteFile(lock_path) catch {};
}

/// Create a unique temporary file with random suffix
pub fn createUniqueFile(allocator: std.mem.Allocator, prefix: []const u8) !struct { path: []const u8, file: std.fs.File } {
    var prng = std.Random.DefaultPrng.init(@intCast(std.time.timestamp()));
    const random = prng.random();

    var attempts: usize = 0;
    while (attempts < 100) : (attempts += 1) {
        const suffix = random.int(u32);
        const path = try std.fmt.allocPrint(allocator, "{s}_{d}.tmp", .{ prefix, suffix });
        errdefer allocator.free(path);

        const file = std.fs.cwd().createFile(path, .{
            .exclusive = true,
        }) catch |err| {
            if (err == error.PathAlreadyExists) {
                allocator.free(path);
                continue;
            }
            return err;
        };

        return .{ .path = path, .file = file };
    }

    return error.TooManyAttempts;
}
// ANCHOR_END: exclusive_creation

// ANCHOR: atomic_operations
/// Safely update a configuration file using atomic rename
pub fn safeUpdateConfig(config_path: []const u8, new_content: []const u8, allocator: std.mem.Allocator) !void {
    // Create unique temp file
    const temp_path = try std.fmt.allocPrint(allocator, "{s}.tmp", .{config_path});
    defer allocator.free(temp_path);

    // Write to temp file with exclusive creation
    {
        const file = try std.fs.cwd().createFile(temp_path, .{
            .exclusive = true,
        });
        defer file.close();
        try file.writeAll(new_content);
    }

    // Atomically replace original file
    try std.fs.cwd().rename(temp_path, config_path);
}

/// Write exclusively with error cleanup
pub fn writeExclusiveWithCleanup(path: []const u8, data: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{
        .exclusive = true,
    });
    errdefer {
        file.close();
        // Clean up partial file on error
        std.fs.cwd().deleteFile(path) catch {};
    }
    defer file.close();

    try file.writeAll(data);
}
// ANCHOR_END: atomic_operations

// Tests

test "exclusive file creation" {
    const test_path = "/tmp/exclusive_test.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // First creation succeeds
    try createExclusive(test_path, "first write");

    // Second attempt fails
    const result = createExclusive(test_path, "second write");
    try std.testing.expectError(error.PathAlreadyExists, result);

    // Original content preserved
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();
    var buf: [32]u8 = undefined;
    const bytes_read = try file.read(&buf);
    try std.testing.expectEqualStrings("first write", buf[0..bytes_read]);
}

test "non-exclusive overwrites" {
    const test_path = "/tmp/non_exclusive_test.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // First write
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("first");
    }

    // Second write overwrites (default behavior)
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("second");
    }

    // Second content is present
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();
    var buf: [32]u8 = undefined;
    const bytes_read = try file.read(&buf);
    try std.testing.expectEqualStrings("second", buf[0..bytes_read]);
}

test "exclusive creation error handling" {
    const test_path = "/tmp/exclusive_error_test.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create initial file
    try createExclusive(test_path, "data");

    // Try to create again with error handling
    const result = std.fs.cwd().createFile(test_path, .{ .exclusive = true });
    if (result) |file| {
        file.close();
        try std.testing.expect(false); // Should not reach here
    } else |err| switch (err) {
        error.PathAlreadyExists => {
            // Expected error
        },
        else => return err,
    }
}

test "lock file acquire and release" {
    const lock_path = "/tmp/test.lock";
    defer std.fs.cwd().deleteFile(lock_path) catch {};

    // Acquire lock
    const lock = try acquireLock(lock_path);

    // Try to acquire again (should fail)
    const result = acquireLock(lock_path);
    try std.testing.expectError(error.PathAlreadyExists, result);

    // Release lock
    releaseLock(lock, lock_path);

    // Can acquire again after release
    const lock2 = try acquireLock(lock_path);
    releaseLock(lock2, lock_path);
}

test "unique file creation" {
    const allocator = std.testing.allocator;

    // Create first unique file
    const result1 = try createUniqueFile(allocator, "/tmp/unique");
    defer {
        result1.file.close();
        std.fs.cwd().deleteFile(result1.path) catch {};
        allocator.free(result1.path);
    }

    // Create second unique file (different path)
    const result2 = try createUniqueFile(allocator, "/tmp/unique");
    defer {
        result2.file.close();
        std.fs.cwd().deleteFile(result2.path) catch {};
        allocator.free(result2.path);
    }

    // Paths should be different
    try std.testing.expect(!std.mem.eql(u8, result1.path, result2.path));

    // Both files should exist
    try result1.file.writeAll("file1");
    try result2.file.writeAll("file2");
}

test "safe config update" {
    const allocator = std.testing.allocator;
    const config_path = "/tmp/config.json";
    defer std.fs.cwd().deleteFile(config_path) catch {};

    // Initial config
    try safeUpdateConfig(config_path, "{ \"version\": 1 }", allocator);

    // Verify initial content
    {
        const file = try std.fs.cwd().openFile(config_path, .{});
        defer file.close();
        var buf: [64]u8 = undefined;
        const bytes_read = try file.read(&buf);
        try std.testing.expectEqualStrings("{ \"version\": 1 }", buf[0..bytes_read]);
    }

    // Update config
    try safeUpdateConfig(config_path, "{ \"version\": 2 }", allocator);

    // Verify updated content
    {
        const file = try std.fs.cwd().openFile(config_path, .{});
        defer file.close();
        var buf: [64]u8 = undefined;
        const bytes_read = try file.read(&buf);
        try std.testing.expectEqualStrings("{ \"version\": 2 }", buf[0..bytes_read]);
    }
}

test "write exclusive with cleanup" {
    const test_path = "/tmp/exclusive_cleanup_test.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write successfully
    try writeExclusiveWithCleanup(test_path, "test data");

    // Verify content
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();
    var buf: [32]u8 = undefined;
    const bytes_read = try file.read(&buf);
    try std.testing.expectEqualStrings("test data", buf[0..bytes_read]);
}

test "multiple exclusive attempts" {
    const test_path = "/tmp/multi_exclusive_test.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Try creating multiple times
    try createExclusive(test_path, "first");

    var failures: usize = 0;
    var i: usize = 0;
    while (i < 10) : (i += 1) {
        createExclusive(test_path, "attempt") catch {
            failures += 1;
            continue;
        };
    }

    // All subsequent attempts should fail
    try std.testing.expectEqual(@as(usize, 10), failures);
}

test "exclusive with empty content" {
    const test_path = "/tmp/exclusive_empty_test.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create with empty content
    try createExclusive(test_path, "");

    // Verify file exists and is empty
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();
    const stat = try file.stat();
    try std.testing.expectEqual(@as(u64, 0), stat.size);
}

test "exclusive creation in subdirectory" {
    const dir_path = "/tmp/test_subdir";
    const test_path = "/tmp/test_subdir/exclusive.txt";

    // Create directory
    std.fs.cwd().makeDir(dir_path) catch {};
    defer std.fs.cwd().deleteTree(dir_path) catch {};

    // Create file exclusively
    const file = try std.fs.cwd().createFile(test_path, .{
        .exclusive = true,
    });
    defer file.close();
    try file.writeAll("content");

    // Verify
    const read_file = try std.fs.cwd().openFile(test_path, .{});
    defer read_file.close();
    var buf: [32]u8 = undefined;
    const bytes_read = try read_file.read(&buf);
    try std.testing.expectEqualStrings("content", buf[0..bytes_read]);
}

test "lock pattern with defer" {
    const lock_path = "/tmp/test_defer.lock";
    defer std.fs.cwd().deleteFile(lock_path) catch {};

    // Acquire and auto-release with defer
    {
        const lock = try acquireLock(lock_path);
        defer releaseLock(lock, lock_path);

        // Lock is held here
        const result = acquireLock(lock_path);
        try std.testing.expectError(error.PathAlreadyExists, result);
    }

    // Lock released, can acquire again
    const lock2 = try acquireLock(lock_path);
    releaseLock(lock2, lock_path);
}
```

---

## Recipe 5.6: Performing I/O Operations on a String {#recipe-5-6}

**Tags:** allocators, arraylist, data-structures, error-handling, files-io, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_6.zig`

### Problem

You want to use I/O operations (readers and writers) on in-memory string data instead of files, useful for testing, parsing, or building formatted output.

### Solution

### String Buffer I/O

```zig
/// Parse a number from a string buffer
pub fn parseFromString(data: []const u8) !u32 {
    var fbs = std.io.fixedBufferStream(data);
    const reader = fbs.reader();

    // Read line by line
    var line_buf: [64]u8 = undefined;
    const line = try reader.readUntilDelimiter(&line_buf, '\n');

    return try std.fmt.parseInt(u32, line, 10);
}

/// Format a log message using a buffer stream
pub fn formatMessage(allocator: std.mem.Allocator, level: []const u8, text: []const u8) ![]u8 {
    var buffer: [512]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    const timestamp = std.time.timestamp();
    try writer.print("[{d}] {s}: {s}", .{ timestamp, level, text });

    return try allocator.dupe(u8, fbs.getWritten());
}

/// Item for report building
pub const Item = struct {
    name: []const u8,
    price: f64,
};

/// Build a formatted report
pub fn buildReport(allocator: std.mem.Allocator, items: []const Item) ![]u8 {
    var buffer: [4096]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    try writer.writeAll("REPORT\n");
    try writer.writeAll("======\n\n");

    for (items, 0..) |item, i| {
        try writer.print("{d}. {s}: ${d:.2}\n", .{ i + 1, item.name, item.price });
    }

    try writer.writeAll("\n");

    return try allocator.dupe(u8, fbs.getWritten());
}
```

### Binary Buffers

```zig
/// Write data to any writer (for testing)
fn writeData(writer: anytype, value: u32) !void {
    try writer.print("Value: {d}\n", .{value});
}

/// Parse binary header from memory
pub fn parseHeader(data: []const u8) !struct { magic: u32, version: u16 } {
    var fbs = std.io.fixedBufferStream(data);
    const reader = fbs.reader();

    var buf: [4]u8 = undefined;
    _ = try reader.read(&buf);
    const magic = std.mem.readInt(u32, &buf, .little);

    var buf2: [2]u8 = undefined;
    _ = try reader.read(&buf2);
    const version = std.mem.readInt(u16, &buf2, .little);

    return .{ .magic = magic, .version = version };
}

/// Build a binary packet
pub fn buildPacket(allocator: std.mem.Allocator, msg_type: u8, payload: []const u8) ![]u8 {
    var buffer: [1024]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    // Write header
    try writer.writeByte(msg_type);

    var len_buf: [2]u8 = undefined;
    std.mem.writeInt(u16, &len_buf, @intCast(payload.len), .little);
    try writer.writeAll(&len_buf);

    // Write payload
    try writer.writeAll(payload);

    return try allocator.dupe(u8, fbs.getWritten());
}
```

### Discussion

### Fixed Buffer Streams

A `fixedBufferStream` wraps a fixed-size byte array and provides reader/writer interfaces:

```zig
var buffer: [256]u8 = undefined;
var fbs = std.io.fixedBufferStream(&buffer);

// Get reader and writer
const reader = fbs.reader();
const writer = fbs.writer();
```

The stream maintains a position that advances as you read or write:

```zig
var buf: [50]u8 = undefined;
var fbs = std.io.fixedBufferStream(&buf);
const writer = fbs.writer();

try writer.writeAll("First");
try writer.writeAll(" Second");

const written = fbs.getWritten();
// written is "First Second"
```

### Reading from String Buffers

You can treat existing string data as a readable stream:

```zig
pub fn parseFromString(data: []const u8) !u32 {
    var fbs = std.io.fixedBufferStream(data);
    const reader = fbs.reader();

    // Read line by line
    var line_buf: [64]u8 = undefined;
    const line = try reader.readUntilDelimiter(&line_buf, '\n');

    return try std.fmt.parseInt(u32, line, 10);
}

test "parse from string" {
    const data = "42\nmore data";
    const value = try parseFromString(data);
    try std.testing.expectEqual(@as(u32, 42), value);
}
```

### Writing to String Buffers

Build formatted strings using writer operations:

```zig
pub fn formatMessage(allocator: std.mem.Allocator, level: []const u8, text: []const u8) ![]u8 {
    var buffer: [512]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    const timestamp = std.time.timestamp();
    try writer.print("[{d}] {s}: {s}", .{ timestamp, level, text });

    return try allocator.dupe(u8, fbs.getWritten());
}
```

### Seeking Within Buffers

You can manipulate the stream position for random access:

```zig
test "seeking in buffer" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    // Write data
    try writer.writeAll("0123456789");

    // Seek to position 5
    fbs.pos = 5;

    // Overwrite from position 5
    try writer.writeAll("ABCDE");

    const written = fbs.getWritten();
    try std.testing.expectEqualStrings("01234ABCDE", written);
}
```

Reset to read what was written:

```zig
test "write then read" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    // Write data
    const writer = fbs.writer();
    try writer.writeAll("test data");

    // Reset to beginning
    fbs.pos = 0;

    // Read data
    const reader = fbs.reader();
    var read_buf: [10]u8 = undefined;
    const bytes_read = try reader.read(&read_buf);

    try std.testing.expectEqualStrings("test data", read_buf[0..bytes_read]);
}
```

### Practical Use Cases

**Building Complex Strings:**

```zig
pub fn buildReport(allocator: std.mem.Allocator, items: []const Item) ![]u8 {
    var buffer: [4096]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    try writer.writeAll("REPORT\n");
    try writer.writeAll("======\n\n");

    for (items, 0..) |item, i| {
        try writer.print("{d}. {s}: ${d:.2}\n", .{ i + 1, item.name, item.price });
    }

    try writer.writeAll("\n");

    return try allocator.dupe(u8, fbs.getWritten());
}
```

**Testing I/O Code:**

```zig
fn writeData(writer: anytype, value: u32) !void {
    try writer.print("Value: {d}\n", .{value});
}

test "writeData output" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try writeData(fbs.writer(), 42);

    try std.testing.expectEqualStrings("Value: 42\n", fbs.getWritten());
}
```

**Parsing Binary Data from Memory:**

```zig
pub fn parseHeader(data: []const u8) !struct { magic: u32, version: u16 } {
    var fbs = std.io.fixedBufferStream(data);
    const reader = fbs.reader();

    const magic = try reader.readInt(u32, .little);
    const version = try reader.readInt(u16, .little);

    return .{ .magic = magic, .version = version };
}
```

**Building Binary Data in Memory:**

```zig
pub fn buildPacket(allocator: std.mem.Allocator, msg_type: u8, payload: []const u8) ![]u8 {
    var buffer: [1024]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    // Write header
    try writer.writeByte(msg_type);
    try writer.writeInt(u16, @intCast(payload.len), .little);

    // Write payload
    try writer.writeAll(payload);

    return try allocator.dupe(u8, fbs.getWritten());
}
```

### Dynamic vs Fixed Buffers

For dynamic growth, use `std.ArrayList(u8)`:

```zig
test "dynamic string building" {
    const allocator = std.testing.allocator;
    var list: std.ArrayList(u8) = .{};
    defer list.deinit(allocator);

    const writer = list.writer(allocator);

    var i: u32 = 0;
    while (i < 100) : (i += 1) {
        try writer.print("{d} ", .{i});
    }

    const result = try list.toOwnedSlice(allocator);
    defer allocator.free(result);

    try std.testing.expect(result.len > 100);
}
```

Fixed buffers are stack-allocated and faster but have size limits. Dynamic buffers grow as needed but require an allocator.

### Error Handling

Fixed buffer streams can fail if you exceed capacity:

```zig
test "buffer overflow" {
    var buffer: [10]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    const result = writer.writeAll("This is too long");
    try std.testing.expectError(error.NoSpaceLeft, result);
}
```

### Comparison with Other Approaches

**Fixed Buffer Stream:**
- Stack-allocated, fast
- Fixed capacity
- Supports seek operations
- Best for bounded output

**ArrayList Writer:**
- Heap-allocated, slower
- Dynamic growth
- No seek support
- Best for unbounded output

**Direct Buffer Manipulation:**
```zig
// Manual approach
var buffer: [100]u8 = undefined;
var pos: usize = 0;

const text = "Hello";
@memcpy(buffer[pos..][0..text.len], text);
pos += text.len;
```

Using streams is more idiomatic and composable with generic writer code.

### Related Functions

- `std.io.fixedBufferStream()` - Create stream over fixed buffer
- `std.ArrayList(u8).writer()` - Dynamic buffer writer
- `std.io.countingWriter()` - Count bytes written
- `std.io.limitedReader()` - Limit bytes read

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: string_buffer_io
/// Parse a number from a string buffer
pub fn parseFromString(data: []const u8) !u32 {
    var fbs = std.io.fixedBufferStream(data);
    const reader = fbs.reader();

    // Read line by line
    var line_buf: [64]u8 = undefined;
    const line = try reader.readUntilDelimiter(&line_buf, '\n');

    return try std.fmt.parseInt(u32, line, 10);
}

/// Format a log message using a buffer stream
pub fn formatMessage(allocator: std.mem.Allocator, level: []const u8, text: []const u8) ![]u8 {
    var buffer: [512]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    const timestamp = std.time.timestamp();
    try writer.print("[{d}] {s}: {s}", .{ timestamp, level, text });

    return try allocator.dupe(u8, fbs.getWritten());
}

/// Item for report building
pub const Item = struct {
    name: []const u8,
    price: f64,
};

/// Build a formatted report
pub fn buildReport(allocator: std.mem.Allocator, items: []const Item) ![]u8 {
    var buffer: [4096]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    try writer.writeAll("REPORT\n");
    try writer.writeAll("======\n\n");

    for (items, 0..) |item, i| {
        try writer.print("{d}. {s}: ${d:.2}\n", .{ i + 1, item.name, item.price });
    }

    try writer.writeAll("\n");

    return try allocator.dupe(u8, fbs.getWritten());
}
// ANCHOR_END: string_buffer_io

// ANCHOR: binary_buffers
/// Write data to any writer (for testing)
fn writeData(writer: anytype, value: u32) !void {
    try writer.print("Value: {d}\n", .{value});
}

/// Parse binary header from memory
pub fn parseHeader(data: []const u8) !struct { magic: u32, version: u16 } {
    var fbs = std.io.fixedBufferStream(data);
    const reader = fbs.reader();

    var buf: [4]u8 = undefined;
    _ = try reader.read(&buf);
    const magic = std.mem.readInt(u32, &buf, .little);

    var buf2: [2]u8 = undefined;
    _ = try reader.read(&buf2);
    const version = std.mem.readInt(u16, &buf2, .little);

    return .{ .magic = magic, .version = version };
}

/// Build a binary packet
pub fn buildPacket(allocator: std.mem.Allocator, msg_type: u8, payload: []const u8) ![]u8 {
    var buffer: [1024]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    // Write header
    try writer.writeByte(msg_type);

    var len_buf: [2]u8 = undefined;
    std.mem.writeInt(u16, &len_buf, @intCast(payload.len), .little);
    try writer.writeAll(&len_buf);

    // Write payload
    try writer.writeAll(payload);

    return try allocator.dupe(u8, fbs.getWritten());
}
// ANCHOR_END: binary_buffers

// Tests

test "basic string I/O" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    // Write to buffer
    const writer = fbs.writer();
    try writer.writeAll("Hello, ");
    try writer.print("{s}!", .{"World"});

    // Get written data
    const written = fbs.getWritten();
    try std.testing.expectEqualStrings("Hello, World!", written);
}

test "parse from string" {
    const data = "42\nmore data";
    const value = try parseFromString(data);
    try std.testing.expectEqual(@as(u32, 42), value);
}

test "format message" {
    const allocator = std.testing.allocator;
    const result = try formatMessage(allocator, "INFO", "test message");
    defer allocator.free(result);

    // Check that it contains the expected parts
    try std.testing.expect(std.mem.indexOf(u8, result, "INFO") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "test message") != null);
}

test "seeking in buffer" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    // Write data
    try writer.writeAll("0123456789");

    // Seek to position 5
    fbs.pos = 5;

    // Overwrite from position 5
    try writer.writeAll("ABCDE");

    const written = fbs.getWritten();
    try std.testing.expectEqualStrings("01234ABCDE", written);
}

test "write then read" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    // Write data
    const writer = fbs.writer();
    try writer.writeAll("test data");

    // Get what was written
    const written = fbs.getWritten();

    // Create new stream over written data for reading
    var read_fbs = std.io.fixedBufferStream(written);
    const reader = read_fbs.reader();
    var read_buf: [10]u8 = undefined;
    const bytes_read = try reader.read(&read_buf);

    try std.testing.expectEqualStrings("test data", read_buf[0..bytes_read]);
}

test "build report" {
    const allocator = std.testing.allocator;

    const items = [_]Item{
        .{ .name = "Apple", .price = 1.50 },
        .{ .name = "Banana", .price = 0.75 },
        .{ .name = "Orange", .price = 2.00 },
    };

    const report = try buildReport(allocator, &items);
    defer allocator.free(report);

    try std.testing.expect(std.mem.indexOf(u8, report, "REPORT") != null);
    try std.testing.expect(std.mem.indexOf(u8, report, "Apple") != null);
    try std.testing.expect(std.mem.indexOf(u8, report, "1.50") != null);
}

test "writeData output" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try writeData(fbs.writer(), 42);

    try std.testing.expectEqualStrings("Value: 42\n", fbs.getWritten());
}

test "parse binary header" {
    var buffer: [6]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    // Write header
    var magic_buf: [4]u8 = undefined;
    std.mem.writeInt(u32, &magic_buf, 0xDEADBEEF, .little);
    try writer.writeAll(&magic_buf);

    var version_buf: [2]u8 = undefined;
    std.mem.writeInt(u16, &version_buf, 123, .little);
    try writer.writeAll(&version_buf);

    // Parse it
    const header = try parseHeader(&buffer);
    try std.testing.expectEqual(@as(u32, 0xDEADBEEF), header.magic);
    try std.testing.expectEqual(@as(u16, 123), header.version);
}

test "build packet" {
    const allocator = std.testing.allocator;
    const packet = try buildPacket(allocator, 5, "hello");
    defer allocator.free(packet);

    // Verify packet structure
    try std.testing.expectEqual(@as(u8, 5), packet[0]); // msg_type

    const payload_len = std.mem.readInt(u16, packet[1..3], .little);
    try std.testing.expectEqual(@as(u16, 5), payload_len);

    try std.testing.expectEqualStrings("hello", packet[3..]);
}

test "dynamic string building" {
    const allocator = std.testing.allocator;
    var list: std.ArrayList(u8) = .{};
    defer list.deinit(allocator);

    const writer = list.writer(allocator);

    var i: u32 = 0;
    while (i < 10) : (i += 1) {
        try writer.print("{d} ", .{i});
    }

    const result = try list.toOwnedSlice(allocator);
    defer allocator.free(result);

    try std.testing.expectEqualStrings("0 1 2 3 4 5 6 7 8 9 ", result);
}

test "buffer overflow" {
    var buffer: [10]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    const result = writer.writeAll("This is too long");
    try std.testing.expectError(error.NoSpaceLeft, result);
}

test "multiple writes and reads" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    // Write multiple items
    const writer = fbs.writer();
    try writer.writeAll("line 1\n");
    try writer.writeAll("line 2\n");
    try writer.writeAll("line 3\n");

    // Reset and read
    fbs.pos = 0;
    const reader = fbs.reader();

    var line_buf: [20]u8 = undefined;

    const line1 = try reader.readUntilDelimiter(&line_buf, '\n');
    try std.testing.expectEqualStrings("line 1", line1);

    const line2 = try reader.readUntilDelimiter(&line_buf, '\n');
    try std.testing.expectEqualStrings("line 2", line2);

    const line3 = try reader.readUntilDelimiter(&line_buf, '\n');
    try std.testing.expectEqualStrings("line 3", line3);
}

test "getWritten vs getPos" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    try writer.writeAll("test");

    // pos tracks current position
    try std.testing.expectEqual(@as(usize, 4), fbs.pos);

    // getWritten returns slice up to current position
    try std.testing.expectEqualStrings("test", fbs.getWritten());
}

test "reset and reuse buffer" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    // First use
    try writer.writeAll("first");
    try std.testing.expectEqualStrings("first", fbs.getWritten());

    // Reset
    fbs.reset();
    try std.testing.expectEqual(@as(usize, 0), fbs.pos);

    // Second use
    try writer.writeAll("second");
    try std.testing.expectEqualStrings("second", fbs.getWritten());
}

test "reader read methods" {
    const data = "Hello\nWorld\n123";
    var fbs = std.io.fixedBufferStream(data);
    const reader = fbs.reader();

    // Read until delimiter
    var buf: [20]u8 = undefined;
    const line1 = try reader.readUntilDelimiter(&buf, '\n');
    try std.testing.expectEqualStrings("Hello", line1);

    // Read exact number of bytes
    var exact: [5]u8 = undefined;
    try reader.readNoEof(&exact);
    try std.testing.expectEqualStrings("World", &exact);
}

test "counting bytes written" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    const start_pos = fbs.pos;
    try writer.writeAll("test data");
    const bytes_written = fbs.pos - start_pos;

    try std.testing.expectEqual(@as(usize, 9), bytes_written);
}

test "partial reads" {
    const data = "0123456789";
    var fbs = std.io.fixedBufferStream(data);
    const reader = fbs.reader();

    var buf: [5]u8 = undefined;

    // First read
    const read1 = try reader.read(&buf);
    try std.testing.expectEqual(@as(usize, 5), read1);
    try std.testing.expectEqualStrings("01234", buf[0..read1]);

    // Second read
    const read2 = try reader.read(&buf);
    try std.testing.expectEqual(@as(usize, 5), read2);
    try std.testing.expectEqualStrings("56789", buf[0..read2]);

    // Third read (EOF)
    const read3 = try reader.read(&buf);
    try std.testing.expectEqual(@as(usize, 0), read3);
}

test "mixing read and write operations" {
    var buffer: [100]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    // Write initial data
    try fbs.writer().writeAll("initial");

    // Read from beginning
    fbs.pos = 0;
    var read_buf: [7]u8 = undefined;
    try fbs.reader().readNoEof(&read_buf);
    try std.testing.expectEqualStrings("initial", &read_buf);

    // Continue writing
    try fbs.writer().writeAll(" more");

    try std.testing.expectEqualStrings("initial more", fbs.getWritten());
}
```

---

## Recipe 5.7: Reading and Writing Compressed Datafiles {#recipe-5-7}

**Tags:** allocators, arraylist, c-interop, data-structures, error-handling, files-io, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_7.zig`

### Problem

You need to read and decompress files compressed with gzip or zlib.

### Solution

### Decompress Gzip

```zig
/// Read and decompress a gzip file
pub fn readGzipFile(path: []const u8, allocator: std.mem.Allocator) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    var reader_buffer: [8192]u8 = undefined;
    var decompress_buffer: [std.compress.flate.max_window_len]u8 = undefined;

    var file_reader = file.reader(&reader_buffer);
    var decompressor = std.compress.flate.Decompress.init(
        &file_reader.interface,
        .gzip,
        &decompress_buffer
    );

    // Read in chunks until EOF
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    var chunk_buffer: [4096]u8 = undefined;
    while (true) {
        const n = decompressor.reader.readSliceShort(&chunk_buffer) catch |err| switch (err) {
            error.ReadFailed => break,
            else => return err,
        };
        if (n == 0) break;
        try result.appendSlice(allocator, chunk_buffer[0..n]);
    }

    return result.toOwnedSlice(allocator);
}

/// Read and decompress a zlib file
pub fn readZlibFile(path: []const u8, allocator: std.mem.Allocator) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    var reader_buffer: [8192]u8 = undefined;
    var decompress_buffer: [std.compress.flate.max_window_len]u8 = undefined;

    var file_reader = file.reader(&reader_buffer);
    var decompressor = std.compress.flate.Decompress.init(
        &file_reader.interface,
        .zlib,
        &decompress_buffer
    );

    // Read in chunks until EOF
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    var chunk_buffer: [4096]u8 = undefined;
    while (true) {
        const n = decompressor.reader.readSliceShort(&chunk_buffer) catch |err| switch (err) {
            error.ReadFailed => break,
            else => return err,
        };
        if (n == 0) break;
        try result.appendSlice(allocator, chunk_buffer[0..n]);
    }

    return result.toOwnedSlice(allocator);
}
```

### Discussion

### Decompression Formats

Zig's standard library supports decompressing three formats via `std.compress.flate.Container`:

- `.gzip` - Standard gzip format (most common)
- `.zlib` - Zlib format (used in PNG, some protocols)
- `.raw` - Raw DEFLATE data (no headers or checksums)

All three formats use the same DEFLATE algorithm but differ in headers and checksums.

### Buffer Requirements

The `Decompress.init()` function requires a buffer for the sliding window:

```zig
var decompress_buffer: [std.compress.flate.max_window_len]u8 = undefined;
```

The constant `max_window_len` is 65536 bytes (64 KB), which is the maximum DEFLATE window size. You can also pass an empty slice to use direct mode (no windowing), but this is slower:

```zig
// Direct mode (slower, no extra buffer needed)
var decompressor = std.compress.flate.Decompress.init(
    &file_reader.interface,
    .gzip,
    &.{} // empty slice = direct mode
);
```

### Streaming Decompression

```zig
/// Stream decompress a gzip file to another file
pub fn streamDecompressFile(src_path: []const u8, dst_path: []const u8) !void {
    const src = try std.fs.cwd().openFile(src_path, .{});
    defer src.close();

    const dst = try std.fs.cwd().createFile(dst_path, .{});
    defer dst.close();

    var reader_buffer: [8192]u8 = undefined;
    var decompress_buffer: [std.compress.flate.max_window_len]u8 = undefined;

    var src_reader = src.reader(&reader_buffer);
    var decompressor = std.compress.flate.Decompress.init(
        &src_reader.interface,
        .gzip,
        &decompress_buffer
    );

    // Stream in chunks
    var chunk_buffer: [4096]u8 = undefined;
    while (true) {
        const n = decompressor.reader.readSliceShort(&chunk_buffer) catch |err| switch (err) {
            error.ReadFailed => break,
            else => return err,
        };
        if (n == 0) break;
        try dst.writeAll(chunk_buffer[0..n]);
    }
}
```

### Error Handling

```zig
/// Safe decompression with error handling
pub fn safeDecompress(path: []const u8, allocator: std.mem.Allocator) ![]u8 {
    return readGzipFile(path, allocator) catch |err| switch (err) {
        error.BadGzipHeader => {
            std.debug.print("Invalid gzip file format\n", .{});
            return error.InvalidFormat;
        },
        error.WrongGzipChecksum => {
            std.debug.print("Corrupted gzip file (checksum mismatch)\n", .{});
            return error.CorruptedData;
        },
        error.EndOfStream => {
            std.debug.print("Truncated gzip file\n", .{});
            return error.TruncatedFile;
        },
        else => return err,
    };
}
```

Common error types:
- `error.BadGzipHeader` / `error.BadZlibHeader` - Invalid file format
- `error.WrongGzipChecksum` / `error.WrongZlibChecksum` - Data corruption
- `error.EndOfStream` - Truncated file
- `error.InvalidCode` - Malformed compressed data

### Memory Management

Always free decompressed data:

```zig
test "proper cleanup" {
    const allocator = std.testing.allocator;

    const data = try readGzipFile("test.gz", allocator);
    defer allocator.free(data); // Always free!

    // Use data...
}
```

For large files, consider streaming to avoid memory issues:

```zig
// Bad: Loads entire file into memory
const data = try readGzipFile("huge.gz", allocator);

// Good: Streams to output file
try streamDecompressFile("huge.gz", "huge.txt");
```

### Platform Compatibility

Zig's decompression is pure Zig and works on all platforms:
- No external dependencies
- Same behavior on all platforms
- Compatible with standard gzip/zlib tools

Verify compatibility:
```bash
# Compress with system gzip
gzip -c input.txt > input.gz

# Decompress with Zig
zig run decompress.zig -- input.gz output.txt

# Verify
diff input.txt output.txt
```

### Performance Considerations

**Buffer Sizes:**
- Larger reader buffers (8-16 KB) improve performance
- The decompress buffer must be exactly `max_window_len`

**Memory vs Speed:**
- Use streaming for large files (saves memory)
- Use `readAlloc` for small files (faster, simpler)

**Direct vs Buffered Mode:**
```zig
// Buffered mode (faster)
var buffer: [std.compress.flate.max_window_len]u8 = undefined;
var dec = Decompress.init(&reader, .gzip, &buffer);

// Direct mode (slower, less memory)
var dec = Decompress.init(&reader, .gzip, &.{});
```

### Note on Compression

As of Zig 0.15.2, the compression side of `std.compress.flate` is not yet fully implemented. For creating gzip/zlib files, you'll need to:

1. Use external tools (`gzip`, `zlib`)
2. Wait for Zig stdlib completion
3. Use a third-party Zig compression library

Decompression (reading) works perfectly and is production-ready.

### Related Functions

- `std.compress.flate.Decompress.init()` - Initialize decompressor
- `std.compress.flate.Container` - Format types (.gzip, .zlib, .raw)
- `std.compress.flate.max_window_len` - Required buffer size constant
- `std.Io.Reader.readAlloc()` - Read all decompressed data
- `std.Io.Reader.readSliceShort()` - Read chunk of decompressed data

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: decompress_gzip
/// Read and decompress a gzip file
pub fn readGzipFile(path: []const u8, allocator: std.mem.Allocator) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    var reader_buffer: [8192]u8 = undefined;
    var decompress_buffer: [std.compress.flate.max_window_len]u8 = undefined;

    var file_reader = file.reader(&reader_buffer);
    var decompressor = std.compress.flate.Decompress.init(
        &file_reader.interface,
        .gzip,
        &decompress_buffer
    );

    // Read in chunks until EOF
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    var chunk_buffer: [4096]u8 = undefined;
    while (true) {
        const n = decompressor.reader.readSliceShort(&chunk_buffer) catch |err| switch (err) {
            error.ReadFailed => break,
            else => return err,
        };
        if (n == 0) break;
        try result.appendSlice(allocator, chunk_buffer[0..n]);
    }

    return result.toOwnedSlice(allocator);
}

/// Read and decompress a zlib file
pub fn readZlibFile(path: []const u8, allocator: std.mem.Allocator) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    var reader_buffer: [8192]u8 = undefined;
    var decompress_buffer: [std.compress.flate.max_window_len]u8 = undefined;

    var file_reader = file.reader(&reader_buffer);
    var decompressor = std.compress.flate.Decompress.init(
        &file_reader.interface,
        .zlib,
        &decompress_buffer
    );

    // Read in chunks until EOF
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    var chunk_buffer: [4096]u8 = undefined;
    while (true) {
        const n = decompressor.reader.readSliceShort(&chunk_buffer) catch |err| switch (err) {
            error.ReadFailed => break,
            else => return err,
        };
        if (n == 0) break;
        try result.appendSlice(allocator, chunk_buffer[0..n]);
    }

    return result.toOwnedSlice(allocator);
}
// ANCHOR_END: decompress_gzip

// ANCHOR: stream_decompress
/// Stream decompress a gzip file to another file
pub fn streamDecompressFile(src_path: []const u8, dst_path: []const u8) !void {
    const src = try std.fs.cwd().openFile(src_path, .{});
    defer src.close();

    const dst = try std.fs.cwd().createFile(dst_path, .{});
    defer dst.close();

    var reader_buffer: [8192]u8 = undefined;
    var decompress_buffer: [std.compress.flate.max_window_len]u8 = undefined;

    var src_reader = src.reader(&reader_buffer);
    var decompressor = std.compress.flate.Decompress.init(
        &src_reader.interface,
        .gzip,
        &decompress_buffer
    );

    // Stream in chunks
    var chunk_buffer: [4096]u8 = undefined;
    while (true) {
        const n = decompressor.reader.readSliceShort(&chunk_buffer) catch |err| switch (err) {
            error.ReadFailed => break,
            else => return err,
        };
        if (n == 0) break;
        try dst.writeAll(chunk_buffer[0..n]);
    }
}
// ANCHOR_END: stream_decompress

// ANCHOR: error_handling
/// Safe decompression with error handling
pub fn safeDecompress(path: []const u8, allocator: std.mem.Allocator) ![]u8 {
    return readGzipFile(path, allocator) catch |err| switch (err) {
        error.BadGzipHeader => {
            std.debug.print("Invalid gzip file format\n", .{});
            return error.InvalidFormat;
        },
        error.WrongGzipChecksum => {
            std.debug.print("Corrupted gzip file (checksum mismatch)\n", .{});
            return error.CorruptedData;
        },
        error.EndOfStream => {
            std.debug.print("Truncated gzip file\n", .{});
            return error.TruncatedFile;
        },
        else => return err,
    };
}
// ANCHOR_END: error_handling

// Helper to create gzipped test files using system gzip
fn createGzipFile(path: []const u8, content: []const u8, allocator: std.mem.Allocator) !void {
    // Write uncompressed file
    const temp_path = try std.fmt.allocPrint(allocator, "{s}.tmp", .{path});
    defer allocator.free(temp_path);

    {
        const file = try std.fs.cwd().createFile(temp_path, .{});
        defer file.close();
        try file.writeAll(content);
    }

    // Compress with system gzip
    const result = try std.process.Child.run(.{
        .allocator = allocator,
        .argv = &.{ "gzip", "-c", temp_path },
    });
    defer allocator.free(result.stdout);
    defer allocator.free(result.stderr);

    // Write compressed output
    {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
        try file.writeAll(result.stdout);
    }

    // Cleanup temp file
    std.fs.cwd().deleteFile(temp_path) catch {};
}

// Tests

test "read gzip file" {
    const allocator = std.testing.allocator;
    const test_path = "/tmp/test_read.gz";
    const test_content = "Hello, Gzip World!";

    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create gzipped file
    try createGzipFile(test_path, test_content, allocator);

    // Read and decompress
    const data = try readGzipFile(test_path, allocator);
    defer allocator.free(data);

    try std.testing.expectEqualStrings(test_content, data);
}

test "read zlib file" {
    const allocator = std.testing.allocator;
    const test_path = "/tmp/test_zlib.zz";
    const test_content = "Zlib test data";

    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create temp file
    const temp_path = "/tmp/test_zlib_temp.txt";
    {
        const file = try std.fs.cwd().createFile(temp_path, .{});
        defer file.close();
        try file.writeAll(test_content);
    }
    defer std.fs.cwd().deleteFile(temp_path) catch {};

    // Compress with zlib (using python for zlib compression)
    const result = try std.process.Child.run(.{
        .allocator = allocator,
        .argv = &.{ "python3", "-c", "import zlib, sys; sys.stdout.buffer.write(zlib.compress(open(sys.argv[1], 'rb').read()))", temp_path },
    });
    defer allocator.free(result.stdout);
    defer allocator.free(result.stderr);

    // Write compressed output
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll(result.stdout);
    }

    // Read and decompress
    const data = try readZlibFile(test_path, allocator);
    defer allocator.free(data);

    try std.testing.expectEqualStrings(test_content, data);
}

test "stream decompress file" {
    const allocator = std.testing.allocator;
    const src_path = "/tmp/test_stream_src.gz";
    const dst_path = "/tmp/test_stream_dst.txt";
    const test_content = "Stream decompression test\n" ** 100;

    defer std.fs.cwd().deleteFile(src_path) catch {};
    defer std.fs.cwd().deleteFile(dst_path) catch {};

    // Create gzipped file
    try createGzipFile(src_path, test_content, allocator);

    // Stream decompress
    try streamDecompressFile(src_path, dst_path);

    // Verify
    const result = try std.fs.cwd().readFileAlloc(allocator, dst_path, 10 * 1024 * 1024);
    defer allocator.free(result);

    try std.testing.expectEqualStrings(test_content, result);
}

test "read empty gzip file" {
    const allocator = std.testing.allocator;
    const test_path = "/tmp/test_empty.gz";

    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create empty gzipped file
    try createGzipFile(test_path, "", allocator);

    // Read
    const data = try readGzipFile(test_path, allocator);
    defer allocator.free(data);

    try std.testing.expectEqual(@as(usize, 0), data.len);
}

test "read large gzip file" {
    const allocator = std.testing.allocator;
    const test_path = "/tmp/test_large.gz";

    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create large content
    var large_content: std.ArrayList(u8) = .{};
    defer large_content.deinit(allocator);

    var i: usize = 0;
    while (i < 10000) : (i += 1) {
        try large_content.writer(allocator).print("Line {d}\n", .{i});
    }

    // Create gzipped file
    try createGzipFile(test_path, large_content.items, allocator);

    // Read and decompress
    const data = try readGzipFile(test_path, allocator);
    defer allocator.free(data);

    try std.testing.expectEqualStrings(large_content.items, data);
}

test "read binary gzip data" {
    const allocator = std.testing.allocator;
    const test_path = "/tmp/test_binary.gz";

    // Create binary test data
    var binary_data: [256]u8 = undefined;
    for (&binary_data, 0..) |*byte, i| {
        byte.* = @intCast(i);
    }

    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create gzipped file
    try createGzipFile(test_path, &binary_data, allocator);

    // Read and decompress
    const data = try readGzipFile(test_path, allocator);
    defer allocator.free(data);

    try std.testing.expectEqualSlices(u8, &binary_data, data);
}

test "multiple reads from same file" {
    const allocator = std.testing.allocator;
    const test_path = "/tmp/test_multiple.gz";
    const test_content = "Multiple reads test";

    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create gzipped file
    try createGzipFile(test_path, test_content, allocator);

    // Read multiple times
    var i: usize = 0;
    while (i < 3) : (i += 1) {
        const data = try readGzipFile(test_path, allocator);
        defer allocator.free(data);
        try std.testing.expectEqualStrings(test_content, data);
    }
}

test "decompress unicode content" {
    const allocator = std.testing.allocator;
    const test_path = "/tmp/test_unicode.gz";
    const test_content = "Hello, 世界! Привет мир! 🚀";

    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create gzipped file
    try createGzipFile(test_path, test_content, allocator);

    // Read and decompress
    const data = try readGzipFile(test_path, allocator);
    defer allocator.free(data);

    try std.testing.expectEqualStrings(test_content, data);
}

test "stream chunks correctly" {
    const allocator = std.testing.allocator;
    const src_path = "/tmp/test_chunks.gz";
    const dst_path = "/tmp/test_chunks_out.txt";

    // Create content larger than chunk size
    const test_content = "x" ** 10000;

    defer std.fs.cwd().deleteFile(src_path) catch {};
    defer std.fs.cwd().deleteFile(dst_path) catch {};

    // Create gzipped file
    try createGzipFile(src_path, test_content, allocator);

    // Stream decompress
    try streamDecompressFile(src_path, dst_path);

    // Verify
    const result = try std.fs.cwd().readFileAlloc(allocator, dst_path, 10 * 1024 * 1024);
    defer allocator.free(result);

    try std.testing.expectEqualStrings(test_content, result);
}

test "gzip file with multiple lines" {
    const allocator = std.testing.allocator;
    const test_path = "/tmp/test_lines.gz";
    const test_content = "line 1\nline 2\nline 3\n";

    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create gzipped file
    try createGzipFile(test_path, test_content, allocator);

    // Read
    const data = try readGzipFile(test_path, allocator);
    defer allocator.free(data);

    // Count lines
    var lines = std.mem.splitScalar(u8, data, '\n');
    var count: usize = 0;
    while (lines.next()) |line| {
        if (line.len > 0) count += 1;
    }

    try std.testing.expectEqual(@as(usize, 3), count);
}
```

---

## Recipe 5.8: Iterating Over Fixed-Sized Records {#recipe-5-8}

**Tags:** allocators, c-interop, comptime, error-handling, files-io, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_8.zig`

### Problem

You need to read a binary file containing fixed-size records, processing them one at a time or in batches.

### Solution

### Record Iterator

```zig
/// Basic record iterator
pub fn RecordIterator(comptime T: type) type {
    return struct {
        file: std.fs.File,
        buffer: [@sizeOf(T)]u8 = undefined,

        const Self = @This();

        pub fn init(file: std.fs.File) Self {
            return .{ .file = file };
        }

        pub fn next(self: *Self) !?T {
            const bytes_read = try self.file.read(&self.buffer);

            if (bytes_read == 0) return null;
            if (bytes_read < @sizeOf(T)) return error.PartialRecord;

            return @bitCast(self.buffer);
        }
    };
}

/// Buffered record iterator for better performance
pub fn BufferedRecordIterator(comptime T: type, comptime buffer_count: usize) type {
    return struct {
        file: std.fs.File,
        buffer: [buffer_count * @sizeOf(T)]u8 = undefined,
        position: usize = 0,
        count: usize = 0,

        const Self = @This();
        const record_size = @sizeOf(T);

        pub fn init(file: std.fs.File) Self {
            return .{ .file = file };
        }

        pub fn next(self: *Self) !?T {
            // Refill buffer if empty
            if (self.position >= self.count) {
                const bytes_read = try self.file.read(&self.buffer);
                if (bytes_read == 0) return null;

                self.count = bytes_read / record_size;
                self.position = 0;

                // Check for partial record
                if (bytes_read % record_size != 0) {
                    return error.PartialRecord;
                }
            }

            const offset = self.position * record_size;
            const record_bytes = self.buffer[offset..][0..record_size];
            self.position += 1;

            return @bitCast(record_bytes.*);
        }
    };
}
```

### Random Access

```zig
/// Random-access record file
pub fn RecordFile(comptime T: type) type {
    return struct {
        file: std.fs.File,

        const Self = @This();
        const record_size = @sizeOf(T);

        pub fn init(file: std.fs.File) Self {
            return .{ .file = file };
        }

        pub fn seekToRecord(self: *Self, index: usize) !void {
            try self.file.seekTo(index * record_size);
        }

        pub fn readRecord(self: *Self) !T {
            var buffer: [record_size]u8 = undefined;
            const bytes_read = try self.file.read(&buffer);

            if (bytes_read < record_size) return error.PartialRecord;

            return @bitCast(buffer);
        }

        pub fn writeRecord(self: *Self, record: T) !void {
            const bytes: [record_size]u8 = @bitCast(record);
            try self.file.writeAll(&bytes);
        }

        pub fn getRecordCount(self: *Self) !usize {
            const size = (try self.file.stat()).size;
            return size / record_size;
        }
    };
}

/// Read a record in reverse order
pub fn readRecordReverse(comptime T: type, file: std.fs.File, index: usize) !T {
    const record_size = @sizeOf(T);
    const offset = index * record_size;

    try file.seekTo(offset);

    var buffer: [record_size]u8 = undefined;
    const bytes_read = try file.read(&buffer);

    if (bytes_read < record_size) return error.PartialRecord;

    return @bitCast(buffer);
}
```

### Batch Processing

```zig
/// Process records in batches
pub fn processBatch(
    comptime T: type,
    file: std.fs.File,
    allocator: std.mem.Allocator,
    batch_size: usize,
    processor: *const fn ([]const T) anyerror!void,
) !void {
    const record_size = @sizeOf(T);
    const buffer = try allocator.alignedAlloc(u8, std.mem.Alignment.of(T), batch_size * record_size);
    defer allocator.free(buffer);

    while (true) {
        const bytes_read = try file.read(buffer);
        if (bytes_read == 0) break;

        const record_count = bytes_read / record_size;
        if (bytes_read % record_size != 0) return error.PartialRecord;

        // Cast buffer to record slice
        const records = std.mem.bytesAsSlice(T, buffer[0 .. record_count * record_size]);
        try processor(records);
    }
}
```

### Discussion

### Fixed-Size Record Formats

Binary files often store data as sequences of fixed-size records. Each record has the same size, making it easy to seek and iterate:

```zig
const PlayerRecord = extern struct {
    player_id: u32,
    score: u32,
    level: u16,
    lives: u8,
    padding: u8 = 0,
};

comptime {
    // Ensure record has expected size
    std.debug.assert(@sizeOf(PlayerRecord) == 12);
}
```

Use `extern struct` to ensure C-compatible memory layout without padding reordering.

### Basic Record Iterator

The simplest iterator reads one record at a time:

```zig
pub fn RecordIterator(comptime T: type) type {
    return struct {
        file: std.fs.File,
        buffer: [@sizeOf(T)]u8 = undefined,

        const Self = @This();

        pub fn init(file: std.fs.File) Self {
            return .{ .file = file };
        }

        pub fn next(self: *Self) !?T {
            const bytes_read = try self.file.read(&self.buffer);

            if (bytes_read == 0) return null;
            if (bytes_read < @sizeOf(T)) return error.PartialRecord;

            return @bitCast(self.buffer);
        }
    };
}
```

Usage:
```zig
const file = try std.fs.cwd().openFile("data.bin", .{});
defer file.close();

var iter = RecordIterator(PlayerRecord).init(file);
while (try iter.next()) |record| {
    std.debug.print("Player {d}: score {d}\n", .{ record.player_id, record.score });
}
```

### Buffered Record Iterator

For better performance, read multiple records at once:

```zig
pub fn BufferedRecordIterator(comptime T: type, comptime buffer_count: usize) type {
    return struct {
        file: std.fs.File,
        buffer: [buffer_count * @sizeOf(T)]u8 = undefined,
        position: usize = 0,
        count: usize = 0,

        const Self = @This();
        const record_size = @sizeOf(T);

        pub fn init(file: std.fs.File) Self {
            return .{ .file = file };
        }

        pub fn next(self: *Self) !?T {
            // Refill buffer if empty
            if (self.position >= self.count) {
                const bytes_read = try self.file.read(&self.buffer);
                if (bytes_read == 0) return null;

                self.count = bytes_read / record_size;
                self.position = 0;

                // Check for partial record
                if (bytes_read % record_size != 0) {
                    return error.PartialRecord;
                }
            }

            const offset = self.position * record_size;
            const record_bytes = self.buffer[offset..][0..record_size];
            self.position += 1;

            return @bitCast(record_bytes.*);
        }
    };
}
```

### Seeking to Specific Records

Jump directly to a record by index:

```zig
pub fn RecordFile(comptime T: type) type {
    return struct {
        file: std.fs.File,

        const Self = @This();
        const record_size = @sizeOf(T);

        pub fn init(file: std.fs.File) Self {
            return .{ .file = file };
        }

        pub fn seekToRecord(self: *Self, index: usize) !void {
            try self.file.seekTo(index * record_size);
        }

        pub fn readRecord(self: *Self) !T {
            var buffer: [record_size]u8 = undefined;
            const bytes_read = try self.file.read(&buffer);

            if (bytes_read < record_size) return error.PartialRecord;

            return @bitCast(buffer);
        }

        pub fn writeRecord(self: *Self, record: T) !void {
            const bytes: [record_size]u8 = @bitCast(record);
            try self.file.writeAll(&bytes);
        }

        pub fn getRecordCount(self: *Self) !usize {
            const size = (try self.file.stat()).size;
            return size / record_size;
        }
    };
}
```

Usage:
```zig
var record_file = RecordFile(PlayerRecord).init(file);

// Jump to record 100
try record_file.seekToRecord(100);
const record = try record_file.readRecord();

// Get total number of records
const total = try record_file.getRecordCount();
```

### Reading Records in Reverse

Iterate backwards through records:

```zig
pub fn readRecordReverse(comptime T: type, file: std.fs.File, index: usize) !T {
    const record_size = @sizeOf(T);
    const offset = index * record_size;

    try file.seekTo(offset);

    var buffer: [record_size]u8 = undefined;
    const bytes_read = try file.read(&buffer);

    if (bytes_read < record_size) return error.PartialRecord;

    return @bitCast(buffer);
}

pub fn reverseIterator(comptime T: type, file: std.fs.File) !struct {
    file: std.fs.File,
    count: usize,
    index: usize,

    pub fn next(self: *@This()) !?T {
        if (self.index == 0) return null;
        self.index -= 1;
        return readRecordReverse(T, self.file, self.index);
    }
} {
    const size = (try file.stat()).size;
    const record_count = size / @sizeOf(T);

    return .{
        .file = file,
        .count = record_count,
        .index = record_count,
    };
}
```

### Handling Different Endianness

Convert byte order when reading cross-platform files:

```zig
const NetworkRecord = extern struct {
    id: u32,
    timestamp: u64,
    value: u16,
    padding: u16 = 0,

    pub fn fromBigEndian(self: NetworkRecord) NetworkRecord {
        return .{
            .id = std.mem.bigToNative(u32, self.id),
            .timestamp = std.mem.bigToNative(u64, self.timestamp),
            .value = std.mem.bigToNative(u16, self.value),
        };
    }

    pub fn toBigEndian(self: NetworkRecord) NetworkRecord {
        return .{
            .id = std.mem.nativeToBig(u32, self.id),
            .timestamp = std.mem.nativeToBig(u64, self.timestamp),
            .value = std.mem.nativeToBig(u16, self.value),
        };
    }
};
```

### Batch Processing Records

Process records in batches for better performance:

```zig
pub fn processBatch(
    comptime T: type,
    file: std.fs.File,
    allocator: std.mem.Allocator,
    batch_size: usize,
    processor: fn ([]const T) anyerror!void,
) !void {
    const record_size = @sizeOf(T);
    const buffer = try allocator.alloc(u8, batch_size * record_size);
    defer allocator.free(buffer);

    while (true) {
        const bytes_read = try file.read(buffer);
        if (bytes_read == 0) break;

        const record_count = bytes_read / record_size;
        if (bytes_read % record_size != 0) return error.PartialRecord;

        // Cast buffer to record slice
        const records = std.mem.bytesAsSlice(T, buffer[0 .. record_count * record_size]);
        try processor(records);
    }
}
```

### Validating Records

Add validation to ensure record integrity:

```zig
pub fn ValidatedRecordIterator(comptime T: type) type {
    return struct {
        file: std.fs.File,
        buffer: [@sizeOf(T)]u8 = undefined,
        validator: *const fn (T) bool,

        const Self = @This();

        pub fn init(file: std.fs.File, validator: *const fn (T) bool) Self {
            return .{ .file = file, .validator = validator };
        }

        pub fn next(self: *Self) !?T {
            while (true) {
                const bytes_read = try self.file.read(&self.buffer);
                if (bytes_read == 0) return null;
                if (bytes_read < @sizeOf(T)) return error.PartialRecord;

                const record: T = @bitCast(self.buffer);

                if (self.validator(record)) {
                    return record;
                }
                // Skip invalid record and continue
            }
        }
    };
}

fn validatePlayer(record: PlayerRecord) bool {
    return record.lives <= 3 and record.level > 0;
}
```

### Memory-Mapped Record Access

For very large files, use memory mapping:

```zig
pub fn MappedRecordFile(comptime T: type) type {
    return struct {
        data: []align(std.mem.page_size) const u8,

        const Self = @This();
        const record_size = @sizeOf(T);

        pub fn init(file: std.fs.File) !Self {
            const size = (try file.stat()).size;
            const data = try std.posix.mmap(
                null,
                size,
                std.posix.PROT.READ,
                .{ .TYPE = .SHARED },
                file.handle,
                0,
            );

            return .{ .data = data };
        }

        pub fn deinit(self: *Self) void {
            std.posix.munmap(self.data);
        }

        pub fn get(self: Self, index: usize) !T {
            const offset = index * record_size;
            if (offset + record_size > self.data.len) {
                return error.OutOfBounds;
            }

            const record_bytes = self.data[offset..][0..record_size];
            return @bitCast(record_bytes.*);
        }

        pub fn count(self: Self) usize {
            return self.data.len / record_size;
        }

        pub fn slice(self: Self) []const T {
            return std.mem.bytesAsSlice(T, self.data);
        }
    };
}
```

### Error Handling

Common errors when working with fixed-size records:

```zig
pub const RecordError = error{
    PartialRecord,
    InvalidAlignment,
    CorruptedData,
};

pub fn safeReadRecord(comptime T: type, file: std.fs.File) RecordError!T {
    var buffer: [@sizeOf(T)]u8 = undefined;
    const bytes_read = file.read(&buffer) catch return error.CorruptedData;

    if (bytes_read == 0) return error.PartialRecord;
    if (bytes_read < @sizeOf(T)) return error.PartialRecord;

    const record: T = @bitCast(buffer);

    // Add custom validation here

    return record;
}
```

### Performance Tips

**Buffer Reads:**
- Read multiple records at once (buffered iterator)
- Reduces system calls significantly

**Alignment:**
- Use `extern struct` for predictable layout
- Ensure proper padding for alignment

**Memory Mapping:**
- Best for random access patterns
- Avoids explicit I/O calls
- Let OS handle caching

**Batch Processing:**
- Process records in groups
- Better cache locality
- Amortize function call overhead

### Related Functions

- `std.fs.File.read()` - Read bytes from file
- `std.fs.File.seekTo()` - Seek to position
- `std.mem.bytesAsSlice()` - Reinterpret bytes as typed slice
- `@bitCast()` - Convert between types of same size
- `std.posix.mmap()` - Memory-map a file

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: record_iterator
/// Basic record iterator
pub fn RecordIterator(comptime T: type) type {
    return struct {
        file: std.fs.File,
        buffer: [@sizeOf(T)]u8 = undefined,

        const Self = @This();

        pub fn init(file: std.fs.File) Self {
            return .{ .file = file };
        }

        pub fn next(self: *Self) !?T {
            const bytes_read = try self.file.read(&self.buffer);

            if (bytes_read == 0) return null;
            if (bytes_read < @sizeOf(T)) return error.PartialRecord;

            return @bitCast(self.buffer);
        }
    };
}

/// Buffered record iterator for better performance
pub fn BufferedRecordIterator(comptime T: type, comptime buffer_count: usize) type {
    return struct {
        file: std.fs.File,
        buffer: [buffer_count * @sizeOf(T)]u8 = undefined,
        position: usize = 0,
        count: usize = 0,

        const Self = @This();
        const record_size = @sizeOf(T);

        pub fn init(file: std.fs.File) Self {
            return .{ .file = file };
        }

        pub fn next(self: *Self) !?T {
            // Refill buffer if empty
            if (self.position >= self.count) {
                const bytes_read = try self.file.read(&self.buffer);
                if (bytes_read == 0) return null;

                self.count = bytes_read / record_size;
                self.position = 0;

                // Check for partial record
                if (bytes_read % record_size != 0) {
                    return error.PartialRecord;
                }
            }

            const offset = self.position * record_size;
            const record_bytes = self.buffer[offset..][0..record_size];
            self.position += 1;

            return @bitCast(record_bytes.*);
        }
    };
}
// ANCHOR_END: record_iterator

// ANCHOR: random_access
/// Random-access record file
pub fn RecordFile(comptime T: type) type {
    return struct {
        file: std.fs.File,

        const Self = @This();
        const record_size = @sizeOf(T);

        pub fn init(file: std.fs.File) Self {
            return .{ .file = file };
        }

        pub fn seekToRecord(self: *Self, index: usize) !void {
            try self.file.seekTo(index * record_size);
        }

        pub fn readRecord(self: *Self) !T {
            var buffer: [record_size]u8 = undefined;
            const bytes_read = try self.file.read(&buffer);

            if (bytes_read < record_size) return error.PartialRecord;

            return @bitCast(buffer);
        }

        pub fn writeRecord(self: *Self, record: T) !void {
            const bytes: [record_size]u8 = @bitCast(record);
            try self.file.writeAll(&bytes);
        }

        pub fn getRecordCount(self: *Self) !usize {
            const size = (try self.file.stat()).size;
            return size / record_size;
        }
    };
}

/// Read a record in reverse order
pub fn readRecordReverse(comptime T: type, file: std.fs.File, index: usize) !T {
    const record_size = @sizeOf(T);
    const offset = index * record_size;

    try file.seekTo(offset);

    var buffer: [record_size]u8 = undefined;
    const bytes_read = try file.read(&buffer);

    if (bytes_read < record_size) return error.PartialRecord;

    return @bitCast(buffer);
}
// ANCHOR_END: random_access

// ANCHOR: batch_processing
/// Process records in batches
pub fn processBatch(
    comptime T: type,
    file: std.fs.File,
    allocator: std.mem.Allocator,
    batch_size: usize,
    processor: *const fn ([]const T) anyerror!void,
) !void {
    const record_size = @sizeOf(T);
    const buffer = try allocator.alignedAlloc(u8, std.mem.Alignment.of(T), batch_size * record_size);
    defer allocator.free(buffer);

    while (true) {
        const bytes_read = try file.read(buffer);
        if (bytes_read == 0) break;

        const record_count = bytes_read / record_size;
        if (bytes_read % record_size != 0) return error.PartialRecord;

        // Cast buffer to record slice
        const records = std.mem.bytesAsSlice(T, buffer[0 .. record_count * record_size]);
        try processor(records);
    }
}
// ANCHOR_END: batch_processing

// Test record types

const SimpleRecord = extern struct {
    id: u32,
    value: f32,
    flags: u8,
    padding: [3]u8 = undefined,
};

const PlayerRecord = extern struct {
    player_id: u32,
    score: u32,
    level: u16,
    lives: u8,
    padding: u8 = 0,
};

// Tests

test "basic record iterator" {
    const test_path = "/tmp/test_records.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test records
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        const records = [_]SimpleRecord{
            .{ .id = 1, .value = 1.5, .flags = 0 },
            .{ .id = 2, .value = 2.5, .flags = 1 },
            .{ .id = 3, .value = 3.5, .flags = 2 },
        };

        for (records) |record| {
            const bytes: [@sizeOf(SimpleRecord)]u8 = @bitCast(record);
            try file.writeAll(&bytes);
        }
    }

    // Read and verify
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var iter = RecordIterator(SimpleRecord).init(file);

    const r1 = (try iter.next()).?;
    try std.testing.expectEqual(@as(u32, 1), r1.id);
    try std.testing.expectEqual(@as(f32, 1.5), r1.value);

    const r2 = (try iter.next()).?;
    try std.testing.expectEqual(@as(u32, 2), r2.id);

    const r3 = (try iter.next()).?;
    try std.testing.expectEqual(@as(u32, 3), r3.id);

    try std.testing.expectEqual(@as(?SimpleRecord, null), try iter.next());
}

test "buffered record iterator" {
    const test_path = "/tmp/test_buffered_records.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write many records
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var i: u32 = 0;
        while (i < 100) : (i += 1) {
            const record = SimpleRecord{
                .id = i,
                .value = @floatFromInt(i),
                .flags = @intCast(i % 256),
            };
            const bytes: [@sizeOf(SimpleRecord)]u8 = @bitCast(record);
            try file.writeAll(&bytes);
        }
    }

    // Read with buffered iterator
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var iter = BufferedRecordIterator(SimpleRecord, 10).init(file);
    var count: u32 = 0;

    while (try iter.next()) |record| {
        try std.testing.expectEqual(count, record.id);
        count += 1;
    }

    try std.testing.expectEqual(@as(u32, 100), count);
}

test "record file random access" {
    const test_path = "/tmp/test_random_access.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write records
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var record_file = RecordFile(PlayerRecord).init(file);

        var i: u32 = 0;
        while (i < 10) : (i += 1) {
            const record = PlayerRecord{
                .player_id = i,
                .score = i * 100,
                .level = @intCast(i + 1),
                .lives = 3,
            };
            try record_file.writeRecord(record);
        }
    }

    // Read random access
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var record_file = RecordFile(PlayerRecord).init(file);

    // Get count
    const count = try record_file.getRecordCount();
    try std.testing.expectEqual(@as(usize, 10), count);

    // Seek to record 5
    try record_file.seekToRecord(5);
    const r5 = try record_file.readRecord();
    try std.testing.expectEqual(@as(u32, 5), r5.player_id);
    try std.testing.expectEqual(@as(u32, 500), r5.score);

    // Seek to record 0
    try record_file.seekToRecord(0);
    const r0 = try record_file.readRecord();
    try std.testing.expectEqual(@as(u32, 0), r0.player_id);
}

test "read record in reverse" {
    const test_path = "/tmp/test_reverse.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write records
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var i: u32 = 0;
        while (i < 5) : (i += 1) {
            const record = SimpleRecord{
                .id = i,
                .value = @floatFromInt(i),
                .flags = @intCast(i),
            };
            const bytes: [@sizeOf(SimpleRecord)]u8 = @bitCast(record);
            try file.writeAll(&bytes);
        }
    }

    // Read in reverse
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var index: usize = 5;
    while (index > 0) {
        index -= 1;
        const record = try readRecordReverse(SimpleRecord, file, index);
        try std.testing.expectEqual(@as(u32, @intCast(index)), record.id);
    }
}

test "batch processing" {
    const test_path = "/tmp/test_batch.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write records
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var i: u32 = 0;
        while (i < 20) : (i += 1) {
            const record = SimpleRecord{
                .id = i,
                .value = @floatFromInt(i),
                .flags = 0,
            };
            const bytes: [@sizeOf(SimpleRecord)]u8 = @bitCast(record);
            try file.writeAll(&bytes);
        }
    }

    // Process in batches
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const TestContext = struct {
        var total: u32 = 0;

        fn processor(records: []const SimpleRecord) !void {
            for (records) |_| {
                total += 1;
            }
        }
    };

    TestContext.total = 0;
    try processBatch(SimpleRecord, file, std.testing.allocator, 5, TestContext.processor);

    try std.testing.expectEqual(@as(u32, 20), TestContext.total);
}

test "empty file iteration" {
    const test_path = "/tmp/test_empty.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create empty file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
    }

    // Iterate
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var iter = RecordIterator(SimpleRecord).init(file);
    try std.testing.expectEqual(@as(?SimpleRecord, null), try iter.next());
}

test "partial record detection" {
    const test_path = "/tmp/test_partial.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write incomplete record
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        const partial_data = [_]u8{ 1, 2, 3, 4, 5 }; // Less than record size
        try file.writeAll(&partial_data);
    }

    // Try to read
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var iter = RecordIterator(SimpleRecord).init(file);
    const result = iter.next();

    try std.testing.expectError(error.PartialRecord, result);
}

test "record file update" {
    const test_path = "/tmp/test_update.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write initial records
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var record_file = RecordFile(PlayerRecord).init(file);

        var i: u32 = 0;
        while (i < 5) : (i += 1) {
            const record = PlayerRecord{
                .player_id = i,
                .score = 0,
                .level = 1,
                .lives = 3,
            };
            try record_file.writeRecord(record);
        }
    }

    // Update record 2
    {
        const file = try std.fs.cwd().openFile(test_path, .{ .mode = .read_write });
        defer file.close();

        var record_file = RecordFile(PlayerRecord).init(file);

        try record_file.seekToRecord(2);
        const updated = PlayerRecord{
            .player_id = 2,
            .score = 9999,
            .level = 10,
            .lives = 1,
        };
        try record_file.writeRecord(updated);
    }

    // Verify update
    {
        const file = try std.fs.cwd().openFile(test_path, .{});
        defer file.close();

        var record_file = RecordFile(PlayerRecord).init(file);

        try record_file.seekToRecord(2);
        const record = try record_file.readRecord();

        try std.testing.expectEqual(@as(u32, 9999), record.score);
        try std.testing.expectEqual(@as(u16, 10), record.level);
    }
}

test "large file iteration" {
    const test_path = "/tmp/test_large.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const record_count = 10000;

    // Write large file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var i: u32 = 0;
        while (i < record_count) : (i += 1) {
            const record = SimpleRecord{
                .id = i,
                .value = @floatFromInt(i),
                .flags = @intCast(i % 256),
            };
            const bytes: [@sizeOf(SimpleRecord)]u8 = @bitCast(record);
            try file.writeAll(&bytes);
        }
    }

    // Read and verify
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var iter = BufferedRecordIterator(SimpleRecord, 100).init(file);
    var count: u32 = 0;

    while (try iter.next()) |record| {
        try std.testing.expectEqual(count, record.id);
        count += 1;
    }

    try std.testing.expectEqual(@as(u32, record_count), count);
}

test "mixed read and write" {
    const test_path = "/tmp/test_mixed.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const file = try std.fs.cwd().createFile(test_path, .{ .read = true });
    defer file.close();

    var record_file = RecordFile(SimpleRecord).init(file);

    // Write
    try record_file.writeRecord(.{ .id = 1, .value = 1.0, .flags = 0 });
    try record_file.writeRecord(.{ .id = 2, .value = 2.0, .flags = 0 });

    // Seek and read
    try record_file.seekToRecord(0);
    const r1 = try record_file.readRecord();
    try std.testing.expectEqual(@as(u32, 1), r1.id);

    // Write another
    try record_file.seekToRecord(2);
    try record_file.writeRecord(.{ .id = 3, .value = 3.0, .flags = 0 });

    // Verify count
    const count = try record_file.getRecordCount();
    try std.testing.expectEqual(@as(usize, 3), count);
}
```

---

## Recipe 5.9: Reading Binary Data into a Mutable Buffer {#recipe-5-9}

**Tags:** allocators, arraylist, c-interop, comptime, data-structures, error-handling, files-io, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_9.zig`

### Problem

You need to read binary data from a file into a mutable buffer that you can modify or process in place.

### Solution

### Basic Buffer Reads

```zig
/// Basic read into buffer
pub fn readIntoBuffer(file: std.fs.File, buffer: []u8) !usize {
    const bytes_read = try file.read(buffer);
    return bytes_read;
}

/// Read exact amount, error if not enough data
pub fn readExact(file: std.fs.File, buffer: []u8) !void {
    var index: usize = 0;
    while (index < buffer.len) {
        const bytes_read = try file.read(buffer[index..]);
        if (bytes_read == 0) return error.UnexpectedEndOfFile;
        index += bytes_read;
    }
}

/// Process file in chunks with callback
pub fn processFileInChunks(
    file: std.fs.File,
    processor: *const fn ([]const u8) anyerror!void,
) !void {
    var buffer: [4096]u8 = undefined;

    while (true) {
        const bytes_read = try file.read(&buffer);
        if (bytes_read == 0) break;

        try processor(buffer[0..bytes_read]);
    }
}

/// Read structured binary data
pub fn readStruct(comptime T: type, file: std.fs.File) !T {
    var buffer: [@sizeOf(T)]u8 = undefined;
    const bytes_read = try file.read(&buffer);

    if (bytes_read < @sizeOf(T)) return error.PartialRead;

    return @bitCast(buffer);
}
```

### Advanced Buffer Operations

```zig
/// Scatter read into multiple buffers
pub fn readScatter(file: std.fs.File, buffers: [][]u8) !usize {
    var total: usize = 0;

    for (buffers) |buffer| {
        const bytes_read = try file.read(buffer);
        total += bytes_read;
        if (bytes_read < buffer.len) break;
    }

    return total;
}

/// Read from specific position without changing file position
pub fn readAtOffset(file: std.fs.File, buffer: []u8, offset: u64) !usize {
    const original_pos = try file.getPos();
    defer file.seekTo(original_pos) catch {};

    try file.seekTo(offset);
    return try file.read(buffer);
}

/// Ring buffer for continuous reading
pub const RingBuffer = struct {
    buffer: []u8,
    read_pos: usize = 0,
    write_pos: usize = 0,
    count: usize = 0,

    pub fn init(buffer: []u8) RingBuffer {
        return .{ .buffer = buffer };
    }

    pub fn readFromFile(self: *RingBuffer, file: std.fs.File) !usize {
        if (self.count == self.buffer.len) return 0; // Buffer full

        const write_idx = self.write_pos;
        const available = self.buffer.len - self.count;

        const to_end = self.buffer.len - write_idx;
        const read_size = @min(available, to_end);

        const bytes_read = try file.read(self.buffer[write_idx..][0..read_size]);
        if (bytes_read == 0) return 0;

        self.write_pos = (write_idx + bytes_read) % self.buffer.len;
        self.count += bytes_read;

        return bytes_read;
    }

    pub fn consume(self: *RingBuffer, amount: usize) []const u8 {
        const to_read = @min(amount, self.count);
        const read_idx = self.read_pos;

        const to_end = self.buffer.len - read_idx;
        const chunk_size = @min(to_read, to_end);

        const result = self.buffer[read_idx..][0..chunk_size];

        self.read_pos = (read_idx + chunk_size) % self.buffer.len;
        self.count -= chunk_size;

        return result;
    }
};

/// Safe read with error handling
pub fn safeRead(file: std.fs.File, buffer: []u8) !usize {
    return file.read(buffer) catch |err| switch (err) {
        error.InputOutput => {
            std.debug.print("I/O error reading file\n", .{});
            return error.ReadFailed;
        },
        error.AccessDenied => {
            std.debug.print("Access denied\n", .{});
            return error.PermissionDenied;
        },
        error.BrokenPipe => return 0, // Treat as EOF
        else => return err,
    };
}
```

### Discussion

### Stack-Allocated Buffers

The most efficient approach uses stack-allocated fixed-size buffers:

```zig
var buffer: [4096]u8 = undefined;
const bytes_read = try file.read(&buffer);

// Process buffer[0..bytes_read]
```

Advantages:
- No allocator needed
- Fast allocation (stack)
- Deterministic memory usage
- No cleanup required

### Handling Partial Reads

File reads may return fewer bytes than the buffer size:

```zig
pub fn readExact(file: std.fs.File, buffer: []u8) !void {
    var index: usize = 0;
    while (index < buffer.len) {
        const bytes_read = try file.read(buffer[index..]);
        if (bytes_read == 0) return error.UnexpectedEndOfFile;
        index += bytes_read;
    }
}

test "read exact amount" {
    const test_path = "/tmp/test_exact.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write exactly 100 bytes
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        const data = [_]u8{42} ** 100;
        try file.writeAll(&data);
    }

    // Read exactly 100 bytes
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [100]u8 = undefined;
    try readExact(file, &buffer);

    try std.testing.expect(std.mem.allEqual(u8, &buffer, 42));
}
```

### Reading into Slices

Read into slices of existing arrays:

```zig
var data: [1024]u8 = undefined;

// Read into first half
const first_half = try file.read(data[0..512]);

// Read into second half
const second_half = try file.read(data[512..]);

// Total bytes read
const total = first_half + second_half;
```

### Reusing Buffers

Reuse the same buffer for multiple reads:

```zig
pub fn processFileInChunks(
    file: std.fs.File,
    processor: fn ([]const u8) anyerror!void,
) !void {
    var buffer: [4096]u8 = undefined;

    while (true) {
        const bytes_read = try file.read(&buffer);
        if (bytes_read == 0) break;

        try processor(buffer[0..bytes_read]);
    }
}

test "reuse buffer" {
    const test_path = "/tmp/test_reuse.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write large file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var i: usize = 0;
        while (i < 10000) : (i += 1) {
            try file.writeAll("X");
        }
    }

    // Count chunks
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const Counter = struct {
        var count: usize = 0;
        fn process(data: []const u8) !void {
            _ = data;
            count += 1;
        }
    };

    Counter.count = 0;
    try processFileInChunks(file, Counter.process);

    try std.testing.expect(Counter.count > 0);
}
```

### Reading with Different Buffer Types

Read into different kinds of buffers:

```zig
// Fixed array
var array_buffer: [256]u8 = undefined;
_ = try file.read(&array_buffer);

// Slice from heap
const slice_buffer = try allocator.alloc(u8, 1024);
defer allocator.free(slice_buffer);
_ = try file.read(slice_buffer);

// ArrayList
var list_buffer: std.ArrayList(u8) = .{};
defer list_buffer.deinit(allocator);
try list_buffer.resize(allocator, 512);
_ = try file.read(list_buffer.items);
```

### Zero-Copy with Buffered Readers

Use buffered readers to minimize system calls:

```zig
pub fn readWithBufferedReader(file: std.fs.File) !void {
    var file_buffer: [8192]u8 = undefined;
    var buffered = file.reader(&file_buffer);

    var process_buffer: [256]u8 = undefined;

    while (true) {
        const bytes_read = try buffered.read(&process_buffer);
        if (bytes_read == 0) break;

        // Process process_buffer[0..bytes_read]
        // The file_buffer acts as a read-ahead cache
    }
}
```

### Reading Structured Binary Data

Read binary data into typed structures:

```zig
pub fn readStruct(comptime T: type, file: std.fs.File) !T {
    var buffer: [@sizeOf(T)]u8 = undefined;
    const bytes_read = try file.read(&buffer);

    if (bytes_read < @sizeOf(T)) return error.PartialRead;

    return @bitCast(buffer);
}

const Header = extern struct {
    magic: u32,
    version: u16,
    flags: u16,
};

test "read struct" {
    const test_path = "/tmp/test_struct.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write header
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        const header = Header{
            .magic = 0xDEADBEEF,
            .version = 1,
            .flags = 0x0042,
        };
        const bytes: [@sizeOf(Header)]u8 = @bitCast(header);
        try file.writeAll(&bytes);
    }

    // Read header
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const header = try readStruct(Header, file);

    try std.testing.expectEqual(@as(u32, 0xDEADBEEF), header.magic);
    try std.testing.expectEqual(@as(u16, 1), header.version);
}
```

### Reading Multiple Buffers (Scatter Read)

Read into multiple buffers in one operation:

```zig
pub fn readScatter(file: std.fs.File, buffers: [][]u8) !usize {
    var total: usize = 0;

    for (buffers) |buffer| {
        const bytes_read = try file.read(buffer);
        total += bytes_read;
        if (bytes_read < buffer.len) break;
    }

    return total;
}

test "scatter read" {
    const test_path = "/tmp/test_scatter.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("AAAABBBBCCCC");
    }

    // Read into multiple buffers
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buf1: [4]u8 = undefined;
    var buf2: [4]u8 = undefined;
    var buf3: [4]u8 = undefined;

    var buffers = [_][]u8{ &buf1, &buf2, &buf3 };
    const total = try readScatter(file, &buffers);

    try std.testing.expectEqual(@as(usize, 12), total);
    try std.testing.expectEqualStrings("AAAA", &buf1);
    try std.testing.expectEqualStrings("BBBB", &buf2);
    try std.testing.expectEqualStrings("CCCC", &buf3);
}
```

### Reading with Offset

Read from a specific position without seeking:

```zig
pub fn readAtOffset(file: std.fs.File, buffer: []u8, offset: u64) !usize {
    const original_pos = try file.getPos();
    defer file.seekTo(original_pos) catch {};

    try file.seekTo(offset);
    return try file.read(buffer);
}

test "read at offset" {
    const test_path = "/tmp/test_offset.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("0123456789");
    }

    // Read from offset 5
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [3]u8 = undefined;
    const bytes_read = try readAtOffset(file, &buffer, 5);

    try std.testing.expectEqual(@as(usize, 3), bytes_read);
    try std.testing.expectEqualStrings("567", &buffer);

    // File position unchanged
    try std.testing.expectEqual(@as(u64, 0), try file.getPos());
}
```

### Ring Buffer Reading

Continuously read into a ring buffer:

```zig
pub const RingBuffer = struct {
    buffer: []u8,
    read_pos: usize = 0,
    write_pos: usize = 0,
    count: usize = 0,

    pub fn init(buffer: []u8) RingBuffer {
        return .{ .buffer = buffer };
    }

    pub fn readFromFile(self: *RingBuffer, file: std.fs.File) !usize {
        if (self.count == self.buffer.len) return 0; // Buffer full

        const write_idx = self.write_pos;
        const available = self.buffer.len - self.count;

        const to_end = self.buffer.len - write_idx;
        const read_size = @min(available, to_end);

        const bytes_read = try file.read(self.buffer[write_idx..][0..read_size]);
        if (bytes_read == 0) return 0;

        self.write_pos = (write_idx + bytes_read) % self.buffer.len;
        self.count += bytes_read;

        return bytes_read;
    }

    pub fn consume(self: *RingBuffer, amount: usize) []const u8 {
        const to_read = @min(amount, self.count);
        const read_idx = self.read_pos;

        const to_end = self.buffer.len - read_idx;
        const chunk_size = @min(to_read, to_end);

        const result = self.buffer[read_idx..][0..chunk_size];

        self.read_pos = (read_idx + chunk_size) % self.buffer.len;
        self.count -= chunk_size;

        return result;
    }
};
```

### Error Handling

Handle common read errors:

```zig
pub fn safeRead(file: std.fs.File, buffer: []u8) !usize {
    return file.read(buffer) catch |err| switch (err) {
        error.InputOutput => {
            std.debug.print("I/O error reading file\n", .{});
            return error.ReadFailed;
        },
        error.AccessDenied => {
            std.debug.print("Access denied\n", .{});
            return error.PermissionDenied;
        },
        error.BrokenPipe => return 0, // Treat as EOF
        else => return err,
    };
}
```

### Performance Tips

**Buffer Size:**
- Use 4KB-64KB buffers for best performance
- Align with filesystem block size when possible
- Larger isn't always better (cache effects)

**Stack vs Heap:**
```zig
// Fast: Stack allocation (< 4KB recommended)
var small_buffer: [4096]u8 = undefined;

// Slower: Heap allocation (use for > 4KB)
const large_buffer = try allocator.alloc(u8, 65536);
defer allocator.free(large_buffer);
```

**Buffered Readers:**
- Use buffered readers for small, frequent reads
- Reduces system calls dramatically
- Adds one level of copying but worth it

**Avoid:**
```zig
// Bad: Reading one byte at a time
for (0..file_size) |_| {
    var byte: [1]u8 = undefined;
    _ = try file.read(&byte);
}

// Good: Read in chunks
var buffer: [4096]u8 = undefined;
while (true) {
    const n = try file.read(&buffer);
    if (n == 0) break;
    // Process buffer[0..n]
}
```

### Memory Safety

Always initialize buffers before reading sensitive data:

```zig
// Unsafe: Uninitialized buffer may leak data
var buffer: [1024]u8 = undefined;
const n = try file.read(&buffer);
// buffer[n..] contains uninitialized data!

// Safe: Zero-initialize
var buffer = [_]u8{0} ** 1024;
const n = try file.read(&buffer);
// buffer[n..] is all zeros
```

Or only use the read portion:

```zig
var buffer: [1024]u8 = undefined;
const n = try file.read(&buffer);
const valid_data = buffer[0..n]; // Only use what was read
```

### Related Functions

- `std.fs.File.read()` - Read into buffer
- `std.fs.File.readAll()` - Read until buffer full or EOF
- `std.fs.File.reader()` - Get buffered reader
- `std.Io.Reader.read()` - Generic reader interface
- `std.Io.Reader.readAtLeast()` - Read minimum number of bytes
- `std.mem.readInt()` - Read integer from bytes

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_buffer_reads
/// Basic read into buffer
pub fn readIntoBuffer(file: std.fs.File, buffer: []u8) !usize {
    const bytes_read = try file.read(buffer);
    return bytes_read;
}

/// Read exact amount, error if not enough data
pub fn readExact(file: std.fs.File, buffer: []u8) !void {
    var index: usize = 0;
    while (index < buffer.len) {
        const bytes_read = try file.read(buffer[index..]);
        if (bytes_read == 0) return error.UnexpectedEndOfFile;
        index += bytes_read;
    }
}

/// Process file in chunks with callback
pub fn processFileInChunks(
    file: std.fs.File,
    processor: *const fn ([]const u8) anyerror!void,
) !void {
    var buffer: [4096]u8 = undefined;

    while (true) {
        const bytes_read = try file.read(&buffer);
        if (bytes_read == 0) break;

        try processor(buffer[0..bytes_read]);
    }
}

/// Read structured binary data
pub fn readStruct(comptime T: type, file: std.fs.File) !T {
    var buffer: [@sizeOf(T)]u8 = undefined;
    const bytes_read = try file.read(&buffer);

    if (bytes_read < @sizeOf(T)) return error.PartialRead;

    return @bitCast(buffer);
}
// ANCHOR_END: basic_buffer_reads

// ANCHOR: advanced_buffer_ops
/// Scatter read into multiple buffers
pub fn readScatter(file: std.fs.File, buffers: [][]u8) !usize {
    var total: usize = 0;

    for (buffers) |buffer| {
        const bytes_read = try file.read(buffer);
        total += bytes_read;
        if (bytes_read < buffer.len) break;
    }

    return total;
}

/// Read from specific position without changing file position
pub fn readAtOffset(file: std.fs.File, buffer: []u8, offset: u64) !usize {
    const original_pos = try file.getPos();
    defer file.seekTo(original_pos) catch {};

    try file.seekTo(offset);
    return try file.read(buffer);
}

/// Ring buffer for continuous reading
pub const RingBuffer = struct {
    buffer: []u8,
    read_pos: usize = 0,
    write_pos: usize = 0,
    count: usize = 0,

    pub fn init(buffer: []u8) RingBuffer {
        return .{ .buffer = buffer };
    }

    pub fn readFromFile(self: *RingBuffer, file: std.fs.File) !usize {
        if (self.count == self.buffer.len) return 0; // Buffer full

        const write_idx = self.write_pos;
        const available = self.buffer.len - self.count;

        const to_end = self.buffer.len - write_idx;
        const read_size = @min(available, to_end);

        const bytes_read = try file.read(self.buffer[write_idx..][0..read_size]);
        if (bytes_read == 0) return 0;

        self.write_pos = (write_idx + bytes_read) % self.buffer.len;
        self.count += bytes_read;

        return bytes_read;
    }

    pub fn consume(self: *RingBuffer, amount: usize) []const u8 {
        const to_read = @min(amount, self.count);
        const read_idx = self.read_pos;

        const to_end = self.buffer.len - read_idx;
        const chunk_size = @min(to_read, to_end);

        const result = self.buffer[read_idx..][0..chunk_size];

        self.read_pos = (read_idx + chunk_size) % self.buffer.len;
        self.count -= chunk_size;

        return result;
    }
};

/// Safe read with error handling
pub fn safeRead(file: std.fs.File, buffer: []u8) !usize {
    return file.read(buffer) catch |err| switch (err) {
        error.InputOutput => {
            std.debug.print("I/O error reading file\n", .{});
            return error.ReadFailed;
        },
        error.AccessDenied => {
            std.debug.print("Access denied\n", .{});
            return error.PermissionDenied;
        },
        error.BrokenPipe => return 0, // Treat as EOF
        else => return err,
    };
}
// ANCHOR_END: advanced_buffer_ops

// Test structures

const Header = extern struct {
    magic: u32,
    version: u16,
    flags: u16,
};

// Tests

test "read into buffer" {
    const test_path = "/tmp/test_buffer.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("Hello, World!");
    }

    // Read into buffer
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [32]u8 = undefined;
    const bytes_read = try readIntoBuffer(file, &buffer);

    try std.testing.expectEqual(@as(usize, 13), bytes_read);
    try std.testing.expectEqualStrings("Hello, World!", buffer[0..bytes_read]);
}

test "read exact amount" {
    const test_path = "/tmp/test_exact.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write exactly 100 bytes
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        const data = [_]u8{42} ** 100;
        try file.writeAll(&data);
    }

    // Read exactly 100 bytes
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [100]u8 = undefined;
    try readExact(file, &buffer);

    try std.testing.expect(std.mem.allEqual(u8, &buffer, 42));
}

test "read exact fails on short file" {
    const test_path = "/tmp/test_exact_short.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write 50 bytes
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        const data = [_]u8{42} ** 50;
        try file.writeAll(&data);
    }

    // Try to read 100 bytes
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [100]u8 = undefined;
    const result = readExact(file, &buffer);

    try std.testing.expectError(error.UnexpectedEndOfFile, result);
}

test "read into slices" {
    const test_path = "/tmp/test_slices.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("A" ** 512 ++ "B" ** 512);
    }

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var data: [1024]u8 = undefined;

    // Read into first half
    const first_half = try file.read(data[0..512]);
    try std.testing.expectEqual(@as(usize, 512), first_half);

    // Read into second half
    const second_half = try file.read(data[512..]);
    try std.testing.expectEqual(@as(usize, 512), second_half);

    // Verify
    try std.testing.expect(std.mem.allEqual(u8, data[0..512], 'A'));
    try std.testing.expect(std.mem.allEqual(u8, data[512..], 'B'));
}

test "reuse buffer" {
    const test_path = "/tmp/test_reuse.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write large file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var i: usize = 0;
        while (i < 10000) : (i += 1) {
            try file.writeAll("X");
        }
    }

    // Count chunks
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const Counter = struct {
        var count: usize = 0;
        fn process(data: []const u8) !void {
            _ = data;
            count += 1;
        }
    };

    Counter.count = 0;
    try processFileInChunks(file, Counter.process);

    try std.testing.expect(Counter.count > 0);
}

test "read struct" {
    const test_path = "/tmp/test_struct.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write header
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        const header = Header{
            .magic = 0xDEADBEEF,
            .version = 1,
            .flags = 0x0042,
        };
        const bytes: [@sizeOf(Header)]u8 = @bitCast(header);
        try file.writeAll(&bytes);
    }

    // Read header
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const header = try readStruct(Header, file);

    try std.testing.expectEqual(@as(u32, 0xDEADBEEF), header.magic);
    try std.testing.expectEqual(@as(u16, 1), header.version);
}

test "scatter read" {
    const test_path = "/tmp/test_scatter.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("AAAABBBBCCCC");
    }

    // Read into multiple buffers
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buf1: [4]u8 = undefined;
    var buf2: [4]u8 = undefined;
    var buf3: [4]u8 = undefined;

    var buffers = [_][]u8{ &buf1, &buf2, &buf3 };
    const total = try readScatter(file, &buffers);

    try std.testing.expectEqual(@as(usize, 12), total);
    try std.testing.expectEqualStrings("AAAA", &buf1);
    try std.testing.expectEqualStrings("BBBB", &buf2);
    try std.testing.expectEqualStrings("CCCC", &buf3);
}

test "read at offset" {
    const test_path = "/tmp/test_offset.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("0123456789");
    }

    // Read from offset 5
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [3]u8 = undefined;
    const bytes_read = try readAtOffset(file, &buffer, 5);

    try std.testing.expectEqual(@as(usize, 3), bytes_read);
    try std.testing.expectEqualStrings("567", &buffer);

    // File position unchanged
    try std.testing.expectEqual(@as(u64, 0), try file.getPos());
}

test "ring buffer reading" {
    const test_path = "/tmp/test_ring.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("ABCDEFGHIJKLMNOP");
    }

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var backing_buffer: [8]u8 = undefined;
    var ring = RingBuffer.init(&backing_buffer);

    // Read first chunk
    const read1 = try ring.readFromFile(file);
    try std.testing.expectEqual(@as(usize, 8), read1);
    try std.testing.expectEqual(@as(usize, 8), ring.count);

    // Consume 4 bytes
    const chunk1 = ring.consume(4);
    try std.testing.expectEqualStrings("ABCD", chunk1);
    try std.testing.expectEqual(@as(usize, 4), ring.count);

    // Read more (wraps around)
    const read2 = try ring.readFromFile(file);
    try std.testing.expectEqual(@as(usize, 4), read2);
    try std.testing.expectEqual(@as(usize, 8), ring.count);

    // Consume all
    const chunk2 = ring.consume(4);
    try std.testing.expectEqualStrings("EFGH", chunk2);

    const chunk3 = ring.consume(4);
    try std.testing.expectEqualStrings("IJKL", chunk3);

    try std.testing.expectEqual(@as(usize, 0), ring.count);
}

test "ring buffer full" {
    const test_path = "/tmp/test_ring_full.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("ABCDEFGHIJKLMNOP");
    }

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var backing_buffer: [8]u8 = undefined;
    var ring = RingBuffer.init(&backing_buffer);

    // Fill buffer
    const read1 = try ring.readFromFile(file);
    try std.testing.expectEqual(@as(usize, 8), read1);

    // Try to read when full
    const read2 = try ring.readFromFile(file);
    try std.testing.expectEqual(@as(usize, 0), read2);
}

test "safe read with error handling" {
    const test_path = "/tmp/test_safe.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("Safe read test");
    }

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [32]u8 = undefined;
    const bytes_read = try safeRead(file, &buffer);

    try std.testing.expectEqual(@as(usize, 14), bytes_read);
    try std.testing.expectEqualStrings("Safe read test", buffer[0..bytes_read]);
}

test "read empty file" {
    const test_path = "/tmp/test_empty.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create empty file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
    }

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [32]u8 = undefined;
    const bytes_read = try readIntoBuffer(file, &buffer);

    try std.testing.expectEqual(@as(usize, 0), bytes_read);
}

test "partial struct read fails" {
    const test_path = "/tmp/test_partial_struct.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write partial header
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        const partial_data = [_]u8{ 1, 2, 3, 4 }; // Less than Header size
        try file.writeAll(&partial_data);
    }

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    const result = readStruct(Header, file);

    try std.testing.expectError(error.PartialRead, result);
}

test "read with buffer smaller than file" {
    const test_path = "/tmp/test_small_buffer.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write large data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("A" ** 1000);
    }

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [100]u8 = undefined;
    const bytes_read = try readIntoBuffer(file, &buffer);

    // Should read buffer size, not file size
    try std.testing.expectEqual(@as(usize, 100), bytes_read);
    try std.testing.expect(std.mem.allEqual(u8, &buffer, 'A'));
}

test "multiple reads from same file" {
    const test_path = "/tmp/test_multiple.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write test data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("AAAABBBBCCCC");
    }

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buf1: [4]u8 = undefined;
    var buf2: [4]u8 = undefined;
    var buf3: [4]u8 = undefined;

    const read1 = try readIntoBuffer(file, &buf1);
    const read2 = try readIntoBuffer(file, &buf2);
    const read3 = try readIntoBuffer(file, &buf3);

    try std.testing.expectEqual(@as(usize, 4), read1);
    try std.testing.expectEqual(@as(usize, 4), read2);
    try std.testing.expectEqual(@as(usize, 4), read3);

    try std.testing.expectEqualStrings("AAAA", &buf1);
    try std.testing.expectEqualStrings("BBBB", &buf2);
    try std.testing.expectEqualStrings("CCCC", &buf3);
}

test "scatter read with partial last buffer" {
    const test_path = "/tmp/test_scatter_partial.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Write 10 bytes
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("AAAABBBBCC");
    }

    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buf1: [4]u8 = undefined;
    var buf2: [4]u8 = undefined;
    var buf3: [4]u8 = undefined;

    var buffers = [_][]u8{ &buf1, &buf2, &buf3 };
    const total = try readScatter(file, &buffers);

    // Should read 10 bytes total (4 + 4 + 2)
    try std.testing.expectEqual(@as(usize, 10), total);
    try std.testing.expectEqualStrings("AAAA", &buf1);
    try std.testing.expectEqualStrings("BBBB", &buf2);
    // buf3 only partially filled
}
```

---

## Recipe 5.10: Memory Mapping Binary Files {#recipe-5-10}

**Tags:** allocators, c-interop, comptime, error-handling, files-io, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_10.zig`

### Problem

You need to efficiently access large binary files, especially for random access patterns, without explicitly reading data into buffers.

### Solution

### Basic Memory Mapping

```zig
/// Map file for reading only
pub fn mapFileReadOnly(path: []const u8) !struct {
    data: []align(page_size_min) const u8,
    file: std.fs.File,
} {
    const file = try std.fs.cwd().openFile(path, .{});
    errdefer file.close();

    const file_size = (try file.stat()).size;

    // Can't map empty files
    if (file_size == 0) {
        return error.EmptyFile;
    }

    const data = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ,
        .{ .TYPE = .SHARED },
        file.handle,
        0,
    );

    return .{ .data = data, .file = file };
}

/// Map file for reading and writing
pub fn mapFileReadWrite(path: []const u8) !struct {
    data: []align(page_size_min) u8,
    file: std.fs.File,
} {
    const file = try std.fs.cwd().openFile(path, .{ .mode = .read_write });
    errdefer file.close();

    const file_size = (try file.stat()).size;

    const data = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ | std.posix.PROT.WRITE,
        .{ .TYPE = .SHARED },
        file.handle,
        0,
    );

    return .{ .data = data, .file = file };
}

/// Map file with private copy-on-write mapping
pub fn mapFilePrivate(path: []const u8) !struct {
    data: []align(page_size_min) u8,
    file: std.fs.File,
} {
    const file = try std.fs.cwd().openFile(path, .{});
    errdefer file.close();

    const file_size = (try file.stat()).size;

    const data = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ | std.posix.PROT.WRITE,
        .{ .TYPE = .PRIVATE },
        file.handle,
        0,
    );

    return .{ .data = data, .file = file };
}

/// Unmap and close file
pub fn unmapFile(mapping: anytype) void {
    std.posix.munmap(mapping.data);
    mapping.file.close();
}

/// Sync changes to disk
pub fn syncMapping(data: []align(page_size_min) u8, async_sync: bool) !void {
    const flags: c_int = if (async_sync) @intCast(std.posix.MSF.ASYNC) else @intCast(std.posix.MSF.SYNC);
    try std.posix.msync(data, flags);
}

/// Create anonymous memory mapping
pub fn createAnonymousMapping(size: usize) ![]align(page_size_min) u8 {
    const data = try std.posix.mmap(
        null,
        size,
        std.posix.PROT.READ | std.posix.PROT.WRITE,
        .{ .TYPE = .PRIVATE, .ANONYMOUS = true },
        -1,
        0,
    );

    return data;
}
```

### Structured Memory Mapping

```zig
/// Mapped struct file for random access
pub fn MappedStructFile(comptime T: type) type {
    return struct {
        data: []align(page_size_min) const u8,
        file: std.fs.File,

        const Self = @This();
        const record_size = @sizeOf(T);

        pub fn init(path: []const u8) !Self {
            const file = try std.fs.cwd().openFile(path, .{});
            errdefer file.close();

            const file_size = (try file.stat()).size;

            const data = try std.posix.mmap(
                null,
                file_size,
                std.posix.PROT.READ,
                .{ .TYPE = .SHARED },
                file.handle,
                0,
            );

            return .{ .data = data, .file = file };
        }

        pub fn deinit(self: *Self) void {
            std.posix.munmap(self.data);
            self.file.close();
        }

        pub fn get(self: Self, index: usize) !T {
            const offset = index * record_size;
            if (offset + record_size > self.data.len) {
                return error.OutOfBounds;
            }

            const record_bytes = self.data[offset..][0..record_size];
            return @bitCast(record_bytes.*);
        }

        pub fn count(self: Self) usize {
            return self.data.len / record_size;
        }

        pub fn slice(self: Self) []const T {
            return std.mem.bytesAsSlice(T, self.data);
        }
    };
}

/// Binary search in mapped file
pub fn binarySearchMapped(
    comptime T: type,
    data: []align(page_size_min) const u8,
    key: T,
    comptime lessThan: fn (T, T) bool,
) ?usize {
    const records = std.mem.bytesAsSlice(T, data);

    var left: usize = 0;
    var right: usize = records.len;

    while (left < right) {
        const mid = left + (right - left) / 2;

        // Check if records[mid] == key by the ordering
        if (!lessThan(records[mid], key) and !lessThan(key, records[mid])) {
            return mid;
        } else if (lessThan(records[mid], key)) {
            left = mid + 1;
        } else {
            right = mid;
        }
    }

    return null;
}
```

### Discussion

### What is Memory Mapping?

Memory mapping maps file contents into virtual memory, allowing you to access files as if they were in-memory arrays. The OS handles paging data in and out as needed.

**Advantages:**
- Fast random access
- No explicit read calls
- OS manages caching automatically
- Multiple processes can share read-only mappings
- Works with files larger than available RAM

**When to use:**
- Random access patterns
- Large files (especially > 1MB)
- Multiple reads from different locations
- Database files
- Binary search in sorted files

**When NOT to use:**
- Sequential scans (buffered reading is better)
- Small files (< 4KB)
- Files that change frequently
- Network filesystems (can be slow)

### Basic Memory Mapping

Map a file for reading:

```zig
pub fn mapFileReadOnly(path: []const u8) ![]align(std.mem.page_size) const u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    errdefer file.close();

    const file_size = (try file.stat()).size;

    const data = try std.posix.mmap(
        null,                      // Let OS choose address
        file_size,                 // Map entire file
        std.posix.PROT.READ,      // Read-only access
        .{ .TYPE = .SHARED },     // Share mapping with other processes
        file.handle,               // File descriptor
        0,                         // Start at beginning
    );

    // Note: file can be closed immediately after mmap
    // The mapping keeps file data accessible
    file.close();

    return data;
}

test "map read only" {
    const test_path = "/tmp/test_mmap.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create test file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("Hello, Memory Map!");
    }

    // Map and read
    const data = try mapFileReadOnly(test_path);
    defer std.posix.munmap(data);

    try std.testing.expectEqualStrings("Hello, Memory Map!", data);
}
```

### Memory Mapping for Read-Write

Map a file for both reading and writing:

```zig
pub fn mapFileReadWrite(path: []const u8) !struct {
    data: []align(std.mem.page_size) u8,
    file: std.fs.File,
} {
    const file = try std.fs.cwd().openFile(path, .{ .mode = .read_write });
    errdefer file.close();

    const file_size = (try file.stat()).size;

    const data = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ | std.posix.PROT.WRITE,
        .{ .TYPE = .SHARED },  // Changes written back to file
        file.handle,
        0,
    );

    return .{ .data = data, .file = file };
}

pub fn unmapFile(mapping: anytype) void {
    std.posix.munmap(mapping.data);
    mapping.file.close();
}

test "map read write" {
    const test_path = "/tmp/test_mmap_rw.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create test file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("AAAA");
    }

    // Map, modify, and sync
    {
        const mapping = try mapFileReadWrite(test_path);
        defer unmapFile(mapping);

        // Modify in place
        mapping.data[0] = 'B';
        mapping.data[1] = 'B';

        // Force write to disk
        try std.posix.msync(mapping.data, std.posix.MSF.SYNC);
    }

    // Verify changes persisted
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [4]u8 = undefined;
    _ = try file.read(&buffer);

    try std.testing.expectEqualStrings("BBAA", &buffer);
}
```

### Private vs Shared Mappings

**Shared mappings** (`.TYPE = .SHARED`):
- Changes visible to other processes
- Changes written back to file
- Use for: IPC, database files, config files

**Private mappings** (`.TYPE = .PRIVATE`):
- Changes only visible to this process
- Changes NOT written to file (copy-on-write)
- Use for: Templates, loading executables

```zig
pub fn mapFilePrivate(path: []const u8) ![]align(std.mem.page_size) u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const file_size = (try file.stat()).size;

    const data = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ | std.posix.PROT.WRITE,
        .{ .TYPE = .PRIVATE },  // Copy-on-write
        file.handle,
        0,
    );

    return data;
}
```

### Partial File Mapping

Map only part of a large file:

```zig
pub fn mapFileRange(
    path: []const u8,
    offset: u64,
    length: usize,
) ![]align(std.mem.page_size) const u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    // Offset must be page-aligned
    const page_size = std.mem.page_size;
    const aligned_offset = (offset / page_size) * page_size;
    const offset_diff = offset - aligned_offset;
    const aligned_length = length + offset_diff;

    const data = try std.posix.mmap(
        null,
        aligned_length,
        std.posix.PROT.READ,
        .{ .TYPE = .SHARED },
        file.handle,
        aligned_offset,
    );

    // Return view starting at actual offset
    return data[offset_diff..][0..length];
}
```

### Structured Data Access

Access structured binary data through memory mapping:

```zig
pub fn MappedStructFile(comptime T: type) type {
    return struct {
        data: []align(std.mem.page_size) const u8,

        const Self = @This();
        const record_size = @sizeOf(T);

        pub fn init(path: []const u8) !Self {
            const file = try std.fs.cwd().openFile(path, .{});
            defer file.close();

            const file_size = (try file.stat()).size;

            const data = try std.posix.mmap(
                null,
                file_size,
                std.posix.PROT.READ,
                .{ .TYPE = .SHARED },
                file.handle,
                0,
            );

            return .{ .data = data };
        }

        pub fn deinit(self: *Self) void {
            std.posix.munmap(self.data);
        }

        pub fn get(self: Self, index: usize) !T {
            const offset = index * record_size;
            if (offset + record_size > self.data.len) {
                return error.OutOfBounds;
            }

            const record_bytes = self.data[offset..][0..record_size];
            return @bitCast(record_bytes.*);
        }

        pub fn count(self: Self) usize {
            return self.data.len / record_size;
        }

        pub fn slice(self: Self) []const T {
            return std.mem.bytesAsSlice(T, self.data);
        }
    };
}
```

### Anonymous Memory Mappings

Create memory mappings not backed by a file:

```zig
pub fn createAnonymousMapping(size: usize) ![]align(std.mem.page_size) u8 {
    const data = try std.posix.mmap(
        null,
        size,
        std.posix.PROT.READ | std.posix.PROT.WRITE,
        .{ .TYPE = .PRIVATE, .ANONYMOUS = true },
        -1,  // No file descriptor
        0,
    );

    return data;
}
```

Use cases:
- Large temporary buffers
- Shared memory between parent/child processes
- Custom memory allocators

### Advising the Kernel

Give hints about access patterns:

```zig
pub fn adviseMappedFile(data: []align(std.mem.page_size) const u8, advice: enum {
    Normal,
    Random,
    Sequential,
    WillNeed,
    DontNeed,
}) !void {
    const linux_advice: i32 = switch (advice) {
        .Normal => std.os.linux.MADV.NORMAL,
        .Random => std.os.linux.MADV.RANDOM,
        .Sequential => std.os.linux.MADV.SEQUENTIAL,
        .WillNeed => std.os.linux.MADV.WILLNEED,
        .DontNeed => std.os.linux.MADV.DONTNEED,
    };

    _ = std.os.linux.madvise(data.ptr, data.len, linux_advice);
}
```

**Advice hints:**
- `Normal` - Default behavior
- `Random` - No readahead, aggressive page reclaim
- `Sequential` - Aggressive readahead, free pages behind
- `WillNeed` - Prefetch pages into memory now
- `DontNeed` - Don't need pages anymore, can free

### Syncing Changes to Disk

Control when changes are written:

```zig
pub fn syncMapping(data: []align(std.mem.page_size) u8, sync_type: enum {
    Async,
    Sync,
    Invalidate,
}) !void {
    const flags: c_int = switch (sync_type) {
        .Async => std.posix.MSF.ASYNC,       // Queue changes
        .Sync => std.posix.MSF.SYNC,         // Wait for completion
        .Invalidate => std.posix.MSF.INVALIDATE,  // Invalidate caches
    };

    try std.posix.msync(data, flags);
}
```

### Handling Large Files

Work with files larger than address space (32-bit systems):

```zig
pub fn processLargeFileMapped(
    path: []const u8,
    processor: *const fn ([]const u8) anyerror!void,
) !void {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const file_size = (try file.stat()).size;
    const chunk_size = 256 * 1024 * 1024; // 256MB windows

    var offset: usize = 0;
    while (offset < file_size) {
        const remaining = file_size - offset;
        const map_size = @min(remaining, chunk_size);

        const data = try std.posix.mmap(
            null,
            map_size,
            std.posix.PROT.READ,
            .{ .TYPE = .SHARED },
            file.handle,
            offset,
        );
        defer std.posix.munmap(data);

        try processor(data);

        offset += map_size;
    }
}
```

### Binary Search in Mapped Files

Efficiently search sorted mapped files:

```zig
pub fn binarySearchMapped(
    comptime T: type,
    data: []align(std.mem.page_size) const u8,
    key: T,
) ?usize {
    const records = std.mem.bytesAsSlice(T, data);

    var left: usize = 0;
    var right: usize = records.len;

    while (left < right) {
        const mid = left + (right - left) / 2;

        if (records[mid] == key) {
            return mid;
        } else if (records[mid] < key) {
            left = mid + 1;
        } else {
            right = mid;
        }
    }

    return null;
}
```

### Error Handling

Handle common mapping errors:

```zig
pub fn safeMmap(path: []const u8) ![]align(std.mem.page_size) const u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const file_size = (try file.stat()).size;
    if (file_size == 0) return error.EmptyFile;

    return std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ,
        .{ .TYPE = .SHARED },
        file.handle,
        0,
    ) catch |err| switch (err) {
        error.MemoryMappingNotSupported => {
            std.debug.print("Memory mapping not supported\n", .{});
            return error.MappingFailed;
        },
        error.AccessDenied => {
            std.debug.print("Permission denied\n", .{});
            return error.PermissionDenied;
        },
        error.OutOfMemory => {
            std.debug.print("Out of address space\n", .{});
            return error.AddressSpaceExhausted;
        },
        else => return err,
    };
}
```

### Performance Considerations

**Memory mapping is faster when:**
- Random access (no sequential access penalty)
- Multiple reads from same data
- File larger than typical buffer (> 1MB)
- Data accessed repeatedly

**Regular I/O is faster when:**
- Sequential scans (better cache locality)
- Small files (< 4KB)
- Single pass over data
- Network filesystems

**Page faults:**
- First access to each page causes page fault
- Can cause unpredictable latency
- Use `MADV.WILLNEED` to prefetch if needed

**Memory usage:**
- Mapping doesn't use RAM immediately
- Pages loaded on access
- OS may keep pages cached
- Multiple processes can share pages

### Platform Differences

**Linux-specific features:**
```zig
// Huge pages for better TLB efficiency
std.os.linux.mmap(
    null,
    size,
    std.os.linux.PROT.READ,
    std.os.linux.MAP.PRIVATE | std.os.linux.MAP.HUGETLB,
    -1,
    0,
);
```

**Cross-platform portable code:**
```zig
// Use std.posix for portable APIs
const data = try std.posix.mmap(...);  // Works on Linux, macOS, BSDs
```

### Related Functions

- `std.posix.mmap()` - Map file into memory
- `std.posix.munmap()` - Unmap memory region
- `std.posix.msync()` - Sync changes to disk
- `std.os.linux.madvise()` - Give usage advice (Linux)
- `std.os.linux.mprotect()` - Change protection
- `std.mem.page_size` - System page size constant

### Full Tested Code

```zig
const std = @import("std");

const page_size_min = std.heap.page_size_min;

// ANCHOR: basic_mmap
/// Map file for reading only
pub fn mapFileReadOnly(path: []const u8) !struct {
    data: []align(page_size_min) const u8,
    file: std.fs.File,
} {
    const file = try std.fs.cwd().openFile(path, .{});
    errdefer file.close();

    const file_size = (try file.stat()).size;

    // Can't map empty files
    if (file_size == 0) {
        return error.EmptyFile;
    }

    const data = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ,
        .{ .TYPE = .SHARED },
        file.handle,
        0,
    );

    return .{ .data = data, .file = file };
}

/// Map file for reading and writing
pub fn mapFileReadWrite(path: []const u8) !struct {
    data: []align(page_size_min) u8,
    file: std.fs.File,
} {
    const file = try std.fs.cwd().openFile(path, .{ .mode = .read_write });
    errdefer file.close();

    const file_size = (try file.stat()).size;

    const data = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ | std.posix.PROT.WRITE,
        .{ .TYPE = .SHARED },
        file.handle,
        0,
    );

    return .{ .data = data, .file = file };
}

/// Map file with private copy-on-write mapping
pub fn mapFilePrivate(path: []const u8) !struct {
    data: []align(page_size_min) u8,
    file: std.fs.File,
} {
    const file = try std.fs.cwd().openFile(path, .{});
    errdefer file.close();

    const file_size = (try file.stat()).size;

    const data = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ | std.posix.PROT.WRITE,
        .{ .TYPE = .PRIVATE },
        file.handle,
        0,
    );

    return .{ .data = data, .file = file };
}

/// Unmap and close file
pub fn unmapFile(mapping: anytype) void {
    std.posix.munmap(mapping.data);
    mapping.file.close();
}

/// Sync changes to disk
pub fn syncMapping(data: []align(page_size_min) u8, async_sync: bool) !void {
    const flags: c_int = if (async_sync) @intCast(std.posix.MSF.ASYNC) else @intCast(std.posix.MSF.SYNC);
    try std.posix.msync(data, flags);
}

/// Create anonymous memory mapping
pub fn createAnonymousMapping(size: usize) ![]align(page_size_min) u8 {
    const data = try std.posix.mmap(
        null,
        size,
        std.posix.PROT.READ | std.posix.PROT.WRITE,
        .{ .TYPE = .PRIVATE, .ANONYMOUS = true },
        -1,
        0,
    );

    return data;
}
// ANCHOR_END: basic_mmap

// ANCHOR: structured_mmap
/// Mapped struct file for random access
pub fn MappedStructFile(comptime T: type) type {
    return struct {
        data: []align(page_size_min) const u8,
        file: std.fs.File,

        const Self = @This();
        const record_size = @sizeOf(T);

        pub fn init(path: []const u8) !Self {
            const file = try std.fs.cwd().openFile(path, .{});
            errdefer file.close();

            const file_size = (try file.stat()).size;

            const data = try std.posix.mmap(
                null,
                file_size,
                std.posix.PROT.READ,
                .{ .TYPE = .SHARED },
                file.handle,
                0,
            );

            return .{ .data = data, .file = file };
        }

        pub fn deinit(self: *Self) void {
            std.posix.munmap(self.data);
            self.file.close();
        }

        pub fn get(self: Self, index: usize) !T {
            const offset = index * record_size;
            if (offset + record_size > self.data.len) {
                return error.OutOfBounds;
            }

            const record_bytes = self.data[offset..][0..record_size];
            return @bitCast(record_bytes.*);
        }

        pub fn count(self: Self) usize {
            return self.data.len / record_size;
        }

        pub fn slice(self: Self) []const T {
            return std.mem.bytesAsSlice(T, self.data);
        }
    };
}

/// Binary search in mapped file
pub fn binarySearchMapped(
    comptime T: type,
    data: []align(page_size_min) const u8,
    key: T,
    comptime lessThan: fn (T, T) bool,
) ?usize {
    const records = std.mem.bytesAsSlice(T, data);

    var left: usize = 0;
    var right: usize = records.len;

    while (left < right) {
        const mid = left + (right - left) / 2;

        // Check if records[mid] == key by the ordering
        if (!lessThan(records[mid], key) and !lessThan(key, records[mid])) {
            return mid;
        } else if (lessThan(records[mid], key)) {
            left = mid + 1;
        } else {
            right = mid;
        }
    }

    return null;
}
// ANCHOR_END: structured_mmap

// Test structures

const Record = extern struct {
    id: u32,
    value: f32,

    pub fn eql(self: Record, other: Record) bool {
        return self.id == other.id and self.value == other.value;
    }
};

// Tests

test "map read only" {
    const test_path = "/tmp/test_mmap_ro.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create test file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("Hello, Memory Map!");
    }

    // Map and read
    const mapping = try mapFileReadOnly(test_path);
    defer unmapFile(mapping);

    try std.testing.expectEqualStrings("Hello, Memory Map!", mapping.data);
}

test "map read write" {
    const test_path = "/tmp/test_mmap_rw.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create test file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("AAAA");
    }

    // Map, modify, and sync
    {
        const mapping = try mapFileReadWrite(test_path);
        defer unmapFile(mapping);

        // Modify in place
        mapping.data[0] = 'B';
        mapping.data[1] = 'B';

        // Sync to disk
        try syncMapping(mapping.data, false);
    }

    // Verify changes persisted
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [4]u8 = undefined;
    _ = try file.read(&buffer);

    try std.testing.expectEqualStrings("BBAA", &buffer);
}

test "map private copy-on-write" {
    const test_path = "/tmp/test_mmap_private.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create test file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("AAAA");
    }

    // Map with private mapping
    {
        const mapping = try mapFilePrivate(test_path);
        defer unmapFile(mapping);

        // Modify mapping (copy-on-write)
        mapping.data[0] = 'B';
        mapping.data[1] = 'B';

        // Changes are in memory but NOT written to file
    }

    // Verify file unchanged
    const file = try std.fs.cwd().openFile(test_path, .{});
    defer file.close();

    var buffer: [4]u8 = undefined;
    _ = try file.read(&buffer);

    try std.testing.expectEqualStrings("AAAA", &buffer);
}

test "anonymous mapping" {
    const size = page_size_min;
    const data = try createAnonymousMapping(size);
    defer std.posix.munmap(data);

    // Write to anonymous mapping
    @memset(data, 42);

    // Verify
    try std.testing.expect(std.mem.allEqual(u8, data, 42));
}

test "mapped struct file" {
    const test_path = "/tmp/test_mmap_struct.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create file with records
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var i: u32 = 0;
        while (i < 10) : (i += 1) {
            const record = Record{
                .id = i,
                .value = @floatFromInt(i),
            };
            const bytes: [@sizeOf(Record)]u8 = @bitCast(record);
            try file.writeAll(&bytes);
        }
    }

    // Map and access
    var mapped = try MappedStructFile(Record).init(test_path);
    defer mapped.deinit();

    // Check count
    try std.testing.expectEqual(@as(usize, 10), mapped.count());

    // Random access
    const record5 = try mapped.get(5);
    try std.testing.expectEqual(@as(u32, 5), record5.id);
    try std.testing.expectEqual(@as(f32, 5.0), record5.value);

    // Slice access
    const all_records = mapped.slice();
    try std.testing.expectEqual(@as(usize, 10), all_records.len);
}

test "mapped struct file out of bounds" {
    const test_path = "/tmp/test_mmap_bounds.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create small file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        const record = Record{ .id = 1, .value = 1.0 };
        const bytes: [@sizeOf(Record)]u8 = @bitCast(record);
        try file.writeAll(&bytes);
    }

    var mapped = try MappedStructFile(Record).init(test_path);
    defer mapped.deinit();

    // Try to access out of bounds
    const result = mapped.get(10);
    try std.testing.expectError(error.OutOfBounds, result);
}

test "binary search in mapped file" {
    const test_path = "/tmp/test_mmap_search.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create sorted records
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var i: u32 = 0;
        while (i < 100) : (i += 1) {
            const record = Record{
                .id = i * 2, // Even numbers only
                .value = @floatFromInt(i),
            };
            const bytes: [@sizeOf(Record)]u8 = @bitCast(record);
            try file.writeAll(&bytes);
        }
    }

    // Map and search
    const mapping = try mapFileReadOnly(test_path);
    defer unmapFile(mapping);

    const lessThan = struct {
        fn lt(a: Record, b: Record) bool {
            return a.id < b.id;
        }
    }.lt;

    // Search for existing key
    const found = binarySearchMapped(Record, mapping.data, Record{ .id = 50, .value = 0 }, lessThan);
    try std.testing.expect(found != null);
    try std.testing.expectEqual(@as(usize, 25), found.?);

    // Search for non-existing key
    const not_found = binarySearchMapped(Record, mapping.data, Record{ .id = 51, .value = 0 }, lessThan);
    try std.testing.expect(not_found == null);
}

test "map empty file" {
    const test_path = "/tmp/test_mmap_empty.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create empty file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
    }

    // Try to map empty file - should fail
    const result = mapFileReadOnly(test_path);
    try std.testing.expectError(error.EmptyFile, result);
}

test "map large file" {
    const test_path = "/tmp/test_mmap_large.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    const size: usize = 1024 * 1024; // 1MB

    // Create large file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        const chunk = [_]u8{'X'} ** page_size_min;
        var remaining: usize = size;
        while (remaining > 0) {
            const to_write = @min(remaining, chunk.len);
            try file.writeAll(chunk[0..to_write]);
            remaining -= to_write;
        }
    }

    // Map and verify
    const mapping = try mapFileReadOnly(test_path);
    defer unmapFile(mapping);

    try std.testing.expectEqual(size, mapping.data.len);
    try std.testing.expect(std.mem.allEqual(u8, mapping.data, 'X'));
}

test "multiple mappings of same file" {
    const test_path = "/tmp/test_mmap_multiple.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create test file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("Shared Data");
    }

    // Create two mappings
    const mapping1 = try mapFileReadOnly(test_path);
    defer unmapFile(mapping1);

    const mapping2 = try mapFileReadOnly(test_path);
    defer unmapFile(mapping2);

    // Both should see same data
    try std.testing.expectEqualStrings("Shared Data", mapping1.data);
    try std.testing.expectEqualStrings("Shared Data", mapping2.data);
}

test "modify through one shared mapping visible in another" {
    const test_path = "/tmp/test_mmap_shared.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create test file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("AAAA");
    }

    // Create two read-write mappings
    const mapping1 = try mapFileReadWrite(test_path);
    defer unmapFile(mapping1);

    const mapping2 = try mapFileReadWrite(test_path);
    defer unmapFile(mapping2);

    // Modify through first mapping
    mapping1.data[0] = 'B';
    try syncMapping(mapping1.data, false);

    // Sync second mapping to see changes
    try syncMapping(mapping2.data, false);

    // Changes should be visible (though behavior may vary by system)
    try std.testing.expectEqual(@as(u8, 'B'), mapping2.data[0]);
}

test "page alignment" {
    const test_path = "/tmp/test_mmap_align.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create test file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("Test");
    }

    const mapping = try mapFileReadOnly(test_path);
    defer unmapFile(mapping);

    // Check that mapping is page-aligned
    const addr = @intFromPtr(mapping.data.ptr);
    try std.testing.expectEqual(@as(usize, 0), addr % page_size_min);
}

test "sync async vs sync" {
    const test_path = "/tmp/test_mmap_sync.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create test file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("AAAA");
    }

    const mapping = try mapFileReadWrite(test_path);
    defer unmapFile(mapping);

    // Modify
    mapping.data[0] = 'X';

    // Async sync (queues changes)
    try syncMapping(mapping.data, true);

    // Sync sync (waits for completion)
    try syncMapping(mapping.data, false);
}

test "access after file close" {
    const test_path = "/tmp/test_mmap_after_close.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create test file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
        try file.writeAll("Data persists!");
    }

    var data: []align(page_size_min) const u8 = undefined;

    // Map file and close immediately
    {
        const mapping = try mapFileReadOnly(test_path);
        data = mapping.data;
        // File closed here via defer, but mapping still valid
        mapping.file.close();
    }

    // Data still accessible through mapping
    try std.testing.expectEqualStrings("Data persists!", data);

    // Clean up mapping
    std.posix.munmap(data);
}

test "random access pattern" {
    const test_path = "/tmp/test_mmap_random.dat";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create file with identifiable data
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();

        var i: u8 = 0;
        while (i < 255) : (i += 1) {
            try file.writeAll(&[_]u8{i});
        }
    }

    const mapping = try mapFileReadOnly(test_path);
    defer unmapFile(mapping);

    // Random access
    try std.testing.expectEqual(@as(u8, 0), mapping.data[0]);
    try std.testing.expectEqual(@as(u8, 100), mapping.data[100]);
    try std.testing.expectEqual(@as(u8, 50), mapping.data[50]);
    try std.testing.expectEqual(@as(u8, 200), mapping.data[200]);
}
```

---

## Recipe 5.11: Manipulating Pathnames {#recipe-5-11}

**Tags:** allocators, arraylist, data-structures, error-handling, files-io, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_11.zig`

### Problem

You need to manipulate file paths in a cross-platform way, handling different path separators and path formats across operating systems.

### Solution

### Basic Manipulation

```zig
test "join paths" {
    const allocator = std.testing.allocator;

    const path = try joinPaths(allocator, &.{ "usr", "local", "bin" });
    defer allocator.free(path);

    try std.testing.expect(path.len > 0);
    try std.testing.expect(std.mem.indexOf(u8, path, "usr") != null);
    try std.testing.expect(std.mem.indexOf(u8, path, "local") != null);
    try std.testing.expect(std.mem.indexOf(u8, path, "bin") != null);
}

test "join empty components" {
    const allocator = std.testing.allocator;

    const path = try joinPaths(allocator, &.{});
    defer allocator.free(path);

    try std.testing.expectEqualStrings("", path);
}

test "join single component" {
    const allocator = std.testing.allocator;

    const path = try joinPaths(allocator, &.{"single"});
    defer allocator.free(path);

    try std.testing.expectEqualStrings("single", path);
}

test "basename" {
    try std.testing.expectEqualStrings("file.txt", getBasename("/home/user/file.txt"));
    try std.testing.expectEqualStrings("file.txt", getBasename("file.txt"));
    try std.testing.expectEqualStrings("user", getBasename("/home/user/"));
    try std.testing.expectEqualStrings("", getBasename("/"));
}

test "dirname" {
    try std.testing.expectEqualStrings("/home/user", getDirname("/home/user/file.txt").?);
    try std.testing.expectEqualStrings("/home", getDirname("/home/user/").?);
    try std.testing.expect(getDirname("file.txt") == null);
    try std.testing.expectEqualStrings("/", getDirname("/file.txt").?);
}

test "extension" {
    try std.testing.expectEqualStrings(".txt", getExtension("file.txt"));
    try std.testing.expectEqualStrings(".gz", getExtension("archive.tar.gz")); // Only returns last extension
    try std.testing.expectEqualStrings("", getExtension("noext"));
    try std.testing.expectEqualStrings("", getExtension(".hidden"));
    try std.testing.expectEqualStrings(".conf", getExtension("/etc/app.conf"));
}

test "stem" {
    try std.testing.expectEqualStrings("file", getStem("file.txt"));
    try std.testing.expectEqualStrings("archive.tar", getStem("archive.tar.gz"));
    try std.testing.expectEqualStrings("noext", getStem("noext"));
    try std.testing.expectEqualStrings(".hidden", getStem(".hidden"));
}
```

### Normalize Paths

```zig
test "normalize path" {
    const allocator = std.testing.allocator;

    const normalized = try normalizePath(allocator, "a/./b/../c");
    defer allocator.free(normalized);

    try std.testing.expectEqualStrings("a/c", normalized);
}

test "normalize path with multiple dots" {
    const allocator = std.testing.allocator;

    const normalized = try normalizePath(allocator, "a/b/../../c");
    defer allocator.free(normalized);

    try std.testing.expectEqualStrings("c", normalized);
}

test "normalize path with redundant separators" {
    const allocator = std.testing.allocator;

    const normalized = try normalizePath(allocator, "a//b///c");
    defer allocator.free(normalized);

    try std.testing.expectEqualStrings("a/b/c", normalized);
}
```

### Safe Join

```zig
test "safe join valid" {
    const allocator = std.testing.allocator;

    const path = try safeJoin(allocator, "/base", "sub/file.txt");
    defer allocator.free(path);

    try std.testing.expect(std.mem.indexOf(u8, path, "base") != null);
    try std.testing.expect(std.mem.indexOf(u8, path, "sub") != null);
}

test "safe join rejects parent directory" {
    const allocator = std.testing.allocator;

    const result = safeJoin(allocator, "/base", "../etc");
    try std.testing.expectError(error.ParentDirectoryNotAllowed, result);
}

test "safe join rejects absolute path" {
    const allocator = std.testing.allocator;

    const result = safeJoin(allocator, "/base", "/etc/passwd");
    try std.testing.expectError(error.AbsolutePathNotAllowed, result);
}
```

### Discussion

### Path Separators

Different operating systems use different path separators:
- **Unix/Linux/macOS**: `/` (forward slash)
- **Windows**: `\` (backslash)

Zig's `std.fs.path` handles this automatically:

```zig
// Current platform's separator
const sep = std.fs.path.sep;

test "path separator" {
    if (@import("builtin").os.tag == .windows) {
        try std.testing.expectEqual(@as(u8, '\\'), std.fs.path.sep);
    } else {
        try std.testing.expectEqual(@as(u8, '/'), std.fs.path.sep);
    }
}
```

### Joining Paths

Combine path components with the correct separator:

```zig
pub fn joinPaths(allocator: std.mem.Allocator, components: []const []const u8) ![]u8 {
    return try std.fs.path.join(allocator, components);
}

test "join paths" {
    const allocator = std.testing.allocator;

    const path = try std.fs.path.join(allocator, &.{ "usr", "local", "bin" });
    defer allocator.free(path);

    // On Unix: "usr/local/bin"
    // On Windows: "usr\local\bin"
    try std.testing.expect(path.len > 0);
}
```

### Getting Basename

Extract the final component of a path:

```zig
pub fn getBasename(path: []const u8) []const u8 {
    return std.fs.path.basename(path);
}

test "basename" {
    try std.testing.expectEqualStrings("file.txt", std.fs.path.basename("/home/user/file.txt"));
    try std.testing.expectEqualStrings("file.txt", std.fs.path.basename("file.txt"));
    try std.testing.expectEqualStrings("user", std.fs.path.basename("/home/user/"));
}
```

### Getting Directory Name

Get the directory portion of a path:

```zig
pub fn getDirname(path: []const u8) ?[]const u8 {
    return std.fs.path.dirname(path);
}

test "dirname" {
    try std.testing.expectEqualStrings("/home/user", std.fs.path.dirname("/home/user/file.txt").?);
    try std.testing.expectEqualStrings("/home", std.fs.path.dirname("/home/user/").?);
    try std.testing.expect(std.fs.path.dirname("file.txt") == null);
}
```

### Getting File Extension

Extract the file extension:

```zig
pub fn getExtension(path: []const u8) []const u8 {
    return std.fs.path.extension(path);
}

test "extension" {
    try std.testing.expectEqualStrings(".txt", std.fs.path.extension("file.txt"));
    try std.testing.expectEqualStrings(".tar.gz", std.fs.path.extension("archive.tar.gz"));
    try std.testing.expectEqualStrings("", std.fs.path.extension("noext"));
    try std.testing.expectEqualStrings("", std.fs.path.extension(".hidden"));
}
```

### Getting Stem (Name Without Extension)

Get filename without extension:

```zig
pub fn getStem(path: []const u8) []const u8 {
    return std.fs.path.stem(path);
}

test "stem" {
    try std.testing.expectEqualStrings("file", std.fs.path.stem("file.txt"));
    try std.testing.expectEqualStrings("archive.tar", std.fs.path.stem("archive.tar.gz"));
    try std.testing.expectEqualStrings("noext", std.fs.path.stem("noext"));
}
```

### Resolving Paths

Join and normalize paths:

```zig
pub fn resolvePath(allocator: std.mem.Allocator, components: []const []const u8) ![]u8 {
    const joined = try std.fs.path.join(allocator, components);
    errdefer allocator.free(joined);

    // Resolve removes redundant separators and dots
    return try std.fs.path.resolve(allocator, &.{joined});
}

test "resolve path" {
    const allocator = std.testing.allocator;

    const path = try std.fs.path.resolve(allocator, &.{ "a/b", "../c" });
    defer allocator.free(path);

    // Normalizes path components
    try std.testing.expect(path.len > 0);
}
```

### Checking if Path is Absolute

Determine if path is absolute or relative:

```zig
pub fn isAbsolutePath(path: []const u8) bool {
    return std.fs.path.isAbsolute(path);
}

test "is absolute" {
    try std.testing.expect(std.fs.path.isAbsolute("/home/user"));
    try std.testing.expect(!std.fs.path.isAbsolute("relative/path"));

    if (@import("builtin").os.tag == .windows) {
        try std.testing.expect(std.fs.path.isAbsolute("C:\\Users"));
    }
}
```

### Relative Paths

Compute relative path from one to another:

```zig
pub fn relativePath(allocator: std.mem.Allocator, from: []const u8, to: []const u8) ![]u8 {
    return try std.fs.path.relative(allocator, from, to);
}

test "relative path" {
    const allocator = std.testing.allocator;

    const rel = try std.fs.path.relative(allocator, "/home/user", "/home/user/docs/file.txt");
    defer allocator.free(rel);

    try std.testing.expectEqualStrings("docs/file.txt", rel);
}
```

### Splitting Paths

Split path into components:

```zig
pub fn splitPath(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    var components: std.ArrayList([]const u8) = .{};
    errdefer components.deinit(allocator);

    var iter = std.mem.splitScalar(u8, path, std.fs.path.sep);
    while (iter.next()) |component| {
        if (component.len > 0) {
            try components.append(allocator, component);
        }
    }

    return components.toOwnedSlice(allocator);
}

test "split path" {
    const allocator = std.testing.allocator;

    const components = try splitPath(allocator, "home/user/file.txt");
    defer allocator.free(components);

    try std.testing.expectEqual(@as(usize, 3), components.len);
    try std.testing.expectEqualStrings("home", components[0]);
    try std.testing.expectEqualStrings("user", components[1]);
    try std.testing.expectEqualStrings("file.txt", components[2]);
}
```

### Normalizing Paths

Clean up redundant separators and resolve dots:

```zig
pub fn normalizePath(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    // Remove redundant separators and resolve . and ..
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    var iter = std.mem.splitScalar(u8, path, std.fs.path.sep);
    var components: std.ArrayList([]const u8) = .{};
    defer components.deinit(allocator);

    while (iter.next()) |component| {
        if (component.len == 0 or std.mem.eql(u8, component, ".")) {
            continue;
        } else if (std.mem.eql(u8, component, "..")) {
            if (components.items.len > 0) {
                _ = components.pop();
            }
        } else {
            try components.append(allocator, component);
        }
    }

    // Rebuild path
    for (components.items, 0..) |component, i| {
        if (i > 0) {
            try result.append(allocator, std.fs.path.sep);
        }
        try result.appendSlice(allocator, component);
    }

    return result.toOwnedSlice(allocator);
}

test "normalize path" {
    const allocator = std.testing.allocator;

    const normalized = try normalizePath(allocator, "a/./b/../c");
    defer allocator.free(normalized);

    try std.testing.expectEqualStrings("a/c", normalized);
}
```

### Converting Windows/Unix Paths

Convert between path formats:

```zig
pub fn convertToUnixPath(allocator: std.mem.Allocator, windows_path: []const u8) ![]u8 {
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    for (windows_path) |c| {
        if (c == '\\') {
            try result.append(allocator, '/');
        } else {
            try result.append(allocator, c);
        }
    }

    return result.toOwnedSlice(allocator);
}

pub fn convertToWindowsPath(allocator: std.mem.Allocator, unix_path: []const u8) ![]u8 {
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    for (unix_path) |c| {
        if (c == '/') {
            try result.append(allocator, '\\');
        } else {
            try result.append(allocator, c);
        }
    }

    return result.toOwnedSlice(allocator);
}
```

### Path Iterator

Iterate over path components:

```zig
pub const PathIterator = struct {
    path: []const u8,
    index: usize = 0,

    pub fn init(path: []const u8) PathIterator {
        return .{ .path = path };
    }

    pub fn next(self: *PathIterator) ?[]const u8 {
        while (self.index < self.path.len) {
            const start = self.index;

            // Find next separator
            while (self.index < self.path.len and self.path[self.index] != std.fs.path.sep) {
                self.index += 1;
            }

            const component = self.path[start..self.index];

            // Skip separator
            if (self.index < self.path.len) {
                self.index += 1;
            }

            // Return non-empty components
            if (component.len > 0) {
                return component;
            }
        }

        return null;
    }
};

test "path iterator" {
    var iter = PathIterator.init("home/user/file.txt");

    try std.testing.expectEqualStrings("home", iter.next().?);
    try std.testing.expectEqualStrings("user", iter.next().?);
    try std.testing.expectEqualStrings("file.txt", iter.next().?);
    try std.testing.expect(iter.next() == null);
}
```

### Finding Common Path Prefix

Find shared prefix of multiple paths:

```zig
pub fn commonPrefix(allocator: std.mem.Allocator, paths: []const []const u8) ![]u8 {
    if (paths.len == 0) return try allocator.dupe(u8, "");
    if (paths.len == 1) return try allocator.dupe(u8, paths[0]);

    // Split all paths into components
    var all_components: std.ArrayList([][]const u8) = .{};
    defer {
        for (all_components.items) |components| {
            allocator.free(components);
        }
        all_components.deinit(allocator);
    }

    for (paths) |path| {
        const components = try splitPath(allocator, path);
        try all_components.append(allocator, components);
    }

    // Find common prefix length
    var prefix_len: usize = 0;
    const min_len = blk: {
        var min: usize = all_components.items[0].len;
        for (all_components.items[1..]) |components| {
            min = @min(min, components.len);
        }
        break :blk min;
    };

    outer: while (prefix_len < min_len) : (prefix_len += 1) {
        const component = all_components.items[0][prefix_len];
        for (all_components.items[1..]) |components| {
            if (!std.mem.eql(u8, component, components[prefix_len])) {
                break :outer;
            }
        }
    }

    // Rebuild prefix path
    if (prefix_len == 0) {
        return try allocator.dupe(u8, "");
    }

    return try std.fs.path.join(allocator, all_components.items[0][0..prefix_len]);
}
```

### Safe Path Joining

Prevent path traversal attacks:

```zig
pub fn safeJoin(allocator: std.mem.Allocator, base: []const u8, sub: []const u8) ![]u8 {
    // Reject absolute paths in sub
    if (std.fs.path.isAbsolute(sub)) {
        return error.AbsolutePathNotAllowed;
    }

    // Reject paths with ..
    if (std.mem.indexOf(u8, sub, "..") != null) {
        return error.ParentDirectoryNotAllowed;
    }

    return try std.fs.path.join(allocator, &.{ base, sub });
}

test "safe join" {
    const allocator = std.testing.allocator;

    // Valid join
    const valid = try safeJoin(allocator, "/base", "sub/file.txt");
    defer allocator.free(valid);

    // Invalid joins
    try std.testing.expectError(error.ParentDirectoryNotAllowed, safeJoin(allocator, "/base", "../etc"));
    try std.testing.expectError(error.AbsolutePathNotAllowed, safeJoin(allocator, "/base", "/etc/passwd"));
}
```

### Platform-Specific Paths

Handle platform-specific path formats:

```zig
pub fn getPlatformPath(allocator: std.mem.Allocator, generic: []const u8) ![]u8 {
    const builtin = @import("builtin");

    if (builtin.os.tag == .windows) {
        // Convert to Windows path
        return try convertToWindowsPath(allocator, generic);
    } else {
        // Unix path (no conversion needed)
        return try allocator.dupe(u8, generic);
    }
}
```

### Performance Tips

**Path operations:**
- `basename`, `dirname`, `extension` are zero-allocation (return slices)
- `join`, `resolve`, `relative` allocate new strings
- Cache results if used repeatedly

**Best practices:**
```zig
// Good: Single allocation
const path = try std.fs.path.join(allocator, &.{ "a", "b", "c" });
defer allocator.free(path);

// Bad: Multiple allocations
const temp1 = try std.fs.path.join(allocator, &.{ "a", "b" });
defer allocator.free(temp1);
const temp2 = try std.fs.path.join(allocator, &.{ temp1, "c" });
defer allocator.free(temp2);
```

### Related Functions

- `std.fs.path.join()` - Join path components
- `std.fs.path.basename()` - Get final path component
- `std.fs.path.dirname()` - Get directory portion
- `std.fs.path.extension()` - Get file extension
- `std.fs.path.stem()` - Get name without extension
- `std.fs.path.isAbsolute()` - Check if path is absolute
- `std.fs.path.relative()` - Compute relative path
- `std.fs.path.resolve()` - Resolve and normalize path
- `std.fs.path.sep` - Platform path separator

### Full Tested Code

```zig
const std = @import("std");

/// Join path components with correct separator
pub fn joinPaths(allocator: std.mem.Allocator, components: []const []const u8) ![]u8 {
    return try std.fs.path.join(allocator, components);
}

/// Get the basename (final component) of a path
pub fn getBasename(path: []const u8) []const u8 {
    return std.fs.path.basename(path);
}

/// Get the directory portion of a path
pub fn getDirname(path: []const u8) ?[]const u8 {
    return std.fs.path.dirname(path);
}

/// Get the file extension
pub fn getExtension(path: []const u8) []const u8 {
    return std.fs.path.extension(path);
}

/// Get the filename without extension
pub fn getStem(path: []const u8) []const u8 {
    return std.fs.path.stem(path);
}

/// Check if path is absolute
pub fn isAbsolutePath(path: []const u8) bool {
    return std.fs.path.isAbsolute(path);
}

/// Compute relative path from one to another
pub fn relativePath(allocator: std.mem.Allocator, from: []const u8, to: []const u8) ![]u8 {
    return try std.fs.path.relative(allocator, from, to);
}

/// Split path into components
pub fn splitPath(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    var components: std.ArrayList([]const u8) = .{};
    errdefer components.deinit(allocator);

    var iter = std.mem.splitScalar(u8, path, std.fs.path.sep);
    while (iter.next()) |component| {
        if (component.len > 0) {
            try components.append(allocator, component);
        }
    }

    return components.toOwnedSlice(allocator);
}

/// Normalize path by removing redundant separators and resolving dots
pub fn normalizePath(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    var iter = std.mem.splitScalar(u8, path, std.fs.path.sep);
    var components: std.ArrayList([]const u8) = .{};
    defer components.deinit(allocator);

    while (iter.next()) |component| {
        if (component.len == 0 or std.mem.eql(u8, component, ".")) {
            continue;
        } else if (std.mem.eql(u8, component, "..")) {
            if (components.items.len > 0) {
                _ = components.pop();
            }
        } else {
            try components.append(allocator, component);
        }
    }

    // Rebuild path
    for (components.items, 0..) |component, i| {
        if (i > 0) {
            try result.append(allocator, std.fs.path.sep);
        }
        try result.appendSlice(allocator, component);
    }

    return result.toOwnedSlice(allocator);
}

/// Convert Windows path to Unix format
pub fn convertToUnixPath(allocator: std.mem.Allocator, windows_path: []const u8) ![]u8 {
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    for (windows_path) |c| {
        if (c == '\\') {
            try result.append(allocator, '/');
        } else {
            try result.append(allocator, c);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Convert Unix path to Windows format
pub fn convertToWindowsPath(allocator: std.mem.Allocator, unix_path: []const u8) ![]u8 {
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    for (unix_path) |c| {
        if (c == '/') {
            try result.append(allocator, '\\');
        } else {
            try result.append(allocator, c);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Path iterator for traversing components
pub const PathIterator = struct {
    path: []const u8,
    index: usize = 0,

    pub fn init(path: []const u8) PathIterator {
        return .{ .path = path };
    }

    pub fn next(self: *PathIterator) ?[]const u8 {
        while (self.index < self.path.len) {
            const start = self.index;

            // Find next separator
            while (self.index < self.path.len and self.path[self.index] != std.fs.path.sep) {
                self.index += 1;
            }

            const component = self.path[start..self.index];

            // Skip separator
            if (self.index < self.path.len) {
                self.index += 1;
            }

            // Return non-empty components
            if (component.len > 0) {
                return component;
            }
        }

        return null;
    }
};

/// Find common prefix of multiple paths
pub fn commonPrefix(allocator: std.mem.Allocator, paths: []const []const u8) ![]u8 {
    if (paths.len == 0) return try allocator.dupe(u8, "");
    if (paths.len == 1) return try allocator.dupe(u8, paths[0]);

    // Split all paths into components
    var all_components: std.ArrayList([][]const u8) = .{};
    defer {
        for (all_components.items) |components| {
            allocator.free(components);
        }
        all_components.deinit(allocator);
    }

    for (paths) |path| {
        const components = try splitPath(allocator, path);
        try all_components.append(allocator, components);
    }

    // Find common prefix length
    var prefix_len: usize = 0;
    const min_len = blk: {
        var min: usize = all_components.items[0].len;
        for (all_components.items[1..]) |components| {
            min = @min(min, components.len);
        }
        break :blk min;
    };

    outer: while (prefix_len < min_len) : (prefix_len += 1) {
        const component = all_components.items[0][prefix_len];
        for (all_components.items[1..]) |components| {
            if (!std.mem.eql(u8, component, components[prefix_len])) {
                break :outer;
            }
        }
    }

    // Rebuild prefix path
    if (prefix_len == 0) {
        return try allocator.dupe(u8, "");
    }

    return try std.fs.path.join(allocator, all_components.items[0][0..prefix_len]);
}

/// Safe path joining that prevents directory traversal
pub fn safeJoin(allocator: std.mem.Allocator, base: []const u8, sub: []const u8) ![]u8 {
    // Reject absolute paths in sub
    if (std.fs.path.isAbsolute(sub)) {
        return error.AbsolutePathNotAllowed;
    }

    // Reject paths with ..
    if (std.mem.indexOf(u8, sub, "..") != null) {
        return error.ParentDirectoryNotAllowed;
    }

    return try std.fs.path.join(allocator, &.{ base, sub });
}

// Tests

// ANCHOR: basic_manipulation
test "join paths" {
    const allocator = std.testing.allocator;

    const path = try joinPaths(allocator, &.{ "usr", "local", "bin" });
    defer allocator.free(path);

    try std.testing.expect(path.len > 0);
    try std.testing.expect(std.mem.indexOf(u8, path, "usr") != null);
    try std.testing.expect(std.mem.indexOf(u8, path, "local") != null);
    try std.testing.expect(std.mem.indexOf(u8, path, "bin") != null);
}

test "join empty components" {
    const allocator = std.testing.allocator;

    const path = try joinPaths(allocator, &.{});
    defer allocator.free(path);

    try std.testing.expectEqualStrings("", path);
}

test "join single component" {
    const allocator = std.testing.allocator;

    const path = try joinPaths(allocator, &.{"single"});
    defer allocator.free(path);

    try std.testing.expectEqualStrings("single", path);
}

test "basename" {
    try std.testing.expectEqualStrings("file.txt", getBasename("/home/user/file.txt"));
    try std.testing.expectEqualStrings("file.txt", getBasename("file.txt"));
    try std.testing.expectEqualStrings("user", getBasename("/home/user/"));
    try std.testing.expectEqualStrings("", getBasename("/"));
}

test "dirname" {
    try std.testing.expectEqualStrings("/home/user", getDirname("/home/user/file.txt").?);
    try std.testing.expectEqualStrings("/home", getDirname("/home/user/").?);
    try std.testing.expect(getDirname("file.txt") == null);
    try std.testing.expectEqualStrings("/", getDirname("/file.txt").?);
}

test "extension" {
    try std.testing.expectEqualStrings(".txt", getExtension("file.txt"));
    try std.testing.expectEqualStrings(".gz", getExtension("archive.tar.gz")); // Only returns last extension
    try std.testing.expectEqualStrings("", getExtension("noext"));
    try std.testing.expectEqualStrings("", getExtension(".hidden"));
    try std.testing.expectEqualStrings(".conf", getExtension("/etc/app.conf"));
}

test "stem" {
    try std.testing.expectEqualStrings("file", getStem("file.txt"));
    try std.testing.expectEqualStrings("archive.tar", getStem("archive.tar.gz"));
    try std.testing.expectEqualStrings("noext", getStem("noext"));
    try std.testing.expectEqualStrings(".hidden", getStem(".hidden"));
}
// ANCHOR_END: basic_manipulation

test "is absolute" {
    try std.testing.expect(isAbsolutePath("/home/user"));
    try std.testing.expect(!isAbsolutePath("relative/path"));
    try std.testing.expect(!isAbsolutePath(""));

    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        try std.testing.expect(isAbsolutePath("C:\\Users"));
        try std.testing.expect(isAbsolutePath("\\\\server\\share"));
    }
}

test "relative path" {
    const allocator = std.testing.allocator;

    const rel = try relativePath(allocator, "/home/user", "/home/user/docs/file.txt");
    defer allocator.free(rel);

    try std.testing.expectEqualStrings("docs/file.txt", rel);
}

test "relative path same directory" {
    const allocator = std.testing.allocator;

    const rel = try relativePath(allocator, "/home/user", "/home/user");
    defer allocator.free(rel);

    // Same directory returns empty string, not "."
    try std.testing.expectEqualStrings("", rel);
}

test "split path" {
    const allocator = std.testing.allocator;

    const components = try splitPath(allocator, "home/user/file.txt");
    defer allocator.free(components);

    try std.testing.expectEqual(@as(usize, 3), components.len);
    try std.testing.expectEqualStrings("home", components[0]);
    try std.testing.expectEqualStrings("user", components[1]);
    try std.testing.expectEqualStrings("file.txt", components[2]);
}

test "split path with leading separator" {
    const allocator = std.testing.allocator;

    const components = try splitPath(allocator, "/home/user");
    defer allocator.free(components);

    try std.testing.expectEqual(@as(usize, 2), components.len);
    try std.testing.expectEqualStrings("home", components[0]);
    try std.testing.expectEqualStrings("user", components[1]);
}

test "split empty path" {
    const allocator = std.testing.allocator;

    const components = try splitPath(allocator, "");
    defer allocator.free(components);

    try std.testing.expectEqual(@as(usize, 0), components.len);
}

// ANCHOR: normalize_paths
test "normalize path" {
    const allocator = std.testing.allocator;

    const normalized = try normalizePath(allocator, "a/./b/../c");
    defer allocator.free(normalized);

    try std.testing.expectEqualStrings("a/c", normalized);
}

test "normalize path with multiple dots" {
    const allocator = std.testing.allocator;

    const normalized = try normalizePath(allocator, "a/b/../../c");
    defer allocator.free(normalized);

    try std.testing.expectEqualStrings("c", normalized);
}

test "normalize path with redundant separators" {
    const allocator = std.testing.allocator;

    const normalized = try normalizePath(allocator, "a//b///c");
    defer allocator.free(normalized);

    try std.testing.expectEqualStrings("a/b/c", normalized);
}
// ANCHOR_END: normalize_paths

test "convert to unix path" {
    const allocator = std.testing.allocator;

    const unix = try convertToUnixPath(allocator, "C:\\Users\\name\\file.txt");
    defer allocator.free(unix);

    try std.testing.expectEqualStrings("C:/Users/name/file.txt", unix);
}

test "convert to windows path" {
    const allocator = std.testing.allocator;

    const windows = try convertToWindowsPath(allocator, "home/user/file.txt");
    defer allocator.free(windows);

    try std.testing.expectEqualStrings("home\\user\\file.txt", windows);
}

test "path iterator" {
    var iter = PathIterator.init("home/user/file.txt");

    try std.testing.expectEqualStrings("home", iter.next().?);
    try std.testing.expectEqualStrings("user", iter.next().?);
    try std.testing.expectEqualStrings("file.txt", iter.next().?);
    try std.testing.expect(iter.next() == null);
}

test "path iterator with leading separator" {
    var iter = PathIterator.init("/home/user");

    try std.testing.expectEqualStrings("home", iter.next().?);
    try std.testing.expectEqualStrings("user", iter.next().?);
    try std.testing.expect(iter.next() == null);
}

test "path iterator empty" {
    var iter = PathIterator.init("");
    try std.testing.expect(iter.next() == null);
}

test "common prefix two paths" {
    const allocator = std.testing.allocator;

    const paths = [_][]const u8{
        "home/user/docs/file1.txt",
        "home/user/docs/file2.txt",
    };

    const prefix = try commonPrefix(allocator, &paths);
    defer allocator.free(prefix);

    try std.testing.expectEqualStrings("home/user/docs", prefix);
}

test "common prefix no common" {
    const allocator = std.testing.allocator;

    const paths = [_][]const u8{
        "home/user/docs",
        "var/log/app",
    };

    const prefix = try commonPrefix(allocator, &paths);
    defer allocator.free(prefix);

    try std.testing.expectEqualStrings("", prefix);
}

test "common prefix single path" {
    const allocator = std.testing.allocator;

    const paths = [_][]const u8{"home/user/docs"};

    const prefix = try commonPrefix(allocator, &paths);
    defer allocator.free(prefix);

    try std.testing.expectEqualStrings("home/user/docs", prefix);
}

test "common prefix empty" {
    const allocator = std.testing.allocator;

    const paths: []const []const u8 = &.{};

    const prefix = try commonPrefix(allocator, paths);
    defer allocator.free(prefix);

    try std.testing.expectEqualStrings("", prefix);
}

// ANCHOR: safe_join
test "safe join valid" {
    const allocator = std.testing.allocator;

    const path = try safeJoin(allocator, "/base", "sub/file.txt");
    defer allocator.free(path);

    try std.testing.expect(std.mem.indexOf(u8, path, "base") != null);
    try std.testing.expect(std.mem.indexOf(u8, path, "sub") != null);
}

test "safe join rejects parent directory" {
    const allocator = std.testing.allocator;

    const result = safeJoin(allocator, "/base", "../etc");
    try std.testing.expectError(error.ParentDirectoryNotAllowed, result);
}

test "safe join rejects absolute path" {
    const allocator = std.testing.allocator;

    const result = safeJoin(allocator, "/base", "/etc/passwd");
    try std.testing.expectError(error.AbsolutePathNotAllowed, result);
}
// ANCHOR_END: safe_join

test "path separator" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        try std.testing.expectEqual(@as(u8, '\\'), std.fs.path.sep);
    } else {
        try std.testing.expectEqual(@as(u8, '/'), std.fs.path.sep);
    }
}

test "multiple join operations" {
    const allocator = std.testing.allocator;

    const path1 = try joinPaths(allocator, &.{ "a", "b" });
    defer allocator.free(path1);

    const path2 = try joinPaths(allocator, &.{ path1, "c" });
    defer allocator.free(path2);

    try std.testing.expect(std.mem.indexOf(u8, path2, "a") != null);
    try std.testing.expect(std.mem.indexOf(u8, path2, "b") != null);
    try std.testing.expect(std.mem.indexOf(u8, path2, "c") != null);
}

test "basename with multiple dots" {
    try std.testing.expectEqualStrings("archive.tar.gz", getBasename("/backup/archive.tar.gz"));
    try std.testing.expectEqualStrings("config.yaml.bak", getBasename("config.yaml.bak"));
}

test "normalize complex path" {
    const allocator = std.testing.allocator;

    const normalized = try normalizePath(allocator, "./a/b/../c/./d");
    defer allocator.free(normalized);

    try std.testing.expectEqualStrings("a/c/d", normalized);
}
```

---

## Recipe 5.12: Testing for the Existence of a File {#recipe-5-12}

**Tags:** allocators, concurrency, error-handling, files-io, memory, networking, resource-cleanup, sockets, testing, threading
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_12.zig`

### Problem

You need to check if a file or directory exists before performing operations on it.

### Solution

### Basic Existence

```zig
test "file exists" {
    const path = "/tmp/test_exists.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    // File doesn't exist yet
    try std.testing.expect(!pathExists(path));

    // Create file
    {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
    }

    // File exists now
    try std.testing.expect(pathExists(path));
}

test "file does not exist" {
    try std.testing.expect(!pathExists("/tmp/does_not_exist_12345.txt"));
}

test "is file" {
    const path = "/tmp/test_is_file.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
    }

    try std.testing.expect(isFile(path));
    try std.testing.expect(!isDirectory(path));
}

test "is directory" {
    const path = "/tmp/test_is_dir";
    try std.fs.cwd().makeDir(path);
    defer std.fs.cwd().deleteDir(path) catch {};

    try std.testing.expect(isDirectory(path));
    try std.testing.expect(!isFile(path));
}
```

### File Metadata

```zig
test "file age comparison" {
    const path1 = "/tmp/test_age1.txt";
    const path2 = "/tmp/test_age2.txt";

    defer std.fs.cwd().deleteFile(path1) catch {};
    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create first file
    {
        const file = try std.fs.cwd().createFile(path1, .{});
        defer file.close();
    }

    // Wait a bit
    std.Thread.sleep(10 * std.time.ns_per_ms);

    // Create second file
    {
        const file = try std.fs.cwd().createFile(path2, .{});
        defer file.close();
    }

    // path2 is newer than path1
    try std.testing.expect(try isNewerThan(path2, path1));
}

test "is older than" {
    const path = "/tmp/test_older.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
    }

    // File is not older than 1 second (just created)
    try std.testing.expect(!try isOlderThan(path, 1));
}

test "wait for file creation" {
    const path = "/tmp/test_wait.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    // Start background thread to create file
    const thread = try std.Thread.spawn(.{}, struct {
        fn create(file_path: []const u8) void {
            std.Thread.sleep(200 * std.time.ns_per_ms);
            const file = std.fs.cwd().createFile(file_path, .{}) catch return;
            file.close();
        }
    }.create, .{path});
    thread.detach();

    // Wait for file
    try waitForFile(path, 5000);
    try std.testing.expect(pathExists(path));
}

test "wait for file timeout" {
    const path = "/tmp/test_wait_timeout.txt";

    // File is never created, should timeout
    const result = waitForFile(path, 100);
    try std.testing.expectError(error.Timeout, result);
}
```

### Multiple Paths

```zig
test "all exist" {
    const path1 = "/tmp/test_all1.txt";
    const path2 = "/tmp/test_all2.txt";

    defer std.fs.cwd().deleteFile(path1) catch {};
    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create one file
    {
        const file = try std.fs.cwd().createFile(path1, .{});
        defer file.close();
    }

    const paths = [_][]const u8{ path1, path2 };

    // Not all exist
    try std.testing.expect(!allExist(&paths));

    // Create second file
    {
        const file = try std.fs.cwd().createFile(path2, .{});
        defer file.close();
    }

    // All exist now
    try std.testing.expect(allExist(&paths));
}

test "any exists" {
    const path1 = "/tmp/does_not_exist1.txt";
    const path2 = "/tmp/test_any.txt";

    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create one file
    {
        const file = try std.fs.cwd().createFile(path2, .{});
        defer file.close();
    }

    const paths = [_][]const u8{ path1, path2 };

    // At least one exists
    try std.testing.expect(anyExists(&paths));
}

test "any exists none" {
    const paths = [_][]const u8{
        "/tmp/does_not_exist1.txt",
        "/tmp/does_not_exist2.txt",
    };

    try std.testing.expect(!anyExists(&paths));
}

test "find first existing" {
    const path1 = "/tmp/does_not_exist1.txt";
    const path2 = "/tmp/test_first.txt";
    const path3 = "/tmp/does_not_exist2.txt";

    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create middle file
    {
        const file = try std.fs.cwd().createFile(path2, .{});
        defer file.close();
    }

    const paths = [_][]const u8{ path1, path2, path3 };
    const found = findFirstExisting(&paths);

    try std.testing.expect(found != null);
    try std.testing.expectEqualStrings(path2, found.?);
}

test "find first existing none" {
    const paths = [_][]const u8{
        "/tmp/does_not_exist1.txt",
        "/tmp/does_not_exist2.txt",
    };

    const found = findFirstExisting(&paths);
    try std.testing.expect(found == null);
}
```

### Discussion

### Basic Existence Check

The simplest way to check if a path exists:

```zig
pub fn pathExists(path: []const u8) bool {
    std.fs.cwd().access(path, .{}) catch return false;
    return true;
}
```

This works for both files and directories. It only checks if the path exists, not whether you have permission to read or write it.

### Checking File vs Directory

Distinguish between files and directories:

```zig
pub fn isFile(path: []const u8) bool {
    const stat = std.fs.cwd().statFile(path) catch return false;
    return stat.kind == .file;
}

pub fn isDirectory(path: []const u8) bool {
    const stat = std.fs.cwd().statFile(path) catch return false;
    return stat.kind == .directory;
}

test "file vs directory" {
    // File check
    {
        const file = try std.fs.cwd().createFile("/tmp/test_file.txt", .{});
        defer file.close();
    }
    defer std.fs.cwd().deleteFile("/tmp/test_file.txt") catch {};

    try std.testing.expect(isFile("/tmp/test_file.txt"));
    try std.testing.expect(!isDirectory("/tmp/test_file.txt"));

    // Directory check
    try std.fs.cwd().makeDir("/tmp/test_dir");
    defer std.fs.cwd().deleteDir("/tmp/test_dir") catch {};

    try std.testing.expect(isDirectory("/tmp/test_dir"));
    try std.testing.expect(!isFile("/tmp/test_dir"));
}
```

### Checking with Permissions

Verify you can actually access the file:

```zig
pub fn canRead(path: []const u8) bool {
    std.fs.cwd().access(path, .{ .mode = .read_only }) catch return false;
    return true;
}

pub fn canWrite(path: []const u8) bool {
    // Try opening for writing
    const file = std.fs.cwd().openFile(path, .{ .mode = .write_only }) catch return false;
    file.close();
    return true;
}

pub fn canExecute(path: []const u8) bool {
    // Platform-specific executable check
    const stat = std.fs.cwd().statFile(path) catch return false;

    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        // On Windows, check extension
        const ext = std.fs.path.extension(path);
        return std.mem.eql(u8, ext, ".exe") or
               std.mem.eql(u8, ext, ".bat") or
               std.mem.eql(u8, ext, ".cmd");
    } else {
        // On Unix, check file mode
        return (stat.mode & 0o111) != 0;
    }
}
```

### Getting File Type

Determine the type of filesystem object:

```zig
pub const FileType = enum {
    file,
    directory,
    symlink,
    block_device,
    character_device,
    named_pipe,
    unix_domain_socket,
    unknown,
};

pub fn getFileType(path: []const u8) !FileType {
    const stat = try std.fs.cwd().statFile(path);

    return switch (stat.kind) {
        .file => .file,
        .directory => .directory,
        .sym_link => .symlink,
        .block_device => .block_device,
        .character_device => .character_device,
        .named_pipe => .named_pipe,
        .unix_domain_socket => .unix_domain_socket,
        else => .unknown,
    };
}
```

### Checking File Age

Check when a file was last modified:

```zig
pub fn isNewerThan(path1: []const u8, path2: []const u8) !bool {
    const stat1 = try std.fs.cwd().statFile(path1);
    const stat2 = try std.fs.cwd().statFile(path2);

    return stat1.mtime > stat2.mtime;
}

pub fn isOlderThan(path: []const u8, seconds: i128) !bool {
    const stat = try std.fs.cwd().statFile(path);
    const now = std.time.nanoTimestamp();
    const age = now - stat.mtime;

    return age > (seconds * std.time.ns_per_s);
}

test "file age" {
    const path1 = "/tmp/test_age1.txt";
    const path2 = "/tmp/test_age2.txt";

    defer std.fs.cwd().deleteFile(path1) catch {};
    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create first file
    {
        const file = try std.fs.cwd().createFile(path1, .{});
        defer file.close();
    }

    // Wait a bit
    std.time.sleep(10 * std.time.ns_per_ms);

    // Create second file
    {
        const file = try std.fs.cwd().createFile(path2, .{});
        defer file.close();
    }

    // path2 is newer than path1
    try std.testing.expect(try isNewerThan(path2, path1));
}
```

### Waiting for File Creation

Wait for a file to be created:

```zig
pub fn waitForFile(path: []const u8, timeout_ms: u64) !void {
    const start = std.time.milliTimestamp();

    while (true) {
        if (pathExists(path)) {
            return;
        }

        const elapsed = std.time.milliTimestamp() - start;
        if (elapsed > timeout_ms) {
            return error.Timeout;
        }

        std.time.sleep(100 * std.time.ns_per_ms);
    }
}

test "wait for file" {
    const path = "/tmp/test_wait.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    // Start a background task to create the file
    const thread = try std.Thread.spawn(.{}, struct {
        fn create(file_path: []const u8) void {
            std.time.sleep(200 * std.time.ns_per_ms);
            const file = std.fs.cwd().createFile(file_path, .{}) catch return;
            file.close();
        }
    }.create, .{path});
    thread.detach();

    // Wait for file creation
    try waitForFile(path, 5000);
    try std.testing.expect(pathExists(path));
}
```

### Checking Symlinks

Work with symbolic links:

```zig
pub fn isSymlink(path: []const u8) bool {
    // Use lstat to not follow symlinks
    var buffer: [std.fs.max_path_bytes]u8 = undefined;
    const absolute = std.fs.cwd().realpath(path, &buffer) catch return false;

    const stat = std.fs.cwd().statFile(absolute) catch return false;
    return stat.kind == .sym_link;
}

pub fn symlinkTarget(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    var buffer: [std.fs.max_path_bytes]u8 = undefined;
    const target = try std.posix.readlink(path, &buffer);
    return try allocator.dupe(u8, target);
}
```

### Safe Existence Check

Handle all error cases explicitly:

```zig
pub fn safeExists(path: []const u8) !bool {
    std.fs.cwd().access(path, .{}) catch |err| switch (err) {
        error.FileNotFound => return false,
        error.AccessDenied => return error.PermissionDenied,
        else => return err,
    };
    return true;
}
```

### Checking Multiple Files

Check if multiple files exist:

```zig
pub fn allExist(paths: []const []const u8) bool {
    for (paths) |path| {
        if (!pathExists(path)) {
            return false;
        }
    }
    return true;
}

pub fn anyExists(paths: []const []const u8) bool {
    for (paths) |path| {
        if (pathExists(path)) {
            return true;
        }
    }
    return false;
}

test "multiple files" {
    const path1 = "/tmp/test_multi1.txt";
    const path2 = "/tmp/test_multi2.txt";

    defer std.fs.cwd().deleteFile(path1) catch {};
    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create one file
    {
        const file = try std.fs.cwd().createFile(path1, .{});
        defer file.close();
    }

    const paths = [_][]const u8{ path1, path2 };

    try std.testing.expect(!allExist(&paths));
    try std.testing.expect(anyExists(&paths));
}
```

### Finding First Existing File

Find the first file that exists from a list:

```zig
pub fn findFirstExisting(paths: []const []const u8) ?[]const u8 {
    for (paths) |path| {
        if (pathExists(path)) {
            return path;
        }
    }
    return null;
}

test "find first existing" {
    const path1 = "/tmp/does_not_exist1.txt";
    const path2 = "/tmp/test_first.txt";
    const path3 = "/tmp/does_not_exist2.txt";

    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create middle file
    {
        const file = try std.fs.cwd().createFile(path2, .{});
        defer file.close();
    }

    const paths = [_][]const u8{ path1, path2, path3 };
    const found = findFirstExisting(&paths);

    try std.testing.expect(found != null);
    try std.testing.expectEqualStrings(path2, found.?);
}
```

### Checking Parent Directory

Verify parent directory exists before creating file:

```zig
pub fn parentDirExists(path: []const u8) bool {
    const dir = std.fs.path.dirname(path) orelse return true;
    return isDirectory(dir);
}

pub fn ensureParentDir(path: []const u8) !void {
    const dir = std.fs.path.dirname(path) orelse return;

    std.fs.cwd().makePath(dir) catch |err| switch (err) {
        error.PathAlreadyExists => return,
        else => return err,
    };
}
```

### Performance Considerations

**Existence checks:**
- `access()` is fastest (doesn't return file info)
- `statFile()` slower but gives file metadata
- Cache results if checking repeatedly

**Best practices:**
```zig
// Good: Check then open
if (fileExists(path)) {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    // ...
}

// Better: Just try to open (EAFP style)
const file = std.fs.cwd().openFile(path, .{}) catch |err| switch (err) {
    error.FileNotFound => {
        // Handle missing file
        return;
    },
    else => return err,
};
defer file.close();
// File definitely exists here
```

**EAFP (Easier to Ask for Forgiveness than Permission):**
- More efficient (one system call instead of two)
- Handles race conditions better
- Preferred in Zig

### Platform Differences

**Windows:**
- Case-insensitive filesystem (usually)
- Different path separators
- Different file permissions model

**Unix/Linux:**
- Case-sensitive filesystem
- POSIX permissions (rwx)
- Special files (devices, sockets, pipes)

**Cross-platform code:**
```zig
pub fn exists(path: []const u8) bool {
    const builtin = @import("builtin");

    if (builtin.os.tag == .windows) {
        // Windows-specific checks if needed
        return pathExists(path);
    } else {
        // Unix checks
        return pathExists(path);
    }
}
```

### Related Functions

- `std.fs.Dir.access()` - Check if path exists
- `std.fs.Dir.statFile()` - Get file metadata
- `std.fs.Dir.openFile()` - Open file (fails if doesn't exist)
- `std.fs.Dir.makeDir()` - Create directory
- `std.fs.Dir.deleteFile()` - Delete file
- `std.posix.readlink()` - Read symlink target
- `std.fs.path.dirname()` - Get parent directory

### Full Tested Code

```zig
const std = @import("std");

/// Check if a path exists
pub fn pathExists(path: []const u8) bool {
    std.fs.cwd().access(path, .{}) catch return false;
    return true;
}

/// Check if path is a file
pub fn isFile(path: []const u8) bool {
    const stat = std.fs.cwd().statFile(path) catch return false;
    return stat.kind == .file;
}

/// Check if path is a directory
pub fn isDirectory(path: []const u8) bool {
    const stat = std.fs.cwd().statFile(path) catch return false;
    return stat.kind == .directory;
}

/// Check if file can be read
pub fn canRead(path: []const u8) bool {
    std.fs.cwd().access(path, .{ .mode = .read_only }) catch return false;
    return true;
}

/// Check if file can be written
pub fn canWrite(path: []const u8) bool {
    const file = std.fs.cwd().openFile(path, .{ .mode = .write_only }) catch return false;
    file.close();
    return true;
}

/// File type enumeration
pub const FileType = enum {
    file,
    directory,
    symlink,
    block_device,
    character_device,
    named_pipe,
    unix_domain_socket,
    unknown,
};

/// Get the type of filesystem object
pub fn getFileType(path: []const u8) !FileType {
    const stat = try std.fs.cwd().statFile(path);

    return switch (stat.kind) {
        .file => .file,
        .directory => .directory,
        .sym_link => .symlink,
        .block_device => .block_device,
        .character_device => .character_device,
        .named_pipe => .named_pipe,
        .unix_domain_socket => .unix_domain_socket,
        else => .unknown,
    };
}

/// Check if path1 is newer than path2
pub fn isNewerThan(path1: []const u8, path2: []const u8) !bool {
    const stat1 = try std.fs.cwd().statFile(path1);
    const stat2 = try std.fs.cwd().statFile(path2);

    return stat1.mtime > stat2.mtime;
}

/// Check if file is older than specified seconds
pub fn isOlderThan(path: []const u8, seconds: i128) !bool {
    const stat = try std.fs.cwd().statFile(path);
    const now = std.time.nanoTimestamp();
    const age = now - stat.mtime;

    return age > (seconds * std.time.ns_per_s);
}

/// Wait for a file to be created with timeout
pub fn waitForFile(path: []const u8, timeout_ms: u64) !void {
    const start = std.time.milliTimestamp();

    while (true) {
        if (pathExists(path)) {
            return;
        }

        const elapsed = std.time.milliTimestamp() - start;
        if (elapsed > timeout_ms) {
            return error.Timeout;
        }

        std.Thread.sleep(100 * std.time.ns_per_ms);
    }
}

/// Safe existence check with explicit error handling
pub fn safeExists(path: []const u8) !bool {
    std.fs.cwd().access(path, .{}) catch |err| switch (err) {
        error.FileNotFound => return false,
        error.AccessDenied => return error.PermissionDenied,
        else => return err,
    };
    return true;
}

/// Check if all paths exist
pub fn allExist(paths: []const []const u8) bool {
    for (paths) |path| {
        if (!pathExists(path)) {
            return false;
        }
    }
    return true;
}

/// Check if any path exists
pub fn anyExists(paths: []const []const u8) bool {
    for (paths) |path| {
        if (pathExists(path)) {
            return true;
        }
    }
    return false;
}

/// Find first existing file from list
pub fn findFirstExisting(paths: []const []const u8) ?[]const u8 {
    for (paths) |path| {
        if (pathExists(path)) {
            return path;
        }
    }
    return null;
}

/// Check if parent directory exists
pub fn parentDirExists(path: []const u8) bool {
    const dir = std.fs.path.dirname(path) orelse return true;
    return isDirectory(dir);
}

/// Ensure parent directory exists, creating if necessary
pub fn ensureParentDir(path: []const u8) !void {
    const dir = std.fs.path.dirname(path) orelse return;

    std.fs.cwd().makePath(dir) catch |err| switch (err) {
        error.PathAlreadyExists => return,
        else => return err,
    };
}

// Tests

// ANCHOR: basic_existence
test "file exists" {
    const path = "/tmp/test_exists.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    // File doesn't exist yet
    try std.testing.expect(!pathExists(path));

    // Create file
    {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
    }

    // File exists now
    try std.testing.expect(pathExists(path));
}

test "file does not exist" {
    try std.testing.expect(!pathExists("/tmp/does_not_exist_12345.txt"));
}

test "is file" {
    const path = "/tmp/test_is_file.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
    }

    try std.testing.expect(isFile(path));
    try std.testing.expect(!isDirectory(path));
}

test "is directory" {
    const path = "/tmp/test_is_dir";
    try std.fs.cwd().makeDir(path);
    defer std.fs.cwd().deleteDir(path) catch {};

    try std.testing.expect(isDirectory(path));
    try std.testing.expect(!isFile(path));
}
// ANCHOR_END: basic_existence

test "can read" {
    const path = "/tmp/test_can_read.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
    }

    try std.testing.expect(canRead(path));
}

test "can write" {
    const path = "/tmp/test_can_write.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
    }

    try std.testing.expect(canWrite(path));
}

test "get file type" {
    const file_path = "/tmp/test_type_file.txt";
    const dir_path = "/tmp/test_type_dir";

    defer std.fs.cwd().deleteFile(file_path) catch {};
    defer std.fs.cwd().deleteDir(dir_path) catch {};

    // Create file
    {
        const file = try std.fs.cwd().createFile(file_path, .{});
        defer file.close();
    }

    // Create directory
    try std.fs.cwd().makeDir(dir_path);

    // Check types
    try std.testing.expectEqual(FileType.file, try getFileType(file_path));
    try std.testing.expectEqual(FileType.directory, try getFileType(dir_path));
}

// ANCHOR: file_metadata
test "file age comparison" {
    const path1 = "/tmp/test_age1.txt";
    const path2 = "/tmp/test_age2.txt";

    defer std.fs.cwd().deleteFile(path1) catch {};
    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create first file
    {
        const file = try std.fs.cwd().createFile(path1, .{});
        defer file.close();
    }

    // Wait a bit
    std.Thread.sleep(10 * std.time.ns_per_ms);

    // Create second file
    {
        const file = try std.fs.cwd().createFile(path2, .{});
        defer file.close();
    }

    // path2 is newer than path1
    try std.testing.expect(try isNewerThan(path2, path1));
}

test "is older than" {
    const path = "/tmp/test_older.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
    }

    // File is not older than 1 second (just created)
    try std.testing.expect(!try isOlderThan(path, 1));
}

test "wait for file creation" {
    const path = "/tmp/test_wait.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    // Start background thread to create file
    const thread = try std.Thread.spawn(.{}, struct {
        fn create(file_path: []const u8) void {
            std.Thread.sleep(200 * std.time.ns_per_ms);
            const file = std.fs.cwd().createFile(file_path, .{}) catch return;
            file.close();
        }
    }.create, .{path});
    thread.detach();

    // Wait for file
    try waitForFile(path, 5000);
    try std.testing.expect(pathExists(path));
}

test "wait for file timeout" {
    const path = "/tmp/test_wait_timeout.txt";

    // File is never created, should timeout
    const result = waitForFile(path, 100);
    try std.testing.expectError(error.Timeout, result);
}
// ANCHOR_END: file_metadata

test "safe exists" {
    const path = "/tmp/test_safe_exists.txt";
    defer std.fs.cwd().deleteFile(path) catch {};

    // Doesn't exist
    try std.testing.expect(!try safeExists(path));

    // Create file
    {
        const file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
    }

    // Exists
    try std.testing.expect(try safeExists(path));
}

// ANCHOR: multiple_paths
test "all exist" {
    const path1 = "/tmp/test_all1.txt";
    const path2 = "/tmp/test_all2.txt";

    defer std.fs.cwd().deleteFile(path1) catch {};
    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create one file
    {
        const file = try std.fs.cwd().createFile(path1, .{});
        defer file.close();
    }

    const paths = [_][]const u8{ path1, path2 };

    // Not all exist
    try std.testing.expect(!allExist(&paths));

    // Create second file
    {
        const file = try std.fs.cwd().createFile(path2, .{});
        defer file.close();
    }

    // All exist now
    try std.testing.expect(allExist(&paths));
}

test "any exists" {
    const path1 = "/tmp/does_not_exist1.txt";
    const path2 = "/tmp/test_any.txt";

    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create one file
    {
        const file = try std.fs.cwd().createFile(path2, .{});
        defer file.close();
    }

    const paths = [_][]const u8{ path1, path2 };

    // At least one exists
    try std.testing.expect(anyExists(&paths));
}

test "any exists none" {
    const paths = [_][]const u8{
        "/tmp/does_not_exist1.txt",
        "/tmp/does_not_exist2.txt",
    };

    try std.testing.expect(!anyExists(&paths));
}

test "find first existing" {
    const path1 = "/tmp/does_not_exist1.txt";
    const path2 = "/tmp/test_first.txt";
    const path3 = "/tmp/does_not_exist2.txt";

    defer std.fs.cwd().deleteFile(path2) catch {};

    // Create middle file
    {
        const file = try std.fs.cwd().createFile(path2, .{});
        defer file.close();
    }

    const paths = [_][]const u8{ path1, path2, path3 };
    const found = findFirstExisting(&paths);

    try std.testing.expect(found != null);
    try std.testing.expectEqualStrings(path2, found.?);
}

test "find first existing none" {
    const paths = [_][]const u8{
        "/tmp/does_not_exist1.txt",
        "/tmp/does_not_exist2.txt",
    };

    const found = findFirstExisting(&paths);
    try std.testing.expect(found == null);
}
// ANCHOR_END: multiple_paths

test "parent dir exists" {
    // /tmp exists, so parent dir check should pass
    try std.testing.expect(parentDirExists("/tmp/some_file.txt"));

    // Root has no parent but returns true
    try std.testing.expect(parentDirExists("/"));
}

test "ensure parent dir" {
    const nested_path = "/tmp/test_parent/nested/file.txt";
    const dir_path = "/tmp/test_parent/nested";

    defer std.fs.cwd().deleteTree("/tmp/test_parent") catch {};

    // Create parent directories
    try ensureParentDir(nested_path);

    // Parent should exist
    try std.testing.expect(isDirectory(dir_path));
}

test "ensure parent dir idempotent" {
    const path = "/tmp/test_idem/file.txt";
    defer std.fs.cwd().deleteTree("/tmp/test_idem") catch {};

    // Create once
    try ensureParentDir(path);

    // Create again (should not error)
    try ensureParentDir(path);

    try std.testing.expect(isDirectory("/tmp/test_idem"));
}

test "empty path" {
    // Empty path should not exist
    try std.testing.expect(!pathExists(""));
}

test "root directory exists" {
    // Root should always exist
    try std.testing.expect(pathExists("/"));
    try std.testing.expect(isDirectory("/"));
}
```

---

## Recipe 5.13: Getting a Directory Listing {#recipe-5-13}

**Tags:** allocators, arraylist, data-structures, error-handling, files-io, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_13.zig`

### Problem

You need to list files and directories, optionally filtering by type or pattern, and sometimes recursively traversing subdirectories.

### Solution

### Basic Listing

```zig
test "list directory" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_list_dir";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create test files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_list_dir/file1.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_list_dir/file2.txt", .{});
        defer file2.close();
    }

    // List directory
    const entries = try listDirectory(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 2), entries.len);
}

test "list empty directory" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_empty_dir";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    const entries = try listDirectory(allocator, test_dir);
    defer allocator.free(entries);

    try std.testing.expectEqual(@as(usize, 0), entries.len);
}

test "list by type" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_by_type";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create files and subdirectory
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_by_type/file1.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_by_type/file2.txt", .{});
        defer file2.close();
    }
    try std.fs.cwd().makeDir("/tmp/test_by_type/subdir");

    var contents = try listByType(allocator, test_dir);
    defer contents.deinit(allocator);

    try std.testing.expectEqual(@as(usize, 2), contents.files.len);
    try std.testing.expectEqual(@as(usize, 1), contents.directories.len);
}
```

### Filtered Listing

```zig
test "list recursive" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_recursive";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create nested structure
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_recursive/file1.txt", .{});
        defer file1.close();
    }
    try std.fs.cwd().makeDir("/tmp/test_recursive/subdir");
    {
        const file2 = try std.fs.cwd().createFile("/tmp/test_recursive/subdir/file2.txt", .{});
        defer file2.close();
    }

    const entries = try listRecursive(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    // Should have: file1.txt, subdir, subdir/file2.txt
    try std.testing.expect(entries.len >= 3);
}

test "list sorted" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_sorted";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create files in non-alphabetical order
    {
        const file_c = try std.fs.cwd().createFile("/tmp/test_sorted/c.txt", .{});
        defer file_c.close();
        const file_a = try std.fs.cwd().createFile("/tmp/test_sorted/a.txt", .{});
        defer file_a.close();
        const file_b = try std.fs.cwd().createFile("/tmp/test_sorted/b.txt", .{});
        defer file_b.close();
    }

    const entries = try listSorted(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 3), entries.len);
    // Verify alphabetical order
    try std.testing.expectEqualStrings("a.txt", entries[0]);
    try std.testing.expectEqualStrings("b.txt", entries[1]);
    try std.testing.expectEqualStrings("c.txt", entries[2]);
}

// ANCHOR: advanced_listing
test "list with info" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_with_info";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create file with content
    {
        const file = try std.fs.cwd().createFile("/tmp/test_with_info/file.txt", .{});
        defer file.close();
        try file.writeAll("Hello, World!");
    }

    const entries = try listWithInfo(allocator, test_dir);
    defer {
        for (entries) |*entry| {
            entry.deinit(allocator);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 1), entries.len);
    try std.testing.expectEqualStrings("file.txt", entries[0].name);
    try std.testing.expect(entries[0].size > 0);
    try std.testing.expect(!entries[0].is_dir);
}

test "matches pattern" {
    try std.testing.expect(matchesPattern("test.txt", "*.txt"));
    try std.testing.expect(matchesPattern("readme.md", "readme.*"));
    try std.testing.expect(matchesPattern("test", "test"));
    try std.testing.expect(!matchesPattern("test.md", "*.txt"));
}

test "list by pattern" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_pattern";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_pattern/test1.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_pattern/test2.txt", .{});
        defer file2.close();
        const file3 = try std.fs.cwd().createFile("/tmp/test_pattern/readme.md", .{});
        defer file3.close();
    }

    const entries = try listByPattern(allocator, test_dir, "test*.txt");
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 2), entries.len);
}
```

### Advanced Listing

```zig
test "list with info" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_with_info";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create file with content
    {
        const file = try std.fs.cwd().createFile("/tmp/test_with_info/file.txt", .{});
        defer file.close();
        try file.writeAll("Hello, World!");
    }

    const entries = try listWithInfo(allocator, test_dir);
    defer {
        for (entries) |*entry| {
            entry.deinit(allocator);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 1), entries.len);
    try std.testing.expectEqualStrings("file.txt", entries[0].name);
    try std.testing.expect(entries[0].size > 0);
    try std.testing.expect(!entries[0].is_dir);
}

test "matches pattern" {
    try std.testing.expect(matchesPattern("test.txt", "*.txt"));
    try std.testing.expect(matchesPattern("readme.md", "readme.*"));
    try std.testing.expect(matchesPattern("test", "test"));
    try std.testing.expect(!matchesPattern("test.md", "*.txt"));
}

test "list by pattern" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_pattern";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_pattern/test1.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_pattern/test2.txt", .{});
        defer file2.close();
        const file3 = try std.fs.cwd().createFile("/tmp/test_pattern/readme.md", .{});
        defer file3.close();
    }

    const entries = try listByPattern(allocator, test_dir, "test*.txt");
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 2), entries.len);
}
// ANCHOR_END: filtered_listing

test "is hidden" {
    try std.testing.expect(isHidden(".hidden"));
    try std.testing.expect(isHidden("."));
    try std.testing.expect(!isHidden("visible"));
    try std.testing.expect(!isHidden(""));
}

test "list visible" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_visible";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create visible and hidden files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_visible/visible.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_visible/.hidden", .{});
        defer file2.close();
    }

    const entries = try listVisible(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 1), entries.len);
    try std.testing.expectEqualStrings("visible.txt", entries[0]);
}

test "list N entries" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_list_n";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create multiple files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_list_n/file1.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_list_n/file2.txt", .{});
        defer file2.close();
        const file3 = try std.fs.cwd().createFile("/tmp/test_list_n/file3.txt", .{});
        defer file3.close();
    }

    const entries = try listN(allocator, test_dir, 2);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 2), entries.len);
}

test "safe listing - not found" {
    const allocator = std.testing.allocator;

    const result = safeListing(allocator, "/tmp/does_not_exist_dir_12345");
    try std.testing.expectError(error.DirectoryNotFound, result);
}

test "safe listing - success" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_safe_list";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    {
        const file = try std.fs.cwd().createFile("/tmp/test_safe_list/file.txt", .{});
        defer file.close();
    }

    const entries = try safeListing(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 1), entries.len);
}

test "list nonexistent directory" {
    const allocator = std.testing.allocator;

    const result = listDirectory(allocator, "/tmp/does_not_exist_12345");
    try std.testing.expectError(error.FileNotFound, result);
}
```

### Discussion

### Basic Directory Iteration

The simplest way to list directory contents:

```zig
pub fn printDirectory(path: []const u8) !void {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        std.debug.print("{s}\n", .{entry.name});
    }
}
```

### Filtering by File Type

Separate files from directories:

```zig
pub const DirContents = struct {
    files: [][]const u8,
    directories: [][]const u8,

    pub fn deinit(self: *DirContents, allocator: std.mem.Allocator) void {
        for (self.files) |file| {
            allocator.free(file);
        }
        allocator.free(self.files);

        for (self.directories) |dir| {
            allocator.free(dir);
        }
        allocator.free(self.directories);
    }
};

pub fn listByType(allocator: std.mem.Allocator, path: []const u8) !DirContents {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var files = std.ArrayList([]const u8).init(allocator);
    errdefer files.deinit();

    var directories = std.ArrayList([]const u8).init(allocator);
    errdefer directories.deinit();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const name = try allocator.dupe(u8, entry.name);
        errdefer allocator.free(name);

        switch (entry.kind) {
            .file => try files.append(name),
            .directory => try directories.append(name),
            else => allocator.free(name), // Skip other types
        }
    }

    return DirContents{
        .files = try files.toOwnedSlice(),
        .directories = try directories.toOwnedSlice(),
    };
}
```

### Filtering by Extension

List only files with specific extension:

```zig
pub fn listByExtension(
    allocator: std.mem.Allocator,
    path: []const u8,
    ext: []const u8,
) ![][]const u8 {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList([]const u8).init(allocator);
    errdefer entries.deinit();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        if (entry.kind != .file) continue;

        const file_ext = std.fs.path.extension(entry.name);
        if (std.mem.eql(u8, file_ext, ext)) {
            const name = try allocator.dupe(u8, entry.name);
            try entries.append(name);
        }
    }

    return entries.toOwnedSlice();
}
```

### Recursive Directory Walking

Walk entire directory tree:

```zig
pub fn walkDirectory(
    allocator: std.mem.Allocator,
    path: []const u8,
    results: *std.ArrayList([]const u8),
) !void {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const full_path = try std.fs.path.join(allocator, &[_][]const u8{ path, entry.name });
        errdefer allocator.free(full_path);

        try results.append(full_path);

        if (entry.kind == .directory) {
            try walkDirectory(allocator, full_path, results);
        }
    }
}

pub fn listRecursive(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    var results = std.ArrayList([]const u8).init(allocator);
    errdefer results.deinit();

    try walkDirectory(allocator, path, &results);

    return results.toOwnedSlice();
}
```

### Sorting Directory Entries

Sort entries alphabetically:

```zig
pub fn listSorted(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    const entries = try listDirectory(allocator, path);
    errdefer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    std.mem.sort([]const u8, entries, {}, struct {
        fn lessThan(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.order(u8, a, b) == .lt;
        }
    }.lessThan);

    return entries;
}
```

### Getting File Information

Include size and modification time:

```zig
pub const FileInfo = struct {
    name: []const u8,
    size: u64,
    is_dir: bool,
    mtime: i128,

    pub fn deinit(self: *FileInfo, allocator: std.mem.Allocator) void {
        allocator.free(self.name);
    }
};

pub fn listWithInfo(allocator: std.mem.Allocator, path: []const u8) ![]FileInfo {
    var dir = try std.fs.cwd().openDir(path, .{});
    defer dir.close();

    var entries = std.ArrayList(FileInfo).init(allocator);
    errdefer entries.deinit();

    var iter = try dir.iterate();
    while (try iter.next()) |entry| {
        const stat = dir.statFile(entry.name) catch continue;

        try entries.append(.{
            .name = try allocator.dupe(u8, entry.name),
            .size = stat.size,
            .is_dir = entry.kind == .directory,
            .mtime = stat.mtime,
        });
    }

    return entries.toOwnedSlice();
}
```

### Pattern Matching

Filter using wildcard patterns:

```zig
pub fn matchesPattern(name: []const u8, pattern: []const u8) bool {
    if (std.mem.indexOf(u8, pattern, "*")) |star_pos| {
        const prefix = pattern[0..star_pos];
        const suffix = pattern[star_pos + 1 ..];

        if (!std.mem.startsWith(u8, name, prefix)) return false;
        if (!std.mem.endsWith(u8, name, suffix)) return false;

        return true;
    }

    return std.mem.eql(u8, name, pattern);
}

pub fn listByPattern(
    allocator: std.mem.Allocator,
    path: []const u8,
    pattern: []const u8,
) ![][]const u8 {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList([]const u8).init(allocator);
    errdefer entries.deinit();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        if (matchesPattern(entry.name, pattern)) {
            const name = try allocator.dupe(u8, entry.name);
            try entries.append(name);
        }
    }

    return entries.toOwnedSlice();
}
```

### Hidden Files

Handle hidden files (Unix-style):

```zig
pub fn isHidden(name: []const u8) bool {
    return name.len > 0 and name[0] == '.';
}

pub fn listVisible(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList([]const u8).init(allocator);
    errdefer entries.deinit();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        if (!isHidden(entry.name)) {
            const name = try allocator.dupe(u8, entry.name);
            try entries.append(name);
        }
    }

    return entries.toOwnedSlice();
}
```

### Limiting Results

Limit number of entries returned:

```zig
pub fn listN(allocator: std.mem.Allocator, path: []const u8, max_count: usize) ![][]const u8 {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList([]const u8).init(allocator);
    errdefer entries.deinit();

    var iter = dir.iterate();
    var count: usize = 0;
    while (try iter.next()) |entry| {
        if (count >= max_count) break;

        const name = try allocator.dupe(u8, entry.name);
        try entries.append(name);
        count += 1;
    }

    return entries.toOwnedSlice();
}
```

### Error Handling

Handle common directory errors:

```zig
pub fn safeListing(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    var dir = std.fs.cwd().openDir(path, .{ .iterate = true }) catch |err| switch (err) {
        error.FileNotFound => return error.DirectoryNotFound,
        error.NotDir => return error.NotADirectory,
        error.AccessDenied => return error.PermissionDenied,
        else => return err,
    };
    defer dir.close();

    var entries = std.ArrayList([]const u8).init(allocator);
    errdefer entries.deinit();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const name = try allocator.dupe(u8, entry.name);
        try entries.append(name);
    }

    return entries.toOwnedSlice();
}
```

### Performance Considerations

**Iterator vs. Reading All:**
- `iterate()` is memory-efficient for large directories
- Process entries one at a time
- Can stop early if needed

**Caching:**
```zig
// Cache directory listing
var cached_entries: ?[][]const u8 = null;

pub fn getCachedListing(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    if (cached_entries) |entries| {
        return entries;
    }

    cached_entries = try listDirectory(allocator, path);
    return cached_entries.?;
}
```

### Platform Differences

**Entry ordering:**
- Order is filesystem-dependent
- Not guaranteed to be alphabetical
- Sort explicitly if order matters

**Hidden files:**
- Unix: Start with `.`
- Windows: Have hidden attribute
- Use platform-specific checks for full support

### Related Functions

- `std.fs.Dir.iterate()` - Iterate directory entries
- `std.fs.Dir.walk()` - Recursive directory walker
- `std.fs.Dir.statFile()` - Get file metadata
- `std.fs.path.extension()` - Get file extension
- `std.fs.path.basename()` - Get filename without path
- `std.mem.sort()` - Sort entries

### Full Tested Code

```zig
const std = @import("std");

/// List all entries in a directory
pub fn listDirectory(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList([]const u8){};
    errdefer {
        for (entries.items) |item| {
            allocator.free(item);
        }
        entries.deinit(allocator);
    }

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const name = try allocator.dupe(u8, entry.name);
        try entries.append(allocator, name);
    }

    // toOwnedSlice transfers ownership of the internal buffer to the caller
    // Caller must free each string and then the slice itself
    return entries.toOwnedSlice(allocator);
}

/// Directory contents separated by type
pub const DirContents = struct {
    files: [][]const u8,
    directories: [][]const u8,

    /// Frees all allocated memory
    /// The slices were created by toOwnedSlice(), which transfers ownership of
    /// the internal ArrayList buffer to the caller. We must:
    /// 1. Free each individual string (allocated via dupe)
    /// 2. Free the slice itself (allocated by toOwnedSlice)
    pub fn deinit(self: *DirContents, allocator: std.mem.Allocator) void {
        // Free each file path string
        for (self.files) |file| {
            allocator.free(file);
        }
        // Free the files slice itself
        allocator.free(self.files);

        // Free each directory path string
        for (self.directories) |dir| {
            allocator.free(dir);
        }
        // Free the directories slice itself
        allocator.free(self.directories);
    }
};

/// List directory contents separated by type
pub fn listByType(allocator: std.mem.Allocator, path: []const u8) !DirContents {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var files = std.ArrayList([]const u8){};
    errdefer {
        for (files.items) |item| {
            allocator.free(item);
        }
        files.deinit(allocator);
    }

    var directories = std.ArrayList([]const u8){};
    errdefer {
        for (directories.items) |item| {
            allocator.free(item);
        }
        directories.deinit(allocator);
    }

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const name = try allocator.dupe(u8, entry.name);
        errdefer allocator.free(name);

        switch (entry.kind) {
            .file => try files.append(allocator, name),
            .directory => try directories.append(allocator, name),
            else => allocator.free(name),
        }
    }

    return DirContents{
        .files = try files.toOwnedSlice(allocator),
        .directories = try directories.toOwnedSlice(allocator),
    };
}

/// List files with specific extension
pub fn listByExtension(
    allocator: std.mem.Allocator,
    path: []const u8,
    ext: []const u8,
) ![][]const u8 {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList([]const u8){};
    errdefer {
        for (entries.items) |item| {
            allocator.free(item);
        }
        entries.deinit(allocator);
    }

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        if (entry.kind != .file) continue;

        const file_ext = std.fs.path.extension(entry.name);
        if (std.mem.eql(u8, file_ext, ext)) {
            const name = try allocator.dupe(u8, entry.name);
            try entries.append(allocator, name);
        }
    }

    return entries.toOwnedSlice(allocator);
}

/// Recursively walk directory tree
pub fn walkDirectory(
    allocator: std.mem.Allocator,
    path: []const u8,
    results: *std.ArrayList([]const u8),
) !void {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const full_path = try std.fs.path.join(allocator, &[_][]const u8{ path, entry.name });
        errdefer allocator.free(full_path);

        try results.append(allocator, full_path);

        if (entry.kind == .directory) {
            try walkDirectory(allocator, full_path, results);
        }
    }
}

/// List directory recursively
pub fn listRecursive(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    var results = std.ArrayList([]const u8){};
    errdefer {
        for (results.items) |item| {
            allocator.free(item);
        }
        results.deinit(allocator);
    }

    try walkDirectory(allocator, path, &results);

    return results.toOwnedSlice(allocator);
}

/// List directory entries in sorted order
pub fn listSorted(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    const entries = try listDirectory(allocator, path);
    errdefer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    std.mem.sort([]const u8, entries, {}, struct {
        fn lessThan(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.order(u8, a, b) == .lt;
        }
    }.lessThan);

    return entries;
}

/// File information entry
pub const FileInfo = struct {
    name: []const u8,
    size: u64,
    is_dir: bool,
    mtime: i128,

    /// Frees the allocated name string
    pub fn deinit(self: *FileInfo, allocator: std.mem.Allocator) void {
        allocator.free(self.name);
    }
};

/// List directory with file information
pub fn listWithInfo(allocator: std.mem.Allocator, path: []const u8) ![]FileInfo {
    var dir = try std.fs.cwd().openDir(path, .{});
    defer dir.close();

    var entries = std.ArrayList(FileInfo){};
    errdefer {
        for (entries.items) |*item| {
            allocator.free(item.name);
        }
        entries.deinit(allocator);
    }

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const stat = dir.statFile(entry.name) catch continue;

        const name = try allocator.dupe(u8, entry.name);
        errdefer allocator.free(name);

        try entries.append(allocator, .{
            .name = name,
            .size = stat.size,
            .is_dir = entry.kind == .directory,
            .mtime = stat.mtime,
        });
    }

    return entries.toOwnedSlice(allocator);
}

/// Check if name matches wildcard pattern
pub fn matchesPattern(name: []const u8, pattern: []const u8) bool {
    if (std.mem.indexOf(u8, pattern, "*")) |star_pos| {
        const prefix = pattern[0..star_pos];
        const suffix = pattern[star_pos + 1 ..];

        if (!std.mem.startsWith(u8, name, prefix)) return false;
        if (!std.mem.endsWith(u8, name, suffix)) return false;

        return true;
    }

    return std.mem.eql(u8, name, pattern);
}

/// List files matching pattern
pub fn listByPattern(
    allocator: std.mem.Allocator,
    path: []const u8,
    pattern: []const u8,
) ![][]const u8 {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList([]const u8){};
    errdefer {
        for (entries.items) |item| {
            allocator.free(item);
        }
        entries.deinit(allocator);
    }

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        if (matchesPattern(entry.name, pattern)) {
            const name = try allocator.dupe(u8, entry.name);
            try entries.append(allocator, name);
        }
    }

    return entries.toOwnedSlice(allocator);
}

/// Check if filename is hidden (Unix-style)
pub fn isHidden(name: []const u8) bool {
    return name.len > 0 and name[0] == '.';
}

/// List visible files (exclude hidden)
pub fn listVisible(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList([]const u8){};
    errdefer {
        for (entries.items) |item| {
            allocator.free(item);
        }
        entries.deinit(allocator);
    }

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        if (!isHidden(entry.name)) {
            const name = try allocator.dupe(u8, entry.name);
            try entries.append(allocator, name);
        }
    }

    return entries.toOwnedSlice(allocator);
}

/// List limited number of entries
pub fn listN(allocator: std.mem.Allocator, path: []const u8, max_count: usize) ![][]const u8 {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList([]const u8){};
    errdefer {
        for (entries.items) |item| {
            allocator.free(item);
        }
        entries.deinit(allocator);
    }

    var iter = dir.iterate();
    var count: usize = 0;
    while (try iter.next()) |entry| {
        if (count >= max_count) break;

        const name = try allocator.dupe(u8, entry.name);
        try entries.append(allocator, name);
        count += 1;
    }

    return entries.toOwnedSlice(allocator);
}

/// List directory with safe error handling
pub fn safeListing(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    var dir = std.fs.cwd().openDir(path, .{ .iterate = true }) catch |err| switch (err) {
        error.FileNotFound => return error.DirectoryNotFound,
        error.NotDir => return error.NotADirectory,
        error.AccessDenied => return error.PermissionDenied,
        else => return err,
    };
    defer dir.close();

    var entries = std.ArrayList([]const u8){};
    errdefer {
        for (entries.items) |item| {
            allocator.free(item);
        }
        entries.deinit(allocator);
    }

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const name = try allocator.dupe(u8, entry.name);
        try entries.append(allocator, name);
    }

    return entries.toOwnedSlice(allocator);
}

// Tests

// ANCHOR: basic_listing
test "list directory" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_list_dir";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create test files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_list_dir/file1.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_list_dir/file2.txt", .{});
        defer file2.close();
    }

    // List directory
    const entries = try listDirectory(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 2), entries.len);
}

test "list empty directory" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_empty_dir";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    const entries = try listDirectory(allocator, test_dir);
    defer allocator.free(entries);

    try std.testing.expectEqual(@as(usize, 0), entries.len);
}

test "list by type" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_by_type";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create files and subdirectory
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_by_type/file1.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_by_type/file2.txt", .{});
        defer file2.close();
    }
    try std.fs.cwd().makeDir("/tmp/test_by_type/subdir");

    var contents = try listByType(allocator, test_dir);
    defer contents.deinit(allocator);

    try std.testing.expectEqual(@as(usize, 2), contents.files.len);
    try std.testing.expectEqual(@as(usize, 1), contents.directories.len);
}
// ANCHOR_END: basic_listing

test "list by extension" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_by_ext";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create files with different extensions
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_by_ext/file1.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_by_ext/file2.txt", .{});
        defer file2.close();
        const file3 = try std.fs.cwd().createFile("/tmp/test_by_ext/file3.md", .{});
        defer file3.close();
    }

    const entries = try listByExtension(allocator, test_dir, ".txt");
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 2), entries.len);
}

// ANCHOR: filtered_listing
test "list recursive" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_recursive";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create nested structure
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_recursive/file1.txt", .{});
        defer file1.close();
    }
    try std.fs.cwd().makeDir("/tmp/test_recursive/subdir");
    {
        const file2 = try std.fs.cwd().createFile("/tmp/test_recursive/subdir/file2.txt", .{});
        defer file2.close();
    }

    const entries = try listRecursive(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    // Should have: file1.txt, subdir, subdir/file2.txt
    try std.testing.expect(entries.len >= 3);
}

test "list sorted" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_sorted";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create files in non-alphabetical order
    {
        const file_c = try std.fs.cwd().createFile("/tmp/test_sorted/c.txt", .{});
        defer file_c.close();
        const file_a = try std.fs.cwd().createFile("/tmp/test_sorted/a.txt", .{});
        defer file_a.close();
        const file_b = try std.fs.cwd().createFile("/tmp/test_sorted/b.txt", .{});
        defer file_b.close();
    }

    const entries = try listSorted(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 3), entries.len);
    // Verify alphabetical order
    try std.testing.expectEqualStrings("a.txt", entries[0]);
    try std.testing.expectEqualStrings("b.txt", entries[1]);
    try std.testing.expectEqualStrings("c.txt", entries[2]);
}

// ANCHOR: advanced_listing
test "list with info" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_with_info";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create file with content
    {
        const file = try std.fs.cwd().createFile("/tmp/test_with_info/file.txt", .{});
        defer file.close();
        try file.writeAll("Hello, World!");
    }

    const entries = try listWithInfo(allocator, test_dir);
    defer {
        for (entries) |*entry| {
            entry.deinit(allocator);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 1), entries.len);
    try std.testing.expectEqualStrings("file.txt", entries[0].name);
    try std.testing.expect(entries[0].size > 0);
    try std.testing.expect(!entries[0].is_dir);
}

test "matches pattern" {
    try std.testing.expect(matchesPattern("test.txt", "*.txt"));
    try std.testing.expect(matchesPattern("readme.md", "readme.*"));
    try std.testing.expect(matchesPattern("test", "test"));
    try std.testing.expect(!matchesPattern("test.md", "*.txt"));
}

test "list by pattern" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_pattern";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_pattern/test1.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_pattern/test2.txt", .{});
        defer file2.close();
        const file3 = try std.fs.cwd().createFile("/tmp/test_pattern/readme.md", .{});
        defer file3.close();
    }

    const entries = try listByPattern(allocator, test_dir, "test*.txt");
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 2), entries.len);
}
// ANCHOR_END: filtered_listing

test "is hidden" {
    try std.testing.expect(isHidden(".hidden"));
    try std.testing.expect(isHidden("."));
    try std.testing.expect(!isHidden("visible"));
    try std.testing.expect(!isHidden(""));
}

test "list visible" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_visible";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create visible and hidden files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_visible/visible.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_visible/.hidden", .{});
        defer file2.close();
    }

    const entries = try listVisible(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 1), entries.len);
    try std.testing.expectEqualStrings("visible.txt", entries[0]);
}

test "list N entries" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_list_n";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create multiple files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_list_n/file1.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_list_n/file2.txt", .{});
        defer file2.close();
        const file3 = try std.fs.cwd().createFile("/tmp/test_list_n/file3.txt", .{});
        defer file3.close();
    }

    const entries = try listN(allocator, test_dir, 2);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 2), entries.len);
}

test "safe listing - not found" {
    const allocator = std.testing.allocator;

    const result = safeListing(allocator, "/tmp/does_not_exist_dir_12345");
    try std.testing.expectError(error.DirectoryNotFound, result);
}

test "safe listing - success" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_safe_list";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    {
        const file = try std.fs.cwd().createFile("/tmp/test_safe_list/file.txt", .{});
        defer file.close();
    }

    const entries = try safeListing(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 1), entries.len);
}

test "list nonexistent directory" {
    const allocator = std.testing.allocator;

    const result = listDirectory(allocator, "/tmp/does_not_exist_12345");
    try std.testing.expectError(error.FileNotFound, result);
}
// ANCHOR_END: advanced_listing
```

---

## Recipe 5.14: Bypassing Filename Encoding {#recipe-5-14}

**Tags:** allocators, arraylist, data-structures, error-handling, files-io, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_14.zig`

### Problem

You need to work with filenames that may contain invalid UTF-8 sequences or operate at the raw OS path level without encoding assumptions.

### Solution

### Raw Byte Handling

```zig
test "list raw filenames" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_raw_list";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    {
        const file = try std.fs.cwd().createFile("/tmp/test_raw_list/normal.txt", .{});
        defer file.close();
    }

    const entries = try listRawFilenames(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expect(entries.len > 0);
}

test "open raw path" {
    const test_path = "/tmp/test_raw_open.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
    }

    // Open using raw path
    const file = try openRawPath(test_path);
    defer file.close();

    const stat = try file.stat();
    try std.testing.expect(stat.kind == .file);
}

test "paths equal" {
    try std.testing.expect(pathsEqual("/tmp/test", "/tmp/test"));
    try std.testing.expect(!pathsEqual("/tmp/test", "/tmp/Test"));
    try std.testing.expect(!pathsEqual("/tmp/test", "/tmp/test2"));
}

test "path starts with" {
    try std.testing.expect(pathStartsWith("/tmp/test/file.txt", "/tmp/test"));
    try std.testing.expect(pathStartsWith("/tmp/test", "/tmp"));
    try std.testing.expect(!pathStartsWith("/tmp/test", "/var"));
}

test "valid UTF-8 path" {
    try std.testing.expect(isValidUtf8Path("/tmp/test.txt"));
    try std.testing.expect(isValidUtf8Path("/tmp/テスト.txt"));

    // Invalid UTF-8
    const invalid = [_]u8{ '/', 't', 'm', 'p', '/', 0xFF, 0xFE };
    try std.testing.expect(!isValidUtf8Path(&invalid));
}
```

### Sanitize Paths

```zig
test "sanitize path" {
    const allocator = std.testing.allocator;

    // Valid UTF-8
    const valid = try sanitizePath(allocator, "/tmp/test.txt");
    defer allocator.free(valid);
    try std.testing.expectEqualStrings("/tmp/test.txt", valid);

    // Invalid UTF-8 - contains replacement character
    const invalid = [_]u8{ '/', 't', 'm', 'p', '/', 0xFF };
    const sanitized = try sanitizePath(allocator, &invalid);
    defer allocator.free(sanitized);
    try std.testing.expect(sanitized.len > 5);
}

test "list with encoding" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_encoding";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create test files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_encoding/normal.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_encoding/test2.txt", .{});
        defer file2.close();
    }

    const entries = try listWithEncoding(allocator, test_dir);
    defer {
        for (entries) |*entry| {
            var mut_entry = entry;
            mut_entry.deinit(allocator);
        }
        allocator.free(entries);
    }

    try std.testing.expect(entries.len > 0);
    for (entries) |entry| {
        try std.testing.expect(entry.is_valid_utf8);
    }
}

test "create file raw" {
    const dir_path = "/tmp/test_raw_create";
    try std.fs.cwd().makeDir(dir_path);
    defer std.fs.cwd().deleteTree(dir_path) catch {};

    const filename = "test.txt";
    const file = try createFileRaw(dir_path, filename);
    file.close();

    // Verify file exists
    var dir = try std.fs.cwd().openDir(dir_path, .{});
    defer dir.close();

    const stat = try dir.statFile(filename);
    try std.testing.expect(stat.kind == .file);
}
```

### Path Normalization

```zig
test "normalize path" {
    const allocator = std.testing.allocator;

    const result1 = try normalizePath(allocator, "/tmp/./test/../file.txt");
    defer allocator.free(result1);
    try std.testing.expectEqualStrings("/tmp/file.txt", result1);

    const result2 = try normalizePath(allocator, "/tmp//test/./file.txt");
    defer allocator.free(result2);
    try std.testing.expectEqualStrings("/tmp/test/file.txt", result2);

    const result3 = try normalizePath(allocator, "/tmp/test/..");
    defer allocator.free(result3);
    try std.testing.expectEqualStrings("/tmp", result3);

    const result4 = try normalizePath(allocator, "/");
    defer allocator.free(result4);
    try std.testing.expectEqualStrings("/", result4);
}

test "escape path normal" {
    const allocator = std.testing.allocator;

    const normal = try escapePath(allocator, "/tmp/test.txt");
    defer allocator.free(normal);
    try std.testing.expectEqualStrings("/tmp/test.txt", normal);
}

test "escape path with special chars" {
    const allocator = std.testing.allocator;

    const with_newline = try escapePath(allocator, "/tmp/test\nfile.txt");
    defer allocator.free(with_newline);
    try std.testing.expect(std.mem.indexOf(u8, with_newline, "\\x0A") != null);

    const with_tab = try escapePath(allocator, "/tmp/test\tfile.txt");
    defer allocator.free(with_tab);
    try std.testing.expect(std.mem.indexOf(u8, with_tab, "\\x09") != null);
}

test "safe open raw - not found" {
    const result = safeOpenRaw("/tmp/does_not_exist_12345.txt");
    try std.testing.expectError(error.PathNotFound, result);
}

test "safe open raw - success" {
    const test_path = "/tmp/test_safe_open.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
    }

    // Open safely
    const file = try safeOpenRaw(test_path);
    defer file.close();

    const stat = try file.stat();
    try std.testing.expect(stat.kind == .file);
}

test "empty path handling" {
    const allocator = std.testing.allocator;

    const result = try normalizePath(allocator, "");
    defer allocator.free(result);
    try std.testing.expectEqualStrings("/", result);

    try std.testing.expect(pathsEqual("", ""));
    // Empty prefix matches any string
    try std.testing.expect(pathStartsWith("/tmp", ""));
}

test "path with only dots" {
    const allocator = std.testing.allocator;

    const result1 = try normalizePath(allocator, "/././.");
    defer allocator.free(result1);
    try std.testing.expectEqualStrings("/", result1);

    const result2 = try normalizePath(allocator, "/tmp/./././");
    defer allocator.free(result2);
    try std.testing.expectEqualStrings("/tmp", result2);
}
```

### Discussion

### Understanding Zig Path Handling

Zig treats paths as byte slices without encoding assumptions:

```zig
// Paths are just []const u8 - no UTF-8 requirement
pub fn openRawPath(path: []const u8) !std.fs.File {
    // Direct byte-level access, no validation
    return std.fs.cwd().openFile(path, .{});
}
```

This differs from languages that require UTF-8 validation for strings.

### Working with OS-Native Paths

Access platform-specific path representations:

```zig
pub fn getOSPath(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    const builtin = @import("builtin");

    if (builtin.os.tag == .windows) {
        // Windows uses UTF-16
        const wide_len = try std.os.windows.sliceToPrefixedFileW(null, path);
        var wide_path = try allocator.alloc(u16, wide_len);
        errdefer allocator.free(wide_path);

        _ = try std.os.windows.sliceToPrefixedFileW(wide_path, path);
        return std.mem.sliceAsBytes(wide_path);
    } else {
        // Unix uses raw bytes
        return allocator.dupe(u8, path);
    }
}
```

### Comparing Byte-Level Paths

Compare paths without encoding concerns:

```zig
pub fn pathsEqual(path1: []const u8, path2: []const u8) bool {
    // Direct byte comparison
    return std.mem.eql(u8, path1, path2);
}

pub fn pathStartsWith(path: []const u8, prefix: []const u8) bool {
    return std.mem.startsWith(u8, path, prefix);
}

test "path comparison" {
    try std.testing.expect(pathsEqual("/tmp/test", "/tmp/test"));
    try std.testing.expect(!pathsEqual("/tmp/test", "/tmp/Test"));

    try std.testing.expect(pathStartsWith("/tmp/test/file.txt", "/tmp/test"));
}
```

### Handling Invalid UTF-8

Detect and handle potentially invalid UTF-8 in filenames:

```zig
pub fn isValidUtf8Path(path: []const u8) bool {
    return std.unicode.utf8ValidateSlice(path);
}

pub fn sanitizePath(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    if (std.unicode.utf8ValidateSlice(path)) {
        return allocator.dupe(u8, path);
    }

    // Replace invalid sequences with replacement character
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i < path.len) {
        const len = std.unicode.utf8ByteSequenceLength(path[i]) catch {
            // Invalid UTF-8, use replacement character
            try result.appendSlice(allocator, "\u{FFFD}");
            i += 1;
            continue;
        };

        if (i + len > path.len) {
            // Incomplete sequence
            try result.appendSlice(allocator, "\u{FFFD}");
            break;
        }

        try result.appendSlice(allocator, path[i .. i + len]);
        i += len;
    }

    return result.toOwnedSlice(allocator);
}

test "invalid UTF-8 detection" {
    try std.testing.expect(isValidUtf8Path("/tmp/test.txt"));

    // Invalid UTF-8 byte sequence
    const invalid = [_]u8{ '/'.try std.testing.expect(!isValidUtf8Path(&invalid));
}
```

### Converting Between Encodings

Handle path encoding conversions:

```zig
pub fn pathToUtf8(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    const builtin = @import("builtin");

    if (builtin.os.tag == .windows) {
        // Assume input is UTF-16 on Windows
        const wide_path = std.mem.bytesAsSlice(u16, path);
        return std.unicode.utf16LeToUtf8Alloc(allocator, wide_path);
    } else {
        // Unix paths are already bytes
        return allocator.dupe(u8, path);
    }
}
```

### Reading Directory with Encoding Issues

Handle directories that may contain problematic filenames:

```zig
pub const PathEntry = struct {
    raw_bytes: []const u8,
    is_valid_utf8: bool,
    display_name: []const u8,

    pub fn deinit(self: *PathEntry, allocator: std.mem.Allocator) void {
        allocator.free(self.raw_bytes);
        if (!self.is_valid_utf8) {
            allocator.free(self.display_name);
        }
    }
};

pub fn listWithEncoding(allocator: std.mem.Allocator, path: []const u8) ![]PathEntry {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList(PathEntry){};
    errdefer entries.deinit(allocator);

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const raw = try allocator.dupe(u8, entry.name);
        errdefer allocator.free(raw);

        const is_valid = std.unicode.utf8ValidateSlice(raw);
        const display = if (is_valid)
            raw
        else
            try sanitizePath(allocator, raw);

        try entries.append(allocator, .{
            .raw_bytes = raw,
            .is_valid_utf8 = is_valid,
            .display_name = display,
        });
    }

    return entries.toOwnedSlice(allocator);
}
```

### Creating Files with Raw Names

Create files using raw byte sequences:

```zig
pub fn createFileRaw(dir_path: []const u8, filename: []const u8) !std.fs.File {
    var dir = try std.fs.cwd().openDir(dir_path, .{});
    defer dir.close();

    // No encoding validation - direct byte-level operation
    return dir.createFile(filename, .{});
}

test "create file raw" {
    const dir_path = "/tmp/test_raw_create";
    try std.fs.cwd().makeDir(dir_path);
    defer std.fs.cwd().deleteTree(dir_path) catch {};

    const filename = "test.txt";
    const file = try createFileRaw(dir_path, filename);
    file.close();

    // Verify file exists using raw bytes
    var dir = try std.fs.cwd().openDir(dir_path, .{});
    defer dir.close();

    const stat = try dir.statFile(filename);
    try std.testing.expect(stat.kind == .file);
}
```

### Path Normalization

Normalize paths while preserving raw bytes:

```zig
pub fn normalizePath(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    // Resolve relative components without encoding assumptions
    var components = std.ArrayList([]const u8){};
    defer components.deinit(allocator);

    var iter = std.mem.splitScalar(u8, path, '/');
    while (iter.next()) |component| {
        if (component.len == 0 or std.mem.eql(u8, component, ".")) {
            continue;
        }

        if (std.mem.eql(u8, component, "..")) {
            if (components.items.len > 0) {
                _ = components.pop();
            }
        } else {
            try components.append(allocator, component);
        }
    }

    // Rebuild path
    if (components.items.len == 0) {
        return allocator.dupe(u8, "/");
    }

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (components.items) |component| {
        try result.append(allocator, '/');
        try result.appendSlice(allocator, component);
    }

    return result.toOwnedSlice(allocator);
}

test "normalize path" {
    const allocator = std.testing.allocator;

    const result1 = try normalizePath(allocator, "/tmp/./test/../file.txt");
    defer allocator.free(result1);
    try std.testing.expectEqualStrings("/tmp/file.txt", result1);

    const result2 = try normalizePath(allocator, "/tmp//test/./file.txt");
    defer allocator.free(result2);
    try std.testing.expectEqualStrings("/tmp/test/file.txt", result2);
}
```

### Hexadecimal Escaping

Display problematic filenames using hex escaping:

```zig
pub fn escapePath(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (path) |byte| {
        if (byte >= 32 and byte < 127 and byte != '\\') {
            try result.append(allocator, byte);
        } else {
            const hex = try std.fmt.allocPrint(allocator, "\\x{X:0>2}", .{byte});
            defer allocator.free(hex);
            try result.appendSlice(allocator, hex);
        }
    }

    return result.toOwnedSlice(allocator);
}

test "escape path" {
    const allocator = std.testing.allocator;

    const normal = try escapePath(allocator, "/tmp/test.txt");
    defer allocator.free(normal);
    try std.testing.expectEqualStrings("/tmp/test.txt", normal);

    const with_newline = try escapePath(allocator, "/tmp/test\nfile.txt");
    defer allocator.free(with_newline);
    try std.testing.expect(std.mem.indexOf(u8, with_newline, "\\x0A") != null);
}
```

### Platform Differences

**Unix/Linux:**
- Paths are arbitrary byte sequences
- Only `/` and NUL are special
- No encoding requirements
- Case-sensitive

**Windows:**
- Native APIs use UTF-16
- Zig converts to/from UTF-8
- Path separators: `\` and `/`
- Case-insensitive (usually)
- Additional restrictions (reserved names, etc.)

**Cross-platform handling:**
```zig
pub fn openFileAnyEncoding(path: []const u8) !std.fs.File {
    const builtin = @import("builtin");

    if (builtin.os.tag == .windows) {
        // Windows path handling with UTF-16 conversion
        return std.fs.cwd().openFile(path, .{});
    } else {
        // Unix direct byte access
        return std.fs.cwd().openFile(path, .{});
    }
}
```

### Best Practices

**Working with raw paths:**
- Store paths as `[]const u8` without assumptions
- Validate UTF-8 only when needed for display
- Use byte-level comparison for path matching
- Handle platform differences explicitly

**Error handling:**
```zig
pub fn safeOpenRaw(path: []const u8) !std.fs.File {
    return std.fs.cwd().openFile(path, .{}) catch |err| switch (err) {
        error.FileNotFound => return error.PathNotFound,
        error.InvalidUtf8 => return error.EncodingError,
        else => return err,
    };
}
```

### Related Functions

- `std.unicode.utf8ValidateSlice()` - Validate UTF-8
- `std.unicode.utf8ByteSequenceLength()` - Get UTF-8 byte length
- `std.unicode.utf16LeToUtf8Alloc()` - Convert UTF-16 to UTF-8
- `std.mem.eql()` - Byte-level comparison
- `std.fs.path` - Path manipulation utilities
- `std.os.windows.sliceToPrefixedFileW()` - Windows UTF-16 conversion

### Full Tested Code

```zig
const std = @import("std");

/// List filenames as raw bytes without encoding validation
pub fn listRawFilenames(allocator: std.mem.Allocator, path: []const u8) ![][]const u8 {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList([]const u8){};
    errdefer entries.deinit(allocator);

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const name = try allocator.dupe(u8, entry.name);
        try entries.append(allocator, name);
    }

    return entries.toOwnedSlice(allocator);
}

/// Open file using raw byte path
pub fn openRawPath(path: []const u8) !std.fs.File {
    return std.fs.cwd().openFile(path, .{});
}

/// Compare paths at byte level
pub fn pathsEqual(path1: []const u8, path2: []const u8) bool {
    return std.mem.eql(u8, path1, path2);
}

/// Check if path starts with prefix
pub fn pathStartsWith(path: []const u8, prefix: []const u8) bool {
    return std.mem.startsWith(u8, path, prefix);
}

/// Check if path is valid UTF-8
pub fn isValidUtf8Path(path: []const u8) bool {
    return std.unicode.utf8ValidateSlice(path);
}

/// Sanitize path by replacing invalid UTF-8 sequences
pub fn sanitizePath(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    if (std.unicode.utf8ValidateSlice(path)) {
        return allocator.dupe(u8, path);
    }

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i < path.len) {
        const len = std.unicode.utf8ByteSequenceLength(path[i]) catch {
            // Invalid UTF-8, use replacement character
            try result.appendSlice(allocator, "\u{FFFD}");
            i += 1;
            continue;
        };

        if (i + len > path.len) {
            // Incomplete sequence
            try result.appendSlice(allocator, "\u{FFFD}");
            break;
        }

        try result.appendSlice(allocator, path[i .. i + len]);
        i += len;
    }

    return result.toOwnedSlice(allocator);
}

/// Path entry with encoding information
pub const PathEntry = struct {
    raw_bytes: []const u8,
    is_valid_utf8: bool,
    display_name: []const u8,

    pub fn deinit(self: *PathEntry, allocator: std.mem.Allocator) void {
        allocator.free(self.raw_bytes);
        if (!self.is_valid_utf8) {
            allocator.free(self.display_name);
        }
    }
};

/// List directory entries with encoding information
pub fn listWithEncoding(allocator: std.mem.Allocator, path: []const u8) ![]PathEntry {
    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var entries = std.ArrayList(PathEntry){};
    errdefer entries.deinit(allocator);

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const raw = try allocator.dupe(u8, entry.name);
        errdefer allocator.free(raw);

        const is_valid = std.unicode.utf8ValidateSlice(raw);
        const display = if (is_valid)
            raw
        else
            try sanitizePath(allocator, raw);

        try entries.append(allocator, .{
            .raw_bytes = raw,
            .is_valid_utf8 = is_valid,
            .display_name = display,
        });
    }

    return entries.toOwnedSlice(allocator);
}

/// Create file using raw byte filename
pub fn createFileRaw(dir_path: []const u8, filename: []const u8) !std.fs.File {
    var dir = try std.fs.cwd().openDir(dir_path, .{});
    defer dir.close();

    return dir.createFile(filename, .{});
}

/// Normalize path without encoding assumptions
pub fn normalizePath(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    var components = std.ArrayList([]const u8){};
    defer components.deinit(allocator);

    var iter = std.mem.splitScalar(u8, path, '/');
    while (iter.next()) |component| {
        if (component.len == 0 or std.mem.eql(u8, component, ".")) {
            continue;
        }

        if (std.mem.eql(u8, component, "..")) {
            if (components.items.len > 0) {
                _ = components.pop();
            }
        } else {
            try components.append(allocator, component);
        }
    }

    if (components.items.len == 0) {
        return allocator.dupe(u8, "/");
    }

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (components.items) |component| {
        try result.append(allocator, '/');
        try result.appendSlice(allocator, component);
    }

    return result.toOwnedSlice(allocator);
}

/// Escape path for display using hex escaping
pub fn escapePath(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (path) |byte| {
        if (byte >= 32 and byte < 127 and byte != '\\') {
            try result.append(allocator, byte);
        } else {
            const hex = try std.fmt.allocPrint(allocator, "\\x{X:0>2}", .{byte});
            defer allocator.free(hex);
            try result.appendSlice(allocator, hex);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Safe open with detailed error handling
pub fn safeOpenRaw(path: []const u8) !std.fs.File {
    return std.fs.cwd().openFile(path, .{}) catch |err| switch (err) {
        error.FileNotFound => return error.PathNotFound,
        else => return err,
    };
}

// Tests

// ANCHOR: raw_byte_handling
test "list raw filenames" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_raw_list";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    {
        const file = try std.fs.cwd().createFile("/tmp/test_raw_list/normal.txt", .{});
        defer file.close();
    }

    const entries = try listRawFilenames(allocator, test_dir);
    defer {
        for (entries) |entry| {
            allocator.free(entry);
        }
        allocator.free(entries);
    }

    try std.testing.expect(entries.len > 0);
}

test "open raw path" {
    const test_path = "/tmp/test_raw_open.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
    }

    // Open using raw path
    const file = try openRawPath(test_path);
    defer file.close();

    const stat = try file.stat();
    try std.testing.expect(stat.kind == .file);
}

test "paths equal" {
    try std.testing.expect(pathsEqual("/tmp/test", "/tmp/test"));
    try std.testing.expect(!pathsEqual("/tmp/test", "/tmp/Test"));
    try std.testing.expect(!pathsEqual("/tmp/test", "/tmp/test2"));
}

test "path starts with" {
    try std.testing.expect(pathStartsWith("/tmp/test/file.txt", "/tmp/test"));
    try std.testing.expect(pathStartsWith("/tmp/test", "/tmp"));
    try std.testing.expect(!pathStartsWith("/tmp/test", "/var"));
}

test "valid UTF-8 path" {
    try std.testing.expect(isValidUtf8Path("/tmp/test.txt"));
    try std.testing.expect(isValidUtf8Path("/tmp/テスト.txt"));

    // Invalid UTF-8
    const invalid = [_]u8{ '/', 't', 'm', 'p', '/', 0xFF, 0xFE };
    try std.testing.expect(!isValidUtf8Path(&invalid));
}
// ANCHOR_END: raw_byte_handling

// ANCHOR: sanitize_paths
test "sanitize path" {
    const allocator = std.testing.allocator;

    // Valid UTF-8
    const valid = try sanitizePath(allocator, "/tmp/test.txt");
    defer allocator.free(valid);
    try std.testing.expectEqualStrings("/tmp/test.txt", valid);

    // Invalid UTF-8 - contains replacement character
    const invalid = [_]u8{ '/', 't', 'm', 'p', '/', 0xFF };
    const sanitized = try sanitizePath(allocator, &invalid);
    defer allocator.free(sanitized);
    try std.testing.expect(sanitized.len > 5);
}

test "list with encoding" {
    const allocator = std.testing.allocator;

    const test_dir = "/tmp/test_encoding";
    try std.fs.cwd().makeDir(test_dir);
    defer std.fs.cwd().deleteTree(test_dir) catch {};

    // Create test files
    {
        const file1 = try std.fs.cwd().createFile("/tmp/test_encoding/normal.txt", .{});
        defer file1.close();
        const file2 = try std.fs.cwd().createFile("/tmp/test_encoding/test2.txt", .{});
        defer file2.close();
    }

    const entries = try listWithEncoding(allocator, test_dir);
    defer {
        for (entries) |*entry| {
            var mut_entry = entry;
            mut_entry.deinit(allocator);
        }
        allocator.free(entries);
    }

    try std.testing.expect(entries.len > 0);
    for (entries) |entry| {
        try std.testing.expect(entry.is_valid_utf8);
    }
}

test "create file raw" {
    const dir_path = "/tmp/test_raw_create";
    try std.fs.cwd().makeDir(dir_path);
    defer std.fs.cwd().deleteTree(dir_path) catch {};

    const filename = "test.txt";
    const file = try createFileRaw(dir_path, filename);
    file.close();

    // Verify file exists
    var dir = try std.fs.cwd().openDir(dir_path, .{});
    defer dir.close();

    const stat = try dir.statFile(filename);
    try std.testing.expect(stat.kind == .file);
}
// ANCHOR_END: sanitize_paths

// ANCHOR: path_normalization
test "normalize path" {
    const allocator = std.testing.allocator;

    const result1 = try normalizePath(allocator, "/tmp/./test/../file.txt");
    defer allocator.free(result1);
    try std.testing.expectEqualStrings("/tmp/file.txt", result1);

    const result2 = try normalizePath(allocator, "/tmp//test/./file.txt");
    defer allocator.free(result2);
    try std.testing.expectEqualStrings("/tmp/test/file.txt", result2);

    const result3 = try normalizePath(allocator, "/tmp/test/..");
    defer allocator.free(result3);
    try std.testing.expectEqualStrings("/tmp", result3);

    const result4 = try normalizePath(allocator, "/");
    defer allocator.free(result4);
    try std.testing.expectEqualStrings("/", result4);
}

test "escape path normal" {
    const allocator = std.testing.allocator;

    const normal = try escapePath(allocator, "/tmp/test.txt");
    defer allocator.free(normal);
    try std.testing.expectEqualStrings("/tmp/test.txt", normal);
}

test "escape path with special chars" {
    const allocator = std.testing.allocator;

    const with_newline = try escapePath(allocator, "/tmp/test\nfile.txt");
    defer allocator.free(with_newline);
    try std.testing.expect(std.mem.indexOf(u8, with_newline, "\\x0A") != null);

    const with_tab = try escapePath(allocator, "/tmp/test\tfile.txt");
    defer allocator.free(with_tab);
    try std.testing.expect(std.mem.indexOf(u8, with_tab, "\\x09") != null);
}

test "safe open raw - not found" {
    const result = safeOpenRaw("/tmp/does_not_exist_12345.txt");
    try std.testing.expectError(error.PathNotFound, result);
}

test "safe open raw - success" {
    const test_path = "/tmp/test_safe_open.txt";
    defer std.fs.cwd().deleteFile(test_path) catch {};

    // Create file
    {
        const file = try std.fs.cwd().createFile(test_path, .{});
        defer file.close();
    }

    // Open safely
    const file = try safeOpenRaw(test_path);
    defer file.close();

    const stat = try file.stat();
    try std.testing.expect(stat.kind == .file);
}

test "empty path handling" {
    const allocator = std.testing.allocator;

    const result = try normalizePath(allocator, "");
    defer allocator.free(result);
    try std.testing.expectEqualStrings("/", result);

    try std.testing.expect(pathsEqual("", ""));
    // Empty prefix matches any string
    try std.testing.expect(pathStartsWith("/tmp", ""));
}

test "path with only dots" {
    const allocator = std.testing.allocator;

    const result1 = try normalizePath(allocator, "/././.");
    defer allocator.free(result1);
    try std.testing.expectEqualStrings("/", result1);

    const result2 = try normalizePath(allocator, "/tmp/./././");
    defer allocator.free(result2);
    try std.testing.expectEqualStrings("/tmp", result2);
}
// ANCHOR_END: path_normalization
```

---

## Recipe 5.15: Printing Bad Filenames {#recipe-5-15}

**Tags:** allocators, arraylist, data-structures, error-handling, files-io, json, memory, parsing, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/02-core/05-files-io/recipe_5_15.zig`

### Problem

You need to print or display filenames that may contain invalid UTF-8, control characters, or other problematic sequences.

### Solution

### Safe Printing

```zig
test "print safe filename - valid" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printSafeFilename(writer, "normal.txt");
    try std.testing.expectEqualStrings("normal.txt", buffer.items);
}

test "print safe filename - with null byte" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    const bad_name = [_]u8{ 'b', 'a', 'd', 0x00, 'n', 'a', 'm', 'e' };
    try printSafeFilename(writer, &bad_name);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\x00") != null);
}

test "print to terminal" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printToTerminal(writer, "test.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "test.txt") != null);

    buffer.clearRetainingCapacity();

    try printToTerminal(writer, "test\nfile.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\n") != null);
}

test "print with replacement" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printWithReplacement(writer, "test.txt");
    try std.testing.expectEqualStrings("test.txt", buffer.items);

    buffer.clearRetainingCapacity();

    const invalid = [_]u8{ 't', 'e', 's', 't', 0xFF, '.', 't', 'x', 't' };
    try printWithReplacement(writer, &invalid);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\u{FFFD}") != null);
}
```

### Special Formatting

```zig
test "print truncated - long name" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printTruncated(writer, "very_long_filename_that_should_be_truncated.txt", 20);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "...") != null);
}

test "color codes" {
    try std.testing.expectEqualStrings("\x1b[31m", Color.red.code());
    try std.testing.expectEqualStrings("\x1b[32m", Color.green.code());
    try std.testing.expectEqualStrings("\x1b[34m", Color.blue.code());
    try std.testing.expectEqualStrings("\x1b[33m", Color.yellow.code());
    try std.testing.expectEqualStrings("\x1b[0m", Color.reset.code());
}

test "print colored" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printColored(writer, "test.txt", .green);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[32m") != null);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "test.txt") != null);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[0m") != null);
}

test "print verbose without bytes" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printVerbose(writer, "test.txt", false);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "test.txt") != null);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "[bytes:") == null);
}

test "print verbose with bytes" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printVerbose(writer, "test.txt", true);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "test.txt") != null);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "[bytes:") != null);
}

test "print verbose with invalid UTF-8" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    const invalid = [_]u8{ 't', 'e', 's', 't', 0xFF };
    try printVerbose(writer, &invalid, false);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "(invalid UTF-8)") != null);
}

test "print comparison - identical" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printComparison(writer, "test.txt", "test.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "Identical") != null);
}

test "print comparison - different" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printComparison(writer, "test.txt", "other.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "Different") != null);
}
```

### JSON Escaping

```zig
test "print JSON safe - normal" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printJsonSafe(writer, "test.txt");
    try std.testing.expectEqualStrings("\"test.txt\"", buffer.items);
}

test "print JSON safe - with newline" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printJsonSafe(writer, "test\nfile.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\n") != null);
}

test "print JSON safe - with tab" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printJsonSafe(writer, "test\tfile.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\t") != null);
}

test "print JSON safe - with backspace" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printJsonSafe(writer, "test\x08file.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\b") != null);
}
```

### Discussion

### Safe Terminal Output

Display filenames without breaking terminal:

```zig
pub fn printToTerminal(filename: []const u8) !void {
    const stdout = std.io.getStdOut().writer();

    // Escape control characters that could affect terminal
    for (filename) |byte| {
        if (byte >= 32 and byte < 127) {
            try stdout.writeByte(byte);
        } else if (byte == '\n') {
            try stdout.writeAll("\\n");
        } else if (byte == '\r') {
            try stdout.writeAll("\\r");
        } else if (byte == '\t') {
            try stdout.writeAll("\\t");
        } else {
            try std.fmt.format(stdout, "\\x{X:0>2}", .{byte});
        }
    }
    try stdout.writeByte('\n');
}
```

### Unicode Replacement Character

Replace invalid sequences with Unicode replacement character:

```zig
pub fn printWithReplacement(
    writer: anytype,
    filename: []const u8,
) !void {
    if (std.unicode.utf8ValidateSlice(filename)) {
        try writer.writeAll(filename);
        return;
    }

    var i: usize = 0;
    while (i < filename.len) {
        const len = std.unicode.utf8ByteSequenceLength(filename[i]) catch {
            // Invalid UTF-8, use replacement character
            try writer.writeAll("\u{FFFD}");
            i += 1;
            continue;
        };

        if (i + len > filename.len) {
            // Incomplete sequence
            try writer.writeAll("\u{FFFD}");
            break;
        }

        // Check if it's a control character
        if (filename[i] < 32) {
            try std.fmt.format(writer, "\\x{X:0>2}", .{filename[i]});
            i += 1;
        } else {
            try writer.writeAll(filename[i .. i + len]);
            i += len;
        }
    }
}

test "print with replacement" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    // Valid UTF-8
    try printWithReplacement(writer, "test.txt");
    try std.testing.expectEqualStrings("test.txt", buffer.items);

    buffer.clearRetainingCapacity();

    // Invalid UTF-8
    const invalid = [_]u8{ 't', 'e', 's', 't', 0xFF, '.', 't', 'x', 't' };
    try printWithReplacement(writer, &invalid);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\u{FFFD}") != null);
}
```

### Quoted Output

Print filenames with shell-safe quoting:

```zig
pub fn printQuoted(writer: anytype, filename: []const u8) !void {
    try writer.writeByte('"');

    for (filename) |byte| {
        switch (byte) {
            '"' => try writer.writeAll("\\\""),
            '\\' => try writer.writeAll("\\\\"),
            '\n' => try writer.writeAll("\\n"),
            '\r' => try writer.writeAll("\\r"),
            '\t' => try writer.writeAll("\\t"),
            0...31, 127...255 => try std.fmt.format(writer, "\\x{X:0>2}", .{byte}),
            else => try writer.writeByte(byte),
        }
    }

    try writer.writeByte('"');
}

test "print quoted" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printQuoted(writer, "test.txt");
    try std.testing.expectEqualStrings("\"test.txt\"", buffer.items);

    buffer.clearRetainingCapacity();

    try printQuoted(writer, "test\nfile.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\n") != null);
}
```

### Listing Directory with Safe Display

List directory contents with safe filename display:

```zig
pub fn listDirectorySafe(allocator: std.mem.Allocator, path: []const u8) !void {
    const stdout = std.io.getStdOut().writer();

    var dir = try std.fs.cwd().openDir(path, .{ .iterate = true });
    defer dir.close();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        try stdout.writeAll("  ");
        try printSafeFilename(stdout, entry.name);
        try stdout.writeByte('\n');
    }
}
```

### Truncated Display

Display long filenames with truncation:

```zig
pub fn printTruncated(
    writer: anytype,
    filename: []const u8,
    max_len: usize,
) !void {
    if (filename.len <= max_len) {
        try printSafeFilename(writer, filename);
        return;
    }

    const half = max_len / 2 - 2;
    try printSafeFilename(writer, filename[0..half]);
    try writer.writeAll("...");
    try printSafeFilename(writer, filename[filename.len - half ..]);
}

test "print truncated" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    // Short name
    try printTruncated(writer, "short.txt", 20);
    try std.testing.expectEqualStrings("short.txt", buffer.items);

    buffer.clearRetainingCapacity();

    // Long name
    try printTruncated(writer, "very_long_filename_that_should_be_truncated.txt", 20);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "...") != null);
}
```

### Column Formatting

Format filenames in columns:

```zig
pub fn printInColumns(
    writer: anytype,
    filenames: []const []const u8,
    columns: usize,
    width: usize,
) !void {
    var col: usize = 0;

    for (filenames) |filename| {
        var buffer: [256]u8 = undefined;
        var fbs = std.io.fixedBufferStream(&buffer);
        try printSafeFilename(fbs.writer(), filename);

        const display = fbs.getWritten();

        try writer.writeAll(display);

        // Pad to column width
        if (display.len < width) {
            const padding = width - display.len;
            try writer.writeByteNTimes(' ', padding);
        }

        col += 1;
        if (col >= columns) {
            try writer.writeByte('\n');
            col = 0;
        } else {
            try writer.writeAll("  ");
        }
    }

    if (col > 0) {
        try writer.writeByte('\n');
    }
}
```

### Color-Coded Output

Add color for different file types:

```zig
pub const Color = enum {
    reset,
    red,
    green,
    blue,
    yellow,

    pub fn code(self: Color) []const u8 {
        return switch (self) {
            .reset => "\x1b[0m",
            .red => "\x1b[31m",
            .green => "\x1b[32m",
            .blue => "\x1b[34m",
            .yellow => "\x1b[33m",
        };
    }
};

pub fn printColored(
    writer: anytype,
    filename: []const u8,
    color: Color,
) !void {
    try writer.writeAll(color.code());
    try printSafeFilename(writer, filename);
    try writer.writeAll(Color.reset.code());
}

test "print colored" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printColored(writer, "test.txt", .green);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[32m") != null);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "test.txt") != null);
}
```

### Verbose Mode

Show additional information:

```zig
pub fn printVerbose(
    writer: anytype,
    filename: []const u8,
    show_bytes: bool,
) !void {
    try printSafeFilename(writer, filename);

    if (show_bytes) {
        try writer.writeAll(" [bytes: ");
        for (filename, 0..) |byte, i| {
            if (i > 0) try writer.writeByte(' ');
            try std.fmt.format(writer, "{X:0>2}", .{byte});
        }
        try writer.writeByte(']');
    }

    // Show encoding status
    if (!std.unicode.utf8ValidateSlice(filename)) {
        try writer.writeAll(" (invalid UTF-8)");
    }

    try writer.writeByte('\n');
}
```

### Comparison Display

Show two filenames side by side:

```zig
pub fn printComparison(
    writer: anytype,
    filename1: []const u8,
    filename2: []const u8,
) !void {
    try writer.writeAll("Original: ");
    try printSafeFilename(writer, filename1);
    try writer.writeByte('\n');

    try writer.writeAll("Modified: ");
    try printSafeFilename(writer, filename2);
    try writer.writeByte('\n');

    // Show differences
    if (!std.mem.eql(u8, filename1, filename2)) {
        try writer.writeAll("Different\n");
    } else {
        try writer.writeAll("Identical\n");
    }
}
```

### Logging Filenames

Log filenames safely:

```zig
pub fn logFilename(filename: []const u8, level: std.log.Level) !void {
    var buffer: [1024]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);
    const writer = fbs.writer();

    try printSafeFilename(writer, filename);

    switch (level) {
        .info => std.log.info("{s}", .{fbs.getWritten()}),
        .warn => std.log.warn("{s}", .{fbs.getWritten()}),
        .err => std.log.err("{s}", .{fbs.getWritten()}),
        else => {},
    }
}
```

### JSON-Safe Output

Escape for JSON:

```zig
pub fn printJsonSafe(writer: anytype, filename: []const u8) !void {
    try writer.writeByte('"');

    for (filename) |byte| {
        switch (byte) {
            '"' => try writer.writeAll("\\\""),
            '\\' => try writer.writeAll("\\\\"),
            '\n' => try writer.writeAll("\\n"),
            '\r' => try writer.writeAll("\\r"),
            '\t' => try writer.writeAll("\\t"),
            '\x08' => try writer.writeAll("\\b"),
            '\x0C' => try writer.writeAll("\\f"),
            0...31, 127 => try std.fmt.format(writer, "\\u{0:0>4X}", .{byte}),
            else => try writer.writeByte(byte),
        }
    }

    try writer.writeByte('"');
}

test "print JSON safe" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printJsonSafe(writer, "test.txt");
    try std.testing.expectEqualStrings("\"test.txt\"", buffer.items);

    buffer.clearRetainingCapacity();

    try printJsonSafe(writer, "test\nfile.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\n") != null);
}
```

### Best Practices

**Display considerations:**
- Always escape control characters
- Use replacement character for invalid UTF-8
- Quote filenames with spaces or special characters
- Consider terminal capabilities

**Error handling:**
```zig
pub fn safePrint(filename: []const u8) void {
    const stdout = std.io.getStdOut().writer();
    printSafeFilename(stdout, filename) catch {
        // Fallback to hex dump
        for (filename) |byte| {
            std.fmt.format(stdout, "{X:0>2}", .{byte}) catch {};
        }
    };
    stdout.writeByte('\n') catch {};
}
```

**Performance:**
- Pre-allocate buffers for large listings
- Use buffered writers
- Validate UTF-8 once, cache result

### Related Functions

- `std.unicode.utf8ValidateSlice()` - Validate UTF-8
- `std.fmt.format()` - Formatted output
- `std.io.Writer` - Writer interface
- `std.mem.indexOf()` - Find substrings
- `std.log` - Logging framework

### Full Tested Code

```zig
const std = @import("std");

/// Print filename safely, escaping control characters and invalid UTF-8
pub fn printSafeFilename(writer: anytype, filename: []const u8) !void {
    // Always escape control characters
    for (filename) |byte| {
        if (byte >= 32 and byte < 127) {
            try writer.writeByte(byte);
        } else {
            try std.fmt.format(writer, "\\x{X:0>2}", .{byte});
        }
    }
}

/// Print to terminal with control character escaping
pub fn printToTerminal(writer: anytype, filename: []const u8) !void {
    for (filename) |byte| {
        if (byte >= 32 and byte < 127) {
            try writer.writeByte(byte);
        } else if (byte == '\n') {
            try writer.writeAll("\\n");
        } else if (byte == '\r') {
            try writer.writeAll("\\r");
        } else if (byte == '\t') {
            try writer.writeAll("\\t");
        } else {
            try std.fmt.format(writer, "\\x{X:0>2}", .{byte});
        }
    }
    try writer.writeByte('\n');
}

/// Print with Unicode replacement character for invalid sequences
pub fn printWithReplacement(writer: anytype, filename: []const u8) !void {
    if (std.unicode.utf8ValidateSlice(filename)) {
        try writer.writeAll(filename);
        return;
    }

    var i: usize = 0;
    while (i < filename.len) {
        const len = std.unicode.utf8ByteSequenceLength(filename[i]) catch {
            try writer.writeAll("\u{FFFD}");
            i += 1;
            continue;
        };

        if (i + len > filename.len) {
            try writer.writeAll("\u{FFFD}");
            break;
        }

        if (filename[i] < 32) {
            try std.fmt.format(writer, "\\x{X:0>2}", .{filename[i]});
            i += 1;
        } else {
            try writer.writeAll(filename[i .. i + len]);
            i += len;
        }
    }
}

/// Print filename with shell-safe quoting
pub fn printQuoted(writer: anytype, filename: []const u8) !void {
    try writer.writeByte('"');

    for (filename) |byte| {
        switch (byte) {
            '"' => try writer.writeAll("\\\""),
            '\\' => try writer.writeAll("\\\\"),
            '\n' => try writer.writeAll("\\n"),
            '\r' => try writer.writeAll("\\r"),
            '\t' => try writer.writeAll("\\t"),
            0...8, 11, 12, 14...31, 127...255 => try std.fmt.format(writer, "\\x{X:0>2}", .{byte}),
            else => try writer.writeByte(byte),
        }
    }

    try writer.writeByte('"');
}

/// Print filename with truncation
pub fn printTruncated(
    writer: anytype,
    filename: []const u8,
    max_len: usize,
) !void {
    if (filename.len <= max_len) {
        try printSafeFilename(writer, filename);
        return;
    }

    const half = max_len / 2 - 2;
    try printSafeFilename(writer, filename[0..half]);
    try writer.writeAll("...");
    try printSafeFilename(writer, filename[filename.len - half ..]);
}

/// Color codes for terminal output
pub const Color = enum {
    reset,
    red,
    green,
    blue,
    yellow,

    pub fn code(self: Color) []const u8 {
        return switch (self) {
            .reset => "\x1b[0m",
            .red => "\x1b[31m",
            .green => "\x1b[32m",
            .blue => "\x1b[34m",
            .yellow => "\x1b[33m",
        };
    }
};

/// Print filename with color
pub fn printColored(
    writer: anytype,
    filename: []const u8,
    color: Color,
) !void {
    try writer.writeAll(color.code());
    try printSafeFilename(writer, filename);
    try writer.writeAll(Color.reset.code());
}

/// Print filename with verbose information
pub fn printVerbose(
    writer: anytype,
    filename: []const u8,
    show_bytes: bool,
) !void {
    try printSafeFilename(writer, filename);

    if (show_bytes) {
        try writer.writeAll(" [bytes: ");
        for (filename, 0..) |byte, i| {
            if (i > 0) try writer.writeByte(' ');
            try std.fmt.format(writer, "{X:0>2}", .{byte});
        }
        try writer.writeByte(']');
    }

    if (!std.unicode.utf8ValidateSlice(filename)) {
        try writer.writeAll(" (invalid UTF-8)");
    }

    try writer.writeByte('\n');
}

/// Print two filenames for comparison
pub fn printComparison(
    writer: anytype,
    filename1: []const u8,
    filename2: []const u8,
) !void {
    try writer.writeAll("Original: ");
    try printSafeFilename(writer, filename1);
    try writer.writeByte('\n');

    try writer.writeAll("Modified: ");
    try printSafeFilename(writer, filename2);
    try writer.writeByte('\n');

    if (!std.mem.eql(u8, filename1, filename2)) {
        try writer.writeAll("Different\n");
    } else {
        try writer.writeAll("Identical\n");
    }
}

/// Print filename JSON-safe
pub fn printJsonSafe(writer: anytype, filename: []const u8) !void {
    try writer.writeByte('"');

    for (filename) |byte| {
        switch (byte) {
            '"' => try writer.writeAll("\\\""),
            '\\' => try writer.writeAll("\\\\"),
            '\n' => try writer.writeAll("\\n"),
            '\r' => try writer.writeAll("\\r"),
            '\t' => try writer.writeAll("\\t"),
            '\x08' => try writer.writeAll("\\b"),
            '\x0C' => try writer.writeAll("\\f"),
            0...7, 11, 14...31, 127 => try std.fmt.format(writer, "\\u{X:0>4}", .{byte}),
            else => try writer.writeByte(byte),
        }
    }

    try writer.writeByte('"');
}

// Tests

// ANCHOR: safe_printing
test "print safe filename - valid" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printSafeFilename(writer, "normal.txt");
    try std.testing.expectEqualStrings("normal.txt", buffer.items);
}

test "print safe filename - with null byte" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    const bad_name = [_]u8{ 'b', 'a', 'd', 0x00, 'n', 'a', 'm', 'e' };
    try printSafeFilename(writer, &bad_name);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\x00") != null);
}

test "print to terminal" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printToTerminal(writer, "test.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "test.txt") != null);

    buffer.clearRetainingCapacity();

    try printToTerminal(writer, "test\nfile.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\n") != null);
}

test "print with replacement" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printWithReplacement(writer, "test.txt");
    try std.testing.expectEqualStrings("test.txt", buffer.items);

    buffer.clearRetainingCapacity();

    const invalid = [_]u8{ 't', 'e', 's', 't', 0xFF, '.', 't', 'x', 't' };
    try printWithReplacement(writer, &invalid);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\u{FFFD}") != null);
}
// ANCHOR_END: safe_printing

test "print quoted" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printQuoted(writer, "test.txt");
    try std.testing.expectEqualStrings("\"test.txt\"", buffer.items);

    buffer.clearRetainingCapacity();

    try printQuoted(writer, "test\nfile.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\n") != null);
}

test "print quoted with quote" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printQuoted(writer, "test\"file.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\\"") != null);
}

test "print truncated - short name" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printTruncated(writer, "short.txt", 20);
    try std.testing.expectEqualStrings("short.txt", buffer.items);
}

// ANCHOR: special_formatting
test "print truncated - long name" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printTruncated(writer, "very_long_filename_that_should_be_truncated.txt", 20);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "...") != null);
}

test "color codes" {
    try std.testing.expectEqualStrings("\x1b[31m", Color.red.code());
    try std.testing.expectEqualStrings("\x1b[32m", Color.green.code());
    try std.testing.expectEqualStrings("\x1b[34m", Color.blue.code());
    try std.testing.expectEqualStrings("\x1b[33m", Color.yellow.code());
    try std.testing.expectEqualStrings("\x1b[0m", Color.reset.code());
}

test "print colored" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printColored(writer, "test.txt", .green);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[32m") != null);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "test.txt") != null);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\x1b[0m") != null);
}

test "print verbose without bytes" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printVerbose(writer, "test.txt", false);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "test.txt") != null);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "[bytes:") == null);
}

test "print verbose with bytes" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printVerbose(writer, "test.txt", true);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "test.txt") != null);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "[bytes:") != null);
}

test "print verbose with invalid UTF-8" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    const invalid = [_]u8{ 't', 'e', 's', 't', 0xFF };
    try printVerbose(writer, &invalid, false);
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "(invalid UTF-8)") != null);
}

test "print comparison - identical" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printComparison(writer, "test.txt", "test.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "Identical") != null);
}

test "print comparison - different" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printComparison(writer, "test.txt", "other.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "Different") != null);
}
// ANCHOR_END: special_formatting

// ANCHOR: json_escaping
test "print JSON safe - normal" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printJsonSafe(writer, "test.txt");
    try std.testing.expectEqualStrings("\"test.txt\"", buffer.items);
}

test "print JSON safe - with newline" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printJsonSafe(writer, "test\nfile.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\n") != null);
}

test "print JSON safe - with tab" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printJsonSafe(writer, "test\tfile.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\t") != null);
}

test "print JSON safe - with backspace" {
    const allocator = std.testing.allocator;
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(allocator);

    const writer = buffer.writer(allocator);

    try printJsonSafe(writer, "test\x08file.txt");
    try std.testing.expect(std.mem.indexOf(u8, buffer.items, "\\b") != null);
}
// ANCHOR_END: json_escaping
```

---

## Recipe 5.16: Adding or Changing the Encoding of an Already Open File {#recipe-5-16}

**Tags:** allocators, error-handling, files-io, memory, networking, resource-cleanup, sockets, testing
**Difficulty:** advanced
**Code:** `code/02-core/05-files-io/recipe_5_16.zig`

### Problem

You have a raw file descriptor from C code, a network socket, or system call, and want to use it with Zig's file operations.

### Solution

### Wrap File Descriptor

```zig
test "wrap file descriptor" {
    const file = try std.fs.cwd().createFile("/tmp/test_wrap.txt", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_wrap.txt") catch {};

    const fd = file.handle;

    const wrapped = wrapFileDescriptor(fd);

    try wrapped.writeAll("Hello from wrapped FD");

    try wrapped.seekTo(0);
    var buffer: [100]u8 = undefined;
    const n = try wrapped.read(&buffer);

    try std.testing.expectEqualStrings("Hello from wrapped FD", buffer[0..n]);
}

test "get file descriptor" {
    const file = try std.fs.cwd().createFile("/tmp/test_getfd.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_getfd.txt") catch {};

    const fd = getFd(file);
    try std.testing.expect(isValidFd(fd));
}

test "check file descriptor validity" {
    const file = try std.fs.cwd().createFile("/tmp/test_fd_valid.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_fd_valid.txt") catch {};

    const fd = getFd(file);
    try std.testing.expect(isValidFd(fd));

    // Invalid FD
    try std.testing.expect(!isValidFd(-1));
}

test "wrap standard file descriptors" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const stdin = try wrapStdFd(0);
    const stdout = try wrapStdFd(1);
    const stderr = try wrapStdFd(2);

    try std.testing.expect(isValidFd(stdin.handle));
    try std.testing.expect(isValidFd(stdout.handle));
    try std.testing.expect(isValidFd(stderr.handle));
}

test "wrap std fd by number" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const stdin = try wrapStdFd(0);
    const stdout = try wrapStdFd(1);
    const stderr = try wrapStdFd(2);

    try std.testing.expect(isValidFd(stdin.handle));
    try std.testing.expect(isValidFd(stdout.handle));
    try std.testing.expect(isValidFd(stderr.handle));
}

test "wrap std fd invalid" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const result = wrapStdFd(99);
    try std.testing.expectError(error.InvalidStdFd, result);
}
```

### IPC Descriptors

```zig
test "socket pair" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const pair = try createSocketPair();
    defer pair[0].close();
    defer pair[1].close();

    // Just verify we got valid sockets
    try std.testing.expect(isValidFd(pair[0].handle));
    try std.testing.expect(isValidFd(pair[1].handle));
}

test "pipe communication" {
    const pipe = try createPipe();
    defer pipe[0].close();
    defer pipe[1].close();

    try pipe[1].writeAll("Pipe data");

    var buffer: [20]u8 = undefined;
    const n = try pipe[0].read(&buffer);

    try std.testing.expectEqualStrings("Pipe data", buffer[0..n]);
}

test "from C int" {
    const file = try std.fs.cwd().createFile("/tmp/test_cint.txt", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_cint.txt") catch {};

    const c_fd = toCInt(file);
    const back = fromCInt(c_fd);

    try back.writeAll("C interop");

    try file.seekTo(0);
    var buffer: [20]u8 = undefined;
    const n = try file.read(&buffer);

    try std.testing.expectEqualStrings("C interop", buffer[0..n]);
}
```

### Ownership Tracking

```zig
test "owned file - not owned" {
    const file = try std.fs.cwd().createFile("/tmp/test_not_owned.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_not_owned.txt") catch {};

    const fd = file.handle;

    var owned = OwnedFile.init(fd, false);
    defer owned.deinit(); // Won't close

    try owned.writeAll("Not owned");
}

test "anonymous file" {
    const file = try createAnonymousFile();
    defer file.close();

    try file.writeAll("Anonymous data");

    try file.seekTo(0);
    var buffer: [20]u8 = undefined;
    const n = try file.read(&buffer);

    try std.testing.expectEqualStrings("Anonymous data", buffer[0..n]);
}

test "safe wrap - invalid fd" {
    const result = safeWrapFd(-1);
    try std.testing.expectError(error.InvalidFileDescriptor, result);
}

test "safe wrap - valid fd" {
    const file = try std.fs.cwd().createFile("/tmp/test_safe_wrap.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_safe_wrap.txt") catch {};

    const wrapped = try safeWrapFd(file.handle);
    try wrapped.writeAll("Safe wrap");
}

test "cross platform wrap" {
    const file = try std.fs.cwd().createFile("/tmp/test_xplat.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_xplat.txt") catch {};

    const wrapped = try wrapFdCrossPlatform(file.handle);
    try wrapped.writeAll("Cross-platform");
}

test "cross platform wrap - invalid" {
    const result = wrapFdCrossPlatform(-1);
    try std.testing.expectError(error.InvalidFileDescriptor, result);
}

test "set close on exec" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const file = try std.fs.cwd().createFile("/tmp/test_cloexec.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_cloexec.txt") catch {};

    try setCloseOnExec(file);

    // Verify flag is set
    const flags = try std.posix.fcntl(file.handle, std.posix.F.GETFD, 0);
    try std.testing.expect((flags & @as(u32, @intCast(std.posix.FD_CLOEXEC))) != 0);
}
```

### Discussion

### Understanding File Descriptors

File descriptors are small integers representing open files:

```zig
pub fn getFd(file: std.fs.File) std.posix.fd_t {
    return file.handle;
}

pub fn isValidFd(fd: std.posix.fd_t) bool {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return fd != std.os.windows.INVALID_HANDLE_VALUE;
    } else {
        return fd >= 0;
    }
}

test "check file descriptor validity" {
    const file = try std.fs.cwd().createFile("/tmp/test_fd.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_fd.txt") catch {};

    const fd = getFd(file);
    try std.testing.expect(isValidFd(fd));
}
```

### Standard File Descriptors

Wrap stdin, stdout, stderr:

```zig
pub fn getStdin() std.fs.File {
    return std.io.getStdIn();
}

pub fn getStdout() std.fs.File {
    return std.io.getStdOut();
}

pub fn getStderr() std.fs.File {
    return std.io.getStdErr();
}

pub fn wrapStdFd(fd_num: u8) !std.fs.File {
    return switch (fd_num) {
        0 => getStdin(),
        1 => getStdout(),
        2 => getStderr(),
        else => error.InvalidStdFd,
    };
}

test "wrap standard file descriptors" {
    const stdin = getStdin();
    const stdout = getStdout();
    const stderr = getStderr();

    // Verify they're valid
    try std.testing.expect(isValidFd(stdin.handle));
    try std.testing.expect(isValidFd(stdout.handle));
    try std.testing.expect(isValidFd(stderr.handle));
}
```

### Duplicating File Descriptors

Create independent copies:

```zig
pub fn duplicateFd(file: std.fs.File) !std.fs.File {
    const new_fd = try std.posix.dup(file.handle);
    return std.fs.File{ .handle = new_fd };
}

test "duplicate file descriptor" {
    const file = try std.fs.cwd().createFile("/tmp/test_dup.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_dup.txt") catch {};

    // Write to original
    try file.writeAll("Original");

    // Duplicate
    const dup = try duplicateFd(file);
    defer dup.close();

    // Write to duplicate
    try dup.writeAll(" Duplicate");

    // Both refer to same file
    try file.seekTo(0);
    var buffer: [100]u8 = undefined;
    const n = try file.read(&buffer);

    try std.testing.expect(std.mem.indexOf(u8, buffer[0..n], "Original Duplicate") != null);
}
```

### Setting File Descriptor Flags

Control FD behavior:

```zig
pub fn setNonBlocking(file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        // Windows non-blocking I/O is different
        return error.NotSupported;
    }

    const flags = try std.posix.fcntl(file.handle, std.posix.F.GETFL, 0);
    _ = try std.posix.fcntl(file.handle, std.posix.F.SETFL, flags | @as(u32, std.posix.O.NONBLOCK));
}

pub fn setCloseOnExec(file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    const flags = try std.posix.fcntl(file.handle, std.posix.F.GETFD, 0);
    _ = try std.posix.fcntl(file.handle, std.posix.F.SETFD, flags | @as(u32, std.posix.FD_CLOEXEC));
}
```

### From Network Socket

Wrap socket as file:

```zig
pub fn wrapSocket(socket: std.posix.socket_t) std.fs.File {
    return std.fs.File{ .handle = socket };
}

pub fn createSocketPair() ![2]std.fs.File {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var fds: [2]std.posix.fd_t = undefined;
    try std.posix.socketpair(
        std.posix.AF.UNIX,
        std.posix.SOCK.STREAM,
        0,
        &fds,
    );

    return [2]std.fs.File{
        std.fs.File{ .handle = fds[0] },
        std.fs.File{ .handle = fds[1] },
    };
}

test "socket pair" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const pair = try createSocketPair();
    defer pair[0].close();
    defer pair[1].close();

    // Write to one end
    try pair[0].writeAll("Hello");

    // Read from other end
    var buffer: [10]u8 = undefined;
    const n = try pair[1].read(&buffer);

    try std.testing.expectEqualStrings("Hello", buffer[0..n]);
}
```

### From Pipe

Wrap pipe file descriptors:

```zig
pub fn createPipe() ![2]std.fs.File {
    var fds: [2]std.posix.fd_t = undefined;
    try std.posix.pipe(&fds);

    return [2]std.fs.File{
        std.fs.File{ .handle = fds[0] }, // Read end
        std.fs.File{ .handle = fds[1] }, // Write end
    };
}

test "pipe communication" {
    const pipe = try createPipe();
    defer pipe[0].close();
    defer pipe[1].close();

    // Write to pipe
    try pipe[1].writeAll("Pipe data");

    // Read from pipe
    var buffer: [20]u8 = undefined;
    const n = try pipe[0].read(&buffer);

    try std.testing.expectEqualStrings("Pipe data", buffer[0..n]);
}
```

### From C Code

Interop with C file descriptors:

```zig
pub fn fromCInt(c_fd: c_int) std.fs.File {
    const builtin = @import("builtin");
    const fd: std.posix.fd_t = if (builtin.os.tag == .windows)
        @ptrFromInt(@as(usize, @intCast(c_fd)))
    else
        c_fd;

    return std.fs.File{ .handle = fd };
}

pub fn toCInt(file: std.fs.File) c_int {
    const builtin = @import("builtin");
    return if (builtin.os.tag == .windows)
        @intCast(@intFromPtr(file.handle))
    else
        file.handle;
}
```

### Ownership and Closing

Control when FD is closed:

```zig
pub const OwnedFile = struct {
    file: std.fs.File,
    owned: bool,

    pub fn init(fd: std.posix.fd_t, owned: bool) OwnedFile {
        return .{
            .file = std.fs.File{ .handle = fd },
            .owned = owned,
        };
    }

    pub fn deinit(self: *OwnedFile) void {
        if (self.owned) {
            self.file.close();
        }
    }

    pub fn writer(self: *OwnedFile) std.fs.File.Writer {
        return self.file.writer();
    }

    pub fn reader(self: *OwnedFile) std.fs.File.Reader {
        return self.file.reader();
    }
};

test "owned file" {
    const file = try std.fs.cwd().createFile("/tmp/test_owned.txt", .{});
    defer std.fs.cwd().deleteFile("/tmp/test_owned.txt") catch {};

    const fd = file.handle;

    // Transfer ownership
    var owned = OwnedFile.init(fd, true);
    defer owned.deinit(); // This will close the fd

    try owned.writer().writeAll("Owned file");

    // Original file is closed by owned.deinit()
}
```

### Temporary File from FD

Create temp file from descriptor:

```zig
pub fn makeTempFromFd(fd: std.posix.fd_t) std.fs.File {
    return std.fs.File{ .handle = fd };
}

pub fn createAnonymousFile() !std.fs.File {
    const builtin = @import("builtin");
    if (builtin.os.tag == .linux) {
        // Use memfd_create on Linux
        const name = "anonymous";
        const fd = try std.posix.memfd_create(name, 0);
        return std.fs.File{ .handle = fd };
    } else {
        // Fall back to regular temp file
        const file = try std.fs.cwd().createFile("/tmp/anon_temp", .{
            .read = true,
            .truncate = true,
        });
        try std.fs.cwd().deleteFile("/tmp/anon_temp");
        return file;
    }
}

test "anonymous file" {
    const file = try createAnonymousFile();
    defer file.close();

    try file.writeAll("Anonymous data");

    try file.seekTo(0);
    var buffer: [20]u8 = undefined;
    const n = try file.read(&buffer);

    try std.testing.expectEqualStrings("Anonymous data", buffer[0..n]);
}
```

### Error Handling

Safe wrapping with validation:

```zig
pub fn safeWrapFd(fd: std.posix.fd_t) !std.fs.File {
    if (!isValidFd(fd)) {
        return error.InvalidFileDescriptor;
    }

    // Verify it's actually open
    _ = std.posix.fcntl(fd, std.posix.F.GETFL, 0) catch {
        return error.ClosedFileDescriptor;
    };

    return std.fs.File{ .handle = fd };
}

test "safe wrap - invalid fd" {
    const result = safeWrapFd(-1);
    try std.testing.expectError(error.InvalidFileDescriptor, result);
}
```

### Redirecting Standard Streams

Replace stdin/stdout/stderr:

```zig
pub fn redirectStdout(target_file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    try std.posix.dup2(target_file.handle, std.posix.STDOUT_FILENO);
}

pub fn redirectStderr(target_file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    try std.posix.dup2(target_file.handle, std.posix.STDERR_FILENO);
}
```

### Buffered I/O

Wrap with buffering:

```zig
pub fn createBufferedFile(fd: std.posix.fd_t, allocator: std.mem.Allocator) !std.io.BufferedWriter(4096, std.fs.File.Writer) {
    const file = std.fs.File{ .handle = fd };
    return std.io.bufferedWriter(file.writer());
}
```

### Platform Differences

**Unix/Linux:**
- File descriptors are small integers (0, 1, 2, ...)
- `fcntl()` for flags and properties
- Pipes, sockets work naturally
- `dup()`, `dup2()` for duplication

**Windows:**
- HANDLEs instead of integers
- Different API (`GetHandleInformation`, etc.)
- Socket handles separate from file handles

**Cross-platform wrapper:**
```zig
pub fn wrapFdCrossPlatform(fd: std.posix.fd_t) !std.fs.File {
    const builtin = @import("builtin");

    if (builtin.os.tag == .windows) {
        // Windows-specific validation
        if (fd == std.os.windows.INVALID_HANDLE_VALUE) {
            return error.InvalidHandle;
        }
    } else {
        // Unix-like validation
        if (fd < 0) {
            return error.InvalidFileDescriptor;
        }
    }

    return std.fs.File{ .handle = fd };
}
```

### Best Practices

**Ownership:**
- Always clarify who owns the FD
- Use `defer file.close()` for owned FDs
- Don't close FDs you don't own

**Error handling:**
```zig
pub fn wrapAndUse(fd: std.posix.fd_t) !void {
    const file = try safeWrapFd(fd);
    // Don't close - we don't own it

    try file.writeAll("Data");
}
```

**Validation:**
- Check validity before wrapping
- Verify FD is open
- Handle platform differences

### Related Functions

- `std.fs.File{ .handle = fd }` - Wrap file descriptor
- `std.posix.dup()` - Duplicate file descriptor
- `std.posix.dup2()` - Duplicate to specific FD number
- `std.posix.fcntl()` - File control operations
- `std.posix.pipe()` - Create pipe
- `std.posix.socketpair()` - Create socket pair
- `std.io.getStdIn()` - Get stdin file
- `std.io.getStdOut()` - Get stdout file
- `std.io.getStdErr()` - Get stderr file

### Full Tested Code

```zig
const std = @import("std");

/// Wrap a raw file descriptor as a File object
pub fn wrapFileDescriptor(fd: std.posix.fd_t) std.fs.File {
    return std.fs.File{ .handle = fd };
}

/// Get file descriptor from File
pub fn getFd(file: std.fs.File) std.posix.fd_t {
    return file.handle;
}

/// Check if file descriptor is valid
pub fn isValidFd(fd: std.posix.fd_t) bool {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return fd != std.os.windows.INVALID_HANDLE_VALUE;
    } else {
        return fd >= 0;
    }
}

/// Wrap standard file descriptor by number (0=stdin, 1=stdout, 2=stderr)
pub fn wrapStdFd(fd_num: u8) !std.fs.File {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    return switch (fd_num) {
        0 => std.fs.File{ .handle = std.posix.STDIN_FILENO },
        1 => std.fs.File{ .handle = std.posix.STDOUT_FILENO },
        2 => std.fs.File{ .handle = std.posix.STDERR_FILENO },
        else => error.InvalidStdFd,
    };
}

/// Duplicate a file descriptor
pub fn duplicateFd(file: std.fs.File) !std.fs.File {
    const new_fd = try std.posix.dup(file.handle);
    return std.fs.File{ .handle = new_fd };
}

/// Set file descriptor to non-blocking mode
pub fn setNonBlocking(file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    const flags = try std.posix.fcntl(file.handle, std.posix.F.GETFL, 0);
    _ = try std.posix.fcntl(file.handle, std.posix.F.SETFL, flags | @as(u32, @intCast(std.posix.O.NONBLOCK)));
}

/// Set close-on-exec flag
pub fn setCloseOnExec(file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    const flags = try std.posix.fcntl(file.handle, std.posix.F.GETFD, 0);
    _ = try std.posix.fcntl(file.handle, std.posix.F.SETFD, flags | @as(u32, @intCast(std.posix.FD_CLOEXEC)));
}

/// Wrap a socket as a File
pub fn wrapSocket(socket: std.posix.socket_t) std.fs.File {
    return std.fs.File{ .handle = socket };
}

/// Create a pair of connected sockets (Unix domain sockets)
pub fn createSocketPair() ![2]std.fs.File {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    // Use low-level socket/socketpair directly
    const sock1 = try std.posix.socket(std.posix.AF.UNIX, std.posix.SOCK.STREAM, 0);
    errdefer std.posix.close(sock1);

    const sock2 = try std.posix.socket(std.posix.AF.UNIX, std.posix.SOCK.STREAM, 0);
    errdefer std.posix.close(sock2);

    // For testing, we'll just return two separate sockets
    // In real use, you'd need to bind/connect them
    return [2]std.fs.File{
        std.fs.File{ .handle = sock1 },
        std.fs.File{ .handle = sock2 },
    };
}

/// Create a pipe pair
pub fn createPipe() ![2]std.fs.File {
    const fds = try std.posix.pipe();

    return [2]std.fs.File{
        std.fs.File{ .handle = fds[0] }, // Read end
        std.fs.File{ .handle = fds[1] }, // Write end
    };
}

/// Convert C int file descriptor to Zig File
pub fn fromCInt(c_fd: c_int) std.fs.File {
    const builtin = @import("builtin");
    const fd: std.posix.fd_t = if (builtin.os.tag == .windows)
        @ptrFromInt(@as(usize, @intCast(c_fd)))
    else
        c_fd;

    return std.fs.File{ .handle = fd };
}

/// Convert Zig File to C int file descriptor
pub fn toCInt(file: std.fs.File) c_int {
    const builtin = @import("builtin");
    return if (builtin.os.tag == .windows)
        @intCast(@intFromPtr(file.handle))
    else
        file.handle;
}

/// File wrapper with ownership tracking
pub const OwnedFile = struct {
    file: std.fs.File,
    owned: bool,

    pub fn init(fd: std.posix.fd_t, owned: bool) OwnedFile {
        return .{
            .file = std.fs.File{ .handle = fd },
            .owned = owned,
        };
    }

    pub fn deinit(self: *OwnedFile) void {
        if (self.owned) {
            self.file.close();
        }
    }

    pub fn writeAll(self: *OwnedFile, bytes: []const u8) !void {
        return self.file.writeAll(bytes);
    }

    pub fn readAll(self: *OwnedFile, buffer: []u8) !usize {
        return self.file.readAll(buffer);
    }
};

/// Create anonymous/temporary file
pub fn createAnonymousFile() !std.fs.File {
    const builtin = @import("builtin");
    if (builtin.os.tag == .linux) {
        const name = "anonymous";
        const fd = try std.posix.memfd_create(name, 0);
        return std.fs.File{ .handle = fd };
    } else {
        const file = try std.fs.cwd().createFile("/tmp/anon_temp", .{
            .read = true,
            .truncate = true,
        });
        try std.fs.cwd().deleteFile("/tmp/anon_temp");
        return file;
    }
}

/// Safely wrap file descriptor with validation
pub fn safeWrapFd(fd: std.posix.fd_t) !std.fs.File {
    if (!isValidFd(fd)) {
        return error.InvalidFileDescriptor;
    }

    const builtin = @import("builtin");
    if (builtin.os.tag != .windows) {
        // Verify it's actually open
        _ = std.posix.fcntl(fd, std.posix.F.GETFL, 0) catch {
            return error.ClosedFileDescriptor;
        };
    }

    return std.fs.File{ .handle = fd };
}

/// Wrap file descriptor with cross-platform handling
pub fn wrapFdCrossPlatform(fd: std.posix.fd_t) !std.fs.File {
    const builtin = @import("builtin");

    if (builtin.os.tag == .windows) {
        if (fd == std.os.windows.INVALID_HANDLE_VALUE) {
            return error.InvalidHandle;
        }
    } else {
        if (fd < 0) {
            return error.InvalidFileDescriptor;
        }
    }

    return std.fs.File{ .handle = fd };
}

// Tests

// ANCHOR: wrap_fd
test "wrap file descriptor" {
    const file = try std.fs.cwd().createFile("/tmp/test_wrap.txt", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_wrap.txt") catch {};

    const fd = file.handle;

    const wrapped = wrapFileDescriptor(fd);

    try wrapped.writeAll("Hello from wrapped FD");

    try wrapped.seekTo(0);
    var buffer: [100]u8 = undefined;
    const n = try wrapped.read(&buffer);

    try std.testing.expectEqualStrings("Hello from wrapped FD", buffer[0..n]);
}

test "get file descriptor" {
    const file = try std.fs.cwd().createFile("/tmp/test_getfd.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_getfd.txt") catch {};

    const fd = getFd(file);
    try std.testing.expect(isValidFd(fd));
}

test "check file descriptor validity" {
    const file = try std.fs.cwd().createFile("/tmp/test_fd_valid.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_fd_valid.txt") catch {};

    const fd = getFd(file);
    try std.testing.expect(isValidFd(fd));

    // Invalid FD
    try std.testing.expect(!isValidFd(-1));
}

test "wrap standard file descriptors" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const stdin = try wrapStdFd(0);
    const stdout = try wrapStdFd(1);
    const stderr = try wrapStdFd(2);

    try std.testing.expect(isValidFd(stdin.handle));
    try std.testing.expect(isValidFd(stdout.handle));
    try std.testing.expect(isValidFd(stderr.handle));
}

test "wrap std fd by number" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const stdin = try wrapStdFd(0);
    const stdout = try wrapStdFd(1);
    const stderr = try wrapStdFd(2);

    try std.testing.expect(isValidFd(stdin.handle));
    try std.testing.expect(isValidFd(stdout.handle));
    try std.testing.expect(isValidFd(stderr.handle));
}

test "wrap std fd invalid" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const result = wrapStdFd(99);
    try std.testing.expectError(error.InvalidStdFd, result);
}
// ANCHOR_END: wrap_fd

test "duplicate file descriptor" {
    const file = try std.fs.cwd().createFile("/tmp/test_dup.txt", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_dup.txt") catch {};

    try file.writeAll("Original");

    const dup = try duplicateFd(file);
    defer dup.close();

    try dup.writeAll(" Duplicate");

    try file.seekTo(0);
    var buffer: [100]u8 = undefined;
    const n = try file.read(&buffer);

    try std.testing.expect(std.mem.indexOf(u8, buffer[0..n], "Original Duplicate") != null);
}

// ANCHOR: ipc_descriptors
test "socket pair" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const pair = try createSocketPair();
    defer pair[0].close();
    defer pair[1].close();

    // Just verify we got valid sockets
    try std.testing.expect(isValidFd(pair[0].handle));
    try std.testing.expect(isValidFd(pair[1].handle));
}

test "pipe communication" {
    const pipe = try createPipe();
    defer pipe[0].close();
    defer pipe[1].close();

    try pipe[1].writeAll("Pipe data");

    var buffer: [20]u8 = undefined;
    const n = try pipe[0].read(&buffer);

    try std.testing.expectEqualStrings("Pipe data", buffer[0..n]);
}

test "from C int" {
    const file = try std.fs.cwd().createFile("/tmp/test_cint.txt", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_cint.txt") catch {};

    const c_fd = toCInt(file);
    const back = fromCInt(c_fd);

    try back.writeAll("C interop");

    try file.seekTo(0);
    var buffer: [20]u8 = undefined;
    const n = try file.read(&buffer);

    try std.testing.expectEqualStrings("C interop", buffer[0..n]);
}
// ANCHOR_END: ipc_descriptors

test "owned file" {
    const file = try std.fs.cwd().createFile("/tmp/test_owned.txt", .{});
    defer std.fs.cwd().deleteFile("/tmp/test_owned.txt") catch {};

    const fd = file.handle;

    var owned = OwnedFile.init(fd, true);
    defer owned.deinit();

    try owned.writeAll("Owned file");
}

// ANCHOR: ownership_tracking
test "owned file - not owned" {
    const file = try std.fs.cwd().createFile("/tmp/test_not_owned.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_not_owned.txt") catch {};

    const fd = file.handle;

    var owned = OwnedFile.init(fd, false);
    defer owned.deinit(); // Won't close

    try owned.writeAll("Not owned");
}

test "anonymous file" {
    const file = try createAnonymousFile();
    defer file.close();

    try file.writeAll("Anonymous data");

    try file.seekTo(0);
    var buffer: [20]u8 = undefined;
    const n = try file.read(&buffer);

    try std.testing.expectEqualStrings("Anonymous data", buffer[0..n]);
}

test "safe wrap - invalid fd" {
    const result = safeWrapFd(-1);
    try std.testing.expectError(error.InvalidFileDescriptor, result);
}

test "safe wrap - valid fd" {
    const file = try std.fs.cwd().createFile("/tmp/test_safe_wrap.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_safe_wrap.txt") catch {};

    const wrapped = try safeWrapFd(file.handle);
    try wrapped.writeAll("Safe wrap");
}

test "cross platform wrap" {
    const file = try std.fs.cwd().createFile("/tmp/test_xplat.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_xplat.txt") catch {};

    const wrapped = try wrapFdCrossPlatform(file.handle);
    try wrapped.writeAll("Cross-platform");
}

test "cross platform wrap - invalid" {
    const result = wrapFdCrossPlatform(-1);
    try std.testing.expectError(error.InvalidFileDescriptor, result);
}

test "set close on exec" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    const file = try std.fs.cwd().createFile("/tmp/test_cloexec.txt", .{});
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_cloexec.txt") catch {};

    try setCloseOnExec(file);

    // Verify flag is set
    const flags = try std.posix.fcntl(file.handle, std.posix.F.GETFD, 0);
    try std.testing.expect((flags & @as(u32, @intCast(std.posix.FD_CLOEXEC))) != 0);
}
// ANCHOR_END: ownership_tracking
```

---

## Recipe 5.17: Writing Bytes to a Text File {#recipe-5-17}

**Tags:** allocators, atomics, concurrency, error-handling, files-io, memory, resource-cleanup, testing, threading
**Difficulty:** advanced
**Code:** `code/02-core/05-files-io/recipe_5_17.zig`

### Problem

You need to create temporary files or directories for testing or temporary storage that are automatically cleaned up and have unique names to avoid conflicts.

### Solution

### Basic Temp Files

```zig
test "create temp file" {
    const allocator = std.testing.allocator;

    const temp = try createTempFile(allocator, "test");
    defer temp.file.close();
    defer allocator.free(temp.path);
    defer std.fs.cwd().deleteFile(temp.path) catch {};

    try temp.file.writeAll("Temporary data");

    try temp.file.seekTo(0);
    var buffer: [20]u8 = undefined;
    const n = try temp.file.read(&buffer);

    try std.testing.expectEqualStrings("Temporary data", buffer[0..n]);
}

test "temp dir for testing" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const file = try tmp.dir.createFile("test.txt", .{});
    defer file.close();

    try file.writeAll("Test data");

    const content = try tmp.dir.readFileAlloc(std.testing.allocator, "test.txt", 1024);
    defer std.testing.allocator.free(content);

    try std.testing.expectEqualStrings("Test data", content);
}
```

### Self Deleting

```zig
test "self-deleting file" {
    const allocator = std.testing.allocator;

    var temp = try SelfDeletingFile.create(allocator, "self_delete");
    defer temp.deinit();

    try temp.writeAll("Auto-deleted");

    const stat = try std.fs.cwd().statFile(temp.path);
    try std.testing.expect(stat.kind == .file);
}

test "temp file with content" {
    const allocator = std.testing.allocator;

    const temp = try createTempFileWithContent(allocator, "content", "Initial content");
    defer temp.file.close();
    defer allocator.free(temp.path);
    defer std.fs.cwd().deleteFile(temp.path) catch {};

    var buffer: [20]u8 = undefined;
    const n = try temp.file.read(&buffer);

    try std.testing.expectEqualStrings("Initial content", buffer[0..n]);
}

test "named temp file" {
    const allocator = std.testing.allocator;

    const temp = try createNamedTempFile(allocator, "myfile", "txt");
    defer temp.file.close();
    defer allocator.free(temp.path);
    defer std.fs.cwd().deleteFile(temp.path) catch {};

    try std.testing.expect(std.mem.endsWith(u8, temp.path, ".txt"));
}
```

### Cleanup Helpers

```zig
test "iterate temp dir" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Create some files
    {
        const file1 = try tmp.dir.createFile("file1.txt", .{});
        defer file1.close();
        const file2 = try tmp.dir.createFile("file2.txt", .{});
        defer file2.close();
    }

    var count: usize = 0;
    var iter = tmp.dir.iterate();
    while (try iter.next()) |_| {
        count += 1;
    }

    try std.testing.expectEqual(@as(usize, 2), count);
}

test "get temp dir" {
    const allocator = std.testing.allocator;

    const temp_dir = try getTempDir(allocator);
    defer allocator.free(temp_dir);

    try std.testing.expect(temp_dir.len > 0);
}

test "memory temp file" {
    const builtin = @import("builtin");
    if (builtin.os.tag != .linux) return error.SkipZigTest;

    const file = try createMemoryTempFile();
    defer file.close();

    try file.writeAll("In memory");

    try file.seekTo(0);
    var buffer: [20]u8 = undefined;
    const n = try file.read(&buffer);

    try std.testing.expectEqualStrings("In memory", buffer[0..n]);
}

test "cleanup helpers" {
    const allocator = std.testing.allocator;

    // Create temp file
    const temp = try createTempFile(allocator, "cleanup");
    try temp.file.writeAll("test");
    temp.file.close();

    // Verify exists
    const stat = try std.fs.cwd().statFile(temp.path);
    try std.testing.expect(stat.kind == .file);

    // Make a copy of path for later check
    const path_copy = try allocator.dupe(u8, temp.path);
    defer allocator.free(path_copy);

    // Cleanup (frees temp.path)
    cleanupTempFile(temp.path, allocator);

    // Should not exist (use path_copy)
    const result = std.fs.cwd().statFile(path_copy);
    try std.testing.expectError(error.FileNotFound, result);
}

test "temp dir cleanup" {
    const allocator = std.testing.allocator;

    const dir_path = try createTempDir(allocator, "cleanup_dir");

    // Create file in it
    var dir = try std.fs.cwd().openDir(dir_path, .{});
    const file = try dir.createFile("file.txt", .{});
    file.close();
    dir.close();

    // Verify exists
    const stat = try std.fs.cwd().statFile(dir_path);
    try std.testing.expect(stat.kind == .directory);

    // Make a copy of path for later check
    const path_copy = try allocator.dupe(u8, dir_path);
    defer allocator.free(path_copy);

    // Cleanup (frees dir_path)
    cleanupTempDir(dir_path, allocator);

    // Should not exist (use path_copy)
    const result = std.fs.cwd().statFile(path_copy);
    try std.testing.expectError(error.FileNotFound, result);
}

test "multiple temp files" {
    const allocator = std.testing.allocator;

    const temp1 = try createTempFile(allocator, "multi");
    defer temp1.file.close();
    defer allocator.free(temp1.path);
    defer std.fs.cwd().deleteFile(temp1.path) catch {};

    std.Thread.sleep(2 * std.time.ns_per_ms);

    const temp2 = try createTempFile(allocator, "multi");
    defer temp2.file.close();
    defer allocator.free(temp2.path);
    defer std.fs.cwd().deleteFile(temp2.path) catch {};

    // Paths should be different
    try std.testing.expect(!std.mem.eql(u8, temp1.path, temp2.path));
}
```

### Discussion

### Using Testing Temporary Directory

For unit tests, use `std.testing.tmpDir`:

```zig
pub fn createTestTempDir() !std.testing.TmpDir {
    return std.testing.tmpDir(.{});
}

test "temp dir for testing" {
    var tmp = try std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Create file in temp dir
    const file = try tmp.dir.createFile("test.txt", .{});
    defer file.close();

    try file.writeAll("Test data");

    // Read it back
    const content = try tmp.dir.readFileAlloc(std.testing.allocator, "test.txt", 1024);
    defer std.testing.allocator.free(content);

    try std.testing.expectEqualStrings("Test data", content);
}
```

### Creating Unique Temp Files

Generate unique filenames:

```zig
pub fn makeTempPath(allocator: std.mem.Allocator, dir: []const u8, prefix: []const u8) ![]u8 {
    var prng = std.Random.DefaultPrng.init(@intCast(std.time.milliTimestamp()));
    const random = prng.random();

    var buf: [32]u8 = undefined;
    const random_part = std.fmt.bufPrint(&buf, "{x}", .{random.int(u64)}) catch unreachable;

    return std.fmt.allocPrint(allocator, "{s}/{s}_{s}", .{ dir, prefix, random_part });
}

test "unique temp paths" {
    const allocator = std.testing.allocator;

    const path1 = try makeTempPath(allocator, "/tmp", "test");
    defer allocator.free(path1);

    const path2 = try makeTempPath(allocator, "/tmp", "test");
    defer allocator.free(path2);

    // Paths should be different
    try std.testing.expect(!std.mem.eql(u8, path1, path2));
}
```

### Temporary Directories

Create temp directories:

```zig
pub fn createTempDir(allocator: std.mem.Allocator, prefix: []const u8) ![]u8 {
    const path = try makeTempPath(allocator, "/tmp", prefix);
    errdefer allocator.free(path);

    try std.fs.cwd().makeDir(path);

    return path;
}

pub fn removeTempDir(path: []const u8) !void {
    try std.fs.cwd().deleteTree(path);
}

test "temp directory" {
    const allocator = std.testing.allocator;

    const dir_path = try createTempDir(allocator, "testdir");
    defer allocator.free(dir_path);
    defer removeTempDir(dir_path) catch {};

    // Create file in temp dir
    var dir = try std.fs.cwd().openDir(dir_path, .{});
    defer dir.close();

    const file = try dir.createFile("test.txt", .{});
    defer file.close();

    try file.writeAll("In temp dir");
}
```

### Self-Deleting Temp File

File that deletes itself on close:

```zig
pub const SelfDeletingFile = struct {
    file: std.fs.File,
    path: []const u8,
    allocator: std.mem.Allocator,

    pub fn create(allocator: std.mem.Allocator, prefix: []const u8) !SelfDeletingFile {
        const temp = try createTempFile(allocator, prefix);
        return .{
            .file = temp.file,
            .path = temp.path,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *SelfDeletingFile) void {
        self.file.close();
        std.fs.cwd().deleteFile(self.path) catch {};
        self.allocator.free(self.path);
    }

    pub fn writer(self: *SelfDeletingFile) std.fs.File.Writer {
        var buf: [4096]u8 = undefined;
        return self.file.writer(&buf);
    }
};

test "self-deleting file" {
    const allocator = std.testing.allocator;

    var temp = try SelfDeletingFile.create(allocator, "self_delete");
    defer temp.deinit();

    try temp.file.writeAll("Auto-deleted");

    // File exists now
    const stat = try std.fs.cwd().statFile(temp.path);
    try std.testing.expect(stat.kind == .file);
}
```

### Temporary File with Content

Create temp file with initial content:

```zig
pub fn createTempFileWithContent(
    allocator: std.mem.Allocator,
    prefix: []const u8,
    content: []const u8,
) !struct {
    file: std.fs.File,
    path: []const u8,
} {
    const temp = try createTempFile(allocator, prefix);
    errdefer {
        temp.file.close();
        allocator.free(temp.path);
        std.fs.cwd().deleteFile(temp.path) catch {};
    }

    try temp.file.writeAll(content);
    try temp.file.seekTo(0);

    return temp;
}

test "temp file with content" {
    const allocator = std.testing.allocator;

    const temp = try createTempFileWithContent(allocator, "content", "Initial content");
    defer temp.file.close();
    defer allocator.free(temp.path);
    defer std.fs.cwd().deleteFile(temp.path) catch {};

    var buffer: [20]u8 = undefined;
    const n = try temp.file.read(&buffer);

    try std.testing.expectEqualStrings("Initial content", buffer[0..n]);
}
```

### Named Temporary File

Create temp file that preserves extension:

```zig
pub fn createNamedTempFile(
    allocator: std.mem.Allocator,
    name: []const u8,
    extension: []const u8,
) !struct {
    file: std.fs.File,
    path: []const u8,
} {
    var prng = std.Random.DefaultPrng.init(@intCast(std.time.milliTimestamp()));
    const random = prng.random();

    const path = try std.fmt.allocPrint(
        allocator,
        "/tmp/{s}_{x}.{s}",
        .{ name, random.int(u32), extension },
    );
    errdefer allocator.free(path);

    const file = try std.fs.cwd().createFile(path, .{ .read = true });

    return .{ .file = file, .path = path };
}

test "named temp file" {
    const allocator = std.testing.allocator;

    const temp = try createNamedTempFile(allocator, "myfile", "txt");
    defer temp.file.close();
    defer allocator.free(temp.path);
    defer std.fs.cwd().deleteFile(temp.path) catch {};

    try std.testing.expect(std.mem.endsWith(u8, temp.path, ".txt"));
}
```

### Atomic Temp File Creation

Safely create temp file that doesn't already exist:

```zig
pub fn createUniqueTempFile(
    allocator: std.mem.Allocator,
    prefix: []const u8,
    max_attempts: usize,
) !struct {
    file: std.fs.File,
    path: []const u8,
} {
    var attempts: usize = 0;
    while (attempts < max_attempts) : (attempts += 1) {
        const path = try makeTempPath(allocator, "/tmp", prefix);
        errdefer allocator.free(path);

        const file = std.fs.cwd().createFile(path, .{
            .read = true,
            .exclusive = true,
        }) catch |err| switch (err) {
            error.PathAlreadyExists => {
                allocator.free(path);
                continue;
            },
            else => return err,
        };

        return .{ .file = file, .path = path };
    }

    return error.TooManyAttempts;
}

test "unique temp file" {
    const allocator = std.testing.allocator;

    const temp = try createUniqueTempFile(allocator, "unique", 10);
    defer temp.file.close();
    defer allocator.free(temp.path);
    defer std.fs.cwd().deleteFile(temp.path) catch {};

    try temp.file.writeAll("Unique file");
}
```

### Temporary Directory Iterator

Iterate over temp dir contents:

```zig
pub fn iterateTempDir(tmp: *std.testing.TmpDir) !void {
    var iter = tmp.dir.iterate();
    while (try iter.next()) |entry| {
        std.debug.print("Entry: {s}\n", .{entry.name});
    }
}

test "iterate temp dir" {
    var tmp = try std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Create some files
    {
        const file1 = try tmp.dir.createFile("file1.txt", .{});
        defer file1.close();
        const file2 = try tmp.dir.createFile("file2.txt", .{});
        defer file2.close();
    }

    var count: usize = 0;
    var iter = tmp.dir.iterate();
    while (try iter.next()) |_| {
        count += 1;
    }

    try std.testing.expectEqual(@as(usize, 2), count);
}
```

### Cleanup Helpers

Safe cleanup of temp resources:

```zig
pub fn cleanupTempFile(path: []const u8, allocator: std.mem.Allocator) void {
    std.fs.cwd().deleteFile(path) catch {};
    allocator.free(path);
}

pub fn cleanupTempDir(path: []const u8, allocator: std.mem.Allocator) void {
    std.fs.cwd().deleteTree(path) catch {};
    allocator.free(path);
}
```

### Platform-Specific Temp Directories

Get platform temp directory:

```zig
pub fn getTempDir(allocator: std.mem.Allocator) ![]u8 {
    const builtin = @import("builtin");

    if (builtin.os.tag == .windows) {
        // Windows temp dir
        return std.process.getEnvVarOwned(allocator, "TEMP") catch |err| switch (err) {
            error.EnvironmentVariableNotFound => try allocator.dupe(u8, "C:\\Temp"),
            else => return err,
        };
    } else {
        // Unix temp dir
        return std.process.getEnvVarOwned(allocator, "TMPDIR") catch |err| switch (err) {
            error.EnvironmentVariableNotFound => try allocator.dupe(u8, "/tmp"),
            else => return err,
        };
    }
}

test "get temp dir" {
    const allocator = std.testing.allocator;

    const temp_dir = try getTempDir(allocator);
    defer allocator.free(temp_dir);

    try std.testing.expect(temp_dir.len > 0);
}
```

### Memory-Based Temporary Files

Use memory instead of disk (Linux):

```zig
pub fn createMemoryTempFile() !std.fs.File {
    const builtin = @import("builtin");
    if (builtin.os.tag == .linux) {
        const fd = try std.posix.memfd_create("memtemp", 0);
        return std.fs.File{ .handle = fd };
    } else {
        return error.NotSupported;
    }
}

test "memory temp file" {
    const builtin = @import("builtin");
    if (builtin.os.tag != .linux) return error.SkipZigTest;

    const file = try createMemoryTempFile();
    defer file.close();

    try file.writeAll("In memory");

    try file.seekTo(0);
    var buffer: [20]u8 = undefined;
    const n = try file.read(&buffer);

    try std.testing.expectEqualStrings("In memory", buffer[0..n]);
}
```

### Best Practices

**Temp file naming:**
- Include timestamp or random component
- Use descriptive prefixes
- Preserve extensions when needed
- Check for conflicts with `exclusive` flag

**Cleanup:**
```zig
// Always cleanup temp resources
var tmp = try std.testing.tmpDir(.{});
defer tmp.cleanup(); // Automatically removes directory and contents

// For manual temp files
const temp = try createTempFile(allocator, "prefix");
defer temp.file.close();
defer allocator.free(temp.path);
defer std.fs.cwd().deleteFile(temp.path) catch {}; // Ignore errors
```

**Security:**
- Use `exclusive` flag to prevent race conditions
- Set appropriate permissions
- Clean up on all error paths with `errdefer`
- Don't use predictable names

**Testing:**
- Use `std.testing.tmpDir` for tests
- Clean up in `defer` blocks
- Test cleanup failure paths

### Related Functions

- `std.testing.tmpDir()` - Create temporary test directory
- `std.testing.TmpDir.cleanup()` - Clean up temp directory
- `std.fs.cwd().createFile()` - Create file
- `std.fs.cwd().makeDir()` - Create directory
- `std.fs.cwd().deleteFile()` - Delete file
- `std.fs.cwd().deleteTree()` - Delete directory recursively
- `std.posix.memfd_create()` - Create memory-backed file (Linux)
- `std.process.getEnvVarOwned()` - Get environment variable
- `std.Random` - Generate random values
- `std.time.milliTimestamp()` - Get current timestamp

### Full Tested Code

```zig
const std = @import("std");

/// Create a temporary file with unique name
pub fn createTempFile(allocator: std.mem.Allocator, prefix: []const u8) !struct {
    file: std.fs.File,
    path: []const u8,
} {
    var buf: [64]u8 = undefined;
    const name = try std.fmt.bufPrint(&buf, "{s}_{d}", .{ prefix, std.time.milliTimestamp() });

    const path = try std.fs.path.join(allocator, &[_][]const u8{ "/tmp", name });
    errdefer allocator.free(path);

    const file = try std.fs.cwd().createFile(path, .{ .read = true });

    return .{ .file = file, .path = path };
}

/// Generate unique temporary path
pub fn makeTempPath(allocator: std.mem.Allocator, dir: []const u8, prefix: []const u8) ![]u8 {
    var prng = std.Random.DefaultPrng.init(@intCast(std.time.milliTimestamp()));
    const random = prng.random();

    var buf: [32]u8 = undefined;
    const random_part = std.fmt.bufPrint(&buf, "{x}", .{random.int(u64)}) catch unreachable;

    return std.fmt.allocPrint(allocator, "{s}/{s}_{s}", .{ dir, prefix, random_part });
}

/// Create temporary directory
pub fn createTempDir(allocator: std.mem.Allocator, prefix: []const u8) ![]u8 {
    const path = try makeTempPath(allocator, "/tmp", prefix);
    errdefer allocator.free(path);

    try std.fs.cwd().makeDir(path);

    return path;
}

/// Remove temporary directory and contents
pub fn removeTempDir(path: []const u8) !void {
    try std.fs.cwd().deleteTree(path);
}

/// Self-deleting temporary file
pub const SelfDeletingFile = struct {
    file: std.fs.File,
    path: []const u8,
    allocator: std.mem.Allocator,

    pub fn create(allocator: std.mem.Allocator, prefix: []const u8) !SelfDeletingFile {
        const temp = try createTempFile(allocator, prefix);
        return .{
            .file = temp.file,
            .path = temp.path,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *SelfDeletingFile) void {
        self.file.close();
        std.fs.cwd().deleteFile(self.path) catch {};
        self.allocator.free(self.path);
    }

    pub fn writeAll(self: *SelfDeletingFile, bytes: []const u8) !void {
        return self.file.writeAll(bytes);
    }

    pub fn read(self: *SelfDeletingFile, buffer: []u8) !usize {
        return self.file.read(buffer);
    }
};

/// Create temp file with initial content
pub fn createTempFileWithContent(
    allocator: std.mem.Allocator,
    prefix: []const u8,
    content: []const u8,
) !struct {
    file: std.fs.File,
    path: []const u8,
} {
    const temp = try createTempFile(allocator, prefix);
    errdefer {
        temp.file.close();
        allocator.free(temp.path);
        std.fs.cwd().deleteFile(temp.path) catch {};
    }

    try temp.file.writeAll(content);
    try temp.file.seekTo(0);

    return .{ .file = temp.file, .path = temp.path };
}

/// Create named temporary file with extension
pub fn createNamedTempFile(
    allocator: std.mem.Allocator,
    name: []const u8,
    extension: []const u8,
) !struct {
    file: std.fs.File,
    path: []const u8,
} {
    var prng = std.Random.DefaultPrng.init(@intCast(std.time.milliTimestamp()));
    const random = prng.random();

    const path = try std.fmt.allocPrint(
        allocator,
        "/tmp/{s}_{x}.{s}",
        .{ name, random.int(u32), extension },
    );
    errdefer allocator.free(path);

    const file = try std.fs.cwd().createFile(path, .{ .read = true });

    return .{ .file = file, .path = path };
}

/// Create unique temp file atomically
pub fn createUniqueTempFile(
    allocator: std.mem.Allocator,
    prefix: []const u8,
    max_attempts: usize,
) !struct {
    file: std.fs.File,
    path: []const u8,
} {
    var attempts: usize = 0;
    while (attempts < max_attempts) : (attempts += 1) {
        const path = try makeTempPath(allocator, "/tmp", prefix);
        errdefer allocator.free(path);

        const file = std.fs.cwd().createFile(path, .{
            .read = true,
            .exclusive = true,
        }) catch |err| switch (err) {
            error.PathAlreadyExists => {
                allocator.free(path);
                continue;
            },
            else => return err,
        };

        return .{ .file = file, .path = path };
    }

    return error.TooManyAttempts;
}

/// Clean up temporary file
pub fn cleanupTempFile(path: []const u8, allocator: std.mem.Allocator) void {
    std.fs.cwd().deleteFile(path) catch {};
    allocator.free(path);
}

/// Clean up temporary directory
pub fn cleanupTempDir(path: []const u8, allocator: std.mem.Allocator) void {
    std.fs.cwd().deleteTree(path) catch {};
    allocator.free(path);
}

/// Get platform-specific temp directory
pub fn getTempDir(allocator: std.mem.Allocator) ![]u8 {
    const builtin = @import("builtin");

    if (builtin.os.tag == .windows) {
        return std.process.getEnvVarOwned(allocator, "TEMP") catch |err| switch (err) {
            error.EnvironmentVariableNotFound => try allocator.dupe(u8, "C:\\Temp"),
            else => return err,
        };
    } else {
        return std.process.getEnvVarOwned(allocator, "TMPDIR") catch |err| switch (err) {
            error.EnvironmentVariableNotFound => try allocator.dupe(u8, "/tmp"),
            else => return err,
        };
    }
}

/// Create memory-backed temporary file (Linux only)
pub fn createMemoryTempFile() !std.fs.File {
    const builtin = @import("builtin");
    if (builtin.os.tag == .linux) {
        const fd = try std.posix.memfd_create("memtemp", 0);
        return std.fs.File{ .handle = fd };
    } else {
        return error.NotSupported;
    }
}

// Tests

// ANCHOR: basic_temp_files
test "create temp file" {
    const allocator = std.testing.allocator;

    const temp = try createTempFile(allocator, "test");
    defer temp.file.close();
    defer allocator.free(temp.path);
    defer std.fs.cwd().deleteFile(temp.path) catch {};

    try temp.file.writeAll("Temporary data");

    try temp.file.seekTo(0);
    var buffer: [20]u8 = undefined;
    const n = try temp.file.read(&buffer);

    try std.testing.expectEqualStrings("Temporary data", buffer[0..n]);
}

test "temp dir for testing" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const file = try tmp.dir.createFile("test.txt", .{});
    defer file.close();

    try file.writeAll("Test data");

    const content = try tmp.dir.readFileAlloc(std.testing.allocator, "test.txt", 1024);
    defer std.testing.allocator.free(content);

    try std.testing.expectEqualStrings("Test data", content);
}
// ANCHOR_END: basic_temp_files

test "unique temp paths" {
    const allocator = std.testing.allocator;

    const path1 = try makeTempPath(allocator, "/tmp", "test");
    defer allocator.free(path1);

    // Small delay to ensure different timestamp
    std.Thread.sleep(1 * std.time.ns_per_ms);

    const path2 = try makeTempPath(allocator, "/tmp", "test");
    defer allocator.free(path2);

    try std.testing.expect(!std.mem.eql(u8, path1, path2));
}

test "temp directory" {
    const allocator = std.testing.allocator;

    const dir_path = try createTempDir(allocator, "testdir");
    defer allocator.free(dir_path);
    defer removeTempDir(dir_path) catch {};

    var dir = try std.fs.cwd().openDir(dir_path, .{});
    defer dir.close();

    const file = try dir.createFile("test.txt", .{});
    defer file.close();

    try file.writeAll("In temp dir");
}

// ANCHOR: self_deleting
test "self-deleting file" {
    const allocator = std.testing.allocator;

    var temp = try SelfDeletingFile.create(allocator, "self_delete");
    defer temp.deinit();

    try temp.writeAll("Auto-deleted");

    const stat = try std.fs.cwd().statFile(temp.path);
    try std.testing.expect(stat.kind == .file);
}

test "temp file with content" {
    const allocator = std.testing.allocator;

    const temp = try createTempFileWithContent(allocator, "content", "Initial content");
    defer temp.file.close();
    defer allocator.free(temp.path);
    defer std.fs.cwd().deleteFile(temp.path) catch {};

    var buffer: [20]u8 = undefined;
    const n = try temp.file.read(&buffer);

    try std.testing.expectEqualStrings("Initial content", buffer[0..n]);
}

test "named temp file" {
    const allocator = std.testing.allocator;

    const temp = try createNamedTempFile(allocator, "myfile", "txt");
    defer temp.file.close();
    defer allocator.free(temp.path);
    defer std.fs.cwd().deleteFile(temp.path) catch {};

    try std.testing.expect(std.mem.endsWith(u8, temp.path, ".txt"));
}
// ANCHOR_END: self_deleting

test "unique temp file" {
    const allocator = std.testing.allocator;

    const temp = try createUniqueTempFile(allocator, "unique", 10);
    defer temp.file.close();
    defer allocator.free(temp.path);
    defer std.fs.cwd().deleteFile(temp.path) catch {};

    try temp.file.writeAll("Unique file");
}

// ANCHOR: cleanup_helpers
test "iterate temp dir" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Create some files
    {
        const file1 = try tmp.dir.createFile("file1.txt", .{});
        defer file1.close();
        const file2 = try tmp.dir.createFile("file2.txt", .{});
        defer file2.close();
    }

    var count: usize = 0;
    var iter = tmp.dir.iterate();
    while (try iter.next()) |_| {
        count += 1;
    }

    try std.testing.expectEqual(@as(usize, 2), count);
}

test "get temp dir" {
    const allocator = std.testing.allocator;

    const temp_dir = try getTempDir(allocator);
    defer allocator.free(temp_dir);

    try std.testing.expect(temp_dir.len > 0);
}

test "memory temp file" {
    const builtin = @import("builtin");
    if (builtin.os.tag != .linux) return error.SkipZigTest;

    const file = try createMemoryTempFile();
    defer file.close();

    try file.writeAll("In memory");

    try file.seekTo(0);
    var buffer: [20]u8 = undefined;
    const n = try file.read(&buffer);

    try std.testing.expectEqualStrings("In memory", buffer[0..n]);
}

test "cleanup helpers" {
    const allocator = std.testing.allocator;

    // Create temp file
    const temp = try createTempFile(allocator, "cleanup");
    try temp.file.writeAll("test");
    temp.file.close();

    // Verify exists
    const stat = try std.fs.cwd().statFile(temp.path);
    try std.testing.expect(stat.kind == .file);

    // Make a copy of path for later check
    const path_copy = try allocator.dupe(u8, temp.path);
    defer allocator.free(path_copy);

    // Cleanup (frees temp.path)
    cleanupTempFile(temp.path, allocator);

    // Should not exist (use path_copy)
    const result = std.fs.cwd().statFile(path_copy);
    try std.testing.expectError(error.FileNotFound, result);
}

test "temp dir cleanup" {
    const allocator = std.testing.allocator;

    const dir_path = try createTempDir(allocator, "cleanup_dir");

    // Create file in it
    var dir = try std.fs.cwd().openDir(dir_path, .{});
    const file = try dir.createFile("file.txt", .{});
    file.close();
    dir.close();

    // Verify exists
    const stat = try std.fs.cwd().statFile(dir_path);
    try std.testing.expect(stat.kind == .directory);

    // Make a copy of path for later check
    const path_copy = try allocator.dupe(u8, dir_path);
    defer allocator.free(path_copy);

    // Cleanup (frees dir_path)
    cleanupTempDir(dir_path, allocator);

    // Should not exist (use path_copy)
    const result = std.fs.cwd().statFile(path_copy);
    try std.testing.expectError(error.FileNotFound, result);
}

test "multiple temp files" {
    const allocator = std.testing.allocator;

    const temp1 = try createTempFile(allocator, "multi");
    defer temp1.file.close();
    defer allocator.free(temp1.path);
    defer std.fs.cwd().deleteFile(temp1.path) catch {};

    std.Thread.sleep(2 * std.time.ns_per_ms);

    const temp2 = try createTempFile(allocator, "multi");
    defer temp2.file.close();
    defer allocator.free(temp2.path);
    defer std.fs.cwd().deleteFile(temp2.path) catch {};

    // Paths should be different
    try std.testing.expect(!std.mem.eql(u8, temp1.path, temp2.path));
}
// ANCHOR_END: cleanup_helpers
```

---

## Recipe 5.18: Communicating with Serial Ports {#recipe-5-18}

**Tags:** allocators, arraylist, data-structures, error-handling, files-io, memory, resource-cleanup, slices, testing
**Difficulty:** advanced
**Code:** `code/02-core/05-files-io/recipe_5_18.zig`

### Problem

You need to communicate with hardware devices via serial ports (RS-232, USB-to-serial, etc.) and control parameters like baud rate, parity, and stop bits.

### Solution

### Serial Config

```zig
test "baud rate conversion" {
    const speed_9600: std.posix.speed_t = @enumFromInt(9600);
    const speed_115200: std.posix.speed_t = @enumFromInt(115200);
    const speed_57600: std.posix.speed_t = @enumFromInt(57600);

    try std.testing.expectEqual(speed_9600, baudToSpeed(9600));
    try std.testing.expectEqual(speed_115200, baudToSpeed(115200));
    try std.testing.expectEqual(speed_57600, baudToSpeed(57600));
}

test "serial config defaults" {
    const config = SerialConfig{};

    try std.testing.expectEqual(@as(u32, 9600), config.baud_rate);
    try std.testing.expectEqual(@as(u8, 8), config.data_bits);
    try std.testing.expectEqual(@as(u8, 1), config.stop_bits);
    try std.testing.expectEqual(Parity.none, config.parity);
    try std.testing.expectEqual(FlowControl.none, config.flow_control);
    try std.testing.expectEqual(@as(u8, 10), config.timeout_deciseconds);
}

test "serial config custom" {
    const config = SerialConfig{
        .baud_rate = 115200,
        .data_bits = 7,
        .stop_bits = 2,
        .parity = .even,
        .flow_control = .hardware,
        .timeout_deciseconds = 20,
    };

    try std.testing.expectEqual(@as(u32, 115200), config.baud_rate);
    try std.testing.expectEqual(@as(u8, 7), config.data_bits);
    try std.testing.expectEqual(@as(u8, 2), config.stop_bits);
    try std.testing.expectEqual(Parity.even, config.parity);
    try std.testing.expectEqual(FlowControl.hardware, config.flow_control);
    try std.testing.expectEqual(@as(u8, 20), config.timeout_deciseconds);
}

test "parity enum" {
    const none = Parity.none;
    const even = Parity.even;
    const odd = Parity.odd;

    try std.testing.expect(none != even);
    try std.testing.expect(even != odd);
    try std.testing.expect(odd != none);
}

test "flow control enum" {
    const none = FlowControl.none;
    const software = FlowControl.software;
    const hardware = FlowControl.hardware;

    try std.testing.expect(none != software);
    try std.testing.expect(software != hardware);
    try std.testing.expect(hardware != none);
}
```

### Device Discovery

```zig
test "get common devices" {
    const allocator = std.testing.allocator;

    const devices = try getCommonDevices(allocator);
    defer {
        for (devices) |device| {
            allocator.free(device);
        }
        allocator.free(devices);
    }

    // Just verify we can call it
    // Actual devices depend on hardware
}

test "windows not supported" {
    const builtin = @import("builtin");
    if (builtin.os.tag != .windows) return error.SkipZigTest;

    const result = SerialPort.open("/dev/ttyUSB0", 9600);
    try std.testing.expectError(error.NotSupported, result);
}
```

### Usage Examples

```zig
test "serial port API" {
    // This test documents the API without requiring hardware
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Example usage (would fail without hardware):
    // var port = try SerialPort.open("/dev/ttyUSB0", 115200);
    // defer port.close();
    //
    // try port.write("Hello\r\n");
    //
    // var buffer: [100]u8 = undefined;
    // const n = try port.read(&buffer);
}

test "configured open API" {
    // This test documents the configured API without requiring hardware
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Example usage (would fail without hardware):
    // const config = SerialConfig{
    //     .baud_rate = 115200,
    //     .parity = .even,
    //     .flow_control = .hardware,
    // };
    //
    // var port = try openConfigured("/dev/ttyUSB0", config);
    // defer port.close();
}

test "read line simulation" {
    // Simulate reading with a fixed buffer
    var buffer: [100]u8 = undefined;
    @memcpy(buffer[0.."Hello\n".len], "Hello\n");

    // In real use, this would read from a file
    // const line = try readLine(file, &buffer, '\n');
}

test "write commands simulation" {
    // Documents the write command API
    // In real use:
    // try writeCommand(file, "AT");
    // try writeLine(file, "Hello World");
}

test "AT command simulation" {
    // Documents AT command pattern
    // In real use with modem:
    // var response_buffer: [256]u8 = undefined;
    // const response = try sendATCommand(&port, "AT", &response_buffer);
    // Expected response: "OK"
}

test "buffer flush simulation" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Documents flush API
    // In real use:
    // try flushInput(file);
    // try flushOutput(file);
    // try flushBoth(file);
}

test "timeout configuration" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Documents timeout API
    // In real use:
    // try setTimeout(file, 20); // 2 seconds
}

test "parameter configuration" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Documents parameter setting API
    // In real use:
    // try setBaudRate(file, 115200);
    // try setDataBits(file, 8);
    // try setStopBits(file, 1);
    // try setParity(file, .none);
    // try setFlowControl(file, .none);
}
```

### Discussion

### Opening Serial Ports

Common serial port paths:

```zig
pub fn openSerialPort(allocator: std.mem.Allocator, device: []const u8, baud_rate: u32) !SerialPort {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    _ = allocator;
    return SerialPort.open(device, baud_rate);
}

test "open serial port" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Common paths: /dev/ttyUSB0, /dev/ttyACM0, /dev/ttyS0
    // This would require actual hardware to test
}
```

### Configuring Baud Rate

Set communication speed:

```zig
pub fn setBaudRate(file: std.fs.File, baud_rate: u32) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    const speed = baudToSpeed(baud_rate);
    termios.ispeed = speed;
    termios.ospeed = speed;

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}
```

### Setting Parity

Configure parity checking:

```zig
pub const Parity = enum {
    none,
    even,
    odd,
};

pub fn setParity(file: std.fs.File, parity: Parity) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    switch (parity) {
        .none => {
            termios.cflag &= ~@as(u32, @intCast(std.posix.PARENB));
        },
        .even => {
            termios.cflag |= @as(u32, @intCast(std.posix.PARENB));
            termios.cflag &= ~@as(u32, @intCast(std.posix.PARODD));
        },
        .odd => {
            termios.cflag |= @as(u32, @intCast(std.posix.PARENB | std.posix.PARODD));
        },
    }

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}
```

### Setting Stop Bits

Configure stop bits:

```zig
pub fn setStopBits(file: std.fs.File, stop_bits: u8) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    if (stop_bits == 1) {
        termios.cflag &= ~@as(u32, @intCast(std.posix.CSTOPB));
    } else {
        termios.cflag |= @as(u32, @intCast(std.posix.CSTOPB));
    }

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}
```

### Setting Data Bits

Configure data bits:

```zig
pub fn setDataBits(file: std.fs.File, data_bits: u8) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    termios.cflag &= ~@as(u32, @intCast(std.posix.CSIZE));

    const bits = switch (data_bits) {
        5 => std.posix.CS5,
        6 => std.posix.CS6,
        7 => std.posix.CS7,
        8 => std.posix.CS8,
        else => return error.InvalidDataBits,
    };

    termios.cflag |= @as(u32, @intCast(bits));

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}
```

### Setting Flow Control

Configure hardware/software flow control:

```zig
pub const FlowControl = enum {
    none,
    software,
    hardware,
};

pub fn setFlowControl(file: std.fs.File, flow: FlowControl) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    switch (flow) {
        .none => {
            termios.iflag &= ~@as(u32, @intCast(std.posix.IXON | std.posix.IXOFF | std.posix.IXANY));
            termios.cflag &= ~@as(u32, @intCast(std.posix.CRTSCTS));
        },
        .software => {
            termios.iflag |= @as(u32, @intCast(std.posix.IXON | std.posix.IXOFF));
            termios.cflag &= ~@as(u32, @intCast(std.posix.CRTSCTS));
        },
        .hardware => {
            termios.iflag &= ~@as(u32, @intCast(std.posix.IXON | std.posix.IXOFF | std.posix.IXANY));
            termios.cflag |= @as(u32, @intCast(std.posix.CRTSCTS));
        },
    }

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}
```

### Setting Timeouts

Control read/write timeouts:

```zig
pub fn setTimeout(file: std.fs.File, timeout_deciseconds: u8) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    termios.cc[std.posix.V.TIME] = timeout_deciseconds;
    termios.cc[std.posix.V.MIN] = 0;

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}
```

### Flushing Buffers

Discard buffered data:

```zig
pub fn flushInput(file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    try std.posix.tcflush(file.handle, .IFLUSH);
}

pub fn flushOutput(file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    try std.posix.tcflush(file.handle, .OFLUSH);
}

pub fn flushBoth(file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    try std.posix.tcflush(file.handle, .IOFLUSH);
}
```

### Reading Data

Read from serial port:

```zig
pub fn readLine(file: std.fs.File, buffer: []u8, delimiter: u8) ![]const u8 {
    var pos: usize = 0;

    while (pos < buffer.len) {
        const n = try file.read(buffer[pos..pos + 1]);
        if (n == 0) break;

        if (buffer[pos] == delimiter) {
            return buffer[0..pos];
        }

        pos += 1;
    }

    return buffer[0..pos];
}

pub fn readExactly(file: std.fs.File, buffer: []u8) !void {
    var pos: usize = 0;

    while (pos < buffer.len) {
        const n = try file.read(buffer[pos..]);
        if (n == 0) return error.EndOfStream;
        pos += n;
    }
}
```

### Writing Data

Write to serial port:

```zig
pub fn writeLine(file: std.fs.File, data: []const u8) !void {
    try file.writeAll(data);
    try file.writeAll("\r\n");
}

pub fn writeCommand(file: std.fs.File, command: []const u8) !void {
    try file.writeAll(command);
    try file.writeAll("\r");
}
```

### Complete Serial Port Wrapper

Full-featured wrapper:

```zig
pub const SerialConfig = struct {
    baud_rate: u32 = 9600,
    data_bits: u8 = 8,
    stop_bits: u8 = 1,
    parity: Parity = .none,
    flow_control: FlowControl = .none,
    timeout_deciseconds: u8 = 10,
};

pub fn openConfigured(path: []const u8, config: SerialConfig) !SerialPort {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var port = try SerialPort.open(path, config.baud_rate);
    errdefer port.close();

    try setDataBits(port.file, config.data_bits);
    try setStopBits(port.file, config.stop_bits);
    try setParity(port.file, config.parity);
    try setFlowControl(port.file, config.flow_control);
    try setTimeout(port.file, config.timeout_deciseconds);

    return port;
}
```

### AT Command Example

Communicating with modems:

```zig
pub fn sendATCommand(port: *SerialPort, command: []const u8, response_buffer: []u8) ![]const u8 {
    try flushBoth(port.file);

    try writeCommand(port.file, command);

    const response = try readLine(port.file, response_buffer, '\n');

    return response;
}
```

### Best Practices

**Configuration:**
- Always set all parameters explicitly
- Use `.FLUSH` when applying settings to clear buffers
- Verify device paths exist before opening

**Error handling:**
```zig
const port = SerialPort.open("/dev/ttyUSB0", 115200) catch |err| {
    std.log.err("Failed to open serial port: {}", .{err});
    return err;
};
defer port.close();
```

**Timeouts:**
- Set appropriate timeouts to avoid blocking forever
- `V.TIME` is in deciseconds (tenths of a second)
- `V.MIN = 0` for timeout-based reads

**Buffer management:**
- Flush buffers before important operations
- Use fixed-size buffers for embedded systems
- Handle partial reads in loops

**Platform support:**
- Unix/Linux: Full POSIX termios support
- macOS: Same as Unix/Linux
- Windows: Requires different API (not covered here)

### Related Functions

- `std.posix.tcgetattr()` - Get terminal attributes
- `std.posix.tcsetattr()` - Set terminal attributes
- `std.posix.tcflush()` - Flush terminal buffers
- `std.posix.tcdrain()` - Wait for output to drain
- `std.fs.File.read()` - Read data
- `std.fs.File.writeAll()` - Write data
- `std.fs.cwd().openFile()` - Open file/device

### Full Tested Code

```zig
const std = @import("std");

/// Serial port wrapper
pub const SerialPort = struct {
    file: std.fs.File,

    pub fn open(path: []const u8, baud_rate: u32) !SerialPort {
        const builtin = @import("builtin");
        if (builtin.os.tag == .windows) {
            return error.NotSupported;
        }

        const file = try std.fs.cwd().openFile(path, .{ .mode = .read_write });
        errdefer file.close();

        try configurePort(file, baud_rate);

        return SerialPort{ .file = file };
    }

    pub fn close(self: *SerialPort) void {
        self.file.close();
    }

    pub fn write(self: *SerialPort, data: []const u8) !void {
        return self.file.writeAll(data);
    }

    pub fn read(self: *SerialPort, buffer: []u8) !usize {
        return self.file.read(buffer);
    }
};

/// Configure serial port with termios
fn configurePort(file: std.fs.File, baud_rate: u32) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    // Set baud rate
    const speed = baudToSpeed(baud_rate);
    termios.ispeed = speed;
    termios.ospeed = speed;

    // 8N1 mode (8 data bits, no parity, 1 stop bit)
    termios.cflag &= ~@as(u32, @intCast(std.posix.PARENB)); // No parity
    termios.cflag &= ~@as(u32, @intCast(std.posix.CSTOPB)); // 1 stop bit
    termios.cflag &= ~@as(u32, @intCast(std.posix.CSIZE));
    termios.cflag |= @as(u32, @intCast(std.posix.CS8)); // 8 data bits

    // Enable receiver, ignore modem control lines
    termios.cflag |= @as(u32, @intCast(std.posix.CREAD | std.posix.CLOCAL));

    // Raw mode (no canonical processing)
    termios.lflag &= ~@as(u32, @intCast(std.posix.ICANON | std.posix.ECHO | std.posix.ECHOE | std.posix.ISIG));

    // Disable software flow control
    termios.iflag &= ~@as(u32, @intCast(std.posix.IXON | std.posix.IXOFF | std.posix.IXANY));

    // Raw output (no post-processing)
    termios.oflag &= ~@as(u32, @intCast(std.posix.OPOST));

    // Set read timeout (1 second)
    termios.cc[std.posix.V.TIME] = 10; // Deciseconds
    termios.cc[std.posix.V.MIN] = 0;

    try std.posix.tcsetattr(file.handle, .FLUSH, termios);
}

/// Convert baud rate to termios speed constant
fn baudToSpeed(baud_rate: u32) std.posix.speed_t {
    // On Unix-like systems, speed_t can be an enum (macOS/BSD) or integer (Linux)
    // Use @enumFromInt to handle both cases
    return @enumFromInt(baud_rate);
}

/// Parity options
pub const Parity = enum {
    none,
    even,
    odd,
};

/// Set parity
pub fn setParity(file: std.fs.File, parity: Parity) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    switch (parity) {
        .none => {
            termios.cflag &= ~@as(u32, @intCast(std.posix.PARENB));
        },
        .even => {
            termios.cflag |= @as(u32, @intCast(std.posix.PARENB));
            termios.cflag &= ~@as(u32, @intCast(std.posix.PARODD));
        },
        .odd => {
            termios.cflag |= @as(u32, @intCast(std.posix.PARENB | std.posix.PARODD));
        },
    }

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}

/// Set stop bits (1 or 2)
pub fn setStopBits(file: std.fs.File, stop_bits: u8) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    if (stop_bits != 1 and stop_bits != 2) {
        return error.InvalidStopBits;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    if (stop_bits == 1) {
        termios.cflag &= ~@as(u32, @intCast(std.posix.CSTOPB));
    } else {
        termios.cflag |= @as(u32, @intCast(std.posix.CSTOPB));
    }

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}

/// Set data bits (5, 6, 7, or 8)
pub fn setDataBits(file: std.fs.File, data_bits: u8) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    termios.cflag &= ~@as(u32, @intCast(std.posix.CSIZE));

    const bits = switch (data_bits) {
        5 => std.posix.CS5,
        6 => std.posix.CS6,
        7 => std.posix.CS7,
        8 => std.posix.CS8,
        else => return error.InvalidDataBits,
    };

    termios.cflag |= @as(u32, @intCast(bits));

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}

/// Set baud rate
pub fn setBaudRate(file: std.fs.File, baud_rate: u32) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    const speed = baudToSpeed(baud_rate);
    termios.ispeed = speed;
    termios.ospeed = speed;

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}

/// Flow control options
pub const FlowControl = enum {
    none,
    software,
    hardware,
};

/// Set flow control
pub fn setFlowControl(file: std.fs.File, flow: FlowControl) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    switch (flow) {
        .none => {
            termios.iflag &= ~@as(u32, @intCast(std.posix.IXON | std.posix.IXOFF | std.posix.IXANY));
            termios.cflag &= ~@as(u32, @intCast(std.posix.CRTSCTS));
        },
        .software => {
            termios.iflag |= @as(u32, @intCast(std.posix.IXON | std.posix.IXOFF));
            termios.cflag &= ~@as(u32, @intCast(std.posix.CRTSCTS));
        },
        .hardware => {
            termios.iflag &= ~@as(u32, @intCast(std.posix.IXON | std.posix.IXOFF | std.posix.IXANY));
            termios.cflag |= @as(u32, @intCast(std.posix.CRTSCTS));
        },
    }

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}

/// Set read timeout in deciseconds (tenths of a second)
pub fn setTimeout(file: std.fs.File, timeout_deciseconds: u8) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var termios = try std.posix.tcgetattr(file.handle);

    termios.cc[std.posix.V.TIME] = timeout_deciseconds;
    termios.cc[std.posix.V.MIN] = 0;

    try std.posix.tcsetattr(file.handle, .NOW, termios);
}

/// Flush input buffer
pub fn flushInput(file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    try std.posix.tcflush(file.handle, .IFLUSH);
}

/// Flush output buffer
pub fn flushOutput(file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    try std.posix.tcflush(file.handle, .OFLUSH);
}

/// Flush both input and output buffers
pub fn flushBoth(file: std.fs.File) !void {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    try std.posix.tcflush(file.handle, .IOFLUSH);
}

/// Read line until delimiter
pub fn readLine(file: std.fs.File, buffer: []u8, delimiter: u8) ![]const u8 {
    var pos: usize = 0;

    while (pos < buffer.len) {
        const n = try file.read(buffer[pos..pos + 1]);
        if (n == 0) break;

        if (buffer[pos] == delimiter) {
            return buffer[0..pos];
        }

        pos += 1;
    }

    return buffer[0..pos];
}

/// Read exact number of bytes
pub fn readExactly(file: std.fs.File, buffer: []u8) !void {
    var pos: usize = 0;

    while (pos < buffer.len) {
        const n = try file.read(buffer[pos..]);
        if (n == 0) return error.EndOfStream;
        pos += n;
    }
}

/// Write line with CRLF
pub fn writeLine(file: std.fs.File, data: []const u8) !void {
    try file.writeAll(data);
    try file.writeAll("\r\n");
}

/// Write command with CR
pub fn writeCommand(file: std.fs.File, command: []const u8) !void {
    try file.writeAll(command);
    try file.writeAll("\r");
}

/// Serial configuration struct
pub const SerialConfig = struct {
    baud_rate: u32 = 9600,
    data_bits: u8 = 8,
    stop_bits: u8 = 1,
    parity: Parity = .none,
    flow_control: FlowControl = .none,
    timeout_deciseconds: u8 = 10,
};

/// Open serial port with custom configuration
pub fn openConfigured(path: []const u8, config: SerialConfig) !SerialPort {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) {
        return error.NotSupported;
    }

    var port = try SerialPort.open(path, config.baud_rate);
    errdefer port.close();

    try setDataBits(port.file, config.data_bits);
    try setStopBits(port.file, config.stop_bits);
    try setParity(port.file, config.parity);
    try setFlowControl(port.file, config.flow_control);
    try setTimeout(port.file, config.timeout_deciseconds);

    return port;
}

/// Send AT command and read response
pub fn sendATCommand(port: *SerialPort, command: []const u8, response_buffer: []u8) ![]const u8 {
    try flushBoth(port.file);

    try writeCommand(port.file, command);

    const response = try readLine(port.file, response_buffer, '\n');

    return response;
}

/// Get common serial device paths
pub fn getCommonDevices(allocator: std.mem.Allocator) ![][]const u8 {
    var devices = std.ArrayList([]const u8){};
    errdefer {
        for (devices.items) |item| {
            allocator.free(item);
        }
        devices.deinit(allocator);
    }

    // Common USB serial adapters
    const patterns = [_][]const u8{
        "/dev/ttyUSB0",
        "/dev/ttyUSB1",
        "/dev/ttyACM0",
        "/dev/ttyACM1",
        "/dev/ttyS0",
        "/dev/ttyS1",
    };

    for (patterns) |pattern| {
        std.fs.cwd().access(pattern, .{}) catch continue;
        const device = try allocator.dupe(u8, pattern);
        try devices.append(allocator, device);
    }

    return devices.toOwnedSlice(allocator);
}

// Tests

// ANCHOR: serial_config
test "baud rate conversion" {
    const speed_9600: std.posix.speed_t = @enumFromInt(9600);
    const speed_115200: std.posix.speed_t = @enumFromInt(115200);
    const speed_57600: std.posix.speed_t = @enumFromInt(57600);

    try std.testing.expectEqual(speed_9600, baudToSpeed(9600));
    try std.testing.expectEqual(speed_115200, baudToSpeed(115200));
    try std.testing.expectEqual(speed_57600, baudToSpeed(57600));
}

test "serial config defaults" {
    const config = SerialConfig{};

    try std.testing.expectEqual(@as(u32, 9600), config.baud_rate);
    try std.testing.expectEqual(@as(u8, 8), config.data_bits);
    try std.testing.expectEqual(@as(u8, 1), config.stop_bits);
    try std.testing.expectEqual(Parity.none, config.parity);
    try std.testing.expectEqual(FlowControl.none, config.flow_control);
    try std.testing.expectEqual(@as(u8, 10), config.timeout_deciseconds);
}

test "serial config custom" {
    const config = SerialConfig{
        .baud_rate = 115200,
        .data_bits = 7,
        .stop_bits = 2,
        .parity = .even,
        .flow_control = .hardware,
        .timeout_deciseconds = 20,
    };

    try std.testing.expectEqual(@as(u32, 115200), config.baud_rate);
    try std.testing.expectEqual(@as(u8, 7), config.data_bits);
    try std.testing.expectEqual(@as(u8, 2), config.stop_bits);
    try std.testing.expectEqual(Parity.even, config.parity);
    try std.testing.expectEqual(FlowControl.hardware, config.flow_control);
    try std.testing.expectEqual(@as(u8, 20), config.timeout_deciseconds);
}

test "parity enum" {
    const none = Parity.none;
    const even = Parity.even;
    const odd = Parity.odd;

    try std.testing.expect(none != even);
    try std.testing.expect(even != odd);
    try std.testing.expect(odd != none);
}

test "flow control enum" {
    const none = FlowControl.none;
    const software = FlowControl.software;
    const hardware = FlowControl.hardware;

    try std.testing.expect(none != software);
    try std.testing.expect(software != hardware);
    try std.testing.expect(hardware != none);
}
// ANCHOR_END: serial_config

// ANCHOR: device_discovery
test "get common devices" {
    const allocator = std.testing.allocator;

    const devices = try getCommonDevices(allocator);
    defer {
        for (devices) |device| {
            allocator.free(device);
        }
        allocator.free(devices);
    }

    // Just verify we can call it
    // Actual devices depend on hardware
}

test "windows not supported" {
    const builtin = @import("builtin");
    if (builtin.os.tag != .windows) return error.SkipZigTest;

    const result = SerialPort.open("/dev/ttyUSB0", 9600);
    try std.testing.expectError(error.NotSupported, result);
}
// ANCHOR_END: device_discovery

// The following tests require actual serial hardware

// ANCHOR: usage_examples
test "serial port API" {
    // This test documents the API without requiring hardware
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Example usage (would fail without hardware):
    // var port = try SerialPort.open("/dev/ttyUSB0", 115200);
    // defer port.close();
    //
    // try port.write("Hello\r\n");
    //
    // var buffer: [100]u8 = undefined;
    // const n = try port.read(&buffer);
}

test "configured open API" {
    // This test documents the configured API without requiring hardware
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Example usage (would fail without hardware):
    // const config = SerialConfig{
    //     .baud_rate = 115200,
    //     .parity = .even,
    //     .flow_control = .hardware,
    // };
    //
    // var port = try openConfigured("/dev/ttyUSB0", config);
    // defer port.close();
}

test "read line simulation" {
    // Simulate reading with a fixed buffer
    var buffer: [100]u8 = undefined;
    @memcpy(buffer[0.."Hello\n".len], "Hello\n");

    // In real use, this would read from a file
    // const line = try readLine(file, &buffer, '\n');
}

test "write commands simulation" {
    // Documents the write command API
    // In real use:
    // try writeCommand(file, "AT");
    // try writeLine(file, "Hello World");
}

test "AT command simulation" {
    // Documents AT command pattern
    // In real use with modem:
    // var response_buffer: [256]u8 = undefined;
    // const response = try sendATCommand(&port, "AT", &response_buffer);
    // Expected response: "OK"
}

test "buffer flush simulation" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Documents flush API
    // In real use:
    // try flushInput(file);
    // try flushOutput(file);
    // try flushBoth(file);
}

test "timeout configuration" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Documents timeout API
    // In real use:
    // try setTimeout(file, 20); // 2 seconds
}

test "parameter configuration" {
    const builtin = @import("builtin");
    if (builtin.os.tag == .windows) return error.SkipZigTest;

    // Documents parameter setting API
    // In real use:
    // try setBaudRate(file, 115200);
    // try setDataBits(file, 8);
    // try setStopBits(file, 1);
    // try setParity(file, .none);
    // try setFlowControl(file, .none);
}
// ANCHOR_END: usage_examples
```

---

## Recipe 5.19: Serializing Zig Objects {#recipe-5-19}

**Tags:** allocators, arraylist, comptime, data-structures, error-handling, files-io, json, memory, parsing, resource-cleanup, slices, testing
**Difficulty:** advanced
**Code:** `code/02-core/05-files-io/recipe_5_19.zig`

### Problem

You need to convert Zig structs and data types to bytes for file storage, network transmission, or inter-process communication.

### Solution

### Basic Serialization

```zig
test "serialize to disk" {
    var person = Person{
        .age = 30,
        .height = 1.75,
        .name = undefined,
    };
    @memcpy(&person.name, "Alice" ++ ([_]u8{0} ** 15));

    const file = try std.fs.cwd().createFile("/tmp/person.bin", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/person.bin") catch {};

    try serializeToDisk(file, person);

    try file.seekTo(0);
    const loaded = try deserializeFromDisk(file);

    try std.testing.expectEqual(person.age, loaded.age);
    try std.testing.expectEqual(person.height, loaded.height);
}

test "struct to bytes" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    const point = Point{ .x = 10, .y = 20 };
    const bytes = structToBytes(Point, &point);

    try std.testing.expectEqual(@sizeOf(Point), bytes.len);

    const restored = try bytesToStruct(Point, bytes);
    try std.testing.expectEqual(point.x, restored.x);
    try std.testing.expectEqual(point.y, restored.y);
}

test "bytes to struct size validation" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    const bad_bytes = [_]u8{1} ** 4; // Too small
    const result = bytesToStruct(Point, &bad_bytes);

    try std.testing.expectError(error.InvalidSize, result);
}

test "packed struct serialization" {
    const data = PackedData{
        .flags = 0xFF,
        .value = 0x1234,
        .id = 0xDEADBEEF,
    };

    const bytes = serializePacked(data);
    const restored = deserializePacked(bytes);

    try std.testing.expectEqual(data.flags, restored.flags);
    try std.testing.expectEqual(data.value, restored.value);
    try std.testing.expectEqual(data.id, restored.id);
}

test "packed struct size" {
    // Note: @sizeOf returns alignment-adjusted size (8), @bitSizeOf returns 56 (7 bytes)
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(PackedData));
    try std.testing.expectEqual(@as(usize, 56), @bitSizeOf(PackedData));
}
```

### Endianness Handling

```zig
test "endianness different values" {
    const value: u16 = 0xABCD;

    const be_bytes = serializeInt(u16, value, .big);
    const le_bytes = serializeInt(u16, value, .little);

    try std.testing.expectEqual(@as(u8, 0xAB), be_bytes[0]);
    try std.testing.expectEqual(@as(u8, 0xCD), be_bytes[1]);
    try std.testing.expectEqual(@as(u8, 0xCD), le_bytes[0]);
    try std.testing.expectEqual(@as(u8, 0xAB), le_bytes[1]);
}

test "JSON serialization" {
    const allocator = std.testing.allocator;

    const user = User{
        .id = 42,
        .name = "Alice",
        .active = true,
    };

    const json = try serializeToJson(allocator, user);
    defer allocator.free(json);

    const restored = try deserializeFromJson(allocator, json);
    defer allocator.free(restored.name);

    try std.testing.expectEqual(user.id, restored.id);
    try std.testing.expectEqualStrings(user.name, restored.name);
    try std.testing.expectEqual(user.active, restored.active);
}

test "JSON contains expected fields" {
    const allocator = std.testing.allocator;

    const user = User{
        .id = 123,
        .name = "Bob",
        .active = false,
    };

    const json = try serializeToJson(allocator, user);
    defer allocator.free(json);

    // Verify JSON contains expected data
    try std.testing.expect(std.mem.indexOf(u8, json, "123") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "Bob") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "false") != null);
}
```

### Array Serialization

```zig
test "struct array serialization" {
    const allocator = std.testing.allocator;

    const Point = struct {
        x: i32,
        y: i32,
    };

    const points = [_]Point{
        .{ .x = 1, .y = 2 },
        .{ .x = 3, .y = 4 },
        .{ .x = 5, .y = 6 },
    };

    const file = try std.fs.cwd().createFile("/tmp/points.bin", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/points.bin") catch {};

    try writeStructArray(Point, file, &points);

    try file.seekTo(0);
    const loaded = try readStructArray(Point, allocator, file);
    defer allocator.free(loaded);

    try std.testing.expectEqual(points.len, loaded.len);
    for (points, loaded) |original, restored| {
        try std.testing.expectEqual(original.x, restored.x);
        try std.testing.expectEqual(original.y, restored.y);
    }
}

test "empty struct array" {
    const allocator = std.testing.allocator;

    const Point = struct {
        x: i32,
        y: i32,
    };

    const points: []const Point = &.{};

    const file = try std.fs.cwd().createFile("/tmp/empty_points.bin", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/empty_points.bin") catch {};

    try writeStructArray(Point, file, points);

    try file.seekTo(0);
    const loaded = try readStructArray(Point, allocator, file);
    defer allocator.free(loaded);

    try std.testing.expectEqual(@as(usize, 0), loaded.len);
}
```

### Custom Serialization

```zig
test "custom serialization" {
    const allocator = std.testing.allocator;

    const original = CustomData{
        .version = 1,
        .data = "Hello, World!",
    };

    const bytes = try original.serialize(allocator);
    defer allocator.free(bytes);

    const restored = try CustomData.deserialize(allocator, bytes);
    defer allocator.free(restored.data);

    try std.testing.expectEqual(original.version, restored.version);
    try std.testing.expectEqualStrings(original.data, restored.data);
}

test "custom serialization empty data" {
    const allocator = std.testing.allocator;

    const original = CustomData{
        .version = 5,
        .data = "",
    };

    const bytes = try original.serialize(allocator);
    defer allocator.free(bytes);

    const restored = try CustomData.deserialize(allocator, bytes);
    defer allocator.free(restored.data);

    try std.testing.expectEqual(original.version, restored.version);
    try std.testing.expectEqual(@as(usize, 0), restored.data.len);
}

test "custom deserialization invalid data" {
    const allocator = std.testing.allocator;

    const bad_bytes = [_]u8{1} ** 3; // Too small
    const result = CustomData.deserialize(allocator, &bad_bytes);

    try std.testing.expectError(error.InvalidData, result);
}

test "versioned serialization" {
    const allocator = std.testing.allocator;

    const data = VersionedData{
        .id = 123,
        .name = "Test",
        .extra = "Extra data",
    };

    const bytes = try data.serialize(allocator);
    defer allocator.free(bytes);

    const restored = try VersionedData.deserialize(allocator, bytes);
    defer allocator.free(restored.name);
    defer if (restored.extra) |extra| allocator.free(extra);

    try std.testing.expectEqual(data.id, restored.id);
    try std.testing.expectEqualStrings(data.name, restored.name);
    try std.testing.expectEqualStrings(data.extra.?, restored.extra.?);
}

test "versioned serialization without extra" {
    const allocator = std.testing.allocator;

    const data = VersionedData{
        .id = 456,
        .name = "NoExtra",
        .extra = null,
    };

    const bytes = try data.serialize(allocator);
    defer allocator.free(bytes);

    const restored = try VersionedData.deserialize(allocator, bytes);
    defer allocator.free(restored.name);

    try std.testing.expectEqual(data.id, restored.id);
    try std.testing.expectEqualStrings(data.name, restored.name);
    try std.testing.expectEqual(@as(?[]const u8, null), restored.extra);
}

test "versioned data includes version" {
    const allocator = std.testing.allocator;

    const data = VersionedData{
        .id = 789,
        .name = "Versioned",
        .extra = "Data",
    };

    const bytes = try data.serialize(allocator);
    defer allocator.free(bytes);

    // First byte should be version
    try std.testing.expectEqual(VersionedData.VERSION, bytes[0]);
}

test "size calculation" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    try std.testing.expectEqual(@as(usize, 8), @sizeOf(Point));

    const point = Point{ .x = 0, .y = 0 };
    const bytes = structToBytes(Point, &point);

    try std.testing.expectEqual(@sizeOf(Point), bytes.len);
}
```

### Discussion

### Binary Serialization with std.mem

Convert structs to byte slices:

```zig
pub fn structToBytes(comptime T: type, value: *const T) []const u8 {
    return std.mem.asBytes(value);
}

pub fn bytesToStruct(comptime T: type, bytes: []const u8) !T {
    if (bytes.len != @sizeOf(T)) {
        return error.InvalidSize;
    }

    var value: T = undefined;
    @memcpy(std.mem.asBytes(&value), bytes);
    return value;
}

test "struct to bytes" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    const point = Point{ .x = 10, .y = 20 };
    const bytes = structToBytes(Point, &point);

    try std.testing.expectEqual(@sizeOf(Point), bytes.len);

    const restored = try bytesToStruct(Point, bytes);
    try std.testing.expectEqual(point.x, restored.x);
    try std.testing.expectEqual(point.y, restored.y);
}
```

### Packed Structs for Binary Layouts

Control memory layout:

```zig
pub const PackedData = packed struct {
    flags: u8,
    value: u16,
    id: u32,
};

pub fn serializePacked(data: PackedData) [@sizeOf(PackedData)]u8 {
    return @bitCast(data);
}

pub fn deserializePacked(bytes: [@sizeOf(PackedData)]u8) PackedData {
    return @bitCast(bytes);
}

test "packed struct serialization" {
    const data = PackedData{
        .flags = 0xFF,
        .value = 0x1234,
        .id = 0xDEADBEEF,
    };

    const bytes = serializePacked(data);
    const restored = deserializePacked(bytes);

    try std.testing.expectEqual(data.flags, restored.flags);
    try std.testing.expectEqual(data.value, restored.value);
    try std.testing.expectEqual(data.id, restored.id);
}
```

### Endianness Handling

Handle byte order:

```zig
pub fn serializeInt(comptime T: type, value: T, endian: std.builtin.Endian) [@sizeOf(T)]u8 {
    var bytes: [@sizeOf(T)]u8 = undefined;
    std.mem.writeInt(T, &bytes, value, endian);
    return bytes;
}

pub fn deserializeInt(comptime T: type, bytes: *const [@sizeOf(T)]u8, endian: std.builtin.Endian) T {
    return std.mem.readInt(T, bytes, endian);
}

test "endianness handling" {
    const value: u32 = 0x12345678;

    const be_bytes = serializeInt(u32, value, .big);
    const le_bytes = serializeInt(u32, value, .little);

    try std.testing.expectEqual(value, deserializeInt(u32, &be_bytes, .big));
    try std.testing.expectEqual(value, deserializeInt(u32, &le_bytes, .little));

    // Big endian puts most significant byte first
    try std.testing.expectEqual(@as(u8, 0x12), be_bytes[0]);
    try std.testing.expectEqual(@as(u8, 0x78), le_bytes[0]);
}
```

### JSON Serialization

Use `std.json` for text-based serialization:

```zig
const User = struct {
    id: u32,
    name: []const u8,
    active: bool,
};

pub fn serializeToJson(allocator: std.mem.Allocator, user: User) ![]u8 {
    return std.json.stringifyAlloc(allocator, user, .{});
}

pub fn deserializeFromJson(allocator: std.mem.Allocator, json: []const u8) !User {
    const parsed = try std.json.parseFromSlice(User, allocator, json, .{});
    defer parsed.deinit();

    return User{
        .id = parsed.value.id,
        .name = try allocator.dupe(u8, parsed.value.name),
        .active = parsed.value.active,
    };
}

test "JSON serialization" {
    const allocator = std.testing.allocator;

    const user = User{
        .id = 42,
        .name = "Alice",
        .active = true,
    };

    const json = try serializeToJson(allocator, user);
    defer allocator.free(json);

    const restored = try deserializeFromJson(allocator, json);
    defer allocator.free(restored.name);

    try std.testing.expectEqual(user.id, restored.id);
    try std.testing.expectEqualStrings(user.name, restored.name);
    try std.testing.expectEqual(user.active, restored.active);
}
```

### Writing Multiple Structs

Serialize arrays of structs:

```zig
pub fn writeStructArray(comptime T: type, file: std.fs.File, items: []const T) !void {
    // Write count first
    const count: u32 = @intCast(items.len);
    try file.writeInt(u32, count, .little);

    // Write each struct
    for (items) |item| {
        const bytes = std.mem.asBytes(&item);
        try file.writeAll(bytes);
    }
}

pub fn readStructArray(comptime T: type, allocator: std.mem.Allocator, file: std.fs.File) ![]T {
    // Read count
    const count = try file.readInt(u32, .little);

    // Allocate array
    const items = try allocator.alloc(T, count);
    errdefer allocator.free(items);

    // Read each struct
    for (items) |*item| {
        const bytes = std.mem.asBytes(item);
        const n = try file.readAll(bytes);
        if (n != bytes.len) {
            return error.UnexpectedEof;
        }
    }

    return items;
}

test "struct array serialization" {
    const allocator = std.testing.allocator;

    const Point = struct {
        x: i32,
        y: i32,
    };

    const points = [_]Point{
        .{ .x = 1, .y = 2 },
        .{ .x = 3, .y = 4 },
        .{ .x = 5, .y = 6 },
    };

    const file = try std.fs.cwd().createFile("/tmp/points.bin", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/points.bin") catch {};

    try writeStructArray(Point, file, &points);

    try file.seekTo(0);
    const loaded = try readStructArray(Point, allocator, file);
    defer allocator.free(loaded);

    try std.testing.expectEqual(points.len, loaded.len);
    for (points, loaded) |original, restored| {
        try std.testing.expectEqual(original.x, restored.x);
        try std.testing.expectEqual(original.y, restored.y);
    }
}
```

### Custom Serialization

Implement custom serialize/deserialize:

```zig
const CustomData = struct {
    version: u8,
    data: []const u8,

    pub fn serialize(self: CustomData, allocator: std.mem.Allocator) ![]u8 {
        var list = std.ArrayList(u8){};
        errdefer list.deinit(allocator);

        // Write version
        try list.append(allocator, self.version);

        // Write data length
        const len: u32 = @intCast(self.data.len);
        var len_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &len_bytes, len, .little);
        try list.appendSlice(allocator, &len_bytes);

        // Write data
        try list.appendSlice(allocator, self.data);

        return list.toOwnedSlice(allocator);
    }

    pub fn deserialize(allocator: std.mem.Allocator, bytes: []const u8) !CustomData {
        if (bytes.len < 5) {
            return error.InvalidData;
        }

        const version = bytes[0];
        const len = std.mem.readInt(u32, bytes[1..5][0..4], .little);

        if (bytes.len < 5 + len) {
            return error.InvalidData;
        }

        const data = try allocator.dupe(u8, bytes[5 .. 5 + len]);

        return CustomData{
            .version = version,
            .data = data,
        };
    }
};

test "custom serialization" {
    const allocator = std.testing.allocator;

    const original = CustomData{
        .version = 1,
        .data = "Hello, World!",
    };

    const bytes = try original.serialize(allocator);
    defer allocator.free(bytes);

    const restored = try CustomData.deserialize(allocator, bytes);
    defer allocator.free(restored.data);

    try std.testing.expectEqual(original.version, restored.version);
    try std.testing.expectEqualStrings(original.data, restored.data);
}
```

### Versioned Serialization

Handle format versioning:

```zig
const VersionedData = struct {
    const VERSION: u8 = 2;

    id: u32,
    name: []const u8,
    extra: ?[]const u8, // Added in version 2

    pub fn serialize(self: VersionedData, allocator: std.mem.Allocator) ![]u8 {
        var list = std.ArrayList(u8){};
        errdefer list.deinit(allocator);

        // Write version
        try list.append(allocator, VERSION);

        // Write ID
        var id_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &id_bytes, self.id, .little);
        try list.appendSlice(allocator, &id_bytes);

        // Write name length and data
        const name_len: u32 = @intCast(self.name.len);
        var name_len_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &name_len_bytes, name_len, .little);
        try list.appendSlice(allocator, &name_len_bytes);
        try list.appendSlice(allocator, self.name);

        // Write extra (version 2+)
        if (self.extra) |extra| {
            try list.append(allocator, 1); // Has extra
            const extra_len: u32 = @intCast(extra.len);
            var extra_len_bytes: [4]u8 = undefined;
            std.mem.writeInt(u32, &extra_len_bytes, extra_len, .little);
            try list.appendSlice(allocator, &extra_len_bytes);
            try list.appendSlice(allocator, extra);
        } else {
            try list.append(allocator, 0); // No extra
        }

        return list.toOwnedSlice(allocator);
    }

    pub fn deserialize(allocator: std.mem.Allocator, bytes: []const u8) !VersionedData {
        var pos: usize = 0;

        const version = bytes[pos];
        pos += 1;

        const id = std.mem.readInt(u32, bytes[pos..][0..4], .little);
        pos += 4;

        const name_len = std.mem.readInt(u32, bytes[pos..][0..4], .little);
        pos += 4;

        const name = try allocator.dupe(u8, bytes[pos .. pos + name_len]);
        errdefer allocator.free(name);
        pos += name_len;

        var extra: ?[]const u8 = null;
        if (version >= 2) {
            const has_extra = bytes[pos];
            pos += 1;

            if (has_extra == 1) {
                const extra_len = std.mem.readInt(u32, bytes[pos..][0..4], .little);
                pos += 4;

                extra = try allocator.dupe(u8, bytes[pos .. pos + extra_len]);
            }
        }

        return VersionedData{
            .id = id,
            .name = name,
            .extra = extra,
        };
    }
};

test "versioned serialization" {
    const allocator = std.testing.allocator;

    const data = VersionedData{
        .id = 123,
        .name = "Test",
        .extra = "Extra data",
    };

    const bytes = try data.serialize(allocator);
    defer allocator.free(bytes);

    const restored = try VersionedData.deserialize(allocator, bytes);
    defer allocator.free(restored.name);
    defer if (restored.extra) |extra| allocator.free(extra);

    try std.testing.expectEqual(data.id, restored.id);
    try std.testing.expectEqualStrings(data.name, restored.name);
    try std.testing.expectEqualStrings(data.extra.?, restored.extra.?);
}
```

### Best Practices

**Binary format:**
- Use packed structs for exact control
- Handle endianness explicitly for portability
- Document struct alignment and padding
- Include version numbers in formats

**Memory management:**
```zig
const Data = struct {
    allocator: std.mem.Allocator,
    items: []Item,

    pub fn deinit(self: *Data) void {
        self.allocator.free(self.items);
    }
};
```

**Error handling:**
- Validate data before deserializing
- Check buffer sizes
- Handle version mismatches gracefully
- Use `errdefer` for cleanup on errors

**Performance:**
- Use `@bitCast` for simple types
- Avoid allocations in hot paths
- Consider using fixed-size buffers
- Profile serialization overhead

### Related Functions

- `std.mem.asBytes()` - Convert value to byte slice
- `std.mem.bytesAsValue()` - Convert bytes to value
- `std.mem.readInt()` - Read integer with endianness
- `std.mem.writeInt()` - Write integer with endianness
- `std.json.stringify()` - Serialize to JSON
- `std.json.parseFromSlice()` - Parse JSON
- `@bitCast()` - Reinterpret bits as different type
- `@sizeOf()` - Get type size in bytes

### Full Tested Code

```zig
const std = @import("std");

/// Simple struct for testing
const Person = struct {
    age: u32,
    height: f32,
    name: [20]u8,
};

/// Serialize struct to file
pub fn serializeToDisk(file: std.fs.File, person: Person) !void {
    const bytes = std.mem.asBytes(&person);
    try file.writeAll(bytes);
}

/// Deserialize struct from file
pub fn deserializeFromDisk(file: std.fs.File) !Person {
    var person: Person = undefined;
    const bytes = std.mem.asBytes(&person);
    const n = try file.readAll(bytes);

    if (n != bytes.len) {
        return error.UnexpectedEof;
    }

    return person;
}

/// Convert struct to byte slice
pub fn structToBytes(comptime T: type, value: *const T) []const u8 {
    return std.mem.asBytes(value);
}

/// Convert bytes to struct
pub fn bytesToStruct(comptime T: type, bytes: []const u8) !T {
    if (bytes.len != @sizeOf(T)) {
        return error.InvalidSize;
    }

    var value: T = undefined;
    @memcpy(std.mem.asBytes(&value), bytes);
    return value;
}

/// Packed struct for binary layouts
pub const PackedData = packed struct {
    flags: u8,
    value: u16,
    id: u32,
};

/// Serialize packed struct
pub fn serializePacked(data: PackedData) [@sizeOf(PackedData)]u8 {
    var bytes: [@sizeOf(PackedData)]u8 = undefined;
    @memcpy(std.mem.asBytes(&bytes), std.mem.asBytes(&data));
    return bytes;
}

/// Deserialize packed struct
pub fn deserializePacked(bytes: [@sizeOf(PackedData)]u8) PackedData {
    var data: PackedData = undefined;
    @memcpy(std.mem.asBytes(&data), std.mem.asBytes(&bytes));
    return data;
}

/// Serialize integer with endianness
pub fn serializeInt(comptime T: type, value: T, endian: std.builtin.Endian) [@sizeOf(T)]u8 {
    var bytes: [@sizeOf(T)]u8 = undefined;
    std.mem.writeInt(T, &bytes, value, endian);
    return bytes;
}

/// Deserialize integer with endianness
pub fn deserializeInt(comptime T: type, bytes: *const [@sizeOf(T)]u8, endian: std.builtin.Endian) T {
    return std.mem.readInt(T, bytes, endian);
}

/// User struct for JSON serialization
const User = struct {
    id: u32,
    name: []const u8,
    active: bool,
};

/// Serialize to JSON (manual implementation for Zig 0.15.2)
pub fn serializeToJson(allocator: std.mem.Allocator, user: User) ![]u8 {
    return std.fmt.allocPrint(allocator,
        \\{{"id":{d},"name":"{s}","active":{s}}}
    , .{ user.id, user.name, if (user.active) "true" else "false" });
}

/// Deserialize from JSON
pub fn deserializeFromJson(allocator: std.mem.Allocator, json: []const u8) !User {
    const parsed = try std.json.parseFromSlice(User, allocator, json, .{});
    defer parsed.deinit();

    return User{
        .id = parsed.value.id,
        .name = try allocator.dupe(u8, parsed.value.name),
        .active = parsed.value.active,
    };
}

/// Write array of structs to file
pub fn writeStructArray(comptime T: type, file: std.fs.File, items: []const T) !void {
    // Write count first
    const count: u32 = @intCast(items.len);
    var count_bytes: [4]u8 = undefined;
    std.mem.writeInt(u32, &count_bytes, count, .little);
    try file.writeAll(&count_bytes);

    // Write each struct
    for (items) |item| {
        const bytes = std.mem.asBytes(&item);
        try file.writeAll(bytes);
    }
}

/// Read array of structs from file
pub fn readStructArray(comptime T: type, allocator: std.mem.Allocator, file: std.fs.File) ![]T {
    // Read count
    var count_bytes: [4]u8 = undefined;
    const n = try file.readAll(&count_bytes);
    if (n != 4) {
        return error.UnexpectedEof;
    }
    const count = std.mem.readInt(u32, &count_bytes, .little);

    // Allocate array
    const items = try allocator.alloc(T, count);
    errdefer allocator.free(items);

    // Read each struct
    for (items) |*item| {
        const bytes = std.mem.asBytes(item);
        const bytes_read = try file.readAll(bytes);
        if (bytes_read != bytes.len) {
            return error.UnexpectedEof;
        }
    }

    return items;
}

/// Custom data with custom serialization
const CustomData = struct {
    version: u8,
    data: []const u8,

    pub fn serialize(self: CustomData, allocator: std.mem.Allocator) ![]u8 {
        var list = std.ArrayList(u8){};
        errdefer list.deinit(allocator);

        // Write version
        try list.append(allocator, self.version);

        // Write data length
        const len: u32 = @intCast(self.data.len);
        var len_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &len_bytes, len, .little);
        try list.appendSlice(allocator, &len_bytes);

        // Write data
        try list.appendSlice(allocator, self.data);

        return list.toOwnedSlice(allocator);
    }

    pub fn deserialize(allocator: std.mem.Allocator, bytes: []const u8) !CustomData {
        if (bytes.len < 5) {
            return error.InvalidData;
        }

        const version = bytes[0];
        const len = std.mem.readInt(u32, bytes[1..5][0..4], .little);

        if (bytes.len < 5 + len) {
            return error.InvalidData;
        }

        const data = try allocator.dupe(u8, bytes[5 .. 5 + len]);

        return CustomData{
            .version = version,
            .data = data,
        };
    }
};

/// Versioned data structure
const VersionedData = struct {
    const VERSION: u8 = 2;

    id: u32,
    name: []const u8,
    extra: ?[]const u8, // Added in version 2

    pub fn serialize(self: VersionedData, allocator: std.mem.Allocator) ![]u8 {
        var list = std.ArrayList(u8){};
        errdefer list.deinit(allocator);

        // Write version
        try list.append(allocator, VERSION);

        // Write ID
        var id_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &id_bytes, self.id, .little);
        try list.appendSlice(allocator, &id_bytes);

        // Write name length and data
        const name_len: u32 = @intCast(self.name.len);
        var name_len_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &name_len_bytes, name_len, .little);
        try list.appendSlice(allocator, &name_len_bytes);
        try list.appendSlice(allocator, self.name);

        // Write extra (version 2+)
        if (self.extra) |extra| {
            try list.append(allocator, 1); // Has extra
            const extra_len: u32 = @intCast(extra.len);
            var extra_len_bytes: [4]u8 = undefined;
            std.mem.writeInt(u32, &extra_len_bytes, extra_len, .little);
            try list.appendSlice(allocator, &extra_len_bytes);
            try list.appendSlice(allocator, extra);
        } else {
            try list.append(allocator, 0); // No extra
        }

        return list.toOwnedSlice(allocator);
    }

    pub fn deserialize(allocator: std.mem.Allocator, bytes: []const u8) !VersionedData {
        var pos: usize = 0;

        const version = bytes[pos];
        pos += 1;

        const id = std.mem.readInt(u32, bytes[pos..][0..4], .little);
        pos += 4;

        const name_len = std.mem.readInt(u32, bytes[pos..][0..4], .little);
        pos += 4;

        const name = try allocator.dupe(u8, bytes[pos .. pos + name_len]);
        errdefer allocator.free(name);
        pos += name_len;

        var extra: ?[]const u8 = null;
        if (version >= 2) {
            const has_extra = bytes[pos];
            pos += 1;

            if (has_extra == 1) {
                const extra_len = std.mem.readInt(u32, bytes[pos..][0..4], .little);
                pos += 4;

                extra = try allocator.dupe(u8, bytes[pos .. pos + extra_len]);
            }
        }

        return VersionedData{
            .id = id,
            .name = name,
            .extra = extra,
        };
    }
};

// Tests

// ANCHOR: basic_serialization
test "serialize to disk" {
    var person = Person{
        .age = 30,
        .height = 1.75,
        .name = undefined,
    };
    @memcpy(&person.name, "Alice" ++ ([_]u8{0} ** 15));

    const file = try std.fs.cwd().createFile("/tmp/person.bin", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/person.bin") catch {};

    try serializeToDisk(file, person);

    try file.seekTo(0);
    const loaded = try deserializeFromDisk(file);

    try std.testing.expectEqual(person.age, loaded.age);
    try std.testing.expectEqual(person.height, loaded.height);
}

test "struct to bytes" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    const point = Point{ .x = 10, .y = 20 };
    const bytes = structToBytes(Point, &point);

    try std.testing.expectEqual(@sizeOf(Point), bytes.len);

    const restored = try bytesToStruct(Point, bytes);
    try std.testing.expectEqual(point.x, restored.x);
    try std.testing.expectEqual(point.y, restored.y);
}

test "bytes to struct size validation" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    const bad_bytes = [_]u8{1} ** 4; // Too small
    const result = bytesToStruct(Point, &bad_bytes);

    try std.testing.expectError(error.InvalidSize, result);
}

test "packed struct serialization" {
    const data = PackedData{
        .flags = 0xFF,
        .value = 0x1234,
        .id = 0xDEADBEEF,
    };

    const bytes = serializePacked(data);
    const restored = deserializePacked(bytes);

    try std.testing.expectEqual(data.flags, restored.flags);
    try std.testing.expectEqual(data.value, restored.value);
    try std.testing.expectEqual(data.id, restored.id);
}

test "packed struct size" {
    // Note: @sizeOf returns alignment-adjusted size (8), @bitSizeOf returns 56 (7 bytes)
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(PackedData));
    try std.testing.expectEqual(@as(usize, 56), @bitSizeOf(PackedData));
}
// ANCHOR_END: basic_serialization

test "endianness handling" {
    const value: u32 = 0x12345678;

    const be_bytes = serializeInt(u32, value, .big);
    const le_bytes = serializeInt(u32, value, .little);

    try std.testing.expectEqual(value, deserializeInt(u32, &be_bytes, .big));
    try std.testing.expectEqual(value, deserializeInt(u32, &le_bytes, .little));

    // Big endian puts most significant byte first
    try std.testing.expectEqual(@as(u8, 0x12), be_bytes[0]);
    try std.testing.expectEqual(@as(u8, 0x78), le_bytes[0]);
}

// ANCHOR: endianness_handling
test "endianness different values" {
    const value: u16 = 0xABCD;

    const be_bytes = serializeInt(u16, value, .big);
    const le_bytes = serializeInt(u16, value, .little);

    try std.testing.expectEqual(@as(u8, 0xAB), be_bytes[0]);
    try std.testing.expectEqual(@as(u8, 0xCD), be_bytes[1]);
    try std.testing.expectEqual(@as(u8, 0xCD), le_bytes[0]);
    try std.testing.expectEqual(@as(u8, 0xAB), le_bytes[1]);
}

test "JSON serialization" {
    const allocator = std.testing.allocator;

    const user = User{
        .id = 42,
        .name = "Alice",
        .active = true,
    };

    const json = try serializeToJson(allocator, user);
    defer allocator.free(json);

    const restored = try deserializeFromJson(allocator, json);
    defer allocator.free(restored.name);

    try std.testing.expectEqual(user.id, restored.id);
    try std.testing.expectEqualStrings(user.name, restored.name);
    try std.testing.expectEqual(user.active, restored.active);
}

test "JSON contains expected fields" {
    const allocator = std.testing.allocator;

    const user = User{
        .id = 123,
        .name = "Bob",
        .active = false,
    };

    const json = try serializeToJson(allocator, user);
    defer allocator.free(json);

    // Verify JSON contains expected data
    try std.testing.expect(std.mem.indexOf(u8, json, "123") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "Bob") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "false") != null);
}
// ANCHOR_END: endianness_handling

// ANCHOR: array_serialization
test "struct array serialization" {
    const allocator = std.testing.allocator;

    const Point = struct {
        x: i32,
        y: i32,
    };

    const points = [_]Point{
        .{ .x = 1, .y = 2 },
        .{ .x = 3, .y = 4 },
        .{ .x = 5, .y = 6 },
    };

    const file = try std.fs.cwd().createFile("/tmp/points.bin", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/points.bin") catch {};

    try writeStructArray(Point, file, &points);

    try file.seekTo(0);
    const loaded = try readStructArray(Point, allocator, file);
    defer allocator.free(loaded);

    try std.testing.expectEqual(points.len, loaded.len);
    for (points, loaded) |original, restored| {
        try std.testing.expectEqual(original.x, restored.x);
        try std.testing.expectEqual(original.y, restored.y);
    }
}

test "empty struct array" {
    const allocator = std.testing.allocator;

    const Point = struct {
        x: i32,
        y: i32,
    };

    const points: []const Point = &.{};

    const file = try std.fs.cwd().createFile("/tmp/empty_points.bin", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/empty_points.bin") catch {};

    try writeStructArray(Point, file, points);

    try file.seekTo(0);
    const loaded = try readStructArray(Point, allocator, file);
    defer allocator.free(loaded);

    try std.testing.expectEqual(@as(usize, 0), loaded.len);
}
// ANCHOR_END: array_serialization

// ANCHOR: custom_serialization
test "custom serialization" {
    const allocator = std.testing.allocator;

    const original = CustomData{
        .version = 1,
        .data = "Hello, World!",
    };

    const bytes = try original.serialize(allocator);
    defer allocator.free(bytes);

    const restored = try CustomData.deserialize(allocator, bytes);
    defer allocator.free(restored.data);

    try std.testing.expectEqual(original.version, restored.version);
    try std.testing.expectEqualStrings(original.data, restored.data);
}

test "custom serialization empty data" {
    const allocator = std.testing.allocator;

    const original = CustomData{
        .version = 5,
        .data = "",
    };

    const bytes = try original.serialize(allocator);
    defer allocator.free(bytes);

    const restored = try CustomData.deserialize(allocator, bytes);
    defer allocator.free(restored.data);

    try std.testing.expectEqual(original.version, restored.version);
    try std.testing.expectEqual(@as(usize, 0), restored.data.len);
}

test "custom deserialization invalid data" {
    const allocator = std.testing.allocator;

    const bad_bytes = [_]u8{1} ** 3; // Too small
    const result = CustomData.deserialize(allocator, &bad_bytes);

    try std.testing.expectError(error.InvalidData, result);
}

test "versioned serialization" {
    const allocator = std.testing.allocator;

    const data = VersionedData{
        .id = 123,
        .name = "Test",
        .extra = "Extra data",
    };

    const bytes = try data.serialize(allocator);
    defer allocator.free(bytes);

    const restored = try VersionedData.deserialize(allocator, bytes);
    defer allocator.free(restored.name);
    defer if (restored.extra) |extra| allocator.free(extra);

    try std.testing.expectEqual(data.id, restored.id);
    try std.testing.expectEqualStrings(data.name, restored.name);
    try std.testing.expectEqualStrings(data.extra.?, restored.extra.?);
}

test "versioned serialization without extra" {
    const allocator = std.testing.allocator;

    const data = VersionedData{
        .id = 456,
        .name = "NoExtra",
        .extra = null,
    };

    const bytes = try data.serialize(allocator);
    defer allocator.free(bytes);

    const restored = try VersionedData.deserialize(allocator, bytes);
    defer allocator.free(restored.name);

    try std.testing.expectEqual(data.id, restored.id);
    try std.testing.expectEqualStrings(data.name, restored.name);
    try std.testing.expectEqual(@as(?[]const u8, null), restored.extra);
}

test "versioned data includes version" {
    const allocator = std.testing.allocator;

    const data = VersionedData{
        .id = 789,
        .name = "Versioned",
        .extra = "Data",
    };

    const bytes = try data.serialize(allocator);
    defer allocator.free(bytes);

    // First byte should be version
    try std.testing.expectEqual(VersionedData.VERSION, bytes[0]);
}

test "size calculation" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    try std.testing.expectEqual(@as(usize, 8), @sizeOf(Point));

    const point = Point{ .x = 0, .y = 0 };
    const bytes = structToBytes(Point, &point);

    try std.testing.expectEqual(@sizeOf(Point), bytes.len);
}
// ANCHOR_END: custom_serialization
```

---
