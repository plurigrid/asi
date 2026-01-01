# Data Encoding (CSV, JSON, XML) Recipes

*9 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [6.1](#recipe-6-1) | Reading and Writing CSV Data | intermediate |
| [6.2](#recipe-6-2) | Reading and Writing JSON Data | intermediate |
| [6.3](#recipe-6-3) | Parsing Simple XML Data | intermediate |
| [6.4](#recipe-6-4) | Parsing and Modifying XML | intermediate |
| [6.5](#recipe-6-5) | Turning a Dictionary into XML | intermediate |
| [6.6](#recipe-6-6) | Interacting with a Relational Database | intermediate |
| [6.7](#recipe-6-7) | Decoding and Encoding Hexadecimal Digits | intermediate |
| [6.8](#recipe-6-8) | Decoding and Encoding Base64 | intermediate |
| [6.9](#recipe-6-9) | Reading and Writing Binary Arrays of Structures | intermediate |

---

## Recipe 6.1: Reading and Writing CSV Data {#recipe-6-1}

**Tags:** allocators, arraylist, comptime, csv, data-encoding, data-structures, error-handling, memory, parsing, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/06-data-encoding/recipe_6_1.zig`

### Problem

You need to read and write CSV (Comma-Separated Values) files, handling quoted fields, commas within fields, and newlines properly.

### Solution

### CSV Writer

```zig
/// CSV Writer
pub const CsvWriter = struct {
    writer: std.io.AnyWriter,
    delimiter: u8 = ',',

    pub fn init(writer: std.io.AnyWriter) CsvWriter {
        return .{ .writer = writer };
    }

    pub fn writeRow(self: *CsvWriter, fields: []const []const u8) !void {
        for (fields, 0..) |field, i| {
            if (i > 0) try self.writer.writeByte(self.delimiter);
            try self.writeField(field);
        }
        try self.writer.writeByte('\n');
    }

    fn writeField(self: *CsvWriter, field: []const u8) !void {
        const needs_quotes = blk: {
            for (field) |c| {
                if (c == self.delimiter or c == '"' or c == '\n' or c == '\r') {
                    break :blk true;
                }
            }
            break :blk false;
        };

        if (needs_quotes) {
            try self.writer.writeByte('"');
            for (field) |c| {
                if (c == '"') try self.writer.writeByte('"');
                try self.writer.writeByte(c);
            }
            try self.writer.writeByte('"');
        } else {
            try self.writer.writeAll(field);
        }
    }

    pub fn writeHeader(self: *CsvWriter, headers: []const []const u8) !void {
        try self.writeRow(headers);
    }
};
```

### CSV Reader

```zig
/// CSV Reader
pub const CsvReader = struct {
    allocator: std.mem.Allocator,
    reader: std.io.AnyReader,
    delimiter: u8 = ',',
    buffer: std.ArrayList(u8),

    pub fn init(allocator: std.mem.Allocator, reader: std.io.AnyReader) CsvReader {
        return .{
            .allocator = allocator,
            .reader = reader,
            .buffer = .{},
        };
    }

    pub fn deinit(self: *CsvReader) void {
        self.buffer.deinit(self.allocator);
    }

    pub fn readRow(self: *CsvReader, allocator: std.mem.Allocator) !?[][]u8 {
        var fields: std.ArrayList([]u8) = .{};
        errdefer {
            for (fields.items) |field| allocator.free(field);
            fields.deinit(allocator);
        }

        var in_quotes = false;
        var field_start: usize = 0;
        self.buffer.clearRetainingCapacity();

        while (true) {
            const byte = self.reader.readByte() catch |err| switch (err) {
                error.EndOfStream => {
                    if (self.buffer.items.len > 0 or fields.items.len > 0) {
                        const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                        try fields.append(allocator, field);
                        return try fields.toOwnedSlice(allocator);
                    }
                    return null;
                },
                else => return err,
            };

            if (in_quotes) {
                if (byte == '"') {
                    const next = self.reader.readByte() catch |err| switch (err) {
                        error.EndOfStream => {
                            in_quotes = false;
                            continue;
                        },
                        else => return err,
                    };

                    if (next == '"') {
                        try self.buffer.append(self.allocator, '"');
                    } else {
                        in_quotes = false;
                        if (next == self.delimiter) {
                            const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                            try fields.append(allocator, field);
                            self.buffer.clearRetainingCapacity();
                            field_start = 0;
                        } else if (next == '\n') {
                            const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                            try fields.append(allocator, field);
                            return try fields.toOwnedSlice(allocator);
                        } else if (next != '\r') {
                            try self.buffer.append(self.allocator, next);
                        }
                    }
                } else {
                    try self.buffer.append(self.allocator, byte);
                }
            } else {
                if (byte == '"' and self.buffer.items.len == field_start) {
                    in_quotes = true;
                } else if (byte == self.delimiter) {
                    const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                    try fields.append(allocator, field);
                    self.buffer.clearRetainingCapacity();
                    field_start = 0;
                } else if (byte == '\n') {
                    const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                    try fields.append(allocator, field);
                    return try fields.toOwnedSlice(allocator);
                } else if (byte != '\r') {
                    try self.buffer.append(self.allocator, byte);
                }
            }
        }
    }
};
```

### TSV Variant

```zig
/// Write TSV (tab-separated values)
pub fn writeTsv(writer: std.io.AnyWriter, rows: []const []const []const u8) !void {
    var csv = CsvWriter.init(writer);
    csv.delimiter = '\t';

    for (rows) |row| {
        try csv.writeRow(row);
    }
}
```

### Discussion

### CSV Format Basics

CSV files store tabular data in plain text:
- Fields separated by commas
- Records (rows) separated by newlines
- Fields containing commas, quotes, or newlines must be quoted
- Quotes within quoted fields are escaped by doubling them

### Writing CSV Files

Basic CSV writer implementation:

```zig
pub const CsvWriter = struct {
    writer: std.io.AnyWriter,
    delimiter: u8 = ',',

    pub fn init(writer: std.io.AnyWriter) CsvWriter {
        return .{ .writer = writer };
    }

    pub fn writeRow(self: *CsvWriter, fields: []const []const u8) !void {
        for (fields, 0..) |field, i| {
            if (i > 0) try self.writer.writeByte(self.delimiter);
            try self.writeField(field);
        }
        try self.writer.writeByte('\n');
    }

    fn writeField(self: *CsvWriter, field: []const u8) !void {
        const needs_quotes = blk: {
            for (field) |c| {
                if (c == self.delimiter or c == '"' or c == '\n' or c == '\r') {
                    break :blk true;
                }
            }
            break :blk false;
        };

        if (needs_quotes) {
            try self.writer.writeByte('"');
            for (field) |c| {
                if (c == '"') try self.writer.writeByte('"'); // Escape quotes
                try self.writer.writeByte(c);
            }
            try self.writer.writeByte('"');
        } else {
            try self.writer.writeAll(field);
        }
    }

    pub fn writeHeader(self: *CsvWriter, headers: []const []const u8) !void {
        try self.writeRow(headers);
    }
};
```

### Reading CSV Files

CSV reader with proper parsing:

```zig
pub const CsvReader = struct {
    allocator: std.mem.Allocator,
    reader: std.io.AnyReader,
    delimiter: u8 = ',',
    buffer: std.ArrayList(u8),

    pub fn init(allocator: std.mem.Allocator, reader: std.io.AnyReader) CsvReader {
        return .{
            .allocator = allocator,
            .reader = reader,
            .buffer = std.ArrayList(u8).init(allocator),
        };
    }

    pub fn deinit(self: *CsvReader) void {
        self.buffer.deinit();
    }

    pub fn readRow(self: *CsvReader, allocator: std.mem.Allocator) !?[][]u8 {
        var fields: std.ArrayList([]u8) = .{};
        errdefer {
            for (fields.items) |field| allocator.free(field);
            fields.deinit(allocator);
        }

        var in_quotes = false;
        var field_start: usize = 0;
        self.buffer.clearRetainingCapacity();

        while (true) {
            const byte = self.reader.readByte() catch |err| switch (err) {
                error.EndOfStream => {
                    if (self.buffer.items.len > 0 or fields.items.len > 0) {
                        const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                        try fields.append(allocator, field);
                        return try fields.toOwnedSlice(allocator);
                    }
                    return null;
                },
                else => return err,
            };

            if (in_quotes) {
                if (byte == '"') {
                    // Check for escaped quote
                    const next = self.reader.readByte() catch |err| switch (err) {
                        error.EndOfStream => {
                            in_quotes = false;
                            continue;
                        },
                        else => return err,
                    };

                    if (next == '"') {
                        try self.buffer.append(self.allocator, '"');
                    } else {
                        in_quotes = false;
                        // Put back the character
                        if (next == self.delimiter) {
                            const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                            try fields.append(allocator, field);
                            self.buffer.clearRetainingCapacity();
                            field_start = 0;
                        } else if (next == '\n') {
                            const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                            try fields.append(allocator, field);
                            return try fields.toOwnedSlice(allocator);
                        } else if (next != '\r') {
                            try self.buffer.append(self.allocator, next);
                        }
                    }
                } else {
                    try self.buffer.append(self.allocator, byte);
                }
            } else {
                if (byte == '"' and self.buffer.items.len == field_start) {
                    in_quotes = true;
                } else if (byte == self.delimiter) {
                    const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                    try fields.append(allocator, field);
                    self.buffer.clearRetainingCapacity();
                    field_start = 0;
                } else if (byte == '\n') {
                    const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                    try fields.append(allocator, field);
                    return try fields.toOwnedSlice(allocator);
                } else if (byte != '\r') {
                    try self.buffer.append(self.allocator, byte);
                }
            }
        }
    }
};
```

### Reading CSV with Headers

Parse CSV with header row:

```zig
pub fn readCsvWithHeaders(
    allocator: std.mem.Allocator,
    reader: std.io.AnyReader,
) !struct {
    headers: [][]u8,
    rows: [][][]u8,
} {
    var csv_reader = CsvReader.init(allocator, reader);
    defer csv_reader.deinit();

    // Read headers
    const headers = (try csv_reader.readRow(allocator)) orelse return error.EmptyFile;
    errdefer {
        for (headers) |h| allocator.free(h);
        allocator.free(headers);
    }

    // Read data rows
    var rows: std.ArrayList([][]u8) = .{};
    errdefer {
        for (rows.items) |row| {
            for (row) |field| allocator.free(field);
            allocator.free(row);
        }
        rows.deinit(allocator);
    }

    while (try csv_reader.readRow(allocator)) |row| {
        try rows.append(allocator, row);
    }

    return .{
        .headers = headers,
        .rows = try rows.toOwnedSlice(allocator),
    };
}
```

### Writing Structs as CSV

Convert structs to CSV rows:

```zig
pub fn writeStructs(
    comptime T: type,
    writer: std.io.AnyWriter,
    items: []const T,
    allocator: std.mem.Allocator,
) !void {
    var csv = CsvWriter.init(writer);

    // Write header from struct fields
    const fields = @typeInfo(T).Struct.fields;
    var headers: [fields.len][]const u8 = undefined;
    inline for (fields, 0..) |field, i| {
        headers[i] = field.name;
    }
    try csv.writeHeader(&headers);

    // Write rows
    for (items) |item| {
        var row: [fields.len][]u8 = undefined;
        inline for (fields, 0..) |field, i| {
            const value = @field(item, field.name);
            row[i] = try std.fmt.allocPrint(allocator, "{any}", .{value});
        }
        defer {
            inline for (&row) |r| allocator.free(r);
        }
        try csv.writeRow(&row);
    }
}
```

### Alternative Delimiter Support

Support TSV (tab-separated) and other formats:

```zig
pub fn writeTsv(writer: std.io.AnyWriter, rows: []const []const []const u8) !void {
    var csv = CsvWriter.init(writer);
    csv.delimiter = '\t';

    for (rows) |row| {
        try csv.writeRow(row);
    }
}
```

### Streaming Large CSV Files

Process CSV files without loading entire file into memory:

```zig
pub fn processLargeCsv(
    allocator: std.mem.Allocator,
    path: []const u8,
    processor: *const fn ([][]const u8) anyerror!void,
) !void {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    var reader_buffer: [8192]u8 = undefined;
    var file_reader = file.reader(&reader_buffer);

    var csv_reader = CsvReader.init(allocator, file_reader.any());
    defer csv_reader.deinit();

    while (try csv_reader.readRow(allocator)) |row| {
        defer {
            for (row) |field| allocator.free(field);
            allocator.free(row);
        }
        try processor(row);
    }
}
```

### Error Handling

Handle malformed CSV:

```zig
pub const CsvError = error{
    UnterminatedQuote,
    InvalidFormat,
    EmptyFile,
};

pub fn validateCsvRow(row: []const []const u8, expected_fields: usize) !void {
    if (row.len != expected_fields) {
        return error.InvalidFormat;
    }
}
```

### CSV Escaping Rules

The CSV escaping rules:
1. Fields containing delimiter, quote, or newline must be quoted
2. Quotes inside quoted fields are doubled (`""`)
3. Leading/trailing whitespace preserved in quoted fields
4. Empty fields represented as empty string

Examples:
```
Normal field          -> Normal field
Field, with comma     -> "Field, with comma"
Field with "quotes"   -> "Field with ""quotes"""
Field with
newline               -> "Field with
newline"
```

### Performance Tips

**Writing:**
- Use buffered writer for better performance
- Pre-allocate row arrays when possible
- Batch writes when generating many rows

**Reading:**
- Use buffered reader
- Process rows as you read (streaming)
- Reuse allocations where possible

**Memory:**
```zig
// Good: Process row by row
while (try csv.readRow(allocator)) |row| {
    defer {
        for (row) |field| allocator.free(field);
        allocator.free(row);
    }
    try processRow(row);
}

// Bad: Load entire file into memory
const all_rows = try readAllRows(allocator, reader);
defer freeAllRows(allocator, all_rows);
```

### Common Patterns

**Reading into structs:**
```zig
const Person = struct {
    name: []const u8,
    age: u32,
    city: []const u8,
};

pub fn parsePerson(row: []const []const u8) !Person {
    if (row.len != 3) return error.InvalidFormat;

    return .{
        .name = row[0],
        .age = try std.fmt.parseInt(u32, row[1], 10),
        .city = row[2],
    };
}
```

**Writing from database query results:**
```zig
pub fn exportQueryToCsv(
    query_results: []const QueryRow,
    writer: std.io.AnyWriter,
) !void {
    var csv = CsvWriter.init(writer);

    for (query_results) |result| {
        const row = [_][]const u8{
            result.column1,
            result.column2,
            result.column3,
        };
        try csv.writeRow(&row);
    }
}
```

### Unicode and Encoding

CSV files typically use UTF-8:
```zig
// Zig strings are UTF-8 by default, so this just works
try csv.writeRow(&.{ "Name", "Nom", "名前" });
```

For other encodings, you'd need to convert:
```zig
// Hypothetical: Convert from Latin-1 to UTF-8
const utf8_field = try convertLatin1ToUtf8(allocator, latin1_field);
defer allocator.free(utf8_field);
try csv.writeField(utf8_field);
```

### Related Formats

**TSV (Tab-Separated Values):**
- Same as CSV but uses tabs
- Less ambiguous (tabs rarely appear in data)
- Just set `delimiter = '\t'`

**RFC 4180 Compliance:**
- Standard CSV format specification
- Our implementation follows RFC 4180
- Handle CRLF vs LF line endings
- Optional header row

### Related Functions

- `std.mem.tokenizeAny()` - Simple field splitting
- `std.fmt.allocPrint()` - Format values as strings
- `std.io.AnyWriter` - Generic writer interface
- `std.io.AnyReader` - Generic reader interface
- `std.ArrayList` - Dynamic arrays

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: csv_writer
/// CSV Writer
pub const CsvWriter = struct {
    writer: std.io.AnyWriter,
    delimiter: u8 = ',',

    pub fn init(writer: std.io.AnyWriter) CsvWriter {
        return .{ .writer = writer };
    }

    pub fn writeRow(self: *CsvWriter, fields: []const []const u8) !void {
        for (fields, 0..) |field, i| {
            if (i > 0) try self.writer.writeByte(self.delimiter);
            try self.writeField(field);
        }
        try self.writer.writeByte('\n');
    }

    fn writeField(self: *CsvWriter, field: []const u8) !void {
        const needs_quotes = blk: {
            for (field) |c| {
                if (c == self.delimiter or c == '"' or c == '\n' or c == '\r') {
                    break :blk true;
                }
            }
            break :blk false;
        };

        if (needs_quotes) {
            try self.writer.writeByte('"');
            for (field) |c| {
                if (c == '"') try self.writer.writeByte('"');
                try self.writer.writeByte(c);
            }
            try self.writer.writeByte('"');
        } else {
            try self.writer.writeAll(field);
        }
    }

    pub fn writeHeader(self: *CsvWriter, headers: []const []const u8) !void {
        try self.writeRow(headers);
    }
};
// ANCHOR_END: csv_writer

// ANCHOR: csv_reader
/// CSV Reader
pub const CsvReader = struct {
    allocator: std.mem.Allocator,
    reader: std.io.AnyReader,
    delimiter: u8 = ',',
    buffer: std.ArrayList(u8),

    pub fn init(allocator: std.mem.Allocator, reader: std.io.AnyReader) CsvReader {
        return .{
            .allocator = allocator,
            .reader = reader,
            .buffer = .{},
        };
    }

    pub fn deinit(self: *CsvReader) void {
        self.buffer.deinit(self.allocator);
    }

    pub fn readRow(self: *CsvReader, allocator: std.mem.Allocator) !?[][]u8 {
        var fields: std.ArrayList([]u8) = .{};
        errdefer {
            for (fields.items) |field| allocator.free(field);
            fields.deinit(allocator);
        }

        var in_quotes = false;
        var field_start: usize = 0;
        self.buffer.clearRetainingCapacity();

        while (true) {
            const byte = self.reader.readByte() catch |err| switch (err) {
                error.EndOfStream => {
                    if (self.buffer.items.len > 0 or fields.items.len > 0) {
                        const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                        try fields.append(allocator, field);
                        return try fields.toOwnedSlice(allocator);
                    }
                    return null;
                },
                else => return err,
            };

            if (in_quotes) {
                if (byte == '"') {
                    const next = self.reader.readByte() catch |err| switch (err) {
                        error.EndOfStream => {
                            in_quotes = false;
                            continue;
                        },
                        else => return err,
                    };

                    if (next == '"') {
                        try self.buffer.append(self.allocator, '"');
                    } else {
                        in_quotes = false;
                        if (next == self.delimiter) {
                            const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                            try fields.append(allocator, field);
                            self.buffer.clearRetainingCapacity();
                            field_start = 0;
                        } else if (next == '\n') {
                            const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                            try fields.append(allocator, field);
                            return try fields.toOwnedSlice(allocator);
                        } else if (next != '\r') {
                            try self.buffer.append(self.allocator, next);
                        }
                    }
                } else {
                    try self.buffer.append(self.allocator, byte);
                }
            } else {
                if (byte == '"' and self.buffer.items.len == field_start) {
                    in_quotes = true;
                } else if (byte == self.delimiter) {
                    const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                    try fields.append(allocator, field);
                    self.buffer.clearRetainingCapacity();
                    field_start = 0;
                } else if (byte == '\n') {
                    const field = try allocator.dupe(u8, self.buffer.items[field_start..]);
                    try fields.append(allocator, field);
                    return try fields.toOwnedSlice(allocator);
                } else if (byte != '\r') {
                    try self.buffer.append(self.allocator, byte);
                }
            }
        }
    }
};
// ANCHOR_END: csv_reader

// ANCHOR: tsv_variant
/// Write TSV (tab-separated values)
pub fn writeTsv(writer: std.io.AnyWriter, rows: []const []const []const u8) !void {
    var csv = CsvWriter.init(writer);
    csv.delimiter = '\t';

    for (rows) |row| {
        try csv.writeRow(row);
    }
}
// ANCHOR_END: tsv_variant

// Tests

test "write simple csv" {
    var buffer: [1024]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    var csv = CsvWriter.init(stream.writer().any());

    try csv.writeRow(&.{ "Name", "Age", "City" });
    try csv.writeRow(&.{ "Alice", "30", "New York" });
    try csv.writeRow(&.{ "Bob", "25", "San Francisco" });

    const result = stream.getWritten();
    try std.testing.expectEqualStrings(
        "Name,Age,City\nAlice,30,New York\nBob,25,San Francisco\n",
        result,
    );
}

test "write csv with quotes" {
    var buffer: [1024]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    var csv = CsvWriter.init(stream.writer().any());

    try csv.writeRow(&.{ "Name", "Description" });
    try csv.writeRow(&.{ "Item", "Contains, comma" });

    const result = stream.getWritten();
    try std.testing.expectEqualStrings(
        "Name,Description\nItem,\"Contains, comma\"\n",
        result,
    );
}

test "write csv with escaped quotes" {
    var buffer: [1024]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    var csv = CsvWriter.init(stream.writer().any());

    try csv.writeRow(&.{ "Title", "Quote" });
    try csv.writeRow(&.{ "Book", "He said \"Hello\"" });

    const result = stream.getWritten();
    try std.testing.expectEqualStrings(
        "Title,Quote\nBook,\"He said \"\"Hello\"\"\"\n",
        result,
    );
}

test "write csv with newlines" {
    var buffer: [1024]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    var csv = CsvWriter.init(stream.writer().any());

    try csv.writeRow(&.{ "Field", "Value" });
    try csv.writeRow(&.{ "Multi", "Line\nValue" });

    const result = stream.getWritten();
    try std.testing.expectEqualStrings(
        "Field,Value\nMulti,\"Line\nValue\"\n",
        result,
    );
}

test "write empty fields" {
    var buffer: [1024]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    var csv = CsvWriter.init(stream.writer().any());

    try csv.writeRow(&.{ "A", "", "C" });
    try csv.writeRow(&.{ "", "B", "" });

    const result = stream.getWritten();
    try std.testing.expectEqualStrings(
        "A,,C\n,B,\n",
        result,
    );
}

test "read simple csv" {
    const data = "Name,Age,City\nAlice,30,New York\nBob,25,San Francisco\n";
    var stream = std.io.fixedBufferStream(data);

    const allocator = std.testing.allocator;
    var csv = CsvReader.init(allocator, stream.reader().any());
    defer csv.deinit();

    // Read header
    const header = (try csv.readRow(allocator)).?;
    defer {
        for (header) |field| allocator.free(field);
        allocator.free(header);
    }

    try std.testing.expectEqual(@as(usize, 3), header.len);
    try std.testing.expectEqualStrings("Name", header[0]);
    try std.testing.expectEqualStrings("Age", header[1]);
    try std.testing.expectEqualStrings("City", header[2]);

    // Read first row
    const row1 = (try csv.readRow(allocator)).?;
    defer {
        for (row1) |field| allocator.free(field);
        allocator.free(row1);
    }

    try std.testing.expectEqual(@as(usize, 3), row1.len);
    try std.testing.expectEqualStrings("Alice", row1[0]);
    try std.testing.expectEqualStrings("30", row1[1]);
    try std.testing.expectEqualStrings("New York", row1[2]);

    // Read second row
    const row2 = (try csv.readRow(allocator)).?;
    defer {
        for (row2) |field| allocator.free(field);
        allocator.free(row2);
    }

    try std.testing.expectEqual(@as(usize, 3), row2.len);
    try std.testing.expectEqualStrings("Bob", row2[0]);
}

test "read csv with quoted fields" {
    const data = "Name,Description\nItem,\"Contains, comma\"\n";
    var stream = std.io.fixedBufferStream(data);

    const allocator = std.testing.allocator;
    var csv = CsvReader.init(allocator, stream.reader().any());
    defer csv.deinit();

    // Skip header
    const header = (try csv.readRow(allocator)).?;
    defer {
        for (header) |field| allocator.free(field);
        allocator.free(header);
    }

    const row = (try csv.readRow(allocator)).?;
    defer {
        for (row) |field| allocator.free(field);
        allocator.free(row);
    }

    try std.testing.expectEqualStrings("Item", row[0]);
    try std.testing.expectEqualStrings("Contains, comma", row[1]);
}

test "read csv with escaped quotes" {
    const data = "Title,Quote\nBook,\"He said \"\"Hello\"\"\"\n";
    var stream = std.io.fixedBufferStream(data);

    const allocator = std.testing.allocator;
    var csv = CsvReader.init(allocator, stream.reader().any());
    defer csv.deinit();

    // Skip header
    const header = (try csv.readRow(allocator)).?;
    defer {
        for (header) |field| allocator.free(field);
        allocator.free(header);
    }

    const row = (try csv.readRow(allocator)).?;
    defer {
        for (row) |field| allocator.free(field);
        allocator.free(row);
    }

    try std.testing.expectEqualStrings("Book", row[0]);
    try std.testing.expectEqualStrings("He said \"Hello\"", row[1]);
}

test "read csv with newlines in quotes" {
    const data = "Field,Value\nMulti,\"Line\nValue\"\n";
    var stream = std.io.fixedBufferStream(data);

    const allocator = std.testing.allocator;
    var csv = CsvReader.init(allocator, stream.reader().any());
    defer csv.deinit();

    // Skip header
    const header = (try csv.readRow(allocator)).?;
    defer {
        for (header) |field| allocator.free(field);
        allocator.free(header);
    }

    const row = (try csv.readRow(allocator)).?;
    defer {
        for (row) |field| allocator.free(field);
        allocator.free(row);
    }

    try std.testing.expectEqualStrings("Multi", row[0]);
    try std.testing.expectEqualStrings("Line\nValue", row[1]);
}

test "read empty csv" {
    const data = "";
    var stream = std.io.fixedBufferStream(data);

    const allocator = std.testing.allocator;
    var csv = CsvReader.init(allocator, stream.reader().any());
    defer csv.deinit();

    const row = try csv.readRow(allocator);
    try std.testing.expect(row == null);
}

test "read csv with empty fields" {
    const data = "A,,C\n,B,\n";
    var stream = std.io.fixedBufferStream(data);

    const allocator = std.testing.allocator;
    var csv = CsvReader.init(allocator, stream.reader().any());
    defer csv.deinit();

    const row1 = (try csv.readRow(allocator)).?;
    defer {
        for (row1) |field| allocator.free(field);
        allocator.free(row1);
    }

    try std.testing.expectEqual(@as(usize, 3), row1.len);
    try std.testing.expectEqualStrings("A", row1[0]);
    try std.testing.expectEqualStrings("", row1[1]);
    try std.testing.expectEqualStrings("C", row1[2]);
}

test "write tsv" {
    var buffer: [1024]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    const rows = [_][]const []const u8{
        &.{ "Name", "Age" },
        &.{ "Alice", "30" },
    };

    try writeTsv(stream.writer().any(), &rows);

    const result = stream.getWritten();
    try std.testing.expectEqualStrings("Name\tAge\nAlice\t30\n", result);
}

test "roundtrip csv" {
    const allocator = std.testing.allocator;

    // Write CSV
    var write_buffer: [1024]u8 = undefined;
    var write_stream = std.io.fixedBufferStream(&write_buffer);

    var writer = CsvWriter.init(write_stream.writer().any());
    try writer.writeRow(&.{ "Name", "Value" });
    try writer.writeRow(&.{ "Test", "Data" });

    const written = write_stream.getWritten();

    // Read CSV back
    var read_stream = std.io.fixedBufferStream(written);
    var reader = CsvReader.init(allocator, read_stream.reader().any());
    defer reader.deinit();

    const row1 = (try reader.readRow(allocator)).?;
    defer {
        for (row1) |field| allocator.free(field);
        allocator.free(row1);
    }

    const row2 = (try reader.readRow(allocator)).?;
    defer {
        for (row2) |field| allocator.free(field);
        allocator.free(row2);
    }

    try std.testing.expectEqualStrings("Name", row1[0]);
    try std.testing.expectEqualStrings("Test", row2[0]);
}

test "single field csv" {
    var buffer: [128]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    var csv = CsvWriter.init(stream.writer().any());
    try csv.writeRow(&.{"Single"});

    const result = stream.getWritten();
    try std.testing.expectEqualStrings("Single\n", result);
}

test "read single field csv" {
    const data = "Single\n";
    var stream = std.io.fixedBufferStream(data);

    const allocator = std.testing.allocator;
    var csv = CsvReader.init(allocator, stream.reader().any());
    defer csv.deinit();

    const row = (try csv.readRow(allocator)).?;
    defer {
        for (row) |field| allocator.free(field);
        allocator.free(row);
    }

    try std.testing.expectEqual(@as(usize, 1), row.len);
    try std.testing.expectEqualStrings("Single", row[0]);
}

test "csv with unicode" {
    var buffer: [1024]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    var csv = CsvWriter.init(stream.writer().any());
    try csv.writeRow(&.{ "Name", "Nom", "名前" });
    try csv.writeRow(&.{ "Hello", "Bonjour", "こんにちは" });

    const result = stream.getWritten();
    try std.testing.expect(std.mem.indexOf(u8, result, "名前") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "こんにちは") != null);
}
```

---

## Recipe 6.2: Reading and Writing JSON Data {#recipe-6-2}

**Tags:** allocators, arena-allocator, arraylist, comptime, data-encoding, data-structures, error-handling, hashmap, json, memory, parsing, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/06-data-encoding/recipe_6_2.zig`

### Problem

You need to read and write JSON data, parse it into Zig structs, or work with dynamic JSON structures.

### Solution

### JSON Parsing

```zig
/// Parse JSON into a struct
pub fn parseJson(
    comptime T: type,
    allocator: std.mem.Allocator,
    json_text: []const u8,
) !std.json.Parsed(T) {
    return try std.json.parseFromSlice(T, allocator, json_text, .{});
}
```

### JSON Stringifying

```zig
/// Stringify value with allocator
pub fn stringifyAlloc(allocator: std.mem.Allocator, value: anytype) ![]u8 {
    return try std.json.Stringify.valueAlloc(allocator, value, .{});
}

/// Pretty print JSON
pub fn prettyPrint(value: anytype, writer: std.io.AnyWriter) !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const json_str = try std.json.Stringify.valueAlloc(allocator, value, .{
        .whitespace = .indent_2,
    });
    try writer.writeAll(json_str);
}
```

### JSON Error Handling

```zig
/// Safe JSON parsing with error handling
pub fn parseJsonSafe(
    comptime T: type,
    allocator: std.mem.Allocator,
    json_text: []const u8,
) !std.json.Parsed(T) {
    return std.json.parseFromSlice(T, allocator, json_text, .{}) catch |err| switch (err) {
        error.UnexpectedEndOfInput => {
            std.debug.print("Incomplete JSON\n", .{});
            return error.InvalidJson;
        },
        error.InvalidCharacter => {
            std.debug.print("Invalid JSON character\n", .{});
            return error.InvalidJson;
        },
        error.UnexpectedToken => {
            std.debug.print("Unexpected JSON token\n", .{});
            return error.InvalidJson;
        },
        error.SyntaxError => {
            std.debug.print("Invalid JSON syntax\n", .{});
            return error.InvalidJson;
        },
        else => return err,
    };
}
```

### Discussion

### Parsing JSON into Structs

The most common use case is parsing JSON into known structs:

```zig
const User = struct {
    id: u32,
    name: []const u8,
    active: bool,
    score: ?f32 = null,
};

pub fn parseUser(allocator: std.mem.Allocator, json_text: []const u8) !std.json.Parsed(User) {
    return try std.json.parseFromSlice(
        User,
        allocator,
        json_text,
        .{},
    );
}

test "parse user" {
    const json =
        \\{"id":123,"name":"Alice","active":true,"score":98.5}
    ;

    const parsed = try parseUser(std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(u32, 123), parsed.value.id);
    try std.testing.expectEqualStrings("Alice", parsed.value.name);
    try std.testing.expect(parsed.value.active);
    try std.testing.expectEqual(@as(f32, 98.5), parsed.value.score.?);
}
```

### Writing JSON from Structs

Serialize structs to JSON:

```zig
pub fn stringifyToBuffer(value: anytype, buffer: []u8) ![]const u8 {
    var stream = std.io.fixedBufferStream(buffer);
    try std.json.stringify(value, .{}, stream.writer());
    return stream.getWritten();
}

pub fn stringifyAlloc(allocator: std.mem.Allocator, value: anytype) ![]u8 {
    var list: std.ArrayList(u8) = .{};
    errdefer list.deinit(allocator);

    try std.json.stringify(value, .{}, list.writer(allocator));
    return try list.toOwnedSlice(allocator);
}

test "stringify to buffer" {
    const data = .{ .x = 10, .y = 20 };

    var buffer: [128]u8 = undefined;
    const result = try stringifyToBuffer(data, &buffer);

    try std.testing.expect(std.mem.indexOf(u8, result, "10") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "20") != null);
}
```

### Pretty Printing JSON

Format JSON with indentation:

```zig
pub fn prettyPrint(
    value: anytype,
    writer: std.io.AnyWriter,
) !void {
    try std.json.stringify(value, .{
        .whitespace = .indent_2,
    }, writer);
}

test "pretty print" {
    const data = .{
        .name = "Test",
        .items = .{ 1, 2, 3 },
    };

    var buffer: [256]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    try prettyPrint(data, stream.writer().any());

    const result = stream.getWritten();
    // Should contain newlines and indentation
    try std.testing.expect(std.mem.indexOf(u8, result, "\n") != null);
}
```

### Parsing Arrays

Parse JSON arrays:

```zig
test "parse array" {
    const json = "[1, 2, 3, 4, 5]";

    const parsed = try std.json.parseFromSlice(
        []i32,
        std.testing.allocator,
        json,
        .{},
    );
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 5), parsed.value.len);
    try std.testing.expectEqual(@as(i32, 1), parsed.value[0]);
    try std.testing.expectEqual(@as(i32, 5), parsed.value[4]);
}
```

### Nested Structures

Handle nested JSON objects:

```zig
const Address = struct {
    street: []const u8,
    city: []const u8,
    zip: []const u8,
};

const Person = struct {
    name: []const u8,
    age: u32,
    address: Address,
};

test "nested structures" {
    const json =
        \\{
        \\  "name": "Alice",
        \\  "age": 30,
        \\  "address": {
        \\    "street": "123 Main St",
        \\    "city": "Springfield",
        \\    "zip": "12345"
        \\  }
        \\}
    ;

    const parsed = try std.json.parseFromSlice(
        Person,
        std.testing.allocator,
        json,
        .{},
    );
    defer parsed.deinit();

    try std.testing.expectEqualStrings("Alice", parsed.value.name);
    try std.testing.expectEqualStrings("Springfield", parsed.value.address.city);
}
```

### Optional Fields

Handle optional JSON fields:

```zig
const Config = struct {
    host: []const u8,
    port: u16,
    ssl: ?bool = null,
    timeout: ?u32 = null,
};

test "optional fields" {
    const json =
        \\{"host":"localhost","port":8080,"ssl":true}
    ;

    const parsed = try std.json.parseFromSlice(
        Config,
        std.testing.allocator,
        json,
        .{},
    );
    defer parsed.deinit();

    try std.testing.expectEqual(@as(u16, 8080), parsed.value.port);
    try std.testing.expectEqual(@as(bool, true), parsed.value.ssl.?);
    try std.testing.expect(parsed.value.timeout == null);
}
```

### Dynamic JSON Values

Work with unknown JSON structures using `std.json.Value`:

```zig
test "dynamic json" {
    const json =
        \\{"name":"Alice","scores":[95,87,92]}
    ;

    const parsed = try std.json.parseFromSlice(
        std.json.Value,
        std.testing.allocator,
        json,
        .{},
    );
    defer parsed.deinit();

    const obj = parsed.value.object;
    const name = obj.get("name").?.string;
    try std.testing.expectEqualStrings("Alice", name);

    const scores = obj.get("scores").?.array;
    try std.testing.expectEqual(@as(usize, 3), scores.items.len);
}
```

### Custom Serialization

Implement custom JSON serialization:

```zig
const Point = struct {
    x: f32,
    y: f32,

    pub fn jsonStringify(self: Point, jws: anytype) !void {
        try jws.beginObject();
        try jws.objectField("x");
        try jws.write(self.x);
        try jws.objectField("y");
        try jws.write(self.y);
        try jws.endObject();
    }
};

test "custom serialization" {
    const point = Point{ .x = 10.5, .y = 20.3 };

    var buffer: [128]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    try std.json.stringify(point, .{}, stream.writer());

    const result = stream.getWritten();
    try std.testing.expect(std.mem.indexOf(u8, result, "10.5") != null);
}
```

### Custom Parsing

Implement custom JSON parsing:

```zig
const Color = struct {
    r: u8,
    g: u8,
    b: u8,

    pub fn jsonParse(
        allocator: std.mem.Allocator,
        source: anytype,
        options: std.json.ParseOptions,
    ) !Color {
        _ = allocator;
        _ = options;

        const value = try std.json.innerParse(std.json.Value, allocator, source, options);
        defer value.deinit();

        if (value.value == .string) {
            // Parse hex color like "#FF0000"
            const hex = value.value.string;
            if (hex[0] != '#' or hex.len != 7) return error.InvalidColor;

            return Color{
                .r = try std.fmt.parseInt(u8, hex[1..3], 16),
                .g = try std.fmt.parseInt(u8, hex[3..5], 16),
                .b = try std.fmt.parseInt(u8, hex[5..7], 16),
            };
        }

        return error.InvalidColor;
    }
};
```

### Streaming JSON Parsing

Parse large JSON files incrementally:

```zig
pub fn parseJsonStream(
    allocator: std.mem.Allocator,
    reader: std.io.AnyReader,
) !std.json.Parsed(std.json.Value) {
    const json_text = try reader.readAllAlloc(allocator, 1024 * 1024);
    defer allocator.free(json_text);

    return try std.json.parseFromSlice(
        std.json.Value,
        allocator,
        json_text,
        .{},
    );
}
```

### Handling Errors

Graceful error handling:

```zig
pub fn parseJsonSafe(
    comptime T: type,
    allocator: std.mem.Allocator,
    json_text: []const u8,
) !std.json.Parsed(T) {
    return std.json.parseFromSlice(T, allocator, json_text, .{}) catch |err| switch (err) {
        error.UnexpectedEndOfInput => {
            std.debug.print("Incomplete JSON\n", .{});
            return error.InvalidJson;
        },
        error.InvalidCharacter => {
            std.debug.print("Invalid JSON character\n", .{});
            return error.InvalidJson;
        },
        error.UnexpectedToken => {
            std.debug.print("Unexpected JSON token\n", .{});
            return error.InvalidJson;
        },
        else => return err,
    };
}
```

### Validating JSON Schema

Basic schema validation:

```zig
pub fn validateUser(user: anytype) !void {
    if (user.age < 0 or user.age > 150) {
        return error.InvalidAge;
    }

    if (user.name.len == 0) {
        return error.EmptyName;
    }
}

test "validate json" {
    const json =
        \\{"name":"","age":30}
    ;

    const parsed = try std.json.parseFromSlice(
        struct { name: []const u8, age: i32 },
        std.testing.allocator,
        json,
        .{},
    );
    defer parsed.deinit();

    const result = validateUser(parsed.value);
    try std.testing.expectError(error.EmptyName, result);
}
```

### Working with Maps

Parse JSON objects as hashmaps:

```zig
test "json to hashmap" {
    const json =
        \\{"key1":"value1","key2":"value2"}
    ;

    const parsed = try std.json.parseFromSlice(
        std.json.Value,
        std.testing.allocator,
        json,
        .{},
    );
    defer parsed.deinit();

    const map = parsed.value.object;
    try std.testing.expectEqualStrings("value1", map.get("key1").?.string);
    try std.testing.expectEqualStrings("value2", map.get("key2").?.string);
}
```

### Handling Numbers

Different number types in JSON:

```zig
const Numbers = struct {
    int_val: i64,
    float_val: f64,
    optional_num: ?f32 = null,
};

test "parse numbers" {
    const json =
        \\{"int_val":42,"float_val":3.14159}
    ;

    const parsed = try std.json.parseFromSlice(
        Numbers,
        std.testing.allocator,
        json,
        .{},
    );
    defer parsed.deinit();

    try std.testing.expectEqual(@as(i64, 42), parsed.value.int_val);
    try std.testing.expectApproxEqRel(@as(f64, 3.14159), parsed.value.float_val, 0.0001);
}
```

### Escaping Special Characters

JSON automatically handles escaping:

```zig
test "special characters" {
    const data = .{
        .message = "Line 1\nLine 2\tTabbed",
        .quote = "He said \"Hello\"",
    };

    var buffer: [256]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    try std.json.stringify(data, .{}, stream.writer());

    const result = stream.getWritten();
    try std.testing.expect(std.mem.indexOf(u8, result, "\\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "\\\"") != null);
}
```

### Performance Considerations

**Parsing:**
- `parseFromSlice` allocates memory for parsed data
- Always call `.deinit()` on parsed results
- For large files, consider streaming approaches

**Writing:**
- Use `ArrayList` writer for dynamic size
- Use `fixedBufferStream` when size is known
- Pretty printing adds overhead

**Memory:**
```zig
// Good: Parse once, use, then free
const parsed = try std.json.parseFromSlice(T, allocator, json, .{});
defer parsed.deinit();
use(parsed.value);

// Bad: Multiple parses without cleanup
const p1 = try std.json.parseFromSlice(T, allocator, json, .{});
const p2 = try std.json.parseFromSlice(T, allocator, json, .{}); // Leak!
```

### Common Patterns

**Configuration files:**
```zig
pub fn loadConfig(allocator: std.mem.Allocator, path: []const u8) !Config {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const json_text = try file.readToEndAlloc(allocator, 1024 * 1024);
    defer allocator.free(json_text);

    const parsed = try std.json.parseFromSlice(Config, allocator, json_text, .{});
    errdefer parsed.deinit();

    return parsed.value;
}
```

**API responses:**
```zig
pub fn parseApiResponse(
    allocator: std.mem.Allocator,
    response_body: []const u8,
) !ApiResult {
    const parsed = try std.json.parseFromSlice(
        ApiResult,
        allocator,
        response_body,
        .{ .ignore_unknown_fields = true },
    );
    defer parsed.deinit();

    return try allocator.dupe(ApiResult, &.{parsed.value});
}
```

### JSON Lines (JSONL)

Parse newline-delimited JSON:

```zig
pub fn parseJsonLines(
    comptime T: type,
    allocator: std.mem.Allocator,
    text: []const u8,
) ![]T {
    var results: std.ArrayList(T) = .{};
    errdefer results.deinit(allocator);

    var lines = std.mem.splitScalar(u8, text, '\n');
    while (lines.next()) |line| {
        if (line.len == 0) continue;

        const parsed = try std.json.parseFromSlice(T, allocator, line, .{});
        defer parsed.deinit();

        try results.append(allocator, parsed.value);
    }

    return try results.toOwnedSlice(allocator);
}
```

### Related Functions

- `std.json.parseFromSlice()` - Parse JSON into struct
- `std.json.stringify()` - Serialize to JSON
- `std.json.Value` - Dynamic JSON value
- `std.json.ParseOptions` - Parsing configuration
- `std.json.StringifyOptions` - Serialization options
- `std.json.innerParse()` - Custom parsing helper

### Full Tested Code

```zig
const std = @import("std");

// Test structures

const Person = struct {
    name: []const u8,
    age: u32,
    email: ?[]const u8 = null,
};

const User = struct {
    id: u32,
    name: []const u8,
    active: bool,
    score: ?f32 = null,
};

const Address = struct {
    street: []const u8,
    city: []const u8,
    zip: []const u8,
};

const PersonWithAddress = struct {
    name: []const u8,
    age: u32,
    address: Address,
};

const Config = struct {
    host: []const u8,
    port: u16,
    ssl: ?bool = null,
    timeout: ?u32 = null,
};

const Numbers = struct {
    int_val: i64,
    float_val: f64,
    optional_num: ?f32 = null,
};

// Helper functions

// ANCHOR: json_parsing
/// Parse JSON into a struct
pub fn parseJson(
    comptime T: type,
    allocator: std.mem.Allocator,
    json_text: []const u8,
) !std.json.Parsed(T) {
    return try std.json.parseFromSlice(T, allocator, json_text, .{});
}
// ANCHOR_END: json_parsing

/// Stringify value to buffer using FixedBufferAllocator to avoid heap allocations
/// This is more efficient than allocating on the heap and copying
pub fn stringifyToBuffer(value: anytype, buffer: []u8) ![]const u8 {
    var fba = std.heap.FixedBufferAllocator.init(buffer);
    const allocator = fba.allocator();

    const json_str = try std.json.Stringify.valueAlloc(allocator, value, .{});
    // json_str is already in buffer, no copy needed
    return json_str;
}

// ANCHOR: json_stringifying
/// Stringify value with allocator
pub fn stringifyAlloc(allocator: std.mem.Allocator, value: anytype) ![]u8 {
    return try std.json.Stringify.valueAlloc(allocator, value, .{});
}

/// Pretty print JSON
pub fn prettyPrint(value: anytype, writer: std.io.AnyWriter) !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const json_str = try std.json.Stringify.valueAlloc(allocator, value, .{
        .whitespace = .indent_2,
    });
    try writer.writeAll(json_str);
}
// ANCHOR_END: json_stringifying

// ANCHOR: json_error_handling
/// Safe JSON parsing with error handling
pub fn parseJsonSafe(
    comptime T: type,
    allocator: std.mem.Allocator,
    json_text: []const u8,
) !std.json.Parsed(T) {
    return std.json.parseFromSlice(T, allocator, json_text, .{}) catch |err| switch (err) {
        error.UnexpectedEndOfInput => {
            std.debug.print("Incomplete JSON\n", .{});
            return error.InvalidJson;
        },
        error.InvalidCharacter => {
            std.debug.print("Invalid JSON character\n", .{});
            return error.InvalidJson;
        },
        error.UnexpectedToken => {
            std.debug.print("Unexpected JSON token\n", .{});
            return error.InvalidJson;
        },
        error.SyntaxError => {
            std.debug.print("Invalid JSON syntax\n", .{});
            return error.InvalidJson;
        },
        else => return err,
    };
}
// ANCHOR_END: json_error_handling

// Tests

test "parse json into struct" {
    const json_text =
        \\{"name":"Alice","age":30,"email":"alice@example.com"}
    ;

    const parsed = try parseJson(Person, std.testing.allocator, json_text);
    defer parsed.deinit();

    try std.testing.expectEqualStrings("Alice", parsed.value.name);
    try std.testing.expectEqual(@as(u32, 30), parsed.value.age);
    try std.testing.expectEqualStrings("alice@example.com", parsed.value.email.?);
}

test "stringify struct to json" {
    const person = Person{
        .name = "Bob",
        .age = 25,
        .email = "bob@example.com",
    };

    var buffer: [256]u8 = undefined;
    const result = try stringifyToBuffer(person, &buffer);

    try std.testing.expect(std.mem.indexOf(u8, result, "Bob") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "25") != null);
}

test "parse user with optional field" {
    const json =
        \\{"id":123,"name":"Alice","active":true,"score":98.5}
    ;

    const parsed = try parseJson(User, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(u32, 123), parsed.value.id);
    try std.testing.expectEqualStrings("Alice", parsed.value.name);
    try std.testing.expect(parsed.value.active);
    try std.testing.expectEqual(@as(f32, 98.5), parsed.value.score.?);
}

test "parse user without optional field" {
    const json =
        \\{"id":456,"name":"Bob","active":false}
    ;

    const parsed = try parseJson(User, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(u32, 456), parsed.value.id);
    try std.testing.expect(!parsed.value.active);
    try std.testing.expect(parsed.value.score == null);
}

test "stringify to buffer" {
    const data = .{ .x = 10, .y = 20 };

    var buffer: [128]u8 = undefined;
    const result = try stringifyToBuffer(data, &buffer);

    try std.testing.expect(std.mem.indexOf(u8, result, "10") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "20") != null);
}

test "stringify with allocator" {
    const data = .{ .name = "Test", .value = 42 };

    const result = try stringifyAlloc(std.testing.allocator, data);
    defer std.testing.allocator.free(result);

    try std.testing.expect(std.mem.indexOf(u8, result, "Test") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "42") != null);
}

test "pretty print json" {
    const data = .{
        .name = "Test",
        .items = .{ 1, 2, 3 },
    };

    var buffer: [256]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);

    try prettyPrint(data, stream.writer().any());

    const result = stream.getWritten();
    try std.testing.expect(std.mem.indexOf(u8, result, "\n") != null);
}

test "parse array" {
    const json = "[1, 2, 3, 4, 5]";

    const parsed = try parseJson([]i32, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 5), parsed.value.len);
    try std.testing.expectEqual(@as(i32, 1), parsed.value[0]);
    try std.testing.expectEqual(@as(i32, 5), parsed.value[4]);
}

test "nested structures" {
    const json =
        \\{
        \\  "name": "Alice",
        \\  "age": 30,
        \\  "address": {
        \\    "street": "123 Main St",
        \\    "city": "Springfield",
        \\    "zip": "12345"
        \\  }
        \\}
    ;

    const parsed = try parseJson(PersonWithAddress, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqualStrings("Alice", parsed.value.name);
    try std.testing.expectEqual(@as(u32, 30), parsed.value.age);
    try std.testing.expectEqualStrings("123 Main St", parsed.value.address.street);
    try std.testing.expectEqualStrings("Springfield", parsed.value.address.city);
    try std.testing.expectEqualStrings("12345", parsed.value.address.zip);
}

test "optional fields" {
    const json =
        \\{"host":"localhost","port":8080,"ssl":true}
    ;

    const parsed = try parseJson(Config, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqualStrings("localhost", parsed.value.host);
    try std.testing.expectEqual(@as(u16, 8080), parsed.value.port);
    try std.testing.expectEqual(@as(bool, true), parsed.value.ssl.?);
    try std.testing.expect(parsed.value.timeout == null);
}

test "dynamic json" {
    const json =
        \\{"name":"Alice","scores":[95,87,92]}
    ;

    const parsed = try parseJson(std.json.Value, std.testing.allocator, json);
    defer parsed.deinit();

    const obj = parsed.value.object;
    const name = obj.get("name").?.string;
    try std.testing.expectEqualStrings("Alice", name);

    const scores = obj.get("scores").?.array;
    try std.testing.expectEqual(@as(usize, 3), scores.items.len);
    try std.testing.expectEqual(@as(i64, 95), scores.items[0].integer);
}

test "parse numbers" {
    const json =
        \\{"int_val":42,"float_val":3.14159}
    ;

    const parsed = try parseJson(Numbers, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(i64, 42), parsed.value.int_val);
    try std.testing.expectApproxEqRel(@as(f64, 3.14159), parsed.value.float_val, 0.0001);
}

test "special characters" {
    const data = .{
        .message = "Line 1\nLine 2\tTabbed",
        .quote = "He said \"Hello\"",
    };

    var buffer: [256]u8 = undefined;
    const result = try stringifyToBuffer(data, &buffer);
    try std.testing.expect(std.mem.indexOf(u8, result, "\\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "\\\"") != null);
}

test "empty object" {
    const json = "{}";

    const EmptyStruct = struct {};
    const parsed = try parseJson(EmptyStruct, std.testing.allocator, json);
    defer parsed.deinit();

    // Just verify it parses successfully
    _ = parsed.value;
}

test "empty array" {
    const json = "[]";

    const parsed = try parseJson([]i32, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 0), parsed.value.len);
}

test "null value" {
    const json =
        \\{"name":"Alice","age":30,"email":null}
    ;

    const parsed = try parseJson(Person, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqualStrings("Alice", parsed.value.name);
    try std.testing.expect(parsed.value.email == null);
}

test "boolean values" {
    const BoolData = struct {
        flag1: bool,
        flag2: bool,
    };

    const json =
        \\{"flag1":true,"flag2":false}
    ;

    const parsed = try parseJson(BoolData, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expect(parsed.value.flag1);
    try std.testing.expect(!parsed.value.flag2);
}

test "stringify boolean" {
    const data = .{ .enabled = true, .disabled = false };

    var buffer: [128]u8 = undefined;
    const result = try stringifyToBuffer(data, &buffer);

    try std.testing.expect(std.mem.indexOf(u8, result, "true") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "false") != null);
}

test "parse error handling" {
    const bad_json = "{invalid json";

    const result = parseJsonSafe(Person, std.testing.allocator, bad_json);
    try std.testing.expectError(error.InvalidJson, result);
}

test "incomplete json" {
    const incomplete = "{\"name\":\"Alice\"";

    const result = parseJsonSafe(Person, std.testing.allocator, incomplete);
    try std.testing.expectError(error.InvalidJson, result);
}

test "json to hashmap" {
    const json =
        \\{"key1":"value1","key2":"value2"}
    ;

    const parsed = try parseJson(std.json.Value, std.testing.allocator, json);
    defer parsed.deinit();

    const map = parsed.value.object;
    try std.testing.expectEqualStrings("value1", map.get("key1").?.string);
    try std.testing.expectEqualStrings("value2", map.get("key2").?.string);
}

test "array of objects" {
    const json =
        \\[{"name":"Alice","age":30},{"name":"Bob","age":25}]
    ;

    const PersonSimple = struct {
        name: []const u8,
        age: u32,
    };

    const parsed = try parseJson([]PersonSimple, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 2), parsed.value.len);
    try std.testing.expectEqualStrings("Alice", parsed.value[0].name);
    try std.testing.expectEqual(@as(u32, 30), parsed.value[0].age);
    try std.testing.expectEqualStrings("Bob", parsed.value[1].name);
    try std.testing.expectEqual(@as(u32, 25), parsed.value[1].age);
}

test "nested arrays" {
    const json =
        \\[[1,2],[3,4],[5,6]]
    ;

    const parsed = try parseJson([][]i32, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 3), parsed.value.len);
    try std.testing.expectEqual(@as(i32, 1), parsed.value[0][0]);
    try std.testing.expectEqual(@as(i32, 6), parsed.value[2][1]);
}

test "whitespace handling" {
    const json =
        \\  {  "name"  :  "Alice"  ,  "age"  :  30  }
    ;

    const PersonSimple = struct {
        name: []const u8,
        age: u32,
    };

    const parsed = try parseJson(PersonSimple, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqualStrings("Alice", parsed.value.name);
    try std.testing.expectEqual(@as(u32, 30), parsed.value.age);
}

test "large numbers" {
    const LargeNums = struct {
        big_int: i64,
        big_float: f64,
    };

    const json =
        \\{"big_int":9007199254740991,"big_float":1.7976931348623157e308}
    ;

    const parsed = try parseJson(LargeNums, std.testing.allocator, json);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(i64, 9007199254740991), parsed.value.big_int);
    try std.testing.expect(parsed.value.big_float > 1e308);
}

test "unicode in strings" {
    const data = .{
        .english = "Hello",
        .japanese = "こんにちは",
        .emoji = "🎉",
    };

    var buffer: [256]u8 = undefined;
    const result = try stringifyToBuffer(data, &buffer);

    try std.testing.expect(std.mem.indexOf(u8, result, "Hello") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "こんにちは") != null);
    try std.testing.expect(std.mem.indexOf(u8, result, "🎉") != null);
}

test "roundtrip conversion" {
    const original = Person{
        .name = "Charlie",
        .age = 35,
        .email = "charlie@example.com",
    };

    // Stringify
    const json_str = try stringifyAlloc(std.testing.allocator, original);
    defer std.testing.allocator.free(json_str);

    // Parse back
    const parsed = try parseJson(Person, std.testing.allocator, json_str);
    defer parsed.deinit();

    try std.testing.expectEqualStrings(original.name, parsed.value.name);
    try std.testing.expectEqual(original.age, parsed.value.age);
}
```

---

## Recipe 6.3: Parsing Simple XML Data {#recipe-6-3}

**Tags:** allocators, arraylist, c-interop, data-encoding, data-structures, error-handling, hashmap, memory, parsing, resource-cleanup, slices, testing, xml
**Difficulty:** intermediate
**Code:** `code/03-advanced/06-data-encoding/recipe_6_3.zig`

### Problem

You need to parse simple XML data to extract elements, attributes, and text content.

### Solution

### Find Element

```zig
/// Find a single XML element by tag name
/// NOTE: This is a naive implementation for simple, well-formed XML.
/// For robust parsing with proper handling of edge cases, attributes,
/// and complex XML structures, see recipe_6_4.zig (StreamingXmlParser).
pub fn findElement(xml: []const u8, tag: []const u8) ?[]const u8 {
    const open_tag = std.fmt.allocPrint(
        std.heap.page_allocator,
        "<{s}",
        .{tag},
    ) catch return null;
    defer std.heap.page_allocator.free(open_tag);

    const close_tag = std.fmt.allocPrint(
        std.heap.page_allocator,
        "</{s}>",
        .{tag},
    ) catch return null;
    defer std.heap.page_allocator.free(close_tag);

    var pos: usize = 0;
    while (std.mem.indexOfPos(u8, xml, pos, open_tag)) |start| {
        // Verify this is an exact tag match, not a prefix
        // e.g., searching for <user should not match <username>
        const char_after_tag = start + open_tag.len;
        if (char_after_tag < xml.len) {
            const next_char = xml[char_after_tag];
            // Check for valid tag boundaries: '>', ' ', '\t', '\n', '\r', '/'
            if (next_char == '>' or next_char == ' ' or next_char == '\t' or
                next_char == '\n' or next_char == '\r' or next_char == '/')
            {
                // This is a valid tag match
                const tag_end = std.mem.indexOfPos(u8, xml, start, ">") orelse return null;
                const end = std.mem.indexOfPos(u8, xml, tag_end, close_tag) orelse return null;
                return xml[tag_end + 1 .. end];
            }
        }
        // Not a valid match, continue searching
        pos = start + open_tag.len;
    }

    return null;
}
```

### Parse Attributes

```zig
/// Parse attributes from an XML tag
pub fn parseAttributes(
    allocator: std.mem.Allocator,
    tag_content: []const u8,
) !std.StringHashMap([]const u8) {
    var attrs = std.StringHashMap([]const u8).init(allocator);
    errdefer attrs.deinit();

    // First, remove the element name
    const first_space = std.mem.indexOfAny(u8, tag_content, " \t\n\r") orelse return attrs;
    const attrs_part = std.mem.trim(u8, tag_content[first_space..], " \t\n\r");

    var i: usize = 0;
    while (i < attrs_part.len) {
        // Skip whitespace
        while (i < attrs_part.len and (attrs_part[i] == ' ' or attrs_part[i] == '\t' or attrs_part[i] == '\n' or attrs_part[i] == '\r')) {
            i += 1;
        }
        if (i >= attrs_part.len) break;

        // Find key
        const key_start = i;
        while (i < attrs_part.len and attrs_part[i] != '=' and attrs_part[i] != ' ' and attrs_part[i] != '\t') {
            i += 1;
        }
        const key = std.mem.trim(u8, attrs_part[key_start..i], " \t");

        // Skip whitespace and =
        while (i < attrs_part.len and (attrs_part[i] == ' ' or attrs_part[i] == '\t' or attrs_part[i] == '=')) {
            i += 1;
        }
        if (i >= attrs_part.len) break;

        // Find value
        var value: []const u8 = undefined;
        if (attrs_part[i] == '"') {
            // Quoted value
            i += 1;
            const value_start = i;
            while (i < attrs_part.len and attrs_part[i] != '"') {
                i += 1;
            }
            value = attrs_part[value_start..i];
            if (i < attrs_part.len) i += 1; // Skip closing quote
        } else {
            // Unquoted value
            const value_start = i;
            while (i < attrs_part.len and attrs_part[i] != ' ' and attrs_part[i] != '\t') {
                i += 1;
            }
            value = attrs_part[value_start..i];
        }

        try attrs.put(key, value);
    }

    return attrs;
}
```

### Find All Elements

```zig
/// Find all elements with a given tag
/// NOTE: This is a naive implementation for simple, well-formed XML.
/// For robust parsing, see recipe_6_4.zig (StreamingXmlParser).
pub fn findAllElements(
    allocator: std.mem.Allocator,
    xml: []const u8,
    tag: []const u8,
) ![][]const u8 {
    var results: std.ArrayList([]const u8) = .{};
    errdefer results.deinit(allocator);

    const open_tag = try std.fmt.allocPrint(allocator, "<{s}", .{tag});
    defer allocator.free(open_tag);

    const close_tag = try std.fmt.allocPrint(allocator, "</{s}>", .{tag});
    defer allocator.free(close_tag);

    var pos: usize = 0;
    while (std.mem.indexOfPos(u8, xml, pos, open_tag)) |start| {
        // Verify this is an exact tag match, not a prefix
        // e.g., searching for <user should not match <username>
        const char_after_tag = start + open_tag.len;
        if (char_after_tag < xml.len) {
            const next_char = xml[char_after_tag];
            // Check for valid tag boundaries: '>', ' ', '\t', '\n', '\r', '/'
            if (next_char == '>' or next_char == ' ' or next_char == '\t' or
                next_char == '\n' or next_char == '\r' or next_char == '/')
            {
                // This is a valid tag match
                const tag_end = std.mem.indexOfPos(u8, xml, start, ">") orelse break;
                const end = std.mem.indexOfPos(u8, xml, tag_end, close_tag) orelse break;

                const content = xml[tag_end + 1 .. end];
                try results.append(allocator, content);

                pos = end + close_tag.len;
                continue;
            }
        }
        // Not a valid match, continue searching
        pos = start + open_tag.len;
    }

    return try results.toOwnedSlice(allocator);
}
```

### Discussion

### Basic XML Parsing

Zig doesn't have built-in XML support, so we build parsers manually:

```zig
pub fn parseSimpleElement(
    allocator: std.mem.Allocator,
    xml: []const u8,
    tag: []const u8,
) !?XmlElement {
    const content = findElement(xml, tag) orelse return null;

    var element = XmlElement{
        .name = tag,
        .attributes = std.StringHashMap([]const u8).init(allocator),
        .text = content,
        .allocator = allocator,
    };

    return element;
}

test "parse simple element" {
    const xml = "<user>Alice</user>";

    var element = (try parseSimpleElement(
        std.testing.allocator,
        xml,
        "user",
    )).?;
    defer element.deinit();

    try std.testing.expectEqualStrings("user", element.name);
    try std.testing.expectEqualStrings("Alice", element.text.?);
}
```

### Extracting Attributes

Parse XML attributes from element tags:

```zig
pub fn parseAttributes(
    allocator: std.mem.Allocator,
    tag_content: []const u8,
) !std.StringHashMap([]const u8) {
    var attrs = std.StringHashMap([]const u8).init(allocator);
    errdefer attrs.deinit();

    var iter = std.mem.tokenizeAny(u8, tag_content, " \t\n\r");
    // Skip element name
    _ = iter.next();

    while (iter.next()) |attr| {
        const eq_pos = std.mem.indexOf(u8, attr, "=") orelse continue;
        const key = std.mem.trim(u8, attr[0..eq_pos], " \t");
        var value = std.mem.trim(u8, attr[eq_pos + 1 ..], " \t");

        // Remove quotes
        if (value.len >= 2 and value[0] == '"' and value[value.len - 1] == '"') {
            value = value[1 .. value.len - 1];
        }

        try attrs.put(key, value);
    }

    return attrs;
}

test "parse attributes" {
    const tag = "user id=\"123\" name=\"Alice\"";

    var attrs = try parseAttributes(std.testing.allocator, tag);
    defer attrs.deinit();

    try std.testing.expectEqualStrings("123", attrs.get("id").?);
    try std.testing.expectEqualStrings("Alice", attrs.get("name").?);
}
```

### Finding All Elements

Extract multiple elements with the same tag:

```zig
pub fn findAllElements(
    allocator: std.mem.Allocator,
    xml: []const u8,
    tag: []const u8,
) ![][]const u8 {
    var results: std.ArrayList([]const u8) = .{};
    errdefer results.deinit(allocator);

    const open_tag = try std.fmt.allocPrint(allocator, "<{s}", .{tag});
    defer allocator.free(open_tag);

    const close_tag = try std.fmt.allocPrint(allocator, "</{s}>", .{tag});
    defer allocator.free(close_tag);

    var pos: usize = 0;
    while (std.mem.indexOfPos(u8, xml, pos, open_tag)) |start| {
        const tag_end = std.mem.indexOfPos(u8, xml, start, ">") orelse break;
        const end = std.mem.indexOfPos(u8, xml, tag_end, close_tag) orelse break;

        const content = xml[tag_end + 1 .. end];
        try results.append(allocator, content);

        pos = end + close_tag.len;
    }

    return try results.toOwnedSlice(allocator);
}

test "find all elements" {
    const xml =
        \\<users>
        \\  <user>Alice</user>
        \\  <user>Bob</user>
        \\  <user>Charlie</user>
        \\</users>
    ;

    const users = try findAllElements(std.testing.allocator, xml, "user");
    defer std.testing.allocator.free(users);

    try std.testing.expectEqual(@as(usize, 3), users.len);
    try std.testing.expectEqualStrings("Alice", users[0]);
    try std.testing.expectEqualStrings("Bob", users[1]);
    try std.testing.expectEqualStrings("Charlie", users[2]);
}
```

### Nested Elements

Handle nested XML structures:

```zig
pub const XmlNode = struct {
    name: []const u8,
    text: ?[]const u8 = null,
    children: []XmlNode = &.{},
    attributes: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn deinit(self: *XmlNode) void {
        for (self.children) |*child| {
            child.deinit();
        }
        self.allocator.free(self.children);
        self.attributes.deinit();
    }
};

test "nested elements" {
    const xml =
        \\<person>
        \\  <name>Alice</name>
        \\  <address>
        \\    <city>New York</city>
        \\    <zip>10001</zip>
        \\  </address>
        \\</person>
    ;

    const name = findElement(xml, "name").?;
    try std.testing.expectEqualStrings("Alice", std.mem.trim(u8, name, " \n\r\t"));

    const address = findElement(xml, "address").?;
    const city = findElement(address, "city").?;
    try std.testing.expectEqualStrings("New York", std.mem.trim(u8, city, " \n\r\t"));
}
```

### Escaping Special Characters

Handle XML entities:

```zig
pub fn unescapeXml(allocator: std.mem.Allocator, text: []const u8) ![]u8 {
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i < text.len) {
        if (text[i] == '&') {
            if (std.mem.startsWith(u8, text[i..], "&lt;")) {
                try result.append(allocator, '<');
                i += 4;
            } else if (std.mem.startsWith(u8, text[i..], "&gt;")) {
                try result.append(allocator, '>');
                i += 4;
            } else if (std.mem.startsWith(u8, text[i..], "&amp;")) {
                try result.append(allocator, '&');
                i += 5;
            } else if (std.mem.startsWith(u8, text[i..], "&quot;")) {
                try result.append(allocator, '"');
                i += 6;
            } else if (std.mem.startsWith(u8, text[i..], "&apos;")) {
                try result.append(allocator, '\'');
                i += 6;
            } else {
                try result.append(allocator, text[i]);
                i += 1;
            }
        } else {
            try result.append(allocator, text[i]);
            i += 1;
        }
    }

    return try result.toOwnedSlice(allocator);
}

test "unescape xml" {
    const escaped = "Hello &lt;world&gt; &amp; &quot;friends&quot;";

    const unescaped = try unescapeXml(std.testing.allocator, escaped);
    defer std.testing.allocator.free(unescaped);

    try std.testing.expectEqualStrings("Hello <world> & \"friends\"", unescaped);
}
```

### Validating XML

Basic XML validation:

```zig
pub fn isWellFormed(xml: []const u8) bool {
    var depth: i32 = 0;
    var i: usize = 0;

    while (i < xml.len) {
        if (xml[i] == '<') {
            if (i + 1 < xml.len and xml[i + 1] == '/') {
                // Closing tag
                depth -= 1;
                if (depth < 0) return false;
            } else if (i + 1 < xml.len and xml[i + 1] != '!' and xml[i + 1] != '?') {
                // Opening tag (skip comments and declarations)
                depth += 1;
            }
        }
        i += 1;
    }

    return depth == 0;
}

test "validate xml" {
    try std.testing.expect(isWellFormed("<root><child>text</child></root>"));
    try std.testing.expect(!isWellFormed("<root><child>text</root>"));
    try std.testing.expect(!isWellFormed("<root><child>text</child>"));
}
```

### Reading XML from Files

Load and parse XML files:

```zig
pub fn parseXmlFile(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const xml_content = try file.readToEndAlloc(allocator, 10 * 1024 * 1024);
    return xml_content;
}

test "read xml file" {
    const xml_content = "<test>content</test>";

    // Create temporary file
    const tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    var tmp_file = try tmp_dir.dir.createFile("test.xml", .{});
    defer tmp_file.close();

    try tmp_file.writeAll(xml_content);

    // Read it back
    const path = try std.fs.path.join(
        std.testing.allocator,
        &.{ "zig-cache", "tmp", tmp_dir.sub_path[0..], "test.xml" },
    );
    defer std.testing.allocator.free(path);

    const content = try parseXmlFile(std.testing.allocator, path);
    defer std.testing.allocator.free(content);

    try std.testing.expectEqualStrings(xml_content, content);
}
```

### Using C Libraries (libxml2)

For complex XML parsing, link with libxml2:

```zig
// In build.zig:
// exe.linkSystemLibrary("xml2");
// exe.addIncludePath(.{ .path = "/usr/include/libxml2" });

const c = @cImport({
    @cInclude("libxml/parser.h");
    @cInclude("libxml/tree.h");
});

pub fn parseXmlWithLibxml2(xml: [*:0]const u8) ?*c.xmlDoc {
    const doc = c.xmlReadMemory(
        xml,
        @intCast(std.mem.len(xml)),
        null,
        null,
        0,
    );
    return doc;
}
```

### Performance Considerations

**Manual Parsing:**
- Fast for simple, known XML structures
- Low memory overhead
- No external dependencies
- Limited validation

**Using libxml2:**
- Full XML specification support
- Better error handling
- Heavier dependency
- More complex to integrate

**Best Practices:**
```zig
// Good: Parse once, reuse results
const elements = try findAllElements(allocator, xml, "item");
defer allocator.free(elements);
for (elements) |elem| {
    try processElement(elem);
}

// Bad: Repeated parsing
for (0..count) |i| {
    const elem = findElement(xml, "item"); // Inefficient!
}
```

### Error Handling

Handle malformed XML gracefully:

```zig
pub const XmlError = error{
    MalformedXml,
    UnexpectedEndOfInput,
    InvalidTag,
};

pub fn parseElementSafe(xml: []const u8, tag: []const u8) XmlError![]const u8 {
    const content = findElement(xml, tag) orelse return error.InvalidTag;

    if (!isWellFormed(xml)) {
        return error.MalformedXml;
    }

    return content;
}

test "error handling" {
    const bad_xml = "<root><unclosed>";

    const result = parseElementSafe(bad_xml, "root");
    try std.testing.expectError(error.MalformedXml, result);
}
```

### Common Patterns

**Configuration files:**
```zig
pub fn loadConfig(allocator: std.mem.Allocator, path: []const u8) !Config {
    const xml = try parseXmlFile(allocator, path);
    defer allocator.free(xml);

    const host = findElement(xml, "host") orelse return error.MissingHost;
    const port = findElement(xml, "port") orelse return error.MissingPort;

    return Config{
        .host = try allocator.dupe(u8, host),
        .port = try std.fmt.parseInt(u16, port, 10),
    };
}
```

**Data extraction:**
```zig
pub fn extractData(allocator: std.mem.Allocator, xml: []const u8) ![]Data {
    const items = try findAllElements(allocator, xml, "item");
    defer allocator.free(items);

    var results: std.ArrayList(Data) = .{};
    errdefer results.deinit(allocator);

    for (items) |item| {
        const name = findElement(item, "name") orelse continue;
        const value = findElement(item, "value") orelse continue;

        try results.append(allocator, Data{
            .name = try allocator.dupe(u8, name),
            .value = try std.fmt.parseInt(i32, value, 10),
        });
    }

    return try results.toOwnedSlice(allocator);
}
```

### Limitations

This simple parser handles basic XML but doesn't support:
- CDATA sections
- Processing instructions
- Namespaces
- DTD validation
- Complex entity references

For production XML parsing, consider using libxml2 or a Zig XML library.

### Related Functions

- `std.mem.indexOf()` - Find substrings
- `std.mem.tokenizeAny()` - Split strings
- `std.mem.trim()` - Remove whitespace
- `std.StringHashMap` - Store attributes
- `std.ArrayList` - Dynamic arrays
- `std.fs.File.readToEndAlloc()` - Read files

### Full Tested Code

```zig
const std = @import("std");

// XML Element structure
pub const XmlElement = struct {
    name: []const u8,
    attributes: std.StringHashMap([]const u8),
    text: ?[]const u8 = null,
    allocator: std.mem.Allocator,

    pub fn deinit(self: *XmlElement) void {
        self.attributes.deinit();
    }
};

// XML Node for nested structures
pub const XmlNode = struct {
    name: []const u8,
    text: ?[]const u8 = null,
    children: []XmlNode = &.{},
    attributes: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn deinit(self: *XmlNode) void {
        for (self.children) |*child| {
            child.deinit();
        }
        self.allocator.free(self.children);
        self.attributes.deinit();
    }
};

// ANCHOR: find_element
/// Find a single XML element by tag name
/// NOTE: This is a naive implementation for simple, well-formed XML.
/// For robust parsing with proper handling of edge cases, attributes,
/// and complex XML structures, see recipe_6_4.zig (StreamingXmlParser).
pub fn findElement(xml: []const u8, tag: []const u8) ?[]const u8 {
    const open_tag = std.fmt.allocPrint(
        std.heap.page_allocator,
        "<{s}",
        .{tag},
    ) catch return null;
    defer std.heap.page_allocator.free(open_tag);

    const close_tag = std.fmt.allocPrint(
        std.heap.page_allocator,
        "</{s}>",
        .{tag},
    ) catch return null;
    defer std.heap.page_allocator.free(close_tag);

    var pos: usize = 0;
    while (std.mem.indexOfPos(u8, xml, pos, open_tag)) |start| {
        // Verify this is an exact tag match, not a prefix
        // e.g., searching for <user should not match <username>
        const char_after_tag = start + open_tag.len;
        if (char_after_tag < xml.len) {
            const next_char = xml[char_after_tag];
            // Check for valid tag boundaries: '>', ' ', '\t', '\n', '\r', '/'
            if (next_char == '>' or next_char == ' ' or next_char == '\t' or
                next_char == '\n' or next_char == '\r' or next_char == '/')
            {
                // This is a valid tag match
                const tag_end = std.mem.indexOfPos(u8, xml, start, ">") orelse return null;
                const end = std.mem.indexOfPos(u8, xml, tag_end, close_tag) orelse return null;
                return xml[tag_end + 1 .. end];
            }
        }
        // Not a valid match, continue searching
        pos = start + open_tag.len;
    }

    return null;
}
// ANCHOR_END: find_element

/// Parse a simple XML element
pub fn parseSimpleElement(
    allocator: std.mem.Allocator,
    xml: []const u8,
    tag: []const u8,
) !?XmlElement {
    const content = findElement(xml, tag) orelse return null;

    const element = XmlElement{
        .name = tag,
        .attributes = std.StringHashMap([]const u8).init(allocator),
        .text = content,
        .allocator = allocator,
    };

    return element;
}

// ANCHOR: parse_attributes
/// Parse attributes from an XML tag
pub fn parseAttributes(
    allocator: std.mem.Allocator,
    tag_content: []const u8,
) !std.StringHashMap([]const u8) {
    var attrs = std.StringHashMap([]const u8).init(allocator);
    errdefer attrs.deinit();

    // First, remove the element name
    const first_space = std.mem.indexOfAny(u8, tag_content, " \t\n\r") orelse return attrs;
    const attrs_part = std.mem.trim(u8, tag_content[first_space..], " \t\n\r");

    var i: usize = 0;
    while (i < attrs_part.len) {
        // Skip whitespace
        while (i < attrs_part.len and (attrs_part[i] == ' ' or attrs_part[i] == '\t' or attrs_part[i] == '\n' or attrs_part[i] == '\r')) {
            i += 1;
        }
        if (i >= attrs_part.len) break;

        // Find key
        const key_start = i;
        while (i < attrs_part.len and attrs_part[i] != '=' and attrs_part[i] != ' ' and attrs_part[i] != '\t') {
            i += 1;
        }
        const key = std.mem.trim(u8, attrs_part[key_start..i], " \t");

        // Skip whitespace and =
        while (i < attrs_part.len and (attrs_part[i] == ' ' or attrs_part[i] == '\t' or attrs_part[i] == '=')) {
            i += 1;
        }
        if (i >= attrs_part.len) break;

        // Find value
        var value: []const u8 = undefined;
        if (attrs_part[i] == '"') {
            // Quoted value
            i += 1;
            const value_start = i;
            while (i < attrs_part.len and attrs_part[i] != '"') {
                i += 1;
            }
            value = attrs_part[value_start..i];
            if (i < attrs_part.len) i += 1; // Skip closing quote
        } else {
            // Unquoted value
            const value_start = i;
            while (i < attrs_part.len and attrs_part[i] != ' ' and attrs_part[i] != '\t') {
                i += 1;
            }
            value = attrs_part[value_start..i];
        }

        try attrs.put(key, value);
    }

    return attrs;
}
// ANCHOR_END: parse_attributes

// ANCHOR: find_all_elements
/// Find all elements with a given tag
/// NOTE: This is a naive implementation for simple, well-formed XML.
/// For robust parsing, see recipe_6_4.zig (StreamingXmlParser).
pub fn findAllElements(
    allocator: std.mem.Allocator,
    xml: []const u8,
    tag: []const u8,
) ![][]const u8 {
    var results: std.ArrayList([]const u8) = .{};
    errdefer results.deinit(allocator);

    const open_tag = try std.fmt.allocPrint(allocator, "<{s}", .{tag});
    defer allocator.free(open_tag);

    const close_tag = try std.fmt.allocPrint(allocator, "</{s}>", .{tag});
    defer allocator.free(close_tag);

    var pos: usize = 0;
    while (std.mem.indexOfPos(u8, xml, pos, open_tag)) |start| {
        // Verify this is an exact tag match, not a prefix
        // e.g., searching for <user should not match <username>
        const char_after_tag = start + open_tag.len;
        if (char_after_tag < xml.len) {
            const next_char = xml[char_after_tag];
            // Check for valid tag boundaries: '>', ' ', '\t', '\n', '\r', '/'
            if (next_char == '>' or next_char == ' ' or next_char == '\t' or
                next_char == '\n' or next_char == '\r' or next_char == '/')
            {
                // This is a valid tag match
                const tag_end = std.mem.indexOfPos(u8, xml, start, ">") orelse break;
                const end = std.mem.indexOfPos(u8, xml, tag_end, close_tag) orelse break;

                const content = xml[tag_end + 1 .. end];
                try results.append(allocator, content);

                pos = end + close_tag.len;
                continue;
            }
        }
        // Not a valid match, continue searching
        pos = start + open_tag.len;
    }

    return try results.toOwnedSlice(allocator);
}
// ANCHOR_END: find_all_elements

/// Unescape XML entities
pub fn unescapeXml(allocator: std.mem.Allocator, text: []const u8) ![]u8 {
    var result: std.ArrayList(u8) = .{};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i < text.len) {
        if (text[i] == '&') {
            if (std.mem.startsWith(u8, text[i..], "&lt;")) {
                try result.append(allocator, '<');
                i += 4;
            } else if (std.mem.startsWith(u8, text[i..], "&gt;")) {
                try result.append(allocator, '>');
                i += 4;
            } else if (std.mem.startsWith(u8, text[i..], "&amp;")) {
                try result.append(allocator, '&');
                i += 5;
            } else if (std.mem.startsWith(u8, text[i..], "&quot;")) {
                try result.append(allocator, '"');
                i += 6;
            } else if (std.mem.startsWith(u8, text[i..], "&apos;")) {
                try result.append(allocator, '\'');
                i += 6;
            } else {
                try result.append(allocator, text[i]);
                i += 1;
            }
        } else {
            try result.append(allocator, text[i]);
            i += 1;
        }
    }

    return try result.toOwnedSlice(allocator);
}

/// Check if XML is well-formed
pub fn isWellFormed(xml: []const u8) bool {
    var depth: i32 = 0;
    var i: usize = 0;

    while (i < xml.len) {
        if (xml[i] == '<') {
            if (i + 1 < xml.len and xml[i + 1] == '/') {
                // Closing tag
                depth -= 1;
                if (depth < 0) return false;
            } else if (i + 1 < xml.len and xml[i + 1] != '!' and xml[i + 1] != '?') {
                // Opening tag (skip comments and declarations)
                depth += 1;
            }
        }
        i += 1;
    }

    return depth == 0;
}

/// Read XML from file
pub fn parseXmlFile(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const xml_content = try file.readToEndAlloc(allocator, 10 * 1024 * 1024);
    return xml_content;
}

/// XML parsing errors
pub const XmlError = error{
    MalformedXml,
    UnexpectedEndOfInput,
    InvalidTag,
};

/// Parse element with error handling
pub fn parseElementSafe(xml: []const u8, tag: []const u8) XmlError![]const u8 {
    if (!isWellFormed(xml)) {
        return error.MalformedXml;
    }

    const content = findElement(xml, tag) orelse return error.InvalidTag;

    return content;
}

// Tests

test "find xml element" {
    const xml = "<root><name>Alice</name><age>30</age></root>";

    const name = findElement(xml, "name").?;
    try std.testing.expectEqualStrings("Alice", name);

    const age = findElement(xml, "age").?;
    try std.testing.expectEqualStrings("30", age);
}

test "find element not found" {
    const xml = "<root><name>Alice</name></root>";

    const missing = findElement(xml, "missing");
    try std.testing.expect(missing == null);
}

test "parse simple element" {
    const xml = "<user>Alice</user>";

    var element = (try parseSimpleElement(
        std.testing.allocator,
        xml,
        "user",
    )).?;
    defer element.deinit();

    try std.testing.expectEqualStrings("user", element.name);
    try std.testing.expectEqualStrings("Alice", element.text.?);
}

test "parse element with no content" {
    const xml = "<root></root>";

    var element = (try parseSimpleElement(
        std.testing.allocator,
        xml,
        "root",
    )).?;
    defer element.deinit();

    try std.testing.expectEqualStrings("", element.text.?);
}

test "parse attributes" {
    const tag = "user id=\"123\" name=\"Alice\"";

    var attrs = try parseAttributes(std.testing.allocator, tag);
    defer attrs.deinit();

    try std.testing.expectEqualStrings("123", attrs.get("id").?);
    try std.testing.expectEqualStrings("Alice", attrs.get("name").?);
}

test "parse attributes with spaces" {
    const tag = "img src = \"image.png\"  alt = \"Picture\"  ";

    var attrs = try parseAttributes(std.testing.allocator, tag);
    defer attrs.deinit();

    try std.testing.expectEqualStrings("image.png", attrs.get("src").?);
    try std.testing.expectEqualStrings("Picture", attrs.get("alt").?);
}

test "parse single attribute" {
    const tag = "link href=\"/path\"";

    var attrs = try parseAttributes(std.testing.allocator, tag);
    defer attrs.deinit();

    try std.testing.expectEqualStrings("/path", attrs.get("href").?);
}

test "find all elements" {
    const xml =
        \\<users>
        \\  <user>Alice</user>
        \\  <user>Bob</user>
        \\  <user>Charlie</user>
        \\</users>
    ;

    const users = try findAllElements(std.testing.allocator, xml, "user");
    defer std.testing.allocator.free(users);

    try std.testing.expectEqual(@as(usize, 3), users.len);
    try std.testing.expect(std.mem.indexOf(u8, users[0], "Alice") != null);
    try std.testing.expect(std.mem.indexOf(u8, users[1], "Bob") != null);
    try std.testing.expect(std.mem.indexOf(u8, users[2], "Charlie") != null);
}

test "find all elements empty" {
    const xml = "<root></root>";

    const items = try findAllElements(std.testing.allocator, xml, "item");
    defer std.testing.allocator.free(items);

    try std.testing.expectEqual(@as(usize, 0), items.len);
}

test "nested elements" {
    const xml =
        \\<person>
        \\  <name>Alice</name>
        \\  <address>
        \\    <city>New York</city>
        \\    <zip>10001</zip>
        \\  </address>
        \\</person>
    ;

    const name = findElement(xml, "name").?;
    try std.testing.expect(std.mem.indexOf(u8, name, "Alice") != null);

    const address = findElement(xml, "address").?;
    const city = findElement(address, "city").?;
    try std.testing.expect(std.mem.indexOf(u8, city, "New York") != null);

    const zip = findElement(address, "zip").?;
    try std.testing.expect(std.mem.indexOf(u8, zip, "10001") != null);
}

test "deeply nested elements" {
    const xml =
        \\<root>
        \\  <level1>
        \\    <level2>
        \\      <level3>Deep</level3>
        \\    </level2>
        \\  </level1>
        \\</root>
    ;

    const level1 = findElement(xml, "level1").?;
    const level2 = findElement(level1, "level2").?;
    const level3 = findElement(level2, "level3").?;
    try std.testing.expect(std.mem.indexOf(u8, level3, "Deep") != null);
}

test "unescape xml" {
    const escaped = "Hello &lt;world&gt; &amp; &quot;friends&quot;";

    const unescaped = try unescapeXml(std.testing.allocator, escaped);
    defer std.testing.allocator.free(unescaped);

    try std.testing.expectEqualStrings("Hello <world> & \"friends\"", unescaped);
}

test "unescape xml with apostrophe" {
    const escaped = "It&apos;s working";

    const unescaped = try unescapeXml(std.testing.allocator, escaped);
    defer std.testing.allocator.free(unescaped);

    try std.testing.expectEqualStrings("It's working", unescaped);
}

test "unescape xml no entities" {
    const text = "Plain text";

    const result = try unescapeXml(std.testing.allocator, text);
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("Plain text", result);
}

test "validate xml well formed" {
    try std.testing.expect(isWellFormed("<root><child>text</child></root>"));
    try std.testing.expect(isWellFormed("<a><b><c></c></b></a>"));
    try std.testing.expect(isWellFormed("<empty></empty>"));
}

test "validate xml malformed" {
    try std.testing.expect(!isWellFormed("<root><child>text</root>"));
    try std.testing.expect(!isWellFormed("<root><child>text</child>"));
    try std.testing.expect(!isWellFormed("</root>"));
    try std.testing.expect(!isWellFormed("<root></child></root>"));
}

test "validate xml with comments" {
    const xml = "<!-- Comment --><root>text</root>";
    try std.testing.expect(isWellFormed(xml));
}

test "validate xml with declaration" {
    const xml = "<?xml version=\"1.0\"?><root>text</root>";
    try std.testing.expect(isWellFormed(xml));
}

test "read xml file" {
    const xml_content = "<test>content</test>";

    // Create temporary file
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    var tmp_file = try tmp_dir.dir.createFile("test.xml", .{});
    try tmp_file.writeAll(xml_content);
    tmp_file.close();

    // Read it back using the tmp_dir
    const file = try tmp_dir.dir.openFile("test.xml", .{});
    defer file.close();

    const content = try file.readToEndAlloc(std.testing.allocator, 10 * 1024 * 1024);
    defer std.testing.allocator.free(content);

    try std.testing.expectEqualStrings(xml_content, content);
}

test "read xml file not found" {
    const result = parseXmlFile(std.testing.allocator, "nonexistent.xml");
    try std.testing.expectError(error.FileNotFound, result);
}

test "error handling invalid tag" {
    const bad_xml = "<root><child>text</child></root>";

    const result = parseElementSafe(bad_xml, "missing");
    try std.testing.expectError(error.InvalidTag, result);
}

test "error handling malformed xml" {
    const bad_xml = "<root><unclosed>";

    const result = parseElementSafe(bad_xml, "root");
    try std.testing.expectError(error.MalformedXml, result);
}

test "parse element safe success" {
    const xml = "<root><child>text</child></root>";

    const result = try parseElementSafe(xml, "child");
    try std.testing.expectEqualStrings("text", result);
}

test "xml with whitespace" {
    const xml =
        \\  <root>
        \\    <name>  Alice  </name>
        \\  </root>
    ;

    const name = findElement(xml, "name").?;
    const trimmed = std.mem.trim(u8, name, " \n\r\t");
    try std.testing.expectEqualStrings("Alice", trimmed);
}

test "xml with mixed content" {
    const xml = "<p>Hello <b>world</b>!</p>";

    const p = findElement(xml, "p").?;
    try std.testing.expect(std.mem.indexOf(u8, p, "Hello") != null);
    try std.testing.expect(std.mem.indexOf(u8, p, "world") != null);

    const b = findElement(p, "b").?;
    try std.testing.expectEqualStrings("world", b);
}

test "xml self-closing tags" {
    const xml = "<root><item/><item/></root>";

    // Self-closing tags won't be found by our simple parser
    // This test documents the limitation
    const items = try findAllElements(std.testing.allocator, xml, "item");
    defer std.testing.allocator.free(items);

    // Our simple parser doesn't handle self-closing tags
    try std.testing.expectEqual(@as(usize, 0), items.len);
}

test "xml with numbers" {
    const xml = "<data><count>42</count><price>19.99</price></data>";

    const count_str = findElement(xml, "count").?;
    const count = try std.fmt.parseInt(i32, count_str, 10);
    try std.testing.expectEqual(@as(i32, 42), count);

    const price_str = findElement(xml, "price").?;
    const price = try std.fmt.parseFloat(f32, price_str);
    try std.testing.expectApproxEqRel(@as(f32, 19.99), price, 0.01);
}

test "xml empty string" {
    const xml = "";

    const result = findElement(xml, "root");
    try std.testing.expect(result == null);
}

test "xml single element" {
    const xml = "<root>value</root>";

    const root = findElement(xml, "root").?;
    try std.testing.expectEqualStrings("value", root);
}

test "xml unicode content" {
    const xml = "<message>こんにちは世界</message>";

    const message = findElement(xml, "message").?;
    try std.testing.expectEqualStrings("こんにちは世界", message);
}

test "xml boolean values" {
    const xml = "<config><enabled>true</enabled><debug>false</debug></config>";

    const enabled_str = findElement(xml, "enabled").?;
    const enabled = std.mem.eql(u8, enabled_str, "true");
    try std.testing.expect(enabled);

    const debug_str = findElement(xml, "debug").?;
    const debug = std.mem.eql(u8, debug_str, "true");
    try std.testing.expect(!debug);
}

test "tag name prefix matching bug fix" {
    // This test verifies that searching for <user> doesn't match <username>
    const xml =
        \\<root>
        \\  <user>Alice</user>
        \\  <username>alice123</username>
        \\  <user_id>42</user_id>
        \\  <user>Bob</user>
        \\</root>
    ;

    // Should only find <user> tags, not <username> or <user_id>
    const users = try findAllElements(std.testing.allocator, xml, "user");
    defer std.testing.allocator.free(users);

    try std.testing.expectEqual(@as(usize, 2), users.len);
    try std.testing.expect(std.mem.indexOf(u8, users[0], "Alice") != null);
    try std.testing.expect(std.mem.indexOf(u8, users[1], "Bob") != null);

    // Verify username tag exists separately
    const username = findElement(xml, "username").?;
    try std.testing.expect(std.mem.indexOf(u8, username, "alice123") != null);

    // Verify user_id tag exists separately
    const user_id = findElement(xml, "user_id").?;
    try std.testing.expect(std.mem.indexOf(u8, user_id, "42") != null);
}

test "exact tag match with attributes" {
    // Test that tags with attributes are correctly identified
    const xml =
        \\<root>
        \\  <item id="1">First</item>
        \\  <itemized>Not an item tag</itemized>
        \\  <item id="2">Second</item>
        \\</root>
    ;

    const items = try findAllElements(std.testing.allocator, xml, "item");
    defer std.testing.allocator.free(items);

    // Should find 2 <item> tags, not <itemized>
    try std.testing.expectEqual(@as(usize, 2), items.len);
    try std.testing.expect(std.mem.indexOf(u8, items[0], "First") != null);
    try std.testing.expect(std.mem.indexOf(u8, items[1], "Second") != null);

    // Verify itemized tag is separate
    const itemized = findElement(xml, "itemized").?;
    try std.testing.expect(std.mem.indexOf(u8, itemized, "Not an item tag") != null);
}
```

---

## Recipe 6.4: Parsing and Modifying XML {#recipe-6-4}

**Tags:** allocators, arena-allocator, arraylist, comptime, data-encoding, data-structures, error-handling, memory, parsing, resource-cleanup, testing, xml
**Difficulty:** intermediate
**Code:** `code/03-advanced/06-data-encoding/recipe_6_4.zig`

### Problem

You need to parse very large XML files that don't fit comfortably in memory, or you want to start processing data before the entire file is read.

### Solution

### Streaming Parser

```zig
/// Streaming XML parser for processing large files
pub const StreamingXmlParser = struct {
    file: std.fs.File,
    buffer: [4096]u8,
    pos: usize,
    end: usize,

    pub fn init(file: std.fs.File) StreamingXmlParser {
        return .{
            .file = file,
            .buffer = undefined,
            .pos = 0,
            .end = 0,
        };
    }

    pub fn next(self: *StreamingXmlParser, allocator: std.mem.Allocator) !XmlEvent {
        while (true) {
            // Refill buffer if needed
            if (self.pos >= self.end) {
                self.end = try self.file.read(&self.buffer);
                self.pos = 0;
                if (self.end == 0) {
                    return XmlEvent.eof;
                }
            }

            // Skip whitespace
            while (self.pos < self.end and std.ascii.isWhitespace(self.buffer[self.pos])) {
                self.pos += 1;
            }

            if (self.pos >= self.end) continue;

            // Check for tag start
            if (self.buffer[self.pos] == '<') {
                return try self.parseTag(allocator);
            } else {
                if (try self.parseText(allocator)) |event| {
                    return event;
                }
                // Empty text, continue to next event
                continue;
            }
        }
    }

    fn parseTag(self: *StreamingXmlParser, allocator: std.mem.Allocator) !XmlEvent {
        self.pos += 1; // Skip '<'

        // Check for end tag
        const is_end_tag = if (self.pos < self.end) self.buffer[self.pos] == '/' else false;
        if (is_end_tag) {
            self.pos += 1;
        }

        // Find tag name end
        const start = self.pos;
        while (self.pos < self.end and self.buffer[self.pos] != '>' and self.buffer[self.pos] != '/' and !std.ascii.isWhitespace(self.buffer[self.pos])) {
            self.pos += 1;
        }

        const name = try allocator.dupe(u8, self.buffer[start..self.pos]);

        // Check for self-closing tag
        var is_self_closing = false;
        while (self.pos < self.end and self.buffer[self.pos] != '>') {
            if (self.buffer[self.pos] == '/') {
                is_self_closing = true;
            }
            self.pos += 1;
        }
        if (self.pos < self.end) {
            self.pos += 1; // Skip '>'
        }

        if (is_end_tag) {
            return XmlEvent{ .end_element = .{ .name = name } };
        } else {
            // For self-closing tags, we only return start_element
            // The caller needs to handle this specially if needed
            return XmlEvent{ .start_element = .{ .name = name } };
        }
    }

    fn parseText(self: *StreamingXmlParser, allocator: std.mem.Allocator) error{OutOfMemory}!?XmlEvent {
        const start = self.pos;

        while (self.pos < self.end and self.buffer[self.pos] != '<') {
            self.pos += 1;
        }

        // NOTE: This implementation trims whitespace for simplicity, which is appropriate
        // for data-centric XML (like config files). For document-oriented XML with mixed
        // content (e.g., "<b>Bold</b> <i>text</i>"), whitespace can be significant.
        // In production, consider making whitespace handling configurable based on your use case.
        const text = std.mem.trim(u8, self.buffer[start..self.pos], &std.ascii.whitespace);
        if (text.len == 0) {
            return null; // Skip empty text, caller will continue parsing
        }

        return XmlEvent{ .text = .{ .content = try allocator.dupe(u8, text) } };
    }
};
```

### Process Large XML

```zig
/// Process large XML file counting elements
pub fn processLargeXml(file: std.fs.File, allocator: std.mem.Allocator) !usize {
    var parser = StreamingXmlParser.init(file);
    var count: usize = 0;

    while (true) {
        const event = try parser.next(allocator);

        switch (event) {
            .start_element => |elem| {
                defer allocator.free(elem.name);
                count += 1;
            },
            .end_element => |elem| {
                defer allocator.free(elem.name);
            },
            .text => |text| {
                defer allocator.free(text.content);
            },
            .eof => break,
        }
    }

    return count;
}
```

### Extract Elements

```zig
/// Extract text content from specific elements
pub fn extractElements(
    file: std.fs.File,
    allocator: std.mem.Allocator,
    target_name: []const u8,
) !std.ArrayList([]const u8) {
    var parser = StreamingXmlParser.init(file);
    var results = std.ArrayList([]const u8){};
    errdefer {
        for (results.items) |item| {
            allocator.free(item);
        }
        results.deinit(allocator);
    }

    var in_target = false;

    while (true) {
        const event = try parser.next(allocator);

        switch (event) {
            .start_element => |elem| {
                if (std.mem.eql(u8, elem.name, target_name)) {
                    in_target = true;
                }
                allocator.free(elem.name);
            },
            .end_element => |elem| {
                if (std.mem.eql(u8, elem.name, target_name)) {
                    in_target = false;
                }
                allocator.free(elem.name);
            },
            .text => |text| {
                if (in_target) {
                    try results.append(allocator, try allocator.dupe(u8, text.content));
                }
                allocator.free(text.content);
            },
            .eof => break,
        }
    }

    return results;
}
```

            if (self.pos >= self.end) continue;

            // Check for tag start
            if (self.buffer[self.pos] == '<') {
                return try self.parseTag(allocator);
            } else {
                return try self.parseText(allocator);
            }
        }
    }

    fn parseTag(self: *StreamingXmlParser, allocator: std.mem.Allocator) !XmlEvent {
        self.pos += 1; // Skip '<'

        // Check for end tag
        const is_end_tag = if (self.pos < self.end) self.buffer[self.pos] == '/' else false;
        if (is_end_tag) {
            self.pos += 1;
        }

        // Find tag name end
        const start = self.pos;
        while (self.pos < self.end and self.buffer[self.pos] != '>' and !std.ascii.isWhitespace(self.buffer[self.pos])) {
            self.pos += 1;
        }

        const name = try allocator.dupe(u8, self.buffer[start..self.pos]);

        // Skip to end of tag
        while (self.pos < self.end and self.buffer[self.pos] != '>') {
            self.pos += 1;
        }
        if (self.pos < self.end) {
            self.pos += 1; // Skip '>'
        }

        if (is_end_tag) {
            return XmlEvent{ .end_element = .{ .name = name } };
        } else {
            return XmlEvent{ .start_element = .{ .name = name } };
        }
    }

    fn parseText(self: *StreamingXmlParser, allocator: std.mem.Allocator) !XmlEvent {
        const start = self.pos;

        while (self.pos < self.end and self.buffer[self.pos] != '<') {
            self.pos += 1;
        }

        const text = std.mem.trim(u8, self.buffer[start..self.pos], &std.ascii.whitespace);
        if (text.len == 0) {
            return self.next(allocator);
        }

        return XmlEvent{ .text = .{ .content = try allocator.dupe(u8, text) } };
    }
};

test "streaming XML parser" {
    const allocator = std.testing.allocator;

    const xml_data = "<root><item>value</item></root>";

    const file = try std.fs.cwd().createFile("/tmp/test_stream.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_stream.xml") catch {};

    try file.writeAll(xml_data);
    try file.seekTo(0);

    var parser = StreamingXmlParser.init(file);

    const event1 = try parser.next(allocator);
    defer if (event1 == .start_element) allocator.free(event1.start_element.name);
    try std.testing.expect(event1 == .start_element);
    try std.testing.expectEqualStrings("root", event1.start_element.name);

    const event2 = try parser.next(allocator);
    defer if (event2 == .start_element) allocator.free(event2.start_element.name);
    try std.testing.expect(event2 == .start_element);

    const event3 = try parser.next(allocator);
    defer if (event3 == .text) allocator.free(event3.text.content);
    try std.testing.expect(event3 == .text);
}
```

### Discussion

### Streaming Parser Benefits

Memory-efficient processing:

```zig
pub fn processLargeXml(file: std.fs.File, allocator: std.mem.Allocator) !usize {
    var parser = StreamingXmlParser.init(file);
    var count: usize = 0;

    while (true) {
        const event = try parser.next(allocator);

        switch (event) {
            .start_element => |elem| {
                defer allocator.free(elem.name);
                count += 1;
            },
            .end_element => |elem| {
                defer allocator.free(elem.name);
            },
            .text => |text| {
                defer allocator.free(text.content);
            },
            .eof => break,
        }
    }

    return count;
}

test "process large XML" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/large.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/large.xml") catch {};

    try file.writeAll("<root><a/><b/><c/></root>");
    try file.seekTo(0);

    const count = try processLargeXml(file, allocator);
    try std.testing.expectEqual(@as(usize, 4), count);
}
```

### Extracting Specific Elements

Filter while parsing:

```zig
pub fn extractElements(
    file: std.fs.File,
    allocator: std.mem.Allocator,
    target_name: []const u8,
) !std.ArrayList([]const u8) {
    var parser = StreamingXmlParser.init(file);
    var results = std.ArrayList([]const u8){};
    errdefer {
        for (results.items) |item| {
            allocator.free(item);
        }
        results.deinit(allocator);
    }

    var in_target = false;

    while (true) {
        const event = try parser.next(allocator);

        switch (event) {
            .start_element => |elem| {
                if (std.mem.eql(u8, elem.name, target_name)) {
                    in_target = true;
                }
                allocator.free(elem.name);
            },
            .end_element => |elem| {
                if (std.mem.eql(u8, elem.name, target_name)) {
                    in_target = false;
                }
                allocator.free(elem.name);
            },
            .text => |text| {
                if (in_target) {
                    try results.append(allocator, try allocator.dupe(u8, text.content));
                }
                allocator.free(text.content);
            },
            .eof => break,
        }
    }

    return results;
}

test "extract specific elements" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/extract.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/extract.xml") catch {};

    try file.writeAll("<root><item>A</item><other>B</other><item>C</item></root>");
    try file.seekTo(0);

    var results = try extractElements(file, allocator, "item");
    defer {
        for (results.items) |item| {
            allocator.free(item);
        }
        results.deinit(allocator);
    }

    try std.testing.expectEqual(@as(usize, 2), results.items.len);
}
```

### Counting Elements

Process without storing:

```zig
pub fn countElements(
    file: std.fs.File,
    allocator: std.mem.Allocator,
    element_name: []const u8,
) !usize {
    var parser = StreamingXmlParser.init(file);
    var count: usize = 0;

    while (true) {
        const event = try parser.next(allocator);

        switch (event) {
            .start_element => |elem| {
                if (std.mem.eql(u8, elem.name, element_name)) {
                    count += 1;
                }
                allocator.free(elem.name);
            },
            .end_element => |elem| {
                allocator.free(elem.name);
            },
            .text => |text| {
                allocator.free(text.content);
            },
            .eof => break,
        }
    }

    return count;
}

test "count elements" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/count.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/count.xml") catch {};

    try file.writeAll("<root><item/><item/><item/></root>");
    try file.seekTo(0);

    const count = try countElements(file, allocator, "item");
    try std.testing.expectEqual(@as(usize, 3), count);
}
```

### Buffered Reading

Optimize I/O with larger buffers:

```zig
pub fn StreamingXmlParserBuffered(comptime buffer_size: usize) type {
    return struct {
        const Self = @This();

        reader: std.fs.File.Reader,
        buffer: [buffer_size]u8,
        pos: usize,
        end: usize,

        pub fn init(file: std.fs.File) Self {
            return .{
                .reader = file.reader(),
                .buffer = undefined,
                .pos = 0,
                .end = 0,
            };
        }

        pub fn next(self: *Self, allocator: std.mem.Allocator) !XmlEvent {
            // Same implementation as StreamingXmlParser
            _ = allocator;
            _ = self;
            return XmlEvent.eof;
        }
    };
}

test "buffered parser" {
    const Parser = StreamingXmlParserBuffered(8192);
    const file = try std.fs.cwd().createFile("/tmp/buffered.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/buffered.xml") catch {};

    var parser = Parser.init(file);
    _ = parser;
}
```

### Processing in Chunks

Handle data in manageable pieces:

```zig
pub fn processXmlChunk(
    parser: *StreamingXmlParser,
    allocator: std.mem.Allocator,
    max_events: usize,
) !usize {
    var processed: usize = 0;

    while (processed < max_events) {
        const event = try parser.next(allocator);

        switch (event) {
            .start_element => |elem| {
                defer allocator.free(elem.name);
                processed += 1;
            },
            .end_element => |elem| {
                defer allocator.free(elem.name);
                processed += 1;
            },
            .text => |text| {
                defer allocator.free(text.content);
                processed += 1;
            },
            .eof => break,
        }
    }

    return processed;
}

test "process in chunks" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/chunks.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/chunks.xml") catch {};

    try file.writeAll("<root><a/><b/><c/></root>");
    try file.seekTo(0);

    var parser = StreamingXmlParser.init(file);

    const chunk1 = try processXmlChunk(&parser, allocator, 3);
    try std.testing.expect(chunk1 > 0);
}
```

### Best Practices

**Memory management:**
- Free event data immediately after processing
- Use arena allocator for temporary data
- Process in chunks for bounded memory usage

**Error handling:**
```zig
pub fn safeProcessXml(file: std.fs.File, allocator: std.mem.Allocator) !void {
    var parser = StreamingXmlParser.init(file);

    while (true) {
        const event = parser.next(allocator) catch |err| {
            std.log.err("XML parsing error: {}", .{err});
            return err;
        };

        switch (event) {
            .start_element => |elem| {
                defer allocator.free(elem.name);
                // Process
            },
            .end_element => |elem| {
                defer allocator.free(elem.name);
            },
            .text => |text| {
                defer allocator.free(text.content);
            },
            .eof => break,
        }
    }
}
```

**Performance:**
- Use larger buffers for sequential reads
- Minimize allocations by reusing buffers
- Process events immediately instead of storing
- Consider using `std.io.BufferedReader`

**Robustness:**
- Handle malformed XML gracefully
- Validate structure during parsing
- Implement depth tracking for nesting
- Support entity decoding

### Related Functions

- `std.fs.File.reader()` - Get file reader
- `std.io.BufferedReader()` - Add buffering
- `std.mem.trim()` - Trim whitespace
- `std.ascii.isWhitespace()` - Check whitespace
- `std.ArrayList()` - Dynamic array for results
- `std.mem.eql()` - String comparison

### Full Tested Code

```zig
const std = @import("std");

/// XML event types for streaming parser
pub const XmlEvent = union(enum) {
    start_element: struct {
        name: []const u8,
    },
    end_element: struct {
        name: []const u8,
    },
    text: struct {
        content: []const u8,
    },
    eof,
};

// ANCHOR: streaming_parser
/// Streaming XML parser for processing large files
pub const StreamingXmlParser = struct {
    file: std.fs.File,
    buffer: [4096]u8,
    pos: usize,
    end: usize,

    pub fn init(file: std.fs.File) StreamingXmlParser {
        return .{
            .file = file,
            .buffer = undefined,
            .pos = 0,
            .end = 0,
        };
    }

    pub fn next(self: *StreamingXmlParser, allocator: std.mem.Allocator) !XmlEvent {
        while (true) {
            // Refill buffer if needed
            if (self.pos >= self.end) {
                self.end = try self.file.read(&self.buffer);
                self.pos = 0;
                if (self.end == 0) {
                    return XmlEvent.eof;
                }
            }

            // Skip whitespace
            while (self.pos < self.end and std.ascii.isWhitespace(self.buffer[self.pos])) {
                self.pos += 1;
            }

            if (self.pos >= self.end) continue;

            // Check for tag start
            if (self.buffer[self.pos] == '<') {
                return try self.parseTag(allocator);
            } else {
                if (try self.parseText(allocator)) |event| {
                    return event;
                }
                // Empty text, continue to next event
                continue;
            }
        }
    }

    fn parseTag(self: *StreamingXmlParser, allocator: std.mem.Allocator) !XmlEvent {
        self.pos += 1; // Skip '<'

        // Check for end tag
        const is_end_tag = if (self.pos < self.end) self.buffer[self.pos] == '/' else false;
        if (is_end_tag) {
            self.pos += 1;
        }

        // Find tag name end
        const start = self.pos;
        while (self.pos < self.end and self.buffer[self.pos] != '>' and self.buffer[self.pos] != '/' and !std.ascii.isWhitespace(self.buffer[self.pos])) {
            self.pos += 1;
        }

        const name = try allocator.dupe(u8, self.buffer[start..self.pos]);

        // Check for self-closing tag
        var is_self_closing = false;
        while (self.pos < self.end and self.buffer[self.pos] != '>') {
            if (self.buffer[self.pos] == '/') {
                is_self_closing = true;
            }
            self.pos += 1;
        }
        if (self.pos < self.end) {
            self.pos += 1; // Skip '>'
        }

        if (is_end_tag) {
            return XmlEvent{ .end_element = .{ .name = name } };
        } else {
            // For self-closing tags, we only return start_element
            // The caller needs to handle this specially if needed
            return XmlEvent{ .start_element = .{ .name = name } };
        }
    }

    fn parseText(self: *StreamingXmlParser, allocator: std.mem.Allocator) error{OutOfMemory}!?XmlEvent {
        const start = self.pos;

        while (self.pos < self.end and self.buffer[self.pos] != '<') {
            self.pos += 1;
        }

        // NOTE: This implementation trims whitespace for simplicity, which is appropriate
        // for data-centric XML (like config files). For document-oriented XML with mixed
        // content (e.g., "<b>Bold</b> <i>text</i>"), whitespace can be significant.
        // In production, consider making whitespace handling configurable based on your use case.
        const text = std.mem.trim(u8, self.buffer[start..self.pos], &std.ascii.whitespace);
        if (text.len == 0) {
            return null; // Skip empty text, caller will continue parsing
        }

        return XmlEvent{ .text = .{ .content = try allocator.dupe(u8, text) } };
    }
};
// ANCHOR_END: streaming_parser

// ANCHOR: process_large_xml
/// Process large XML file counting elements
pub fn processLargeXml(file: std.fs.File, allocator: std.mem.Allocator) !usize {
    var parser = StreamingXmlParser.init(file);
    var count: usize = 0;

    while (true) {
        const event = try parser.next(allocator);

        switch (event) {
            .start_element => |elem| {
                defer allocator.free(elem.name);
                count += 1;
            },
            .end_element => |elem| {
                defer allocator.free(elem.name);
            },
            .text => |text| {
                defer allocator.free(text.content);
            },
            .eof => break,
        }
    }

    return count;
}
// ANCHOR_END: process_large_xml

// ANCHOR: extract_elements
/// Extract text content from specific elements
pub fn extractElements(
    file: std.fs.File,
    allocator: std.mem.Allocator,
    target_name: []const u8,
) !std.ArrayList([]const u8) {
    var parser = StreamingXmlParser.init(file);
    var results = std.ArrayList([]const u8){};
    errdefer {
        for (results.items) |item| {
            allocator.free(item);
        }
        results.deinit(allocator);
    }

    var in_target = false;

    while (true) {
        const event = try parser.next(allocator);

        switch (event) {
            .start_element => |elem| {
                if (std.mem.eql(u8, elem.name, target_name)) {
                    in_target = true;
                }
                allocator.free(elem.name);
            },
            .end_element => |elem| {
                if (std.mem.eql(u8, elem.name, target_name)) {
                    in_target = false;
                }
                allocator.free(elem.name);
            },
            .text => |text| {
                if (in_target) {
                    try results.append(allocator, try allocator.dupe(u8, text.content));
                }
                allocator.free(text.content);
            },
            .eof => break,
        }
    }

    return results;
}
// ANCHOR_END: extract_elements

/// Count occurrences of specific element
pub fn countElements(
    file: std.fs.File,
    allocator: std.mem.Allocator,
    element_name: []const u8,
) !usize {
    var parser = StreamingXmlParser.init(file);
    var count: usize = 0;

    while (true) {
        const event = try parser.next(allocator);

        switch (event) {
            .start_element => |elem| {
                if (std.mem.eql(u8, elem.name, element_name)) {
                    count += 1;
                }
                allocator.free(elem.name);
            },
            .end_element => |elem| {
                allocator.free(elem.name);
            },
            .text => |text| {
                allocator.free(text.content);
            },
            .eof => break,
        }
    }

    return count;
}

/// Generic buffered streaming parser
pub fn StreamingXmlParserBuffered(comptime buffer_size: usize) type {
    return struct {
        const Self = @This();

        file: std.fs.File,
        buffer: [buffer_size]u8,
        pos: usize,
        end: usize,

        pub fn init(file: std.fs.File) Self {
            return .{
                .file = file,
                .buffer = undefined,
                .pos = 0,
                .end = 0,
            };
        }

        pub fn next(self: *Self, allocator: std.mem.Allocator) !XmlEvent {
            while (true) {
                // Refill buffer if needed
                if (self.pos >= self.end) {
                    self.end = try self.file.read(&self.buffer);
                    self.pos = 0;
                    if (self.end == 0) {
                        return XmlEvent.eof;
                    }
                }

                // Skip whitespace
                while (self.pos < self.end and std.ascii.isWhitespace(self.buffer[self.pos])) {
                    self.pos += 1;
                }

                if (self.pos >= self.end) continue;

                // Check for tag start
                if (self.buffer[self.pos] == '<') {
                    return try self.parseTag(allocator);
                } else {
                    if (try self.parseText(allocator)) |event| {
                        return event;
                    }
                    // Empty text, continue to next event
                    continue;
                }
            }
        }

        fn parseTag(self: *Self, allocator: std.mem.Allocator) !XmlEvent {
            self.pos += 1; // Skip '<'

            // Check for end tag
            const is_end_tag = if (self.pos < self.end) self.buffer[self.pos] == '/' else false;
            if (is_end_tag) {
                self.pos += 1;
            }

            // Find tag name end
            const start = self.pos;
            while (self.pos < self.end and self.buffer[self.pos] != '>' and self.buffer[self.pos] != '/' and !std.ascii.isWhitespace(self.buffer[self.pos])) {
                self.pos += 1;
            }

            const name = try allocator.dupe(u8, self.buffer[start..self.pos]);

            // Check for self-closing tag
            var is_self_closing = false;
            while (self.pos < self.end and self.buffer[self.pos] != '>') {
                if (self.buffer[self.pos] == '/') {
                    is_self_closing = true;
                }
                self.pos += 1;
            }
            if (self.pos < self.end) {
                self.pos += 1; // Skip '>'
            }

            if (is_end_tag) {
                return XmlEvent{ .end_element = .{ .name = name } };
            } else {
                // For self-closing tags, we only return start_element
                // The caller needs to handle this specially if needed
                return XmlEvent{ .start_element = .{ .name = name } };
            }
        }

        fn parseText(self: *Self, allocator: std.mem.Allocator) error{OutOfMemory}!?XmlEvent {
            const start = self.pos;

            while (self.pos < self.end and self.buffer[self.pos] != '<') {
                self.pos += 1;
            }

            // NOTE: This implementation trims whitespace for simplicity, which is appropriate
            // for data-centric XML (like config files). For document-oriented XML with mixed
            // content (e.g., "<b>Bold</b> <i>text</i>"), whitespace can be significant.
            // In production, consider making whitespace handling configurable based on your use case.
            const text = std.mem.trim(u8, self.buffer[start..self.pos], &std.ascii.whitespace);
            if (text.len == 0) {
                return null; // Skip empty text, caller will continue parsing
            }

            return XmlEvent{ .text = .{ .content = try allocator.dupe(u8, text) } };
        }
    };
}

/// Process XML in chunks
pub fn processXmlChunk(
    parser: *StreamingXmlParser,
    allocator: std.mem.Allocator,
    max_events: usize,
) !usize {
    var processed: usize = 0;

    while (processed < max_events) {
        const event = try parser.next(allocator);

        switch (event) {
            .start_element => |elem| {
                defer allocator.free(elem.name);
                processed += 1;
            },
            .end_element => |elem| {
                defer allocator.free(elem.name);
                processed += 1;
            },
            .text => |text| {
                defer allocator.free(text.content);
                processed += 1;
            },
            .eof => break,
        }
    }

    return processed;
}

/// Safe XML processing with error handling
pub fn safeProcessXml(file: std.fs.File, allocator: std.mem.Allocator) !void {
    var parser = StreamingXmlParser.init(file);

    while (true) {
        const event = parser.next(allocator) catch |err| {
            std.log.err("XML parsing error: {}", .{err});
            return err;
        };

        switch (event) {
            .start_element => |elem| {
                defer allocator.free(elem.name);
                // Process
            },
            .end_element => |elem| {
                defer allocator.free(elem.name);
            },
            .text => |text| {
                defer allocator.free(text.content);
            },
            .eof => break,
        }
    }
}

// Tests

test "streaming XML parser" {
    const allocator = std.testing.allocator;

    const xml_data = "<root><item>value</item></root>";

    const file = try std.fs.cwd().createFile("/tmp/test_stream.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/test_stream.xml") catch {};

    try file.writeAll(xml_data);
    try file.seekTo(0);

    var parser = StreamingXmlParser.init(file);

    const event1 = try parser.next(allocator);
    defer if (event1 == .start_element) allocator.free(event1.start_element.name);
    try std.testing.expect(event1 == .start_element);
    try std.testing.expectEqualStrings("root", event1.start_element.name);

    const event2 = try parser.next(allocator);
    defer if (event2 == .start_element) allocator.free(event2.start_element.name);
    try std.testing.expect(event2 == .start_element);

    const event3 = try parser.next(allocator);
    defer if (event3 == .text) allocator.free(event3.text.content);
    try std.testing.expect(event3 == .text);
}

test "process large XML" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/large.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/large.xml") catch {};

    try file.writeAll("<root><a/><b/><c/></root>");
    try file.seekTo(0);

    const count = try processLargeXml(file, allocator);
    try std.testing.expectEqual(@as(usize, 4), count);
}

test "extract specific elements" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/extract.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/extract.xml") catch {};

    try file.writeAll("<root><item>A</item><other>B</other><item>C</item></root>");
    try file.seekTo(0);

    var results = try extractElements(file, allocator, "item");
    defer {
        for (results.items) |item| {
            allocator.free(item);
        }
        results.deinit(allocator);
    }

    try std.testing.expectEqual(@as(usize, 2), results.items.len);
    try std.testing.expectEqualStrings("A", results.items[0]);
    try std.testing.expectEqualStrings("C", results.items[1]);
}

test "count elements" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/count.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/count.xml") catch {};

    try file.writeAll("<root><item/><item/><item/></root>");
    try file.seekTo(0);

    const count = try countElements(file, allocator, "item");
    try std.testing.expectEqual(@as(usize, 3), count);
}

test "buffered parser" {
    const Parser = StreamingXmlParserBuffered(8192);
    const file = try std.fs.cwd().createFile("/tmp/buffered.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/buffered.xml") catch {};

    try file.writeAll("<root><item/></root>");
    try file.seekTo(0);

    var parser = Parser.init(file);
    const allocator = std.testing.allocator;

    const event = try parser.next(allocator);
    defer if (event == .start_element) allocator.free(event.start_element.name);

    try std.testing.expect(event == .start_element);
}

test "process in chunks" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/chunks.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/chunks.xml") catch {};

    try file.writeAll("<root><a/><b/><c/></root>");
    try file.seekTo(0);

    var parser = StreamingXmlParser.init(file);

    const chunk1 = try processXmlChunk(&parser, allocator, 3);
    try std.testing.expect(chunk1 > 0);
}

test "empty XML" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/empty.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/empty.xml") catch {};

    try file.writeAll("");
    try file.seekTo(0);

    var parser = StreamingXmlParser.init(file);
    const event = try parser.next(allocator);

    try std.testing.expect(event == .eof);
}

test "nested elements" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/nested.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/nested.xml") catch {};

    try file.writeAll("<root><parent><child>text</child></parent></root>");
    try file.seekTo(0);

    var parser = StreamingXmlParser.init(file);

    // root start
    const e1 = try parser.next(allocator);
    defer if (e1 == .start_element) allocator.free(e1.start_element.name);
    try std.testing.expect(e1 == .start_element);

    // parent start
    const e2 = try parser.next(allocator);
    defer if (e2 == .start_element) allocator.free(e2.start_element.name);
    try std.testing.expect(e2 == .start_element);

    // child start
    const e3 = try parser.next(allocator);
    defer if (e3 == .start_element) allocator.free(e3.start_element.name);
    try std.testing.expect(e3 == .start_element);
}

test "self-closing tags" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/selfclose.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/selfclose.xml") catch {};

    try file.writeAll("<root><item/></root>");
    try file.seekTo(0);

    const count = try processLargeXml(file, allocator);
    try std.testing.expectEqual(@as(usize, 2), count);
}

test "XML with attributes" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/attrs.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/attrs.xml") catch {};

    try file.writeAll("<root><item id=\"1\">text</item></root>");
    try file.seekTo(0);

    var parser = StreamingXmlParser.init(file);

    const e1 = try parser.next(allocator);
    defer if (e1 == .start_element) allocator.free(e1.start_element.name);

    const e2 = try parser.next(allocator);
    defer if (e2 == .start_element) allocator.free(e2.start_element.name);
    try std.testing.expectEqualStrings("item", e2.start_element.name);
}

test "safe process XML" {
    const allocator = std.testing.allocator;

    const file = try std.fs.cwd().createFile("/tmp/safe.xml", .{ .read = true });
    defer file.close();
    defer std.fs.cwd().deleteFile("/tmp/safe.xml") catch {};

    try file.writeAll("<root><item/></root>");
    try file.seekTo(0);

    try safeProcessXml(file, allocator);
}
```

---

## Recipe 6.5: Turning a Dictionary into XML {#recipe-6-5}

**Tags:** allocators, arena-allocator, arraylist, comptime, data-encoding, data-structures, error-handling, hashmap, memory, parsing, resource-cleanup, slices, testing, xml
**Difficulty:** intermediate
**Code:** `code/03-advanced/06-data-encoding/recipe_6_5.zig`

### Problem

You need to convert Zig data structures (hash maps, structs, arrays) into XML format for configuration files, APIs, or data exchange.

### Solution

### Dict to XML

```zig
/// Convert hash map to XML
pub fn dictToXml(
    allocator: std.mem.Allocator,
    map: std.StringHashMap([]const u8),
    root_name: []const u8,
) ![]u8 {
    var xml = std.ArrayList(u8){};
    errdefer xml.deinit(allocator);

    // Write opening tag
    try xml.appendSlice(allocator, "<");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    // Write entries
    var iter = map.iterator();
    while (iter.next()) |entry| {
        try xml.appendSlice(allocator, "  <");
        try xml.appendSlice(allocator, entry.key_ptr.*);
        try xml.appendSlice(allocator, ">");

        // Escape value to prevent XML injection
        const escaped_value = try escapeXml(allocator, entry.value_ptr.*);
        defer allocator.free(escaped_value);
        try xml.appendSlice(allocator, escaped_value);

        try xml.appendSlice(allocator, "</");
        try xml.appendSlice(allocator, entry.key_ptr.*);
        try xml.appendSlice(allocator, ">\n");
    }

    // Write closing tag
    try xml.appendSlice(allocator, "</");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    return xml.toOwnedSlice(allocator);
}
```

### Struct to XML

```zig
/// Convert struct to XML using reflection
pub fn structToXml(
    allocator: std.mem.Allocator,
    comptime T: type,
    value: T,
    root_name: []const u8,
) ![]u8 {
    var xml = std.ArrayList(u8){};
    errdefer xml.deinit(allocator);

    try xml.appendSlice(allocator, "<");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    const info = @typeInfo(T);
    switch (info) {
        .@"struct" => |struct_info| {
            inline for (struct_info.fields) |field| {
                try xml.appendSlice(allocator, "  <");
                try xml.appendSlice(allocator, field.name);
                try xml.appendSlice(allocator, ">");

                const field_value = @field(value, field.name);
                const FieldType = @TypeOf(field_value);
                const field_str = if (FieldType == []const u8 or FieldType == []u8)
                    try std.fmt.allocPrint(allocator, "{s}", .{field_value})
                else
                    try std.fmt.allocPrint(allocator, "{any}", .{field_value});
                defer allocator.free(field_str);

                // Escape field value to prevent XML injection
                const escaped_field = try escapeXml(allocator, field_str);
                defer allocator.free(escaped_field);
                try xml.appendSlice(allocator, escaped_field);

                try xml.appendSlice(allocator, "</");
                try xml.appendSlice(allocator, field.name);
                try xml.appendSlice(allocator, ">\n");
            }
        },
        else => return error.UnsupportedType,
    }

    try xml.appendSlice(allocator, "</");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    return xml.toOwnedSlice(allocator);
}
```

### XML Writer

```zig
/// XML writer with pretty printing
pub const XmlWriter = struct {
    list: std.ArrayList(u8),
    indent_level: usize,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) XmlWriter {
        return .{
            .list = std.ArrayList(u8){},
            .indent_level = 0,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *XmlWriter) void {
        self.list.deinit(self.allocator);
    }

    pub fn startElement(self: *XmlWriter, name: []const u8) !void {
        try self.writeIndent();
        try self.list.appendSlice(self.allocator, "<");
        try self.list.appendSlice(self.allocator, name);
        try self.list.appendSlice(self.allocator, ">\n");
        self.indent_level += 1;
    }

    pub fn endElement(self: *XmlWriter, name: []const u8) !void {
        self.indent_level -= 1;
        try self.writeIndent();
        try self.list.appendSlice(self.allocator, "</");
        try self.list.appendSlice(self.allocator, name);
        try self.list.appendSlice(self.allocator, ">\n");
    }

    pub fn writeText(self: *XmlWriter, text: []const u8) !void {
        // Escape text to prevent XML injection
        const escaped_text = try escapeXml(self.allocator, text);
        defer self.allocator.free(escaped_text);
        try self.list.appendSlice(self.allocator, escaped_text);
    }

    pub fn toOwnedSlice(self: *XmlWriter) ![]u8 {
        return self.list.toOwnedSlice(self.allocator);
    }

    fn writeIndent(self: *XmlWriter) !void {
        var i: usize = 0;
        while (i < self.indent_level) : (i += 1) {
            try self.list.appendSlice(self.allocator, "  ");
        }
    }

    pub fn startElementWithAttrs(
        self: *XmlWriter,
        name: []const u8,
        attrs: std.StringHashMap([]const u8),
    ) !void {
        try self.writeIndent();
        try self.list.appendSlice(self.allocator, "<");
        try self.list.appendSlice(self.allocator, name);

        var iter = attrs.iterator();
        while (iter.next()) |attr| {
            try self.list.appendSlice(self.allocator, " ");
            try self.list.appendSlice(self.allocator, attr.key_ptr.*);
            try self.list.appendSlice(self.allocator, "=\"");

            // Escape attribute value to prevent XML injection
            const escaped_attr = try escapeXml(self.allocator, attr.value_ptr.*);
            defer self.allocator.free(escaped_attr);
            try self.list.appendSlice(self.allocator, escaped_attr);

            try self.list.appendSlice(self.allocator, "\"");
        }

        try self.list.appendSlice(self.allocator, ">\n");
        self.indent_level += 1;
    }

    pub fn writeElement(self: *XmlWriter, name: []const u8, text: []const u8) !void {
        try self.writeIndent();
        try self.list.appendSlice(self.allocator, "<");
        try self.list.appendSlice(self.allocator, name);
        try self.list.appendSlice(self.allocator, ">");

        // Escape text to prevent XML injection
        const escaped_text = try escapeXml(self.allocator, text);
        defer self.allocator.free(escaped_text);
        try self.list.appendSlice(self.allocator, escaped_text);

        try self.list.appendSlice(self.allocator, "</");
        try self.list.appendSlice(self.allocator, name);
        try self.list.appendSlice(self.allocator, ">\n");
    }
};
```
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<person>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<name>Alice</name>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "</person>") != null);
}
```

### Discussion

### Struct to XML

Convert structs to XML:

```zig
pub fn structToXml(
    allocator: std.mem.Allocator,
    comptime T: type,
    value: T,
    root_name: []const u8,
) ![]u8 {
    var xml = std.ArrayList(u8){};
    errdefer xml.deinit(allocator);

    try xml.appendSlice(allocator, "<");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    const info = @typeInfo(T);
    inline for (info.Struct.fields) |field| {
        try xml.appendSlice(allocator, "  <");
        try xml.appendSlice(allocator, field.name);
        try xml.appendSlice(allocator, ">");

        const field_value = @field(value, field.name);
        const field_str = try std.fmt.allocPrint(allocator, "{any}", .{field_value});
        defer allocator.free(field_str);
        try xml.appendSlice(allocator, field_str);

        try xml.appendSlice(allocator, "</");
        try xml.appendSlice(allocator, field.name);
        try xml.appendSlice(allocator, ">\n");
    }

    try xml.appendSlice(allocator, "</");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    return xml.toOwnedSlice(allocator);
}

test "struct to XML" {
    const allocator = std.testing.allocator;

    const Person = struct {
        name: []const u8,
        age: u32,
    };

    const person = Person{
        .name = "Bob",
        .age = 25,
    };

    const xml = try structToXml(allocator, Person, person, "person");
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<person>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<name>Bob</name>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<age>25</age>") != null);
}
```

### Array to XML

Convert arrays to XML:

```zig
pub fn arrayToXml(
    allocator: std.mem.Allocator,
    comptime T: type,
    items: []const T,
    root_name: []const u8,
    item_name: []const u8,
) ![]u8 {
    var xml = std.ArrayList(u8){};
    errdefer xml.deinit(allocator);

    try xml.appendSlice(allocator, "<");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    for (items) |item| {
        try xml.appendSlice(allocator, "  <");
        try xml.appendSlice(allocator, item_name);
        try xml.appendSlice(allocator, ">");

        const item_str = try std.fmt.allocPrint(allocator, "{any}", .{item});
        defer allocator.free(item_str);
        try xml.appendSlice(allocator, item_str);

        try xml.appendSlice(allocator, "</");
        try xml.appendSlice(allocator, item_name);
        try xml.appendSlice(allocator, ">\n");
    }

    try xml.appendSlice(allocator, "</");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    return xml.toOwnedSlice(allocator);
}

test "array to XML" {
    const allocator = std.testing.allocator;

    const numbers = [_]u32{ 1, 2, 3, 4, 5 };

    const xml = try arrayToXml(allocator, u32, &numbers, "numbers", "number");
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<numbers>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<number>1</number>") != null);
}
```

### XML with Attributes

Add attributes to elements:

```zig
pub fn dictToXmlWithAttrs(
    allocator: std.mem.Allocator,
    map: std.StringHashMap([]const u8),
    attrs: std.StringHashMap([]const u8),
    root_name: []const u8,
) ![]u8 {
    var xml = std.ArrayList(u8){};
    errdefer xml.deinit(allocator);

    // Opening tag with attributes
    try xml.appendSlice(allocator, "<");
    try xml.appendSlice(allocator, root_name);

    var attr_iter = attrs.iterator();
    while (attr_iter.next()) |attr| {
        try xml.appendSlice(allocator, " ");
        try xml.appendSlice(allocator, attr.key_ptr.*);
        try xml.appendSlice(allocator, "=\"");
        try xml.appendSlice(allocator, attr.value_ptr.*);
        try xml.appendSlice(allocator, "\"");
    }

    try xml.appendSlice(allocator, ">\n");

    // Elements
    var iter = map.iterator();
    while (iter.next()) |entry| {
        try xml.appendSlice(allocator, "  <");
        try xml.appendSlice(allocator, entry.key_ptr.*);
        try xml.appendSlice(allocator, ">");
        try xml.appendSlice(allocator, entry.value_ptr.*);
        try xml.appendSlice(allocator, "</");
        try xml.appendSlice(allocator, entry.key_ptr.*);
        try xml.appendSlice(allocator, ">\n");
    }

    try xml.appendSlice(allocator, "</");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    return xml.toOwnedSlice(allocator);
}

test "XML with attributes" {
    const allocator = std.testing.allocator;

    var map = std.StringHashMap([]const u8).init(allocator);
    defer map.deinit();
    try map.put("title", "Book");

    var attrs = std.StringHashMap([]const u8).init(allocator);
    defer attrs.deinit();
    try attrs.put("id", "123");
    try attrs.put("version", "1.0");

    const xml = try dictToXmlWithAttrs(allocator, map, attrs, "item");
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "id=\"123\"") != null);
}
```

### Escaping XML Special Characters

Handle special characters:

```zig
pub fn escapeXml(allocator: std.mem.Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        switch (char) {
            '<' => try result.appendSlice(allocator, "&lt;"),
            '>' => try result.appendSlice(allocator, "&gt;"),
            '&' => try result.appendSlice(allocator, "&amp;"),
            '"' => try result.appendSlice(allocator, "&quot;"),
            '\'' => try result.appendSlice(allocator, "&apos;"),
            else => try result.append(allocator, char),
        }
    }

    return result.toOwnedSlice(allocator);
}

test "escape XML" {
    const allocator = std.testing.allocator;

    const escaped = try escapeXml(allocator, "A < B & C > D");
    defer allocator.free(escaped);

    try std.testing.expectEqualStrings("A &lt; B &amp; C &gt; D", escaped);
}
```

### Nested Structures

Handle nested maps:

```zig
pub fn nestedDictToXml(
    allocator: std.mem.Allocator,
    map: std.StringHashMap(std.StringHashMap([]const u8)),
    root_name: []const u8,
) ![]u8 {
    var xml = std.ArrayList(u8){};
    errdefer xml.deinit(allocator);

    try xml.appendSlice(allocator, "<");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    var iter = map.iterator();
    while (iter.next()) |entry| {
        try xml.appendSlice(allocator, "  <");
        try xml.appendSlice(allocator, entry.key_ptr.*);
        try xml.appendSlice(allocator, ">\n");

        var inner_iter = entry.value_ptr.iterator();
        while (inner_iter.next()) |inner| {
            try xml.appendSlice(allocator, "    <");
            try xml.appendSlice(allocator, inner.key_ptr.*);
            try xml.appendSlice(allocator, ">");
            try xml.appendSlice(allocator, inner.value_ptr.*);
            try xml.appendSlice(allocator, "</");
            try xml.appendSlice(allocator, inner.key_ptr.*);
            try xml.appendSlice(allocator, ">\n");
        }

        try xml.appendSlice(allocator, "  </");
        try xml.appendSlice(allocator, entry.key_ptr.*);
        try xml.appendSlice(allocator, ">\n");
    }

    try xml.appendSlice(allocator, "</");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    return xml.toOwnedSlice(allocator);
}
```

### Pretty Printing

Format with indentation:

```zig
pub const XmlWriter = struct {
    list: std.ArrayList(u8),
    indent_level: usize,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) XmlWriter {
        return .{
            .list = std.ArrayList(u8){},
            .indent_level = 0,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *XmlWriter) void {
        self.list.deinit(self.allocator);
    }

    pub fn startElement(self: *XmlWriter, name: []const u8) !void {
        try self.writeIndent();
        try self.list.appendSlice(self.allocator, "<");
        try self.list.appendSlice(self.allocator, name);
        try self.list.appendSlice(self.allocator, ">\n");
        self.indent_level += 1;
    }

    pub fn endElement(self: *XmlWriter, name: []const u8) !void {
        self.indent_level -= 1;
        try self.writeIndent();
        try self.list.appendSlice(self.allocator, "</");
        try self.list.appendSlice(self.allocator, name);
        try self.list.appendSlice(self.allocator, ">\n");
    }

    pub fn writeText(self: *XmlWriter, text: []const u8) !void {
        try self.list.appendSlice(self.allocator, text);
    }

    pub fn toOwnedSlice(self: *XmlWriter) ![]u8 {
        return self.list.toOwnedSlice(self.allocator);
    }

    fn writeIndent(self: *XmlWriter) !void {
        var i: usize = 0;
        while (i < self.indent_level) : (i += 1) {
            try self.list.appendSlice(self.allocator, "  ");
        }
    }
};

test "XML writer" {
    const allocator = std.testing.allocator;

    var writer = XmlWriter.init(allocator);
    defer writer.deinit();

    try writer.startElement("root");
    try writer.startElement("item");
    try writer.writeText("value");
    try writer.endElement("item");
    try writer.endElement("root");

    const xml = try writer.toOwnedSlice();
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "  <item>") != null);
}
```

### Best Practices

**Escaping:**
- Always escape special characters: `<`, `>`, `&`, `"`, `'`
- Use escaping for both element content and attribute values
- Consider CDATA sections for large text blocks

**Structure:**
```zig
// Use consistent naming
const xml = try dictToXml(allocator, map, "root");

// Validate element names (no spaces, start with letter)
fn isValidElementName(name: []const u8) bool {
    if (name.len == 0) return false;
    if (!std.ascii.isAlphabetic(name[0])) return false;
    for (name) |c| {
        if (!std.ascii.isAlphanumeric(c) and c != '_' and c != '-') {
            return false;
        }
    }
    return true;
}
```

**Memory:**
- Use arena allocator for temporary XML generation
- Write directly to file for large documents
- Consider streaming for very large outputs

**Formatting:**
- Add XML declaration: `<?xml version="1.0" encoding="UTF-8"?>`
- Use consistent indentation
- Consider minified output for network transfer

### Related Functions

- `std.ArrayList()` - Dynamic string building
- `std.StringHashMap()` - Key-value storage
- `std.fmt.allocPrint()` - Format values
- `@typeInfo()` - Struct reflection
- `std.mem.indexOf()` - String search
- `std.ascii.isAlphanumeric()` - Character validation

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: dict_to_xml
/// Convert hash map to XML
pub fn dictToXml(
    allocator: std.mem.Allocator,
    map: std.StringHashMap([]const u8),
    root_name: []const u8,
) ![]u8 {
    var xml = std.ArrayList(u8){};
    errdefer xml.deinit(allocator);

    // Write opening tag
    try xml.appendSlice(allocator, "<");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    // Write entries
    var iter = map.iterator();
    while (iter.next()) |entry| {
        try xml.appendSlice(allocator, "  <");
        try xml.appendSlice(allocator, entry.key_ptr.*);
        try xml.appendSlice(allocator, ">");

        // Escape value to prevent XML injection
        const escaped_value = try escapeXml(allocator, entry.value_ptr.*);
        defer allocator.free(escaped_value);
        try xml.appendSlice(allocator, escaped_value);

        try xml.appendSlice(allocator, "</");
        try xml.appendSlice(allocator, entry.key_ptr.*);
        try xml.appendSlice(allocator, ">\n");
    }

    // Write closing tag
    try xml.appendSlice(allocator, "</");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    return xml.toOwnedSlice(allocator);
}
// ANCHOR_END: dict_to_xml

// ANCHOR: struct_to_xml
/// Convert struct to XML using reflection
pub fn structToXml(
    allocator: std.mem.Allocator,
    comptime T: type,
    value: T,
    root_name: []const u8,
) ![]u8 {
    var xml = std.ArrayList(u8){};
    errdefer xml.deinit(allocator);

    try xml.appendSlice(allocator, "<");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    const info = @typeInfo(T);
    switch (info) {
        .@"struct" => |struct_info| {
            inline for (struct_info.fields) |field| {
                try xml.appendSlice(allocator, "  <");
                try xml.appendSlice(allocator, field.name);
                try xml.appendSlice(allocator, ">");

                const field_value = @field(value, field.name);
                const FieldType = @TypeOf(field_value);
                const field_str = if (FieldType == []const u8 or FieldType == []u8)
                    try std.fmt.allocPrint(allocator, "{s}", .{field_value})
                else
                    try std.fmt.allocPrint(allocator, "{any}", .{field_value});
                defer allocator.free(field_str);

                // Escape field value to prevent XML injection
                const escaped_field = try escapeXml(allocator, field_str);
                defer allocator.free(escaped_field);
                try xml.appendSlice(allocator, escaped_field);

                try xml.appendSlice(allocator, "</");
                try xml.appendSlice(allocator, field.name);
                try xml.appendSlice(allocator, ">\n");
            }
        },
        else => return error.UnsupportedType,
    }

    try xml.appendSlice(allocator, "</");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    return xml.toOwnedSlice(allocator);
}
// ANCHOR_END: struct_to_xml

/// Convert array to XML
pub fn arrayToXml(
    allocator: std.mem.Allocator,
    comptime T: type,
    items: []const T,
    root_name: []const u8,
    item_name: []const u8,
) ![]u8 {
    var xml = std.ArrayList(u8){};
    errdefer xml.deinit(allocator);

    try xml.appendSlice(allocator, "<");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    for (items) |item| {
        try xml.appendSlice(allocator, "  <");
        try xml.appendSlice(allocator, item_name);
        try xml.appendSlice(allocator, ">");

        const item_str = try std.fmt.allocPrint(allocator, "{any}", .{item});
        defer allocator.free(item_str);

        // Escape item value to prevent XML injection
        const escaped_item = try escapeXml(allocator, item_str);
        defer allocator.free(escaped_item);
        try xml.appendSlice(allocator, escaped_item);

        try xml.appendSlice(allocator, "</");
        try xml.appendSlice(allocator, item_name);
        try xml.appendSlice(allocator, ">\n");
    }

    try xml.appendSlice(allocator, "</");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    return xml.toOwnedSlice(allocator);
}

/// Convert hash map to XML with attributes
pub fn dictToXmlWithAttrs(
    allocator: std.mem.Allocator,
    map: std.StringHashMap([]const u8),
    attrs: std.StringHashMap([]const u8),
    root_name: []const u8,
) ![]u8 {
    var xml = std.ArrayList(u8){};
    errdefer xml.deinit(allocator);

    // Opening tag with attributes
    try xml.appendSlice(allocator, "<");
    try xml.appendSlice(allocator, root_name);

    var attr_iter = attrs.iterator();
    while (attr_iter.next()) |attr| {
        try xml.appendSlice(allocator, " ");
        try xml.appendSlice(allocator, attr.key_ptr.*);
        try xml.appendSlice(allocator, "=\"");

        // Escape attribute value to prevent XML injection
        const escaped_attr = try escapeXml(allocator, attr.value_ptr.*);
        defer allocator.free(escaped_attr);
        try xml.appendSlice(allocator, escaped_attr);

        try xml.appendSlice(allocator, "\"");
    }

    try xml.appendSlice(allocator, ">\n");

    // Elements
    var iter = map.iterator();
    while (iter.next()) |entry| {
        try xml.appendSlice(allocator, "  <");
        try xml.appendSlice(allocator, entry.key_ptr.*);
        try xml.appendSlice(allocator, ">");

        // Escape element value to prevent XML injection
        const escaped_value = try escapeXml(allocator, entry.value_ptr.*);
        defer allocator.free(escaped_value);
        try xml.appendSlice(allocator, escaped_value);

        try xml.appendSlice(allocator, "</");
        try xml.appendSlice(allocator, entry.key_ptr.*);
        try xml.appendSlice(allocator, ">\n");
    }

    try xml.appendSlice(allocator, "</");
    try xml.appendSlice(allocator, root_name);
    try xml.appendSlice(allocator, ">\n");

    return xml.toOwnedSlice(allocator);
}

/// Escape XML special characters
pub fn escapeXml(allocator: std.mem.Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        switch (char) {
            '<' => try result.appendSlice(allocator, "&lt;"),
            '>' => try result.appendSlice(allocator, "&gt;"),
            '&' => try result.appendSlice(allocator, "&amp;"),
            '"' => try result.appendSlice(allocator, "&quot;"),
            '\'' => try result.appendSlice(allocator, "&apos;"),
            else => try result.append(allocator, char),
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Validate XML element name
pub fn isValidElementName(name: []const u8) bool {
    if (name.len == 0) return false;
    if (!std.ascii.isAlphabetic(name[0]) and name[0] != '_') return false;
    for (name) |c| {
        if (!std.ascii.isAlphanumeric(c) and c != '_' and c != '-' and c != '.') {
            return false;
        }
    }
    return true;
}

// ANCHOR: xml_writer
/// XML writer with pretty printing
pub const XmlWriter = struct {
    list: std.ArrayList(u8),
    indent_level: usize,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) XmlWriter {
        return .{
            .list = std.ArrayList(u8){},
            .indent_level = 0,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *XmlWriter) void {
        self.list.deinit(self.allocator);
    }

    pub fn startElement(self: *XmlWriter, name: []const u8) !void {
        try self.writeIndent();
        try self.list.appendSlice(self.allocator, "<");
        try self.list.appendSlice(self.allocator, name);
        try self.list.appendSlice(self.allocator, ">\n");
        self.indent_level += 1;
    }

    pub fn endElement(self: *XmlWriter, name: []const u8) !void {
        self.indent_level -= 1;
        try self.writeIndent();
        try self.list.appendSlice(self.allocator, "</");
        try self.list.appendSlice(self.allocator, name);
        try self.list.appendSlice(self.allocator, ">\n");
    }

    pub fn writeText(self: *XmlWriter, text: []const u8) !void {
        // Escape text to prevent XML injection
        const escaped_text = try escapeXml(self.allocator, text);
        defer self.allocator.free(escaped_text);
        try self.list.appendSlice(self.allocator, escaped_text);
    }

    pub fn toOwnedSlice(self: *XmlWriter) ![]u8 {
        return self.list.toOwnedSlice(self.allocator);
    }

    fn writeIndent(self: *XmlWriter) !void {
        var i: usize = 0;
        while (i < self.indent_level) : (i += 1) {
            try self.list.appendSlice(self.allocator, "  ");
        }
    }

    pub fn startElementWithAttrs(
        self: *XmlWriter,
        name: []const u8,
        attrs: std.StringHashMap([]const u8),
    ) !void {
        try self.writeIndent();
        try self.list.appendSlice(self.allocator, "<");
        try self.list.appendSlice(self.allocator, name);

        var iter = attrs.iterator();
        while (iter.next()) |attr| {
            try self.list.appendSlice(self.allocator, " ");
            try self.list.appendSlice(self.allocator, attr.key_ptr.*);
            try self.list.appendSlice(self.allocator, "=\"");

            // Escape attribute value to prevent XML injection
            const escaped_attr = try escapeXml(self.allocator, attr.value_ptr.*);
            defer self.allocator.free(escaped_attr);
            try self.list.appendSlice(self.allocator, escaped_attr);

            try self.list.appendSlice(self.allocator, "\"");
        }

        try self.list.appendSlice(self.allocator, ">\n");
        self.indent_level += 1;
    }

    pub fn writeElement(self: *XmlWriter, name: []const u8, text: []const u8) !void {
        try self.writeIndent();
        try self.list.appendSlice(self.allocator, "<");
        try self.list.appendSlice(self.allocator, name);
        try self.list.appendSlice(self.allocator, ">");

        // Escape text to prevent XML injection
        const escaped_text = try escapeXml(self.allocator, text);
        defer self.allocator.free(escaped_text);
        try self.list.appendSlice(self.allocator, escaped_text);

        try self.list.appendSlice(self.allocator, "</");
        try self.list.appendSlice(self.allocator, name);
        try self.list.appendSlice(self.allocator, ">\n");
    }
};
// ANCHOR_END: xml_writer

/// Add XML declaration
pub fn addXmlDeclaration(allocator: std.mem.Allocator, xml: []const u8) ![]u8 {
    const declaration = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
    return std.fmt.allocPrint(allocator, "{s}{s}", .{ declaration, xml });
}

// Tests

test "dict to XML" {
    const allocator = std.testing.allocator;

    var map = std.StringHashMap([]const u8).init(allocator);
    defer map.deinit();

    try map.put("name", "Alice");
    try map.put("age", "30");

    const xml = try dictToXml(allocator, map, "person");
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<person>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<name>Alice</name>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<age>30</age>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "</person>") != null);
}

test "struct to XML" {
    const allocator = std.testing.allocator;

    const Person = struct {
        name: []const u8,
        age: u32,
    };

    const person = Person{
        .name = "Bob",
        .age = 25,
    };

    const xml = try structToXml(allocator, Person, person, "person");
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<person>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<name>Bob</name>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<age>25</age>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "</person>") != null);
}

test "array to XML" {
    const allocator = std.testing.allocator;

    const numbers = [_]u32{ 1, 2, 3, 4, 5 };

    const xml = try arrayToXml(allocator, u32, &numbers, "numbers", "number");
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<numbers>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<number>1</number>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<number>5</number>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "</numbers>") != null);
}

test "XML with attributes" {
    const allocator = std.testing.allocator;

    var map = std.StringHashMap([]const u8).init(allocator);
    defer map.deinit();
    try map.put("title", "Book");

    var attrs = std.StringHashMap([]const u8).init(allocator);
    defer attrs.deinit();
    try attrs.put("id", "123");
    try attrs.put("version", "1.0");

    const xml = try dictToXmlWithAttrs(allocator, map, attrs, "item");
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "id=\"123\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "version=\"1.0\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<title>Book</title>") != null);
}

test "escape XML" {
    const allocator = std.testing.allocator;

    const escaped = try escapeXml(allocator, "A < B & C > D");
    defer allocator.free(escaped);

    try std.testing.expectEqualStrings("A &lt; B &amp; C &gt; D", escaped);
}

test "escape XML quotes" {
    const allocator = std.testing.allocator;

    const escaped = try escapeXml(allocator, "Say \"Hello\" & 'World'");
    defer allocator.free(escaped);

    try std.testing.expect(std.mem.indexOf(u8, escaped, "&quot;") != null);
    try std.testing.expect(std.mem.indexOf(u8, escaped, "&apos;") != null);
    try std.testing.expect(std.mem.indexOf(u8, escaped, "&amp;") != null);
}

test "valid element names" {
    try std.testing.expect(isValidElementName("root"));
    try std.testing.expect(isValidElementName("my_element"));
    try std.testing.expect(isValidElementName("element-123"));
    try std.testing.expect(isValidElementName("_private"));

    try std.testing.expect(!isValidElementName(""));
    try std.testing.expect(!isValidElementName("123start"));
    try std.testing.expect(!isValidElementName("has space"));
    try std.testing.expect(!isValidElementName("has@symbol"));
}

test "XML writer" {
    const allocator = std.testing.allocator;

    var writer = XmlWriter.init(allocator);
    defer writer.deinit();

    try writer.startElement("root");
    try writer.startElement("item");
    try writer.writeText("value");
    try writer.endElement("item");
    try writer.endElement("root");

    const xml = try writer.toOwnedSlice();
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<root>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "  <item>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "</root>") != null);
}

test "XML writer with attributes" {
    const allocator = std.testing.allocator;

    var writer = XmlWriter.init(allocator);
    defer writer.deinit();

    var attrs = std.StringHashMap([]const u8).init(allocator);
    defer attrs.deinit();
    try attrs.put("id", "42");

    try writer.startElementWithAttrs("item", attrs);
    try writer.writeText("content");
    try writer.endElement("item");

    const xml = try writer.toOwnedSlice();
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "id=\"42\"") != null);
}

test "XML writer write element" {
    const allocator = std.testing.allocator;

    var writer = XmlWriter.init(allocator);
    defer writer.deinit();

    try writer.startElement("root");
    try writer.writeElement("name", "Alice");
    try writer.writeElement("age", "30");
    try writer.endElement("root");

    const xml = try writer.toOwnedSlice();
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<name>Alice</name>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<age>30</age>") != null);
}

test "empty dict to XML" {
    const allocator = std.testing.allocator;

    var map = std.StringHashMap([]const u8).init(allocator);
    defer map.deinit();

    const xml = try dictToXml(allocator, map, "empty");
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<empty>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "</empty>") != null);
}

test "empty array to XML" {
    const allocator = std.testing.allocator;

    const numbers: []const u32 = &.{};

    const xml = try arrayToXml(allocator, u32, numbers, "numbers", "number");
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<numbers>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "</numbers>") != null);
}

test "struct with bool to XML" {
    const allocator = std.testing.allocator;

    const Config = struct {
        enabled: bool,
        count: i32,
    };

    const config = Config{
        .enabled = true,
        .count = -5,
    };

    const xml = try structToXml(allocator, Config, config, "config");
    defer allocator.free(xml);

    try std.testing.expect(std.mem.indexOf(u8, xml, "<enabled>true</enabled>") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "<count>-5</count>") != null);
}

test "add XML declaration" {
    const allocator = std.testing.allocator;

    const simple_xml = "<root/>";
    const with_declaration = try addXmlDeclaration(allocator, simple_xml);
    defer allocator.free(with_declaration);

    try std.testing.expect(std.mem.startsWith(u8, with_declaration, "<?xml version=\"1.0\""));
    try std.testing.expect(std.mem.indexOf(u8, with_declaration, "<root/>") != null);
}

test "escape empty string" {
    const allocator = std.testing.allocator;

    const escaped = try escapeXml(allocator, "");
    defer allocator.free(escaped);

    try std.testing.expectEqualStrings("", escaped);
}

test "escape no special chars" {
    const allocator = std.testing.allocator;

    const escaped = try escapeXml(allocator, "Normal text 123");
    defer allocator.free(escaped);

    try std.testing.expectEqualStrings("Normal text 123", escaped);
}

test "prevent XML injection in dict" {
    const allocator = std.testing.allocator;

    var map = std.StringHashMap([]const u8).init(allocator);
    defer map.deinit();

    // Attempt XML injection via malicious value
    try map.put("name", "</name><admin>true</admin><name>");

    const xml = try dictToXml(allocator, map, "user");
    defer allocator.free(xml);

    // Verify malicious tags are escaped and not executable
    try std.testing.expect(std.mem.indexOf(u8, xml, "&lt;/name&gt;") != null);
    try std.testing.expect(std.mem.indexOf(u8, xml, "&lt;admin&gt;") != null);
    // Ensure raw tags are NOT present
    try std.testing.expect(std.mem.indexOf(u8, xml, "<admin>") == null);
}

test "prevent XML injection in attributes" {
    const allocator = std.testing.allocator;

    var map = std.StringHashMap([]const u8).init(allocator);
    defer map.deinit();
    try map.put("title", "Book");

    var attrs = std.StringHashMap([]const u8).init(allocator);
    defer attrs.deinit();
    // Attempt injection via attribute value
    try attrs.put("id", "\"><script>alert('xss')</script><x y=\"");

    const xml = try dictToXmlWithAttrs(allocator, map, attrs, "item");
    defer allocator.free(xml);

    // Verify malicious content is escaped
    try std.testing.expect(std.mem.indexOf(u8, xml, "&quot;&gt;&lt;script&gt;") != null);
    // Ensure raw script tag is NOT present
    try std.testing.expect(std.mem.indexOf(u8, xml, "<script>") == null);
}
```

---

## Recipe 6.6: Interacting with a Relational Database {#recipe-6-6}

**Tags:** allocators, c-interop, data-encoding, error-handling, http, json, memory, networking, parsing, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/06-data-encoding/recipe_6_6.zig`

### Problem

You need to store and query structured data using a relational database, specifically SQLite. You want to know the best way to integrate SQLite into your Zig application, whether using a wrapper library for convenience or raw C bindings for maximum control.

### Solution

Zig offers two main approaches to working with SQLite databases:

### Beginner Approach: Using a Wrapper Library

For most applications, using a thin wrapper like `zqlite.zig` provides a clean, easy-to-use API while still staying close to SQLite's behavior.

#### Setup Beginner

```zig
// Beginner setup requires zqlite dependency
// This shows the import and basic types you would use
//
// const zqlite = @import("zqlite");
// const OpenFlags = zqlite.OpenFlags;
//
// Common flags:
// - OpenFlags.Create: Create database if it doesn't exist
// - OpenFlags.ReadWrite: Open for reading and writing
// - OpenFlags.EXResCode: Return extended error codes
```

#### Basic CRUD Beginner

```zig
// Basic CRUD operations with zqlite wrapper
//
// This demonstrates the simple, beginner-friendly API:
//
// test "basic database operations with zqlite" {
//     const allocator = testing.allocator;
//
//     // Open in-memory database for testing
//     const flags = zqlite.OpenFlags.Create | zqlite.OpenFlags.EXResCode;
//     var conn = try zqlite.open(":memory:", flags);
//     defer conn.close(); // Always clean up resources
//
//     // CREATE TABLE
//     try conn.exec(
//         \\CREATE TABLE users (
//         \\    id INTEGER PRIMARY KEY,
//         \\    name TEXT NOT NULL,
//         \\    age INTEGER
//         \\)
//     , .{});
//
//     // INSERT data with parameters (prevents SQL injection)
//     try conn.exec(
//         "INSERT INTO users (name, age) VALUES (?1, ?2), (?3, ?4)",
//         .{ "Alice", 30, "Bob", 25 }
//     );
//
//     // SELECT single row
//     if (try conn.row("SELECT name, age FROM users WHERE name = ?1", .{"Alice"})) |row| {
//         defer row.deinit(); // Clean up row resources
//
//         const name = row.text(0);  // Get column 0 as text
//         const age = row.int(1);    // Get column 1 as integer
//
//         try testing.expectEqualStrings("Alice", name);
//         try testing.expectEqual(30, age);
//     }
//
//     // UPDATE
//     try conn.exec("UPDATE users SET age = ?1 WHERE name = ?2", .{ 31, "Alice" });
//
//     // DELETE
//     try conn.exec("DELETE FROM users WHERE name = ?1", .{"Bob"});
// }
```

#### Query Multiple Beginner

```zig
// Querying multiple rows with iteration
//
// test "query multiple rows with zqlite" {
//     const allocator = testing.allocator;
//
//     const flags = zqlite.OpenFlags.Create;
//     var conn = try zqlite.open(":memory:", flags);
//     defer conn.close();
//
//     try conn.exec(
//         "CREATE TABLE products (id INTEGER, name TEXT, price REAL)",
//         .{}
//     );
//
//     try conn.exec(
//         "INSERT INTO products VALUES (1, 'Widget', 9.99), (2, 'Gadget', 19.99), (3, 'Doohickey', 4.99)",
//         .{}
//     );
//
//     // Query multiple rows
//     var rows = try conn.rows("SELECT name, price FROM products WHERE price < ?1 ORDER BY price", .{15.0});
//     defer rows.deinit();
//
//     var count: usize = 0;
//     while (rows.next()) |row| {
//         count += 1;
//         const name = row.text(0);
//         const price = row.float(1);
//         std.debug.print("{s}: ${d:.2}\n", .{ name, price });
//     }
//
//     try testing.expectEqual(2, count); // Widget and Doohickey
//
//     // Always check for iteration errors
//     if (rows.err) |err| return err;
// }
```

**Querying multiple rows:**

```zig
var rows = try conn.rows(
    "SELECT name, age FROM users WHERE age > ?1 ORDER BY name",
    .{20}
);
defer rows.deinit();

while (rows.next()) |row| {
    const name = row.text(0);
    const age = row.int(1);
    std.debug.print("{s}: {d}\n", .{ name, age });
}

// Always check for iteration errors
if (rows.err) |err| return err;
```

### Expert Approach: Raw C Bindings

For maximum control, educational purposes, or when you need direct access to all SQLite features, you can use `@cImport` to work with the C API directly.

**Setup** (in `build.zig`):

```zig
exe.linkSystemLibrary("sqlite3");
exe.linkLibC();
```

**Import SQLite C API:**

```zig
const c = @cImport({
    @cInclude("sqlite3.h");
});

const SQLITE_OK = 0;
const SQLITE_ROW = 100;
const SQLITE_DONE = 101;

const SqliteError = error{
    OpenFailed,
    PrepareFailed,
    ExecFailed,
    BindFailed,
    StepFailed,
};

fn checkSqlite(result: c_int) SqliteError!void {
    if (result != SQLITE_OK) {
        return SqliteError.ExecFailed;
    }
}
```

**Basic CRUD operations with raw C API:**

```zig
pub fn main() !void {
    var db: ?*c.sqlite3 = null;

    // Open database
    var result = c.sqlite3_open("myapp.db", &db);
    if (result != SQLITE_OK) return SqliteError.OpenFailed;
    defer _ = c.sqlite3_close(db);

    // CREATE TABLE
    const create_sql = "CREATE TABLE IF NOT EXISTS users (id INTEGER PRIMARY KEY, name TEXT, age INTEGER)";
    result = c.sqlite3_exec(db, create_sql, null, null, null);
    try checkSqlite(result);

    // INSERT using prepared statement
    const insert_sql = "INSERT INTO users (name, age) VALUES (?1, ?2)";
    var stmt: ?*c.sqlite3_stmt = null;

    result = c.sqlite3_prepare_v2(db, insert_sql, -1, &stmt, null);
    if (result != SQLITE_OK) return SqliteError.PrepareFailed;
    defer _ = c.sqlite3_finalize(stmt);

    // Bind parameters (indices start at 1)
    result = c.sqlite3_bind_text(stmt, 1, "Alice", -1, null);
    try checkSqlite(result);
    result = c.sqlite3_bind_int(stmt, 2, 30);
    try checkSqlite(result);

    // Execute
    result = c.sqlite3_step(stmt);
    if (result != SQLITE_DONE) return SqliteError.StepFailed;

    // Reset and reuse for another insert
    _ = c.sqlite3_reset(stmt);
    result = c.sqlite3_bind_text(stmt, 1, "Bob", -1, null);
    try checkSqlite(result);
    result = c.sqlite3_bind_int(stmt, 2, 25);
    try checkSqlite(result);
    result = c.sqlite3_step(stmt);
    if (result != SQLITE_DONE) return SqliteError.StepFailed;
}
```

**Querying data:**

```zig
const select_sql = "SELECT name, age FROM users WHERE age > ?1";
var select_stmt: ?*c.sqlite3_stmt = null;

result = c.sqlite3_prepare_v2(db, select_sql, -1, &select_stmt, null);
if (result != SQLITE_OK) return SqliteError.PrepareFailed;
defer _ = c.sqlite3_finalize(select_stmt);

result = c.sqlite3_bind_int(select_stmt, 1, 20);
try checkSqlite(result);

// Iterate through results
while (c.sqlite3_step(select_stmt) == SQLITE_ROW) {
    // Get column values (indices start at 0)
    const name_ptr = c.sqlite3_column_text(select_stmt, 0);
    const age = c.sqlite3_column_int(select_stmt, 1);

    // Convert C string to Zig slice
    const name = std.mem.span(@as([*:0]const u8, @ptrCast(name_ptr)));

    std.debug.print("{s}: {d}\n", .{ name, age });
}
```

**Transactions with proper error handling:**

```zig
// Begin transaction
result = c.sqlite3_exec(db, "BEGIN TRANSACTION", null, null, null);
try checkSqlite(result);

// Use errdefer to rollback on error
errdefer _ = c.sqlite3_exec(db, "ROLLBACK", null, null, null);

// Multiple operations...
try c.sqlite3_exec(db, "INSERT INTO logs (message) VALUES ('Started')", null, null, null);
try c.sqlite3_exec(db, "INSERT INTO logs (message) VALUES ('Processing')", null, null, null);
try c.sqlite3_exec(db, "INSERT INTO logs (message) VALUES ('Completed')", null, null, null);

// Commit if all succeeded
result = c.sqlite3_exec(db, "COMMIT", null, null, null);
try checkSqlite(result);
```

### Discussion

### When to Use Each Approach

**Use a wrapper library (like zqlite.zig) when:**
- You want cleaner, more idiomatic Zig code
- You're building a typical CRUD application
- You prefer type-safe row access with `.text()`, `.int()`, `.float()` methods
- You want less boilerplate and easier error handling
- You're new to Zig or SQLite

**Use raw C bindings when:**
- You need access to advanced SQLite features not exposed by wrappers
- You're learning C interoperability in Zig
- You want zero abstraction overhead
- You're integrating with existing C code
- You need precise control over memory and resource management

### Resource Management Patterns

Both approaches require careful resource management. Zig's `defer` and `errdefer` make this straightforward:

**Key patterns:**
1. Always pair resource acquisition with `defer` cleanup
2. Use `errdefer` for error-path cleanup (especially for transactions)
3. Check all return codes - SQLite uses integer codes, not Zig errors
4. Prepare statements once, reuse multiple times for efficiency
5. Use `:memory:` databases for tests to avoid filesystem dependencies

```zig
var db: ?*c.sqlite3 = null;
if (c.sqlite3_open(path, &db) != SQLITE_OK) return error.OpenFailed;
defer _ = c.sqlite3_close(db);  // Cleanup happens automatically

var stmt: ?*c.sqlite3_stmt = null;
if (c.sqlite3_prepare_v2(db, sql, -1, &stmt, null) != SQLITE_OK)
    return error.PrepareFailed;
defer _ = c.sqlite3_finalize(stmt);  // Statement cleanup
```

### Type Mapping

SQLite has dynamic typing, but you typically access values with specific types:

| SQLite Type | Zig Type | Wrapper Method | C API Function |
|-------------|----------|----------------|----------------|
| INTEGER | `i32`, `i64` | `row.int(i)` | `sqlite3_column_int()` |
| REAL | `f64` | `row.float(i)` | `sqlite3_column_double()` |
| TEXT | `[]const u8` | `row.text(i)` | `sqlite3_column_text()` |
| BLOB | `[]const u8` | `row.blob(i)` | `sqlite3_column_blob()` |
| NULL | `?T` | Check separately | `sqlite3_column_type()` |

### Comparison to Python's sqlite3

If you're coming from Python, here are the key differences:

**Python:**
```python
import sqlite3

conn = sqlite3.connect('myapp.db')
cursor = conn.cursor()
cursor.execute("INSERT INTO users VALUES (?, ?)", ("Alice", 30))
rows = cursor.execute("SELECT * FROM users").fetchall()
conn.commit()
conn.close()
```

**Zig (with wrapper):**
```zig
var conn = try zqlite.open("myapp.db", .{});
defer conn.close();
try conn.exec("INSERT INTO users VALUES (?1, ?2)", .{"Alice", 30});
var rows = try conn.rows("SELECT * FROM users", .{});
defer rows.deinit();
while (rows.next()) |row| { /* process */ }
```

**Key differences:**
- Zig requires explicit error handling with `try`
- Resources must be explicitly freed with `defer`
- Allocators must be passed explicitly when needed
- No automatic transactions - you control when to commit
- Type conversions are explicit
- No context managers - use `defer` instead

### Security: SQL Injection Prevention

Always use parameterized queries, never string concatenation:

**WRONG - Vulnerable to SQL injection:**
```zig
const name = getUserInput();
const sql = try std.fmt.allocPrint(allocator, "SELECT * FROM users WHERE name = '{s}'", .{name});
// DON'T DO THIS!
```

**RIGHT - Safe with parameters:**
```zig
const name = getUserInput();
try conn.exec("SELECT * FROM users WHERE name = ?1", .{name});
// SQLite handles escaping properly
```

### Testing Strategy

Use in-memory databases for unit tests to avoid filesystem dependencies:

```zig
test "database operations" {
    var conn = try zqlite.open(":memory:", .{});
    defer conn.close();

    // Your tests here - database is destroyed when conn.close() runs
}
```

### Full Tested Code

```zig
// Recipe 6.6: Interacting with a Relational Database (SQLite)
// Target Zig Version: 0.15.2
//
// This recipe demonstrates two approaches to SQLite database interaction:
// 1. Beginner: Using a simple wrapper library (zqlite.zig)
// 2. Expert: Using raw C bindings via @cImport
//
// NOTE: To run these examples, you need:
// - SQLite3 development library installed on your system
// - For beginner approach: zqlite dependency added to build.zig.zon
// - build.zig configured to link sqlite3 and libc

const std = @import("std");
const testing = std.testing;

// ============================================================================
// BEGINNER APPROACH: Using zqlite.zig wrapper
// ============================================================================
//
// To use this approach, add to build.zig.zon:
//   zig fetch --save git+https://github.com/karlseguin/zqlite.zig#master
//
// And in build.zig:
//   exe.linkSystemLibrary("sqlite3");
//   exe.linkLibC();
//   const zqlite = b.dependency("zqlite", .{
//       .target = target,
//       .optimize = optimize,
//   });
//   exe.root_module.addImport("zqlite", zqlite.module("zqlite"));

// Uncomment to use with actual zqlite dependency:
// const zqlite = @import("zqlite");

// ANCHOR: setup_beginner
// Beginner setup requires zqlite dependency
// This shows the import and basic types you would use
//
// const zqlite = @import("zqlite");
// const OpenFlags = zqlite.OpenFlags;
//
// Common flags:
// - OpenFlags.Create: Create database if it doesn't exist
// - OpenFlags.ReadWrite: Open for reading and writing
// - OpenFlags.EXResCode: Return extended error codes
// ANCHOR_END: setup_beginner

// ANCHOR: basic_crud_beginner
// Basic CRUD operations with zqlite wrapper
//
// This demonstrates the simple, beginner-friendly API:
//
// test "basic database operations with zqlite" {
//     const allocator = testing.allocator;
//
//     // Open in-memory database for testing
//     const flags = zqlite.OpenFlags.Create | zqlite.OpenFlags.EXResCode;
//     var conn = try zqlite.open(":memory:", flags);
//     defer conn.close(); // Always clean up resources
//
//     // CREATE TABLE
//     try conn.exec(
//         \\CREATE TABLE users (
//         \\    id INTEGER PRIMARY KEY,
//         \\    name TEXT NOT NULL,
//         \\    age INTEGER
//         \\)
//     , .{});
//
//     // INSERT data with parameters (prevents SQL injection)
//     try conn.exec(
//         "INSERT INTO users (name, age) VALUES (?1, ?2), (?3, ?4)",
//         .{ "Alice", 30, "Bob", 25 }
//     );
//
//     // SELECT single row
//     if (try conn.row("SELECT name, age FROM users WHERE name = ?1", .{"Alice"})) |row| {
//         defer row.deinit(); // Clean up row resources
//
//         const name = row.text(0);  // Get column 0 as text
//         const age = row.int(1);    // Get column 1 as integer
//
//         try testing.expectEqualStrings("Alice", name);
//         try testing.expectEqual(30, age);
//     }
//
//     // UPDATE
//     try conn.exec("UPDATE users SET age = ?1 WHERE name = ?2", .{ 31, "Alice" });
//
//     // DELETE
//     try conn.exec("DELETE FROM users WHERE name = ?1", .{"Bob"});
// }
// ANCHOR_END: basic_crud_beginner

// ANCHOR: query_multiple_beginner
// Querying multiple rows with iteration
//
// test "query multiple rows with zqlite" {
//     const allocator = testing.allocator;
//
//     const flags = zqlite.OpenFlags.Create;
//     var conn = try zqlite.open(":memory:", flags);
//     defer conn.close();
//
//     try conn.exec(
//         "CREATE TABLE products (id INTEGER, name TEXT, price REAL)",
//         .{}
//     );
//
//     try conn.exec(
//         "INSERT INTO products VALUES (1, 'Widget', 9.99), (2, 'Gadget', 19.99), (3, 'Doohickey', 4.99)",
//         .{}
//     );
//
//     // Query multiple rows
//     var rows = try conn.rows("SELECT name, price FROM products WHERE price < ?1 ORDER BY price", .{15.0});
//     defer rows.deinit();
//
//     var count: usize = 0;
//     while (rows.next()) |row| {
//         count += 1;
//         const name = row.text(0);
//         const price = row.float(1);
//         std.debug.print("{s}: ${d:.2}\n", .{ name, price });
//     }
//
//     try testing.expectEqual(2, count); // Widget and Doohickey
//
//     // Always check for iteration errors
//     if (rows.err) |err| return err;
// }
// ANCHOR_END: query_multiple_beginner

// ============================================================================
// EXPERT APPROACH: Raw C bindings with @cImport
// ============================================================================

// ANCHOR: setup_expert
// Expert setup using raw C bindings
// Requires sqlite3 development libraries installed
//
// In build.zig:
//   exe.linkSystemLibrary("sqlite3");
//   exe.linkLibC();

const c = @cImport({
    @cInclude("sqlite3.h");
});

// SQLite error codes we'll check
const SQLITE_OK = 0;
const SQLITE_ROW = 100;
const SQLITE_DONE = 101;
// ANCHOR_END: setup_expert

// ANCHOR: error_handling_expert
// Custom error handling for SQLite C API
const SqliteError = error{
    OpenFailed,
    PrepareFailed,
    ExecFailed,
    BindFailed,
    StepFailed,
    FinalizeFailed,
};

// Helper to check SQLite result codes
fn checkSqlite(result: c_int) SqliteError!void {
    if (result != SQLITE_OK) {
        return SqliteError.ExecFailed;
    }
}
// ANCHOR_END: error_handling_expert

// ANCHOR: basic_crud_expert
// Basic CRUD operations using raw C API
test "basic database operations with raw C API" {
    var db: ?*c.sqlite3 = null;

    // Open database - returns error code
    var result = c.sqlite3_open(":memory:", &db);
    if (result != SQLITE_OK) {
        std.debug.print("Failed to open database: {d}\n", .{result});
        return SqliteError.OpenFailed;
    }
    // Must close database when done
    defer _ = c.sqlite3_close(db);

    // CREATE TABLE
    const create_sql = "CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT, age INTEGER)";
    result = c.sqlite3_exec(db, create_sql, null, null, null);
    try checkSqlite(result);

    // INSERT using prepared statement
    const insert_sql = "INSERT INTO users (name, age) VALUES (?1, ?2)";
    var insert_stmt: ?*c.sqlite3_stmt = null;

    result = c.sqlite3_prepare_v2(db, insert_sql, -1, &insert_stmt, null);
    if (result != SQLITE_OK) return SqliteError.PrepareFailed;
    defer _ = c.sqlite3_finalize(insert_stmt);

    // Bind parameters (indices start at 1)
    result = c.sqlite3_bind_text(insert_stmt, 1, "Alice", -1, null);
    try checkSqlite(result);
    result = c.sqlite3_bind_int(insert_stmt, 2, 30);
    try checkSqlite(result);

    // Execute
    result = c.sqlite3_step(insert_stmt);
    if (result != SQLITE_DONE) return SqliteError.StepFailed;

    // Reset and insert another row
    _ = c.sqlite3_reset(insert_stmt);
    result = c.sqlite3_bind_text(insert_stmt, 1, "Bob", -1, null);
    try checkSqlite(result);
    result = c.sqlite3_bind_int(insert_stmt, 2, 25);
    try checkSqlite(result);
    result = c.sqlite3_step(insert_stmt);
    if (result != SQLITE_DONE) return SqliteError.StepFailed;

    // SELECT query
    const select_sql = "SELECT name, age FROM users WHERE age > ?1";
    var select_stmt: ?*c.sqlite3_stmt = null;

    result = c.sqlite3_prepare_v2(db, select_sql, -1, &select_stmt, null);
    if (result != SQLITE_OK) return SqliteError.PrepareFailed;
    defer _ = c.sqlite3_finalize(select_stmt);

    result = c.sqlite3_bind_int(select_stmt, 1, 26);
    try checkSqlite(result);

    // Fetch results
    var found_alice = false;
    while (c.sqlite3_step(select_stmt) == SQLITE_ROW) {
        // Get column values (indices start at 0)
        const name_ptr = c.sqlite3_column_text(select_stmt, 0);
        const age = c.sqlite3_column_int(select_stmt, 1);

        // Convert C string to Zig slice
        const name = std.mem.span(@as([*:0]const u8, @ptrCast(name_ptr)));

        if (std.mem.eql(u8, name, "Alice")) {
            found_alice = true;
            try testing.expectEqual(30, age);
        }
    }

    try testing.expect(found_alice);
}
// ANCHOR_END: basic_crud_expert

// ANCHOR: transactions_expert
// Transaction handling with errdefer for automatic rollback
test "transactions with raw C API" {
    var db: ?*c.sqlite3 = null;
    var result = c.sqlite3_open(":memory:", &db);
    if (result != SQLITE_OK) return SqliteError.OpenFailed;
    defer _ = c.sqlite3_close(db);

    // Create table
    const create_sql = "CREATE TABLE logs (id INTEGER PRIMARY KEY, message TEXT)";
    result = c.sqlite3_exec(db, create_sql, null, null, null);
    try checkSqlite(result);

    // Begin transaction
    result = c.sqlite3_exec(db, "BEGIN TRANSACTION", null, null, null);
    try checkSqlite(result);

    // Use errdefer to rollback on error
    errdefer _ = c.sqlite3_exec(db, "ROLLBACK", null, null, null);

    // Multiple inserts in transaction
    const insert1 = "INSERT INTO logs (message) VALUES ('Started')";
    result = c.sqlite3_exec(db, insert1, null, null, null);
    try checkSqlite(result);

    const insert2 = "INSERT INTO logs (message) VALUES ('Processing')";
    result = c.sqlite3_exec(db, insert2, null, null, null);
    try checkSqlite(result);

    const insert3 = "INSERT INTO logs (message) VALUES ('Completed')";
    result = c.sqlite3_exec(db, insert3, null, null, null);
    try checkSqlite(result);

    // Commit transaction
    result = c.sqlite3_exec(db, "COMMIT", null, null, null);
    try checkSqlite(result);

    // Verify all rows were inserted
    const count_sql = "SELECT COUNT(*) FROM logs";
    var stmt: ?*c.sqlite3_stmt = null;
    result = c.sqlite3_prepare_v2(db, count_sql, -1, &stmt, null);
    if (result != SQLITE_OK) return SqliteError.PrepareFailed;
    defer _ = c.sqlite3_finalize(stmt);

    if (c.sqlite3_step(stmt) == SQLITE_ROW) {
        const count = c.sqlite3_column_int(stmt, 0);
        try testing.expectEqual(3, count);
    }
}
// ANCHOR_END: transactions_expert

// ANCHOR: prepared_statements_expert
// Reusing prepared statements efficiently
test "reusable prepared statements" {
    var db: ?*c.sqlite3 = null;
    var result = c.sqlite3_open(":memory:", &db);
    if (result != SQLITE_OK) return SqliteError.OpenFailed;
    defer _ = c.sqlite3_close(db);

    const create_sql = "CREATE TABLE scores (player TEXT, score INTEGER)";
    result = c.sqlite3_exec(db, create_sql, null, null, null);
    try checkSqlite(result);

    // Prepare statement once
    const insert_sql = "INSERT INTO scores (player, score) VALUES (?1, ?2)";
    var stmt: ?*c.sqlite3_stmt = null;
    result = c.sqlite3_prepare_v2(db, insert_sql, -1, &stmt, null);
    if (result != SQLITE_OK) return SqliteError.PrepareFailed;
    defer _ = c.sqlite3_finalize(stmt);

    // Reuse statement for multiple inserts
    const players = [_][]const u8{ "Alice", "Bob", "Charlie" };
    const scores = [_]i32{ 100, 85, 92 };

    for (players, scores) |player, score| {
        // Reset statement for reuse
        _ = c.sqlite3_reset(stmt);
        _ = c.sqlite3_clear_bindings(stmt);

        // Bind new values
        result = c.sqlite3_bind_text(stmt, 1, player.ptr, @intCast(player.len), null);
        try checkSqlite(result);
        result = c.sqlite3_bind_int(stmt, 2, score);
        try checkSqlite(result);

        // Execute
        result = c.sqlite3_step(stmt);
        if (result != SQLITE_DONE) return SqliteError.StepFailed;
    }

    // Verify inserts
    const count_sql = "SELECT COUNT(*) FROM scores";
    var count_stmt: ?*c.sqlite3_stmt = null;
    result = c.sqlite3_prepare_v2(db, count_sql, -1, &count_stmt, null);
    if (result != SQLITE_OK) return SqliteError.PrepareFailed;
    defer _ = c.sqlite3_finalize(count_stmt);

    if (c.sqlite3_step(count_stmt) == SQLITE_ROW) {
        const count = c.sqlite3_column_int(count_stmt, 0);
        try testing.expectEqual(3, count);
    }
}
// ANCHOR_END: prepared_statements_expert

// ANCHOR: resource_management_pattern
// Pattern for safe resource management in Zig with SQLite
//
// Key principles:
// 1. Always use defer for cleanup immediately after resource acquisition
// 2. Use errdefer for error-path cleanup (e.g., transaction rollback)
// 3. Check all return codes - SQLite uses integers, not Zig errors
// 4. Prepare statements once, reuse multiple times
// 5. Use :memory: databases for tests to avoid filesystem dependencies
//
// Example pattern:
//
// var db: ?*c.sqlite3 = null;
// if (c.sqlite3_open(path, &db) != SQLITE_OK) return error.OpenFailed;
// defer _ = c.sqlite3_close(db);
//
// var stmt: ?*c.sqlite3_stmt = null;
// if (c.sqlite3_prepare_v2(db, sql, -1, &stmt, null) != SQLITE_OK)
//     return error.PrepareFailed;
// defer _ = c.sqlite3_finalize(stmt);
//
// // Use errdefer for transactions
// _ = c.sqlite3_exec(db, "BEGIN", null, null, null);
// errdefer _ = c.sqlite3_exec(db, "ROLLBACK", null, null, null);
// // ... operations ...
// _ = c.sqlite3_exec(db, "COMMIT", null, null, null);
// ANCHOR_END: resource_management_pattern
```

### See Also

- Recipe 5.4: Reading and Writing Binary Data
- Recipe 6.2: Reading and Writing JSON Data
- Recipe 15.1: Accessing C Code Using @cImport
- Recipe 15.7: Managing Memory Between C and Zig Boundaries

---

## Recipe 6.7: Decoding and Encoding Hexadecimal Digits {#recipe-6-7}

**Tags:** allocators, arraylist, data-encoding, data-structures, error-handling, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/06-data-encoding/recipe_6_7.zig`

### Problem

You need to convert binary data to hexadecimal strings for display or debugging, or decode hexadecimal strings back to binary data.

### Solution

### Basic Hex Conversion

```zig
/// Convert bytes to hexadecimal string (lowercase)
pub fn bytesToHex(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    var list = std.ArrayList(u8){};
    errdefer list.deinit(allocator);

    for (bytes) |byte| {
        try list.writer(allocator).print("{x:0>2}", .{byte});
    }

    return list.toOwnedSlice(allocator);
}

/// Convert hexadecimal string to bytes
pub fn hexToBytes(allocator: std.mem.Allocator, hex: []const u8) ![]u8 {
    if (hex.len % 2 != 0) {
        return error.InvalidHexLength;
    }

    var result = try allocator.alloc(u8, hex.len / 2);
    errdefer allocator.free(result);

    for (0..result.len) |i| {
        const high = try hexCharToNibble(hex[i * 2]);
        const low = try hexCharToNibble(hex[i * 2 + 1]);
        result[i] = (high << 4) | low;
    }

    return result;
}
```

### Hex Dump

```zig
/// Create hex dump with ASCII representation
pub fn hexDump(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var offset: usize = 0;
    while (offset < bytes.len) {
        const line_len = @min(16, bytes.len - offset);
        const line = bytes[offset .. offset + line_len];

        // Offset
        const offset_str = try std.fmt.allocPrint(allocator, "{x:0>8}  ", .{offset});
        defer allocator.free(offset_str);
        try result.appendSlice(allocator, offset_str);

        // Hex bytes
        for (line, 0..) |byte, i| {
            if (i == 8) {
                try result.append(allocator, ' ');
            }
            const hex = try std.fmt.allocPrint(allocator, "{x:0>2} ", .{byte});
            defer allocator.free(hex);
            try result.appendSlice(allocator, hex);
        }

        // Padding
        if (line_len < 16) {
            var i: usize = line_len;
            while (i < 16) : (i += 1) {
                try result.appendSlice(allocator, "   ");
                if (i == 7) {
                    try result.append(allocator, ' ');
                }
            }
        }

        // ASCII
        try result.appendSlice(allocator, " |");
        for (line) |byte| {
            const char = if (std.ascii.isPrint(byte)) byte else '.';
            try result.append(allocator, char);
        }
        try result.appendSlice(allocator, "|\n");

        offset += line_len;
    }

    return result.toOwnedSlice(allocator);
}
```

### Advanced Hex Ops

```zig
/// Encode bytes to hex in pre-allocated buffer
pub fn bytesToHexBuf(bytes: []const u8, out: []u8) !void {
    if (out.len < bytes.len * 2) {
        return error.BufferTooSmall;
    }

    const hex_chars = "0123456789abcdef";
    for (bytes, 0..) |byte, i| {
        out[i * 2] = hex_chars[byte >> 4];
        out[i * 2 + 1] = hex_chars[byte & 0x0F];
    }
}

/// Decode hex string to bytes, skipping invalid characters
pub fn hexToBytesLenient(allocator: std.mem.Allocator, hex: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i + 1 < hex.len) {
        const high = hexCharToNibble(hex[i]) catch {
            i += 1;
            continue;
        };
        const low = hexCharToNibble(hex[i + 1]) catch {
            i += 1;
            continue;
        };

        try result.append(allocator, (high << 4) | low);
        i += 2;
    }

    return result.toOwnedSlice(allocator);
}
```

    try std.testing.expectEqualStrings("deadbeef", hex);
}

test "hex to bytes" {
    const allocator = std.testing.allocator;

    const bytes = try hexToBytes(allocator, "deadbeef");
    defer allocator.free(bytes);

    try std.testing.expectEqual(@as(usize, 4), bytes.len);
    try std.testing.expectEqual(@as(u8, 0xDE), bytes[0]);
    try std.testing.expectEqual(@as(u8, 0xAD), bytes[1]);
    try std.testing.expectEqual(@as(u8, 0xBE), bytes[2]);
    try std.testing.expectEqual(@as(u8, 0xEF), bytes[3]);
}
```

### Discussion

### Uppercase Hexadecimal

Use uppercase hex digits with the `{X}` format specifier:

```zig
pub fn bytesToHexUpper(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    var list = std.ArrayList(u8){};
    errdefer list.deinit(allocator);

    for (bytes) |byte| {
        try list.writer(allocator).print("{X:0>2}", .{byte});
    }

    return list.toOwnedSlice(allocator);
}

test "bytes to hex uppercase" {
    const allocator = std.testing.allocator;

    const bytes = [_]u8{ 0xDE, 0xAD, 0xBE, 0xEF };
    const hex = try bytesToHexUpper(allocator, &bytes);
    defer allocator.free(hex);

    try std.testing.expectEqualStrings("DEADBEEF", hex);
}
```

### Hex with Separators

Add separators between bytes:

```zig
pub fn bytesToHexWithSep(
    allocator: std.mem.Allocator,
    bytes: []const u8,
    separator: []const u8,
) ![]u8 {
    if (bytes.len == 0) {
        return allocator.alloc(u8, 0);
    }

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (bytes, 0..) |byte, i| {
        if (i > 0) {
            try result.appendSlice(allocator, separator);
        }
        const hex = try std.fmt.allocPrint(allocator, "{x:0>2}", .{byte});
        defer allocator.free(hex);
        try result.appendSlice(allocator, hex);
    }

    return result.toOwnedSlice(allocator);
}

test "hex with separator" {
    const allocator = std.testing.allocator;

    const bytes = [_]u8{ 0xDE, 0xAD, 0xBE, 0xEF };
    const hex = try bytesToHexWithSep(allocator, &bytes, ":");
    defer allocator.free(hex);

    try std.testing.expectEqualStrings("de:ad:be:ef", hex);
}
```

### Hex Dump

Create hex dump with ASCII:

```zig
pub fn hexDump(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var offset: usize = 0;
    while (offset < bytes.len) {
        const line_len = @min(16, bytes.len - offset);
        const line = bytes[offset .. offset + line_len];

        // Offset
        const offset_str = try std.fmt.allocPrint(allocator, "{x:0>8}  ", .{offset});
        defer allocator.free(offset_str);
        try result.appendSlice(allocator, offset_str);

        // Hex bytes
        for (line, 0..) |byte, i| {
            if (i == 8) {
                try result.append(allocator, ' ');
            }
            const hex = try std.fmt.allocPrint(allocator, "{x:0>2} ", .{byte});
            defer allocator.free(hex);
            try result.appendSlice(allocator, hex);
        }

        // Padding
        if (line_len < 16) {
            var i: usize = line_len;
            while (i < 16) : (i += 1) {
                try result.appendSlice(allocator, "   ");
                if (i == 7) {
                    try result.append(allocator, ' ');
                }
            }
        }

        // ASCII
        try result.appendSlice(allocator, " |");
        for (line) |byte| {
            const char = if (std.ascii.isPrint(byte)) byte else '.';
            try result.append(allocator, char);
        }
        try result.appendSlice(allocator, "|\n");

        offset += line_len;
    }

    return result.toOwnedSlice(allocator);
}

test "hex dump" {
    const allocator = std.testing.allocator;

    const bytes = "Hello, World!\x00\xFF";
    const dump = try hexDump(allocator, bytes);
    defer allocator.free(dump);

    try std.testing.expect(std.mem.indexOf(u8, dump, "48 65 6c 6c") != null);
    try std.testing.expect(std.mem.indexOf(u8, dump, "|Hello, World|") != null);
}
```

### Integer to Hex

Convert integers to hex:

```zig
pub fn u32ToHex(allocator: std.mem.Allocator, value: u32) ![]u8 {
    return std.fmt.allocPrint(allocator, "{x}", .{value});
}

pub fn u32ToHexPadded(allocator: std.mem.Allocator, value: u32) ![]u8 {
    return std.fmt.allocPrint(allocator, "{x:0>8}", .{value});
}

test "integer to hex" {
    const allocator = std.testing.allocator;

    const hex1 = try u32ToHex(allocator, 0xDEADBEEF);
    defer allocator.free(hex1);
    try std.testing.expectEqualStrings("deadbeef", hex1);

    const hex2 = try u32ToHexPadded(allocator, 0x42);
    defer allocator.free(hex2);
    try std.testing.expectEqualStrings("00000042", hex2);
}
```

### Hex to Integer

Parse hex strings to integers:

```zig
pub fn hexToU32(hex: []const u8) !u32 {
    return try std.fmt.parseInt(u32, hex, 16);
}

pub fn hexToU64(hex: []const u8) !u64 {
    return try std.fmt.parseInt(u64, hex, 16);
}

test "hex to integer" {
    try std.testing.expectEqual(@as(u32, 0xDEADBEEF), try hexToU32("DEADBEEF"));
    try std.testing.expectEqual(@as(u32, 0xDEADBEEF), try hexToU32("deadbeef"));
    try std.testing.expectEqual(@as(u64, 0x123456789ABCDEF0), try hexToU64("123456789ABCDEF0"));
}
```

### Validating Hex Strings

Check if string is valid hex:

```zig
pub fn isValidHex(hex: []const u8) bool {
    if (hex.len == 0 or hex.len % 2 != 0) {
        return false;
    }

    for (hex) |char| {
        switch (char) {
            '0'...'9', 'a'...'f', 'A'...'F' => {},
            else => return false,
        }
    }

    return true;
}

test "validate hex" {
    try std.testing.expect(isValidHex("deadbeef"));
    try std.testing.expect(isValidHex("DEADBEEF"));
    try std.testing.expect(isValidHex("0123456789abcdefABCDEF"));

    try std.testing.expect(!isValidHex("xyz"));
    try std.testing.expect(!isValidHex("dead")); // odd length allowed for this test
    try std.testing.expect(!isValidHex(""));
}
```

### In-Place Hex Encoding

Encode to pre-allocated buffer:

```zig
pub fn bytesToHexBuf(bytes: []const u8, out: []u8) !void {
    if (out.len < bytes.len * 2) {
        return error.BufferTooSmall;
    }

    const hex_chars = "0123456789abcdef";
    for (bytes, 0..) |byte, i| {
        out[i * 2] = hex_chars[byte >> 4];
        out[i * 2 + 1] = hex_chars[byte & 0x0F];
    }
}

test "hex to buffer" {
    const bytes = [_]u8{ 0xDE, 0xAD, 0xBE, 0xEF };
    var buf: [8]u8 = undefined;

    try bytesToHexBuf(&bytes, &buf);

    try std.testing.expectEqualStrings("deadbeef", &buf);
}
```

### Decoding with Error Recovery

Skip invalid characters:

```zig
pub fn hexToBytesLenient(allocator: std.mem.Allocator, hex: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i + 1 < hex.len) {
        const high = hexCharToNibble(hex[i]) catch {
            i += 1;
            continue;
        };
        const low = hexCharToNibble(hex[i + 1]) catch {
            i += 1;
            continue;
        };

        try result.append(allocator, (high << 4) | low);
        i += 2;
    }

    return result.toOwnedSlice(allocator);
}

test "hex lenient parsing" {
    const allocator = std.testing.allocator;

    const bytes = try hexToBytesLenient(allocator, "de:ad:be:ef");
    defer allocator.free(bytes);

    try std.testing.expectEqual(@as(usize, 4), bytes.len);
}
```

### Best Practices

**Encoding:**
- Use `{x:0>2}` format specifier for lowercase hex
- Use `{X:0>2}` format specifier for uppercase hex
- Pre-allocate buffers for large conversions with `bytesToHexBuf`

**Decoding:**
```zig
// Validate before decoding
if (!isValidHex(input)) {
    return error.InvalidHex;
}

const bytes = try hexToBytes(allocator, input);
defer allocator.free(bytes);
```

**Performance:**
- In-place encoding avoids allocations
- Use fixed buffers for known sizes
- Batch process large data

**Error handling:**
- Check hex string length (must be even)
- Validate all characters are valid hex digits
- Handle case-insensitivity when needed

### Related Functions

- `std.fmt.allocPrint()` - Format and allocate string
- `std.fmt.parseInt()` - Parse hex string to integer with base 16
- `std.ArrayList.writer()` - Get writer for efficient string building
- `std.ascii.isPrint()` - Check if character is printable
- `std.mem.indexOf()` - Find substring

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_hex_conversion
/// Convert bytes to hexadecimal string (lowercase)
pub fn bytesToHex(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    var list = std.ArrayList(u8){};
    errdefer list.deinit(allocator);

    for (bytes) |byte| {
        try list.writer(allocator).print("{x:0>2}", .{byte});
    }

    return list.toOwnedSlice(allocator);
}

/// Convert hexadecimal string to bytes
pub fn hexToBytes(allocator: std.mem.Allocator, hex: []const u8) ![]u8 {
    if (hex.len % 2 != 0) {
        return error.InvalidHexLength;
    }

    var result = try allocator.alloc(u8, hex.len / 2);
    errdefer allocator.free(result);

    for (0..result.len) |i| {
        const high = try hexCharToNibble(hex[i * 2]);
        const low = try hexCharToNibble(hex[i * 2 + 1]);
        result[i] = (high << 4) | low;
    }

    return result;
}
// ANCHOR_END: basic_hex_conversion

/// Convert hex character to nibble (4 bits)
fn hexCharToNibble(char: u8) !u8 {
    return switch (char) {
        '0'...'9' => char - '0',
        'a'...'f' => char - 'a' + 10,
        'A'...'F' => char - 'A' + 10,
        else => error.InvalidHexCharacter,
    };
}

/// Convert bytes to hexadecimal string (uppercase)
pub fn bytesToHexUpper(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    var list = std.ArrayList(u8){};
    errdefer list.deinit(allocator);

    for (bytes) |byte| {
        try list.writer(allocator).print("{X:0>2}", .{byte});
    }

    return list.toOwnedSlice(allocator);
}

/// Convert bytes to hex with separator
pub fn bytesToHexWithSep(
    allocator: std.mem.Allocator,
    bytes: []const u8,
    separator: []const u8,
) ![]u8 {
    if (bytes.len == 0) {
        return allocator.alloc(u8, 0);
    }

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (bytes, 0..) |byte, i| {
        if (i > 0) {
            try result.appendSlice(allocator, separator);
        }
        const hex = try std.fmt.allocPrint(allocator, "{x:0>2}", .{byte});
        defer allocator.free(hex);
        try result.appendSlice(allocator, hex);
    }

    return result.toOwnedSlice(allocator);
}

// ANCHOR: hex_dump
/// Create hex dump with ASCII representation
pub fn hexDump(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var offset: usize = 0;
    while (offset < bytes.len) {
        const line_len = @min(16, bytes.len - offset);
        const line = bytes[offset .. offset + line_len];

        // Offset
        const offset_str = try std.fmt.allocPrint(allocator, "{x:0>8}  ", .{offset});
        defer allocator.free(offset_str);
        try result.appendSlice(allocator, offset_str);

        // Hex bytes
        for (line, 0..) |byte, i| {
            if (i == 8) {
                try result.append(allocator, ' ');
            }
            const hex = try std.fmt.allocPrint(allocator, "{x:0>2} ", .{byte});
            defer allocator.free(hex);
            try result.appendSlice(allocator, hex);
        }

        // Padding
        if (line_len < 16) {
            var i: usize = line_len;
            while (i < 16) : (i += 1) {
                try result.appendSlice(allocator, "   ");
                if (i == 7) {
                    try result.append(allocator, ' ');
                }
            }
        }

        // ASCII
        try result.appendSlice(allocator, " |");
        for (line) |byte| {
            const char = if (std.ascii.isPrint(byte)) byte else '.';
            try result.append(allocator, char);
        }
        try result.appendSlice(allocator, "|\n");

        offset += line_len;
    }

    return result.toOwnedSlice(allocator);
}
// ANCHOR_END: hex_dump

/// Convert u32 to hex string
pub fn u32ToHex(allocator: std.mem.Allocator, value: u32) ![]u8 {
    return std.fmt.allocPrint(allocator, "{x}", .{value});
}

/// Convert u32 to padded hex string
pub fn u32ToHexPadded(allocator: std.mem.Allocator, value: u32) ![]u8 {
    return std.fmt.allocPrint(allocator, "{x:0>8}", .{value});
}

/// Parse hex string to u32
pub fn hexToU32(hex: []const u8) !u32 {
    return try std.fmt.parseInt(u32, hex, 16);
}

/// Parse hex string to u64
pub fn hexToU64(hex: []const u8) !u64 {
    return try std.fmt.parseInt(u64, hex, 16);
}

/// Check if string is valid hexadecimal
pub fn isValidHex(hex: []const u8) bool {
    if (hex.len == 0 or hex.len % 2 != 0) {
        return false;
    }

    for (hex) |char| {
        switch (char) {
            '0'...'9', 'a'...'f', 'A'...'F' => {},
            else => return false,
        }
    }

    return true;
}

// ANCHOR: advanced_hex_ops
/// Encode bytes to hex in pre-allocated buffer
pub fn bytesToHexBuf(bytes: []const u8, out: []u8) !void {
    if (out.len < bytes.len * 2) {
        return error.BufferTooSmall;
    }

    const hex_chars = "0123456789abcdef";
    for (bytes, 0..) |byte, i| {
        out[i * 2] = hex_chars[byte >> 4];
        out[i * 2 + 1] = hex_chars[byte & 0x0F];
    }
}

/// Decode hex string to bytes, skipping invalid characters
pub fn hexToBytesLenient(allocator: std.mem.Allocator, hex: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i + 1 < hex.len) {
        const high = hexCharToNibble(hex[i]) catch {
            i += 1;
            continue;
        };
        const low = hexCharToNibble(hex[i + 1]) catch {
            i += 1;
            continue;
        };

        try result.append(allocator, (high << 4) | low);
        i += 2;
    }

    return result.toOwnedSlice(allocator);
}
// ANCHOR_END: advanced_hex_ops

// Tests

test "bytes to hex" {
    const allocator = std.testing.allocator;

    const bytes = [_]u8{ 0xDE, 0xAD, 0xBE, 0xEF };
    const hex = try bytesToHex(allocator, &bytes);
    defer allocator.free(hex);

    try std.testing.expectEqualStrings("deadbeef", hex);
}

test "hex to bytes" {
    const allocator = std.testing.allocator;

    const bytes = try hexToBytes(allocator, "deadbeef");
    defer allocator.free(bytes);

    try std.testing.expectEqual(@as(usize, 4), bytes.len);
    try std.testing.expectEqual(@as(u8, 0xDE), bytes[0]);
    try std.testing.expectEqual(@as(u8, 0xAD), bytes[1]);
    try std.testing.expectEqual(@as(u8, 0xBE), bytes[2]);
    try std.testing.expectEqual(@as(u8, 0xEF), bytes[3]);
}

test "bytes to hex uppercase" {
    const allocator = std.testing.allocator;

    const bytes = [_]u8{ 0xDE, 0xAD, 0xBE, 0xEF };
    const hex = try bytesToHexUpper(allocator, &bytes);
    defer allocator.free(hex);

    try std.testing.expectEqualStrings("DEADBEEF", hex);
}

test "hex with separator" {
    const allocator = std.testing.allocator;

    const bytes = [_]u8{ 0xDE, 0xAD, 0xBE, 0xEF };
    const hex = try bytesToHexWithSep(allocator, &bytes, ":");
    defer allocator.free(hex);

    try std.testing.expectEqualStrings("de:ad:be:ef", hex);
}

test "hex with space separator" {
    const allocator = std.testing.allocator;

    const bytes = [_]u8{ 0x01, 0x02, 0x03 };
    const hex = try bytesToHexWithSep(allocator, &bytes, " ");
    defer allocator.free(hex);

    try std.testing.expectEqualStrings("01 02 03", hex);
}

test "hex dump" {
    const allocator = std.testing.allocator;

    const bytes = "Hello, World!\x00\xFF";
    const dump = try hexDump(allocator, bytes);
    defer allocator.free(dump);

    try std.testing.expect(std.mem.indexOf(u8, dump, "48 65 6c 6c") != null);
    try std.testing.expect(std.mem.indexOf(u8, dump, "|Hello, World") != null);
}

test "integer to hex" {
    const allocator = std.testing.allocator;

    const hex1 = try u32ToHex(allocator, 0xDEADBEEF);
    defer allocator.free(hex1);
    try std.testing.expectEqualStrings("deadbeef", hex1);

    const hex2 = try u32ToHexPadded(allocator, 0x42);
    defer allocator.free(hex2);
    try std.testing.expectEqualStrings("00000042", hex2);
}

test "hex to integer" {
    try std.testing.expectEqual(@as(u32, 0xDEADBEEF), try hexToU32("DEADBEEF"));
    try std.testing.expectEqual(@as(u32, 0xDEADBEEF), try hexToU32("deadbeef"));
    try std.testing.expectEqual(@as(u64, 0x123456789ABCDEF0), try hexToU64("123456789ABCDEF0"));
}

test "validate hex" {
    try std.testing.expect(isValidHex("deadbeef"));
    try std.testing.expect(isValidHex("DEADBEEF"));
    try std.testing.expect(isValidHex("0123456789abcdefABCDEF0f"));

    try std.testing.expect(!isValidHex("xyz"));
    try std.testing.expect(!isValidHex("dead ")); // contains space
    try std.testing.expect(!isValidHex(""));
    try std.testing.expect(!isValidHex("abc")); // odd length
}

test "hex to buffer" {
    const bytes = [_]u8{ 0xDE, 0xAD, 0xBE, 0xEF };
    var buf: [8]u8 = undefined;

    try bytesToHexBuf(&bytes, &buf);

    try std.testing.expectEqualStrings("deadbeef", &buf);
}

test "hex to buffer too small" {
    const bytes = [_]u8{ 0xDE, 0xAD, 0xBE, 0xEF };
    var buf: [6]u8 = undefined;

    const result = bytesToHexBuf(&bytes, &buf);
    try std.testing.expectError(error.BufferTooSmall, result);
}

test "hex lenient parsing" {
    const allocator = std.testing.allocator;

    const bytes = try hexToBytesLenient(allocator, "de:ad:be:ef");
    defer allocator.free(bytes);

    try std.testing.expectEqual(@as(usize, 4), bytes.len);
    try std.testing.expectEqual(@as(u8, 0xDE), bytes[0]);
    try std.testing.expectEqual(@as(u8, 0xAD), bytes[1]);
}

test "hex lenient with spaces" {
    const allocator = std.testing.allocator;

    const bytes = try hexToBytesLenient(allocator, "de ad be ef");
    defer allocator.free(bytes);

    try std.testing.expectEqual(@as(usize, 4), bytes.len);
}

test "empty bytes to hex" {
    const allocator = std.testing.allocator;

    const bytes: []const u8 = &.{};
    const hex = try bytesToHex(allocator, bytes);
    defer allocator.free(hex);

    try std.testing.expectEqualStrings("", hex);
}

test "empty hex to bytes" {
    const allocator = std.testing.allocator;

    const bytes = try hexToBytes(allocator, "");
    defer allocator.free(bytes);

    try std.testing.expectEqual(@as(usize, 0), bytes.len);
}

test "single byte hex" {
    const allocator = std.testing.allocator;

    const bytes = [_]u8{0xFF};
    const hex = try bytesToHex(allocator, &bytes);
    defer allocator.free(hex);

    try std.testing.expectEqualStrings("ff", hex);
}

test "hex case insensitive decode" {
    const allocator = std.testing.allocator;

    const bytes1 = try hexToBytes(allocator, "abcdef");
    defer allocator.free(bytes1);

    const bytes2 = try hexToBytes(allocator, "ABCDEF");
    defer allocator.free(bytes2);

    const bytes3 = try hexToBytes(allocator, "AbCdEf");
    defer allocator.free(bytes3);

    try std.testing.expectEqualSlices(u8, bytes1, bytes2);
    try std.testing.expectEqualSlices(u8, bytes1, bytes3);
}

test "invalid hex length" {
    const allocator = std.testing.allocator;

    const result = hexToBytes(allocator, "abc");
    try std.testing.expectError(error.InvalidHexLength, result);
}

test "invalid hex character" {
    const allocator = std.testing.allocator;

    const result = hexToBytes(allocator, "abcg");
    try std.testing.expectError(error.InvalidHexCharacter, result);
}

test "hex nibble conversion" {
    try std.testing.expectEqual(@as(u8, 0), try hexCharToNibble('0'));
    try std.testing.expectEqual(@as(u8, 9), try hexCharToNibble('9'));
    try std.testing.expectEqual(@as(u8, 10), try hexCharToNibble('a'));
    try std.testing.expectEqual(@as(u8, 15), try hexCharToNibble('f'));
    try std.testing.expectEqual(@as(u8, 10), try hexCharToNibble('A'));
    try std.testing.expectEqual(@as(u8, 15), try hexCharToNibble('F'));

    try std.testing.expectError(error.InvalidHexCharacter, hexCharToNibble('g'));
    try std.testing.expectError(error.InvalidHexCharacter, hexCharToNibble('G'));
    try std.testing.expectError(error.InvalidHexCharacter, hexCharToNibble(' '));
}

test "zero padded hex" {
    const allocator = std.testing.allocator;

    const hex = try u32ToHexPadded(allocator, 0x00);
    defer allocator.free(hex);

    try std.testing.expectEqualStrings("00000000", hex);
}

test "hex separator empty bytes" {
    const allocator = std.testing.allocator;

    const bytes: []const u8 = &.{};
    const hex = try bytesToHexWithSep(allocator, bytes, ":");
    defer allocator.free(hex);

    try std.testing.expectEqualStrings("", hex);
}

test "large hex conversion" {
    const allocator = std.testing.allocator;

    var bytes: [256]u8 = undefined;
    for (&bytes, 0..) |*byte, i| {
        byte.* = @intCast(i);
    }

    const hex = try bytesToHex(allocator, &bytes);
    defer allocator.free(hex);

    try std.testing.expectEqual(@as(usize, 512), hex.len);

    const decoded = try hexToBytes(allocator, hex);
    defer allocator.free(decoded);

    try std.testing.expectEqualSlices(u8, &bytes, decoded);
}
```

---

## Recipe 6.8: Decoding and Encoding Base64 {#recipe-6-8}

**Tags:** allocators, arraylist, data-encoding, data-structures, error-handling, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/06-data-encoding/recipe_6_8.zig`

### Problem

You need to encode binary data as Base64 for transmission over text-only channels, or decode Base64 strings back to binary data.

### Solution

### Basic Base64

```zig
/// Encode data to Base64
pub fn encodeBase64(allocator: std.mem.Allocator, data: []const u8) ![]u8 {
    const encoder = std.base64.standard.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    const encoded = try allocator.alloc(u8, encoded_len);
    errdefer allocator.free(encoded);

    _ = encoder.encode(encoded, data);
    return encoded;
}

/// Decode Base64 to bytes
pub fn decodeBase64(allocator: std.mem.Allocator, encoded: []const u8) ![]u8 {
    const decoder = std.base64.standard.Decoder;
    const decoded_len = try decoder.calcSizeForSlice(encoded);

    const decoded = try allocator.alloc(u8, decoded_len);
    errdefer allocator.free(decoded);

    try decoder.decode(decoded, encoded);
    return decoded;
}
```

### URL Safe Base64

```zig
/// Encode data to URL-safe Base64
pub fn encodeBase64Url(allocator: std.mem.Allocator, data: []const u8) ![]u8 {
    const encoder = std.base64.url_safe.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    const encoded = try allocator.alloc(u8, encoded_len);
    errdefer allocator.free(encoded);

    _ = encoder.encode(encoded, data);
    return encoded;
}

/// Decode URL-safe Base64 to bytes
pub fn decodeBase64Url(allocator: std.mem.Allocator, encoded: []const u8) ![]u8 {
    const decoder = std.base64.url_safe.Decoder;
    const decoded_len = try decoder.calcSizeForSlice(encoded);

    const decoded = try allocator.alloc(u8, decoded_len);
    errdefer allocator.free(decoded);

    try decoder.decode(decoded, encoded);
    return decoded;
}
```

### Streaming Base64

```zig
/// Encode data to Base64 in streaming fashion
pub fn encodeBase64Stream(
    writer: anytype,
    data: []const u8,
    chunk_size: usize,
) !void {
    const encoder = std.base64.standard.Encoder;

    // Adjust chunk size to be multiple of 3 for proper Base64 encoding
    const adjusted_chunk = (chunk_size / 3) * 3;
    if (adjusted_chunk == 0) return error.ChunkTooSmall;

    var i: usize = 0;
    while (i < data.len) {
        const is_last = (i + adjusted_chunk >= data.len);
        const end = if (is_last) data.len else i + adjusted_chunk;
        const chunk = data[i..end];

        const encoded_len = encoder.calcSize(chunk.len);
        var buffer: [4096]u8 = undefined;

        _ = encoder.encode(buffer[0..encoded_len], chunk);
        try writer.writeAll(buffer[0..encoded_len]);

        i = end;
    }
}
```

### Discussion

### URL-Safe Base64

Use URL-safe encoding for filenames and URLs:

```zig
pub fn encodeBase64Url(allocator: std.mem.Allocator, data: []const u8) ![]u8 {
    const encoder = std.base64.url_safe.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    const encoded = try allocator.alloc(u8, encoded_len);
    errdefer allocator.free(encoded);

    return encoder.encode(encoded, data);
}

pub fn decodeBase64Url(allocator: std.mem.Allocator, encoded: []const u8) ![]u8 {
    const decoder = std.base64.url_safe.Decoder;
    const decoded_len = try decoder.calcSizeForSlice(encoded);

    const decoded = try allocator.alloc(u8, decoded_len);
    errdefer allocator.free(decoded);

    try decoder.decode(decoded, encoded);
    return decoded;
}

test "URL-safe base64" {
    const allocator = std.testing.allocator;

    const data = [_]u8{ 0xFF, 0xEF, 0xBE };

    const encoded = try encodeBase64Url(allocator, &data);
    defer allocator.free(encoded);

    // URL-safe uses '-' and '_' instead of '+' and '/'
    try std.testing.expect(std.mem.indexOf(u8, encoded, "+") == null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "/") == null);

    const decoded = try decodeBase64Url(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualSlices(u8, &data, decoded);
}
```

### Encoding Without Padding

Remove padding characters:

```zig
pub fn encodeBase64NoPad(allocator: std.mem.Allocator, data: []const u8) ![]u8 {
    const encoder = std.base64.standard_no_pad.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    const encoded = try allocator.alloc(u8, encoded_len);
    errdefer allocator.free(encoded);

    return encoder.encode(encoded, data);
}

test "base64 without padding" {
    const allocator = std.testing.allocator;

    const data = "Hello";

    const encoded = try encodeBase64NoPad(allocator, data);
    defer allocator.free(encoded);

    // Should not end with '='
    try std.testing.expect(encoded[encoded.len - 1] != '=');
    try std.testing.expectEqualStrings("SGVsbG8", encoded);
}
```

### Streaming Base64 Encoding

Encode large data in chunks:

```zig
pub fn encodeBase64Stream(
    writer: anytype,
    data: []const u8,
    chunk_size: usize,
) !void {
    const encoder = std.base64.standard.Encoder;

    // Adjust chunk size to be multiple of 3 for proper Base64 encoding
    const adjusted_chunk = (chunk_size / 3) * 3;
    if (adjusted_chunk == 0) return error.ChunkTooSmall;

    var i: usize = 0;
    while (i < data.len) {
        const is_last = (i + adjusted_chunk >= data.len);
        const end = if (is_last) data.len else i + adjusted_chunk;
        const chunk = data[i..end];

        const encoded_len = encoder.calcSize(chunk.len);
        var buffer: [4096]u8 = undefined;

        _ = encoder.encode(buffer[0..encoded_len], chunk);
        try writer.writeAll(buffer[0..encoded_len]);

        i = end;
    }
}

test "streaming base64 encoding" {
    const allocator = std.testing.allocator;

    const data = "The quick brown fox jumps over the lazy dog";

    var list = std.ArrayList(u8){};
    errdefer list.deinit(allocator);

    try encodeBase64Stream(list.writer(allocator), data, 10);

    const encoded = try list.toOwnedSlice(allocator);
    defer allocator.free(encoded);

    // Verify it decodes correctly
    const decoded = try decodeBase64(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualStrings(data, decoded);
}
```

### Decoding with Validation

Validate Base64 input:

```zig
pub fn isValidBase64(input: []const u8) bool {
    const decoder = std.base64.standard.Decoder;

    // Check length
    if (input.len == 0) return true;
    if (input.len % 4 != 0) return false;

    // Try to allocate and decode to validate
    var buffer: [4096]u8 = undefined;
    if (input.len / 4 * 3 > buffer.len) return false;

    const size = decoder.calcSizeForSlice(input) catch return false;
    decoder.decode(buffer[0..size], input) catch return false;

    return true;
}

test "validate base64" {
    try std.testing.expect(isValidBase64("SGVsbG8="));
    try std.testing.expect(isValidBase64("SGVsbG8sIFdvcmxkIQ=="));

    try std.testing.expect(!isValidBase64("SGVsb!!!"));
    try std.testing.expect(!isValidBase64("Not valid"));
}
```

### Encoding Binary Data

Handle arbitrary binary data:

```zig
pub fn encodeBinaryToBase64(
    allocator: std.mem.Allocator,
    data: []const u8,
) ![]u8 {
    const encoder = std.base64.standard.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    const encoded = try allocator.alloc(u8, encoded_len);
    errdefer allocator.free(encoded);

    return encoder.encode(encoded, data);
}

test "encode binary data" {
    const allocator = std.testing.allocator;

    const binary = [_]u8{ 0x00, 0xFF, 0x42, 0xAA, 0x55 };

    const encoded = try encodeBinaryToBase64(allocator, &binary);
    defer allocator.free(encoded);

    const decoded = try decodeBase64(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualSlices(u8, &binary, decoded);
}
```

### Fixed Buffer Encoding

Encode into a fixed-size buffer:

```zig
pub fn encodeBase64Buf(data: []const u8, out: []u8) ![]u8 {
    const encoder = std.base64.standard.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    if (out.len < encoded_len) {
        return error.BufferTooSmall;
    }

    return encoder.encode(out[0..encoded_len], data);
}

test "fixed buffer encoding" {
    const data = "Hello, World!";
    var buffer: [256]u8 = undefined;

    const encoded = try encodeBase64Buf(data, &buffer);

    try std.testing.expectEqualStrings("SGVsbG8sIFdvcmxkIQ==", encoded);
}

test "buffer too small" {
    const data = "Hello, World!";
    var buffer: [10]u8 = undefined;

    const result = encodeBase64Buf(data, &buffer);
    try std.testing.expectError(error.BufferTooSmall, result);
}
```

### Decoding Whitespace-Tolerant

Handle Base64 with whitespace:

```zig
pub fn decodeBase64Lenient(
    allocator: std.mem.Allocator,
    encoded: []const u8,
) ![]u8 {
    // Remove whitespace
    var cleaned = std.ArrayList(u8){};
    errdefer cleaned.deinit(allocator);

    for (encoded) |char| {
        if (!std.ascii.isWhitespace(char)) {
            try cleaned.append(allocator, char);
        }
    }

    const clean_data = try cleaned.toOwnedSlice(allocator);
    defer allocator.free(clean_data);

    return decodeBase64(allocator, clean_data);
}

test "decode with whitespace" {
    const allocator = std.testing.allocator;

    const encoded = "SGVs bG8s\nIFdv cmxk\r\nIQ==";

    const decoded = try decodeBase64Lenient(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualStrings("Hello, World!", decoded);
}
```

### Best Practices

**Encoding:**
- Use standard Base64 for general purposes
- Use URL-safe variant for URLs and filenames
- Use no-padding variant when padding causes issues
- Consider streaming for large data

**Decoding:**
```zig
// Always validate before decoding
if (!isValidBase64(input)) {
    return error.InvalidBase64;
}

const decoded = try decodeBase64(allocator, input);
defer allocator.free(decoded);
```

**Performance:**
- Pre-allocate buffers when size is known
- Use fixed buffers for small data
- Stream large data to avoid memory spikes

**Security:**
- Validate input length to prevent DoS
- Be aware of padding oracle attacks in cryptographic contexts
- Clean up sensitive data after decoding

### Related Functions

- `std.base64.standard.Encoder` - Standard Base64 encoder
- `std.base64.standard.Decoder` - Standard Base64 decoder
- `std.base64.url_safe.Encoder` - URL-safe Base64 encoder
- `std.base64.url_safe.Decoder` - URL-safe Base64 decoder
- `std.base64.standard_no_pad` - Base64 without padding
- `std.ascii.isWhitespace()` - Check for whitespace characters

### Full Tested Code

```zig
const std = @import("std");

// ANCHOR: basic_base64
/// Encode data to Base64
pub fn encodeBase64(allocator: std.mem.Allocator, data: []const u8) ![]u8 {
    const encoder = std.base64.standard.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    const encoded = try allocator.alloc(u8, encoded_len);
    errdefer allocator.free(encoded);

    _ = encoder.encode(encoded, data);
    return encoded;
}

/// Decode Base64 to bytes
pub fn decodeBase64(allocator: std.mem.Allocator, encoded: []const u8) ![]u8 {
    const decoder = std.base64.standard.Decoder;
    const decoded_len = try decoder.calcSizeForSlice(encoded);

    const decoded = try allocator.alloc(u8, decoded_len);
    errdefer allocator.free(decoded);

    try decoder.decode(decoded, encoded);
    return decoded;
}
// ANCHOR_END: basic_base64

// ANCHOR: url_safe_base64
/// Encode data to URL-safe Base64
pub fn encodeBase64Url(allocator: std.mem.Allocator, data: []const u8) ![]u8 {
    const encoder = std.base64.url_safe.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    const encoded = try allocator.alloc(u8, encoded_len);
    errdefer allocator.free(encoded);

    _ = encoder.encode(encoded, data);
    return encoded;
}

/// Decode URL-safe Base64 to bytes
pub fn decodeBase64Url(allocator: std.mem.Allocator, encoded: []const u8) ![]u8 {
    const decoder = std.base64.url_safe.Decoder;
    const decoded_len = try decoder.calcSizeForSlice(encoded);

    const decoded = try allocator.alloc(u8, decoded_len);
    errdefer allocator.free(decoded);

    try decoder.decode(decoded, encoded);
    return decoded;
}
// ANCHOR_END: url_safe_base64

/// Encode data to Base64 without padding
pub fn encodeBase64NoPad(allocator: std.mem.Allocator, data: []const u8) ![]u8 {
    const encoder = std.base64.standard_no_pad.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    const encoded = try allocator.alloc(u8, encoded_len);
    errdefer allocator.free(encoded);

    _ = encoder.encode(encoded, data);
    return encoded;
}

// ANCHOR: streaming_base64
/// Encode data to Base64 in streaming fashion
pub fn encodeBase64Stream(
    writer: anytype,
    data: []const u8,
    chunk_size: usize,
) !void {
    const encoder = std.base64.standard.Encoder;

    // Adjust chunk size to be multiple of 3 for proper Base64 encoding
    const adjusted_chunk = (chunk_size / 3) * 3;
    if (adjusted_chunk == 0) return error.ChunkTooSmall;

    var i: usize = 0;
    while (i < data.len) {
        const is_last = (i + adjusted_chunk >= data.len);
        const end = if (is_last) data.len else i + adjusted_chunk;
        const chunk = data[i..end];

        const encoded_len = encoder.calcSize(chunk.len);
        var buffer: [4096]u8 = undefined;

        _ = encoder.encode(buffer[0..encoded_len], chunk);
        try writer.writeAll(buffer[0..encoded_len]);

        i = end;
    }
}
// ANCHOR_END: streaming_base64

/// Validate Base64 string
pub fn isValidBase64(input: []const u8) bool {
    const decoder = std.base64.standard.Decoder;

    // Check length
    if (input.len == 0) return true;
    if (input.len % 4 != 0) return false;

    // Try to allocate and decode to validate
    var buffer: [4096]u8 = undefined;
    if (input.len / 4 * 3 > buffer.len) return false;

    const size = decoder.calcSizeForSlice(input) catch return false;
    decoder.decode(buffer[0..size], input) catch return false;

    return true;
}

/// Encode binary data to Base64
pub fn encodeBinaryToBase64(
    allocator: std.mem.Allocator,
    data: []const u8,
) ![]u8 {
    const encoder = std.base64.standard.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    const encoded = try allocator.alloc(u8, encoded_len);
    errdefer allocator.free(encoded);

    _ = encoder.encode(encoded, data);
    return encoded;
}

/// Encode to fixed buffer
pub fn encodeBase64Buf(data: []const u8, out: []u8) ![]u8 {
    const encoder = std.base64.standard.Encoder;
    const encoded_len = encoder.calcSize(data.len);

    if (out.len < encoded_len) {
        return error.BufferTooSmall;
    }

    _ = encoder.encode(out[0..encoded_len], data);
    return out[0..encoded_len];
}

/// Decode Base64 with whitespace tolerance
pub fn decodeBase64Lenient(
    allocator: std.mem.Allocator,
    encoded: []const u8,
) ![]u8 {
    // Remove whitespace
    var cleaned = std.ArrayList(u8){};
    errdefer cleaned.deinit(allocator);

    for (encoded) |char| {
        if (!std.ascii.isWhitespace(char)) {
            try cleaned.append(allocator, char);
        }
    }

    const clean_data = try cleaned.toOwnedSlice(allocator);
    defer allocator.free(clean_data);

    return decodeBase64(allocator, clean_data);
}

// Tests

test "encode and decode base64" {
    const allocator = std.testing.allocator;

    const original = "Hello, World!";

    const encoded = try encodeBase64(allocator, original);
    defer allocator.free(encoded);

    try std.testing.expectEqualStrings("SGVsbG8sIFdvcmxkIQ==", encoded);

    const decoded = try decodeBase64(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualStrings(original, decoded);
}

test "URL-safe base64" {
    const allocator = std.testing.allocator;

    const data = [_]u8{ 0xFF, 0xEF, 0xBE };

    const encoded = try encodeBase64Url(allocator, &data);
    defer allocator.free(encoded);

    // URL-safe uses '-' and '_' instead of '+' and '/'
    try std.testing.expect(std.mem.indexOf(u8, encoded, "+") == null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "/") == null);

    const decoded = try decodeBase64Url(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualSlices(u8, &data, decoded);
}

test "base64 without padding" {
    const allocator = std.testing.allocator;

    const data = "Hello";

    const encoded = try encodeBase64NoPad(allocator, data);
    defer allocator.free(encoded);

    // Should not end with '='
    try std.testing.expect(encoded[encoded.len - 1] != '=');
    try std.testing.expectEqualStrings("SGVsbG8", encoded);
}

test "streaming base64 encoding" {
    const allocator = std.testing.allocator;

    const data = "The quick brown fox jumps over the lazy dog";

    var list = std.ArrayList(u8){};
    errdefer list.deinit(allocator);

    try encodeBase64Stream(list.writer(allocator), data, 10);

    const encoded = try list.toOwnedSlice(allocator);
    defer allocator.free(encoded);

    // Verify it decodes correctly
    const decoded = try decodeBase64(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualStrings(data, decoded);
}

test "validate base64" {
    try std.testing.expect(isValidBase64("SGVsbG8="));
    try std.testing.expect(isValidBase64("SGVsbG8sIFdvcmxkIQ=="));

    try std.testing.expect(!isValidBase64("SGVsb!!!"));
    try std.testing.expect(!isValidBase64("Not valid"));
}

test "encode binary data" {
    const allocator = std.testing.allocator;

    const binary = [_]u8{ 0x00, 0xFF, 0x42, 0xAA, 0x55 };

    const encoded = try encodeBinaryToBase64(allocator, &binary);
    defer allocator.free(encoded);

    const decoded = try decodeBase64(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualSlices(u8, &binary, decoded);
}

test "fixed buffer encoding" {
    const data = "Hello, World!";
    var buffer: [256]u8 = undefined;

    const encoded = try encodeBase64Buf(data, &buffer);

    try std.testing.expectEqualStrings("SGVsbG8sIFdvcmxkIQ==", encoded);
}

test "buffer too small" {
    const data = "Hello, World!";
    var buffer: [10]u8 = undefined;

    const result = encodeBase64Buf(data, &buffer);
    try std.testing.expectError(error.BufferTooSmall, result);
}

test "decode with whitespace" {
    const allocator = std.testing.allocator;

    const encoded = "SGVs bG8s\nIFdv cmxk\r\nIQ==";

    const decoded = try decodeBase64Lenient(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualStrings("Hello, World!", decoded);
}

test "empty string" {
    const allocator = std.testing.allocator;

    const encoded = try encodeBase64(allocator, "");
    defer allocator.free(encoded);

    try std.testing.expectEqualStrings("", encoded);

    const decoded = try decodeBase64(allocator, "");
    defer allocator.free(decoded);

    try std.testing.expectEqualStrings("", decoded);
}

test "single character" {
    const allocator = std.testing.allocator;

    const encoded = try encodeBase64(allocator, "A");
    defer allocator.free(encoded);

    try std.testing.expectEqualStrings("QQ==", encoded);

    const decoded = try decodeBase64(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualStrings("A", decoded);
}

test "all byte values" {
    const allocator = std.testing.allocator;

    var bytes: [256]u8 = undefined;
    for (&bytes, 0..) |*byte, i| {
        byte.* = @intCast(i);
    }

    const encoded = try encodeBase64(allocator, &bytes);
    defer allocator.free(encoded);

    const decoded = try decodeBase64(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualSlices(u8, &bytes, decoded);
}

test "roundtrip with special characters" {
    const allocator = std.testing.allocator;

    const original = "Hello\x00World\xFF\x01\x02";

    const encoded = try encodeBase64(allocator, original);
    defer allocator.free(encoded);

    const decoded = try decodeBase64(allocator, encoded);
    defer allocator.free(decoded);

    try std.testing.expectEqualStrings(original, decoded);
}

test "URL-safe vs standard" {
    const allocator = std.testing.allocator;

    // Data that will produce '+' or '/' in standard encoding
    const data = [_]u8{ 0xFB, 0xFF };

    const standard = try encodeBase64(allocator, &data);
    defer allocator.free(standard);

    const url_safe = try encodeBase64Url(allocator, &data);
    defer allocator.free(url_safe);

    // They should be different
    try std.testing.expect(!std.mem.eql(u8, standard, url_safe));

    // But both should decode to the same data
    const decoded_standard = try decodeBase64(allocator, standard);
    defer allocator.free(decoded_standard);

    const decoded_url = try decodeBase64Url(allocator, url_safe);
    defer allocator.free(decoded_url);

    try std.testing.expectEqualSlices(u8, &data, decoded_standard);
    try std.testing.expectEqualSlices(u8, &data, decoded_url);
}
```

---

## Recipe 6.9: Reading and Writing Binary Arrays of Structures {#recipe-6-9}

**Tags:** allocators, data-encoding, error-handling, memory, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/03-advanced/06-data-encoding/recipe_6_9.zig`

### Problem

You need to read or write binary files containing arrays of structured data, such as records from a database or network packets.

### Solution

### Basic Binary I/O

```zig
/// Write array of records to file
pub fn writeRecords(file: std.fs.File, records: []const Record) !void {
    const bytes = std.mem.sliceAsBytes(records);
    try file.writeAll(bytes);
}

/// Read array of records from file
pub fn readRecords(allocator: std.mem.Allocator, file: std.fs.File) ![]Record {
    const file_size = (try file.stat()).size;
    const record_count = file_size / @sizeOf(Record);

    const records = try allocator.alloc(Record, record_count);
    errdefer allocator.free(records);

    const bytes = std.mem.sliceAsBytes(records);
    const bytes_read = try file.readAll(bytes);

    if (bytes_read != bytes.len) {
        return error.UnexpectedEof;
    }

    return records;
}
```

### Endianness Handling

```zig
/// Network packet with endianness handling
const NetworkPacket = struct {
    version: u16,
    length: u32,
    sequence: u64,

    pub fn toBytes(self: NetworkPacket, endian: std.builtin.Endian) ![14]u8 {
        var bytes: [14]u8 = undefined;
        std.mem.writeInt(u16, bytes[0..2], self.version, endian);
        std.mem.writeInt(u32, bytes[2..6], self.length, endian);
        std.mem.writeInt(u64, bytes[6..14], self.sequence, endian);
        return bytes;
    }

    pub fn fromBytes(bytes: []const u8, endian: std.builtin.Endian) !NetworkPacket {
        if (bytes.len < 14) return error.BufferTooSmall;

        return NetworkPacket{
            .version = std.mem.readInt(u16, bytes[0..2], endian),
            .length = std.mem.readInt(u32, bytes[2..6], endian),
            .sequence = std.mem.readInt(u64, bytes[6..14], endian),
        };
    }
};
```

### Memory Mapping

```zig
/// Read records using memory mapping
pub fn readRecordsMmap(file: std.fs.File) ![]align(4096) const Record {
    const file_size = (try file.stat()).size;

    const mapped = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ,
        std.posix.MAP{ .TYPE = .SHARED },
        file.handle,
        0,
    );

    return std.mem.bytesAsSlice(Record, mapped);
}
```
        const file = try tmp_dir.createFile("records.bin", .{});
        defer file.close();
        try writeRecords(file, &records);
    }

    // Read
    {
        const file = try tmp_dir.openFile("records.bin", .{});
        defer file.close();

        const read_records = try readRecords(allocator, file);
        defer allocator.free(read_records);

        try std.testing.expectEqual(@as(usize, 2), read_records.len);
        try std.testing.expectEqual(records[0].id, read_records[0].id);
        try std.testing.expectEqual(records[0].x, read_records[0].x);
    }
}
```

### Discussion

### Packed Structs for Binary Formats

Use `packed struct` to control memory layout:

```zig
const BitmapHeader = packed struct {
    magic: u16,           // "BM"
    file_size: u32,
    reserved1: u16,
    reserved2: u16,
    offset: u32,
};

pub fn writeBitmapHeader(file: std.fs.File, header: BitmapHeader) !void {
    const bytes = std.mem.asBytes(&header);
    try file.writeAll(bytes);
}

pub fn readBitmapHeader(file: std.fs.File) !BitmapHeader {
    var header: BitmapHeader = undefined;
    const bytes = std.mem.asBytes(&header);
    const bytes_read = try file.readAll(bytes);

    if (bytes_read != bytes.len) {
        return error.UnexpectedEof;
    }

    return header;
}

test "bitmap header" {
    const header = BitmapHeader{
        .magic = 0x4D42, // "BM" in little-endian
        .file_size = 1024,
        .reserved1 = 0,
        .reserved2 = 0,
        .offset = 54,
    };

    // Packed struct size (may have padding)
    try std.testing.expect(@sizeOf(BitmapHeader) >= 14);

    var tmp = std.testing.tmpDir(.{});
    var tmp_dir = tmp.dir;
    defer tmp.cleanup();

    {
        const file = try tmp_dir.createFile("header.bin", .{});
        defer file.close();
        try writeBitmapHeader(file, header);
    }

    {
        const file = try tmp_dir.openFile("header.bin", .{});
        defer file.close();

        const read_header = try readBitmapHeader(file);
        try std.testing.expectEqual(header.magic, read_header.magic);
        try std.testing.expectEqual(header.file_size, read_header.file_size);
    }
}
```

### Endianness Handling

Handle byte order for cross-platform files:

```zig
const NetworkPacket = struct {
    version: u16,
    length: u32,
    sequence: u64,

    pub fn toBytes(self: NetworkPacket, endian: std.builtin.Endian) ![14]u8 {
        var bytes: [14]u8 = undefined;
        std.mem.writeInt(u16, bytes[0..2], self.version, endian);
        std.mem.writeInt(u32, bytes[2..6], self.length, endian);
        std.mem.writeInt(u64, bytes[6..14], self.sequence, endian);
        return bytes;
    }

    pub fn fromBytes(bytes: []const u8, endian: std.builtin.Endian) !NetworkPacket {
        if (bytes.len < 14) return error.BufferTooSmall;

        return NetworkPacket{
            .version = std.mem.readInt(u16, bytes[0..2], endian),
            .length = std.mem.readInt(u32, bytes[2..6], endian),
            .sequence = std.mem.readInt(u64, bytes[6..14], endian),
        };
    }
};

test "endianness handling" {
    const packet = NetworkPacket{
        .version = 1,
        .length = 256,
        .sequence = 0x123456789ABCDEF0,
    };

    const big_endian = try packet.toBytes(.big);
    const little_endian = try packet.toBytes(.little);

    // Different byte order
    try std.testing.expect(!std.mem.eql(u8, &big_endian, &little_endian));

    // But both decode correctly
    const from_big = try NetworkPacket.fromBytes(&big_endian, .big);
    const from_little = try NetworkPacket.fromBytes(&little_endian, .little);

    try std.testing.expectEqual(packet.version, from_big.version);
    try std.testing.expectEqual(packet.version, from_little.version);
}
```

### Variable-Length Records

Handle records with variable-length fields:

```zig
const VarRecord = struct {
    id: u32,
    name_len: u32,
    name: []const u8,

    pub fn write(self: VarRecord, writer: anytype) !void {
        try writer.writeInt(u32, self.id, .little);
        try writer.writeInt(u32, @intCast(self.name.len), .little);
        try writer.writeAll(self.name);
    }

    pub fn read(allocator: std.mem.Allocator, reader: anytype) !VarRecord {
        const id = try reader.readInt(u32, .little);
        const name_len = try reader.readInt(u32, .little);

        const name = try allocator.alloc(u8, name_len);
        errdefer allocator.free(name);

        const bytes_read = try reader.readAll(name);
        if (bytes_read != name_len) {
            return error.UnexpectedEof;
        }

        return VarRecord{
            .id = id,
            .name_len = name_len,
            .name = name,
        };
    }

    pub fn deinit(self: VarRecord, allocator: std.mem.Allocator) void {
        allocator.free(self.name);
    }
};

test "variable-length records" {
    const allocator = std.testing.allocator;

    const record = VarRecord{
        .id = 42,
        .name_len = 5,
        .name = "Alice",
    };

    var buffer: [256]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try record.write(fbs.writer());

    fbs.pos = 0;
    const read_record = try VarRecord.read(allocator, fbs.reader());
    defer read_record.deinit(allocator);

    try std.testing.expectEqual(record.id, read_record.id);
    try std.testing.expectEqualStrings(record.name, read_record.name);
}
```

### Struct Arrays with Padding

Handle alignment and padding:

```zig
const AlignedRecord = struct {
    a: u8,
    // Padding will be inserted here
    b: u32,
    c: u16,
    // Padding may be inserted here too

    pub fn serialize(self: AlignedRecord) [7]u8 {
        var bytes = [_]u8{0} ** 7;
        bytes[0] = self.a;
        std.mem.writeInt(u32, bytes[1..5], self.b, .little);
        std.mem.writeInt(u16, bytes[5..7], self.c, .little);
        return bytes;
    }

    pub fn deserialize(bytes: [7]u8) AlignedRecord {
        return .{
            .a = bytes[0],
            .b = std.mem.readInt(u32, bytes[1..5], .little),
            .c = std.mem.readInt(u16, bytes[5..7], .little),
        };
    }
};

test "aligned records" {
    const record = AlignedRecord{
        .a = 0x12,
        .b = 0x34567890,
        .c = 0xABCD,
    };

    // Regular struct has padding
    const struct_size = @sizeOf(AlignedRecord);
    try std.testing.expect(struct_size > 7); // Has padding

    // Serialized form is compact
    const bytes = record.serialize();
    try std.testing.expectEqual(@as(usize, 7), bytes.len);

    const deserialized = AlignedRecord.deserialize(bytes);
    try std.testing.expectEqual(record.a, deserialized.a);
    try std.testing.expectEqual(record.b, deserialized.b);
    try std.testing.expectEqual(record.c, deserialized.c);
}
```

### Writing Records Individually

Write records one at a time for sequential processing:

```zig
pub fn writeRecordsBuf(
    file: std.fs.File,
    records: []const Record,
) !void {
    for (records) |record| {
        const bytes = std.mem.asBytes(&record);
        try file.writeAll(bytes);
    }
}

pub fn readRecordsBuf(
    allocator: std.mem.Allocator,
    file: std.fs.File,
    count: usize,
) ![]Record {
    const records = try allocator.alloc(Record, count);
    errdefer allocator.free(records);

    for (records) |*record| {
        const bytes = std.mem.asBytes(record);
        const bytes_read = try file.readAll(bytes);
        if (bytes_read != bytes.len) {
            return error.UnexpectedEof;
        }
    }

    return records;
}

test "individual record IO" {
    const allocator = std.testing.allocator;

    const records = [_]Record{
        .{ .id = 1, .x = 1.0, .y = 2.0, .flags = 1 },
        .{ .id = 2, .x = 3.0, .y = 4.0, .flags = 2 },
        .{ .id = 3, .x = 5.0, .y = 6.0, .flags = 3 },
    };

    var tmp = std.testing.tmpDir(.{});
    var tmp_dir = tmp.dir;
    defer tmp.cleanup();

    {
        const file = try tmp_dir.createFile("records.bin", .{});
        defer file.close();
        try writeRecordsBuf(file, &records);
    }

    {
        const file = try tmp_dir.openFile("records.bin", .{});
        defer file.close();

        const read_records = try readRecordsBuf(allocator, file, records.len);
        defer allocator.free(read_records);

        try std.testing.expectEqual(records.len, read_records.len);
        for (records, read_records) |orig, read| {
            try std.testing.expectEqual(orig.id, read.id);
        }
    }
}
```

### Memory-Mapped Files

Use memory mapping for large datasets:

```zig
pub fn readRecordsMmap(file: std.fs.File) ![]align(4096) const Record {
    const file_size = (try file.stat()).size;

    const mapped = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ,
        std.posix.MAP{ .TYPE = .SHARED },
        file.handle,
        0,
    );

    return std.mem.bytesAsSlice(Record, mapped);
}

test "memory-mapped records" {
    const records = [_]Record{
        .{ .id = 1, .x = 10.0, .y = 20.0, .flags = 1 },
        .{ .id = 2, .x = 30.0, .y = 40.0, .flags = 2 },
    };

    var tmp = std.testing.tmpDir(.{});
    var tmp_dir = tmp.dir;
    defer tmp.cleanup();

    {
        const file = try tmp_dir.createFile("mmap.bin", .{});
        defer file.close();
        try writeRecords(file, &records);
    }

    {
        const file = try tmp_dir.openFile("mmap.bin", .{});
        defer file.close();

        const mapped_records = try readRecordsMmap(file);
        defer std.posix.munmap(@alignCast(std.mem.sliceAsBytes(mapped_records)));

        try std.testing.expectEqual(@as(usize, 2), mapped_records.len);
        try std.testing.expectEqual(records[0].id, mapped_records[0].id);
    }
}
```

### Best Practices

**Struct Layout:**
- Use `packed struct` for exact binary formats
- Be aware of alignment and padding in regular structs
- Document expected binary layout
- Consider using explicit serialization for portability

**Endianness:**
```zig
// Always specify endianness for cross-platform files
const bytes = try std.mem.writeInt(u32, buffer, value, .little);

// Use native endian only for temp files
const native_bytes = try std.mem.writeInt(u32, buffer, value, .native);
```

**Error Handling:**
```zig
// Always check for unexpected EOF
const bytes_read = try file.readAll(buffer);
if (bytes_read != buffer.len) {
    return error.UnexpectedEof;
}

// Validate file size
const file_size = (try file.stat()).size;
if (file_size % @sizeOf(Record) != 0) {
    return error.InvalidFileSize;
}
```

**Performance:**
- Use memory mapping for large read-only datasets
- Batch writes when possible by using slices
- Consider alignment for direct I/O
- Profile before optimizing

**Struct Size:**
- Packed structs may still have alignment padding
- Use `@sizeOf()` to verify actual size
- For exact binary layout, use manual serialization

### Related Functions

- `std.mem.asBytes()` - Convert value to byte slice
- `std.mem.bytesAsSlice()` - Convert bytes to typed slice
- `std.mem.sliceAsBytes()` - Convert slice to bytes
- `std.mem.readInt()` - Read integer with endianness
- `std.mem.writeInt()` - Write integer with endianness
- `std.io.bufferedReader()` - Create buffered reader
- `std.io.bufferedWriter()` - Create buffered writer
- `std.posix.mmap()` - Memory-map a file
- `std.posix.munmap()` - Unmap memory

### Full Tested Code

```zig
const std = @import("std");

/// Basic record structure
const Record = packed struct {
    id: u32,
    x: f32,
    y: f32,
    flags: u8,
};

// ANCHOR: basic_binary_io
/// Write array of records to file
pub fn writeRecords(file: std.fs.File, records: []const Record) !void {
    const bytes = std.mem.sliceAsBytes(records);
    try file.writeAll(bytes);
}

/// Read array of records from file
pub fn readRecords(allocator: std.mem.Allocator, file: std.fs.File) ![]Record {
    const file_size = (try file.stat()).size;
    const record_count = file_size / @sizeOf(Record);

    const records = try allocator.alloc(Record, record_count);
    errdefer allocator.free(records);

    const bytes = std.mem.sliceAsBytes(records);
    const bytes_read = try file.readAll(bytes);

    if (bytes_read != bytes.len) {
        return error.UnexpectedEof;
    }

    return records;
}
// ANCHOR_END: basic_binary_io

/// Bitmap header example
const BitmapHeader = packed struct {
    magic: u16,
    file_size: u32,
    reserved1: u16,
    reserved2: u16,
    offset: u32,
};

/// Write bitmap header
pub fn writeBitmapHeader(file: std.fs.File, header: BitmapHeader) !void {
    const bytes = std.mem.asBytes(&header);
    try file.writeAll(bytes);
}

/// Read bitmap header
pub fn readBitmapHeader(file: std.fs.File) !BitmapHeader {
    var header: BitmapHeader = undefined;
    const bytes = std.mem.asBytes(&header);
    const bytes_read = try file.readAll(bytes);

    if (bytes_read != bytes.len) {
        return error.UnexpectedEof;
    }

    return header;
}

// ANCHOR: endianness_handling
/// Network packet with endianness handling
const NetworkPacket = struct {
    version: u16,
    length: u32,
    sequence: u64,

    pub fn toBytes(self: NetworkPacket, endian: std.builtin.Endian) ![14]u8 {
        var bytes: [14]u8 = undefined;
        std.mem.writeInt(u16, bytes[0..2], self.version, endian);
        std.mem.writeInt(u32, bytes[2..6], self.length, endian);
        std.mem.writeInt(u64, bytes[6..14], self.sequence, endian);
        return bytes;
    }

    pub fn fromBytes(bytes: []const u8, endian: std.builtin.Endian) !NetworkPacket {
        if (bytes.len < 14) return error.BufferTooSmall;

        return NetworkPacket{
            .version = std.mem.readInt(u16, bytes[0..2], endian),
            .length = std.mem.readInt(u32, bytes[2..6], endian),
            .sequence = std.mem.readInt(u64, bytes[6..14], endian),
        };
    }
};
// ANCHOR_END: endianness_handling

/// Variable-length record
const VarRecord = struct {
    id: u32,
    name_len: u32,
    name: []const u8,

    pub fn write(self: VarRecord, writer: anytype) !void {
        try writer.writeInt(u32, self.id, .little);
        try writer.writeInt(u32, @intCast(self.name.len), .little);
        try writer.writeAll(self.name);
    }

    pub fn read(allocator: std.mem.Allocator, reader: anytype) !VarRecord {
        const id = try reader.readInt(u32, .little);
        const name_len = try reader.readInt(u32, .little);

        const name = try allocator.alloc(u8, name_len);
        errdefer allocator.free(name);

        const bytes_read = try reader.readAll(name);
        if (bytes_read != name_len) {
            return error.UnexpectedEof;
        }

        return VarRecord{
            .id = id,
            .name_len = name_len,
            .name = name,
        };
    }

    pub fn deinit(self: VarRecord, allocator: std.mem.Allocator) void {
        allocator.free(self.name);
    }
};

/// Aligned record with manual serialization
const AlignedRecord = struct {
    a: u8,
    b: u32,
    c: u16,

    pub fn serialize(self: AlignedRecord) [7]u8 {
        var bytes = [_]u8{0} ** 7;
        bytes[0] = self.a;
        std.mem.writeInt(u32, bytes[1..5], self.b, .little);
        std.mem.writeInt(u16, bytes[5..7], self.c, .little);
        return bytes;
    }

    pub fn deserialize(bytes: [7]u8) AlignedRecord {
        return .{
            .a = bytes[0],
            .b = std.mem.readInt(u32, bytes[1..5], .little),
            .c = std.mem.readInt(u16, bytes[5..7], .little),
        };
    }
};

/// Write records one at a time
pub fn writeRecordsBuf(
    file: std.fs.File,
    records: []const Record,
) !void {
    for (records) |record| {
        const bytes = std.mem.asBytes(&record);
        try file.writeAll(bytes);
    }
}

/// Read records one at a time
pub fn readRecordsBuf(
    allocator: std.mem.Allocator,
    file: std.fs.File,
    count: usize,
) ![]Record {
    const records = try allocator.alloc(Record, count);
    errdefer allocator.free(records);

    for (records) |*record| {
        const bytes = std.mem.asBytes(record);
        const bytes_read = try file.readAll(bytes);
        if (bytes_read != bytes.len) {
            return error.UnexpectedEof;
        }
    }

    return records;
}

// ANCHOR: memory_mapping
/// Read records using memory mapping
pub fn readRecordsMmap(file: std.fs.File) ![]align(4096) const Record {
    const file_size = (try file.stat()).size;

    const mapped = try std.posix.mmap(
        null,
        file_size,
        std.posix.PROT.READ,
        std.posix.MAP{ .TYPE = .SHARED },
        file.handle,
        0,
    );

    return std.mem.bytesAsSlice(Record, mapped);
}
// ANCHOR_END: memory_mapping

// Tests

test "write and read records" {
    const allocator = std.testing.allocator;

    const records = [_]Record{
        .{ .id = 1, .x = 10.5, .y = 20.5, .flags = 0xFF },
        .{ .id = 2, .x = 30.0, .y = 40.0, .flags = 0x01 },
    };

    var tmp = std.testing.tmpDir(.{});
    var tmp_dir = tmp.dir;
    defer tmp.cleanup();

    // Write
    {
        const file = try tmp_dir.createFile("records.bin", .{});
        defer file.close();
        try writeRecords(file, &records);
    }

    // Read
    {
        const file = try tmp_dir.openFile("records.bin", .{});
        defer file.close();

        const read_records = try readRecords(allocator, file);
        defer allocator.free(read_records);

        try std.testing.expectEqual(@as(usize, 2), read_records.len);
        try std.testing.expectEqual(records[0].id, read_records[0].id);
        try std.testing.expectEqual(records[0].x, read_records[0].x);
    }
}

test "bitmap header" {
    const header = BitmapHeader{
        .magic = 0x4D42,
        .file_size = 1024,
        .reserved1 = 0,
        .reserved2 = 0,
        .offset = 54,
    };

    // Packed struct size (may have padding)
    try std.testing.expect(@sizeOf(BitmapHeader) >= 14);

    var tmp = std.testing.tmpDir(.{});
    var tmp_dir = tmp.dir;
    defer tmp.cleanup();

    {
        const file = try tmp_dir.createFile("header.bin", .{});
        defer file.close();
        try writeBitmapHeader(file, header);
    }

    {
        const file = try tmp_dir.openFile("header.bin", .{});
        defer file.close();

        const read_header = try readBitmapHeader(file);
        try std.testing.expectEqual(header.magic, read_header.magic);
        try std.testing.expectEqual(header.file_size, read_header.file_size);
    }
}

test "endianness handling" {
    const packet = NetworkPacket{
        .version = 1,
        .length = 256,
        .sequence = 0x123456789ABCDEF0,
    };

    const big_endian = try packet.toBytes(.big);
    const little_endian = try packet.toBytes(.little);

    // Different byte order
    try std.testing.expect(!std.mem.eql(u8, &big_endian, &little_endian));

    // But both decode correctly
    const from_big = try NetworkPacket.fromBytes(&big_endian, .big);
    const from_little = try NetworkPacket.fromBytes(&little_endian, .little);

    try std.testing.expectEqual(packet.version, from_big.version);
    try std.testing.expectEqual(packet.version, from_little.version);
}

test "variable-length records" {
    const allocator = std.testing.allocator;

    const record = VarRecord{
        .id = 42,
        .name_len = 5,
        .name = "Alice",
    };

    var buffer: [256]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try record.write(fbs.writer());

    fbs.pos = 0;
    const read_record = try VarRecord.read(allocator, fbs.reader());
    defer read_record.deinit(allocator);

    try std.testing.expectEqual(record.id, read_record.id);
    try std.testing.expectEqualStrings(record.name, read_record.name);
}

test "aligned records" {
    const record = AlignedRecord{
        .a = 0x12,
        .b = 0x34567890,
        .c = 0xABCD,
    };

    // Regular struct has padding
    const struct_size = @sizeOf(AlignedRecord);
    try std.testing.expect(struct_size > 7);

    // Serialized form is compact
    const bytes = record.serialize();
    try std.testing.expectEqual(@as(usize, 7), bytes.len);

    const deserialized = AlignedRecord.deserialize(bytes);
    try std.testing.expectEqual(record.a, deserialized.a);
    try std.testing.expectEqual(record.b, deserialized.b);
    try std.testing.expectEqual(record.c, deserialized.c);
}

test "buffered binary IO" {
    const allocator = std.testing.allocator;

    const records = [_]Record{
        .{ .id = 1, .x = 1.0, .y = 2.0, .flags = 1 },
        .{ .id = 2, .x = 3.0, .y = 4.0, .flags = 2 },
        .{ .id = 3, .x = 5.0, .y = 6.0, .flags = 3 },
    };

    var tmp = std.testing.tmpDir(.{});
    var tmp_dir = tmp.dir;
    defer tmp.cleanup();

    {
        const file = try tmp_dir.createFile("buffered.bin", .{});
        defer file.close();
        try writeRecordsBuf(file, &records);
    }

    {
        const file = try tmp_dir.openFile("buffered.bin", .{});
        defer file.close();

        const read_records = try readRecordsBuf(allocator, file, records.len);
        defer allocator.free(read_records);

        try std.testing.expectEqual(records.len, read_records.len);
        for (records, read_records) |orig, read| {
            try std.testing.expectEqual(orig.id, read.id);
        }
    }
}

test "memory-mapped records" {
    const records = [_]Record{
        .{ .id = 1, .x = 10.0, .y = 20.0, .flags = 1 },
        .{ .id = 2, .x = 30.0, .y = 40.0, .flags = 2 },
    };

    var tmp = std.testing.tmpDir(.{});
    var tmp_dir = tmp.dir;
    defer tmp.cleanup();

    {
        const file = try tmp_dir.createFile("mmap.bin", .{});
        defer file.close();
        try writeRecords(file, &records);
    }

    {
        const file = try tmp_dir.openFile("mmap.bin", .{});
        defer file.close();

        const mapped_records = try readRecordsMmap(file);
        defer std.posix.munmap(@alignCast(std.mem.sliceAsBytes(mapped_records)));

        try std.testing.expectEqual(@as(usize, 2), mapped_records.len);
        try std.testing.expectEqual(records[0].id, mapped_records[0].id);
    }
}

test "empty file" {
    const allocator = std.testing.allocator;

    var tmp = std.testing.tmpDir(.{});
    var tmp_dir = tmp.dir;
    defer tmp.cleanup();

    {
        const file = try tmp_dir.createFile("empty.bin", .{});
        defer file.close();
        try writeRecords(file, &[_]Record{});
    }

    {
        const file = try tmp_dir.openFile("empty.bin", .{});
        defer file.close();

        const read_records = try readRecords(allocator, file);
        defer allocator.free(read_records);

        try std.testing.expectEqual(@as(usize, 0), read_records.len);
    }
}

test "record size" {
    // Packed struct size (may have padding for alignment)
    try std.testing.expect(@sizeOf(Record) >= 13);
}

test "network packet sizes" {
    const packet = NetworkPacket{
        .version = 1,
        .length = 100,
        .sequence = 1000,
    };

    const bytes = try packet.toBytes(.little);
    try std.testing.expectEqual(@as(usize, 14), bytes.len);
}

test "variable record with empty name" {
    const allocator = std.testing.allocator;

    const record = VarRecord{
        .id = 1,
        .name_len = 0,
        .name = "",
    };

    var buffer: [256]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buffer);

    try record.write(fbs.writer());

    fbs.pos = 0;
    const read_record = try VarRecord.read(allocator, fbs.reader());
    defer read_record.deinit(allocator);

    try std.testing.expectEqual(record.id, read_record.id);
    try std.testing.expectEqual(@as(usize, 0), read_record.name.len);
}

test "roundtrip multiple records" {
    const allocator = std.testing.allocator;

    var records = [_]Record{
        .{ .id = 1, .x = 1.5, .y = 2.5, .flags = 0x01 },
        .{ .id = 2, .x = 3.5, .y = 4.5, .flags = 0x02 },
        .{ .id = 3, .x = 5.5, .y = 6.5, .flags = 0x03 },
        .{ .id = 4, .x = 7.5, .y = 8.5, .flags = 0x04 },
        .{ .id = 5, .x = 9.5, .y = 10.5, .flags = 0x05 },
    };

    var tmp = std.testing.tmpDir(.{});
    var tmp_dir = tmp.dir;
    defer tmp.cleanup();

    {
        const file = try tmp_dir.createFile("multi.bin", .{});
        defer file.close();
        try writeRecords(file, &records);
    }

    {
        const file = try tmp_dir.openFile("multi.bin", .{});
        defer file.close();

        const read_records = try readRecords(allocator, file);
        defer allocator.free(read_records);

        try std.testing.expectEqual(records.len, read_records.len);

        for (records, read_records) |orig, read| {
            try std.testing.expectEqual(orig.id, read.id);
            try std.testing.expectEqual(orig.x, read.x);
            try std.testing.expectEqual(orig.y, read.y);
            try std.testing.expectEqual(orig.flags, read.flags);
        }
    }
}
```

---
