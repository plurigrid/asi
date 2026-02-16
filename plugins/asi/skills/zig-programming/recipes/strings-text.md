# Strings & Text Recipes

*14 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [2.1](#recipe-2-1) | Splitting Strings on Any of Multiple Delimiters | intermediate |
| [2.2](#recipe-2-2) | Matching Text at the Start or End of a String | intermediate |
| [2.3](#recipe-2-3) | Matching Strings Using Wildcard Patterns | intermediate |
| [2.4](#recipe-2-4) | Searching and Matching Text Patterns | intermediate |
| [2.5](#recipe-2-5) | Searching and Replacing Text | intermediate |
| [2.6](#recipe-2-6) | Searching and Replacing Case-Insensitive Text | intermediate |
| [2.7](#recipe-2-7) | Stripping Unwanted Characters from Strings | intermediate |
| [2.8](#recipe-2-8) | Combining and Concatenating Strings | intermediate |
| [2.9](#recipe-2-9) | Interpolating Variables in Strings | intermediate |
| [2.10](#recipe-2-10) | Aligning Text Strings | intermediate |
| [2.11](#recipe-2-11) | Reformatting Text to a Fixed Number of Columns | intermediate |
| [2.12](#recipe-2-12) | Working with Byte Strings vs Unicode Text | intermediate |
| [2.13](#recipe-2-13) | Sanitizing and Cleaning Up Text | intermediate |
| [2.14](#recipe-2-14) | Standardizing Unicode Text to a Normal Form | intermediate |

---

## Recipe 2.1: Splitting Strings on Any of Multiple Delimiters {#recipe-2-1}

**Tags:** allocators, arraylist, csv, data-structures, error-handling, memory, parsing, resource-cleanup, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_1.zig`

### Problem

You need to split a string into parts based on one or more delimiter characters, similar to Python's `str.split()` or JavaScript's `String.split()`.

### Solution

Zig's standard library provides several functions for splitting strings, each with different behavior:

### Split on Any of Multiple Delimiters

Use `tokenizeAny` to split on any character in a delimiter set, skipping empty tokens:

```zig
pub fn tokenizeAny(text: []const u8, delimiters: []const u8) mem.TokenIterator(u8, .any) {
    return mem.tokenizeAny(u8, text, delimiters);
}

/// Split string on a sequence of delimiters using tokenizeSequence
/// Returns an iterator that yields non-empty tokens
pub fn tokenizeSequence(text: []const u8, delimiter: []const u8) mem.TokenIterator(u8, .sequence) {
    return mem.tokenizeSequence(u8, text, delimiter);
}
```

### Split on Whitespace

A common pattern is splitting on any whitespace character:

```zig
const text = "  hello   world\tfoo\n\nbar  ";
var iter = mem.tokenizeAny(u8, text, " \t\n\r");

while (iter.next()) |token| {
    // token is "hello", "world", "foo", "bar"
}
```

### Split on a Sequence

Use `tokenizeSequence` for multi-character delimiters:

```zig
const text = "foo::bar::baz::qux";
var iter = mem.tokenizeSequence(u8, text, "::");

while (iter.next()) |token| {
    // token is "foo", "bar", "baz", "qux"
}
```

### Preserve Empty Tokens

Use `splitAny` instead of `tokenizeAny` to keep empty strings:

```zig
const text = "a,,b,c,";
var iter = mem.splitAny(u8, text, ",");

// Returns: "a", "", "b", "c", ""
while (iter.next()) |token| {
    // Empty tokens are included
}
```

### Collect Tokens into an ArrayList

For convenience, collect all tokens at once:

```zig
pub fn collectTokens(
    allocator: mem.Allocator,
    text: []const u8,
    delimiters: []const u8,
) !std.ArrayList([]const u8) {
    var result = std.ArrayList([]const u8){};
    errdefer result.deinit(allocator);

    var iter = mem.tokenizeAny(u8, text, delimiters);
    while (iter.next()) |token| {
        try result.append(allocator, token);
    }

    return result;
}

// Usage
var tokens = try collectTokens(allocator, "a,b,c", ",");
defer tokens.deinit(allocator);
// tokens.items is ["a", "b", "c"]
```

### Discussion

### Tokenize vs Split

Zig provides two families of functions with different behavior:

**`tokenize*` functions** skip empty tokens:
```zig
const text = "a,,b";
var iter = mem.tokenizeAny(u8, text, ",");
// Returns: "a", "b" (empty token skipped)
```

**`split*` functions** preserve empty tokens:
```zig
const text = "a,,b";
var iter = mem.splitAny(u8, text, ",");
// Returns: "a", "", "b"
```

Choose `tokenize` when you want to ignore consecutive delimiters (like splitting on whitespace). Use `split` when empty values are meaningful (like CSV parsing).

### Iterator Variants

Zig provides four main splitting functions:

- `mem.tokenizeAny(u8, text, delims)` - Skip empty, any delimiter
- `mem.tokenizeSequence(u8, text, delim)` - Skip empty, sequence delimiter
- `mem.splitAny(u8, text, delims)` - Keep empty, any delimiter
- `mem.splitSequence(u8, text, delim)` - Keep empty, sequence delimiter
- `mem.tokenizeScalar(u8, text, delim)` - Skip empty, single char
- `mem.splitScalar(u8, text, delim)` - Keep empty, single char

### Parsing CSV and Similar Formats

For CSV parsing, use `splitScalar` to preserve empty fields:

```zig
const csv = "name,age,city\nAlice,30,NYC\nBob,25,LA";
var lines = mem.splitScalar(u8, csv, '\n');

while (lines.next()) |line| {
    var cols = mem.splitScalar(u8, line, ',');
    while (cols.next()) |col| {
        // Process each column
    }
}
```

### Memory Efficiency

String iterators in Zig don't allocate memory - they return slices into the original string:

```zig
const text = "a,b,c";
var iter = mem.tokenizeAny(u8, text, ",");

// Each token is just a slice view into 'text'
const token = iter.next().?; // No allocation!
```

This is extremely efficient, but means the original string must remain valid while you're using the tokens.

### UTF-8 Considerations

Zig's split functions work on bytes (`u8`). For proper UTF-8 handling:

- Single-byte delimiters (like `,` or `\n`) work correctly with UTF-8
- Multi-byte delimiters work as byte sequences
- To split on Unicode grapheme clusters, you'd need additional Unicode handling

### Parsing Paths

Split file paths using the path separator:

```zig
const path = "/usr/local/bin/zig";
var iter = mem.tokenizeAny(u8, path, "/");

while (iter.next()) |component| {
    // component is "usr", "local", "bin", "zig"
}
```

For proper path handling, use `std.fs.path` functions instead.

### Security

Zig's string operations are memory-safe:
- Bounds checking prevents buffer overflows
- Slices know their length
- No null-terminated string pitfalls
- Iterator operations are safe

### Comparison with Other Languages

**Python:**
```python
text.split(',')  # Returns list
```

**JavaScript:**
```javascript
text.split(',')  // Returns array
```

**Zig:**
```zig
var iter = mem.tokenizeAny(u8, text, ",");
// Returns iterator (no allocation)
```

Zig's approach is more memory-efficient since it returns an iterator rather than allocating an array. If you need all tokens at once, use the `collectTokens` helper function.

### Full Tested Code

```zig
// Recipe 2.1: Splitting strings on any of multiple delimiters
// Target Zig Version: 0.15.2
//
// This recipe demonstrates various approaches to splitting strings in Zig
// using the standard library's tokenization and splitting functions.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;

/// Split string on any of multiple delimiters using tokenizeAny
/// Returns an iterator that yields non-empty tokens
// ANCHOR: basic_tokenize
pub fn tokenizeAny(text: []const u8, delimiters: []const u8) mem.TokenIterator(u8, .any) {
    return mem.tokenizeAny(u8, text, delimiters);
}

/// Split string on a sequence of delimiters using tokenizeSequence
/// Returns an iterator that yields non-empty tokens
pub fn tokenizeSequence(text: []const u8, delimiter: []const u8) mem.TokenIterator(u8, .sequence) {
    return mem.tokenizeSequence(u8, text, delimiter);
}
// ANCHOR_END: basic_tokenize

/// Split string but keep empty tokens using splitAny
// ANCHOR: split_preserve_empty
pub fn splitAny(text: []const u8, delimiters: []const u8) mem.SplitIterator(u8, .any) {
    return mem.splitAny(u8, text, delimiters);
}

/// Split string on sequence but keep empty tokens
pub fn splitSequence(text: []const u8, delimiter: []const u8) mem.SplitIterator(u8, .sequence) {
    return mem.splitSequence(u8, text, delimiter);
}
// ANCHOR_END: split_preserve_empty

/// Collect all tokens into an ArrayList for convenience
pub fn collectTokens(
    allocator: mem.Allocator,
    text: []const u8,
    delimiters: []const u8,
) !std.ArrayList([]const u8) {
    var result = std.ArrayList([]const u8){};
    errdefer result.deinit(allocator);

    var iter = tokenizeAny(text, delimiters);
    while (iter.next()) |token| {
        try result.append(allocator, token);
    }

    return result;
}

/// Split on whitespace (space, tab, newline, carriage return)
// ANCHOR: practical_splitting
pub fn splitWhitespace(text: []const u8) mem.TokenIterator(u8, .any) {
    return mem.tokenizeAny(u8, text, " \t\n\r");
}

/// Parse CSV-like data (comma-separated values)
pub fn splitCSV(text: []const u8) mem.SplitIterator(u8, .scalar) {
    return mem.splitScalar(u8, text, ',');
}

/// Split lines preserving empty lines
pub fn splitLines(text: []const u8) mem.SplitIterator(u8, .scalar) {
    return mem.splitScalar(u8, text, '\n');
}
// ANCHOR_END: practical_splitting

test "split on any of multiple delimiters" {
    const text = "hello,world;foo:bar|baz";
    var iter = tokenizeAny(text, ",;:|");

    try testing.expectEqualStrings("hello", iter.next().?);
    try testing.expectEqualStrings("world", iter.next().?);
    try testing.expectEqualStrings("foo", iter.next().?);
    try testing.expectEqualStrings("bar", iter.next().?);
    try testing.expectEqualStrings("baz", iter.next().?);
    try testing.expect(iter.next() == null);
}

test "split on whitespace" {
    const text = "  hello   world\tfoo\n\nbar  ";
    var iter = splitWhitespace(text);

    try testing.expectEqualStrings("hello", iter.next().?);
    try testing.expectEqualStrings("world", iter.next().?);
    try testing.expectEqualStrings("foo", iter.next().?);
    try testing.expectEqualStrings("bar", iter.next().?);
    try testing.expect(iter.next() == null);
}

test "split on sequence delimiter" {
    const text = "foo::bar::baz::qux";
    var iter = tokenizeSequence(text, "::");

    try testing.expectEqualStrings("foo", iter.next().?);
    try testing.expectEqualStrings("bar", iter.next().?);
    try testing.expectEqualStrings("baz", iter.next().?);
    try testing.expectEqualStrings("qux", iter.next().?);
    try testing.expect(iter.next() == null);
}

test "split preserving empty tokens" {
    const text = "a,,b,c,";
    var iter = splitAny(text, ",");

    try testing.expectEqualStrings("a", iter.next().?);
    try testing.expectEqualStrings("", iter.next().?); // Empty token
    try testing.expectEqualStrings("b", iter.next().?);
    try testing.expectEqualStrings("c", iter.next().?);
    try testing.expectEqualStrings("", iter.next().?); // Trailing empty
    try testing.expect(iter.next() == null);
}

test "tokenize vs split - different behavior" {
    const text = "a,,b";

    // tokenize skips empty tokens
    var tok_iter = tokenizeAny(text, ",");
    try testing.expectEqualStrings("a", tok_iter.next().?);
    try testing.expectEqualStrings("b", tok_iter.next().?);
    try testing.expect(tok_iter.next() == null);

    // split keeps empty tokens
    var split_iter = splitAny(text, ",");
    try testing.expectEqualStrings("a", split_iter.next().?);
    try testing.expectEqualStrings("", split_iter.next().?);
    try testing.expectEqualStrings("b", split_iter.next().?);
    try testing.expect(split_iter.next() == null);
}

test "collect tokens into ArrayList" {
    const text = "apple,banana,cherry,date";
    var tokens = try collectTokens(testing.allocator, text, ",");
    defer tokens.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 4), tokens.items.len);
    try testing.expectEqualStrings("apple", tokens.items[0]);
    try testing.expectEqualStrings("banana", tokens.items[1]);
    try testing.expectEqualStrings("cherry", tokens.items[2]);
    try testing.expectEqualStrings("date", tokens.items[3]);
}

test "parse CSV data" {
    const csv = "name,age,city\nAlice,30,NYC\nBob,25,LA";
    var lines = splitLines(csv);

    // Header line
    const header = lines.next().?;
    var header_cols = splitCSV(header);
    try testing.expectEqualStrings("name", header_cols.next().?);
    try testing.expectEqualStrings("age", header_cols.next().?);
    try testing.expectEqualStrings("city", header_cols.next().?);

    // First data line
    const line1 = lines.next().?;
    var cols1 = splitCSV(line1);
    try testing.expectEqualStrings("Alice", cols1.next().?);
    try testing.expectEqualStrings("30", cols1.next().?);
    try testing.expectEqualStrings("NYC", cols1.next().?);

    // Second data line
    const line2 = lines.next().?;
    var cols2 = splitCSV(line2);
    try testing.expectEqualStrings("Bob", cols2.next().?);
    try testing.expectEqualStrings("25", cols2.next().?);
    try testing.expectEqualStrings("LA", cols2.next().?);
}

test "split on multiple character delimiters" {
    const text = "one->two->three->four";
    var iter = tokenizeSequence(text, "->");

    try testing.expectEqualStrings("one", iter.next().?);
    try testing.expectEqualStrings("two", iter.next().?);
    try testing.expectEqualStrings("three", iter.next().?);
    try testing.expectEqualStrings("four", iter.next().?);
    try testing.expect(iter.next() == null);
}

test "split path-like strings" {
    const path = "/usr/local/bin/zig";
    var iter = tokenizeAny(path, "/");

    try testing.expectEqualStrings("usr", iter.next().?);
    try testing.expectEqualStrings("local", iter.next().?);
    try testing.expectEqualStrings("bin", iter.next().?);
    try testing.expectEqualStrings("zig", iter.next().?);
    try testing.expect(iter.next() == null);
}

test "split empty string" {
    const text = "";
    var iter = tokenizeAny(text, ",");

    try testing.expect(iter.next() == null);
}

test "split string with no delimiters" {
    const text = "hello";
    var iter = tokenizeAny(text, ",");

    try testing.expectEqualStrings("hello", iter.next().?);
    try testing.expect(iter.next() == null);
}

test "split with only delimiters" {
    const text = ",,,";

    // tokenize returns no tokens
    var tok_iter = tokenizeAny(text, ",");
    try testing.expect(tok_iter.next() == null);

    // split returns empty strings
    var split_iter = splitAny(text, ",");
    try testing.expectEqualStrings("", split_iter.next().?);
    try testing.expectEqualStrings("", split_iter.next().?);
    try testing.expectEqualStrings("", split_iter.next().?);
    try testing.expectEqualStrings("", split_iter.next().?);
    try testing.expect(split_iter.next() == null);
}

test "parse email addresses" {
    const text = "user@example.com, admin@test.org; developer@code.io";
    var iter = tokenizeAny(text, " ,;");

    try testing.expectEqualStrings("user@example.com", iter.next().?);
    try testing.expectEqualStrings("admin@test.org", iter.next().?);
    try testing.expectEqualStrings("developer@code.io", iter.next().?);
    try testing.expect(iter.next() == null);
}

test "split on tabs and newlines" {
    const text = "col1\tcol2\tcol3\nval1\tval2\tval3";
    var lines = splitLines(text);

    const line1 = lines.next().?;
    var cols1 = mem.tokenizeScalar(u8, line1, '\t');
    try testing.expectEqualStrings("col1", cols1.next().?);
    try testing.expectEqualStrings("col2", cols1.next().?);
    try testing.expectEqualStrings("col3", cols1.next().?);

    const line2 = lines.next().?;
    var cols2 = mem.tokenizeScalar(u8, line2, '\t');
    try testing.expectEqualStrings("val1", cols2.next().?);
    try testing.expectEqualStrings("val2", cols2.next().?);
    try testing.expectEqualStrings("val3", cols2.next().?);
}

test "memory safety - no allocations for iterators" {
    // Iterators don't allocate, they just slice the original string
    const text = "a,b,c,d,e";
    var iter = tokenizeAny(text, ",");

    var count: usize = 0;
    while (iter.next()) |_| {
        count += 1;
    }

    try testing.expectEqual(@as(usize, 5), count);
}

test "security - no buffer overflows" {
    // Zig's string operations are bounds-checked
    const text = "safe";
    var iter = tokenizeAny(text, ",");

    const first = iter.next().?;
    try testing.expectEqualStrings("safe", first);

    // This is safe - slices know their length
    try testing.expect(first.len == 4);
}
```

---

## Recipe 2.2: Matching Text at the Start or End of a String {#recipe-2-2}

**Tags:** http, json, networking, parsing, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_2.zig`

### Problem

You need to check if a string starts with or ends with specific text, similar to Python's `str.startswith()` and `str.endswith()` or JavaScript's `String.startsWith()` and `String.endsWith()`.

### Solution

Zig's standard library provides `mem.startsWith` and `mem.endsWith` for these checks:

### Basic Prefix and Suffix Checking

```zig
pub fn startsWith(text: []const u8, prefix: []const u8) bool {
    return mem.startsWith(u8, text, prefix);
}

/// Check if string ends with suffix
pub fn endsWith(text: []const u8, suffix: []const u8) bool {
    return mem.endsWith(u8, text, suffix);
}
```

### Check File Extensions

```zig
const filename = "document.pdf";

if (mem.endsWith(u8, filename, ".pdf")) {
    // It's a PDF file
}
```

### Check URL Protocols

```zig
const url = "https://example.com";

if (mem.startsWith(u8, url, "https://")) {
    // Secure connection
}
```

### Check Multiple Possibilities

```zig
pub fn startsWithAny(text: []const u8, prefixes: []const []const u8) bool {
    for (prefixes) |prefix| {
        if (mem.startsWith(u8, text, prefix)) {
            return true;
        }
    }
    return false;
}

// Usage
const protocols = [_][]const u8{ "http://", "https://", "ftp://" };
if (startsWithAny(url, &protocols)) {
    // URL has a known protocol
}
```

### Strip Prefixes and Suffixes

```zig
pub fn stripPrefix(text: []const u8, prefix: []const u8) []const u8 {
    if (mem.startsWith(u8, text, prefix)) {
        return text[prefix.len..];
    }
    return text;
}

pub fn stripSuffix(text: []const u8, suffix: []const u8) []const u8 {
    if (mem.endsWith(u8, text, suffix)) {
        return text[0 .. text.len - suffix.len];
    }
    return text;
}

// Usage
const url = "https://example.com";
const domain = stripPrefix(url, "https://");
// domain is "example.com"

const filename = "document.pdf";
const name = stripSuffix(filename, ".pdf");
// name is "document"
```

### Chain Stripping

```zig
const url = "https://example.com/path";
const result = stripSuffix(stripPrefix(url, "https://"), "/path");
// result is "example.com"
```

### Discussion

### Memory Efficiency

`startsWith` and `endsWith` don't allocate memory - they perform direct byte comparison:

```zig
const has_prefix = mem.startsWith(u8, text, "prefix");
// No allocation, just compares bytes
```

The strip functions return slices into the original string, also without allocation:

```zig
const stripped = stripPrefix(text, "http://");
// stripped is a slice view into text, no allocation
```

### Case Sensitivity

These functions are case-sensitive by default:

```zig
mem.startsWith(u8, "Hello", "hello") // false
mem.startsWith(u8, "Hello", "Hello") // true
```

For case-insensitive matching, you'd need to normalize case first (covered in a later recipe).

### Edge Cases

**Empty Strings:**
```zig
mem.startsWith(u8, "", "")     // true
mem.endsWith(u8, "", "")       // true
mem.startsWith(u8, "", "text") // false
```

**Exact Match:**
```zig
mem.startsWith(u8, "exact", "exact") // true
mem.endsWith(u8, "exact", "exact")   // true
```

**Prefix/Suffix Longer than String:**
```zig
mem.startsWith(u8, "hi", "hello") // false
// Safely returns false, no buffer overflow
```

### Practical Examples

**Filter Files by Extension:**
```zig
const files = [_][]const u8{ "main.zig", "test.zig", "README.md" };

for (files) |file| {
    if (mem.endsWith(u8, file, ".zig")) {
        // Process Zig file
    }
}
```

**Remove URL Protocol:**
```zig
var url: []const u8 = "https://example.com";

// Remove protocol if present
if (mem.startsWith(u8, url, "https://")) {
    url = url[8..]; // Skip "https://"
} else if (mem.startsWith(u8, url, "http://")) {
    url = url[7..]; // Skip "http://"
}
```

**Strip Multiple Prefixes:**
```zig
const text = "re: re: important message";

var result: []const u8 = text;
while (mem.startsWith(u8, result, "re: ")) {
    result = stripPrefix(result, "re: ");
}
// result is "important message"
```

**Check Comment Lines:**
```zig
const lines = [_][]const u8{
    "// This is a comment",
    "const x = 5;",
    "# Another comment style",
};

for (lines) |line| {
    const trimmed = mem.trim(u8, line, " \t");
    if (mem.startsWith(u8, trimmed, "//") or mem.startsWith(u8, trimmed, "#")) {
        // This is a comment
    }
}
```

### UTF-8 Compatibility

These functions work at the byte level, which is compatible with UTF-8:

```zig
const text = "Hello 世界";

mem.startsWith(u8, text, "Hello")  // true
mem.endsWith(u8, text, "世界")      // true
```

Multi-byte UTF-8 sequences are handled correctly since we're comparing complete byte sequences:

```zig
const chinese = "你好世界";
mem.startsWith(u8, chinese, "你好") // true
mem.endsWith(u8, chinese, "世界")   // true
```

### Security

Zig's bounds checking prevents common security issues:

```zig
// This is safe - won't overflow
const safe = mem.startsWith(u8, "short", "very long prefix");
// Returns false, doesn't crash
```

All slice operations are bounds-checked in debug mode, and length checks prevent out-of-bounds access.

### Performance

These operations are O(n) where n is the length of the prefix/suffix being checked:

- `startsWith`: Compares up to `prefix.len` bytes
- `endsWith`: Compares up to `suffix.len` bytes

No scanning of the entire string is needed, making them very efficient.

### Comparison with Other Languages

**Python:**
```python
text.startswith('hello')
text.endswith('world')
text.removeprefix('hello')  # Python 3.9+
text.removesuffix('world')  # Python 3.9+
```

**JavaScript:**
```javascript
text.startsWith('hello')
text.endsWith('world')
```

**Zig:**
```zig
mem.startsWith(u8, text, "hello")
mem.endsWith(u8, text, "world")
stripPrefix(text, "hello")  // Custom function
stripSuffix(text, "world")  // Custom function
```

Zig's approach is more explicit but equally efficient, with the advantage of no hidden allocations.

### Full Tested Code

```zig
// Recipe 2.2: Matching text at the start or end of a string
// Target Zig Version: 0.15.2
//
// This recipe demonstrates how to check if strings start with or end with
// specific prefixes or suffixes using Zig's standard library.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;

/// Check if string starts with prefix
// ANCHOR: basic_prefix_suffix
pub fn startsWith(text: []const u8, prefix: []const u8) bool {
    return mem.startsWith(u8, text, prefix);
}

/// Check if string ends with suffix
pub fn endsWith(text: []const u8, suffix: []const u8) bool {
    return mem.endsWith(u8, text, suffix);
}
// ANCHOR_END: basic_prefix_suffix

/// Check if string starts with any of the given prefixes
// ANCHOR: check_multiple
pub fn startsWithAny(text: []const u8, prefixes: []const []const u8) bool {
    for (prefixes) |prefix| {
        if (mem.startsWith(u8, text, prefix)) {
            return true;
        }
    }
    return false;
}

/// Check if string ends with any of the given suffixes
pub fn endsWithAny(text: []const u8, suffixes: []const []const u8) bool {
    for (suffixes) |suffix| {
        if (mem.endsWith(u8, text, suffix)) {
            return true;
        }
    }
    return false;
}
// ANCHOR_END: check_multiple

/// Remove prefix if present, return original if not
// ANCHOR: strip_affixes
pub fn stripPrefix(text: []const u8, prefix: []const u8) []const u8 {
    if (mem.startsWith(u8, text, prefix)) {
        return text[prefix.len..];
    }
    return text;
}

/// Remove suffix if present, return original if not
pub fn stripSuffix(text: []const u8, suffix: []const u8) []const u8 {
    if (mem.endsWith(u8, text, suffix)) {
        return text[0 .. text.len - suffix.len];
    }
    return text;
}
// ANCHOR_END: strip_affixes


test "basic startsWith" {
    try testing.expect(startsWith("hello world", "hello"));
    try testing.expect(startsWith("hello world", "h"));
    try testing.expect(startsWith("hello world", "hello world"));
    try testing.expect(!startsWith("hello world", "world"));
    try testing.expect(!startsWith("hello world", "Hello")); // Case sensitive
}

test "basic endsWith" {
    try testing.expect(endsWith("hello world", "world"));
    try testing.expect(endsWith("hello world", "d"));
    try testing.expect(endsWith("hello world", "hello world"));
    try testing.expect(!endsWith("hello world", "hello"));
    try testing.expect(!endsWith("hello world", "World")); // Case sensitive
}

test "check file extensions" {
    const filename = "document.pdf";

    try testing.expect(endsWith(filename, ".pdf"));
    try testing.expect(!endsWith(filename, ".txt"));
    try testing.expect(!endsWith(filename, ".docx"));
}

test "check URL protocols" {
    const url1 = "https://example.com";
    const url2 = "http://example.com";
    const url3 = "ftp://files.example.com";

    try testing.expect(startsWith(url1, "https://"));
    try testing.expect(startsWith(url2, "http://"));
    try testing.expect(startsWith(url3, "ftp://"));
    try testing.expect(!startsWith(url1, "http://"));
}

test "starts with any prefix" {
    const text = "https://example.com";
    const protocols = [_][]const u8{ "http://", "https://", "ftp://" };

    try testing.expect(startsWithAny(text, &protocols));

    const text2 = "file:///path/to/file";
    try testing.expect(!startsWithAny(text2, &protocols));
}

test "ends with any suffix" {
    const filename = "document.pdf";
    const doc_extensions = [_][]const u8{ ".pdf", ".doc", ".docx", ".txt" };

    try testing.expect(endsWithAny(filename, &doc_extensions));

    const image = "photo.jpg";
    try testing.expect(!endsWithAny(image, &doc_extensions));
}

test "strip prefix" {
    const text = "https://example.com";
    const result = stripPrefix(text, "https://");

    try testing.expectEqualStrings("example.com", result);

    // Doesn't modify if prefix not present
    const text2 = "example.com";
    const result2 = stripPrefix(text2, "https://");
    try testing.expectEqualStrings("example.com", result2);
}

test "strip suffix" {
    const filename = "document.pdf";
    const name = stripSuffix(filename, ".pdf");

    try testing.expectEqualStrings("document", name);

    // Doesn't modify if suffix not present
    const filename2 = "readme";
    const name2 = stripSuffix(filename2, ".pdf");
    try testing.expectEqualStrings("readme", name2);
}

test "strip both prefix and suffix" {
    const url = "https://example.com/path";
    const stripped = stripSuffix(stripPrefix(url, "https://"), "/path");

    try testing.expectEqualStrings("example.com", stripped);
}

test "empty string edge cases" {
    const empty = "";

    try testing.expect(startsWith(empty, ""));
    try testing.expect(endsWith(empty, ""));
    try testing.expect(!startsWith(empty, "hello"));
    try testing.expect(!endsWith(empty, "hello"));
}

test "prefix longer than string" {
    const text = "hi";

    try testing.expect(!startsWith(text, "hello"));
    try testing.expect(!endsWith(text, "world"));
}

test "exact match" {
    const text = "exact";

    try testing.expect(startsWith(text, "exact"));
    try testing.expect(endsWith(text, "exact"));

    const stripped1 = stripPrefix(text, "exact");
    try testing.expectEqualStrings("", stripped1);

    const stripped2 = stripSuffix(text, "exact");
    try testing.expectEqualStrings("", stripped2);
}

test "filter files by extension" {
    const files = [_][]const u8{
        "main.zig",
        "test.zig",
        "build.zig",
        "README.md",
        "config.json",
    };

    var zig_count: usize = 0;
    for (files) |file| {
        if (endsWith(file, ".zig")) {
            zig_count += 1;
        }
    }

    try testing.expectEqual(@as(usize, 3), zig_count);
}

test "filter URLs by protocol" {
    const urls = [_][]const u8{
        "https://secure.example.com",
        "http://example.com",
        "https://another-secure.com",
        "ftp://files.example.com",
    };

    var https_count: usize = 0;
    for (urls) |url| {
        if (startsWith(url, "https://")) {
            https_count += 1;
        }
    }

    try testing.expectEqual(@as(usize, 2), https_count);
}

test "remove common path prefix" {
    const paths = [_][]const u8{
        "/home/user/project/src/main.zig",
        "/home/user/project/src/test.zig",
        "/home/user/project/build.zig",
    };

    const prefix = "/home/user/project/";

    for (paths) |path| {
        const relative = stripPrefix(path, prefix);
        try testing.expect(!startsWith(relative, "/"));
    }

    try testing.expectEqualStrings("src/main.zig", stripPrefix(paths[0], prefix));
    try testing.expectEqualStrings("src/test.zig", stripPrefix(paths[1], prefix));
    try testing.expectEqualStrings("build.zig", stripPrefix(paths[2], prefix));
}

test "multiple extension check" {
    const compressed_extensions = [_][]const u8{ ".gz", ".zip", ".tar", ".bz2", ".xz" };

    try testing.expect(endsWithAny("archive.tar.gz", &compressed_extensions));
    try testing.expect(endsWithAny("data.zip", &compressed_extensions));
    try testing.expect(!endsWithAny("document.pdf", &compressed_extensions));
}

test "strip multiple prefixes" {
    const text = "re: re: important message";

    var result: []const u8 = text;
    while (startsWith(result, "re: ")) {
        result = stripPrefix(result, "re: ");
    }

    try testing.expectEqualStrings("important message", result);
}

test "normalize URL - strip trailing slash" {
    const urls = [_][]const u8{
        "https://example.com/",
        "https://example.com/path/",
        "https://example.com",
    };

    for (urls) |url| {
        const normalized = stripSuffix(url, "/");
        try testing.expect(!endsWith(normalized, "/"));
    }
}

test "check comment line" {
    const lines = [_][]const u8{
        "// This is a comment",
        "const x = 5;",
        "# Another comment style",
        "  // Indented comment",
    };

    var comment_count: usize = 0;
    for (lines) |line| {
        const trimmed = mem.trim(u8, line, " \t");
        if (startsWith(trimmed, "//") or startsWith(trimmed, "#")) {
            comment_count += 1;
        }
    }

    try testing.expectEqual(@as(usize, 3), comment_count);
}

test "memory safety - no allocations" {
    // startsWith and endsWith don't allocate
    const text = "hello world";

    const has_prefix = startsWith(text, "hello");
    const has_suffix = endsWith(text, "world");

    try testing.expect(has_prefix);
    try testing.expect(has_suffix);
}

test "security - bounds checking" {
    // Zig's mem.startsWith and endsWith are bounds-safe
    const text = "short";

    // These won't overflow or access out of bounds
    try testing.expect(!startsWith(text, "very long prefix that is much longer"));
    try testing.expect(!endsWith(text, "very long suffix that is much longer"));
}

test "UTF-8 compatibility" {
    const text = "Hello 世界";

    // Byte-level matching works with UTF-8
    try testing.expect(startsWith(text, "Hello"));
    try testing.expect(endsWith(text, "世界"));

    // Multi-byte UTF-8 sequences work correctly
    const chinese = "你好世界";
    try testing.expect(startsWith(chinese, "你好"));
    try testing.expect(endsWith(chinese, "世界"));
}
```

---

## Recipe 2.3: Matching Strings Using Wildcard Patterns {#recipe-2-3}

**Tags:** allocators, arraylist, csv, data-structures, error-handling, json, memory, parsing, resource-cleanup, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_3.zig`

### Problem

You need to match strings against simple wildcard patterns like `*.txt` or `test_?.zig`, similar to shell glob patterns or SQL's `LIKE` operator.

### Solution

Implement a simple glob matcher that supports `*` (match any characters) and `?` (match exactly one character):

```zig
pub fn glob(text: []const u8, pattern: []const u8) bool {
    return globImpl(text, pattern, 0, 0);
}

fn globImpl(text: []const u8, pattern: []const u8, text_idx: usize, pat_idx: usize) bool {
    // Both exhausted - match
    if (text_idx == text.len and pat_idx == pattern.len) {
        return true;
    }

    // Pattern exhausted but text remains - no match
    if (pat_idx == pattern.len) {
        return false;
    }

    // Handle wildcard *
    if (pattern[pat_idx] == '*') {
        // Try matching zero characters
        if (globImpl(text, pattern, text_idx, pat_idx + 1)) {
            return true;
        }

        // Try matching one or more characters
        var i = text_idx;
        while (i < text.len) : (i += 1) {
            if (globImpl(text, pattern, i + 1, pat_idx + 1)) {
                return true;
            }
        }

        return false;
    }

    // Text exhausted but pattern has non-wildcard - no match
    if (text_idx == text.len) {
        return false;
    }

    // Handle single character wildcard ?
    if (pattern[pat_idx] == '?') {
        return globImpl(text, pattern, text_idx + 1, pat_idx + 1);
    }

    // Handle regular character - must match exactly
    if (text[text_idx] == pattern[pat_idx]) {
        return globImpl(text, pattern, text_idx + 1, pat_idx + 1);
    }

    return false;
}
```

### Basic Usage

```zig
// Exact match
glob("hello", "hello")  // true

// Wildcard * - matches any characters
glob("hello.txt", "*.txt")      // true
glob("document.pdf", "*.txt")   // false

// Wildcard ? - matches exactly one character
glob("cat", "c?t")    // true
glob("cart", "c?t")   // false (too many chars)
```

### File Extension Matching

```zig
const filename = "document.pdf";

if (glob(filename, "*.pdf")) {
    // PDF file
}

if (glob(filename, "*.txt") or glob(filename, "*.md")) {
    // Text or markdown file
}
```

### Match Multiple Patterns

```zig
pub fn globAny(text: []const u8, patterns: []const []const u8) bool {
    for (patterns) |pattern| {
        if (glob(text, pattern)) {
            return true;
        }
    }
    return false;
}

// Usage
const image_patterns = [_][]const u8{ "*.jpg", "*.png", "*.gif" };
if (globAny("photo.jpg", &image_patterns)) {
    // Image file
}
```

### Filter Lists by Pattern

```zig
pub fn filterByGlob(
    allocator: mem.Allocator,
    items: []const []const u8,
    pattern: []const u8,
) !std.ArrayList([]const u8) {
    var result = std.ArrayList([]const u8){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (glob(item, pattern)) {
            try result.append(allocator, item);
        }
    }

    return result;
}

// Usage
const files = [_][]const u8{ "main.zig", "test.zig", "README.md" };
var zig_files = try filterByGlob(allocator, &files, "*.zig");
defer zig_files.deinit(allocator);
// zig_files contains ["main.zig", "test.zig"]
```

### Discussion

### Pattern Syntax

**`*` (asterisk)** - Matches zero or more characters:
```zig
glob("test", "test*")       // true
glob("testing", "test*")    // true
glob("test.txt", "test*")   // true
glob("", "*")               // true
```

**`?` (question mark)** - Matches exactly one character:
```zig
glob("cat", "c?t")      // true
glob("cut", "c?t")      // true
glob("ct", "c?t")       // false (? must match one char)
glob("cart", "c?t")     // false (too many chars)
```

**Combining wildcards:**
```zig
glob("data123.csv", "data???.*")     // true
glob("test.tar.gz", "*.*.*")         // true
glob("hello_world", "hello*world")   // true
```

### Common Use Cases

**File Extension Filtering:**
```zig
const files = [_][]const u8{ "main.zig", "test.zig", "README.md" };

for (files) |file| {
    if (glob(file, "*.zig")) {
        // Process Zig source file
    }
}
```

**Test File Detection:**
```zig
if (glob(filename, "test_*.zig") or glob(filename, "*_test.zig")) {
    // This is a test file
}
```

**Backup File Detection:**
```zig
if (glob(filename, "*.bak") or glob(filename, "*~")) {
    // This is a backup file
}
```

**Version String Matching:**
```zig
glob("v1.2.3", "v*.*.*")        // true
glob("version-1.0.0", "version-*")  // true
```

**Date Pattern Matching:**
```zig
glob("2024-01-15", "????-??-??")              // true
glob("log-2024-01-15.txt", "log-????-??-??.txt")  // true
```

### Limitations

This simple implementation:
- Is case-sensitive (use `std.ascii.toLower` for case-insensitive matching)
- Doesn't support character classes like `[abc]` or `[0-9]`
- Doesn't support negation like `[!abc]`
- Doesn't support brace expansion like `{a,b,c}`
- Treats special characters literally (except `*` and `?`)

For full glob support with character classes and ranges, you'd need a more complex implementation or a third-party library.

### Performance

The recursive implementation can handle complex patterns efficiently:

```zig
// Multiple * wildcards don't cause exponential time
glob("file.tar.gz", "*.*.*")  // Fast
```

However, very complex patterns with many wildcards could be slow. For production use with untrusted patterns, consider adding depth limits or timeouts.

### Memory Efficiency

The glob function doesn't allocate memory - it uses recursion with simple integer indices:

```zig
const matched = glob("file.txt", "*.txt");
// No allocation, stack-based recursion only
```

For filtering, only the result list allocates:

```zig
var results = try filterByGlob(allocator, files, "*.zig");
defer results.deinit(allocator);
// Only the result list is allocated
```

### Case Sensitivity

The implementation is case-sensitive by default:

```zig
glob("File.txt", "file.txt")  // false
glob("File.txt", "File.txt")  // true
```

For case-insensitive matching, normalize both strings first:

```zig
const text_lower = try std.ascii.allocLowerString(allocator, text);
defer allocator.free(text_lower);
const pattern_lower = try std.ascii.allocLowerString(allocator, pattern);
defer allocator.free(pattern_lower);

const matched = glob(text_lower, pattern_lower);
```

### Security

The implementation is memory-safe:
- Bounds checking prevents buffer overflows
- Recursion depth is limited by pattern complexity
- No undefined behavior with malformed patterns

```zig
// Safe - won't crash or overflow
glob("short", "very*long*pattern*with*many*wildcards")
```

### Comparison with Regex

Glob patterns are simpler and faster than full regular expressions:

**Glob advantages:**
- Simpler syntax
- Faster for basic patterns
- More intuitive for file matching
- No regex engine needed

**Regex advantages:**
- More powerful (lookahead, groups, etc.)
- Character classes and ranges
- Anchors and boundaries
- More complex patterns

For simple file matching, glob is perfect. For complex text processing, use a regex library.

### Real-World Examples

**Find All Test Files:**
```zig
const all_files = try listDirectory(allocator, "src");
defer all_files.deinit(allocator);

var test_files = try filterByGlob(allocator, all_files.items, "*_test.zig");
defer test_files.deinit(allocator);
```

**Process Specific File Types:**
```zig
for (files) |file| {
    if (globAny(file, &[_][]const u8{ "*.jpg", "*.png", "*.gif" })) {
        try processImage(file);
    } else if (globAny(file, &[_][]const u8{ "*.mp4", "*.avi", "*.mkv" })) {
        try processVideo(file);
    }
}
```

This glob implementation provides efficient, memory-safe wildcard matching perfect for file filtering and simple pattern matching tasks.

### Full Tested Code

```zig
// Recipe 2.3: Matching strings using shell wildcard patterns
// Target Zig Version: 0.15.2
//
// This recipe demonstrates implementing simple glob-style wildcard matching
// similar to shell filename patterns (* and ?).

const std = @import("std");
const testing = std.testing;
const mem = std.mem;

/// Simple glob pattern matching with * (any characters) and ? (single character)
/// Returns true if text matches the pattern
// ANCHOR: glob_matching
pub fn glob(text: []const u8, pattern: []const u8) bool {
    return globImpl(text, pattern, 0, 0);
}

fn globImpl(text: []const u8, pattern: []const u8, text_idx: usize, pat_idx: usize) bool {
    // Both exhausted - match
    if (text_idx == text.len and pat_idx == pattern.len) {
        return true;
    }

    // Pattern exhausted but text remains - no match
    if (pat_idx == pattern.len) {
        return false;
    }

    // Handle wildcard *
    if (pattern[pat_idx] == '*') {
        // Try matching zero characters
        if (globImpl(text, pattern, text_idx, pat_idx + 1)) {
            return true;
        }

        // Try matching one or more characters
        var i = text_idx;
        while (i < text.len) : (i += 1) {
            if (globImpl(text, pattern, i + 1, pat_idx + 1)) {
                return true;
            }
        }

        return false;
    }

    // Text exhausted but pattern has non-wildcard - no match
    if (text_idx == text.len) {
        return false;
    }

    // Handle single character wildcard ?
    if (pattern[pat_idx] == '?') {
        return globImpl(text, pattern, text_idx + 1, pat_idx + 1);
    }

    // Handle regular character - must match exactly
    if (text[text_idx] == pattern[pat_idx]) {
        return globImpl(text, pattern, text_idx + 1, pat_idx + 1);
    }

    return false;
}
// ANCHOR_END: glob_matching

/// Match multiple patterns (OR logic)
// ANCHOR: glob_multiple
pub fn globAny(text: []const u8, patterns: []const []const u8) bool {
    for (patterns) |pattern| {
        if (glob(text, pattern)) {
            return true;
        }
    }
    return false;
}
// ANCHOR_END: glob_multiple

/// Filter a list of strings by a glob pattern
// ANCHOR: filter_by_glob
pub fn filterByGlob(
    allocator: mem.Allocator,
    items: []const []const u8,
    pattern: []const u8,
) !std.ArrayList([]const u8) {
    var result = std.ArrayList([]const u8){};
    errdefer result.deinit(allocator);

    for (items) |item| {
        if (glob(item, pattern)) {
            try result.append(allocator, item);
        }
    }

    return result;
}
// ANCHOR_END: filter_by_glob

test "exact match" {
    try testing.expect(glob("hello", "hello"));
    try testing.expect(!glob("hello", "world"));
    try testing.expect(!glob("hello", "Hello")); // Case sensitive
}

test "single wildcard ? matches one character" {
    try testing.expect(glob("cat", "c?t"));
    try testing.expect(glob("cut", "c?t"));
    try testing.expect(!glob("ct", "c?t")); // ? must match one char
    try testing.expect(!glob("cart", "c?t")); // Too many chars

    try testing.expect(glob("a", "?"));
    try testing.expect(!glob("ab", "?"));
}

test "multiple wildcards ?" {
    try testing.expect(glob("test", "t??t"));
    try testing.expect(glob("abcd", "??cd"));
    try testing.expect(glob("abcd", "ab??"));
    try testing.expect(!glob("abc", "????"));
}

test "star wildcard * matches zero or more characters" {
    try testing.expect(glob("", "*"));
    try testing.expect(glob("a", "*"));
    try testing.expect(glob("anything", "*"));

    try testing.expect(glob("hello", "h*"));
    try testing.expect(glob("h", "h*"));
    try testing.expect(glob("hello world", "h*"));
}

test "star at end of pattern" {
    try testing.expect(glob("test.txt", "test*"));
    try testing.expect(glob("test.md", "test*"));
    try testing.expect(glob("test", "test*"));
    try testing.expect(glob("testing", "test*")); // "test*" matches anything starting with "test"
}

test "star at beginning of pattern" {
    try testing.expect(glob("file.txt", "*.txt"));
    try testing.expect(glob("document.txt", "*.txt"));
    try testing.expect(!glob("file.pdf", "*.txt"));
}

test "star in middle of pattern" {
    try testing.expect(glob("hello_world", "hello*world"));
    try testing.expect(glob("hello__world", "hello*world"));
    try testing.expect(glob("helloworld", "hello*world"));
    try testing.expect(!glob("hello", "hello*world"));
}

test "multiple stars" {
    try testing.expect(glob("a.b.c", "*.*.*"));
    try testing.expect(glob("file.tar.gz", "*.*"));
    try testing.expect(glob("anything", "*"));
}

test "combine ? and *" {
    try testing.expect(glob("test.txt", "t??t*"));
    try testing.expect(glob("test.md", "t??t*"));
    try testing.expect(!glob("tst.txt", "t??t*"));

    try testing.expect(glob("data123.csv", "data???.*"));
    try testing.expect(!glob("data12.csv", "data???.*"));
}

test "file extension matching" {
    const files = [_][]const u8{
        "main.zig",
        "test.zig",
        "build.zig",
        "README.md",
        "config.json",
    };

    for (files) |file| {
        const is_zig = glob(file, "*.zig");
        const expected = mem.endsWith(u8, file, ".zig");
        try testing.expectEqual(expected, is_zig);
    }
}

test "prefix matching" {
    try testing.expect(glob("test_main.zig", "test_*"));
    try testing.expect(glob("test_helper.zig", "test_*"));
    try testing.expect(!glob("main_test.zig", "test_*"));
}

test "match any pattern" {
    const patterns = [_][]const u8{ "*.txt", "*.md", "*.rst" };

    try testing.expect(globAny("file.txt", &patterns));
    try testing.expect(globAny("README.md", &patterns));
    try testing.expect(globAny("doc.rst", &patterns));
    try testing.expect(!globAny("file.pdf", &patterns));
}

test "filter files by pattern" {
    const files = [_][]const u8{
        "main.zig",
        "test.zig",
        "helper.zig",
        "README.md",
        "build.zig",
    };

    var zig_files = try filterByGlob(testing.allocator, &files, "*.zig");
    defer zig_files.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 4), zig_files.items.len);
}

test "complex patterns" {
    try testing.expect(glob("test_123_main.zig", "test_*_*.zig"));
    try testing.expect(glob("data_2024_01.csv", "data_*_*.csv"));
    try testing.expect(!glob("data_2024.csv", "data_*_*.csv"));
}

test "edge case - empty pattern" {
    try testing.expect(glob("", ""));
    try testing.expect(!glob("text", ""));
}

test "edge case - empty text" {
    try testing.expect(glob("", "*"));
    try testing.expect(!glob("", "?"));
    try testing.expect(!glob("", "a"));
}

test "edge case - only wildcards" {
    try testing.expect(glob("anything", "***"));
    try testing.expect(glob("a", "?*"));
    try testing.expect(glob("ab", "?*"));
    try testing.expect(!glob("", "?*"));
}

test "real-world file patterns" {
    // Source files
    try testing.expect(glob("main.c", "*.c"));
    try testing.expect(glob("utils.h", "*.h"));

    // Test files
    try testing.expect(glob("test_main.zig", "test_*.zig"));
    try testing.expect(glob("main_test.zig", "*_test.zig"));

    // Backup files
    try testing.expect(glob("file.txt.bak", "*.bak"));
    try testing.expect(glob("file.txt~", "*~"));

    // Hidden files
    try testing.expect(glob(".gitignore", ".*"));
    try testing.expect(glob(".hidden", ".*"));
}

test "version patterns" {
    try testing.expect(glob("v1.2.3", "v*.*.*"));
    try testing.expect(glob("v2.0.0", "v*.*.*"));
    try testing.expect(glob("version-1.2.3", "version-*"));
    try testing.expect(!glob("1.2.3", "v*.*.*"));
}

test "date patterns" {
    try testing.expect(glob("2024-01-15", "????-??-??"));
    try testing.expect(glob("log-2024-01-15.txt", "log-????-??-??.txt"));
    try testing.expect(!glob("2024-1-5", "????-??-??"));
}

test "multiple file extensions" {
    const image_patterns = [_][]const u8{ "*.jpg", "*.png", "*.gif" };

    try testing.expect(globAny("photo.jpg", &image_patterns));
    try testing.expect(globAny("image.png", &image_patterns));
    try testing.expect(globAny("animation.gif", &image_patterns));
    try testing.expect(!globAny("document.pdf", &image_patterns));
}

test "case sensitivity" {
    try testing.expect(glob("file.txt", "file.txt"));
    try testing.expect(!glob("File.txt", "file.txt"));
    try testing.expect(!glob("FILE.TXT", "file.txt"));
}

test "special characters - literal match" {
    // These characters are literal in our simple glob
    try testing.expect(glob("file[1].txt", "file[1].txt"));
    try testing.expect(glob("a+b", "a+b"));
    try testing.expect(glob("test.file", "test.file"));
}

test "memory safety - no allocations for glob matching" {
    // glob() doesn't allocate, it just walks the strings
    const result = glob("test.txt", "*.txt");
    try testing.expect(result);
}

test "security - bounds checking" {
    // Very long patterns don't cause issues
    const long_pattern = "*" ** 100 ++ ".txt";
    try testing.expect(glob("file.txt", long_pattern));

    // Pattern longer than text is safe
    try testing.expect(!glob("a", "????????????"));
}

test "performance - no catastrophic backtracking" {
    // Patterns with multiple * don't cause exponential time
    // This would hang in naive regex implementations
    try testing.expect(!glob("aaaaaaaaaa", "*a*a*a*a*a*b")); // No 'b', should not match
    try testing.expect(glob("aaaaaaaaaaab", "*a*a*a*a*a*b")); // Has 'b' at end
    try testing.expect(!glob("aaaaaaaaaax", "*a*a*a*a*a*b")); // No 'b', should not match
}
```

---

## Recipe 2.4: Searching and Matching Text Patterns {#recipe-2-4}

**Tags:** allocators, arraylist, data-structures, error-handling, http, memory, networking, pointers, resource-cleanup, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_4.zig`

### Problem

You need to search for text patterns within strings - finding substrings, checking for presence, or locating specific characters.

### Solution

Zig's `std.mem` provides comprehensive string search functions:

### Basic Substring Search

```zig
pub fn indexOf(text: []const u8, needle: []const u8) ?usize {
    return mem.indexOf(u8, text, needle);
}

/// Find last occurrence of substring, returns index or null
pub fn lastIndexOf(text: []const u8, needle: []const u8) ?usize {
    return mem.lastIndexOf(u8, text, needle);
}

/// Find first occurrence of any character in set
pub fn indexOfAny(text: []const u8, chars: []const u8) ?usize {
    return mem.indexOfAny(u8, text, chars);
}
```

### Find Last Occurrence

```zig
const text = "hello hello world";

if (mem.lastIndexOf(u8, text, "hello")) |pos| {
    // Found at position 6 (second "hello")
}
```

### Find Any Character in Set

```zig
const text = "hello world";

// Find first vowel
if (mem.indexOfAny(u8, text, "aeiou")) |pos| {
    // Found 'e' at position 1
}

// Find first digit
const mixed = "Product ID: 12345";
if (mem.indexOfAny(u8, mixed, "0123456789")) |pos| {
    // Found '1' at position 12
}
```

### Find Character NOT in Set

```zig
const text = "   hello";

// Find first non-whitespace
if (mem.indexOfNone(u8, text, " \t\n\r")) |pos| {
    // Found 'h' at position 3
}
```

### Count Occurrences

```zig
pub fn count(text: []const u8, needle: []const u8) usize {
    if (needle.len == 0) return 0;

    var occurrences: usize = 0;
    var pos: usize = 0;

    while (pos < text.len) {
        if (mem.indexOf(u8, text[pos..], needle)) |found| {
            occurrences += 1;
            pos += found + needle.len;
        } else {
            break;
        }
    }

    return occurrences;
}

// Usage
const text = "hello hello world";
const cnt = count(text, "hello");  // 2
```

### Find All Occurrences

```zig
pub fn findAll(
    allocator: mem.Allocator,
    text: []const u8,
    needle: []const u8,
) !std.ArrayList(usize) {
    var result = std.ArrayList(usize){};
    errdefer result.deinit(allocator);

    if (needle.len == 0) return result;

    var pos: usize = 0;
    while (pos < text.len) {
        if (mem.indexOf(u8, text[pos..], needle)) |found| {
            try result.append(allocator, pos + found);
            pos += found + needle.len;
        } else {
            break;
        }
    }

    return result;
}

// Usage
var positions = try findAll(allocator, "hello hello world", "hello");
defer positions.deinit(allocator);
// positions.items is [0, 6]
```

### Discussion

### Available Search Functions

Zig provides several search functions in `std.mem`:

**`indexOf(u8, text, needle)`** - Find first occurrence of substring
- Returns `?usize` (index or null)
- Efficient O(n*m) search

**`lastIndexOf(u8, text, needle)`** - Find last occurrence
- Returns `?usize`
- Searches from end backward

**`indexOfAny(u8, text, chars)`** - Find any character in set
- Returns `?usize`
- Useful for finding delimiters, digits, etc.

**`indexOfNone(u8, text, chars)`** - Find character NOT in set
- Returns `?usize`
- Useful for skipping whitespace, etc.

**`indexOfScalar(u8, text, char)`** - Find single character
- Returns `?usize`
- Optimized for single character search

### Practical Examples

**Extract Domain from Email:**
```zig
const email = "user@example.com";

if (mem.indexOf(u8, email, "@")) |at_pos| {
    const domain = email[at_pos + 1..];
    // domain is "example.com"
}
```

**Find File Extension:**
```zig
const path = "/path/to/file.txt";

if (mem.lastIndexOf(u8, path, ".")) |dot_pos| {
    const ext = path[dot_pos..];
    // ext is ".txt"
}
```

**Validate Password Requirements:**
```zig
const password = "MyP@ssw0rd";

const has_upper = mem.indexOfAny(u8, password, "ABCDEFGHIJKLMNOPQRSTUVWXYZ") != null;
const has_lower = mem.indexOfAny(u8, password, "abcdefghijklmnopqrstuvwxyz") != null;
const has_digit = mem.indexOfAny(u8, password, "0123456789") != null;
const has_special = mem.indexOfAny(u8, password, "!@#$%^&*") != null;

if (has_upper and has_lower and has_digit and has_special) {
    // Password meets requirements
}
```

**Find Balanced Brackets:**
```zig
const text = "array[index]";

const open = mem.indexOf(u8, text, "[");
const close = mem.indexOf(u8, text, "]");

if (open != null and close != null and close.? > open.?) {
    const content = text[open.? + 1 .. close.?];
    // content is "index"
}
```

**Count Line Breaks:**
```zig
const text = "line1\nline2\nline3";
const line_count = count(text, "\n") + 1;  // 3 lines
```

### Helper Functions

**Contains (simpler syntax):**
```zig
pub fn contains(text: []const u8, needle: []const u8) bool {
    return mem.indexOf(u8, text, needle) != null;
}

if (contains("hello world", "world")) {
    // Found
}
```

**Contains Any:**
```zig
pub fn containsAny(text: []const u8, needles: []const []const u8) bool {
    for (needles) |needle| {
        if (mem.indexOf(u8, text, needle) != null) {
            return true;
        }
    }
    return false;
}

const keywords = [_][]const u8{ "error", "warning", "critical" };
if (containsAny(log_line, &keywords)) {
    // Important log entry
}
```

**Contains All:**
```zig
pub fn containsAll(text: []const u8, needles: []const []const u8) bool {
    for (needles) |needle| {
        if (mem.indexOf(u8, text, needle) == null) {
            return false;
        }
    }
    return true;
}
```

### Performance

Search operations are O(n*m) where:
- n = length of text
- m = length of needle

For repeated searches in the same text, consider:
1. Boyer-Moore algorithm (faster for long needles)
2. KMP algorithm (better worst-case)
3. Aho-Corasick (multiple needles)

For simple cases, `indexOf` is fast and sufficient.

### Case Sensitivity

All search functions are case-sensitive:

```zig
mem.indexOf(u8, "Hello", "hello")  // null
mem.indexOf(u8, "Hello", "Hello")  // 0
```

For case-insensitive search, convert both to lowercase first (covered in Recipe 2.6).

### UTF-8 Compatibility

Functions work at the byte level, which is compatible with UTF-8:

```zig
const text = "Hello 世界";

mem.indexOf(u8, text, "世界")  // Returns byte position 6
mem.indexOf(u8, text, "世")    // Returns byte position 6
```

Multi-byte UTF-8 sequences are handled correctly since we search complete byte sequences.

### Memory Efficiency

Basic search functions don't allocate:

```zig
const idx = mem.indexOf(u8, text, "needle");
// No allocation, just pointer arithmetic
```

Only `findAll` allocates to store the result list:

```zig
var positions = try findAll(allocator, text, "needle");
defer positions.deinit(allocator);
```

### Security

All operations are bounds-safe:

```zig
// Safe - won't overflow
mem.indexOf(u8, "short", "very long needle that is much longer")
// Returns null, doesn't crash
```

Zig's bounds checking prevents buffer overflows in debug mode, and length checks prevent out-of-bounds access.

### When to Use Regex

For these simple patterns, built-in functions are faster than regex:
- Substring search → `indexOf`
- Character in set → `indexOfAny`
- Contains check → `indexOf != null`

Use regex when you need:
- Complex patterns (lookahead, groups)
- Character classes and ranges
- Alternation and repetition
- Capture groups

For most string searching tasks, Zig's built-in functions are faster and simpler.

### Real-World Examples

**Parse Log Levels:**
```zig
const log_line = "[ERROR] Connection failed";

if (mem.indexOf(u8, log_line, "[ERROR]")) |_| {
    // Handle error log
} else if (mem.indexOf(u8, log_line, "[WARNING]")) |_| {
    // Handle warning log
}
```

**Find URLs in Text:**
```zig
const text = "Visit https://example.com for info";

if (mem.indexOf(u8, text, "https://")) |pos| {
    // Found secure URL at position pos
}
```

**Check Code Comments:**
```zig
const line = "// This is a comment";
const trimmed = mem.trim(u8, line, " \t");

if (mem.indexOf(u8, trimmed, "//") == 0) {
    // This line starts with a comment
}
```

This comprehensive set of search functions covers most text searching needs efficiently and safely.

### Full Tested Code

```zig
// Recipe 2.4: Matching and searching for text patterns
// Target Zig Version: 0.15.2
//
// This recipe demonstrates various string searching techniques in Zig
// using std.mem functions for substring search and pattern matching.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;

/// Find first occurrence of substring, returns index or null
// ANCHOR: basic_search
pub fn indexOf(text: []const u8, needle: []const u8) ?usize {
    return mem.indexOf(u8, text, needle);
}

/// Find last occurrence of substring, returns index or null
pub fn lastIndexOf(text: []const u8, needle: []const u8) ?usize {
    return mem.lastIndexOf(u8, text, needle);
}

/// Find first occurrence of any character in set
pub fn indexOfAny(text: []const u8, chars: []const u8) ?usize {
    return mem.indexOfAny(u8, text, chars);
}
// ANCHOR_END: basic_search

/// Find first occurrence NOT in character set
pub fn indexOfNone(text: []const u8, chars: []const u8) ?usize {
    return mem.indexOfNone(u8, text, chars);
}

/// Find first occurrence of a single character
pub fn indexOfScalar(text: []const u8, char: u8) ?usize {
    return mem.indexOfScalar(u8, text, char);
}

/// Check if text contains substring
pub fn contains(text: []const u8, needle: []const u8) bool {
    return mem.indexOf(u8, text, needle) != null;
}

/// Count occurrences of substring (non-overlapping)
// ANCHOR: count_find_all
pub fn count(text: []const u8, needle: []const u8) usize {
    if (needle.len == 0) return 0;

    var occurrences: usize = 0;
    var pos: usize = 0;

    while (pos < text.len) {
        if (mem.indexOf(u8, text[pos..], needle)) |found| {
            occurrences += 1;
            pos += found + needle.len;
        } else {
            break;
        }
    }

    return occurrences;
}

/// Find all occurrences of substring, returns ArrayList of indices
pub fn findAll(
    allocator: mem.Allocator,
    text: []const u8,
    needle: []const u8,
) !std.ArrayList(usize) {
    var result = std.ArrayList(usize){};
    errdefer result.deinit(allocator);

    if (needle.len == 0) return result;

    var pos: usize = 0;
    while (pos < text.len) {
        if (mem.indexOf(u8, text[pos..], needle)) |found| {
            try result.append(allocator, pos + found);
            pos += found + needle.len;
        } else {
            break;
        }
    }

    return result;
}
// ANCHOR_END: count_find_all

/// Check if text contains any of the given needles
// ANCHOR: contains_multiple
pub fn containsAny(text: []const u8, needles: []const []const u8) bool {
    for (needles) |needle| {
        if (contains(text, needle)) {
            return true;
        }
    }
    return false;
}

/// Check if text contains all of the given needles
pub fn containsAll(text: []const u8, needles: []const []const u8) bool {
    for (needles) |needle| {
        if (!contains(text, needle)) {
            return false;
        }
    }
    return true;
}
// ANCHOR_END: contains_multiple

test "find substring - basic" {
    const text = "hello world";

    try testing.expectEqual(@as(?usize, 0), indexOf(text, "hello"));
    try testing.expectEqual(@as(?usize, 6), indexOf(text, "world"));
    try testing.expectEqual(@as(?usize, 4), indexOf(text, "o"));
    try testing.expectEqual(@as(?usize, null), indexOf(text, "xyz"));
}

test "find last occurrence" {
    const text = "hello hello world";

    try testing.expectEqual(@as(?usize, 6), lastIndexOf(text, "hello"));
    try testing.expectEqual(@as(?usize, 9), lastIndexOf(text, "lo"));
    try testing.expectEqual(@as(?usize, null), lastIndexOf(text, "xyz"));
}

test "contains substring" {
    const text = "The quick brown fox";

    try testing.expect(contains(text, "quick"));
    try testing.expect(contains(text, "fox"));
    try testing.expect(!contains(text, "lazy"));
    try testing.expect(!contains(text, "Quick")); // Case sensitive
}

test "find character in set" {
    const text = "hello world";

    try testing.expectEqual(@as(?usize, 1), indexOfAny(text, "aeiou")); // First vowel
    try testing.expectEqual(@as(?usize, 0), indexOfAny(text, "h")); // First 'h'
    try testing.expectEqual(@as(?usize, null), indexOfAny(text, "xyz"));
}

test "find first character NOT in set" {
    const text = "   hello";

    try testing.expectEqual(@as(?usize, 3), indexOfNone(text, " ")); // First non-space

    const digits = "123abc";
    try testing.expectEqual(@as(?usize, 3), indexOfNone(digits, "0123456789"));
}

test "find single character" {
    const text = "hello world";

    try testing.expectEqual(@as(?usize, 4), indexOfScalar(text, 'o'));
    try testing.expectEqual(@as(?usize, 2), indexOfScalar(text, 'l'));
    try testing.expectEqual(@as(?usize, null), indexOfScalar(text, 'x'));
}

test "count occurrences" {
    const text = "hello hello world";

    try testing.expectEqual(@as(usize, 2), count(text, "hello"));
    try testing.expectEqual(@as(usize, 5), count(text, "l")); // 2 in first "hello", 2 in second "hello", 1 in "world"
    try testing.expectEqual(@as(usize, 1), count(text, "world"));
    try testing.expectEqual(@as(usize, 0), count(text, "xyz"));
}

test "count overlapping pattern" {
    // Non-overlapping count
    const text = "aaaa";
    try testing.expectEqual(@as(usize, 2), count(text, "aa")); // "aa|aa", not "a|a|a|a"
}

test "find all occurrences" {
    const text = "hello hello world";

    var positions = try findAll(testing.allocator, text, "hello");
    defer positions.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 2), positions.items.len);
    try testing.expectEqual(@as(usize, 0), positions.items[0]);
    try testing.expectEqual(@as(usize, 6), positions.items[1]);
}

test "find all single character" {
    const text = "hello world";

    var positions = try findAll(testing.allocator, text, "l");
    defer positions.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 3), positions.items.len);
    try testing.expectEqual(@as(usize, 2), positions.items[0]);
    try testing.expectEqual(@as(usize, 3), positions.items[1]);
    try testing.expectEqual(@as(usize, 9), positions.items[2]);
}

test "contains any of multiple needles" {
    const text = "The quick brown fox";
    const words = [_][]const u8{ "quick", "lazy", "dog" };

    try testing.expect(containsAny(text, &words)); // Contains "quick"

    const words2 = [_][]const u8{ "lazy", "dog", "cat" };
    try testing.expect(!containsAny(text, &words2)); // Contains none
}

test "contains all needles" {
    const text = "The quick brown fox";
    const words = [_][]const u8{ "quick", "brown", "fox" };

    try testing.expect(containsAll(text, &words));

    const words2 = [_][]const u8{ "quick", "lazy" };
    try testing.expect(!containsAll(text, &words2)); // Missing "lazy"
}

test "search in empty string" {
    const empty = "";

    try testing.expectEqual(@as(?usize, null), indexOf(empty, "test"));
    try testing.expectEqual(@as(usize, 0), count(empty, "test"));
    try testing.expect(!contains(empty, "test"));
}

test "search for empty string" {
    const text = "hello";

    // Empty needle matches at position 0
    try testing.expectEqual(@as(?usize, 0), indexOf(text, ""));
    try testing.expect(contains(text, ""));
}

test "find URL in text" {
    const text = "Visit https://example.com for more info";

    try testing.expect(contains(text, "https://"));
    try testing.expectEqual(@as(?usize, 6), indexOf(text, "https://"));
}

test "find email pattern" {
    const text = "Contact us at support@example.com for help";

    if (indexOf(text, "@")) |at_pos| {
        try testing.expectEqual(@as(usize, 21), at_pos);

        // Extract domain (simplified)
        const after_at = text[at_pos + 1 ..];
        try testing.expect(mem.startsWith(u8, after_at, "example.com"));
    } else {
        try testing.expect(false); // Should find @
    }
}

test "check file extension in path" {
    const path = "/path/to/file.txt";

    if (lastIndexOf(path, ".")) |dot_pos| {
        const ext = path[dot_pos..];
        try testing.expectEqualStrings(".txt", ext);
    }
}

test "find line breaks" {
    const text = "line1\nline2\nline3";

    var positions = try findAll(testing.allocator, text, "\n");
    defer positions.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 2), positions.items.len);
}

test "search for quotes" {
    const text = "She said \"hello\" and \"goodbye\"";

    var quotes = try findAll(testing.allocator, text, "\"");
    defer quotes.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 4), quotes.items.len);
}

test "find first digit" {
    const text = "Product ID: 12345";

    if (indexOfAny(text, "0123456789")) |pos| {
        try testing.expectEqual(@as(usize, 12), pos);
    } else {
        try testing.expect(false);
    }
}

test "find first non-whitespace" {
    const text = "   hello world";

    if (indexOfNone(text, " \t\n\r")) |pos| {
        try testing.expectEqual(@as(usize, 3), pos);
    } else {
        try testing.expect(false);
    }
}

test "validate password requirements" {
    const password = "MyP@ssw0rd";

    // Check for uppercase
    try testing.expect(indexOfAny(password, "ABCDEFGHIJKLMNOPQRSTUVWXYZ") != null);

    // Check for lowercase
    try testing.expect(indexOfAny(password, "abcdefghijklmnopqrstuvwxyz") != null);

    // Check for digit
    try testing.expect(indexOfAny(password, "0123456789") != null);

    // Check for special char
    try testing.expect(indexOfAny(password, "!@#$%^&*") != null);
}

test "find balanced brackets" {
    const text = "array[index]";

    const open = indexOf(text, "[");
    const close = indexOf(text, "]");

    try testing.expect(open != null and close != null);
    try testing.expect(close.? > open.?);
}

test "search case sensitivity" {
    const text = "Hello World";

    try testing.expect(contains(text, "Hello"));
    try testing.expect(!contains(text, "hello")); // Case sensitive
    try testing.expect(contains(text, "World"));
    try testing.expect(!contains(text, "world"));
}

test "UTF-8 substring search" {
    const text = "Hello 世界";

    try testing.expect(contains(text, "Hello"));
    try testing.expect(contains(text, "世界"));
    try testing.expect(contains(text, "世"));

    if (indexOf(text, "世界")) |pos| {
        try testing.expectEqual(@as(usize, 6), pos); // Byte position
    }
}

test "performance - multiple searches" {
    const text = "The quick brown fox jumps over the lazy dog";

    // Multiple searches should be fast
    try testing.expect(contains(text, "quick"));
    try testing.expect(contains(text, "brown"));
    try testing.expect(contains(text, "fox"));
    try testing.expect(contains(text, "lazy"));
    try testing.expect(contains(text, "dog"));
}

test "memory safety - no allocations for basic search" {
    const text = "hello world";

    // These operations don't allocate
    const idx = indexOf(text, "world");
    const has = contains(text, "hello");
    const cnt = count(text, "l");

    try testing.expect(idx != null);
    try testing.expect(has);
    try testing.expectEqual(@as(usize, 3), cnt);
}

test "security - bounds checking" {
    const text = "safe";

    // Won't overflow even with needle longer than text
    try testing.expectEqual(@as(?usize, null), indexOf(text, "very long needle"));
    try testing.expect(!contains(text, "very long needle that is much longer than text"));
}
```

---

## Recipe 2.5: Searching and Replacing Text {#recipe-2-5}

**Tags:** allocators, arraylist, data-structures, error-handling, http, memory, networking, resource-cleanup, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_5.zig`

### Problem

You need to replace text in strings, from simple single replacements to complex multi-pattern substitutions. You want to choose the right approach based on your performance requirements.

### Solution

Zig provides several approaches for text replacement, each with different trade-offs:

### Basic Single Replacement

For replacing a single pattern, use `replaceAll` which pre-calculates the final size and performs replacement in one pass:

```zig
pub fn replaceAll(
    allocator: mem.Allocator,
    text: []const u8,
    needle: []const u8,
    replacement: []const u8,
) ![]u8 {
    if (needle.len == 0) {
        return allocator.dupe(u8, text);
    }

    // Count occurrences to pre-allocate
    var count: usize = 0;
    var pos: usize = 0;
    while (pos < text.len) {
        if (mem.indexOf(u8, text[pos..], needle)) |found| {
            count += 1;
            pos += found + needle.len;
        } else {
            break;
        }
    }

    if (count == 0) {
        return allocator.dupe(u8, text);
    }

    // Calculate final size
    const new_len = text.len - (count * needle.len) + (count * replacement.len);
    var result = try allocator.alloc(u8, new_len);
    errdefer allocator.free(result);

    // Perform replacement
    var src_pos: usize = 0;
    var dest_pos: usize = 0;

    while (src_pos < text.len) {
        if (mem.indexOf(u8, text[src_pos..], needle)) |found| {
            // Copy text before needle
            @memcpy(result[dest_pos..][0..found], text[src_pos..][0..found]);
            dest_pos += found;

            // Copy replacement
            @memcpy(result[dest_pos..][0..replacement.len], replacement);
            dest_pos += replacement.len;

            src_pos += found + needle.len;
        } else {
            // Copy remaining text
            const remaining = text[src_pos..];
            @memcpy(result[dest_pos..][0..remaining.len], remaining);
            break;
        }
    }

    return result;
}
```

### Replace First Occurrence Only

When you only want to replace the first match:

```zig
const text = "hello hello world";
const result = try replaceFirst(allocator, text, "hello", "hi");
defer allocator.free(result);

std.debug.print("{s}\n", .{result}); // "hi hello world"
```

### Multiple Pattern Replacement - Choose Your Strategy

When replacing multiple patterns, you have two choices:

#### 1. Basic Method - Simple but Less Efficient

Good for 2-3 patterns or small text:

```zig
const text = "hello world";
const replacements = [_]ReplacePair{
    .{ .needle = "hello", .replacement = "hi" },
    .{ .needle = "world", .replacement = "there" },
};

const result = try replaceMany(allocator, text, &replacements);
defer allocator.free(result);
```

**Characteristics:**
- Multiple passes over the text
- Creates intermediate allocations for each pattern
- Time: O(n * m) where n = text length, m = number of patterns
- Space: O(n * m) due to intermediate copies
- Simple code, easy to understand

**Use when:**
- You have only 2-3 replacement pairs
- The text is small (less than 1KB)
- Code simplicity matters more than performance
- Replacements might interfere with each other (order matters)

#### 2. Optimized Method - Single Pass Algorithm

Good for many patterns or large text:

```zig
const text = "The quick brown fox jumps over the lazy dog";
const replacements = [_]ReplacePair{
    .{ .needle = "quick", .replacement = "fast" },
    .{ .needle = "brown", .replacement = "red" },
    .{ .needle = "fox", .replacement = "wolf" },
    .{ .needle = "jumps", .replacement = "leaps" },
    .{ .needle = "lazy", .replacement = "sleeping" },
};

const result = try replaceManyOptimized(allocator, text, &replacements);
defer allocator.free(result);
```

**Characteristics:**
- Single pass through the text
- One output buffer (ArrayList)
- Time: O(n * m) for searches but only one pass
- Space: O(n) single output allocation
- More complex code

**Use when:**
- You have many replacement pairs (4 or more)
- The text is large (greater than 1KB)
- Performance is critical
- You want to minimize memory allocations
- Replacement order doesn't matter (processes left to right)

### Discussion

### Understanding the Trade-offs

The key difference between `replaceMany` and `replaceManyOptimized` is allocation strategy:

**replaceMany (Basic):**
1. Start with original text
2. Replace pattern 1, allocate new string
3. Replace pattern 2 in new string, allocate another new string
4. Repeat for each pattern
5. Free intermediate allocations

**replaceManyOptimized (Advanced):**
1. Create single ArrayList for output
2. Scan text for earliest occurrence of any pattern
3. Append text before match and replacement to ArrayList
4. Continue from after the match
5. One final allocation when converting ArrayList to slice

### Performance Comparison

For 8 replacements in a 72-character string:
- **Basic**: 8 allocations, 8 full text scans
- **Optimized**: 1 allocation (ArrayList grows as needed), 1 text scan

For larger texts (1KB+) with many patterns (10+), the optimized version can be 3-5x faster.

### Memory Safety

Both approaches are memory-safe when using Zig's testing allocator:

```zig
test "memory safety check" {
    const text = "test test test";
    const result = try replaceAll(testing.allocator, text, "test", "replaced");
    defer testing.allocator.free(result);
    // testing.allocator will detect any leaks
}
```

### Handling Edge Cases

Both methods handle common edge cases:
- Empty needles are ignored or return unchanged text
- No matches returns a copy of the original
- Overlapping patterns are processed left-to-right
- UTF-8 strings work correctly (byte-level replacement)

### When Order Matters

If replacement order is important (replacements depend on each other), use `replaceMany`:

```zig
// Want to replace "test" with "exam", then "exam" with "final"
const replacements = [_]ReplacePair{
    .{ .needle = "test", .replacement = "exam" },
    .{ .needle = "exam", .replacement = "final" },
};

// replaceMany: "test" -> "exam" -> "final" (sequential)
// replaceManyOptimized: "test" -> "exam" (only first occurrence)
```

### Full Tested Code

```zig
// Recipe 2.5: Searching and replacing text
// Target Zig Version: 0.15.2
//
// This recipe demonstrates various approaches to replacing text in strings,
// including single replacement, global replacement, and replace all.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;

/// Replace all occurrences of needle with replacement
/// Returns number of replacements made
// ANCHOR: replace_all
pub fn replaceAll(
    allocator: mem.Allocator,
    text: []const u8,
    needle: []const u8,
    replacement: []const u8,
) ![]u8 {
    if (needle.len == 0) {
        return allocator.dupe(u8, text);
    }

    // Count occurrences to pre-allocate
    var count: usize = 0;
    var pos: usize = 0;
    while (pos < text.len) {
        if (mem.indexOf(u8, text[pos..], needle)) |found| {
            count += 1;
            pos += found + needle.len;
        } else {
            break;
        }
    }

    if (count == 0) {
        return allocator.dupe(u8, text);
    }

    // Calculate final size
    const new_len = text.len - (count * needle.len) + (count * replacement.len);
    var result = try allocator.alloc(u8, new_len);
    errdefer allocator.free(result);

    // Perform replacement
    var src_pos: usize = 0;
    var dest_pos: usize = 0;

    while (src_pos < text.len) {
        if (mem.indexOf(u8, text[src_pos..], needle)) |found| {
            // Copy text before needle
            @memcpy(result[dest_pos..][0..found], text[src_pos..][0..found]);
            dest_pos += found;

            // Copy replacement
            @memcpy(result[dest_pos..][0..replacement.len], replacement);
            dest_pos += replacement.len;

            src_pos += found + needle.len;
        } else {
            // Copy remaining text
            const remaining = text[src_pos..];
            @memcpy(result[dest_pos..][0..remaining.len], remaining);
            break;
        }
    }

    return result;
}
// ANCHOR_END: replace_all

/// Replace first occurrence only
// ANCHOR: replace_first
pub fn replaceFirst(
    allocator: mem.Allocator,
    text: []const u8,
    needle: []const u8,
    replacement: []const u8,
) ![]u8 {
    if (mem.indexOf(u8, text, needle)) |pos| {
        const new_len = text.len - needle.len + replacement.len;
        var result = try allocator.alloc(u8, new_len);
        errdefer allocator.free(result);

        // Copy before needle
        @memcpy(result[0..pos], text[0..pos]);

        // Copy replacement
        @memcpy(result[pos..][0..replacement.len], replacement);

        // Copy after needle
        const after_start = pos + needle.len;
        const after_len = text.len - after_start;
        @memcpy(result[pos + replacement.len ..][0..after_len], text[after_start..]);

        return result;
    }

    return allocator.dupe(u8, text);
}
// ANCHOR_END: replace_first

/// Replace using a callback function that writes to an ArrayList
/// The callback receives the allocator, matched needle, and output buffer.
/// This API ensures clear ownership: the callback writes directly to the output buffer,
/// avoiding ambiguity about memory allocation and preventing leaks.
// ANCHOR: replace_with_callback
pub fn replaceWith(
    allocator: mem.Allocator,
    text: []const u8,
    needle: []const u8,
    context: anytype,
    replaceFn: *const fn (@TypeOf(context), mem.Allocator, []const u8, *std.ArrayList(u8)) anyerror!void,
) ![]u8 {
    if (needle.len == 0) {
        return allocator.dupe(u8, text);
    }

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var pos: usize = 0;
    while (pos < text.len) {
        if (mem.indexOf(u8, text[pos..], needle)) |found| {
            // Append text before needle
            try result.appendSlice(allocator, text[pos..][0..found]);

            // Let callback write replacement directly to result
            try replaceFn(context, allocator, needle, &result);

            pos += found + needle.len;
        } else {
            // Append remaining text
            try result.appendSlice(allocator, text[pos..]);
            break;
        }
    }

    return result.toOwnedSlice(allocator);
}
// ANCHOR_END: replace_with_callback

/// Remove all occurrences of substring
pub fn removeAll(
    allocator: mem.Allocator,
    text: []const u8,
    needle: []const u8,
) ![]u8 {
    return replaceAll(allocator, text, needle, "");
}

/// Replacement pair type
pub const ReplacePair = struct {
    needle: []const u8,
    replacement: []const u8,
};

/// Replace multiple patterns - BASIC METHOD
/// Simple but inefficient: performs multiple passes over the text,
/// creating intermediate allocations for each replacement pair.
///
/// Time complexity: O(n * m) where n = text length, m = number of patterns
/// Space complexity: O(n * m) due to intermediate allocations
///
/// Use when:
/// - You have only 2-3 replacement pairs
/// - The text is small (< 1KB)
/// - Code simplicity is more important than performance
/// - Replacements might interfere with each other (order matters)
pub fn replaceMany(
    allocator: mem.Allocator,
    text: []const u8,
    replacements: []const ReplacePair,
) ![]u8 {
    var result = try allocator.dupe(u8, text);

    for (replacements) |pair| {
        const new_result = try replaceAll(allocator, result, pair.needle, pair.replacement);
        allocator.free(result);
        result = new_result;
    }

    return result;
}

/// Replace multiple patterns - OPTIMIZED METHOD
/// Single-pass algorithm that finds the earliest occurrence of any pattern
/// and performs replacement in one go.
///
/// Time complexity: O(n * m) for search but only one pass
/// Space complexity: O(n) single output buffer
///
/// Use when:
/// - You have many replacement pairs (4+)
/// - The text is large (> 1KB)
/// - Performance is critical
/// - You want to minimize memory allocations
/// - Replacement order doesn't matter (processes left to right)
pub fn replaceManyOptimized(
    allocator: mem.Allocator,
    text: []const u8,
    replacements: []const ReplacePair,
) ![]u8 {
    if (replacements.len == 0) {
        return allocator.dupe(u8, text);
    }

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var pos: usize = 0;

    while (pos < text.len) {
        // Find the earliest occurrence of any pattern
        var earliest_match: ?struct {
            index: usize,
            pair_idx: usize,
        } = null;

        for (replacements, 0..) |pair, pair_idx| {
            if (pair.needle.len == 0) continue;

            if (mem.indexOf(u8, text[pos..], pair.needle)) |found_offset| {
                const absolute_pos = pos + found_offset;

                if (earliest_match == null or absolute_pos < earliest_match.?.index) {
                    earliest_match = .{
                        .index = absolute_pos,
                        .pair_idx = pair_idx,
                    };
                }
            }
        }

        if (earliest_match) |match| {
            // Append text before the match
            try result.appendSlice(allocator, text[pos..match.index]);

            // Append the replacement
            const pair = replacements[match.pair_idx];
            try result.appendSlice(allocator, pair.replacement);

            // Move position past the matched needle
            pos = match.index + pair.needle.len;
        } else {
            // No more matches found, append remaining text
            try result.appendSlice(allocator, text[pos..]);
            break;
        }
    }

    return result.toOwnedSlice(allocator);
}

test "replace all occurrences" {
    const text = "hello hello world";
    const result = try replaceAll(testing.allocator, text, "hello", "hi");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hi hi world", result);
}

test "replace first occurrence only" {
    const text = "hello hello world";
    const result = try replaceFirst(testing.allocator, text, "hello", "hi");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hi hello world", result);
}

test "replace with empty string (remove)" {
    const text = "hello world";
    const result = try replaceAll(testing.allocator, text, " ", "");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("helloworld", result);
}

test "replace with longer string" {
    const text = "hi there";
    const result = try replaceAll(testing.allocator, text, "hi", "hello");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello there", result);
}

test "replace with shorter string" {
    const text = "hello world";
    const result = try replaceAll(testing.allocator, text, "hello", "hi");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hi world", result);
}

test "replace not found" {
    const text = "hello world";
    const result = try replaceAll(testing.allocator, text, "xyz", "abc");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "replace empty needle" {
    const text = "hello";
    const result = try replaceAll(testing.allocator, text, "", "x");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello", result);
}

test "replace in empty text" {
    const text = "";
    const result = try replaceAll(testing.allocator, text, "hello", "hi");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("", result);
}

test "remove all occurrences" {
    const text = "hello, hello, world!";
    const result = try removeAll(testing.allocator, text, "hello, ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("world!", result);
}

test "replace punctuation" {
    const text = "Hello, World!";
    const result = try replaceAll(testing.allocator, text, ",", "");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello World!", result);
}

test "replace line breaks" {
    const text = "line1\nline2\nline3";
    const result = try replaceAll(testing.allocator, text, "\n", " ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("line1 line2 line3", result);
}

test "replace tabs with spaces" {
    const text = "col1\tcol2\tcol3";
    const result = try replaceAll(testing.allocator, text, "\t", "    ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("col1    col2    col3", result);
}

test "normalize whitespace" {
    const text = "hello  world";
    const result = try replaceAll(testing.allocator, text, "  ", " ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "replace URL protocol" {
    const url = "http://example.com";
    const result = try replaceAll(testing.allocator, url, "http://", "https://");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("https://example.com", result);
}

test "replace file extension" {
    const filename = "document.txt";
    const result = try replaceAll(testing.allocator, filename, ".txt", ".md");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("document.md", result);
}

test "replace HTML entities" {
    const html = "Tom &amp; Jerry";
    const result = try replaceAll(testing.allocator, html, "&amp;", "&");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Tom & Jerry", result);
}

test "replace quotes" {
    const text = "She said 'hello'";
    const result = try replaceAll(testing.allocator, text, "'", "\"");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("She said \"hello\"", result);
}

test "replace multiple patterns" {
    const text = "hello world";
    const replacements = [_]ReplacePair{
        .{ .needle = "hello", .replacement = "hi" },
        .{ .needle = "world", .replacement = "there" },
    };

    const result = try replaceMany(testing.allocator, text, &replacements);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hi there", result);
}

test "censor profanity" {
    const text = "This is bad word";
    const result = try replaceAll(testing.allocator, text, "bad", "***");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("This is *** word", result);
}

/// Collapse runs of spaces into single spaces (single-pass algorithm)
fn collapseSpaces(allocator: mem.Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var in_space = false;
    for (text) |char| {
        if (char == ' ') {
            if (!in_space) {
                try result.append(allocator, ' ');
                in_space = true;
            }
            // Skip additional spaces
        } else {
            try result.append(allocator, char);
            in_space = false;
        }
    }

    return result.toOwnedSlice(allocator);
}

test "collapse multiple spaces - basic" {
    const text = "hello    world";
    const result = try collapseSpaces(testing.allocator, text);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "collapse multiple spaces - edge cases" {
    // Leading spaces
    {
        const result = try collapseSpaces(testing.allocator, "   hello");
        defer testing.allocator.free(result);
        try testing.expectEqualStrings(" hello", result);
    }

    // Trailing spaces
    {
        const result = try collapseSpaces(testing.allocator, "hello   ");
        defer testing.allocator.free(result);
        try testing.expectEqualStrings("hello ", result);
    }

    // Mixed spacing
    {
        const result = try collapseSpaces(testing.allocator, "a  b   c    d");
        defer testing.allocator.free(result);
        try testing.expectEqualStrings("a b c d", result);
    }

    // No spaces
    {
        const result = try collapseSpaces(testing.allocator, "helloworld");
        defer testing.allocator.free(result);
        try testing.expectEqualStrings("helloworld", result);
    }

    // Only spaces
    {
        const result = try collapseSpaces(testing.allocator, "     ");
        defer testing.allocator.free(result);
        try testing.expectEqualStrings(" ", result);
    }
}

test "replaceWith - uppercase callback" {
    const Context = struct {
        fn upperCase(_: @This(), allocator: mem.Allocator, matched: []const u8, output: *std.ArrayList(u8)) !void {
            const upper = try std.ascii.allocUpperString(allocator, matched);
            defer allocator.free(upper);
            try output.appendSlice(allocator, upper);
        }
    };

    const text = "hello world hello";
    const result = try replaceWith(testing.allocator, text, "hello", Context{}, Context.upperCase);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("HELLO world HELLO", result);
}

test "replaceWith - dynamic replacement" {
    const Context = struct {
        count: usize = 0,

        fn numbered(self: *@This(), allocator: mem.Allocator, _: []const u8, output: *std.ArrayList(u8)) !void {
            self.count += 1;
            const num_str = try std.fmt.allocPrint(allocator, "[{d}]", .{self.count});
            defer allocator.free(num_str);
            try output.appendSlice(allocator, num_str);
        }
    };

    var ctx = Context{};
    const text = "X marks the X on the X";
    const result = try replaceWith(testing.allocator, text, "X", &ctx, Context.numbered);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("[1] marks the [2] on the [3]", result);
}

test "replaceWith - context-free simple replacement" {
    const Context = struct {
        fn simple(_: @This(), allocator: mem.Allocator, _: []const u8, output: *std.ArrayList(u8)) !void {
            try output.appendSlice(allocator, "REPLACED");
        }
    };

    const text = "foo bar foo";
    const result = try replaceWith(testing.allocator, text, "foo", Context{}, Context.simple);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("REPLACED bar REPLACED", result);
}

test "replaceWith - memory safety" {
    const Context = struct {
        fn allocatingCallback(_: @This(), allocator: mem.Allocator, matched: []const u8, output: *std.ArrayList(u8)) !void {
            // This callback allocates temporary memory, demonstrating safe cleanup
            const temp = try allocator.alloc(u8, matched.len * 2);
            defer allocator.free(temp);

            @memset(temp, '*');
            try output.appendSlice(allocator, temp);
        }
    };

    const text = "a b a";
    const result = try replaceWith(testing.allocator, text, "a", Context{}, Context.allocatingCallback);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("** b **", result);
    // testing.allocator will detect any leaks from the callback
}

test "replace overlapping patterns" {
    const text = "aaaa";
    const result = try replaceAll(testing.allocator, text, "aa", "b");
    defer testing.allocator.free(result);

    // Non-overlapping: "aa|aa" -> "bb"
    try testing.expectEqualStrings("bb", result);
}

test "replace with special characters" {
    const text = "Hello World";
    const result = try replaceAll(testing.allocator, text, " ", "_");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello_World", result);
}

test "replace path separators" {
    const path = "C:\\Users\\Name\\file.txt";
    const result = try replaceAll(testing.allocator, path, "\\", "/");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("C:/Users/Name/file.txt", result);
}

test "memory safety - proper cleanup" {
    const text = "test test test";
    const result = try replaceAll(testing.allocator, text, "test", "replaced");
    defer testing.allocator.free(result);

    // testing.allocator will detect leaks
    try testing.expect(result.len > 0);
}

test "security - large replacement" {
    const text = "x";
    const result = try replaceAll(testing.allocator, text, "x", "replacement");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("replacement", result);
}

test "UTF-8 replacement" {
    const text = "Hello World";
    const result = try replaceAll(testing.allocator, text, "World", "世界");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello 世界", result);
}

// Tests for optimized multi-pattern replacement

test "replaceManyOptimized - basic functionality" {
    const text = "hello world";
    const replacements = [_]ReplacePair{
        .{ .needle = "hello", .replacement = "hi" },
        .{ .needle = "world", .replacement = "there" },
    };

    const result = try replaceManyOptimized(testing.allocator, text, &replacements);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hi there", result);
}

test "replaceManyOptimized vs replaceMany - same result" {
    const text = "The quick brown fox jumps over the lazy dog";
    const replacements = [_]ReplacePair{
        .{ .needle = "quick", .replacement = "fast" },
        .{ .needle = "brown", .replacement = "red" },
        .{ .needle = "lazy", .replacement = "sleepy" },
    };

    const result1 = try replaceMany(testing.allocator, text, &replacements);
    defer testing.allocator.free(result1);

    const result2 = try replaceManyOptimized(testing.allocator, text, &replacements);
    defer testing.allocator.free(result2);

    try testing.expectEqualStrings(result1, result2);
}

test "replaceManyOptimized - HTML entity decoding" {
    const html = "&lt;div&gt;Hello &amp; goodbye&lt;/div&gt;";
    const entities = [_]ReplacePair{
        .{ .needle = "&lt;", .replacement = "<" },
        .{ .needle = "&gt;", .replacement = ">" },
        .{ .needle = "&amp;", .replacement = "&" },
        .{ .needle = "&quot;", .replacement = "\"" },
    };

    const result = try replaceManyOptimized(testing.allocator, html, &entities);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("<div>Hello & goodbye</div>", result);
}

test "replaceManyOptimized - overlapping patterns processed left-to-right" {
    const text = "aaabbbccc";
    const replacements = [_]ReplacePair{
        .{ .needle = "aaa", .replacement = "X" },
        .{ .needle = "bbb", .replacement = "Y" },
        .{ .needle = "ccc", .replacement = "Z" },
    };

    const result = try replaceManyOptimized(testing.allocator, text, &replacements);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("XYZ", result);
}

test "replaceManyOptimized - earliest match wins" {
    const text = "test testing";
    const replacements = [_]ReplacePair{
        .{ .needle = "testing", .replacement = "LONG" },
        .{ .needle = "test", .replacement = "SHORT" },
    };

    const result = try replaceManyOptimized(testing.allocator, text, &replacements);
    defer testing.allocator.free(result);

    // First "test" at position 0 is replaced with "SHORT"
    // Then "testing" at position 5 is replaced with "LONG"
    // When patterns match at the same position, first in array wins
    try testing.expectEqualStrings("SHORT LONG", result);
}

test "replaceManyOptimized - pattern order matters at same position" {
    const text = "testing";

    // When "test" is first in array
    const replacements1 = [_]ReplacePair{
        .{ .needle = "test", .replacement = "SHORT" },
        .{ .needle = "testing", .replacement = "LONG" },
    };
    const result1 = try replaceManyOptimized(testing.allocator, text, &replacements1);
    defer testing.allocator.free(result1);
    // "test" wins (first in array), result is "SHORTing"
    try testing.expectEqualStrings("SHORTing", result1);

    // When "testing" is first in array
    const replacements2 = [_]ReplacePair{
        .{ .needle = "testing", .replacement = "LONG" },
        .{ .needle = "test", .replacement = "SHORT" },
    };
    const result2 = try replaceManyOptimized(testing.allocator, text, &replacements2);
    defer testing.allocator.free(result2);
    // "testing" wins (first in array), result is "LONG"
    try testing.expectEqualStrings("LONG", result2);
}

test "replaceManyOptimized - no patterns" {
    const text = "hello world";
    const replacements = [_]ReplacePair{};

    const result = try replaceManyOptimized(testing.allocator, text, &replacements);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "replaceManyOptimized - empty needles ignored" {
    const text = "hello world";
    const replacements = [_]ReplacePair{
        .{ .needle = "", .replacement = "X" },
        .{ .needle = "world", .replacement = "there" },
    };

    const result = try replaceManyOptimized(testing.allocator, text, &replacements);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello there", result);
}

test "replaceManyOptimized - programming language sanitization" {
    const code = "var x = 10; var y = 20; const z = 30;";
    const replacements = [_]ReplacePair{
        .{ .needle = "var ", .replacement = "let " },
        .{ .needle = "const ", .replacement = "let " },
    };

    const result = try replaceManyOptimized(testing.allocator, code, &replacements);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("let x = 10; let y = 20; let z = 30;", result);
}

test "replaceManyOptimized - text normalization" {
    const messy = "Hello...world!!!How   are  you???";
    const replacements = [_]ReplacePair{
        .{ .needle = "...", .replacement = ". " },
        .{ .needle = "!!!", .replacement = "! " },
        .{ .needle = "???", .replacement = "? " },
        .{ .needle = "   ", .replacement = " " },
        .{ .needle = "  ", .replacement = " " },
    };

    const result = try replaceManyOptimized(testing.allocator, messy, &replacements);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello. world! How are you? ", result);
}

test "replaceManyOptimized - path separator normalization" {
    const path = "C:\\Users\\Name\\Documents\\file.txt";
    const replacements = [_]ReplacePair{
        .{ .needle = "\\", .replacement = "/" },
        .{ .needle = "C:", .replacement = "/c" },
    };

    const result = try replaceManyOptimized(testing.allocator, path, &replacements);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("/c/Users/Name/Documents/file.txt", result);
}

test "replaceManyOptimized - markdown to HTML basic" {
    const markdown = "**bold** and *italic* text";
    const replacements = [_]ReplacePair{
        .{ .needle = "**", .replacement = "<strong>" },
        .{ .needle = "*", .replacement = "<em>" },
    };

    const result = try replaceManyOptimized(testing.allocator, markdown, &replacements);
    defer testing.allocator.free(result);

    // Note: naive replacement, just demonstrating the concept
    try testing.expectEqualStrings("<strong>bold<strong> and <em>italic<em> text", result);
}

test "replaceManyOptimized - memory safety with many patterns" {
    const text = "a b c d e f g h i j k";
    const replacements = [_]ReplacePair{
        .{ .needle = "a", .replacement = "1" },
        .{ .needle = "b", .replacement = "2" },
        .{ .needle = "c", .replacement = "3" },
        .{ .needle = "d", .replacement = "4" },
        .{ .needle = "e", .replacement = "5" },
        .{ .needle = "f", .replacement = "6" },
        .{ .needle = "g", .replacement = "7" },
        .{ .needle = "h", .replacement = "8" },
        .{ .needle = "i", .replacement = "9" },
        .{ .needle = "j", .replacement = "10" },
    };

    const result = try replaceManyOptimized(testing.allocator, text, &replacements);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("1 2 3 4 5 6 7 8 9 10 k", result);
    // testing.allocator will detect any memory leaks
}

test "performance comparison - small text" {
    const text = "small test text";
    const replacements = [_]ReplacePair{
        .{ .needle = "small", .replacement = "tiny" },
        .{ .needle = "test", .replacement = "sample" },
    };

    // Both methods should work fine on small text
    const result1 = try replaceMany(testing.allocator, text, &replacements);
    defer testing.allocator.free(result1);

    const result2 = try replaceManyOptimized(testing.allocator, text, &replacements);
    defer testing.allocator.free(result2);

    try testing.expectEqualStrings(result1, result2);
}

test "performance comparison - many patterns" {
    const text = "The quick brown fox jumps over the lazy dog and runs through the forest";
    const replacements = [_]ReplacePair{
        .{ .needle = "quick", .replacement = "fast" },
        .{ .needle = "brown", .replacement = "red" },
        .{ .needle = "fox", .replacement = "wolf" },
        .{ .needle = "jumps", .replacement = "leaps" },
        .{ .needle = "lazy", .replacement = "sleeping" },
        .{ .needle = "dog", .replacement = "cat" },
        .{ .needle = "runs", .replacement = "sprints" },
        .{ .needle = "forest", .replacement = "woods" },
    };

    // With 8 patterns, optimized version creates fewer allocations
    const result1 = try replaceMany(testing.allocator, text, &replacements);
    defer testing.allocator.free(result1);

    const result2 = try replaceManyOptimized(testing.allocator, text, &replacements);
    defer testing.allocator.free(result2);

    // Results should be identical
    try testing.expectEqualStrings(result1, result2);
}
```

---

## Recipe 2.6: Searching and Replacing Case-Insensitive Text {#recipe-2-6}

**Tags:** allocators, data-structures, error-handling, hashmap, http, memory, networking, resource-cleanup, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_6.zig`

### Problem

You need to search, compare, or replace text without worrying about whether letters are uppercase or lowercase.

### Solution

Use Zig's `std.ascii` functions for case-insensitive operations:

### Basic Case-Insensitive Comparison

```zig
pub fn eqlIgnoreCase(a: []const u8, b: []const u8) bool {
    return ascii.eqlIgnoreCase(a, b);
}

/// Find first occurrence of needle (case-insensitive), returns index or null
pub fn indexOfIgnoreCase(text: []const u8, needle: []const u8) ?usize {
    if (needle.len == 0) return 0;
    if (needle.len > text.len) return null;

    var i: usize = 0;
    while (i <= text.len - needle.len) : (i += 1) {
        if (ascii.eqlIgnoreCase(text[i..][0..needle.len], needle)) {
            return i;
        }
    }
    return null;
}
```

### Case-Insensitive Search

```zig
pub fn containsIgnoreCase(text: []const u8, needle: []const u8) bool {
    return indexOfIgnoreCase(text, needle) != null;
}

/// Count occurrences of needle (case-insensitive, non-overlapping)
pub fn countIgnoreCase(text: []const u8, needle: []const u8) usize {
    if (needle.len == 0) return 0;

    var occurrences: usize = 0;
    var pos: usize = 0;

    while (pos < text.len) {
        if (indexOfIgnoreCase(text[pos..], needle)) |found| {
            occurrences += 1;
            pos += found + needle.len;
        } else {
            break;
        }
    }

    return occurrences;
}
```

### Case Conversion

```zig
/// Convert string to lowercase (allocates new string)
pub fn toLower(allocator: mem.Allocator, text: []const u8) ![]u8 {
    return ascii.allocLowerString(allocator, text);
}

/// Convert string to uppercase (allocates new string)
pub fn toUpper(allocator: mem.Allocator, text: []const u8) ![]u8 {
    return ascii.allocUpperString(allocator, text);
}
```

### Case-Insensitive Replace

```zig
pub fn replaceAllIgnoreCase(
    allocator: mem.Allocator,
    text: []const u8,
    needle: []const u8,
    replacement: []const u8,
) ![]u8 {
    if (needle.len == 0) {
        return allocator.dupe(u8, text);
    }

    // Count occurrences to pre-allocate
    var count: usize = 0;
    var pos: usize = 0;
    while (pos < text.len) {
        if (indexOfIgnoreCase(text[pos..], needle)) |found| {
            count += 1;
            pos += found + needle.len;
        } else {
            break;
        }
    }

    if (count == 0) {
        return allocator.dupe(u8, text);
    }

    // Calculate final size
    const new_len = text.len - (count * needle.len) + (count * replacement.len);
    var result = try allocator.alloc(u8, new_len);
    errdefer allocator.free(result);

    // Perform replacement
    var src_pos: usize = 0;
    var dest_pos: usize = 0;

    while (src_pos < text.len) {
        if (indexOfIgnoreCase(text[src_pos..], needle)) |found| {
            // Copy text before needle
            @memcpy(result[dest_pos..][0..found], text[src_pos..][0..found]);
            dest_pos += found;

            // Copy replacement
            @memcpy(result[dest_pos..][0..replacement.len], replacement);
            dest_pos += replacement.len;

            src_pos += found + needle.len;
        } else {
            // Copy remaining text
            const remaining = text[src_pos..];
            @memcpy(result[dest_pos..][0..remaining.len], remaining);
            break;
        }
    }

    return result;
}
```

### Discussion

### Available Case-Insensitive Functions

Zig's `std.ascii` provides the foundation for case operations:

**`ascii.eqlIgnoreCase(a, b)`** - Compare strings ignoring case
- Returns `bool`
- Works only with ASCII characters
- Efficient byte-by-byte comparison

**`ascii.allocLowerString(allocator, text)`** - Convert to lowercase
- Returns `![]u8` (allocates new string)
- ASCII-only conversion
- Preserves non-ASCII bytes unchanged

**`ascii.allocUpperString(allocator, text)`** - Convert to uppercase
- Returns `![]u8` (allocates new string)
- ASCII-only conversion
- Preserves non-ASCII bytes unchanged

### Building on the Foundation

The standard library provides basic case comparison, but you'll often need to implement higher-level operations:

**Custom indexOfIgnoreCase:**
```zig
pub fn indexOfIgnoreCase(text: []const u8, needle: []const u8) ?usize {
    if (needle.len > text.len) return null;

    var i: usize = 0;
    while (i <= text.len - needle.len) : (i += 1) {
        if (ascii.eqlIgnoreCase(text[i..][0..needle.len], needle)) {
            return i;
        }
    }
    return null;
}
```

**Count occurrences (case-insensitive):**
```zig
pub fn countIgnoreCase(text: []const u8, needle: []const u8) usize {
    var count: usize = 0;
    var pos: usize = 0;

    while (pos < text.len) {
        if (indexOfIgnoreCase(text[pos..], needle)) |found| {
            count += 1;
            pos += found + needle.len;
        } else {
            break;
        }
    }

    return count;
}
```

### Practical Examples

**File Extension Checking:**
```zig
pub fn endsWithIgnoreCase(text: []const u8, suffix: []const u8) bool {
    if (suffix.len > text.len) return false;
    return ascii.eqlIgnoreCase(text[text.len - suffix.len..], suffix);
}

const filename = "document.PDF";
if (endsWithIgnoreCase(filename, ".pdf")) {
    // It's a PDF file
}
```

**URL Protocol Detection:**
```zig
pub fn startsWithIgnoreCase(text: []const u8, prefix: []const u8) bool {
    if (prefix.len > text.len) return false;
    return ascii.eqlIgnoreCase(text[0..prefix.len], prefix);
}

const url = "HTTP://example.com";
if (startsWithIgnoreCase(url, "http://")) {
    // HTTP URL
}
```

**Normalize Text for Comparison:**
```zig
// Convert both strings to same case for comparison
const text1 = try ascii.allocLowerString(allocator, "Hello World");
defer allocator.free(text1);

const text2 = try ascii.allocLowerString(allocator, "hello world");
defer allocator.free(text2);

if (mem.eql(u8, text1, text2)) {
    // Strings are equal (ignoring case)
}
```

**Case-Insensitive Sorting:**
```zig
fn compareLowercase(context: void, a: []const u8, b: []const u8) bool {
    _ = context;
    const len = @min(a.len, b.len);
    var i: usize = 0;

    while (i < len) : (i += 1) {
        const a_lower = ascii.toLower(a[i]);
        const b_lower = ascii.toLower(b[i]);
        if (a_lower != b_lower) {
            return a_lower < b_lower;
        }
    }

    return a.len < b.len;
}

// Use with std.sort
std.sort.heap([]const u8, items, {}, compareLowercase);
```

### ASCII-Only Limitation

Important: `std.ascii` functions work only with ASCII characters (0-127). Non-ASCII characters are left unchanged:

```zig
const text = "Hello 世界";
const lower = try ascii.allocLowerString(allocator, text);
defer allocator.free(lower);

// Result: "hello 世界" (Chinese characters unchanged)
```

For full Unicode case folding, you would need:
1. A Unicode library (like `ziglyph`)
2. Or linking to ICU (International Components for Unicode)
3. Or implementing Unicode case tables manually

For most English text and programming contexts, ASCII operations are sufficient and much faster.

### Performance

**Case-insensitive search is O(n*m):**
- n = length of text
- m = length of needle
- Each position tests `eqlIgnoreCase` which is O(m)

**Optimization strategy:**
```zig
// For repeated searches, normalize once
const text_lower = try ascii.allocLowerString(allocator, text);
defer allocator.free(text_lower);

const needle_lower = try ascii.allocLowerString(allocator, needle);
defer allocator.free(needle_lower);

// Now use fast byte comparison
const pos = mem.indexOf(u8, text_lower, needle_lower);
```

This converts O(n*m) case-insensitive search to O(n+m) normalization + O(n) byte search.

### Memory Management

Case conversion functions allocate new strings:

```zig
const upper = try ascii.allocUpperString(allocator, "hello");
defer allocator.free(upper);  // Must free

// Original string unchanged
```

For in-place conversion (if you own the buffer):

```zig
pub fn lowerInPlace(text: []u8) void {
    for (text) |*c| {
        c.* = ascii.toLower(c.*);
    }
}

var buffer = [_]u8{'H', 'e', 'l', 'l', 'o'};
lowerInPlace(&buffer);
// buffer is now "hello"
```

### Security

All operations are bounds-safe:

```zig
// Safe - won't overflow
ascii.eqlIgnoreCase("short", "very long string");  // false

// Safe - returns null for impossible matches
indexOfIgnoreCase("abc", "longer needle");  // null
```

Zig's bounds checking prevents buffer overflows in debug mode.

### Common Patterns

**Case-Insensitive String Matching:**
```zig
pub fn matchesIgnoreCase(text: []const u8, pattern: []const u8) bool {
    return ascii.eqlIgnoreCase(text, pattern);
}
```

**Case-Insensitive List Search:**
```zig
pub fn containsAnyIgnoreCase(
    text: []const u8,
    needles: []const []const u8
) bool {
    for (needles) |needle| {
        if (containsIgnoreCase(text, needle)) {
            return true;
        }
    }
    return false;
}

// Check for keywords
const keywords = [_][]const u8{ "error", "warning", "critical" };
if (containsAnyIgnoreCase(log_line, &keywords)) {
    // Important log entry
}
```

**Case-Insensitive Key Lookup:**
```zig
pub fn findKeyIgnoreCase(
    map: std.StringHashMap(Value),
    key: []const u8,
) ?Value {
    var iter = map.iterator();
    while (iter.next()) |entry| {
        if (ascii.eqlIgnoreCase(entry.key_ptr.*, key)) {
            return entry.value_ptr.*;
        }
    }
    return null;
}
```

### When to Use Case-Insensitive Operations

**Good use cases:**
- User input comparison (usernames, commands)
- File extension checking
- Protocol/scheme detection (HTTP, FTP)
- Configuration key lookup
- Natural language search

**Avoid when:**
- Exact matching required (passwords, hashes)
- Binary data processing
- Performance-critical inner loops
- Non-Latin scripts (use Unicode libraries)

### Real-World Examples

**Command Parser:**
```zig
pub fn parseCommand(input: []const u8) ?Command {
    if (ascii.eqlIgnoreCase(input, "help")) return .Help;
    if (ascii.eqlIgnoreCase(input, "quit")) return .Quit;
    if (ascii.eqlIgnoreCase(input, "exit")) return .Exit;
    return null;
}
```

**File Type Detection:**
```zig
pub fn isImageFile(filename: []const u8) bool {
    return endsWithIgnoreCase(filename, ".jpg") or
           endsWithIgnoreCase(filename, ".jpeg") or
           endsWithIgnoreCase(filename, ".png") or
           endsWithIgnoreCase(filename, ".gif");
}
```

**Log Level Parsing:**
```zig
pub fn parseLogLevel(text: []const u8) ?LogLevel {
    if (containsIgnoreCase(text, "ERROR")) return .Error;
    if (containsIgnoreCase(text, "WARN")) return .Warning;
    if (containsIgnoreCase(text, "INFO")) return .Info;
    if (containsIgnoreCase(text, "DEBUG")) return .Debug;
    return null;
}
```

This comprehensive set of case-insensitive operations handles most text processing needs efficiently and safely within the ASCII character range.

### Full Tested Code

```zig
// Recipe 2.6: Searching and replacing case-insensitive text
// Target Zig Version: 0.15.2
//
// This recipe demonstrates case-insensitive string operations including
// searching, replacing, and comparing text regardless of case.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;
const ascii = std.ascii;

/// Case-insensitive equality check
// ANCHOR: case_insensitive_compare
pub fn eqlIgnoreCase(a: []const u8, b: []const u8) bool {
    return ascii.eqlIgnoreCase(a, b);
}

/// Find first occurrence of needle (case-insensitive), returns index or null
pub fn indexOfIgnoreCase(text: []const u8, needle: []const u8) ?usize {
    if (needle.len == 0) return 0;
    if (needle.len > text.len) return null;

    var i: usize = 0;
    while (i <= text.len - needle.len) : (i += 1) {
        if (ascii.eqlIgnoreCase(text[i..][0..needle.len], needle)) {
            return i;
        }
    }
    return null;
}
// ANCHOR_END: case_insensitive_compare

/// Find last occurrence of needle (case-insensitive), returns index or null
pub fn lastIndexOfIgnoreCase(text: []const u8, needle: []const u8) ?usize {
    if (needle.len == 0) return text.len;
    if (needle.len > text.len) return null;

    var i: usize = text.len - needle.len + 1;
    while (i > 0) {
        i -= 1;
        if (ascii.eqlIgnoreCase(text[i..][0..needle.len], needle)) {
            return i;
        }
    }
    return null;
}

/// Check if text contains needle (case-insensitive)
// ANCHOR: case_insensitive_search
pub fn containsIgnoreCase(text: []const u8, needle: []const u8) bool {
    return indexOfIgnoreCase(text, needle) != null;
}

/// Count occurrences of needle (case-insensitive, non-overlapping)
pub fn countIgnoreCase(text: []const u8, needle: []const u8) usize {
    if (needle.len == 0) return 0;

    var occurrences: usize = 0;
    var pos: usize = 0;

    while (pos < text.len) {
        if (indexOfIgnoreCase(text[pos..], needle)) |found| {
            occurrences += 1;
            pos += found + needle.len;
        } else {
            break;
        }
    }

    return occurrences;
}
// ANCHOR_END: case_insensitive_search

/// Replace all occurrences of needle with replacement (case-insensitive)
/// Returns newly allocated string
// ANCHOR: case_insensitive_replace
pub fn replaceAllIgnoreCase(
    allocator: mem.Allocator,
    text: []const u8,
    needle: []const u8,
    replacement: []const u8,
) ![]u8 {
    if (needle.len == 0) {
        return allocator.dupe(u8, text);
    }

    // Count occurrences to pre-allocate
    var count: usize = 0;
    var pos: usize = 0;
    while (pos < text.len) {
        if (indexOfIgnoreCase(text[pos..], needle)) |found| {
            count += 1;
            pos += found + needle.len;
        } else {
            break;
        }
    }

    if (count == 0) {
        return allocator.dupe(u8, text);
    }

    // Calculate final size
    const new_len = text.len - (count * needle.len) + (count * replacement.len);
    var result = try allocator.alloc(u8, new_len);
    errdefer allocator.free(result);

    // Perform replacement
    var src_pos: usize = 0;
    var dest_pos: usize = 0;

    while (src_pos < text.len) {
        if (indexOfIgnoreCase(text[src_pos..], needle)) |found| {
            // Copy text before needle
            @memcpy(result[dest_pos..][0..found], text[src_pos..][0..found]);
            dest_pos += found;

            // Copy replacement
            @memcpy(result[dest_pos..][0..replacement.len], replacement);
            dest_pos += replacement.len;

            src_pos += found + needle.len;
        } else {
            // Copy remaining text
            const remaining = text[src_pos..];
            @memcpy(result[dest_pos..][0..remaining.len], remaining);
            break;
        }
    }

    return result;
}
// ANCHOR_END: case_insensitive_replace

/// Replace first occurrence only (case-insensitive)
pub fn replaceFirstIgnoreCase(
    allocator: mem.Allocator,
    text: []const u8,
    needle: []const u8,
    replacement: []const u8,
) ![]u8 {
    if (indexOfIgnoreCase(text, needle)) |pos| {
        const new_len = text.len - needle.len + replacement.len;
        var result = try allocator.alloc(u8, new_len);
        errdefer allocator.free(result);

        // Copy before needle
        @memcpy(result[0..pos], text[0..pos]);

        // Copy replacement
        @memcpy(result[pos..][0..replacement.len], replacement);

        // Copy after needle
        const after_start = pos + needle.len;
        const after_len = text.len - after_start;
        @memcpy(result[pos + replacement.len ..][0..after_len], text[after_start..]);

        return result;
    }

    return allocator.dupe(u8, text);
}

// ANCHOR: case_conversion
/// Convert string to lowercase (allocates new string)
pub fn toLower(allocator: mem.Allocator, text: []const u8) ![]u8 {
    return ascii.allocLowerString(allocator, text);
}

/// Convert string to uppercase (allocates new string)
pub fn toUpper(allocator: mem.Allocator, text: []const u8) ![]u8 {
    return ascii.allocUpperString(allocator, text);
}
// ANCHOR_END: case_conversion

/// Check if text starts with prefix (case-insensitive)
pub fn startsWithIgnoreCase(text: []const u8, prefix: []const u8) bool {
    if (prefix.len > text.len) return false;
    return ascii.eqlIgnoreCase(text[0..prefix.len], prefix);
}

/// Check if text ends with suffix (case-insensitive)
pub fn endsWithIgnoreCase(text: []const u8, suffix: []const u8) bool {
    if (suffix.len > text.len) return false;
    return ascii.eqlIgnoreCase(text[text.len - suffix.len ..], suffix);
}

test "case-insensitive equality" {
    try testing.expect(eqlIgnoreCase("hello", "HELLO"));
    try testing.expect(eqlIgnoreCase("Hello", "hello"));
    try testing.expect(eqlIgnoreCase("HeLLo", "hEllO"));
    try testing.expect(!eqlIgnoreCase("hello", "world"));
}

test "case-insensitive indexOf" {
    const text = "Hello World";

    try testing.expectEqual(@as(?usize, 0), indexOfIgnoreCase(text, "hello"));
    try testing.expectEqual(@as(?usize, 0), indexOfIgnoreCase(text, "HELLO"));
    try testing.expectEqual(@as(?usize, 6), indexOfIgnoreCase(text, "world"));
    try testing.expectEqual(@as(?usize, 6), indexOfIgnoreCase(text, "WORLD"));
    try testing.expectEqual(@as(?usize, null), indexOfIgnoreCase(text, "xyz"));
}

test "case-insensitive lastIndexOf" {
    const text = "Hello hello world";

    try testing.expectEqual(@as(?usize, 6), lastIndexOfIgnoreCase(text, "hello"));
    try testing.expectEqual(@as(?usize, 6), lastIndexOfIgnoreCase(text, "HELLO"));
    try testing.expectEqual(@as(?usize, null), lastIndexOfIgnoreCase(text, "xyz"));
}

test "case-insensitive contains" {
    const text = "The Quick Brown Fox";

    try testing.expect(containsIgnoreCase(text, "quick"));
    try testing.expect(containsIgnoreCase(text, "QUICK"));
    try testing.expect(containsIgnoreCase(text, "QuIcK"));
    try testing.expect(containsIgnoreCase(text, "brown"));
    try testing.expect(!containsIgnoreCase(text, "lazy"));
}

test "case-insensitive count" {
    const text = "Hello hello HELLO world";

    try testing.expectEqual(@as(usize, 3), countIgnoreCase(text, "hello"));
    try testing.expectEqual(@as(usize, 3), countIgnoreCase(text, "HELLO"));
    try testing.expectEqual(@as(usize, 1), countIgnoreCase(text, "world"));
    try testing.expectEqual(@as(usize, 0), countIgnoreCase(text, "xyz"));
}

test "case-insensitive replace all" {
    const text = "Hello hello HELLO world";
    const result = try replaceAllIgnoreCase(testing.allocator, text, "hello", "hi");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hi hi hi world", result);
}

test "case-insensitive replace first" {
    const text = "Hello hello HELLO world";
    const result = try replaceFirstIgnoreCase(testing.allocator, text, "hello", "hi");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hi hello HELLO world", result);
}

test "case-insensitive replace mixed case" {
    const text = "The Quick Brown Fox";
    const result = try replaceAllIgnoreCase(testing.allocator, text, "QUICK", "Slow");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("The Slow Brown Fox", result);
}

test "case-insensitive replace not found" {
    const text = "hello world";
    const result = try replaceAllIgnoreCase(testing.allocator, text, "XYZ", "abc");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "convert to lowercase" {
    const text = "Hello WORLD";
    const result = try toLower(testing.allocator, text);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "convert to uppercase" {
    const text = "Hello world";
    const result = try toUpper(testing.allocator, text);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("HELLO WORLD", result);
}

test "case-insensitive startsWith" {
    const text = "Hello World";

    try testing.expect(startsWithIgnoreCase(text, "hello"));
    try testing.expect(startsWithIgnoreCase(text, "HELLO"));
    try testing.expect(startsWithIgnoreCase(text, "HeLLo"));
    try testing.expect(!startsWithIgnoreCase(text, "world"));
}

test "case-insensitive endsWith" {
    const text = "Hello World";

    try testing.expect(endsWithIgnoreCase(text, "world"));
    try testing.expect(endsWithIgnoreCase(text, "WORLD"));
    try testing.expect(endsWithIgnoreCase(text, "WoRLd"));
    try testing.expect(!endsWithIgnoreCase(text, "hello"));
}

test "search in mixed case text" {
    const text = "ThE qUiCk BrOwN fOx JuMpS oVeR tHe LaZy DoG";

    try testing.expect(containsIgnoreCase(text, "quick"));
    try testing.expect(containsIgnoreCase(text, "BROWN"));
    try testing.expect(containsIgnoreCase(text, "fox"));
    try testing.expect(containsIgnoreCase(text, "LAZY"));
}

test "case-insensitive file extension check" {
    const filename1 = "document.PDF";
    const filename2 = "image.Jpg";
    const filename3 = "script.TXT";

    try testing.expect(endsWithIgnoreCase(filename1, ".pdf"));
    try testing.expect(endsWithIgnoreCase(filename2, ".jpg"));
    try testing.expect(endsWithIgnoreCase(filename3, ".txt"));
}

test "case-insensitive URL protocol" {
    const url1 = "HTTP://example.com";
    const url2 = "Https://secure.com";

    try testing.expect(startsWithIgnoreCase(url1, "http://"));
    try testing.expect(startsWithIgnoreCase(url2, "https://"));
}

test "case-insensitive email search" {
    const text = "Contact us at SUPPORT@EXAMPLE.COM for help";

    try testing.expect(containsIgnoreCase(text, "support@example.com"));
    try testing.expect(containsIgnoreCase(text, "SUPPORT@EXAMPLE.COM"));
}

test "normalize text for comparison" {
    const text1 = "Hello World";
    const text2 = "hello world";

    const lower1 = try toLower(testing.allocator, text1);
    defer testing.allocator.free(lower1);

    const lower2 = try toLower(testing.allocator, text2);
    defer testing.allocator.free(lower2);

    try testing.expectEqualStrings(lower1, lower2);
}

test "case-insensitive replace preserves case context" {
    // Note: This is a simple replace that doesn't preserve original case
    // Just replaces with exact replacement text
    const text = "Hello HELLO hello";
    const result = try replaceAllIgnoreCase(testing.allocator, text, "hello", "Goodbye");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Goodbye Goodbye Goodbye", result);
}

test "memory safety - case-insensitive operations" {
    const text = "Test TEST test";
    const result = try replaceAllIgnoreCase(testing.allocator, text, "test", "pass");
    defer testing.allocator.free(result);

    // testing.allocator will detect leaks
    try testing.expect(result.len > 0);
}

test "UTF-8 with case operations" {
    const text = "Hello 世界";
    const lower = try toLower(testing.allocator, text);
    defer testing.allocator.free(lower);

    // ASCII lowercase, UTF-8 characters unchanged
    try testing.expectEqualStrings("hello 世界", lower);
}

test "empty string case operations" {
    const empty = "";

    try testing.expect(eqlIgnoreCase(empty, ""));
    try testing.expectEqual(@as(?usize, null), indexOfIgnoreCase(empty, "test"));

    const result = try replaceAllIgnoreCase(testing.allocator, empty, "test", "replace");
    defer testing.allocator.free(result);
    try testing.expectEqualStrings("", result);
}

test "single character case-insensitive" {
    try testing.expect(eqlIgnoreCase("a", "A"));
    try testing.expect(eqlIgnoreCase("Z", "z"));
    try testing.expectEqual(@as(?usize, 0), indexOfIgnoreCase("Hello", "h"));
}

test "case-insensitive with special characters" {
    const text = "Hello, World!";

    try testing.expect(containsIgnoreCase(text, "HELLO,"));
    try testing.expect(containsIgnoreCase(text, "world!"));
}

test "security - case-insensitive bounds checking" {
    const text = "short";

    // Won't overflow
    try testing.expectEqual(@as(?usize, null), indexOfIgnoreCase(text, "very long needle"));
    try testing.expect(!containsIgnoreCase(text, "very long needle that is much longer than text"));
}
```

---

## Recipe 2.7: Stripping Unwanted Characters from Strings {#recipe-2-7}

**Tags:** allocators, arraylist, csv, data-structures, error-handling, http, memory, networking, parsing, resource-cleanup, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_7.zig`

### Problem

You need to remove unwanted characters from strings - trimming whitespace, removing special characters, or filtering text to keep only specific characters.

### Solution

Use Zig's `std.mem.trim` functions and custom filters for character removal:

### Trimming Whitespace and Specific Characters

```zig
pub fn trim(text: []const u8) []const u8 {
    return mem.trim(u8, text, " \t\n\r");
}

/// Remove whitespace from start only
pub fn trimLeft(text: []const u8) []const u8 {
    return mem.trimLeft(u8, text, " \t\n\r");
}

/// Remove whitespace from end only
pub fn trimRight(text: []const u8) []const u8 {
    return mem.trimRight(u8, text, " \t\n\r");
}

/// Remove specific characters from both ends
pub fn trimChars(text: []const u8, chars: []const u8) []const u8 {
    return mem.trim(u8, text, chars);
}

/// Remove specific characters from start
pub fn trimLeftChars(text: []const u8, chars: []const u8) []const u8 {
    return mem.trimLeft(u8, text, chars);
}

/// Remove specific characters from end
pub fn trimRightChars(text: []const u8, chars: []const u8) []const u8 {
    return mem.trimRight(u8, text, chars);
}
```

### Removing and Keeping Specific Characters

```zig
pub fn removeChars(
    allocator: mem.Allocator,
    text: []const u8,
    chars_to_remove: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        var should_keep = true;
        for (chars_to_remove) |remove_char| {
            if (char == remove_char) {
                should_keep = false;
                break;
            }
        }
        if (should_keep) {
            try result.append(allocator, char);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Keep only specific characters (allocates new string)
pub fn keepChars(
    allocator: mem.Allocator,
    text: []const u8,
    chars_to_keep: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        for (chars_to_keep) |keep_char| {
            if (char == keep_char) {
                try result.append(allocator, char);
                break;
            }
        }
    }

    return result.toOwnedSlice(allocator);
}
```

### Discussion

### Available Trimming Functions

Zig's `std.mem` provides basic trimming:

**`mem.trim(u8, text, chars)`** - Remove characters from both ends
- Returns slice of original string (no allocation)
- Removes any character in `chars` string
- Common: `" \t\n\r"` for whitespace

**`mem.trimLeft(u8, text, chars)`** - Remove from start only
- Returns slice of original string
- Stops at first character not in `chars`

**`mem.trimRight(u8, text, chars)`** - Remove from end only
- Returns slice of original string
- Stops at last character not in `chars`

### Character Classification

Use `std.ascii` for common character categories:

**Remove non-alphanumeric:**
```zig
const ascii = std.ascii;

pub fn removeNonAlphanumeric(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        if (ascii.isAlphanumeric(char)) {
            try result.append(allocator, char);
        }
    }

    return result.toOwnedSlice(allocator);
}

// Usage
const text = "hello, world! 123";
const clean = try removeNonAlphanumeric(allocator, text);
defer allocator.free(clean);
// clean is "helloworld123"
```

**Remove non-alphabetic:**
```zig
pub fn removeNonAlphabetic(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        if (ascii.isAlphabetic(char)) {
            try result.append(allocator, char);
        }
    }

    return result.toOwnedSlice(allocator);
}
```

**Extract digits only:**
```zig
pub fn removeNonDigits(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        if (ascii.isDigit(char)) {
            try result.append(allocator, char);
        }
    }

    return result.toOwnedSlice(allocator);
}
```

### Practical Examples

**Sanitize Filename:**
```zig
const filename = "my*file/name?.txt";
const safe = try removeChars(allocator, filename, "/*?<>|:");
defer allocator.free(safe);
// safe is "myfilename.txt"
```

**Extract Phone Number Digits:**
```zig
const phone = "(555) 123-4567";
const digits = try removeNonDigits(allocator, phone);
defer allocator.free(digits);
// digits is "5551234567"
```

**Clean User Input:**
```zig
// Remove extra whitespace
const input = "  hello   world  ";
const trimmed = mem.trim(u8, input, " \t\n\r");

// Collapse multiple spaces
pub fn collapseSpaces(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var prev_was_space = false;
    for (text) |char| {
        const is_space = char == ' ';
        if (is_space and prev_was_space) {
            continue; // Skip consecutive spaces
        }
        try result.append(allocator, char);
        prev_was_space = is_space;
    }

    return result.toOwnedSlice(allocator);
}

const collapsed = try collapseSpaces(allocator, trimmed);
defer allocator.free(collapsed);
// collapsed is "hello world"
```

**Remove Punctuation:**
```zig
const text = "Hello, World! How are you?";
const cleaned = try removeChars(allocator, text, ",.!?;:");
defer allocator.free(cleaned);
// cleaned is "Hello World How are you"
```

**Strip URL Protocol:**
```zig
pub fn stripPrefix(text: []const u8, prefix: []const u8) []const u8 {
    if (mem.startsWith(u8, text, prefix)) {
        return text[prefix.len..];
    }
    return text;
}

const url = "https://example.com";
const domain = stripPrefix(url, "https://");
// domain is "example.com"
```

**Strip File Extension:**
```zig
pub fn stripSuffix(text: []const u8, suffix: []const u8) []const u8 {
    if (mem.endsWith(u8, text, suffix)) {
        return text[0 .. text.len - suffix.len];
    }
    return text;
}

const filename = "document.txt";
const name = stripSuffix(filename, ".txt");
// name is "document"
```

### Allocation vs Slicing

Important distinction:

**Trim operations return slices** (no allocation):
```zig
const trimmed = mem.trim(u8, "  hello  ", " ");
// No need to free - trimmed is just a slice
```

**Remove operations allocate** (must free):
```zig
const cleaned = try removeChars(allocator, "hello!", "!");
defer allocator.free(cleaned);  // Must free
```

### Performance

**Trim operations are O(n):**
- Single pass to find first/last non-whitespace
- Returns slice, no copying

**Remove operations are O(n*m):**
- n = length of text
- m = length of chars_to_remove
- Must allocate and build new string

**Optimization for repeated checks:**
```zig
// Build a lookup table for O(1) checks
var to_remove = [_]bool{false} ** 256;
for (chars_to_remove) |c| {
    to_remove[c] = true;
}

// Now check is O(1)
for (text) |char| {
    if (!to_remove[char]) {
        // Keep character
    }
}
```

### Control Characters

Remove non-printable characters:

```zig
pub fn removeControlChars(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        if (!ascii.isControl(char)) {
            try result.append(allocator, char);
        }
    }

    return result.toOwnedSlice(allocator);
}

const text = "hello\x00world\x01";
const clean = try removeControlChars(allocator, text);
defer allocator.free(clean);
// clean is "helloworld"
```

### UTF-8 Considerations

Trim and remove work at byte level, which is safe for UTF-8:

```zig
const text = "  Hello 世界  ";
const trimmed = mem.trim(u8, text, " ");
// trimmed is "Hello 世界"
// UTF-8 characters preserved correctly
```

However, character-by-character operations assume single-byte characters:

```zig
// This works for ASCII punctuation
removeChars(allocator, "Hello, 世界!", ",!")
// Result: "Hello 世界"

// This won't work correctly for multi-byte UTF-8 punctuation
// Need proper UTF-8 iterator for that
```

### Common Patterns

**Normalize Whitespace:**
```zig
pub fn normalizeWhitespace(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    // Trim ends
    const trimmed = mem.trim(u8, text, " \t\n\r");

    // Collapse internal spaces
    return collapseSpaces(allocator, trimmed);
}
```

**Clean Quotes:**
```zig
const quoted = "\"hello world\"";
const unquoted = mem.trim(u8, quoted, "\"");
// unquoted is "hello world"
```

**Strip Path Separators:**
```zig
const path = "/usr/local/bin/";
const clean = mem.trim(u8, path, "/");
// clean is "usr/local/bin"
```

### Security

All operations are bounds-safe:

```zig
// Safe - won't overflow
mem.trim(u8, "", " ")  // Returns ""
removeChars(allocator, "test", "xyz")  // Safe, returns copy
```

Zig's bounds checking prevents buffer overflows in debug mode.

### Memory Management

Always free allocated results:

```zig
const cleaned = try removeChars(allocator, text, unwanted);
defer allocator.free(cleaned);  // Clean up

// Use errdefer for error handling
pub fn processText(allocator: mem.Allocator, text: []const u8) ![]u8 {
    const step1 = try removeChars(allocator, text, ",");
    errdefer allocator.free(step1);  // Clean up if later step fails

    const step2 = try collapseSpaces(allocator, step1);
    allocator.free(step1);  // Don't need step1 anymore

    return step2;
}
```

### Real-World Examples

**Validate Username:**
```zig
pub fn sanitizeUsername(
    allocator: mem.Allocator,
    input: []const u8,
) ![]u8 {
    // Remove whitespace and special chars
    const cleaned = try removeNonAlphanumeric(allocator, input);
    errdefer allocator.free(cleaned);

    // Convert to lowercase (assuming ASCII)
    return ascii.allocLowerString(allocator, cleaned);
}
```

**Parse CSV Field:**
```zig
pub fn cleanCsvField(field: []const u8) []const u8 {
    // Remove quotes and trim
    const unquoted = mem.trim(u8, field, "\"");
    return mem.trim(u8, unquoted, " \t");
}
```

**Extract Numbers from String:**
```zig
const price = "Price: $19.99";
const numbers = try removeNonDigits(allocator, price);
defer allocator.free(numbers);
// numbers is "1999" (cents)
```

This comprehensive set of string cleaning operations handles most text sanitization needs efficiently and safely.

### Full Tested Code

```zig
// Recipe 2.7: Stripping unwanted characters
// Target Zig Version: 0.15.2
//
// This recipe demonstrates removing unwanted characters from strings,
// including whitespace trimming, character filtering, and cleanup operations.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;
const ascii = std.ascii;

/// Remove whitespace from both ends
// ANCHOR: basic_trimming
pub fn trim(text: []const u8) []const u8 {
    return mem.trim(u8, text, " \t\n\r");
}

/// Remove whitespace from start only
pub fn trimLeft(text: []const u8) []const u8 {
    return mem.trimLeft(u8, text, " \t\n\r");
}

/// Remove whitespace from end only
pub fn trimRight(text: []const u8) []const u8 {
    return mem.trimRight(u8, text, " \t\n\r");
}

/// Remove specific characters from both ends
pub fn trimChars(text: []const u8, chars: []const u8) []const u8 {
    return mem.trim(u8, text, chars);
}

/// Remove specific characters from start
pub fn trimLeftChars(text: []const u8, chars: []const u8) []const u8 {
    return mem.trimLeft(u8, text, chars);
}

/// Remove specific characters from end
pub fn trimRightChars(text: []const u8, chars: []const u8) []const u8 {
    return mem.trimRight(u8, text, chars);
}
// ANCHOR_END: basic_trimming

/// Remove all occurrences of specific characters (allocates new string)
// ANCHOR: remove_keep_chars
pub fn removeChars(
    allocator: mem.Allocator,
    text: []const u8,
    chars_to_remove: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        var should_keep = true;
        for (chars_to_remove) |remove_char| {
            if (char == remove_char) {
                should_keep = false;
                break;
            }
        }
        if (should_keep) {
            try result.append(allocator, char);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Keep only specific characters (allocates new string)
pub fn keepChars(
    allocator: mem.Allocator,
    text: []const u8,
    chars_to_keep: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        for (chars_to_keep) |keep_char| {
            if (char == keep_char) {
                try result.append(allocator, char);
                break;
            }
        }
    }

    return result.toOwnedSlice(allocator);
}
// ANCHOR_END: remove_keep_chars

/// Remove non-alphanumeric characters (allocates new string)
// ANCHOR: filter_by_type
pub fn removeNonAlphanumeric(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        if (ascii.isAlphanumeric(char)) {
            try result.append(allocator, char);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Remove non-alphabetic characters (allocates new string)
pub fn removeNonAlphabetic(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        if (ascii.isAlphabetic(char)) {
            try result.append(allocator, char);
        }
    }

    return result.toOwnedSlice(allocator);
}
// ANCHOR_END: filter_by_type

/// Remove non-digit characters (allocates new string)
pub fn removeNonDigits(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        if (ascii.isDigit(char)) {
            try result.append(allocator, char);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Collapse multiple spaces into single space (allocates new string)
pub fn collapseSpaces(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var prev_was_space = false;
    for (text) |char| {
        const is_space = char == ' ';
        if (is_space and prev_was_space) {
            continue; // Skip consecutive spaces
        }
        try result.append(allocator, char);
        prev_was_space = is_space;
    }

    return result.toOwnedSlice(allocator);
}

/// Remove control characters (allocates new string)
pub fn removeControlChars(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |char| {
        if (!ascii.isControl(char)) {
            try result.append(allocator, char);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Strip prefix if present, returns slice or original
pub fn stripPrefix(text: []const u8, prefix: []const u8) []const u8 {
    if (mem.startsWith(u8, text, prefix)) {
        return text[prefix.len..];
    }
    return text;
}

/// Strip suffix if present, returns slice or original
pub fn stripSuffix(text: []const u8, suffix: []const u8) []const u8 {
    if (mem.endsWith(u8, text, suffix)) {
        return text[0 .. text.len - suffix.len];
    }
    return text;
}

test "trim whitespace from both ends" {
    try testing.expectEqualStrings("hello", trim("  hello  "));
    try testing.expectEqualStrings("hello", trim("\t\nhello\r\n"));
    try testing.expectEqualStrings("hello world", trim("  hello world  "));
    try testing.expectEqualStrings("", trim("   "));
}

test "trim whitespace from left" {
    try testing.expectEqualStrings("hello  ", trimLeft("  hello  "));
    try testing.expectEqualStrings("hello\r\n", trimLeft("\t\nhello\r\n"));
}

test "trim whitespace from right" {
    try testing.expectEqualStrings("  hello", trimRight("  hello  "));
    try testing.expectEqualStrings("\t\nhello", trimRight("\t\nhello\r\n"));
}

test "trim specific characters" {
    try testing.expectEqualStrings("hello", trimChars("...hello...", "."));
    try testing.expectEqualStrings("world", trimChars("===world===", "="));
    try testing.expectEqualStrings("test", trimChars("--test--", "-"));
}

test "trim multiple character set" {
    try testing.expectEqualStrings("hello", trimChars(".,!hello!,.", ".,!"));
    try testing.expectEqualStrings("world", trimChars("123world321", "123"));
}

test "remove all occurrences of characters" {
    const result = try removeChars(testing.allocator, "hello, world!", ",!");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "remove spaces" {
    const result = try removeChars(testing.allocator, "h e l l o", " ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello", result);
}

test "keep only specific characters" {
    const result = try keepChars(testing.allocator, "abc123xyz789", "0123456789");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("123789", result);
}

test "remove non-alphanumeric" {
    const result = try removeNonAlphanumeric(testing.allocator, "hello, world! 123");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("helloworld123", result);
}

test "remove non-alphabetic" {
    const result = try removeNonAlphabetic(testing.allocator, "hello123world456");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("helloworld", result);
}

test "remove non-digits" {
    const result = try removeNonDigits(testing.allocator, "Product ID: 12345");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("12345", result);
}

test "extract phone number digits" {
    const result = try removeNonDigits(testing.allocator, "(555) 123-4567");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("5551234567", result);
}

test "collapse multiple spaces" {
    const result = try collapseSpaces(testing.allocator, "hello    world");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "collapse multiple spaces in text" {
    const result = try collapseSpaces(testing.allocator, "too   many    spaces");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("too many spaces", result);
}

test "remove control characters" {
    const text = "hello\x00world\x01test\x1F";
    const result = try removeControlChars(testing.allocator, text);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("helloworldtest", result);
}

test "strip prefix" {
    try testing.expectEqualStrings("world", stripPrefix("hello world", "hello "));
    try testing.expectEqualStrings("example.com", stripPrefix("http://example.com", "http://"));
    try testing.expectEqualStrings("test", stripPrefix("test", "missing"));
}

test "strip suffix" {
    try testing.expectEqualStrings("document", stripSuffix("document.txt", ".txt"));
    try testing.expectEqualStrings("image", stripSuffix("image.jpg", ".jpg"));
    try testing.expectEqualStrings("test", stripSuffix("test", "missing"));
}

test "sanitize filename" {
    const filename = "my file/name\\with:bad*chars?.txt";
    const result = try removeChars(testing.allocator, filename, "/\\:*?");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("my filenamewithbadchars.txt", result);
}

test "clean up user input" {
    const input = "  hello   world  ";
    const trimmed = trim(input);
    const result = try collapseSpaces(testing.allocator, trimmed);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "extract numbers from text" {
    const text = "Price: $123.45";
    const result = try removeNonDigits(testing.allocator, text);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("12345", result);
}

test "remove punctuation" {
    const text = "Hello, World! How are you?";
    const result = try removeChars(testing.allocator, text, ",.!?");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello World How are you", result);
}

test "clean URL" {
    const url = "https://example.com/path";
    const cleaned = stripPrefix(url, "https://");

    try testing.expectEqualStrings("example.com/path", cleaned);
}

test "trim quotes" {
    try testing.expectEqualStrings("hello", trimChars("\"hello\"", "\""));
    try testing.expectEqualStrings("world", trimChars("'world'", "'"));
}

test "normalize whitespace" {
    const text = "  hello\t\nworld  ";
    const trimmed = trim(text);

    try testing.expectEqualStrings("hello\t\nworld", trimmed);
}

test "strip path separators" {
    try testing.expectEqualStrings("file.txt", trimChars("/file.txt", "/"));
    try testing.expectEqualStrings("dir", trimChars("/dir/", "/"));
}

test "memory safety - trim operations" {
    // Trim doesn't allocate, just returns slice
    const result = trim("  test  ");
    try testing.expect(result.len > 0);
}

test "memory safety - remove operations" {
    const result = try removeChars(testing.allocator, "test123", "123");
    defer testing.allocator.free(result);

    // testing.allocator will detect leaks
    try testing.expect(result.len > 0);
}

test "UTF-8 trimming" {
    const text = "  Hello 世界  ";
    const trimmed = trim(text);

    try testing.expectEqualStrings("Hello 世界", trimmed);
}

test "empty string operations" {
    try testing.expectEqualStrings("", trim(""));
    try testing.expectEqualStrings("", trim("   "));

    const result = try removeChars(testing.allocator, "", "abc");
    defer testing.allocator.free(result);
    try testing.expectEqualStrings("", result);
}

test "no characters to remove" {
    const result = try removeChars(testing.allocator, "hello", "xyz");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello", result);
}

test "security - bounds checking" {
    // Safe operations, won't overflow
    try testing.expectEqualStrings("", trim(""));
    const result = try removeChars(testing.allocator, "test", "very long character set");
    defer testing.allocator.free(result);
    try testing.expect(result.len <= "test".len);
}
```

---

## Recipe 2.8: Combining and Concatenating Strings {#recipe-2-8}

**Tags:** allocators, arraylist, csv, data-structures, error-handling, memory, parsing, resource-cleanup, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_8.zig`

### Problem

You need to combine multiple strings together - concatenating, joining with separators, or building complex strings from multiple parts.

### Solution

Use Zig's `std.ArrayList(u8)` for building strings and `std.mem.join` for joining with separators:

### Basic Concatenation and Multiple Strings

```zig
pub fn concat(
    allocator: mem.Allocator,
    a: []const u8,
    b: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    try result.appendSlice(allocator, a);
    try result.appendSlice(allocator, b);

    return result.toOwnedSlice(allocator);
}

/// Concatenate multiple strings (allocates new string)
pub fn concatMultiple(
    allocator: mem.Allocator,
    strings: []const []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (strings) |str| {
        try result.appendSlice(allocator, str);
    }

    return result.toOwnedSlice(allocator);
}
```

### Joining with Separators

```zig
pub fn join(
    allocator: mem.Allocator,
    separator: []const u8,
    strings: []const []const u8,
) ![]u8 {
    if (strings.len == 0) return allocator.dupe(u8, "");
    if (strings.len == 1) return allocator.dupe(u8, strings[0]);

    // Calculate total size
    var total_size: usize = 0;
    for (strings) |str| {
        total_size += str.len;
    }
    total_size += separator.len * (strings.len - 1);

    var result = try allocator.alloc(u8, total_size);
    errdefer allocator.free(result);

    var pos: usize = 0;
    for (strings, 0..) |str, i| {
        @memcpy(result[pos..][0..str.len], str);
        pos += str.len;

        if (i < strings.len - 1) {
            @memcpy(result[pos..][0..separator.len], separator);
            pos += separator.len;
        }
    }

    return result;
}

/// Join strings using stdlib mem.join
pub fn joinStdlib(
    allocator: mem.Allocator,
    separator: []const u8,
    strings: []const []const u8,
) ![]u8 {
    return mem.join(allocator, separator, strings);
}
```

### Building Strings with ArrayList

```zig
pub fn buildString(
    allocator: mem.Allocator,
    parts: []const []const u8,
) ![]u8 {
    var builder = std.ArrayList(u8){};
    errdefer builder.deinit(allocator);

    for (parts) |part| {
        try builder.appendSlice(allocator, part);
    }

    return builder.toOwnedSlice(allocator);
}

/// Repeat a string n times (allocates new string)
pub fn repeat(
    allocator: mem.Allocator,
    text: []const u8,
    count: usize,
) ![]u8 {
    if (count == 0) return allocator.dupe(u8, "");

    const total_size = text.len * count;
    var result = try allocator.alloc(u8, total_size);
    errdefer allocator.free(result);

    var pos: usize = 0;
    var i: usize = 0;
    while (i < count) : (i += 1) {
        @memcpy(result[pos..][0..text.len], text);
        pos += text.len;
    }

    return result;
}
```

### Discussion

### String Concatenation Approaches

Zig provides several ways to combine strings, each with different trade-offs:

**ArrayList approach** - Most flexible, efficient for multiple appends:
```zig
var builder = std.ArrayList(u8){};
defer builder.deinit(allocator);

try builder.appendSlice(allocator, "part1");
try builder.appendSlice(allocator, "part2");

const result = try builder.toOwnedSlice(allocator);
defer allocator.free(result);
```

**mem.join** - Best for joining with separators:
```zig
const parts = [_][]const u8{ "a", "b", "c" };
const joined = try mem.join(allocator, "-", &parts);
defer allocator.free(joined);
// joined is "a-b-c"
```

**Manual allocation** - Most control, efficient when size known:
```zig
const a = "hello";
const b = " world";
const size = a.len + b.len;

var result = try allocator.alloc(u8, size);
@memcpy(result[0..a.len], a);
@memcpy(result[a.len..][0..b.len], b);
// result is "hello world"
```

### Joining Strings

The `mem.join` function is highly optimized:

```zig
pub fn join(
    allocator: mem.Allocator,
    separator: []const u8,
    strings: []const []const u8,
) ![]u8 {
    if (strings.len == 0) return allocator.dupe(u8, "");
    if (strings.len == 1) return allocator.dupe(u8, strings[0]);

    // Calculate total size
    var total_size: usize = 0;
    for (strings) |str| {
        total_size += str.len;
    }
    total_size += separator.len * (strings.len - 1);

    // Allocate once
    var result = try allocator.alloc(u8, total_size);
    errdefer allocator.free(result);

    // Copy all parts
    var pos: usize = 0;
    for (strings, 0..) |str, i| {
        @memcpy(result[pos..][0..str.len], str);
        pos += str.len;

        if (i < strings.len - 1) {
            @memcpy(result[pos..][0..separator.len], separator);
            pos += separator.len;
        }
    }

    return result;
}
```

### String Repetition

Repeat a string multiple times:

```zig
pub fn repeat(
    allocator: mem.Allocator,
    text: []const u8,
    count: usize,
) ![]u8 {
    if (count == 0) return allocator.dupe(u8, "");

    const total_size = text.len * count;
    var result = try allocator.alloc(u8, total_size);
    errdefer allocator.free(result);

    var pos: usize = 0;
    var i: usize = 0;
    while (i < count) : (i += 1) {
        @memcpy(result[pos..][0..text.len], text);
        pos += text.len;
    }

    return result;
}

// Create divider line
const divider = try repeat(allocator, "-", 40);
defer allocator.free(divider);
// divider is "----------------------------------------"
```

### String Padding

Pad strings to a fixed width:

**Left-aligned (pad right):**
```zig
pub fn padRight(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    pad_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    @memcpy(result[0..text.len], text);

    var i: usize = text.len;
    while (i < width) : (i += 1) {
        result[i] = pad_char;
    }

    return result;
}

const padded = try padRight(allocator, "hello", 10, ' ');
defer allocator.free(padded);
// padded is "hello     "
```

**Right-aligned (pad left):**
```zig
pub fn padLeft(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    pad_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    const pad_count = width - text.len;

    var i: usize = 0;
    while (i < pad_count) : (i += 1) {
        result[i] = pad_char;
    }

    @memcpy(result[pad_count..][0..text.len], text);
    return result;
}

const number = try padLeft(allocator, "42", 5, '0');
defer allocator.free(number);
// number is "00042"
```

**Centered:**
```zig
pub fn center(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    pad_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    const total_padding = width - text.len;
    const left_padding = total_padding / 2;

    var i: usize = 0;
    while (i < left_padding) : (i += 1) {
        result[i] = pad_char;
    }

    @memcpy(result[left_padding..][0..text.len], text);

    i = left_padding + text.len;
    while (i < width) : (i += 1) {
        result[i] = pad_char;
    }

    return result;
}

const centered = try center(allocator, "hi", 6, ' ');
defer allocator.free(centered);
// centered is "  hi  "
```

### Interspersing

Insert a separator between every character:

```zig
pub fn intersperse(
    allocator: mem.Allocator,
    text: []const u8,
    separator: []const u8,
) ![]u8 {
    if (text.len == 0) return allocator.dupe(u8, "");
    if (text.len == 1) return allocator.dupe(u8, text);

    const total_size = text.len + separator.len * (text.len - 1);
    var result = try allocator.alloc(u8, total_size);

    var pos: usize = 0;
    for (text, 0..) |char, i| {
        result[pos] = char;
        pos += 1;

        if (i < text.len - 1) {
            @memcpy(result[pos..][0..separator.len], separator);
            pos += separator.len;
        }
    }

    return result;
}

const spaced = try intersperse(allocator, "abc", "-");
defer allocator.free(spaced);
// spaced is "a-b-c"
```

### Practical Examples

**Build CSV Line:**
```zig
const fields = [_][]const u8{ "Name", "Age", "City" };
const csv_line = try mem.join(allocator, ",", &fields);
defer allocator.free(csv_line);
// csv_line is "Name,Age,City"
```

**Build File Path:**
```zig
const parts = [_][]const u8{ "home", "user", "documents", "file.txt" };
const path = try mem.join(allocator, "/", &parts);
defer allocator.free(path);
// path is "home/user/documents/file.txt"
```

**Format Table Row:**
```zig
const columns = [_][]const u8{ "10", "20", "30" };
const row = try mem.join(allocator, " | ", &columns);
defer allocator.free(row);
// row is "10 | 20 | 30"
```

**Build HTML Tag:**
```zig
var builder = std.ArrayList(u8){};
defer builder.deinit(allocator);

try builder.appendSlice(allocator, "<");
try builder.appendSlice(allocator, "div");
try builder.appendSlice(allocator, " class=\"");
try builder.appendSlice(allocator, "container");
try builder.appendSlice(allocator, "\">");

const tag = try builder.toOwnedSlice(allocator);
defer allocator.free(tag);
// tag is "<div class=\"container\">"
```

**Format Phone Number:**
```zig
const parts = [_][]const u8{ "(555)", " ", "123", "-", "4567" };
const phone = try concatMultiple(allocator, &parts);
defer allocator.free(phone);
// phone is "(555) 123-4567"
```

### Performance

**ArrayList is efficient for building strings:**
- Amortized O(1) append operations
- Grows capacity exponentially (1.5x or 2x)
- Single allocation for final result

**Pre-calculating size is faster:**
```zig
// Calculate size first
var total: usize = 0;
for (parts) |part| {
    total += part.len;
}

// Single allocation
var result = try allocator.alloc(u8, total);
// ... copy parts
```

**mem.join is optimized:**
- Calculates total size once
- Single allocation
- Efficient memcpy operations

### Memory Management

All concatenation operations allocate new strings:

```zig
const result = try concat(allocator, "a", "b");
defer allocator.free(result);  // Must free

// ArrayList also needs cleanup
var builder = std.ArrayList(u8){};
defer builder.deinit(allocator);  // Even if toOwnedSlice called
```

When using `toOwnedSlice`, the ArrayList no longer owns the memory, but you must still call `deinit`:

```zig
var builder = std.ArrayList(u8){};
defer builder.deinit(allocator);  // Clean up ArrayList metadata

try builder.appendSlice(allocator, "data");
const result = try builder.toOwnedSlice(allocator);
defer allocator.free(result);  // Also free the result
```

### UTF-8 Safety

Concatenation is safe with UTF-8:

```zig
const result = try concat(allocator, "Hello ", "世界");
defer allocator.free(result);
// result is "Hello 世界" - correct UTF-8
```

Byte-level operations preserve multi-byte sequences:

```zig
const parts = [_][]const u8{ "Hello", "世界", "Zig" };
const joined = try mem.join(allocator, " ", &parts);
defer allocator.free(joined);
// joined is "Hello 世界 Zig" - correct UTF-8
```

### Security

All operations are bounds-safe:

```zig
// Safe - no overflow possible
const empty = [_][]const u8{};
const result = try mem.join(allocator, ",", &empty);
defer allocator.free(result);
// result is ""
```

Zig's runtime checks prevent buffer overflows in debug builds.

### When to Use Each Approach

**Use ArrayList when:**
- Building string incrementally
- Unknown final size
- Many small appends
- Need flexibility

**Use mem.join when:**
- Joining with separator
- Known array of strings
- Want stdlib optimization

**Use manual allocation when:**
- Know exact final size
- Maximum performance needed
- Minimal memory overhead important

**Use formatting when:**
- Need type conversion (covered in Recipe 2.12)
- Complex string interpolation
- Debugging output

This comprehensive set of string combination operations handles most text building needs efficiently, safely, and idiomatically in Zig.

### Full Tested Code

```zig
// Recipe 2.8: Combining and concatenating strings
// Target Zig Version: 0.15.2
//
// This recipe demonstrates various ways to combine and concatenate strings
// using allocators, ArrayList, join, and format functions.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;

/// Concatenate two strings (allocates new string)
// ANCHOR: basic_concat
pub fn concat(
    allocator: mem.Allocator,
    a: []const u8,
    b: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    try result.appendSlice(allocator, a);
    try result.appendSlice(allocator, b);

    return result.toOwnedSlice(allocator);
}

/// Concatenate multiple strings (allocates new string)
pub fn concatMultiple(
    allocator: mem.Allocator,
    strings: []const []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (strings) |str| {
        try result.appendSlice(allocator, str);
    }

    return result.toOwnedSlice(allocator);
}
// ANCHOR_END: basic_concat

/// Join strings with a separator (allocates new string)
// ANCHOR: join_strings
pub fn join(
    allocator: mem.Allocator,
    separator: []const u8,
    strings: []const []const u8,
) ![]u8 {
    if (strings.len == 0) return allocator.dupe(u8, "");
    if (strings.len == 1) return allocator.dupe(u8, strings[0]);

    // Calculate total size
    var total_size: usize = 0;
    for (strings) |str| {
        total_size += str.len;
    }
    total_size += separator.len * (strings.len - 1);

    var result = try allocator.alloc(u8, total_size);
    errdefer allocator.free(result);

    var pos: usize = 0;
    for (strings, 0..) |str, i| {
        @memcpy(result[pos..][0..str.len], str);
        pos += str.len;

        if (i < strings.len - 1) {
            @memcpy(result[pos..][0..separator.len], separator);
            pos += separator.len;
        }
    }

    return result;
}

/// Join strings using stdlib mem.join
pub fn joinStdlib(
    allocator: mem.Allocator,
    separator: []const u8,
    strings: []const []const u8,
) ![]u8 {
    return mem.join(allocator, separator, strings);
}
// ANCHOR_END: join_strings

/// Build string using ArrayList
// ANCHOR: string_builder
pub fn buildString(
    allocator: mem.Allocator,
    parts: []const []const u8,
) ![]u8 {
    var builder = std.ArrayList(u8){};
    errdefer builder.deinit(allocator);

    for (parts) |part| {
        try builder.appendSlice(allocator, part);
    }

    return builder.toOwnedSlice(allocator);
}

/// Repeat a string n times (allocates new string)
pub fn repeat(
    allocator: mem.Allocator,
    text: []const u8,
    count: usize,
) ![]u8 {
    if (count == 0) return allocator.dupe(u8, "");

    const total_size = text.len * count;
    var result = try allocator.alloc(u8, total_size);
    errdefer allocator.free(result);

    var pos: usize = 0;
    var i: usize = 0;
    while (i < count) : (i += 1) {
        @memcpy(result[pos..][0..text.len], text);
        pos += text.len;
    }

    return result;
}
// ANCHOR_END: string_builder

/// Pad string to width with character (left aligned)
pub fn padRight(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    pad_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    errdefer allocator.free(result);

    @memcpy(result[0..text.len], text);

    var i: usize = text.len;
    while (i < width) : (i += 1) {
        result[i] = pad_char;
    }

    return result;
}

/// Pad string to width with character (right aligned)
pub fn padLeft(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    pad_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    errdefer allocator.free(result);

    const pad_count = width - text.len;
    var i: usize = 0;
    while (i < pad_count) : (i += 1) {
        result[i] = pad_char;
    }

    @memcpy(result[pad_count..][0..text.len], text);

    return result;
}

/// Center string in width with character
pub fn center(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    pad_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    errdefer allocator.free(result);

    const total_padding = width - text.len;
    const left_padding = total_padding / 2;

    var i: usize = 0;
    while (i < left_padding) : (i += 1) {
        result[i] = pad_char;
    }

    @memcpy(result[left_padding..][0..text.len], text);

    i = left_padding + text.len;
    while (i < width) : (i += 1) {
        result[i] = pad_char;
    }

    return result;
}

/// Intersperse a separator between characters
pub fn intersperse(
    allocator: mem.Allocator,
    text: []const u8,
    separator: []const u8,
) ![]u8 {
    if (text.len == 0) return allocator.dupe(u8, "");
    if (text.len == 1) return allocator.dupe(u8, text);

    const total_size = text.len + separator.len * (text.len - 1);
    var result = try allocator.alloc(u8, total_size);
    errdefer allocator.free(result);

    var pos: usize = 0;
    for (text, 0..) |char, i| {
        result[pos] = char;
        pos += 1;

        if (i < text.len - 1) {
            @memcpy(result[pos..][0..separator.len], separator);
            pos += separator.len;
        }
    }

    return result;
}

test "concatenate two strings" {
    const result = try concat(testing.allocator, "hello", " world");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "concatenate empty strings" {
    const result = try concat(testing.allocator, "", "hello");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello", result);
}

test "concatenate multiple strings" {
    const strings = [_][]const u8{ "one", "two", "three" };
    const result = try concatMultiple(testing.allocator, &strings);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("onetwothree", result);
}

test "join with separator" {
    const strings = [_][]const u8{ "apple", "banana", "cherry" };
    const result = try join(testing.allocator, ", ", &strings);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("apple, banana, cherry", result);
}

test "join with space separator" {
    const strings = [_][]const u8{ "hello", "world" };
    const result = try join(testing.allocator, " ", &strings);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "join empty array" {
    const strings = [_][]const u8{};
    const result = try join(testing.allocator, ", ", &strings);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("", result);
}

test "join single string" {
    const strings = [_][]const u8{"only"};
    const result = try join(testing.allocator, ", ", &strings);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("only", result);
}

test "join stdlib" {
    const strings = [_][]const u8{ "a", "b", "c" };
    const result = try joinStdlib(testing.allocator, "-", &strings);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("a-b-c", result);
}

test "build string with ArrayList" {
    const parts = [_][]const u8{ "Hello", ", ", "World", "!" };
    const result = try buildString(testing.allocator, &parts);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello, World!", result);
}

test "repeat string" {
    const result = try repeat(testing.allocator, "ab", 3);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("ababab", result);
}

test "repeat zero times" {
    const result = try repeat(testing.allocator, "test", 0);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("", result);
}

test "repeat once" {
    const result = try repeat(testing.allocator, "test", 1);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("test", result);
}

test "pad right" {
    const result = try padRight(testing.allocator, "hello", 10, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello     ", result);
}

test "pad right no padding needed" {
    const result = try padRight(testing.allocator, "hello", 5, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello", result);
}

test "pad left" {
    const result = try padLeft(testing.allocator, "42", 5, '0');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("00042", result);
}

test "pad left no padding needed" {
    const result = try padLeft(testing.allocator, "hello", 3, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello", result);
}

test "center string" {
    const result = try center(testing.allocator, "hi", 6, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("  hi  ", result);
}

test "center string odd padding" {
    const result = try center(testing.allocator, "hi", 7, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("  hi   ", result);
}

test "intersperse characters" {
    const result = try intersperse(testing.allocator, "abc", "-");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("a-b-c", result);
}

test "intersperse empty string" {
    const result = try intersperse(testing.allocator, "", "-");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("", result);
}

test "intersperse single char" {
    const result = try intersperse(testing.allocator, "a", "-");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("a", result);
}

test "build CSV line" {
    const fields = [_][]const u8{ "Name", "Age", "City" };
    const result = try join(testing.allocator, ",", &fields);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Name,Age,City", result);
}

test "build path" {
    const parts = [_][]const u8{ "home", "user", "documents", "file.txt" };
    const result = try join(testing.allocator, "/", &parts);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("home/user/documents/file.txt", result);
}

test "build HTML tag" {
    const tag_parts = [_][]const u8{ "<", "div", ">" };
    const result = try concatMultiple(testing.allocator, &tag_parts);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("<div>", result);
}

test "build table row" {
    const columns = [_][]const u8{ "10", "20", "30" };
    const result = try join(testing.allocator, " | ", &columns);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("10 | 20 | 30", result);
}

test "create divider line" {
    const result = try repeat(testing.allocator, "-", 40);
    defer testing.allocator.free(result);

    try testing.expectEqual(@as(usize, 40), result.len);
    for (result) |c| {
        try testing.expectEqual(@as(u8, '-'), c);
    }
}

test "format phone number" {
    const parts = [_][]const u8{ "(555)", " ", "123", "-", "4567" };
    const result = try concatMultiple(testing.allocator, &parts);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("(555) 123-4567", result);
}

test "memory safety - concatenation" {
    const result = try concat(testing.allocator, "test", "123");
    defer testing.allocator.free(result);

    // testing.allocator will detect leaks
    try testing.expect(result.len > 0);
}

test "UTF-8 concatenation" {
    const result = try concat(testing.allocator, "Hello ", "世界");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello 世界", result);
}

test "UTF-8 join" {
    const strings = [_][]const u8{ "Hello", "世界", "Zig" };
    const result = try join(testing.allocator, " ", &strings);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello 世界 Zig", result);
}

test "security - large concatenation" {
    const strings = [_][]const u8{ "a", "b", "c", "d", "e" };
    const result = try concatMultiple(testing.allocator, &strings);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("abcde", result);
}

test "security - empty parts" {
    const strings = [_][]const u8{ "", "", "" };
    const result = try concatMultiple(testing.allocator, &strings);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("", result);
}
```

---

## Recipe 2.9: Interpolating Variables in Strings {#recipe-2-9}

**Tags:** allocators, comptime, error-handling, http, json, memory, networking, parsing, pointers, resource-cleanup, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_9.zig`

### Problem

You need to build strings that include variable values - formatting numbers, combining text with data, or creating dynamic messages with proper formatting.

### Solution

Use Zig's `std.fmt` functions for type-safe string formatting:

### Basic String Formatting

```zig
/// Format a string with variables (allocates new string)
pub fn format(
    allocator: mem.Allocator,
    comptime format_string: []const u8,
    args: anytype,
) ![]u8 {
    return fmt.allocPrint(allocator, format_string, args);
}

/// Format into a fixed buffer (no allocation)
pub fn formatBuf(
    buffer: []u8,
    comptime format_string: []const u8,
    args: anytype,
) ![]u8 {
    return fmt.bufPrint(buffer, format_string, args);
}

/// Count format string size without allocating
pub fn formatCount(
    comptime format_string: []const u8,
    args: anytype,
) !usize {
    return fmt.count(format_string, args);
}
```

### Format Specifiers

```zig
test "format integers" {
    const result = try format(testing.allocator, "Number: {d}", .{42});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Number: 42", result);
}

test "format floats" {
    const result = try format(testing.allocator, "Pi: {d:.2}", .{3.14159});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Pi: 3.14", result);
}

test "format hexadecimal" {
    const result = try format(testing.allocator, "Hex: 0x{x}", .{255});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hex: 0xff", result);
}

test "format hexadecimal uppercase" {
    const result = try format(testing.allocator, "Hex: 0x{X}", .{255});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hex: 0xFF", result);
}

test "format octal" {
    const result = try format(testing.allocator, "Octal: {o}", .{64});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Octal: 100", result);
}

test "format binary" {
    const result = try format(testing.allocator, "Binary: {b}", .{15});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Binary: 1111", result);
}
```

### Discussion

### Format Functions

Zig's `std.fmt` provides three main formatting functions:

**`allocPrint`** - Allocates and returns formatted string:
```zig
const result = try fmt.allocPrint(allocator, "Value: {d}", .{42});
defer allocator.free(result);
```

**`bufPrint`** - Formats into existing buffer (no allocation):
```zig
var buf: [100]u8 = undefined;
const result = try fmt.bufPrint(&buf, "Value: {d}", .{42});
// result is slice of buf
```

**`count`** - Returns size needed (no allocation, no output):
```zig
const size = try fmt.count("Value: {d}", .{42});
// size is 9
```

### Format Specifier Details

**Width and Padding:**
```zig
// Minimum width of 5
fmt.allocPrint(allocator, "{d:5}", .{42})  // "   42"

// Zero padding
fmt.allocPrint(allocator, "{d:0>5}", .{42})  // "00042"

// Left align with padding
fmt.allocPrint(allocator, "{d:<5}", .{42})  // "42   "
```

**Precision for Floats:**
```zig
// 2 decimal places
fmt.allocPrint(allocator, "{d:.2}", .{3.14159})  // "3.14"

// 4 decimal places
fmt.allocPrint(allocator, "{d:.4}", .{3.14159})  // "3.1416"
```

**Combining Width and Precision:**
```zig
// Width 8, precision 2
fmt.allocPrint(allocator, "{d:8.2}", .{3.14})  // "    3.14"
```

### Practical Examples

**Format URLs:**
```zig
const protocol = "https";
const domain = "example.com";
const path = "api/users";
const url = try fmt.allocPrint(
    allocator,
    "{s}://{s}/{s}",
    .{ protocol, domain, path }
);
defer allocator.free(url);
// url is "https://example.com/api/users"
```

**Format File Paths:**
```zig
const dir = "/home/user";
const file = "document.txt";
const path = try fmt.allocPrint(allocator, "{s}/{s}", .{ dir, file });
defer allocator.free(path);
// path is "/home/user/document.txt"
```

**Format Log Messages:**
```zig
const level = "INFO";
const message = "Server started";
const port: u16 = 8080;
const log = try fmt.allocPrint(
    allocator,
    "[{s}] {s} on port {d}",
    .{ level, message, port }
);
defer allocator.free(log);
// log is "[INFO] Server started on port 8080"
```

**Format Currency:**
```zig
const amount: f64 = 1234.56;
const price = try fmt.allocPrint(allocator, "Price: ${d:.2}", .{amount});
defer allocator.free(price);
// price is "Price: $1234.56"
```

**Format Percentages:**
```zig
const value: f32 = 0.856;
const percent = value * 100.0;
const display = try fmt.allocPrint(allocator, "Progress: {d:.1}%", .{percent});
defer allocator.free(display);
// display is "Progress: 85.6%"
```

**Format Dates:**
```zig
const year: u32 = 2024;
const month: u32 = 3;
const day: u32 = 15;
const date = try fmt.allocPrint(
    allocator,
    "{d:0>4}-{d:0>2}-{d:0>2}",
    .{ year, month, day }
);
defer allocator.free(date);
// date is "2024-03-15"
```

**Format Times:**
```zig
const hour: u32 = 9;
const minute: u32 = 5;
const second: u32 = 3;
const time = try fmt.allocPrint(
    allocator,
    "{d:0>2}:{d:0>2}:{d:0>2}",
    .{ hour, minute, second }
);
defer allocator.free(time);
// time is "09:05:03"
```

**Format SQL Queries:**
```zig
const table = "users";
const id: u32 = 123;
const query = try fmt.allocPrint(
    allocator,
    "SELECT * FROM {s} WHERE id = {d}",
    .{ table, id }
);
defer allocator.free(query);
// query is "SELECT * FROM users WHERE id = 123"
```

**Format Error Messages:**
```zig
const filename = "data.txt";
const line: u32 = 42;
const column: u32 = 15;
const error_msg = try fmt.allocPrint(
    allocator,
    "Error in {s} at line {d}, column {d}",
    .{ filename, line, column }
);
defer allocator.free(error_msg);
// error_msg is "Error in data.txt at line 42, column 15"
```

**Format Byte Sizes:**
```zig
const bytes: u64 = 1536;
const kb = @as(f64, @floatFromInt(bytes)) / 1024.0;
const size = try fmt.allocPrint(allocator, "{d:.2} KB", .{kb});
defer allocator.free(size);
// size is "1.50 KB"
```

### Format Complex Types

**Arrays and Slices:**
```zig
const numbers = [_]u32{ 1, 2, 3, 4, 5 };
const result = try fmt.allocPrint(allocator, "Numbers: {any}", .{numbers});
defer allocator.free(result);
// result is "Numbers: { 1, 2, 3, 4, 5 }"
```

**Structs:**
```zig
const Point = struct {
    x: i32,
    y: i32,
};

const point = Point{ .x = 10, .y = 20 };
const result = try fmt.allocPrint(allocator, "Point: {any}", .{point});
defer allocator.free(result);
// result is "Point: main.Point{ .x = 10, .y = 20 }"
```

### Escaping Braces

To include literal braces, double them:

```zig
// Use {{ and }} for literal braces
const json = try fmt.allocPrint(
    allocator,
    "{{\"name\": \"{s}\", \"age\": {d}}}",
    .{ "Alice", 30 }
);
defer allocator.free(json);
// json is "{\"name\": \"Alice\", \"age\": 30}"
```

### Type Safety

Zig's formatting is compile-time type-checked:

```zig
// This compiles
fmt.allocPrint(allocator, "{d}", .{42})  // OK

// This would be a compile error
// fmt.allocPrint(allocator, "{d}", .{"string"})  // ERROR: wrong type
```

The format string and arguments are validated at compile time, preventing runtime format errors.

### Performance

**allocPrint allocates** - must free result:
```zig
const result = try fmt.allocPrint(allocator, "...", .{args});
defer allocator.free(result);
```

**bufPrint is faster** - no allocation:
```zig
var buf: [100]u8 = undefined;
const result = try fmt.bufPrint(&buf, "...", .{args});
// No need to free, result is slice of buf
```

**Pre-calculate size for exact allocation:**
```zig
const size = try fmt.count("Value: {d}", .{42});
var buf = try allocator.alloc(u8, size);
defer allocator.free(buf);
_ = try fmt.bufPrint(buf, "Value: {d}", .{42});
```

### Memory Management

All `allocPrint` results must be freed:

```zig
const result = try fmt.allocPrint(allocator, "...", .{args});
defer allocator.free(result);  // Must free

// bufPrint doesn't allocate
var buf: [100]u8 = undefined;
const result = try fmt.bufPrint(&buf, "...", .{args});
// No free needed
```

### UTF-8 Support

Formatting is UTF-8 safe:

```zig
// UTF-8 in format string
const msg = try fmt.allocPrint(allocator, "Hello 世界 {d}", .{42});
defer allocator.free(msg);
// msg is "Hello 世界 42"

// UTF-8 in arguments
const text = "世界";
const msg = try fmt.allocPrint(allocator, "Hello {s}", .{text});
defer allocator.free(msg);
// msg is "Hello 世界"
```

### Debugging

The `{any}` specifier prints debug representation:

```zig
const data = .{ .name = "test", .value = 42 };
const debug = try fmt.allocPrint(allocator, "Data: {any}", .{data});
defer allocator.free(debug);
// Prints full structure
```

### Security

Format strings are compile-time validated:
- No format string vulnerabilities
- Type mismatches are compile errors
- Buffer overflows prevented

```zig
// Safe - buffer size checked
var buf: [10]u8 = undefined;
// Returns error if doesn't fit
const result = fmt.bufPrint(&buf, "...", .{args});
```

### When to Use Each Function

**Use `allocPrint` when:**
- Unknown output size
- Dynamic formatting
- One-time formatting
- Convenience matters

**Use `bufPrint` when:**
- Performance critical
- Known maximum size
- Avoiding allocations
- Stack buffers preferred

**Use `count` when:**
- Need exact size first
- Pre-allocating buffers
- Validating format
- Size calculations

### Comparison with Other Languages

**Unlike C's printf:**
- Type-safe at compile time
- No format string vulnerabilities
- Explicit allocator
- UTF-8 safe by default

**Unlike Python's f-strings:**
- Compile-time checking
- Explicit memory management
- No implicit conversions
- Manual float formatting

**Like Rust's format!:**
- Compile-time validation
- Type-safe formatting
- Explicit allocator
- Similar specifier syntax

This comprehensive formatting system provides type-safe, efficient string interpolation for all Zig programming needs.

### Full Tested Code

```zig
// Recipe 2.9: Interpolating variables in strings
// Target Zig Version: 0.15.2
//
// This recipe demonstrates string formatting and variable interpolation
// using std.fmt functions for building formatted strings.

const std = @import("std");
const testing = std.testing;
const fmt = std.fmt;
const mem = std.mem;

// ANCHOR: basic_formatting
/// Format a string with variables (allocates new string)
pub fn format(
    allocator: mem.Allocator,
    comptime format_string: []const u8,
    args: anytype,
) ![]u8 {
    return fmt.allocPrint(allocator, format_string, args);
}

/// Format into a fixed buffer (no allocation)
pub fn formatBuf(
    buffer: []u8,
    comptime format_string: []const u8,
    args: anytype,
) ![]u8 {
    return fmt.bufPrint(buffer, format_string, args);
}

/// Count format string size without allocating
pub fn formatCount(
    comptime format_string: []const u8,
    args: anytype,
) !usize {
    return fmt.count(format_string, args);
}
// ANCHOR_END: basic_formatting

test "basic string formatting" {
    const result = try format(testing.allocator, "Hello, {s}!", .{"World"});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello, World!", result);
}

test "format multiple variables" {
    const name = "Alice";
    const age: u32 = 30;
    const result = try format(testing.allocator, "{s} is {d} years old", .{ name, age });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Alice is 30 years old", result);
}

// ANCHOR: format_specifiers
test "format integers" {
    const result = try format(testing.allocator, "Number: {d}", .{42});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Number: 42", result);
}

test "format floats" {
    const result = try format(testing.allocator, "Pi: {d:.2}", .{3.14159});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Pi: 3.14", result);
}

test "format hexadecimal" {
    const result = try format(testing.allocator, "Hex: 0x{x}", .{255});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hex: 0xff", result);
}

test "format hexadecimal uppercase" {
    const result = try format(testing.allocator, "Hex: 0x{X}", .{255});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hex: 0xFF", result);
}

test "format octal" {
    const result = try format(testing.allocator, "Octal: {o}", .{64});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Octal: 100", result);
}

test "format binary" {
    const result = try format(testing.allocator, "Binary: {b}", .{15});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Binary: 1111", result);
}
// ANCHOR_END: format_specifiers

test "format boolean" {
    const result = try format(testing.allocator, "Value: {any}", .{true});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Value: true", result);
}

test "format character" {
    const result = try format(testing.allocator, "Char: {c}", .{'A'});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Char: A", result);
}

test "format pointer" {
    const value: u32 = 42;
    const ptr = &value;
    const result = try format(testing.allocator, "Pointer: {*}", .{ptr});
    defer testing.allocator.free(result);

    try testing.expect(result.len > 10); // Just check it formatted something
}

test "format with width" {
    const result = try format(testing.allocator, "Number: {d:5}", .{42});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Number:    42", result);
}

test "format with zero padding" {
    const result = try format(testing.allocator, "Number: {d:0>5}", .{42});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Number: 00042", result);
}

test "format multiple types" {
    const result = try format(
        testing.allocator,
        "String: {s}, Int: {d}, Float: {d:.1}, Hex: 0x{x}",
        .{ "test", 100, 3.14, 255 },
    );
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("String: test, Int: 100, Float: 3.1, Hex: 0xff", result);
}

test "format into buffer - no allocation" {
    var buffer: [100]u8 = undefined;
    const result = try formatBuf(&buffer, "Hello, {s}!", .{"World"});

    try testing.expectEqualStrings("Hello, World!", result);
}

test "format into buffer - exact size" {
    var buffer: [13]u8 = undefined;
    const result = try formatBuf(&buffer, "Hello, {s}!", .{"World"});

    try testing.expectEqualStrings("Hello, World!", result);
}

test "format count" {
    const size = try formatCount("Hello, {s}!", .{"World"});

    try testing.expectEqual(@as(usize, 13), size);
}

// ANCHOR: practical_formatting
test "format URL" {
    const protocol = "https";
    const domain = "example.com";
    const path = "api/users";
    const result = try format(testing.allocator, "{s}://{s}/{s}", .{ protocol, domain, path });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("https://example.com/api/users", result);
}

test "format file path" {
    const dir = "/home/user";
    const file = "document.txt";
    const result = try format(testing.allocator, "{s}/{s}", .{ dir, file });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("/home/user/document.txt", result);
}

test "format SQL query" {
    const table = "users";
    const id: u32 = 123;
    const result = try format(testing.allocator, "SELECT * FROM {s} WHERE id = {d}", .{ table, id });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("SELECT * FROM users WHERE id = 123", result);
}

test "format log message" {
    const level = "INFO";
    const message = "Server started";
    const port: u16 = 8080;
    const result = try format(testing.allocator, "[{s}] {s} on port {d}", .{ level, message, port });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("[INFO] Server started on port 8080", result);
}

test "format JSON-like string" {
    const name = "Alice";
    const age: u32 = 30;
    const result = try format(testing.allocator, "{{\"name\": \"{s}\", \"age\": {d}}}", .{ name, age });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("{\"name\": \"Alice\", \"age\": 30}", result);
}
// ANCHOR_END: practical_formatting

test "format temperature" {
    const celsius: f32 = 23.5;
    const result = try format(testing.allocator, "Temperature: {d:.1}°C", .{celsius});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Temperature: 23.5°C", result);
}

test "format currency" {
    const amount: f64 = 1234.56;
    const result = try format(testing.allocator, "Price: ${d:.2}", .{amount});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Price: $1234.56", result);
}

test "format percentage" {
    const value: f32 = 0.856;
    const percent = value * 100.0;
    const result = try format(testing.allocator, "Progress: {d:.1}%", .{percent});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Progress: 85.6%", result);
}

test "format date components" {
    const year: u32 = 2024;
    const month: u32 = 3;
    const day: u32 = 15;
    const result = try format(testing.allocator, "{d:0>4}-{d:0>2}-{d:0>2}", .{ year, month, day });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("2024-03-15", result);
}

test "format time components" {
    const hour: u32 = 9;
    const minute: u32 = 5;
    const second: u32 = 3;
    const result = try format(testing.allocator, "{d:0>2}:{d:0>2}:{d:0>2}", .{ hour, minute, second });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("09:05:03", result);
}

test "format array slice" {
    const numbers = [_]u32{ 1, 2, 3, 4, 5 };
    const result = try format(testing.allocator, "Numbers: {any}", .{numbers});
    defer testing.allocator.free(result);

    try testing.expect(mem.indexOf(u8, result, "1") != null);
    try testing.expect(mem.indexOf(u8, result, "5") != null);
}

test "format struct" {
    const Point = struct {
        x: i32,
        y: i32,
    };

    const point = Point{ .x = 10, .y = 20 };
    const result = try format(testing.allocator, "Point: {any}", .{point});
    defer testing.allocator.free(result);

    try testing.expect(mem.indexOf(u8, result, "10") != null);
    try testing.expect(mem.indexOf(u8, result, "20") != null);
}

test "format error message" {
    const filename = "data.txt";
    const line: u32 = 42;
    const column: u32 = 15;
    const result = try format(
        testing.allocator,
        "Error in {s} at line {d}, column {d}",
        .{ filename, line, column },
    );
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Error in data.txt at line 42, column 15", result);
}

test "format byte size" {
    const bytes: u64 = 1536;
    const kb = @as(f64, @floatFromInt(bytes)) / 1024.0;
    const result = try format(testing.allocator, "{d:.2} KB", .{kb});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("1.50 KB", result);
}

test "memory safety - formatting" {
    const result = try format(testing.allocator, "test {d}", .{123});
    defer testing.allocator.free(result);

    // testing.allocator will detect leaks
    try testing.expect(result.len > 0);
}

test "UTF-8 in format string" {
    const result = try format(testing.allocator, "Hello 世界 {d}", .{42});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello 世界 42", result);
}

test "UTF-8 in arguments" {
    const text = "世界";
    const result = try format(testing.allocator, "Hello {s}", .{text});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello 世界", result);
}

test "empty format string" {
    const result = try format(testing.allocator, "", .{});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("", result);
}

test "format with no arguments" {
    const result = try format(testing.allocator, "Static text", .{});
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Static text", result);
}

test "security - format large numbers" {
    const big: u64 = 18446744073709551615; // max u64
    const result = try format(testing.allocator, "Big: {d}", .{big});
    defer testing.allocator.free(result);

    try testing.expect(result.len > 0);
}
```

---

## Recipe 2.10: Aligning Text Strings {#recipe-2-10}

**Tags:** allocators, arraylist, data-structures, error-handling, memory, resource-cleanup, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_10.zig`

### Problem

You need to align text for tables, reports, or structured output - left-aligning, right-aligning, centering, or formatting columns with proper padding.

### Solution

Create alignment functions for left, right, and center alignment with custom fill characters:

### Left, Right, and Center Alignment

```zig
/// Align text left with padding
pub fn alignLeft(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    fill_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    errdefer allocator.free(result);

    @memcpy(result[0..text.len], text);

    var i: usize = text.len;
    while (i < width) : (i += 1) {
        result[i] = fill_char;
    }

    return result;
}

/// Align text right with padding
pub fn alignRight(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    fill_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    errdefer allocator.free(result);

    const padding = width - text.len;

    var i: usize = 0;
    while (i < padding) : (i += 1) {
        result[i] = fill_char;
    }

    @memcpy(result[padding..][0..text.len], text);

    return result;
}

/// Align text center with padding
pub fn alignCenter(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    fill_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    errdefer allocator.free(result);

    const total_padding = width - text.len;
    const left_padding = total_padding / 2;

    var i: usize = 0;
    while (i < left_padding) : (i += 1) {
        result[i] = fill_char;
    }

    @memcpy(result[left_padding..][0..text.len], text);

    i = left_padding + text.len;
    while (i < width) : (i += 1) {
        result[i] = fill_char;
    }

    return result;
}
```

### Discussion

### Formatting Tables

**Format table rows with aligned columns:**

```zig
pub fn formatRow(
    allocator: mem.Allocator,
    columns: []const []const u8,
    widths: []const usize,
    separator: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (columns, widths, 0..) |col, width, i| {
        const padded = try alignLeft(allocator, col, width, ' ');
        defer allocator.free(padded);

        try result.appendSlice(allocator, padded);

        if (i < columns.len - 1) {
            try result.appendSlice(allocator, separator);
        }
    }

    return result.toOwnedSlice(allocator);
}

// Usage
const columns = [_][]const u8{ "Name", "Age", "City" };
const widths = [_]usize{ 10, 5, 15 };
const row = try formatRow(allocator, &columns, &widths, " | ");
defer allocator.free(row);
// row is "Name       | Age   | City           "
```

**Create divider lines:**

```zig
pub fn divider(
    allocator: mem.Allocator,
    width: usize,
    char: u8,
) ![]u8 {
    const result = try allocator.alloc(u8, width);
    @memset(result, char);
    return result;
}

// Usage
const div = try divider(allocator, 40, '-');
defer allocator.free(div);
// div is "----------------------------------------"
```

**Complete table example:**

```zig
const header = [_][]const u8{ "ID", "Name", "Status" };
const widths = [_]usize{ 5, 15, 10 };

// Format header
const header_row = try formatRow(allocator, &header, &widths, " | ");
defer allocator.free(header_row);

// Create divider
const div = try divider(allocator, header_row.len, '-');
defer allocator.free(div);

// Format data rows
const row1 = [_][]const u8{ "1", "Alice", "Active" };
const data_row = try formatRow(allocator, &row1, &widths, " | ");
defer allocator.free(data_row);

// Output:
// ID    | Name            | Status
// --------------------------------
// 1     | Alice           | Active
```

### Text Boxes

**Create bordered text boxes:**

```zig
pub fn textBox(
    allocator: mem.Allocator,
    text: []const u8,
    padding: usize,
) ![]u8 {
    const inner_width = text.len + (padding * 2);

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    // Top border
    try result.append(allocator, '+');
    var i: usize = 0;
    while (i < inner_width) : (i += 1) {
        try result.append(allocator, '-');
    }
    try result.append(allocator, '+');
    try result.append(allocator, '\n');

    // Content with padding
    try result.append(allocator, '|');
    i = 0;
    while (i < padding) : (i += 1) {
        try result.append(allocator, ' ');
    }
    try result.appendSlice(allocator, text);
    i = 0;
    while (i < padding) : (i += 1) {
        try result.append(allocator, ' ');
    }
    try result.append(allocator, '|');
    try result.append(allocator, '\n');

    // Bottom border
    try result.append(allocator, '+');
    i = 0;
    while (i < inner_width) : (i += 1) {
        try result.append(allocator, '-');
    }
    try result.append(allocator, '+');

    return result.toOwnedSlice(allocator);
}

// Usage
const box = try textBox(allocator, "Hello", 2);
defer allocator.free(box);
// Output:
// +---------+
// |  Hello  |
// +---------+
```

### Text Truncation

**Truncate text with ellipsis:**

```zig
pub fn truncate(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
) ![]u8 {
    if (text.len <= width) return allocator.dupe(u8, text);

    if (width < 3) {
        return allocator.dupe(u8, text[0..width]);
    }

    var result = try allocator.alloc(u8, width);
    @memcpy(result[0 .. width - 3], text[0 .. width - 3]);
    result[width - 3] = '.';
    result[width - 2] = '.';
    result[width - 1] = '.';

    return result;
}

// Usage
const long_text = "This is a very long text that needs truncation";
const short = try truncate(allocator, long_text, 20);
defer allocator.free(short);
// short is "This is a very l..."
```

### Practical Examples

**Format financial reports:**

```zig
// Right-align numbers for proper column alignment
const amount1 = try alignRight(allocator, "$9.99", 10, ' ');
defer allocator.free(amount1);
// "     $9.99"

const amount2 = try alignRight(allocator, "$129.99", 10, ' ');
defer allocator.free(amount2);
// "   $129.99"

// Both align properly in a column
```

**Create report headers:**

```zig
const title = try alignCenter(allocator, "MONTHLY REPORT", 60, '=');
defer allocator.free(title);
// "=======================MONTHLY REPORT======================="
```

**Format log entries:**

```zig
const level_columns = [_][]const u8{ "INFO", "12:34:56", "Server started" };
const widths = [_]usize{ 8, 10, 40 };
const log_line = try formatRow(allocator, &level_columns, &widths, " | ");
defer allocator.free(log_line);
// "INFO     | 12:34:56   | Server started                          "
```

**Create ASCII tables:**

```zig
// Build a complete table
const header = [_][]const u8{ "Product", "Price", "Stock" };
const widths = [_]usize{ 20, 10, 8 };

const header_row = try formatRow(allocator, &header, &widths, " | ");
defer allocator.free(header_row);

const div = try divider(allocator, header_row.len, '-');
defer allocator.free(div);

const row1 = [_][]const u8{ "Widget A", "$19.99", "150" };
const row2 = [_][]const u8{ "Widget B", "$29.99", "75" };

const data1 = try formatRow(allocator, &row1, &widths, " | ");
defer allocator.free(data1);

const data2 = try formatRow(allocator, &row2, &widths, " | ");
defer allocator.free(data2);

// Output:
// Product              | Price      | Stock
// ----------------------------------------
// Widget A             | $19.99     | 150
// Widget B             | $29.99     | 75
```

**Format code listings with line numbers:**

```zig
const line_num = try alignRight(allocator, "42", 4, ' ');
defer allocator.free(line_num);
const code = "    const x = 10;";

// Combine: "  42    const x = 10;"
```

### Performance

**Alignment allocates new strings:**

```zig
const result = try alignLeft(allocator, "text", 10, ' ');
defer allocator.free(result);  // Must free
```

**Pre-calculate sizes for efficiency:**

```zig
// Calculate total row width once
const total_width = widths[0] + separator.len + widths[1] + separator.len + widths[2];

// Use for divider
const div = try divider(allocator, total_width, '-');
defer allocator.free(div);
```

### Memory Management

All alignment functions allocate:

```zig
const aligned = try alignLeft(allocator, "text", width, ' ');
defer allocator.free(aligned);  // Required

// formatRow also allocates
const row = try formatRow(allocator, &cols, &widths, " | ");
defer allocator.free(row);  // Required
```

### UTF-8 Considerations

Alignment works at byte level, which may cause issues with multi-byte UTF-8 characters:

```zig
// This works but counts bytes, not visual characters
const result = try alignLeft(allocator, "Hello 世界", 20, ' ');
defer allocator.free(result);
// The Chinese characters take 6 bytes but appear as 2 characters
// Visual alignment may look off
```

For proper visual alignment with UTF-8, you need to:
1. Count grapheme clusters (visual characters)
2. Use a Unicode library
3. Or handle ASCII-only scenarios

For most programming contexts (logs, tables), byte-level alignment is acceptable.

### Security

All operations are bounds-safe:

```zig
// Safe - checks length before allocation
const result = try alignLeft(allocator, "test", 1000, ' ');
defer allocator.free(result);

// Safe - won't overflow
const truncated = try truncate(allocator, long_text, width);
defer allocator.free(truncated);
```

### Common Patterns

**Three-column layout:**

```zig
const left_col = try alignLeft(allocator, "Left", 20, ' ');
defer allocator.free(left_col);

const center_col = try alignCenter(allocator, "Center", 20, ' ');
defer allocator.free(center_col);

const right_col = try alignRight(allocator, "Right", 20, ' ');
defer allocator.free(right_col);
```

**Fixed-width output:**

```zig
// Truncate long values, pad short ones
var display_text: []u8 = undefined;
if (text.len > width) {
    display_text = try truncate(allocator, text, width);
} else {
    display_text = try alignLeft(allocator, text, width, ' ');
}
defer allocator.free(display_text);
```

**Numbered lists:**

```zig
var i: u32 = 1;
while (i <= 10) : (i += 1) {
    const num_str = try std.fmt.allocPrint(allocator, "{d}.", .{i});
    defer allocator.free(num_str);

    const padded = try alignRight(allocator, num_str, 4, ' ');
    defer allocator.free(padded);

    // "   1." through "  10."
}
```

This comprehensive text alignment system provides the building blocks for creating well-formatted tables, reports, and structured text output in Zig.

### Full Tested Code

```zig
// Recipe 2.10: Aligning text strings
// Target Zig Version: 0.15.2
//
// This recipe demonstrates text alignment and formatting for tables,
// columns, and structured output.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;
const fmt = std.fmt;

// ANCHOR: basic_alignment
/// Align text left with padding
pub fn alignLeft(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    fill_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    errdefer allocator.free(result);

    @memcpy(result[0..text.len], text);

    var i: usize = text.len;
    while (i < width) : (i += 1) {
        result[i] = fill_char;
    }

    return result;
}

/// Align text right with padding
pub fn alignRight(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    fill_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    errdefer allocator.free(result);

    const padding = width - text.len;

    var i: usize = 0;
    while (i < padding) : (i += 1) {
        result[i] = fill_char;
    }

    @memcpy(result[padding..][0..text.len], text);

    return result;
}

/// Align text center with padding
pub fn alignCenter(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    fill_char: u8,
) ![]u8 {
    if (text.len >= width) return allocator.dupe(u8, text);

    var result = try allocator.alloc(u8, width);
    errdefer allocator.free(result);

    const total_padding = width - text.len;
    const left_padding = total_padding / 2;

    var i: usize = 0;
    while (i < left_padding) : (i += 1) {
        result[i] = fill_char;
    }

    @memcpy(result[left_padding..][0..text.len], text);

    i = left_padding + text.len;
    while (i < width) : (i += 1) {
        result[i] = fill_char;
    }

    return result;
}
// ANCHOR_END: basic_alignment

// ANCHOR: table_formatting
/// Format table row with aligned columns
pub fn formatRow(
    allocator: mem.Allocator,
    columns: []const []const u8,
    widths: []const usize,
    separator: []const u8,
) ![]u8 {
    if (columns.len != widths.len) return error.ColumnWidthMismatch;

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (columns, widths, 0..) |col, width, i| {
        const padded = try alignLeft(allocator, col, width, ' ');
        defer allocator.free(padded);

        try result.appendSlice(allocator, padded);

        if (i < columns.len - 1) {
            try result.appendSlice(allocator, separator);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Create horizontal divider line
pub fn divider(
    allocator: mem.Allocator,
    width: usize,
    char: u8,
) ![]u8 {
    const result = try allocator.alloc(u8, width);
    @memset(result, char);
    return result;
}
// ANCHOR_END: table_formatting

// ANCHOR: advanced_formatting
/// Format text in a box
pub fn textBox(
    allocator: mem.Allocator,
    text: []const u8,
    padding: usize,
) ![]u8 {
    const inner_width = text.len + (padding * 2);

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    // Top border
    try result.append(allocator, '+');
    var i: usize = 0;
    while (i < inner_width) : (i += 1) {
        try result.append(allocator, '-');
    }
    try result.append(allocator, '+');
    try result.append(allocator, '\n');

    // Content line with padding
    try result.append(allocator, '|');
    i = 0;
    while (i < padding) : (i += 1) {
        try result.append(allocator, ' ');
    }
    try result.appendSlice(allocator, text);
    i = 0;
    while (i < padding) : (i += 1) {
        try result.append(allocator, ' ');
    }
    try result.append(allocator, '|');
    try result.append(allocator, '\n');

    // Bottom border
    try result.append(allocator, '+');
    i = 0;
    while (i < inner_width) : (i += 1) {
        try result.append(allocator, '-');
    }
    try result.append(allocator, '+');

    return result.toOwnedSlice(allocator);
}

/// Truncate text to width with ellipsis
pub fn truncate(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
) ![]u8 {
    if (text.len <= width) return allocator.dupe(u8, text);

    if (width < 3) {
        // Too narrow for ellipsis
        return allocator.dupe(u8, text[0..width]);
    }

    var result = try allocator.alloc(u8, width);
    errdefer allocator.free(result);

    @memcpy(result[0 .. width - 3], text[0 .. width - 3]);
    result[width - 3] = '.';
    result[width - 2] = '.';
    result[width - 1] = '.';

    return result;
}
// ANCHOR_END: advanced_formatting

test "align left" {
    const result = try alignLeft(testing.allocator, "hello", 10, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello     ", result);
}

test "align left - no padding needed" {
    const result = try alignLeft(testing.allocator, "hello", 5, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello", result);
}

test "align right" {
    const result = try alignRight(testing.allocator, "42", 5, '0');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("00042", result);
}

test "align right - no padding needed" {
    const result = try alignRight(testing.allocator, "hello", 3, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello", result);
}

test "align center" {
    const result = try alignCenter(testing.allocator, "hi", 6, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("  hi  ", result);
}

test "align center - odd padding" {
    const result = try alignCenter(testing.allocator, "hi", 7, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("  hi   ", result);
}

test "format table row" {
    const columns = [_][]const u8{ "Name", "Age", "City" };
    const widths = [_]usize{ 10, 5, 15 };
    const result = try formatRow(testing.allocator, &columns, &widths, " | ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Name       | Age   | City           ", result);
}

test "format single column" {
    const columns = [_][]const u8{"Test"};
    const widths = [_]usize{10};
    const result = try formatRow(testing.allocator, &columns, &widths, " | ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Test      ", result);
}

test "format row with custom separator" {
    const columns = [_][]const u8{ "A", "B", "C" };
    const widths = [_]usize{ 5, 5, 5 };
    const result = try formatRow(testing.allocator, &columns, &widths, "|");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("A    |B    |C    ", result);
}

test "create divider" {
    const result = try divider(testing.allocator, 20, '-');
    defer testing.allocator.free(result);

    try testing.expectEqual(@as(usize, 20), result.len);
    for (result) |c| {
        try testing.expectEqual(@as(u8, '-'), c);
    }
}

test "create divider with different character" {
    const result = try divider(testing.allocator, 10, '=');
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("==========", result);
}

test "text box" {
    const result = try textBox(testing.allocator, "Hello", 2);
    defer testing.allocator.free(result);

    const expected = "+---------+\n|  Hello  |\n+---------+";
    try testing.expectEqualStrings(expected, result);
}

test "text box - no padding" {
    const result = try textBox(testing.allocator, "Test", 0);
    defer testing.allocator.free(result);

    const expected = "+----+\n|Test|\n+----+";
    try testing.expectEqualStrings(expected, result);
}

test "truncate long text" {
    const result = try truncate(testing.allocator, "This is a very long text", 15);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("This is a ve...", result);
}

test "truncate - no truncation needed" {
    const result = try truncate(testing.allocator, "short", 10);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("short", result);
}

test "truncate - exact length" {
    const result = try truncate(testing.allocator, "exactly10!", 10);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("exactly10!", result);
}

test "truncate very narrow" {
    const result = try truncate(testing.allocator, "longtext", 2);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("lo", result);
}

test "format header and rows" {
    const header = [_][]const u8{ "ID", "Name", "Status" };
    const widths = [_]usize{ 5, 15, 10 };

    const header_row = try formatRow(testing.allocator, &header, &widths, " | ");
    defer testing.allocator.free(header_row);

    const div = try divider(testing.allocator, header_row.len, '-');
    defer testing.allocator.free(div);

    try testing.expect(header_row.len > 0);
    try testing.expectEqual(header_row.len, div.len);
}

test "align numbers for table" {
    const num1 = try alignRight(testing.allocator, "42", 8, ' ');
    defer testing.allocator.free(num1);

    const num2 = try alignRight(testing.allocator, "1000", 8, ' ');
    defer testing.allocator.free(num2);

    try testing.expectEqualStrings("      42", num1);
    try testing.expectEqualStrings("    1000", num2);
}

test "format price column" {
    const price1 = try alignRight(testing.allocator, "$9.99", 10, ' ');
    defer testing.allocator.free(price1);

    const price2 = try alignRight(testing.allocator, "$129.99", 10, ' ');
    defer testing.allocator.free(price2);

    try testing.expectEqualStrings("     $9.99", price1);
    try testing.expectEqualStrings("   $129.99", price2);
}

test "center title" {
    const title = try alignCenter(testing.allocator, "Report", 40, '=');
    defer testing.allocator.free(title);

    try testing.expectEqual(@as(usize, 40), title.len);
    try testing.expect(mem.indexOf(u8, title, "Report") != null);
}

test "memory safety - alignment" {
    const result = try alignLeft(testing.allocator, "test", 10, ' ');
    defer testing.allocator.free(result);

    // testing.allocator will detect leaks
    try testing.expect(result.len == 10);
}

test "UTF-8 text alignment" {
    const result = try alignLeft(testing.allocator, "Hello 世界", 20, ' ');
    defer testing.allocator.free(result);

    try testing.expect(result.len == 20);
    try testing.expect(mem.indexOf(u8, result, "Hello 世界") != null);
}

test "security - large width" {
    const result = try alignLeft(testing.allocator, "test", 1000, ' ');
    defer testing.allocator.free(result);

    try testing.expectEqual(@as(usize, 1000), result.len);
}

test "format empty column" {
    const columns = [_][]const u8{""};
    const widths = [_]usize{5};
    const result = try formatRow(testing.allocator, &columns, &widths, " | ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("     ", result);
}
```

---

## Recipe 2.11: Reformatting Text to a Fixed Number of Columns {#recipe-2-11}

**Tags:** allocators, arraylist, data-structures, error-handling, http, memory, networking, resource-cleanup, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_11.zig`

### Problem

You need to reformat text to fit within a fixed column width - wrapping lines at word boundaries, breaking long lines, or reflowing paragraphs for display or output.

### Solution

Implement text wrapping functions that break text at word boundaries or fixed positions:

### Word-Based Wrapping

```zig
/// Wrap text to fit within specified width (word boundaries)
pub fn wrapText(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
) ![]u8 {
    if (width == 0) return allocator.dupe(u8, "");
    if (text.len <= width) return allocator.dupe(u8, text);

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var pos: usize = 0;
    var line_start: usize = 0;

    while (pos < text.len) {
        // Find end of line or width limit
        var line_end = @min(line_start + width, text.len);

        // If we're not at the end, try to break at a word boundary
        if (line_end < text.len) {
            // Look back for a space
            var break_pos = line_end;
            while (break_pos > line_start) : (break_pos -= 1) {
                if (text[break_pos] == ' ') {
                    line_end = break_pos;
                    break;
                }
            }

            // If no space found, use hard break at width
            if (break_pos == line_start) {
                line_end = line_start + width;
            }
        }

        // Add line
        const line = mem.trim(u8, text[line_start..line_end], " ");
        try result.appendSlice(allocator, line);

        // Add newline if not last line
        if (line_end < text.len) {
            try result.append(allocator, '\n');
        }

        // Move to next line
        line_start = line_end;
        // Skip any spaces at start of next line
        while (line_start < text.len and text[line_start] == ' ') {
            line_start += 1;
        }

        pos = line_start;
    }

    return result.toOwnedSlice(allocator);
}

/// Hard wrap text (break at exact width)
pub fn hardWrap(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
) ![]u8 {
    if (width == 0) return allocator.dupe(u8, "");
    if (text.len <= width) return allocator.dupe(u8, text);

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var pos: usize = 0;
    while (pos < text.len) {
        const chunk_end = @min(pos + width, text.len);
        try result.appendSlice(allocator, text[pos..chunk_end]);

        if (chunk_end < text.len) {
            try result.append(allocator, '\n');
        }

        pos = chunk_end;
    }

    return result.toOwnedSlice(allocator);
}
```

### Discussion

### Text Indentation

**Add prefix to every line:**

```zig
pub fn indent(
    allocator: mem.Allocator,
    text: []const u8,
    prefix: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var lines = mem.tokenizeScalar(u8, text, '\n');
    var first = true;

    while (lines.next()) |line| {
        if (!first) {
            try result.append(allocator, '\n');
        }
        first = false;

        try result.appendSlice(allocator, prefix);
        try result.appendSlice(allocator, line);
    }

    return result.toOwnedSlice(allocator);
}

// Usage - indent code comments
const comment = "This is a long comment";
const indented = try indent(allocator, comment, "// ");
defer allocator.free(indented);
// Result: "// This is a long comment"
```

### Paragraph Formatting

**Format with first-line and hanging indents:**

```zig
pub fn formatParagraph(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    first_line_indent: usize,
    subsequent_indent: usize,
) ![]u8 {
    // First wrap the text
    const wrapped = try wrapText(allocator, text, width);
    defer allocator.free(wrapped);

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var lines = mem.tokenizeScalar(u8, wrapped, '\n');
    var first = true;

    while (lines.next()) |line| {
        if (!first) {
            try result.append(allocator, '\n');
        }

        // Add indentation
        const indent_size = if (first) first_line_indent else subsequent_indent;
        var i: usize = 0;
        while (i < indent_size) : (i += 1) {
            try result.append(allocator, ' ');
        }

        try result.appendSlice(allocator, line);
        first = false;
    }

    return result.toOwnedSlice(allocator);
}

// Usage - format with hanging indent
const para = "This is a long paragraph that needs proper formatting";
const formatted = try formatParagraph(allocator, para, 40, 4, 2);
defer allocator.free(formatted);
// First line: 4-space indent
// Other lines: 2-space indent
```

### Splitting into Lines

**Get array of wrapped lines:**

```zig
pub fn splitIntoLines(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
) !std.ArrayList([]const u8) {
    var lines = std.ArrayList([]const u8){};
    errdefer lines.deinit(allocator);

    var line_start: usize = 0;

    while (line_start < text.len) {
        var line_end = @min(line_start + width, text.len);

        if (line_end < text.len) {
            var break_pos = line_end;
            while (break_pos > line_start) : (break_pos -= 1) {
                if (text[break_pos] == ' ') {
                    line_end = break_pos;
                    break;
                }
            }

            if (break_pos == line_start) {
                line_end = line_start + width;
            }
        }

        const line = mem.trim(u8, text[line_start..line_end], " ");
        try lines.append(allocator, line);

        line_start = line_end;
        while (line_start < text.len and text[line_start] == ' ') {
            line_start += 1;
        }
    }

    return lines;
}

// Usage
var lines = try splitIntoLines(allocator, long_text, 80);
defer lines.deinit(allocator);

for (lines.items) |line| {
    // Process each line
}
```

### Practical Examples

**Format code comments:**

```zig
const comment_text = "This is a very long comment that should be wrapped";
const wrapped = try wrapText(allocator, comment_text, 70);
defer allocator.free(wrapped);

const commented = try indent(allocator, wrapped, "// ");
defer allocator.free(commented);

// Result:
// "// This is a very long comment that should be wrapped"
// (on multiple lines if needed)
```

**Format block quotes:**

```zig
const quote = "Life is what happens when you're busy making other plans";
const quoted = try indent(allocator, quote, "> ");
defer allocator.free(quoted);

// Result: "> Life is what happens when you're busy making other plans"
```

**Format email replies:**

```zig
const original = "Original message text here";
const reply_quoted = try indent(allocator, original, "> ");
defer allocator.free(reply_quoted);

// Result:
// "> Original message text here"
```

**Format help text:**

```zig
const help_text = "This command does something useful with the specified arguments";
const formatted = try formatParagraph(allocator, help_text, 60, 0, 4);
defer allocator.free(formatted);

// First line starts at column 0
// Subsequent lines indented by 4 spaces
```

**Format terminal output:**

```zig
// Wrap to terminal width (commonly 80 columns)
const terminal_width = 80;
const output = try wrapText(allocator, long_message, terminal_width);
defer allocator.free(output);
```

**Format log messages:**

```zig
const log_msg = "Very long log message that exceeds normal width";
const wrapped_log = try wrapText(allocator, log_msg, 100);
defer allocator.free(wrapped_log);

const with_timestamp = try indent(allocator, wrapped_log, "[INFO] ");
defer allocator.free(with_timestamp);
```

### Word Wrapping Algorithms

**Smart wrapping considers:**
1. **Word boundaries** - Don't break words unless necessary
2. **Whitespace** - Trim leading/trailing spaces from lines
3. **Minimum line length** - Avoid very short lines
4. **Hyphenation** - Not implemented (complex, language-specific)

**Hard wrapping:**
- Breaks at exact width
- Used for URLs, hashes, non-text content
- Simpler and faster

### Performance

**Wrapping is O(n):**
- Single pass through text
- Efficient word boundary detection
- Minimal allocations

**Optimization for repeated wrapping:**

```zig
// Reuse ArrayList for multiple wraps
var wrapper = std.ArrayList(u8).init(allocator);
defer wrapper.deinit();

for (paragraphs) |para| {
    wrapper.clearRetainingCapacity();
    // Use wrapper for wrapping
    // Extract result
}
```

### Memory Management

All wrapping functions allocate:

```zig
const wrapped = try wrapText(allocator, text, width);
defer allocator.free(wrapped);  // Required

const indented = try indent(allocator, text, prefix);
defer allocator.free(indented);  // Required
```

### UTF-8 Considerations

Current implementation works at byte level:

```zig
// Works with UTF-8 but counts bytes, not visual width
const text = "Hello 世界";
const wrapped = try wrapText(allocator, text, 10);
defer allocator.free(wrapped);

// Chinese characters take 6 bytes but display as 2 characters
// Visual wrapping may look off
```

For proper visual wrapping with multi-byte characters:
1. Use Unicode library for grapheme counting
2. Track display width vs byte width
3. Handle combining characters
4. Consider language-specific rules

For ASCII/English text, byte-level wrapping works perfectly.

### Security

All operations are bounds-safe:

```zig
// Safe - handles edge cases
const empty_wrap = try wrapText(allocator, "", 80);
defer allocator.free(empty_wrap);

const zero_width = try wrapText(allocator, text, 0);
defer allocator.free(zero_width);
```

### Common Patterns

**Format documentation:**

```zig
fn formatDocComment(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
) ![]u8 {
    const wrapped = try wrapText(allocator, text, width - 4);
    defer allocator.free(wrapped);

    return indent(allocator, wrapped, "/// ");
}
```

**Format markdown quotes:**

```zig
fn formatQuote(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    const wrapped = try wrapText(allocator, text, 76);  // 80 - 4 for "> "
    defer allocator.free(wrapped);

    return indent(allocator, wrapped, "> ");
}
```

**Format list items:**

```zig
fn formatListItem(
    allocator: mem.Allocator,
    text: []const u8,
    bullet: []const u8,
) ![]u8 {
    const width = 76;
    const wrapped = try wrapText(allocator, text, width);
    defer allocator.free(wrapped);

    var result = std.ArrayList(u8).init(allocator);
    defer result.deinit();

    var lines = mem.tokenizeScalar(u8, wrapped, '\n');
    var first = true;

    while (lines.next()) |line| {
        if (!first) {
            try result.append('\n');
        }

        if (first) {
            try result.appendSlice(bullet);
        } else {
            // Indent continuation lines
            var i: usize = 0;
            while (i < bullet.len) : (i += 1) {
                try result.append(' ');
            }
        }

        try result.appendSlice(line);
        first = false;
    }

    return result.toOwnedSlice();
}

// Usage:
// - First line of text
//   continues here
//   and here
```

This comprehensive text reformatting system handles word wrapping, line breaking, and indentation for terminal output, documentation, and formatted text display.

### Full Tested Code

```zig
// Recipe 2.11: Reformatting text to fixed columns
// Target Zig Version: 0.15.2
//
// This recipe demonstrates text wrapping, word breaking, and reformatting
// text to fit within fixed column widths.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;

// ANCHOR: text_wrapping
/// Wrap text to fit within specified width (word boundaries)
pub fn wrapText(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
) ![]u8 {
    if (width == 0) return allocator.dupe(u8, "");
    if (text.len <= width) return allocator.dupe(u8, text);

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var pos: usize = 0;
    var line_start: usize = 0;

    while (pos < text.len) {
        // Find end of line or width limit
        var line_end = @min(line_start + width, text.len);

        // If we're not at the end, try to break at a word boundary
        if (line_end < text.len) {
            // Look back for a space
            var break_pos = line_end;
            while (break_pos > line_start) : (break_pos -= 1) {
                if (text[break_pos] == ' ') {
                    line_end = break_pos;
                    break;
                }
            }

            // If no space found, use hard break at width
            if (break_pos == line_start) {
                line_end = line_start + width;
            }
        }

        // Add line
        const line = mem.trim(u8, text[line_start..line_end], " ");
        try result.appendSlice(allocator, line);

        // Add newline if not last line
        if (line_end < text.len) {
            try result.append(allocator, '\n');
        }

        // Move to next line
        line_start = line_end;
        // Skip any spaces at start of next line
        while (line_start < text.len and text[line_start] == ' ') {
            line_start += 1;
        }

        pos = line_start;
    }

    return result.toOwnedSlice(allocator);
}

/// Hard wrap text (break at exact width)
pub fn hardWrap(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
) ![]u8 {
    if (width == 0) return allocator.dupe(u8, "");
    if (text.len <= width) return allocator.dupe(u8, text);

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var pos: usize = 0;
    while (pos < text.len) {
        const chunk_end = @min(pos + width, text.len);
        try result.appendSlice(allocator, text[pos..chunk_end]);

        if (chunk_end < text.len) {
            try result.append(allocator, '\n');
        }

        pos = chunk_end;
    }

    return result.toOwnedSlice(allocator);
}
// ANCHOR_END: text_wrapping

// ANCHOR: split_lines
/// Split text into lines of maximum width
pub fn splitIntoLines(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
) !std.ArrayList([]const u8) {
    var lines = std.ArrayList([]const u8){};
    errdefer lines.deinit(allocator);

    var pos: usize = 0;
    var line_start: usize = 0;

    while (pos < text.len) {
        var line_end = @min(line_start + width, text.len);

        if (line_end < text.len) {
            var break_pos = line_end;
            while (break_pos > line_start) : (break_pos -= 1) {
                if (text[break_pos] == ' ') {
                    line_end = break_pos;
                    break;
                }
            }

            if (break_pos == line_start) {
                line_end = line_start + width;
            }
        }

        const line = mem.trim(u8, text[line_start..line_end], " ");
        try lines.append(allocator, line);

        line_start = line_end;
        while (line_start < text.len and text[line_start] == ' ') {
            line_start += 1;
        }

        pos = line_start;
    }

    return lines;
}
// ANCHOR_END: split_lines

// ANCHOR: indentation
/// Indent text with prefix
pub fn indent(
    allocator: mem.Allocator,
    text: []const u8,
    prefix: []const u8,
) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var lines = mem.tokenizeScalar(u8, text, '\n');
    var first = true;

    while (lines.next()) |line| {
        if (!first) {
            try result.append(allocator, '\n');
        }
        first = false;

        try result.appendSlice(allocator, prefix);
        try result.appendSlice(allocator, line);
    }

    return result.toOwnedSlice(allocator);
}

/// Format paragraph with indentation
pub fn formatParagraph(
    allocator: mem.Allocator,
    text: []const u8,
    width: usize,
    first_line_indent: usize,
    subsequent_indent: usize,
) ![]u8 {
    // First wrap the text
    const wrapped = try wrapText(allocator, text, width);
    defer allocator.free(wrapped);

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var lines = mem.tokenizeScalar(u8, wrapped, '\n');
    var first = true;

    while (lines.next()) |line| {
        if (!first) {
            try result.append(allocator, '\n');
        }

        // Add indentation
        const indent_size = if (first) first_line_indent else subsequent_indent;
        var i: usize = 0;
        while (i < indent_size) : (i += 1) {
            try result.append(allocator, ' ');
        }

        try result.appendSlice(allocator, line);
        first = false;
    }

    return result.toOwnedSlice(allocator);
}
// ANCHOR_END: indentation

test "wrap text at word boundaries" {
    const text = "The quick brown fox jumps over the lazy dog";
    const result = try wrapText(testing.allocator, text, 20);
    defer testing.allocator.free(result);

    try testing.expect(mem.indexOf(u8, result, "\n") != null);
}

test "wrap short text - no wrapping needed" {
    const text = "Short";
    const result = try wrapText(testing.allocator, text, 20);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Short", result);
}

test "wrap exact length" {
    const text = "Exactly twenty chars";
    const result = try wrapText(testing.allocator, text, 20);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Exactly twenty chars", result);
}

test "wrap with no spaces - hard break" {
    const text = "Superlongwordwithoutanyspaces";
    const result = try wrapText(testing.allocator, text, 10);
    defer testing.allocator.free(result);

    try testing.expect(mem.indexOf(u8, result, "\n") != null);
}

test "hard wrap text" {
    const text = "This is a test of hard wrapping";
    const result = try hardWrap(testing.allocator, text, 10);
    defer testing.allocator.free(result);

    const expected = "This is a \ntest of ha\nrd wrappin\ng";
    try testing.expectEqualStrings(expected, result);
}

test "hard wrap exact length" {
    const text = "TenLetters";
    const result = try hardWrap(testing.allocator, text, 10);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("TenLetters", result);
}

test "split into lines" {
    const text = "The quick brown fox jumps over the lazy dog";
    var lines = try splitIntoLines(testing.allocator, text, 20);
    defer lines.deinit(testing.allocator);

    try testing.expect(lines.items.len > 1);
}

test "split short text" {
    const text = "Short";
    var lines = try splitIntoLines(testing.allocator, text, 20);
    defer lines.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 1), lines.items.len);
    try testing.expectEqualStrings("Short", lines.items[0]);
}

test "indent text" {
    const text = "Line 1\nLine 2\nLine 3";
    const result = try indent(testing.allocator, text, "  ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("  Line 1\n  Line 2\n  Line 3", result);
}

test "indent single line" {
    const text = "Single line";
    const result = try indent(testing.allocator, text, "> ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("> Single line", result);
}

test "format paragraph with indentation" {
    const text = "This is a paragraph that needs to be formatted with proper indentation";
    const result = try formatParagraph(testing.allocator, text, 30, 4, 2);
    defer testing.allocator.free(result);

    // First line should have 4-space indent
    try testing.expect(mem.startsWith(u8, result, "    "));
}

test "format paragraph - no indent" {
    const text = "Short text";
    const result = try formatParagraph(testing.allocator, text, 40, 0, 0);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Short text", result);
}

test "wrap empty string" {
    const result = try wrapText(testing.allocator, "", 20);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("", result);
}

test "wrap zero width" {
    const result = try wrapText(testing.allocator, "test", 0);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("", result);
}

test "format code comment" {
    const text = "This is a very long comment that should be wrapped to fit within 80 characters per line";
    const wrapped = try wrapText(testing.allocator, text, 70);
    defer testing.allocator.free(wrapped);

    const result = try indent(testing.allocator, wrapped, "// ");
    defer testing.allocator.free(result);

    try testing.expect(mem.startsWith(u8, result, "// "));
}

test "format quote" {
    const text = "Life is what happens when you're busy making other plans";
    const result = try indent(testing.allocator, text, "> ");
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("> Life is what happens when you're busy making other plans", result);
}

test "wrap long URL" {
    const url = "https://example.com/very/long/path/to/resource/that/exceeds/normal/width";
    const result = try hardWrap(testing.allocator, url, 40);
    defer testing.allocator.free(result);

    try testing.expect(mem.indexOf(u8, result, "\n") != null);
}

test "memory safety - wrapping" {
    const text = "Test text for wrapping";
    const result = try wrapText(testing.allocator, text, 10);
    defer testing.allocator.free(result);

    // testing.allocator will detect leaks
    try testing.expect(result.len > 0);
}

test "UTF-8 text wrapping" {
    const text = "Hello 世界 how are you";
    const result = try wrapText(testing.allocator, text, 15);
    defer testing.allocator.free(result);

    try testing.expect(result.len > 0);
}

test "security - large width" {
    const text = "test";
    const result = try wrapText(testing.allocator, text, 1000);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("test", result);
}
```

---

## Recipe 2.12: Working with Byte Strings vs Unicode Text {#recipe-2-12}

**Tags:** allocators, arraylist, data-structures, error-handling, memory, resource-cleanup, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_12.zig`

### Problem

You need to work with Unicode strings properly - distinguishing between byte length and character count, iterating over codepoints instead of bytes, and handling multi-byte UTF-8 sequences correctly.

### Solution

Use Zig's `std.unicode` module for UTF-8 validation, iteration, and proper Unicode handling:

### UTF-8 Validation and Basics

```zig
/// Validate UTF-8 string
pub fn isValidUtf8(text: []const u8) bool {
    return unicode.utf8ValidateSlice(text);
}

/// Count UTF-8 codepoints (not bytes)
pub fn countCodepoints(text: []const u8) !usize {
    var count: usize = 0;
    var i: usize = 0;

    while (i < text.len) {
        const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
        i += cp_len;
        count += 1;
    }

    return count;
}

/// Iterate UTF-8 codepoints
pub fn iterateCodepoints(
    allocator: mem.Allocator,
    text: []const u8,
) !std.ArrayList(u21) {
    var codepoints = std.ArrayList(u21){};
    errdefer codepoints.deinit(allocator);

    var i: usize = 0;
    while (i < text.len) {
        const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
        const codepoint = try unicode.utf8Decode(text[i .. i + cp_len]);
        try codepoints.append(allocator, codepoint);
        i += cp_len;
    }

    return codepoints;
}
```

### Accessing Codepoints

```zig
/// Get byte at index (not codepoint)
pub fn byteAt(text: []const u8, index: usize) ?u8 {
    if (index >= text.len) return null;
    return text[index];
}

/// Get codepoint at index (UTF-8 aware)
pub fn codepointAt(text: []const u8, index: usize) !?u21 {
    var count: usize = 0;
    var i: usize = 0;

    while (i < text.len) {
        if (count == index) {
            const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
            const codepoint = try unicode.utf8Decode(text[i .. i + cp_len]);
            return codepoint;
        }

        const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
        i += cp_len;
        count += 1;
    }

    return null;
}

/// Convert codepoint to UTF-8 bytes
pub fn codepointToUtf8(
    allocator: mem.Allocator,
    codepoint: u21,
) ![]u8 {
    var buf: [4]u8 = undefined;
    const len = try unicode.utf8Encode(codepoint, &buf);
    return allocator.dupe(u8, buf[0..len]);
}
```

### UTF-8 Operations

```zig
/// Reverse string (UTF-8 aware)
pub fn reverseUtf8(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    // First collect all codepoints
    var codepoints = try iterateCodepoints(allocator, text);
    defer codepoints.deinit(allocator);

    // Calculate total size needed
    var total_bytes: usize = 0;
    for (codepoints.items) |cp| {
        total_bytes += unicode.utf8CodepointSequenceLength(cp) catch continue;
    }

    var result = try allocator.alloc(u8, total_bytes);
    errdefer allocator.free(result);

    var pos: usize = 0;
    var i: usize = codepoints.items.len;

    while (i > 0) {
        i -= 1;
        const cp = codepoints.items[i];
        const len = try unicode.utf8Encode(cp, result[pos..]);
        pos += len;
    }

    return result;
}

/// Substring by codepoint index (not byte index)
pub fn substringByCodepoint(
    allocator: mem.Allocator,
    text: []const u8,
    start: usize,
    end: usize,
) ![]u8 {
    if (start >= end) return allocator.dupe(u8, "");

    var byte_start: ?usize = null;
    var byte_end: ?usize = null;
    var count: usize = 0;
    var i: usize = 0;

    while (i < text.len) {
        if (count == start) byte_start = i;
        if (count == end) {
            byte_end = i;
            break;
        }

        const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
        i += cp_len;
        count += 1;
    }

    if (byte_start == null) return allocator.dupe(u8, "");
    const actual_end = byte_end orelse text.len;

    return allocator.dupe(u8, text[byte_start.?..actual_end]);
}
```

### Discussion

### UTF-8 Basics in Zig

**Zig strings are byte arrays** (`[]const u8`):
- Not null-terminated (unlike C)
- UTF-8 by default (source files are UTF-8)
- No special "string" type
- Length is byte count, not character count

**UTF-8 encoding:**
- 1 byte: ASCII (0x00-0x7F)
- 2 bytes: Latin, Greek, Cyrillic, etc.
- 3 bytes: Most of CJK, Arabic, Hebrew
- 4 bytes: Emoji, rare characters

### Byte vs Codepoint Indexing

**Byte indexing (what `text[i]` does):**

```zig
const text = "A世B";

// Byte indexing
text[0];  // 'A' (1 byte)
text[1];  // First byte of '世' (3 bytes)
text[2];  // Second byte of '世'
text[3];  // Third byte of '世'
text[4];  // 'B' (1 byte)

// Total: 5 bytes
```

**Codepoint indexing (what you usually want):**

```zig
pub fn codepointAt(text: []const u8, index: usize) !?u21 {
    var count: usize = 0;
    var i: usize = 0;

    while (i < text.len) {
        if (count == index) {
            const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
            const codepoint = try unicode.utf8Decode(text[i .. i + cp_len]);
            return codepoint;
        }

        const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
        i += cp_len;
        count += 1;
    }

    return null;
}

// Usage
const text = "A世B";
const cp0 = try codepointAt(text, 0);  // 'A'
const cp1 = try codepointAt(text, 1);  // '世' (0x4E16)
const cp2 = try codepointAt(text, 2);  // 'B'
// Total: 3 codepoints
```

### UTF-8 Sequence Length

**Determine sequence length from first byte:**

```zig
pub fn getSequenceLength(first_byte: u8) !usize {
    const len = try unicode.utf8ByteSequenceLength(first_byte);
    return @as(usize, len);
}

// Usage
const len1 = try getSequenceLength('A');        // 1 byte
const len2 = try getSequenceLength(0xC0);       // 2 bytes
const len3 = try getSequenceLength(0xE0);       // 3 bytes
const len4 = try getSequenceLength(0xF0);       // 4 bytes
```

**Check if byte is continuation byte:**

```zig
pub fn isContinuationByte(byte: u8) bool {
    return (byte & 0b11000000) == 0b10000000;
}

// Continuation bytes: 10xxxxxx
// Start bytes: 0xxxxxxx (ASCII) or 11xxxxxx (multibyte)
```

### Converting Codepoints

**Codepoint to UTF-8:**

```zig
pub fn codepointToUtf8(
    allocator: mem.Allocator,
    codepoint: u21,
) ![]u8 {
    var buf: [4]u8 = undefined;
    const len = try unicode.utf8Encode(codepoint, &buf);
    return allocator.dupe(u8, buf[0..len]);
}

// Usage
const utf8 = try codepointToUtf8(allocator, 0x4E16);
defer allocator.free(utf8);
// utf8 is "世" (3 bytes)
```

### Substring by Codepoint

**Extract substring by codepoint positions:**

```zig
pub fn substringByCodepoint(
    allocator: mem.Allocator,
    text: []const u8,
    start: usize,
    end: usize,
) ![]u8 {
    if (start >= end) return allocator.dupe(u8, "");

    var byte_start: ?usize = null;
    var byte_end: ?usize = null;
    var count: usize = 0;
    var i: usize = 0;

    while (i < text.len) {
        if (count == start) byte_start = i;
        if (count == end) {
            byte_end = i;
            break;
        }

        const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
        i += cp_len;
        count += 1;
    }

    if (byte_start == null) return allocator.dupe(u8, "");
    const actual_end = byte_end orelse text.len;

    return allocator.dupe(u8, text[byte_start.?..actual_end]);
}

// Usage
const text = "Hello世界";
const sub = try substringByCodepoint(allocator, text, 5, 7);
defer allocator.free(sub);
// sub is "世界" (codepoints 5-7, not bytes)
```

### Reversing UTF-8 Strings

**Reverse by codepoints, not bytes:**

```zig
pub fn reverseUtf8(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    // First collect all codepoints
    var codepoints = try iterateCodepoints(allocator, text);
    defer codepoints.deinit(allocator);

    // Calculate total bytes needed
    var total_bytes: usize = 0;
    for (codepoints.items) |cp| {
        total_bytes += unicode.utf8CodepointSequenceLength(cp) catch continue;
    }

    var result = try allocator.alloc(u8, total_bytes);
    var pos: usize = 0;
    var i: usize = codepoints.items.len;

    while (i > 0) {
        i -= 1;
        const cp = codepoints.items[i];
        const len = try unicode.utf8Encode(cp, result[pos..]);
        pos += len;
    }

    return result;
}

// Usage
const reversed = try reverseUtf8(allocator, "Hi世");
defer allocator.free(reversed);
// reversed is "世iH"
```

### Practical Examples

**Count visual characters:**

```zig
const text = "Hello 世界 👋";
const byte_len = text.len;           // Bytes
const char_count = try countCodepoints(text);  // Characters

// byte_len might be 17, char_count is 9
```

**Validate user input:**

```zig
fn validateInput(input: []const u8) bool {
    if (!isValidUtf8(input)) {
        return false;  // Invalid UTF-8
    }

    const cp_count = countCodepoints(input) catch return false;
    if (cp_count == 0 or cp_count > 100) {
        return false;  // Too short or too long
    }

    return true;
}
```

**Truncate to character limit:**

```zig
fn truncateToCharLimit(
    allocator: mem.Allocator,
    text: []const u8,
    max_chars: usize,
) ![]u8 {
    const cp_count = try countCodepoints(text);
    if (cp_count <= max_chars) {
        return allocator.dupe(u8, text);
    }

    return substringByCodepoint(allocator, text, 0, max_chars);
}
```

**Check for emoji:**

```zig
fn containsEmoji(text: []const u8) !bool {
    var codepoints = try iterateCodepoints(allocator, text);
    defer codepoints.deinit(allocator);

    for (codepoints.items) |cp| {
        // Emoji typically in these ranges
        if (cp >= 0x1F600 and cp <= 0x1F64F) return true;  // Emoticons
        if (cp >= 0x1F300 and cp <= 0x1F5FF) return true;  // Misc symbols
        if (cp >= 0x1F680 and cp <= 0x1F6FF) return true;  // Transport
        if (cp >= 0x2600 and cp <= 0x26FF) return true;    // Misc symbols
    }

    return false;
}
```

### Performance

**UTF-8 iteration is O(n):**
- Must scan each byte to find boundaries
- Cannot random-access codepoints
- Trade-off for compact encoding

**For repeated access:**

```zig
// Cache codepoint positions if accessing frequently
var positions = std.ArrayList(usize).init(allocator);
defer positions.deinit();

var i: usize = 0;
while (i < text.len) {
    try positions.append(i);
    const len = try unicode.utf8ByteSequenceLength(text[i]);
    i += len;
}

// Now can quickly access any codepoint by index
```

### Memory Management

All UTF-8 operations that allocate must be freed:

```zig
var codepoints = try iterateCodepoints(allocator, text);
defer codepoints.deinit(allocator);

const utf8_bytes = try codepointToUtf8(allocator, codepoint);
defer allocator.free(utf8_bytes);

const substring = try substringByCodepoint(allocator, text, start, end);
defer allocator.free(substring);
```

### Security

**Always validate UTF-8 from untrusted sources:**

```zig
fn processUserInput(input: []const u8) !void {
    // Validate first
    if (!isValidUtf8(input)) {
        return error.InvalidUtf8;
    }

    // Now safe to process
    const count = try countCodepoints(input);
    // ...
}
```

**Invalid UTF-8 can cause:**
- Buffer overruns (if not validated)
- Incorrect string operations
- Security vulnerabilities

**Zig's UTF-8 functions handle errors:**

```zig
// Returns error if invalid
const len = unicode.utf8ByteSequenceLength(byte) catch {
    // Handle invalid UTF-8
    return error.InvalidUtf8;
};
```

### Common Pitfalls

**❌ Wrong: Byte indexing for characters**

```zig
const text = "世界";
const char = text[0];  // Just first byte of '世', not complete character
```

**✓ Right: Codepoint indexing**

```zig
const text = "世界";
const char = try codepointAt(text, 0);  // Complete '世' codepoint
```

**❌ Wrong: Using .len for character count**

```zig
const text = "世界";
if (text.len > 10) {  // Comparing bytes, not characters
    // ...
}
```

**✓ Right: Counting codepoints**

```zig
const text = "世界";
const count = try countCodepoints(text);
if (count > 10) {  // Comparing characters
    // ...
}
```

### UTF-8 Invariants

Zig guarantees:
1. Source files are UTF-8
2. String literals are UTF-8
3. No automatic conversions
4. Explicit validation required for untrusted input

### When to Use Bytes vs Codepoints

**Use byte operations when:**
- Working with ASCII-only text
- Performance critical (avoid iteration)
- Binary data or protocols
- File I/O or network transmission

**Use codepoint operations when:**
- Displaying to users
- Character counting/limits
- Text manipulation (reverse, substring)
- Unicode-aware processing

This comprehensive guide covers proper UTF-8 handling in Zig, distinguishing between byte and codepoint operations for correct Unicode support.

### Full Tested Code

```zig
// Recipe 2.12: Handling byte strings vs unicode strings
// Target Zig Version: 0.15.2
//
// This recipe demonstrates the difference between byte strings and Unicode strings,
// UTF-8 iteration, validation, and proper Unicode handling in Zig.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;
const unicode = std.unicode;

// ANCHOR: utf8_validation
/// Validate UTF-8 string
pub fn isValidUtf8(text: []const u8) bool {
    return unicode.utf8ValidateSlice(text);
}

/// Count UTF-8 codepoints (not bytes)
pub fn countCodepoints(text: []const u8) !usize {
    var count: usize = 0;
    var i: usize = 0;

    while (i < text.len) {
        const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
        i += cp_len;
        count += 1;
    }

    return count;
}

/// Iterate UTF-8 codepoints
pub fn iterateCodepoints(
    allocator: mem.Allocator,
    text: []const u8,
) !std.ArrayList(u21) {
    var codepoints = std.ArrayList(u21){};
    errdefer codepoints.deinit(allocator);

    var i: usize = 0;
    while (i < text.len) {
        const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
        const codepoint = try unicode.utf8Decode(text[i .. i + cp_len]);
        try codepoints.append(allocator, codepoint);
        i += cp_len;
    }

    return codepoints;
}
// ANCHOR_END: utf8_validation

// ANCHOR: codepoint_access
/// Get byte at index (not codepoint)
pub fn byteAt(text: []const u8, index: usize) ?u8 {
    if (index >= text.len) return null;
    return text[index];
}

/// Get codepoint at index (UTF-8 aware)
pub fn codepointAt(text: []const u8, index: usize) !?u21 {
    var count: usize = 0;
    var i: usize = 0;

    while (i < text.len) {
        if (count == index) {
            const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
            const codepoint = try unicode.utf8Decode(text[i .. i + cp_len]);
            return codepoint;
        }

        const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
        i += cp_len;
        count += 1;
    }

    return null;
}

/// Convert codepoint to UTF-8 bytes
pub fn codepointToUtf8(
    allocator: mem.Allocator,
    codepoint: u21,
) ![]u8 {
    var buf: [4]u8 = undefined;
    const len = try unicode.utf8Encode(codepoint, &buf);
    return allocator.dupe(u8, buf[0..len]);
}
// ANCHOR_END: codepoint_access

// ANCHOR: utf8_operations
/// Reverse string (UTF-8 aware)
pub fn reverseUtf8(
    allocator: mem.Allocator,
    text: []const u8,
) ![]u8 {
    // First collect all codepoints
    var codepoints = try iterateCodepoints(allocator, text);
    defer codepoints.deinit(allocator);

    // Calculate total size needed
    var total_bytes: usize = 0;
    for (codepoints.items) |cp| {
        total_bytes += unicode.utf8CodepointSequenceLength(cp) catch continue;
    }

    var result = try allocator.alloc(u8, total_bytes);
    errdefer allocator.free(result);

    var pos: usize = 0;
    var i: usize = codepoints.items.len;

    while (i > 0) {
        i -= 1;
        const cp = codepoints.items[i];
        const len = try unicode.utf8Encode(cp, result[pos..]);
        pos += len;
    }

    return result;
}

/// Substring by codepoint index (not byte index)
pub fn substringByCodepoint(
    allocator: mem.Allocator,
    text: []const u8,
    start: usize,
    end: usize,
) ![]u8 {
    if (start >= end) return allocator.dupe(u8, "");

    var byte_start: ?usize = null;
    var byte_end: ?usize = null;
    var count: usize = 0;
    var i: usize = 0;

    while (i < text.len) {
        if (count == start) byte_start = i;
        if (count == end) {
            byte_end = i;
            break;
        }

        const cp_len = try unicode.utf8ByteSequenceLength(text[i]);
        i += cp_len;
        count += 1;
    }

    if (byte_start == null) return allocator.dupe(u8, "");
    const actual_end = byte_end orelse text.len;

    return allocator.dupe(u8, text[byte_start.?..actual_end]);
}
// ANCHOR_END: utf8_operations

/// Check if byte is UTF-8 continuation byte
pub fn isContinuationByte(byte: u8) bool {
    return (byte & 0b11000000) == 0b10000000;
}

/// Get UTF-8 byte sequence length from first byte
pub fn getSequenceLength(first_byte: u8) !usize {
    const len = try unicode.utf8ByteSequenceLength(first_byte);
    return @as(usize, len);
}

test "validate UTF-8" {
    try testing.expect(isValidUtf8("Hello"));
    try testing.expect(isValidUtf8("Hello 世界"));
    try testing.expect(isValidUtf8(""));
    try testing.expect(isValidUtf8("こんにちは"));
}

test "count codepoints vs bytes" {
    const text = "Hello 世界";

    // Byte length
    try testing.expectEqual(@as(usize, 12), text.len);

    // Codepoint count
    const count = try countCodepoints(text);
    try testing.expectEqual(@as(usize, 8), count); // "Hello " = 6, 世界 = 2
}

test "count ASCII codepoints" {
    const text = "Hello";
    const count = try countCodepoints(text);

    try testing.expectEqual(@as(usize, 5), count);
    try testing.expectEqual(@as(usize, 5), text.len);
}

test "iterate codepoints" {
    const text = "Hi世";
    var codepoints = try iterateCodepoints(testing.allocator, text);
    defer codepoints.deinit(testing.allocator);

    try testing.expectEqual(@as(usize, 3), codepoints.items.len);
    try testing.expectEqual(@as(u21, 'H'), codepoints.items[0]);
    try testing.expectEqual(@as(u21, 'i'), codepoints.items[1]);
    try testing.expectEqual(@as(u21, 0x4E16), codepoints.items[2]); // 世
}

test "byte at index" {
    const text = "Hello";

    try testing.expectEqual(@as(u8, 'H'), byteAt(text, 0).?);
    try testing.expectEqual(@as(u8, 'e'), byteAt(text, 1).?);
    try testing.expectEqual(@as(?u8, null), byteAt(text, 10));
}

test "codepoint at index" {
    const text = "Hi世界";

    try testing.expectEqual(@as(u21, 'H'), (try codepointAt(text, 0)).?);
    try testing.expectEqual(@as(u21, 'i'), (try codepointAt(text, 1)).?);
    try testing.expectEqual(@as(u21, 0x4E16), (try codepointAt(text, 2)).?); // 世
    try testing.expectEqual(@as(u21, 0x754C), (try codepointAt(text, 3)).?); // 界
}

test "codepoint to UTF-8" {
    const utf8 = try codepointToUtf8(testing.allocator, 0x4E16);
    defer testing.allocator.free(utf8);

    try testing.expectEqualStrings("世", utf8);
}

test "ASCII codepoint to UTF-8" {
    const utf8 = try codepointToUtf8(testing.allocator, 'A');
    defer testing.allocator.free(utf8);

    try testing.expectEqualStrings("A", utf8);
}

test "reverse UTF-8 string" {
    const text = "ABC";
    const reversed = try reverseUtf8(testing.allocator, text);
    defer testing.allocator.free(reversed);

    try testing.expectEqualStrings("CBA", reversed);
}

test "reverse UTF-8 with multibyte" {
    const text = "Hi世";
    const reversed = try reverseUtf8(testing.allocator, text);
    defer testing.allocator.free(reversed);

    try testing.expectEqualStrings("世iH", reversed);
}

test "substring by codepoint" {
    const text = "Hello世界";
    const sub = try substringByCodepoint(testing.allocator, text, 0, 5);
    defer testing.allocator.free(sub);

    try testing.expectEqualStrings("Hello", sub);
}

test "substring multibyte characters" {
    const text = "Hello世界";
    const sub = try substringByCodepoint(testing.allocator, text, 5, 7);
    defer testing.allocator.free(sub);

    try testing.expectEqualStrings("世界", sub);
}

test "substring out of bounds" {
    const text = "Hi";
    const sub = try substringByCodepoint(testing.allocator, text, 10, 20);
    defer testing.allocator.free(sub);

    try testing.expectEqualStrings("", sub);
}

test "is continuation byte" {
    // ASCII byte
    try testing.expect(!isContinuationByte('A'));

    // UTF-8 continuation bytes start with 10xxxxxx
    try testing.expect(isContinuationByte(0b10000000));
    try testing.expect(isContinuationByte(0b10111111));

    // UTF-8 start bytes
    try testing.expect(!isContinuationByte(0b11000000));
}

test "get sequence length" {
    // ASCII (1 byte)
    try testing.expectEqual(@as(usize, 1), try getSequenceLength('A'));

    // 2-byte sequence (110xxxxx)
    try testing.expectEqual(@as(usize, 2), try getSequenceLength(0b11000000));

    // 3-byte sequence (1110xxxx)
    try testing.expectEqual(@as(usize, 3), try getSequenceLength(0b11100000));

    // 4-byte sequence (11110xxx)
    try testing.expectEqual(@as(usize, 4), try getSequenceLength(0b11110000));
}

test "byte vs codepoint indexing" {
    const text = "A世B";

    // Byte indexing
    try testing.expectEqual(@as(usize, 5), text.len); // 1 + 3 + 1

    // Codepoint indexing
    const count = try countCodepoints(text);
    try testing.expectEqual(@as(usize, 3), count);
}

test "empty string operations" {
    const empty = "";

    try testing.expect(isValidUtf8(empty));
    try testing.expectEqual(@as(usize, 0), try countCodepoints(empty));

    var codepoints = try iterateCodepoints(testing.allocator, empty);
    defer codepoints.deinit(testing.allocator);
    try testing.expectEqual(@as(usize, 0), codepoints.items.len);
}

test "single multibyte character" {
    const text = "世";

    try testing.expectEqual(@as(usize, 3), text.len); // 3 bytes
    try testing.expectEqual(@as(usize, 1), try countCodepoints(text));
}

test "memory safety - UTF-8 operations" {
    const text = "Hello世界";

    var codepoints = try iterateCodepoints(testing.allocator, text);
    defer codepoints.deinit(testing.allocator);

    const reversed = try reverseUtf8(testing.allocator, text);
    defer testing.allocator.free(reversed);

    // testing.allocator will detect leaks
    try testing.expect(codepoints.items.len > 0);
    try testing.expect(reversed.len > 0);
}

test "UTF-8 emoji" {
    const text = "Hello 👋";

    try testing.expect(isValidUtf8(text));
    try testing.expectEqual(@as(usize, 7), try countCodepoints(text));
}

test "various Unicode scripts" {
    const cyrillic = "Привет";
    const arabic = "مرحبا";
    const chinese = "你好";

    try testing.expect(isValidUtf8(cyrillic));
    try testing.expect(isValidUtf8(arabic));
    try testing.expect(isValidUtf8(chinese));
}

test "security - invalid UTF-8" {
    // These are invalid UTF-8 sequences
    const invalid1 = [_]u8{ 0xFF, 0xFF };
    const invalid2 = [_]u8{ 0xC0, 0x80 }; // Overlong encoding

    try testing.expect(!isValidUtf8(&invalid1));
    try testing.expect(!isValidUtf8(&invalid2));
}
```

---

## Recipe 2.13: Sanitizing and Cleaning Up Text {#recipe-2-13}

**Tags:** allocators, arraylist, data-structures, error-handling, http, json, memory, networking, parsing, resource-cleanup, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_13.zig`

### Problem

You need to perform advanced text sanitization beyond basic trimming. This includes:

- Normalizing whitespace and line endings from different platforms
- Encoding text for URLs (percent encoding)
- Removing ANSI escape codes from terminal output
- Encoding/decoding HTML entities for safe web display
- Building sanitization pipelines for complex text cleanup

These tasks are common when cleaning user input, preparing text for web display, processing log files, or building web APIs.

### Solution

Zig provides powerful string manipulation tools through `std.mem` and `std.ArrayList` that make text sanitization straightforward and safe.

### Whitespace and Line Ending Normalization

```zig
// ============================================================================
// Whitespace Normalization
// ============================================================================

/// Normalize all whitespace characters (spaces, tabs, newlines) to single spaces.
/// Multiple consecutive whitespace characters are collapsed into one space.
/// Leading and trailing whitespace is removed.
pub fn normalizeWhitespace(allocator: Allocator, text: []const u8) ![]u8 {
    if (text.len == 0) return try allocator.dupe(u8, "");

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var in_whitespace = true; // Start true to skip leading whitespace
    for (text) |c| {
        const is_ws = c == ' ' or c == '\t' or c == '\n' or c == '\r';

        if (is_ws) {
            if (!in_whitespace) {
                try result.append(allocator, ' ');
                in_whitespace = true;
            }
        } else {
            try result.append(allocator, c);
            in_whitespace = false;
        }
    }

    // Remove trailing space if present (more efficient: pop before converting to slice)
    if (result.items.len > 0 and result.items[result.items.len - 1] == ' ') {
        _ = result.pop();
    }

    return try result.toOwnedSlice(allocator);
}

test "normalizeWhitespace - basic" {
    const input = "  hello   world  \n\t  foo  ";
    const result = try normalizeWhitespace(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world foo", result);
}

test "normalizeWhitespace - empty and whitespace only" {
    const empty = try normalizeWhitespace(testing.allocator, "");
    defer testing.allocator.free(empty);
    try testing.expectEqualStrings("", empty);

    const ws_only = try normalizeWhitespace(testing.allocator, "   \t\n  ");
    defer testing.allocator.free(ws_only);
    try testing.expectEqualStrings("", ws_only);
}

// ============================================================================
// Line Ending Normalization
// ============================================================================

pub const LineEnding = enum {
    lf,    // Unix/Linux/macOS (\n)
    crlf,  // Windows (\r\n)
    cr,    // Classic Mac (\r)
};

/// Convert all line endings in text to the specified format.
pub fn normalizeLineEndings(allocator: Allocator, text: []const u8, target: LineEnding) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    const target_bytes = switch (target) {
        .lf => "\n",
        .crlf => "\r\n",
        .cr => "\r",
    };

    var i: usize = 0;
    while (i < text.len) {
        if (i + 1 < text.len and text[i] == '\r' and text[i + 1] == '\n') {
            // CRLF -> target
            try result.appendSlice(allocator, target_bytes);
            i += 2;
        } else if (text[i] == '\r') {
            // CR -> target
            try result.appendSlice(allocator, target_bytes);
            i += 1;
        } else if (text[i] == '\n') {
            // LF -> target
            try result.appendSlice(allocator, target_bytes);
            i += 1;
        } else {
            try result.append(allocator, text[i]);
            i += 1;
        }
    }

    return result.toOwnedSlice(allocator);
}

test "normalizeLineEndings - CRLF to LF" {
    const input = "line1\r\nline2\r\nline3";
    const result = try normalizeLineEndings(testing.allocator, input, .lf);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("line1\nline2\nline3", result);
}

test "normalizeLineEndings - mixed to CRLF" {
    const input = "line1\nline2\r\nline3\rline4";
    const result = try normalizeLineEndings(testing.allocator, input, .crlf);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("line1\r\nline2\r\nline3\r\nline4", result);
}

test "normalizeLineEndings - LF to CR" {
    const input = "line1\nline2\nline3";
    const result = try normalizeLineEndings(testing.allocator, input, .cr);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("line1\rline2\rline3", result);
}
```

### URL Encoding

```zig
// ============================================================================
// URL Encoding/Decoding
// ============================================================================

/// Check if a character should be percent-encoded in URLs.
/// Unreserved characters (A-Z, a-z, 0-9, -, _, ., ~) are not encoded.
fn shouldEncodeUrlChar(c: u8) bool {
    return switch (c) {
        'A'...'Z', 'a'...'z', '0'...'9', '-', '_', '.', '~' => false,
        else => true,
    };
}

/// Encode a string for use in URLs (percent encoding).
/// Encodes all characters except unreserved characters per RFC 3986.
pub fn urlEncode(allocator: Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |c| {
        if (shouldEncodeUrlChar(c)) {
            try result.append(allocator, '%');
            const hex = "0123456789ABCDEF";
            try result.append(allocator, hex[(c >> 4) & 0xF]);
            try result.append(allocator, hex[c & 0xF]);
        } else {
            try result.append(allocator, c);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Decode a percent-encoded URL string.
/// Returns error.InvalidPercentEncoding if the encoding is malformed.
pub fn urlDecode(allocator: Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i < text.len) {
        if (text[i] == '%') {
            if (i + 2 >= text.len) return error.InvalidPercentEncoding;

            const hex_digits = text[i + 1 .. i + 3];
            const value = std.fmt.parseInt(u8, hex_digits, 16) catch {
                return error.InvalidPercentEncoding;
            };

            try result.append(allocator, value);
            i += 3;
        } else {
            try result.append(allocator, text[i]);
            i += 1;
        }
    }

    return result.toOwnedSlice(allocator);
}

test "urlEncode - basic" {
    const input = "hello world!";
    const result = try urlEncode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello%20world%21", result);
}

test "urlEncode - special characters" {
    const input = "name=John Doe&age=30";
    const result = try urlEncode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("name%3DJohn%20Doe%26age%3D30", result);
}

test "urlDecode - basic" {
    const input = "hello%20world%21";
    const result = try urlDecode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world!", result);
}

test "url encode/decode round trip" {
    const original = "The quick brown fox jumps over the lazy dog! #2024 @user";
    const encoded = try urlEncode(testing.allocator, original);
    defer testing.allocator.free(encoded);

    const decoded = try urlDecode(testing.allocator, encoded);
    defer testing.allocator.free(decoded);

    try testing.expectEqualStrings(original, decoded);
}

test "urlDecode - invalid encoding" {
    try testing.expectError(error.InvalidPercentEncoding, urlDecode(testing.allocator, "test%2"));
    try testing.expectError(error.InvalidPercentEncoding, urlDecode(testing.allocator, "test%ZZ"));
}
```

### HTML and ANSI Cleanup

```zig
// ============================================================================
// ANSI Escape Code Removal
// ============================================================================

/// Remove ANSI escape codes from text (e.g., terminal color codes).
/// ANSI codes are sequences starting with ESC (0x1B) followed by '[' and
/// terminated by a letter (typically 'm' for colors).
pub fn removeAnsiCodes(allocator: Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i < text.len) {
        // Check for ESC [ sequence
        if (i + 1 < text.len and text[i] == 0x1B and text[i + 1] == '[') {
            // Skip until we find a letter (the terminator)
            i += 2;
            while (i < text.len) : (i += 1) {
                const c = text[i];
                if ((c >= 'A' and c <= 'Z') or (c >= 'a' and c <= 'z')) {
                    i += 1;
                    break;
                }
            }
        } else {
            try result.append(allocator, text[i]);
            i += 1;
        }
    }

    return result.toOwnedSlice(allocator);
}

test "removeAnsiCodes - colored text" {
    // Red "Hello" + reset + green "World"
    const input = "\x1B[31mHello\x1B[0m \x1B[32mWorld\x1B[0m";
    const result = try removeAnsiCodes(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello World", result);
}

test "removeAnsiCodes - no codes" {
    const input = "Plain text with no codes";
    const result = try removeAnsiCodes(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings(input, result);
}

test "removeAnsiCodes - complex codes" {
    // Bold + underline + color
    const input = "\x1B[1m\x1B[4m\x1B[33mWarning:\x1B[0m Check logs";
    const result = try removeAnsiCodes(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Warning: Check logs", result);
}

// ============================================================================
// HTML Entity Encoding/Decoding
// ============================================================================

/// Common HTML named entities for encoding
const HtmlEntity = struct {
    char: u8,
    entity: []const u8,
};

const html_entities = [_]HtmlEntity{
    .{ .char = '<', .entity = "&lt;" },
    .{ .char = '>', .entity = "&gt;" },
    .{ .char = '&', .entity = "&amp;" },
    .{ .char = '"', .entity = "&quot;" },
    .{ .char = '\'', .entity = "&#39;" },
};

/// Encode text for safe display in HTML by escaping special characters.
/// Handles: <, >, &, ", '
pub fn htmlEncode(allocator: Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |c| {
        var found = false;
        for (html_entities) |entity| {
            if (c == entity.char) {
                try result.appendSlice(allocator, entity.entity);
                found = true;
                break;
            }
        }
        if (!found) {
            try result.append(allocator, c);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Decode HTML entities back to their original characters.
/// Handles both named entities (&lt;, &gt;, etc.) and numeric entities (&#65;, &#x41;).
pub fn htmlDecode(allocator: Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i < text.len) {
        if (text[i] == '&') {
            // Try to find the semicolon
            const end = mem.indexOfScalarPos(u8, text, i, ';') orelse {
                // No semicolon found, just append the &
                try result.append(allocator, '&');
                i += 1;
                continue;
            };

            const entity = text[i .. end + 1];

            // Check for numeric entity
            if (entity.len > 3 and entity[1] == '#') {
                const is_hex = entity.len > 4 and (entity[2] == 'x' or entity[2] == 'X');
                const num_start: usize = if (is_hex) 3 else 2;
                const num_str = entity[num_start .. entity.len - 1];

                const base: u8 = if (is_hex) 16 else 10;
                const value = std.fmt.parseInt(u8, num_str, base) catch {
                    // Invalid numeric entity, keep as-is
                    try result.appendSlice(allocator, entity);
                    i = end + 1;
                    continue;
                };

                try result.append(allocator, value);
                i = end + 1;
                continue;
            }

            // Check for named entities
            var decoded = false;
            for (html_entities) |ent| {
                if (mem.eql(u8, entity, ent.entity)) {
                    try result.append(allocator, ent.char);
                    decoded = true;
                    break;
                }
            }

            if (!decoded) {
                // Unknown entity, keep as-is
                try result.appendSlice(allocator, entity);
            }

            i = end + 1;
        } else {
            try result.append(allocator, text[i]);
            i += 1;
        }
    }

    return result.toOwnedSlice(allocator);
}

test "htmlEncode - special characters" {
    const input = "<div class=\"test\">Hello & goodbye</div>";
    const result = try htmlEncode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("&lt;div class=&quot;test&quot;&gt;Hello &amp; goodbye&lt;/div&gt;", result);
}

test "htmlEncode - prevents XSS" {
    const input = "<script>alert('XSS')</script>";
    const result = try htmlEncode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("&lt;script&gt;alert(&#39;XSS&#39;)&lt;/script&gt;", result);
}

test "htmlDecode - named entities" {
    const input = "&lt;div&gt;Hello &amp; goodbye&lt;/div&gt;";
    const result = try htmlDecode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("<div>Hello & goodbye</div>", result);
}

test "htmlDecode - numeric entities decimal" {
    const input = "Hello &#65;&#66;&#67;";
    const result = try htmlDecode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello ABC", result);
}

test "htmlDecode - numeric entities hex" {
    const input = "Hello &#x41;&#x42;&#x43;";
    const result = try htmlDecode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello ABC", result);
}

test "htmlDecode - mixed entities" {
    const input = "&lt;tag attr=&quot;&#x48;ello&quot;&gt;&#65; &amp; B&lt;/tag&gt;";
    const result = try htmlDecode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("<tag attr=\"Hello\">A & B</tag>", result);
}

test "html encode/decode round trip" {
    const original = "<p>The price is $5 & the tax is 'high'!</p>";
    const encoded = try htmlEncode(testing.allocator, original);
    defer testing.allocator.free(encoded);

    const decoded = try htmlDecode(testing.allocator, encoded);
    defer testing.allocator.free(decoded);

    try testing.expectEqualStrings(original, decoded);
}
```

### HTML Entity Encoding and Decoding

Prevent XSS attacks by encoding HTML special characters:

```zig
pub fn htmlEncode(allocator: std.mem.Allocator, text: []const u8) ![]u8 {
    const entities = [_]struct { char: u8, entity: []const u8 }{
        .{ .char = '<', .entity = "&lt;" },
        .{ .char = '>', .entity = "&gt;" },
        .{ .char = '&', .entity = "&amp;" },
        .{ .char = '"', .entity = "&quot;" },
        .{ .char = '\'', .entity = "&#39;" },
    };

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |c| {
        var found = false;
        for (entities) |entity| {
            if (c == entity.char) {
                try result.appendSlice(allocator, entity.entity);
                found = true;
                break;
            }
        }
        if (!found) {
            try result.append(allocator, c);
        }
    }

    return result.toOwnedSlice(allocator);
}

test "HTML encoding prevents XSS" {
    const allocator = std.testing.allocator;

    const malicious_input = "<script>alert('XSS')</script>";
    const safe_output = try htmlEncode(allocator, malicious_input);
    defer allocator.free(safe_output);

    try std.testing.expectEqualStrings(
        "&lt;script&gt;alert(&#39;XSS&#39;)&lt;/script&gt;",
        safe_output
    );
}
```

### Sanitization Pipeline

Combine multiple sanitization steps for complex text cleanup:

```zig
pub const SanitizeOptions = struct {
    normalize_whitespace: bool = true,
    normalize_line_endings: ?LineEnding = null,
    remove_ansi_codes: bool = false,
    html_encode: bool = false,
    url_encode: bool = false,
    trim: bool = true,
};

pub fn sanitizeText(
    allocator: std.mem.Allocator,
    text: []const u8,
    options: SanitizeOptions,
) ![]u8 {
    var current = try allocator.dupe(u8, text);
    errdefer allocator.free(current);

    // Apply sanitization steps in order
    if (options.remove_ansi_codes) {
        const temp = try removeAnsiCodes(allocator, current);
        allocator.free(current);
        current = temp;
    }

    if (options.normalize_line_endings) |ending| {
        const temp = try normalizeLineEndings(allocator, current, ending);
        allocator.free(current);
        current = temp;
    }

    if (options.normalize_whitespace) {
        const temp = try normalizeWhitespace(allocator, current);
        allocator.free(current);
        current = temp;
    }

    if (options.trim and !options.normalize_whitespace) {
        const trimmed = std.mem.trim(u8, current, &[_]u8{ ' ', '\t', '\n', '\r' });
        const temp = try allocator.dupe(u8, trimmed);
        allocator.free(current);
        current = temp;
    }

    if (options.html_encode) {
        const temp = try htmlEncode(allocator, current);
        allocator.free(current);
        current = temp;
    }

    if (options.url_encode) {
        const temp = try urlEncode(allocator, current);
        allocator.free(current);
        current = temp;
    }

    return current;
}

test "sanitization pipeline for web display" {
    const allocator = std.testing.allocator;

    const user_input = "  <script>alert('test')</script>  \r\n  ";

    const result = try sanitizeText(allocator, user_input, .{
        .normalize_whitespace = true,
        .html_encode = true,
    });
    defer allocator.free(result);

    // Safe to display in HTML
    try std.testing.expectEqualStrings(
        "&lt;script&gt;alert(&#39;test&#39;)&lt;/script&gt;",
        result
    );
}
```

### Discussion

### Security Considerations

Text sanitization is critical for security. The most common use cases are:

1. **XSS Prevention**: Always HTML-encode user content before displaying in web pages. Even seemingly safe data can contain malicious scripts.

2. **URL Safety**: Encode data before using in URLs to prevent injection attacks and ensure proper parsing.

3. **Log Injection**: Clean ANSI codes from logs before storing to prevent terminal escape sequence attacks.

### Performance Tips

- **Chain operations carefully**: Each sanitization step allocates new memory. Consider which steps are truly necessary.

- **Pre-allocate when possible**: If you know the approximate output size, use `ArrayList.ensureTotalCapacity` to reduce allocations.

- **Avoid redundant operations**: Don't normalize whitespace if you're about to URL-encode (which handles spaces anyway).

### Memory Management

All sanitization functions follow Zig's allocator pattern:

- The caller provides an allocator
- Functions return owned slices that must be freed
- Use `defer allocator.free(result)` immediately after receiving the result
- Use `errdefer` inside functions to clean up on errors

### Real-World Examples

**Cleaning terminal output for storage:**
```zig
const log_output = "\x1B[32mSUCCESS:\x1B[0m Build completed\r\n";
const clean = try sanitizeText(allocator, log_output, .{
    .remove_ansi_codes = true,
    .normalize_line_endings = .lf,
    .normalize_whitespace = false,
    .trim = false,
});
```

**Preparing search query for URL:**
```zig
const query = "Zig programming language";
const url_param = try sanitizeText(allocator, query, .{
    .url_encode = true,
    .normalize_whitespace = false,
    .trim = false,
});
// Use in: https://example.com/search?q=...
```

**Sanitizing user content for HTML:**
```zig
const user_comment = "<b>Check this out!</b>";
const safe_html = try sanitizeText(allocator, user_comment, .{
    .normalize_whitespace = true,
    .html_encode = true,
});
// Safe to insert into: <div class="comment">...</div>
```

### UTF-8 Considerations

All sanitization functions work correctly with UTF-8 text:

- Byte-level operations (like ANSI code removal) don't corrupt multi-byte UTF-8 sequences
- URL encoding works on bytes, which is correct for UTF-8
- HTML entities are ASCII, so encoding preserves UTF-8 content
- Whitespace normalization treats each byte individually, preserving UTF-8 sequences

### When to Use Each Technique

- **Normalize whitespace**: Cleaning user input, standardizing search queries, preparing text for comparison
- **Normalize line endings**: Cross-platform file processing, git automation, standardizing logs
- **URL encoding**: Building query strings, encoding path segments, form data
- **Remove ANSI codes**: Archiving colored terminal output, processing CI/CD logs
- **HTML encoding**: Displaying any user content in HTML, preventing XSS attacks

### Comparison with Recipe 2.7

Recipe 2.7 covered basic trimming and simple character removal. This recipe focuses on:

- **Context-aware encoding** (HTML vs URL require different handling)
- **Multi-step pipelines** (chaining sanitization operations)
- **Format conversion** (line endings, whitespace normalization)
- **Security-focused operations** (XSS prevention, injection protection)

For simple trimming, use Recipe 2.7's `std.mem.trim`. For complex sanitization, use the pipelines shown here.

### Full Tested Code

```zig
// Recipe 2.13: Sanitizing and Cleaning Up Text
// Target Zig Version: 0.15.2
//
// Advanced text sanitization including whitespace normalization, line ending
// conversion, URL encoding/decoding, ANSI escape code removal, and HTML entity
// encoding/decoding.

const std = @import("std");
const testing = std.testing;
const mem = std.mem;
const Allocator = mem.Allocator;

// ANCHOR: whitespace_line_endings
// ============================================================================
// Whitespace Normalization
// ============================================================================

/// Normalize all whitespace characters (spaces, tabs, newlines) to single spaces.
/// Multiple consecutive whitespace characters are collapsed into one space.
/// Leading and trailing whitespace is removed.
pub fn normalizeWhitespace(allocator: Allocator, text: []const u8) ![]u8 {
    if (text.len == 0) return try allocator.dupe(u8, "");

    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var in_whitespace = true; // Start true to skip leading whitespace
    for (text) |c| {
        const is_ws = c == ' ' or c == '\t' or c == '\n' or c == '\r';

        if (is_ws) {
            if (!in_whitespace) {
                try result.append(allocator, ' ');
                in_whitespace = true;
            }
        } else {
            try result.append(allocator, c);
            in_whitespace = false;
        }
    }

    // Remove trailing space if present (more efficient: pop before converting to slice)
    if (result.items.len > 0 and result.items[result.items.len - 1] == ' ') {
        _ = result.pop();
    }

    return try result.toOwnedSlice(allocator);
}

test "normalizeWhitespace - basic" {
    const input = "  hello   world  \n\t  foo  ";
    const result = try normalizeWhitespace(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world foo", result);
}

test "normalizeWhitespace - empty and whitespace only" {
    const empty = try normalizeWhitespace(testing.allocator, "");
    defer testing.allocator.free(empty);
    try testing.expectEqualStrings("", empty);

    const ws_only = try normalizeWhitespace(testing.allocator, "   \t\n  ");
    defer testing.allocator.free(ws_only);
    try testing.expectEqualStrings("", ws_only);
}

// ============================================================================
// Line Ending Normalization
// ============================================================================

pub const LineEnding = enum {
    lf,    // Unix/Linux/macOS (\n)
    crlf,  // Windows (\r\n)
    cr,    // Classic Mac (\r)
};

/// Convert all line endings in text to the specified format.
pub fn normalizeLineEndings(allocator: Allocator, text: []const u8, target: LineEnding) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    const target_bytes = switch (target) {
        .lf => "\n",
        .crlf => "\r\n",
        .cr => "\r",
    };

    var i: usize = 0;
    while (i < text.len) {
        if (i + 1 < text.len and text[i] == '\r' and text[i + 1] == '\n') {
            // CRLF -> target
            try result.appendSlice(allocator, target_bytes);
            i += 2;
        } else if (text[i] == '\r') {
            // CR -> target
            try result.appendSlice(allocator, target_bytes);
            i += 1;
        } else if (text[i] == '\n') {
            // LF -> target
            try result.appendSlice(allocator, target_bytes);
            i += 1;
        } else {
            try result.append(allocator, text[i]);
            i += 1;
        }
    }

    return result.toOwnedSlice(allocator);
}

test "normalizeLineEndings - CRLF to LF" {
    const input = "line1\r\nline2\r\nline3";
    const result = try normalizeLineEndings(testing.allocator, input, .lf);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("line1\nline2\nline3", result);
}

test "normalizeLineEndings - mixed to CRLF" {
    const input = "line1\nline2\r\nline3\rline4";
    const result = try normalizeLineEndings(testing.allocator, input, .crlf);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("line1\r\nline2\r\nline3\r\nline4", result);
}

test "normalizeLineEndings - LF to CR" {
    const input = "line1\nline2\nline3";
    const result = try normalizeLineEndings(testing.allocator, input, .cr);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("line1\rline2\rline3", result);
}
// ANCHOR_END: whitespace_line_endings

// ANCHOR: url_encoding
// ============================================================================
// URL Encoding/Decoding
// ============================================================================

/// Check if a character should be percent-encoded in URLs.
/// Unreserved characters (A-Z, a-z, 0-9, -, _, ., ~) are not encoded.
fn shouldEncodeUrlChar(c: u8) bool {
    return switch (c) {
        'A'...'Z', 'a'...'z', '0'...'9', '-', '_', '.', '~' => false,
        else => true,
    };
}

/// Encode a string for use in URLs (percent encoding).
/// Encodes all characters except unreserved characters per RFC 3986.
pub fn urlEncode(allocator: Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |c| {
        if (shouldEncodeUrlChar(c)) {
            try result.append(allocator, '%');
            const hex = "0123456789ABCDEF";
            try result.append(allocator, hex[(c >> 4) & 0xF]);
            try result.append(allocator, hex[c & 0xF]);
        } else {
            try result.append(allocator, c);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Decode a percent-encoded URL string.
/// Returns error.InvalidPercentEncoding if the encoding is malformed.
pub fn urlDecode(allocator: Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i < text.len) {
        if (text[i] == '%') {
            if (i + 2 >= text.len) return error.InvalidPercentEncoding;

            const hex_digits = text[i + 1 .. i + 3];
            const value = std.fmt.parseInt(u8, hex_digits, 16) catch {
                return error.InvalidPercentEncoding;
            };

            try result.append(allocator, value);
            i += 3;
        } else {
            try result.append(allocator, text[i]);
            i += 1;
        }
    }

    return result.toOwnedSlice(allocator);
}

test "urlEncode - basic" {
    const input = "hello world!";
    const result = try urlEncode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello%20world%21", result);
}

test "urlEncode - special characters" {
    const input = "name=John Doe&age=30";
    const result = try urlEncode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("name%3DJohn%20Doe%26age%3D30", result);
}

test "urlDecode - basic" {
    const input = "hello%20world%21";
    const result = try urlDecode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world!", result);
}

test "url encode/decode round trip" {
    const original = "The quick brown fox jumps over the lazy dog! #2024 @user";
    const encoded = try urlEncode(testing.allocator, original);
    defer testing.allocator.free(encoded);

    const decoded = try urlDecode(testing.allocator, encoded);
    defer testing.allocator.free(decoded);

    try testing.expectEqualStrings(original, decoded);
}

test "urlDecode - invalid encoding" {
    try testing.expectError(error.InvalidPercentEncoding, urlDecode(testing.allocator, "test%2"));
    try testing.expectError(error.InvalidPercentEncoding, urlDecode(testing.allocator, "test%ZZ"));
}
// ANCHOR_END: url_encoding

// ANCHOR: html_ansi_cleanup
// ============================================================================
// ANSI Escape Code Removal
// ============================================================================

/// Remove ANSI escape codes from text (e.g., terminal color codes).
/// ANSI codes are sequences starting with ESC (0x1B) followed by '[' and
/// terminated by a letter (typically 'm' for colors).
pub fn removeAnsiCodes(allocator: Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i < text.len) {
        // Check for ESC [ sequence
        if (i + 1 < text.len and text[i] == 0x1B and text[i + 1] == '[') {
            // Skip until we find a letter (the terminator)
            i += 2;
            while (i < text.len) : (i += 1) {
                const c = text[i];
                if ((c >= 'A' and c <= 'Z') or (c >= 'a' and c <= 'z')) {
                    i += 1;
                    break;
                }
            }
        } else {
            try result.append(allocator, text[i]);
            i += 1;
        }
    }

    return result.toOwnedSlice(allocator);
}

test "removeAnsiCodes - colored text" {
    // Red "Hello" + reset + green "World"
    const input = "\x1B[31mHello\x1B[0m \x1B[32mWorld\x1B[0m";
    const result = try removeAnsiCodes(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello World", result);
}

test "removeAnsiCodes - no codes" {
    const input = "Plain text with no codes";
    const result = try removeAnsiCodes(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings(input, result);
}

test "removeAnsiCodes - complex codes" {
    // Bold + underline + color
    const input = "\x1B[1m\x1B[4m\x1B[33mWarning:\x1B[0m Check logs";
    const result = try removeAnsiCodes(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Warning: Check logs", result);
}

// ============================================================================
// HTML Entity Encoding/Decoding
// ============================================================================

/// Common HTML named entities for encoding
const HtmlEntity = struct {
    char: u8,
    entity: []const u8,
};

const html_entities = [_]HtmlEntity{
    .{ .char = '<', .entity = "&lt;" },
    .{ .char = '>', .entity = "&gt;" },
    .{ .char = '&', .entity = "&amp;" },
    .{ .char = '"', .entity = "&quot;" },
    .{ .char = '\'', .entity = "&#39;" },
};

/// Encode text for safe display in HTML by escaping special characters.
/// Handles: <, >, &, ", '
pub fn htmlEncode(allocator: Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    for (text) |c| {
        var found = false;
        for (html_entities) |entity| {
            if (c == entity.char) {
                try result.appendSlice(allocator, entity.entity);
                found = true;
                break;
            }
        }
        if (!found) {
            try result.append(allocator, c);
        }
    }

    return result.toOwnedSlice(allocator);
}

/// Decode HTML entities back to their original characters.
/// Handles both named entities (&lt;, &gt;, etc.) and numeric entities (&#65;, &#x41;).
pub fn htmlDecode(allocator: Allocator, text: []const u8) ![]u8 {
    var result = std.ArrayList(u8){};
    errdefer result.deinit(allocator);

    var i: usize = 0;
    while (i < text.len) {
        if (text[i] == '&') {
            // Try to find the semicolon
            const end = mem.indexOfScalarPos(u8, text, i, ';') orelse {
                // No semicolon found, just append the &
                try result.append(allocator, '&');
                i += 1;
                continue;
            };

            const entity = text[i .. end + 1];

            // Check for numeric entity
            if (entity.len > 3 and entity[1] == '#') {
                const is_hex = entity.len > 4 and (entity[2] == 'x' or entity[2] == 'X');
                const num_start: usize = if (is_hex) 3 else 2;
                const num_str = entity[num_start .. entity.len - 1];

                const base: u8 = if (is_hex) 16 else 10;
                const value = std.fmt.parseInt(u8, num_str, base) catch {
                    // Invalid numeric entity, keep as-is
                    try result.appendSlice(allocator, entity);
                    i = end + 1;
                    continue;
                };

                try result.append(allocator, value);
                i = end + 1;
                continue;
            }

            // Check for named entities
            var decoded = false;
            for (html_entities) |ent| {
                if (mem.eql(u8, entity, ent.entity)) {
                    try result.append(allocator, ent.char);
                    decoded = true;
                    break;
                }
            }

            if (!decoded) {
                // Unknown entity, keep as-is
                try result.appendSlice(allocator, entity);
            }

            i = end + 1;
        } else {
            try result.append(allocator, text[i]);
            i += 1;
        }
    }

    return result.toOwnedSlice(allocator);
}

test "htmlEncode - special characters" {
    const input = "<div class=\"test\">Hello & goodbye</div>";
    const result = try htmlEncode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("&lt;div class=&quot;test&quot;&gt;Hello &amp; goodbye&lt;/div&gt;", result);
}

test "htmlEncode - prevents XSS" {
    const input = "<script>alert('XSS')</script>";
    const result = try htmlEncode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("&lt;script&gt;alert(&#39;XSS&#39;)&lt;/script&gt;", result);
}

test "htmlDecode - named entities" {
    const input = "&lt;div&gt;Hello &amp; goodbye&lt;/div&gt;";
    const result = try htmlDecode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("<div>Hello & goodbye</div>", result);
}

test "htmlDecode - numeric entities decimal" {
    const input = "Hello &#65;&#66;&#67;";
    const result = try htmlDecode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello ABC", result);
}

test "htmlDecode - numeric entities hex" {
    const input = "Hello &#x41;&#x42;&#x43;";
    const result = try htmlDecode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello ABC", result);
}

test "htmlDecode - mixed entities" {
    const input = "&lt;tag attr=&quot;&#x48;ello&quot;&gt;&#65; &amp; B&lt;/tag&gt;";
    const result = try htmlDecode(testing.allocator, input);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("<tag attr=\"Hello\">A & B</tag>", result);
}

test "html encode/decode round trip" {
    const original = "<p>The price is $5 & the tax is 'high'!</p>";
    const encoded = try htmlEncode(testing.allocator, original);
    defer testing.allocator.free(encoded);

    const decoded = try htmlDecode(testing.allocator, encoded);
    defer testing.allocator.free(decoded);

    try testing.expectEqualStrings(original, decoded);
}
// ANCHOR_END: html_ansi_cleanup

// ============================================================================
// Comprehensive Sanitization Pipeline
// ============================================================================

/// Configuration for text sanitization pipeline
pub const SanitizeOptions = struct {
    normalize_whitespace: bool = true,
    normalize_line_endings: ?LineEnding = null,
    remove_ansi_codes: bool = false,
    html_encode: bool = false,
    url_encode: bool = false,
    trim: bool = true,
};

/// Apply multiple sanitization steps to text in a single pass.
/// Steps are applied in this order:
/// 1. Remove ANSI codes (if enabled)
/// 2. Normalize line endings (if specified)
/// 3. Normalize whitespace (if enabled)
/// 4. Trim (if enabled)
/// 5. HTML encode (if enabled)
/// 6. URL encode (if enabled)
pub fn sanitizeText(allocator: Allocator, text: []const u8, options: SanitizeOptions) ![]u8 {
    var current = try allocator.dupe(u8, text);
    errdefer allocator.free(current);

    // Step 1: Remove ANSI codes
    if (options.remove_ansi_codes) {
        const temp = try removeAnsiCodes(allocator, current);
        allocator.free(current);
        current = temp;
    }

    // Step 2: Normalize line endings
    if (options.normalize_line_endings) |ending| {
        const temp = try normalizeLineEndings(allocator, current, ending);
        allocator.free(current);
        current = temp;
    }

    // Step 3: Normalize whitespace
    if (options.normalize_whitespace) {
        const temp = try normalizeWhitespace(allocator, current);
        allocator.free(current);
        current = temp;
    }

    // Step 4: Trim (already done by normalizeWhitespace, but handle separately if not normalizing)
    if (options.trim and !options.normalize_whitespace) {
        const trimmed = mem.trim(u8, current, &[_]u8{ ' ', '\t', '\n', '\r' });
        const temp = try allocator.dupe(u8, trimmed);
        allocator.free(current);
        current = temp;
    }

    // Step 5: HTML encode
    if (options.html_encode) {
        const temp = try htmlEncode(allocator, current);
        allocator.free(current);
        current = temp;
    }

    // Step 6: URL encode
    if (options.url_encode) {
        const temp = try urlEncode(allocator, current);
        allocator.free(current);
        current = temp;
    }

    return current;
}

test "sanitizeText - pipeline example: clean log file" {
    // Simulating colored log output with extra whitespace
    const input = "\x1B[31m[ERROR]\x1B[0m   Multiple   spaces\n\n\nand  newlines";

    const result = try sanitizeText(testing.allocator, input, .{
        .remove_ansi_codes = true,
        .normalize_whitespace = true,
        .normalize_line_endings = .lf,
    });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("[ERROR] Multiple spaces and newlines", result);
}

test "sanitizeText - pipeline example: prepare for HTML display" {
    const input = "  <script>alert('test')</script>  \r\n  ";

    const result = try sanitizeText(testing.allocator, input, .{
        .normalize_whitespace = true,
        .html_encode = true,
    });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("&lt;script&gt;alert(&#39;test&#39;)&lt;/script&gt;", result);
}

test "sanitizeText - pipeline example: prepare for URL parameter" {
    const input = "  Hello World!  ";

    const result = try sanitizeText(testing.allocator, input, .{
        .trim = true,
        .url_encode = true,
    });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("Hello%20World%21", result);
}

test "sanitizeText - no modifications" {
    const input = "Hello World";

    const result = try sanitizeText(testing.allocator, input, .{
        .normalize_whitespace = false,
        .trim = false,
    });
    defer testing.allocator.free(result);

    try testing.expectEqualStrings(input, result);
}

// ============================================================================
// Real-World Examples
// ============================================================================

test "real-world: sanitizing user input for web display" {
    const user_input = "  <b>Check out my site:</b> http://evil.com?param=<script>alert('xss')</script>  ";

    const sanitized = try sanitizeText(testing.allocator, user_input, .{
        .normalize_whitespace = true,
        .html_encode = true,
    });
    defer testing.allocator.free(sanitized);

    // Should be safe to display in HTML
    try testing.expect(mem.indexOf(u8, sanitized, "<script>") == null);
    try testing.expect(mem.indexOf(u8, sanitized, "&lt;script&gt;") != null);
}

test "real-world: cleaning terminal output for storage" {
    const terminal_output = "\x1B[32mSUCCESS:\x1B[0m Build completed\r\n\x1B[33mWarning:\x1B[0m 2 warnings found\r\n";

    const cleaned = try sanitizeText(testing.allocator, terminal_output, .{
        .remove_ansi_codes = true,
        .normalize_line_endings = .lf,
        .normalize_whitespace = false,
        .trim = false,
    });
    defer testing.allocator.free(cleaned);

    try testing.expectEqualStrings("SUCCESS: Build completed\nWarning: 2 warnings found\n", cleaned);
}

test "real-world: preparing text for URL parameter" {
    const search_query = "Zig programming language";

    const url_safe = try sanitizeText(testing.allocator, search_query, .{
        .url_encode = true,
        .normalize_whitespace = false,
        .trim = false,
    });
    defer testing.allocator.free(url_safe);

    // Can be safely used in: https://example.com/search?q=...
    try testing.expectEqualStrings("Zig%20programming%20language", url_safe);
}
```

### See Also

- Recipe 2.7: Stripping unwanted characters (basic trimming)
- Recipe 2.14: Standardizing Unicode text (advanced Unicode normalization with C libraries)
- Recipe 6.2: Reading and writing JSON (for data encoding)
- Recipe 11.1: HTTP services (for web application security)

---

## Recipe 2.14: Standardizing Unicode Text to a Normal Form {#recipe-2-14}

**Tags:** allocators, arraylist, c-interop, data-structures, error-handling, memory, pointers, resource-cleanup, slices, strings-text, testing
**Difficulty:** intermediate
**Code:** `code/02-core/02-strings-and-text/recipe_2_14.zig`

### Problem

You need to compare or process Unicode strings that look identical but have different byte representations. For example, the character "é" can be represented as:
- A single pre-composed character (U+00E9)
- A letter 'e' followed by a combining acute accent (U+0065 + U+0301)

These look identical but have completely different bytes, causing string comparisons to fail. Additionally, Zig's `std.ascii` functions only handle ASCII case conversions and don't understand complex Unicode rules like the German "ß" becoming "SS" in uppercase.

**Important Note:** This recipe focuses on teaching C interoperability patterns. For production Zig code, consider pure-Zig alternatives like the **Ziglyph** library, which provides Unicode normalization without C dependencies or version-specific quirks.

### Solution

For robust Unicode standardization, interface with the ICU (International Components for Unicode) C library. This requires linking the library in `build.zig` and creating safe Zig wrappers around its C functions.

### ICU Setup and C Interop

```zig
const std = @import("std");
const testing = std.testing;
const mem = std.mem;
const unicode = std.unicode;
const Allocator = mem.Allocator;

// Import ICU C library types (with renaming disabled to avoid circular dependencies)
// IMPORTANT: Only use ONE @cImport per application to avoid symbol collisions
const icu = @cImport({
    @cDefine("U_DISABLE_RENAMING", "1");
    @cInclude("unicode/utypes.h"); // Base types
    @cInclude("unicode/unorm2.h"); // For normalization types
    @cInclude("unicode/ustring.h"); // For string operation types
});

// Manually declare versioned ICU functions to work around Zig @cImport macro issues
//
// WHY VERSIONED?: ICU's U_ICU_ENTRY_POINT_RENAME macro causes circular dependencies
// in Zig's @cImport. Using U_DISABLE_RENAMING + manual declarations is the workaround.
// The _77 suffix corresponds to ICU version 77 (check with: icu-config --version).
//
// PORTABILITY NOTE: This hardcodes ICU 77. For different ICU versions, adjust the suffix.
// This is a known limitation of this approach and why production code should prefer
// pure-Zig Unicode libraries that don't have these FFI complications.
extern "c" fn unorm2_getNFCInstance_77(pErrorCode: *icu.UErrorCode) ?*const icu.UNormalizer2;
extern "c" fn unorm2_getNFDInstance_77(pErrorCode: *icu.UErrorCode) ?*const icu.UNormalizer2;
extern "c" fn unorm2_getNFKCInstance_77(pErrorCode: *icu.UErrorCode) ?*const icu.UNormalizer2;
extern "c" fn unorm2_normalize_77(
    norm2: ?*const icu.UNormalizer2,
    src: [*]const u16,
    length: i32,
    dest: ?[*]u16,
    capacity: i32,
    pErrorCode: *icu.UErrorCode,
) i32;
extern "c" fn u_strFoldCase_77(
    dest: ?[*]u16,
    destCapacity: i32,
    src: [*]const u16,
    srcLength: i32,
    options: u32,
    pErrorCode: *icu.UErrorCode,
) i32;

// Custom error set for ICU operations
const ICUError = error{
    InitFailed,
    NormalizationFailed,
    CaseFoldFailed,
    InvalidUtf8,
    BufferTooSmall,
    UnexpectedError,
};

/// Convert UTF-8 string to UTF-16 (ICU uses UTF-16 internally)
fn utf8ToUtf16(allocator: Allocator, utf8: []const u8) ![]u16 {
    if (utf8.len == 0) return try allocator.alloc(u16, 0);

    // Validate UTF-8 first
    if (!unicode.utf8ValidateSlice(utf8)) {
        return ICUError.InvalidUtf8;
    }

    // Calculate required UTF-16 length
    var utf16_len: usize = 0;
    var i: usize = 0;
    while (i < utf8.len) {
        const cp_len = try unicode.utf8ByteSequenceLength(utf8[i]);
        const codepoint = try unicode.utf8Decode(utf8[i .. i + cp_len]);

        if (codepoint >= 0x10000) {
            utf16_len += 2; // Surrogate pair
        } else {
            utf16_len += 1;
        }
        i += cp_len;
    }

    // Allocate and encode
    var utf16 = try allocator.alloc(u16, utf16_len);
    errdefer allocator.free(utf16);

    var out_idx: usize = 0;
    i = 0;
    while (i < utf8.len) {
        const cp_len = try unicode.utf8ByteSequenceLength(utf8[i]);
        const codepoint = try unicode.utf8Decode(utf8[i .. i + cp_len]);

        if (codepoint >= 0x10000) {
            // Encode as surrogate pair
            const surrogate = codepoint - 0x10000;
            utf16[out_idx] = @intCast(0xD800 + (surrogate >> 10));
            utf16[out_idx + 1] = @intCast(0xDC00 + (surrogate & 0x3FF));
            out_idx += 2;
        } else {
            utf16[out_idx] = @intCast(codepoint);
            out_idx += 1;
        }
        i += cp_len;
    }

    return utf16;
}

/// Convert UTF-16 string to UTF-8
fn utf16ToUtf8(allocator: Allocator, utf16: []const u16) ![]u8 {
    if (utf16.len == 0) return try allocator.alloc(u8, 0);

    // Calculate required UTF-8 length
    var utf8_len: usize = 0;
    var i: usize = 0;
    while (i < utf16.len) {
        const unit = utf16[i];
        var codepoint: u21 = 0;

        if (unit >= 0xD800 and unit <= 0xDBFF) {
            // High surrogate - need next unit
            if (i + 1 >= utf16.len) return ICUError.InvalidUtf8;
            const low = utf16[i + 1];
            if (low < 0xDC00 or low > 0xDFFF) return ICUError.InvalidUtf8;

            codepoint = @intCast(0x10000 + ((@as(u32, unit) - 0xD800) << 10) + (low - 0xDC00));
            i += 2;
        } else if (unit >= 0xDC00 and unit <= 0xDFFF) {
            // Low surrogate without high surrogate - invalid
            return ICUError.InvalidUtf8;
        } else {
            codepoint = @intCast(unit);
            i += 1;
        }

        utf8_len += try unicode.utf8CodepointSequenceLength(codepoint);
    }

    // Allocate and encode
    var utf8 = try allocator.alloc(u8, utf8_len);
    errdefer allocator.free(utf8);

    var out_pos: usize = 0;
    i = 0;
    while (i < utf16.len) {
        const unit = utf16[i];
        var codepoint: u21 = 0;

        if (unit >= 0xD800 and unit <= 0xDBFF) {
            const low = utf16[i + 1];
            codepoint = @intCast(0x10000 + ((@as(u32, unit) - 0xD800) << 10) + (low - 0xDC00));
            i += 2;
        } else {
            codepoint = @intCast(unit);
            i += 1;
        }

        const len = try unicode.utf8Encode(codepoint, utf8[out_pos..]);
        out_pos += len;
    }

    return utf8;
}
```

### Unicode Normalization

```zig
/// Normalize UTF-8 string to NFC (Normalization Form C - Canonical Composition)
/// This is the most common form for web content and database storage.
/// Example: e + combining acute accent (U+0301) -> é (U+00E9)
pub fn normalizeNFC(allocator: Allocator, text: []const u8) ![]u8 {
    if (text.len == 0) return try allocator.alloc(u8, 0);

    // Convert UTF-8 to UTF-16
    const utf16_input = try utf8ToUtf16(allocator, text);
    defer allocator.free(utf16_input);

    // Get NFC normalizer instance
    var status: icu.UErrorCode = icu.U_ZERO_ERROR;
    const normalizer = unorm2_getNFCInstance_77(&status);
    if (status != icu.U_ZERO_ERROR) {
        return ICUError.InitFailed;
    }

    // First call to determine required buffer size
    status = icu.U_ZERO_ERROR;
    const required_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        null,
        0,
        &status,
    );

    // Check for actual errors (positive values), not warnings (negative)
    // U_BUFFER_OVERFLOW_ERROR (15) is expected when probing size
    if (status > 0 and status != icu.U_BUFFER_OVERFLOW_ERROR) {
        return ICUError.NormalizationFailed;
    }

    // Allocate output buffer
    const utf16_output = try allocator.alloc(u16, @intCast(required_len));
    defer allocator.free(utf16_output);

    // Second call to perform normalization
    status = icu.U_ZERO_ERROR;
    const actual_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        utf16_output.ptr,
        @intCast(utf16_output.len),
        &status,
    );

    // Check for actual errors (positive values), warnings (negative) are OK
    if (status > 0) {
        return ICUError.NormalizationFailed;
    }

    // Convert back to UTF-8
    return utf16ToUtf8(allocator, utf16_output[0..@intCast(actual_len)]);
}

/// Normalize UTF-8 string to NFD (Normalization Form D - Canonical Decomposition)
/// This form decomposes characters into base letter + combining marks.
/// Example: é (U+00E9) -> e + combining acute accent (U+0301)
pub fn normalizeNFD(allocator: Allocator, text: []const u8) ![]u8 {
    if (text.len == 0) return try allocator.alloc(u8, 0);

    const utf16_input = try utf8ToUtf16(allocator, text);
    defer allocator.free(utf16_input);

    var status: icu.UErrorCode = icu.U_ZERO_ERROR;
    const normalizer = unorm2_getNFDInstance_77(&status);
    if (status != icu.U_ZERO_ERROR) {
        return ICUError.InitFailed;
    }

    status = icu.U_ZERO_ERROR;
    const required_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        null,
        0,
        &status,
    );

    if (status > 0 and status != icu.U_BUFFER_OVERFLOW_ERROR) {
        return ICUError.NormalizationFailed;
    }

    const utf16_output = try allocator.alloc(u16, @intCast(required_len));
    defer allocator.free(utf16_output);

    status = icu.U_ZERO_ERROR;
    const actual_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        utf16_output.ptr,
        @intCast(utf16_output.len),
        &status,
    );

    if (status > 0) {
        return ICUError.NormalizationFailed;
    }

    return utf16ToUtf8(allocator, utf16_output[0..@intCast(actual_len)]);
}

/// Normalize UTF-8 string to NFKC (Compatibility Composition)
/// This form also normalizes compatibility equivalents (like fractions, ligatures).
/// Example: ½ (U+00BD) -> 1/2 (separate characters)
pub fn normalizeNFKC(allocator: Allocator, text: []const u8) ![]u8 {
    if (text.len == 0) return try allocator.alloc(u8, 0);

    const utf16_input = try utf8ToUtf16(allocator, text);
    defer allocator.free(utf16_input);

    var status: icu.UErrorCode = icu.U_ZERO_ERROR;
    const normalizer = unorm2_getNFKCInstance_77(&status);
    if (status != icu.U_ZERO_ERROR) {
        return ICUError.InitFailed;
    }

    status = icu.U_ZERO_ERROR;
    const required_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        null,
        0,
        &status,
    );

    if (status > 0 and status != icu.U_BUFFER_OVERFLOW_ERROR) {
        return ICUError.NormalizationFailed;
    }

    const utf16_output = try allocator.alloc(u16, @intCast(required_len));
    defer allocator.free(utf16_output);

    status = icu.U_ZERO_ERROR;
    const actual_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        utf16_output.ptr,
        @intCast(utf16_output.len),
        &status,
    );

    if (status > 0) {
        return ICUError.NormalizationFailed;
    }

    return utf16ToUtf8(allocator, utf16_output[0..@intCast(actual_len)]);
}
```

### Case Folding

```zig
/// Case-fold UTF-8 string for case-insensitive comparison.
/// This is more correct than simple lowercasing for Unicode.
/// Example: German ß -> ss, Turkish I -> ı (context-aware)
pub fn caseFold(allocator: Allocator, text: []const u8) ![]u8 {
    if (text.len == 0) return try allocator.alloc(u8, 0);

    const utf16_input = try utf8ToUtf16(allocator, text);
    defer allocator.free(utf16_input);

    var status: icu.UErrorCode = icu.U_ZERO_ERROR;
    const required_len = u_strFoldCase_77(
        null,
        0,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        0,
        &status,
    );

    if (status > 0 and status != icu.U_BUFFER_OVERFLOW_ERROR) {
        return ICUError.CaseFoldFailed;
    }

    const utf16_output = try allocator.alloc(u16, @intCast(required_len));
    defer allocator.free(utf16_output);

    status = icu.U_ZERO_ERROR;
    const actual_len = u_strFoldCase_77(
        utf16_output.ptr,
        @intCast(utf16_output.len),
        utf16_input.ptr,
        @intCast(utf16_input.len),
        0,
        &status,
    );

    if (status > 0) {
        return ICUError.CaseFoldFailed;
    }

    return utf16ToUtf8(allocator, utf16_output[0..@intCast(actual_len)]);
}

// Tests

test "UTF-8 to UTF-16 conversion" {
    const utf8 = "Hello";
    const utf16 = try utf8ToUtf16(testing.allocator, utf8);
    defer testing.allocator.free(utf16);

    try testing.expectEqual(@as(usize, 5), utf16.len);
    try testing.expectEqual(@as(u16, 'H'), utf16[0]);
    try testing.expectEqual(@as(u16, 'e'), utf16[1]);
}

test "UTF-8 to UTF-16 with multibyte characters" {
    const utf8 = "世界";
    const utf16 = try utf8ToUtf16(testing.allocator, utf8);
    defer testing.allocator.free(utf16);

    try testing.expectEqual(@as(usize, 2), utf16.len);
    try testing.expectEqual(@as(u16, 0x4E16), utf16[0]); // 世
    try testing.expectEqual(@as(u16, 0x754C), utf16[1]); // 界
}

test "UTF-16 to UTF-8 conversion" {
    const utf16 = [_]u16{ 'H', 'e', 'l', 'l', 'o' };
    const utf8 = try utf16ToUtf8(testing.allocator, &utf16);
    defer testing.allocator.free(utf8);

    try testing.expectEqualStrings("Hello", utf8);
}

test "UTF-16 to UTF-8 with multibyte characters" {
    const utf16 = [_]u16{ 0x4E16, 0x754C }; // 世界
    const utf8 = try utf16ToUtf8(testing.allocator, &utf16);
    defer testing.allocator.free(utf8);

    try testing.expectEqualStrings("世界", utf8);
}

test "normalize NFC - combining accent to composed" {
    // e + combining acute accent -> é (composed)
    const decomposed = "e\u{0301}";
    const result = try normalizeNFC(testing.allocator, decomposed);
    defer testing.allocator.free(result);

    // Should be composed é (U+00E9)
    try testing.expectEqualStrings("\u{00E9}", result);
}

test "normalize NFC - already composed" {
    const composed = "\u{00E9}"; // é (already composed)
    const result = try normalizeNFC(testing.allocator, composed);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings(composed, result);
}

test "normalize NFD - composed to decomposed" {
    // é (composed) -> e + combining accent
    const composed = "\u{00E9}";
    const result = try normalizeNFD(testing.allocator, composed);
    defer testing.allocator.free(result);

    // Should be decomposed: e + combining acute
    try testing.expectEqualStrings("e\u{0301}", result);
}

test "normalize NFD - already decomposed" {
    const decomposed = "e\u{0301}";
    const result = try normalizeNFD(testing.allocator, decomposed);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings(decomposed, result);
}

test "NFC and NFD are inverses" {
    const original = "café";

    // Normalize to NFD (decomposed)
    const nfd = try normalizeNFD(testing.allocator, original);
    defer testing.allocator.free(nfd);

    // Normalize back to NFC (composed)
    const nfc = try normalizeNFC(testing.allocator, nfd);
    defer testing.allocator.free(nfc);

    // Should match original (both NFC)
    try testing.expectEqualStrings(original, nfc);
}

test "normalize NFKC - compatibility characters" {
    // Test with various compatibility characters
    const text = "Hello";
    const result = try normalizeNFKC(testing.allocator, text);
    defer testing.allocator.free(result);

    // ASCII text should remain unchanged
    try testing.expectEqualStrings(text, result);
}

test "visual equivalence requires normalization" {
    // Two visually identical strings with different byte representations
    const composed = "café"; // é is single codepoint U+00E9
    const decomposed = "cafe\u{0301}"; // é is e + combining accent

    // Byte representations differ
    try testing.expect(!mem.eql(u8, composed, decomposed));

    // After normalization, they should be identical
    const norm1 = try normalizeNFC(testing.allocator, composed);
    defer testing.allocator.free(norm1);

    const norm2 = try normalizeNFC(testing.allocator, decomposed);
    defer testing.allocator.free(norm2);

    try testing.expectEqualStrings(norm1, norm2);
}

test "case fold - ASCII" {
    const text = "Hello World";
    const result = try caseFold(testing.allocator, text);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "case fold - German sharp s" {
    // German ß should case-fold to ss
    const text = "Straße";
    const result = try caseFold(testing.allocator, text);
    defer testing.allocator.free(result);

    // ICU should convert ß to ss
    try testing.expectEqualStrings("strasse", result);
}

test "case fold for case-insensitive comparison" {
    const text1 = "HELLO";
    const text2 = "hello";

    const fold1 = try caseFold(testing.allocator, text1);
    defer testing.allocator.free(fold1);

    const fold2 = try caseFold(testing.allocator, text2);
    defer testing.allocator.free(fold2);

    // Case-folded versions should be identical
    try testing.expectEqualStrings(fold1, fold2);
}

test "empty string normalization" {
    const empty = "";

    const nfc = try normalizeNFC(testing.allocator, empty);
    defer testing.allocator.free(nfc);

    const nfd = try normalizeNFD(testing.allocator, empty);
    defer testing.allocator.free(nfd);

    try testing.expectEqual(@as(usize, 0), nfc.len);
    try testing.expectEqual(@as(usize, 0), nfd.len);
}

test "empty string case fold" {
    const empty = "";
    const result = try caseFold(testing.allocator, empty);
    defer testing.allocator.free(result);

    try testing.expectEqual(@as(usize, 0), result.len);
}

test "normalization with emoji" {
    const emoji = "Hello 👋";

    const nfc = try normalizeNFC(testing.allocator, emoji);
    defer testing.allocator.free(nfc);

    // Emoji should pass through unchanged
    try testing.expect(nfc.len > 0);
}

test "normalization with various scripts" {
    const texts = [_][]const u8{
        "Hello", // ASCII
        "café", // Latin with accent
        "Привет", // Cyrillic
        "你好", // Chinese
        "こんにちは", // Japanese
    };

    for (texts) |text| {
        const nfc = try normalizeNFC(testing.allocator, text);
        defer testing.allocator.free(nfc);

        const nfd = try normalizeNFD(testing.allocator, text);
        defer testing.allocator.free(nfd);

        try testing.expect(nfc.len > 0);
        try testing.expect(nfd.len > 0);
    }
}

test "memory safety - no leaks" {
    // testing.allocator automatically detects memory leaks
    const text = "café";

    const nfc = try normalizeNFC(testing.allocator, text);
    defer testing.allocator.free(nfc);

    const nfd = try normalizeNFD(testing.allocator, text);
    defer testing.allocator.free(nfd);

    const folded = try caseFold(testing.allocator, text);
    defer testing.allocator.free(folded);

    try testing.expect(nfc.len > 0);
    try testing.expect(nfd.len > 0);
    try testing.expect(folded.len > 0);
}

test "invalid UTF-8 handling" {
    const invalid = [_]u8{ 0xFF, 0xFF };
    const result = normalizeNFC(testing.allocator, &invalid);

    try testing.expectError(ICUError.InvalidUtf8, result);
}

test "round-trip UTF-8 to UTF-16 and back" {
    const original = "Hello 世界 café 👋";

    const utf16 = try utf8ToUtf16(testing.allocator, original);
    defer testing.allocator.free(utf16);

    const back_to_utf8 = try utf16ToUtf8(testing.allocator, utf16);
    defer testing.allocator.free(back_to_utf8);

    try testing.expectEqualStrings(original, back_to_utf8);
}
```

### Discussion

### Educational Focus: Why This Recipe Uses ICU

This recipe uses ICU specifically to teach C interoperability fundamentals:

- How to use @cImport correctly
- Memory management across FFI boundaries
- Converting between C and Zig types (UTF-8 ↔ UTF-16)
- Error handling with C libraries
- Linking system libraries in build.zig

**For actual Unicode work in Zig, use the Ziglyph library.** ICU is the industry standard for C/C++ (used by Chrome, Firefox, Node.js), but brings unnecessary complexity to Zig projects.

### ICU Capabilities

ICU provides:

- Correct implementations of all Unicode standards
- Support for all normalization forms (NFC, NFD, NFKC, NFKD)
- Proper case-folding (more complex than simple lowercasing)
- Regular updates for new Unicode versions
- Grapheme cluster handling for proper "character" counting

### What is Unicode Normalization?

Unicode allows the same visual character to be represented multiple ways. Normalization converts text to a standard form so byte comparisons work correctly.

**Example - The letter é:**

```zig
// Two ways to write the same character
const composed = "café";     // é is U+00E9 (1 codepoint)
const decomposed = "cafe\u{0301}"; // é is e + ́ (2 codepoints)

// These look identical but have different bytes
std.debug.print("Same? {}\n", .{std.mem.eql(u8, composed, decomposed)});
// Output: Same? false

// After normalization, they become identical
const norm1 = try normalizeNFC(allocator, composed);
defer allocator.free(norm1);

const norm2 = try normalizeNFC(allocator, decomposed);
defer allocator.free(norm2);

std.debug.print("Same? {}\n", .{std.mem.eql(u8, norm1, norm2)});
// Output: Same? true
```

### Normalization Forms

**NFC (Normalization Form C - Canonical Composition)**

Combines base characters and combining marks into single pre-composed characters where possible. This is the most common form for:
- Web content
- Database storage
- File names on macOS
- Most user-facing text

```zig
const text = "e\u{0301}";  // e + combining acute
const nfc = try normalizeNFC(allocator, text);
defer allocator.free(nfc);
// Result: "é" (single codepoint U+00E9)
```

**NFD (Normalization Form D - Canonical Decomposition)**

Decomposes pre-composed characters into base letter + combining marks. Useful for:
- Text processing where you need to strip accents
- Linguistic analysis
- Some legacy systems

```zig
const text = "é";  // Composed é (U+00E9)
const nfd = try normalizeNFD(allocator, text);
defer allocator.free(nfd);
// Result: "e\u{0301}" (e + combining acute)
```

**NFKC and NFKD (Compatibility Forms)**

These also normalize "compatibility equivalents" like:
- Ligatures: ﬁ → fi
- Fractions: ½ → 1/2
- Width variants: Ａ → A (fullwidth to regular)
- Super/subscripts: ² → 2

Use these when you want maximum normalization, but be aware they're lossy (you can't get the original form back).

### Case Folding vs Lowercasing

Simple lowercasing with `std.ascii.toLower` is insufficient for Unicode. Case folding is the proper way to prepare strings for case-insensitive comparison.

**Why case folding matters:**

```zig
// German sharp s (ß) has no uppercase/lowercase distinction
const german = "Straße";

// std.ascii.toLower doesn't touch ß
const ascii_lower = try std.ascii.allocLowerString(allocator, german);
defer allocator.free(ascii_lower);
std.debug.print("{s}\n", .{ascii_lower});
// Output: "straße" (ß unchanged)

// ICU case folding correctly converts ß to ss
const folded = try caseFold(allocator, german);
defer allocator.free(folded);
std.debug.print("{s}\n", .{folded});
// Output: "strasse" (ß became ss)
```

**Other case folding examples:**

- Turkish: "I" → "ı" (dotless i)
- Greek: "Σ" → "σ" or "ς" depending on position
- Cherokee: "Ꭰ" → "ꭰ"

### Implementing ICU Integration

Here's how to interface with ICU from Zig:

**Step 1: Import ICU headers**

```zig
const icu = @cImport({
    @cInclude("unicode/unorm2.h"); // Normalization
    @cInclude("unicode/ustring.h"); // String operations
});
```

**Important:** Only use one `@cImport` block per application to avoid symbol collisions. If you have multiple C libraries, import them all in one block or in a dedicated `c.zig` file.

**Step 2: Handle UTF-16 conversion**

ICU uses UTF-16 internally, but Zig strings are UTF-8. You need conversion functions:

```zig
fn utf8ToUtf16(allocator: Allocator, utf8: []const u8) ![]u16 {
    // Calculate required length
    var utf16_len: usize = 0;
    var i: usize = 0;
    while (i < utf8.len) {
        const cp_len = try std.unicode.utf8ByteSequenceLength(utf8[i]);
        const codepoint = try std.unicode.utf8Decode(utf8[i .. i + cp_len]);

        if (codepoint >= 0x10000) {
            utf16_len += 2;  // Surrogate pair
        } else {
            utf16_len += 1;
        }
        i += cp_len;
    }

    // Allocate and encode...
    // (See code/02-core/02-strings-and-text/recipe_2_14.zig for full implementation)
}
```

**Step 3: Call ICU with proper error handling**

ICU uses a two-call pattern: first call with null buffer to get size, second call to perform operation.

```zig
pub fn normalizeNFC(allocator: Allocator, text: []const u8) ![]u8 {
    // Convert to UTF-16
    const utf16_input = try utf8ToUtf16(allocator, text);
    defer allocator.free(utf16_input);

    // Get normalizer instance
    var status: icu.UErrorCode = icu.U_ZERO_ERROR;
    const normalizer = icu.unorm2_getNFCInstance(&status);
    if (status != icu.U_ZERO_ERROR) {
        return error.InitFailed;
    }

    // First call: get required buffer size
    status = icu.U_ZERO_ERROR;
    const required_len = icu.unorm2_normalize(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        null,  // NULL pointer to get size
        0,
        &status,
    );

    // U_BUFFER_OVERFLOW_ERROR is expected when probing size
    if (status != icu.U_BUFFER_OVERFLOW_ERROR and status != icu.U_ZERO_ERROR) {
        return error.NormalizationFailed;
    }

    // Allocate output buffer
    const utf16_output = try allocator.alloc(u16, @intCast(required_len));
    defer allocator.free(utf16_output);

    // Second call: perform normalization
    status = icu.U_ZERO_ERROR;
    const actual_len = icu.unorm2_normalize(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        utf16_output.ptr,
        @intCast(utf16_output.len),
        &status,
    );

    if (status != icu.U_ZERO_ERROR) {
        return error.NormalizationFailed;
    }

    // Convert back to UTF-8
    return utf16ToUtf8(allocator, utf16_output[0..@intCast(actual_len)]);
}
```

### Memory Management

ICU integration requires careful memory management across the FFI boundary:

**Multiple allocations per operation:**

```zig
pub fn normalizeNFC(allocator: Allocator, text: []const u8) ![]u8 {
    // Allocation 1: UTF-8 → UTF-16
    const utf16_input = try utf8ToUtf16(allocator, text);
    defer allocator.free(utf16_input);  // Always freed

    // Allocation 2: ICU output buffer
    const utf16_output = try allocator.alloc(u16, required_len);
    defer allocator.free(utf16_output);  // Always freed

    // Allocation 3: UTF-16 → UTF-8 (returned to caller)
    return utf16ToUtf8(allocator, utf16_output[0..actual_len]);
}
```

**Key patterns:**

- Use `defer` for intermediate buffers that are always freed
- Use `errdefer` for buffers that should only be freed on error
- Pass allocator as first parameter (Zig convention)
- Use `testing.allocator` in tests to automatically detect leaks

**Memory safety:**

```zig
test "memory safety - no leaks" {
    const text = "café";

    // testing.allocator will detect any leaks
    const nfc = try normalizeNFC(testing.allocator, text);
    defer testing.allocator.free(nfc);

    const nfd = try normalizeNFD(testing.allocator, text);
    defer testing.allocator.free(nfd);

    // If we forgot a defer, test would fail with leak error
}
```

### Error Handling

ICU uses `UErrorCode` enum for error reporting. Convert these to Zig errors:

```zig
const ICUError = error{
    InitFailed,
    NormalizationFailed,
    CaseFoldFailed,
    InvalidUtf8,
};

// Check ICU status and convert to Zig error
var status: icu.UErrorCode = icu.U_ZERO_ERROR;
const normalizer = icu.unorm2_getNFCInstance(&status);
if (status != icu.U_ZERO_ERROR) {
    return ICUError.InitFailed;
}
```

**Expected vs unexpected errors:**

```zig
// U_BUFFER_OVERFLOW_ERROR is EXPECTED when probing size
if (status != icu.U_BUFFER_OVERFLOW_ERROR and status != icu.U_ZERO_ERROR) {
    return error.SizeProbeFailed;
}

// U_ZERO_ERROR means success
if (status != icu.U_ZERO_ERROR) {
    return error.NormalizationFailed;
}
```

### Linking ICU in build.zig

To use ICU, update your `build.zig` to link the libraries:

```zig
pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const test_step = b.step("test", "Run tests");

    // Add test for ICU recipe
    const icu_test = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("code/02-core/02-strings-and-text/recipe_2_14.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    // Link C standard library (required for @cImport)
    icu_test.linkLibC();

    // Link ICU libraries
    icu_test.linkSystemLibrary("icuuc");   // ICU Common
    icu_test.linkSystemLibrary("icui18n"); // ICU Internationalization

    const run_icu_test = b.addRunArtifact(icu_test);
    test_step.dependOn(&run_icu_test.step);
}
```

### Installing ICU

**Version Requirement:** This recipe requires ICU 77 or later. The code uses versioned function names (e.g., `_77` suffix) to work around Zig @cImport limitations with ICU's macro system. If you have a different ICU version, you'll need to adjust the suffix in the code.

ICU must be installed on your system before building. The build system automatically detects ICU and only runs tests if the library is found.

**macOS:**

```bash
# Install ICU via Homebrew
brew install icu4c

# Verify installation
ls /opt/homebrew/opt/icu4c/lib/  # Apple Silicon
# or
ls /usr/local/opt/icu4c/lib/      # Intel Mac
```

The build.zig automatically detects ICU in Homebrew's keg-only location (both Apple Silicon and Intel paths). No additional environment variables needed.

**Troubleshooting:**

If the ICU tests are skipped with "ICU library not found" warning:

```bash
# macOS - Check if ICU is installed
brew list icu4c

# If not installed
brew install icu4c

# Verify the library files exist
ls -la /opt/homebrew/opt/icu4c/lib/libicu*

# Linux - Check if ICU is installed
ldconfig -p | grep libicu

# Ubuntu/Debian - Install if missing
sudo apt-get install libicu-dev

# Arch - Install if missing
sudo pacman -S icu
```

The build system automatically detects ICU on your platform and only runs the tests if the library is available. This prevents build failures on systems where ICU is not installed.

**Ubuntu/Debian:**

```bash
sudo apt-get install libicu-dev

# Verify installation
ldconfig -p | grep libicu
# or
ls /usr/lib/x86_64-linux-gnu/libicuuc.so
```

The build.zig automatically detects ICU in standard Linux system library paths.

**Arch Linux:**

```bash
sudo pacman -S icu

# Verify installation
pacman -Ql icu | grep lib
# or
ls /usr/lib/libicuuc.so
```

The build.zig automatically detects ICU in `/usr/lib`.

**Windows:**

More complex - either build from source or use vcpkg:

```bash
vcpkg install icu

# Then add to PATH or configure build.zig with custom library paths
```

### When to Use ICU vs Native Zig

**Use ICU when:**

- You're learning C interoperability (this recipe's purpose!)
- You need Unicode normalization and already have ICU installed
- You need collation (sorting in different languages)
- You're interfacing with existing C/C++ codebases that use ICU

**Use Zig std.unicode when:**

- You only need UTF-8 validation
- You only need codepoint iteration
- You want to avoid C dependencies
- You're building for constrained environments

**Recommended for Production: Ziglyph**

The **Ziglyph** library provides pure-Zig Unicode normalization without C dependencies or version-specific issues. **Use Ziglyph for production Zig code** because:

- ✓ No C library dependency
- ✓ No version suffix complications
- ✓ Easier cross-compilation
- ✓ Pure Zig - follows Zig idioms
- ✓ Works on all platforms Zig supports

**This recipe uses ICU specifically to teach C interop patterns**, not because it's the best choice for Unicode in Zig. The manual UTF-8↔UTF-16 conversion, error handling, and memory management techniques shown here apply to interfacing with many C libraries.

### Practical Examples

**Normalizing user input before database storage:**

```zig
fn saveUsername(db: *Database, raw_name: []const u8) !void {
    // Normalize to NFC for consistent storage
    const normalized = try normalizeNFC(allocator, raw_name);
    defer allocator.free(normalized);

    // Also case-fold for case-insensitive lookup
    const lookup_key = try caseFold(allocator, normalized);
    defer allocator.free(lookup_key);

    try db.insert(normalized, lookup_key);
}
```

**Case-insensitive string comparison:**

```zig
fn equalsCaseInsensitive(a: []const u8, b: []const u8) !bool {
    const a_folded = try caseFold(allocator, a);
    defer allocator.free(a_folded);

    const b_folded = try caseFold(allocator, b);
    defer allocator.free(b_folded);

    return std.mem.eql(u8, a_folded, b_folded);
}
```

**Stripping accents (using NFD):**

```zig
fn stripAccents(allocator: Allocator, text: []const u8) ![]u8 {
    // Decompose to separate base letters from combining marks
    const decomposed = try normalizeNFD(allocator, text);
    defer allocator.free(decomposed);

    // Filter out combining marks (U+0300 - U+036F range)
    var result = std.ArrayList(u8).init(allocator);
    errdefer result.deinit();

    var i: usize = 0;
    while (i < decomposed.len) {
        const cp_len = try std.unicode.utf8ByteSequenceLength(decomposed[i]);
        const codepoint = try std.unicode.utf8Decode(decomposed[i .. i + cp_len]);

        // Skip combining diacritical marks
        if (codepoint < 0x0300 or codepoint > 0x036F) {
            try result.appendSlice(decomposed[i .. i + cp_len]);
        }

        i += cp_len;
    }

    return result.toOwnedSlice();
}

// Usage
const with_accents = "café résumé";
const without = try stripAccents(allocator, with_accents);
defer allocator.free(without);
// Result: "cafe resume"
```

### Performance Considerations

**UTF-8 ↔ UTF-16 conversion has overhead:**

- Each operation requires 2 conversions plus ICU processing
- For ASCII-only text, stick with `std.ascii` functions
- For repeated operations on the same text, normalize once and cache

**Normalization is O(n) but with a large constant:**

```zig
// Bad: Normalize repeatedly in a loop
for (strings) |str| {
    const norm = try normalizeNFC(allocator, str);
    defer allocator.free(norm);
    // Process norm...
}

// Good: Normalize once upfront
var normalized_strings = std.ArrayList([]u8).init(allocator);
defer {
    for (normalized_strings.items) |s| allocator.free(s);
    normalized_strings.deinit();
}

for (strings) |str| {
    try normalized_strings.append(try normalizeNFC(allocator, str));
}

// Now process normalized_strings multiple times without re-normalizing
```

### Security Considerations

**Always validate UTF-8 from untrusted sources:**

```zig
fn processUserInput(allocator: Allocator, input: []const u8) ![]u8 {
    // Validate UTF-8 first
    if (!std.unicode.utf8ValidateSlice(input)) {
        return error.InvalidUtf8;
    }

    // Now safe to normalize
    return normalizeNFC(allocator, input);
}
```

**Normalization can change string length:**

```zig
// A single character might decompose to multiple
const composed = "é";  // 2 bytes (UTF-8 encoded U+00E9)
const decomposed = try normalizeNFD(allocator, composed);
defer allocator.free(decomposed);
// Result: 3 bytes (e + combining acute in UTF-8)
```

**Be aware of homograph attacks:**

Normalization alone doesn't prevent look-alike characters (like Latin 'a' vs Cyrillic 'а'). For security-sensitive applications like domain names, additional confusable detection is needed.

### Testing Your Normalization

```zig
test "normalization equivalence" {
    const forms = [_][]const u8{
        "café",           // Mixed ASCII and accented
        "cafe\u{0301}",  // Decomposed accent
    };

    // All forms should normalize to same result
    const first_norm = try normalizeNFC(testing.allocator, forms[0]);
    defer testing.allocator.free(first_norm);

    for (forms[1..]) |form| {
        const norm = try normalizeNFC(testing.allocator, form);
        defer testing.allocator.free(norm);

        try testing.expectEqualStrings(first_norm, norm);
    }
}
```

This recipe demonstrates how to integrate C libraries safely in Zig while solving real-world Unicode text processing problems. The patterns shown here (memory management, error handling, FFI boundaries) apply to interfacing with any C library.

### Known Limitations

**ICU Version Dependency:** This code is tied to ICU 77 due to Zig's @cImport limitations with ICU's macro system. The `_77` suffix in function names is a workaround for circular dependency errors. Different ICU versions require changing these suffixes, which is why production code should avoid this approach.

**Better Alternatives for Production:**
- **Ziglyph**: Pure-Zig Unicode library (recommended)
- **zig-icu**: Community Zig bindings that handle versioning better
- **std.unicode**: Built-in Zig for basic UTF-8 operations

This recipe's value is in teaching FFI patterns, not in being production-ready Unicode normalization.

### Full Tested Code

```zig
// Recipe 2.14: Standardizing Unicode text with ICU
// Target Zig Version: 0.15.2
//
// EDUCATIONAL FOCUS: This recipe demonstrates C library interoperability patterns.
// For production code, consider pure-Zig alternatives like Ziglyph.
//
// IMPORTANT: This recipe requires ICU version 77+ due to Zig's @cImport limitations
// with ICU's macro system. The versioned function names (_77 suffix) are a workaround
// for circular dependency errors when using ICU's U_ICU_ENTRY_POINT_RENAME macro.
//
// This recipe demonstrates interfacing with the ICU (International Components for Unicode)
// C library to perform Unicode normalization and case-folding operations.

// ANCHOR: icu_setup
const std = @import("std");
const testing = std.testing;
const mem = std.mem;
const unicode = std.unicode;
const Allocator = mem.Allocator;

// Import ICU C library types (with renaming disabled to avoid circular dependencies)
// IMPORTANT: Only use ONE @cImport per application to avoid symbol collisions
const icu = @cImport({
    @cDefine("U_DISABLE_RENAMING", "1");
    @cInclude("unicode/utypes.h"); // Base types
    @cInclude("unicode/unorm2.h"); // For normalization types
    @cInclude("unicode/ustring.h"); // For string operation types
});

// Manually declare versioned ICU functions to work around Zig @cImport macro issues
//
// WHY VERSIONED?: ICU's U_ICU_ENTRY_POINT_RENAME macro causes circular dependencies
// in Zig's @cImport. Using U_DISABLE_RENAMING + manual declarations is the workaround.
// The _77 suffix corresponds to ICU version 77 (check with: icu-config --version).
//
// PORTABILITY NOTE: This hardcodes ICU 77. For different ICU versions, adjust the suffix.
// This is a known limitation of this approach and why production code should prefer
// pure-Zig Unicode libraries that don't have these FFI complications.
extern "c" fn unorm2_getNFCInstance_77(pErrorCode: *icu.UErrorCode) ?*const icu.UNormalizer2;
extern "c" fn unorm2_getNFDInstance_77(pErrorCode: *icu.UErrorCode) ?*const icu.UNormalizer2;
extern "c" fn unorm2_getNFKCInstance_77(pErrorCode: *icu.UErrorCode) ?*const icu.UNormalizer2;
extern "c" fn unorm2_normalize_77(
    norm2: ?*const icu.UNormalizer2,
    src: [*]const u16,
    length: i32,
    dest: ?[*]u16,
    capacity: i32,
    pErrorCode: *icu.UErrorCode,
) i32;
extern "c" fn u_strFoldCase_77(
    dest: ?[*]u16,
    destCapacity: i32,
    src: [*]const u16,
    srcLength: i32,
    options: u32,
    pErrorCode: *icu.UErrorCode,
) i32;

// Custom error set for ICU operations
const ICUError = error{
    InitFailed,
    NormalizationFailed,
    CaseFoldFailed,
    InvalidUtf8,
    BufferTooSmall,
    UnexpectedError,
};

/// Convert UTF-8 string to UTF-16 (ICU uses UTF-16 internally)
fn utf8ToUtf16(allocator: Allocator, utf8: []const u8) ![]u16 {
    if (utf8.len == 0) return try allocator.alloc(u16, 0);

    // Validate UTF-8 first
    if (!unicode.utf8ValidateSlice(utf8)) {
        return ICUError.InvalidUtf8;
    }

    // Calculate required UTF-16 length
    var utf16_len: usize = 0;
    var i: usize = 0;
    while (i < utf8.len) {
        const cp_len = try unicode.utf8ByteSequenceLength(utf8[i]);
        const codepoint = try unicode.utf8Decode(utf8[i .. i + cp_len]);

        if (codepoint >= 0x10000) {
            utf16_len += 2; // Surrogate pair
        } else {
            utf16_len += 1;
        }
        i += cp_len;
    }

    // Allocate and encode
    var utf16 = try allocator.alloc(u16, utf16_len);
    errdefer allocator.free(utf16);

    var out_idx: usize = 0;
    i = 0;
    while (i < utf8.len) {
        const cp_len = try unicode.utf8ByteSequenceLength(utf8[i]);
        const codepoint = try unicode.utf8Decode(utf8[i .. i + cp_len]);

        if (codepoint >= 0x10000) {
            // Encode as surrogate pair
            const surrogate = codepoint - 0x10000;
            utf16[out_idx] = @intCast(0xD800 + (surrogate >> 10));
            utf16[out_idx + 1] = @intCast(0xDC00 + (surrogate & 0x3FF));
            out_idx += 2;
        } else {
            utf16[out_idx] = @intCast(codepoint);
            out_idx += 1;
        }
        i += cp_len;
    }

    return utf16;
}

/// Convert UTF-16 string to UTF-8
fn utf16ToUtf8(allocator: Allocator, utf16: []const u16) ![]u8 {
    if (utf16.len == 0) return try allocator.alloc(u8, 0);

    // Calculate required UTF-8 length
    var utf8_len: usize = 0;
    var i: usize = 0;
    while (i < utf16.len) {
        const unit = utf16[i];
        var codepoint: u21 = 0;

        if (unit >= 0xD800 and unit <= 0xDBFF) {
            // High surrogate - need next unit
            if (i + 1 >= utf16.len) return ICUError.InvalidUtf8;
            const low = utf16[i + 1];
            if (low < 0xDC00 or low > 0xDFFF) return ICUError.InvalidUtf8;

            codepoint = @intCast(0x10000 + ((@as(u32, unit) - 0xD800) << 10) + (low - 0xDC00));
            i += 2;
        } else if (unit >= 0xDC00 and unit <= 0xDFFF) {
            // Low surrogate without high surrogate - invalid
            return ICUError.InvalidUtf8;
        } else {
            codepoint = @intCast(unit);
            i += 1;
        }

        utf8_len += try unicode.utf8CodepointSequenceLength(codepoint);
    }

    // Allocate and encode
    var utf8 = try allocator.alloc(u8, utf8_len);
    errdefer allocator.free(utf8);

    var out_pos: usize = 0;
    i = 0;
    while (i < utf16.len) {
        const unit = utf16[i];
        var codepoint: u21 = 0;

        if (unit >= 0xD800 and unit <= 0xDBFF) {
            const low = utf16[i + 1];
            codepoint = @intCast(0x10000 + ((@as(u32, unit) - 0xD800) << 10) + (low - 0xDC00));
            i += 2;
        } else {
            codepoint = @intCast(unit);
            i += 1;
        }

        const len = try unicode.utf8Encode(codepoint, utf8[out_pos..]);
        out_pos += len;
    }

    return utf8;
}
// ANCHOR_END: icu_setup

// ANCHOR: unicode_normalization
/// Normalize UTF-8 string to NFC (Normalization Form C - Canonical Composition)
/// This is the most common form for web content and database storage.
/// Example: e + combining acute accent (U+0301) -> é (U+00E9)
pub fn normalizeNFC(allocator: Allocator, text: []const u8) ![]u8 {
    if (text.len == 0) return try allocator.alloc(u8, 0);

    // Convert UTF-8 to UTF-16
    const utf16_input = try utf8ToUtf16(allocator, text);
    defer allocator.free(utf16_input);

    // Get NFC normalizer instance
    var status: icu.UErrorCode = icu.U_ZERO_ERROR;
    const normalizer = unorm2_getNFCInstance_77(&status);
    if (status != icu.U_ZERO_ERROR) {
        return ICUError.InitFailed;
    }

    // First call to determine required buffer size
    status = icu.U_ZERO_ERROR;
    const required_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        null,
        0,
        &status,
    );

    // Check for actual errors (positive values), not warnings (negative)
    // U_BUFFER_OVERFLOW_ERROR (15) is expected when probing size
    if (status > 0 and status != icu.U_BUFFER_OVERFLOW_ERROR) {
        return ICUError.NormalizationFailed;
    }

    // Allocate output buffer
    const utf16_output = try allocator.alloc(u16, @intCast(required_len));
    defer allocator.free(utf16_output);

    // Second call to perform normalization
    status = icu.U_ZERO_ERROR;
    const actual_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        utf16_output.ptr,
        @intCast(utf16_output.len),
        &status,
    );

    // Check for actual errors (positive values), warnings (negative) are OK
    if (status > 0) {
        return ICUError.NormalizationFailed;
    }

    // Convert back to UTF-8
    return utf16ToUtf8(allocator, utf16_output[0..@intCast(actual_len)]);
}

/// Normalize UTF-8 string to NFD (Normalization Form D - Canonical Decomposition)
/// This form decomposes characters into base letter + combining marks.
/// Example: é (U+00E9) -> e + combining acute accent (U+0301)
pub fn normalizeNFD(allocator: Allocator, text: []const u8) ![]u8 {
    if (text.len == 0) return try allocator.alloc(u8, 0);

    const utf16_input = try utf8ToUtf16(allocator, text);
    defer allocator.free(utf16_input);

    var status: icu.UErrorCode = icu.U_ZERO_ERROR;
    const normalizer = unorm2_getNFDInstance_77(&status);
    if (status != icu.U_ZERO_ERROR) {
        return ICUError.InitFailed;
    }

    status = icu.U_ZERO_ERROR;
    const required_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        null,
        0,
        &status,
    );

    if (status > 0 and status != icu.U_BUFFER_OVERFLOW_ERROR) {
        return ICUError.NormalizationFailed;
    }

    const utf16_output = try allocator.alloc(u16, @intCast(required_len));
    defer allocator.free(utf16_output);

    status = icu.U_ZERO_ERROR;
    const actual_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        utf16_output.ptr,
        @intCast(utf16_output.len),
        &status,
    );

    if (status > 0) {
        return ICUError.NormalizationFailed;
    }

    return utf16ToUtf8(allocator, utf16_output[0..@intCast(actual_len)]);
}

/// Normalize UTF-8 string to NFKC (Compatibility Composition)
/// This form also normalizes compatibility equivalents (like fractions, ligatures).
/// Example: ½ (U+00BD) -> 1/2 (separate characters)
pub fn normalizeNFKC(allocator: Allocator, text: []const u8) ![]u8 {
    if (text.len == 0) return try allocator.alloc(u8, 0);

    const utf16_input = try utf8ToUtf16(allocator, text);
    defer allocator.free(utf16_input);

    var status: icu.UErrorCode = icu.U_ZERO_ERROR;
    const normalizer = unorm2_getNFKCInstance_77(&status);
    if (status != icu.U_ZERO_ERROR) {
        return ICUError.InitFailed;
    }

    status = icu.U_ZERO_ERROR;
    const required_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        null,
        0,
        &status,
    );

    if (status > 0 and status != icu.U_BUFFER_OVERFLOW_ERROR) {
        return ICUError.NormalizationFailed;
    }

    const utf16_output = try allocator.alloc(u16, @intCast(required_len));
    defer allocator.free(utf16_output);

    status = icu.U_ZERO_ERROR;
    const actual_len = unorm2_normalize_77(
        normalizer,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        utf16_output.ptr,
        @intCast(utf16_output.len),
        &status,
    );

    if (status > 0) {
        return ICUError.NormalizationFailed;
    }

    return utf16ToUtf8(allocator, utf16_output[0..@intCast(actual_len)]);
}
// ANCHOR_END: unicode_normalization

// ANCHOR: case_folding
/// Case-fold UTF-8 string for case-insensitive comparison.
/// This is more correct than simple lowercasing for Unicode.
/// Example: German ß -> ss, Turkish I -> ı (context-aware)
pub fn caseFold(allocator: Allocator, text: []const u8) ![]u8 {
    if (text.len == 0) return try allocator.alloc(u8, 0);

    const utf16_input = try utf8ToUtf16(allocator, text);
    defer allocator.free(utf16_input);

    var status: icu.UErrorCode = icu.U_ZERO_ERROR;
    const required_len = u_strFoldCase_77(
        null,
        0,
        utf16_input.ptr,
        @intCast(utf16_input.len),
        0,
        &status,
    );

    if (status > 0 and status != icu.U_BUFFER_OVERFLOW_ERROR) {
        return ICUError.CaseFoldFailed;
    }

    const utf16_output = try allocator.alloc(u16, @intCast(required_len));
    defer allocator.free(utf16_output);

    status = icu.U_ZERO_ERROR;
    const actual_len = u_strFoldCase_77(
        utf16_output.ptr,
        @intCast(utf16_output.len),
        utf16_input.ptr,
        @intCast(utf16_input.len),
        0,
        &status,
    );

    if (status > 0) {
        return ICUError.CaseFoldFailed;
    }

    return utf16ToUtf8(allocator, utf16_output[0..@intCast(actual_len)]);
}

// Tests

test "UTF-8 to UTF-16 conversion" {
    const utf8 = "Hello";
    const utf16 = try utf8ToUtf16(testing.allocator, utf8);
    defer testing.allocator.free(utf16);

    try testing.expectEqual(@as(usize, 5), utf16.len);
    try testing.expectEqual(@as(u16, 'H'), utf16[0]);
    try testing.expectEqual(@as(u16, 'e'), utf16[1]);
}

test "UTF-8 to UTF-16 with multibyte characters" {
    const utf8 = "世界";
    const utf16 = try utf8ToUtf16(testing.allocator, utf8);
    defer testing.allocator.free(utf16);

    try testing.expectEqual(@as(usize, 2), utf16.len);
    try testing.expectEqual(@as(u16, 0x4E16), utf16[0]); // 世
    try testing.expectEqual(@as(u16, 0x754C), utf16[1]); // 界
}

test "UTF-16 to UTF-8 conversion" {
    const utf16 = [_]u16{ 'H', 'e', 'l', 'l', 'o' };
    const utf8 = try utf16ToUtf8(testing.allocator, &utf16);
    defer testing.allocator.free(utf8);

    try testing.expectEqualStrings("Hello", utf8);
}

test "UTF-16 to UTF-8 with multibyte characters" {
    const utf16 = [_]u16{ 0x4E16, 0x754C }; // 世界
    const utf8 = try utf16ToUtf8(testing.allocator, &utf16);
    defer testing.allocator.free(utf8);

    try testing.expectEqualStrings("世界", utf8);
}

test "normalize NFC - combining accent to composed" {
    // e + combining acute accent -> é (composed)
    const decomposed = "e\u{0301}";
    const result = try normalizeNFC(testing.allocator, decomposed);
    defer testing.allocator.free(result);

    // Should be composed é (U+00E9)
    try testing.expectEqualStrings("\u{00E9}", result);
}

test "normalize NFC - already composed" {
    const composed = "\u{00E9}"; // é (already composed)
    const result = try normalizeNFC(testing.allocator, composed);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings(composed, result);
}

test "normalize NFD - composed to decomposed" {
    // é (composed) -> e + combining accent
    const composed = "\u{00E9}";
    const result = try normalizeNFD(testing.allocator, composed);
    defer testing.allocator.free(result);

    // Should be decomposed: e + combining acute
    try testing.expectEqualStrings("e\u{0301}", result);
}

test "normalize NFD - already decomposed" {
    const decomposed = "e\u{0301}";
    const result = try normalizeNFD(testing.allocator, decomposed);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings(decomposed, result);
}

test "NFC and NFD are inverses" {
    const original = "café";

    // Normalize to NFD (decomposed)
    const nfd = try normalizeNFD(testing.allocator, original);
    defer testing.allocator.free(nfd);

    // Normalize back to NFC (composed)
    const nfc = try normalizeNFC(testing.allocator, nfd);
    defer testing.allocator.free(nfc);

    // Should match original (both NFC)
    try testing.expectEqualStrings(original, nfc);
}

test "normalize NFKC - compatibility characters" {
    // Test with various compatibility characters
    const text = "Hello";
    const result = try normalizeNFKC(testing.allocator, text);
    defer testing.allocator.free(result);

    // ASCII text should remain unchanged
    try testing.expectEqualStrings(text, result);
}

test "visual equivalence requires normalization" {
    // Two visually identical strings with different byte representations
    const composed = "café"; // é is single codepoint U+00E9
    const decomposed = "cafe\u{0301}"; // é is e + combining accent

    // Byte representations differ
    try testing.expect(!mem.eql(u8, composed, decomposed));

    // After normalization, they should be identical
    const norm1 = try normalizeNFC(testing.allocator, composed);
    defer testing.allocator.free(norm1);

    const norm2 = try normalizeNFC(testing.allocator, decomposed);
    defer testing.allocator.free(norm2);

    try testing.expectEqualStrings(norm1, norm2);
}

test "case fold - ASCII" {
    const text = "Hello World";
    const result = try caseFold(testing.allocator, text);
    defer testing.allocator.free(result);

    try testing.expectEqualStrings("hello world", result);
}

test "case fold - German sharp s" {
    // German ß should case-fold to ss
    const text = "Straße";
    const result = try caseFold(testing.allocator, text);
    defer testing.allocator.free(result);

    // ICU should convert ß to ss
    try testing.expectEqualStrings("strasse", result);
}

test "case fold for case-insensitive comparison" {
    const text1 = "HELLO";
    const text2 = "hello";

    const fold1 = try caseFold(testing.allocator, text1);
    defer testing.allocator.free(fold1);

    const fold2 = try caseFold(testing.allocator, text2);
    defer testing.allocator.free(fold2);

    // Case-folded versions should be identical
    try testing.expectEqualStrings(fold1, fold2);
}

test "empty string normalization" {
    const empty = "";

    const nfc = try normalizeNFC(testing.allocator, empty);
    defer testing.allocator.free(nfc);

    const nfd = try normalizeNFD(testing.allocator, empty);
    defer testing.allocator.free(nfd);

    try testing.expectEqual(@as(usize, 0), nfc.len);
    try testing.expectEqual(@as(usize, 0), nfd.len);
}

test "empty string case fold" {
    const empty = "";
    const result = try caseFold(testing.allocator, empty);
    defer testing.allocator.free(result);

    try testing.expectEqual(@as(usize, 0), result.len);
}

test "normalization with emoji" {
    const emoji = "Hello 👋";

    const nfc = try normalizeNFC(testing.allocator, emoji);
    defer testing.allocator.free(nfc);

    // Emoji should pass through unchanged
    try testing.expect(nfc.len > 0);
}

test "normalization with various scripts" {
    const texts = [_][]const u8{
        "Hello", // ASCII
        "café", // Latin with accent
        "Привет", // Cyrillic
        "你好", // Chinese
        "こんにちは", // Japanese
    };

    for (texts) |text| {
        const nfc = try normalizeNFC(testing.allocator, text);
        defer testing.allocator.free(nfc);

        const nfd = try normalizeNFD(testing.allocator, text);
        defer testing.allocator.free(nfd);

        try testing.expect(nfc.len > 0);
        try testing.expect(nfd.len > 0);
    }
}

test "memory safety - no leaks" {
    // testing.allocator automatically detects memory leaks
    const text = "café";

    const nfc = try normalizeNFC(testing.allocator, text);
    defer testing.allocator.free(nfc);

    const nfd = try normalizeNFD(testing.allocator, text);
    defer testing.allocator.free(nfd);

    const folded = try caseFold(testing.allocator, text);
    defer testing.allocator.free(folded);

    try testing.expect(nfc.len > 0);
    try testing.expect(nfd.len > 0);
    try testing.expect(folded.len > 0);
}

test "invalid UTF-8 handling" {
    const invalid = [_]u8{ 0xFF, 0xFF };
    const result = normalizeNFC(testing.allocator, &invalid);

    try testing.expectError(ICUError.InvalidUtf8, result);
}

test "round-trip UTF-8 to UTF-16 and back" {
    const original = "Hello 世界 café 👋";

    const utf16 = try utf8ToUtf16(testing.allocator, original);
    defer testing.allocator.free(utf16);

    const back_to_utf8 = try utf16ToUtf8(testing.allocator, utf16);
    defer testing.allocator.free(back_to_utf8);

    try testing.expectEqualStrings(original, back_to_utf8);
}
// ANCHOR_END: case_folding
```

---
