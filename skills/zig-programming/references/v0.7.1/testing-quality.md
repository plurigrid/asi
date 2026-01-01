# Testing and Code Quality

*Testing framework, undefined behavior, and best practices*


---

<!-- Source: 48-style-guide.md -->


These coding conventions are not enforced by the compiler, but they are shipped in
this documentation along with the compiler in order to provide a point of
reference, should anyone wish to point to an authority on agreed upon Zig
coding style.

### Whitespace

- 4 space indentation
- Open braces on same line, unless you need to wrap.
- If a list of things is longer than 2, put each item on its own line and
  exercise the ability to put an extra comma at the end.
- Line length: aim for 100; use common sense.

### Names

Roughly speaking: `camelCaseFunctionName`, `TitleCaseTypeName`,
`snake_case_variable_name`. More precisely:

- If `x` is a `type`
  then `x` should be `TitleCase`, unless it
  is a `struct` with 0 fields and is never meant to be instantiated,
  in which case it is considered to be a "namespace" and uses `snake_case`.
- If `x` is callable, and `x`'s return type is
  `type`, then `x` should be `TitleCase`.
- If `x` is otherwise callable, then `x` should
  be `camelCase`.
- Otherwise, `x` should be `snake_case`.

Acronyms, initialisms, proper nouns, or any other word that has capitalization
rules in written English are subject to naming conventions just like any other
word. Even acronyms that are only 2 letters long are subject to these
conventions.

File names fall into two categories: types and namespaces. If the file
(implicity a struct) has top level fields, it should be named like any
other struct with fields using `TitleCase`. Otherwise,
it should use `snake_case`. Directory names should be
`snake_case`.

These are general rules of thumb; if it makes sense to do something different,
do what makes sense. For example, if there is an established convention such as
`ENOENT`, follow the established convention.

### Examples

```zig
const namespace_name = @import("dir_name/file_name.zig");
const TypeName = @import("dir_name/TypeName.zig");
var global_var: i32 = undefined;
const const_name = 42;
const primitive_type_alias = f32;
const string_alias = []u8;

const StructName = struct {
    field: i32,
};
const StructAlias = StructName;

fn functionName(param_name: TypeName) void {
    var functionPointer = functionName;
    functionPointer();
    functionPointer = otherFunction;
    functionPointer();
}
const functionAlias = functionName;

fn ListTemplateFunction(comptime ChildType: type, comptime fixed_size: usize) type {
    return List(ChildType, fixed_size);
}

fn ShortList(comptime T: type, comptime n: usize) type {
    return struct {
        field_name: [n]T,
        fn methodName() void {}
    };
}

// The word XML loses its casing when used in Zig identifiers.
const xml_document =
    \\<?xml version="1.0" encoding="UTF-8"?>
    \\<document>
    \\</document>
;
const XmlParser = struct {
    field: i32,
};

// The initials BE (Big Endian) are just another word in Zig identifier names.
fn readU32Be() u32 {}

```

See the Zig Standard Library for more examples.


---

<!-- Source: 49-source-encoding.md -->


Zig source code is encoded in UTF-8. An invalid UTF-8 byte sequence results in a compile error.

Throughout all zig source code (including in comments), some codepoints are never allowed:

- Ascii control characters, except for U+000a (LF): U+0000 - U+0009, U+000b - U+0001f, U+007f. (Note that Windows line endings (CRLF) are not allowed, and hard tabs are not allowed.)
- Non-Ascii Unicode line endings: U+0085 (NEL), U+2028 (LS), U+2029 (PS).

The codepoint U+000a (LF) (which is encoded as the single-byte value 0x0a) is the line terminator character. This character always terminates a line of zig source code (except possibly the last line of the file).

For some discussion on the rationale behind these design decisions, see [issue #663](https://github.com/ziglang/zig/issues/663)


---
