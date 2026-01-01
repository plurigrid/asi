# C Interoperability

*Interfacing with C code and cross-compilation*


---

### C

Although Zig is independent of C, and, unlike most other languages, does not depend on libc,
Zig acknowledges the importance of interacting with existing C code.

There are a few ways that Zig facilitates C interop.

#### C Type Primitives

These have guaranteed C ABI compatibility and can be used like any other type.

- `c_char`
- `c_short`
- `c_ushort`
- `c_int`
- `c_uint`
- `c_long`
- `c_ulong`
- `c_longlong`
- `c_ulonglong`
- `c_longdouble`

To interop with the C `void` type, use `anyopaque`.

See also:

- [Primitive Types](#Primitive-Types)

#### Import from C Header File

The `@cImport` builtin function can be used
to directly import symbols from `.h` files:

**`cImport_builtin.zig`:**

```zig
const c = @cImport({
    // See https://github.com/ziglang/zig/issues/515
    @cDefine("_NO_CRT_STDIO_INLINE", "1");
    @cInclude("stdio.h");
});
pub fn main() void {
    _ = c.printf("hello\n");
}

```

**Shell:**

```shell
$ zig build-exe cImport_builtin.zig -lc
$ ./cImport_builtin
hello

```

The `@cImport` function takes an expression as a parameter.
This expression is evaluated at compile-time and is used to control
preprocessor directives and include multiple `.h` files:

**`@cImport Expression`:**

```zig
const builtin = @import("builtin");

const c = @cImport({
    @cDefine("NDEBUG", builtin.mode == .ReleaseFast);
    if (something) {
        @cDefine("_GNU_SOURCE", {});
    }
    @cInclude("stdlib.h");
    if (something) {
        @cUndef("_GNU_SOURCE");
    }
    @cInclude("soundio.h");
});

```

See also:

- [@cImport](#cImport)
- [@cInclude](#cInclude)
- [@cDefine](#cDefine)
- [@cUndef](#cUndef)
- [@import](#import)

#### C Translation CLI

Zig's C translation capability is available as a CLI tool via `zig translate-c`.
It requires a single filename as an argument. It may also take a set of optional flags that are
forwarded to clang. It writes the translated file to stdout.

##### Command line flags

- `-I`:
  Specify a search directory for include files. May be used multiple times. Equivalent to
  [
  clang's `-I` flag](https://releases.llvm.org/12.0.0/tools/clang/docs/ClangCommandLineReference.html#cmdoption-clang-i-dir). The current directory is *not* included by default;
  use `-I.` to include it.
- `-D`: Define a preprocessor macro. Equivalent to
  [
  clang's `-D` flag](https://releases.llvm.org/12.0.0/tools/clang/docs/ClangCommandLineReference.html#cmdoption-clang-d-macro).
- `-cflags [flags] --`: Pass arbitrary additional
  [command line
  flags](https://releases.llvm.org/12.0.0/tools/clang/docs/ClangCommandLineReference.html) to clang. Note: the list of flags must end with `--`
- `-target`: The [target triple](47-targets.md#Targets) for the translated Zig code.
  If no target is specified, the current host target will be used.

##### Using -target and -cflags

**Important!** When translating C code with `zig translate-c`,
you **must** use the same `-target` triple that you will use when compiling
the translated code. In addition, you **must** ensure that the `-cflags` used,
if any, match the cflags used by code on the target system. Using the incorrect `-target`
or `-cflags` could result in clang or Zig parse failures, or subtle ABI incompatibilities
when linking with C code.

**varytarget.h:**

```c
long FOO = __LONG_MAX__;

```

**Shell:**

```shell
$ zig translate-c -target thumb-freestanding-gnueabihf varytarget.h|grep FOO
pub export var FOO: c_long = 2147483647;
$ zig translate-c -target x86_64-macos-gnu varytarget.h|grep FOO
pub export var FOO: c_long = 9223372036854775807;

```

**varycflags.h:**

```c
enum FOO { BAR };
int do_something(enum FOO foo);

```

**Shell:**

```shell
$ zig translate-c varycflags.h|grep -B1 do_something
pub const enum_FOO = c_uint;
pub extern fn do_something(foo: enum_FOO) c_int;
$ zig translate-c -cflags -fshort-enums -- varycflags.h|grep -B1 do_something
pub const enum_FOO = u8;
pub extern fn do_something(foo: enum_FOO) c_int;

```

##### @cImport vs translate-c

`@cImport` and `zig translate-c` use the same underlying
C translation functionality, so on a technical level they are equivalent. In practice,
`@cImport` is useful as a way to quickly and easily access numeric constants, typedefs,
and record types without needing any extra setup. If you need to pass [cflags](#Using--target-and--cflags)
to clang, or if you would like to edit the translated code, it is recommended to use
`zig translate-c` and save the results to a file. Common reasons for editing
the generated code include: changing `anytype` parameters in function-like macros to more
specific types; changing `[*c]T` pointers to `[*]T` or
`*T` pointers for improved type safety; and
[enabling or disabling runtime safety](#setRuntimeSafety) within specific functions.

See also:

- [Targets](47-targets.md#Targets)
- [C Type Primitives](#C-Type-Primitives)
- [Pointers](13-pointers.md#Pointers)
- [C Pointers](#C-Pointers)
- [Import from C Header File](#Import-from-C-Header-File)
- [@cInclude](#cInclude)
- [@cImport](#cImport)
- [@setRuntimeSafety](#setRuntimeSafety)

#### C Translation Caching

The C translation feature (whether used via `zig translate-c` or
`@cImport`) integrates with the Zig caching system. Subsequent runs with
the same source file, target, and cflags will use the cache instead of repeatedly translating
the same code.

To see where the cached files are stored when compiling code that uses `@cImport`,
use the `--verbose-cimport` flag:

**`verbose_cimport_flag.zig`:**

```zig
const c = @cImport({
    @cDefine("_NO_CRT_STDIO_INLINE", "1");
    @cInclude("stdio.h");
});
pub fn main() void {
    _ = c;
}

```

**Shell:**

```shell
$ zig build-exe verbose_cimport_flag.zig -lc --verbose-cimport
info(compilation): C import source: /home/andy/dev/zig/.zig-cache/o/f9216ef6681abef94b056af4b875b0bd/cimport.h
info(compilation): C import .d file: /home/andy/dev/zig/.zig-cache/o/f9216ef6681abef94b056af4b875b0bd/cimport.h.d
$ ./verbose_cimport_flag

```

`cimport.h` contains the file to translate (constructed from calls to
`@cInclude`, `@cDefine`, and `@cUndef`),
`cimport.h.d` is the list of file dependencies, and
`cimport.zig` contains the translated output.

See also:

- [Import from C Header File](#Import-from-C-Header-File)
- [C Translation CLI](#C-Translation-CLI)
- [@cInclude](#cInclude)
- [@cImport](#cImport)

#### Translation failures

Some C constructs cannot be translated to Zig - for example, *goto*,
structs with bitfields, and token-pasting macros. Zig employs *demotion* to allow translation
to continue in the face of non-translatable entities.

Demotion comes in three varieties - [opaque](18-opaque.md#opaque), *extern*, and
`@compileError`.
C structs and unions that cannot be translated correctly will be translated as `opaque{}`.
Functions that contain opaque types or code constructs that cannot be translated will be demoted
to `extern` declarations.
Thus, non-translatable types can still be used as pointers, and non-translatable functions
can be called so long as the linker is aware of the compiled function.

`@compileError` is used when top-level definitions (global variables,
function prototypes, macros) cannot be translated or demoted. Since Zig uses lazy analysis for
top-level declarations, untranslatable entities will not cause a compile error in your code unless
you actually use them.

See also:

- [opaque](18-opaque.md#opaque)
- [extern](#extern)
- [@compileError](#compileError)

#### C Macros

C Translation makes a best-effort attempt to translate function-like macros into equivalent
Zig functions. Since C macros operate at the level of lexical tokens, not all C macros
can be translated to Zig. Macros that cannot be translated will be demoted to
`@compileError`. Note that C code which *uses* macros will be
translated without any additional issues (since Zig operates on the pre-processed source
with macros expanded). It is merely the macros themselves which may not be translatable to
Zig.

Consider the following example:

**macro.c:**

```c
#define MAKELOCAL(NAME, INIT) int NAME = INIT
int foo(void) {
   MAKELOCAL(a, 1);
   MAKELOCAL(b, 2);
   return a + b;
}

```

**Shell:**

```shell
$ zig translate-c macro.c > macro.zig

```

**`macro.zig`:**

```zig
pub export fn foo() c_int {
    var a: c_int = 1;
    _ = &a;
    var b: c_int = 2;
    _ = &b;
    return a + b;
}
pub const MAKELOCAL = @compileError("unable to translate C expr: unexpected token .Equal"); // macro.c:1:9

```

Note that `foo` was translated correctly despite using a non-translatable
macro. `MAKELOCAL` was demoted to `@compileError` since
it cannot be expressed as a Zig function; this simply means that you cannot directly use
`MAKELOCAL` from Zig.

See also:

- [@compileError](#compileError)

#### C Pointers

This type is to be avoided whenever possible. The only valid reason for using a C pointer is in
auto-generated code from translating C code.

When importing C header files, it is ambiguous whether pointers should be translated as
single-item pointers (`*T`) or many-item pointers (`[*]T`).
C pointers are a compromise so that Zig code can utilize translated header files directly.

`[*c]T` - C pointer.

- Supports all the syntax of the other two pointer types (`*T`) and (`[*]T`).
- Coerces to other pointer types, as well as [Optional Pointers](#Optional-Pointers).
  When a C pointer is coerced to a non-optional pointer, safety-checked
  [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior) occurs if the address is 0.
- Allows address 0. On non-freestanding targets, dereferencing address 0 is safety-checked
  [Illegal Behavior](40-illegal-behavior.md#Illegal-Behavior). Optional C pointers introduce another bit to keep track of
  null, just like `?usize`. Note that creating an optional C pointer
  is unnecessary as one can use normal [Optional Pointers](#Optional-Pointers).
- Supports [Type Coercion](#Type-Coercion) to and from integers.
- Supports comparison with integers.
- Does not support Zig-only pointer attributes such as alignment. Use normal [Pointers](13-pointers.md#Pointers)
  please!

When a C pointer is pointing to a single struct (not an array), dereference the C pointer to
access the struct's fields or member data. That syntax looks like
this:

`ptr_to_struct.*.struct_member`

This is comparable to doing `->` in C.

When a C pointer is pointing to an array of structs, the syntax reverts to this:

`ptr_to_struct_array[index].struct_member`

#### C Variadic Functions

Zig supports extern variadic functions.

**`test_variadic_function.zig`:**

```zig
const std = @import("std");
const testing = std.testing;

pub extern "c" fn printf(format: [*:0]const u8, ...) c_int;

test "variadic function" {
    try testing.expect(printf("Hello, world!\n") == 14);
    try testing.expect(@typeInfo(@TypeOf(printf)).@"fn".is_var_args);
}

```

**Shell:**

```shell
$ zig test test_variadic_function.zig -lc
1/1 test_variadic_function.test.variadic function...OK
All 1 tests passed.
Hello, world!

```

Variadic functions can be implemented using [@cVaStart](#cVaStart), [@cVaEnd](#cVaEnd), [@cVaArg](#cVaArg) and [@cVaCopy](#cVaCopy).

**`test_defining_variadic_function.zig`:**

```zig
const std = @import("std");
const testing = std.testing;
const builtin = @import("builtin");

fn add(count: c_int, ...) callconv(.c) c_int {
    var ap = @cVaStart();
    defer @cVaEnd(&ap);
    var i: usize = 0;
    var sum: c_int = 0;
    while (i < count) : (i += 1) {
        sum += @cVaArg(&ap, c_int);
    }
    return sum;
}

test "defining a variadic function" {
    if (builtin.cpu.arch == .aarch64 and builtin.os.tag != .macos) {
        // https://github.com/ziglang/zig/issues/14096
        return error.SkipZigTest;
    }
    if (builtin.cpu.arch == .x86_64 and builtin.os.tag == .windows) {
        // https://github.com/ziglang/zig/issues/16961
        return error.SkipZigTest;
    }

    try std.testing.expectEqual(@as(c_int, 0), add(0));
    try std.testing.expectEqual(@as(c_int, 1), add(1, @as(c_int, 1)));
    try std.testing.expectEqual(@as(c_int, 3), add(2, @as(c_int, 1), @as(c_int, 2)));
}

```

**Shell:**

```shell
$ zig test test_defining_variadic_function.zig
1/1 test_defining_variadic_function.test.defining a variadic function...OK
All 1 tests passed.

```

#### Exporting a C Library

One of the primary use cases for Zig is exporting a library with the C ABI for other programming languages
to call into. The `export` keyword in front of functions, variables, and types causes them to
be part of the library API:

**`mathtest.zig`:**

```zig
export fn add(a: i32, b: i32) i32 {
    return a + b;
}

```

To make a static library:

**Shell:**

```shell
$ zig build-lib mathtest.zig

```

To make a shared library:

**Shell:**

```shell
$ zig build-lib mathtest.zig -dynamic

```

Here is an example with the [Zig Build System](44-zig-build-system.md#Zig-Build-System):

**test.c:**

```c
// This header is generated by zig from mathtest.zig
#include "mathtest.h"
#include <stdio.h>

int main(int argc, char **argv) {
    int32_t result = add(42, 1337);
    printf("%d\n", result);
    return 0;
}

```

**`build_c.zig`:**

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const lib = b.addLibrary(.{
        .linkage = .dynamic,
        .name = "mathtest",
        .root_module = b.createModule(.{
            .root_source_file = b.path("mathtest.zig"),
        }),
        .version = .{ .major = 1, .minor = 0, .patch = 0 },
    });
    const exe = b.addExecutable(.{
        .name = "test",
        .root_module = b.createModule(.{
            .link_libc = true,
        }),
    });
    exe.root_module.addCSourceFile(.{ .file = b.path("test.c"), .flags = &.{"-std=c99"} });
    exe.root_module.linkLibrary(lib);

    b.default_step.dependOn(&exe.step);

    const run_cmd = exe.run();

    const test_step = b.step("test", "Test the program");
    test_step.dependOn(&run_cmd.step);
}

```

**Shell:**

```shell
$ zig build test
1379

```

See also:

- [export](#export)

#### Mixing Object Files

You can mix Zig object files with any other object files that respect the C ABI. Example:

**`base64.zig`:**

```zig
const base64 = @import("std").base64;

export fn decode_base_64(
    dest_ptr: [*]u8,
    dest_len: usize,
    source_ptr: [*]const u8,
    source_len: usize,
) usize {
    const src = source_ptr[0..source_len];
    const dest = dest_ptr[0..dest_len];
    const base64_decoder = base64.standard.Decoder;
    const decoded_size = base64_decoder.calcSizeForSlice(src) catch unreachable;
    base64_decoder.decode(dest[0..decoded_size], src) catch unreachable;
    return decoded_size;
}

```

**test.c:**

```c
// This header is generated by zig from base64.zig
#include "base64.h"

#include <string.h>
#include <stdio.h>

int main(int argc, char **argv) {
    const char *encoded = "YWxsIHlvdXIgYmFzZSBhcmUgYmVsb25nIHRvIHVz";
    char buf[200];

    size_t len = decode_base_64(buf, 200, encoded, strlen(encoded));
    buf[len] = 0;
    puts(buf);

    return 0;
}

```

**`build_object.zig`:**

```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const obj = b.addObject(.{
        .name = "base64",
        .root_module = b.createModule(.{
            .root_source_file = b.path("base64.zig"),
        }),
    });

    const exe = b.addExecutable(.{
        .name = "test",
        .root_module = b.createModule(.{
            .link_libc = true,
        }),
    });
    exe.root_module.addCSourceFile(.{ .file = b.path("test.c"), .flags = &.{"-std=c99"} });
    exe.root_module.addObject(obj);
    b.installArtifact(exe);
}

```

**Shell:**

```shell
$ zig build
$ ./zig-out/bin/test
all your base are belong to us

```

See also:

- [Targets](47-targets.md#Targets)
- [Zig Build System](44-zig-build-system.md#Zig-Build-System)


---

### WebAssembly

Zig supports building for WebAssembly out of the box.

#### Freestanding

For host environments like the web browser and nodejs, build as an executable using the freestanding
OS target. Here's an example of running Zig code compiled to WebAssembly with nodejs.

**`math.zig`:**

```zig
extern fn print(i32) void;

export fn add(a: i32, b: i32) void {
    print(a + b);
}

```

**Shell:**

```shell
$ zig build-exe math.zig -target wasm32-freestanding -fno-entry --export=add

```

**test.js:**

```javascript
const fs = require('fs');
const source = fs.readFileSync("./math.wasm");
const typedArray = new Uint8Array(source);

WebAssembly.instantiate(typedArray, {
  env: {
    print: (result) => { console.log(`The result is ${result}`); }
  }}).then(result => {
  const add = result.instance.exports.add;
  add(1, 2);
});

```

**Shell:**

```shell
$ node test.js
The result is 3

```

#### WASI

Zig's support for WebAssembly System Interface (WASI) is under active development.
Example of using the standard library and reading command line arguments:

**`wasi_args.zig`:**

```zig
const std = @import("std");

pub fn main() !void {
    var general_purpose_allocator: std.heap.GeneralPurposeAllocator(.{}) = .init;
    const gpa = general_purpose_allocator.allocator();
    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);

    for (args, 0..) |arg, i| {
        std.debug.print("{}: {s}\n", .{ i, arg });
    }
}

```

**Shell:**

```shell
$ zig build-exe wasi_args.zig -target wasm32-wasi

```

**Shell:**

```shell
$ wasmtime wasi_args.wasm 123 hello
0: wasi_args.wasm
1: 123
2: hello

```

A more interesting example would be extracting the list of preopens from the runtime.
This is now supported in the standard library via `std.fs.wasi.Preopens`:

**`wasi_preopens.zig`:**

```zig
const std = @import("std");
const fs = std.fs;

pub fn main() !void {
    var general_purpose_allocator: std.heap.GeneralPurposeAllocator(.{}) = .init;
    const gpa = general_purpose_allocator.allocator();

    var arena_instance = std.heap.ArenaAllocator.init(gpa);
    defer arena_instance.deinit();
    const arena = arena_instance.allocator();

    const preopens = try fs.wasi.preopensAlloc(arena);

    for (preopens.names, 0..) |preopen, i| {
        std.debug.print("{}: {s}\n", .{ i, preopen });
    }
}

```

**Shell:**

```shell
$ zig build-exe wasi_preopens.zig -target wasm32-wasi

```

**Shell:**

```shell
$ wasmtime --dir=. wasi_preopens.wasm
0: stdin
1: stdout
2: stderr
3: .

```


---

### Targets

**Target** refers to the computer that will be used to run an executable.
It is composed of the CPU architecture, the set of enabled CPU features, operating system,
minimum and maximum operating system version, ABI, and ABI version.

Zig is a general-purpose programming language which means that it is designed to
generate optimal code for a large set of targets. The command `zig targets`
provides information about all of the targets the compiler is aware of.

When no target option is provided to the compiler, the default choice
is to target the **host computer**, meaning that the
resulting executable will be *unsuitable for copying to a different
computer*. In order to copy an executable to another computer, the compiler
needs to know about the target requirements via the `-target` option.

The Zig Standard Library (`@import("std")`) has
cross-platform abstractions, making the same source code viable on many targets.
Some code is more portable than other code. In general, Zig code is extremely
portable compared to other programming languages.

Each platform requires its own implementations to make Zig's
cross-platform abstractions work. These implementations are at various
degrees of completion. Each tagged release of the compiler comes with
release notes that provide the full support table for each target.


---
