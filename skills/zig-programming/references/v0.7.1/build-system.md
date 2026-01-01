# Build System

*Building projects with Zig*


---

<!-- Source: 44-zig-build-system.md -->


The Zig Build System provides a cross-platform, dependency-free way to declare
the logic required to build a project. With this system, the logic to build
a project is written in a build.zig file, using the Zig Build System API to
declare and configure build artifacts and other tasks.

Some examples of tasks the build system can help with:

- Creating build artifacts by executing the Zig compiler. This includes
  building Zig source code as well as C and C++ source code.
- Capturing user-configured options and using those options to configure
  the build.
- Surfacing build configuration as [comptime](32-comptime.md#comptime) values by providing a
  file that can be [imported](#import) by Zig code.
- Caching build artifacts to avoid unnecessarily repeating steps.
- Executing build artifacts or system-installed tools.
- Running tests and verifying the output of executing a build artifact matches
  the expected value.
- Running `zig fmt` on a codebase or a subset of it.
- Custom tasks.

To use the build system, run `zig build --help`
to see a command-line usage help menu. This will include project-specific
options that were declared in the build.zig script.

### Building an Executable

This `build.zig` file is automatically generated
by `zig init-exe`.

```zig
const Builder = @import("std").build.Builder;

pub fn build(b: *Builder) void {
    // Standard target options allows the person running `zig build` to choose
    // what target to build for. Here we do not override the defaults, which
    // means any target is allowed, and the default is native. Other options
    // for restricting supported target set are available.
    const target = b.standardTargetOptions(.{});

    // Standard release options allow the person running `zig build` to select
    // between Debug, ReleaseSafe, ReleaseFast, and ReleaseSmall.
    const mode = b.standardReleaseOptions();

    const exe = b.addExecutable("example", "src/main.zig");
    exe.setTarget(target);
    exe.setBuildMode(mode);
    exe.install();

    const run_cmd = exe.run();
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the app");
    run_step.dependOn(&run_cmd.step);
}

```

### Building a Library

This `build.zig` file is automatically generated
by `zig init-lib`.

```zig
const Builder = @import("std").build.Builder;

pub fn build(b: *Builder) void {
    const mode = b.standardReleaseOptions();
    const lib = b.addStaticLibrary("example", "src/main.zig");
    lib.setBuildMode(mode);
    lib.install();

    var main_tests = b.addTest("src/main.zig");
    main_tests.setBuildMode(mode);

    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&main_tests.step);
}

```

### Compiling C Source Code

```zig
lib.addCSourceFile("src/lib.c", &[_][]const u8{
    "-Wall",
    "-Wextra",
    "-Werror",
});

```


---
