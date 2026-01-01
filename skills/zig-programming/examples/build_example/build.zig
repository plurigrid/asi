const std = @import("std");

pub fn build(b: *std.Build) void {
    // Standard target and optimization options
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Create executable
    const exe = b.addExecutable(.{
        .name = "build_example",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Install the executable
    b.installArtifact(exe);

    // Create run step
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());

    // Allow passing arguments to the application
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    // Create "run" step
    const run_step = b.step("run", "Run the application");
    run_step.dependOn(&run_cmd.step);

    // Create unit tests for main module
    const main_tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Create run step for tests
    const run_main_tests = b.addRunArtifact(main_tests);

    // Create unit tests for math_utils module
    const math_tests = b.addTest(.{
        .root_source_file = b.path("src/math_utils.zig"),
        .target = target,
        .optimize = optimize,
    });

    const run_math_tests = b.addRunArtifact(math_tests);

    // Create unit tests for string_utils module
    const string_tests = b.addTest(.{
        .root_source_file = b.path("src/string_utils.zig"),
        .target = target,
        .optimize = optimize,
    });

    const run_string_tests = b.addRunArtifact(string_tests);

    // Create "test" step that runs all tests
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_main_tests.step);
    test_step.dependOn(&run_math_tests.step);
    test_step.dependOn(&run_string_tests.step);

    // Create a library from math_utils (optional - demonstrates library creation)
    const math_lib = b.addStaticLibrary(.{
        .name = "math_utils",
        .root_source_file = b.path("src/math_utils.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Install the library (optional)
    const install_lib = b.addInstallArtifact(math_lib, .{});
    const lib_step = b.step("lib", "Build and install the math library");
    lib_step.dependOn(&install_lib.step);
}
