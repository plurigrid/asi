// Target Zig Version: 0.15.2
// For other versions, see references/version-differences.md

const std = @import("std");

pub fn build(b: *std.Build) void {
    // Standard target and optimization options
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Create executable
    const exe = b.addExecutable(.{
        .name = "myapp",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Install the executable
    b.installArtifact(exe);

    // Create run command
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());

    // Allow arguments to be passed
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    // Create run step
    const run_step = b.step("run", "Run the app");
    run_step.dependOn(&run_cmd.step);

    // Create unit tests
    const unit_tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    const run_unit_tests = b.addRunArtifact(unit_tests);

    // Create test step
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_unit_tests.step);
}