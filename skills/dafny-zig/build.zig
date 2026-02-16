const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // DAST (Dafny AST) module - IR representation
    const dast_mod = b.addModule("dast", .{
        .root_source_file = b.path("src/dast.zig"),
        .target = target,
        .optimize = optimize,
    });

    // ZAST (Zig AST) module - output representation
    const zast_mod = b.addModule("zast", .{
        .root_source_file = b.path("src/zast.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Runtime library module
    const runtime_mod = b.addModule("dafny_runtime", .{
        .root_source_file = b.path("src/runtime.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Compiler module - DAST to ZAST translation
    const compiler_mod = b.addModule("compiler", .{
        .root_source_file = b.path("src/compiler.zig"),
        .target = target,
        .optimize = optimize,
    });
    compiler_mod.addImport("dast", dast_mod);
    compiler_mod.addImport("zast", zast_mod);

    // Main executable
    const main_mod = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    main_mod.addImport("dast", dast_mod);
    main_mod.addImport("zast", zast_mod);
    main_mod.addImport("compiler", compiler_mod);
    main_mod.addImport("dafny_runtime", runtime_mod);

    const exe = b.addExecutable(.{
        .name = "dafny-zig",
        .root_module = main_mod,
    });
    b.installArtifact(exe);

    // Run step
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }
    const run_step = b.step("run", "Run the Dafny-to-Zig compiler");
    run_step.dependOn(&run_cmd.step);

    // Tests
    const dast_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/dast.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    const run_dast_tests = b.addRunArtifact(dast_tests);

    const zast_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/zast.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    const run_zast_tests = b.addRunArtifact(zast_tests);

    const compiler_test_mod = b.createModule(.{
        .root_source_file = b.path("src/compiler.zig"),
        .target = target,
        .optimize = optimize,
    });
    compiler_test_mod.addImport("dast", dast_mod);
    compiler_test_mod.addImport("zast", zast_mod);

    const compiler_tests = b.addTest(.{
        .root_module = compiler_test_mod,
    });
    const run_compiler_tests = b.addRunArtifact(compiler_tests);

    const runtime_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/runtime.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    const run_runtime_tests = b.addRunArtifact(runtime_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_dast_tests.step);
    test_step.dependOn(&run_zast_tests.step);
    test_step.dependOn(&run_compiler_tests.step);
    test_step.dependOn(&run_runtime_tests.step);
}
