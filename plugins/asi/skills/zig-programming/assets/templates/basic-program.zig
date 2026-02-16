// Target Zig Version: 0.15.2
// For other versions, see references/version-differences.md

const std = @import("std");

pub fn main() !void {
    // Get a general purpose allocator
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Get stdout writer
    const stdout = std.io.getStdOut().writer();

    // Your code here
    try stdout.print("Hello, Zig!\n", .{});
}