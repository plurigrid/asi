// Target Zig Version: 0.15.2
// For other versions, see references/version-differences.md

const std = @import("std");

// CLI Application Template
// Demonstrates argument parsing, subcommands, and user interaction

const Config = struct {
    verbose: bool = false,
    output_file: ?[]const u8 = null,
    input_files: std.ArrayList([]const u8),

    pub fn init(allocator: std.mem.Allocator) Config {
        return .{
            .input_files = std.ArrayList([]const u8).init(allocator),
        };
    }

    pub fn deinit(self: *Config) void {
        self.input_files.deinit();
    }
};

fn printUsage() void {
    const usage =
        \\Usage: myapp [OPTIONS] COMMAND [ARGS]
        \\
        \\Commands:
        \\  process   Process input files
        \\  convert   Convert file format
        \\  help      Show this help message
        \\
        \\Options:
        \\  -v, --verbose        Enable verbose output
        \\  -o, --output FILE    Specify output file
        \\  -h, --help           Show this help message
        \\
    ;
    std.debug.print("{s}", .{usage});
}

fn processCommand(config: Config, args: []const []const u8) !void {
    const stdout = std.io.getStdOut().writer();

    if (config.verbose) {
        try stdout.print("Processing files (verbose mode)...\n", .{});
    }

    // TODO: Implement your processing logic here
    for (args) |arg| {
        if (config.verbose) {
            try stdout.print("Processing: {s}\n", .{arg});
        }

        // Your processing code here
    }

    if (config.output_file) |output| {
        if (config.verbose) {
            try stdout.print("Writing output to: {s}\n", .{output});
        }
        // TODO: Write results to output file
    }

    try stdout.print("Processing complete!\n", .{});
}

fn convertCommand(config: Config, args: []const []const u8) !void {
    const stdout = std.io.getStdOut().writer();

    if (config.verbose) {
        try stdout.print("Converting files (verbose mode)...\n", .{});
    }

    if (args.len < 1) {
        try stdout.print("Error: No input file specified\n", .{});
        return error.MissingArgument;
    }

    const input_file = args[0];
    const output_file = config.output_file orelse "output.txt";

    if (config.verbose) {
        try stdout.print("Converting {s} -> {s}\n", .{ input_file, output_file });
    }

    // TODO: Implement your conversion logic here

    try stdout.print("Conversion complete!\n", .{});
}

pub fn main() !void {
    // Setup allocator
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Get command line arguments
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    // Parse command line arguments
    var config = Config.init(allocator);
    defer config.deinit();

    var command: ?[]const u8 = null;
    var command_args = std.ArrayList([]const u8).init(allocator);
    defer command_args.deinit();

    var i: usize = 1; // Skip program name
    while (i < args.len) : (i += 1) {
        const arg = args[i];

        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) {
            printUsage();
            return;
        } else if (std.mem.eql(u8, arg, "-v") or std.mem.eql(u8, arg, "--verbose")) {
            config.verbose = true;
        } else if (std.mem.eql(u8, arg, "-o") or std.mem.eql(u8, arg, "--output")) {
            if (i + 1 >= args.len) {
                std.debug.print("Error: --output requires a filename\n", .{});
                return error.MissingArgument;
            }
            i += 1;
            config.output_file = args[i];
        } else if (command == null and !std.mem.startsWith(u8, arg, "-")) {
            // First non-option argument is the command
            command = arg;
        } else {
            // Subsequent arguments go to the command
            try command_args.append(arg);
        }
    }

    // Execute command
    const cmd = command orelse {
        std.debug.print("Error: No command specified\n\n", .{});
        printUsage();
        return error.MissingCommand;
    };

    if (std.mem.eql(u8, cmd, "process")) {
        try processCommand(config, command_args.items);
    } else if (std.mem.eql(u8, cmd, "convert")) {
        try convertCommand(config, command_args.items);
    } else if (std.mem.eql(u8, cmd, "help")) {
        printUsage();
    } else {
        std.debug.print("Error: Unknown command '{s}'\n\n", .{cmd});
        printUsage();
        return error.UnknownCommand;
    }
}

// Tests
const testing = std.testing;

test "Config initialization" {
    const allocator = testing.allocator;
    var config = Config.init(allocator);
    defer config.deinit();

    try testing.expect(!config.verbose);
    try testing.expect(config.output_file == null);
    try testing.expectEqual(@as(usize, 0), config.input_files.items.len);
}
