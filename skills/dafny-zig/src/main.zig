const std = @import("std");
const dast = @import("dast");
const zast = @import("zast");
const compiler = @import("compiler");

/// Parse errors for DAST JSON parsing
const ParseError = error{
    ExpectedObject,
    ExpectedString,
    MissingField,
    MissingType,
    UnknownItemType,
    JsonParseError,
    OutOfMemory,
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    if (args.len < 2) {
        try printUsage();
        return;
    }

    const command = args[1];

    if (std.mem.eql(u8, command, "help") or std.mem.eql(u8, command, "--help") or std.mem.eql(u8, command, "-h")) {
        try printUsage();
        return;
    }

    if (std.mem.eql(u8, command, "compile")) {
        if (args.len < 3) {
            std.debug.print("Error: compile requires an input file\n", .{});
            return;
        }
        try compileFile(allocator, args[2], if (args.len > 3) args[3] else null);
        return;
    }

    if (std.mem.eql(u8, command, "version")) {
        std.debug.print("dafny-zig 0.1.0\n", .{});
        std.debug.print("Dafny to Zig compiler backend\n", .{});
        return;
    }

    std.debug.print("Unknown command: {s}\n", .{command});
    try printUsage();
}

fn printUsage() !void {
    std.debug.print(
        \\dafny-zig - Dafny to Zig compiler backend
        \\
        \\USAGE:
        \\    dafny-zig <COMMAND> [OPTIONS]
        \\
        \\COMMANDS:
        \\    compile <input.json> [output.zig]    Compile DAST JSON to Zig source
        \\    version                              Print version information
        \\    help                                 Print this help message
        \\
        \\EXAMPLES:
        \\    dafny-zig compile module.dast.json output.zig
        \\    dafny-zig compile module.dast.json  # outputs to stdout
        \\
        \\DESCRIPTION:
        \\    This tool reads Dafny's intermediate representation (DAST) in JSON format
        \\    and produces equivalent Zig source code. It is designed to be used as a
        \\    backend for the Dafny compiler.
        \\
        \\    To generate DAST JSON from Dafny source:
        \\        dafny translate-from dafny --to=lib --output=module.dast.json module.dfy
        \\
        \\
    , .{});
}

fn compileFile(allocator: std.mem.Allocator, input_path: []const u8, output_path: ?[]const u8) !void {
    // Read input file
    const file = std.fs.cwd().openFile(input_path, .{}) catch |err| {
        std.debug.print("Error: Could not open input file '{s}': {}\n", .{ input_path, err });
        return;
    };
    defer file.close();

    const content = file.readToEndAlloc(allocator, 10 * 1024 * 1024) catch |err| {
        std.debug.print("Error: Could not read input file: {}\n", .{err});
        return;
    };
    defer allocator.free(content);

    // Parse DAST JSON
    const module = parseDastJson(allocator, content) catch |err| {
        std.debug.print("Error: Could not parse DAST JSON: {}\n", .{err});
        return;
    };

    // Compile to ZAST
    var comp = compiler.Compiler.init(allocator);
    defer comp.deinit();

    const source_file = comp.compileModule(&module) catch |err| {
        std.debug.print("Error: Compilation failed: {}\n", .{err});
        return;
    };

    // Write output
    if (output_path) |out_path| {
        const out_file = std.fs.cwd().createFile(out_path, .{}) catch |err| {
            std.debug.print("Error: Could not create output file '{s}': {}\n", .{ out_path, err });
            return;
        };
        defer out_file.close();

        var buf: [8192]u8 = undefined;
        var writer = out_file.writer(&buf);
        source_file.write(&writer.interface) catch |err| {
            std.debug.print("Error: Could not write output: {}\n", .{err});
            return;
        };
        writer.interface.flush() catch {};

        std.debug.print("Successfully compiled to '{s}'\n", .{out_path});
    } else {
        // Write to stdout
        const stdout = std.fs.File.stdout();
        var buf: [8192]u8 = undefined;
        var writer = stdout.writer(&buf);
        source_file.write(&writer.interface) catch |err| {
            std.debug.print("Error: Could not write output: {}\n", .{err});
            return;
        };
        writer.interface.flush() catch {};
    }
}

/// Parse DAST from JSON
fn parseDastJson(allocator: std.mem.Allocator, content: []const u8) ParseError!dast.Module {
    // Basic JSON parsing for DAST
    // The actual Dafny compiler outputs DAST in a specific JSON format
    // This is a simplified parser that handles the core structure

    const parsed = std.json.parseFromSlice(std.json.Value, allocator, content, .{}) catch |err| {
        std.debug.print("JSON parse error: {}\n", .{err});
        return error.JsonParseError;
    };
    defer parsed.deinit();

    return try parseModule(allocator, parsed.value);
}

fn parseModule(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.Module {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    // Get module name
    const name_json = obj.get("name") orelse return error.MissingField;
    const name = try parseName(name_json);

    // Get attributes
    const attrs = if (obj.get("attributes")) |attrs_json| try parseAttributes(allocator, attrs_json) else &[_]dast.Attribute{};

    // Get body items
    var body_items = std.ArrayListUnmanaged(dast.ModuleItem){};
    if (obj.get("body")) |body_json| {
        if (body_json == .array) {
            for (body_json.array.items) |item_json| {
                if (parseModuleItem(allocator, item_json)) |item| {
                    try body_items.append(allocator, item);
                } else |_| {
                    // Skip items we can't parse
                }
            }
        }
    }

    return .{
        .name = name,
        .doc_string = "",
        .attributes = attrs,
        .requires_externs = obj.get("requiresExterns") != null,
        .body = body_items.toOwnedSlice(allocator) catch &[_]dast.ModuleItem{},
    };
}

fn parseName(json: std.json.Value) ParseError!dast.Name {
    if (json == .string) {
        return .{
            .dafny_name = json.string,
            .compile_name = null,
        };
    }
    if (json == .object) {
        const obj = json.object;
        return .{
            .dafny_name = if (obj.get("dafnyName")) |n| (if (n == .string) n.string else "") else "",
            .compile_name = if (obj.get("compileName")) |n| (if (n == .string) n.string else null) else null,
        };
    }
    return .{ .dafny_name = "", .compile_name = null };
}

fn parseAttributes(allocator: std.mem.Allocator, json: std.json.Value) ParseError![]const dast.Attribute {
    if (json != .array) return &[_]dast.Attribute{};

    var attrs = std.ArrayListUnmanaged(dast.Attribute){};
    for (json.array.items) |attr_json| {
        if (attr_json == .object) {
            const obj = attr_json.object;
            const name = if (obj.get("name")) |n| (if (n == .string) n.string else "") else "";
            try attrs.append(allocator, .{
                .name = name,
                .args = &[_][]const u8{}, // TODO: parse attribute arguments
            });
        }
    }
    return attrs.toOwnedSlice(allocator) catch &[_]dast.Attribute{};
}

fn parseModuleItem(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.ModuleItem {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    // Check item type
    const item_type = obj.get("_type") orelse obj.get("type") orelse return error.MissingType;
    if (item_type != .string) return error.ExpectedString;

    const type_str = item_type.string;

    if (std.mem.eql(u8, type_str, "Module")) {
        const nested = try parseModule(allocator, json);
        const ptr = try allocator.create(dast.Module);
        ptr.* = nested;
        return .{ .module = ptr };
    }

    if (std.mem.eql(u8, type_str, "Class")) {
        const class = try parseClass(allocator, json);
        const ptr = try allocator.create(dast.Class);
        ptr.* = class;
        return .{ .class = ptr };
    }

    if (std.mem.eql(u8, type_str, "Trait")) {
        const trait = try parseTrait(allocator, json);
        const ptr = try allocator.create(dast.Trait);
        ptr.* = trait;
        return .{ .trait = ptr };
    }

    if (std.mem.eql(u8, type_str, "Datatype")) {
        const dt = try parseDatatype(allocator, json);
        const ptr = try allocator.create(dast.Datatype);
        ptr.* = dt;
        return .{ .datatype = ptr };
    }

    if (std.mem.eql(u8, type_str, "Newtype")) {
        const nt = try parseNewtype(allocator, json);
        const ptr = try allocator.create(dast.Newtype);
        ptr.* = nt;
        return .{ .newtype = ptr };
    }

    if (std.mem.eql(u8, type_str, "TypeSynonym") or std.mem.eql(u8, type_str, "SynonymType")) {
        const syn = try parseSynonymType(allocator, json);
        const ptr = try allocator.create(dast.SynonymType);
        ptr.* = syn;
        return .{ .synonym_type = ptr };
    }

    return error.UnknownItemType;
}

fn parseClass(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.Class {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const name = try parseName(obj.get("name") orelse return error.MissingField);
    const attrs = if (obj.get("attributes")) |a| try parseAttributes(allocator, a) else &[_]dast.Attribute{};

    // Parse type parameters
    const type_params = if (obj.get("typeParams")) |tp| try parseTypeParams(allocator, tp) else &[_]dast.TypeArgDecl{};

    // Parse superclass traits
    const super_traits = if (obj.get("superclassTraits")) |st| try parseTypes(allocator, st) else &[_]dast.Type{};

    // Parse fields
    const fields = if (obj.get("fields")) |f| try parseFields(allocator, f) else &[_]dast.Field{};

    // Parse body (methods)
    var body_items = std.ArrayListUnmanaged(dast.ClassItem){};
    if (obj.get("body")) |body_json| {
        if (body_json == .array) {
            for (body_json.array.items) |item| {
                if (parseClassItem(allocator, item)) |ci| {
                    try body_items.append(allocator, ci);
                } else |_| {}
            }
        }
    }

    return .{
        .name = name,
        .enclosing_module = .{ .id = "" },
        .type_params = type_params,
        .super_classes = super_traits,
        .fields = fields,
        .body = body_items.toOwnedSlice(allocator) catch &[_]dast.ClassItem{},
        .attributes = attrs,
    };
}

fn parseTrait(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.Trait {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const name = try parseName(obj.get("name") orelse return error.MissingField);
    const attrs = if (obj.get("attributes")) |a| try parseAttributes(allocator, a) else &[_]dast.Attribute{};
    const type_params = if (obj.get("typeParams")) |tp| try parseTypeParams(allocator, tp) else &[_]dast.TypeArgDecl{};

    var body_items = std.ArrayListUnmanaged(dast.ClassItem){};
    if (obj.get("body")) |body_json| {
        if (body_json == .array) {
            for (body_json.array.items) |item| {
                if (parseClassItem(allocator, item)) |ci| {
                    try body_items.append(allocator, ci);
                } else |_| {}
            }
        }
    }

    return .{
        .name = name,
        .type_params = type_params,
        .trait_type = .general_trait,
        .parents = &[_]dast.Type{}, // TODO
        .body = body_items.toOwnedSlice(allocator) catch &[_]dast.ClassItem{},
        .attributes = attrs,
    };
}

fn parseDatatype(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.Datatype {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const name = try parseName(obj.get("name") orelse return error.MissingField);
    const attrs = if (obj.get("attributes")) |a| try parseAttributes(allocator, a) else &[_]dast.Attribute{};
    const type_params = if (obj.get("typeParams")) |tp| try parseTypeParams(allocator, tp) else &[_]dast.TypeArgDecl{};

    // Parse constructors
    var ctors = std.ArrayListUnmanaged(dast.DatatypeCtor){};
    if (obj.get("ctors")) |ctors_json| {
        if (ctors_json == .array) {
            for (ctors_json.array.items) |ctor_json| {
                if (parseDatatypeCtor(allocator, ctor_json)) |ctor| {
                    try ctors.append(allocator, ctor);
                } else |_| {}
            }
        }
    }

    return .{
        .name = name,
        .enclosing_module = .{ .id = "" },
        .type_params = type_params,
        .ctors = ctors.toOwnedSlice(allocator) catch &[_]dast.DatatypeCtor{},
        .body = &[_]dast.ClassItem{},
        .is_co_datatype = false,
        .equality_support = .never,
        .attributes = attrs,
    };
}

fn parseDatatypeCtor(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.DatatypeCtor {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const name = try parseName(obj.get("name") orelse return error.MissingField);

    // Parse destructor fields
    var args = std.ArrayListUnmanaged(dast.DatatypeDtor){};
    if (obj.get("args")) |args_json| {
        if (args_json == .array) {
            for (args_json.array.items) |arg_json| {
                if (parseDatatypeDtor(allocator, arg_json)) |dtor| {
                    try args.append(allocator, dtor);
                } else |_| {}
            }
        }
    }

    const args_slice = args.toOwnedSlice(allocator) catch &[_]dast.DatatypeDtor{};
    return .{
        .name = name,
        .args = args_slice,
        .has_any_args = args_slice.len > 0,
    };
}

// ... (skip parseDatatypeDtor, parseNewtype, parseSynonymType, parseClassItem, parseMethod as they are small or handled above) ...

// But wait, I need to check parseMethod because it has `params` list etc.
// Since `replace` requires EXACT context, I should break this down or be very careful.
// The file is small enough that I can just replace the blocks that use ArrayList.

// Let's restart the replace block strategy to be safe. I'll replace the block from `parseAttributes` down to `parseTypes` in chunks.

// Chunk 1: parseAttributes
// Chunk 2: parseClass (body items)
// Chunk 3: parseTrait (body items)
// Chunk 4: parseDatatype (ctors)
// Chunk 5: parseDatatypeCtor (args)
// Chunk 6: parseTypeParams
// Chunk 7: parseIdents
// Chunk 8: parseTypes
// Chunk 9: parseFields
// Chunk 10: parseFormals
// Chunk 11: parseVarNames
// Chunk 12: parseStatements
// Chunk 13: parseExpression (Call args)

// This is safer. I'll do them in parallel if possible, or sequential. I'll do the first batch.

fn parseDatatypeDtor(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.DatatypeDtor {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const callable: ?dast.Name = if (obj.get("callableName")) |cn| blk: {
        if (cn == .string) break :blk .{ .dafny_name = cn.string, .compile_name = null };
        break :blk null;
    } else null;

    return .{
        .formal = try parseFormal(allocator, json),
        .callable_name = callable,
    };
}

fn parseNewtype(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.Newtype {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const name = try parseName(obj.get("name") orelse return error.MissingField);
    const attrs = if (obj.get("attributes")) |a| try parseAttributes(allocator, a) else &[_]dast.Attribute{};
    const type_params = if (obj.get("typeParams")) |tp| try parseTypeParams(allocator, tp) else &[_]dast.TypeArgDecl{};

    const base_type = if (obj.get("base")) |b| try parseType(allocator, b) else dast.Type{ .primitive = .int };

    return .{
        .name = name,
        .type_params = type_params,
        .base = base_type,
        .range = .no_range,
        .constraint = null,
        .witness = null,
        .attributes = attrs,
    };
}

fn parseSynonymType(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.SynonymType {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const name = try parseName(obj.get("name") orelse return error.MissingField);
    const attrs = if (obj.get("attributes")) |a| try parseAttributes(allocator, a) else &[_]dast.Attribute{};
    const type_params = if (obj.get("typeParams")) |tp| try parseTypeParams(allocator, tp) else &[_]dast.TypeArgDecl{};

    const base_type = if (obj.get("base")) |b| try parseType(allocator, b) else dast.Type{ .primitive = .int };

    return .{
        .name = name,
        .type_params = type_params,
        .base = base_type,
        .witness = null,
        .attributes = attrs,
    };
}

fn parseClassItem(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.ClassItem {
    if (json != .object) return error.ExpectedObject;

    const method = try parseMethod(allocator, json);
    const ptr = try allocator.create(dast.Method);
    ptr.* = method;
    return .{ .method = ptr };
}

fn parseMethod(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.Method {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const name = try parseName(obj.get("name") orelse return error.MissingField);
    const attrs = if (obj.get("attributes")) |a| try parseAttributes(allocator, a) else &[_]dast.Attribute{};
    const type_params = if (obj.get("typeParams")) |tp| try parseTypeParams(allocator, tp) else &[_]dast.TypeArgDecl{};

    // Parse parameters
    const params = if (obj.get("params")) |p| try parseFormals(allocator, p) else &[_]dast.Formal{};

    // Parse return types
    const out_types = if (obj.get("outTypes")) |ot| try parseTypes(allocator, ot) else &[_]dast.Type{};
    const out_vars: ?[]const dast.Ident = if (obj.get("outVars")) |ov| try parseIdents(allocator, ov) else null;

    // Parse body
    const body = if (obj.get("body")) |b| try parseStatements(allocator, b) else &[_]dast.Statement{};
    const has_body = obj.get("body") != null;

    return .{
        .doc_string = "",
        .is_static = if (obj.get("isStatic")) |s| (s == .bool and s.bool) else false,
        .has_body = has_body,
        .overriding_path = null,
        .name = name,
        .type_params = type_params,
        .params = params,
        .body = body,
        .out_types = out_types,
        .out_vars = out_vars,
        .attributes = attrs,
    };
}

fn parseTypeParams(allocator: std.mem.Allocator, json: std.json.Value) ParseError![]const dast.TypeArgDecl {
    if (json != .array) return &[_]dast.TypeArgDecl{};

    var params = std.ArrayListUnmanaged(dast.TypeArgDecl){};
    for (json.array.items) |item| {
        if (item == .object) {
            const obj = item.object;
            const name = if (obj.get("name")) |n| (if (n == .string) n.string else "") else "";
            try params.append(allocator, .{
                .name = .{ .id = name },
                .bounds = &[_]dast.TypeArgBound{},
                .variance = .nonvariant,
            });
        }
    }
    return params.toOwnedSlice(allocator) catch &[_]dast.TypeArgDecl{};
}

fn parseIdents(allocator: std.mem.Allocator, json: std.json.Value) ParseError![]const dast.Ident {
    if (json != .array) return &[_]dast.Ident{};

    var idents = std.ArrayListUnmanaged(dast.Ident){};
    for (json.array.items) |item| {
        if (item == .string) {
            try idents.append(allocator, .{ .id = item.string });
        } else if (item == .object) {
            const obj = item.object;
            const id = if (obj.get("id")) |i| (if (i == .string) i.string else "") else "";
            try idents.append(allocator, .{ .id = id });
        }
    }
    return idents.toOwnedSlice(allocator) catch &[_]dast.Ident{};
}

fn parseTypes(allocator: std.mem.Allocator, json: std.json.Value) ParseError![]const dast.Type {
    if (json != .array) return &[_]dast.Type{};

    var types = std.ArrayListUnmanaged(dast.Type){};
    for (json.array.items) |item| {
        try types.append(allocator, try parseType(allocator, item));
    }
    return types.toOwnedSlice(allocator) catch &[_]dast.Type{};
}

fn parseType(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.Type {
    _ = allocator;

    if (json == .string) {
        const s = json.string;
        // Handle primitive types
        if (std.mem.eql(u8, s, "int")) return .{ .primitive = .int };
        if (std.mem.eql(u8, s, "real")) return .{ .primitive = .real };
        if (std.mem.eql(u8, s, "bool")) return .{ .primitive = .bool };
        if (std.mem.eql(u8, s, "char")) return .{ .primitive = .char };
        if (std.mem.eql(u8, s, "string")) return .{ .primitive = .string };

        // Otherwise it's a type argument
        return .{ .type_arg = .{ .id = s } };
    }

    if (json == .object) {
        const obj = json.object;
        const type_kind = obj.get("_type") orelse obj.get("kind");

        if (type_kind) |kind| {
            if (kind == .string) {
                const kind_str = kind.string;
                if (std.mem.eql(u8, kind_str, "Primitive")) {
                    if (obj.get("value")) |v| {
                        if (v == .string) {
                            const prim = v.string;
                            if (std.mem.eql(u8, prim, "Int")) return .{ .primitive = .int };
                            if (std.mem.eql(u8, prim, "Real")) return .{ .primitive = .real };
                            if (std.mem.eql(u8, prim, "Bool")) return .{ .primitive = .bool };
                            if (std.mem.eql(u8, prim, "Char")) return .{ .primitive = .char };
                            if (std.mem.eql(u8, prim, "String")) return .{ .primitive = .string };
                        }
                    }
                }
                // TODO: handle seq, set, map, array, etc.
            }
        }
    }

    // Default to object type
    return .object;
}

fn parseFields(allocator: std.mem.Allocator, json: std.json.Value) ParseError![]const dast.Field {
    if (json != .array) return &[_]dast.Field{};

    var fields = std.ArrayListUnmanaged(dast.Field){};
    for (json.array.items) |item| {
        if (item == .object) {
            const formal = try parseFormal(allocator, item);
            try fields.append(allocator, .{ .formal = formal, .default_value = null });
        }
    }
    return fields.toOwnedSlice(allocator) catch &[_]dast.Field{};
}

fn parseFormals(allocator: std.mem.Allocator, json: std.json.Value) ParseError![]const dast.Formal {
    if (json != .array) return &[_]dast.Formal{};

    var formals = std.ArrayListUnmanaged(dast.Formal){};
    for (json.array.items) |item| {
        try formals.append(allocator, try parseFormal(allocator, item));
    }
    return formals.toOwnedSlice(allocator) catch &[_]dast.Formal{};
}

fn parseFormal(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.Formal {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const name_json = obj.get("name") orelse return error.MissingField;
    const name: dast.VarName = if (name_json == .string) .{
        .dafny_name = name_json.string,
        .compile_name = null,
    } else blk: {
        if (name_json == .object) {
            const nobj = name_json.object;
            break :blk .{
                .dafny_name = if (nobj.get("dafnyName")) |n| (if (n == .string) n.string else "") else "",
                .compile_name = if (nobj.get("compileName")) |n| (if (n == .string) n.string else null) else null,
            };
        }
        break :blk .{ .dafny_name = "", .compile_name = null };
    };

    const typ = if (obj.get("type")) |t| try parseType(allocator, t) else dast.Type{ .primitive = .int };

    return .{
        .name = name,
        .typ = typ,
        .attributes = &[_]dast.Attribute{},
    };
}

fn parseVarNames(allocator: std.mem.Allocator, json: std.json.Value) ParseError![]const dast.VarName {
    if (json != .array) return &[_]dast.VarName{};

    var names = std.ArrayListUnmanaged(dast.VarName){};
    for (json.array.items) |item| {
        if (item == .string) {
            try names.append(allocator, .{ .dafny_name = item.string, .compile_name = null });
        } else if (item == .object) {
            const obj = item.object;
            try names.append(allocator, .{
                .dafny_name = if (obj.get("dafnyName")) |n| (if (n == .string) n.string else "") else "",
                .compile_name = if (obj.get("compileName")) |n| (if (n == .string) n.string else null) else null,
            });
        }
    }
    return names.toOwnedSlice(allocator) catch &[_]dast.VarName{};
}

fn parseStatements(allocator: std.mem.Allocator, json: std.json.Value) ParseError![]const dast.Statement {
    if (json != .array) return &[_]dast.Statement{};

    var stmts = std.ArrayListUnmanaged(dast.Statement){};
    for (json.array.items) |item| {
        if (parseStatement(allocator, item)) |stmt| {
            try stmts.append(allocator, stmt);
        } else |_| {}
    }
    return stmts.toOwnedSlice(allocator) catch &[_]dast.Statement{};
}

fn parseStatement(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.Statement {
    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const stmt_type = obj.get("_type") orelse obj.get("type") orelse return error.MissingType;
    if (stmt_type != .string) return error.ExpectedString;

    const type_str = stmt_type.string;

    if (std.mem.eql(u8, type_str, "DeclareVar")) {
        const name_json = obj.get("name") orelse return error.MissingField;
        const value_ptr: ?*const dast.Expression = if (obj.get("value") orelse obj.get("init")) |v| blk: {
            const ptr = try allocator.create(dast.Expression);
            ptr.* = try parseExpression(allocator, v);
            break :blk ptr;
        } else null;

        return .{
            .decl_stmt = .{
                .name = if (name_json == .string) .{ .dafny_name = name_json.string, .compile_name = null } else .{ .dafny_name = "", .compile_name = null },
                .typ = if (obj.get("type")) |t| try parseType(allocator, t) else dast.Type{ .primitive = .int },
                .value = value_ptr,
            },
        };
    }

    if (std.mem.eql(u8, type_str, "Return")) {
        const ret_ptr = try allocator.create(dast.Expression);
        ret_ptr.* = if (obj.get("value")) |v| try parseExpression(allocator, v) else .{ .literal = .null_lit };
        return .{ .return_stmt = ret_ptr };
    }

    if (std.mem.eql(u8, type_str, "Print")) {
        const print_ptr = try allocator.create(dast.Expression);
        if (obj.get("args")) |args| {
            if (args == .array and args.array.items.len > 0) {
                print_ptr.* = try parseExpression(allocator, args.array.items[0]);
            } else {
                print_ptr.* = .{ .literal = .{ .string_lit = "" } };
            }
        } else {
            print_ptr.* = .{ .literal = .{ .string_lit = "" } };
        }
        return .{ .print = print_ptr };
    }

    // Default to halt for unrecognized statements
    return .halt;
}

fn parseExpression(allocator: std.mem.Allocator, json: std.json.Value) ParseError!dast.Expression {
    if (json == .string) {
        return .{ .ident = .{ .dafny_name = json.string, .compile_name = null } };
    }

    if (json == .integer) {
        // Convert integer to string representation
        var buf: [32]u8 = undefined;
        const int_str = std.fmt.bufPrint(&buf, "{}", .{json.integer}) catch "0";
        const str_copy = allocator.dupe(u8, int_str) catch "0";
        return .{ .literal = .{ .int_lit = str_copy } };
    }

    if (json == .bool) {
        return .{ .literal = .{ .bool_lit = json.bool } };
    }

    if (json != .object) return error.ExpectedObject;
    const obj = json.object;

    const expr_type = obj.get("_type") orelse obj.get("type");
    if (expr_type == null) {
        // Try to infer from content
        if (obj.get("value")) |v| {
            if (v == .integer) {
                var buf: [32]u8 = undefined;
                const int_str = std.fmt.bufPrint(&buf, "{}", .{v.integer}) catch "0";
                const str_copy = allocator.dupe(u8, int_str) catch "0";
                return .{ .literal = .{ .int_lit = str_copy } };
            }
            if (v == .bool) return .{ .literal = .{ .bool_lit = v.bool } };
            if (v == .string) return .{ .literal = .{ .string_lit = v.string } };
        }
        return .{ .literal = .null_lit };
    }

    if (expr_type.? != .string) return error.ExpectedString;
    const type_str = expr_type.?.string;

    if (std.mem.eql(u8, type_str, "Literal")) {
        if (obj.get("value")) |v| {
            if (v == .integer) {
                var buf: [32]u8 = undefined;
                const int_str = std.fmt.bufPrint(&buf, "{}", .{v.integer}) catch "0";
                const str_copy = allocator.dupe(u8, int_str) catch "0";
                return .{ .literal = .{ .int_lit = str_copy } };
            }
            if (v == .bool) return .{ .literal = .{ .bool_lit = v.bool } };
            if (v == .string) return .{ .literal = .{ .string_lit = v.string } };
        }
        return .{ .literal = .null_lit };
    }

    if (std.mem.eql(u8, type_str, "Ident")) {
        if (obj.get("name")) |n| {
            if (n == .string) return .{ .ident = .{ .dafny_name = n.string, .compile_name = null } };
        }
        return .{ .ident = .{ .dafny_name = "", .compile_name = null } };
    }

    if (std.mem.eql(u8, type_str, "BinaryOp") or std.mem.eql(u8, type_str, "BinOp")) {
        const left_ptr = try allocator.create(dast.Expression);
        left_ptr.* = if (obj.get("left")) |l| try parseExpression(allocator, l) else .{ .literal = .null_lit };
        const right_ptr = try allocator.create(dast.Expression);
        right_ptr.* = if (obj.get("right")) |r| try parseExpression(allocator, r) else .{ .literal = .null_lit };

        const op: dast.BinOp = if (obj.get("op")) |op_json| blk: {
            if (op_json == .string) {
                const op_str = op_json.string;
                if (std.mem.eql(u8, op_str, "+") or std.mem.eql(u8, op_str, "Add")) break :blk .add;
                if (std.mem.eql(u8, op_str, "-") or std.mem.eql(u8, op_str, "Sub")) break :blk .sub;
                if (std.mem.eql(u8, op_str, "*") or std.mem.eql(u8, op_str, "Mul")) break :blk .mul;
                if (std.mem.eql(u8, op_str, "/") or std.mem.eql(u8, op_str, "Div")) break :blk .div;
                if (std.mem.eql(u8, op_str, "%") or std.mem.eql(u8, op_str, "Mod")) break :blk .mod;
                if (std.mem.eql(u8, op_str, "==") or std.mem.eql(u8, op_str, "Eq")) break :blk .eq;
                if (std.mem.eql(u8, op_str, "!=") or std.mem.eql(u8, op_str, "Neq")) break :blk .neq;
                if (std.mem.eql(u8, op_str, "<") or std.mem.eql(u8, op_str, "Lt")) break :blk .lt;
                if (std.mem.eql(u8, op_str, "<=") or std.mem.eql(u8, op_str, "Le")) break :blk .le;
                if (std.mem.eql(u8, op_str, ">") or std.mem.eql(u8, op_str, "Gt")) break :blk .gt;
                if (std.mem.eql(u8, op_str, ">=") or std.mem.eql(u8, op_str, "Ge")) break :blk .ge;
                if (std.mem.eql(u8, op_str, "&&") or std.mem.eql(u8, op_str, "And")) break :blk .and_op;
                if (std.mem.eql(u8, op_str, "||") or std.mem.eql(u8, op_str, "Or")) break :blk .or_op;
            }
            break :blk .add;
        } else .add;

        return .{
            .bin_op = .{
                .op = op,
                .left = left_ptr,
                .right = right_ptr,
            },
        };
    }

    if (std.mem.eql(u8, type_str, "Call")) {
        var args = std.ArrayListUnmanaged(dast.Expression){};
        if (obj.get("args")) |args_json| {
            if (args_json == .array) {
                for (args_json.array.items) |arg| {
                    try args.append(allocator, try parseExpression(allocator, arg));
                }
            }
        }

        const on_ptr = try allocator.create(dast.Expression);
        on_ptr.* = if (obj.get("on")) |on| try parseExpression(allocator, on) else .{ .literal = .null_lit };

        const call_name: dast.CallName = if (obj.get("name")) |n| blk: {
            if (n == .string) break :blk .{ .call_name = .{ .dafny_name = n.string, .compile_name = null } };
            break :blk .{ .call_name = .{ .dafny_name = "", .compile_name = null } };
        } else .{ .call_name = .{ .dafny_name = "", .compile_name = null } };

        return .{
            .call = .{
                .on = on_ptr,
                .call_name = call_name,
                .type_args = &[_]dast.Type{},
                .args = args.toOwnedSlice(allocator) catch &[_]dast.Expression{},
            },
        };
    }

    // Default
    return .{ .literal = .null_lit };
}

test "main compiles" {
    // Just ensure main.zig compiles correctly
    _ = main;
}
