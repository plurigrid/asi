//! ZAST - Zig Abstract Syntax Tree
//!
//! This module represents Zig code as an AST that can be pretty-printed
//! to generate valid Zig source code from compiled Dafny.
//!
//! Design goals:
//! - Generate idiomatic Zig code
//! - Support all Zig constructs needed for Dafny compilation
//! - Easy pretty-printing with configurable formatting

const std = @import("std");
const Allocator = std.mem.Allocator;

// ============================================================================
// IDENTIFIERS AND PATHS
// ============================================================================

/// A Zig identifier
pub const Ident = struct {
    name: []const u8,

    pub fn init(name: []const u8) Ident {
        return .{ .name = name };
    }

    /// Write identifier to writer
    pub fn write(self: Ident, writer: anytype) !void {
        try writer.writeAll(self.name);
    }
};

/// A path (e.g., std.mem.Allocator)
pub const Path = struct {
    segments: []const Ident,

    pub fn init(segments: []const Ident) Path {
        return .{ .segments = segments };
    }

    pub fn single(name: []const u8) Path {
        return .{ .segments = &[_]Ident{Ident.init(name)} };
    }

    pub fn write(self: Path, writer: anytype) !void {
        for (self.segments, 0..) |seg, i| {
            if (i > 0) try writer.writeAll(".");
            try seg.write(writer);
        }
    }
};

// ============================================================================
// TYPES
// ============================================================================

/// Zig types
pub const Type = union(enum) {
    /// Named type (e.g., u32, MyStruct)
    ident: Ident,
    /// Path type (e.g., std.mem.Allocator)
    path: Path,
    /// Pointer type (*T, *const T)
    ptr: struct {
        is_const: bool,
        child: *const Type,
    },
    /// Slice type ([]T, []const T)
    slice: struct {
        is_const: bool,
        child: *const Type,
    },
    /// Array type ([N]T)
    array: struct {
        len: usize,
        child: *const Type,
    },
    /// Optional type (?T)
    optional: *const Type,
    /// Error union type (E!T)
    error_union: struct {
        error_type: ?*const Type,
        payload: *const Type,
    },
    /// Function type (fn(args) ret)
    function: struct {
        params: []const FnParam,
        ret: *const Type,
    },
    /// anytype (comptime inferred)
    any: void,
    /// void
    void: void,
    /// bool
    bool: void,
    /// Comptime type
    comptime_type: *const Type,
    /// Integer types
    i8: void,
    i16: void,
    i32: void,
    i64: void,
    i128: void,
    u8: void,
    u16: void,
    u32: void,
    u64: void,
    u128: void,
    usize: void,
    isize: void,
    /// Float types
    f16: void,
    f32: void,
    f64: void,
    f128: void,
    /// @Type expression
    type_expr: *const Expr,

    pub fn write(self: Type, writer: anytype) !void {
        switch (self) {
            .ident => |id| try id.write(writer),
            .path => |p| try p.write(writer),
            .ptr => |p| {
                try writer.writeAll(if (p.is_const) "*const " else "*");
                try p.child.write(writer);
            },
            .slice => |s| {
                try writer.writeAll(if (s.is_const) "[]const " else "[]");
                try s.child.write(writer);
            },
            .array => |a| {
                try writer.print("[{d}]", .{a.len});
                try a.child.write(writer);
            },
            .optional => |o| {
                try writer.writeAll("?");
                try o.write(writer);
            },
            .error_union => |e| {
                if (e.error_type) |et| {
                    try et.write(writer);
                }
                try writer.writeAll("!");
                try e.payload.write(writer);
            },
            .function => |f| {
                try writer.writeAll("fn(");
                for (f.params, 0..) |param, i| {
                    if (i > 0) try writer.writeAll(", ");
                    try param.write(writer);
                }
                try writer.writeAll(") ");
                try f.ret.write(writer);
            },
            .any => try writer.writeAll("anytype"),
            .void => try writer.writeAll("void"),
            .bool => try writer.writeAll("bool"),
            .comptime_type => |ct| {
                try writer.writeAll("comptime ");
                try ct.write(writer);
            },
            .i8 => try writer.writeAll("i8"),
            .i16 => try writer.writeAll("i16"),
            .i32 => try writer.writeAll("i32"),
            .i64 => try writer.writeAll("i64"),
            .i128 => try writer.writeAll("i128"),
            .u8 => try writer.writeAll("u8"),
            .u16 => try writer.writeAll("u16"),
            .u32 => try writer.writeAll("u32"),
            .u64 => try writer.writeAll("u64"),
            .u128 => try writer.writeAll("u128"),
            .usize => try writer.writeAll("usize"),
            .isize => try writer.writeAll("isize"),
            .f16 => try writer.writeAll("f16"),
            .f32 => try writer.writeAll("f32"),
            .f64 => try writer.writeAll("f64"),
            .f128 => try writer.writeAll("f128"),
            .type_expr => |e| try e.write(writer),
        }
    }
};

/// Function parameter
pub const FnParam = struct {
    name: ?Ident,
    typ: Type,

    pub fn write(self: FnParam, writer: anytype) anyerror!void {
        if (self.name) |n| {
            try n.write(writer);
            try writer.writeAll(": ");
        }
        try self.typ.write(writer);
    }
};

// ============================================================================
// EXPRESSIONS
// ============================================================================

/// Binary operators
pub const BinOp = enum {
    // Arithmetic
    add,
    sub,
    mul,
    div,
    mod,
    // Comparison
    eq,
    neq,
    lt,
    le,
    gt,
    ge,
    // Logical
    bool_and,
    bool_or,
    // Bitwise
    bit_and,
    bit_or,
    bit_xor,
    shl,
    shr,
    // Array/pointer
    array_cat,

    pub fn toString(self: BinOp) []const u8 {
        return switch (self) {
            .add => "+",
            .sub => "-",
            .mul => "*",
            .div => "/",
            .mod => "%",
            .eq => "==",
            .neq => "!=",
            .lt => "<",
            .le => "<=",
            .gt => ">",
            .ge => ">=",
            .bool_and => "and",
            .bool_or => "or",
            .bit_and => "&",
            .bit_or => "|",
            .bit_xor => "^",
            .shl => "<<",
            .shr => ">>",
            .array_cat => "++",
        };
    }
};

/// Unary operators
pub const UnaryOp = enum {
    negate,
    bool_not,
    bit_not,
    ptr_deref,
    addr_of,

    pub fn toString(self: UnaryOp) []const u8 {
        return switch (self) {
            .negate => "-",
            .bool_not => "!",
            .bit_not => "~",
            .ptr_deref => ".*",
            .addr_of => "&",
        };
    }
};

/// Zig expressions
pub const Expr = union(enum) {
    /// Literal values
    int_lit: i128,
    uint_lit: u128,
    float_lit: f64,
    string_lit: []const u8,
    char_lit: u8,
    bool_lit: bool,
    null_lit: void,
    undefined_lit: void,

    /// Identifier
    ident: Ident,

    /// Path (e.g., std.mem.eql)
    path: Path,

    /// Field access (expr.field)
    field: struct {
        expr: *const Expr,
        field: Ident,
    },

    /// Index access (expr[index])
    index: struct {
        expr: *const Expr,
        index: *const Expr,
    },

    /// Slice (expr[lo..hi])
    slice: struct {
        expr: *const Expr,
        lo: ?*const Expr,
        hi: ?*const Expr,
    },

    /// Binary operation
    bin_op: struct {
        op: BinOp,
        left: *const Expr,
        right: *const Expr,
    },

    /// Unary operation
    un_op: struct {
        op: UnaryOp,
        expr: *const Expr,
    },

    /// Function call
    call: struct {
        func: *const Expr,
        args: []const Expr,
    },

    /// Struct initialization
    struct_init: struct {
        typ: ?*const Type,
        fields: []const FieldInit,
    },

    /// Array initialization
    array_init: struct {
        typ: ?*const Type,
        elements: []const Expr,
    },

    /// If expression
    if_expr: struct {
        cond: *const Expr,
        then_expr: *const Expr,
        else_expr: ?*const Expr,
    },

    /// Block expression
    block: struct {
        label: ?Ident,
        stmts: []const Stmt,
        result: ?*const Expr,
    },

    /// Try expression (try expr)
    try_expr: *const Expr,

    /// Catch expression (expr catch |err| handler)
    catch_expr: struct {
        expr: *const Expr,
        err_name: ?Ident,
        handler: *const Expr,
    },

    /// Orelse expression (expr orelse default)
    orelse_expr: struct {
        expr: *const Expr,
        default: *const Expr,
    },

    /// Optional unwrap (expr.?)
    unwrap: *const Expr,

    /// Type coercion (@as(T, expr))
    as_expr: struct {
        typ: *const Type,
        expr: *const Expr,
    },

    /// @intCast, @floatCast, etc.
    builtin_call: struct {
        name: []const u8,
        args: []const Expr,
    },

    /// Anonymous struct literal .{ ... }
    anon_struct: []const FieldInit,

    /// Anonymous array literal .{ ... }
    anon_array: []const Expr,

    /// Grouped expression (expr)
    grouped: *const Expr,

    pub fn write(self: Expr, writer: anytype) anyerror!void {
        switch (self) {
            .int_lit => |i| try writer.print("{d}", .{i}),
            .uint_lit => |u| try writer.print("{d}", .{u}),
            .float_lit => |f| try writer.print("{d}", .{f}),
            .string_lit => |s| {
                try writer.writeAll("\"");
                try writer.writeAll(s); // TODO: escape
                try writer.writeAll("\"");
            },
            .char_lit => |c| try writer.print("'{c}'", .{c}),
            .bool_lit => |b| try writer.writeAll(if (b) "true" else "false"),
            .null_lit => try writer.writeAll("null"),
            .undefined_lit => try writer.writeAll("undefined"),
            .ident => |id| try id.write(writer),
            .path => |p| try p.write(writer),
            .field => |f| {
                try f.expr.write(writer);
                try writer.writeAll(".");
                try f.field.write(writer);
            },
            .index => |idx| {
                try idx.expr.write(writer);
                try writer.writeAll("[");
                try idx.index.write(writer);
                try writer.writeAll("]");
            },
            .slice => |s| {
                try s.expr.write(writer);
                try writer.writeAll("[");
                if (s.lo) |lo| try lo.write(writer);
                try writer.writeAll("..");
                if (s.hi) |hi| try hi.write(writer);
                try writer.writeAll("]");
            },
            .bin_op => |b| {
                try b.left.write(writer);
                try writer.print(" {s} ", .{b.op.toString()});
                try b.right.write(writer);
            },
            .un_op => |u| {
                if (u.op == .ptr_deref) {
                    try u.expr.write(writer);
                    try writer.writeAll(".*");
                } else {
                    try writer.writeAll(u.op.toString());
                    try u.expr.write(writer);
                }
            },
            .call => |c| {
                try c.func.write(writer);
                try writer.writeAll("(");
                for (c.args, 0..) |arg, i| {
                    if (i > 0) try writer.writeAll(", ");
                    try arg.write(writer);
                }
                try writer.writeAll(")");
            },
            .struct_init => |s| {
                if (s.typ) |t| try t.write(writer);
                try writer.writeAll(".{");
                for (s.fields, 0..) |f, i| {
                    if (i > 0) try writer.writeAll(", ");
                    try f.write(writer);
                }
                try writer.writeAll("}");
            },
            .array_init => |a| {
                if (a.typ) |t| try t.write(writer);
                try writer.writeAll(".{");
                for (a.elements, 0..) |elem, i| {
                    if (i > 0) try writer.writeAll(", ");
                    try elem.write(writer);
                }
                try writer.writeAll("}");
            },
            .if_expr => |ie| {
                try writer.writeAll("if (");
                try ie.cond.write(writer);
                try writer.writeAll(") ");
                try ie.then_expr.write(writer);
                if (ie.else_expr) |ee| {
                    try writer.writeAll(" else ");
                    try ee.write(writer);
                }
            },
            .block => |b| {
                if (b.label) |l| {
                    try l.write(writer);
                    try writer.writeAll(": ");
                }
                try writer.writeAll("{\n");
                for (b.stmts) |stmt| {
                    try stmt.write(writer);
                }
                if (b.result) |r| {
                    try r.write(writer);
                    try writer.writeAll("\n");
                }
                try writer.writeAll("}");
            },
            .try_expr => |te| {
                try writer.writeAll("try ");
                try te.write(writer);
            },
            .catch_expr => |ce| {
                try ce.expr.write(writer);
                try writer.writeAll(" catch ");
                if (ce.err_name) |en| {
                    try writer.writeAll("|");
                    try en.write(writer);
                    try writer.writeAll("| ");
                }
                try ce.handler.write(writer);
            },
            .orelse_expr => |oe| {
                try oe.expr.write(writer);
                try writer.writeAll(" orelse ");
                try oe.default.write(writer);
            },
            .unwrap => |uw| {
                try uw.write(writer);
                try writer.writeAll(".?");
            },
            .as_expr => |ae| {
                try writer.writeAll("@as(");
                try ae.typ.write(writer);
                try writer.writeAll(", ");
                try ae.expr.write(writer);
                try writer.writeAll(")");
            },
            .builtin_call => |bc| {
                try writer.print("@{s}(", .{bc.name});
                for (bc.args, 0..) |arg, i| {
                    if (i > 0) try writer.writeAll(", ");
                    try arg.write(writer);
                }
                try writer.writeAll(")");
            },
            .anon_struct => |fields| {
                try writer.writeAll(".{");
                for (fields, 0..) |f, i| {
                    if (i > 0) try writer.writeAll(", ");
                    try f.write(writer);
                }
                try writer.writeAll("}");
            },
            .anon_array => |elems| {
                try writer.writeAll(".{");
                for (elems, 0..) |elem, i| {
                    if (i > 0) try writer.writeAll(", ");
                    try elem.write(writer);
                }
                try writer.writeAll("}");
            },
            .grouped => |g| {
                try writer.writeAll("(");
                try g.write(writer);
                try writer.writeAll(")");
            },
        }
    }
};

/// Field initializer
pub const FieldInit = struct {
    name: Ident,
    value: Expr,

    pub fn write(self: FieldInit, writer: anytype) !void {
        try writer.writeAll(".");
        try self.name.write(writer);
        try writer.writeAll(" = ");
        try self.value.write(writer);
    }
};

// ============================================================================
// STATEMENTS
// ============================================================================

/// Zig statements
pub const Stmt = union(enum) {
    /// Variable declaration (const/var)
    var_decl: struct {
        is_const: bool,
        name: Ident,
        typ: ?*const Type,
        value: ?*const Expr,
    },

    /// Assignment
    assign: struct {
        lhs: *const Expr,
        rhs: *const Expr,
    },

    /// Compound assignment (+=, -=, etc.)
    compound_assign: struct {
        op: BinOp,
        lhs: *const Expr,
        rhs: *const Expr,
    },

    /// Expression statement
    expr_stmt: *const Expr,

    /// If statement
    if_stmt: struct {
        cond: *const Expr,
        then_block: []const Stmt,
        else_block: ?[]const Stmt,
    },

    /// While loop
    while_stmt: struct {
        cond: *const Expr,
        body: []const Stmt,
        else_block: ?[]const Stmt,
    },

    /// For loop
    for_stmt: struct {
        iterable: *const Expr,
        captures: []const Ident,
        body: []const Stmt,
        else_block: ?[]const Stmt,
    },

    /// Switch statement
    switch_stmt: struct {
        expr: *const Expr,
        cases: []const SwitchCase,
    },

    /// Return statement
    return_stmt: ?*const Expr,

    /// Break statement
    break_stmt: struct {
        label: ?Ident,
        value: ?*const Expr,
    },

    /// Continue statement
    continue_stmt: ?Ident,

    /// Defer statement
    defer_stmt: *const Stmt,

    /// Errdefer statement
    errdefer_stmt: *const Stmt,

    /// Unreachable
    unreachable_stmt: void,

    pub fn write(self: Stmt, writer: anytype) !void {
        switch (self) {
            .var_decl => |v| {
                try writer.writeAll(if (v.is_const) "const " else "var ");
                try v.name.write(writer);
                if (v.typ) |t| {
                    try writer.writeAll(": ");
                    try t.write(writer);
                }
                if (v.value) |val| {
                    try writer.writeAll(" = ");
                    try val.write(writer);
                }
                try writer.writeAll(";\n");
            },
            .assign => |a| {
                try a.lhs.write(writer);
                try writer.writeAll(" = ");
                try a.rhs.write(writer);
                try writer.writeAll(";\n");
            },
            .compound_assign => |ca| {
                try ca.lhs.write(writer);
                try writer.print(" {s}= ", .{ca.op.toString()});
                try ca.rhs.write(writer);
                try writer.writeAll(";\n");
            },
            .expr_stmt => |e| {
                try e.write(writer);
                try writer.writeAll(";\n");
            },
            .if_stmt => |i| {
                try writer.writeAll("if (");
                try i.cond.write(writer);
                try writer.writeAll(") {\n");
                for (i.then_block) |stmt| try stmt.write(writer);
                try writer.writeAll("}");
                if (i.else_block) |eb| {
                    try writer.writeAll(" else {\n");
                    for (eb) |stmt| try stmt.write(writer);
                    try writer.writeAll("}");
                }
                try writer.writeAll("\n");
            },
            .while_stmt => |w| {
                try writer.writeAll("while (");
                try w.cond.write(writer);
                try writer.writeAll(") {\n");
                for (w.body) |stmt| try stmt.write(writer);
                try writer.writeAll("}");
                if (w.else_block) |eb| {
                    try writer.writeAll(" else {\n");
                    for (eb) |stmt| try stmt.write(writer);
                    try writer.writeAll("}");
                }
                try writer.writeAll("\n");
            },
            .for_stmt => |f| {
                try writer.writeAll("for (");
                try f.iterable.write(writer);
                try writer.writeAll(") |");
                for (f.captures, 0..) |cap, idx| {
                    if (idx > 0) try writer.writeAll(", ");
                    try cap.write(writer);
                }
                try writer.writeAll("| {\n");
                for (f.body) |stmt| try stmt.write(writer);
                try writer.writeAll("}");
                if (f.else_block) |eb| {
                    try writer.writeAll(" else {\n");
                    for (eb) |stmt| try stmt.write(writer);
                    try writer.writeAll("}");
                }
                try writer.writeAll("\n");
            },
            .switch_stmt => |s| {
                try writer.writeAll("switch (");
                try s.expr.write(writer);
                try writer.writeAll(") {\n");
                for (s.cases) |case| try case.write(writer);
                try writer.writeAll("}\n");
            },
            .return_stmt => |r| {
                try writer.writeAll("return");
                if (r) |val| {
                    try writer.writeAll(" ");
                    try val.write(writer);
                }
                try writer.writeAll(";\n");
            },
            .break_stmt => |b| {
                try writer.writeAll("break");
                if (b.label) |l| {
                    try writer.writeAll(" :");
                    try l.write(writer);
                }
                if (b.value) |v| {
                    try writer.writeAll(" ");
                    try v.write(writer);
                }
                try writer.writeAll(";\n");
            },
            .continue_stmt => |c| {
                try writer.writeAll("continue");
                if (c) |l| {
                    try writer.writeAll(" :");
                    try l.write(writer);
                }
                try writer.writeAll(";\n");
            },
            .defer_stmt => |d| {
                try writer.writeAll("defer ");
                try d.write(writer);
            },
            .errdefer_stmt => |e| {
                try writer.writeAll("errdefer ");
                try e.write(writer);
            },
            .unreachable_stmt => try writer.writeAll("unreachable;\n"),
        }
    }
};

/// Switch case
pub const SwitchCase = struct {
    patterns: []const Expr,
    is_else: bool,
    capture: ?Ident,
    body: []const Stmt,

    pub fn write(self: SwitchCase, writer: anytype) anyerror!void {
        if (self.is_else) {
            try writer.writeAll("else");
        } else {
            for (self.patterns, 0..) |pat, i| {
                if (i > 0) try writer.writeAll(", ");
                try pat.write(writer);
            }
        }
        if (self.capture) |cap| {
            try writer.writeAll(" => |");
            try cap.write(writer);
            try writer.writeAll("|");
        } else {
            try writer.writeAll(" =>");
        }
        try writer.writeAll(" {\n");
        for (self.body) |stmt| try stmt.write(writer);
        try writer.writeAll("},\n");
    }
};

// ============================================================================
// DECLARATIONS
// ============================================================================

/// Top-level declarations
pub const Decl = union(enum) {
    /// Function declaration
    fn_decl: FnDecl,

    /// Struct declaration
    struct_decl: StructDecl,

    /// Enum declaration
    enum_decl: EnumDecl,

    /// Union declaration
    union_decl: UnionDecl,

    /// Constant declaration
    const_decl: struct {
        is_pub: bool,
        name: Ident,
        typ: ?*const Type,
        value: Expr,
    },

    /// Variable declaration
    var_decl: struct {
        is_pub: bool,
        is_threadlocal: bool,
        name: Ident,
        typ: ?*const Type,
        value: ?Expr,
    },

    /// Test declaration
    test_decl: struct {
        name: []const u8,
        body: []const Stmt,
    },

    /// Comptime block
    comptime_block: []const Stmt,

    pub fn write(self: Decl, writer: anytype) !void {
        switch (self) {
            .fn_decl => |f| try f.write(writer),
            .struct_decl => |s| try s.write(writer),
            .enum_decl => |e| try e.write(writer),
            .union_decl => |u| try u.write(writer),
            .const_decl => |c| {
                if (c.is_pub) try writer.writeAll("pub ");
                try writer.writeAll("const ");
                try c.name.write(writer);
                if (c.typ) |t| {
                    try writer.writeAll(": ");
                    try t.write(writer);
                }
                try writer.writeAll(" = ");
                try c.value.write(writer);
                try writer.writeAll(";\n");
            },
            .var_decl => |v| {
                if (v.is_pub) try writer.writeAll("pub ");
                if (v.is_threadlocal) try writer.writeAll("threadlocal ");
                try writer.writeAll("var ");
                try v.name.write(writer);
                if (v.typ) |t| {
                    try writer.writeAll(": ");
                    try t.write(writer);
                }
                if (v.value) |val| {
                    try writer.writeAll(" = ");
                    try val.write(writer);
                }
                try writer.writeAll(";\n");
            },
            .test_decl => |t| {
                try writer.print("test \"{s}\" {{\n", .{t.name});
                for (t.body) |stmt| try stmt.write(writer);
                try writer.writeAll("}\n");
            },
            .comptime_block => |b| {
                try writer.writeAll("comptime {\n");
                for (b) |stmt| try stmt.write(writer);
                try writer.writeAll("}\n");
            },
        }
    }
};

/// Function declaration
pub const FnDecl = struct {
    doc_comment: ?[]const u8,
    is_pub: bool,
    is_export: bool,
    is_inline: bool,
    name: Ident,
    params: []const FnParam,
    ret_type: ?*const Type,
    body: ?[]const Stmt,

    pub fn write(self: FnDecl, writer: anytype) !void {
        if (self.doc_comment) |doc| {
            try writer.print("/// {s}\n", .{doc});
        }
        if (self.is_pub) try writer.writeAll("pub ");
        if (self.is_export) try writer.writeAll("export ");
        if (self.is_inline) try writer.writeAll("inline ");
        try writer.writeAll("fn ");
        try self.name.write(writer);
        try writer.writeAll("(");
        for (self.params, 0..) |param, i| {
            if (i > 0) try writer.writeAll(", ");
            try param.write(writer);
        }
        try writer.writeAll(") ");
        if (self.ret_type) |rt| {
            try rt.write(writer);
        } else {
            try writer.writeAll("void");
        }
        if (self.body) |b| {
            try writer.writeAll(" {\n");
            for (b) |stmt| try stmt.write(writer);
            try writer.writeAll("}\n");
        } else {
            try writer.writeAll(";\n");
        }
    }
};

/// Struct declaration
pub const StructDecl = struct {
    doc_comment: ?[]const u8,
    is_pub: bool,
    name: Ident,
    fields: []const StructField,
    decls: []const Decl,

    pub fn write(self: StructDecl, writer: anytype) anyerror!void {
        if (self.doc_comment) |doc| {
            try writer.print("/// {s}\n", .{doc});
        }
        if (self.is_pub) try writer.writeAll("pub ");
        try writer.writeAll("const ");
        try self.name.write(writer);
        try writer.writeAll(" = struct {\n");
        for (self.fields) |field| try field.write(writer);
        for (self.decls) |decl| try decl.write(writer);
        try writer.writeAll("};\n");
    }
};

/// Struct field
pub const StructField = struct {
    doc_comment: ?[]const u8,
    name: Ident,
    typ: Type,
    default: ?Expr,

    pub fn write(self: StructField, writer: anytype) !void {
        if (self.doc_comment) |doc| {
            try writer.print("    /// {s}\n", .{doc});
        }
        try writer.writeAll("    ");
        try self.name.write(writer);
        try writer.writeAll(": ");
        try self.typ.write(writer);
        if (self.default) |d| {
            try writer.writeAll(" = ");
            try d.write(writer);
        }
        try writer.writeAll(",\n");
    }
};

/// Enum declaration
pub const EnumDecl = struct {
    doc_comment: ?[]const u8,
    is_pub: bool,
    name: Ident,
    tag_type: ?*const Type,
    fields: []const EnumField,
    decls: []const Decl,

    pub fn write(self: EnumDecl, writer: anytype) anyerror!void {
        if (self.doc_comment) |doc| {
            try writer.print("/// {s}\n", .{doc});
        }
        if (self.is_pub) try writer.writeAll("pub ");
        try writer.writeAll("const ");
        try self.name.write(writer);
        try writer.writeAll(" = enum");
        if (self.tag_type) |tt| {
            try writer.writeAll("(");
            try tt.write(writer);
            try writer.writeAll(")");
        }
        try writer.writeAll(" {\n");
        for (self.fields) |field| try field.write(writer);
        for (self.decls) |decl| try decl.write(writer);
        try writer.writeAll("};\n");
    }
};

/// Enum field
pub const EnumField = struct {
    name: Ident,
    value: ?Expr,

    pub fn write(self: EnumField, writer: anytype) !void {
        try writer.writeAll("    ");
        try self.name.write(writer);
        if (self.value) |v| {
            try writer.writeAll(" = ");
            try v.write(writer);
        }
        try writer.writeAll(",\n");
    }
};

/// Union declaration
pub const UnionDecl = struct {
    doc_comment: ?[]const u8,
    is_pub: bool,
    name: Ident,
    tag_type: ?*const Type,
    fields: []const UnionField,
    decls: []const Decl,

    pub fn write(self: UnionDecl, writer: anytype) anyerror!void {
        if (self.doc_comment) |doc| {
            try writer.print("/// {s}\n", .{doc});
        }
        if (self.is_pub) try writer.writeAll("pub ");
        try writer.writeAll("const ");
        try self.name.write(writer);
        try writer.writeAll(" = union");
        if (self.tag_type) |tt| {
            try writer.writeAll("(");
            try tt.write(writer);
            try writer.writeAll(")");
        }
        try writer.writeAll(" {\n");
        for (self.fields) |field| try field.write(writer);
        for (self.decls) |decl| try decl.write(writer);
        try writer.writeAll("};\n");
    }
};

/// Union field
pub const UnionField = struct {
    name: Ident,
    typ: ?Type,

    pub fn write(self: UnionField, writer: anytype) !void {
        try writer.writeAll("    ");
        try self.name.write(writer);
        if (self.typ) |t| {
            try writer.writeAll(": ");
            try t.write(writer);
        }
        try writer.writeAll(",\n");
    }
};

// ============================================================================
// SOURCE FILE
// ============================================================================

/// A complete Zig source file
pub const SourceFile = struct {
    doc_comment: ?[]const u8,
    imports: []const Import,
    decls: []const Decl,

    pub fn write(self: SourceFile, writer: anytype) !void {
        if (self.doc_comment) |doc| {
            try writer.print("//! {s}\n\n", .{doc});
        }
        for (self.imports) |imp| try imp.write(writer);
        if (self.imports.len > 0) try writer.writeAll("\n");
        for (self.decls) |decl| {
            try decl.write(writer);
            try writer.writeAll("\n");
        }
    }
};

/// Import declaration
pub const Import = struct {
    name: Ident,
    path: []const u8,

    pub fn write(self: Import, writer: anytype) !void {
        try writer.writeAll("const ");
        try self.name.write(writer);
        try writer.print(" = @import(\"{s}\");\n", .{self.path});
    }
};

// ============================================================================
// TESTS
// ============================================================================

test "type writing" {
    var buf: [256]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buf);
    const writer = stream.writer();

    const int_type = Type{ .i32 = {} };
    try int_type.write(writer);
    try std.testing.expectEqualStrings("i32", stream.getWritten());
}

test "expression writing" {
    var buf: [256]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buf);
    const writer = stream.writer();

    const expr = Expr{ .int_lit = 42 };
    try expr.write(writer);
    try std.testing.expectEqualStrings("42", stream.getWritten());
}

test "function declaration writing" {
    var buf: [1024]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buf);
    const writer = stream.writer();

    const ret_type = Type{ .void = {} };
    const fn_decl = FnDecl{
        .doc_comment = "A simple function",
        .is_pub = true,
        .is_export = false,
        .is_inline = false,
        .name = Ident.init("hello"),
        .params = &[_]FnParam{},
        .ret_type = &ret_type,
        .body = &[_]Stmt{},
    };
    try fn_decl.write(writer);
    const output = stream.getWritten();
    try std.testing.expect(std.mem.indexOf(u8, output, "pub fn hello()") != null);
}
