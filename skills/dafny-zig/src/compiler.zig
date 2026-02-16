const std = @import("std");
const dast = @import("dast");
const zast = @import("zast");
const Allocator = std.mem.Allocator;

/// Compilation errors
pub const CompileError = error{
    OutOfMemory,
    UnsupportedFeature,
    InvalidType,
    InvalidExpression,
};

/// Compiler state for translating DAST to ZAST
pub const Compiler = struct {
    allocator: Allocator,
    /// Current module being compiled
    current_module: ?*const dast.Module = null,
    /// Type environment for resolving types
    type_env: std.StringHashMap(TypeInfo) = undefined,
    /// Variable environment for scoping
    var_env: std.StringHashMap(VarInfo) = undefined,
    /// Generated imports
    imports: std.ArrayListUnmanaged(zast.Import) = .{},
    /// Whether we need the runtime library
    needs_runtime: bool = false,

    const TypeInfo = struct {
        dafny_type: dast.Type,
        zig_type: zast.Type,
    };

    const VarInfo = struct {
        name: []const u8,
        zig_name: []const u8,
        ty: zast.Type,
        is_mutable: bool,
    };

    pub fn init(allocator: Allocator) Compiler {
        return .{
            .allocator = allocator,
            .type_env = std.StringHashMap(TypeInfo).init(allocator),
            .var_env = std.StringHashMap(VarInfo).init(allocator),
            .imports = .{},
        };
    }

    pub fn deinit(self: *Compiler) void {
        self.type_env.deinit();
        self.var_env.deinit();
        self.imports.deinit(self.allocator);
    }

    /// Compile a Dafny module to a Zig source file
    pub fn compileModule(self: *Compiler, module: *const dast.Module) CompileError!zast.SourceFile {
        self.current_module = module;
        self.needs_runtime = false;

        var decls = std.ArrayListUnmanaged(zast.Decl){};

        // Compile each module item
        if (module.body) |body| {
            for (body) |item| {
                const compiled = try self.compileModuleItem(item);
                for (compiled) |decl| {
                    try decls.append(self.allocator, decl);
                }
            }
        }

        // Build imports
        var imports = std.ArrayListUnmanaged(zast.Import){};
        try imports.append(self.allocator, .{ .name = .{ .name = "std" }, .path = "std" });

        if (self.needs_runtime) {
            try imports.append(self.allocator, .{ .name = .{ .name = "rt" }, .path = "dafny_runtime" });
        }

        return .{
            .doc_comment = null,
            .imports = imports.toOwnedSlice(self.allocator) catch &[_]zast.Import{},
            .decls = decls.toOwnedSlice(self.allocator) catch &[_]zast.Decl{},
        };
    }

    /// Compile a module item to zero or more Zig declarations
    fn compileModuleItem(self: *Compiler, item: dast.ModuleItem) CompileError![]zast.Decl {
        var decls = std.ArrayListUnmanaged(zast.Decl){};

        switch (item) {
            .module => |m| {
                // Nested modules become namespaced structs
                const nested = try self.compileModule(m);
                const struct_decl = zast.Decl{
                    .struct_decl = .{
                        .doc_comment = null,
                        .is_pub = true,
                        .name = .{ .name = m.name.dafny_name },
                        .fields = &[_]zast.StructField{},
                        .decls = nested.decls,
                    },
                };
                try decls.append(self.allocator, struct_decl);
            },
            .class => |c| {
                try decls.append(self.allocator, try self.compileClass(c));
            },
            .trait => |t| {
                try decls.append(self.allocator, try self.compileTrait(t));
            },
            .newtype => |n| {
                try decls.append(self.allocator, try self.compileNewtype(n));
            },
            .synonym_type => |s| {
                try decls.append(self.allocator, try self.compileSynonymType(s));
            },
            .datatype => |d| {
                const datatype_decls = try self.compileDatatype(d);
                for (datatype_decls) |decl| {
                    try decls.append(self.allocator, decl);
                }
            },
        }

        return decls.toOwnedSlice(self.allocator) catch &[_]zast.Decl{};
    }

    /// Compile a Dafny class to a Zig struct
    fn compileClass(self: *Compiler, class: *const dast.Class) CompileError!zast.Decl {
        var fields = std.ArrayListUnmanaged(zast.StructField){};
        var methods = std.ArrayListUnmanaged(zast.Decl){};

        for (class.body) |item| {
            switch (item) {
                .method => |m| {
                    try methods.append(self.allocator, try self.compileMethod(m));
                },
            }
        }

        // Add fields from class
        for (class.fields) |field| {
            try fields.append(self.allocator, .{
                .doc_comment = null,
                .name = .{ .name = self.sanitizeIdent(field.formal.name.dafny_name) },
                .typ = try self.compileType(field.formal.typ),
                .default = null,
            });
        }

        return .{
            .struct_decl = .{
                .doc_comment = null,
                .is_pub = true,
                .name = .{ .name = self.sanitizeIdent(class.name.dafny_name) },
                .fields = fields.toOwnedSlice(self.allocator) catch &[_]zast.StructField{},
                .decls = methods.toOwnedSlice(self.allocator) catch &[_]zast.Decl{},
            },
        };
    }

    /// Compile a Dafny trait to a Zig interface (vtable pattern)
    fn compileTrait(self: *Compiler, trait: *const dast.Trait) CompileError!zast.Decl {
        var fields = std.ArrayListUnmanaged(zast.StructField){};

        // Allocate types for pointers
        const vtable_type = try self.allocator.create(zast.Type);
        vtable_type.* = .{ .ident = .{ .name = "VTable" } };
        const anyopaque_type = try self.allocator.create(zast.Type);
        anyopaque_type.* = .{ .ident = .{ .name = "anyopaque" } };

        // Add vtable pointer
        try fields.append(self.allocator, .{
            .doc_comment = null,
            .name = .{ .name = "vtable" },
            .typ = .{ .ptr = .{
                .is_const = true,
                .child = vtable_type,
            } },
            .default = null,
        });

        // Add context pointer for implementations
        try fields.append(self.allocator, .{
            .doc_comment = null,
            .name = .{ .name = "ctx" },
            .typ = .{ .ptr = .{
                .is_const = false,
                .child = anyopaque_type,
            } },
            .default = null,
        });

        // Create VTable struct with function pointers
        var vtable_fields = std.ArrayListUnmanaged(zast.StructField){};
        for (trait.body) |item| {
            switch (item) {
                .method => |m| {
                    // Create function pointer type for each method
                    const fn_type = try self.compileMethodSignature(m);
                    try vtable_fields.append(self.allocator, .{
                        .doc_comment = null,
                        .name = .{ .name = self.sanitizeIdent(m.name.dafny_name) },
                        .typ = fn_type,
                        .default = null,
                    });
                },
            }
        }

        var inner_decls = std.ArrayListUnmanaged(zast.Decl){};
        try inner_decls.append(self.allocator, .{
            .struct_decl = .{
                .doc_comment = null,
                .is_pub = true,
                .name = .{ .name = "VTable" },
                .fields = vtable_fields.toOwnedSlice(self.allocator) catch &[_]zast.StructField{},
                .decls = &[_]zast.Decl{},
            },
        });

        return .{
            .struct_decl = .{
                .doc_comment = null,
                .is_pub = true,
                .name = .{ .name = self.sanitizeIdent(trait.name.dafny_name) },
                .fields = fields.toOwnedSlice(self.allocator) catch &[_]zast.StructField{},
                .decls = inner_decls.toOwnedSlice(self.allocator) catch &[_]zast.Decl{},
            },
        };
    }

    /// Compile a Dafny newtype to a Zig distinct type
    fn compileNewtype(self: *Compiler, newtype: *const dast.Newtype) CompileError!zast.Decl {
        const base_type = try self.compileType(newtype.base);

        // Create a struct wrapper for the newtype
        var fields = std.ArrayListUnmanaged(zast.StructField){};
        try fields.append(self.allocator, .{
            .doc_comment = null,
            .name = .{ .name = "value" },
            .typ = base_type,
            .default = null,
        });

        return .{
            .struct_decl = .{
                .doc_comment = null,
                .is_pub = true,
                .name = .{ .name = self.sanitizeIdent(newtype.name.dafny_name) },
                .fields = fields.toOwnedSlice(self.allocator) catch &[_]zast.StructField{},
                .decls = &[_]zast.Decl{},
            },
        };
    }

    /// Compile a Dafny synonym type to a Zig type alias
    fn compileSynonymType(self: *Compiler, syn: *const dast.SynonymType) CompileError!zast.Decl {
        const base_type = try self.compileType(syn.base);

        // For type aliases, we use an identifier or path expression as the value
        const value_expr: zast.Expr = switch (base_type) {
            .ident => |id| .{ .ident = id },
            .path => |p| .{ .path = p },
            else => .{ .ident = .{ .name = "anyopaque" } }, // fallback for complex types
        };

        return .{
            .const_decl = .{
                .is_pub = true,
                .name = .{ .name = self.sanitizeIdent(syn.name.dafny_name) },
                .typ = null,
                .value = value_expr,
            },
        };
    }

    /// Compile a Dafny datatype to a Zig tagged union
    fn compileDatatype(self: *Compiler, datatype: *const dast.Datatype) CompileError![]zast.Decl {
        var decls = std.ArrayListUnmanaged(zast.Decl){};

        // Create the tagged union
        var union_fields = std.ArrayListUnmanaged(zast.UnionField){};

        for (datatype.ctors) |ctor| {
            // If constructor has arguments, create a payload struct
            if (ctor.args.len > 0) {
                // For now, use void - in real implementation we'd create inline struct
                try union_fields.append(self.allocator, .{
                    .name = .{ .name = self.sanitizeIdent(ctor.name.dafny_name) },
                    .typ = zast.Type.void,
                });
            } else {
                // No payload - use void
                try union_fields.append(self.allocator, .{
                    .name = .{ .name = self.sanitizeIdent(ctor.name.dafny_name) },
                    .typ = null,
                });
            }
        }

        try decls.append(self.allocator, .{
            .union_decl = .{
                .doc_comment = null,
                .is_pub = true,
                .name = .{ .name = self.sanitizeIdent(datatype.name.dafny_name) },
                .tag_type = null, // auto-generate tag
                .fields = union_fields.toOwnedSlice(self.allocator) catch &[_]zast.UnionField{},
                .decls = &[_]zast.Decl{},
            },
        });

        return decls.toOwnedSlice(self.allocator) catch &[_]zast.Decl{};
    }

    /// Compile a method to a Zig function
    fn compileMethod(self: *Compiler, method: *const dast.Method) CompileError!zast.Decl {
        var params = std.ArrayListUnmanaged(zast.FnParam){};

        // Add self parameter for methods
        if (!method.is_static) {
            const self_type = try self.allocator.create(zast.Type);
            self_type.* = .{ .ident = .{ .name = "Self" } };
            try params.append(self.allocator, .{
                .name = .{ .name = "self" },
                .typ = .{ .ptr = .{
                    .is_const = !method.has_body, // const if no body (abstract)
                    .child = self_type,
                } },
            });
        }

        // Add regular parameters
        for (method.params) |param| {
            try params.append(self.allocator, .{
                .name = .{ .name = self.sanitizeIdent(param.name.dafny_name) },
                .typ = try self.compileType(param.typ),
            });
        }

        // Compile return type
        const ret_type: ?*const zast.Type = if (method.out_types.len == 0)
            null
        else if (method.out_types.len == 1) blk: {
            const t = try self.allocator.create(zast.Type);
            t.* = try self.compileType(method.out_types[0]);
            break :blk t;
        } else null; // TODO: handle multiple returns

        // Compile body
        const body: ?[]const zast.Stmt = if (method.has_body and method.body.len > 0) blk: {
            var stmts = std.ArrayListUnmanaged(zast.Stmt){};
            for (method.body) |stmt| {
                try stmts.append(self.allocator, try self.compileStatement(stmt));
            }
            break :blk stmts.toOwnedSlice(self.allocator) catch &[_]zast.Stmt{};
        } else null;

        return .{
            .fn_decl = .{
                .doc_comment = null,
                .is_pub = true,
                .is_export = false,
                .is_inline = false,
                .name = .{ .name = self.sanitizeIdent(method.name.dafny_name) },
                .params = params.toOwnedSlice(self.allocator) catch &[_]zast.FnParam{},
                .ret_type = ret_type,
                .body = body,
            },
        };
    }

    /// Compile a method signature to a function pointer type
    fn compileMethodSignature(self: *Compiler, method: *const dast.Method) CompileError!zast.Type {
        var fn_params = std.ArrayListUnmanaged(zast.FnParam){};

        // Add context pointer as first param
        const anyopaque_type = try self.allocator.create(zast.Type);
        anyopaque_type.* = .{ .ident = .{ .name = "anyopaque" } };
        try fn_params.append(self.allocator, .{
            .name = .{ .name = "ctx" },
            .typ = .{ .ptr = .{
                .child = anyopaque_type,
                .is_const = false,
            } },
        });

        // Add regular parameters
        for (method.params) |param| {
            try fn_params.append(self.allocator, .{
                .name = .{ .name = self.sanitizeIdent(param.name.dafny_name) },
                .typ = try self.compileType(param.typ),
            });
        }

        const ret_type: *const zast.Type = if (method.out_types.len == 0) blk: {
            const t = try self.allocator.create(zast.Type);
            t.* = .void;
            break :blk t;
        } else if (method.out_types.len == 1) blk: {
            const t = try self.allocator.create(zast.Type);
            t.* = try self.compileType(method.out_types[0]);
            break :blk t;
        } else blk: {
            const t = try self.allocator.create(zast.Type);
            t.* = .void; // TODO: tuple returns
            break :blk t;
        };

        return .{
            .function = .{
                .params = fn_params.toOwnedSlice(self.allocator) catch &[_]zast.FnParam{},
                .ret = ret_type,
            },
        };
    }

    /// Compile a Dafny type to a Zig type
    pub fn compileType(self: *Compiler, ty: dast.Type) CompileError!zast.Type {
        switch (ty) {
            .primitive => |p| return self.compilePrimitive(p),
            .user_defined => |ud| {
                // Build path from resolved type
                if (ud.path.len > 0) {
                    var path_segments = std.ArrayListUnmanaged(zast.Ident){};
                    for (ud.path) |ident| {
                        try path_segments.append(self.allocator, .{ .name = self.sanitizeIdent(ident.id) });
                    }
                    if (path_segments.items.len == 1) {
                        return .{ .ident = path_segments.items[0] };
                    }
                    return .{ .path = .{ .segments = path_segments.toOwnedSlice(self.allocator) catch &[_]zast.Ident{} } };
                }
                return .{ .ident = .{ .name = "anyopaque" } };
            },
            .tuple => |types| {
                // Zig doesn't have tuples, use anonymous struct type
                // For now, just use anyopaque as a placeholder
                _ = types;
                return .{ .ident = .{ .name = "anyopaque" } };
            },
            .array => |arr| {
                const elem = try self.allocator.create(zast.Type);
                elem.* = try self.compileType(arr.element.*);
                self.needs_runtime = true;
                return .{ .slice = .{
                    .is_const = false,
                    .child = elem,
                } };
            },
            .seq => |elem_ptr| {
                self.needs_runtime = true;
                const elem = try self.allocator.create(zast.Type);
                elem.* = try self.compileType(elem_ptr.*);
                return .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "Seq" } } } };
            },
            .set => |_| {
                self.needs_runtime = true;
                return .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "Set" } } } };
            },
            .multiset => |_| {
                self.needs_runtime = true;
                return .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "MultiSet" } } } };
            },
            .map => |_| {
                self.needs_runtime = true;
                return .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "Map" } } } };
            },
            .arrow => |arrow| {
                var param_list = std.ArrayListUnmanaged(zast.FnParam){};
                for (arrow.args) |arg| {
                    try param_list.append(self.allocator, .{
                        .name = null,
                        .typ = try self.compileType(arg),
                    });
                }
                const ret = try self.allocator.create(zast.Type);
                ret.* = try self.compileType(arrow.result.*);
                return .{
                    .function = .{
                        .params = param_list.toOwnedSlice(self.allocator) catch &[_]zast.FnParam{},
                        .ret = ret,
                    },
                };
            },
            .type_arg => |name| {
                return .{ .ident = .{ .name = self.sanitizeIdent(name.id) } };
            },
            .object => {
                const anyopaque_child = try self.allocator.create(zast.Type);
                anyopaque_child.* = .{ .ident = .{ .name = "anyopaque" } };
                return .{ .ptr = .{
                    .child = anyopaque_child,
                    .is_const = false,
                } };
            },
            .set_builder => |inner_ptr| {
                self.needs_runtime = true;
                _ = inner_ptr; // Element type for set comprehension
                return .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "Set" } } } };
            },
            .map_builder => |mb| {
                self.needs_runtime = true;
                _ = mb; // Key/value types for map comprehension
                return .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "Map" } } } };
            },
            .passthrough => |zig_type| {
                // Direct Zig type passthrough
                return .{ .ident = .{ .name = zig_type } };
            },
        }
    }

    /// Compile a Dafny primitive type to a Zig type
    fn compilePrimitive(self: *Compiler, prim: dast.Primitive) zast.Type {
        _ = self;
        return switch (prim) {
            .int => .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "BigInt" } } } },
            .real => .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "BigRational" } } } },
            .string => .{ .ident = .{ .name = "[]const u8" } },
            .bool => .bool,
            .char => .u32, // Unicode codepoint
        };
    }

    /// Compile a Dafny statement to a Zig statement
    pub fn compileStatement(self: *Compiler, stmt: dast.Statement) CompileError!zast.Stmt {
        switch (stmt) {
            .decl_stmt => |decl| {
                const init_expr: ?*const zast.Expr = if (decl.value) |init_val| blk: {
                    const e = try self.allocator.create(zast.Expr);
                    e.* = try self.compileExpression(init_val.*);
                    break :blk e;
                } else null;

                const typ_ptr = try self.allocator.create(zast.Type);
                typ_ptr.* = try self.compileType(decl.typ);
                return .{
                    .var_decl = .{
                        .name = .{ .name = self.sanitizeIdent(decl.name.dafny_name) },
                        .typ = typ_ptr,
                        .value = init_expr,
                        .is_const = true,
                    },
                };
            },
            .assign => |assign| {
                const lhs = try self.compileAssignLhs(assign.lhs.*);
                const rhs_expr = try self.allocator.create(zast.Expr);
                rhs_expr.* = try self.compileExpression(assign.value.*);
                return .{
                    .assign = .{
                        .lhs = lhs,
                        .rhs = rhs_expr,
                    },
                };
            },
            .if_stmt => |if_s| {
                const cond = try self.allocator.create(zast.Expr);
                cond.* = try self.compileExpression(if_s.cond.*);

                var then_stmts = std.ArrayListUnmanaged(zast.Stmt){};
                for (if_s.then_branch) |s| {
                    try then_stmts.append(self.allocator, try self.compileStatement(s));
                }
                const then_body = try self.allocator.create(zast.Expr);
                then_body.* = .{ .block = .{
                    .label = null,
                    .stmts = then_stmts.toOwnedSlice(self.allocator) catch &[_]zast.Stmt{},
                    .result = null,
                } };

                const else_body: ?*const zast.Expr = if (if_s.else_branch.len > 0) blk: {
                    var else_stmts = std.ArrayListUnmanaged(zast.Stmt){};
                    for (if_s.else_branch) |s| {
                        try else_stmts.append(self.allocator, try self.compileStatement(s));
                    }
                    const eb = try self.allocator.create(zast.Expr);
                    eb.* = .{ .block = .{
                        .label = null,
                        .stmts = else_stmts.toOwnedSlice(self.allocator) catch &[_]zast.Stmt{},
                        .result = null,
                    } };
                    break :blk eb;
                } else null;

                return .{
                    .if_stmt = .{
                        .cond = cond,
                        .then_block = then_stmts.toOwnedSlice(self.allocator) catch &[_]zast.Stmt{},
                        .else_block = if (else_body) |eb| eb.block.stmts else null,
                    },
                };
            },
            .while_stmt => |while_s| {
                const cond = try self.allocator.create(zast.Expr);
                cond.* = try self.compileExpression(while_s.cond.*);

                var body_stmts = std.ArrayListUnmanaged(zast.Stmt){};
                for (while_s.body) |s| {
                    try body_stmts.append(self.allocator, try self.compileStatement(s));
                }

                return .{
                    .while_stmt = .{
                        .cond = cond,
                        .body = body_stmts.toOwnedSlice(self.allocator) catch &[_]zast.Stmt{},
                        .else_block = null,
                    },
                };
            },
            .foreach => |foreach| {
                // Compile iterable expression
                const iterable = try self.allocator.create(zast.Expr);
                iterable.* = try self.compileExpression(foreach.over.*);

                var captures = std.ArrayListUnmanaged(zast.Ident){};
                try captures.append(self.allocator, .{ .name = self.sanitizeIdent(foreach.bound_name.dafny_name) });

                var body_stmts = std.ArrayListUnmanaged(zast.Stmt){};
                for (foreach.body) |s| {
                    try body_stmts.append(self.allocator, try self.compileStatement(s));
                }

                return .{
                    .for_stmt = .{
                        .captures = captures.toOwnedSlice(self.allocator) catch &[_]zast.Ident{},
                        .iterable = iterable,
                        .body = body_stmts.toOwnedSlice(self.allocator) catch &[_]zast.Stmt{},
                        .else_block = null,
                    },
                };
            },
            .call => |call| {
                const call_expr = try self.allocator.create(zast.Expr);
                call_expr.* = try self.compileCall(call.on, call.call_name, call.args);
                return .{ .expr_stmt = call_expr };
            },
            .return_stmt => |ret| {
                const val: ?*const zast.Expr = if (ret) |r| blk: {
                    const e = try self.allocator.create(zast.Expr);
                    e.* = try self.compileExpression(r.*);
                    break :blk e;
                } else null;
                return .{ .return_stmt = val };
            },
            .print => |expr_ptr| {
                // Generate std.debug.print call
                var args = std.ArrayListUnmanaged(zast.Expr){};
                try args.append(self.allocator, .{ .string_lit = "{any}" });
                try args.append(self.allocator, try self.compileExpression(expr_ptr.*));

                const print_fn = try self.allocator.create(zast.Expr);
                print_fn.* = .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "std" }, .{ .name = "debug" }, .{ .name = "print" } } } };

                const call_expr = try self.allocator.create(zast.Expr);
                call_expr.* = .{
                    .call = .{
                        .func = print_fn,
                        .args = args.toOwnedSlice(self.allocator) catch &[_]zast.Expr{},
                    },
                };
                return .{ .expr_stmt = call_expr };
            },
            .break_stmt => |label| {
                return .{ .break_stmt = .{
                    .label = if (label) |l| zast.Ident{ .name = l } else null,
                    .value = null,
                } };
            },

            .labeled => |labeled| {
                var stmts = std.ArrayListUnmanaged(zast.Stmt){};
                for (labeled.body) |s| {
                    try stmts.append(self.allocator, try self.compileStatement(s));
                }
                const block = try self.allocator.create(zast.Expr);
                block.* = .{ .block = .{
                    .label = .{ .name = labeled.label },
                    .stmts = stmts.toOwnedSlice(self.allocator) catch &[_]zast.Stmt{},
                    .result = null,
                } };
                return .{ .expr_stmt = block };
            },
            .halt => {
                return .{ .unreachable_stmt = {} };
            },
            // Other statements - return empty block as no-op
            .early_return, .tail_recursive, .jump_tail_call_start, .construct_new_array => {
                return .{ .expr_stmt = blk: {
                    const empty = try self.allocator.create(zast.Expr);
                    empty.* = .{ .block = .{ .label = null, .stmts = &[_]zast.Stmt{}, .result = null } };
                    break :blk empty;
                } };
            },
        }
    }

    /// Compile assignment left-hand side
    fn compileAssignLhs(self: *Compiler, lhs: dast.AssignLhs) CompileError!*const zast.Expr {
        const expr = try self.allocator.create(zast.Expr);
        switch (lhs) {
            .ident => |name| {
                expr.* = .{ .ident = .{ .name = self.sanitizeIdent(name.id) } };
            },
            .select => |sel| {
                const base = try self.allocator.create(zast.Expr);
                base.* = try self.compileExpression(sel.expr.*);
                expr.* = .{ .field = .{
                    .expr = base,
                    .field = .{ .name = self.sanitizeIdent(sel.field.dafny_name) },
                } };
            },
            .index => |idx| {
                const base = try self.allocator.create(zast.Expr);
                base.* = try self.compileExpression(idx.expr.*);
                const index_expr = try self.allocator.create(zast.Expr);
                index_expr.* = try self.compileExpression(idx.indices[0]);
                expr.* = .{ .index = .{
                    .expr = base,
                    .index = index_expr, // Zig only supports single index
                } };
            },
        }
        return expr;
    }

    /// Compile a Dafny expression to a Zig expression
    pub fn compileExpression(self: *Compiler, expr: dast.Expression) CompileError!zast.Expr {
        switch (expr) {
            .literal => |lit| return self.compileLiteral(lit),
            .ident => |name| return .{ .ident = .{ .name = self.sanitizeIdent(name.dafny_name) } },
            .companion => |path| {
                var parts = std.ArrayListUnmanaged([]const u8){};
                for (path) |ident| {
                    try parts.append(self.allocator, self.sanitizeIdent(ident.id));
                }
                if (parts.items.len == 1) {
                    return .{ .ident = .{ .name = parts.items[0] } };
                }
                var ident_parts = std.ArrayListUnmanaged(zast.Ident){};
                for (parts.items) |part| {
                    try ident_parts.append(self.allocator, .{ .name = part });
                }
                return .{ .path = .{ .segments = ident_parts.toOwnedSlice(self.allocator) catch &[_]zast.Ident{} } };
            },
            .tuple => |exprs| {
                var values = std.ArrayListUnmanaged(zast.Expr){};
                for (exprs) |e| {
                    try values.append(self.allocator, try self.compileExpression(e));
                }
                return .{ .anon_array = values.toOwnedSlice(self.allocator) catch &[_]zast.Expr{} };
            },
            .new => |new| {
                // Object creation becomes struct initialization
                var fields = std.ArrayListUnmanaged(zast.FieldInit){};
                for (new.args, 0..) |arg, i| {
                    const val = try self.allocator.create(zast.Expr);
                    val.* = try self.compileExpression(arg);
                    // Use numbered field names
                    const name = std.fmt.allocPrint(self.allocator, "_{d}", .{i}) catch "field";
                    try fields.append(self.allocator, .{ .name = .{ .name = name }, .value = val.* });
                }
                // Build type from path
                var type_path = std.ArrayListUnmanaged(zast.Ident){};
                for (new.path) |ident| {
                    try type_path.append(self.allocator, .{ .name = ident.id });
                }
                return .{
                    .struct_init = .{
                        .typ = try self.allocator.create(zast.Type), // Allocate type on heap if needed, or modify zast to hold value
                        .fields = fields.toOwnedSlice(self.allocator) catch &[_]zast.FieldInit{},
                    },
                };
            },
            .new_uninit_array => |arr| {
                // Array allocation
                self.needs_runtime = true;
                var dims = std.ArrayListUnmanaged(zast.Expr){};
                for (arr.dims) |dim| {
                    try dims.append(self.allocator, try self.compileExpression(dim));
                }
                const alloc_fn = try self.allocator.create(zast.Expr);
                alloc_fn.* = .{ .field = .{
                    .expr = blk: {
                        const rt = try self.allocator.create(zast.Expr);
                        rt.* = .{ .ident = .{ .name = "rt" } };
                        break :blk rt;
                    },
                    .field = .{ .name = "allocArray" },
                } };
                return .{
                    .call = .{
                        .func = alloc_fn,
                        .args = dims.toOwnedSlice(self.allocator) catch &[_]zast.Expr{},
                    },
                };
            },
            .select => |sel| {
                const base = try self.allocator.create(zast.Expr);
                base.* = try self.compileExpression(sel.expr.*);
                return .{ .field = .{
                    .expr = base,
                    .field = .{ .name = self.sanitizeIdent(sel.field.dafny_name) },
                } };
            },
            .index => |idx| {
                const base = try self.allocator.create(zast.Expr);
                base.* = try self.compileExpression(idx.expr.*);
                const index_expr = try self.allocator.create(zast.Expr);
                index_expr.* = try self.compileExpression(idx.indices[0]);
                return .{ .index = .{
                    .expr = base,
                    .index = index_expr,
                } };
            },
            .index_range => |rng| {
                const base = try self.allocator.create(zast.Expr);
                base.* = try self.compileExpression(rng.expr.*);

                const lo: ?*const zast.Expr = if (rng.lo) |l| blk: {
                    const e = try self.allocator.create(zast.Expr);
                    e.* = try self.compileExpression(l.*);
                    break :blk e;
                } else null;

                const hi: ?*const zast.Expr = if (rng.hi) |h| blk: {
                    const e = try self.allocator.create(zast.Expr);
                    e.* = try self.compileExpression(h.*);
                    break :blk e;
                } else null;

                return .{
                    .slice = .{
                        .expr = base,
                        .lo = lo,
                        .hi = hi,
                    },
                };
            },
            .call => |call| {
                return self.compileCall(call.on, call.call_name, call.args);
            },
            .un_op => |un| {
                const operand = try self.allocator.create(zast.Expr);
                operand.* = try self.compileExpression(un.expr.*);
                const op: zast.UnaryOp = switch (un.op) {
                    .not => .bool_not,
                    .bitnot => .bit_not,
                    .cardinality => {
                        // |x| becomes x.len()
                        return .{ .field = .{
                            .expr = operand,
                            .field = .{ .name = "len" },
                        } };
                    },
                };
                return .{ .un_op = .{ .op = op, .expr = operand } };
            },
            .bin_op => |bin| {
                return self.compileBinOp(bin);
            },
            .ite => |tern| {
                const cond = try self.allocator.create(zast.Expr);
                cond.* = try self.compileExpression(tern.cond.*);
                const then_e = try self.allocator.create(zast.Expr);
                then_e.* = try self.compileExpression(tern.then_expr.*);
                const else_e = try self.allocator.create(zast.Expr);
                else_e.* = try self.compileExpression(tern.else_expr.*);

                return .{
                    .if_expr = .{
                        .cond = cond,
                        .then_expr = then_e,
                        .else_expr = else_e,
                    },
                };
            },
            .lambda => |lam| {
                var params = std.ArrayListUnmanaged(zast.FnParam){};
                for (lam.params) |p| {
                    try params.append(self.allocator, .{
                        .name = .{ .name = self.sanitizeIdent(p.name.dafny_name) },
                        .typ = try self.compileType(p.typ),
                    });
                }
                // TODO: compile lambda body (list of statements) properly

                // Lambda becomes anonymous function literal (stub)
                return .{
                    .struct_init = .{
                        .typ = null,
                        .fields = &[_]zast.FieldInit{},
                    },
                };
            },
            .seq_construct => |seq| {
                self.needs_runtime = true;
                const len = try self.allocator.create(zast.Expr);
                len.* = try self.compileExpression(seq.length.*);
                const elem_fn = try self.allocator.create(zast.Expr);
                elem_fn.* = try self.compileExpression(seq.elem.*);

                const seq_fn = try self.allocator.create(zast.Expr);
                seq_fn.* = .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "Seq" }, .{ .name = "init" } } } };

                return .{
                    .call = .{
                        .func = seq_fn,
                        .args = &[_]zast.Expr{ len.*, elem_fn.* },
                    },
                };
            },
            .seq_value => |sv| {
                self.needs_runtime = true;
                var arr_elems = std.ArrayListUnmanaged(zast.Expr){};
                for (sv.elements) |e| {
                    const elem = try self.allocator.create(zast.Expr);
                    elem.* = try self.compileExpression(e);
                    try arr_elems.append(self.allocator, elem.*);
                }
                return .{
                    .array_init = .{
                        .typ = null,
                        .elements = arr_elems.toOwnedSlice(self.allocator) catch &[_]zast.Expr{},
                    },
                };
            },
            .set_value => |elems| {
                self.needs_runtime = true;
                var arr_elems = std.ArrayListUnmanaged(zast.Expr){};
                for (elems) |e| {
                    const elem = try self.allocator.create(zast.Expr);
                    elem.* = try self.compileExpression(e);
                    try arr_elems.append(self.allocator, elem.*);
                }
                const set_fn = try self.allocator.create(zast.Expr);
                set_fn.* = .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "Set" }, .{ .name = "fromSlice" } } } };

                const arr = try self.allocator.create(zast.Expr);
                arr.* = .{
                    .array_init = .{
                        .typ = null,
                        .elements = arr_elems.toOwnedSlice(self.allocator) catch &[_]zast.Expr{},
                    },
                };

                return .{
                    .call = .{
                        .func = set_fn,
                        .args = &[_]zast.Expr{arr.*},
                    },
                };
            },
            .map_value => |entries| {
                self.needs_runtime = true;
                var keys = std.ArrayListUnmanaged(zast.Expr){};
                var vals = std.ArrayListUnmanaged(zast.Expr){};
                for (entries) |entry| {
                    const k = try self.allocator.create(zast.Expr);
                    k.* = try self.compileExpression(entry.key);
                    try keys.append(self.allocator, k.*);
                    const v = try self.allocator.create(zast.Expr);
                    v.* = try self.compileExpression(entry.value);
                    try vals.append(self.allocator, v.*);
                }
                const map_fn = try self.allocator.create(zast.Expr);
                map_fn.* = .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "Map" }, .{ .name = "fromEntries" } } } };

                return .{
                    .call = .{
                        .func = map_fn,
                        .args = &[_]zast.Expr{},
                    },
                };
            },
            .datatype_value => |dt| {
                // Constructor call for datatype
                const ctor_name = self.sanitizeIdent(dt.variant.dafny_name);
                // TODO: handle arguments (dt.contents)
                return .{ .ident = .{ .name = ctor_name } };
            },
            .this => return .{ .ident = .{ .name = "self" } },
            .type_test => |tt| {
                const e = try self.allocator.create(zast.Expr);
                e.* = try self.compileExpression(tt.expr.*);
                // Type test becomes @TypeOf comparison
                const typeof_fn = try self.allocator.create(zast.Expr);
                typeof_fn.* = .{ .builtin = "@TypeOf" };

                return .{
                    .call = .{
                        .func = typeof_fn,
                        .args = &[_]zast.Expr{e.*},
                    },
                };
            },
            .convert => |conv| {
                const e = try self.allocator.create(zast.Expr);
                e.* = try self.compileExpression(conv.expr.*);
                const target_type = try self.compileType(conv.to);
                // Type conversion
                return .{
                    .cast = .{
                        .expr = e,
                        .ty = target_type,
                    },
                };
            },
            else => return error.UnsupportedFeature,
        }
    }

    /// Compile a literal
    fn compileLiteral(self: *Compiler, lit: dast.Literal) CompileError!zast.Expr {
        _ = self;
        switch (lit) {
            .bool_lit => |b| return .{ .bool_lit = b },
            .int_lit => |i| {
                // Parse int string
                const val = std.fmt.parseInt(i128, i, 10) catch 0;
                return .{ .int_lit = val };
            },
            .decimal_lit => |_| return .{ .float_lit = 0.0 },
            .char_lit => |c| return .{ .char_lit = @truncate(c) },
            .char_lit_utf16 => |c| return .{ .char_lit = @truncate(c) },
            .string_lit => |s| return .{ .string_lit = s },
            .null_lit => return .null_lit,
        }
    }

    /// Compile a binary operation
    fn compileBinOp(self: *Compiler, bin: anytype) CompileError!zast.Expr {
        const lhs = try self.allocator.create(zast.Expr);
        lhs.* = try self.compileExpression(bin.left.*);
        const rhs = try self.allocator.create(zast.Expr);
        rhs.* = try self.compileExpression(bin.right.*);

        // Map Dafny operators to Zig operators
        const op: ?zast.BinOp = switch (bin.op) {
            // Comparison
            .eq => .eq,
            .neq => .neq,
            .lt => .lt,
            .le => .le,
            .gt => .gt,
            .ge => .ge,
            // Logical
            .and_op => .bool_and,
            .or_op => .bool_or,
            .implies => null, // a ==> b becomes !a || b
            // explies not in dast BinOp
            .iff => null, // a <==> b becomes a == b
            // Arithmetic
            .add => .add,
            .sub => .sub,
            .mul => .mul,
            .div => .div,
            .mod => .mod,
            // Bitwise
            .bit_and => .bit_and,
            .bit_or => .bit_or,
            .bit_xor => .bit_xor,
            .bit_shl => .shl,
            .bit_shr => .shr,
            // Collection operations - need runtime calls
            .in_set, .not_in_set, .set_union, .set_intersection, .set_difference, .proper_subset, .subset, .superset, .proper_superset, .disjoint, .seq_concat, .seq_prefix, .seq_proper_prefix, .multiset_union, .multiset_intersection, .multiset_difference, .submultiset, .proper_submultiset, .supermultiset, .proper_supermultiset, .multiset_disjoint, .map_merge, .map_subtraction, .passthrough => null,
        };

        if (op) |z_op| {
            return .{
                .bin_op = .{
                    .op = z_op,
                    .left = lhs,
                    .right = rhs,
                },
            };
        }

        // Handle special operators
        switch (bin.op) {
            .implies => {
                // a ==> b  becomes  !a or b
                const not_a = try self.allocator.create(zast.Expr);
                not_a.* = .{ .un_op = .{ .op = .bool_not, .expr = lhs } };
                return .{
                    .bin_op = .{
                        .op = .bool_or,
                        .left = not_a,
                        .right = rhs,
                    },
                };
            },
            // explies (a <== b) not in Dafny AST; handled by else branch
            .iff => {
                // a <==> b  becomes  a == b
                return .{
                    .bin_op = .{
                        .op = .eq,
                        .left = lhs,
                        .right = rhs,
                    },
                };
            },
            .in_set => {
                self.needs_runtime = true;
                const contains_fn = try self.allocator.create(zast.Expr);
                contains_fn.* = .{ .field = .{ .expr = rhs, .field = .{ .name = "contains" } } };
                return .{
                    .call = .{
                        .func = contains_fn,
                        .args = &[_]zast.Expr{lhs.*},
                    },
                };
            },
            .not_in_set => {
                self.needs_runtime = true;
                const contains_fn = try self.allocator.create(zast.Expr);
                contains_fn.* = .{ .field = .{ .expr = rhs, .field = .{ .name = "contains" } } };
                const contains_call = try self.allocator.create(zast.Expr);
                contains_call.* = .{
                    .call = .{
                        .func = contains_fn,
                        .args = &[_]zast.Expr{lhs.*},
                    },
                };
                return .{ .un_op = .{ .op = .bool_not, .expr = contains_call } };
            },
            .set_union => {
                self.needs_runtime = true;
                const union_fn = try self.allocator.create(zast.Expr);
                union_fn.* = .{ .field = .{ .expr = lhs, .field = .{ .name = "setUnion" } } };
                return .{
                    .call = .{
                        .func = union_fn,
                        .args = &[_]zast.Expr{rhs.*},
                    },
                };
            },
            .set_intersection => {
                self.needs_runtime = true;
                const inter_fn = try self.allocator.create(zast.Expr);
                inter_fn.* = .{ .field = .{ .expr = lhs, .field = .{ .name = "intersect" } } };
                return .{
                    .call = .{
                        .func = inter_fn,
                        .args = &[_]zast.Expr{rhs.*},
                    },
                };
            },
            .set_difference => {
                self.needs_runtime = true;
                const diff_fn = try self.allocator.create(zast.Expr);
                diff_fn.* = .{ .field = .{ .expr = lhs, .field = .{ .name = "difference" } } };
                return .{
                    .call = .{
                        .func = diff_fn,
                        .args = &[_]zast.Expr{rhs.*},
                    },
                };
            },
            .subset => {
                self.needs_runtime = true;
                const subset_fn = try self.allocator.create(zast.Expr);
                subset_fn.* = .{ .field = .{ .expr = lhs, .field = .{ .name = "isSubsetOf" } } };
                return .{
                    .call = .{
                        .func = subset_fn,
                        .args = &[_]zast.Expr{rhs.*},
                    },
                };
            },
            .seq_concat => {
                self.needs_runtime = true;
                const concat_fn = try self.allocator.create(zast.Expr);
                concat_fn.* = .{ .field = .{ .expr = lhs, .field = .{ .name = "concat" } } };
                return .{
                    .call = .{
                        .func = concat_fn,
                        .args = &[_]zast.Expr{rhs.*},
                    },
                };
            },
            else => {
                // Fallback - use runtime helper
                self.needs_runtime = true;
                return .{ .ident = .{ .name = "TODO_UNHANDLED_OP" } };
            },
        }
    }

    /// Compile a method/function call
    fn compileCall(self: *Compiler, on: ?*const dast.Expression, call_name: dast.CallName, args: []const dast.Expression) CompileError!zast.Expr {
        var call_args = std.ArrayListUnmanaged(zast.Expr){};

        // Compile arguments
        for (args) |arg| {
            try call_args.append(self.allocator, try self.compileExpression(arg));
        }

        // Build function expression
        const func: *const zast.Expr = switch (call_name) {
            .call_name => |name| blk: {
                const f = try self.allocator.create(zast.Expr);
                if (on) |receiver| {
                    const base = try self.allocator.create(zast.Expr);
                    base.* = try self.compileExpression(receiver.*);
                    f.* = .{ .field = .{
                        .expr = base,
                        .field = .{ .name = self.sanitizeIdent(name.dafny_name) },
                    } };
                } else {
                    f.* = .{ .ident = .{ .name = self.sanitizeIdent(name.dafny_name) } };
                }
                break :blk f;
            },
            .map_builder_add, .map_builder_build, .set_builder_add, .set_builder_build => |_| blk: {
                self.needs_runtime = true;
                const f = try self.allocator.create(zast.Expr);
                f.* = .{ .path = .{ .segments = &[_]zast.Ident{ .{ .name = "rt" }, .{ .name = "Builder" }, .{ .name = "new" } } } }; // TODO: correct runtime builder
                break :blk f;
            },
        };

        return .{
            .call = .{
                .func = func,
                .args = call_args.toOwnedSlice(self.allocator) catch &[_]zast.Expr{},
            },
        };
    }

    /// Sanitize a Dafny identifier for use in Zig
    fn sanitizeIdent(self: *Compiler, name: []const u8) []const u8 {
        // Zig reserved words
        const reserved = [_][]const u8{
            "align",      "and",       "anyframe",   "anytype",
            "asm",        "async",     "await",      "break",
            "catch",      "comptime",  "const",      "continue",
            "defer",      "else",      "enum",       "errdefer",
            "error",      "export",    "extern",     "false",
            "fn",         "for",       "if",         "import",
            "inline",     "noalias",   "noinline",   "nosuspend",
            "null",       "opaque",    "or",         "orelse",
            "packed",     "pub",       "resume",     "return",
            "struct",     "suspend",   "switch",     "test",
            "threadlocal", "true",     "try",        "type",
            "undefined",  "union",     "unreachable", "usingnamespace",
            "var",        "void",      "volatile",   "while",
        };

        for (reserved) |kw| {
            if (std.mem.eql(u8, name, kw)) {
                return std.fmt.allocPrint(self.allocator, "@\"{s}\"", .{name}) catch name;
            }
        }

        // Handle names starting with underscore (Zig convention for unused)
        if (name.len > 0 and name[0] == '_' and name.len > 1) {
            return std.fmt.allocPrint(self.allocator, "d_{s}", .{name[1..]}) catch name;
        }

        return self.allocator.dupe(u8, name) catch name;
    }
};

// Tests
test "compile primitive types" {
    const allocator = std.testing.allocator;
    var compiler = Compiler.init(allocator);
    defer compiler.deinit();

            const bool_type = try compiler.compileType(.{ .primitive = .bool });
        
            // Expect the Zig type to be the boolean primitive
        
            try std.testing.expect(std.meta.activeTag(bool_type) == .bool);
        }
test "sanitize reserved words" {
    const allocator = std.testing.allocator;
    var compiler = Compiler.init(allocator);
    defer compiler.deinit();

    const sanitized = compiler.sanitizeIdent("return");
    defer allocator.free(sanitized);
    try std.testing.expectEqualStrings("@\"return\"", sanitized);

    const normal = compiler.sanitizeIdent("myFunction");
    defer allocator.free(normal);
    try std.testing.expectEqualStrings("myFunction", normal);
}
