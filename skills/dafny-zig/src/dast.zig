//! DAST - Dafny Abstract Syntax Tree
//!
//! This module represents the compiled Dafny AST (DAST) that serves as the
//! intermediate representation between Dafny source and Zig code generation.
//!
//! The structure mirrors the official Dafny DAST specification from:
//! dafny/Source/DafnyCore/Backends/Dafny/AST.dfy
//!
//! Design principles (from Dafny):
//! - The Compiled Dafny AST should be minimal
//! - Generated code should look idiomatic and close to original Dafny

const std = @import("std");
const Allocator = std.mem.Allocator;

// ============================================================================
// NAMES AND IDENTIFIERS
// ============================================================================

/// A Dafny name (needs escaping in target language)
pub const Name = struct {
    dafny_name: []const u8,
    compile_name: ?[]const u8 = null,

    pub fn init(name: []const u8) Name {
        return .{ .dafny_name = name };
    }
};

/// Variable name (may need different escaping than type names)
pub const VarName = struct {
    dafny_name: []const u8,
    compile_name: ?[]const u8 = null,

    pub fn init(name: []const u8) VarName {
        return .{ .dafny_name = name };
    }
};

/// Identifier
pub const Ident = struct {
    id: []const u8,

    pub fn init(id: []const u8) Ident {
        return .{ .id = id };
    }
};

// ============================================================================
// ATTRIBUTES
// ============================================================================

/// Dafny attribute (e.g., {:extern}, {:axiom})
pub const Attribute = struct {
    name: []const u8,
    args: []const []const u8,

    pub fn init(name: []const u8, args: []const []const u8) Attribute {
        return .{ .name = name, .args = args };
    }
};

// ============================================================================
// MODULES
// ============================================================================

/// A Dafny module
pub const Module = struct {
    name: Name,
    doc_string: []const u8,
    attributes: []const Attribute,
    requires_externs: bool,
    body: ?[]const ModuleItem,

    pub fn init(
        name: Name,
        doc_string: []const u8,
        attributes: []const Attribute,
        requires_externs: bool,
        body: ?[]const ModuleItem,
    ) Module {
        return .{
            .name = name,
            .doc_string = doc_string,
            .attributes = attributes,
            .requires_externs = requires_externs,
            .body = body,
        };
    }
};

/// Items that can appear in a module
pub const ModuleItem = union(enum) {
    module: *const Module,
    class: *const Class,
    trait: *const Trait,
    newtype: *const Newtype,
    synonym_type: *const SynonymType,
    datatype: *const Datatype,

    pub fn getName(self: ModuleItem) Name {
        return switch (self) {
            .module => |m| m.name,
            .class => |c| c.name,
            .trait => |t| t.name,
            .newtype => |n| n.name,
            .synonym_type => |s| s.name,
            .datatype => |d| d.name,
        };
    }

    pub fn getAttributes(self: ModuleItem) []const Attribute {
        return switch (self) {
            .module => |m| m.attributes,
            .class => |c| c.attributes,
            .trait => |t| t.attributes,
            .newtype => |n| n.attributes,
            .synonym_type => |s| s.attributes,
            .datatype => |d| d.attributes,
        };
    }
};

// ============================================================================
// TYPES
// ============================================================================

/// Primitive types
pub const Primitive = enum {
    int,
    real,
    string,
    bool,
    char,
};

/// Trait type classification
pub const TraitType = enum {
    object_trait,
    general_trait,
};

/// Resolved type base kind
pub const ResolvedTypeBase = union(enum) {
    class: void,
    datatype: struct {
        variance: []const Variance,
        variances_are_known: bool,
    },
    trait: TraitType,
    newtype: struct {
        base_type: *const Type,
        range: NewtypeRange,
        erase: bool,
    },
};

/// Variance for type parameters
pub const Variance = enum {
    nonvariant,
    covariant,
    contravariant,
};

/// Range constraint for newtypes
pub const NewtypeRange = union(enum) {
    no_range: void,
    u8_range: void,
    u16_range: void,
    u32_range: void,
    u64_range: void,
    u128_range: void,
    i8_range: void,
    i16_range: void,
    i32_range: void,
    i64_range: void,
    i128_range: void,
    native_array_index: void,
    big_ordinal: void,
};

/// Resolved type with full path information
pub const ResolvedType = struct {
    path: []const Ident,
    type_args: []const Type,
    kind: ResolvedTypeBase,
    attributes: []const Attribute,
    property_fields: []const Ident,
    extended_types: []const Type,
};

/// Dafny type
pub const Type = union(enum) {
    user_defined: ResolvedType,
    tuple: []const Type,
    array: struct { element: *const Type, dims: usize },
    seq: *const Type,
    set: *const Type,
    multiset: *const Type,
    map: struct { key: *const Type, value: *const Type },
    set_builder: *const Type,
    map_builder: struct { key: *const Type, value: *const Type },
    arrow: struct { args: []const Type, result: *const Type },
    primitive: Primitive,
    passthrough: []const u8,
    type_arg: Ident,
    object: void,

    /// Check if this is a primitive int
    pub fn isPrimitiveInt(self: Type) bool {
        return switch (self) {
            .primitive => |p| p == .int,
            else => false,
        };
    }

    /// Check if this is a general trait
    pub fn isGeneralTrait(self: Type) bool {
        return switch (self) {
            .user_defined => |r| switch (r.kind) {
                .trait => |t| t == .general_trait,
                else => false,
            },
            else => false,
        };
    }
};

// ============================================================================
// TYPE PARAMETERS
// ============================================================================

/// Type parameter bound
pub const TypeArgBound = union(enum) {
    supports_equality: void,
    supports_default: void,
};

/// Type parameter declaration
pub const TypeArgDecl = struct {
    name: Ident,
    bounds: []const TypeArgBound,
    variance: Variance,
};

// ============================================================================
// CLASSES AND TRAITS
// ============================================================================

/// A Dafny class
pub const Class = struct {
    name: Name,
    enclosing_module: Ident,
    type_params: []const TypeArgDecl,
    super_classes: []const Type,
    fields: []const Field,
    body: []const ClassItem,
    attributes: []const Attribute,
};

/// A Dafny trait
pub const Trait = struct {
    name: Name,
    type_params: []const TypeArgDecl,
    trait_type: TraitType,
    parents: []const Type,
    body: []const ClassItem,
    attributes: []const Attribute,
};

/// Items that can appear in a class
pub const ClassItem = union(enum) {
    method: *const Method,
};

/// A field in a class or datatype
pub const Field = struct {
    formal: Formal,
    default_value: ?*const Expression,
};

/// A formal parameter
pub const Formal = struct {
    name: VarName,
    typ: Type,
    attributes: []const Attribute,
};

// ============================================================================
// DATATYPES AND NEWTYPES
// ============================================================================

/// A Dafny datatype
pub const Datatype = struct {
    name: Name,
    enclosing_module: Ident,
    type_params: []const TypeArgDecl,
    ctors: []const DatatypeCtor,
    body: []const ClassItem,
    is_co_datatype: bool,
    equality_support: EqualitySupport,
    attributes: []const Attribute,
};

/// Datatype constructor
pub const DatatypeCtor = struct {
    name: Name,
    args: []const DatatypeDtor,
    has_any_args: bool,
};

/// Datatype destructor (field accessor)
pub const DatatypeDtor = struct {
    formal: Formal,
    callable_name: ?Name,
};

/// Equality support level
pub const EqualitySupport = enum {
    never,
    cons_params,
};

/// A Dafny newtype
pub const Newtype = struct {
    name: Name,
    type_params: []const TypeArgDecl,
    base: Type,
    range: NewtypeRange,
    constraint: ?*const Expression,
    witness: ?Witness,
    attributes: []const Attribute,
};

/// Witness for a newtype
pub const Witness = struct {
    witness_expr: *const Expression,
    is_ghost: bool,
};

/// A type synonym
pub const SynonymType = struct {
    name: Name,
    type_params: []const TypeArgDecl,
    base: Type,
    witness: ?Witness,
    attributes: []const Attribute,
};

// ============================================================================
// METHODS AND FUNCTIONS
// ============================================================================

/// A Dafny method
pub const Method = struct {
    doc_string: []const u8,
    is_static: bool,
    has_body: bool,
    overriding_path: ?[]const Ident,
    name: Name,
    type_params: []const TypeArgDecl,
    params: []const Formal,
    body: []const Statement,
    out_types: []const Type,
    out_vars: ?[]const Ident,
    attributes: []const Attribute,
};

// ============================================================================
// STATEMENTS
// ============================================================================

/// Dafny statements
pub const Statement = union(enum) {
    decl_stmt: struct {
        name: VarName,
        typ: Type,
        value: ?*const Expression,
    },
    assign: struct {
        lhs: *const AssignLhs,
        value: *const Expression,
    },
    if_stmt: struct {
        cond: *const Expression,
        then_branch: []const Statement,
        else_branch: []const Statement,
    },
    labeled: struct {
        label: []const u8,
        body: []const Statement,
    },
    while_stmt: struct {
        cond: *const Expression,
        body: []const Statement,
    },
    foreach: struct {
        bound_name: VarName,
        bound_type: Type,
        over: *const Expression,
        body: []const Statement,
    },
    call: struct {
        on: ?*const Expression,
        call_name: CallName,
        type_args: []const Type,
        args: []const Expression,
        outs: ?[]const Ident,
    },
    return_stmt: ?*const Expression,
    early_return: void,
    break_stmt: ?[]const u8, // optional label
    tail_recursive: []const Statement,
    jump_tail_call_start: void,
    halt: void,
    print: *const Expression,
    construct_new_array: struct {
        dims: []const Expression,
        typ: Type,
    },
};

/// Left-hand side of an assignment
pub const AssignLhs = union(enum) {
    ident: Ident,
    select: struct {
        expr: *const Expression,
        field: VarName,
    },
    index: struct {
        expr: *const Expression,
        indices: []const Expression,
    },
};

/// Call name variants
pub const CallName = union(enum) {
    call_name: Name,
    map_builder_add: void,
    map_builder_build: void,
    set_builder_add: void,
    set_builder_build: void,
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
    and_op,
    or_op,
    implies,
    iff,
    // Bitwise
    bit_and,
    bit_or,
    bit_xor,
    bit_shl,
    bit_shr,
    // Set operations
    in_set,
    not_in_set,
    set_union,
    set_intersection,
    set_difference,
    subset,
    proper_subset,
    superset,
    proper_superset,
    disjoint,
    // Sequence operations
    seq_concat,
    seq_prefix,
    seq_proper_prefix,
    // Multiset operations
    multiset_union,
    multiset_intersection,
    multiset_difference,
    submultiset,
    proper_submultiset,
    supermultiset,
    proper_supermultiset,
    multiset_disjoint,
    // Map operations
    map_merge,
    map_subtraction,
    // Passthrough (target-language specific)
    passthrough,
};

/// Unary operators
pub const UnaryOp = enum {
    not,
    bitnot,
    cardinality,
};

/// Literal values
pub const Literal = union(enum) {
    bool_lit: bool,
    int_lit: []const u8, // arbitrary precision
    decimal_lit: struct { mantissa: []const u8, suffix: []const u8 },
    string_lit: []const u8,
    char_lit: u32, // Unicode codepoint
    char_lit_utf16: u16,
    null_lit: void,
};

/// Dafny expressions
pub const Expression = union(enum) {
    literal: Literal,
    ident: VarName,
    companion: []const Ident, // path to companion object
    extern_companion: []const Ident,
    tuple: []const Expression,
    new: struct {
        path: []const Ident,
        type_args: []const Type,
        args: []const Expression,
    },
    new_uninit_array: struct {
        dims: []const Expression,
        typ: Type,
    },
    array_index_to_int: *const Expression,
    final_bounded_pool: *const Expression,
    set_builder: struct {
        elem_type: Type,
        set_type: Type,
    },
    map_builder: struct {
        key_type: Type,
        value_type: Type,
    },
    seq_construct: struct {
        length: *const Expression,
        elem: *const Expression,
    },
    seq_value: struct {
        elements: []const Expression,
        typ: Type,
    },
    set_value: []const Expression,
    multiset_value: []const Expression,
    map_value: []const struct { key: Expression, value: Expression },
    this: void,
    ite: struct {
        cond: *const Expression,
        then_expr: *const Expression,
        else_expr: *const Expression,
    },
    un_op: struct {
        op: UnaryOp,
        expr: *const Expression,
    },
    bin_op: struct {
        op: BinOp,
        left: *const Expression,
        right: *const Expression,
    },
    array_len: struct {
        expr: *const Expression,
        dim: usize,
        native_length: bool,
    },
    map_keys: *const Expression,
    map_values: *const Expression,
    map_items: *const Expression,
    select: struct {
        expr: *const Expression,
        field: VarName,
        is_const: bool,
        on_datatype: bool,
        field_mutability: FieldMutability,
    },
    select_fn: struct {
        expr: *const Expression,
        field: VarName,
        on_datatype: bool,
        is_static: bool,
        is_const: bool,
        arity: usize,
    },
    index: struct {
        expr: *const Expression,
        coll_kind: CollKind,
        indices: []const Expression,
    },
    index_range: struct {
        expr: *const Expression,
        is_array: bool,
        lo: ?*const Expression,
        hi: ?*const Expression,
    },
    tuple_select: struct {
        expr: *const Expression,
        index: usize,
        field_type: Type,
    },
    call: struct {
        on: ?*const Expression,
        call_name: CallName,
        type_args: []const Type,
        args: []const Expression,
    },
    lambda: struct {
        params: []const Formal,
        ret_type: Type,
        body: []const Statement,
    },
    beta_redux: struct {
        values: []const struct { formal: Formal, value: Expression },
        ret_type: Type,
        expr: *const Expression,
    },
    iife: struct {
        ident: Ident,
        typ: Type,
        value: *const Expression,
        iife_body: *const Expression,
    },
    apply: struct {
        expr: *const Expression,
        args: []const Expression,
    },
    type_test: struct {
        on: *const Expression,
        dafny_type: []const Ident,
        variant: Name,
    },
    is: struct {
        expr: *const Expression,
        from_type: Type,
        to_type: Type,
    },
    init_of: struct {
        path: []const Ident,
        type_args: []const Type,
        args: []const Expression,
    },
    datatype_value: struct {
        path: []const Ident,
        type_args: []const Type,
        variant: Name,
        is_co_call: bool,
        contents: []const struct { key: VarName, value: Expression },
    },
    convert: struct {
        value: *const Expression,
        from: Type,
        to: Type,
    },
    seq_update: struct {
        expr: *const Expression,
        index_expr: *const Expression,
        value: *const Expression,
    },
    set_update: struct {
        expr: *const Expression,
        in_expr: *const Expression,
        value: bool,
    },
    map_update: struct {
        expr: *const Expression,
        index_expr: *const Expression,
        value: *const Expression,
    },
    multiset_update: struct {
        expr: *const Expression,
        in_expr: *const Expression,
        value: *const Expression,
    },
};

/// Collection kind for indexing
pub const CollKind = enum {
    seq,
    array,
    map,
};

/// Field mutability
pub const FieldMutability = enum {
    constant,
    in_internal_class,
    in_object_or_class,
};

// ============================================================================
// JSON PARSING (for reading DAST from Dafny compiler)
// ============================================================================

/// Parse a DAST Module from JSON
pub fn parseModuleJson(allocator: Allocator, json_str: []const u8) !Module {
    _ = allocator;
    _ = json_str;
    // TODO: Implement JSON parsing of DAST
    return Module.init(
        Name.init("placeholder"),
        "",
        &[_]Attribute{},
        false,
        null,
    );
}

// ============================================================================
// TESTS
// ============================================================================

test "name creation" {
    const name = Name.init("MyClass");
    try std.testing.expectEqualStrings("MyClass", name.dafny_name);
}

test "type primitives" {
    const int_type = Type{ .primitive = .int };
    try std.testing.expect(int_type.isPrimitiveInt());

    const bool_type = Type{ .primitive = .bool };
    try std.testing.expect(!bool_type.isPrimitiveInt());
}

test "module creation" {
    const mod = Module.init(
        Name.init("TestModule"),
        "A test module",
        &[_]Attribute{},
        false,
        null,
    );
    try std.testing.expectEqualStrings("TestModule", mod.name.dafny_name);
    try std.testing.expectEqualStrings("A test module", mod.doc_string);
}
