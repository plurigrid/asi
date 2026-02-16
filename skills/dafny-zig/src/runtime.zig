const std = @import("std");
const Allocator = std.mem.Allocator;

/// Dafny Runtime Library for Zig
/// Provides collection types, big integers, and other Dafny primitives

// ============================================================================
// Big Integer
// ============================================================================

/// Arbitrary precision integer (Dafny's `int` type)
pub const BigInt = struct {
    allocator: Allocator,
    limbs: std.ArrayListUnmanaged(u64) = .{},
    negative: bool = false,

    pub fn init(allocator: Allocator) BigInt {
        return .{
            .allocator = allocator,
            .limbs = .{},
            .negative = false,
        };
    }

    pub fn fromInt(allocator: Allocator, value: i128) !BigInt {
        var result = init(allocator);
        result.negative = value < 0;
        const abs_val: u128 = if (value < 0) @intCast(-value) else @intCast(value);

        if (abs_val == 0) {
            try result.limbs.append(allocator, 0);
        } else {
            var v = abs_val;
            while (v > 0) {
                try result.limbs.append(allocator, @truncate(v));
                v >>= 64;
            }
        }
        return result;
    }

    pub fn deinit(self: *BigInt) void {
        self.limbs.deinit(self.allocator);
    }

    pub fn clone(self: BigInt) !BigInt {
        return .{
            .allocator = self.allocator,
            .limbs = try self.limbs.clone(self.allocator),
            .negative = self.negative,
        };
    }

    pub fn add(self: BigInt, other: BigInt) !BigInt {
        if (self.negative == other.negative) {
            return self.addMagnitudes(other, self.negative);
        } else {
            const cmp = self.compareMagnitude(other);
            if (cmp >= 0) {
                return self.subtractMagnitudes(other, self.negative);
            } else {
                return other.subtractMagnitudes(self, other.negative);
            }
        }
    }

    pub fn sub(self: BigInt, other: BigInt) !BigInt {
        var neg_other = try other.clone();
        neg_other.negative = !neg_other.negative;
        defer neg_other.deinit();
        return self.add(neg_other);
    }

    pub fn mul(self: BigInt, other: BigInt) !BigInt {
        const result_negative = self.negative != other.negative;
        var result = init(self.allocator);
        result.negative = result_negative;
        
        const len_a = self.limbs.items.len;
        const len_b = other.limbs.items.len;
        try result.limbs.resize(self.allocator, len_a + len_b);
        @memset(result.limbs.items, 0);

        for (self.limbs.items, 0..) |a, i| {
            var carry: u64 = 0;
            for (other.limbs.items, 0..) |b, j| {
                const product: u128 = @as(u128, a) * @as(u128, b) + @as(u128, result.limbs.items[i + j]) + @as(u128, carry);
                result.limbs.items[i + j] = @truncate(product);
                carry = @truncate(product >> 64);
            }
            if (carry != 0) {
                result.limbs.items[i + len_b] = carry;
            }
        }

        result.normalize();
        return result;
    }

    pub fn compare(self: BigInt, other: BigInt) i32 {
        if (self.negative != other.negative) {
            return if (self.negative) @as(i32, -1) else @as(i32, 1);
        }
        const mag_cmp = self.compareMagnitude(other);
        return if (self.negative) -mag_cmp else mag_cmp;
    }

    pub fn eql(self: BigInt, other: BigInt) bool {
        return self.compare(other) == 0;
    }

    fn compareMagnitude(self: BigInt, other: BigInt) i32 {
        const len_a = self.limbs.items.len;
        const len_b = other.limbs.items.len;
        if (len_a != len_b) {
            return if (len_a > len_b) @as(i32, 1) else @as(i32, -1);
        }
        var i: usize = len_a;
        while (i > 0) {
            i -= 1;
            const a = self.limbs.items[i];
            const b = other.limbs.items[i];
            if (a != b) {
                return if (a > b) @as(i32, 1) else @as(i32, -1);
            }
        }
        return 0;
    }

    fn addMagnitudes(self: BigInt, other: BigInt, negative: bool) !BigInt {
        var result = init(self.allocator);
        result.negative = negative;
        
        const len_a = self.limbs.items.len;
        const len_b = other.limbs.items.len;
        const max_len = @max(len_a, len_b);
        try result.limbs.ensureTotalCapacity(self.allocator, max_len + 1);

        var carry: u64 = 0;
        for (0..max_len) |i| {
            const a: u64 = if (i < len_a) self.limbs.items[i] else 0;
            const b: u64 = if (i < len_b) other.limbs.items[i] else 0;
            const sum: u128 = @as(u128, a) + @as(u128, b) + @as(u128, carry);
            result.limbs.appendAssumeCapacity(@truncate(sum));
            carry = @truncate(sum >> 64);
        }
        if (carry != 0) {
            result.limbs.appendAssumeCapacity(carry);
        }
        result.normalize();
        return result;
    }

    fn subtractMagnitudes(self: BigInt, other: BigInt, negative: bool) !BigInt {
        var result = init(self.allocator);
        result.negative = negative;
        
        const len_a = self.limbs.items.len;
        const len_b = other.limbs.items.len;
        try result.limbs.ensureTotalCapacity(self.allocator, len_a);

        var borrow: u64 = 0;
        for (0..len_a) |i| {
            const a = self.limbs.items[i];
            const b: u64 = if (i < len_b) other.limbs.items[i] else 0;
            const diff: i128 = @as(i128, a) - @as(i128, b) - @as(i128, borrow);
            if (diff < 0) {
                result.limbs.appendAssumeCapacity(@truncate(@as(u128, @bitCast(diff + (@as(i128, 1) << 64)))));
                borrow = 1;
            } else {
                result.limbs.appendAssumeCapacity(@truncate(@as(u128, @bitCast(diff))));
                borrow = 0;
            }
        }
        result.normalize();
        return result;
    }

    fn normalize(self: *BigInt) void {
        while (self.limbs.items.len > 1 and self.limbs.items[self.limbs.items.len - 1] == 0) {
            _ = self.limbs.pop();
        }
    }

    pub fn format(
        self: BigInt,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        if (self.negative) {
            try writer.writeByte('-');
        }
        if (self.limbs.items.len == 0) {
            try writer.writeByte('0');
            return;
        }
        var i: usize = self.limbs.items.len;
        while (i > 0) {
            i -= 1;
            try writer.print("{x}", .{self.limbs.items[i]});
        }
    }
};

// ============================================================================
// Big Rational
// ============================================================================

/// Arbitrary precision rational (Dafny's `real` type)
pub const BigRational = struct {
    numerator: BigInt,
    denominator: BigInt,

    pub fn init(allocator: Allocator) !BigRational {
        return .{
            .numerator = try BigInt.fromInt(allocator, 0),
            .denominator = try BigInt.fromInt(allocator, 1),
        };
    }

    pub fn fromInts(allocator: Allocator, num: i128, den: i128) !BigRational {
        return .{
            .numerator = try BigInt.fromInt(allocator, num),
            .denominator = try BigInt.fromInt(allocator, den),
        };
    }

    pub fn deinit(self: *BigRational) void {
        self.numerator.deinit();
        self.denominator.deinit();
    }

    pub fn add(self: BigRational, other: BigRational) !BigRational {
        // a/b + c/d = (ad + bc) / bd
        const ad = try self.numerator.mul(other.denominator);
        const bc = try other.numerator.mul(self.denominator);
        const numerator = try ad.add(bc);
        const denominator = try self.denominator.mul(other.denominator);
        return .{
            .numerator = numerator,
            .denominator = denominator,
        };
    }

    pub fn mul(self: BigRational, other: BigRational) !BigRational {
        return .{
            .numerator = try self.numerator.mul(other.numerator),
            .denominator = try self.denominator.mul(other.denominator),
        };
    }
};

// ============================================================================
// Reference Counting
// ============================================================================

/// Reference counted slice
pub fn RcSlice(comptime T: type) type {
    return struct {
        const Self = @This();

        items: []const T,
        count: *usize,
        allocator: Allocator,

        pub fn init(allocator: Allocator, items: []const T) !Self {
            const owned = try allocator.alloc(T, items.len);
            @memcpy(owned, items);
            const rc = try allocator.create(usize);
            rc.* = 1;
            return .{
                .items = owned,
                .count = rc,
                .allocator = allocator,
            };
        }

        pub fn retain(self: Self) Self {
            self.count.* += 1;
            return self;
        }

        pub fn release(self: *Self) void {
            self.count.* -= 1;
            if (self.count.* == 0) {
                self.allocator.free(@constCast(self.items));
                self.allocator.destroy(self.count);
            }
        }
    };
}

// ============================================================================
// Sequence
// ============================================================================

/// Immutable sequence type (Dafny's `seq<T>`)
pub fn Seq(comptime T: type) type {
    return struct {
        const Self = @This();

        rc: RcSlice(T),
        start: usize,
        len_val: usize,

        pub fn init(allocator: Allocator, items: []const T) !Self {
            const rc = try RcSlice(T).init(allocator, items);
            return .{
                .rc = rc,
                .start = 0,
                .len_val = items.len,
            };
        }

        pub fn empty(allocator: Allocator) !Self {
            return init(allocator, &[_]T{});
        }

        pub fn fromFn(allocator: Allocator, length: usize, f: *const fn (usize) T) !Self {
            const items = try allocator.alloc(T, length);
            for (0..length) |i| {
                items[i] = f(i);
            }
            const rc_count = try allocator.create(usize);
            rc_count.* = 1;
            const rc = RcSlice(T){
                .items = items,
                .count = rc_count,
                .allocator = allocator,
            };
            return .{
                .rc = rc,
                .start = 0,
                .len_val = length,
            };
        }

        pub fn deinit(self: *Self) void {
            self.rc.release();
        }

        pub fn clone(self: Self) Self {
            return .{
                .rc = self.rc.retain(),
                .start = self.start,
                .len_val = self.len_val,
            };
        }

        pub fn len(self: Self) usize {
            return self.len_val;
        }

        pub fn get(self: Self, index: usize) T {
            return self.rc.items[self.start + index];
        }

        pub fn set(self: Self, index: usize, value: T) !Self {
            // Copy-on-write
            var new_items = try self.rc.allocator.alloc(T, self.len_val);
            @memcpy(new_items, self.rc.items[self.start .. self.start + self.len_val]);
            new_items[index] = value;
            
            const rc = try RcSlice(T).init(self.rc.allocator, new_items);
            // Free temp buffer since init copied it
            self.rc.allocator.free(new_items);
            
            return .{
                .rc = rc,
                .start = 0,
                .len_val = self.len_val,
            };
        }

        pub fn concat(self: Self, other: Self) !Self {
            const new_len = self.len_val + other.len_val;
            var new_items = try self.rc.allocator.alloc(T, new_len);
            @memcpy(new_items[0..self.len_val], self.rc.items[self.start .. self.start + self.len_val]);
            @memcpy(new_items[self.len_val..], other.rc.items[other.start .. other.start + other.len_val]);
            
            const rc = try RcSlice(T).init(self.rc.allocator, new_items);
            self.rc.allocator.free(new_items);

            return .{
                .rc = rc,
                .start = 0,
                .len_val = new_len,
            };
        }

        pub fn slice(self: Self, start: usize, end: usize) !Self {
            return .{
                .rc = self.rc.retain(),
                .start = self.start + start,
                .len_val = end - start,
            };
        }

        pub fn contains(self: Self, value: T) bool {
            const slice_view = self.rc.items[self.start .. self.start + self.len_val];
            for (slice_view) |item| {
                if (std.meta.eql(item, value)) return true;
            }
            return false;
        }

        pub fn eql(self: Self, other: Self) bool {
            if (self.len_val != other.len_val) return false;
            const s1 = self.rc.items[self.start .. self.start + self.len_val];
            const s2 = other.rc.items[other.start .. other.start + other.len_val];
            for (s1, s2) |a, b| {
                if (!std.meta.eql(a, b)) return false;
            }
            return true;
        }

        pub fn iterator(self: Self) Iterator {
            return .{ .seq = self, .index = 0 };
        }

        pub const Iterator = struct {
            seq: Self,
            index: usize,

            pub fn next(self: *Iterator) ?T {
                if (self.index >= self.seq.len_val) return null;
                const item = self.seq.get(self.index);
                self.index += 1;
                return item;
            }
        };
    };
}

// ============================================================================
// Set
// ============================================================================

/// Immutable set type (Dafny's `set<T>`)
pub fn Set(comptime T: type) type {
    return struct {
        const Self = @This();

        allocator: Allocator,
        map: std.AutoHashMapUnmanaged(T, void) = .{},

        pub fn init(allocator: Allocator) Self {
            return .{
                .allocator = allocator,
                .map = .{},
            };
        }

        pub fn fromSlice(allocator: Allocator, items: []const T) !Self {
            var self = Self.init(allocator);
            for (items) |item| {
                try self.map.put(allocator, item, {});
            }
            return self;
        }

        pub fn deinit(self: *Self) void {
            self.map.deinit(self.allocator);
        }

        pub fn clone(self: Self) !Self {
            return .{
                .allocator = self.allocator,
                .map = try self.map.clone(self.allocator),
            };
        }

        pub fn len(self: Self) usize {
            return self.map.count();
        }

        pub fn contains(self: Self, value: T) bool {
            return self.map.contains(value);
        }

        pub fn add(self: Self, value: T) !Self {
            var result = try self.clone();
            try result.map.put(result.allocator, value, {});
            return result;
        }

        pub fn remove(self: Self, value: T) !Self {
            var result = try self.clone();
            _ = result.map.remove(value);
            return result;
        }

        pub fn setUnion(self: Self, other: Self) !Self {
            var result = try self.clone();
            var it = other.map.iterator();
            while (it.next()) |entry| {
                try result.map.put(result.allocator, entry.key_ptr.*, {});
            }
            return result;
        }

        pub fn intersect(self: Self, other: Self) !Self {
            var result = Self.init(self.allocator);
            var it = self.map.iterator();
            while (it.next()) |entry| {
                if (other.contains(entry.key_ptr.*)) {
                    try result.map.put(result.allocator, entry.key_ptr.*, {});
                }
            }
            return result;
        }

        pub fn difference(self: Self, other: Self) !Self {
            var result = Self.init(self.allocator);
            var it = self.map.iterator();
            while (it.next()) |entry| {
                if (!other.contains(entry.key_ptr.*)) {
                    try result.map.put(result.allocator, entry.key_ptr.*, {});
                }
            }
            return result;
        }

        pub fn isSubsetOf(self: Self, other: Self) bool {
            var it = self.map.iterator();
            while (it.next()) |entry| {
                if (!other.contains(entry.key_ptr.*)) {
                    return false;
                }
            }
            return true;
        }

        pub fn isProperSubsetOf(self: Self, other: Self) bool {
            return self.isSubsetOf(other) and self.len() < other.len();
        }

        pub fn eql(self: Self, other: Self) bool {
            if (self.len() != other.len()) return false;
            return self.isSubsetOf(other);
        }

        pub fn iterator(self: *const Self) Iterator {
            return .{ .inner = self.map.iterator() };
        }

        pub const Iterator = struct {
            inner: std.AutoHashMapUnmanaged(T, void).Iterator,

            pub fn next(self: *Iterator) ?T {
                if (self.inner.next()) |entry| {
                    return entry.key_ptr.*;
                }
                return null;
            }
        };
    };
}

// ============================================================================
// MultiSet
// ============================================================================

/// Multiset type (Dafny's `multiset<T>`)
pub fn MultiSet(comptime T: type) type {
    return struct {
        const Self = @This();

        allocator: Allocator,
        map: std.AutoHashMapUnmanaged(T, usize) = .{},

        pub fn init(allocator: Allocator) Self {
            return .{
                .allocator = allocator,
                .map = .{},
            };
        }

        pub fn fromSlice(allocator: Allocator, items: []const T) !Self {
            var self = Self.init(allocator);
            for (items) |item| {
                const current = self.map.get(item) orelse 0;
                try self.map.put(allocator, item, current + 1);
            }
            return self;
        }

        pub fn deinit(self: *Self) void {
            self.map.deinit(self.allocator);
        }

        pub fn count(self: Self, value: T) usize {
            return self.map.get(value) orelse 0;
        }

        pub fn contains(self: Self, value: T) bool {
            return self.count(value) > 0;
        }

        pub fn add(self: Self, value: T, n: usize) !Self {
            var result = Self.init(self.allocator);
            var it = self.map.iterator();
            while (it.next()) |entry| {
                try result.map.put(result.allocator, entry.key_ptr.*, entry.value_ptr.*);
            }
            const current = result.map.get(value) orelse 0;
            try result.map.put(result.allocator, value, current + n);
            return result;
        }

        pub fn remove(self: Self, value: T, n: usize) !Self {
            var result = Self.init(self.allocator);
            var it = self.map.iterator();
            while (it.next()) |entry| {
                try result.map.put(result.allocator, entry.key_ptr.*, entry.value_ptr.*);
            }
            const current = result.map.get(value) orelse 0;
            if (current <= n) {
                _ = result.map.remove(value);
            } else {
                try result.map.put(result.allocator, value, current - n);
            }
            return result;
        }

        pub fn cardinality(self: Self) usize {
            var total: usize = 0;
            var it = self.map.iterator();
            while (it.next()) |entry| {
                total += entry.value_ptr.*;
            }
            return total;
        }

        pub fn setUnion(self: Self, other: Self) !Self {
            var result = Self.init(self.allocator);
            var it = self.map.iterator();
            while (it.next()) |entry| {
                try result.map.put(result.allocator, entry.key_ptr.*, entry.value_ptr.*);
            }
            var other_it = other.map.iterator();
            while (other_it.next()) |entry| {
                const current = result.map.get(entry.key_ptr.*) orelse 0;
                try result.map.put(result.allocator, entry.key_ptr.*, current + entry.value_ptr.*);
            }
            return result;
        }

        pub fn intersect(self: Self, other: Self) !Self {
            var result = Self.init(self.allocator);
            var it = self.map.iterator();
            while (it.next()) |entry| {
                const other_count = other.count(entry.key_ptr.*);
                if (other_count > 0) {
                    try result.map.put(result.allocator, entry.key_ptr.*, @min(entry.value_ptr.*, other_count));
                }
            }
            return result;
        }
    };
}

// ============================================================================
// Map
// ============================================================================

/// Immutable map type (Dafny's `map<K, V>`)
pub fn Map(comptime K: type, comptime V: type) type {
    return struct {
        const Self = @This();

        allocator: Allocator,
        map: std.AutoHashMapUnmanaged(K, V) = .{},

        pub fn init(allocator: Allocator) Self {
            return .{
                .allocator = allocator,
                .map = .{},
            };
        }

        pub fn fromEntries(allocator: Allocator, entries: []const struct { key: K, value: V }) !Self {
            var self = Self.init(allocator);
            for (entries) |entry| {
                try self.map.put(allocator, entry.key, entry.value);
            }
            return self;
        }

        pub fn deinit(self: *Self) void {
            self.map.deinit(self.allocator);
        }

        pub fn clone(self: Self) !Self {
            return .{
                .allocator = self.allocator,
                .map = try self.map.clone(self.allocator),
            };
        }

        pub fn len(self: Self) usize {
            return self.map.count();
        }

        pub fn get(self: Self, key: K) ?V {
            return self.map.get(key);
        }

        pub fn contains(self: Self, key: K) bool {
            return self.map.contains(key);
        }

        pub fn put(self: Self, key: K, value: V) !Self {
            var result = try self.clone();
            try result.map.put(result.allocator, key, value);
            return result;
        }

        pub fn remove(self: Self, key: K) !Self {
            var result = try self.clone();
            _ = result.map.remove(key);
            return result;
        }

        pub fn keys(self: Self) !Set(K) {
            var result = Set(K).init(self.allocator);
            var it = self.map.iterator();
            while (it.next()) |entry| {
                try result.map.put(result.allocator, entry.key_ptr.*, {});
            }
            return result;
        }

        pub fn values(self: *const Self) ValueIterator {
            return .{ .inner = self.map.iterator() };
        }

        pub const ValueIterator = struct {
            inner: std.AutoHashMapUnmanaged(K, V).Iterator,

            pub fn next(self: *ValueIterator) ?V {
                if (self.inner.next()) |entry| {
                    return entry.value_ptr.*;
                }
                return null;
            }
        };

        pub fn eql(self: Self, other: Self) bool {
            if (self.len() != other.len()) return false;
            var it = self.map.iterator();
            while (it.next()) |entry| {
                const other_val = other.get(entry.key_ptr.*) orelse return false;
                if (!std.meta.eql(entry.value_ptr.*, other_val)) return false;
            }
            return true;
        }
    };
}

// ============================================================================
// Array Allocation
// ============================================================================

/// Allocate a multi-dimensional array
pub fn allocArray(comptime T: type, allocator: Allocator, dims: []const usize) ![]T {
    var total: usize = 1;
    for (dims) |dim| {
        total *= dim;
    }
    return try allocator.alloc(T, total);
}

/// Initialize array with function
pub fn initArray(comptime T: type, allocator: Allocator, len: usize, f: *const fn (usize) T) ![]T {
    const arr = try allocator.alloc(T, len);
    for (0..len) |i| {
        arr[i] = f(i);
    }
    return arr;
}

// ============================================================================
// Quantifiers
// ============================================================================

/// Check if predicate holds for all elements
pub fn all(comptime T: type, items: []const T, pred: *const fn (T) bool) bool {
    for (items) |item| {
        if (!pred(item)) return false;
    }
    return true;
}

/// Check if predicate holds for any element
pub fn any(comptime T: type, items: []const T, pred: *const fn (T) bool) bool {
    for (items) |item| {
        if (pred(item)) return true;
    }
    return false;
}

// ============================================================================
// Tuple Support
// ============================================================================

/// Create a tuple type
pub fn Tuple(comptime types: []const type) type {
    return std.meta.Tuple(types);
}

// ============================================================================
// String Operations
// ============================================================================

/// String type (alias for sequence of characters)
pub const DafnyString = Seq(u21);

/// Create string from slice
pub fn string(allocator: Allocator, s: []const u8) !DafnyString {
    var chars = std.ArrayList(u21).init(allocator);
    var utf8 = std.unicode.Utf8View.init(s) catch return error.InvalidUtf8;
    var iter = utf8.iterator();
    while (iter.nextCodepoint()) |cp| {
        try chars.append(cp);
    }
    return DafnyString.init(allocator, chars.items);
}

// ============================================================================
// Tests
// ============================================================================

test "BigInt basic operations" {
    const allocator = std.testing.allocator;

    var a = try BigInt.fromInt(allocator, 42);
    defer a.deinit();

    var b = try BigInt.fromInt(allocator, 8);
    defer b.deinit();

    var sum = try a.add(b);
    defer sum.deinit();

    var expected = try BigInt.fromInt(allocator, 50);
    defer expected.deinit();

    try std.testing.expect(sum.eql(expected));
}

test "Seq operations" {
    const allocator = std.testing.allocator;

    var seq1 = try Seq(i32).init(allocator, &[_]i32{ 1, 2, 3 });
    defer seq1.deinit();

    try std.testing.expectEqual(@as(usize, 3), seq1.len());
    try std.testing.expectEqual(@as(i32, 2), seq1.get(1));

    var seq2 = try Seq(i32).init(allocator, &[_]i32{ 4, 5 });
    defer seq2.deinit();

    var concat = try seq1.concat(seq2);
    defer concat.deinit();

    try std.testing.expectEqual(@as(usize, 5), concat.len());
}

test "Set operations" {
    const allocator = std.testing.allocator;

    var set1 = try Set(i32).fromSlice(allocator, &[_]i32{ 1, 2, 3 });
    defer set1.deinit();

    try std.testing.expect(set1.contains(2));
    try std.testing.expect(!set1.contains(4));

    var set2 = try Set(i32).fromSlice(allocator, &[_]i32{ 2, 3, 4 });
    defer set2.deinit();

    var inter = try set1.intersect(set2);
    defer inter.deinit();

    try std.testing.expectEqual(@as(usize, 2), inter.len());
    try std.testing.expect(inter.contains(2));
    try std.testing.expect(inter.contains(3));
}

test "Map operations" {
    const allocator = std.testing.allocator;

    var map1 = Map(i32, []const u8).init(allocator);
    defer map1.deinit();

    var map2 = try map1.put(1, "one");
    defer map2.deinit();

    var map3 = try map2.put(2, "two");
    defer map3.deinit();

    try std.testing.expectEqual(@as(usize, 2), map3.len());
    try std.testing.expectEqualStrings("one", map3.get(1).?);
}
