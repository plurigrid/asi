const std = @import("std");
const testing = std.testing;

/// Math utilities module demonstrating modular code organization

/// Add two numbers
pub fn add(a: i32, b: i32) i32 {
    return a + b;
}

/// Subtract two numbers
pub fn subtract(a: i32, b: i32) i32 {
    return a - b;
}

/// Multiply two numbers
pub fn multiply(a: i32, b: i32) i32 {
    return a * b;
}

/// Divide two numbers (returns error if division by zero)
pub fn divide(a: i32, b: i32) !i32 {
    if (b == 0) return error.DivisionByZero;
    return @divTrunc(a, b);
}

/// Calculate factorial recursively
pub fn factorial(n: u32) u64 {
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}

/// Check if a number is prime
pub fn isPrime(n: u32) bool {
    if (n < 2) return false;
    if (n == 2) return true;
    if (n % 2 == 0) return false;

    var i: u32 = 3;
    while (i * i <= n) : (i += 2) {
        if (n % i == 0) return false;
    }
    return true;
}

/// Calculate greatest common divisor using Euclidean algorithm
pub fn gcd(a: u32, b: u32) u32 {
    var x = a;
    var y = b;

    while (y != 0) {
        const temp = y;
        y = x % y;
        x = temp;
    }

    return x;
}

// Tests
test "basic arithmetic" {
    try testing.expectEqual(@as(i32, 5), add(2, 3));
    try testing.expectEqual(@as(i32, -1), subtract(2, 3));
    try testing.expectEqual(@as(i32, 6), multiply(2, 3));
    try testing.expectEqual(@as(i32, 2), try divide(6, 3));
}

test "divide by zero" {
    try testing.expectError(error.DivisionByZero, divide(10, 0));
}

test "factorial" {
    try testing.expectEqual(@as(u64, 1), factorial(0));
    try testing.expectEqual(@as(u64, 1), factorial(1));
    try testing.expectEqual(@as(u64, 2), factorial(2));
    try testing.expectEqual(@as(u64, 6), factorial(3));
    try testing.expectEqual(@as(u64, 24), factorial(4));
    try testing.expectEqual(@as(u64, 120), factorial(5));
}

test "prime numbers" {
    try testing.expect(!isPrime(0));
    try testing.expect(!isPrime(1));
    try testing.expect(isPrime(2));
    try testing.expect(isPrime(3));
    try testing.expect(!isPrime(4));
    try testing.expect(isPrime(5));
    try testing.expect(!isPrime(6));
    try testing.expect(isPrime(7));
    try testing.expect(!isPrime(8));
    try testing.expect(!isPrime(9));
    try testing.expect(isPrime(11));
}

test "greatest common divisor" {
    try testing.expectEqual(@as(u32, 6), gcd(12, 18));
    try testing.expectEqual(@as(u32, 1), gcd(17, 19));
    try testing.expectEqual(@as(u32, 5), gcd(15, 25));
    try testing.expectEqual(@as(u32, 12), gcd(12, 0));
}
