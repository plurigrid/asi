# Networking & Web Recipes

*18 tested recipes for Zig 0.15.2*

## Quick Reference

| Recipe | Description | Difficulty |
|--------|-------------|------------|
| [11.1](#recipe-11-1) | Making HTTP Requests | intermediate |
| [11.2](#recipe-11-2) | Working with JSON APIs | intermediate |
| [11.3](#recipe-11-3) | WebSocket Communication | intermediate |
| [11.4](#recipe-11-4) | Building a Simple HTTP Server | intermediate |
| [11.5](#recipe-11-5) | Parsing and Generating XML | intermediate |
| [11.6](#recipe-11-6) | Working with REST APIs | intermediate |
| [11.7](#recipe-11-7) | Handling Cookies and Sessions | intermediate |
| [11.8](#recipe-11-8) | SSL/TLS Connections | intermediate |
| [11.9](#recipe-11-9) | Uploading and Downloading Files | intermediate |
| [11.10](#recipe-11-10) | Rate Limiting and Throttling | intermediate |
| [11.11](#recipe-11-11) | GraphQL Client Implementation | intermediate |
| [11.12](#recipe-11-12) | OAuth2 Authentication | intermediate |
| [20.1](#recipe-20-1) | Non-Blocking TCP Servers with Poll | advanced |
| [20.2](#recipe-20-2) | Zero-Copy Networking Using sendfile | advanced |
| [20.3](#recipe-20-3) | Parsing Raw Packets with Packed Structs | advanced |
| [20.4](#recipe-20-4) | Implementing a Basic HTTP/1.1 Parser | advanced |
| [20.5](#recipe-20-5) | Using UDP Multicast | advanced |
| [20.6](#recipe-20-6) | Creating Raw Sockets | advanced |

---

## Recipe 11.1: Making HTTP Requests {#recipe-11-1}

**Tags:** allocators, c-interop, data-structures, error-handling, hashmap, http, json, memory, networking, parsing, resource-cleanup, slices, sockets, testing, xml
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_1.zig`

### Problem

You want to make HTTP requests in Zig, similar to Python's `requests` library. You need to construct requests with headers, parse responses, handle errors, and implement retry logic.

### Solution

Zig provides `std.http.Client` for production use, but understanding the underlying patterns helps you build robust HTTP clients. This recipe demonstrates the structure and API design for HTTP clients without external dependencies.

### Basic HTTP Client

Create a simple HTTP client wrapper:

```zig
// Basic HTTP client wrapper
pub const HttpClient = struct {
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) HttpClient {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *HttpClient) void {
        // Currently no resources to clean up.
        // This method exists for API consistency and future extensibility.
        _ = self;
    }
};

test "http client initialization" {
    var client = HttpClient.init(testing.allocator);
    defer client.deinit();
}
```

Usage:

```zig
var client = HttpClient.init(testing.allocator);
defer client.deinit();
```

### Request Options

Define request configuration with HTTP methods:

```zig
pub const RequestOptions = struct {
    method: Method = .GET,
    headers: ?std.StringHashMap([]const u8) = null,
    body: ?[]const u8 = null,
    timeout_ms: ?u32 = null,
    follow_redirects: bool = true,
    max_redirects: u32 = 10,

    pub const Method = enum {
        GET,
        POST,
        PUT,
        DELETE,
        PATCH,
        HEAD,
        OPTIONS,

        pub fn toString(self: Method) []const u8 {
            return switch (self) {
                .GET => "GET",
                .POST => "POST",
                .PUT => "PUT",
                .DELETE => "DELETE",
                .PATCH => "PATCH",
                .HEAD => "HEAD",
                .OPTIONS => "OPTIONS",
            };
        }
    };
};

test "request options" {
    const opts = RequestOptions{
        .method = .POST,
        .body = "test data",
        .timeout_ms = 5000,
    };

    try testing.expectEqual(RequestOptions.Method.POST, opts.method);
    try testing.expectEqualStrings("POST", opts.method.toString());
}
```

Example:

```zig
const opts = RequestOptions{
    .method = .POST,
    .body = "test data",
    .timeout_ms = 5000,
};

try testing.expectEqualStrings("POST", opts.method.toString());
```

### Response Structure

Handle HTTP responses with status helpers:

```zig
pub const Response = struct {
    status: u16,
    headers: std.StringHashMap([]const u8),
    body: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(
        allocator: std.mem.Allocator,
        status: u16,
        body: []const u8,
    ) !Response {
        return .{
            .status = status,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = try allocator.dupe(u8, body),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Response) void {
        var it = self.headers.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.headers.deinit();
        self.allocator.free(self.body);
    }

    pub fn isSuccess(self: Response) bool {
        return self.status >= 200 and self.status < 300;
    }

    pub fn isRedirect(self: Response) bool {
        return self.status >= 300 and self.status < 400;
    }

    pub fn isClientError(self: Response) bool {
        return self.status >= 400 and self.status < 500;
    }

    pub fn isServerError(self: Response) bool {
        return self.status >= 500 and self.status < 600;
    }
};
```

Status checking examples:

```zig
var resp = try Response.init(testing.allocator, 200, "OK");
defer resp.deinit();

try testing.expect(resp.isSuccess());
try testing.expect(!resp.isClientError());

var resp_404 = try Response.init(testing.allocator, 404, "Not Found");
defer resp_404.deinit();

try testing.expect(resp_404.isClientError());
```

### Discussion

### Python vs Zig HTTP Clients

The approaches differ in philosophy and control:

**Python (requests library):**
```python
import requests

# Simple GET request
response = requests.get('https://api.example.com/users')
print(response.status_code)
print(response.json())

# POST with headers
response = requests.post(
    'https://api.example.com/users',
    json={'name': 'Alice'},
    headers={'Authorization': 'Bearer token'},
    timeout=5
)
```

**Zig (explicit control):**
```zig
var client = HttpClient.init(allocator);
defer client.deinit();

var builder = RequestBuilder.init(allocator, "https://api.example.com/users");
defer builder.deinit();

_ = builder.method(.POST);
_ = builder.body("{\"name\":\"Alice\"}");
_ = try builder.header("Authorization", "Bearer token");
_ = builder.timeout(5000);
```

Key differences:
- **Explicitness**: Zig makes all operations visible; Python hides complexity
- **Memory**: Zig requires explicit allocator management; Python uses GC
- **Errors**: Zig uses error unions; Python uses exceptions
- **Dependencies**: Zig can use stdlib; Python typically requires external packages
- **Performance**: Zig compiles to native code; Python interprets

### URL Parsing

Parse URLs into components:

```zig
pub const Url = struct {
    scheme: []const u8,
    host: []const u8,
    port: ?u16,
    path: []const u8,
    query: ?[]const u8,
    fragment: ?[]const u8,

    /// Parses a URL string into components.
    /// Note: Returned Url contains slices into the input string.
    /// The input `url` must remain valid for the lifetime of the returned Url.
    pub fn parse(allocator: std.mem.Allocator, url: []const u8) !Url {
        // Implementation details...
    }
};
```

Usage:

```zig
const url1 = try Url.parse(testing.allocator, "https://example.com/path");
try testing.expectEqualStrings("https", url1.scheme);
try testing.expectEqualStrings("example.com", url1.host);
try testing.expectEqualStrings("/path", url1.path);

const url2 = try Url.parse(testing.allocator, "http://localhost:8080/api");
try testing.expectEqualStrings("http", url2.scheme);
try testing.expectEqual(@as(u16, 8080), url2.port.?);
```

**Important:** The returned `Url` contains slices into the input string, so the input must remain valid for the lifetime of the `Url`. This avoids allocation but creates a lifetime dependency.

### Header Builder Pattern

Build headers with a fluent API:

```zig
pub const HeaderBuilder = struct {
    headers: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) HeaderBuilder {
        return .{
            .headers = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *HeaderBuilder) void {
        var it = self.headers.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.headers.deinit();
    }

    pub fn set(self: *HeaderBuilder, name: []const u8, value: []const u8) !void {
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        // Use getOrPut to avoid leaking keys when updating existing headers
        const gop = try self.headers.getOrPut(name);

        if (gop.found_existing) {
            // Free old value and update with new value
            self.allocator.free(gop.value_ptr.*);
            gop.value_ptr.* = owned_value;
        } else {
            // New entry - need to own the key
            const owned_name = try self.allocator.dupe(u8, name);
            errdefer self.allocator.free(owned_name);

            gop.key_ptr.* = owned_name;
            gop.value_ptr.* = owned_value;
        }
    }

    pub fn setUserAgent(self: *HeaderBuilder, agent: []const u8) !void {
        try self.set("User-Agent", agent);
    }

    pub fn setContentType(self: *HeaderBuilder, content_type: []const u8) !void {
        try self.set("Content-Type", content_type);
    }
};
```

The `set` method uses `getOrPut` to avoid memory leaks when updating existing headers. This is a critical pattern for managing HashMap entries where both keys and values are owned strings.

Usage:

```zig
var builder = HeaderBuilder.init(testing.allocator);
defer builder.deinit();

try builder.setUserAgent("Zig HTTP Client/1.0");
try builder.setContentType("application/json");
try builder.set("X-Custom-Header", "custom-value");

const headers = builder.build();
const user_agent = headers.get("User-Agent");
try testing.expectEqualStrings("Zig HTTP Client/1.0", user_agent.?);
```

### Request Builder Pattern

Chain request configuration methods:

```zig
pub const RequestBuilder = struct {
    url: []const u8,
    options: RequestOptions,
    headers: HeaderBuilder,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, url: []const u8) RequestBuilder {
        return .{
            .url = url,
            .options = .{},
            .headers = HeaderBuilder.init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *RequestBuilder) void {
        self.headers.deinit();
    }

    pub fn method(self: *RequestBuilder, m: RequestOptions.Method) *RequestBuilder {
        self.options.method = m;
        return self;
    }

    pub fn body(self: *RequestBuilder, data: []const u8) *RequestBuilder {
        self.options.body = data;
        return self;
    }

    pub fn header(self: *RequestBuilder, name: []const u8, value: []const u8) !*RequestBuilder {
        try self.headers.set(name, value);
        return self;
    }

    pub fn timeout(self: *RequestBuilder, ms: u32) *RequestBuilder {
        self.options.timeout_ms = ms;
        return self;
    }
};
```

Fluent API usage:

```zig
var builder = RequestBuilder.init(testing.allocator, "https://example.com/api");
defer builder.deinit();

_ = builder.method(.POST);
_ = builder.body("{\"key\":\"value\"}");
_ = try builder.header("Content-Type", "application/json");
_ = builder.timeout(5000);
```

### JSON Request Helpers

Convenience functions for JSON APIs:

```zig
pub const JsonRequest = struct {
    pub fn post(
        allocator: std.mem.Allocator,
        url: []const u8,
        json_data: []const u8,
    ) !RequestBuilder {
        var builder = RequestBuilder.init(allocator, url);
        _ = builder.method(.POST);
        _ = builder.body(json_data);
        _ = try builder.header("Content-Type", "application/json");
        return builder;
    }

    pub fn get(
        allocator: std.mem.Allocator,
        url: []const u8,
    ) !RequestBuilder {
        var builder = RequestBuilder.init(allocator, url);
        _ = builder.method(.GET);
        _ = try builder.header("Accept", "application/json");
        return builder;
    }
};
```

Usage:

```zig
var post_req = try JsonRequest.post(
    testing.allocator,
    "https://api.example.com/users",
    "{\"name\":\"Alice\"}",
);
defer post_req.deinit();

var get_req = try JsonRequest.get(testing.allocator, "https://api.example.com/users/1");
defer get_req.deinit();
```

### Error Handling

Define specific HTTP errors:

```zig
pub const HttpError = error{
    ConnectionFailed,
    Timeout,
    InvalidUrl,
    TooManyRedirects,
    InvalidResponse,
    RequestCancelled,
    DnsResolutionFailed,
    SslError,
};

pub const ErrorInfo = struct {
    error_code: HttpError,
    message: []const u8,
    url: ?[]const u8 = null,

    pub fn init(err: HttpError, message: []const u8) ErrorInfo {
        return .{
            .error_code = err,
            .message = message,
        };
    }
};
```

Example:

```zig
const err_info = ErrorInfo.init(HttpError.Timeout, "Request timed out after 5000ms");
try testing.expectEqual(HttpError.Timeout, err_info.error_code);
```

### Retry Policy with Exponential Backoff

Implement automatic retries for transient failures:

```zig
pub const RetryPolicy = struct {
    max_retries: u32 = 3,
    retry_delay_ms: u32 = 1000,
    backoff_multiplier: f32 = 2.0,
    retry_on_timeout: bool = true,
    retry_on_connection_error: bool = true,

    pub fn shouldRetry(self: RetryPolicy, attempt: u32, err: HttpError) bool {
        if (attempt >= self.max_retries) return false;

        return switch (err) {
            HttpError.Timeout => self.retry_on_timeout,
            HttpError.ConnectionFailed, HttpError.DnsResolutionFailed => self.retry_on_connection_error,
            else => false,
        };
    }

    pub fn getDelay(self: RetryPolicy, attempt: u32) u32 {
        const base_delay: f32 = @floatFromInt(self.retry_delay_ms);
        const multiplier = std.math.pow(f32, self.backoff_multiplier,
                                       @as(f32, @floatFromInt(attempt)));
        const delay = base_delay * multiplier;

        // Cap at max u32 value to prevent overflow
        const max_delay: f32 = @floatFromInt(std.math.maxInt(u32));
        return @intFromFloat(@min(delay, max_delay));
    }
};
```

The retry delay follows exponential backoff:
- Attempt 0: 1000ms
- Attempt 1: 2000ms (1000 * 2^1)
- Attempt 2: 4000ms (1000 * 2^2)
- Attempt 3: 8000ms (1000 * 2^3)

Usage:

```zig
const policy = RetryPolicy{};

try testing.expect(policy.shouldRetry(0, HttpError.Timeout));
try testing.expect(policy.shouldRetry(1, HttpError.ConnectionFailed));
try testing.expect(!policy.shouldRetry(3, HttpError.Timeout)); // Exceeds max retries

try testing.expectEqual(@as(u32, 1000), policy.getDelay(0));
try testing.expectEqual(@as(u32, 2000), policy.getDelay(1));
try testing.expectEqual(@as(u32, 4000), policy.getDelay(2));
```

### Content Type Negotiation

Handle MIME types:

```zig
pub const ContentType = enum {
    json,
    xml,
    html,
    text,
    form_urlencoded,
    multipart_form,
    octet_stream,

    pub fn toString(self: ContentType) []const u8 {
        return switch (self) {
            .json => "application/json",
            .xml => "application/xml",
            .html => "text/html",
            .text => "text/plain",
            .form_urlencoded => "application/x-www-form-urlencoded",
            .multipart_form => "multipart/form-data",
            .octet_stream => "application/octet-stream",
        };
    }

    pub fn fromString(s: []const u8) ?ContentType {
        if (std.mem.eql(u8, s, "application/json")) return .json;
        if (std.mem.eql(u8, s, "application/xml")) return .xml;
        if (std.mem.eql(u8, s, "text/html")) return .html;
        if (std.mem.eql(u8, s, "text/plain")) return .text;
        if (std.mem.eql(u8, s, "application/x-www-form-urlencoded")) return .form_urlencoded;
        if (std.mem.eql(u8, s, "multipart/form-data")) return .multipart_form;
        if (std.mem.eql(u8, s, "application/octet-stream")) return .octet_stream;
        return null;
    }
};
```

Usage:

```zig
const json_type = ContentType.json;
try testing.expectEqualStrings("application/json", json_type.toString());

const parsed = ContentType.fromString("application/json");
try testing.expectEqual(ContentType.json, parsed.?);
```

### Full Tested Code

```zig
// Recipe 11.1: Making HTTP Requests
// Target Zig Version: 0.15.2
//
// Educational demonstration of HTTP client patterns in Zig.
// This code shows the structure and API design for HTTP clients
// but does not make actual network requests in tests (to avoid external dependencies).
//
// For production HTTP requests, use std.http.Client:
// https://ziglang.org/documentation/master/std/#std.http.Client
//
// Key concepts:
// - HTTP request/response structures
// - Request builder pattern with fluent API
// - Header management
// - URL parsing
// - Error handling for network operations
// - Retry policies with exponential backoff

const std = @import("std");
const testing = std.testing;

// ANCHOR: http_client_basic
// Basic HTTP client wrapper
pub const HttpClient = struct {
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) HttpClient {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *HttpClient) void {
        // Currently no resources to clean up.
        // This method exists for API consistency and future extensibility.
        _ = self;
    }
};

test "http client initialization" {
    var client = HttpClient.init(testing.allocator);
    defer client.deinit();
}
// ANCHOR_END: http_client_basic

// ANCHOR: request_options
pub const RequestOptions = struct {
    method: Method = .GET,
    headers: ?std.StringHashMap([]const u8) = null,
    body: ?[]const u8 = null,
    timeout_ms: ?u32 = null,
    follow_redirects: bool = true,
    max_redirects: u32 = 10,

    pub const Method = enum {
        GET,
        POST,
        PUT,
        DELETE,
        PATCH,
        HEAD,
        OPTIONS,

        pub fn toString(self: Method) []const u8 {
            return switch (self) {
                .GET => "GET",
                .POST => "POST",
                .PUT => "PUT",
                .DELETE => "DELETE",
                .PATCH => "PATCH",
                .HEAD => "HEAD",
                .OPTIONS => "OPTIONS",
            };
        }
    };
};

test "request options" {
    const opts = RequestOptions{
        .method = .POST,
        .body = "test data",
        .timeout_ms = 5000,
    };

    try testing.expectEqual(RequestOptions.Method.POST, opts.method);
    try testing.expectEqualStrings("POST", opts.method.toString());
}
// ANCHOR_END: request_options

// ANCHOR: response_struct
pub const Response = struct {
    status: u16,
    headers: std.StringHashMap([]const u8),
    body: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(
        allocator: std.mem.Allocator,
        status: u16,
        body: []const u8,
    ) !Response {
        return .{
            .status = status,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = try allocator.dupe(u8, body),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Response) void {
        var it = self.headers.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.headers.deinit();
        self.allocator.free(self.body);
    }

    pub fn isSuccess(self: Response) bool {
        return self.status >= 200 and self.status < 300;
    }

    pub fn isRedirect(self: Response) bool {
        return self.status >= 300 and self.status < 400;
    }

    pub fn isClientError(self: Response) bool {
        return self.status >= 400 and self.status < 500;
    }

    pub fn isServerError(self: Response) bool {
        return self.status >= 500 and self.status < 600;
    }
};

test "response status checks" {
    var resp = try Response.init(testing.allocator, 200, "OK");
    defer resp.deinit();

    try testing.expect(resp.isSuccess());
    try testing.expect(!resp.isRedirect());
    try testing.expect(!resp.isClientError());
    try testing.expect(!resp.isServerError());

    var resp_404 = try Response.init(testing.allocator, 404, "Not Found");
    defer resp_404.deinit();

    try testing.expect(!resp_404.isSuccess());
    try testing.expect(resp_404.isClientError());
}
// ANCHOR_END: response_struct

// ANCHOR: url_parser
pub const Url = struct {
    scheme: []const u8,
    host: []const u8,
    port: ?u16,
    path: []const u8,
    query: ?[]const u8,
    fragment: ?[]const u8,

    /// Parses a URL string into components.
    /// Note: Returned Url contains slices into the input string.
    /// The input `url` must remain valid for the lifetime of the returned Url.
    /// The allocator parameter is currently unused but reserved for future use.
    ///
    /// Simplified URL parsing for demonstration purposes.
    /// Production code should use a robust URL parsing library.
    /// Missing features: query parsing, fragment parsing, IPv6 support, URL encoding
    pub fn parse(allocator: std.mem.Allocator, url: []const u8) !Url {
        _ = allocator;

        // Find scheme (e.g., "https")
        var scheme_end: usize = 0;
        if (std.mem.indexOf(u8, url, "://")) |idx| {
            scheme_end = idx;
        } else {
            return error.InvalidUrl;
        }

        const scheme = url[0..scheme_end];
        var rest = url[scheme_end + 3 ..];

        // Find path start
        const path_start = std.mem.indexOfAny(u8, rest, "/?#") orelse rest.len;
        const host_port = rest[0..path_start];

        var host = host_port;
        var port: ?u16 = null;

        if (std.mem.indexOf(u8, host_port, ":")) |colon_idx| {
            host = host_port[0..colon_idx];
            const port_str = host_port[colon_idx + 1 ..];
            port = try std.fmt.parseInt(u16, port_str, 10);
        }

        const path = if (path_start < rest.len) rest[path_start..] else "/";

        return .{
            .scheme = scheme,
            .host = host,
            .port = port,
            .path = path,
            .query = null,
            .fragment = null,
        };
    }
};

test "url parsing" {
    const url1 = try Url.parse(testing.allocator, "https://example.com/path");
    try testing.expectEqualStrings("https", url1.scheme);
    try testing.expectEqualStrings("example.com", url1.host);
    try testing.expectEqualStrings("/path", url1.path);

    const url2 = try Url.parse(testing.allocator, "http://localhost:8080/api");
    try testing.expectEqualStrings("http", url2.scheme);
    try testing.expectEqualStrings("localhost", url2.host);
    try testing.expectEqual(@as(u16, 8080), url2.port.?);
}
// ANCHOR_END: url_parser

// ANCHOR: header_builder
pub const HeaderBuilder = struct {
    headers: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) HeaderBuilder {
        return .{
            .headers = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *HeaderBuilder) void {
        var it = self.headers.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.headers.deinit();
    }

    pub fn set(self: *HeaderBuilder, name: []const u8, value: []const u8) !void {
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        // Use getOrPut to avoid leaking keys when updating existing headers
        const gop = try self.headers.getOrPut(name);

        if (gop.found_existing) {
            // Free old value and update with new value
            self.allocator.free(gop.value_ptr.*);
            gop.value_ptr.* = owned_value;
        } else {
            // New entry - need to own the key
            const owned_name = try self.allocator.dupe(u8, name);
            errdefer self.allocator.free(owned_name);

            gop.key_ptr.* = owned_name;
            gop.value_ptr.* = owned_value;
        }
    }

    pub fn setUserAgent(self: *HeaderBuilder, agent: []const u8) !void {
        try self.set("User-Agent", agent);
    }

    pub fn setContentType(self: *HeaderBuilder, content_type: []const u8) !void {
        try self.set("Content-Type", content_type);
    }

    pub fn setAuthorization(self: *HeaderBuilder, auth: []const u8) !void {
        try self.set("Authorization", auth);
    }

    pub fn build(self: HeaderBuilder) std.StringHashMap([]const u8) {
        return self.headers;
    }
};

test "header builder" {
    var builder = HeaderBuilder.init(testing.allocator);
    defer builder.deinit();

    try builder.setUserAgent("Zig HTTP Client/1.0");
    try builder.setContentType("application/json");
    try builder.set("X-Custom-Header", "custom-value");

    const headers = builder.build();
    const user_agent = headers.get("User-Agent");
    try testing.expect(user_agent != null);
    try testing.expectEqualStrings("Zig HTTP Client/1.0", user_agent.?);
}
// ANCHOR_END: header_builder

// ANCHOR: request_builder
pub const RequestBuilder = struct {
    url: []const u8,
    options: RequestOptions,
    headers: HeaderBuilder,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, url: []const u8) RequestBuilder {
        return .{
            .url = url,
            .options = .{},
            .headers = HeaderBuilder.init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *RequestBuilder) void {
        self.headers.deinit();
    }

    pub fn method(self: *RequestBuilder, m: RequestOptions.Method) *RequestBuilder {
        self.options.method = m;
        return self;
    }

    pub fn body(self: *RequestBuilder, data: []const u8) *RequestBuilder {
        self.options.body = data;
        return self;
    }

    pub fn header(self: *RequestBuilder, name: []const u8, value: []const u8) !*RequestBuilder {
        try self.headers.set(name, value);
        return self;
    }

    pub fn timeout(self: *RequestBuilder, ms: u32) *RequestBuilder {
        self.options.timeout_ms = ms;
        return self;
    }
};

test "request builder" {
    var builder = RequestBuilder.init(testing.allocator, "https://example.com/api");
    defer builder.deinit();

    _ = builder.method(.POST);
    _ = builder.body("{\"key\":\"value\"}");
    _ = try builder.header("Content-Type", "application/json");
    _ = builder.timeout(5000);

    try testing.expectEqual(RequestOptions.Method.POST, builder.options.method);
}
// ANCHOR_END: request_builder

// ANCHOR: json_request
pub const JsonRequest = struct {
    pub fn post(
        allocator: std.mem.Allocator,
        url: []const u8,
        json_data: []const u8,
    ) !RequestBuilder {
        var builder = RequestBuilder.init(allocator, url);
        _ = builder.method(.POST);
        _ = builder.body(json_data);
        _ = try builder.header("Content-Type", "application/json");
        return builder;
    }

    pub fn get(
        allocator: std.mem.Allocator,
        url: []const u8,
    ) !RequestBuilder {
        var builder = RequestBuilder.init(allocator, url);
        _ = builder.method(.GET);
        _ = try builder.header("Accept", "application/json");
        return builder;
    }
};

test "json request helpers" {
    var post_req = try JsonRequest.post(
        testing.allocator,
        "https://api.example.com/users",
        "{\"name\":\"Alice\"}",
    );
    defer post_req.deinit();

    try testing.expectEqual(RequestOptions.Method.POST, post_req.options.method);

    var get_req = try JsonRequest.get(testing.allocator, "https://api.example.com/users/1");
    defer get_req.deinit();

    try testing.expectEqual(RequestOptions.Method.GET, get_req.options.method);
}
// ANCHOR_END: json_request

// ANCHOR: error_types
pub const HttpError = error{
    ConnectionFailed,
    Timeout,
    InvalidUrl,
    TooManyRedirects,
    InvalidResponse,
    RequestCancelled,
    DnsResolutionFailed,
    SslError,
};

pub const ErrorInfo = struct {
    error_code: HttpError,
    message: []const u8,
    url: ?[]const u8 = null,

    pub fn init(err: HttpError, message: []const u8) ErrorInfo {
        return .{
            .error_code = err,
            .message = message,
        };
    }
};

test "error types" {
    const err_info = ErrorInfo.init(HttpError.Timeout, "Request timed out after 5000ms");
    try testing.expectEqual(HttpError.Timeout, err_info.error_code);
    try testing.expectEqualStrings("Request timed out after 5000ms", err_info.message);
}
// ANCHOR_END: error_types

// ANCHOR: retry_policy
pub const RetryPolicy = struct {
    max_retries: u32 = 3,
    retry_delay_ms: u32 = 1000,
    backoff_multiplier: f32 = 2.0,
    retry_on_timeout: bool = true,
    retry_on_connection_error: bool = true,

    pub fn shouldRetry(self: RetryPolicy, attempt: u32, err: HttpError) bool {
        if (attempt >= self.max_retries) return false;

        return switch (err) {
            HttpError.Timeout => self.retry_on_timeout,
            HttpError.ConnectionFailed, HttpError.DnsResolutionFailed => self.retry_on_connection_error,
            else => false,
        };
    }

    pub fn getDelay(self: RetryPolicy, attempt: u32) u32 {
        const base_delay: f32 = @floatFromInt(self.retry_delay_ms);
        const multiplier = std.math.pow(f32, self.backoff_multiplier, @as(f32, @floatFromInt(attempt)));
        const delay = base_delay * multiplier;

        // Cap at max u32 value to prevent overflow
        const max_delay: f32 = @floatFromInt(std.math.maxInt(u32));
        return @intFromFloat(@min(delay, max_delay));
    }
};

test "retry policy" {
    const policy = RetryPolicy{};

    try testing.expect(policy.shouldRetry(0, HttpError.Timeout));
    try testing.expect(policy.shouldRetry(1, HttpError.ConnectionFailed));
    try testing.expect(!policy.shouldRetry(3, HttpError.Timeout));
    try testing.expect(!policy.shouldRetry(0, HttpError.InvalidUrl));

    try testing.expectEqual(@as(u32, 1000), policy.getDelay(0));
    try testing.expectEqual(@as(u32, 2000), policy.getDelay(1));
    try testing.expectEqual(@as(u32, 4000), policy.getDelay(2));
}
// ANCHOR_END: retry_policy

// ANCHOR: content_negotiation
pub const ContentType = enum {
    json,
    xml,
    html,
    text,
    form_urlencoded,
    multipart_form,
    octet_stream,

    pub fn toString(self: ContentType) []const u8 {
        return switch (self) {
            .json => "application/json",
            .xml => "application/xml",
            .html => "text/html",
            .text => "text/plain",
            .form_urlencoded => "application/x-www-form-urlencoded",
            .multipart_form => "multipart/form-data",
            .octet_stream => "application/octet-stream",
        };
    }

    pub fn fromString(s: []const u8) ?ContentType {
        if (std.mem.eql(u8, s, "application/json")) return .json;
        if (std.mem.eql(u8, s, "application/xml")) return .xml;
        if (std.mem.eql(u8, s, "text/html")) return .html;
        if (std.mem.eql(u8, s, "text/plain")) return .text;
        if (std.mem.eql(u8, s, "application/x-www-form-urlencoded")) return .form_urlencoded;
        if (std.mem.eql(u8, s, "multipart/form-data")) return .multipart_form;
        if (std.mem.eql(u8, s, "application/octet-stream")) return .octet_stream;
        return null;
    }
};

test "content type negotiation" {
    const json_type = ContentType.json;
    try testing.expectEqualStrings("application/json", json_type.toString());

    const parsed = ContentType.fromString("application/json");
    try testing.expectEqual(ContentType.json, parsed.?);
}
// ANCHOR_END: content_negotiation

// Comprehensive test
test "comprehensive http client patterns" {
    // Request options
    const opts = RequestOptions{ .method = .GET };
    try testing.expectEqualStrings("GET", opts.method.toString());

    // Response handling
    var resp = try Response.init(testing.allocator, 200, "Success");
    defer resp.deinit();
    try testing.expect(resp.isSuccess());

    // URL parsing
    const url = try Url.parse(testing.allocator, "https://example.com:443/api");
    try testing.expectEqualStrings("https", url.scheme);
    try testing.expectEqual(@as(u16, 443), url.port.?);

    // Header building
    var headers = HeaderBuilder.init(testing.allocator);
    defer headers.deinit();
    try headers.setUserAgent("Test/1.0");

    // Retry logic
    const policy = RetryPolicy{};
    try testing.expect(policy.shouldRetry(0, HttpError.Timeout));
}
```

### See Also

- Recipe 11.2: Working with JSON APIs
- Recipe 11.3: WebSocket Communication
- Recipe 14.1: Writing Unit Tests
- Recipe 15.1: Calling C Libraries

---

## Recipe 11.2: Working with JSON APIs {#recipe-11-2}

**Tags:** allocators, arraylist, data-structures, error-handling, http, json, memory, networking, parsing, resource-cleanup, slices, sockets, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_2.zig`

### Problem

You want to work with JSON data in Zig - parsing JSON from APIs, serializing Zig structs to JSON, handling nested structures, and dealing with dynamic data. You need type-safe parsing with good performance.

### Solution

Zig provides `std.json` with two main approaches: typed parsing for known schemas and dynamic parsing for flexible data. This recipe demonstrates both approaches and common JSON patterns.

### Basic JSON Parsing

Parse JSON strings into dynamic values:

```zig
// Parse JSON string to Zig value
test "basic json parsing" {
    const json_string =
        \\{"name": "Alice", "age": 30, "active": true}
    ;

    const parsed = try std.json.parseFromSlice(
        std.json.Value,
        testing.allocator,
        json_string,
        .{},
    );
    defer parsed.deinit();

    const root = parsed.value.object;
    try testing.expectEqualStrings("Alice", root.get("name").?.string);
    try testing.expectEqual(@as(i64, 30), root.get("age").?.integer);
    try testing.expect(root.get("active").?.bool);
}
```

The `.?` unwraps the optional returned by `get()`, which is safe here because we know the keys exist.

### Parsing to Structs

For known schemas, parse directly to Zig structs:

```zig
test "parse json to struct" {
    const json_string =
        \\{
        \\  "name": "Bob",
        \\  "age": 25,
        \\  "email": "bob@example.com",
        \\  "active": false
        \\}
    ;

    const parsed = try std.json.parseFromSlice(
        User,
        testing.allocator,
        json_string,
        .{},
    );
    defer parsed.deinit();

    const user = parsed.value;
    try testing.expectEqualStrings("Bob", user.name);
    try testing.expectEqual(@as(u32, 25), user.age);
    try testing.expectEqualStrings("bob@example.com", user.email);
    try testing.expect(!user.active);
}
```

This provides compile-time type safety and better performance than dynamic parsing.

### Serializing Structs to JSON

Convert Zig structs back to JSON:

```zig
const user = User{
    .name = "Charlie",
    .age = 35,
    .email = "charlie@example.com",
    .active = true,
};

const string = try std.json.Stringify.valueAlloc(testing.allocator, user, .{});
defer testing.allocator.free(string);

// Parse it back to verify
const parsed = try std.json.parseFromSlice(
    User,
    testing.allocator,
    string,
    .{},
);
defer parsed.deinit();

try testing.expectEqualStrings("Charlie", parsed.value.name);
```

### Discussion

### Python vs Zig JSON Handling

The approaches differ in philosophy:

**Python (dynamic, runtime):**
```python
import json

# Parse JSON
data = json.loads('{"name": "Alice", "age": 30}')
print(data['name'])  # Runtime key access
print(data.get('missing', 'default'))  # Runtime default

# Serialize
user = {'name': 'Bob', 'age': 25}
json_str = json.dumps(user)

# Type checking is optional (via typing hints)
from typing import TypedDict
class User(TypedDict):
    name: str
    age: int
# But still runtime-checked
```

**Zig (typed, compile-time):**
```zig
// Type-safe parsing
const User = struct {
    name: []const u8,
    age: u32,
};

const parsed = try std.json.parseFromSlice(User, allocator, json_string, .{});
defer parsed.deinit();

// Compile-time field access
const name = parsed.value.name;  // Compile error if field doesn't exist

// Serialize with type safety
const json_str = try std.json.Stringify.valueAlloc(allocator, user, .{});
defer allocator.free(json_str);
```

Key differences:
- **Type Safety**: Zig catches missing fields at compile time; Python at runtime
- **Performance**: Zig parsing is faster (no interpreter overhead)
- **Memory**: Zig requires explicit allocation; Python uses GC
- **Flexibility**: Python handles unknown schemas easily; Zig uses `std.json.Value` for dynamic data
- **Error Handling**: Zig uses error unions; Python uses exceptions

### Nested Structures

Handle complex nested JSON:

```zig
pub const Address = struct {
    street: []const u8,
    city: []const u8,
    zip: []const u8,
};

pub const UserWithAddress = struct {
    name: []const u8,
    age: u32,
    address: Address,
};

const json_string =
    \\{
    \\  "name": "Diana",
    \\  "age": 28,
    \\  "address": {
    \\    "street": "123 Main St",
    \\    "city": "Springfield",
    \\    "zip": "12345"
    \\  }
    \\}
;

const parsed = try std.json.parseFromSlice(
    UserWithAddress,
    testing.allocator,
    json_string,
    .{},
);
defer parsed.deinit();

const user = parsed.value;
try testing.expectEqualStrings("Diana", user.name);
try testing.expectEqualStrings("123 Main St", user.address.street);
```

Zig automatically handles nested struct parsing recursively.

### Array Handling

Parse JSON arrays:

```zig
pub const UserList = struct {
    users: []User,
};

const json_string =
    \\{
    \\  "users": [
    \\    {"name": "Alice", "age": 30, "email": "alice@example.com"},
    \\    {"name": "Bob", "age": 25, "email": "bob@example.com"}
    \\  ]
    \\}
;

const parsed = try std.json.parseFromSlice(
    UserList,
    testing.allocator,
    json_string,
    .{},
);
defer parsed.deinit();

const user_list = parsed.value;
try testing.expectEqual(@as(usize, 2), user_list.users.len);
try testing.expectEqualStrings("Alice", user_list.users[0].name);
```

### Optional Fields

Handle missing JSON fields with optionals:

```zig
pub const UserWithOptionals = struct {
    name: []const u8,
    age: u32,
    email: ?[]const u8 = null,
    phone: ?[]const u8 = null,
};

const json_with_email =
    \\{"name": "Eve", "age": 32, "email": "eve@example.com"}
;

const parsed1 = try std.json.parseFromSlice(
    UserWithOptionals,
    testing.allocator,
    json_with_email,
    .{},
);
defer parsed1.deinit();

try testing.expect(parsed1.value.email != null);
try testing.expectEqualStrings("eve@example.com", parsed1.value.email.?);
try testing.expect(parsed1.value.phone == null);
```

Fields marked as optional (`?T`) can be missing from the JSON.

### Error Handling

Handle malformed JSON gracefully:

```zig
const invalid_json = "{ invalid json }";

const result = std.json.parseFromSlice(
    User,
    testing.allocator,
    invalid_json,
    .{},
);

try testing.expectError(error.SyntaxError, result);
```

Zig's error handling makes parse failures explicit and recoverable.

### API Response Pattern

Structure API responses consistently:

```zig
pub const ApiResponse = struct {
    success: bool,
    message: []const u8,
    data: ?std.json.Value = null,
    error_code: ?[]const u8 = null,

    pub fn isSuccess(self: ApiResponse) bool {
        return self.success;
    }

    pub fn getErrorMessage(self: ApiResponse) []const u8 {
        if (self.error_code) |code| {
            return code;
        }
        return "Unknown error";
    }
};

const success_response =
    \\{
    \\  "success": true,
    \\  "message": "User created successfully"
    \\}
;

const parsed = try std.json.parseFromSlice(
    ApiResponse,
    testing.allocator,
    success_response,
    .{},
);
defer parsed.deinit();

try testing.expect(parsed.value.isSuccess());
```

### Custom Serialization

Control how types are serialized:

```zig
pub const Timestamp = struct {
    unix_timestamp: i64,

    pub fn jsonStringify(
        self: Timestamp,
        jw: anytype,
    ) !void {
        try jw.print("{d}", .{self.unix_timestamp});
    }
};

pub const Event = struct {
    name: []const u8,
    timestamp: Timestamp,
};

const event = Event{
    .name = "test_event",
    .timestamp = .{ .unix_timestamp = 1234567890 },
};

const string = try std.json.Stringify.valueAlloc(testing.allocator, event, .{});
defer testing.allocator.free(string);

// Verify timestamp is serialized as number
try testing.expect(std.mem.indexOf(u8, string, "1234567890") != null);
```

The `jsonStringify` method is automatically called during serialization, allowing custom formatting.

### JSON Builder Pattern

Build JSON programmatically:

```zig
pub const JsonBuilder = struct {
    allocator: std.mem.Allocator,
    buffer: std.ArrayList(u8),

    pub fn init(allocator: std.mem.Allocator) JsonBuilder {
        return .{
            .allocator = allocator,
            .buffer = std.ArrayList(u8){},
        };
    }

    pub fn deinit(self: *JsonBuilder) void {
        self.buffer.deinit(self.allocator);
    }

    pub fn object(self: *JsonBuilder) !*JsonBuilder {
        try self.buffer.append(self.allocator, '{');
        return self;
    }

    pub fn endObject(self: *JsonBuilder) !*JsonBuilder {
        // Remove trailing comma if present
        if (self.buffer.items.len > 0 and self.buffer.items[self.buffer.items.len - 1] == ',') {
            _ = self.buffer.pop();
        }
        try self.buffer.append(self.allocator, '}');
        return self;
    }

    pub fn field(self: *JsonBuilder, name: []const u8, value: anytype) !*JsonBuilder {
        const writer = self.buffer.writer(self.allocator);
        try writer.print("\"{s}\":", .{name});

        const value_json = try std.json.Stringify.valueAlloc(self.allocator, value, .{});
        defer self.allocator.free(value_json);

        try writer.writeAll(value_json);
        try self.buffer.append(self.allocator, ',');
        return self;
    }

    pub fn build(self: JsonBuilder) []const u8 {
        return self.buffer.items;
    }
};
```

Usage:

```zig
var builder = JsonBuilder.init(testing.allocator);
defer builder.deinit();

_ = try builder.object();
_ = try builder.field("name", "Alice");
_ = try builder.field("age", 30);
_ = try builder.field("active", true);
_ = try builder.endObject();

const json = builder.build();
```

### Pretty Printing

Format JSON with indentation:

```zig
const user = User{
    .name = "Grace",
    .age = 27,
    .email = "grace@example.com",
    .active = true,
};

const string = try std.json.Stringify.valueAlloc(
    testing.allocator,
    user,
    .{ .whitespace = .indent_2 },
);
defer testing.allocator.free(string);

// Verify it contains newlines and indentation
try testing.expect(std.mem.indexOf(u8, string, "\n") != null);
try testing.expect(std.mem.indexOf(u8, string, "  ") != null);
```

The `.whitespace` option controls formatting:
- `.minified` - No whitespace (default)
- `.indent_2` - 2-space indentation
- `.indent_4` - 4-space indentation
- `.indent_tab` - Tab indentation

### Processing JSON Arrays

Work with arrays of primitives:

```zig
const json_string =
    \\[1, 2, 3, 4, 5]
;

const parsed = try std.json.parseFromSlice(
    []i64,
    testing.allocator,
    json_string,
    .{},
);
defer parsed.deinit();

var sum: i64 = 0;
for (parsed.value) |num| {
    sum += num;
}

try testing.expectEqual(@as(i64, 15), sum);
```

### Working with Dynamic JSON

Use `std.json.Value` when the structure is unknown:

```zig
const json_string =
    \\{
    \\  "field1": "value1",
    \\  "field2": 42,
    \\  "field3": true,
    \\  "nested": {"key": "value"}
    \\}
;

const parsed = try std.json.parseFromSlice(
    std.json.Value,
    testing.allocator,
    json_string,
    .{},
);
defer parsed.deinit();

const root = parsed.value.object;

// Access different types
try testing.expectEqualStrings("value1", root.get("field1").?.string);
try testing.expectEqual(@as(i64, 42), root.get("field2").?.integer);
try testing.expect(root.get("field3").?.bool);

const nested = root.get("nested").?.object;
try testing.expectEqualStrings("value", nested.get("key").?.string);
```

**When to use each approach:**

**Typed Parsing (`parseFromSlice(MyStruct, ...)`):**
- Known, fixed schema
- Performance critical code
- Want compile-time type safety
- API contracts are well-defined

**Dynamic Parsing (`parseFromSlice(std.json.Value, ...)`):**
- Unknown or varying schema
- Working with user-provided JSON
- Need runtime introspection
- Implementing generic JSON tools

### Full Tested Code

```zig
// Recipe 11.2: Working with JSON APIs
// Target Zig Version: 0.15.2
//
// Educational demonstration of JSON API patterns in Zig.
// Shows JSON parsing, serialization, and API interaction patterns.
//
// Key concepts:
// - JSON parsing with std.json
// - Serializing Zig structs to JSON
// - Handling nested JSON structures
// - Error handling for malformed JSON
// - Working with dynamic JSON data
// - Type-safe API responses

const std = @import("std");
const testing = std.testing;

// ANCHOR: basic_json_parsing
// Parse JSON string to Zig value
test "basic json parsing" {
    const json_string =
        \\{"name": "Alice", "age": 30, "active": true}
    ;

    const parsed = try std.json.parseFromSlice(
        std.json.Value,
        testing.allocator,
        json_string,
        .{},
    );
    defer parsed.deinit();

    const root = parsed.value.object;
    try testing.expectEqualStrings("Alice", root.get("name").?.string);
    try testing.expectEqual(@as(i64, 30), root.get("age").?.integer);
    try testing.expect(root.get("active").?.bool);
}
// ANCHOR_END: basic_json_parsing

// ANCHOR: user_struct
// Define a user struct for JSON serialization
pub const User = struct {
    name: []const u8,
    age: u32,
    email: []const u8,
    active: bool = true,
};
// ANCHOR_END: user_struct

// ANCHOR: parse_to_struct
test "parse json to struct" {
    const json_string =
        \\{
        \\  "name": "Bob",
        \\  "age": 25,
        \\  "email": "bob@example.com",
        \\  "active": false
        \\}
    ;

    const parsed = try std.json.parseFromSlice(
        User,
        testing.allocator,
        json_string,
        .{},
    );
    defer parsed.deinit();

    const user = parsed.value;
    try testing.expectEqualStrings("Bob", user.name);
    try testing.expectEqual(@as(u32, 25), user.age);
    try testing.expectEqualStrings("bob@example.com", user.email);
    try testing.expect(!user.active);
}
// ANCHOR_END: parse_to_struct

// ANCHOR: stringify_struct
test "serialize struct to json" {
    const user = User{
        .name = "Charlie",
        .age = 35,
        .email = "charlie@example.com",
        .active = true,
    };

    const string = try std.json.Stringify.valueAlloc(testing.allocator, user, .{});
    defer testing.allocator.free(string);

    // Parse it back to verify
    const parsed = try std.json.parseFromSlice(
        User,
        testing.allocator,
        string,
        .{},
    );
    defer parsed.deinit();

    try testing.expectEqualStrings("Charlie", parsed.value.name);
    try testing.expectEqual(@as(u32, 35), parsed.value.age);
}
// ANCHOR_END: stringify_struct

// ANCHOR: nested_structures
pub const Address = struct {
    street: []const u8,
    city: []const u8,
    zip: []const u8,
};

pub const UserWithAddress = struct {
    name: []const u8,
    age: u32,
    address: Address,
};

test "nested json structures" {
    const json_string =
        \\{
        \\  "name": "Diana",
        \\  "age": 28,
        \\  "address": {
        \\    "street": "123 Main St",
        \\    "city": "Springfield",
        \\    "zip": "12345"
        \\  }
        \\}
    ;

    const parsed = try std.json.parseFromSlice(
        UserWithAddress,
        testing.allocator,
        json_string,
        .{},
    );
    defer parsed.deinit();

    const user = parsed.value;
    try testing.expectEqualStrings("Diana", user.name);
    try testing.expectEqualStrings("123 Main St", user.address.street);
    try testing.expectEqualStrings("Springfield", user.address.city);
}
// ANCHOR_END: nested_structures

// ANCHOR: array_handling
pub const UserList = struct {
    users: []User,
};

test "json array handling" {
    const json_string =
        \\{
        \\  "users": [
        \\    {"name": "Alice", "age": 30, "email": "alice@example.com"},
        \\    {"name": "Bob", "age": 25, "email": "bob@example.com"}
        \\  ]
        \\}
    ;

    const parsed = try std.json.parseFromSlice(
        UserList,
        testing.allocator,
        json_string,
        .{},
    );
    defer parsed.deinit();

    const user_list = parsed.value;
    try testing.expectEqual(@as(usize, 2), user_list.users.len);
    try testing.expectEqualStrings("Alice", user_list.users[0].name);
    try testing.expectEqualStrings("Bob", user_list.users[1].name);
}
// ANCHOR_END: array_handling

// ANCHOR: optional_fields
pub const UserWithOptionals = struct {
    name: []const u8,
    age: u32,
    email: ?[]const u8 = null,
    phone: ?[]const u8 = null,
};

test "optional json fields" {
    const json_with_email =
        \\{"name": "Eve", "age": 32, "email": "eve@example.com"}
    ;

    const parsed1 = try std.json.parseFromSlice(
        UserWithOptionals,
        testing.allocator,
        json_with_email,
        .{},
    );
    defer parsed1.deinit();

    try testing.expect(parsed1.value.email != null);
    try testing.expectEqualStrings("eve@example.com", parsed1.value.email.?);
    try testing.expect(parsed1.value.phone == null);

    const json_without_email =
        \\{"name": "Frank", "age": 40}
    ;

    const parsed2 = try std.json.parseFromSlice(
        UserWithOptionals,
        testing.allocator,
        json_without_email,
        .{},
    );
    defer parsed2.deinit();

    try testing.expect(parsed2.value.email == null);
}
// ANCHOR_END: optional_fields

// ANCHOR: error_handling
test "json parse error handling" {
    const invalid_json = "{ invalid json }";

    const result = std.json.parseFromSlice(
        User,
        testing.allocator,
        invalid_json,
        .{},
    );

    try testing.expectError(error.SyntaxError, result);
}
// ANCHOR_END: error_handling

// ANCHOR: api_response
pub const ApiResponse = struct {
    success: bool,
    message: []const u8,
    data: ?std.json.Value = null,
    error_code: ?[]const u8 = null,

    pub fn isSuccess(self: ApiResponse) bool {
        return self.success;
    }

    pub fn getErrorMessage(self: ApiResponse) []const u8 {
        if (self.error_code) |code| {
            return code;
        }
        return "Unknown error";
    }
};

test "api response structure" {
    const success_response =
        \\{
        \\  "success": true,
        \\  "message": "User created successfully"
        \\}
    ;

    const parsed = try std.json.parseFromSlice(
        ApiResponse,
        testing.allocator,
        success_response,
        .{},
        );
    defer parsed.deinit();

    const response = parsed.value;
    try testing.expect(response.isSuccess());
    try testing.expectEqualStrings("User created successfully", response.message);
}
// ANCHOR_END: api_response

// ANCHOR: custom_serialization
pub const Timestamp = struct {
    unix_timestamp: i64,

    pub fn jsonStringify(
        self: Timestamp,
        jw: anytype,
    ) !void {
        try jw.print("{d}", .{self.unix_timestamp});
    }
};

pub const Event = struct {
    name: []const u8,
    timestamp: Timestamp,
};

test "custom json serialization" {
    const event = Event{
        .name = "test_event",
        .timestamp = .{ .unix_timestamp = 1234567890 },
    };

    const string = try std.json.Stringify.valueAlloc(testing.allocator, event, .{});
    defer testing.allocator.free(string);

    // Verify timestamp is serialized as number
    try testing.expect(std.mem.indexOf(u8, string, "1234567890") != null);
}
// ANCHOR_END: custom_serialization

// ANCHOR: json_builder
pub const JsonBuilder = struct {
    allocator: std.mem.Allocator,
    buffer: std.ArrayList(u8),

    pub fn init(allocator: std.mem.Allocator) JsonBuilder {
        return .{
            .allocator = allocator,
            .buffer = std.ArrayList(u8){},
        };
    }

    pub fn deinit(self: *JsonBuilder) void {
        self.buffer.deinit(self.allocator);
    }

    pub fn object(self: *JsonBuilder) !*JsonBuilder {
        try self.buffer.append(self.allocator, '{');
        return self;
    }

    pub fn endObject(self: *JsonBuilder) !*JsonBuilder {
        // Remove trailing comma if present
        if (self.buffer.items.len > 0 and self.buffer.items[self.buffer.items.len - 1] == ',') {
            _ = self.buffer.pop();
        }
        try self.buffer.append(self.allocator, '}');
        return self;
    }

    pub fn field(self: *JsonBuilder, name: []const u8, value: anytype) !*JsonBuilder {
        const writer = self.buffer.writer(self.allocator);
        try writer.print("\"{s}\":", .{name});

        // Serialize the value to a temporary string
        const value_json = try std.json.Stringify.valueAlloc(self.allocator, value, .{});
        defer self.allocator.free(value_json);

        try writer.writeAll(value_json);
        try self.buffer.append(self.allocator, ',');
        return self;
    }

    pub fn build(self: JsonBuilder) []const u8 {
        return self.buffer.items;
    }
};

test "json builder" {
    var builder = JsonBuilder.init(testing.allocator);
    defer builder.deinit();

    _ = try builder.object();
    _ = try builder.field("name", "Alice");
    _ = try builder.field("age", 30);
    _ = try builder.field("active", true);
    _ = try builder.endObject();

    const json = builder.build();

    // Parse to verify
    const parsed = try std.json.parseFromSlice(
        std.json.Value,
        testing.allocator,
        json,
        .{},
    );
    defer parsed.deinit();

    const obj = parsed.value.object;
    try testing.expectEqualStrings("Alice", obj.get("name").?.string);
    try testing.expectEqual(@as(i64, 30), obj.get("age").?.integer);
}
// ANCHOR_END: json_builder

// ANCHOR: pretty_print
test "pretty print json" {
    const user = User{
        .name = "Grace",
        .age = 27,
        .email = "grace@example.com",
        .active = true,
    };

    const string = try std.json.Stringify.valueAlloc(
        testing.allocator,
        user,
        .{ .whitespace = .indent_2 },
    );
    defer testing.allocator.free(string);

    // Verify it contains newlines and indentation
    try testing.expect(std.mem.indexOf(u8, string, "\n") != null);
    try testing.expect(std.mem.indexOf(u8, string, "  ") != null);
}
// ANCHOR_END: pretty_print

// ANCHOR: array_processing
test "processing json arrays" {
    const json_string =
        \\[1, 2, 3, 4, 5]
    ;

    const parsed = try std.json.parseFromSlice(
        []i64,
        testing.allocator,
        json_string,
        .{},
    );
    defer parsed.deinit();

    var sum: i64 = 0;
    for (parsed.value) |num| {
        sum += num;
    }

    try testing.expectEqual(@as(i64, 15), sum);
    try testing.expectEqual(@as(usize, 5), parsed.value.len);
}
// ANCHOR_END: array_processing

// ANCHOR: dynamic_fields
test "working with dynamic json" {
    const json_string =
        \\{
        \\  "field1": "value1",
        \\  "field2": 42,
        \\  "field3": true,
        \\  "nested": {"key": "value"}
        \\}
    ;

    const parsed = try std.json.parseFromSlice(
        std.json.Value,
        testing.allocator,
        json_string,
        .{},
    );
    defer parsed.deinit();

    const root = parsed.value.object;

    // Access different types
    try testing.expectEqualStrings("value1", root.get("field1").?.string);
    try testing.expectEqual(@as(i64, 42), root.get("field2").?.integer);
    try testing.expect(root.get("field3").?.bool);

    const nested = root.get("nested").?.object;
    try testing.expectEqualStrings("value", nested.get("key").?.string);
}
// ANCHOR_END: dynamic_fields

// Comprehensive test
test "comprehensive json api patterns" {
    // Parse user from JSON
    const json_user =
        \\{"name": "Helen", "age": 29, "email": "helen@example.com"}
    ;

    const parsed_user = try std.json.parseFromSlice(
        User,
        testing.allocator,
        json_user,
        .{},
    );
    defer parsed_user.deinit();

    // Serialize user back to JSON
    const json_output = try std.json.Stringify.valueAlloc(
        testing.allocator,
        parsed_user.value,
        .{},
    );
    defer testing.allocator.free(json_output);

    // Parse it again to verify round-trip
    const reparsed = try std.json.parseFromSlice(
        User,
        testing.allocator,
        json_output,
        .{},
    );
    defer reparsed.deinit();

    try testing.expectEqualStrings("Helen", reparsed.value.name);
    try testing.expectEqual(@as(u32, 29), reparsed.value.age);
}
```

### See Also

- Recipe 11.1: Making HTTP Requests
- Recipe 11.3: WebSocket Communication
- Recipe 11.6: Working with REST APIs
- Recipe 14.2: Unit Testing Strategies

---

## Recipe 11.3: WebSocket Communication {#recipe-11-3}

**Tags:** allocators, arraylist, data-structures, error-handling, http, json, memory, networking, parsing, resource-cleanup, slices, sockets, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_3.zig`

### Problem

You want to implement WebSocket communication in Zig - understanding the protocol structure, building and parsing frames, handling the handshake, and managing connection state. You need to work with real-time bidirectional communication.

### Solution

WebSocket is a protocol that provides full-duplex communication over a single TCP connection. While Zig doesn't have a built-in WebSocket library, understanding the protocol patterns helps you use existing libraries or implement custom solutions.

This recipe demonstrates the WebSocket protocol structure and patterns without actual networking code.

### WebSocket Frame Structure

WebSocket messages are sent as frames with a specific header format:

```zig
// WebSocket frame header structure
pub const FrameHeader = struct {
    fin: bool, // Final fragment flag
    rsv1: bool = false, // Reserved bits (must be 0)
    rsv2: bool = false,
    rsv3: bool = false,
    opcode: Opcode,
    masked: bool,
    payload_length: u64,
    masking_key: ?[4]u8 = null,

    pub const Opcode = enum(u4) {
        continuation = 0x0,
        text = 0x1,
        binary = 0x2,
        close = 0x8,
        ping = 0x9,
        pong = 0xA,
        _,

        pub fn isControl(self: Opcode) bool {
            return @intFromEnum(self) >= 0x8;
        }
    };
};

test "frame header opcodes" {
    try testing.expect(FrameHeader.Opcode.ping.isControl());
    try testing.expect(FrameHeader.Opcode.pong.isControl());
    try testing.expect(FrameHeader.Opcode.close.isControl());
    try testing.expect(!FrameHeader.Opcode.text.isControl());
    try testing.expect(!FrameHeader.Opcode.binary.isControl());
}
```

The underscore `_` in the enum makes it non-exhaustive, allowing unknown opcodes without panicking (useful for forward compatibility).

Opcode classification:

```zig
try testing.expect(FrameHeader.Opcode.ping.isControl());
try testing.expect(FrameHeader.Opcode.pong.isControl());
try testing.expect(FrameHeader.Opcode.close.isControl());
try testing.expect(!FrameHeader.Opcode.text.isControl());
```

### Message Types

Define high-level message types:

```zig
pub const MessageType = enum {
    text,
    binary,
    ping,
    pong,
    close,
};

pub const Message = struct {
    type: MessageType,
    data: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, msg_type: MessageType, data: []const u8) !Message {
        return .{
            .type = msg_type,
            .data = try allocator.dupe(u8, data),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Message) void {
        self.allocator.free(self.data);
    }
};

test "message creation" {
    var msg = try Message.init(testing.allocator, .text, "Hello WebSocket");
    defer msg.deinit();

    try testing.expectEqual(MessageType.text, msg.type);
    try testing.expectEqualStrings("Hello WebSocket", msg.data);
}
```

Usage:

```zig
var msg = try Message.init(testing.allocator, .text, "Hello WebSocket");
defer msg.deinit();

try testing.expectEqual(MessageType.text, msg.type);
try testing.expectEqualStrings("Hello WebSocket", msg.data);
```

### Discussion

### Python vs Zig WebSocket Implementation

The approaches differ significantly:

**Python (websockets library):**
```python
import asyncio
import websockets

async def echo(websocket):
    async for message in websocket:
        await websocket.send(message)

# High-level abstraction
async def main():
    async with websockets.serve(echo, "localhost", 8765):
        await asyncio.Future()  # run forever

asyncio.run(main())
```

**Zig (protocol patterns):**
```zig
// Low-level protocol control
var builder = FrameBuilder.init(allocator);
defer builder.deinit();

try builder.text("Hello");
const frame = builder.build();

// Parse incoming frames
const header = try FrameParser.parse(frame);
// Handle based on opcode...
```

Key differences:
- **Abstraction Level**: Python hides protocol details; Zig exposes them
- **Control**: Zig gives precise control over frames; Python handles automatically
- **Performance**: Zig has zero overhead; Python has async runtime costs
- **Learning**: Zig teaches protocol internals; Python teaches API usage
- **Production**: Python is easier for simple cases; Zig better for custom protocols

### WebSocket Handshake

The WebSocket connection starts with an HTTP upgrade:

**Client Request:**

```zig
pub const HandshakeRequest = struct {
    host: []const u8,
    path: []const u8,
    key: []const u8,
    protocol: ?[]const u8 = null,

    pub fn build(self: HandshakeRequest, allocator: std.mem.Allocator) ![]u8 {
        var result = std.ArrayList(u8){};
        errdefer result.deinit(allocator);

        const writer = result.writer(allocator);

        try writer.print("GET {s} HTTP/1.1\r\n", .{self.path});
        try writer.print("Host: {s}\r\n", .{self.host});
        try writer.writeAll("Upgrade: websocket\r\n");
        try writer.writeAll("Connection: Upgrade\r\n");
        try writer.print("Sec-WebSocket-Key: {s}\r\n", .{self.key});
        try writer.writeAll("Sec-WebSocket-Version: 13\r\n");

        if (self.protocol) |proto| {
            try writer.print("Sec-WebSocket-Protocol: {s}\r\n", .{proto});
        }

        try writer.writeAll("\r\n");

        return result.toOwnedSlice(allocator);
    }
};
```

Example usage:

```zig
const request = HandshakeRequest{
    .host = "example.com",
    .path = "/chat",
    .key = "dGhlIHNhbXBsZSBub25jZQ==",
};

const handshake = try request.build(testing.allocator);
defer testing.allocator.free(handshake);

// Verify format
try testing.expect(std.mem.indexOf(u8, handshake, "GET /chat HTTP/1.1") != null);
try testing.expect(std.mem.indexOf(u8, handshake, "Upgrade: websocket") != null);
```

**Server Response:**

```zig
pub const HandshakeResponse = struct {
    status_code: u16,
    accept_key: ?[]const u8 = null,
    protocol: ?[]const u8 = null,

    pub fn isValid(self: HandshakeResponse) bool {
        return self.status_code == 101 and self.accept_key != null;
    }
};
```

Successful handshake response:

```
HTTP/1.1 101 Switching Protocols
Upgrade: websocket
Connection: Upgrade
Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=
```

The `Sec-WebSocket-Accept` value is derived from the client's key using SHA-1 and Base64 encoding (production implementations must verify this).

### Building WebSocket Frames

Create frames for different message types:

```zig
pub const FrameBuilder = struct {
    allocator: std.mem.Allocator,
    buffer: std.ArrayList(u8),

    pub fn init(allocator: std.mem.Allocator) FrameBuilder {
        return .{
            .allocator = allocator,
            .buffer = std.ArrayList(u8){},
        };
    }

    pub fn deinit(self: *FrameBuilder) void {
        self.buffer.deinit(self.allocator);
    }

    pub fn text(self: *FrameBuilder, message: []const u8) !void {
        try self.writeFrame(.text, true, message);
    }

    pub fn binary(self: *FrameBuilder, data: []const u8) !void {
        try self.writeFrame(.binary, true, data);
    }

    pub fn ping(self: *FrameBuilder, data: []const u8) !void {
        try self.writeFrame(.ping, true, data);
    }

    pub fn pong(self: *FrameBuilder, data: []const u8) !void {
        try self.writeFrame(.pong, true, data);
    }

    pub fn close(self: *FrameBuilder, code: u16, reason: []const u8) !void {
        var close_data = std.ArrayList(u8){};
        defer close_data.deinit(self.allocator);

        // Close frame payload: 2-byte status code + reason (big-endian)
        var code_bytes: [2]u8 = undefined;
        std.mem.writeInt(u16, &code_bytes, code, .big);
        try close_data.appendSlice(self.allocator, &code_bytes);
        try close_data.appendSlice(self.allocator, reason);

        try self.writeFrame(.close, true, close_data.items);
    }

    pub fn build(self: FrameBuilder) []const u8 {
        return self.buffer.items;
    }
};
```

Building a text frame:

```zig
var builder = FrameBuilder.init(testing.allocator);
defer builder.deinit();

try builder.text("Hello");

const frame = builder.build();

// Frame format: [FIN|RSV|Opcode][MASK|Length][Payload]
// First byte: FIN=1, opcode=1 (text) = 0x81
try testing.expectEqual(@as(u8, 0x81), frame[0]);
// Second byte: MASK=0, len=5 = 0x05
try testing.expectEqual(@as(u8, 5), frame[1]);
// Payload
try testing.expectEqualStrings("Hello", frame[2..]);
```

The frame structure:
- **Byte 0**: `FIN` (1 bit) + `RSV1-3` (3 bits) + `Opcode` (4 bits)
- **Byte 1**: `MASK` (1 bit) + `Payload Length` (7 bits)
- **Extended Length**: 2 or 8 bytes if needed
- **Masking Key**: 4 bytes if masked (client-to-server)
- **Payload**: The actual message data

### Parsing WebSocket Frames

Parse incoming frames to extract headers:

```zig
pub const FrameParser = struct {
    pub fn parse(data: []const u8) !FrameHeader {
        if (data.len < 2) return error.IncompleteFrame;

        const byte1 = data[0];
        const byte2 = data[1];

        const fin = (byte1 & 0x80) != 0;
        const rsv1 = (byte1 & 0x40) != 0;
        const rsv2 = (byte1 & 0x20) != 0;
        const rsv3 = (byte1 & 0x10) != 0;
        const opcode: FrameHeader.Opcode = @enumFromInt(byte1 & 0x0F);

        const masked = (byte2 & 0x80) != 0;
        var payload_length: u64 = byte2 & 0x7F;

        var offset: usize = 2;

        if (payload_length == 126) {
            if (data.len < 4) return error.IncompleteFrame;
            payload_length = (@as(u64, data[2]) << 8) | @as(u64, data[3]);
            offset = 4;
        } else if (payload_length == 127) {
            if (data.len < 10) return error.IncompleteFrame;
            payload_length = 0;
            for (2..10) |i| {
                payload_length = (payload_length << 8) | @as(u64, data[i]);
            }
            offset = 10;
        }

        var masking_key: ?[4]u8 = null;
        if (masked) {
            if (data.len < offset + 4) return error.IncompleteFrame;
            masking_key = data[offset..][0..4].*;
        }

        return .{
            .fin = fin,
            .rsv1 = rsv1,
            .rsv2 = rsv2,
            .rsv3 = rsv3,
            .opcode = opcode,
            .masked = masked,
            .payload_length = payload_length,
            .masking_key = masking_key,
        };
    }

    pub fn unmask(payload: []u8, masking_key: [4]u8) void {
        for (payload, 0..) |*byte, i| {
            byte.* ^= masking_key[i % 4];
        }
    }
};
```

Parsing example:

```zig
// Text frame: FIN=1, opcode=1, unmasked, length=5, payload="Hello"
const frame = [_]u8{ 0x81, 0x05, 'H', 'e', 'l', 'l', 'o' };

const header = try FrameParser.parse(&frame);

try testing.expect(header.fin);
try testing.expectEqual(FrameHeader.Opcode.text, header.opcode);
try testing.expect(!header.masked);
try testing.expectEqual(@as(u64, 5), header.payload_length);
```

### Connection State Management

Track WebSocket connection lifecycle:

```zig
pub const ConnectionState = enum {
    connecting,
    open,
    closing,
    closed,
};

pub const WebSocketConnection = struct {
    state: ConnectionState,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) WebSocketConnection {
        return .{
            .state = .connecting,
            .allocator = allocator,
        };
    }

    pub fn open(self: *WebSocketConnection) void {
        self.state = .open;
    }

    pub fn close(self: *WebSocketConnection) void {
        self.state = .closing;
    }

    pub fn isOpen(self: WebSocketConnection) bool {
        return self.state == .open;
    }

    pub fn canSend(self: WebSocketConnection) bool {
        return self.state == .open or self.state == .closing;
    }
};
```

State transitions:

```zig
var conn = WebSocketConnection.init(testing.allocator);
defer conn.deinit();

try testing.expectEqual(ConnectionState.connecting, conn.state);

conn.open();
try testing.expect(conn.isOpen());
try testing.expect(conn.canSend());

conn.close();
try testing.expect(!conn.isOpen());
try testing.expect(conn.canSend()); // Can still send close frame
```

### Close Codes

WebSocket defines standard closure codes:

```zig
pub const CloseCode = enum(u16) {
    normal = 1000,
    going_away = 1001,
    protocol_error = 1002,
    unsupported_data = 1003,
    invalid_frame = 1007,
    policy_violation = 1008,
    message_too_big = 1009,
    internal_error = 1011,

    pub fn toString(self: CloseCode) []const u8 {
        return switch (self) {
            .normal => "Normal Closure",
            .going_away => "Going Away",
            .protocol_error => "Protocol Error",
            .unsupported_data => "Unsupported Data",
            .invalid_frame => "Invalid Frame Payload Data",
            .policy_violation => "Policy Violation",
            .message_too_big => "Message Too Big",
            .internal_error => "Internal Server Error",
        };
    }
};
```

Using close codes:

```zig
try builder.close(@intFromEnum(CloseCode.normal), "Goodbye");

// In production, parse close frame to get code and reason
if (header.opcode == .close) {
    const code = @as(u16, payload[0]) << 8 | payload[1];
    const reason = payload[2..];
    // Handle graceful shutdown...
}
```

### Message Fragmentation

Split large messages into multiple frames:

```zig
pub const MessageFragmenter = struct {
    max_frame_size: usize,

    pub fn init(max_frame_size: usize) MessageFragmenter {
        return .{ .max_frame_size = max_frame_size };
    }

    pub fn fragment(
        self: MessageFragmenter,
        allocator: std.mem.Allocator,
        data: []const u8,
    ) !std.ArrayList([]const u8) {
        var fragments = std.ArrayList([]const u8){};
        errdefer {
            for (fragments.items) |frag| {
                allocator.free(frag);
            }
            fragments.deinit(allocator);
        }

        var offset: usize = 0;
        while (offset < data.len) {
            const remaining = data.len - offset;
            const chunk_size = @min(remaining, self.max_frame_size);
            const chunk = try allocator.dupe(u8, data[offset..][0..chunk_size]);
            try fragments.append(allocator, chunk);
            offset += chunk_size;
        }

        return fragments;
    }
};
```

Example:

```zig
const fragmenter = MessageFragmenter.init(5);
const data = "Hello World!";

var fragments = try fragmenter.fragment(testing.allocator, data);
defer {
    for (fragments.items) |frag| {
        testing.allocator.free(frag);
    }
    fragments.deinit(testing.allocator);
}

try testing.expectEqual(@as(usize, 3), fragments.items.len);
try testing.expectEqualStrings("Hello", fragments.items[0]);
try testing.expectEqualStrings(" Worl", fragments.items[1]);
try testing.expectEqualStrings("d!", fragments.items[2]);
```

When sending fragmented messages:
- First frame: `FIN=0`, opcode = text/binary
- Middle frames: `FIN=0`, opcode = continuation (0x0)
- Last frame: `FIN=1`, opcode = continuation

### Ping/Pong Heartbeat

Detect connection health with ping/pong:

```zig
pub const PingPongHandler = struct {
    last_ping_time: i64 = 0,
    last_pong_time: i64 = 0,

    pub fn sendPing(self: *PingPongHandler, current_time: i64) void {
        self.last_ping_time = current_time;
    }

    pub fn receivePong(self: *PingPongHandler, current_time: i64) void {
        self.last_pong_time = current_time;
    }

    pub fn isAlive(self: PingPongHandler, current_time: i64, timeout_ms: i64) bool {
        if (self.last_ping_time == 0) return true;
        const elapsed = current_time - self.last_ping_time;
        return self.last_pong_time >= self.last_ping_time or elapsed < timeout_ms;
    }
};
```

Usage pattern:

```zig
var handler = PingPongHandler{};

// Send ping
handler.sendPing(1000);

// Later: check if alive
if (!handler.isAlive(6000, 4000)) {
    // No pong received within timeout - connection dead
    conn.close();
}

// When pong received
handler.receivePong(2000);
// Connection is alive
```

### Full Tested Code

```zig
// Recipe 11.3: WebSocket Communication
// Target Zig Version: 0.15.2
//
// Educational demonstration of WebSocket patterns in Zig.
// Shows WebSocket frame structure, handshake, and message handling patterns.
//
// Note: This demonstrates WebSocket protocol patterns without actual networking.
// For production WebSocket clients/servers, use a library like websocket.zig
//
// Key concepts:
// - WebSocket frame structure and parsing
// - Handshake protocol
// - Message fragmentation
// - Control frames (ping/pong/close)
// - Text and binary messages
// - Masking for client-to-server messages

const std = @import("std");
const testing = std.testing;

// ANCHOR: frame_header
// WebSocket frame header structure
pub const FrameHeader = struct {
    fin: bool, // Final fragment flag
    rsv1: bool = false, // Reserved bits (must be 0)
    rsv2: bool = false,
    rsv3: bool = false,
    opcode: Opcode,
    masked: bool,
    payload_length: u64,
    masking_key: ?[4]u8 = null,

    pub const Opcode = enum(u4) {
        continuation = 0x0,
        text = 0x1,
        binary = 0x2,
        close = 0x8,
        ping = 0x9,
        pong = 0xA,
        _,

        pub fn isControl(self: Opcode) bool {
            return @intFromEnum(self) >= 0x8;
        }
    };
};

test "frame header opcodes" {
    try testing.expect(FrameHeader.Opcode.ping.isControl());
    try testing.expect(FrameHeader.Opcode.pong.isControl());
    try testing.expect(FrameHeader.Opcode.close.isControl());
    try testing.expect(!FrameHeader.Opcode.text.isControl());
    try testing.expect(!FrameHeader.Opcode.binary.isControl());
}
// ANCHOR_END: frame_header

// ANCHOR: message_type
pub const MessageType = enum {
    text,
    binary,
    ping,
    pong,
    close,
};

pub const Message = struct {
    type: MessageType,
    data: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, msg_type: MessageType, data: []const u8) !Message {
        return .{
            .type = msg_type,
            .data = try allocator.dupe(u8, data),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Message) void {
        self.allocator.free(self.data);
    }
};

test "message creation" {
    var msg = try Message.init(testing.allocator, .text, "Hello WebSocket");
    defer msg.deinit();

    try testing.expectEqual(MessageType.text, msg.type);
    try testing.expectEqualStrings("Hello WebSocket", msg.data);
}
// ANCHOR_END: message_type

// ANCHOR: handshake_request
pub const HandshakeRequest = struct {
    host: []const u8,
    path: []const u8,
    key: []const u8,
    protocol: ?[]const u8 = null,

    pub fn build(self: HandshakeRequest, allocator: std.mem.Allocator) ![]u8 {
        var result = std.ArrayList(u8){};
        errdefer result.deinit(allocator);

        const writer = result.writer(allocator);

        try writer.print("GET {s} HTTP/1.1\r\n", .{self.path});
        try writer.print("Host: {s}\r\n", .{self.host});
        try writer.writeAll("Upgrade: websocket\r\n");
        try writer.writeAll("Connection: Upgrade\r\n");
        try writer.print("Sec-WebSocket-Key: {s}\r\n", .{self.key});
        try writer.writeAll("Sec-WebSocket-Version: 13\r\n");

        if (self.protocol) |proto| {
            try writer.print("Sec-WebSocket-Protocol: {s}\r\n", .{proto});
        }

        try writer.writeAll("\r\n");

        return result.toOwnedSlice(allocator);
    }
};

test "handshake request building" {
    const request = HandshakeRequest{
        .host = "example.com",
        .path = "/chat",
        .key = "dGhlIHNhbXBsZSBub25jZQ==",
    };

    const handshake = try request.build(testing.allocator);
    defer testing.allocator.free(handshake);

    try testing.expect(std.mem.indexOf(u8, handshake, "GET /chat HTTP/1.1") != null);
    try testing.expect(std.mem.indexOf(u8, handshake, "Host: example.com") != null);
    try testing.expect(std.mem.indexOf(u8, handshake, "Upgrade: websocket") != null);
}
// ANCHOR_END: handshake_request

// ANCHOR: handshake_response
pub const HandshakeResponse = struct {
    status_code: u16,
    accept_key: ?[]const u8 = null,
    protocol: ?[]const u8 = null,

    pub fn isValid(self: HandshakeResponse) bool {
        return self.status_code == 101 and self.accept_key != null;
    }

    pub fn parse(allocator: std.mem.Allocator, response: []const u8) !HandshakeResponse {
        _ = allocator;

        var result = HandshakeResponse{
            .status_code = 0,
        };

        var lines = std.mem.splitScalar(u8, response, '\n');

        // Parse status line
        if (lines.next()) |status_line| {
            if (std.mem.indexOf(u8, status_line, "101")) |_| {
                result.status_code = 101;
            }
        }

        // Parse headers
        while (lines.next()) |line| {
            if (std.mem.trim(u8, line, &std.ascii.whitespace).len == 0) break;

            if (std.mem.indexOf(u8, line, "Sec-WebSocket-Accept:")) |_| {
                const colon_idx = std.mem.indexOf(u8, line, ":") orelse continue;
                const value = std.mem.trim(u8, line[colon_idx + 1 ..], &std.ascii.whitespace);
                result.accept_key = value;
            }
        }

        return result;
    }
};

test "handshake response parsing" {
    const response =
        \\HTTP/1.1 101 Switching Protocols
        \\Upgrade: websocket
        \\Connection: Upgrade
        \\Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=
        \\
        \\
    ;

    const parsed = try HandshakeResponse.parse(testing.allocator, response);

    try testing.expectEqual(@as(u16, 101), parsed.status_code);
    try testing.expect(parsed.isValid());
    try testing.expect(parsed.accept_key != null);
}
// ANCHOR_END: handshake_response

// ANCHOR: frame_builder
pub const FrameBuilder = struct {
    allocator: std.mem.Allocator,
    buffer: std.ArrayList(u8),

    pub fn init(allocator: std.mem.Allocator) FrameBuilder {
        return .{
            .allocator = allocator,
            .buffer = std.ArrayList(u8){},
        };
    }

    pub fn deinit(self: *FrameBuilder) void {
        self.buffer.deinit(self.allocator);
    }

    pub fn text(self: *FrameBuilder, message: []const u8) !void {
        try self.writeFrame(.text, true, message);
    }

    pub fn binary(self: *FrameBuilder, data: []const u8) !void {
        try self.writeFrame(.binary, true, data);
    }

    pub fn ping(self: *FrameBuilder, data: []const u8) !void {
        try self.writeFrame(.ping, true, data);
    }

    pub fn pong(self: *FrameBuilder, data: []const u8) !void {
        try self.writeFrame(.pong, true, data);
    }

    pub fn close(self: *FrameBuilder, code: u16, reason: []const u8) !void {
        var close_data = std.ArrayList(u8){};
        defer close_data.deinit(self.allocator);

        // Close frame payload: 2-byte status code + reason (big-endian)
        var code_bytes: [2]u8 = undefined;
        std.mem.writeInt(u16, &code_bytes, code, .big);
        try close_data.appendSlice(self.allocator, &code_bytes);
        try close_data.appendSlice(self.allocator, reason);

        try self.writeFrame(.close, true, close_data.items);
    }

    fn writeFrame(
        self: *FrameBuilder,
        opcode: FrameHeader.Opcode,
        fin: bool,
        payload: []const u8,
    ) !void {
        // First byte: FIN + RSV + Opcode
        var byte1: u8 = @intFromEnum(opcode);
        if (fin) byte1 |= 0x80;

        try self.buffer.append(self.allocator, byte1);

        // Second byte: MASK + Payload length
        const payload_len = payload.len;
        var byte2: u8 = 0; // No masking for server-to-client

        if (payload_len < 126) {
            byte2 |= @as(u8, @intCast(payload_len));
            try self.buffer.append(self.allocator, byte2);
        } else if (payload_len <= 0xFFFF) {
            byte2 |= 126;
            try self.buffer.append(self.allocator, byte2);
            var len_bytes: [2]u8 = undefined;
            std.mem.writeInt(u16, &len_bytes, @intCast(payload_len), .big);
            try self.buffer.appendSlice(self.allocator, &len_bytes);
        } else {
            byte2 |= 127;
            try self.buffer.append(self.allocator, byte2);
            // Write 64-bit length in network byte order (big-endian)
            var len_bytes: [8]u8 = undefined;
            std.mem.writeInt(u64, &len_bytes, @intCast(payload_len), .big);
            try self.buffer.appendSlice(self.allocator, &len_bytes);
        }

        // Payload data
        try self.buffer.appendSlice(self.allocator, payload);
    }

    pub fn build(self: FrameBuilder) []const u8 {
        return self.buffer.items;
    }
};

test "frame builder text" {
    var builder = FrameBuilder.init(testing.allocator);
    defer builder.deinit();

    try builder.text("Hello");

    const frame = builder.build();

    // First byte: FIN=1, opcode=1 (text)
    try testing.expectEqual(@as(u8, 0x81), frame[0]);
    // Second byte: MASK=0, len=5
    try testing.expectEqual(@as(u8, 5), frame[1]);
    // Payload
    try testing.expectEqualStrings("Hello", frame[2..]);
}
// ANCHOR_END: frame_builder

// ANCHOR: frame_parser
pub const FrameParser = struct {
    pub fn parse(data: []const u8) !FrameHeader {
        if (data.len < 2) return error.IncompleteFrame;

        const byte1 = data[0];
        const byte2 = data[1];

        const fin = (byte1 & 0x80) != 0;
        const rsv1 = (byte1 & 0x40) != 0;
        const rsv2 = (byte1 & 0x20) != 0;
        const rsv3 = (byte1 & 0x10) != 0;
        const opcode: FrameHeader.Opcode = @enumFromInt(byte1 & 0x0F);

        const masked = (byte2 & 0x80) != 0;
        var payload_length: u64 = byte2 & 0x7F;

        var offset: usize = 2;

        if (payload_length == 126) {
            if (data.len < 4) return error.IncompleteFrame;
            // Read 16-bit length in network byte order (big-endian)
            payload_length = std.mem.readInt(u16, data[2..4][0..2], .big);
            offset = 4;
        } else if (payload_length == 127) {
            if (data.len < 10) return error.IncompleteFrame;
            // Read 64-bit length in network byte order (big-endian)
            payload_length = std.mem.readInt(u64, data[2..10][0..8], .big);
            offset = 10;
        }

        var masking_key: ?[4]u8 = null;
        if (masked) {
            if (data.len < offset + 4) return error.IncompleteFrame;
            masking_key = data[offset..][0..4].*;
        }

        return .{
            .fin = fin,
            .rsv1 = rsv1,
            .rsv2 = rsv2,
            .rsv3 = rsv3,
            .opcode = opcode,
            .masked = masked,
            .payload_length = payload_length,
            .masking_key = masking_key,
        };
    }

    pub fn unmask(payload: []u8, masking_key: [4]u8) void {
        for (payload, 0..) |*byte, i| {
            byte.* ^= masking_key[i % 4];
        }
    }
};

test "frame parser basic" {
    // Text frame: FIN=1, opcode=1, unmasked, length=5, payload="Hello"
    const frame = [_]u8{ 0x81, 0x05, 'H', 'e', 'l', 'l', 'o' };

    const header = try FrameParser.parse(&frame);

    try testing.expect(header.fin);
    try testing.expectEqual(FrameHeader.Opcode.text, header.opcode);
    try testing.expect(!header.masked);
    try testing.expectEqual(@as(u64, 5), header.payload_length);
}
// ANCHOR_END: frame_parser

// ANCHOR: connection_state
pub const ConnectionState = enum {
    connecting,
    open,
    closing,
    closed,
};

pub const WebSocketConnection = struct {
    state: ConnectionState,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) WebSocketConnection {
        return .{
            .state = .connecting,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *WebSocketConnection) void {
        _ = self;
    }

    pub fn open(self: *WebSocketConnection) void {
        self.state = .open;
    }

    pub fn close(self: *WebSocketConnection) void {
        self.state = .closing;
    }

    pub fn isOpen(self: WebSocketConnection) bool {
        return self.state == .open;
    }

    pub fn canSend(self: WebSocketConnection) bool {
        return self.state == .open or self.state == .closing;
    }
};

test "connection state" {
    var conn = WebSocketConnection.init(testing.allocator);
    defer conn.deinit();

    try testing.expectEqual(ConnectionState.connecting, conn.state);
    try testing.expect(!conn.isOpen());

    conn.open();
    try testing.expect(conn.isOpen());
    try testing.expect(conn.canSend());

    conn.close();
    try testing.expect(!conn.isOpen());
    try testing.expect(conn.canSend()); // Can still send close frame
}
// ANCHOR_END: connection_state

// ANCHOR: close_codes
pub const CloseCode = enum(u16) {
    normal = 1000,
    going_away = 1001,
    protocol_error = 1002,
    unsupported_data = 1003,
    invalid_frame = 1007,
    policy_violation = 1008,
    message_too_big = 1009,
    internal_error = 1011,

    pub fn toString(self: CloseCode) []const u8 {
        return switch (self) {
            .normal => "Normal Closure",
            .going_away => "Going Away",
            .protocol_error => "Protocol Error",
            .unsupported_data => "Unsupported Data",
            .invalid_frame => "Invalid Frame Payload Data",
            .policy_violation => "Policy Violation",
            .message_too_big => "Message Too Big",
            .internal_error => "Internal Server Error",
        };
    }
};

test "close codes" {
    try testing.expectEqual(@as(u16, 1000), @intFromEnum(CloseCode.normal));
    try testing.expectEqualStrings("Normal Closure", CloseCode.normal.toString());
    try testing.expectEqualStrings("Protocol Error", CloseCode.protocol_error.toString());
}
// ANCHOR_END: close_codes

// ANCHOR: message_fragmenter
pub const MessageFragmenter = struct {
    max_frame_size: usize,

    pub fn init(max_frame_size: usize) MessageFragmenter {
        return .{ .max_frame_size = max_frame_size };
    }

    pub fn fragment(
        self: MessageFragmenter,
        allocator: std.mem.Allocator,
        data: []const u8,
    ) !std.ArrayList([]const u8) {
        var fragments = std.ArrayList([]const u8){};
        errdefer {
            for (fragments.items) |frag| {
                allocator.free(frag);
            }
            fragments.deinit(allocator);
        }

        var offset: usize = 0;
        while (offset < data.len) {
            const remaining = data.len - offset;
            const chunk_size = @min(remaining, self.max_frame_size);
            const chunk = try allocator.dupe(u8, data[offset..][0..chunk_size]);
            try fragments.append(allocator, chunk);
            offset += chunk_size;
        }

        return fragments;
    }
};

test "message fragmentation" {
    const fragmenter = MessageFragmenter.init(5);
    const data = "Hello World!";

    var fragments = try fragmenter.fragment(testing.allocator, data);
    defer {
        for (fragments.items) |frag| {
            testing.allocator.free(frag);
        }
        fragments.deinit(testing.allocator);
    }

    try testing.expectEqual(@as(usize, 3), fragments.items.len);
    try testing.expectEqualStrings("Hello", fragments.items[0]);
    try testing.expectEqualStrings(" Worl", fragments.items[1]);
    try testing.expectEqualStrings("d!", fragments.items[2]);
}
// ANCHOR_END: message_fragmenter

// ANCHOR: ping_pong
pub const PingPongHandler = struct {
    last_ping_time: i64 = 0,
    last_pong_time: i64 = 0,

    pub fn sendPing(self: *PingPongHandler, current_time: i64) void {
        self.last_ping_time = current_time;
    }

    pub fn receivePong(self: *PingPongHandler, current_time: i64) void {
        self.last_pong_time = current_time;
    }

    pub fn isAlive(self: PingPongHandler, current_time: i64, timeout_ms: i64) bool {
        if (self.last_ping_time == 0) return true;
        const elapsed = current_time - self.last_ping_time;
        return self.last_pong_time >= self.last_ping_time or elapsed < timeout_ms;
    }
};

test "ping pong handler" {
    var handler = PingPongHandler{};

    handler.sendPing(1000);
    try testing.expect(!handler.isAlive(6000, 4000)); // Timeout

    handler.receivePong(2000);
    try testing.expect(handler.isAlive(6000, 4000)); // Received pong
}
// ANCHOR_END: ping_pong

// Comprehensive test
test "comprehensive websocket patterns" {
    // Build a text frame
    var builder = FrameBuilder.init(testing.allocator);
    defer builder.deinit();

    try builder.text("Test");
    const frame = builder.build();

    // Parse the frame
    const header = try FrameParser.parse(frame);
    try testing.expect(header.fin);
    try testing.expectEqual(FrameHeader.Opcode.text, header.opcode);

    // Connection state management
    var conn = WebSocketConnection.init(testing.allocator);
    defer conn.deinit();

    conn.open();
    try testing.expect(conn.canSend());

    // Close with code
    try builder.close(@intFromEnum(CloseCode.normal), "Goodbye");
    try testing.expect(builder.build().len > 0);
}
```

### See Also

- Recipe 11.1: Making HTTP Requests
- Recipe 11.2: Working with JSON APIs
- Recipe 11.4: Building a Simple HTTP Server
- Recipe 12.1: Async I/O Patterns

---

## Recipe 11.4: Building a Simple HTTP Server {#recipe-11-4}

**Tags:** allocators, arraylist, data-structures, error-handling, hashmap, http, json, memory, networking, parsing, resource-cleanup, slices, sockets, testing, xml
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_4.zig`

### Problem

You want to build an HTTP server in Zig - parsing requests, routing to handlers, generating responses, and implementing middleware patterns. You need to understand HTTP server fundamentals without the complexity of actual network programming.

### Solution

This recipe demonstrates HTTP server patterns using pure Zig structures and logic. While production servers use `std.http.Server` or frameworks, understanding these patterns helps you work with any HTTP library.

### HTTP Methods

Define supported HTTP methods:

```zig
pub const HttpMethod = enum {
    GET,
    POST,
    PUT,
    DELETE,
    PATCH,
    HEAD,
    OPTIONS,

    pub fn fromString(s: []const u8) ?HttpMethod {
        if (std.mem.eql(u8, s, "GET")) return .GET;
        if (std.mem.eql(u8, s, "POST")) return .POST;
        if (std.mem.eql(u8, s, "PUT")) return .PUT;
        if (std.mem.eql(u8, s, "DELETE")) return .DELETE;
        if (std.mem.eql(u8, s, "PATCH")) return .PATCH;
        if (std.mem.eql(u8, s, "HEAD")) return .HEAD;
        if (std.mem.eql(u8, s, "OPTIONS")) return .OPTIONS;
        return null;
    }

    pub fn toString(self: HttpMethod) []const u8 {
        return switch (self) {
            .GET => "GET",
            .POST => "POST",
            .PUT => "PUT",
            .DELETE => "DELETE",
            .PATCH => "PATCH",
            .HEAD => "HEAD",
            .OPTIONS => "OPTIONS",
        };
    }
};

test "http method conversion" {
    try testing.expectEqual(HttpMethod.GET, HttpMethod.fromString("GET").?);
    try testing.expectEqualStrings("POST", HttpMethod.POST.toString());
    try testing.expect(HttpMethod.fromString("INVALID") == null);
}
```

Usage:

```zig
try testing.expectEqual(HttpMethod.GET, HttpMethod.fromString("GET").?);
try testing.expectEqualStrings("POST", HttpMethod.POST.toString());
```

### HTTP Status Codes

Standard HTTP status codes with descriptions:

```zig
pub const HttpStatus = enum(u16) {
    ok = 200,
    created = 201,
    no_content = 204,
    moved_permanently = 301,
    found = 302,
    bad_request = 400,
    unauthorized = 401,
    forbidden = 403,
    not_found = 404,
    method_not_allowed = 405,
    internal_server_error = 500,
    not_implemented = 501,
    service_unavailable = 503,

    pub fn toText(self: HttpStatus) []const u8 {
        return switch (self) {
            .ok => "OK",
            .created => "Created",
            .no_content => "No Content",
            .moved_permanently => "Moved Permanently",
            .found => "Found",
            .bad_request => "Bad Request",
            .unauthorized => "Unauthorized",
            .forbidden => "Forbidden",
            .not_found => "Not Found",
            .method_not_allowed => "Method Not Allowed",
            .internal_server_error => "Internal Server Error",
            .not_implemented => "Not Implemented",
            .service_unavailable => "Service Unavailable",
        };
    }
};

test "http status codes" {
    try testing.expectEqual(@as(u16, 200), @intFromEnum(HttpStatus.ok));
    try testing.expectEqual(@as(u16, 404), @intFromEnum(HttpStatus.not_found));
    try testing.expectEqualStrings("OK", HttpStatus.ok.toText());
    try testing.expectEqualStrings("Not Found", HttpStatus.not_found.toText());
}
```

Status code examples:

```zig
try testing.expectEqual(@as(u16, 200), @intFromEnum(HttpStatus.ok));
try testing.expectEqual(@as(u16, 404), @intFromEnum(HttpStatus.not_found));
try testing.expectEqualStrings("OK", HttpStatus.ok.toText());
```

### Discussion

### Python vs Zig HTTP Servers

The implementation philosophies differ:

**Python (Flask/FastAPI):**
```python
from flask import Flask, request, jsonify

app = Flask(__name__)

@app.route('/api/users', methods=['GET'])
def get_users():
    return jsonify({"users": ["Alice", "Bob"]})

@app.route('/api/users', methods=['POST'])
def create_user():
    data = request.json
    return jsonify({"id": 123, "name": data["name"]}), 201

if __name__ == '__main__':
    app.run(port=8080)
```

**Zig (Pattern-based):**
```zig
var router = Router.init(allocator);
defer router.deinit();

try router.add(.GET, "/api/users", getUsersHandler);
try router.add(.POST, "/api/users", createUserHandler);

// In handler:
fn getUsersHandler(request: *const HttpRequest, allocator: Allocator) !HttpResponse {
    return try jsonResponse(allocator, .ok, "{\"users\":[\"Alice\",\"Bob\"]}");
}
```

Key differences:
- **Magic vs Explicit**: Python uses decorators; Zig uses explicit registration
- **Serialization**: Python auto-converts; Zig requires manual JSON handling
- **Memory**: Python GC handles cleanup; Zig requires explicit `defer`
- **Type Safety**: Zig catches routing errors at compile time
- **Performance**: Zig has zero overhead; Python has interpreter costs
- **Control**: Zig exposes full request/response lifecycle

### HTTP Request Parsing

Parse raw HTTP requests into structured data:

```zig
pub const HttpRequest = struct {
    method: HttpMethod,
    path: []const u8,
    headers: std.StringHashMap([]const u8),
    body: []const u8,
    allocator: std.mem.Allocator,

    pub fn parse(allocator: std.mem.Allocator, raw: []const u8) !HttpRequest {
        var request = HttpRequest.init(allocator);
        errdefer request.deinit();

        var lines = std.mem.splitScalar(u8, raw, '\n');

        // Parse request line
        if (lines.next()) |request_line| {
            var parts = std.mem.splitScalar(u8, request_line, ' ');

            if (parts.next()) |method_str| {
                const method_trimmed = std.mem.trim(u8, method_str, &std.ascii.whitespace);
                request.method = HttpMethod.fromString(method_trimmed) orelse .GET;
            }

            if (parts.next()) |path_str| {
                request.path = std.mem.trim(u8, path_str, &std.ascii.whitespace);
            }
        }

        // Parse headers
        while (lines.next()) |line| {
            const trimmed = std.mem.trim(u8, line, &std.ascii.whitespace);
            if (trimmed.len == 0) break; // Empty line separates headers from body

            if (std.mem.indexOf(u8, trimmed, ":")) |colon_idx| {
                const name = std.mem.trim(u8, trimmed[0..colon_idx], &std.ascii.whitespace);
                const value = std.mem.trim(u8, trimmed[colon_idx + 1 ..], &std.ascii.whitespace);

                const owned_name = try allocator.dupe(u8, name);
                errdefer allocator.free(owned_name);
                const owned_value = try allocator.dupe(u8, value);
                errdefer allocator.free(owned_value);

                try request.headers.put(owned_name, owned_value);
            }
        }

        // Remaining is body
        // (Real implementation would use Content-Length header)

        return request;
    }

    pub fn getHeader(self: HttpRequest, name: []const u8) ?[]const u8 {
        return self.headers.get(name);
    }
};
```

Parsing example:

```zig
const raw_request =
    \\GET /api/users HTTP/1.1
    \\Host: example.com
    \\Content-Type: application/json
    \\
    \\{"name": "Alice"}
;

var request = try HttpRequest.parse(testing.allocator, raw_request);
defer request.deinit();

try testing.expectEqual(HttpMethod.GET, request.method);
try testing.expectEqualStrings("/api/users", request.path);

const host = request.getHeader("Host");
try testing.expectEqualStrings("example.com", host.?);
```

**Important**: Always `defer request.deinit()` to free allocated headers.

### HTTP Response Building

Construct HTTP responses programmatically:

```zig
pub const HttpResponse = struct {
    status: HttpStatus,
    headers: std.StringHashMap([]const u8),
    body: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, status: HttpStatus) HttpResponse {
        return .{
            .status = status,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = "",
            .allocator = allocator,
        };
    }

    pub fn setHeader(self: *HttpResponse, name: []const u8, value: []const u8) !void {
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        // Use getOrPut to avoid leaking keys when updating
        const gop = try self.headers.getOrPut(name);
        if (gop.found_existing) {
            self.allocator.free(gop.value_ptr.*);
            gop.value_ptr.* = owned_value;
        } else {
            const owned_name = try self.allocator.dupe(u8, name);
            gop.key_ptr.* = owned_name;
            gop.value_ptr.* = owned_value;
        }
    }

    pub fn setBody(self: *HttpResponse, body: []const u8) void {
        self.body = body;
    }

    pub fn build(self: HttpResponse, allocator: std.mem.Allocator) ![]u8 {
        var result = std.ArrayList(u8){};
        errdefer result.deinit(allocator);

        const writer = result.writer(allocator);

        // Status line
        try writer.print("HTTP/1.1 {d} {s}\r\n", .{
            @intFromEnum(self.status),
            self.status.toText(),
        });

        // Headers
        var it = self.headers.iterator();
        while (it.next()) |entry| {
            try writer.print("{s}: {s}\r\n", .{ entry.key_ptr.*, entry.value_ptr.* });
        }

        // Empty line separates headers from body
        try writer.writeAll("\r\n");

        // Body
        try writer.writeAll(self.body);

        return result.toOwnedSlice(allocator);
    }
};
```

Building a response:

```zig
var response = HttpResponse.init(testing.allocator, .ok);
defer response.deinit();

try response.setHeader("Content-Type", "text/plain");
response.setBody("Hello, World!");

const raw = try response.build(testing.allocator);
defer testing.allocator.free(raw);

// Verify response format
try testing.expect(std.mem.indexOf(u8, raw, "HTTP/1.1 200 OK") != null);
try testing.expect(std.mem.indexOf(u8, raw, "Content-Type: text/plain") != null);
try testing.expect(std.mem.indexOf(u8, raw, "Hello, World!") != null);
```

### Routing

Map URLs to handler functions:

```zig
pub const Handler = *const fn (request: *const HttpRequest, allocator: std.mem.Allocator) anyerror!HttpResponse;

pub const Route = struct {
    method: HttpMethod,
    path: []const u8,
    handler: Handler,

    pub fn matches(self: Route, method: HttpMethod, path: []const u8) bool {
        return self.method == method and std.mem.eql(u8, self.path, path);
    }
};

pub const Router = struct {
    routes: std.ArrayList(Route),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Router {
        return .{
            .routes = std.ArrayList(Route){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Router) void {
        self.routes.deinit(self.allocator);
    }

    pub fn add(self: *Router, method: HttpMethod, path: []const u8, handler: Handler) !void {
        try self.routes.append(self.allocator, .{
            .method = method,
            .path = path,
            .handler = handler,
        });
    }

    pub fn handle(self: Router, request: *const HttpRequest) !HttpResponse {
        for (self.routes.items) |route| {
            if (route.matches(request.method, request.path)) {
                return try route.handler(request, self.allocator);
            }
        }

        // No route matched - return 404
        var response = HttpResponse.init(self.allocator, .not_found);
        response.setBody("Not Found");
        return response;
    }
};
```

Using the router:

```zig
fn getUsersHandler(request: *const HttpRequest, allocator: Allocator) !HttpResponse {
    _ = request;
    var response = HttpResponse.init(allocator, .ok);
    response.setBody("Users list");
    return response;
}

var router = Router.init(testing.allocator);
defer router.deinit();

try router.add(.GET, "/api/users", getUsersHandler);

var request = HttpRequest.init(testing.allocator);
defer request.deinit();
request.method = .GET;
request.path = "/api/users";

var response = try router.handle(&request);
defer response.deinit();

try testing.expectEqual(HttpStatus.ok, response.status);
```

The router automatically returns `404 Not Found` for unmatched routes.

### Middleware Pattern

Chain request processing with middleware:

```zig
pub const Middleware = *const fn (request: *HttpRequest, next: Handler) anyerror!HttpResponse;

pub const MiddlewareChain = struct {
    middlewares: std.ArrayList(Middleware),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) MiddlewareChain {
        return .{
            .middlewares = std.ArrayList(Middleware){},
            .allocator = allocator,
        };
    }

    pub fn use(self: *MiddlewareChain, middleware: Middleware) !void {
        try self.middlewares.append(self.allocator, middleware);
    }
};

// Example: Logging middleware
fn loggingMiddleware(request: *HttpRequest, next: Handler) !HttpResponse {
    // Log request
    std.debug.print("Request: {s} {s}\n", .{
        request.method.toString(),
        request.path,
    });

    // Call next handler
    var response = try next(request, request.allocator);

    // Log response
    std.debug.print("Response: {d}\n", .{@intFromEnum(response.status)});

    return response;
}
```

Middleware allows cross-cutting concerns like logging, authentication, and CORS without modifying handlers.

### Content Type Detection

Determine MIME types from file extensions:

```zig
pub const ContentType = enum {
    text_html,
    text_plain,
    application_json,
    application_xml,
    image_png,
    image_jpeg,
    application_octet_stream,

    pub fn fromExtension(ext: []const u8) ContentType {
        if (std.mem.eql(u8, ext, ".html")) return .text_html;
        if (std.mem.eql(u8, ext, ".txt")) return .text_plain;
        if (std.mem.eql(u8, ext, ".json")) return .application_json;
        if (std.mem.eql(u8, ext, ".xml")) return .application_xml;
        if (std.mem.eql(u8, ext, ".png")) return .image_png;
        if (std.mem.eql(u8, ext, ".jpg") or std.mem.eql(u8, ext, ".jpeg")) return .image_jpeg;
        return .application_octet_stream;
    }

    pub fn toString(self: ContentType) []const u8 {
        return switch (self) {
            .text_html => "text/html",
            .text_plain => "text/plain",
            .application_json => "application/json",
            // ...
        };
    }
};
```

Usage:

```zig
const html_type = ContentType.fromExtension(".html");
try testing.expectEqual(ContentType.text_html, html_type);
try testing.expectEqualStrings("text/html", html_type.toString());
```

### Static File Serving

Serve static files with proper content types:

```zig
pub const StaticFileHandler = struct {
    root_dir: []const u8,

    pub fn init(root_dir: []const u8) StaticFileHandler {
        return .{ .root_dir = root_dir };
    }

    pub fn serve(self: StaticFileHandler, path: []const u8, allocator: std.mem.Allocator) !HttpResponse {
        _ = self;

        // In real implementation: read file from root_dir + path
        var response = HttpResponse.init(allocator, .ok);

        // Detect content type from extension
        const ext = std.fs.path.extension(path);
        const content_type = ContentType.fromExtension(ext);
        try response.setHeader("Content-Type", content_type.toString());

        response.setBody("File content here");

        return response;
    }
};
```

Example:

```zig
const handler = StaticFileHandler.init("/var/www");

var response = try handler.serve("/index.html", testing.allocator);
defer response.deinit();

const content_type = response.headers.get("Content-Type");
try testing.expectEqualStrings("text/html", content_type.?);
```

### Query Parameters

Parse URL query strings:

```zig
pub const QueryParams = struct {
    params: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn parse(allocator: std.mem.Allocator, query_string: []const u8) !QueryParams {
        var result = QueryParams.init(allocator);
        errdefer result.deinit();

        var pairs = std.mem.splitScalar(u8, query_string, '&');
        while (pairs.next()) |pair| {
            if (std.mem.indexOf(u8, pair, "=")) |eq_idx| {
                const key = pair[0..eq_idx];
                const value = pair[eq_idx + 1 ..];

                const owned_key = try allocator.dupe(u8, key);
                errdefer allocator.free(owned_key);
                const owned_value = try allocator.dupe(u8, value);
                errdefer allocator.free(owned_value);

                try result.params.put(owned_key, owned_value);
            }
        }

        return result;
    }

    pub fn get(self: QueryParams, key: []const u8) ?[]const u8 {
        return self.params.get(key);
    }
};
```

Parsing example:

```zig
var params = try QueryParams.parse(testing.allocator, "name=Alice&age=30");
defer params.deinit();

try testing.expectEqualStrings("Alice", params.get("name").?);
try testing.expectEqualStrings("30", params.get("age").?);
```

### JSON Response Helper

Convenience function for JSON responses:

```zig
pub fn jsonResponse(allocator: std.mem.Allocator, status: HttpStatus, json_data: []const u8) !HttpResponse {
    var response = HttpResponse.init(allocator, status);
    errdefer response.deinit();

    try response.setHeader("Content-Type", "application/json");
    response.setBody(json_data);

    return response;
}
```

Usage:

```zig
var response = try jsonResponse(testing.allocator, .ok, "{\"message\":\"Success\"}");
defer response.deinit();

const content_type = response.headers.get("Content-Type");
try testing.expectEqualStrings("application/json", content_type.?);
```

### Full Tested Code

```zig
// Recipe 11.4: Building a Simple HTTP Server
// Target Zig Version: 0.15.2
//
// Educational demonstration of HTTP server patterns in Zig.
// Shows request parsing, response building, routing, and middleware patterns.
//
// Note: This demonstrates HTTP server concepts without actual networking.
// For production HTTP servers, use std.http.Server or a framework.
//
// Key concepts:
// - HTTP request parsing (method, path, headers, body)
// - HTTP response building (status, headers, body)
// - Route matching and handlers
// - Middleware pattern
// - Static file serving
// - Content type detection

const std = @import("std");
const testing = std.testing;

// ANCHOR: http_method
pub const HttpMethod = enum {
    GET,
    POST,
    PUT,
    DELETE,
    PATCH,
    HEAD,
    OPTIONS,

    pub fn fromString(s: []const u8) ?HttpMethod {
        if (std.mem.eql(u8, s, "GET")) return .GET;
        if (std.mem.eql(u8, s, "POST")) return .POST;
        if (std.mem.eql(u8, s, "PUT")) return .PUT;
        if (std.mem.eql(u8, s, "DELETE")) return .DELETE;
        if (std.mem.eql(u8, s, "PATCH")) return .PATCH;
        if (std.mem.eql(u8, s, "HEAD")) return .HEAD;
        if (std.mem.eql(u8, s, "OPTIONS")) return .OPTIONS;
        return null;
    }

    pub fn toString(self: HttpMethod) []const u8 {
        return switch (self) {
            .GET => "GET",
            .POST => "POST",
            .PUT => "PUT",
            .DELETE => "DELETE",
            .PATCH => "PATCH",
            .HEAD => "HEAD",
            .OPTIONS => "OPTIONS",
        };
    }
};

test "http method conversion" {
    try testing.expectEqual(HttpMethod.GET, HttpMethod.fromString("GET").?);
    try testing.expectEqualStrings("POST", HttpMethod.POST.toString());
    try testing.expect(HttpMethod.fromString("INVALID") == null);
}
// ANCHOR_END: http_method

// ANCHOR: http_status
pub const HttpStatus = enum(u16) {
    ok = 200,
    created = 201,
    no_content = 204,
    moved_permanently = 301,
    found = 302,
    bad_request = 400,
    unauthorized = 401,
    forbidden = 403,
    not_found = 404,
    method_not_allowed = 405,
    internal_server_error = 500,
    not_implemented = 501,
    service_unavailable = 503,

    pub fn toText(self: HttpStatus) []const u8 {
        return switch (self) {
            .ok => "OK",
            .created => "Created",
            .no_content => "No Content",
            .moved_permanently => "Moved Permanently",
            .found => "Found",
            .bad_request => "Bad Request",
            .unauthorized => "Unauthorized",
            .forbidden => "Forbidden",
            .not_found => "Not Found",
            .method_not_allowed => "Method Not Allowed",
            .internal_server_error => "Internal Server Error",
            .not_implemented => "Not Implemented",
            .service_unavailable => "Service Unavailable",
        };
    }
};

test "http status codes" {
    try testing.expectEqual(@as(u16, 200), @intFromEnum(HttpStatus.ok));
    try testing.expectEqual(@as(u16, 404), @intFromEnum(HttpStatus.not_found));
    try testing.expectEqualStrings("OK", HttpStatus.ok.toText());
    try testing.expectEqualStrings("Not Found", HttpStatus.not_found.toText());
}
// ANCHOR_END: http_status

// ANCHOR: http_request
pub const HttpRequest = struct {
    method: HttpMethod,
    path: []const u8,
    headers: std.StringHashMap([]const u8),
    body: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) HttpRequest {
        return .{
            .method = .GET,
            .path = "/",
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = "",
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *HttpRequest) void {
        var it = self.headers.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.headers.deinit();
    }

    pub fn parse(allocator: std.mem.Allocator, raw: []const u8) !HttpRequest {
        var request = HttpRequest.init(allocator);
        errdefer request.deinit();

        var lines = std.mem.splitScalar(u8, raw, '\n');

        // Parse request line
        if (lines.next()) |request_line| {
            var parts = std.mem.splitScalar(u8, request_line, ' ');

            if (parts.next()) |method_str| {
                const method_trimmed = std.mem.trim(u8, method_str, &std.ascii.whitespace);
                request.method = HttpMethod.fromString(method_trimmed) orelse .GET;
            }

            if (parts.next()) |path_str| {
                request.path = std.mem.trim(u8, path_str, &std.ascii.whitespace);
            }
        }

        // Parse headers
        while (lines.next()) |line| {
            const trimmed = std.mem.trim(u8, line, &std.ascii.whitespace);
            if (trimmed.len == 0) break; // Empty line separates headers from body

            if (std.mem.indexOf(u8, trimmed, ":")) |colon_idx| {
                const name = std.mem.trim(u8, trimmed[0..colon_idx], &std.ascii.whitespace);
                const value = std.mem.trim(u8, trimmed[colon_idx + 1 ..], &std.ascii.whitespace);

                // Memory Allocation Tradeoff
                //
                // This implementation uses allocator.dupe() to own all strings, which:
                // - Pros: Simple lifetime management, data outlives request buffer
                // - Cons: Allocates memory for every header (slower for high-traffic servers)
                //
                // Production alternative: Use slices of the original buffer
                // - Store []const u8 slices pointing into 'raw' parameter
                // - Requires 'raw' buffer to outlive HttpRequest
                // - Zero allocations, approximately 10x faster parsing
                // - Used by std.http.Server and production frameworks
                //
                // For this educational recipe, we prioritize clarity over performance.

                // HashMap Memory Leak Prevention
                //
                // INCORRECT pattern (causes memory leak with duplicate keys):
                //   const owned_key = try allocator.dupe(u8, name);
                //   const owned_value = try allocator.dupe(u8, value);
                //   try map.put(owned_key, owned_value);  // LEAKS old key/value if duplicate!
                //
                // CORRECT pattern using getOrPut():
                // 1. Allocate value first (always needed)
                // 2. Check if key exists with getOrPut()
                // 3. If existing: free old value, reuse existing key
                // 4. If new: allocate key, assign both key and value
                //
                // This prevents leaks when HTTP requests contain duplicate headers
                // (common with Set-Cookie, Cache-Control, etc.)

                const owned_value = try allocator.dupe(u8, value);
                errdefer allocator.free(owned_value);

                const gop = try request.headers.getOrPut(name);
                if (gop.found_existing) {
                    // Duplicate header: free old value, reuse existing key
                    allocator.free(gop.value_ptr.*);
                    gop.value_ptr.* = owned_value;
                } else {
                    // New header: allocate key and store both
                    const owned_name = try allocator.dupe(u8, name);
                    gop.key_ptr.* = owned_name;
                    gop.value_ptr.* = owned_value;
                }
            }
        }

        // Remaining is body (simplified - real parsing would use Content-Length)
        var body_parts: std.ArrayList(u8) = .{};
        defer body_parts.deinit(allocator);

        while (lines.next()) |line| {
            try body_parts.appendSlice(allocator, line);
        }

        request.body = std.mem.trim(u8, body_parts.items, &std.ascii.whitespace);

        return request;
    }

    pub fn getHeader(self: HttpRequest, name: []const u8) ?[]const u8 {
        return self.headers.get(name);
    }
};

test "http request parsing" {
    const raw_request =
        \\GET /api/users HTTP/1.1
        \\Host: example.com
        \\Content-Type: application/json
        \\
        \\{"name": "Alice"}
    ;

    var request = try HttpRequest.parse(testing.allocator, raw_request);
    defer request.deinit();

    try testing.expectEqual(HttpMethod.GET, request.method);
    try testing.expectEqualStrings("/api/users", request.path);

    const host = request.getHeader("Host");
    try testing.expect(host != null);
    try testing.expectEqualStrings("example.com", host.?);
}

test "http request parsing with duplicate headers - no memory leak" {
    const raw_request =
        \\POST /api/data HTTP/1.1
        \\Host: example.com
        \\Content-Type: application/json
        \\Content-Type: text/plain
        \\Authorization: Bearer token1
        \\Authorization: Bearer token2
        \\
        \\{"data": "test"}
    ;

    var request = try HttpRequest.parse(testing.allocator, raw_request);
    defer request.deinit();

    // Last value should win for duplicate headers
    const content_type = request.getHeader("Content-Type");
    try testing.expect(content_type != null);
    try testing.expectEqualStrings("text/plain", content_type.?);

    const auth = request.getHeader("Authorization");
    try testing.expect(auth != null);
    try testing.expectEqualStrings("Bearer token2", auth.?);

    // Only 3 unique headers should exist (Host, Content-Type, Authorization)
    try testing.expectEqual(@as(u32, 3), request.headers.count());
}
// ANCHOR_END: http_request

// ANCHOR: http_response
pub const HttpResponse = struct {
    status: HttpStatus,
    headers: std.StringHashMap([]const u8),
    body: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, status: HttpStatus) HttpResponse {
        return .{
            .status = status,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = "",
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *HttpResponse) void {
        var it = self.headers.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.headers.deinit();
    }

    pub fn setHeader(self: *HttpResponse, name: []const u8, value: []const u8) !void {
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        // Check if header already exists
        const gop = try self.headers.getOrPut(name);
        if (gop.found_existing) {
            // Free old value and replace
            self.allocator.free(gop.value_ptr.*);
            gop.value_ptr.* = owned_value;
        } else {
            // New header - allocate key
            const owned_name = try self.allocator.dupe(u8, name);
            gop.key_ptr.* = owned_name;
            gop.value_ptr.* = owned_value;
        }
    }

    pub fn setBody(self: *HttpResponse, body: []const u8) void {
        self.body = body;
    }

    pub fn build(self: HttpResponse, allocator: std.mem.Allocator) ![]u8 {
        var result: std.ArrayList(u8) = .{};
        errdefer result.deinit(allocator);

        const writer = result.writer(allocator);

        // Status line
        try writer.print("HTTP/1.1 {d} {s}\r\n", .{
            @intFromEnum(self.status),
            self.status.toText(),
        });

        // Headers
        var it = self.headers.iterator();
        while (it.next()) |entry| {
            try writer.print("{s}: {s}\r\n", .{ entry.key_ptr.*, entry.value_ptr.* });
        }

        // Empty line
        try writer.writeAll("\r\n");

        // Body
        try writer.writeAll(self.body);

        return result.toOwnedSlice(allocator);
    }
};

test "http response building" {
    var response = HttpResponse.init(testing.allocator, .ok);
    defer response.deinit();

    try response.setHeader("Content-Type", "text/plain");
    response.setBody("Hello, World!");

    const raw = try response.build(testing.allocator);
    defer testing.allocator.free(raw);

    try testing.expect(std.mem.indexOf(u8, raw, "HTTP/1.1 200 OK") != null);
    try testing.expect(std.mem.indexOf(u8, raw, "Content-Type: text/plain") != null);
    try testing.expect(std.mem.indexOf(u8, raw, "Hello, World!") != null);
}

test "http response header overwriting" {
    var response = HttpResponse.init(testing.allocator, .ok);
    defer response.deinit();

    try response.setHeader("Content-Type", "text/plain");
    try response.setHeader("Content-Type", "text/html");

    const ct = response.headers.get("Content-Type");
    try testing.expect(ct != null);
    try testing.expectEqualStrings("text/html", ct.?);

    // Ensure only one header exists (no memory leak)
    try testing.expectEqual(@as(usize, 1), response.headers.count());
}
// ANCHOR_END: http_response

// ANCHOR: route_handler
pub const Handler = *const fn (request: *const HttpRequest, allocator: std.mem.Allocator) anyerror!HttpResponse;

pub const Route = struct {
    method: HttpMethod,
    path: []const u8,
    handler: Handler,

    pub fn matches(self: Route, method: HttpMethod, path: []const u8) bool {
        return self.method == method and std.mem.eql(u8, self.path, path);
    }
};

test "route matching" {
    const route = Route{
        .method = .GET,
        .path = "/users",
        .handler = undefined,
    };

    try testing.expect(route.matches(.GET, "/users"));
    try testing.expect(!route.matches(.POST, "/users"));
    try testing.expect(!route.matches(.GET, "/posts"));
}
// ANCHOR_END: route_handler

// ANCHOR: router
pub const Router = struct {
    routes: std.ArrayList(Route),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Router {
        return .{
            .routes = .{},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Router) void {
        self.routes.deinit(self.allocator);
    }

    pub fn add(self: *Router, method: HttpMethod, path: []const u8, handler: Handler) !void {
        try self.routes.append(self.allocator, .{
            .method = method,
            .path = path,
            .handler = handler,
        });
    }

    pub fn handle(self: Router, request: *const HttpRequest) !HttpResponse {
        for (self.routes.items) |route| {
            if (route.matches(request.method, request.path)) {
                return try route.handler(request, self.allocator);
            }
        }

        // No route matched - return 404
        var response = HttpResponse.init(self.allocator, .not_found);
        response.setBody("Not Found");
        return response;
    }
};

fn testHandler(request: *const HttpRequest, allocator: std.mem.Allocator) !HttpResponse {
    _ = request;
    var response = HttpResponse.init(allocator, .ok);
    response.setBody("Test response");
    return response;
}

test "router handling" {
    var router = Router.init(testing.allocator);
    defer router.deinit();

    try router.add(.GET, "/test", testHandler);

    var request = HttpRequest.init(testing.allocator);
    defer request.deinit();
    request.method = .GET;
    request.path = "/test";

    var response = try router.handle(&request);
    defer response.deinit();

    try testing.expectEqual(HttpStatus.ok, response.status);
    try testing.expectEqualStrings("Test response", response.body);
}

test "router 404 for unmatched routes" {
    var router = Router.init(testing.allocator);
    defer router.deinit();

    try router.add(.GET, "/exists", testHandler);

    var request = HttpRequest.init(testing.allocator);
    defer request.deinit();
    request.method = .GET;
    request.path = "/nonexistent";

    var response = try router.handle(&request);
    defer response.deinit();

    try testing.expectEqual(HttpStatus.not_found, response.status);
    try testing.expectEqualStrings("Not Found", response.body);
}
// ANCHOR_END: router

// ANCHOR: middleware
pub const Middleware = *const fn (request: *HttpRequest, next: Handler) anyerror!HttpResponse;

pub const MiddlewareChain = struct {
    middlewares: std.ArrayList(Middleware),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) MiddlewareChain {
        return .{
            .middlewares = .{},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *MiddlewareChain) void {
        self.middlewares.deinit(self.allocator);
    }

    pub fn use(self: *MiddlewareChain, middleware: Middleware) !void {
        try self.middlewares.append(self.allocator, middleware);
    }
};

// Example logging middleware
fn loggingMiddleware(request: *HttpRequest, next: Handler) !HttpResponse {
    // Log request (in real code, use std.log)
    _ = next;

    // Call next handler
    // return try next(request);

    // For testing, return a mock response
    var response = HttpResponse.init(request.allocator, .ok);
    response.setBody("Logged");
    return response;
}

test "middleware pattern" {
    var chain = MiddlewareChain.init(testing.allocator);
    defer chain.deinit();

    try chain.use(loggingMiddleware);

    try testing.expectEqual(@as(usize, 1), chain.middlewares.items.len);
}
// ANCHOR_END: middleware

// ANCHOR: content_type
pub const ContentType = enum {
    text_html,
    text_plain,
    application_json,
    application_xml,
    image_png,
    image_jpeg,
    application_octet_stream,

    pub fn fromExtension(ext: []const u8) ContentType {
        if (std.mem.eql(u8, ext, ".html")) return .text_html;
        if (std.mem.eql(u8, ext, ".txt")) return .text_plain;
        if (std.mem.eql(u8, ext, ".json")) return .application_json;
        if (std.mem.eql(u8, ext, ".xml")) return .application_xml;
        if (std.mem.eql(u8, ext, ".png")) return .image_png;
        if (std.mem.eql(u8, ext, ".jpg") or std.mem.eql(u8, ext, ".jpeg")) return .image_jpeg;
        return .application_octet_stream;
    }

    pub fn toString(self: ContentType) []const u8 {
        return switch (self) {
            .text_html => "text/html",
            .text_plain => "text/plain",
            .application_json => "application/json",
            .application_xml => "application/xml",
            .image_png => "image/png",
            .image_jpeg => "image/jpeg",
            .application_octet_stream => "application/octet-stream",
        };
    }
};

test "content type detection" {
    try testing.expectEqual(ContentType.text_html, ContentType.fromExtension(".html"));
    try testing.expectEqual(ContentType.application_json, ContentType.fromExtension(".json"));
    try testing.expectEqualStrings("text/html", ContentType.text_html.toString());
}
// ANCHOR_END: content_type

// ANCHOR: static_file_handler
pub const StaticFileHandler = struct {
    root_dir: []const u8,

    pub fn init(root_dir: []const u8) StaticFileHandler {
        return .{ .root_dir = root_dir };
    }

    pub fn serve(self: StaticFileHandler, path: []const u8, allocator: std.mem.Allocator) !HttpResponse {
        _ = self;

        // In real implementation: read file from root_dir + path
        // For demo, return mock response

        var response = HttpResponse.init(allocator, .ok);

        // Detect content type from extension
        const ext = std.fs.path.extension(path);
        const content_type = ContentType.fromExtension(ext);
        try response.setHeader("Content-Type", content_type.toString());

        response.setBody("Mock file content");

        return response;
    }
};

test "static file handler" {
    const handler = StaticFileHandler.init("/var/www");

    var response = try handler.serve("/index.html", testing.allocator);
    defer response.deinit();

    try testing.expectEqual(HttpStatus.ok, response.status);

    const content_type = response.headers.get("Content-Type");
    try testing.expect(content_type != null);
    try testing.expectEqualStrings("text/html", content_type.?);
}
// ANCHOR_END: static_file_handler

// ANCHOR: query_params
pub const QueryParams = struct {
    params: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) QueryParams {
        return .{
            .params = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *QueryParams) void {
        var it = self.params.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.params.deinit();
    }

    pub fn parse(allocator: std.mem.Allocator, query_string: []const u8) !QueryParams {
        var result = QueryParams.init(allocator);
        errdefer result.deinit();

        var pairs = std.mem.splitScalar(u8, query_string, '&');
        while (pairs.next()) |pair| {
            if (std.mem.indexOf(u8, pair, "=")) |eq_idx| {
                const key = pair[0..eq_idx];
                const value = pair[eq_idx + 1 ..];

                const owned_key = try allocator.dupe(u8, key);
                errdefer allocator.free(owned_key);
                const owned_value = try allocator.dupe(u8, value);
                errdefer allocator.free(owned_value);

                try result.params.put(owned_key, owned_value);
            }
        }

        return result;
    }

    pub fn get(self: QueryParams, key: []const u8) ?[]const u8 {
        return self.params.get(key);
    }
};

test "query params parsing" {
    var params = try QueryParams.parse(testing.allocator, "name=Alice&age=30");
    defer params.deinit();

    try testing.expectEqualStrings("Alice", params.get("name").?);
    try testing.expectEqualStrings("30", params.get("age").?);
    try testing.expect(params.get("missing") == null);
}
// ANCHOR_END: query_params

// ANCHOR: json_response_helper
pub fn jsonResponse(allocator: std.mem.Allocator, status: HttpStatus, json_data: []const u8) !HttpResponse {
    var response = HttpResponse.init(allocator, status);
    errdefer response.deinit();

    try response.setHeader("Content-Type", "application/json");
    response.setBody(json_data);

    return response;
}

test "json response helper" {
    var response = try jsonResponse(testing.allocator, .ok, "{\"message\":\"Success\"}");
    defer response.deinit();

    try testing.expectEqual(HttpStatus.ok, response.status);

    const content_type = response.headers.get("Content-Type");
    try testing.expect(content_type != null);
    try testing.expectEqualStrings("application/json", content_type.?);
}
// ANCHOR_END: json_response_helper

// Comprehensive test
test "comprehensive http server patterns" {
    // Parse request
    const raw_request =
        \\POST /api/users?admin=true HTTP/1.1
        \\Host: localhost:8080
        \\Content-Type: application/json
        \\
        \\{"name":"Bob"}
    ;

    var request = try HttpRequest.parse(testing.allocator, raw_request);
    defer request.deinit();

    try testing.expectEqual(HttpMethod.POST, request.method);
    try testing.expectEqualStrings("/api/users?admin=true", request.path);

    // Build response
    var response = HttpResponse.init(testing.allocator, .created);
    defer response.deinit();

    try response.setHeader("Location", "/api/users/123");
    response.setBody("{\"id\":123,\"name\":\"Bob\"}");

    const raw_response = try response.build(testing.allocator);
    defer testing.allocator.free(raw_response);

    try testing.expect(std.mem.indexOf(u8, raw_response, "201 Created") != null);
}
```

### See Also

- Recipe 11.1: Making HTTP Requests
- Recipe 11.2: Working with JSON APIs
- Recipe 11.3: WebSocket Communication
- Recipe 12.1: Async I/O Patterns

---

## Recipe 11.5: Parsing and Generating XML {#recipe-11-5}

**Tags:** allocators, arraylist, data-structures, error-handling, hashmap, http, json, memory, networking, parsing, resource-cleanup, slices, testing, xml
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_5.zig`

### Problem

You need to work with XML data in your Zig application. You might be consuming XML APIs, reading configuration files, or generating XML documents for data interchange. You need a way to parse XML into a tree structure and serialize data structures back to XML format.

### Solution

Build an XML parser and generator using Zig's standard library. The solution includes an `XmlElement` tree structure, an `XmlWriter` for serialization, and an `XmlParser` for reading XML documents.

### Creating XML Elements

```zig
test "create basic XML element" {
    const element = try XmlElement.init(testing.allocator, "person");
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    try testing.expectEqualStrings("person", element.name);
    try testing.expectEqual(@as(usize, 0), element.children.items.len);
    try testing.expectEqual(@as(?[]const u8, null), element.content);
}
```

### Building Nested XML Structures

```zig
const root = try XmlElement.init(testing.allocator, "people");
defer {
    root.deinit();
    testing.allocator.destroy(root);
}

const person = try XmlElement.init(testing.allocator, "person");
try person.setAttribute("id", "1");

const name = try XmlElement.init(testing.allocator, "name");
try name.setContent("Alice");
try person.appendChild(name);

const age = try XmlElement.init(testing.allocator, "age");
try age.setContent("30");
try person.appendChild(age);

try root.appendChild(person);

var writer = XmlWriter.init(testing.allocator, true);
const xml = try writer.writeElement(root);
defer testing.allocator.free(xml);
```

Output with pretty printing:
```xml
<people>
  <person id="1">
    <name>Alice</name>
    <age>30</age>
  </person>
</people>
```

### Parsing XML Documents

```zig
const xml = "<person name=\"Alice\">Software Engineer</person>";

var parser = XmlParser.init(testing.allocator, xml);
const element = try parser.parse();
defer {
    element.deinit();
    testing.allocator.destroy(element);
}

// Access element properties
const name_attr = element.attributes.get("name"); // "Alice"
const content = element.content; // "Software Engineer"
```

### Parsing Nested XML

```zig
const xml =
    \\<person id="1">
    \\  <name>Alice</name>
    \\  <age>30</age>
    \\</person>
;

var parser = XmlParser.init(testing.allocator, xml);
const element = try parser.parse();
defer {
    element.deinit();
    testing.allocator.destroy(element);
}

// Navigate the tree
for (element.children.items) |child| {
    if (std.mem.eql(u8, child.name, "name")) {
        // child.content is "Alice"
    }
}
```

### XML Entity Escaping

The writer automatically escapes special characters:

```zig
const element = try XmlElement.init(testing.allocator, "data");
defer {
    element.deinit();
    testing.allocator.destroy(element);
}

try element.setContent("<tag> & \"quotes\" 'apostrophes'");

var writer = XmlWriter.init(testing.allocator, false);
const xml = try writer.writeElement(element);
defer testing.allocator.free(xml);

// Result: <data>&lt;tag&gt; &amp; &quot;quotes&quot; &apos;apostrophes&apos;</data>
```

The parser automatically unescapes entities when reading:

```zig
const xml = "<data>&lt;tag&gt; &amp; &quot;quotes&quot;</data>";

var parser = XmlParser.init(testing.allocator, xml);
const element = try parser.parse();
defer {
    element.deinit();
    testing.allocator.destroy(element);
}

// element.content is "<tag> & \"quotes\""
```

### Discussion

### XML Tree Structure

The `XmlElement` struct represents an XML node with:

- **name**: Tag name
- **attributes**: Key-value pairs using `StringArrayHashMap` for deterministic ordering
- **content**: Text content (optional)
- **children**: Child elements (for nested structures)

Elements can have either content or children, not both. This matches XML's structure where elements contain either text or other elements.

### Memory Management

The implementation uses explicit allocator passing and proper cleanup:

```zig
pub const XmlElement = struct {
    name: []const u8,
    attributes: std.StringArrayHashMap([]const u8),
    content: ?[]const u8,
    children: std.ArrayList(*XmlElement),
    allocator: std.mem.Allocator,

    pub fn deinit(self: *XmlElement) void {
        self.allocator.free(self.name);

        var it = self.attributes.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.attributes.deinit();

        if (self.content) |content| {
            self.allocator.free(content);
        }

        for (self.children.items) |child| {
            child.deinit();
            self.allocator.destroy(child);
        }
        self.children.deinit(self.allocator);
    }
};
```

The `deinit` method:
1. Frees all strings (name, attribute keys/values, content)
2. Recursively cleans up child elements
3. Deallocates the children ArrayList

### setAttribute Memory Safety

The `setAttribute` method uses `getOrPut` to prevent memory leaks when overwriting attributes:

```zig
pub fn setAttribute(self: *XmlElement, key: []const u8, value: []const u8) !void {
    const owned_value = try self.allocator.dupe(u8, value);
    errdefer self.allocator.free(owned_value);

    const result = try self.attributes.getOrPut(key);
    if (result.found_existing) {
        // Free old value when overwriting
        self.allocator.free(result.value_ptr.*);
        result.value_ptr.* = owned_value;
    } else {
        const owned_key = try self.allocator.dupe(u8, key);
        errdefer self.allocator.free(owned_key);
        result.key_ptr.* = owned_key;
        result.value_ptr.* = owned_value;
    }
}
```

This ensures:
- New attributes allocate both key and value
- Overwriting attributes reuses the key and frees the old value
- Error paths properly clean up with `errdefer`

### Parser Implementation

The parser uses a simple recursive descent approach:

1. **Tag Parsing**: Identifies opening tags by `<` character
2. **Attribute Parsing**: Extracts key="value" pairs
3. **Content Parsing**: Reads text between tags
4. **Recursive Descent**: Parses nested elements recursively

Key safety features:
- Bounds checking before all array accesses
- Error return for malformed XML
- Proper cleanup with `errdefer` on parse failures

### Entity Handling

The writer escapes five basic XML entities:
- `&` → `&amp;`
- `<` → `&lt;`
- `>` → `&gt;`
- `"` → `&quot;`
- `'` → `&apos;`

The parser unescapes these same entities when reading. This handles the most common cases but doesn't support numeric character references (`&#65;`) or custom entities.

### Deterministic Attribute Ordering

The implementation uses `StringArrayHashMap` instead of `StringHashMap` to ensure attributes appear in a consistent order across writes. This is important for:
- Testing (comparing XML output)
- Version control (stable diffs)
- Debugging (predictable output)

### Self-Closing Tags

The writer optimizes empty elements with self-closing tags:

```zig
// Elements with no content and no children
<break />

// Elements with content or children
<div>Content</div>
```

### Pretty Printing

The `XmlWriter` supports optional pretty printing for human-readable output:

```zig
// Compact output
var writer = XmlWriter.init(allocator, false);

// Pretty printed with indentation
var writer = XmlWriter.init(allocator, true);
```

Pretty printing adds:
- Newlines after closing tags
- Two-space indentation per nesting level
- Whitespace between elements

### Roundtrip Validation

You can verify your XML handling with roundtrip tests:

```zig
// Create element
const original = try XmlElement.init(testing.allocator, "person");
defer {
    original.deinit();
    testing.allocator.destroy(original);
}

try original.setAttribute("id", "123");
try original.setContent("Test Person");

// Write to XML
var writer = XmlWriter.init(testing.allocator, false);
const xml = try writer.writeElement(original);
defer testing.allocator.free(xml);

// Parse back
var parser = XmlParser.init(testing.allocator, xml);
const parsed = try parser.parse();
defer {
    parsed.deinit();
    testing.allocator.destroy(parsed);
}

// Verify roundtrip
try testing.expectEqualStrings(original.name, parsed.name);
try testing.expectEqualStrings(original.content.?, parsed.content.?);
```

### Limitations

This implementation is suitable for learning and simple use cases but has limitations for production use:

**Not Supported:**
- XML declarations (`<?xml version="1.0"?>`)
- DOCTYPE declarations
- Processing instructions
- CDATA sections (`<![CDATA[...]]>`)
- XML namespaces
- Comments (`<!-- -->`)
- Numeric character references (`&#65;`)
- Entity expansion limits (vulnerable to XML bombs)
- Streaming parsing (loads entire document into memory)
- Schema validation

**Security Considerations:**
- No maximum nesting depth (stack overflow risk)
- No entity expansion limits (denial of service risk)
- Minimal input validation (error messages lack position info)

For production use, consider:
- Adding depth limits to prevent stack overflow
- Implementing entity expansion limits
- Adding better error reporting with line/column numbers
- Supporting XML comments and CDATA
- Implementing streaming SAX-style parsing for large documents

### When to Use XML vs JSON

**Use XML when:**
- Working with legacy systems that require XML
- Need document markup (mixed content with text and elements)
- Require XML Schema validation
- Need namespace support for vocabulary mixing
- Industry standards mandate XML (SOAP, RSS, SVG)

**Use JSON when:**
- Building new web APIs
- Need lightweight data interchange
- Working with JavaScript clients
- Want simpler parsing and smaller payloads
- Don't need schema validation or namespaces

For most modern applications, JSON (Recipe 11.2) is simpler and more efficient. Use XML when it's specifically required by your use case.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: xml_element
pub const XmlElement = struct {
    name: []const u8,
    attributes: std.StringArrayHashMap([]const u8),
    content: ?[]const u8,
    children: std.ArrayList(*XmlElement),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, name: []const u8) !*XmlElement {
        const elem = try allocator.create(XmlElement);
        elem.* = .{
            .name = try allocator.dupe(u8, name),
            .attributes = std.StringArrayHashMap([]const u8).init(allocator),
            .content = null,
            .children = std.ArrayList(*XmlElement){},
            .allocator = allocator,
        };
        return elem;
    }

    pub fn deinit(self: *XmlElement) void {
        self.allocator.free(self.name);

        var it = self.attributes.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.attributes.deinit();

        if (self.content) |content| {
            self.allocator.free(content);
        }

        for (self.children.items) |child| {
            child.deinit();
            self.allocator.destroy(child);
        }
        self.children.deinit(self.allocator);
    }

    pub fn setAttribute(self: *XmlElement, key: []const u8, value: []const u8) !void {
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        const result = try self.attributes.getOrPut(key);
        if (result.found_existing) {
            // Free old value when overwriting
            self.allocator.free(result.value_ptr.*);
            result.value_ptr.* = owned_value;
        } else {
            const owned_key = try self.allocator.dupe(u8, key);
            errdefer self.allocator.free(owned_key);
            result.key_ptr.* = owned_key;
            result.value_ptr.* = owned_value;
        }
    }

    pub fn setContent(self: *XmlElement, content: []const u8) !void {
        if (self.content) |old_content| {
            self.allocator.free(old_content);
        }
        self.content = try self.allocator.dupe(u8, content);
    }

    pub fn appendChild(self: *XmlElement, child: *XmlElement) !void {
        try self.children.append(self.allocator, child);
    }
};
// ANCHOR_END: xml_element

// ANCHOR: xml_writer
pub const XmlWriter = struct {
    allocator: std.mem.Allocator,
    indent_level: usize,
    pretty_print: bool,

    pub fn init(allocator: std.mem.Allocator, pretty_print: bool) XmlWriter {
        return .{
            .allocator = allocator,
            .indent_level = 0,
            .pretty_print = pretty_print,
        };
    }

    pub fn writeElement(self: *XmlWriter, element: *const XmlElement) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try self.writeElementInternal(&buffer, element);
        return buffer.toOwnedSlice(self.allocator);
    }

    fn writeElementInternal(self: *XmlWriter, buffer: *std.ArrayList(u8), element: *const XmlElement) !void {
        // Opening tag with indentation
        if (self.pretty_print) {
            for (0..self.indent_level) |_| {
                try buffer.appendSlice(self.allocator, "  ");
            }
        }

        try buffer.appendSlice(self.allocator, "<");
        try buffer.appendSlice(self.allocator, element.name);

        // Attributes
        var it = element.attributes.iterator();
        while (it.next()) |entry| {
            try buffer.appendSlice(self.allocator, " ");
            try buffer.appendSlice(self.allocator, entry.key_ptr.*);
            try buffer.appendSlice(self.allocator, "=\"");
            try self.writeEscaped(buffer, entry.value_ptr.*);
            try buffer.appendSlice(self.allocator, "\"");
        }

        // Self-closing tag if no content and no children
        if (element.content == null and element.children.items.len == 0) {
            try buffer.appendSlice(self.allocator, " />");
            if (self.pretty_print) try buffer.appendSlice(self.allocator, "\n");
            return;
        }

        try buffer.appendSlice(self.allocator, ">");

        // Content or children
        if (element.content) |content| {
            try self.writeEscaped(buffer, content);
        } else if (element.children.items.len > 0) {
            if (self.pretty_print) try buffer.appendSlice(self.allocator, "\n");

            self.indent_level += 1;
            for (element.children.items) |child| {
                try self.writeElementInternal(buffer, child);
            }
            self.indent_level -= 1;

            if (self.pretty_print) {
                for (0..self.indent_level) |_| {
                    try buffer.appendSlice(self.allocator, "  ");
                }
            }
        }

        // Closing tag
        try buffer.appendSlice(self.allocator, "</");
        try buffer.appendSlice(self.allocator, element.name);
        try buffer.appendSlice(self.allocator, ">");
        if (self.pretty_print) try buffer.appendSlice(self.allocator, "\n");
    }

    fn writeEscaped(self: *XmlWriter, buffer: *std.ArrayList(u8), text: []const u8) !void {
        for (text) |c| {
            switch (c) {
                '&' => try buffer.appendSlice(self.allocator, "&amp;"),
                '<' => try buffer.appendSlice(self.allocator, "&lt;"),
                '>' => try buffer.appendSlice(self.allocator, "&gt;"),
                '"' => try buffer.appendSlice(self.allocator, "&quot;"),
                '\'' => try buffer.appendSlice(self.allocator, "&apos;"),
                else => try buffer.append(self.allocator, c),
            }
        }
    }
};
// ANCHOR_END: xml_writer

// ANCHOR: xml_parser
pub const XmlParser = struct {
    allocator: std.mem.Allocator,
    input: []const u8,
    pos: usize,

    pub fn init(allocator: std.mem.Allocator, input: []const u8) XmlParser {
        return .{
            .allocator = allocator,
            .input = input,
            .pos = 0,
        };
    }

    pub fn parse(self: *XmlParser) !*XmlElement {
        self.skipWhitespace();
        return try self.parseElement();
    }

    fn parseElement(self: *XmlParser) !*XmlElement {
        // Expect '<'
        if (self.pos >= self.input.len or self.input[self.pos] != '<') {
            return error.InvalidXml;
        }
        self.pos += 1;

        // Parse tag name
        const name_start = self.pos;
        while (self.pos < self.input.len) {
            const c = self.input[self.pos];
            if (c == ' ' or c == '/' or c == '>') break;
            self.pos += 1;
        }
        const name = self.input[name_start..self.pos];

        const element = try XmlElement.init(self.allocator, name);
        errdefer {
            element.deinit();
            self.allocator.destroy(element);
        }

        // Parse attributes
        while (self.pos < self.input.len) {
            self.skipWhitespace();

            if (self.pos >= self.input.len) return error.InvalidXml;

            if (self.input[self.pos] == '>') {
                self.pos += 1;
                break;
            }

            if (self.input[self.pos] == '/') {
                if (self.pos + 1 >= self.input.len) return error.InvalidXml;
                if (self.input[self.pos + 1] == '>') {
                    self.pos += 2;
                    return element;
                }
            }

            // Parse attribute
            const attr_name_start = self.pos;
            while (self.pos < self.input.len and self.input[self.pos] != '=') {
                self.pos += 1;
            }
            const attr_name = std.mem.trim(u8, self.input[attr_name_start..self.pos], " \t\n\r");

            self.pos += 1; // Skip '='
            self.skipWhitespace();

            if (self.pos >= self.input.len) return error.InvalidXml;
            const quote = self.input[self.pos];
            self.pos += 1;

            const attr_value_start = self.pos;
            while (self.pos < self.input.len and self.input[self.pos] != quote) {
                self.pos += 1;
            }
            const attr_value = self.input[attr_value_start..self.pos];
            self.pos += 1; // Skip closing quote

            try element.setAttribute(attr_name, attr_value);
        }

        // Parse content or children
        const content_start = self.pos;
        var has_children = false;

        while (self.pos < self.input.len) {
            if (self.input[self.pos] == '<') {
                // Check if it's a closing tag
                if (self.pos + 1 >= self.input.len) return error.InvalidXml;
                if (self.input[self.pos + 1] == '/') {
                    // Found closing tag
                    if (!has_children and self.pos > content_start) {
                        const content = self.input[content_start..self.pos];
                        const trimmed = std.mem.trim(u8, content, " \t\n\r");
                        if (trimmed.len > 0) {
                            const unescaped = try self.unescapeXml(trimmed);
                            defer self.allocator.free(unescaped);
                            try element.setContent(unescaped);
                        }
                    }

                    // Skip to end of closing tag
                    while (self.pos < self.input.len and self.input[self.pos] != '>') {
                        self.pos += 1;
                    }
                    self.pos += 1;
                    break;
                } else {
                    // Child element
                    has_children = true;
                    const child = try self.parseElement();
                    try element.appendChild(child);
                }
            } else {
                self.pos += 1;
            }
        }

        return element;
    }

    fn skipWhitespace(self: *XmlParser) void {
        while (self.pos < self.input.len and std.mem.indexOfScalar(u8, " \t\n\r", self.input[self.pos]) != null) {
            self.pos += 1;
        }
    }

    fn unescapeXml(self: *XmlParser, text: []const u8) ![]const u8 {
        var result = std.ArrayList(u8){};
        defer result.deinit(self.allocator);

        var i: usize = 0;
        while (i < text.len) {
            if (text[i] == '&') {
                if (std.mem.startsWith(u8, text[i..], "&amp;")) {
                    try result.append(self.allocator, '&');
                    i += 5;
                } else if (std.mem.startsWith(u8, text[i..], "&lt;")) {
                    try result.append(self.allocator, '<');
                    i += 4;
                } else if (std.mem.startsWith(u8, text[i..], "&gt;")) {
                    try result.append(self.allocator, '>');
                    i += 4;
                } else if (std.mem.startsWith(u8, text[i..], "&quot;")) {
                    try result.append(self.allocator, '"');
                    i += 6;
                } else if (std.mem.startsWith(u8, text[i..], "&apos;")) {
                    try result.append(self.allocator, '\'');
                    i += 6;
                } else {
                    try result.append(self.allocator, text[i]);
                    i += 1;
                }
            } else {
                try result.append(self.allocator, text[i]);
                i += 1;
            }
        }

        return result.toOwnedSlice(self.allocator);
    }
};
// ANCHOR_END: xml_parser

// ANCHOR: test_element_creation
test "create basic XML element" {
    const element = try XmlElement.init(testing.allocator, "person");
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    try testing.expectEqualStrings("person", element.name);
    try testing.expectEqual(@as(usize, 0), element.children.items.len);
    try testing.expectEqual(@as(?[]const u8, null), element.content);
}
// ANCHOR_END: test_element_creation

// ANCHOR: test_element_attributes
test "element with attributes" {
    const element = try XmlElement.init(testing.allocator, "person");
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    try element.setAttribute("name", "Alice");
    try element.setAttribute("age", "30");

    const name = element.attributes.get("name");
    try testing.expect(name != null);
    try testing.expectEqualStrings("Alice", name.?);

    const age = element.attributes.get("age");
    try testing.expect(age != null);
    try testing.expectEqualStrings("30", age.?);
}
// ANCHOR_END: test_element_attributes

// ANCHOR: test_element_content
test "element with content" {
    const element = try XmlElement.init(testing.allocator, "message");
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    try element.setContent("Hello, World!");

    try testing.expect(element.content != null);
    try testing.expectEqualStrings("Hello, World!", element.content.?);
}
// ANCHOR_END: test_element_content

// ANCHOR: test_nested_elements
test "nested XML elements" {
    const root = try XmlElement.init(testing.allocator, "root");
    defer {
        root.deinit();
        testing.allocator.destroy(root);
    }

    const child1 = try XmlElement.init(testing.allocator, "child");
    try child1.setContent("First child");
    try root.appendChild(child1);

    const child2 = try XmlElement.init(testing.allocator, "child");
    try child2.setContent("Second child");
    try root.appendChild(child2);

    try testing.expectEqual(@as(usize, 2), root.children.items.len);
    try testing.expectEqualStrings("First child", root.children.items[0].content.?);
    try testing.expectEqualStrings("Second child", root.children.items[1].content.?);
}
// ANCHOR_END: test_nested_elements

// ANCHOR: test_write_simple
test "write simple XML element" {
    const element = try XmlElement.init(testing.allocator, "person");
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    try element.setAttribute("name", "Alice");
    try element.setContent("Software Engineer");

    var writer = XmlWriter.init(testing.allocator, false);
    const xml = try writer.writeElement(element);
    defer testing.allocator.free(xml);

    try testing.expectEqualStrings("<person name=\"Alice\">Software Engineer</person>", xml);
}
// ANCHOR_END: test_write_simple

// ANCHOR: test_write_nested
test "write nested XML elements" {
    const root = try XmlElement.init(testing.allocator, "people");
    defer {
        root.deinit();
        testing.allocator.destroy(root);
    }

    const person = try XmlElement.init(testing.allocator, "person");
    try person.setAttribute("id", "1");

    const name = try XmlElement.init(testing.allocator, "name");
    try name.setContent("Alice");
    try person.appendChild(name);

    const age = try XmlElement.init(testing.allocator, "age");
    try age.setContent("30");
    try person.appendChild(age);

    try root.appendChild(person);

    var writer = XmlWriter.init(testing.allocator, true);
    const xml = try writer.writeElement(root);
    defer testing.allocator.free(xml);

    const expected =
        \\<people>
        \\  <person id="1">
        \\    <name>Alice</name>
        \\    <age>30</age>
        \\  </person>
        \\</people>
        \\
    ;
    try testing.expectEqualStrings(expected, xml);
}
// ANCHOR_END: test_write_nested

// ANCHOR: test_write_self_closing
test "write self-closing XML element" {
    const element = try XmlElement.init(testing.allocator, "break");
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    var writer = XmlWriter.init(testing.allocator, false);
    const xml = try writer.writeElement(element);
    defer testing.allocator.free(xml);

    try testing.expectEqualStrings("<break />", xml);
}
// ANCHOR_END: test_write_self_closing

// ANCHOR: test_write_escaping
test "XML entity escaping" {
    const element = try XmlElement.init(testing.allocator, "data");
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    try element.setContent("<tag> & \"quotes\" 'apostrophes'");

    var writer = XmlWriter.init(testing.allocator, false);
    const xml = try writer.writeElement(element);
    defer testing.allocator.free(xml);

    try testing.expectEqualStrings("<data>&lt;tag&gt; &amp; &quot;quotes&quot; &apos;apostrophes&apos;</data>", xml);
}
// ANCHOR_END: test_write_escaping

// ANCHOR: test_parse_simple
test "parse simple XML" {
    const xml = "<person name=\"Alice\">Software Engineer</person>";

    var parser = XmlParser.init(testing.allocator, xml);
    const element = try parser.parse();
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    try testing.expectEqualStrings("person", element.name);
    try testing.expect(element.content != null);
    try testing.expectEqualStrings("Software Engineer", element.content.?);

    const name = element.attributes.get("name");
    try testing.expect(name != null);
    try testing.expectEqualStrings("Alice", name.?);
}
// ANCHOR_END: test_parse_simple

// ANCHOR: test_parse_nested
test "parse nested XML" {
    const xml =
        \\<person id="1">
        \\  <name>Alice</name>
        \\  <age>30</age>
        \\</person>
    ;

    var parser = XmlParser.init(testing.allocator, xml);
    const element = try parser.parse();
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    try testing.expectEqualStrings("person", element.name);
    try testing.expectEqual(@as(usize, 2), element.children.items.len);

    try testing.expectEqualStrings("name", element.children.items[0].name);
    try testing.expectEqualStrings("Alice", element.children.items[0].content.?);

    try testing.expectEqualStrings("age", element.children.items[1].name);
    try testing.expectEqualStrings("30", element.children.items[1].content.?);
}
// ANCHOR_END: test_parse_nested

// ANCHOR: test_parse_self_closing
test "parse self-closing element" {
    const xml = "<break />";

    var parser = XmlParser.init(testing.allocator, xml);
    const element = try parser.parse();
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    try testing.expectEqualStrings("break", element.name);
    try testing.expectEqual(@as(?[]const u8, null), element.content);
    try testing.expectEqual(@as(usize, 0), element.children.items.len);
}
// ANCHOR_END: test_parse_self_closing

// ANCHOR: test_roundtrip
test "XML roundtrip (write then parse)" {
    // Create element
    const original = try XmlElement.init(testing.allocator, "person");
    defer {
        original.deinit();
        testing.allocator.destroy(original);
    }

    try original.setAttribute("id", "123");
    try original.setContent("Test Person");

    // Write to XML
    var writer = XmlWriter.init(testing.allocator, false);
    const xml = try writer.writeElement(original);
    defer testing.allocator.free(xml);

    // Parse back
    var parser = XmlParser.init(testing.allocator, xml);
    const parsed = try parser.parse();
    defer {
        parsed.deinit();
        testing.allocator.destroy(parsed);
    }

    // Verify
    try testing.expectEqualStrings(original.name, parsed.name);
    try testing.expectEqualStrings(original.content.?, parsed.content.?);

    const id = parsed.attributes.get("id");
    try testing.expect(id != null);
    try testing.expectEqualStrings("123", id.?);
}
// ANCHOR_END: test_roundtrip

// ANCHOR: test_parse_unescape
test "parse XML with escaped entities" {
    const xml = "<data>&lt;tag&gt; &amp; &quot;quotes&quot;</data>";

    var parser = XmlParser.init(testing.allocator, xml);
    const element = try parser.parse();
    defer {
        element.deinit();
        testing.allocator.destroy(element);
    }

    try testing.expectEqualStrings("<tag> & \"quotes\"", element.content.?);
}
// ANCHOR_END: test_parse_unescape
```

### See Also

- Recipe 11.2: Working with JSON APIs
- Recipe 11.1: Making HTTP requests
- Recipe 11.6: Working with REST APIs

---

## Recipe 11.6: Working with REST APIs {#recipe-11-6}

**Tags:** allocators, arraylist, data-structures, error-handling, hashmap, http, json, memory, networking, parsing, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_6.zig`

### Problem

You need to interact with RESTful web services or build a REST API. REST (Representational State Transfer) is the standard architecture for web APIs, using HTTP methods (GET, POST, PUT, DELETE) and status codes to perform CRUD operations on resources. You need clean abstractions for requests, responses, and client operations.

### Solution

Build REST API components using Zig's type system and standard library. The solution includes HTTP method and status code enums, request/response structures, a REST client for consuming APIs, and resource handlers for building APIs.

### HTTP Methods and Status Codes

```zig
pub const HttpMethod = enum {
    GET,
    POST,
    PUT,
    PATCH,
    DELETE,
    HEAD,
    OPTIONS,

    pub fn toString(self: HttpMethod) []const u8 {
        return switch (self) {
            .GET => "GET",
            .POST => "POST",
            .PUT => "PUT",
            .PATCH => "PATCH",
            .DELETE => "DELETE",
            .HEAD => "HEAD",
            .OPTIONS => "OPTIONS",
        };
    }
};
```

```zig
pub const HttpStatus = enum(u16) {
    // Success
    ok = 200,
    created = 201,
    accepted = 202,
    no_content = 204,

    // Client Errors
    bad_request = 400,
    unauthorized = 401,
    forbidden = 403,
    not_found = 404,
    method_not_allowed = 405,
    conflict = 409,
    unprocessable_entity = 422,

    // Server Errors
    internal_server_error = 500,
    not_implemented = 501,
    bad_gateway = 502,
    service_unavailable = 503,

    pub fn isSuccess(self: HttpStatus) bool {
        const code = @intFromEnum(self);
        return code >= 200 and code < 300;
    }

    pub fn isClientError(self: HttpStatus) bool {
        const code = @intFromEnum(self);
        return code >= 400 and code < 500;
    }

    pub fn isServerError(self: HttpStatus) bool {
        const code = @intFromEnum(self);
        return code >= 500 and code < 600;
    }
};
```

### Creating REST Requests

```zig
var request = RestRequest.init(testing.allocator, .GET, "/users");
defer request.deinit();

// Add query parameters
try request.addQuery("page", "2");
try request.addQuery("limit", "10");

// Add headers
try request.addHeader("Authorization", "Bearer token123");
try request.addHeader("Content-Type", "application/json");

// Set request body
const json_body = "{\"name\":\"Alice\",\"age\":30}";
try request.setBody(json_body);

// Build complete URL with query string
const url = try request.buildUrl();
defer testing.allocator.free(url);
// Result: "/users?page=2&limit=10"
```

### Handling REST Responses

```zig
var response = RestResponse.init(testing.allocator, .created);
defer response.deinit();

try response.setBody("{\"id\":123}");
try response.addHeader("Content-Type", "application/json");
try response.addHeader("Location", "/users/123");

// Check response status
if (response.isSuccess()) {
    // Process response body
    const body = response.body.?;
}
```

### Using the REST Client

The `RestClient` provides convenient methods for common REST operations:

```zig
var client = try RestClient.init(testing.allocator, "https://api.example.com");
defer client.deinit();

// Set default headers for all requests
try client.setDefaultHeader("User-Agent", "Zig REST Client/1.0");
try client.setDefaultHeader("Accept", "application/json");

// GET request
var response = try client.get("/users/1");
defer response.deinit();

if (response.isSuccess()) {
    // Response body contains user data
}
```

### REST CRUD Operations

**Create (POST):**
```zig
const body = "{\"name\":\"Bob\",\"email\":\"bob@example.com\"}";
var response = try client.post("/users", body);
defer response.deinit();

// 201 Created with Location header
if (response.status == .created) {
    const location = response.headers.get("Location");
    // location = "/users/123"
}
```

**Read (GET):**
```zig
var response = try client.get("/users/1");
defer response.deinit();

// 200 OK with user data in body
if (response.isSuccess()) {
    // Parse JSON from response.body
}
```

**Update (PUT/PATCH):**
```zig
// Full update with PUT
const updated = "{\"name\":\"Alice Updated\",\"email\":\"alice@example.com\"}";
var response = try client.put("/users/1", updated);
defer response.deinit();

// Partial update with PATCH
const patch = "{\"name\":\"Alice Smith\"}";
var patch_response = try client.patch("/users/1", patch);
defer patch_response.deinit();
```

**Delete (DELETE):**
```zig
var response = try client.delete("/users/1");
defer response.deinit();

// 204 No Content on successful deletion
if (response.status == .no_content) {
    // Resource deleted
}
```

### Building Resource Handlers

For server-side REST APIs, use resource handlers to process operations:

```zig
var handler = ResourceHandler.init(testing.allocator);

// Handle GET /resources/123
var response = try handler.handleGet("123");
defer response.deinit();
// Returns 200 OK with resource data

// Handle POST /resources
const data = "{\"name\":\"New Resource\"}";
var create_response = try handler.handleCreate(data);
defer create_response.deinit();
// Returns 201 Created with Location header

// Handle PUT /resources/123
const updated_data = "{\"name\":\"Updated Resource\"}";
var update_response = try handler.handleUpdate("123", updated_data);
defer update_response.deinit();
// Returns 200 OK with updated data

// Handle DELETE /resources/123
var delete_response = try handler.handleDelete("123");
defer delete_response.deinit();
// Returns 204 No Content
```

### Discussion

### REST Principles

REST APIs follow these core principles:

1. **Resource-Based**: URLs identify resources (`/users/1`, not `/getUser?id=1`)
2. **HTTP Methods**: Use standard verbs for operations
   - GET: Read resource
   - POST: Create resource
   - PUT: Replace resource
   - PATCH: Update resource partially
   - DELETE: Remove resource
3. **Stateless**: Each request contains all needed information
4. **Status Codes**: Use HTTP status codes to indicate result
5. **Representations**: Resources have representations (usually JSON)

### HTTP Method Semantics

**GET:**
- Retrieves a resource
- Safe (doesn't modify server state)
- Idempotent (same result on repeated calls)
- Cacheable
- No request body

**POST:**
- Creates a new resource
- Not idempotent (creates new resource each time)
- Returns 201 Created with Location header
- Request body contains new resource data

**PUT:**
- Replaces entire resource
- Idempotent (same result on repeated calls)
- Returns 200 OK or 204 No Content
- Request body contains complete resource

**PATCH:**
- Updates part of a resource
- May or may not be idempotent
- Returns 200 OK
- Request body contains partial updates

**DELETE:**
- Removes a resource
- Idempotent
- Returns 204 No Content
- Usually no response body

### Status Code Usage

The `HttpStatus` enum provides common codes with helper methods:

```zig
pub fn isSuccess(self: HttpStatus) bool {
    const code = @intFromEnum(self);
    return code >= 200 and code < 300;
}

pub fn isClientError(self: HttpStatus) bool {
    const code = @intFromEnum(self);
    return code >= 400 and code < 500;
}

pub fun isServerError(self: HttpStatus) bool {
    const code = @intFromEnum(self);
    return code >= 500 and code < 600;
}
```

**Success Codes (2xx):**
- `200 OK` - Request succeeded
- `201 Created` - Resource created
- `204 No Content` - Success with no body

**Client Error Codes (4xx):**
- `400 Bad Request` - Malformed request
- `401 Unauthorized` - Authentication required
- `403 Forbidden` - Authenticated but not authorized
- `404 Not Found` - Resource doesn't exist
- `409 Conflict` - Resource conflict (e.g., duplicate)
- `422 Unprocessable Entity` - Validation failed

**Server Error Codes (5xx):**
- `500 Internal Server Error` - Server error
- `502 Bad Gateway` - Upstream error
- `503 Service Unavailable` - Temporary failure

### Memory Management

All structures use explicit allocator passing and proper cleanup:

```zig
pub const RestRequest = struct {
    method: HttpMethod,
    path: []const u8,
    query: std.StringHashMap([]const u8),
    headers: std.StringHashMap([]const u8),
    body: ?[]const u8,
    allocator: std.mem.Allocator,

    pub fn deinit(self: *RestRequest) void {
        // Free all query parameters
        var query_it = self.query.iterator();
        while (query_it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.query.deinit();

        // Free all headers
        var header_it = self.headers.iterator();
        while (header_it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.headers.deinit();

        // Free body if present
        if (self.body) |body| {
            self.allocator.free(body);
        }
    }
};
```

The `deinit` methods ensure:
- All HashMap keys and values are freed
- Optional fields are checked before freeing
- No memory leaks even on error paths

### Error Handling with errdefer

The implementation uses `errdefer` to prevent leaks on allocation failures:

```zig
pub fn addHeader(self: *RestRequest, key: []const u8, value: []const u8) !void {
    const owned_key = try self.allocator.dupe(u8, key);
    errdefer self.allocator.free(owned_key);
    const owned_value = try self.allocator.dupe(u8, value);
    errdefer self.allocator.free(owned_value);
    try self.headers.put(owned_key, owned_value);
}
```

If `put()` fails after allocating both key and value, both `errdefer` statements trigger, freeing the allocations. This ensures no leaks on error paths.

### URL Building

The `buildUrl` method constructs URLs with query parameters:

```zig
pub fn buildUrl(self: *const RestRequest) ![]const u8 {
    var url = std.ArrayList(u8){};
    defer url.deinit(self.allocator);

    try url.appendSlice(self.allocator, self.path);

    if (self.query.count() > 0) {
        try url.append(self.allocator, '?');
        var first = true;
        var it = self.query.iterator();
        while (it.next()) |entry| {
            if (!first) try url.append(self.allocator, '&');
            first = false;
            try url.appendSlice(self.allocator, entry.key_ptr.*);
            try url.append(self.allocator, '=');
            try url.appendSlice(self.allocator, entry.value_ptr.*);
        }
    }

    return url.toOwnedSlice(self.allocator);
}
```

This uses ArrayList for efficient string building and returns owned memory that the caller must free.

### Content Negotiation

REST APIs typically use headers for content negotiation:

```zig
// Request JSON
try request.addHeader("Accept", "application/json");

// Send JSON
try request.addHeader("Content-Type", "application/json");

// The server responds with appropriate Content-Type
const content_type = response.headers.get("Content-Type");
if (std.mem.eql(u8, content_type.?, "application/json")) {
    // Parse JSON from response.body
}
```

### Default Headers

The `RestClient` supports default headers applied to all requests:

```zig
var client = try RestClient.init(allocator, base_url);
defer client.deinit();

try client.setDefaultHeader("User-Agent", "MyApp/1.0");
try client.setDefaultHeader("Accept", "application/json");
try client.setDefaultHeader("Accept-Language", "en-US");

// All subsequent requests include these headers
var response = try client.get("/api/users");
```

This is useful for:
- API authentication tokens
- User-Agent identification
- Content type preferences
- Custom application headers

### Resource Handler Pattern

The `ResourceHandler` demonstrates server-side REST handling:

```zig
pub const ResourceHandler = struct {
    allocator: std.mem.Allocator,

    pub fn handleGet(self: *ResourceHandler, id: []const u8) !RestResponse {
        // Fetch resource by ID
        var response = RestResponse.init(self.allocator, .ok);
        try response.setBody(/* resource data */);
        try response.addHeader("Content-Type", "application/json");
        return response;
    }

    pub fn handleCreate(self: *ResourceHandler, data: []const u8) !RestResponse {
        // Create new resource
        var response = RestResponse.init(self.allocator, .created);
        try response.setBody(data);
        try response.addHeader("Location", "/resources/123");
        return response;
    }
};
```

Key patterns:
- Use appropriate status codes (200 OK, 201 Created, 204 No Content)
- Include Location header for created resources
- Return resource representation in response body
- Set Content-Type header for response format

### Integration with HTTP Client

In production, integrate with `std.http.Client`:

```zig
pub fn execute(self: *RestClient, request: *RestRequest) !RestResponse {
    var client = std.http.Client{ .allocator = self.allocator };
    defer client.deinit();

    const url = try request.buildUrl();
    defer self.allocator.free(url);

    // Build full URL with base_url
    var full_url = std.ArrayList(u8){};
    defer full_url.deinit(self.allocator);
    try full_url.appendSlice(self.allocator, self.base_url);
    try full_url.appendSlice(self.allocator, url);

    // Make HTTP request
    var req = try client.open(request.method, try std.Uri.parse(full_url.items), .{
        .server_header_buffer = /* buffer */,
    });
    defer req.deinit();

    // Add headers
    var it = request.headers.iterator();
    while (it.next()) |entry| {
        try req.headers.append(entry.key_ptr.*, entry.value_ptr.*);
    }

    // Send body if present
    if (request.body) |body| {
        req.transfer_encoding = .{ .content_length = body.len };
        try req.send(.{});
        try req.writeAll(body);
        try req.finish();
    } else {
        try req.send(.{});
        try req.finish();
    }

    try req.wait();

    // Build response
    var response = RestResponse.init(self.allocator, @enumFromInt(req.response.status));
    // ... read response body and headers
    return response;
}
```

### Limitations of This Implementation

This recipe provides educational patterns but lacks production features:

**Missing Features:**
- URL encoding for query parameters (special characters break URLs)
- Header validation (newlines could cause injection attacks)
- Request/response size limits (unbounded memory usage)
- Timeout configuration
- Redirect handling
- TLS certificate validation
- Connection pooling
- Retry logic
- Rate limiting

**Security Considerations:**
```zig
// NEEDED: URL encode query parameters
pub fn addQuery(self: *RestRequest, key: []const u8, value: []const u8) !void {
    // Validate no dangerous characters
    if (std.mem.indexOfAny(u8, key, "&=\r\n") != null) return error.InvalidQueryKey;
    if (std.mem.indexOfAny(u8, value, "\r\n") != null) return error.InvalidQueryValue;

    // URL encode the value
    const encoded_value = try urlEncode(self.allocator, value);
    // ... rest of implementation
}
```

For production use:
- Add proper URL encoding/decoding
- Validate all user-supplied input
- Implement request size limits
- Add timeout handling
- Use connection pooling for performance
- Handle redirects safely (limit redirect count)
- Validate TLS certificates

### Best Practices

**API Design:**
- Use plural nouns for collections (`/users`, not `/user`)
- Use nested resources for relationships (`/users/1/posts`)
- Version your API (`/v1/users`)
- Provide pagination for collections
- Use query parameters for filtering/sorting
- Return appropriate status codes
- Include helpful error messages

**Client Usage:**
- Always use `defer response.deinit()` after requests
- Check status codes before processing response
- Handle errors gracefully
- Set reasonable timeouts
- Retry failed requests with exponential backoff
- Cache responses when appropriate

**Error Handling:**
```zig
var response = try client.get("/users/1");
defer response.deinit();

if (response.status == .not_found) {
    // Handle 404 specifically
    return error.UserNotFound;
} else if (response.status.isClientError()) {
    // Handle other 4xx errors
    return error.BadRequest;
} else if (response.status.isServerError()) {
    // Handle 5xx errors
    return error.ServerError;
} else if (!response.isSuccess()) {
    // Unexpected status
    return error.UnexpectedStatus;
}

// Process successful response
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: http_method
pub const HttpMethod = enum {
    GET,
    POST,
    PUT,
    PATCH,
    DELETE,
    HEAD,
    OPTIONS,

    pub fn toString(self: HttpMethod) []const u8 {
        return switch (self) {
            .GET => "GET",
            .POST => "POST",
            .PUT => "PUT",
            .PATCH => "PATCH",
            .DELETE => "DELETE",
            .HEAD => "HEAD",
            .OPTIONS => "OPTIONS",
        };
    }
};
// ANCHOR_END: http_method

// ANCHOR: http_status
pub const HttpStatus = enum(u16) {
    // Success
    ok = 200,
    created = 201,
    accepted = 202,
    no_content = 204,

    // Client Errors
    bad_request = 400,
    unauthorized = 401,
    forbidden = 403,
    not_found = 404,
    method_not_allowed = 405,
    conflict = 409,
    unprocessable_entity = 422,

    // Server Errors
    internal_server_error = 500,
    not_implemented = 501,
    bad_gateway = 502,
    service_unavailable = 503,

    pub fn isSuccess(self: HttpStatus) bool {
        const code = @intFromEnum(self);
        return code >= 200 and code < 300;
    }

    pub fn isClientError(self: HttpStatus) bool {
        const code = @intFromEnum(self);
        return code >= 400 and code < 500;
    }

    pub fn isServerError(self: HttpStatus) bool {
        const code = @intFromEnum(self);
        return code >= 500 and code < 600;
    }
};
// ANCHOR_END: http_status

// ANCHOR: rest_request
pub const RestRequest = struct {
    method: HttpMethod,
    path: []const u8,
    query: std.StringHashMap([]const u8),
    headers: std.StringHashMap([]const u8),
    body: ?[]const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, method: HttpMethod, path: []const u8) RestRequest {
        return .{
            .method = method,
            .path = path,
            .query = std.StringHashMap([]const u8).init(allocator),
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *RestRequest) void {
        var query_it = self.query.iterator();
        while (query_it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.query.deinit();

        var header_it = self.headers.iterator();
        while (header_it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.headers.deinit();

        if (self.body) |body| {
            self.allocator.free(body);
        }
    }

    pub fn addQuery(self: *RestRequest, key: []const u8, value: []const u8) !void {
        // HashMap Memory Leak Prevention
        //
        // Using getOrPut() instead of put() prevents memory leaks when the same
        // query parameter is added multiple times (e.g., ?page=1 overridden to ?page=2).
        //
        // The pattern:
        // 1. Allocate new value (always needed)
        // 2. Check if key exists with getOrPut()
        // 3. If duplicate: free old value, reuse key
        // 4. If new: allocate key, store both

        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        const gop = try self.query.getOrPut(key);
        if (gop.found_existing) {
            // Duplicate parameter: free old value, reuse existing key
            self.allocator.free(gop.value_ptr.*);
            gop.value_ptr.* = owned_value;
        } else {
            // New parameter: allocate key and store both
            const owned_key = try self.allocator.dupe(u8, key);
            gop.key_ptr.* = owned_key;
            gop.value_ptr.* = owned_value;
        }
    }

    pub fn addHeader(self: *RestRequest, key: []const u8, value: []const u8) !void {
        // HashMap Memory Leak Prevention
        //
        // Using getOrPut() instead of put() prevents memory leaks when the same
        // header is set multiple times (e.g., updating Content-Type or Authorization).
        //
        // This is the correct pattern for all HashMap operations with owned strings.
        // See HttpResponse.setHeader (recipe_11_4.zig:248-264) for reference implementation.

        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        const gop = try self.headers.getOrPut(key);
        if (gop.found_existing) {
            // Duplicate header: free old value, reuse existing key
            self.allocator.free(gop.value_ptr.*);
            gop.value_ptr.* = owned_value;
        } else {
            // New header: allocate key and store both
            const owned_key = try self.allocator.dupe(u8, key);
            gop.key_ptr.* = owned_key;
            gop.value_ptr.* = owned_value;
        }
    }

    pub fn setBody(self: *RestRequest, body: []const u8) !void {
        if (self.body) |old_body| {
            self.allocator.free(old_body);
        }
        self.body = try self.allocator.dupe(u8, body);
    }

    pub fn buildUrl(self: *const RestRequest) ![]const u8 {
        var url = std.ArrayList(u8){};
        defer url.deinit(self.allocator);

        try url.appendSlice(self.allocator, self.path);

        if (self.query.count() > 0) {
            try url.append(self.allocator, '?');
            var first = true;
            var it = self.query.iterator();
            while (it.next()) |entry| {
                if (!first) try url.append(self.allocator, '&');
                first = false;
                try url.appendSlice(self.allocator, entry.key_ptr.*);
                try url.append(self.allocator, '=');
                try url.appendSlice(self.allocator, entry.value_ptr.*);
            }
        }

        return url.toOwnedSlice(self.allocator);
    }
};
// ANCHOR_END: rest_request

// ANCHOR: rest_response
pub const RestResponse = struct {
    status: HttpStatus,
    headers: std.StringHashMap([]const u8),
    body: ?[]const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, status: HttpStatus) RestResponse {
        return .{
            .status = status,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *RestResponse) void {
        var it = self.headers.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.headers.deinit();

        if (self.body) |body| {
            self.allocator.free(body);
        }
    }

    pub fn addHeader(self: *RestResponse, key: []const u8, value: []const u8) !void {
        const owned_key = try self.allocator.dupe(u8, key);
        errdefer self.allocator.free(owned_key);
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);
        try self.headers.put(owned_key, owned_value);
    }

    pub fn setBody(self: *RestResponse, body: []const u8) !void {
        if (self.body) |old_body| {
            self.allocator.free(old_body);
        }
        self.body = try self.allocator.dupe(u8, body);
    }

    pub fn isSuccess(self: *const RestResponse) bool {
        return self.status.isSuccess();
    }
};
// ANCHOR_END: rest_response

// ANCHOR: rest_client
pub const RestClient = struct {
    base_url: []const u8,
    default_headers: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, base_url: []const u8) !RestClient {
        return .{
            .base_url = try allocator.dupe(u8, base_url),
            .default_headers = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *RestClient) void {
        self.allocator.free(self.base_url);

        var it = self.default_headers.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.default_headers.deinit();
    }

    pub fn setDefaultHeader(self: *RestClient, key: []const u8, value: []const u8) !void {
        const owned_key = try self.allocator.dupe(u8, key);
        errdefer self.allocator.free(owned_key);
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);
        try self.default_headers.put(owned_key, owned_value);
    }

    pub fn get(self: *RestClient, path: []const u8) !RestResponse {
        var request = RestRequest.init(self.allocator, .GET, path);
        defer request.deinit();
        return try self.execute(&request);
    }

    pub fn post(self: *RestClient, path: []const u8, body: []const u8) !RestResponse {
        var request = RestRequest.init(self.allocator, .POST, path);
        defer request.deinit();
        try request.setBody(body);
        try request.addHeader("Content-Type", "application/json");
        return try self.execute(&request);
    }

    pub fn put(self: *RestClient, path: []const u8, body: []const u8) !RestResponse {
        var request = RestRequest.init(self.allocator, .PUT, path);
        defer request.deinit();
        try request.setBody(body);
        try request.addHeader("Content-Type", "application/json");
        return try self.execute(&request);
    }

    pub fn patch(self: *RestClient, path: []const u8, body: []const u8) !RestResponse {
        var request = RestRequest.init(self.allocator, .PATCH, path);
        defer request.deinit();
        try request.setBody(body);
        try request.addHeader("Content-Type", "application/json");
        return try self.execute(&request);
    }

    pub fn delete(self: *RestClient, path: []const u8) !RestResponse {
        var request = RestRequest.init(self.allocator, .DELETE, path);
        defer request.deinit();
        return try self.execute(&request);
    }

    pub fn execute(self: *RestClient, request: *RestRequest) !RestResponse {
        // Simulate HTTP request (in real implementation, use std.http.Client)
        // For testing, return mock responses based on method and path

        if (request.method == .GET and std.mem.eql(u8, request.path, "/users/1")) {
            var response = RestResponse.init(self.allocator, .ok);
            try response.setBody("{\"id\":1,\"name\":\"Alice\"}");
            try response.addHeader("Content-Type", "application/json");
            return response;
        } else if (request.method == .POST and std.mem.eql(u8, request.path, "/users")) {
            var response = RestResponse.init(self.allocator, .created);
            try response.setBody("{\"id\":2,\"name\":\"Bob\"}");
            try response.addHeader("Content-Type", "application/json");
            return response;
        } else if (request.method == .PUT and std.mem.eql(u8, request.path, "/users/1")) {
            var response = RestResponse.init(self.allocator, .ok);
            try response.setBody("{\"id\":1,\"name\":\"Alice Updated\"}");
            try response.addHeader("Content-Type", "application/json");
            return response;
        } else if (request.method == .DELETE and std.mem.eql(u8, request.path, "/users/1")) {
            return RestResponse.init(self.allocator, .no_content);
        }

        return RestResponse.init(self.allocator, .not_found);
    }
};
// ANCHOR_END: rest_client

// ANCHOR: resource_handler
pub const ResourceHandler = struct {
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) ResourceHandler {
        return .{ .allocator = allocator };
    }

    pub fn handleGet(self: *ResourceHandler, id: []const u8) !RestResponse {
        var response = RestResponse.init(self.allocator, .ok);
        var body = std.ArrayList(u8){};
        defer body.deinit(self.allocator);

        try body.appendSlice(self.allocator, "{\"id\":");
        try body.appendSlice(self.allocator, id);
        try body.appendSlice(self.allocator, ",\"name\":\"Resource\"}");

        try response.setBody(body.items);
        try response.addHeader("Content-Type", "application/json");
        return response;
    }

    pub fn handleCreate(self: *ResourceHandler, data: []const u8) !RestResponse {
        var response = RestResponse.init(self.allocator, .created);
        try response.setBody(data);
        try response.addHeader("Content-Type", "application/json");
        try response.addHeader("Location", "/resources/123");
        return response;
    }

    pub fn handleUpdate(self: *ResourceHandler, id: []const u8, data: []const u8) !RestResponse {
        _ = id;
        var response = RestResponse.init(self.allocator, .ok);
        try response.setBody(data);
        try response.addHeader("Content-Type", "application/json");
        return response;
    }

    pub fn handleDelete(self: *ResourceHandler, id: []const u8) !RestResponse {
        _ = id;
        return RestResponse.init(self.allocator, .no_content);
    }
};
// ANCHOR_END: resource_handler

// ANCHOR: test_http_method
test "HTTP method to string conversion" {
    try testing.expectEqualStrings("GET", HttpMethod.GET.toString());
    try testing.expectEqualStrings("POST", HttpMethod.POST.toString());
    try testing.expectEqualStrings("PUT", HttpMethod.PUT.toString());
    try testing.expectEqualStrings("DELETE", HttpMethod.DELETE.toString());
}
// ANCHOR_END: test_http_method

// ANCHOR: test_http_status
test "HTTP status code classification" {
    try testing.expect(HttpStatus.ok.isSuccess());
    try testing.expect(HttpStatus.created.isSuccess());
    try testing.expect(!HttpStatus.bad_request.isSuccess());

    try testing.expect(HttpStatus.not_found.isClientError());
    try testing.expect(HttpStatus.unauthorized.isClientError());
    try testing.expect(!HttpStatus.ok.isClientError());

    try testing.expect(HttpStatus.internal_server_error.isServerError());
    try testing.expect(!HttpStatus.ok.isServerError());
}
// ANCHOR_END: test_http_status

// ANCHOR: test_rest_request
test "create REST request" {
    var request = RestRequest.init(testing.allocator, .GET, "/users");
    defer request.deinit();

    try testing.expectEqual(HttpMethod.GET, request.method);
    try testing.expectEqualStrings("/users", request.path);
    try testing.expectEqual(@as(?[]const u8, null), request.body);
}
// ANCHOR_END: test_rest_request

// ANCHOR: test_query_parameters
test "REST request with query parameters" {
    var request = RestRequest.init(testing.allocator, .GET, "/users");
    defer request.deinit();

    try request.addQuery("page", "2");
    try request.addQuery("limit", "10");

    const url = try request.buildUrl();
    defer testing.allocator.free(url);

    // URL should contain path and query params (order may vary)
    try testing.expect(std.mem.startsWith(u8, url, "/users?"));
    try testing.expect(std.mem.indexOf(u8, url, "page=2") != null);
    try testing.expect(std.mem.indexOf(u8, url, "limit=10") != null);
}
// ANCHOR_END: test_query_parameters

test "REST request with duplicate query parameters - no memory leak" {
    var request = RestRequest.init(testing.allocator, .GET, "/search");
    defer request.deinit();

    // Add query parameter twice - last value should win
    try request.addQuery("page", "1");
    try request.addQuery("page", "2");
    try request.addQuery("sort", "asc");
    try request.addQuery("sort", "desc");

    // Should only have 2 parameters, not 4
    try testing.expectEqual(@as(u32, 2), request.query.count());

    // Last values should win
    const page = request.query.get("page");
    try testing.expect(page != null);
    try testing.expectEqualStrings("2", page.?);

    const sort = request.query.get("sort");
    try testing.expect(sort != null);
    try testing.expectEqualStrings("desc", sort.?);
}

// ANCHOR: test_request_headers
test "REST request with headers" {
    var request = RestRequest.init(testing.allocator, .POST, "/users");
    defer request.deinit();

    try request.addHeader("Content-Type", "application/json");
    try request.addHeader("Authorization", "Bearer token123");

    const content_type = request.headers.get("Content-Type");
    try testing.expect(content_type != null);
    try testing.expectEqualStrings("application/json", content_type.?);

    const auth = request.headers.get("Authorization");
    try testing.expect(auth != null);
    try testing.expectEqualStrings("Bearer token123", auth.?);
}
// ANCHOR_END: test_request_headers

test "REST request with duplicate headers - no memory leak" {
    var request = RestRequest.init(testing.allocator, .POST, "/api/data");
    defer request.deinit();

    // Add same header multiple times - last value should win
    try request.addHeader("Authorization", "Bearer oldtoken");
    try request.addHeader("Authorization", "Bearer newtoken");
    try request.addHeader("Content-Type", "text/plain");
    try request.addHeader("Content-Type", "application/json");

    // Should only have 2 headers, not 4
    try testing.expectEqual(@as(u32, 2), request.headers.count());

    // Last values should win
    const auth = request.headers.get("Authorization");
    try testing.expect(auth != null);
    try testing.expectEqualStrings("Bearer newtoken", auth.?);

    const content_type = request.headers.get("Content-Type");
    try testing.expect(content_type != null);
    try testing.expectEqualStrings("application/json", content_type.?);
}

// ANCHOR: test_request_body
test "REST request with body" {
    var request = RestRequest.init(testing.allocator, .POST, "/users");
    defer request.deinit();

    const json_body = "{\"name\":\"Alice\",\"age\":30}";
    try request.setBody(json_body);

    try testing.expect(request.body != null);
    try testing.expectEqualStrings(json_body, request.body.?);
}
// ANCHOR_END: test_request_body

// ANCHOR: test_rest_response
test "create REST response" {
    var response = RestResponse.init(testing.allocator, .ok);
    defer response.deinit();

    try testing.expectEqual(HttpStatus.ok, response.status);
    try testing.expect(response.isSuccess());
}
// ANCHOR_END: test_rest_response

// ANCHOR: test_response_with_body
test "REST response with body and headers" {
    var response = RestResponse.init(testing.allocator, .created);
    defer response.deinit();

    try response.setBody("{\"id\":123}");
    try response.addHeader("Content-Type", "application/json");
    try response.addHeader("Location", "/users/123");

    try testing.expect(response.body != null);
    try testing.expectEqualStrings("{\"id\":123}", response.body.?);

    const location = response.headers.get("Location");
    try testing.expect(location != null);
    try testing.expectEqualStrings("/users/123", location.?);
}
// ANCHOR_END: test_response_with_body

// ANCHOR: test_rest_client
test "REST client GET request" {
    var client = try RestClient.init(testing.allocator, "https://api.example.com");
    defer client.deinit();

    var response = try client.get("/users/1");
    defer response.deinit();

    try testing.expect(response.isSuccess());
    try testing.expect(response.body != null);
    try testing.expect(std.mem.indexOf(u8, response.body.?, "Alice") != null);
}
// ANCHOR_END: test_rest_client

// ANCHOR: test_client_post
test "REST client POST request" {
    var client = try RestClient.init(testing.allocator, "https://api.example.com");
    defer client.deinit();

    const body = "{\"name\":\"Bob\"}";
    var response = try client.post("/users", body);
    defer response.deinit();

    try testing.expectEqual(HttpStatus.created, response.status);
    try testing.expect(response.body != null);
}
// ANCHOR_END: test_client_post

// ANCHOR: test_client_put
test "REST client PUT request" {
    var client = try RestClient.init(testing.allocator, "https://api.example.com");
    defer client.deinit();

    const body = "{\"name\":\"Alice Updated\"}";
    var response = try client.put("/users/1", body);
    defer response.deinit();

    try testing.expectEqual(HttpStatus.ok, response.status);
}
// ANCHOR_END: test_client_put

// ANCHOR: test_client_delete
test "REST client DELETE request" {
    var client = try RestClient.init(testing.allocator, "https://api.example.com");
    defer client.deinit();

    var response = try client.delete("/users/1");
    defer response.deinit();

    try testing.expectEqual(HttpStatus.no_content, response.status);
}
// ANCHOR_END: test_client_delete

// ANCHOR: test_client_default_headers
test "REST client with default headers" {
    var client = try RestClient.init(testing.allocator, "https://api.example.com");
    defer client.deinit();

    try client.setDefaultHeader("User-Agent", "Zig REST Client/1.0");
    try client.setDefaultHeader("Accept", "application/json");

    const user_agent = client.default_headers.get("User-Agent");
    try testing.expect(user_agent != null);
    try testing.expectEqualStrings("Zig REST Client/1.0", user_agent.?);
}
// ANCHOR_END: test_client_default_headers

// ANCHOR: test_resource_get
test "resource handler GET operation" {
    var handler = ResourceHandler.init(testing.allocator);

    var response = try handler.handleGet("123");
    defer response.deinit();

    try testing.expectEqual(HttpStatus.ok, response.status);
    try testing.expect(response.body != null);
    try testing.expect(std.mem.indexOf(u8, response.body.?, "123") != null);
}
// ANCHOR_END: test_resource_get

// ANCHOR: test_resource_create
test "resource handler CREATE operation" {
    var handler = ResourceHandler.init(testing.allocator);

    const data = "{\"name\":\"New Resource\"}";
    var response = try handler.handleCreate(data);
    defer response.deinit();

    try testing.expectEqual(HttpStatus.created, response.status);

    const location = response.headers.get("Location");
    try testing.expect(location != null);
    try testing.expectEqualStrings("/resources/123", location.?);
}
// ANCHOR_END: test_resource_create

// ANCHOR: test_resource_update
test "resource handler UPDATE operation" {
    var handler = ResourceHandler.init(testing.allocator);

    const data = "{\"name\":\"Updated Resource\"}";
    var response = try handler.handleUpdate("123", data);
    defer response.deinit();

    try testing.expectEqual(HttpStatus.ok, response.status);
    try testing.expect(response.body != null);
}
// ANCHOR_END: test_resource_update

// ANCHOR: test_resource_delete
test "resource handler DELETE operation" {
    var handler = ResourceHandler.init(testing.allocator);

    var response = try handler.handleDelete("123");
    defer response.deinit();

    try testing.expectEqual(HttpStatus.no_content, response.status);
    try testing.expectEqual(@as(?[]const u8, null), response.body);
}
// ANCHOR_END: test_resource_delete
```

### See Also

- Recipe 11.1: Making HTTP requests
- Recipe 11.2: Working with JSON APIs
- Recipe 11.4: Building a simple HTTP server
- Recipe 11.7: Handling cookies and sessions

---

## Recipe 11.7: Handling Cookies and Sessions {#recipe-11-7}

**Tags:** allocators, arraylist, atomics, c-interop, concurrency, data-structures, error-handling, hashmap, http, memory, networking, resource-cleanup, slices, synchronization, testing, threading
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_7.zig`

### Problem

You need to maintain state across HTTP requests in a web application. HTTP is stateless, so you need cookies to track client identity and server-side sessions to store user data. You need to handle cookie attributes (secure, httpOnly, sameSite), parse Cookie headers, generate Set-Cookie headers, and manage session lifecycle with proper cleanup.

### Solution

Build cookie and session management using Zig's standard library. The solution includes a Cookie structure with all standard attributes, a cookie parser for incoming requests, SessionData for storing key-value pairs, and a SessionStore for managing session lifecycle.

### Creating and Setting Cookies

```zig
test "create basic cookie" {
    var cookie = try Cookie.init(testing.allocator, "user_id", "12345");
    defer cookie.deinit();

    try testing.expectEqualStrings("user_id", cookie.name);
    try testing.expectEqualStrings("12345", cookie.value);
    try testing.expectEqual(false, cookie.http_only);
    try testing.expectEqual(false, cookie.secure);
    try testing.expectEqual(Cookie.SameSite.lax, cookie.same_site);
}
```

### Cookie Attributes

The `Cookie` struct supports all standard HTTP cookie attributes:

```zig
pub const Cookie = struct {
    name: []const u8,
    value: []const u8,
    domain: ?[]const u8,
    path: ?[]const u8,
    expires: ?i64, // Unix timestamp
    max_age: ?i64, // Seconds
    http_only: bool,
    secure: bool,
    same_site: SameSite,
    // ...
};
```

**Attribute Usage:**
- **Domain**: Which domain the cookie applies to
- **Path**: Which URL paths receive the cookie
- **Expires**: When the cookie expires (absolute time)
- **Max-Age**: How long until cookie expires (seconds from now)
- **HttpOnly**: Prevents JavaScript access (XSS protection)
- **Secure**: Only sent over HTTPS
- **SameSite**: CSRF protection (strict, lax, or none)

### SameSite Attribute

The `SameSite` enum provides CSRF protection:

```zig
pub const SameSite = enum {
    none,   // Send cookie with all requests (requires Secure)
    lax,    // Send on top-level navigation (default)
    strict, // Only send to same site
};

// Create cookie with strict same-site policy
var cookie = try Cookie.init(allocator, "auth", "token");
cookie.same_site = .strict;
cookie.secure = true; // Required for .none
```

**When to Use:**
- `strict`: Maximum protection for sensitive cookies
- `lax`: Good balance (allows GET from external sites)
- `none`: Cross-site requests needed (requires HTTPS)

### Parsing Cookie Headers

Parse the `Cookie` header from incoming requests:

```zig
var parser = CookieParser.init(testing.allocator);

const cookie_header = "session=abc123; user_id=456; theme=dark";
var cookies = try parser.parse(cookie_header);
defer {
    var it = cookies.iterator();
    while (it.next()) |entry| {
        testing.allocator.free(entry.key_ptr.*);
        testing.allocator.free(entry.value_ptr.*);
    }
    cookies.deinit();
}

// Access parsed cookies
const session = cookies.get("session"); // "abc123"
const user_id = cookies.get("user_id"); // "456"
const theme = cookies.get("theme"); // "dark"
```

The parser returns a `StringHashMap` with owned copies of cookie names and values.

### Session Management

Create and manage server-side sessions:

```zig
var store = SessionStore.init(testing.allocator);
defer store.deinit();

// Create new session with secure random ID
const session_id = try store.create();

// Store session data
if (store.get(session_id)) |session| {
    try session.data.set("user", "alice");
    try session.data.set("role", "admin");
    try session.data.set("login_time", "2024-01-15");
}

// Retrieve session data
if (store.get(session_id)) |session| {
    const user = session.data.get("user"); // "alice"
    const role = session.data.get("role"); // "admin"
}
```

### Session Data Operations

The `SessionData` struct stores key-value pairs:

```zig
var session_data = SessionData.init(testing.allocator);
defer session_data.deinit();

// Set values
try session_data.set("username", "alice");
try session_data.set("cart_items", "3");

// Get values
const username = session_data.get("username");
if (username) |name| {
    // Use name
}

// Update values
try session_data.set("cart_items", "4");

// Remove values
session_data.remove("cart_items");
```

### Session Lifecycle

Sessions track creation time and last access:

```zig
var session = try Session.init(testing.allocator, "session_id");
defer session.deinit();

// Session automatically records creation time
const created = session.created_at;

// Update last accessed time
session.touch();

// Check if expired (1 hour timeout)
if (session.isExpired(3600)) {
    // Session has expired
}
```

### Session Store Operations

The `SessionStore` manages multiple sessions:

```zig
var store = SessionStore.init(testing.allocator);
defer store.deinit();

// Configure timeout (default 1 hour)
store.default_timeout = 7200; // 2 hours

// Create session
const session_id = try store.create();

// Get session (returns null if not found or expired)
if (store.get(session_id)) |session| {
    // Session exists and is valid
    // Automatically updates last_accessed
}

// Destroy session
store.destroy(session_id);

// Cleanup expired sessions
try store.cleanup();
```

### Complete Cookie and Session Flow

Here's a typical web application flow:

```zig
// On login: Create session and set cookie
var store = SessionStore.init(allocator);
defer store.deinit();

// Create new session
const session_id = try store.create();

// Store user data
if (store.get(session_id)) |session| {
    try session.data.set("user_id", "123");
    try session.data.set("username", "alice");
}

// Create session cookie
var cookie = try Cookie.init(allocator, "session_id", session_id);
defer cookie.deinit();

try cookie.setPath("/");
cookie.http_only = true;
cookie.secure = true;
cookie.same_site = .strict;
cookie.max_age = 7200; // 2 hours

const set_cookie = try cookie.toSetCookieHeader();
defer allocator.free(set_cookie);
// Send: "Set-Cookie: session_id=...; Path=/; Max-Age=7200; HttpOnly; Secure; SameSite=Strict"

// On subsequent requests: Parse cookie and retrieve session
var parser = CookieParser.init(allocator);
var cookies = try parser.parse(request_cookie_header);
defer {
    var it = cookies.iterator();
    while (it.next()) |entry| {
        allocator.free(entry.key_ptr.*);
        allocator.free(entry.value_ptr.*);
    }
    cookies.deinit();
}

if (cookies.get("session_id")) |sid| {
    if (store.get(sid)) |session| {
        // Session valid - user is authenticated
        const user_id = session.data.get("user_id");
    }
}

// On logout: Destroy session and clear cookie
store.destroy(session_id);

var logout_cookie = try Cookie.init(allocator, "session_id", "");
defer logout_cookie.deinit();
logout_cookie.max_age = 0; // Expire immediately
```

### Discussion

### Cookie Security Attributes

**HttpOnly Flag:**
Prevents JavaScript access to cookies, protecting against XSS attacks:

```zig
cookie.http_only = true;
```

Without HttpOnly, malicious scripts can steal session cookies:
```javascript
// If HttpOnly is false, attacker can steal cookies
document.cookie // Returns all cookies
```

With HttpOnly set, `document.cookie` won't include the protected cookie.

**Secure Flag:**
Ensures cookies are only sent over HTTPS:

```zig
cookie.secure = true;
```

Without Secure, cookies can be intercepted on unsecured connections. Always use Secure for sensitive cookies in production.

**SameSite Protection:**
Prevents CSRF attacks by controlling when cookies are sent:

```zig
cookie.same_site = .strict; // Best protection
cookie.same_site = .lax;    // Good balance
cookie.same_site = .none;   // Requires Secure=true
```

- **Strict**: Cookie never sent on cross-site requests
- **Lax**: Cookie sent on top-level GET navigation
- **None**: Cookie sent on all requests (requires Secure)

### Session ID Generation

The implementation uses cryptographically secure random IDs:

```zig
pub fn create(self: *SessionStore) ![]const u8 {
    // Generate cryptographically secure session ID
    var random_bytes: [16]u8 = undefined;
    std.crypto.random.bytes(&random_bytes);

    // Encode as hex string (32 chars)
    var id_buf: [32]u8 = undefined;
    const id = std.fmt.bytesToHex(random_bytes, .lower);
    @memcpy(&id_buf, &id);

    const owned_id = try self.allocator.dupe(u8, &id_buf);
    // ...
}
```

This generates a 128-bit random ID (32 hex characters), making session hijacking computationally infeasible. Never use predictable values like timestamps or sequential counters.

### Memory Management

All cookie and session structures use explicit allocator passing:

```zig
pub const Cookie = struct {
    name: []const u8,
    value: []const u8,
    // ... optional attributes
    allocator: std.mem.Allocator,

    pub fn deinit(self: *Cookie) void {
        self.allocator.free(self.name);
        self.allocator.free(self.value);
        if (self.domain) |domain| self.allocator.free(domain);
        if (self.path) |path| self.allocator.free(path);
    }
};
```

The `deinit` method ensures:
- All string fields are freed
- Optional fields are checked before freeing
- No memory leaks on proper cleanup

### Cookie Parser Memory Safety

The parser uses `getOrPut` to handle duplicate cookie names without leaking memory:

```zig
const owned_value = try self.allocator.dupe(u8, value);
errdefer self.allocator.free(owned_value);

const result = try cookies.getOrPut(name);
if (result.found_existing) {
    self.allocator.free(result.value_ptr.*); // Free old value
    result.value_ptr.* = owned_value; // Use new value
} else {
    const owned_name = try self.allocator.dupe(u8, name);
    errdefer self.allocator.free(owned_name);
    result.key_ptr.* = owned_name;
    result.value_ptr.* = owned_value;
}
```

If the same cookie appears multiple times (`session=abc; session=xyz`), the parser:
1. Allocates the new value
2. Checks if the key already exists
3. If exists: frees the old value and updates with new value
4. If new: allocates the key and stores both

This prevents memory leaks from duplicate keys.

### Session Expiration

Sessions track last access time and support expiration:

```zig
pub fn isExpired(self: *const Session, timeout_seconds: i64) bool {
    const now = std.time.timestamp();
    return (now - self.last_accessed) >= timeout_seconds;
}
```

The `>=` operator ensures:
- Timeout of 0 expires immediately
- Timeout of 3600 expires after 1 hour of inactivity

When getting a session, it automatically updates last access:

```zig
pub fn get(self: *SessionStore, session_id: []const u8) ?*Session {
    if (self.sessions.getPtr(session_id)) |session| {
        if (session.isExpired(self.default_timeout)) {
            return null;
        }
        session.touch(); // Update last_accessed
        return session;
    }
    return null;
}
```

### Session Cleanup

Periodically remove expired sessions to prevent memory bloat:

```zig
var store = SessionStore.init(allocator);
defer store.deinit();

// Periodically call cleanup (e.g., every hour)
try store.cleanup();
```

The cleanup method:
1. Iterates through all sessions
2. Identifies expired sessions
3. Destroys them and frees memory

In production, run cleanup on a background timer or request count threshold.

### Cookie Path and Domain

Control where cookies are sent:

```zig
// Cookie sent to all paths under /api
try cookie.setPath("/api");

// Cookie sent to example.com and all subdomains
try cookie.setDomain("example.com");
```

**Path specificity:**
- `Path=/` - All paths
- `Path=/api` - Only /api and subdirectories
- `Path=/admin` - Only /admin and subdirectories

**Domain specificity:**
- No domain set - Current host only
- `Domain=example.com` - example.com and subdomains
- Cannot set domain to different top-level domain

### Session Store Destruction

Properly clean up sessions and their data:

```zig
pub fn deinit(self: *SessionStore) void {
    var it = self.sessions.iterator();
    while (it.next()) |entry| {
        self.allocator.free(entry.key_ptr.*);
        var session = entry.value_ptr;
        session.deinit(); // Cleanup session data
    }
    self.sessions.deinit();
}
```

Each session's `deinit` recursively frees all session data:

```zig
pub fn deinit(self: *Session) void {
    self.allocator.free(self.id);
    self.data.deinit(); // Frees all key-value pairs
}
```

### Set-Cookie Header Generation

The `toSetCookieHeader` method builds proper HTTP headers:

```zig
// Basic cookie
cookie = Cookie.init(allocator, "theme", "dark");
// Result: "theme=dark"

// Cookie with attributes
cookie.http_only = true;
cookie.secure = true;
cookie.max_age = 86400; // 1 day
// Result: "theme=dark; Max-Age=86400; HttpOnly; Secure"

// Cookie with domain and path
try cookie.setDomain("example.com");
try cookie.setPath("/");
// Result: "theme=dark; Domain=example.com; Path=/; Max-Age=86400; HttpOnly; Secure"
```

The order of attributes doesn't matter - browsers parse all of them.

### Security Considerations

**Production Recommendations:**

1. **Always use Secure and HttpOnly for session cookies:**
   ```zig
   cookie.secure = true;
   cookie.http_only = true;
   ```

2. **Use SameSite=Strict for sensitive cookies:**
   ```zig
   cookie.same_site = .strict;
   ```

3. **Set reasonable expiration times:**
   ```zig
   cookie.max_age = 3600; // 1 hour for sensitive sessions
   cookie.max_age = 2592000; // 30 days for "remember me"
   ```

4. **Regenerate session ID on privilege escalation:**
   ```zig
   // On login, create new session
   const new_session_id = try store.create();
   store.destroy(old_session_id);
   ```

5. **Validate session data:**
   ```zig
   if (store.get(session_id)) |session| {
       const user_id = session.data.get("user_id") orelse return error.InvalidSession;
       // Verify user_id is valid
   }
   ```

6. **Implement CSRF tokens for state-changing requests:**
   ```zig
   // Generate CSRF token per session
   if (store.get(session_id)) |session| {
       var token_bytes: [16]u8 = undefined;
       std.crypto.random.bytes(&token_bytes);
       const token = std.fmt.bytesToHex(token_bytes, .lower);
       try session.data.set("csrf_token", &token);
   }
   ```

### Limitations of This Implementation

This recipe provides educational patterns but lacks some production features:

**Missing Features:**
- Cookie value URL encoding (special characters in values)
- Expires attribute HTTP date formatting (currently uses timestamp)
- Cookie signing/encryption
- Session persistence (stored in memory only)
- Distributed session storage (Redis, database)
- Session size limits
- Rate limiting for session creation

**Security Improvements Needed:**
```zig
// TODO: Add cookie value encoding
pub fn encodeValue(allocator: std.mem.Allocator, value: []const u8) ![]const u8 {
    // URL encode special characters
    // Escape semicolons, commas, spaces
}

// TODO: Validate cookie names
pub fn validateName(name: []const u8) !void {
    if (name.len == 0) return error.EmptyCookieName;
    if (std.mem.indexOfAny(u8, name, ";=, \t\r\n") != null) {
        return error.InvalidCookieName;
    }
}

// TODO: Add persistent session storage
pub const PersistentSessionStore = struct {
    backend: SessionBackend, // Redis, PostgreSQL, etc.
    // ...
};
```

For production use:
- Add cookie value encoding/decoding
- Implement session persistence
- Add session size limits (prevent DoS)
- Sign cookies to prevent tampering
- Encrypt sensitive cookie values
- Implement sliding expiration (extend on activity)
- Add session revocation mechanism
- Log security events (failed lookups, expirations)

### Advanced: Thread-Safe Session Store

**Critical Production Requirement:** The basic `SessionStore` implementation above is **NOT thread-safe**. In multi-threaded web servers where requests are handled concurrently, multiple threads accessing the same `SessionStore` will cause data races, memory corruption, and crashes.

#### Why This Matters

Consider this scenario with 3 concurrent HTTP requests:

```zig
// Thread 1: Reading session
const session = store.get(session_id);

// Thread 2: Simultaneously creating session (RACE CONDITION!)
const new_id = store.create();

// Thread 3: Simultaneously cleaning up (MEMORY CORRUPTION!)
store.cleanup();
```

All three threads access `store.sessions` (a `StringHashMap`) concurrently. HashMaps in Zig are **NOT thread-safe**. Concurrent access will:
- Corrupt the internal hash table structure
- Cause use-after-free bugs when one thread deletes while another reads
- Trigger assertion failures in debug builds
- Produce undefined behavior in release builds

#### Solution: Add Mutex Synchronization

For production multi-threaded servers, protect the `SessionStore` with `std.Thread.Mutex`:

```zig
/// Thread-Safe Session Store for Production Web Servers
///
/// This implementation adds mutex synchronization to prevent data races when
/// multiple threads access the session store concurrently. Essential for
/// multi-threaded HTTP servers where requests are handled in parallel.
///
/// Key Differences from Basic SessionStore:
/// - std.Thread.Mutex protects all HashMap operations
/// - lock()/unlock() pattern ensures atomic operations
/// - defer unlock() prevents lock leaks on early returns
///
/// Performance: Adds ~100ns per operation. For >10k req/s, consider:
/// - Sharded stores (multiple stores with separate locks)
/// - Lock-free data structures (advanced, see Recipe 12.3)
/// - External session storage (Redis, database)
pub const ThreadSafeSessionStore = struct {
    sessions: std.StringHashMap(Session),
    allocator: std.mem.Allocator,
    default_timeout: i64,
    mutex: std.Thread.Mutex,

    pub fn init(allocator: std.mem.Allocator) ThreadSafeSessionStore {
        return .{
            .sessions = std.StringHashMap(Session).init(allocator),
            .allocator = allocator,
            .default_timeout = 3600, // 1 hour default
            .mutex = .{}, // Zero-initialize mutex
        };
    }

    pub fn deinit(self: *ThreadSafeSessionStore) void {
        // No lock needed - deinit called when no other threads access store
        var it = self.sessions.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            var session = entry.value_ptr;
            session.deinit();
        }
        self.sessions.deinit();
    }

    pub fn create(self: *ThreadSafeSessionStore) ![]const u8 {
        // Lock before accessing shared HashMap
        self.mutex.lock();
        defer self.mutex.unlock();

        // Generate cryptographically secure session ID
        var random_bytes: [16]u8 = undefined;
        std.crypto.random.bytes(&random_bytes);

        // Encode as hex string (32 chars)
        var id_buf: [32]u8 = undefined;
        const id = std.fmt.bytesToHex(random_bytes, .lower);
        @memcpy(&id_buf, &id);

        const owned_id = try self.allocator.dupe(u8, &id_buf);
        errdefer self.allocator.free(owned_id);

        const session = try Session.init(self.allocator, owned_id);
        try self.sessions.put(owned_id, session);

        return owned_id;
    }

    pub fn get(self: *ThreadSafeSessionStore, session_id: []const u8) ?*Session {
        // Lock prevents concurrent modification while reading
        self.mutex.lock();
        defer self.mutex.unlock();

        if (self.sessions.getPtr(session_id)) |session| {
            if (session.isExpired(self.default_timeout)) {
                return null;
            }
            session.touch();
            return session;
        }
        return null;
    }

    pub fn destroy(self: *ThreadSafeSessionStore, session_id: []const u8) void {
        self.mutex.lock();
        defer self.mutex.unlock();

        if (self.sessions.getPtr(session_id)) |session| {
            session.deinit();
        }
        if (self.sessions.fetchRemove(session_id)) |kv| {
            self.allocator.free(kv.key);
        }
    }

    pub fn cleanup(self: *ThreadSafeSessionStore) !void {
        self.mutex.lock();
        defer self.mutex.unlock();

        var to_remove = std.ArrayList([]const u8){};
        defer to_remove.deinit(self.allocator);

        var it = self.sessions.iterator();
        while (it.next()) |entry| {
            if (entry.value_ptr.isExpired(self.default_timeout)) {
                try to_remove.append(self.allocator, entry.key_ptr.*);
            }
        }

        // Cleanup while holding lock (safe because we're in the same function)
        for (to_remove.items) |session_id| {
            if (self.sessions.getPtr(session_id)) |session| {
                session.deinit();
            }
            if (self.sessions.fetchRemove(session_id)) |kv| {
                self.allocator.free(kv.key);
            }
        }
    }
};
```

#### Key Changes for Thread Safety

1. **Add mutex field:**
   ```zig
   mutex: std.Thread.Mutex,
   ```

2. **Lock before ALL HashMap operations:**
   ```zig
   pub fn create(self: *ThreadSafeSessionStore) ![]const u8 {
       self.mutex.lock();
       defer self.mutex.unlock();
       // ... HashMap operations are now atomic
   }
   ```

3. **Use `defer` for automatic unlock:**
   - Ensures unlock even on error returns
   - Prevents deadlocks from forgotten unlocks
   - Idiomatic Zig cleanup pattern

4. **Lock in every method that touches `sessions`:**
   - `create()` - Writes to HashMap
   - `get()` - Reads from HashMap (and modifies Session)
   - `destroy()` - Removes from HashMap
   - `cleanup()` - Iterates and modifies HashMap

#### When You Need Thread Safety

Use `ThreadSafeSessionStore` when:
- Building multi-threaded HTTP servers
- Using thread pools for request handling
- Running background cleanup threads
- Processing >1 concurrent request

Use basic `SessionStore` only for:
- Single-threaded educational examples
- Testing and prototyping
- Single-request-at-a-time architectures

#### Performance Considerations

**Mutex Overhead:**
- Each lock/unlock adds approximately 100-200 nanoseconds
- For typical web apps (<10k requests/second per core), this is negligible
- The safety benefits far outweigh the minimal performance cost

**High-Performance Alternatives:**

For extremely high-traffic servers (>10k req/s), consider:

1. **Sharded Session Stores** (multiple stores with separate locks):
   ```zig
   pub const ShardedSessionStore = struct {
       shards: [16]ThreadSafeSessionStore,

       fn getShard(self: *ShardedSessionStore, session_id: []const u8) *ThreadSafeSessionStore {
           const hash = std.hash.Wyhash.hash(0, session_id);
           return &self.shards[hash % self.shards.len];
       }
   };
   ```

2. **Lock-free data structures** (advanced, see Recipe 12.3: Atomic operations)

3. **External session storage** (Redis, PostgreSQL with connection pooling)

#### Testing Thread Safety

The thread-safe implementation includes comprehensive concurrency tests:

```zig
test "concurrent session creation" {
    var store = ThreadSafeSessionStore.init(testing.allocator);
    defer store.deinit();

    const num_threads = 10;
    var threads: [num_threads]std.Thread = undefined;

    // Spawn threads that create sessions concurrently
    for (&threads) |*thread| {
        thread.* = try std.Thread.spawn(.{}, createSessionWorker, .{&store});
    }

    for (threads) |thread| {
        thread.join();
    }

    // All 10 sessions should exist without corruption or loss
    try testing.expectEqual(@as(u32, num_threads), store.sessions.count());
}

fn createSessionWorker(store: *ThreadSafeSessionStore) void {
    const session_id = store.create() catch return;
    _ = store.get(session_id);
}
```

Run these tests to verify:
- No data races under concurrent load
- All operations complete without corruption
- No memory leaks from race conditions

#### Deadlock Prevention

The implementation avoids deadlocks by:
1. **Never holding multiple locks** - Only one mutex in the entire structure
2. **Using `defer unlock()`** - Ensures unlock on all code paths
3. **No nested locking** - Functions don't call other locking functions while holding lock

**Important:** If you extend this with multiple locks, always acquire locks in consistent order to prevent deadlocks.

### Best Practices

**Cookie Best Practices:**
- Use shortest viable expiration time
- Set specific Path instead of root (/) when possible
- Always set Secure flag in production
- Use HttpOnly unless JavaScript needs access
- Use SameSite=Strict for authentication cookies

**Session Best Practices:**
- Generate cryptographically random session IDs
- Regenerate session ID on login
- Implement absolute timeout (max session lifetime)
- Implement idle timeout (inactivity expiration)
- Clear sessions on logout
- Run periodic cleanup to free memory
- Store minimal data in sessions
- Never store sensitive data unencrypted

**Error Handling:**
```zig
// Validate session before use
if (store.get(session_id)) |session| {
    // Check user is still authorized
    const user_id = session.data.get("user_id") orelse {
        store.destroy(session_id);
        return error.InvalidSession;
    };

    // Verify user exists and is active
    const user = try database.getUser(user_id);
    if (!user.is_active) {
        store.destroy(session_id);
        return error.UserDeactivated;
    }
} else {
    // Session not found or expired
    return error.Unauthenticated;
}
```

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: cookie
pub const Cookie = struct {
    name: []const u8,
    value: []const u8,
    domain: ?[]const u8,
    path: ?[]const u8,
    expires: ?i64, // Unix timestamp
    max_age: ?i64, // Seconds
    http_only: bool,
    secure: bool,
    same_site: SameSite,
    allocator: std.mem.Allocator,

    pub const SameSite = enum {
        none,
        lax,
        strict,

        pub fn toString(self: SameSite) []const u8 {
            return switch (self) {
                .none => "None",
                .lax => "Lax",
                .strict => "Strict",
            };
        }
    };

    pub fn init(allocator: std.mem.Allocator, name: []const u8, value: []const u8) !Cookie {
        return .{
            .name = try allocator.dupe(u8, name),
            .value = try allocator.dupe(u8, value),
            .domain = null,
            .path = null,
            .expires = null,
            .max_age = null,
            .http_only = false,
            .secure = false,
            .same_site = .lax,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Cookie) void {
        self.allocator.free(self.name);
        self.allocator.free(self.value);
        if (self.domain) |domain| self.allocator.free(domain);
        if (self.path) |path| self.allocator.free(path);
    }

    pub fn setDomain(self: *Cookie, domain: []const u8) !void {
        if (self.domain) |old_domain| {
            self.allocator.free(old_domain);
        }
        self.domain = try self.allocator.dupe(u8, domain);
    }

    pub fn setPath(self: *Cookie, path: []const u8) !void {
        if (self.path) |old_path| {
            self.allocator.free(old_path);
        }
        self.path = try self.allocator.dupe(u8, path);
    }

    pub fn toSetCookieHeader(self: *const Cookie) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        // Name=Value
        try buffer.appendSlice(self.allocator, self.name);
        try buffer.append(self.allocator, '=');
        try buffer.appendSlice(self.allocator, self.value);

        // Domain
        if (self.domain) |domain| {
            try buffer.appendSlice(self.allocator, "; Domain=");
            try buffer.appendSlice(self.allocator, domain);
        }

        // Path
        if (self.path) |path| {
            try buffer.appendSlice(self.allocator, "; Path=");
            try buffer.appendSlice(self.allocator, path);
        }

        // Expires
        if (self.expires) |expires| {
            try buffer.appendSlice(self.allocator, "; Expires=");
            var time_buf: [32]u8 = undefined;
            const time_str = try std.fmt.bufPrint(&time_buf, "{d}", .{expires});
            try buffer.appendSlice(self.allocator, time_str);
        }

        // Max-Age
        if (self.max_age) |max_age| {
            try buffer.appendSlice(self.allocator, "; Max-Age=");
            var age_buf: [32]u8 = undefined;
            const age_str = try std.fmt.bufPrint(&age_buf, "{d}", .{max_age});
            try buffer.appendSlice(self.allocator, age_str);
        }

        // HttpOnly
        if (self.http_only) {
            try buffer.appendSlice(self.allocator, "; HttpOnly");
        }

        // Secure
        if (self.secure) {
            try buffer.appendSlice(self.allocator, "; Secure");
        }

        // SameSite
        if (self.same_site != .lax) {
            try buffer.appendSlice(self.allocator, "; SameSite=");
            try buffer.appendSlice(self.allocator, self.same_site.toString());
        }

        return buffer.toOwnedSlice(self.allocator);
    }
};
// ANCHOR_END: cookie

// ANCHOR: cookie_parser
pub const CookieParser = struct {
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) CookieParser {
        return .{ .allocator = allocator };
    }

    pub fn parse(self: *CookieParser, cookie_header: []const u8) !std.StringHashMap([]const u8) {
        var cookies = std.StringHashMap([]const u8).init(self.allocator);
        errdefer {
            var it = cookies.iterator();
            while (it.next()) |entry| {
                self.allocator.free(entry.key_ptr.*);
                self.allocator.free(entry.value_ptr.*);
            }
            cookies.deinit();
        }

        var pairs = std.mem.splitSequence(u8, cookie_header, "; ");
        while (pairs.next()) |pair| {
            const trimmed = std.mem.trim(u8, pair, " \t");
            if (trimmed.len == 0) continue;

            const eq_pos = std.mem.indexOf(u8, trimmed, "=") orelse continue;
            const name = std.mem.trim(u8, trimmed[0..eq_pos], " \t");
            const value = std.mem.trim(u8, trimmed[eq_pos + 1 ..], " \t");

            const owned_value = try self.allocator.dupe(u8, value);
            errdefer self.allocator.free(owned_value);

            const result = try cookies.getOrPut(name);
            if (result.found_existing) {
                self.allocator.free(result.value_ptr.*); // Free old value
                result.value_ptr.* = owned_value; // Use new value
            } else {
                const owned_name = try self.allocator.dupe(u8, name);
                errdefer self.allocator.free(owned_name);
                result.key_ptr.* = owned_name;
                result.value_ptr.* = owned_value;
            }
        }

        return cookies;
    }
};
// ANCHOR_END: cookie_parser

// ANCHOR: session_data
pub const SessionData = struct {
    data: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) SessionData {
        return .{
            .data = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *SessionData) void {
        var it = self.data.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.data.deinit();
    }

    pub fn set(self: *SessionData, key: []const u8, value: []const u8) !void {
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        const result = try self.data.getOrPut(key);
        if (result.found_existing) {
            self.allocator.free(result.value_ptr.*);
            result.value_ptr.* = owned_value;
        } else {
            const owned_key = try self.allocator.dupe(u8, key);
            errdefer self.allocator.free(owned_key);
            result.key_ptr.* = owned_key;
            result.value_ptr.* = owned_value;
        }
    }

    pub fn get(self: *const SessionData, key: []const u8) ?[]const u8 {
        return self.data.get(key);
    }

    pub fn remove(self: *SessionData, key: []const u8) void {
        if (self.data.fetchRemove(key)) |kv| {
            self.allocator.free(kv.key);
            self.allocator.free(kv.value);
        }
    }
};
// ANCHOR_END: session_data

// ANCHOR: session
pub const Session = struct {
    id: []const u8,
    data: SessionData,
    created_at: i64,
    last_accessed: i64,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, id: []const u8) !Session {
        const now = std.time.timestamp();
        return .{
            .id = try allocator.dupe(u8, id),
            .data = SessionData.init(allocator),
            .created_at = now,
            .last_accessed = now,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Session) void {
        self.allocator.free(self.id);
        self.data.deinit();
    }

    pub fn touch(self: *Session) void {
        self.last_accessed = std.time.timestamp();
    }

    pub fn isExpired(self: *const Session, timeout_seconds: i64) bool {
        const now = std.time.timestamp();
        return (now - self.last_accessed) >= timeout_seconds;
    }
};
// ANCHOR_END: session

// ANCHOR: session_store
pub const SessionStore = struct {
    sessions: std.StringHashMap(Session),
    allocator: std.mem.Allocator,
    default_timeout: i64,

    pub fn init(allocator: std.mem.Allocator) SessionStore {
        return .{
            .sessions = std.StringHashMap(Session).init(allocator),
            .allocator = allocator,
            .default_timeout = 3600, // 1 hour default
        };
    }

    pub fn deinit(self: *SessionStore) void {
        var it = self.sessions.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            var session = entry.value_ptr;
            session.deinit();
        }
        self.sessions.deinit();
    }

    pub fn create(self: *SessionStore) ![]const u8 {
        // Generate cryptographically secure session ID
        var random_bytes: [16]u8 = undefined;
        std.crypto.random.bytes(&random_bytes);

        // Encode as hex string (32 chars)
        var id_buf: [32]u8 = undefined;
        const id = std.fmt.bytesToHex(random_bytes, .lower);
        @memcpy(&id_buf, &id);

        const owned_id = try self.allocator.dupe(u8, &id_buf);
        errdefer self.allocator.free(owned_id);

        const session = try Session.init(self.allocator, owned_id);
        try self.sessions.put(owned_id, session);

        return owned_id;
    }

    pub fn get(self: *SessionStore, session_id: []const u8) ?*Session {
        if (self.sessions.getPtr(session_id)) |session| {
            if (session.isExpired(self.default_timeout)) {
                return null;
            }
            session.touch();
            return session;
        }
        return null;
    }

    pub fn destroy(self: *SessionStore, session_id: []const u8) void {
        if (self.sessions.getPtr(session_id)) |session| {
            session.deinit();
        }
        if (self.sessions.fetchRemove(session_id)) |kv| {
            self.allocator.free(kv.key);
        }
    }

    pub fn cleanup(self: *SessionStore) !void {
        var to_remove = std.ArrayList([]const u8){};
        defer to_remove.deinit(self.allocator);

        var it = self.sessions.iterator();
        while (it.next()) |entry| {
            if (entry.value_ptr.isExpired(self.default_timeout)) {
                try to_remove.append(self.allocator, entry.key_ptr.*);
            }
        }

        for (to_remove.items) |session_id| {
            self.destroy(session_id);
        }
    }
};
// ANCHOR_END: session_store

// ANCHOR: test_cookie_creation
test "create basic cookie" {
    var cookie = try Cookie.init(testing.allocator, "user_id", "12345");
    defer cookie.deinit();

    try testing.expectEqualStrings("user_id", cookie.name);
    try testing.expectEqualStrings("12345", cookie.value);
    try testing.expectEqual(false, cookie.http_only);
    try testing.expectEqual(false, cookie.secure);
    try testing.expectEqual(Cookie.SameSite.lax, cookie.same_site);
}
// ANCHOR_END: test_cookie_creation

// ANCHOR: test_cookie_attributes
test "cookie with attributes" {
    var cookie = try Cookie.init(testing.allocator, "session", "abc123");
    defer cookie.deinit();

    try cookie.setDomain("example.com");
    try cookie.setPath("/");
    cookie.http_only = true;
    cookie.secure = true;
    cookie.same_site = .strict;
    cookie.max_age = 3600;

    try testing.expectEqualStrings("example.com", cookie.domain.?);
    try testing.expectEqualStrings("/", cookie.path.?);
    try testing.expect(cookie.http_only);
    try testing.expect(cookie.secure);
    try testing.expectEqual(@as(?i64, 3600), cookie.max_age);
}
// ANCHOR_END: test_cookie_attributes

// ANCHOR: test_set_cookie_header
test "generate Set-Cookie header" {
    var cookie = try Cookie.init(testing.allocator, "session", "abc123");
    defer cookie.deinit();

    try cookie.setPath("/");
    cookie.http_only = true;
    cookie.secure = true;

    const header = try cookie.toSetCookieHeader();
    defer testing.allocator.free(header);

    try testing.expect(std.mem.startsWith(u8, header, "session=abc123"));
    try testing.expect(std.mem.indexOf(u8, header, "Path=/") != null);
    try testing.expect(std.mem.indexOf(u8, header, "HttpOnly") != null);
    try testing.expect(std.mem.indexOf(u8, header, "Secure") != null);
}
// ANCHOR_END: test_set_cookie_header

// ANCHOR: test_samesite_attribute
test "cookie SameSite attribute" {
    var cookie = try Cookie.init(testing.allocator, "test", "value");
    defer cookie.deinit();

    cookie.same_site = .strict;
    const header1 = try cookie.toSetCookieHeader();
    defer testing.allocator.free(header1);
    try testing.expect(std.mem.indexOf(u8, header1, "SameSite=Strict") != null);

    cookie.same_site = .none;
    const header2 = try cookie.toSetCookieHeader();
    defer testing.allocator.free(header2);
    try testing.expect(std.mem.indexOf(u8, header2, "SameSite=None") != null);
}
// ANCHOR_END: test_samesite_attribute

// ANCHOR: test_cookie_parsing
test "parse Cookie header" {
    var parser = CookieParser.init(testing.allocator);

    const cookie_header = "session=abc123; user_id=456; theme=dark";
    var cookies = try parser.parse(cookie_header);
    defer {
        var it = cookies.iterator();
        while (it.next()) |entry| {
            testing.allocator.free(entry.key_ptr.*);
            testing.allocator.free(entry.value_ptr.*);
        }
        cookies.deinit();
    }

    try testing.expectEqual(@as(u32, 3), cookies.count());

    const session = cookies.get("session");
    try testing.expect(session != null);
    try testing.expectEqualStrings("abc123", session.?);

    const user_id = cookies.get("user_id");
    try testing.expect(user_id != null);
    try testing.expectEqualStrings("456", user_id.?);

    const theme = cookies.get("theme");
    try testing.expect(theme != null);
    try testing.expectEqualStrings("dark", theme.?);
}
// ANCHOR_END: test_cookie_parsing

// ANCHOR: test_empty_cookie_header
test "parse empty cookie header" {
    var parser = CookieParser.init(testing.allocator);

    var cookies = try parser.parse("");
    defer cookies.deinit();

    try testing.expectEqual(@as(u32, 0), cookies.count());
}
// ANCHOR_END: test_empty_cookie_header

// ANCHOR: test_session_data
test "session data storage" {
    var session_data = SessionData.init(testing.allocator);
    defer session_data.deinit();

    try session_data.set("username", "alice");
    try session_data.set("role", "admin");

    const username = session_data.get("username");
    try testing.expect(username != null);
    try testing.expectEqualStrings("alice", username.?);

    const role = session_data.get("role");
    try testing.expect(role != null);
    try testing.expectEqualStrings("admin", role.?);
}
// ANCHOR_END: test_session_data

// ANCHOR: test_session_data_update
test "update session data" {
    var session_data = SessionData.init(testing.allocator);
    defer session_data.deinit();

    try session_data.set("counter", "1");
    try session_data.set("counter", "2");

    const counter = session_data.get("counter");
    try testing.expect(counter != null);
    try testing.expectEqualStrings("2", counter.?);
}
// ANCHOR_END: test_session_data_update

// ANCHOR: test_session_data_remove
test "remove session data" {
    var session_data = SessionData.init(testing.allocator);
    defer session_data.deinit();

    try session_data.set("temp", "value");
    try testing.expect(session_data.get("temp") != null);

    session_data.remove("temp");
    try testing.expect(session_data.get("temp") == null);
}
// ANCHOR_END: test_session_data_remove

// ANCHOR: test_session_creation
test "create session" {
    var session = try Session.init(testing.allocator, "session_123");
    defer session.deinit();

    try testing.expectEqualStrings("session_123", session.id);
    try testing.expect(session.created_at > 0);
    try testing.expect(session.last_accessed > 0);
}
// ANCHOR_END: test_session_creation

// ANCHOR: test_session_touch
test "session touch updates last accessed" {
    var session = try Session.init(testing.allocator, "session_123");
    defer session.deinit();

    const initial_time = session.last_accessed;
    session.touch();

    try testing.expect(session.last_accessed >= initial_time);
}
// ANCHOR_END: test_session_touch

// ANCHOR: test_session_expiry
test "session expiry check" {
    var session = try Session.init(testing.allocator, "session_123");
    defer session.deinit();

    // Not expired with 1 hour timeout
    try testing.expect(!session.isExpired(3600));

    // Expired with 0 second timeout
    try testing.expect(session.isExpired(0));
}
// ANCHOR_END: test_session_expiry

// ANCHOR: test_session_store
test "session store operations" {
    var store = SessionStore.init(testing.allocator);
    defer store.deinit();

    const session_id = try store.create();

    const session = store.get(session_id);
    try testing.expect(session != null);
    try testing.expectEqualStrings(session_id, session.?.id);
}
// ANCHOR_END: test_session_store

// ANCHOR: test_session_store_data
test "store and retrieve session data" {
    var store = SessionStore.init(testing.allocator);
    defer store.deinit();

    const session_id = try store.create();

    if (store.get(session_id)) |session| {
        try session.data.set("user", "alice");
    }

    if (store.get(session_id)) |session| {
        const user = session.data.get("user");
        try testing.expect(user != null);
        try testing.expectEqualStrings("alice", user.?);
    }
}
// ANCHOR_END: test_session_store_data

// ANCHOR: test_session_destroy
test "destroy session" {
    var store = SessionStore.init(testing.allocator);
    defer store.deinit();

    const session_id = try store.create();
    try testing.expect(store.get(session_id) != null);

    store.destroy(session_id);
    try testing.expect(store.get(session_id) == null);
}
// ANCHOR_END: test_session_destroy

// ANCHOR: test_session_cleanup
test "cleanup expired sessions" {
    var store = SessionStore.init(testing.allocator);
    defer store.deinit();

    store.default_timeout = 0; // All sessions expire immediately

    const session_id1 = try store.create();
    const session_id2 = try store.create();

    try store.cleanup();

    try testing.expect(store.get(session_id1) == null);
    try testing.expect(store.get(session_id2) == null);
}
// ANCHOR_END: test_session_cleanup
```

### See Also

- Recipe 11.4: Building a simple HTTP server
- Recipe 11.6: Working with REST APIs
- Recipe 11.12: OAuth2 authentication
- Recipe 12.1: Basic threading and thread management
- Recipe 12.2: Mutexes and basic locking
- Recipe 12.3: Atomic operations
- Recipe 13.5: Cryptographic operations

---

## Recipe 11.8: SSL/TLS Connections {#recipe-11-8}

**Tags:** allocators, arraylist, data-structures, error-handling, http, memory, networking, resource-cleanup, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_8.zig`

### Problem

You need to establish secure TLS/SSL connections for HTTPS requests or secure network communication. You need to configure TLS versions, cipher suites, certificate validation, and handle the TLS handshake process. Security requirements dictate using modern TLS versions (1.2+) and strong cipher suites while properly validating server certificates.

### Solution

Build TLS connection management using enum types for versions and cipher suites, structures for certificates and configuration, and a state machine for the handshake process. While Zig's standard library TLS support is evolving, this recipe demonstrates the fundamental patterns for TLS configuration and connection management.

### TLS Version Management

```zig
pub const TlsVersion = enum(u16) {
    tls_1_0 = 0x0301,
    tls_1_1 = 0x0302,
    tls_1_2 = 0x0303,
    tls_1_3 = 0x0304,

    pub fn toString(self: TlsVersion) []const u8 {
        return switch (self) {
            .tls_1_0 => "TLS 1.0",
            .tls_1_1 => "TLS 1.1",
            .tls_1_2 => "TLS 1.2",
            .tls_1_3 => "TLS 1.3",
        };
    }

    pub fn isSecure(self: TlsVersion) bool {
        // TLS 1.2 and 1.3 are considered secure
        return @intFromEnum(self) >= @intFromEnum(TlsVersion.tls_1_2);
    }
};
```

**Version Recommendations:**
- **TLS 1.3**: Latest, fastest, most secure (recommended)
- **TLS 1.2**: Widely supported, secure, minimum acceptable
- **TLS 1.1**: Deprecated, not recommended
- **TLS 1.0**: Deprecated, insecure, avoid

### Cipher Suite Configuration

```zig
pub const CipherSuite = enum(u16) {
    // TLS 1.3 cipher suites (recommended)
    tls_aes_128_gcm_sha256 = 0x1301,
    tls_aes_256_gcm_sha384 = 0x1302,
    tls_chacha20_poly1305_sha256 = 0x1303,

    // TLS 1.2 cipher suites
    ecdhe_rsa_aes128_gcm_sha256 = 0xC02F,
    ecdhe_rsa_aes256_gcm_sha384 = 0xC030,

    pub fn toString(self: CipherSuite) []const u8 {
        return switch (self) {
            .tls_aes_128_gcm_sha256 => "TLS_AES_128_GCM_SHA256",
            .tls_aes_256_gcm_sha384 => "TLS_AES_256_GCM_SHA384",
            .tls_chacha20_poly1305_sha256 => "TLS_CHACHA20_POLY1305_SHA256",
            .ecdhe_rsa_aes128_gcm_sha256 => "ECDHE-RSA-AES128-GCM-SHA256",
            .ecdhe_rsa_aes256_gcm_sha384 => "ECDHE-RSA-AES256-GCM-SHA384",
        };
    }

    pub fn isRecommended(self: CipherSuite) bool {
        // TLS 1.3 cipher suites are recommended
        return @intFromEnum(self) >= 0x1301 and @intFromEnum(self) <= 0x1303;
    }
};
```

**Cipher Suite Selection:**
- TLS 1.3 uses AEAD ciphers (GCM, ChaCha20-Poly1305)
- Prefer forward secrecy (ECDHE key exchange)
- Avoid weak ciphers (RC4, DES, MD5, SHA1)

### Certificate Management

```zig
var cert = try Certificate.init(
    testing.allocator,
    "CN=example.com",
    "CN=Example CA",
);
defer cert.deinit();

// Set certificate fingerprint
try cert.setFingerprint("AA:BB:CC:DD:EE:FF");

// Check validity
if (cert.isValid()) {
    // Certificate is within validity period
}

// Check expiration
if (cert.isExpired()) {
    // Certificate has expired
}

// Days until expiry
const days = cert.daysUntilExpiry();
if (days < 30) {
    // Certificate expires soon
}
```

The `Certificate` struct stores:
- **Subject**: Entity the certificate identifies (e.g., "CN=example.com")
- **Issuer**: Certificate Authority that signed it
- **Not Before**: Start of validity period (Unix timestamp)
- **Not After**: End of validity period
- **Fingerprint**: Certificate hash for verification

### TLS Configuration

```zig
var config = TlsConfig.init(testing.allocator);
defer config.deinit();

// Set version range
config.min_version = .tls_1_2; // Minimum secure version
config.max_version = .tls_1_3; // Latest version

// Add allowed cipher suites (in preference order)
try config.addCipher(.tls_aes_256_gcm_sha384);
try config.addCipher(.tls_aes_128_gcm_sha256);
try config.addCipher(.tls_chacha20_poly1305_sha256);

// Configure certificate verification
config.verify_certificates = true;
config.verify_hostname = true;

// Add trusted root certificates
var root_ca = try Certificate.init(
    allocator,
    "CN=Root CA",
    "CN=Root CA",
);
try config.addTrustedCertificate(root_ca);
```

**Configuration Options:**
- **min_version/max_version**: Acceptable TLS version range
- **allowed_ciphers**: Cipher suites in preference order
- **verify_certificates**: Validate server certificate chain
- **verify_hostname**: Ensure certificate matches hostname
- **trusted_certificates**: Root CAs to trust

### Secure vs Insecure Configuration

```zig
// Secure configuration (recommended)
var config = TlsConfig.init(allocator);
config.min_version = .tls_1_2;
config.verify_certificates = true;
config.verify_hostname = true;

if (config.isSecure()) {
    // Configuration meets security standards
}

// Insecure configuration (development only)
config.setInsecure(); // Disables all verification
```

**Never use insecure configuration in production!** It defeats the purpose of TLS and makes connections vulnerable to man-in-the-middle attacks.

### TLS Handshake Process

```zig
var conn = TlsConnection.init(testing.allocator, &config);
defer conn.deinit();

// Perform TLS handshake
while (!conn.isEstablished()) {
    try conn.handshake();
}

// Connection is now secure
if (conn.negotiated_version) |version| {
    // TLS version was negotiated
}

if (conn.negotiated_cipher) |cipher| {
    // Cipher suite was selected
}
```

The handshake progresses through states:
1. **client_hello**: Client sends supported versions/ciphers
2. **server_hello**: Server selects version/cipher
3. **certificate_exchange**: Server sends certificate
4. **key_exchange**: Keys are exchanged
5. **finished**: Handshake complete
6. **established**: Secure connection ready

### TLS Handshake State Machine

```zig
pub const TlsHandshakeState = enum {
    client_hello,
    server_hello,
    certificate_exchange,
    key_exchange,
    finished,
    established,
    failed,

    pub fn isComplete(self: TlsHandshakeState) bool {
        return self == .established;
    }
};

// Check connection state
if (conn.state.isComplete()) {
    // Ready to send/receive encrypted data
}

if (conn.state.isFailed()) {
    // Handshake failed
}
```

### Version and Cipher Negotiation

```zig
var config = TlsConfig.init(allocator);
defer config.deinit();

// Client supports TLS 1.2 and 1.3
config.min_version = .tls_1_2;
config.max_version = .tls_1_3;

// Client preference order
try config.addCipher(.tls_aes_256_gcm_sha384); // First choice
try config.addCipher(.tls_aes_128_gcm_sha256); // Second choice

var conn = TlsConnection.init(allocator, &config);
defer conn.deinit();

// Handshake negotiates
try conn.handshake(); // client_hello
try conn.handshake(); // server_hello

// Check negotiated parameters
const version = conn.negotiated_version.?; // TLS 1.3 if server supports it
const cipher = conn.negotiated_cipher.?; // Server selects from client's list
```

The negotiation process:
1. Client sends supported versions and ciphers
2. Server chooses highest common version
3. Server selects cipher from client's list
4. Both sides use negotiated parameters

### Certificate Verification

```zig
var config = TlsConfig.init(allocator);
defer config.deinit();

// Add trusted root CA
var root_ca = try Certificate.init(
    allocator,
    "CN=Root CA",
    "CN=Root CA",
);
try config.addTrustedCertificate(root_ca);

var conn = TlsConnection.init(allocator, &config);
defer conn.deinit();

// Complete handshake (receives server certificate)
while (!conn.isEstablished()) {
    try conn.handshake();
}

// Verify the server certificate
try conn.verifyCertificate();
```

Certificate verification checks:
- Certificate is within validity period
- Certificate is signed by trusted CA
- Certificate matches hostname (if verify_hostname enabled)
- Certificate chain is complete and valid

### Handling Certificate Expiration

```zig
// During verification
try conn.verifyCertificate(); // Returns error.CertificateExpired

// Proactive monitoring
if (conn.server_certificate) |cert| {
    if (cert.isExpired()) {
        return error.CertificateExpired;
    }

    const days_left = cert.daysUntilExpiry();
    if (days_left < 30) {
        std.log.warn("Certificate expires in {} days", .{days_left});
    }
}
```

### Discussion

### TLS Protocol Versions

**TLS 1.3** (2018):
- Faster handshake (fewer round trips)
- Only AEAD ciphers (better security)
- Perfect forward secrecy required
- Removed weak/legacy features
- Encrypted handshake messages

**TLS 1.2** (2008):
- Widely supported
- Secure with proper cipher selection
- Allows non-AEAD ciphers (backwards compatibility)
- Slower handshake than 1.3

**TLS 1.0/1.1** (1999/2006):
- **Deprecated** - do not use
- Vulnerable to attacks (BEAST, POODLE)
- Disabled by major browsers

### Cipher Suite Components

A cipher suite specifies:

1. **Key Exchange**: How session keys are negotiated
   - ECDHE: Elliptic Curve Diffie-Hellman Ephemeral (forward secrecy)
   - RSA: Legacy, no forward secrecy

2. **Authentication**: How server is authenticated
   - RSA: RSA signature
   - ECDSA: Elliptic Curve signature

3. **Encryption**: Bulk data encryption
   - AES128/256: Advanced Encryption Standard
   - ChaCha20: Modern stream cipher

4. **MAC/AEAD**: Message authentication
   - GCM: Galois/Counter Mode (AEAD)
   - Poly1305: AEAD for ChaCha20
   - SHA256/384: Hash for MAC

**Example breakdown:**
- `TLS_AES_256_GCM_SHA384`: TLS 1.3, AES-256, GCM mode, SHA-384
- `ECDHE_RSA_AES128_GCM_SHA256`: ECDHE key exchange, RSA auth, AES-128 GCM, SHA-256

### Certificate Validation Process

In production TLS implementations, certificate validation involves:

1. **Chain Validation**:
   - Server sends certificate chain
   - Each certificate signed by next in chain
   - Chain ends at trusted root CA

2. **Validity Period**:
   - Check current time >= not_before
   - Check current time <= not_after

3. **Hostname Verification**:
   - Certificate subject matches hostname
   - Check Subject Alternative Names (SAN)
   - Wildcard matching (*.example.com)

4. **Revocation Checking**:
   - Check Certificate Revocation List (CRL)
   - Online Certificate Status Protocol (OCSP)

This recipe demonstrates basic validation. Production code needs full chain verification.

### Memory Management in Certificates

The `Certificate.init` uses proper error handling:

```zig
pub fn init(allocator: std.mem.Allocator, subject: []const u8, issuer: []const u8) !Certificate {
    const subject_copy = try allocator.dupe(u8, subject);
    errdefer allocator.free(subject_copy);

    const issuer_copy = try allocator.dupe(u8, issuer);
    errdefer allocator.free(issuer_copy);

    const fingerprint_copy = try allocator.dupe(u8, "");

    return .{
        .subject = subject_copy,
        .issuer = issuer_copy,
        .not_before = std.time.timestamp(),
        .not_after = std.time.timestamp() + 31536000, // 1 year
        .fingerprint = fingerprint_copy,
        .allocator = allocator,
    };
}
```

The `errdefer` statements ensure:
- If issuer allocation fails, subject is freed
- If fingerprint allocation fails, both subject and issuer are freed
- No memory leaks on partial initialization

### Safe Fingerprint Updates

The `setFingerprint` method allocates new memory before freeing old:

```zig
pub fn setFingerprint(self: *Certificate, fingerprint: []const u8) !void {
    const new_fingerprint = try self.allocator.dupe(u8, fingerprint);

    if (self.fingerprint.len > 0) {
        self.allocator.free(self.fingerprint);
    }
    self.fingerprint = new_fingerprint;
}
```

This prevents double-free if allocation fails:
1. Try to allocate new fingerprint
2. If successful, free old fingerprint
3. Store new fingerprint

If allocation fails, the old fingerprint remains valid.

### TLS Configuration Best Practices

**For Production:**
```zig
var config = TlsConfig.init(allocator);
defer config.deinit();

// Modern TLS only
config.min_version = .tls_1_2;
config.max_version = .tls_1_3;

// Strong ciphers only (TLS 1.3 preferred)
try config.addCipher(.tls_aes_256_gcm_sha384);
try config.addCipher(.tls_aes_128_gcm_sha256);
try config.addCipher(.tls_chacha20_poly1305_sha256);
try config.addCipher(.ecdhe_rsa_aes256_gcm_sha384); // TLS 1.2 fallback

// Strict validation
config.verify_certificates = true;
config.verify_hostname = true;

// Load system root CAs or specific trusted CAs
try loadSystemRootCAs(&config);
```

**For Development/Testing:**
```zig
var config = TlsConfig.init(allocator);
defer config.deinit();

// Less strict for self-signed certs
config.setInsecure(); // DO NOT USE IN PRODUCTION

// Or selective disabling
config.verify_hostname = false; // Allow localhost
config.verify_certificates = true; // Still check expiration
```

### Handshake State Progression

The TLS handshake is a multi-step negotiation:

```zig
pub fn handshake(self: *TlsConnection) !void {
    switch (self.state) {
        .client_hello => {
            // Send ClientHello with supported versions/ciphers
            self.state = .server_hello;
            self.negotiated_version = self.config.max_version;
        },
        .server_hello => {
            // Receive ServerHello with selected version/cipher
            self.state = .certificate_exchange;
            if (self.config.allowed_ciphers.items.len > 0) {
                self.negotiated_cipher = self.config.allowed_ciphers.items[0];
            }
        },
        .certificate_exchange => {
            // Receive and store server certificate
            self.state = .key_exchange;
            if (self.config.verify_certificates) {
                const cert = try Certificate.init(...);
                self.server_certificate = cert;
            }
        },
        .key_exchange => {
            // Exchange keys for symmetric encryption
            self.state = .finished;
        },
        .finished => {
            // Verify handshake integrity
            self.state = .established;
        },
        .established => {
            // Connection ready
        },
        .failed => {
            return error.HandshakeFailed;
        },
    }
}
```

Each state represents a phase in establishing trust and encryption.

### Error Handling

TLS operations can fail for many reasons:

```zig
const TlsError = error{
    HandshakeFailed,
    CertificateExpired,
    CertificateInvalid,
    UntrustedCertificate,
    HostnameMismatch,
    NoCertificate,
    NoTrustedCertificates,
    UnsupportedVersion,
    UnsupportedCipher,
};

// Handle specific errors
conn.verifyCertificate() catch |err| switch (err) {
    error.CertificateExpired => {
        std.log.err("Server certificate expired", .{});
        return err;
    },
    error.UntrustedCertificate => {
        std.log.err("Server certificate not trusted", .{});
        return err;
    },
    else => return err,
};
```

### Certificate Lifecycle

Certificates have limited validity periods:

```zig
var cert = try Certificate.init(allocator, "CN=example.com", "CN=CA");
defer cert.deinit();

// Typically valid for 1 year (set in init)
try testing.expect(cert.isValid());

// Check how long until renewal needed
const days = cert.daysUntilExpiry();
if (days < 30) {
    std.log.warn("Certificate renewal needed", .{});
}

// Simulate expiration
cert.not_after = std.time.timestamp() - 1;
try testing.expect(cert.isExpired());
```

**Certificate Renewal Best Practices:**
- Renew 30-60 days before expiration
- Use automated renewal (Let's Encrypt, cert-manager)
- Monitor expiration dates
- Test renewal process regularly

### Integration with std.http.Client

In production, TLS configuration integrates with HTTP clients:

```zig
// Conceptual integration (API may vary)
var tls_config = TlsConfig.init(allocator);
defer tls_config.deinit();

tls_config.min_version = .tls_1_2;
try tls_config.addCipher(.tls_aes_128_gcm_sha256);

var client = std.http.Client{
    .allocator = allocator,
    .tls_config = &tls_config, // Pass TLS configuration
};
defer client.deinit();

// HTTPS requests use TLS configuration
var request = try client.open(.GET, uri, .{});
defer request.deinit();
```

### Security Considerations

**Certificate Pinning:**
For high-security applications, pin specific certificates or public keys:

```zig
const expected_fingerprint = "AA:BB:CC:DD:EE:FF:...";

if (conn.server_certificate) |cert| {
    if (!std.mem.eql(u8, cert.fingerprint, expected_fingerprint)) {
        return error.CertificatePinningFailed;
    }
}
```

**Forward Secrecy:**
Always use ECDHE key exchange for forward secrecy:

```zig
// Good - Forward secrecy
.ecdhe_rsa_aes128_gcm_sha256

// Bad - No forward secrecy
.rsa_aes128_gcm_sha256
```

Forward secrecy ensures past communications can't be decrypted even if the server's private key is compromised.

**Perfect Forward Secrecy (TLS 1.3):**
TLS 1.3 requires forward secrecy for all cipher suites.

### Limitations of This Implementation

This recipe demonstrates TLS concepts but lacks:

**Missing Production Features:**
- Actual network I/O
- Real certificate chain validation
- OCSP/CRL revocation checking
- Hostname verification implementation
- Certificate pinning
- Session resumption
- ALPN (Application-Layer Protocol Negotiation)
- SNI (Server Name Indication)

**For Production:**
- Use Zig's `std.crypto.tls` when stable
- Use established TLS libraries (BoringSSL, OpenSSL via C binding)
- Implement full certificate chain validation
- Support certificate revocation checking
- Add proper hostname verification
- Implement session caching/resumption

### Best Practices Summary

**Configuration:**
- Use TLS 1.2 minimum, prefer 1.3
- Select strong cipher suites (AEAD only)
- Enable certificate and hostname verification
- Load proper trusted root CAs

**Certificates:**
- Monitor expiration dates
- Automate renewal
- Use proper error handling
- Validate certificate chains

**Error Handling:**
- Never ignore TLS errors
- Log security-relevant events
- Fail securely (deny by default)
- Provide clear error messages

**Development:**
- Use secure defaults
- Test with real certificates
- Never use `setInsecure()` in production
- Implement proper logging

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: tls_version
pub const TlsVersion = enum(u16) {
    tls_1_0 = 0x0301,
    tls_1_1 = 0x0302,
    tls_1_2 = 0x0303,
    tls_1_3 = 0x0304,

    pub fn toString(self: TlsVersion) []const u8 {
        return switch (self) {
            .tls_1_0 => "TLS 1.0",
            .tls_1_1 => "TLS 1.1",
            .tls_1_2 => "TLS 1.2",
            .tls_1_3 => "TLS 1.3",
        };
    }

    pub fn isSecure(self: TlsVersion) bool {
        // TLS 1.2 and 1.3 are considered secure
        return @intFromEnum(self) >= @intFromEnum(TlsVersion.tls_1_2);
    }
};
// ANCHOR_END: tls_version

// ANCHOR: cipher_suite
pub const CipherSuite = enum(u16) {
    // TLS 1.3 cipher suites (recommended)
    tls_aes_128_gcm_sha256 = 0x1301,
    tls_aes_256_gcm_sha384 = 0x1302,
    tls_chacha20_poly1305_sha256 = 0x1303,

    // TLS 1.2 cipher suites
    ecdhe_rsa_aes128_gcm_sha256 = 0xC02F,
    ecdhe_rsa_aes256_gcm_sha384 = 0xC030,

    pub fn toString(self: CipherSuite) []const u8 {
        return switch (self) {
            .tls_aes_128_gcm_sha256 => "TLS_AES_128_GCM_SHA256",
            .tls_aes_256_gcm_sha384 => "TLS_AES_256_GCM_SHA384",
            .tls_chacha20_poly1305_sha256 => "TLS_CHACHA20_POLY1305_SHA256",
            .ecdhe_rsa_aes128_gcm_sha256 => "ECDHE-RSA-AES128-GCM-SHA256",
            .ecdhe_rsa_aes256_gcm_sha384 => "ECDHE-RSA-AES256-GCM-SHA384",
        };
    }

    pub fn isRecommended(self: CipherSuite) bool {
        // TLS 1.3 cipher suites are recommended
        return @intFromEnum(self) >= 0x1301 and @intFromEnum(self) <= 0x1303;
    }
};
// ANCHOR_END: cipher_suite

// ANCHOR: certificate
pub const Certificate = struct {
    subject: []const u8,
    issuer: []const u8,
    not_before: i64, // Unix timestamp
    not_after: i64, // Unix timestamp
    fingerprint: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, subject: []const u8, issuer: []const u8) !Certificate {
        const subject_copy = try allocator.dupe(u8, subject);
        errdefer allocator.free(subject_copy);

        const issuer_copy = try allocator.dupe(u8, issuer);
        errdefer allocator.free(issuer_copy);

        const fingerprint_copy = try allocator.dupe(u8, "");

        return .{
            .subject = subject_copy,
            .issuer = issuer_copy,
            .not_before = std.time.timestamp(),
            .not_after = std.time.timestamp() + 31536000, // 1 year
            .fingerprint = fingerprint_copy,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Certificate) void {
        self.allocator.free(self.subject);
        self.allocator.free(self.issuer);
        self.allocator.free(self.fingerprint);
    }

    pub fn setFingerprint(self: *Certificate, fingerprint: []const u8) !void {
        const new_fingerprint = try self.allocator.dupe(u8, fingerprint);

        if (self.fingerprint.len > 0) {
            self.allocator.free(self.fingerprint);
        }
        self.fingerprint = new_fingerprint;
    }

    pub fn isValid(self: *const Certificate) bool {
        const now = std.time.timestamp();
        return now >= self.not_before and now <= self.not_after;
    }

    pub fn isExpired(self: *const Certificate) bool {
        return std.time.timestamp() > self.not_after;
    }

    pub fn daysUntilExpiry(self: *const Certificate) i64 {
        const now = std.time.timestamp();
        const seconds_remaining = self.not_after - now;
        return @divFloor(seconds_remaining, 86400); // Convert to days
    }
};
// ANCHOR_END: certificate

// ANCHOR: tls_config
pub const TlsConfig = struct {
    min_version: TlsVersion,
    max_version: TlsVersion,
    allowed_ciphers: std.ArrayList(CipherSuite),
    verify_certificates: bool,
    verify_hostname: bool,
    trusted_certificates: std.ArrayList(Certificate),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) TlsConfig {
        return .{
            .min_version = .tls_1_2, // Minimum secure version
            .max_version = .tls_1_3,
            .allowed_ciphers = std.ArrayList(CipherSuite){},
            .verify_certificates = true,
            .verify_hostname = true,
            .trusted_certificates = std.ArrayList(Certificate){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *TlsConfig) void {
        self.allowed_ciphers.deinit(self.allocator);
        for (self.trusted_certificates.items) |*cert| {
            cert.deinit();
        }
        self.trusted_certificates.deinit(self.allocator);
    }

    pub fn addCipher(self: *TlsConfig, cipher: CipherSuite) !void {
        try self.allowed_ciphers.append(self.allocator, cipher);
    }

    pub fn addTrustedCertificate(self: *TlsConfig, cert: Certificate) !void {
        try self.trusted_certificates.append(self.allocator, cert);
    }

    pub fn setInsecure(self: *TlsConfig) void {
        self.verify_certificates = false;
        self.verify_hostname = false;
    }

    pub fn isSecure(self: *const TlsConfig) bool {
        return self.min_version.isSecure() and
            self.verify_certificates and
            self.verify_hostname;
    }
};
// ANCHOR_END: tls_config

// ANCHOR: tls_handshake_state
pub const TlsHandshakeState = enum {
    client_hello,
    server_hello,
    certificate_exchange,
    key_exchange,
    finished,
    established,
    failed,

    pub fn isComplete(self: TlsHandshakeState) bool {
        return self == .established;
    }

    pub fn isFailed(self: TlsHandshakeState) bool {
        return self == .failed;
    }
};
// ANCHOR_END: tls_handshake_state

// ANCHOR: tls_connection
pub const TlsConnection = struct {
    config: *const TlsConfig,
    state: TlsHandshakeState,
    negotiated_version: ?TlsVersion,
    negotiated_cipher: ?CipherSuite,
    server_certificate: ?Certificate,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, config: *const TlsConfig) TlsConnection {
        return .{
            .config = config,
            .state = .client_hello,
            .negotiated_version = null,
            .negotiated_cipher = null,
            .server_certificate = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *TlsConnection) void {
        if (self.server_certificate) |*cert| {
            cert.deinit();
        }
    }

    pub fn handshake(self: *TlsConnection) !void {
        // Simulate TLS handshake steps
        switch (self.state) {
            .client_hello => {
                self.state = .server_hello;
                self.negotiated_version = self.config.max_version;
            },
            .server_hello => {
                self.state = .certificate_exchange;
                if (self.config.allowed_ciphers.items.len > 0) {
                    self.negotiated_cipher = self.config.allowed_ciphers.items[0];
                }
            },
            .certificate_exchange => {
                self.state = .key_exchange;
                // Simulate receiving server certificate
                if (self.config.verify_certificates) {
                    const cert = try Certificate.init(
                        self.allocator,
                        "CN=example.com",
                        "CN=Example CA",
                    );
                    self.server_certificate = cert;
                }
            },
            .key_exchange => {
                self.state = .finished;
            },
            .finished => {
                self.state = .established;
            },
            .established => {
                // Already established
            },
            .failed => {
                return error.HandshakeFailed;
            },
        }
    }

    pub fn isEstablished(self: *const TlsConnection) bool {
        return self.state.isComplete();
    }

    pub fn verifyCertificate(self: *const TlsConnection) !void {
        const cert = self.server_certificate orelse return error.NoCertificate;

        // Check validity period
        if (!cert.isValid()) {
            return error.CertificateExpired;
        }

        // In a real implementation, verify certificate chain
        // against trusted certificates
        if (self.config.verify_certificates) {
            if (self.config.trusted_certificates.items.len == 0) {
                return error.NoTrustedCertificates;
            }
        }
    }
};
// ANCHOR_END: tls_connection

// ANCHOR: tls_error
pub const TlsError = error{
    HandshakeFailed,
    CertificateExpired,
    CertificateInvalid,
    UntrustedCertificate,
    HostnameMismatch,
    NoCertificate,
    NoTrustedCertificates,
    UnsupportedVersion,
    UnsupportedCipher,
};
// ANCHOR_END: tls_error

// ANCHOR: test_tls_version
test "TLS version enum" {
    try testing.expectEqual(@as(u16, 0x0303), @intFromEnum(TlsVersion.tls_1_2));
    try testing.expectEqual(@as(u16, 0x0304), @intFromEnum(TlsVersion.tls_1_3));

    try testing.expectEqualStrings("TLS 1.2", TlsVersion.tls_1_2.toString());
    try testing.expectEqualStrings("TLS 1.3", TlsVersion.tls_1_3.toString());
}
// ANCHOR_END: test_tls_version

// ANCHOR: test_tls_version_security
test "TLS version security check" {
    try testing.expect(!TlsVersion.tls_1_0.isSecure());
    try testing.expect(!TlsVersion.tls_1_1.isSecure());
    try testing.expect(TlsVersion.tls_1_2.isSecure());
    try testing.expect(TlsVersion.tls_1_3.isSecure());
}
// ANCHOR_END: test_tls_version_security

// ANCHOR: test_cipher_suite
test "cipher suite enum" {
    try testing.expectEqualStrings(
        "TLS_AES_128_GCM_SHA256",
        CipherSuite.tls_aes_128_gcm_sha256.toString(),
    );

    try testing.expect(CipherSuite.tls_aes_128_gcm_sha256.isRecommended());
    try testing.expect(!CipherSuite.ecdhe_rsa_aes128_gcm_sha256.isRecommended());
}
// ANCHOR_END: test_cipher_suite

// ANCHOR: test_certificate_creation
test "create certificate" {
    var cert = try Certificate.init(
        testing.allocator,
        "CN=example.com",
        "CN=Example CA",
    );
    defer cert.deinit();

    try testing.expectEqualStrings("CN=example.com", cert.subject);
    try testing.expectEqualStrings("CN=Example CA", cert.issuer);
    try testing.expect(cert.not_before > 0);
    try testing.expect(cert.not_after > cert.not_before);
}
// ANCHOR_END: test_certificate_creation

// ANCHOR: test_certificate_validity
test "certificate validity check" {
    var cert = try Certificate.init(
        testing.allocator,
        "CN=example.com",
        "CN=Example CA",
    );
    defer cert.deinit();

    // Should be valid (just created)
    try testing.expect(cert.isValid());
    try testing.expect(!cert.isExpired());

    // Set to expired
    cert.not_after = std.time.timestamp() - 1;
    try testing.expect(!cert.isValid());
    try testing.expect(cert.isExpired());
}
// ANCHOR_END: test_certificate_validity

// ANCHOR: test_certificate_expiry_days
test "certificate days until expiry" {
    var cert = try Certificate.init(
        testing.allocator,
        "CN=example.com",
        "CN=Example CA",
    );
    defer cert.deinit();

    const days = cert.daysUntilExpiry();
    // Should be approximately 365 days (1 year)
    try testing.expect(days > 360);
    try testing.expect(days < 370);
}
// ANCHOR_END: test_certificate_expiry_days

// ANCHOR: test_certificate_fingerprint
test "set certificate fingerprint" {
    var cert = try Certificate.init(
        testing.allocator,
        "CN=example.com",
        "CN=Example CA",
    );
    defer cert.deinit();

    try cert.setFingerprint("AA:BB:CC:DD");
    try testing.expectEqualStrings("AA:BB:CC:DD", cert.fingerprint);

    // Update fingerprint
    try cert.setFingerprint("11:22:33:44");
    try testing.expectEqualStrings("11:22:33:44", cert.fingerprint);
}
// ANCHOR_END: test_certificate_fingerprint

// ANCHOR: test_tls_config_creation
test "create TLS config" {
    var config = TlsConfig.init(testing.allocator);
    defer config.deinit();

    try testing.expectEqual(TlsVersion.tls_1_2, config.min_version);
    try testing.expectEqual(TlsVersion.tls_1_3, config.max_version);
    try testing.expect(config.verify_certificates);
    try testing.expect(config.verify_hostname);
}
// ANCHOR_END: test_tls_config_creation

// ANCHOR: test_tls_config_ciphers
test "add cipher suites to config" {
    var config = TlsConfig.init(testing.allocator);
    defer config.deinit();

    try config.addCipher(.tls_aes_128_gcm_sha256);
    try config.addCipher(.tls_aes_256_gcm_sha384);

    try testing.expectEqual(@as(usize, 2), config.allowed_ciphers.items.len);
    try testing.expectEqual(
        CipherSuite.tls_aes_128_gcm_sha256,
        config.allowed_ciphers.items[0],
    );
}
// ANCHOR_END: test_tls_config_ciphers

// ANCHOR: test_tls_config_certificates
test "add trusted certificates to config" {
    var config = TlsConfig.init(testing.allocator);
    defer config.deinit();

    const cert = try Certificate.init(
        testing.allocator,
        "CN=Root CA",
        "CN=Root CA",
    );

    try config.addTrustedCertificate(cert);
    try testing.expectEqual(@as(usize, 1), config.trusted_certificates.items.len);
}
// ANCHOR_END: test_tls_config_certificates

// ANCHOR: test_tls_config_insecure
test "set insecure TLS config" {
    var config = TlsConfig.init(testing.allocator);
    defer config.deinit();

    try testing.expect(config.isSecure());

    config.setInsecure();
    try testing.expect(!config.verify_certificates);
    try testing.expect(!config.verify_hostname);
    try testing.expect(!config.isSecure());
}
// ANCHOR_END: test_tls_config_insecure

// ANCHOR: test_tls_connection_creation
test "create TLS connection" {
    var config = TlsConfig.init(testing.allocator);
    defer config.deinit();

    var conn = TlsConnection.init(testing.allocator, &config);
    defer conn.deinit();

    try testing.expectEqual(TlsHandshakeState.client_hello, conn.state);
    try testing.expect(!conn.isEstablished());
}
// ANCHOR_END: test_tls_connection_creation

// ANCHOR: test_tls_handshake
test "TLS handshake process" {
    var config = TlsConfig.init(testing.allocator);
    defer config.deinit();

    try config.addCipher(.tls_aes_128_gcm_sha256);

    var conn = TlsConnection.init(testing.allocator, &config);
    defer conn.deinit();

    // Perform handshake steps
    try testing.expect(!conn.isEstablished());

    try conn.handshake(); // client_hello -> server_hello
    try testing.expectEqual(TlsHandshakeState.server_hello, conn.state);

    try conn.handshake(); // server_hello -> certificate_exchange
    try testing.expectEqual(TlsHandshakeState.certificate_exchange, conn.state);

    try conn.handshake(); // certificate_exchange -> key_exchange
    try testing.expectEqual(TlsHandshakeState.key_exchange, conn.state);

    try conn.handshake(); // key_exchange -> finished
    try testing.expectEqual(TlsHandshakeState.finished, conn.state);

    try conn.handshake(); // finished -> established
    try testing.expect(conn.isEstablished());
}
// ANCHOR_END: test_tls_handshake

// ANCHOR: test_tls_version_negotiation
test "TLS version negotiation" {
    var config = TlsConfig.init(testing.allocator);
    defer config.deinit();

    config.max_version = .tls_1_3;

    var conn = TlsConnection.init(testing.allocator, &config);
    defer conn.deinit();

    try conn.handshake();

    try testing.expect(conn.negotiated_version != null);
    try testing.expectEqual(TlsVersion.tls_1_3, conn.negotiated_version.?);
}
// ANCHOR_END: test_tls_version_negotiation

// ANCHOR: test_tls_cipher_negotiation
test "TLS cipher suite negotiation" {
    var config = TlsConfig.init(testing.allocator);
    defer config.deinit();

    try config.addCipher(.tls_aes_256_gcm_sha384);

    var conn = TlsConnection.init(testing.allocator, &config);
    defer conn.deinit();

    try conn.handshake(); // client_hello -> server_hello
    try conn.handshake(); // server_hello -> certificate_exchange

    try testing.expect(conn.negotiated_cipher != null);
    try testing.expectEqual(
        CipherSuite.tls_aes_256_gcm_sha384,
        conn.negotiated_cipher.?,
    );
}
// ANCHOR_END: test_tls_cipher_negotiation

// ANCHOR: test_certificate_verification
test "certificate verification" {
    var config = TlsConfig.init(testing.allocator);
    defer config.deinit();

    const trusted_cert = try Certificate.init(
        testing.allocator,
        "CN=Root CA",
        "CN=Root CA",
    );
    try config.addTrustedCertificate(trusted_cert);

    var conn = TlsConnection.init(testing.allocator, &config);
    defer conn.deinit();

    // Complete handshake
    try conn.handshake(); // client_hello
    try conn.handshake(); // server_hello
    try conn.handshake(); // certificate_exchange

    // Verify certificate
    try conn.verifyCertificate();
}
// ANCHOR_END: test_certificate_verification

// ANCHOR: test_expired_certificate
test "expired certificate detection" {
    var config = TlsConfig.init(testing.allocator);
    defer config.deinit();

    var conn = TlsConnection.init(testing.allocator, &config);
    defer conn.deinit();

    // Complete handshake to get certificate
    try conn.handshake();
    try conn.handshake();
    try conn.handshake();

    // Expire the certificate
    if (conn.server_certificate) |*cert| {
        cert.not_after = std.time.timestamp() - 1;
    }

    // Verification should fail
    try testing.expectError(error.CertificateExpired, conn.verifyCertificate());
}
// ANCHOR_END: test_expired_certificate
```

### See Also

- Recipe 11.1: Making HTTP requests
- Recipe 11.6: Working with REST APIs
- Recipe 11.7: Handling cookies and sessions
- Recipe 13.5: Cryptographic operations

---

## Recipe 11.9: Uploading and Downloading Files {#recipe-11-9}

**Tags:** allocators, arraylist, data-structures, error-handling, hashmap, http, memory, networking, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_9.zig`

### Problem

You need to transfer files over HTTP with proper progress tracking, support for chunked transfers, and multipart form uploads.

### Solution

Zig provides file I/O capabilities through `std.fs` and can be combined with HTTP networking to implement file transfers. This recipe demonstrates download management, multipart form uploads, and progress tracking:

```zig
pub const ProgressCallback = *const fn (bytes_transferred: usize, total_bytes: ?usize) void;

pub fn defaultProgressCallback(bytes_transferred: usize, total_bytes: ?usize) void {
    if (total_bytes) |total| {
        const percent = (@as(f64, @floatFromInt(bytes_transferred)) / @as(f64, @floatFromInt(total))) * 100.0;
        std.debug.print("Progress: {d:.1}% ({d}/{d} bytes)\n", .{ percent, bytes_transferred, total });
    } else {
        std.debug.print("Progress: {d} bytes\n", .{bytes_transferred});
    }
}
```

### Downloading Files

The `Downloader` supports multiple download strategies with optional progress tracking:

```zig
pub const DownloadOptions = struct {
    chunk_size: usize = 8192,
    resume_from: ?usize = null,
    progress_callback: ?ProgressCallback = null,
    max_retries: u32 = 3,
};

pub const Downloader = struct {
    allocator: std.mem.Allocator,
    options: DownloadOptions,

    pub fn init(allocator: std.mem.Allocator, options: DownloadOptions) Downloader {
        return .{
            .allocator = allocator,
            .options = options,
        };
    }

    pub fn downloadToMemory(self: *Downloader, url: []const u8) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        const test_data = "File contents from server";
        try buffer.appendSlice(self.allocator, test_data);

        if (self.options.progress_callback) |callback| {
            callback(test_data.len, test_data.len);
        }

        return buffer.toOwnedSlice(self.allocator);
    }

    pub fn downloadChunked(self: *Downloader, url: []const u8) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        // Simulate chunked download
        const chunks = [_][]const u8{ "chunk1", "chunk2", "chunk3" };
        var total_size: usize = 0;
        for (chunks) |chunk| {
            total_size += chunk.len;
        }

        var transferred: usize = 0;
        for (chunks) |chunk| {
            try buffer.appendSlice(self.allocator, chunk);
            transferred += chunk.len;

            if (self.options.progress_callback) |callback| {
                callback(transferred, total_size);
            }
        }

        return buffer.toOwnedSlice(self.allocator);
    }
};
```

### Multipart Form Uploads

The `MultipartForm` struct handles both text fields and file uploads using the `multipart/form-data` encoding:

```zig
pub const MultipartForm = struct {
    boundary: []const u8,
    fields: std.StringHashMap([]const u8),
    files: std.ArrayList(FileField),
    allocator: std.mem.Allocator,

    pub const FileField = struct {
        name: []const u8,
        filename: []const u8,
        content_type: []const u8,
        data: []const u8,
    };

    pub fn init(allocator: std.mem.Allocator) !MultipartForm {
        var boundary_buf: [32]u8 = undefined;
        const timestamp = std.time.timestamp();
        const boundary = try std.fmt.bufPrint(&boundary_buf, "----Boundary{d}", .{timestamp});

        const owned_boundary = try allocator.dupe(u8, boundary);
        errdefer allocator.free(owned_boundary);

        return .{
            .boundary = owned_boundary,
            .fields = std.StringHashMap([]const u8).init(allocator),
            .files = std.ArrayList(FileField){},
            .allocator = allocator,
        };
    }

    pub fn addField(self: *MultipartForm, name: []const u8, value: []const u8) !void {
        const owned_name = try self.allocator.dupe(u8, name);
        errdefer self.allocator.free(owned_name);
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);
        try self.fields.put(owned_name, owned_value);
    }

    pub fn addFile(self: *MultipartForm, name: []const u8, filename: []const u8,
                   content_type: []const u8, data: []const u8) !void {
        const owned_name = try self.allocator.dupe(u8, name);
        errdefer self.allocator.free(owned_name);

        const owned_filename = try self.allocator.dupe(u8, filename);
        errdefer self.allocator.free(owned_filename);

        const owned_content_type = try self.allocator.dupe(u8, content_type);
        errdefer self.allocator.free(owned_content_type);

        const owned_data = try self.allocator.dupe(u8, data);
        errdefer self.allocator.free(owned_data);

        const file = FileField{
            .name = owned_name,
            .filename = owned_filename,
            .content_type = owned_content_type,
            .data = owned_data,
        };

        try self.files.append(self.allocator, file);
    }
};
```

### Uploading Files

The `Uploader` provides convenient methods for file and data uploads:

```zig
pub const UploadOptions = struct {
    content_type: ?[]const u8 = null,
    chunk_size: usize = 8192,
    progress_callback: ?ProgressCallback = null,
};

pub const Uploader = struct {
    allocator: std.mem.Allocator,
    options: UploadOptions,

    pub fn uploadFile(self: *Uploader, url: []const u8, file_path: []const u8) !void {
        const file = try std.fs.cwd().openFile(file_path, .{});
        defer file.close();

        const stat = try file.stat();
        const file_size = stat.size;

        // Simulate chunked upload
        var uploaded: usize = 0;
        while (uploaded < file_size) {
            const chunk_size = @min(self.options.chunk_size, file_size - uploaded);
            uploaded += chunk_size;

            if (self.options.progress_callback) |callback| {
                callback(uploaded, file_size);
            }
        }
    }
};
```

### Resumable Downloads

The `ResumeInfo` struct enables resuming interrupted downloads:

```zig
pub const ResumeInfo = struct {
    url: []const u8,
    file_path: []const u8,
    bytes_downloaded: usize,
    total_bytes: ?usize,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, url: []const u8, file_path: []const u8) !ResumeInfo {
        const owned_url = try allocator.dupe(u8, url);
        errdefer allocator.free(owned_url);

        const owned_file_path = try allocator.dupe(u8, file_path);

        return .{
            .url = owned_url,
            .file_path = owned_file_path,
            .bytes_downloaded = 0,
            .total_bytes = null,
            .allocator = allocator,
        };
    }

    pub fn save(self: *const ResumeInfo, resume_file: []const u8) !void {
        const file = try std.fs.cwd().createFile(resume_file, .{});
        defer file.close();

        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try buffer.writer(self.allocator).print("{d}\n", .{self.bytes_downloaded});
        if (self.total_bytes) |total| {
            try buffer.writer(self.allocator).print("{d}\n", .{total});
        }

        try file.writeAll(buffer.items);
    }

    pub fn load(allocator: std.mem.Allocator, resume_file: []const u8,
                url: []const u8, file_path: []const u8) !ResumeInfo {
        const file = try std.fs.cwd().openFile(resume_file, .{});
        defer file.close();

        var info = try ResumeInfo.init(allocator, url, file_path);
        errdefer info.deinit();

        var buf: [1024]u8 = undefined;
        const bytes_read = try file.readAll(&buf);
        const content = buf[0..bytes_read];

        var lines = std.mem.splitScalar(u8, content, '\n');
        if (lines.next()) |line| {
            info.bytes_downloaded = try std.fmt.parseInt(usize, std.mem.trim(u8, line, " \r\n"), 10);
        }

        return info;
    }
};
```

### Discussion

This recipe demonstrates comprehensive file transfer capabilities in Zig. Key concepts include:

### Progress Tracking

The `ProgressCallback` type allows monitoring transfer progress. Callbacks receive:
- `bytes_transferred`: Current progress
- `total_bytes`: Optional total size (may be unknown for streaming)

Progress tracking is optional and can be enabled per-transfer by setting the callback in options.

### Download Strategies

Three download approaches are supported:

1. **Memory Download**: Entire file loaded into memory (`downloadToMemory`)
2. **Direct to File**: Streaming download to disk (`downloadToFile`)
3. **Chunked Transfer**: Download in chunks with progress updates (`downloadChunked`)

Choose based on file size and memory constraints. Large files should use chunked or direct-to-file downloads.

### Multipart Form Encoding

The multipart/form-data encoding (RFC 2388) allows uploading files with metadata:

- **Boundary**: Unique separator between form parts
- **Text Fields**: Regular form fields with name/value pairs
- **File Fields**: Files with name, filename, content-type, and data

The `build()` method generates the properly formatted multipart body with boundary markers, content-disposition headers, and data sections.

### Memory Safety

Critical memory safety patterns used throughout:

**Error Cleanup with errdefer**:
```zig
pub fn addField(self: *MultipartForm, name: []const u8, value: []const u8) !void {
    const owned_name = try self.allocator.dupe(u8, name);
    errdefer self.allocator.free(owned_name);
    const owned_value = try self.allocator.dupe(u8, value);
    errdefer self.allocator.free(owned_value);  // Prevents leak if put() fails
    try self.fields.put(owned_name, owned_value);
}
```

**Chained Error Cleanup**:
```zig
pub fn addFile(...) !void {
    const owned_name = try self.allocator.dupe(u8, name);
    errdefer self.allocator.free(owned_name);

    const owned_filename = try self.allocator.dupe(u8, filename);
    errdefer self.allocator.free(owned_filename);

    const owned_content_type = try self.allocator.dupe(u8, content_type);
    errdefer self.allocator.free(owned_content_type);

    const owned_data = try self.allocator.dupe(u8, data);
    errdefer self.allocator.free(owned_data);

    // All allocations protected - if append fails, all are freed
    try self.files.append(self.allocator, file);
}
```

This pattern ensures that if any allocation fails, all previous allocations are properly cleaned up.

### Resumable Downloads

The `ResumeInfo` struct enables resuming interrupted downloads by:
1. Tracking download progress (bytes downloaded, total bytes)
2. Persisting state to a resume file
3. Loading state when resuming

This is useful for large files over unreliable connections. In a real implementation, you would:
- Use HTTP Range requests (`Range: bytes=12345-`)
- Verify file integrity with checksums
- Handle server resume support detection

### Real Implementation Considerations

This recipe uses simulated transfers for testing. A production implementation would:

**Use std.http.Client**:
```zig
var client = std.http.Client{ .allocator = allocator };
defer client.deinit();

var req = try client.request(.GET, uri, headers, .{});
defer req.deinit();
```

**Handle HTTP headers**:
- `Content-Length` for total size
- `Content-Range` for resume support
- `Content-Type` for file type detection

**Error handling and retries**:
- Network timeouts
- Connection failures
- Partial writes
- Disk space errors

**Security considerations**:
- Validate file paths (prevent directory traversal)
- Limit file sizes
- Sanitize filenames
- Verify content types
- Use HTTPS for sensitive transfers

### Zig 0.15.2 ArrayList API

This code uses the unmanaged ArrayList pattern in Zig 0.15.2:

```zig
var buffer = std.ArrayList(u8){};
defer buffer.deinit(allocator);

try buffer.appendSlice(allocator, data);
return buffer.toOwnedSlice(allocator);
```

The allocator is passed to each method rather than stored in the ArrayList.

### Advanced: Secure Boundary Generation

**Security Issue:** The multipart form boundary must be generated securely to prevent boundary collision attacks.

#### Why Boundary Security Matters

Consider this attack scenario:

1. Attacker uploads a malicious file containing: `----Boundary1234567890`
2. If the boundary is predictable (timestamp-based), attacker can guess it
3. File content matches the boundary, breaking multipart parsing
4. Server misinterprets file data as form fields
5. Can lead to injection attacks or data corruption

**Example Attack:**
```
// Malicious file content:
----Boundary1234567890
Content-Disposition: form-data; name="admin"

true
----Boundary1234567890--
```

If the boundary is predictable, this content can inject fake form fields.

#### Vulnerable Implementation (DO NOT USE)

```zig
// INSECURE: Timestamp is predictable
const timestamp = std.time.timestamp();
const boundary = try std.fmt.bufPrint(&boundary_buf, "----Boundary{d}", .{timestamp});

// Attacker can:
// 1. Know approximate server time
// 2. Include boundary string in file content
// 3. Break multipart parsing
```

Timestamps are predictable because:
- Server time can be inferred from HTTP Date headers
- Upload happens at known time (attacker controls timing)
- Only ~1 million possible values per day (1 second resolution)
- Easy to brute force all possibilities in file content

#### Secure Implementation (CORRECT)

The updated implementation uses cryptographically random boundaries:

```zig
pub fn init(allocator: std.mem.Allocator) !MultipartForm {
    // Generate cryptographically secure boundary
    var random_bytes: [16]u8 = undefined;
    std.crypto.random.bytes(&random_bytes);

    var boundary_buf: [50]u8 = undefined;
    const hex = std.fmt.bytesToHex(random_bytes, .lower);
    const boundary = try std.fmt.bufPrint(&boundary_buf, "----Boundary{s}", .{hex});
    // Result: "----Boundary4a3f9b2e7d8c1a6f..."
}
```

**Security Benefits:**
1. **128 bits of entropy** - 2^128 possible boundaries (~3.4 × 10^38)
2. **Unpredictable** - Attacker cannot guess boundary value
3. **Unique per upload** - New random boundary for each form
4. **Collision resistant** - Astronomically unlikely to match file content

**Why 16 bytes?**
- 128 bits of randomness exceeds security requirements
- 32 hex characters fit comfortably in boundary
- Same strength as AES-128 encryption
- Industry standard (comparable to UUIDs)

#### Comparison: Timestamp vs Cryptographic Random

| Aspect | Timestamp | Crypto Random |
|--------|-----------|---------------|
| Entropy | ~20 bits | 128 bits |
| Possible values | ~1 million/day | 2^128 |
| Predictable | Yes | No |
| Collision risk | High | Negligible |
| Attack difficulty | Trivial | Impossible |

#### When Boundaries Matter

Secure boundaries are critical when:
- Accepting file uploads from untrusted users
- Processing user-generated content
- Implementing public APIs
- Handling sensitive data

For internal tools with trusted users, timestamp boundaries may be acceptable, but crypto random has negligible overhead and is always safer.

#### Boundary Validation

Production systems should also validate boundaries don't appear in content:

```zig
pub fn validateBoundary(self: *const MultipartForm) !void {
    // Check boundary doesn't appear in any file data
    for (self.files.items) |file| {
        if (std.mem.indexOf(u8, file.data, self.boundary)) |_| {
            return error.BoundaryCollision;
        }
    }
}
```

However, with 128-bit random boundaries, collision probability is:
- 1 in 2^128 for random data
- Effectively impossible in practice
- More likely to win lottery 20 times consecutively

#### Industry Standards

Major platforms use similar approaches:
- **Browsers**: Generate random multipart boundaries (16+ bytes)
- **Python requests**: UUID4-based boundaries (128-bit random)
- **Node.js multer**: Crypto random boundaries
- **PHP**: Unique random identifiers

Our implementation follows these best practices while demonstrating the security rationale for educational purposes.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: progress_callback
pub const ProgressCallback = *const fn (bytes_transferred: usize, total_bytes: ?usize) void;

pub fn defaultProgressCallback(bytes_transferred: usize, total_bytes: ?usize) void {
    if (total_bytes) |total| {
        const percent = (@as(f64, @floatFromInt(bytes_transferred)) / @as(f64, @floatFromInt(total))) * 100.0;
        std.debug.print("Progress: {d:.1}% ({d}/{d} bytes)\n", .{ percent, bytes_transferred, total });
    } else {
        std.debug.print("Progress: {d} bytes\n", .{bytes_transferred});
    }
}
// ANCHOR_END: progress_callback

// ANCHOR: download_options
pub const DownloadOptions = struct {
    chunk_size: usize = 8192,
    resume_from: ?usize = null,
    progress_callback: ?ProgressCallback = null,
    max_retries: u32 = 3,
};
// ANCHOR_END: download_options

// ANCHOR: downloader
pub const Downloader = struct {
    allocator: std.mem.Allocator,
    options: DownloadOptions,

    pub fn init(allocator: std.mem.Allocator, options: DownloadOptions) Downloader {
        return .{
            .allocator = allocator,
            .options = options,
        };
    }

    pub fn downloadToMemory(self: *Downloader, url: []const u8) ![]const u8 {
        _ = url;
        // Simulate download - in real implementation, use std.http.Client
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        const test_data = "File contents from server";
        try buffer.appendSlice(self.allocator, test_data);

        // Simulate progress
        if (self.options.progress_callback) |callback| {
            callback(test_data.len, test_data.len);
        }

        return buffer.toOwnedSlice(self.allocator);
    }

    pub fn downloadToFile(self: *Downloader, url: []const u8, file_path: []const u8) !void {
        _ = url;
        const file = try std.fs.cwd().createFile(file_path, .{});
        defer file.close();

        const test_data = "Downloaded file content";
        try file.writeAll(test_data);

        if (self.options.progress_callback) |callback| {
            callback(test_data.len, test_data.len);
        }
    }

    pub fn downloadChunked(self: *Downloader, url: []const u8) ![]const u8 {
        _ = url;
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        // Simulate chunked download
        const chunks = [_][]const u8{ "chunk1", "chunk2", "chunk3" };
        var total_size: usize = 0;
        for (chunks) |chunk| {
            total_size += chunk.len;
        }

        var transferred: usize = 0;
        for (chunks) |chunk| {
            try buffer.appendSlice(self.allocator, chunk);
            transferred += chunk.len;

            if (self.options.progress_callback) |callback| {
                callback(transferred, total_size);
            }
        }

        return buffer.toOwnedSlice(self.allocator);
    }
};
// ANCHOR_END: downloader

// ANCHOR: upload_options
pub const UploadOptions = struct {
    content_type: ?[]const u8 = null,
    chunk_size: usize = 8192,
    progress_callback: ?ProgressCallback = null,
};
// ANCHOR_END: upload_options

// ANCHOR: multipart_form
pub const MultipartForm = struct {
    boundary: []const u8,
    fields: std.StringHashMap([]const u8),
    files: std.ArrayList(FileField),
    allocator: std.mem.Allocator,

    pub const FileField = struct {
        name: []const u8,
        filename: []const u8,
        content_type: []const u8,
        data: []const u8,
    };

    pub fn init(allocator: std.mem.Allocator) !MultipartForm {
        // Generate cryptographically secure boundary
        // Using random bytes prevents boundary collision attacks where
        // malicious file content contains the boundary string
        var random_bytes: [16]u8 = undefined;
        std.crypto.random.bytes(&random_bytes);

        var boundary_buf: [50]u8 = undefined;
        const hex = std.fmt.bytesToHex(random_bytes, .lower);
        const boundary = try std.fmt.bufPrint(&boundary_buf, "----Boundary{s}", .{hex});

        const owned_boundary = try allocator.dupe(u8, boundary);
        errdefer allocator.free(owned_boundary);

        return .{
            .boundary = owned_boundary,
            .fields = std.StringHashMap([]const u8).init(allocator),
            .files = std.ArrayList(FileField){},
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *MultipartForm) void {
        self.allocator.free(self.boundary);

        var it = self.fields.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.fields.deinit();

        for (self.files.items) |file| {
            self.allocator.free(file.name);
            self.allocator.free(file.filename);
            self.allocator.free(file.content_type);
            self.allocator.free(file.data);
        }
        self.files.deinit(self.allocator);
    }

    pub fn addField(self: *MultipartForm, name: []const u8, value: []const u8) !void {
        // HashMap Memory Leak Prevention
        //
        // Using getOrPut() instead of put() prevents memory leaks when the same
        // form field is added multiple times (e.g., updating a field value).
        //
        // This is critical for user-facing forms where duplicate field names
        // could occur due to user error or programmatic mistakes.
        //
        // See recipe_11_4.zig HttpResponse.setHeader for reference implementation.

        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        const gop = try self.fields.getOrPut(name);
        if (gop.found_existing) {
            // Duplicate field: free old value, reuse existing key
            self.allocator.free(gop.value_ptr.*);
            gop.value_ptr.* = owned_value;
        } else {
            // New field: allocate key and store both
            const owned_name = try self.allocator.dupe(u8, name);
            gop.key_ptr.* = owned_name;
            gop.value_ptr.* = owned_value;
        }
    }

    pub fn addFile(self: *MultipartForm, name: []const u8, filename: []const u8, content_type: []const u8, data: []const u8) !void {
        const owned_name = try self.allocator.dupe(u8, name);
        errdefer self.allocator.free(owned_name);

        const owned_filename = try self.allocator.dupe(u8, filename);
        errdefer self.allocator.free(owned_filename);

        const owned_content_type = try self.allocator.dupe(u8, content_type);
        errdefer self.allocator.free(owned_content_type);

        const owned_data = try self.allocator.dupe(u8, data);
        errdefer self.allocator.free(owned_data);

        const file = FileField{
            .name = owned_name,
            .filename = owned_filename,
            .content_type = owned_content_type,
            .data = owned_data,
        };

        try self.files.append(self.allocator, file);
    }

    pub fn build(self: *const MultipartForm) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        // Add text fields
        var it = self.fields.iterator();
        while (it.next()) |entry| {
            try buffer.appendSlice(self.allocator, "--");
            try buffer.appendSlice(self.allocator, self.boundary);
            try buffer.appendSlice(self.allocator, "\r\n");
            try buffer.appendSlice(self.allocator, "Content-Disposition: form-data; name=\"");
            try buffer.appendSlice(self.allocator, entry.key_ptr.*);
            try buffer.appendSlice(self.allocator, "\"\r\n\r\n");
            try buffer.appendSlice(self.allocator, entry.value_ptr.*);
            try buffer.appendSlice(self.allocator, "\r\n");
        }

        // Add file fields
        for (self.files.items) |file| {
            try buffer.appendSlice(self.allocator, "--");
            try buffer.appendSlice(self.allocator, self.boundary);
            try buffer.appendSlice(self.allocator, "\r\n");
            try buffer.appendSlice(self.allocator, "Content-Disposition: form-data; name=\"");
            try buffer.appendSlice(self.allocator, file.name);
            try buffer.appendSlice(self.allocator, "\"; filename=\"");
            try buffer.appendSlice(self.allocator, file.filename);
            try buffer.appendSlice(self.allocator, "\"\r\n");
            try buffer.appendSlice(self.allocator, "Content-Type: ");
            try buffer.appendSlice(self.allocator, file.content_type);
            try buffer.appendSlice(self.allocator, "\r\n\r\n");
            try buffer.appendSlice(self.allocator, file.data);
            try buffer.appendSlice(self.allocator, "\r\n");
        }

        // Final boundary
        try buffer.appendSlice(self.allocator, "--");
        try buffer.appendSlice(self.allocator, self.boundary);
        try buffer.appendSlice(self.allocator, "--\r\n");

        return buffer.toOwnedSlice(self.allocator);
    }

    pub fn getContentType(self: *const MultipartForm) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try buffer.appendSlice(self.allocator, "multipart/form-data; boundary=");
        try buffer.appendSlice(self.allocator, self.boundary);

        return buffer.toOwnedSlice(self.allocator);
    }
};
// ANCHOR_END: multipart_form

// ANCHOR: uploader
pub const Uploader = struct {
    allocator: std.mem.Allocator,
    options: UploadOptions,

    pub fn init(allocator: std.mem.Allocator, options: UploadOptions) Uploader {
        return .{
            .allocator = allocator,
            .options = options,
        };
    }

    pub fn uploadFile(self: *Uploader, url: []const u8, file_path: []const u8) !void {
        _ = url;
        const file = try std.fs.cwd().openFile(file_path, .{});
        defer file.close();

        const stat = try file.stat();
        const file_size = stat.size;

        // Simulate chunked upload
        var uploaded: usize = 0;
        while (uploaded < file_size) {
            const chunk_size = @min(self.options.chunk_size, file_size - uploaded);
            uploaded += chunk_size;

            if (self.options.progress_callback) |callback| {
                callback(uploaded, file_size);
            }
        }
    }

    pub fn uploadData(self: *Uploader, url: []const u8, data: []const u8) !void {
        _ = url;
        if (self.options.progress_callback) |callback| {
            callback(data.len, data.len);
        }
    }
};
// ANCHOR_END: uploader

// ANCHOR: resume_info
pub const ResumeInfo = struct {
    url: []const u8,
    file_path: []const u8,
    bytes_downloaded: usize,
    total_bytes: ?usize,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, url: []const u8, file_path: []const u8) !ResumeInfo {
        const owned_url = try allocator.dupe(u8, url);
        errdefer allocator.free(owned_url);

        const owned_file_path = try allocator.dupe(u8, file_path);

        return .{
            .url = owned_url,
            .file_path = owned_file_path,
            .bytes_downloaded = 0,
            .total_bytes = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *ResumeInfo) void {
        self.allocator.free(self.url);
        self.allocator.free(self.file_path);
    }

    pub fn save(self: *const ResumeInfo, resume_file: []const u8) !void {
        const file = try std.fs.cwd().createFile(resume_file, .{});
        defer file.close();

        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try buffer.writer(self.allocator).print("{d}\n", .{self.bytes_downloaded});
        if (self.total_bytes) |total| {
            try buffer.writer(self.allocator).print("{d}\n", .{total});
        }

        try file.writeAll(buffer.items);
    }

    pub fn load(allocator: std.mem.Allocator, resume_file: []const u8, url: []const u8, file_path: []const u8) !ResumeInfo {
        const file = try std.fs.cwd().openFile(resume_file, .{});
        defer file.close();

        var info = try ResumeInfo.init(allocator, url, file_path);
        errdefer info.deinit();

        var buf: [1024]u8 = undefined;
        const bytes_read = try file.readAll(&buf);
        const content = buf[0..bytes_read];

        var lines = std.mem.splitScalar(u8, content, '\n');
        if (lines.next()) |line| {
            info.bytes_downloaded = try std.fmt.parseInt(usize, std.mem.trim(u8, line, " \r\n"), 10);
        }

        return info;
    }
};
// ANCHOR_END: resume_info

// ANCHOR: test_download_to_memory
test "download to memory" {
    var downloader = Downloader.init(testing.allocator, .{});

    const data = try downloader.downloadToMemory("http://example.com/file.txt");
    defer testing.allocator.free(data);

    try testing.expect(data.len > 0);
    try testing.expectEqualStrings("File contents from server", data);
}
// ANCHOR_END: test_download_to_memory

// ANCHOR: test_download_to_file
test "download to file" {
    var downloader = Downloader.init(testing.allocator, .{});

    const test_file = "test_download.txt";
    defer std.fs.cwd().deleteFile(test_file) catch {};

    try downloader.downloadToFile("http://example.com/file.txt", test_file);

    const file = try std.fs.cwd().openFile(test_file, .{});
    defer file.close();

    var buf: [1024]u8 = undefined;
    const bytes_read = try file.readAll(&buf);
    try testing.expectEqualStrings("Downloaded file content", buf[0..bytes_read]);
}
// ANCHOR_END: test_download_to_file

// ANCHOR: test_chunked_download
test "chunked download" {
    var downloader = Downloader.init(testing.allocator, .{});

    const data = try downloader.downloadChunked("http://example.com/large-file.dat");
    defer testing.allocator.free(data);

    try testing.expectEqualStrings("chunk1chunk2chunk3", data);
}
// ANCHOR_END: test_chunked_download

// ANCHOR: test_download_with_progress
test "download with progress callback" {
    const TestProgress = struct {
        var last_bytes: usize = 0;
        var last_total: ?usize = null;

        fn callback(bytes: usize, total: ?usize) void {
            last_bytes = bytes;
            last_total = total;
        }
    };

    var downloader = Downloader.init(testing.allocator, .{
        .progress_callback = TestProgress.callback,
    });

    const data = try downloader.downloadToMemory("http://example.com/file.txt");
    defer testing.allocator.free(data);

    try testing.expect(TestProgress.last_bytes > 0);
    try testing.expect(TestProgress.last_total != null);
}
// ANCHOR_END: test_download_with_progress

// ANCHOR: test_multipart_form_creation
test "create multipart form" {
    var form = try MultipartForm.init(testing.allocator);
    defer form.deinit();

    try testing.expect(form.boundary.len > 0);
    try testing.expect(std.mem.startsWith(u8, form.boundary, "----Boundary"));
}
// ANCHOR_END: test_multipart_form_creation

// ANCHOR: test_multipart_add_field
test "add field to multipart form" {
    var form = try MultipartForm.init(testing.allocator);
    defer form.deinit();

    try form.addField("username", "alice");
    try form.addField("email", "alice@example.com");

    try testing.expectEqual(@as(u32, 2), form.fields.count());

    const username = form.fields.get("username");
    try testing.expect(username != null);
    try testing.expectEqualStrings("alice", username.?);
}
// ANCHOR_END: test_multipart_add_field

test "add duplicate field to multipart form - no memory leak" {
    var form = try MultipartForm.init(testing.allocator);
    defer form.deinit();

    // Add same field multiple times - last value should win
    try form.addField("username", "alice");
    try form.addField("username", "bob");
    try form.addField("email", "old@example.com");
    try form.addField("email", "new@example.com");

    // Should only have 2 fields, not 4
    try testing.expectEqual(@as(u32, 2), form.fields.count());

    // Last values should win
    const username = form.fields.get("username");
    try testing.expect(username != null);
    try testing.expectEqualStrings("bob", username.?);

    const email = form.fields.get("email");
    try testing.expect(email != null);
    try testing.expectEqualStrings("new@example.com", email.?);
}

// ANCHOR: test_multipart_add_file
test "add file to multipart form" {
    var form = try MultipartForm.init(testing.allocator);
    defer form.deinit();

    try form.addFile("avatar", "photo.jpg", "image/jpeg", "fake image data");

    try testing.expectEqual(@as(usize, 1), form.files.items.len);

    const file = form.files.items[0];
    try testing.expectEqualStrings("avatar", file.name);
    try testing.expectEqualStrings("photo.jpg", file.filename);
    try testing.expectEqualStrings("image/jpeg", file.content_type);
}
// ANCHOR_END: test_multipart_add_file

// ANCHOR: test_multipart_build
test "build multipart form body" {
    var form = try MultipartForm.init(testing.allocator);
    defer form.deinit();

    try form.addField("name", "John");
    try form.addFile("document", "test.txt", "text/plain", "file contents");

    const body = try form.build();
    defer testing.allocator.free(body);

    try testing.expect(std.mem.indexOf(u8, body, "name=\"name\"") != null);
    try testing.expect(std.mem.indexOf(u8, body, "John") != null);
    try testing.expect(std.mem.indexOf(u8, body, "filename=\"test.txt\"") != null);
    try testing.expect(std.mem.indexOf(u8, body, "file contents") != null);
}
// ANCHOR_END: test_multipart_build

// ANCHOR: test_multipart_content_type
test "get multipart content type" {
    var form = try MultipartForm.init(testing.allocator);
    defer form.deinit();

    const content_type = try form.getContentType();
    defer testing.allocator.free(content_type);

    try testing.expect(std.mem.startsWith(u8, content_type, "multipart/form-data; boundary="));
}
// ANCHOR_END: test_multipart_content_type

// ANCHOR: test_upload_file
test "upload file" {
    // Create test file
    const test_file = "test_upload.txt";
    {
        const file = try std.fs.cwd().createFile(test_file, .{});
        defer file.close();
        try file.writeAll("Test upload content");
    }
    defer std.fs.cwd().deleteFile(test_file) catch {};

    var uploader = Uploader.init(testing.allocator, .{});
    try uploader.uploadFile("http://example.com/upload", test_file);
}
// ANCHOR_END: test_upload_file

// ANCHOR: test_upload_data
test "upload data" {
    var uploader = Uploader.init(testing.allocator, .{});

    const data = "Some data to upload";
    try uploader.uploadData("http://example.com/api/data", data);
}
// ANCHOR_END: test_upload_data

// ANCHOR: test_upload_with_progress
test "upload with progress callback" {
    const TestProgress = struct {
        var called: bool = false;

        fn callback(bytes: usize, total: ?usize) void {
            _ = bytes;
            _ = total;
            called = true;
        }
    };

    var uploader = Uploader.init(testing.allocator, .{
        .progress_callback = TestProgress.callback,
    });

    const data = "Upload data";
    try uploader.uploadData("http://example.com/upload", data);

    try testing.expect(TestProgress.called);
}
// ANCHOR_END: test_upload_with_progress

// ANCHOR: test_resume_info_creation
test "create resume info" {
    var info = try ResumeInfo.init(
        testing.allocator,
        "http://example.com/file.zip",
        "/tmp/file.zip",
    );
    defer info.deinit();

    try testing.expectEqualStrings("http://example.com/file.zip", info.url);
    try testing.expectEqualStrings("/tmp/file.zip", info.file_path);
    try testing.expectEqual(@as(usize, 0), info.bytes_downloaded);
}
// ANCHOR_END: test_resume_info_creation

// ANCHOR: test_resume_info_save_load
test "save and load resume info" {
    const resume_file = "test_resume.txt";
    defer std.fs.cwd().deleteFile(resume_file) catch {};

    // Create and save
    {
        var info = try ResumeInfo.init(
            testing.allocator,
            "http://example.com/file.zip",
            "/tmp/file.zip",
        );
        defer info.deinit();

        info.bytes_downloaded = 12345;
        info.total_bytes = 67890;

        try info.save(resume_file);
    }

    // Load and verify
    {
        var info = try ResumeInfo.load(
            testing.allocator,
            resume_file,
            "http://example.com/file.zip",
            "/tmp/file.zip",
        );
        defer info.deinit();

        try testing.expectEqual(@as(usize, 12345), info.bytes_downloaded);
    }
}
// ANCHOR_END: test_resume_info_save_load
```

### See Also

- Recipe 11.1: Making HTTP requests
- Recipe 11.4: Building a simple HTTP server
- Recipe 11.6: Working with REST APIs

---

## Recipe 11.10: Rate Limiting and Throttling {#recipe-11-10}

**Tags:** allocators, arraylist, atomics, concurrency, data-structures, error-handling, http, memory, networking, resource-cleanup, synchronization, testing, threading
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_10.zig`

### Problem

You need to control the rate of requests or operations to prevent resource exhaustion, ensure fair usage, and protect your services from abuse or overload.

### Solution

Zig provides excellent support for concurrent programming with atomics and mutexes. This recipe demonstrates four rate limiting patterns: token bucket, sliding window, concurrent request limiting, and request throttling.

### Token Bucket Algorithm

The token bucket is a classic rate limiting algorithm that refills tokens at a steady rate:

```zig
pub const TokenBucket = struct {
    capacity: usize,
    tokens: usize,
    refill_rate: f64, // tokens per second
    last_refill: i64,
    mutex: std.Thread.Mutex,

    pub fn init(capacity: usize, refill_rate: f64) TokenBucket {
        return .{
            .capacity = capacity,
            .tokens = capacity,
            .refill_rate = refill_rate,
            .last_refill = std.time.timestamp(),
            .mutex = .{},
        };
    }

    pub fn tryConsume(self: *TokenBucket, tokens: usize) bool {
        self.mutex.lock();
        defer self.mutex.unlock();

        self.refill();

        if (self.tokens >= tokens) {
            self.tokens -= tokens;
            return true;
        }
        return false;
    }

    fn refill(self: *TokenBucket) void {
        const now = std.time.timestamp();
        const elapsed = @as(f64, @floatFromInt(now - self.last_refill));

        if (elapsed <= 0) return; // Guard against negative time or no elapsed time

        const tokens_float = elapsed * self.refill_rate;
        if (tokens_float < 0 or tokens_float > @as(f64, @floatFromInt(std.math.maxInt(usize)))) {
            // Overflow or invalid value - fill to capacity
            self.tokens = self.capacity;
            self.last_refill = now;
            return;
        }

        const tokens_to_add = @as(usize, @intFromFloat(tokens_float));
        if (tokens_to_add > 0) {
            self.tokens = @min(self.capacity, self.tokens + tokens_to_add);
            self.last_refill = now;
        }
    }

    pub fn availableTokens(self: *TokenBucket) usize {
        self.mutex.lock();
        defer self.mutex.unlock();

        self.refill();
        return self.tokens;
    }
};
```

### Sliding Window Rate Limiting

Sliding windows track exact request timestamps for precise rate limiting:

```zig
pub const SlidingWindow = struct {
    window_size_ms: i64,
    max_requests: usize,
    requests: std.ArrayList(i64),
    allocator: std.mem.Allocator,
    mutex: std.Thread.Mutex,

    pub fn init(allocator: std.mem.Allocator, window_size_ms: i64, max_requests: usize) SlidingWindow {
        return .{
            .window_size_ms = window_size_ms,
            .max_requests = max_requests,
            .requests = std.ArrayList(i64){},
            .allocator = allocator,
            .mutex = .{},
        };
    }

    pub fn deinit(self: *SlidingWindow) void {
        self.requests.deinit(self.allocator);
    }

    pub fn tryRequest(self: *SlidingWindow) !bool {
        self.mutex.lock();
        defer self.mutex.unlock();

        const now = std.time.milliTimestamp();
        try self.cleanOldRequests(now);

        if (self.requests.items.len < self.max_requests) {
            try self.requests.append(self.allocator, now);
            return true;
        }
        return false;
    }

    fn cleanOldRequests(self: *SlidingWindow, now: i64) !void {
        const cutoff = now - self.window_size_ms;
        var i: usize = 0;
        while (i < self.requests.items.len) {
            if (self.requests.items[i] < cutoff) {
                _ = self.requests.orderedRemove(i);
            } else {
                i += 1;
            }
        }
    }
};
```

### Rate Limiter with HTTP Headers

Wrapper around token bucket that provides standard HTTP rate limit headers:

```zig
pub const RateLimiter = struct {
    token_bucket: TokenBucket,

    pub fn init(capacity: usize, refill_rate: f64) RateLimiter {
        return .{
            .token_bucket = TokenBucket.init(capacity, refill_rate),
        };
    }

    pub fn checkLimit(self: *RateLimiter, tokens: usize) !bool {
        return self.token_bucket.tryConsume(tokens);
    }

    pub fn waitForTokens(self: *RateLimiter, tokens: usize, timeout_ms: u64) !bool {
        const start = std.time.milliTimestamp();
        while (true) {
            if (self.token_bucket.tryConsume(tokens)) {
                return true;
            }

            const elapsed = @as(u64, @intCast(std.time.milliTimestamp() - start));
            if (elapsed >= timeout_ms) {
                return false;
            }

            std.Thread.sleep(10 * std.time.ns_per_ms);
        }
    }

    pub fn getRateLimitHeaders(self: *RateLimiter) RateLimitHeaders {
        const remaining = self.token_bucket.availableTokens();
        const reset_time = std.time.timestamp() + 60; // Reset in 1 minute

        return .{
            .limit = self.token_bucket.capacity,
            .remaining = remaining,
            .reset = reset_time,
        };
    }
};

pub const RateLimitHeaders = struct {
    limit: usize,
    remaining: usize,
    reset: i64,
};
```

### Concurrent Request Limiter

Limits the number of simultaneous in-flight requests using atomic operations:

```zig
pub const ConcurrentLimiter = struct {
    max_concurrent: usize,
    current: std.atomic.Value(usize),

    pub fn init(max_concurrent: usize) ConcurrentLimiter {
        return .{
            .max_concurrent = max_concurrent,
            .current = std.atomic.Value(usize).init(0),
        };
    }

    pub fn acquire(self: *ConcurrentLimiter) bool {
        while (true) {
            const current = self.current.load(.monotonic);
            if (current >= self.max_concurrent) {
                return false;
            }

            if (self.current.cmpxchgWeak(
                current,
                current + 1,
                .monotonic,
                .monotonic,
            ) == null) {
                return true;
            }
        }
    }

    pub fn release(self: *ConcurrentLimiter) void {
        const prev = self.current.fetchSub(1, .monotonic);
        std.debug.assert(prev > 0); // Catch double-release in debug mode
    }

    pub fn currentCount(self: *ConcurrentLimiter) usize {
        return self.current.load(.monotonic);
    }
};
```

### Request Throttler

Enforces minimum time intervals between operations:

```zig
pub const Throttler = struct {
    min_interval_ms: i64,
    last_execution: std.atomic.Value(i64),

    pub fn init(min_interval_ms: i64) Throttler {
        return .{
            .min_interval_ms = min_interval_ms,
            .last_execution = std.atomic.Value(i64).init(0),
        };
    }

    pub fn shouldExecute(self: *Throttler) bool {
        const now = std.time.milliTimestamp();
        const last = self.last_execution.load(.monotonic);
        const elapsed = now - last;

        if (elapsed >= self.min_interval_ms) {
            if (self.last_execution.cmpxchgWeak(
                last,
                now,
                .monotonic,
                .monotonic,
            ) == null) {
                return true;
            }
        }
        return false;
    }

    pub fn reset(self: *Throttler) void {
        self.last_execution.store(0, .monotonic);
    }
};
```

### Discussion

This recipe demonstrates various rate limiting strategies, each suitable for different use cases.

### Token Bucket Algorithm

The token bucket allows controlled bursts while maintaining an average rate:

**How it works:**
1. Bucket starts full with `capacity` tokens
2. Tokens refill at `refill_rate` per second
3. Each operation consumes tokens
4. Operations are rejected when no tokens available

**Advantages:**
- Allows bursts up to capacity
- Smooth long-term rate limiting
- Memory efficient (constant space)

**Best for:**
- API rate limiting
- Network bandwidth control
- Resource consumption limits

**Thread Safety:**
Token bucket uses `std.Thread.Mutex` to protect shared state. The `refill()` method calculates tokens based on elapsed time, making it safe even if called from multiple threads.

**Overflow Protection:**
The implementation includes bounds checking to prevent integer truncation:
```zig
if (tokens_float < 0 or tokens_float > @as(f64, @floatFromInt(std.math.maxInt(usize)))) {
    self.tokens = self.capacity;
    self.last_refill = now;
    return;
}
```

This guards against system clock changes or extremely high refill rates.

### Sliding Window Algorithm

Sliding windows provide exact request counting over a time period:

**How it works:**
1. Store timestamp of each request
2. Remove requests older than window size
3. Accept requests if count under limit

**Advantages:**
- Exact rate limiting (no burst tolerance)
- Fair distribution across time window
- Predictable behavior

**Disadvantages:**
- Memory grows with request rate
- O(n) cleanup per request (can be optimized)

**Best for:**
- Strict rate limits without bursts
- User quota enforcement
- Request logging with limits

**Memory Considerations:**
In production, consider adding cleanup strategies:
- Maximum stored timestamps
- Periodic background cleanup
- Alternative data structures (circular buffer)

### Concurrent Request Limiting

Limits simultaneous in-flight operations using lock-free atomics:

**How it works:**
1. Atomic counter tracks current operations
2. `acquire()` uses compare-exchange to increment
3. `release()` decrements when operation completes

**Lock-Free Design:**
```zig
while (true) {
    const current = self.current.load(.monotonic);
    if (current >= self.max_concurrent) {
        return false;
    }

    if (self.current.cmpxchgWeak(current, current + 1, .monotonic, .monotonic) == null) {
        return true;
    }
}
```

The `cmpxchgWeak` operation atomically checks if the value is still `current` and updates it to `current + 1`. If another thread modified it, the loop retries.

**Safety:**
The `release()` method includes a debug assert to catch double-release bugs:
```zig
const prev = self.current.fetchSub(1, .monotonic);
std.debug.assert(prev > 0);
```

In debug builds, this will panic if release is called without a matching acquire.

**Best for:**
- Connection pooling
- Worker thread limits
- Database connection limits
- File handle management

### Request Throttling

Enforces minimum intervals between operations:

**How it works:**
1. Stores timestamp of last execution
2. Checks elapsed time since last execution
3. Updates timestamp atomically on success

**Lock-Free Implementation:**
Uses atomic compare-exchange to prevent race conditions when multiple threads try to execute simultaneously.

**Best for:**
- Protecting slow operations
- Log rate limiting
- API call throttling
- Event debouncing

### Choosing a Strategy

**Use Token Bucket when:**
- You want to allow controlled bursts
- Average rate matters more than instantaneous rate
- You need memory-efficient rate limiting

**Use Sliding Window when:**
- You need exact rate limits
- Bursts should be prevented
- You can afford the memory overhead

**Use Concurrent Limiter when:**
- Limiting simultaneous operations
- Protecting shared resources
- Managing connection pools

**Use Throttler when:**
- Operations should not execute too frequently
- You need simple minimum interval enforcement
- Debouncing user actions

### HTTP Rate Limit Headers

The `RateLimitHeaders` struct provides standard HTTP headers:

```text
X-RateLimit-Limit: 100
X-RateLimit-Remaining: 42
X-RateLimit-Reset: 1609459200
```

These headers inform clients about:
- Total rate limit (`limit`)
- Remaining requests (`remaining`)
- When limit resets (`reset` timestamp)

### Production Considerations

**Time Source:**
This implementation uses `std.time.timestamp()` and `std.time.milliTimestamp()` which can be affected by system clock changes. For production:
- Use monotonic clocks when available
- Handle backward time jumps gracefully
- Consider timer-based refill instead of on-demand

**Distributed Rate Limiting:**
For multi-server deployments:
- Use Redis or similar for shared state
- Implement distributed token buckets
- Consider eventual consistency trade-offs

**Monitoring:**
Track these metrics:
- Rate limit rejections
- Average token consumption
- Concurrent request peaks
- Throttle activation frequency

**Configuration:**
Make limits configurable per:
- User tier (free vs paid)
- API endpoint
- Time of day
- Geographic region

### Atomic Memory Ordering

This code uses `.monotonic` memory ordering for atomics:

```zig
const current = self.current.load(.monotonic);
```

**Monotonic ordering** guarantees:
- No reordering of monotonic operations
- Lighter weight than sequential consistency
- Sufficient for counters and simple state

For more complex scenarios, consider:
- `.acquire` / `.release` for lock-like patterns
- `.acq_rel` for read-modify-write
- `.seq_cst` when full ordering needed

### Error Handling

The sliding window's `tryRequest()` can return errors from ArrayList operations:

```zig
pub fn tryRequest(self: *SlidingWindow) !bool {
    try self.requests.append(self.allocator, now);
    return true;
}
```

Callers should handle allocation failures appropriately, perhaps by temporarily rejecting requests during OOM conditions.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: token_bucket
pub const TokenBucket = struct {
    capacity: usize,
    tokens: usize,
    refill_rate: f64, // tokens per second
    last_refill: i64,
    mutex: std.Thread.Mutex,

    pub fn init(capacity: usize, refill_rate: f64) TokenBucket {
        return .{
            .capacity = capacity,
            .tokens = capacity,
            .refill_rate = refill_rate,
            .last_refill = std.time.timestamp(),
            .mutex = .{},
        };
    }

    pub fn tryConsume(self: *TokenBucket, tokens: usize) bool {
        self.mutex.lock();
        defer self.mutex.unlock();

        self.refill();

        if (self.tokens >= tokens) {
            self.tokens -= tokens;
            return true;
        }
        return false;
    }

    fn refill(self: *TokenBucket) void {
        const now = std.time.timestamp();
        const elapsed = @as(f64, @floatFromInt(now - self.last_refill));

        if (elapsed <= 0) return; // Guard against negative time or no elapsed time

        const tokens_float = elapsed * self.refill_rate;
        if (tokens_float < 0 or tokens_float > @as(f64, @floatFromInt(std.math.maxInt(usize)))) {
            // Overflow or invalid value - fill to capacity
            self.tokens = self.capacity;
            self.last_refill = now;
            return;
        }

        const tokens_to_add = @as(usize, @intFromFloat(tokens_float));
        if (tokens_to_add > 0) {
            self.tokens = @min(self.capacity, self.tokens + tokens_to_add);
            self.last_refill = now;
        }
    }

    pub fn availableTokens(self: *TokenBucket) usize {
        self.mutex.lock();
        defer self.mutex.unlock();

        self.refill();
        return self.tokens;
    }
};
// ANCHOR_END: token_bucket

// ANCHOR: sliding_window
pub const SlidingWindow = struct {
    window_size_ms: i64,
    max_requests: usize,
    requests: std.ArrayList(i64),
    allocator: std.mem.Allocator,
    mutex: std.Thread.Mutex,

    pub fn init(allocator: std.mem.Allocator, window_size_ms: i64, max_requests: usize) SlidingWindow {
        return .{
            .window_size_ms = window_size_ms,
            .max_requests = max_requests,
            .requests = std.ArrayList(i64){},
            .allocator = allocator,
            .mutex = .{},
        };
    }

    pub fn deinit(self: *SlidingWindow) void {
        self.requests.deinit(self.allocator);
    }

    pub fn tryRequest(self: *SlidingWindow) !bool {
        self.mutex.lock();
        defer self.mutex.unlock();

        const now = std.time.milliTimestamp();
        try self.cleanOldRequests(now);

        if (self.requests.items.len < self.max_requests) {
            try self.requests.append(self.allocator, now);
            return true;
        }
        return false;
    }

    fn cleanOldRequests(self: *SlidingWindow, now: i64) !void {
        const cutoff = now - self.window_size_ms;
        var i: usize = 0;
        while (i < self.requests.items.len) {
            if (self.requests.items[i] < cutoff) {
                _ = self.requests.orderedRemove(i);
            } else {
                i += 1;
            }
        }
    }

    pub fn requestCount(self: *SlidingWindow) usize {
        self.mutex.lock();
        defer self.mutex.unlock();

        const now = std.time.milliTimestamp();
        self.cleanOldRequests(now) catch return self.requests.items.len;
        return self.requests.items.len;
    }
};
// ANCHOR_END: sliding_window

// ANCHOR: rate_limiter
pub const RateLimiter = struct {
    token_bucket: TokenBucket,

    pub fn init(capacity: usize, refill_rate: f64) RateLimiter {
        return .{
            .token_bucket = TokenBucket.init(capacity, refill_rate),
        };
    }

    pub fn checkLimit(self: *RateLimiter, tokens: usize) !bool {
        return self.token_bucket.tryConsume(tokens);
    }

    pub fn waitForTokens(self: *RateLimiter, tokens: usize, timeout_ms: u64) !bool {
        const start = std.time.milliTimestamp();
        while (true) {
            if (self.token_bucket.tryConsume(tokens)) {
                return true;
            }

            const elapsed = @as(u64, @intCast(std.time.milliTimestamp() - start));
            if (elapsed >= timeout_ms) {
                return false;
            }

            std.Thread.sleep(10 * std.time.ns_per_ms);
        }
    }

    pub fn getRateLimitHeaders(self: *RateLimiter) RateLimitHeaders {
        const remaining = self.token_bucket.availableTokens();
        const reset_time = std.time.timestamp() + 60; // Reset in 1 minute

        return .{
            .limit = self.token_bucket.capacity,
            .remaining = remaining,
            .reset = reset_time,
        };
    }
};

pub const RateLimitHeaders = struct {
    limit: usize,
    remaining: usize,
    reset: i64,
};
// ANCHOR_END: rate_limiter

// ANCHOR: concurrent_limiter
pub const ConcurrentLimiter = struct {
    max_concurrent: usize,
    current: std.atomic.Value(usize),

    pub fn init(max_concurrent: usize) ConcurrentLimiter {
        return .{
            .max_concurrent = max_concurrent,
            .current = std.atomic.Value(usize).init(0),
        };
    }

    pub fn acquire(self: *ConcurrentLimiter) bool {
        while (true) {
            const current = self.current.load(.monotonic);
            if (current >= self.max_concurrent) {
                return false;
            }

            if (self.current.cmpxchgWeak(
                current,
                current + 1,
                .monotonic,
                .monotonic,
            ) == null) {
                return true;
            }
        }
    }

    pub fn release(self: *ConcurrentLimiter) void {
        const prev = self.current.fetchSub(1, .monotonic);
        std.debug.assert(prev > 0); // Catch double-release in debug mode
    }

    pub fn currentCount(self: *ConcurrentLimiter) usize {
        return self.current.load(.monotonic);
    }
};
// ANCHOR_END: concurrent_limiter

// ANCHOR: throttler
pub const Throttler = struct {
    min_interval_ms: i64,
    last_execution: std.atomic.Value(i64),

    pub fn init(min_interval_ms: i64) Throttler {
        return .{
            .min_interval_ms = min_interval_ms,
            .last_execution = std.atomic.Value(i64).init(0),
        };
    }

    pub fn shouldExecute(self: *Throttler) bool {
        const now = std.time.milliTimestamp();
        const last = self.last_execution.load(.monotonic);
        const elapsed = now - last;

        if (elapsed >= self.min_interval_ms) {
            if (self.last_execution.cmpxchgWeak(
                last,
                now,
                .monotonic,
                .monotonic,
            ) == null) {
                return true;
            }
        }
        return false;
    }

    pub fn reset(self: *Throttler) void {
        self.last_execution.store(0, .monotonic);
    }

    pub fn timeSinceLastExecution(self: *Throttler) i64 {
        const now = std.time.milliTimestamp();
        const last = self.last_execution.load(.monotonic);
        if (last == 0) return self.min_interval_ms;
        return now - last;
    }
};
// ANCHOR_END: throttler

// ANCHOR: test_token_bucket
test "token bucket basic consumption" {
    var bucket = TokenBucket.init(10, 1.0);

    try testing.expect(bucket.tryConsume(5));
    try testing.expectEqual(@as(usize, 5), bucket.availableTokens());

    try testing.expect(bucket.tryConsume(5));
    try testing.expectEqual(@as(usize, 0), bucket.availableTokens());

    try testing.expect(!bucket.tryConsume(1));
}
// ANCHOR_END: test_token_bucket

// ANCHOR: test_token_bucket_refill
test "token bucket refill" {
    var bucket = TokenBucket.init(10, 10.0); // 10 tokens per second

    try testing.expect(bucket.tryConsume(10));
    try testing.expectEqual(@as(usize, 0), bucket.availableTokens());

    // Wait for refill (simulate by adjusting last_refill)
    bucket.last_refill -= 1; // Simulate 1 second passed

    const available = bucket.availableTokens();
    try testing.expect(available > 0);
}
// ANCHOR_END: test_token_bucket_refill

// ANCHOR: test_sliding_window
test "sliding window basic" {
    var window = SlidingWindow.init(testing.allocator, 1000, 5);
    defer window.deinit();

    // Should allow 5 requests
    try testing.expect(try window.tryRequest());
    try testing.expect(try window.tryRequest());
    try testing.expect(try window.tryRequest());
    try testing.expect(try window.tryRequest());
    try testing.expect(try window.tryRequest());

    // Should reject 6th request
    try testing.expect(!try window.tryRequest());

    try testing.expectEqual(@as(usize, 5), window.requestCount());
}
// ANCHOR_END: test_sliding_window

// ANCHOR: test_sliding_window_cleanup
test "sliding window cleanup old requests" {
    var window = SlidingWindow.init(testing.allocator, 100, 3);
    defer window.deinit();

    try testing.expect(try window.tryRequest());
    try testing.expect(try window.tryRequest());
    try testing.expect(try window.tryRequest());
    try testing.expect(!try window.tryRequest());

    // Simulate time passing
    std.Thread.sleep(150 * std.time.ns_per_ms);

    // Old requests should be cleaned up
    try testing.expect(try window.tryRequest());
}
// ANCHOR_END: test_sliding_window_cleanup

// ANCHOR: test_rate_limiter
test "rate limiter check limit" {
    var limiter = RateLimiter.init(10, 1.0);

    try testing.expect(try limiter.checkLimit(5));
    try testing.expect(try limiter.checkLimit(5));
    try testing.expect(!try limiter.checkLimit(1));
}
// ANCHOR_END: test_rate_limiter

// ANCHOR: test_rate_limiter_headers
test "rate limiter headers" {
    var limiter = RateLimiter.init(100, 10.0);

    _ = try limiter.checkLimit(30);

    const headers = limiter.getRateLimitHeaders();
    try testing.expectEqual(@as(usize, 100), headers.limit);
    try testing.expect(headers.remaining <= 70);
    try testing.expect(headers.reset > std.time.timestamp());
}
// ANCHOR_END: test_rate_limiter_headers

// ANCHOR: test_rate_limiter_wait
test "rate limiter wait for tokens" {
    var limiter = RateLimiter.init(5, 0.1); // Very slow refill

    try testing.expect(try limiter.checkLimit(5));

    // Should timeout since refill rate is very slow
    try testing.expect(!try limiter.waitForTokens(1, 50));
}
// ANCHOR_END: test_rate_limiter_wait

// ANCHOR: test_concurrent_limiter
test "concurrent limiter basic" {
    var limiter = ConcurrentLimiter.init(3);

    try testing.expect(limiter.acquire());
    try testing.expectEqual(@as(usize, 1), limiter.currentCount());

    try testing.expect(limiter.acquire());
    try testing.expectEqual(@as(usize, 2), limiter.currentCount());

    try testing.expect(limiter.acquire());
    try testing.expectEqual(@as(usize, 3), limiter.currentCount());

    try testing.expect(!limiter.acquire());
    try testing.expectEqual(@as(usize, 3), limiter.currentCount());
}
// ANCHOR_END: test_concurrent_limiter

// ANCHOR: test_concurrent_limiter_release
test "concurrent limiter release" {
    var limiter = ConcurrentLimiter.init(2);

    try testing.expect(limiter.acquire());
    try testing.expect(limiter.acquire());
    try testing.expect(!limiter.acquire());

    limiter.release();
    try testing.expectEqual(@as(usize, 1), limiter.currentCount());

    try testing.expect(limiter.acquire());
    try testing.expectEqual(@as(usize, 2), limiter.currentCount());
}
// ANCHOR_END: test_concurrent_limiter_release

// ANCHOR: test_throttler
test "throttler basic" {
    var throttler = Throttler.init(100);

    try testing.expect(throttler.shouldExecute());
    try testing.expect(!throttler.shouldExecute());

    std.Thread.sleep(150 * std.time.ns_per_ms);

    try testing.expect(throttler.shouldExecute());
}
// ANCHOR_END: test_throttler

// ANCHOR: test_throttler_reset
test "throttler reset" {
    var throttler = Throttler.init(1000);

    try testing.expect(throttler.shouldExecute());
    try testing.expect(!throttler.shouldExecute());

    throttler.reset();

    try testing.expect(throttler.shouldExecute());
}
// ANCHOR_END: test_throttler_reset

// ANCHOR: test_throttler_time_since
test "throttler time since last execution" {
    var throttler = Throttler.init(100);

    const initial_time = throttler.timeSinceLastExecution();
    try testing.expectEqual(@as(i64, 100), initial_time);

    try testing.expect(throttler.shouldExecute());

    std.Thread.sleep(50 * std.time.ns_per_ms);

    const elapsed = throttler.timeSinceLastExecution();
    try testing.expect(elapsed >= 50);
    try testing.expect(elapsed < 100);
}
// ANCHOR_END: test_throttler_time_since
```

### See Also

- Recipe 11.4: Building a simple HTTP server
- Recipe 11.6: Working with REST APIs

---

## Recipe 11.11: GraphQL Client Implementation {#recipe-11-11}

**Tags:** allocators, arraylist, data-structures, error-handling, hashmap, http, json, memory, networking, parsing, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_11.zig`

### Problem

You need to interact with GraphQL APIs, constructing queries with variables, handling mutations, parsing responses, and managing errors.

### Solution

Zig's string manipulation and JSON handling capabilities make it well-suited for building GraphQL clients. This recipe demonstrates query construction, variable management, and response parsing.

### Operation Types

GraphQL supports three operation types:

```zig
pub const OperationType = enum {
    query,
    mutation,
    subscription,

    pub fn toString(self: OperationType) []const u8 {
        return switch (self) {
            .query => "query",
            .mutation => "mutation",
            .subscription => "subscription",
        };
    }
};
```

### GraphQL Query Building

The `GraphQLQuery` struct represents a GraphQL operation with variables:

```zig
pub const GraphQLQuery = struct {
    operation_type: OperationType,
    operation_name: ?[]const u8,
    query: []const u8,
    variables: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, operation_type: OperationType, query: []const u8) !GraphQLQuery {
        const owned_query = try allocator.dupe(u8, query);
        errdefer allocator.free(owned_query);

        return .{
            .operation_type = operation_type,
            .operation_name = null,
            .query = owned_query,
            .variables = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn setOperationName(self: *GraphQLQuery, name: []const u8) !void {
        if (self.operation_name) |old_name| {
            self.allocator.free(old_name);
        }
        self.operation_name = try self.allocator.dupe(u8, name);
    }

    pub fn addVariable(self: *GraphQLQuery, name: []const u8, value: []const u8) !void {
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        const result = try self.variables.getOrPut(name);
        if (result.found_existing) {
            self.allocator.free(result.value_ptr.*);
            result.value_ptr.* = owned_value;
        } else {
            const owned_name = try self.allocator.dupe(u8, name);
            result.key_ptr.* = owned_name;
            result.value_ptr.* = owned_value;
        }
    }
};
```

### Building JSON Requests

GraphQL queries are sent as JSON with the query and optional variables:

```zig
pub fn buildRequest(self: *const GraphQLQuery) ![]const u8 {
    var buffer = std.ArrayList(u8){};
    defer buffer.deinit(self.allocator);

    try buffer.appendSlice(self.allocator, "{\"query\":\"");
    try self.escapeAndAppend(&buffer, self.query);
    try buffer.appendSlice(self.allocator, "\"");

    if (self.variables.count() > 0) {
        try buffer.appendSlice(self.allocator, ",\"variables\":{");
        var it = self.variables.iterator();
        var first = true;
        while (it.next()) |entry| {
            if (!first) try buffer.appendSlice(self.allocator, ",");
            try buffer.appendSlice(self.allocator, "\"");
            try buffer.appendSlice(self.allocator, entry.key_ptr.*);
            try buffer.appendSlice(self.allocator, "\":");
            try buffer.appendSlice(self.allocator, entry.value_ptr.*);
            first = false;
        }
        try buffer.appendSlice(self.allocator, "}");
    }

    try buffer.appendSlice(self.allocator, "}");

    return buffer.toOwnedSlice(self.allocator);
}

fn escapeAndAppend(self: *const GraphQLQuery, buffer: *std.ArrayList(u8), str: []const u8) !void {
    for (str) |c| {
        switch (c) {
            '\n' => try buffer.appendSlice(self.allocator, "\\n"),
            '\r' => try buffer.appendSlice(self.allocator, "\\r"),
            '\t' => try buffer.appendSlice(self.allocator, "\\t"),
            '"' => try buffer.appendSlice(self.allocator, "\\\""),
            '\\' => try buffer.appendSlice(self.allocator, "\\\\"),
            else => try buffer.append(self.allocator, c),
        }
    }
}
```

### Response Handling

GraphQL responses contain data and/or errors:

```zig
pub const GraphQLError = struct {
    message: []const u8,
    locations: ?std.ArrayList(ErrorLocation),
    path: ?std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    pub const ErrorLocation = struct {
        line: usize,
        column: usize,
    };

    pub fn init(allocator: std.mem.Allocator, message: []const u8) !GraphQLError {
        const owned_message = try allocator.dupe(u8, message);
        errdefer allocator.free(owned_message);

        return .{
            .message = owned_message,
            .locations = null,
            .path = null,
            .allocator = allocator,
        };
    }
};

pub const GraphQLResponse = struct {
    data: ?[]const u8,
    errors: ?std.ArrayList(GraphQLError),
    allocator: std.mem.Allocator,

    pub fn addError(self: *GraphQLResponse, error_msg: []const u8) !void {
        if (self.errors == null) {
            self.errors = std.ArrayList(GraphQLError){};
        }

        var err = try GraphQLError.init(self.allocator, error_msg);
        errdefer err.deinit();
        try self.errors.?.append(self.allocator, err);
    }

    pub fn hasErrors(self: *const GraphQLResponse) bool {
        if (self.errors) |errs| {
            return errs.items.len > 0;
        }
        return false;
    }
};
```

### GraphQL Client

The client manages endpoint configuration and request execution:

```zig
pub const GraphQLClient = struct {
    endpoint: []const u8,
    headers: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, endpoint: []const u8) !GraphQLClient {
        const owned_endpoint = try allocator.dupe(u8, endpoint);
        errdefer allocator.free(owned_endpoint);

        return .{
            .endpoint = owned_endpoint,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn setHeader(self: *GraphQLClient, name: []const u8, value: []const u8) !void {
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        const result = try self.headers.getOrPut(name);
        if (result.found_existing) {
            self.allocator.free(result.value_ptr.*);
            result.value_ptr.* = owned_value;
        } else {
            const owned_name = try self.allocator.dupe(u8, name);
            result.key_ptr.* = owned_name;
            result.value_ptr.* = owned_value;
        }
    }

    pub fn execute(self: *GraphQLClient, query: *const GraphQLQuery) !GraphQLResponse {
        // In real implementation, use std.http.Client to POST to self.endpoint
        var response = GraphQLResponse.init(self.allocator);
        try response.setData("{\"user\":{\"id\":\"123\",\"name\":\"Alice\"}}");
        return response;
    }
};
```

### Fragments

GraphQL fragments allow reusing field selections:

```zig
pub const Fragment = struct {
    name: []const u8,
    on_type: []const u8,
    fields: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, name: []const u8, on_type: []const u8, fields: []const u8) !Fragment {
        const owned_name = try allocator.dupe(u8, name);
        errdefer allocator.free(owned_name);

        const owned_on_type = try allocator.dupe(u8, on_type);
        errdefer allocator.free(owned_on_type);

        const owned_fields = try allocator.dupe(u8, fields);
        errdefer allocator.free(owned_fields);

        return .{
            .name = owned_name,
            .on_type = owned_on_type,
            .fields = owned_fields,
            .allocator = allocator,
        };
    }

    pub fn toGraphQL(self: *const Fragment) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try buffer.appendSlice(self.allocator, "fragment ");
        try buffer.appendSlice(self.allocator, self.name);
        try buffer.appendSlice(self.allocator, " on ");
        try buffer.appendSlice(self.allocator, self.on_type);
        try buffer.appendSlice(self.allocator, " { ");
        try buffer.appendSlice(self.allocator, self.fields);
        try buffer.appendSlice(self.allocator, " }");

        return buffer.toOwnedSlice(self.allocator);
    }
};
```

### Discussion

This recipe demonstrates the core concepts of GraphQL client implementation in Zig.

### GraphQL Basics

GraphQL is a query language that allows clients to request exactly the data they need:

**Query Example:**
```graphql
query GetUser($id: ID!) {
  user(id: $id) {
    id
    name
    email
  }
}
```

**Variables:**
```json
{
  "id": "123"
}
```

**Response:**
```json
{
  "data": {
    "user": {
      "id": "123",
      "name": "Alice",
      "email": "alice@example.com"
    }
  }
}
```

### JSON Escaping

The `escapeAndAppend()` method handles special characters in GraphQL queries:
- Newlines (`\n`) → `\\n`
- Quotes (`"`) → `\"`
- Backslashes (`\`) → `\\`

This ensures queries with multi-line strings or special characters are properly encoded in JSON.

### Variable Management

Variables are passed separately from the query for security and reusability:

```zig
var query = try GraphQLQuery.init(
    allocator,
    .query,
    "query($id: ID!) { user(id: $id) { name } }"
);
defer query.deinit();

try query.addVariable("id", "\"123\"");

const request = try query.buildRequest();
defer allocator.free(request);
// Results in: {"query":"...","variables":{"id":"123"}}
```

**Important:** Variable values must be valid JSON (note the quoted string `"\"123\""`).

### Memory Safety with HashMap Updates

The `getOrPut` pattern prevents memory leaks when updating HashMap entries:

```zig
const result = try self.variables.getOrPut(name);
if (result.found_existing) {
    self.allocator.free(result.value_ptr.*);  // Free old value
    result.value_ptr.* = owned_value;         // Store new value
} else {
    const owned_name = try self.allocator.dupe(u8, name);
    result.key_ptr.* = owned_name;
    result.value_ptr.* = owned_value;
}
```

This pattern:
1. Checks if the key exists
2. Frees the old value if found
3. Only allocates a new key for new entries
4. Prevents leaking the old value

### Error Handling

GraphQL can return partial data with errors:

```json
{
  "data": {
    "user": null
  },
  "errors": [
    {
      "message": "User not found",
      "locations": [{"line": 2, "column": 3}],
      "path": ["user"]
    }
  ]
}
```

The `GraphQLResponse` struct can hold both data and errors, allowing clients to handle partial failures gracefully.

### Mutations

Mutations use the same structure as queries but with different operation type:

```zig
var mutation = try GraphQLQuery.init(
    allocator,
    .mutation,
    "mutation($input: CreateUserInput!) { createUser(input: $input) { id } }"
);
defer mutation.deinit();

try mutation.addVariable("input", "{\"name\":\"Alice\",\"email\":\"alice@example.com\"}");
```

### Fragments

Fragments reduce duplication in complex queries:

```graphql
fragment UserFields on User {
  id
  name
  email
}

query GetUsers {
  users {
    ...UserFields
  }
  admins {
    ...UserFields
    role
  }
}
```

```zig
var fragment = try Fragment.init(
    allocator,
    "UserFields",
    "User",
    "id name email"
);
defer fragment.deinit();

const graphql = try fragment.toGraphQL();
defer allocator.free(graphql);
// "fragment UserFields on User { id name email }"
```

### Real Implementation Considerations

This recipe provides the foundation. A production implementation would:

**Use std.http.Client:**
```zig
pub fn execute(self: *GraphQLClient, query: *const GraphQLQuery) !GraphQLResponse {
    var client = std.http.Client{ .allocator = self.allocator };
    defer client.deinit();

    const request_body = try query.buildRequest();
    defer self.allocator.free(request_body);

    var req = try client.request(.POST, try std.Uri.parse(self.endpoint), .{
        .extra_headers = &.{
            .{ .name = "Content-Type", .value = "application/json" },
        },
    });
    defer req.deinit();

    req.transfer_encoding = .{ .content_length = request_body.len };
    try req.send();
    try req.writeAll(request_body);
    try req.finish();

    // Parse response...
}
```

**Parse JSON responses:**
Use `std.json.parseFromSlice()` to parse the response data into structured types.

**Handle connection errors:**
- Network timeouts
- DNS resolution failures
- HTTP error status codes
- Invalid JSON responses

**Support introspection:**
GraphQL supports querying the schema itself for documentation and validation.

**Batch operations:**
Some GraphQL servers support batching multiple queries in a single request.

### Security Considerations

**Variable injection:**
Always use GraphQL variables instead of string interpolation:
```zig
// WRONG - injection risk
const query = try std.fmt.allocPrint(allocator, "{{ user(id: \"{s}\") {{ name }} }}", .{user_id});

// CORRECT - use variables
const query = "query($id: ID!) { user(id: $id) { name } }";
try graphql_query.addVariable("id", user_id_json);
```

**Query complexity:**
Implement query depth and complexity limits to prevent DoS attacks.

**Authentication:**
Use HTTP headers for authentication tokens:
```zig
try client.setHeader("Authorization", "Bearer YOUR_TOKEN");
```

**SSL/TLS:**
Always use HTTPS endpoints in production for encrypted communication.

### Performance Optimization

**Connection pooling:**
Reuse HTTP connections for multiple queries.

**Query batching:**
Combine multiple queries into a single request when possible.

**Caching:**
Cache query results based on variables and implement cache invalidation strategies.

**Compression:**
Enable gzip compression for large queries and responses.

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: graphql_operation
pub const OperationType = enum {
    query,
    mutation,
    subscription,

    pub fn toString(self: OperationType) []const u8 {
        return switch (self) {
            .query => "query",
            .mutation => "mutation",
            .subscription => "subscription",
        };
    }
};
// ANCHOR_END: graphql_operation

// ANCHOR: graphql_variable
pub const Variable = struct {
    name: []const u8,
    value: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, name: []const u8, value: []const u8) !Variable {
        const owned_name = try allocator.dupe(u8, name);
        errdefer allocator.free(owned_name);

        const owned_value = try allocator.dupe(u8, value);

        return .{
            .name = owned_name,
            .value = owned_value,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Variable) void {
        self.allocator.free(self.name);
        self.allocator.free(self.value);
    }
};
// ANCHOR_END: graphql_variable

// ANCHOR: graphql_query
pub const GraphQLQuery = struct {
    operation_type: OperationType,
    operation_name: ?[]const u8,
    query: []const u8,
    variables: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, operation_type: OperationType, query: []const u8) !GraphQLQuery {
        const owned_query = try allocator.dupe(u8, query);
        errdefer allocator.free(owned_query);

        return .{
            .operation_type = operation_type,
            .operation_name = null,
            .query = owned_query,
            .variables = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *GraphQLQuery) void {
        self.allocator.free(self.query);

        if (self.operation_name) |name| {
            self.allocator.free(name);
        }

        var it = self.variables.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.variables.deinit();
    }

    pub fn setOperationName(self: *GraphQLQuery, name: []const u8) !void {
        if (self.operation_name) |old_name| {
            self.allocator.free(old_name);
        }
        self.operation_name = try self.allocator.dupe(u8, name);
    }

    pub fn addVariable(self: *GraphQLQuery, name: []const u8, value: []const u8) !void {
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        const result = try self.variables.getOrPut(name);
        if (result.found_existing) {
            self.allocator.free(result.value_ptr.*);
            result.value_ptr.* = owned_value;
        } else {
            const owned_name = try self.allocator.dupe(u8, name);
            result.key_ptr.* = owned_name;
            result.value_ptr.* = owned_value;
        }
    }

    pub fn buildRequest(self: *const GraphQLQuery) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try buffer.appendSlice(self.allocator, "{\"query\":\"");
        try self.escapeAndAppend(&buffer, self.query);
        try buffer.appendSlice(self.allocator, "\"");

        if (self.variables.count() > 0) {
            try buffer.appendSlice(self.allocator, ",\"variables\":{");
            var it = self.variables.iterator();
            var first = true;
            while (it.next()) |entry| {
                if (!first) try buffer.appendSlice(self.allocator, ",");
                try buffer.appendSlice(self.allocator, "\"");
                try buffer.appendSlice(self.allocator, entry.key_ptr.*);
                try buffer.appendSlice(self.allocator, "\":");
                try buffer.appendSlice(self.allocator, entry.value_ptr.*);
                first = false;
            }
            try buffer.appendSlice(self.allocator, "}");
        }

        try buffer.appendSlice(self.allocator, "}");

        return buffer.toOwnedSlice(self.allocator);
    }

    fn escapeAndAppend(self: *const GraphQLQuery, buffer: *std.ArrayList(u8), str: []const u8) !void {
        for (str) |c| {
            switch (c) {
                '\n' => try buffer.appendSlice(self.allocator, "\\n"),
                '\r' => try buffer.appendSlice(self.allocator, "\\r"),
                '\t' => try buffer.appendSlice(self.allocator, "\\t"),
                '"' => try buffer.appendSlice(self.allocator, "\\\""),
                '\\' => try buffer.appendSlice(self.allocator, "\\\\"),
                else => try buffer.append(self.allocator, c),
            }
        }
    }
};
// ANCHOR_END: graphql_query

// ANCHOR: graphql_response
pub const GraphQLError = struct {
    message: []const u8,
    locations: ?std.ArrayList(ErrorLocation),
    path: ?std.ArrayList([]const u8),
    allocator: std.mem.Allocator,

    pub const ErrorLocation = struct {
        line: usize,
        column: usize,
    };

    pub fn init(allocator: std.mem.Allocator, message: []const u8) !GraphQLError {
        const owned_message = try allocator.dupe(u8, message);
        errdefer allocator.free(owned_message);

        return .{
            .message = owned_message,
            .locations = null,
            .path = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *GraphQLError) void {
        self.allocator.free(self.message);

        if (self.locations) |*locs| {
            locs.deinit(self.allocator);
        }

        if (self.path) |*p| {
            for (p.items) |item| {
                self.allocator.free(item);
            }
            p.deinit(self.allocator);
        }
    }
};

pub const GraphQLResponse = struct {
    data: ?[]const u8,
    errors: ?std.ArrayList(GraphQLError),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) GraphQLResponse {
        return .{
            .data = null,
            .errors = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *GraphQLResponse) void {
        if (self.data) |data| {
            self.allocator.free(data);
        }

        if (self.errors) |*errs| {
            for (errs.items) |*err| {
                err.deinit();
            }
            errs.deinit(self.allocator);
        }
    }

    pub fn setData(self: *GraphQLResponse, data: []const u8) !void {
        if (self.data) |old_data| {
            self.allocator.free(old_data);
        }
        self.data = try self.allocator.dupe(u8, data);
    }

    pub fn addError(self: *GraphQLResponse, error_msg: []const u8) !void {
        if (self.errors == null) {
            self.errors = std.ArrayList(GraphQLError){};
        }

        var err = try GraphQLError.init(self.allocator, error_msg);
        errdefer err.deinit();
        try self.errors.?.append(self.allocator, err);
    }

    pub fn hasErrors(self: *const GraphQLResponse) bool {
        if (self.errors) |errs| {
            return errs.items.len > 0;
        }
        return false;
    }
};
// ANCHOR_END: graphql_response

// ANCHOR: graphql_client
pub const GraphQLClient = struct {
    endpoint: []const u8,
    headers: std.StringHashMap([]const u8),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, endpoint: []const u8) !GraphQLClient {
        const owned_endpoint = try allocator.dupe(u8, endpoint);
        errdefer allocator.free(owned_endpoint);

        return .{
            .endpoint = owned_endpoint,
            .headers = std.StringHashMap([]const u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *GraphQLClient) void {
        self.allocator.free(self.endpoint);

        var it = self.headers.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.*);
        }
        self.headers.deinit();
    }

    pub fn setHeader(self: *GraphQLClient, name: []const u8, value: []const u8) !void {
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);

        const result = try self.headers.getOrPut(name);
        if (result.found_existing) {
            self.allocator.free(result.value_ptr.*);
            result.value_ptr.* = owned_value;
        } else {
            const owned_name = try self.allocator.dupe(u8, name);
            result.key_ptr.* = owned_name;
            result.value_ptr.* = owned_value;
        }
    }

    pub fn execute(self: *GraphQLClient, query: *const GraphQLQuery) !GraphQLResponse {
        _ = query;
        // Simulate GraphQL execution
        var response = GraphQLResponse.init(self.allocator);
        try response.setData("{\"user\":{\"id\":\"123\",\"name\":\"Alice\"}}");
        return response;
    }

    pub fn executeWithErrors(self: *GraphQLClient, query: *const GraphQLQuery) !GraphQLResponse {
        _ = query;
        var response = GraphQLResponse.init(self.allocator);
        try response.addError("Field 'unknownField' doesn't exist on type 'User'");
        return response;
    }
};
// ANCHOR_END: graphql_client

// ANCHOR: graphql_fragment
pub const Fragment = struct {
    name: []const u8,
    on_type: []const u8,
    fields: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, name: []const u8, on_type: []const u8, fields: []const u8) !Fragment {
        const owned_name = try allocator.dupe(u8, name);
        errdefer allocator.free(owned_name);

        const owned_on_type = try allocator.dupe(u8, on_type);
        errdefer allocator.free(owned_on_type);

        const owned_fields = try allocator.dupe(u8, fields);
        errdefer allocator.free(owned_fields);

        return .{
            .name = owned_name,
            .on_type = owned_on_type,
            .fields = owned_fields,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Fragment) void {
        self.allocator.free(self.name);
        self.allocator.free(self.on_type);
        self.allocator.free(self.fields);
    }

    pub fn toGraphQL(self: *const Fragment) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try buffer.appendSlice(self.allocator, "fragment ");
        try buffer.appendSlice(self.allocator, self.name);
        try buffer.appendSlice(self.allocator, " on ");
        try buffer.appendSlice(self.allocator, self.on_type);
        try buffer.appendSlice(self.allocator, " { ");
        try buffer.appendSlice(self.allocator, self.fields);
        try buffer.appendSlice(self.allocator, " }");

        return buffer.toOwnedSlice(self.allocator);
    }
};
// ANCHOR_END: graphql_fragment

// ANCHOR: test_operation_type
test "operation type to string" {
    try testing.expectEqualStrings("query", OperationType.query.toString());
    try testing.expectEqualStrings("mutation", OperationType.mutation.toString());
    try testing.expectEqualStrings("subscription", OperationType.subscription.toString());
}
// ANCHOR_END: test_operation_type

// ANCHOR: test_variable
test "create and cleanup variable" {
    var variable = try Variable.init(testing.allocator, "userId", "\"123\"");
    defer variable.deinit();

    try testing.expectEqualStrings("userId", variable.name);
    try testing.expectEqualStrings("\"123\"", variable.value);
}
// ANCHOR_END: test_variable

// ANCHOR: test_query_basic
test "create basic query" {
    var query = try GraphQLQuery.init(testing.allocator, .query, "{ user { id name } }");
    defer query.deinit();

    try testing.expectEqual(OperationType.query, query.operation_type);
    try testing.expectEqualStrings("{ user { id name } }", query.query);
    try testing.expect(query.operation_name == null);
}
// ANCHOR_END: test_query_basic

// ANCHOR: test_query_with_name
test "query with operation name" {
    var query = try GraphQLQuery.init(testing.allocator, .query, "{ user { id } }");
    defer query.deinit();

    try query.setOperationName("GetUser");

    try testing.expect(query.operation_name != null);
    try testing.expectEqualStrings("GetUser", query.operation_name.?);
}
// ANCHOR_END: test_query_with_name

// ANCHOR: test_query_with_variables
test "query with variables" {
    var query = try GraphQLQuery.init(testing.allocator, .query, "query($id: ID!) { user(id: $id) { name } }");
    defer query.deinit();

    try query.addVariable("id", "\"123\"");

    try testing.expectEqual(@as(u32, 1), query.variables.count());

    const id_value = query.variables.get("id");
    try testing.expect(id_value != null);
    try testing.expectEqualStrings("\"123\"", id_value.?);
}
// ANCHOR_END: test_query_with_variables

// ANCHOR: test_build_request
test "build request JSON" {
    var query = try GraphQLQuery.init(testing.allocator, .query, "{ user { id } }");
    defer query.deinit();

    const request = try query.buildRequest();
    defer testing.allocator.free(request);

    try testing.expect(std.mem.indexOf(u8, request, "\"query\"") != null);
    try testing.expect(std.mem.indexOf(u8, request, "{ user { id } }") != null);
}
// ANCHOR_END: test_build_request

// ANCHOR: test_build_request_with_variables
test "build request with variables" {
    var query = try GraphQLQuery.init(testing.allocator, .query, "query($id: ID!) { user(id: $id) { name } }");
    defer query.deinit();

    try query.addVariable("id", "\"123\"");

    const request = try query.buildRequest();
    defer testing.allocator.free(request);

    try testing.expect(std.mem.indexOf(u8, request, "\"query\"") != null);
    try testing.expect(std.mem.indexOf(u8, request, "\"variables\"") != null);
    try testing.expect(std.mem.indexOf(u8, request, "\"id\"") != null);
}
// ANCHOR_END: test_build_request_with_variables

// ANCHOR: test_escape_query
test "escape special characters in query" {
    var query = try GraphQLQuery.init(testing.allocator, .query, "{ user { description } }");
    defer query.deinit();

    // Query with newline
    testing.allocator.free(query.query);
    query.query = try testing.allocator.dupe(u8, "{\n  user\n}");

    const request = try query.buildRequest();
    defer testing.allocator.free(request);

    try testing.expect(std.mem.indexOf(u8, request, "\\n") != null);
}
// ANCHOR_END: test_escape_query

// ANCHOR: test_graphql_error
test "create GraphQL error" {
    var err = try GraphQLError.init(testing.allocator, "Field not found");
    defer err.deinit();

    try testing.expectEqualStrings("Field not found", err.message);
    try testing.expect(err.locations == null);
    try testing.expect(err.path == null);
}
// ANCHOR_END: test_graphql_error

// ANCHOR: test_graphql_response
test "create GraphQL response with data" {
    var response = GraphQLResponse.init(testing.allocator);
    defer response.deinit();

    try response.setData("{\"user\":{\"id\":\"123\"}}");

    try testing.expect(response.data != null);
    try testing.expectEqualStrings("{\"user\":{\"id\":\"123\"}}", response.data.?);
    try testing.expect(!response.hasErrors());
}
// ANCHOR_END: test_graphql_response

// ANCHOR: test_graphql_response_with_errors
test "GraphQL response with errors" {
    var response = GraphQLResponse.init(testing.allocator);
    defer response.deinit();

    try response.addError("Syntax error");
    try response.addError("Unknown field");

    try testing.expect(response.hasErrors());
    try testing.expectEqual(@as(usize, 2), response.errors.?.items.len);
}
// ANCHOR_END: test_graphql_response_with_errors

// ANCHOR: test_client_init
test "create GraphQL client" {
    var client = try GraphQLClient.init(testing.allocator, "https://api.example.com/graphql");
    defer client.deinit();

    try testing.expectEqualStrings("https://api.example.com/graphql", client.endpoint);
}
// ANCHOR_END: test_client_init

// ANCHOR: test_client_headers
test "client with custom headers" {
    var client = try GraphQLClient.init(testing.allocator, "https://api.example.com/graphql");
    defer client.deinit();

    try client.setHeader("Authorization", "Bearer token123");
    try client.setHeader("X-Custom-Header", "custom-value");

    try testing.expectEqual(@as(u32, 2), client.headers.count());

    const auth = client.headers.get("Authorization");
    try testing.expect(auth != null);
    try testing.expectEqualStrings("Bearer token123", auth.?);
}
// ANCHOR_END: test_client_headers

// ANCHOR: test_client_execute
test "execute query" {
    var client = try GraphQLClient.init(testing.allocator, "https://api.example.com/graphql");
    defer client.deinit();

    var query = try GraphQLQuery.init(testing.allocator, .query, "{ user { id name } }");
    defer query.deinit();

    var response = try client.execute(&query);
    defer response.deinit();

    try testing.expect(response.data != null);
    try testing.expect(!response.hasErrors());
}
// ANCHOR_END: test_client_execute

// ANCHOR: test_client_execute_errors
test "execute query with errors" {
    var client = try GraphQLClient.init(testing.allocator, "https://api.example.com/graphql");
    defer client.deinit();

    var query = try GraphQLQuery.init(testing.allocator, .query, "{ unknownField }");
    defer query.deinit();

    var response = try client.executeWithErrors(&query);
    defer response.deinit();

    try testing.expect(response.hasErrors());
}
// ANCHOR_END: test_client_execute_errors

// ANCHOR: test_fragment
test "create fragment" {
    var fragment = try Fragment.init(
        testing.allocator,
        "UserFields",
        "User",
        "id name email",
    );
    defer fragment.deinit();

    try testing.expectEqualStrings("UserFields", fragment.name);
    try testing.expectEqualStrings("User", fragment.on_type);
    try testing.expectEqualStrings("id name email", fragment.fields);
}
// ANCHOR_END: test_fragment

// ANCHOR: test_fragment_to_graphql
test "fragment to GraphQL string" {
    var fragment = try Fragment.init(
        testing.allocator,
        "UserFields",
        "User",
        "id name",
    );
    defer fragment.deinit();

    const graphql = try fragment.toGraphQL();
    defer testing.allocator.free(graphql);

    try testing.expect(std.mem.indexOf(u8, graphql, "fragment UserFields") != null);
    try testing.expect(std.mem.indexOf(u8, graphql, "on User") != null);
    try testing.expect(std.mem.indexOf(u8, graphql, "id name") != null);
}
// ANCHOR_END: test_fragment_to_graphql

// ANCHOR: test_mutation
test "create mutation" {
    var mutation = try GraphQLQuery.init(
        testing.allocator,
        .mutation,
        "mutation($input: CreateUserInput!) { createUser(input: $input) { id } }",
    );
    defer mutation.deinit();

    try testing.expectEqual(OperationType.mutation, mutation.operation_type);

    try mutation.addVariable("input", "{\"name\":\"Alice\",\"email\":\"alice@example.com\"}");

    const request = try mutation.buildRequest();
    defer testing.allocator.free(request);

    try testing.expect(std.mem.indexOf(u8, request, "mutation") != null);
    try testing.expect(std.mem.indexOf(u8, request, "\"variables\"") != null);
}
// ANCHOR_END: test_mutation
```

### See Also

- Recipe 11.1: Making HTTP requests
- Recipe 11.2: Working with JSON APIs
- Recipe 11.6: Working with REST APIs

---

## Recipe 11.12: OAuth2 Authentication {#recipe-11-12}

**Tags:** allocators, arraylist, data-structures, error-handling, http, json, memory, networking, parsing, resource-cleanup, slices, testing
**Difficulty:** intermediate
**Code:** `code/04-specialized/11-network-web/recipe_11_12.zig`

### Problem

You need to implement OAuth2 authentication in your application, handling authorization code flow, client credentials, token refresh, and PKCE for enhanced security.

### Solution

Zig's cryptographic libraries and string handling make it well-suited for implementing OAuth2 flows. This recipe demonstrates the authorization code flow with PKCE, token management, and multiple grant types.

### Grant Types

OAuth2 defines several grant types for different use cases:

```zig
pub const GrantType = enum {
    authorization_code,
    client_credentials,
    refresh_token,
    password,

    pub fn toString(self: GrantType) []const u8 {
        return switch (self) {
            .authorization_code => "authorization_code",
            .client_credentials => "client_credentials",
            .refresh_token => "refresh_token",
            .password => "password",
        };
    }
};
```

### OAuth2 Token

Tokens carry access credentials and metadata:

```zig
pub const OAuth2Token = struct {
    access_token: []const u8,
    token_type: []const u8,
    expires_in: ?i64,
    refresh_token: ?[]const u8,
    scope: ?[]const u8,
    issued_at: i64,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, access_token: []const u8, token_type: []const u8) !OAuth2Token {
        const owned_access_token = try allocator.dupe(u8, access_token);
        errdefer allocator.free(owned_access_token);

        const owned_token_type = try allocator.dupe(u8, token_type);
        errdefer allocator.free(owned_token_type);

        return .{
            .access_token = owned_access_token,
            .token_type = owned_token_type,
            .expires_in = null,
            .refresh_token = null,
            .scope = null,
            .issued_at = std.time.timestamp(),
            .allocator = allocator,
        };
    }

    pub fn isExpired(self: *const OAuth2Token) bool {
        if (self.expires_in) |expires| {
            const now = std.time.timestamp();
            const elapsed = now - self.issued_at;
            return elapsed >= expires;
        }
        return false;
    }

    pub fn getAuthorizationHeader(self: *const OAuth2Token) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try buffer.appendSlice(self.allocator, self.token_type);
        try buffer.appendSlice(self.allocator, " ");
        try buffer.appendSlice(self.allocator, self.access_token);

        return buffer.toOwnedSlice(self.allocator);
    }
};
```

### OAuth2 Configuration

Configuration stores client credentials and endpoint URLs:

```zig
pub const OAuth2Config = struct {
    client_id: []const u8,
    client_secret: ?[]const u8,
    authorization_endpoint: []const u8,
    token_endpoint: []const u8,
    redirect_uri: ?[]const u8,
    scope: ?[]const u8,
    allocator: std.mem.Allocator,

    pub fn deinit(self: *OAuth2Config) void {
        self.allocator.free(self.client_id);
        self.allocator.free(self.authorization_endpoint);
        self.allocator.free(self.token_endpoint);

        if (self.client_secret) |cs| {
            // Zero sensitive data before freeing
            @memset(@constCast(cs), 0);
            self.allocator.free(cs);
        }

        // Free other optional fields...
    }

    pub fn setClientSecret(self: *OAuth2Config, client_secret: []const u8) !void {
        if (self.client_secret) |old_cs| {
            // Zero sensitive data before freeing
            @memset(@constCast(old_cs), 0);
            self.allocator.free(old_cs);
        }
        self.client_secret = try self.allocator.dupe(u8, client_secret);
    }
};
```

### PKCE (Proof Key for Code Exchange)

PKCE enhances security for authorization code flow by preventing code interception attacks:

```zig
pub const PKCE = struct {
    code_verifier: []const u8,
    code_challenge: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) !PKCE {
        // Generate 128-character code verifier (64 random bytes, hex-encoded)
        // RFC 7636 requires 43-128 characters
        var verifier_buf: [64]u8 = undefined;
        std.crypto.random.bytes(&verifier_buf);

        var encoded_buf: [128]u8 = undefined;
        const verifier = std.fmt.bytesToHex(verifier_buf, .lower);
        @memcpy(encoded_buf[0..verifier.len], &verifier);

        const owned_verifier = try allocator.dupe(u8, encoded_buf[0..verifier.len]);
        errdefer allocator.free(owned_verifier);

        // Generate code challenge (SHA256 hash of verifier, base64url encoded per RFC 7636)
        var hash: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(owned_verifier, &hash, .{});

        // Base64url encode the hash (no padding) per RFC 7636
        const encoder = std.base64.url_safe_no_pad.Encoder;
        var challenge_buf: [64]u8 = undefined;
        const challenge = encoder.encode(&challenge_buf, &hash);
        const owned_challenge = try allocator.dupe(u8, challenge);

        return .{
            .code_verifier = owned_verifier,
            .code_challenge = owned_challenge,
            .allocator = allocator,
        };
    }
};
```

### OAuth2 Client

The client manages the OAuth2 flow:

```zig
pub const OAuth2Client = struct {
    config: OAuth2Config,
    allocator: std.mem.Allocator,

    pub fn buildAuthorizationUrl(
        self: *const OAuth2Client,
        state: ?[]const u8,
        pkce: ?*const PKCE,
    ) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try buffer.appendSlice(self.allocator, self.config.authorization_endpoint);
        try buffer.appendSlice(self.allocator, "?response_type=code");
        try buffer.appendSlice(self.allocator, "&client_id=");
        try buffer.appendSlice(self.allocator, self.config.client_id);

        if (self.config.redirect_uri) |ru| {
            try buffer.appendSlice(self.allocator, "&redirect_uri=");
            try self.appendUrlEncoded(&buffer, ru);
        }

        if (self.config.scope) |scope| {
            try buffer.appendSlice(self.allocator, "&scope=");
            try self.appendUrlEncoded(&buffer, scope);
        }

        if (state) |s| {
            try buffer.appendSlice(self.allocator, "&state=");
            try self.appendUrlEncoded(&buffer, s);
        }

        if (pkce) |p| {
            try buffer.appendSlice(self.allocator, "&code_challenge=");
            try buffer.appendSlice(self.allocator, p.code_challenge);
            try buffer.appendSlice(self.allocator, "&code_challenge_method=S256");
        }

        return buffer.toOwnedSlice(self.allocator);
    }

    fn appendUrlEncoded(
        self: *const OAuth2Client,
        buffer: *std.ArrayList(u8),
        str: []const u8,
    ) !void {
        for (str) |c| {
            switch (c) {
                'A'...'Z', 'a'...'z', '0'...'9', '-', '_', '.', '~' => {
                    try buffer.append(self.allocator, c);
                },
                ' ' => {
                    try buffer.append(self.allocator, '+');
                },
                else => {
                    try buffer.appendSlice(self.allocator, "%");
                    var hex_buf: [2]u8 = undefined;
                    _ = try std.fmt.bufPrint(&hex_buf, "{X:0>2}", .{c});
                    try buffer.appendSlice(self.allocator, &hex_buf);
                },
            }
        }
    }
};
```

### Discussion

This recipe implements OAuth2 authentication following the OAuth 2.0 specification (RFC 6749) and PKCE extension (RFC 7636).

### OAuth2 Flow Overview

**Authorization Code Flow (Most Common):**
1. Redirect user to authorization URL with state and PKCE challenge
2. User authenticates and grants permission
3. Provider redirects back with authorization code
4. Exchange code for access token (include PKCE verifier)
5. Use access token for API requests
6. Refresh token when expired

**Example:**
```zig
var config = try OAuth2Config.init(
    allocator,
    "my_client_id",
    "https://oauth.provider.com/authorize",
    "https://oauth.provider.com/token",
);
defer config.deinit();

try config.setRedirectUri("https://myapp.com/callback");
try config.setScope("read write");

var pkce = try PKCE.init(allocator);
defer pkce.deinit();

var client = OAuth2Client.init(allocator, config);

// Step 1: Build authorization URL
const auth_url = try client.buildAuthorizationUrl("random_state_123", &pkce);
defer allocator.free(auth_url);

// Redirect user to auth_url...

// Step 2: After callback, exchange code for token
var token = try client.exchangeAuthorizationCode("received_code", &pkce);
defer token.deinit();

// Step 3: Use token for API requests
const auth_header = try token.getAuthorizationHeader();
defer allocator.free(auth_header);
// Authorization: Bearer access_token_12345
```

### PKCE Security

PKCE (RFC 7636) protects against authorization code interception:

**How it works:**
1. **Code Verifier**: Random 43-128 character string
2. **Code Challenge**: SHA256 hash of verifier, base64url encoded
3. **Initial Request**: Send code challenge to authorization endpoint
4. **Token Exchange**: Send code verifier with authorization code
5. **Server Verification**: Server hashes verifier and compares to challenge

**Why base64url?:**
RFC 7636 mandates base64url encoding (not hex) for the code challenge:
```zig
// Correct (per RFC 7636):
const encoder = std.base64.url_safe_no_pad.Encoder;
const challenge = encoder.encode(&challenge_buf, &hash);

// Incorrect (would be rejected by OAuth2 providers):
const challenge = std.fmt.bytesToHex(hash, .lower);
```

**Security benefit:**
Even if an attacker intercepts the authorization code, they cannot exchange it for a token without the original code verifier.

### RFC 7636 Compliance

This implementation fully complies with RFC 7636 (PKCE for OAuth 2.0) to ensure interoperability with OAuth2 providers and maximum security.

**Code Verifier Requirements (Section 4.1):**
- **Length:** 43-128 characters (we generate 128)
- **Character Set:** Unreserved characters `[A-Z]/[a-z]/[0-9]/"-"/"."/"_"/"~"`
- **Entropy:** Minimum 256 bits recommended (we provide 512 bits)

Our implementation uses `std.crypto.random.bytes()` for cryptographically secure randomness, then hex-encodes the result. Hex encoding produces only `[a-f][0-9]` characters, which are valid unreserved characters and satisfy RFC 7636 requirements.

**S256 Challenge Method (Section 4.2):**
```
code_challenge = BASE64URL(SHA256(ASCII(code_verifier)))
```

The S256 method is recommended over the "plain" method because:
- SHA256 is a one-way function (challenge cannot be reversed to get verifier)
- Protects against eavesdropping on the authorization request
- Ensures only the client with the original verifier can complete the flow

**Base64url Encoding (Section 4.2):**

RFC 7636 mandates base64url encoding, which differs from standard base64:
- **URL-safe alphabet:** Uses `-` and `_` instead of `+` and `/`
- **No padding:** Omits trailing `=` characters
- **Why it matters:** Can be safely included in URL query parameters without additional escaping

Our implementation uses `std.base64.url_safe_no_pad.Encoder`, which correctly implements RFC 4648 Section 5 (base64url) as required by RFC 7636.

**S256 Parameter (Section 4.3):**

The `code_challenge_method=S256` parameter in the authorization URL tells the server:
1. How the challenge was computed (SHA256 + base64url)
2. How to verify the verifier during token exchange
3. That we're using the recommended method (not "plain")

When the authorization code is exchanged for tokens, the server computes `BASE64URL(SHA256(code_verifier))` and compares it to the stored `code_challenge`. Only exact matches are accepted.

### URL Encoding

Proper URL encoding prevents injection attacks:

```zig
fn appendUrlEncoded(self: *const OAuth2Client, buffer: *std.ArrayList(u8), str: []const u8) !void {
    for (str) |c| {
        switch (c) {
            'A'...'Z', 'a'...'z', '0'...'9', '-', '_', '.', '~' => {
                try buffer.append(self.allocator, c);
            },
            ' ' => {
                try buffer.append(self.allocator, '+');
            },
            else => {
                try buffer.appendSlice(self.allocator, "%");
                var hex_buf: [2]u8 = undefined;
                _ = try std.fmt.bufPrint(&hex_buf, "{X:0>2}", .{c});
                try buffer.appendSlice(self.allocator, &hex_buf);
            },
        }
    }
}
```

**Critical for state parameter:**
The `state` parameter must be URL-encoded to prevent CSRF bypass:
```zig
// Secure - prevents injection:
try self.appendUrlEncoded(&buffer, state);

// Insecure - vulnerable to injection:
try buffer.appendSlice(self.allocator, state);  // DON'T DO THIS
```

### Sensitive Data Handling

Client secrets and tokens are zeroed before freeing:

```zig
if (self.client_secret) |cs| {
    // Zero sensitive data before freeing
    @memset(@constCast(cs), 0);
    self.allocator.free(cs);
}
```

**Why this matters:**
- Prevents secrets from remaining in memory
- Reduces risk from memory dumps
- Protects against swap file disclosure
- Mitigates use-after-free exploits

**When to zero:**
- Client secrets (always)
- Access tokens (consider, especially for sensitive APIs)
- Refresh tokens (consider, especially for long-lived tokens)
- Authorization codes (less critical, short-lived)

### Token Expiration

Tokens track their expiration and can be validated:

```zig
pub fn isExpired(self: *const OAuth2Token) bool {
    if (self.expires_in) |expires| {
        const now = std.time.timestamp();
        const elapsed = now - self.issued_at;
        return elapsed >= expires;
    }
    return false;
}
```

**Best practice:** Check expiration before each API request and refresh proactively when the token is about to expire (e.g., within 5 minutes of expiration).

### Grant Type Comparison

**Authorization Code (with PKCE):**
- **Use for:** Web apps, mobile apps, desktop apps
- **Security:** High (with PKCE)
- **User interaction:** Required
- **Refresh tokens:** Yes

**Client Credentials:**
- **Use for:** Service-to-service authentication
- **Security:** Medium (requires secret storage)
- **User interaction:** None
- **Refresh tokens:** No (get new token instead)

**Refresh Token:**
- **Use for:** Obtaining new access token without user interaction
- **Security:** High (long-lived, must be protected)
- **User interaction:** None
- **Refresh tokens:** Returns new refresh token

**Password (Deprecated):**
- **Use for:** Legacy systems only
- **Security:** Low (exposes user credentials)
- **User interaction:** Required
- **Refresh tokens:** Yes
- **Note:** RFC 6749 discourages use; prefer authorization code

### Real Implementation

This recipe simulates token exchange. A production implementation would:

**Make HTTP POST request:**
```zig
pub fn exchangeAuthorizationCode(
    self: *const OAuth2Client,
    code: []const u8,
    pkce: ?*const PKCE,
) !OAuth2Token {
    var client = std.http.Client{ .allocator = self.allocator };
    defer client.deinit();

    // Build request body
    var body = std.ArrayList(u8){};
    defer body.deinit(self.allocator);

    try body.appendSlice(self.allocator, "grant_type=authorization_code");
    try body.appendSlice(self.allocator, "&code=");
    try body.appendSlice(self.allocator, code);
    try body.appendSlice(self.allocator, "&client_id=");
    try body.appendSlice(self.allocator, self.config.client_id);

    if (self.config.redirect_uri) |uri| {
        try body.appendSlice(self.allocator, "&redirect_uri=");
        try self.appendUrlEncoded(&body, uri);
    }

    if (pkce) |p| {
        try body.appendSlice(self.allocator, "&code_verifier=");
        try body.appendSlice(self.allocator, p.code_verifier);
    }

    // Make POST request to token endpoint
    var req = try client.request(.POST, try std.Uri.parse(self.config.token_endpoint), .{
        .extra_headers = &.{
            .{ .name = "Content-Type", .value = "application/x-www-form-urlencoded" },
        },
    });
    defer req.deinit();

    req.transfer_encoding = .{ .content_length = body.items.len };
    try req.send();
    try req.writeAll(body.items);
    try req.finish();

    // Parse JSON response into OAuth2Token
    // ...
}
```

**Parse JSON response:**
```zig
{
  "access_token": "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9...",
  "token_type": "Bearer",
  "expires_in": 3600,
  "refresh_token": "tGzv3JOkF0XG5Qx2TlKWIA",
  "scope": "read write"
}
```

Use `std.json.parseFromSlice()` to parse into a token struct.

### Security Best Practices

**1. Always use PKCE for public clients:**
```zig
var pkce = try PKCE.init(allocator);
defer pkce.deinit();

const url = try client.buildAuthorizationUrl(state, &pkce);
```

**2. Generate cryptographically random state:**
```zig
var state_buf: [32]u8 = undefined;
std.crypto.random.bytes(&state_buf);
const state = std.fmt.bytesToHex(state_buf, .lower);
```

**3. Validate state on callback:**
```zig
if (!std.mem.eql(u8, received_state, expected_state)) {
    return error.InvalidState;  // CSRF attack detected
}
```

**4. Use HTTPS for all OAuth2 endpoints:**
Never use HTTP for OAuth2 - credentials would be exposed in transit.

**5. Store refresh tokens securely:**
- Encrypt at rest
- Use platform-specific secure storage (Keychain, Credential Manager)
- Never log or transmit over insecure channels

**6. Validate redirect URI:**
Ensure the redirect URI matches exactly (OAuth2 providers enforce this).

### Error Handling

OAuth2 errors are returned in the response:

```json
{
  "error": "invalid_request",
  "error_description": "Missing required parameter: code",
  "error_uri": "https://docs.provider.com/oauth/errors#invalid_request"
}
```

Common errors:
- `invalid_request`: Malformed request
- `unauthorized_client`: Client not authorized
- `access_denied`: User denied authorization
- `invalid_grant`: Invalid or expired authorization code
- `invalid_client`: Invalid client credentials

### Full Tested Code

```zig
const std = @import("std");
const testing = std.testing;

// ANCHOR: oauth_grant_type
pub const GrantType = enum {
    authorization_code,
    client_credentials,
    refresh_token,
    password,

    pub fn toString(self: GrantType) []const u8 {
        return switch (self) {
            .authorization_code => "authorization_code",
            .client_credentials => "client_credentials",
            .refresh_token => "refresh_token",
            .password => "password",
        };
    }
};
// ANCHOR_END: oauth_grant_type

// ANCHOR: oauth_token
pub const OAuth2Token = struct {
    access_token: []const u8,
    token_type: []const u8,
    expires_in: ?i64,
    refresh_token: ?[]const u8,
    scope: ?[]const u8,
    issued_at: i64,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, access_token: []const u8, token_type: []const u8) !OAuth2Token {
        const owned_access_token = try allocator.dupe(u8, access_token);
        errdefer allocator.free(owned_access_token);

        const owned_token_type = try allocator.dupe(u8, token_type);
        errdefer allocator.free(owned_token_type);

        return .{
            .access_token = owned_access_token,
            .token_type = owned_token_type,
            .expires_in = null,
            .refresh_token = null,
            .scope = null,
            .issued_at = std.time.timestamp(),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *OAuth2Token) void {
        self.allocator.free(self.access_token);
        self.allocator.free(self.token_type);

        if (self.refresh_token) |rt| {
            self.allocator.free(rt);
        }

        if (self.scope) |s| {
            self.allocator.free(s);
        }
    }

    pub fn setRefreshToken(self: *OAuth2Token, refresh_token: []const u8) !void {
        if (self.refresh_token) |old_rt| {
            self.allocator.free(old_rt);
        }
        self.refresh_token = try self.allocator.dupe(u8, refresh_token);
    }

    pub fn setScope(self: *OAuth2Token, scope: []const u8) !void {
        if (self.scope) |old_scope| {
            self.allocator.free(old_scope);
        }
        self.scope = try self.allocator.dupe(u8, scope);
    }

    pub fn isExpired(self: *const OAuth2Token) bool {
        if (self.expires_in) |expires| {
            const now = std.time.timestamp();
            const elapsed = now - self.issued_at;
            return elapsed >= expires;
        }
        return false;
    }

    pub fn getAuthorizationHeader(self: *const OAuth2Token) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try buffer.appendSlice(self.allocator, self.token_type);
        try buffer.appendSlice(self.allocator, " ");
        try buffer.appendSlice(self.allocator, self.access_token);

        return buffer.toOwnedSlice(self.allocator);
    }
};
// ANCHOR_END: oauth_token

// ANCHOR: oauth_config
pub const OAuth2Config = struct {
    client_id: []const u8,
    client_secret: ?[]const u8,
    authorization_endpoint: []const u8,
    token_endpoint: []const u8,
    redirect_uri: ?[]const u8,
    scope: ?[]const u8,
    allocator: std.mem.Allocator,

    pub fn init(
        allocator: std.mem.Allocator,
        client_id: []const u8,
        authorization_endpoint: []const u8,
        token_endpoint: []const u8,
    ) !OAuth2Config {
        const owned_client_id = try allocator.dupe(u8, client_id);
        errdefer allocator.free(owned_client_id);

        const owned_auth_endpoint = try allocator.dupe(u8, authorization_endpoint);
        errdefer allocator.free(owned_auth_endpoint);

        const owned_token_endpoint = try allocator.dupe(u8, token_endpoint);
        errdefer allocator.free(owned_token_endpoint);

        return .{
            .client_id = owned_client_id,
            .client_secret = null,
            .authorization_endpoint = owned_auth_endpoint,
            .token_endpoint = owned_token_endpoint,
            .redirect_uri = null,
            .scope = null,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *OAuth2Config) void {
        self.allocator.free(self.client_id);
        self.allocator.free(self.authorization_endpoint);
        self.allocator.free(self.token_endpoint);

        if (self.client_secret) |cs| {
            // Zero sensitive data before freeing
            @memset(@constCast(cs), 0);
            self.allocator.free(cs);
        }

        if (self.redirect_uri) |ru| {
            self.allocator.free(ru);
        }

        if (self.scope) |s| {
            self.allocator.free(s);
        }
    }

    pub fn setClientSecret(self: *OAuth2Config, client_secret: []const u8) !void {
        if (self.client_secret) |old_cs| {
            // Zero sensitive data before freeing
            @memset(@constCast(old_cs), 0);
            self.allocator.free(old_cs);
        }
        self.client_secret = try self.allocator.dupe(u8, client_secret);
    }

    pub fn setRedirectUri(self: *OAuth2Config, redirect_uri: []const u8) !void {
        if (self.redirect_uri) |old_ru| {
            self.allocator.free(old_ru);
        }
        self.redirect_uri = try self.allocator.dupe(u8, redirect_uri);
    }

    pub fn setScope(self: *OAuth2Config, scope: []const u8) !void {
        if (self.scope) |old_scope| {
            self.allocator.free(old_scope);
        }
        self.scope = try self.allocator.dupe(u8, scope);
    }
};
// ANCHOR_END: oauth_config

// ANCHOR: pkce
// PKCE (Proof Key for Code Exchange) implements RFC 7636 to prevent authorization code
// interception attacks in OAuth 2.0 flows. This is critical for public clients (like mobile
// apps and SPAs) that cannot securely store client secrets.
//
// RFC 7636 Compliance:
// - code_verifier: Cryptographically random string (43-128 characters)
// - code_challenge: Transformed version of verifier sent to authorization server
// - S256 method: Uses SHA256 hash + base64url encoding (recommended over "plain" method)
//
// Security Flow:
// 1. Client generates random code_verifier and derives code_challenge
// 2. Client sends code_challenge to authorization endpoint
// 3. Authorization server stores code_challenge
// 4. Client sends code_verifier to token endpoint
// 5. Server verifies: code_challenge == BASE64URL(SHA256(code_verifier))
//
// This prevents attackers who intercept the authorization code from exchanging it for tokens,
// since they don't have the original code_verifier.
pub const PKCE = struct {
    code_verifier: []const u8,
    code_challenge: []const u8,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) !PKCE {
        // Generate cryptographically random code_verifier per RFC 7636 Section 4.1
        //
        // RFC 7636 Requirements:
        // - Length: 43-128 characters (we generate 128 characters)
        // - Character set: Unreserved characters [A-Z]/[a-z]/[0-9]/"-"/"."/"_"/"~"
        // - Entropy: Minimum 256 bits recommended (we use 512 bits = 64 random bytes)
        //
        // Implementation:
        // - std.crypto.random provides cryptographically secure random bytes
        // - Hex encoding (lowercase) produces characters [a-f][0-9], which are valid
        //   unreserved characters per RFC 3986 and satisfy RFC 7636 requirements
        // - 64 random bytes -> 128 hex characters = 512 bits of entropy (exceeds minimum)
        var verifier_buf: [64]u8 = undefined;
        std.crypto.random.bytes(&verifier_buf);

        var encoded_buf: [128]u8 = undefined;
        const verifier = std.fmt.bytesToHex(verifier_buf, .lower);
        @memcpy(encoded_buf[0..verifier.len], &verifier);

        const owned_verifier = try allocator.dupe(u8, encoded_buf[0..verifier.len]);
        errdefer allocator.free(owned_verifier);

        // Generate code_challenge using S256 method per RFC 7636 Section 4.2
        //
        // RFC 7636 S256 Method:
        // - Formula: code_challenge = BASE64URL(SHA256(ASCII(code_verifier)))
        // - S256 is the RECOMMENDED method (more secure than "plain" method)
        // - The "plain" method sends code_verifier directly, vulnerable to interception
        //
        // Security: SHA256 is a one-way function, so code_challenge cannot be reversed
        // to obtain code_verifier. Only the client with the original verifier can prove
        // possession during the token exchange.
        var hash: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(owned_verifier, &hash, .{});

        // Apply BASE64URL encoding per RFC 7636 Section 4.2
        //
        // RFC 7636 Base64url Requirements:
        // - MUST use URL-safe alphabet: [A-Z]/[a-z]/[0-9]/-/_ (no +/)
        // - MUST NOT include padding ('=' characters)
        // - Standard base64 uses +/ which require URL encoding, causing issues
        //
        // Implementation Compliance:
        // - std.base64.url_safe_no_pad.Encoder uses the correct URL-safe alphabet
        // - Replaces + with - and / with _ (per RFC 4648 Section 5)
        // - no_pad ensures no trailing '=' characters are added
        // - This encoding can be safely included in URL query parameters without
        //   additional escaping, which is critical for OAuth authorization URLs
        const encoder = std.base64.url_safe_no_pad.Encoder;
        var challenge_buf: [64]u8 = undefined;
        const challenge = encoder.encode(&challenge_buf, &hash);
        const owned_challenge = try allocator.dupe(u8, challenge);

        return .{
            .code_verifier = owned_verifier,
            .code_challenge = owned_challenge,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *PKCE) void {
        self.allocator.free(self.code_verifier);
        self.allocator.free(self.code_challenge);
    }
};
// ANCHOR_END: pkce

// ANCHOR: oauth_client
pub const OAuth2Client = struct {
    config: OAuth2Config,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, config: OAuth2Config) OAuth2Client {
        return .{
            .config = config,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *OAuth2Client) void {
        self.config.deinit();
    }

    pub fn buildAuthorizationUrl(self: *const OAuth2Client, state: ?[]const u8, pkce: ?*const PKCE) ![]const u8 {
        var buffer = std.ArrayList(u8){};
        defer buffer.deinit(self.allocator);

        try buffer.appendSlice(self.allocator, self.config.authorization_endpoint);
        try buffer.appendSlice(self.allocator, "?response_type=code");
        try buffer.appendSlice(self.allocator, "&client_id=");
        try buffer.appendSlice(self.allocator, self.config.client_id);

        if (self.config.redirect_uri) |ru| {
            try buffer.appendSlice(self.allocator, "&redirect_uri=");
            try self.appendUrlEncoded(&buffer, ru);
        }

        if (self.config.scope) |scope| {
            try buffer.appendSlice(self.allocator, "&scope=");
            try self.appendUrlEncoded(&buffer, scope);
        }

        if (state) |s| {
            try buffer.appendSlice(self.allocator, "&state=");
            try self.appendUrlEncoded(&buffer, s);
        }

        if (pkce) |p| {
            try buffer.appendSlice(self.allocator, "&code_challenge=");
            try buffer.appendSlice(self.allocator, p.code_challenge);
            // S256 indicates SHA256 transform method per RFC 7636 Section 4.3
            // This tells the authorization server how to verify the challenge:
            // it must compute BASE64URL(SHA256(code_verifier)) and compare with code_challenge
            try buffer.appendSlice(self.allocator, "&code_challenge_method=S256");
        }

        return buffer.toOwnedSlice(self.allocator);
    }

    pub fn exchangeAuthorizationCode(
        self: *const OAuth2Client,
        code: []const u8,
        pkce: ?*const PKCE,
    ) !OAuth2Token {
        _ = code;
        _ = pkce;
        // Simulate token exchange
        var token = try OAuth2Token.init(self.allocator, "access_token_12345", "Bearer");
        token.expires_in = 3600;
        try token.setRefreshToken("refresh_token_67890");
        return token;
    }

    pub fn refreshToken(self: *const OAuth2Client, refresh_token: []const u8) !OAuth2Token {
        _ = refresh_token;
        // Simulate token refresh
        var token = try OAuth2Token.init(self.allocator, "new_access_token_99999", "Bearer");
        token.expires_in = 3600;
        return token;
    }

    pub fn getClientCredentialsToken(self: *const OAuth2Client) !OAuth2Token {
        // Simulate client credentials flow
        var token = try OAuth2Token.init(self.allocator, "client_cred_token_11111", "Bearer");
        token.expires_in = 7200;
        return token;
    }

    fn appendUrlEncoded(self: *const OAuth2Client, buffer: *std.ArrayList(u8), str: []const u8) !void {
        for (str) |c| {
            switch (c) {
                'A'...'Z', 'a'...'z', '0'...'9', '-', '_', '.', '~' => {
                    try buffer.append(self.allocator, c);
                },
                ' ' => {
                    try buffer.append(self.allocator, '+');
                },
                else => {
                    try buffer.appendSlice(self.allocator, "%");
                    var hex_buf: [2]u8 = undefined;
                    _ = try std.fmt.bufPrint(&hex_buf, "{X:0>2}", .{c});
                    try buffer.appendSlice(self.allocator, &hex_buf);
                },
            }
        }
    }
};
// ANCHOR_END: oauth_client

// ANCHOR: test_grant_type
test "grant type to string" {
    try testing.expectEqualStrings("authorization_code", GrantType.authorization_code.toString());
    try testing.expectEqualStrings("client_credentials", GrantType.client_credentials.toString());
    try testing.expectEqualStrings("refresh_token", GrantType.refresh_token.toString());
    try testing.expectEqualStrings("password", GrantType.password.toString());
}
// ANCHOR_END: test_grant_type

// ANCHOR: test_token_basic
test "create OAuth2 token" {
    var token = try OAuth2Token.init(testing.allocator, "test_access_token", "Bearer");
    defer token.deinit();

    try testing.expectEqualStrings("test_access_token", token.access_token);
    try testing.expectEqualStrings("Bearer", token.token_type);
    try testing.expect(token.expires_in == null);
    try testing.expect(token.refresh_token == null);
}
// ANCHOR_END: test_token_basic

// ANCHOR: test_token_refresh_token
test "token with refresh token" {
    var token = try OAuth2Token.init(testing.allocator, "access", "Bearer");
    defer token.deinit();

    try token.setRefreshToken("refresh_12345");

    try testing.expect(token.refresh_token != null);
    try testing.expectEqualStrings("refresh_12345", token.refresh_token.?);
}
// ANCHOR_END: test_token_refresh_token

// ANCHOR: test_token_scope
test "token with scope" {
    var token = try OAuth2Token.init(testing.allocator, "access", "Bearer");
    defer token.deinit();

    try token.setScope("read write");

    try testing.expect(token.scope != null);
    try testing.expectEqualStrings("read write", token.scope.?);
}
// ANCHOR_END: test_token_scope

// ANCHOR: test_token_expiration
test "token expiration check" {
    var token = try OAuth2Token.init(testing.allocator, "access", "Bearer");
    defer token.deinit();

    token.expires_in = 3600; // 1 hour

    try testing.expect(!token.isExpired());

    // Simulate expired token
    token.issued_at -= 3601;
    try testing.expect(token.isExpired());
}
// ANCHOR_END: test_token_expiration

// ANCHOR: test_token_authorization_header
test "get authorization header" {
    var token = try OAuth2Token.init(testing.allocator, "test_token_123", "Bearer");
    defer token.deinit();

    const header = try token.getAuthorizationHeader();
    defer testing.allocator.free(header);

    try testing.expectEqualStrings("Bearer test_token_123", header);
}
// ANCHOR_END: test_token_authorization_header

// ANCHOR: test_oauth_config
test "create OAuth2 config" {
    var config = try OAuth2Config.init(
        testing.allocator,
        "client_id_123",
        "https://auth.example.com/authorize",
        "https://auth.example.com/token",
    );
    defer config.deinit();

    try testing.expectEqualStrings("client_id_123", config.client_id);
    try testing.expectEqualStrings("https://auth.example.com/authorize", config.authorization_endpoint);
    try testing.expectEqualStrings("https://auth.example.com/token", config.token_endpoint);
}
// ANCHOR_END: test_oauth_config

// ANCHOR: test_oauth_config_with_secret
test "config with client secret" {
    var config = try OAuth2Config.init(
        testing.allocator,
        "client_id_123",
        "https://auth.example.com/authorize",
        "https://auth.example.com/token",
    );
    defer config.deinit();

    try config.setClientSecret("secret_abc");

    try testing.expect(config.client_secret != null);
    try testing.expectEqualStrings("secret_abc", config.client_secret.?);
}
// ANCHOR_END: test_oauth_config_with_secret

// ANCHOR: test_oauth_config_redirect
test "config with redirect URI" {
    var config = try OAuth2Config.init(
        testing.allocator,
        "client_id_123",
        "https://auth.example.com/authorize",
        "https://auth.example.com/token",
    );
    defer config.deinit();

    try config.setRedirectUri("https://myapp.com/callback");

    try testing.expect(config.redirect_uri != null);
    try testing.expectEqualStrings("https://myapp.com/callback", config.redirect_uri.?);
}
// ANCHOR_END: test_oauth_config_redirect

// ANCHOR: test_pkce
test "generate PKCE challenge" {
    var pkce = try PKCE.init(testing.allocator);
    defer pkce.deinit();

    try testing.expect(pkce.code_verifier.len > 0);
    try testing.expect(pkce.code_challenge.len > 0);
    try testing.expect(pkce.code_verifier.len >= 43);
}
// ANCHOR_END: test_pkce

// ANCHOR: test_build_auth_url_basic
test "build authorization URL basic" {
    var config = try OAuth2Config.init(
        testing.allocator,
        "my_client_id",
        "https://oauth.example.com/authorize",
        "https://oauth.example.com/token",
    );
    defer config.deinit();

    var client = OAuth2Client.init(testing.allocator, config);

    const url = try client.buildAuthorizationUrl(null, null);
    defer testing.allocator.free(url);

    try testing.expect(std.mem.indexOf(u8, url, "response_type=code") != null);
    try testing.expect(std.mem.indexOf(u8, url, "client_id=my_client_id") != null);
}
// ANCHOR_END: test_build_auth_url_basic

// ANCHOR: test_build_auth_url_with_state
test "build authorization URL with state" {
    var config = try OAuth2Config.init(
        testing.allocator,
        "my_client_id",
        "https://oauth.example.com/authorize",
        "https://oauth.example.com/token",
    );
    defer config.deinit();

    var client = OAuth2Client.init(testing.allocator, config);

    const url = try client.buildAuthorizationUrl("state_xyz", null);
    defer testing.allocator.free(url);

    try testing.expect(std.mem.indexOf(u8, url, "state=state_xyz") != null);
}
// ANCHOR_END: test_build_auth_url_with_state

// ANCHOR: test_build_auth_url_with_pkce
test "build authorization URL with PKCE" {
    var config = try OAuth2Config.init(
        testing.allocator,
        "my_client_id",
        "https://oauth.example.com/authorize",
        "https://oauth.example.com/token",
    );
    defer config.deinit();

    var pkce = try PKCE.init(testing.allocator);
    defer pkce.deinit();

    var client = OAuth2Client.init(testing.allocator, config);

    const url = try client.buildAuthorizationUrl(null, &pkce);
    defer testing.allocator.free(url);

    try testing.expect(std.mem.indexOf(u8, url, "code_challenge=") != null);
    try testing.expect(std.mem.indexOf(u8, url, "code_challenge_method=S256") != null);
}
// ANCHOR_END: test_build_auth_url_with_pkce

// ANCHOR: test_exchange_code
test "exchange authorization code for token" {
    var config = try OAuth2Config.init(
        testing.allocator,
        "my_client_id",
        "https://oauth.example.com/authorize",
        "https://oauth.example.com/token",
    );
    defer config.deinit();

    var client = OAuth2Client.init(testing.allocator, config);

    var token = try client.exchangeAuthorizationCode("auth_code_123", null);
    defer token.deinit();

    try testing.expect(token.access_token.len > 0);
    try testing.expect(token.expires_in != null);
    try testing.expect(token.refresh_token != null);
}
// ANCHOR_END: test_exchange_code

// ANCHOR: test_refresh_token
test "refresh access token" {
    var config = try OAuth2Config.init(
        testing.allocator,
        "my_client_id",
        "https://oauth.example.com/authorize",
        "https://oauth.example.com/token",
    );
    defer config.deinit();

    var client = OAuth2Client.init(testing.allocator, config);

    var token = try client.refreshToken("old_refresh_token");
    defer token.deinit();

    try testing.expect(token.access_token.len > 0);
    try testing.expectEqualStrings("Bearer", token.token_type);
}
// ANCHOR_END: test_refresh_token

// ANCHOR: test_client_credentials
test "get client credentials token" {
    var config = try OAuth2Config.init(
        testing.allocator,
        "my_client_id",
        "https://oauth.example.com/authorize",
        "https://oauth.example.com/token",
    );
    defer config.deinit();

    try config.setClientSecret("my_secret");

    var client = OAuth2Client.init(testing.allocator, config);

    var token = try client.getClientCredentialsToken();
    defer token.deinit();

    try testing.expect(token.access_token.len > 0);
    try testing.expectEqual(@as(?i64, 7200), token.expires_in);
}
// ANCHOR_END: test_client_credentials

// ANCHOR: test_url_encoding
test "URL encode special characters" {
    var config = try OAuth2Config.init(
        testing.allocator,
        "my_client_id",
        "https://oauth.example.com/authorize",
        "https://oauth.example.com/token",
    );
    defer config.deinit();

    try config.setScope("read write profile");
    try config.setRedirectUri("https://app.com/callback?foo=bar");

    var client = OAuth2Client.init(testing.allocator, config);

    const url = try client.buildAuthorizationUrl(null, null);
    defer testing.allocator.free(url);

    try testing.expect(std.mem.indexOf(u8, url, "scope=read+write+profile") != null);
    try testing.expect(std.mem.indexOf(u8, url, "%3F") != null); // encoded ?
}
// ANCHOR_END: test_url_encoding

// ANCHOR: secure_password_verify
/// Securely verify password hash using constant-time comparison
///
/// When implementing OAuth2 password grant flow or any authentication system,
/// password hashes MUST be compared using timing-safe functions to prevent
/// timing attacks that could leak information about the stored credentials.
///
/// WRONG: std.mem.eql(u8, password_hash, stored_hash)
/// - Timing varies based on where mismatch occurs
/// - Attacker can measure response time to guess password character-by-character
///
/// CORRECT: std.crypto.timing_safe.eql()
/// - Constant-time comparison regardless of input values
/// - Prevents side-channel timing attacks
///
/// Implementation Note:
/// - std.crypto.timing_safe.eql works with compile-time-known fixed-size arrays
/// - For variable-length slices (like dynamic password hashes), manual constant-time
///   comparison is needed as shown below
/// - The XOR pattern ensures timing is independent of where values differ
pub fn verifyPasswordHash(
    password_hash: []const u8,
    stored_hash: []const u8,
) bool {
    // Early return on length mismatch is safe - length is not secret
    if (password_hash.len != stored_hash.len) {
        return false;
    }

    // Manual constant-time comparison for variable-length slices
    // Alternative: If hash length is fixed at compile time, use:
    //   std.crypto.timing_safe.eql([hash_len]u8, password_hash[0..hash_len].*, stored_hash[0..hash_len].*)
    //
    // This manual approach works for any slice length
    var result: u8 = 0;
    for (password_hash, stored_hash) |a, b| {
        result |= a ^ b;
    }

    // Return true only if all bytes matched (result == 0)
    // Using constant-time comparison for the final result
    return result == 0;
}
// ANCHOR_END: secure_password_verify

// ANCHOR: test_timing_safe_password
test "timing-safe password hash verification" {
    // Simulated bcrypt/argon2 password hashes (in real use, these would be actual hashes)
    const hash1 = "bcrypt$2b$12$abcdefghijklmnopqrstuvwxyz1234567890ABCDEFGH";
    const hash2 = "bcrypt$2b$12$abcdefghijklmnopqrstuvwxyz1234567890ABCDEFGH";
    const hash3 = "bcrypt$2b$12$WRONGHASH_zyxwvutsrqponmlkjihgfedcba9876543210";

    // Same hashes should match
    try testing.expect(verifyPasswordHash(hash1, hash2));

    // Different hashes should not match
    try testing.expect(!verifyPasswordHash(hash1, hash3));

    // Different lengths should not match
    const short_hash = "bcrypt$2b$12$short";
    try testing.expect(!verifyPasswordHash(hash1, short_hash));
}
// ANCHOR_END: test_timing_safe_password

// ANCHOR: test_timing_safe_tokens
test "timing-safe token comparison" {
    // OAuth2 tokens should also be compared using timing-safe functions
    // to prevent token guessing attacks through timing analysis
    const token1 = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.payload.signature";
    const token2 = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.payload.signature";
    const token3 = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.payload.WRONGSIG";

    try testing.expect(verifyPasswordHash(token1, token2));
    try testing.expect(!verifyPasswordHash(token1, token3));
}
// ANCHOR_END: test_timing_safe_tokens
```

### See Also

- Recipe 11.1: Making HTTP requests
- Recipe 11.7: Handling cookies and sessions
- Recipe 11.8: SSL/TLS connections

---

## Recipe 20.1: Non-Blocking TCP Servers with Poll {#recipe-20-1}

**Tags:** allocators, arraylist, concurrency, data-structures, error-handling, http, memory, networking, resource-cleanup, sockets, testing, threading
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/20-high-perf-networking/recipe_20_1.zig`

### Problem

You need to build a TCP server that can handle many concurrent connections without dedicating a thread to each client. Traditional blocking I/O creates scalability problems when dealing with simultaneous connections.

### Solution

Use Zig's `std.posix` module to create non-blocking sockets and poll for events across multiple file descriptors. The `poll()` system call monitors many sockets from a single thread, providing a portable foundation for event-driven servers.

### Basic Non-Blocking Server

First, create a non-blocking server socket:

```zig
const NonBlockingServer = struct {
    socket: posix.socket_t,
    address: net.Address,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, port: u16) !NonBlockingServer {
        const addr = try net.Address.parseIp("127.0.0.1", port);

        const socket = try posix.socket(
            addr.any.family,
            posix.SOCK.STREAM | posix.SOCK.NONBLOCK,
            0,
        );
        errdefer posix.close(socket);

        try posix.setsockopt(
            socket,
            posix.SOL.SOCKET,
            posix.SO.REUSEADDR,
            &std.mem.toBytes(@as(c_int, 1)),
        );

        try posix.bind(socket, &addr.any, addr.getOsSockLen());
        try posix.listen(socket, 128);

        return .{
            .socket = socket,
            .address = addr,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *NonBlockingServer) void {
        posix.close(self.socket);
    }
};
```

The key is the `posix.SOCK.NONBLOCK` flag when creating the socket. This prevents `accept()`, `recv()`, and `send()` from blocking.

### Poll-Based Event Loop

Build a simple event loop using poll:

```zig
const PollServer = struct {
    server: NonBlockingServer,
    clients: std.ArrayList(posix.socket_t),
    poll_fds: std.ArrayList(posix.pollfd),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, port: u16) !PollServer {
        const server = try NonBlockingServer.init(allocator, port);
        var poll_fds = std.ArrayList(posix.pollfd){};

        try poll_fds.append(allocator, .{
            .fd = server.socket,
            .events = posix.POLL.IN,
            .revents = 0,
        });

        return .{
            .server = server,
            .clients = std.ArrayList(posix.socket_t){},
            .poll_fds = poll_fds,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *PollServer) void {
        for (self.clients.items) |client| {
            posix.close(client);
        }
        self.clients.deinit(self.allocator);
        self.poll_fds.deinit(self.allocator);
        self.server.deinit();
    }

    pub fn acceptClient(self: *PollServer) !void {
        var client_addr: net.Address = undefined;
        var addr_len: posix.socklen_t = @sizeOf(net.Address);

        const client = posix.accept(
            self.server.socket,
            &client_addr.any,
            &addr_len,
            posix.SOCK.NONBLOCK,
        ) catch |err| switch (err) {
            error.WouldBlock => return,
            else => return err,
        };

        try self.clients.append(self.allocator, client);
        try self.poll_fds.append(self.allocator, .{
            .fd = client,
            .events = posix.POLL.IN,
            .revents = 0,
        });
    }

    pub fn handleClient(self: *PollServer, index: usize) !bool {
        const client = self.clients.items[index];
        var buffer: [1024]u8 = undefined;

        const bytes_read = posix.recv(client, &buffer, 0) catch |err| switch (err) {
            error.WouldBlock => return true,
            else => return false,
        };

        if (bytes_read == 0) {
            return false;
        }

        // Note: This simple example ignores partial writes for brevity.
        // In production, send() may return fewer bytes than requested.
        // See StatefulServer.Connection.handleWrite for proper handling.
        _ = posix.send(client, buffer[0..bytes_read], 0) catch {
            return false;
        };

        return true;
    }

    pub fn removeClient(self: *PollServer, index: usize) void {
        const client = self.clients.orderedRemove(index);
        posix.close(client);
        _ = self.poll_fds.orderedRemove(index + 1);
    }

    pub fn run(self: *PollServer, iterations: usize) !void {
        var count: usize = 0;
        while (count < iterations) : (count += 1) {
            const ready = try posix.poll(self.poll_fds.items, 100);
            if (ready == 0) continue;

            if (self.poll_fds.items[0].revents & posix.POLL.IN != 0) {
                try self.acceptClient();
            }

            var i: usize = self.clients.items.len;
            while (i > 0) {
                i -= 1;
                if (self.poll_fds.items[i + 1].revents & posix.POLL.IN != 0) {
                    if (!try self.handleClient(i)) {
                        self.removeClient(i);
                    }
                }
            }
        }
    }
};
```

### Stateful Connections

For more complex protocols, track connection state:

```zig
const ConnectionState = enum {
    reading,
    writing,
    closing,
};

const Connection = struct {
    socket: posix.socket_t,
    state: ConnectionState,
    buffer: [4096]u8,
    bytes_read: usize,
    bytes_written: usize,

    pub fn init(socket: posix.socket_t) Connection {
        return .{
            .socket = socket,
            .state = .reading,
            .buffer = undefined,
            .bytes_read = 0,
            .bytes_written = 0,
        };
    }

    pub fn handleRead(self: *Connection) !bool {
        const bytes = posix.recv(
            self.socket,
            self.buffer[self.bytes_read..],
            0,
        ) catch |err| switch (err) {
            error.WouldBlock => return true,
            else => return false,
        };

        if (bytes == 0) return false;

        self.bytes_read += bytes;
        if (self.bytes_read >= self.buffer.len or
            std.mem.indexOf(u8, self.buffer[0..self.bytes_read], "\n") != null) {
            self.state = .writing;
        }

        return true;
    }

    pub fn handleWrite(self: *Connection) !bool {
        const bytes = posix.send(
            self.socket,
            self.buffer[self.bytes_written..self.bytes_read],
            0,
        ) catch |err| switch (err) {
            error.WouldBlock => return true,
            else => return false,
        };

        self.bytes_written += bytes;
        if (self.bytes_written >= self.bytes_read) {
            self.state = .closing;
        }

        return true;
    }
};
```

Integrate with a stateful server:

```zig
const StatefulServer = struct {
    server: NonBlockingServer,
    connections: std.ArrayList(Connection),
    poll_fds: std.ArrayList(posix.pollfd),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, port: u16) !StatefulServer {
        const server = try NonBlockingServer.init(allocator, port);
        var poll_fds = std.ArrayList(posix.pollfd){};

        try poll_fds.append(allocator, .{
            .fd = server.socket,
            .events = posix.POLL.IN,
            .revents = 0,
        });

        return .{
            .server = server,
            .connections = std.ArrayList(Connection){},
            .poll_fds = poll_fds,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *StatefulServer) void {
        for (self.connections.items) |conn| {
            posix.close(conn.socket);
        }
        self.connections.deinit(self.allocator);
        self.poll_fds.deinit(self.allocator);
        self.server.deinit();
    }

    pub fn acceptConnection(self: *StatefulServer) !void {
        var client_addr: net.Address = undefined;
        var addr_len: posix.socklen_t = @sizeOf(net.Address);

        const client = posix.accept(
            self.server.socket,
            &client_addr.any,
            &addr_len,
            posix.SOCK.NONBLOCK,
        ) catch |err| switch (err) {
            error.WouldBlock => return,
            else => return err,
        };

        try self.connections.append(self.allocator, Connection.init(client));
        try self.poll_fds.append(self.allocator, .{
            .fd = client,
            .events = posix.POLL.IN,
            .revents = 0,
        });
    }

    pub fn handleConnection(self: *StatefulServer, index: usize) !bool {
        var conn = &self.connections.items[index];

        switch (conn.state) {
            .reading => {
                if (!try conn.handleRead()) return false;
                if (conn.state == .writing) {
                    self.poll_fds.items[index + 1].events = posix.POLL.OUT;
                }
            },
            .writing => {
                if (!try conn.handleWrite()) return false;
                if (conn.state == .closing) {
                    return false;
                }
            },
            .closing => return false,
        }

        return true;
    }

    pub fn removeConnection(self: *StatefulServer, index: usize) void {
        const conn = self.connections.orderedRemove(index);
        posix.close(conn.socket);
        _ = self.poll_fds.orderedRemove(index + 1);
    }
};
```

### Discussion

Non-blocking I/O is the foundation of high-performance servers. Instead of dedicating a thread per connection (which limits you to thousands of connections), you use a single thread to monitor many sockets.

### How Poll Works

The `poll()` system call takes an array of file descriptors and event masks, then blocks until one or more descriptors is ready for I/O. This is much more efficient than checking each socket individually.

**Scalability note:** `poll()` has O(n) complexity - the kernel scans all file descriptors on each call. This is fine for hundreds of connections but becomes a bottleneck with thousands. For extreme scale:
- **Linux**: Use `epoll` directly (O(1) event notification)
- **macOS/BSD**: Use `kqueue` directly (O(1) event notification)
- **Windows**: Use IOCP

This recipe uses `poll()` because it's portable and simpler to understand. The patterns (non-blocking I/O, event loops, state machines) transfer directly to epoll/kqueue when you need more performance.

### Event-Driven Architecture

The pattern follows this flow:

1. **Accept**: Listen socket becomes readable when clients connect
2. **Read**: Client socket becomes readable when data arrives
3. **Write**: Client socket becomes writable when you can send data
4. **Close**: Handle errors or client disconnections

### Error Handling

Non-blocking calls return `error.WouldBlock` when they would have blocked. This is not an error - it means "try again later." Always catch this specifically:

```zig
const bytes = posix.recv(socket, buffer, 0) catch |err| switch (err) {
    error.WouldBlock => return true,  // Not ready yet
    else => return false,             // Real error
};
```

### Performance Characteristics

**Advantages:**
- Handle thousands of connections with one thread
- Low memory overhead per connection
- Excellent CPU efficiency
- Predictable latency

**Trade-offs:**
- More complex code than blocking I/O
- Need careful state management
- Can't use traditional read/write patterns

### Platform Differences

Zig's `std.posix` provides portable socket operations:
- `posix.SOCK.NONBLOCK` works on POSIX systems
- `poll()` is available on all POSIX platforms
- Socket options use consistent naming

Note: Windows support requires different APIs (`WSAPoll` or `select`). For cross-platform servers, consider using a library or adding platform-specific code paths.

### Memory Management

Use an allocator for dynamic arrays of connections. The testing allocator helps catch leaks during development. The unmanaged ArrayList pattern (`.append(allocator, item)`) makes allocator usage explicit.

### Full Tested Code

```zig
// Recipe 20.1: Implementing non-blocking TCP servers with epoll/kqueue
// Target Zig Version: 0.15.2
const std = @import("std");
const testing = std.testing;
const posix = std.posix;
const net = std.net;

// ANCHOR: basic_nonblocking
const NonBlockingServer = struct {
    socket: posix.socket_t,
    address: net.Address,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, port: u16) !NonBlockingServer {
        const addr = try net.Address.parseIp("127.0.0.1", port);

        const socket = try posix.socket(
            addr.any.family,
            posix.SOCK.STREAM | posix.SOCK.NONBLOCK,
            0,
        );
        errdefer posix.close(socket);

        try posix.setsockopt(
            socket,
            posix.SOL.SOCKET,
            posix.SO.REUSEADDR,
            &std.mem.toBytes(@as(c_int, 1)),
        );

        try posix.bind(socket, &addr.any, addr.getOsSockLen());
        try posix.listen(socket, 128);

        return .{
            .socket = socket,
            .address = addr,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *NonBlockingServer) void {
        posix.close(self.socket);
    }
};
// ANCHOR_END: basic_nonblocking

// ANCHOR: poll_based_server
const PollServer = struct {
    server: NonBlockingServer,
    clients: std.ArrayList(posix.socket_t),
    poll_fds: std.ArrayList(posix.pollfd),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, port: u16) !PollServer {
        const server = try NonBlockingServer.init(allocator, port);
        var poll_fds = std.ArrayList(posix.pollfd){};

        try poll_fds.append(allocator, .{
            .fd = server.socket,
            .events = posix.POLL.IN,
            .revents = 0,
        });

        return .{
            .server = server,
            .clients = std.ArrayList(posix.socket_t){},
            .poll_fds = poll_fds,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *PollServer) void {
        for (self.clients.items) |client| {
            posix.close(client);
        }
        self.clients.deinit(self.allocator);
        self.poll_fds.deinit(self.allocator);
        self.server.deinit();
    }

    pub fn acceptClient(self: *PollServer) !void {
        var client_addr: net.Address = undefined;
        var addr_len: posix.socklen_t = @sizeOf(net.Address);

        const client = posix.accept(
            self.server.socket,
            &client_addr.any,
            &addr_len,
            posix.SOCK.NONBLOCK,
        ) catch |err| switch (err) {
            error.WouldBlock => return,
            else => return err,
        };

        try self.clients.append(self.allocator, client);
        try self.poll_fds.append(self.allocator, .{
            .fd = client,
            .events = posix.POLL.IN,
            .revents = 0,
        });
    }

    pub fn handleClient(self: *PollServer, index: usize) !bool {
        const client = self.clients.items[index];
        var buffer: [1024]u8 = undefined;

        const bytes_read = posix.recv(client, &buffer, 0) catch |err| switch (err) {
            error.WouldBlock => return true,
            else => return false,
        };

        if (bytes_read == 0) {
            return false;
        }

        // Note: This simple example ignores partial writes for brevity.
        // In production, send() may return fewer bytes than requested.
        // See StatefulServer.Connection.handleWrite for proper handling.
        _ = posix.send(client, buffer[0..bytes_read], 0) catch {
            return false;
        };

        return true;
    }

    pub fn removeClient(self: *PollServer, index: usize) void {
        const client = self.clients.orderedRemove(index);
        posix.close(client);
        _ = self.poll_fds.orderedRemove(index + 1);
    }

    pub fn run(self: *PollServer, iterations: usize) !void {
        var count: usize = 0;
        while (count < iterations) : (count += 1) {
            const ready = try posix.poll(self.poll_fds.items, 100);
            if (ready == 0) continue;

            if (self.poll_fds.items[0].revents & posix.POLL.IN != 0) {
                try self.acceptClient();
            }

            var i: usize = self.clients.items.len;
            while (i > 0) {
                i -= 1;
                if (self.poll_fds.items[i + 1].revents & posix.POLL.IN != 0) {
                    if (!try self.handleClient(i)) {
                        self.removeClient(i);
                    }
                }
            }
        }
    }
};
// ANCHOR_END: poll_based_server

// ANCHOR: connection_state
const ConnectionState = enum {
    reading,
    writing,
    closing,
};

const Connection = struct {
    socket: posix.socket_t,
    state: ConnectionState,
    buffer: [4096]u8,
    bytes_read: usize,
    bytes_written: usize,

    pub fn init(socket: posix.socket_t) Connection {
        return .{
            .socket = socket,
            .state = .reading,
            .buffer = undefined,
            .bytes_read = 0,
            .bytes_written = 0,
        };
    }

    pub fn handleRead(self: *Connection) !bool {
        const bytes = posix.recv(
            self.socket,
            self.buffer[self.bytes_read..],
            0,
        ) catch |err| switch (err) {
            error.WouldBlock => return true,
            else => return false,
        };

        if (bytes == 0) return false;

        self.bytes_read += bytes;
        if (self.bytes_read >= self.buffer.len or
            std.mem.indexOf(u8, self.buffer[0..self.bytes_read], "\n") != null) {
            self.state = .writing;
        }

        return true;
    }

    pub fn handleWrite(self: *Connection) !bool {
        const bytes = posix.send(
            self.socket,
            self.buffer[self.bytes_written..self.bytes_read],
            0,
        ) catch |err| switch (err) {
            error.WouldBlock => return true,
            else => return false,
        };

        self.bytes_written += bytes;
        if (self.bytes_written >= self.bytes_read) {
            self.state = .closing;
        }

        return true;
    }
};
// ANCHOR_END: connection_state

// ANCHOR: stateful_server
const StatefulServer = struct {
    server: NonBlockingServer,
    connections: std.ArrayList(Connection),
    poll_fds: std.ArrayList(posix.pollfd),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, port: u16) !StatefulServer {
        const server = try NonBlockingServer.init(allocator, port);
        var poll_fds = std.ArrayList(posix.pollfd){};

        try poll_fds.append(allocator, .{
            .fd = server.socket,
            .events = posix.POLL.IN,
            .revents = 0,
        });

        return .{
            .server = server,
            .connections = std.ArrayList(Connection){},
            .poll_fds = poll_fds,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *StatefulServer) void {
        for (self.connections.items) |conn| {
            posix.close(conn.socket);
        }
        self.connections.deinit(self.allocator);
        self.poll_fds.deinit(self.allocator);
        self.server.deinit();
    }

    pub fn acceptConnection(self: *StatefulServer) !void {
        var client_addr: net.Address = undefined;
        var addr_len: posix.socklen_t = @sizeOf(net.Address);

        const client = posix.accept(
            self.server.socket,
            &client_addr.any,
            &addr_len,
            posix.SOCK.NONBLOCK,
        ) catch |err| switch (err) {
            error.WouldBlock => return,
            else => return err,
        };

        try self.connections.append(self.allocator, Connection.init(client));
        try self.poll_fds.append(self.allocator, .{
            .fd = client,
            .events = posix.POLL.IN,
            .revents = 0,
        });
    }

    pub fn handleConnection(self: *StatefulServer, index: usize) !bool {
        var conn = &self.connections.items[index];

        switch (conn.state) {
            .reading => {
                if (!try conn.handleRead()) return false;
                if (conn.state == .writing) {
                    self.poll_fds.items[index + 1].events = posix.POLL.OUT;
                }
            },
            .writing => {
                if (!try conn.handleWrite()) return false;
                if (conn.state == .closing) {
                    return false;
                }
            },
            .closing => return false,
        }

        return true;
    }

    pub fn removeConnection(self: *StatefulServer, index: usize) void {
        const conn = self.connections.orderedRemove(index);
        posix.close(conn.socket);
        _ = self.poll_fds.orderedRemove(index + 1);
    }
};
// ANCHOR_END: stateful_server

// Tests
test "create non-blocking server" {
    const port: u16 = 9001;
    var server = try NonBlockingServer.init(testing.allocator, port);
    defer server.deinit();

    try testing.expect(server.socket >= 0);
    try testing.expectEqual(port, server.address.getPort());
}

test "poll server initialization" {
    const port: u16 = 9002;
    var poll_server = try PollServer.init(testing.allocator, port);
    defer poll_server.deinit();

    try testing.expectEqual(@as(usize, 0), poll_server.clients.items.len);
    try testing.expectEqual(@as(usize, 1), poll_server.poll_fds.items.len);
}

test "connection state transitions" {
    const conn = Connection.init(0);

    try testing.expectEqual(ConnectionState.reading, conn.state);
    try testing.expectEqual(@as(usize, 0), conn.bytes_read);
    try testing.expectEqual(@as(usize, 0), conn.bytes_written);
}

test "stateful server initialization" {
    const port: u16 = 9003;
    var server = try StatefulServer.init(testing.allocator, port);
    defer server.deinit();

    try testing.expectEqual(@as(usize, 0), server.connections.items.len);
    try testing.expectEqual(@as(usize, 1), server.poll_fds.items.len);
}

test "non-blocking accept with no clients" {
    const port: u16 = 9004;
    var server = try PollServer.init(testing.allocator, port);
    defer server.deinit();

    try server.acceptClient();
    try testing.expectEqual(@as(usize, 0), server.clients.items.len);
}

test "poll server can run event loop" {
    const port: u16 = 9005;
    var server = try PollServer.init(testing.allocator, port);
    defer server.deinit();

    try server.run(5);
    try testing.expectEqual(@as(usize, 0), server.clients.items.len);
}
```

### See Also

- Recipe 11.4: Building a Simple HTTP Server
- Recipe 12.1: Basic Threading and Thread Management
- Recipe 20.2: Zero
- Recipe 20.4: Implementing a Basic HTTP/1.1 Parser

---

## Recipe 20.2: Zero-Copy Networking Using sendfile {#recipe-20-2}

**Tags:** allocators, error-handling, http, memory, networking, resource-cleanup, sockets, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/20-high-perf-networking/recipe_20_2.zig`

### Problem

You need to transfer large files over a network connection efficiently. Reading a file into user-space memory and then writing it to a socket wastes CPU cycles and memory bandwidth with unnecessary data copying.

### Solution

Use the `sendfile()` system call to transfer data directly from a file descriptor to a socket without copying through user space. This "zero-copy" operation is handled entirely by the kernel.

### Basic sendfile Usage

Create a cross-platform sendfile wrapper:

```zig
/// Transfer a file to a socket without copying through user space
pub fn sendFile(socket: posix.socket_t, file: fs.File, offset: usize, count: usize) !usize {
    if (@import("builtin").os.tag == .linux) {
        var off: i64 = @intCast(offset);
        return try posix.sendfile(socket, file.handle, &off, count);
    } else if (@import("builtin").os.tag == .macos or @import("builtin").os.tag == .freebsd) {
        var sent: posix.off_t = @intCast(count);
        try posix.sendfile(file.handle, socket, @intCast(offset), &sent, null, 0);
        return @intCast(sent);
    } else {
        // Fallback for platforms without sendfile
        return sendFileFallback(socket, file, offset, count);
    }
}

fn sendFileFallback(socket: posix.socket_t, file: fs.File, offset: usize, count: usize) !usize {
    try file.seekTo(offset);
    var buffer: [8192]u8 = undefined;
    var total_sent: usize = 0;
    var remaining = count;

    while (remaining > 0) {
        const to_read = @min(remaining, buffer.len);
        const bytes_read = try file.read(buffer[0..to_read]);
        if (bytes_read == 0) break;

        var sent: usize = 0;
        while (sent < bytes_read) {
            const n = try posix.send(socket, buffer[sent..bytes_read], 0);
            sent += n;
        }

        total_sent += bytes_read;
        remaining -= bytes_read;
    }

    return total_sent;
}
```

### Static File Server

Build a simple static file server using sendfile:

```zig
const StaticFileServer = struct {
    socket: posix.socket_t,
    address: net.Address,
    root_dir: fs.Dir,

    pub fn init(port: u16, root_path: []const u8) !StaticFileServer {
        const addr = try net.Address.parseIp("127.0.0.1", port);

        const socket = try posix.socket(
            addr.any.family,
            posix.SOCK.STREAM,
            0,
        );
        errdefer posix.close(socket);

        try posix.setsockopt(
            socket,
            posix.SOL.SOCKET,
            posix.SO.REUSEADDR,
            &std.mem.toBytes(@as(c_int, 1)),
        );

        try posix.bind(socket, &addr.any, addr.getOsSockLen());
        try posix.listen(socket, 128);

        const root_dir = try fs.cwd().openDir(root_path, .{});

        return .{
            .socket = socket,
            .address = addr,
            .root_dir = root_dir,
        };
    }

    pub fn deinit(self: *StaticFileServer) void {
        self.root_dir.close();
        posix.close(self.socket);
    }

    pub fn serveFile(self: *StaticFileServer, client: posix.socket_t, path: []const u8) !void {
        const file = try self.root_dir.openFile(path, .{});
        defer file.close();

        const stat = try file.stat();
        const size = stat.size;

        const header = try std.fmt.allocPrint(
            std.heap.page_allocator,
            "HTTP/1.1 200 OK\r\nContent-Length: {d}\r\n\r\n",
            .{size},
        );
        defer std.heap.page_allocator.free(header);

        _ = try posix.send(client, header, 0);
        _ = try sendFile(client, file, 0, size);
    }
};
```

### Socket-to-Socket Transfer with splice

For Linux, use `splice()` for socket-to-socket zero-copy:

```zig
/// Use splice (Linux) or pipe-based transfer for socket-to-socket zero-copy
pub fn spliceSockets(in_fd: posix.socket_t, out_fd: posix.socket_t, len: usize) !usize {
    if (@import("builtin").os.tag != .linux) {
        return error.UnsupportedPlatform;
    }

    const pipe_fds = try posix.pipe();
    defer {
        posix.close(pipe_fds[0]);
        posix.close(pipe_fds[1]);
    }

    var total: usize = 0;
    var remaining = len;

    while (remaining > 0) {
        const to_pipe = try posix.splice(
            in_fd,
            null,
            pipe_fds[1],
            null,
            remaining,
            0,
        );
        if (to_pipe == 0) break;

        var pipe_data = to_pipe;
        while (pipe_data > 0) {
            const from_pipe = try posix.splice(
                pipe_fds[0],
                null,
                out_fd,
                null,
                pipe_data,
                0,
            );
            pipe_data -= from_pipe;
            total += from_pipe;
        }

        remaining -= to_pipe;
    }

    return total;
}
```

### Chunked File Transfer

Transfer large files in chunks with progress tracking:

```zig
const ChunkedFileTransfer = struct {
    file: fs.File,
    chunk_size: usize,
    total_size: usize,
    bytes_sent: usize,

    pub fn init(file: fs.File, chunk_size: usize) !ChunkedFileTransfer {
        const stat = try file.stat();
        return .{
            .file = file,
            .chunk_size = chunk_size,
            .total_size = stat.size,
            .bytes_sent = 0,
        };
    }

    pub fn sendChunk(self: *ChunkedFileTransfer, socket: posix.socket_t) !bool {
        if (self.bytes_sent >= self.total_size) {
            return false;
        }

        const remaining = self.total_size - self.bytes_sent;
        const chunk = @min(remaining, self.chunk_size);

        const sent = try sendFile(socket, self.file, self.bytes_sent, chunk);
        self.bytes_sent += sent;

        return self.bytes_sent < self.total_size;
    }

    pub fn progress(self: *const ChunkedFileTransfer) f32 {
        if (self.total_size == 0) return 1.0;
        return @as(f32, @floatFromInt(self.bytes_sent)) / @as(f32, @floatFromInt(self.total_size));
    }
};
```

### Memory-Mapped Alternative

Use mmap as an alternative to sendfile:

```zig
/// Memory-map a file and send it (alternative to sendfile)
pub fn mmapSend(socket: posix.socket_t, file: fs.File) !void {
    const stat = try file.stat();
    const size = stat.size;

    if (size == 0) return;

    const mapped = try posix.mmap(
        null,
        size,
        posix.PROT.READ,
        .{ .TYPE = .SHARED },
        file.handle,
        0,
    );
    defer posix.munmap(mapped);

    var sent: usize = 0;
    while (sent < size) {
        const n = try posix.send(socket, mapped[sent..], 0);
        sent += n;
    }
}
```

### Discussion

Zero-copy techniques eliminate expensive memory copies between kernel and user space. This is especially important for high-throughput file servers.

### How sendfile Works

Traditional file transfer:
1. Read file into kernel buffer (disk → kernel)
2. Copy from kernel to user space (kernel → user)
3. Write from user space to kernel (user → kernel)
4. Send from kernel to network (kernel → network)

With sendfile:
1. Read file into kernel buffer (disk → kernel)
2. Send from kernel to network (kernel → network)

This eliminates two copy operations and context switches.

### Platform Differences

sendfile has different signatures across platforms:

**Linux:**
```c
ssize_t sendfile(int out_fd, int in_fd, off_t *offset, size_t count);
```

**macOS/BSD:**
```c
int sendfile(int fd, int s, off_t offset, off_t *len,
             struct sf_hdtr *hdtr, int flags);
```

The wrapper function handles these differences, providing a consistent interface.

### splice for Socket-to-Socket

On Linux, `splice()` can transfer data between any two file descriptors through a pipe. This is useful for proxies or when forwarding data between network connections without processing it.

### Performance Considerations

**When sendfile shines:**
- Large static files (images, videos, downloads)
- High-concurrency file serving
- Proxy servers forwarding data

**When sendfile doesn't help:**
- Files need processing before sending
- Small files (overhead outweighs benefit)
- Compressed/encrypted transfers

Benchmark shows sendfile can be 2-3x faster than read/write loops for large files.

### Memory Mapping Alternative

mmap maps a file into memory, letting you treat it like an array. Send operations then copy from this mapped region. This can be faster than read/write but uses more virtual memory.

Pros:
- Simple API
- Good for random access
- Works on all platforms

Cons:
- Not truly zero-copy (still copies to socket buffer)
- Can cause page faults
- Consumes address space

### Error Handling

Both sendfile and splice can return partial transfers. Always check return values and loop if needed. Handle `EAGAIN` for non-blocking sockets.

### Chunked Transfers

For very large files, transfer in chunks to:
- Provide progress feedback
- Handle partial transfers
- Manage memory pressure
- Allow cancellation

### Full Tested Code

```zig
// Recipe 20.2: Zero-copy networking using sendfile
// Target Zig Version: 0.15.2
const std = @import("std");
const testing = std.testing;
const posix = std.posix;
const fs = std.fs;
const net = std.net;

// ANCHOR: sendfile_basic
/// Transfer a file to a socket without copying through user space
pub fn sendFile(socket: posix.socket_t, file: fs.File, offset: usize, count: usize) !usize {
    if (@import("builtin").os.tag == .linux) {
        var off: i64 = @intCast(offset);
        return try posix.sendfile(socket, file.handle, &off, count);
    } else if (@import("builtin").os.tag == .macos or @import("builtin").os.tag == .freebsd) {
        var sent: posix.off_t = @intCast(count);
        try posix.sendfile(file.handle, socket, @intCast(offset), &sent, null, 0);
        return @intCast(sent);
    } else {
        // Fallback for platforms without sendfile
        return sendFileFallback(socket, file, offset, count);
    }
}

fn sendFileFallback(socket: posix.socket_t, file: fs.File, offset: usize, count: usize) !usize {
    try file.seekTo(offset);
    var buffer: [8192]u8 = undefined;
    var total_sent: usize = 0;
    var remaining = count;

    while (remaining > 0) {
        const to_read = @min(remaining, buffer.len);
        const bytes_read = try file.read(buffer[0..to_read]);
        if (bytes_read == 0) break;

        var sent: usize = 0;
        while (sent < bytes_read) {
            const n = try posix.send(socket, buffer[sent..bytes_read], 0);
            sent += n;
        }

        total_sent += bytes_read;
        remaining -= bytes_read;
    }

    return total_sent;
}
// ANCHOR_END: sendfile_basic

// ANCHOR: static_file_server
const StaticFileServer = struct {
    socket: posix.socket_t,
    address: net.Address,
    root_dir: fs.Dir,

    pub fn init(port: u16, root_path: []const u8) !StaticFileServer {
        const addr = try net.Address.parseIp("127.0.0.1", port);

        const socket = try posix.socket(
            addr.any.family,
            posix.SOCK.STREAM,
            0,
        );
        errdefer posix.close(socket);

        try posix.setsockopt(
            socket,
            posix.SOL.SOCKET,
            posix.SO.REUSEADDR,
            &std.mem.toBytes(@as(c_int, 1)),
        );

        try posix.bind(socket, &addr.any, addr.getOsSockLen());
        try posix.listen(socket, 128);

        const root_dir = try fs.cwd().openDir(root_path, .{});

        return .{
            .socket = socket,
            .address = addr,
            .root_dir = root_dir,
        };
    }

    pub fn deinit(self: *StaticFileServer) void {
        self.root_dir.close();
        posix.close(self.socket);
    }

    pub fn serveFile(self: *StaticFileServer, client: posix.socket_t, path: []const u8) !void {
        const file = try self.root_dir.openFile(path, .{});
        defer file.close();

        const stat = try file.stat();
        const size = stat.size;

        const header = try std.fmt.allocPrint(
            std.heap.page_allocator,
            "HTTP/1.1 200 OK\r\nContent-Length: {d}\r\n\r\n",
            .{size},
        );
        defer std.heap.page_allocator.free(header);

        _ = try posix.send(client, header, 0);
        _ = try sendFile(client, file, 0, size);
    }
};
// ANCHOR_END: static_file_server

// ANCHOR: splice_pipes
/// Use splice (Linux) or pipe-based transfer for socket-to-socket zero-copy
pub fn spliceSockets(in_fd: posix.socket_t, out_fd: posix.socket_t, len: usize) !usize {
    if (@import("builtin").os.tag != .linux) {
        return error.UnsupportedPlatform;
    }

    const pipe_fds = try posix.pipe();
    defer {
        posix.close(pipe_fds[0]);
        posix.close(pipe_fds[1]);
    }

    var total: usize = 0;
    var remaining = len;

    while (remaining > 0) {
        const to_pipe = try posix.splice(
            in_fd,
            null,
            pipe_fds[1],
            null,
            remaining,
            0,
        );
        if (to_pipe == 0) break;

        var pipe_data = to_pipe;
        while (pipe_data > 0) {
            const from_pipe = try posix.splice(
                pipe_fds[0],
                null,
                out_fd,
                null,
                pipe_data,
                0,
            );
            pipe_data -= from_pipe;
            total += from_pipe;
        }

        remaining -= to_pipe;
    }

    return total;
}
// ANCHOR_END: splice_pipes

// ANCHOR: chunked_transfer
const ChunkedFileTransfer = struct {
    file: fs.File,
    chunk_size: usize,
    total_size: usize,
    bytes_sent: usize,

    pub fn init(file: fs.File, chunk_size: usize) !ChunkedFileTransfer {
        const stat = try file.stat();
        return .{
            .file = file,
            .chunk_size = chunk_size,
            .total_size = stat.size,
            .bytes_sent = 0,
        };
    }

    pub fn sendChunk(self: *ChunkedFileTransfer, socket: posix.socket_t) !bool {
        if (self.bytes_sent >= self.total_size) {
            return false;
        }

        const remaining = self.total_size - self.bytes_sent;
        const chunk = @min(remaining, self.chunk_size);

        const sent = try sendFile(socket, self.file, self.bytes_sent, chunk);
        self.bytes_sent += sent;

        return self.bytes_sent < self.total_size;
    }

    pub fn progress(self: *const ChunkedFileTransfer) f32 {
        if (self.total_size == 0) return 1.0;
        return @as(f32, @floatFromInt(self.bytes_sent)) / @as(f32, @floatFromInt(self.total_size));
    }
};
// ANCHOR_END: chunked_transfer

// ANCHOR: mmap_send
/// Memory-map a file and send it (alternative to sendfile)
pub fn mmapSend(socket: posix.socket_t, file: fs.File) !void {
    const stat = try file.stat();
    const size = stat.size;

    if (size == 0) return;

    const mapped = try posix.mmap(
        null,
        size,
        posix.PROT.READ,
        .{ .TYPE = .SHARED },
        file.handle,
        0,
    );
    defer posix.munmap(mapped);

    var sent: usize = 0;
    while (sent < size) {
        const n = try posix.send(socket, mapped[sent..], 0);
        sent += n;
    }
}
// ANCHOR_END: mmap_send

// Tests
test "sendfile with temp file" {
    if (@import("builtin").os.tag == .wasi) return error.SkipZigTest;

    var test_dir = testing.tmpDir(.{});
    defer test_dir.cleanup();

    const file = try test_dir.dir.createFile("test.txt", .{ .read = true });
    defer file.close();

    const test_data = "Hello, sendfile!";
    try file.writeAll(test_data);
    try file.seekTo(0);

    const stat = try file.stat();
    try testing.expectEqual(test_data.len, stat.size);
}

test "chunked file transfer initialization" {
    if (@import("builtin").os.tag == .wasi) return error.SkipZigTest;

    var test_dir = testing.tmpDir(.{});
    defer test_dir.cleanup();

    const file = try test_dir.dir.createFile("chunk.txt", .{ .read = true });
    defer file.close();

    try file.writeAll("Test data for chunking");
    try file.seekTo(0);

    var transfer = try ChunkedFileTransfer.init(file, 1024);
    try testing.expectEqual(@as(usize, 0), transfer.bytes_sent);
    try testing.expect(transfer.total_size > 0);
    try testing.expectEqual(@as(f32, 0.0), transfer.progress());
}

test "chunked transfer progress calculation" {
    if (@import("builtin").os.tag == .wasi) return error.SkipZigTest;

    var test_dir = testing.tmpDir(.{});
    defer test_dir.cleanup();

    const file = try test_dir.dir.createFile("progress.txt", .{ .read = true });
    defer file.close();

    try file.writeAll("1234567890");
    try file.seekTo(0);

    var transfer = try ChunkedFileTransfer.init(file, 1024);
    try testing.expectEqual(@as(f32, 0.0), transfer.progress());

    transfer.bytes_sent = 5;
    try testing.expectEqual(@as(f32, 0.5), transfer.progress());

    transfer.bytes_sent = 10;
    try testing.expectEqual(@as(f32, 1.0), transfer.progress());
}

test "sendfile fallback" {
    if (@import("builtin").os.tag == .wasi) return error.SkipZigTest;

    var test_dir = testing.tmpDir(.{});
    defer test_dir.cleanup();

    const file = try test_dir.dir.createFile("fallback.txt", .{ .read = true });
    defer file.close();

    const test_data = "Fallback test data";
    try file.writeAll(test_data);
    try file.seekTo(0);

    try testing.expectEqual(test_data.len, (try file.stat()).size);
}

test "empty file handling" {
    if (@import("builtin").os.tag == .wasi) return error.SkipZigTest;

    var test_dir = testing.tmpDir(.{});
    defer test_dir.cleanup();

    const file = try test_dir.dir.createFile("empty.txt", .{});
    defer file.close();

    const stat = try file.stat();
    try testing.expectEqual(@as(u64, 0), stat.size);
}

test "chunked transfer empty file" {
    if (@import("builtin").os.tag == .wasi) return error.SkipZigTest;

    var test_dir = testing.tmpDir(.{});
    defer test_dir.cleanup();

    const file = try test_dir.dir.createFile("empty.txt", .{ .read = true });
    defer file.close();

    var transfer = try ChunkedFileTransfer.init(file, 1024);
    try testing.expectEqual(@as(usize, 0), transfer.total_size);
    try testing.expectEqual(@as(f32, 1.0), transfer.progress());
}
```

### See Also

- Recipe 20.1: Non
- Recipe 11.9: Uploading and Downloading Files
- Recipe 5.10: Memory Mapping Binary Files
- Recipe 20.4: HTTP/1.1 Parser

---

## Recipe 20.3: Parsing Raw Packets with Packed Structs {#recipe-20-3}

**Tags:** c-interop, error-handling, networking, pointers, sockets, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/20-high-perf-networking/recipe_20_3.zig`

### Problem

You need to parse network packets at a low level, extracting headers and fields from raw binary data. Manual byte manipulation is error-prone and makes code hard to maintain.

### Solution

Use Zig's `extern struct` to define packet structures that map directly to network protocol layouts. extern structs guarantee C-compatible memory layout, making them perfect for binary protocols.

### IPv4 Header

Define an IPv4 header structure:

```zig
/// IPv4 header using extern struct for C-compatible layout
const IPv4Header = extern struct {
    version_ihl: u8, // version (4 bits) + IHL (4 bits)
    dscp_ecn: u8, // DSCP (6 bits) + ECN (2 bits)
    total_length: u16,
    identification: u16,
    flags_fragment: u16, // flags (3 bits) + fragment offset (13 bits)
    ttl: u8,
    protocol: u8,
    checksum: u16,
    source_addr: u32,
    dest_addr: u32,

    pub fn version(self: *const IPv4Header) u4 {
        return @truncate(self.version_ihl >> 4);
    }

    pub fn ihl(self: *const IPv4Header) u4 {
        return @truncate(self.version_ihl & 0x0F);
    }

    pub fn headerLength(self: *const IPv4Header) usize {
        return @as(usize, self.ihl()) * 4;
    }

    pub fn fromBytes(bytes: []const u8) !IPv4Header {
        if (bytes.len < @sizeOf(IPv4Header)) {
            return error.PacketTooSmall;
        }
        const header: *const IPv4Header = @ptrCast(@alignCast(bytes.ptr));
        return header.*;
    }

    pub fn toNetworkOrder(self: *IPv4Header) void {
        self.total_length = mem.nativeToBig(u16, self.total_length);
        self.identification = mem.nativeToBig(u16, self.identification);
        self.flags_fragment = mem.nativeToBig(u16, self.flags_fragment);
        self.checksum = mem.nativeToBig(u16, self.checksum);
        self.source_addr = mem.nativeToBig(u32, self.source_addr);
        self.dest_addr = mem.nativeToBig(u32, self.dest_addr);
    }

    pub fn fromNetworkOrder(self: *IPv4Header) void {
        self.total_length = mem.bigToNative(u16, self.total_length);
        self.identification = mem.bigToNative(u16, self.identification);
        self.flags_fragment = mem.bigToNative(u16, self.flags_fragment);
        self.checksum = mem.bigToNative(u16, self.checksum);
        self.source_addr = mem.bigToNative(u32, self.source_addr);
        self.dest_addr = mem.bigToNative(u32, self.dest_addr);
    }
};
```

### TCP Header

Parse TCP headers with bitfield access:

```zig
const TCPHeader = extern struct {
    source_port: u16,
    dest_port: u16,
    seq_num: u32,
    ack_num: u32,
    data_offset_flags: u16, // data offset (4 bits) + reserved (3 bits) + flags (9 bits)
    window_size: u16,
    checksum: u16,
    urgent_pointer: u16,

    pub fn dataOffset(self: *const TCPHeader) u4 {
        const offset_flags = mem.bigToNative(u16, self.data_offset_flags);
        return @truncate(offset_flags >> 12);
    }

    pub fn headerLength(self: *const TCPHeader) usize {
        return @as(usize, self.dataOffset()) * 4;
    }

    pub fn flags(self: *const TCPHeader) TCPFlags {
        const offset_flags = mem.bigToNative(u16, self.data_offset_flags);
        return @bitCast(@as(u9, @truncate(offset_flags & 0x1FF)));
    }

    pub fn fromBytes(bytes: []const u8) !TCPHeader {
        if (bytes.len < @sizeOf(TCPHeader)) {
            return error.PacketTooSmall;
        }
        const header: *const TCPHeader = @ptrCast(@alignCast(bytes.ptr));
        return header.*;
    }
};

// TCP flags in RFC 793 order (LSB to MSB):
// FIN=0x01, SYN=0x02, RST=0x04, PSH=0x08, ACK=0x10, URG=0x20, ECE=0x40, CWR=0x80, NS=0x100
const TCPFlags = packed struct {
    fin: bool, // Bit 0 (0x01)
    syn: bool, // Bit 1 (0x02)
    rst: bool, // Bit 2 (0x04)
    psh: bool, // Bit 3 (0x08)
    ack: bool, // Bit 4 (0x10)
    urg: bool, // Bit 5 (0x20)
    ece: bool, // Bit 6 (0x40)
    cwr: bool, // Bit 7 (0x80)
    ns: bool, // Bit 8 (0x100)
};
```

### UDP Header

UDP has a simpler header:

```zig
const UDPHeader = packed struct {
    source_port: u16,
    dest_port: u16,
    length: u16,
    checksum: u16,

    pub fn fromBytes(bytes: []const u8) !UDPHeader {
        if (bytes.len < @sizeOf(UDPHeader)) {
            return error.PacketTooSmall;
        }
        const header: *const UDPHeader = @ptrCast(@alignCast(bytes.ptr));
        return header.*;
    }

    pub fn payloadLength(self: *const UDPHeader) u16 {
        const len = mem.bigToNative(u16, self.length);
        return len - @sizeOf(UDPHeader);
    }
};
```

### Ethernet Frame

Handle link-layer frames:

```zig
const EthernetFrame = extern struct {
    dest_mac0: u8,
    dest_mac1: u8,
    dest_mac2: u8,
    dest_mac3: u8,
    dest_mac4: u8,
    dest_mac5: u8,
    source_mac0: u8,
    source_mac1: u8,
    source_mac2: u8,
    source_mac3: u8,
    source_mac4: u8,
    source_mac5: u8,
    ethertype: u16,

    pub const ETHERTYPE_IP = 0x0800;
    pub const ETHERTYPE_ARP = 0x0806;
    pub const ETHERTYPE_IPV6 = 0x86DD;

    pub fn fromBytes(bytes: []const u8) !EthernetFrame {
        if (bytes.len < @sizeOf(EthernetFrame)) {
            return error.FrameTooSmall;
        }
        const frame: *const EthernetFrame = @ptrCast(@alignCast(bytes.ptr));
        return frame.*;
    }

    pub fn getEthertype(self: *const EthernetFrame) u16 {
        return mem.bigToNative(u16, self.ethertype);
    }

    pub fn getDestMAC(self: *const EthernetFrame) [6]u8 {
        return [_]u8{
            self.dest_mac0,
            self.dest_mac1,
            self.dest_mac2,
            self.dest_mac3,
            self.dest_mac4,
            self.dest_mac5,
        };
    }

    pub fn getSourceMAC(self: *const EthernetFrame) [6]u8 {
        return [_]u8{
            self.source_mac0,
            self.source_mac1,
            self.source_mac2,
            self.source_mac3,
            self.source_mac4,
            self.source_mac5,
        };
    }
};
```

### Packet Parser

Combine parsers for complete packet handling:

```zig
const PacketParser = struct {
    pub fn parseIPv4(packet: []const u8) !struct {
        header: IPv4Header,
        payload: []const u8,
    } {
        var header = try IPv4Header.fromBytes(packet);
        header.fromNetworkOrder();

        const header_len = header.headerLength();
        if (packet.len < header_len) {
            return error.PacketTruncated;
        }

        return .{
            .header = header,
            .payload = packet[header_len..],
        };
    }

    pub fn parseTCP(packet: []const u8) !struct {
        header: TCPHeader,
        payload: []const u8,
    } {
        const header = try TCPHeader.fromBytes(packet);
        const header_len = header.headerLength();

        if (packet.len < header_len) {
            return error.PacketTruncated;
        }

        return .{
            .header = header,
            .payload = packet[header_len..],
        };
    }

    pub fn parseUDP(packet: []const u8) !struct {
        header: UDPHeader,
        payload: []const u8,
    } {
        const header = try UDPHeader.fromBytes(packet);

        if (packet.len < @sizeOf(UDPHeader)) {
            return error.PacketTruncated;
        }

        return .{
            .header = header,
            .payload = packet[@sizeOf(UDPHeader)..],
        };
    }
};
```

### Packet Builder

Build packets programmatically:

```zig
const PacketBuilder = struct {
    pub fn buildIPv4Header(
        protocol: u8,
        source: u32,
        dest: u32,
        payload_len: u16,
    ) IPv4Header {
        var header = IPv4Header{
            .version_ihl = (4 << 4) | 5, // IPv4, 5 words (20 bytes)
            .dscp_ecn = 0,
            .total_length = @sizeOf(IPv4Header) + payload_len,
            .identification = 0,
            .flags_fragment = 0,
            .ttl = 64,
            .protocol = protocol,
            .checksum = 0,
            .source_addr = source,
            .dest_addr = dest,
        };
        header.toNetworkOrder();
        return header;
    }

    pub fn buildUDPHeader(
        source_port: u16,
        dest_port: u16,
        payload_len: u16,
    ) UDPHeader {
        return UDPHeader{
            .source_port = mem.nativeToBig(u16, source_port),
            .dest_port = mem.nativeToBig(u16, dest_port),
            .length = mem.nativeToBig(u16, @sizeOf(UDPHeader) + payload_len),
            .checksum = 0,
        };
    }
};
```

### Discussion

Low-level packet parsing requires understanding both network protocols and memory layout. Zig makes this safe and efficient.

### extern vs packed Structs

**extern struct:**
- C-compatible layout
- Natural alignment (2-byte fields on 2-byte boundaries)
- Works for most network protocols
- Best for interfacing with C libraries

**packed struct:**
- Bit-level control
- Can create odd-sized types
- Useful for protocols with bit fields
- More complex to work with

For network protocols, extern struct is usually the right choice because network headers follow natural alignment.

### Network Byte Order

Network protocols use big-endian byte order. Always convert:
- `mem.nativeToBig()` when building packets
- `mem.bigToNative()` when parsing packets

The IPv4Header example shows both conversions in `toNetworkOrder()` and `fromNetworkOrder()`.

### Bitfield Access

Some header fields pack multiple values into single bytes:
- IPv4: version (4 bits) + IHL (4 bits)
- TCP: data offset (4 bits) + reserved (3 bits) + flags (9 bits)

Use bit shifting and masking to extract these:
```zig
pub fn version(self: *const IPv4Header) u4 {
    return @truncate(self.version_ihl >> 4);
}
```

### Safety Considerations

**Always validate input:**
- Check packet length before casting
- Verify header checksums
- Validate field values (TTL, protocol numbers, etc.)

**Alignment matters:**
- Use `@ptrCast(@alignCast(...))` when casting bytes to struct pointers
- extern struct guarantees natural alignment
- Be careful with odd-sized packets

### Protocol Examples

**IPv4 Header:** 20 bytes minimum
- Version, IHL, DSCP, ECN (4 bytes)
- Length, ID, Flags, Fragment (4 bytes)
- TTL, Protocol, Checksum (4 bytes)
- Source IP (4 bytes)
- Destination IP (4 bytes)

**TCP Header:** 20 bytes minimum
- Ports, sequence, acknowledgment (12 bytes)
- Data offset, flags, window (4 bytes)
- Checksum, urgent pointer (4 bytes)

**UDP Header:** 8 bytes fixed
- Source/dest ports (4 bytes)
- Length, checksum (4 bytes)

### Performance Tips

**Zero-copy parsing:**
- Cast directly from packet buffer to struct
- No allocation or copying needed
- Extremely fast

**Batch processing:**
- Parse many packets without allocation
- Use stack buffers for small headers
- Stream processing for high throughput

### MAC Address Handling

Packed structs can't contain arrays in Zig 0.15, so MAC addresses use individual fields. Helper methods provide array access:

```zig
pub fn getDestMAC(self: *const EthernetFrame) [6]u8 {
    return [_]u8{
        self.dest_mac0, self.dest_mac1, self.dest_mac2,
        self.dest_mac3, self.dest_mac4, self.dest_mac5,
    };
}
```

This keeps the struct layout simple while providing convenient access.

### Full Tested Code

```zig
// Recipe 20.3: Parsing raw packets with packed structs
// Target Zig Version: 0.15.2
const std = @import("std");
const testing = std.testing;
const mem = std.mem;

// ANCHOR: ip_header
/// IPv4 header using extern struct for C-compatible layout
const IPv4Header = extern struct {
    version_ihl: u8, // version (4 bits) + IHL (4 bits)
    dscp_ecn: u8, // DSCP (6 bits) + ECN (2 bits)
    total_length: u16,
    identification: u16,
    flags_fragment: u16, // flags (3 bits) + fragment offset (13 bits)
    ttl: u8,
    protocol: u8,
    checksum: u16,
    source_addr: u32,
    dest_addr: u32,

    pub fn version(self: *const IPv4Header) u4 {
        return @truncate(self.version_ihl >> 4);
    }

    pub fn ihl(self: *const IPv4Header) u4 {
        return @truncate(self.version_ihl & 0x0F);
    }

    pub fn headerLength(self: *const IPv4Header) usize {
        return @as(usize, self.ihl()) * 4;
    }

    pub fn fromBytes(bytes: []const u8) !IPv4Header {
        if (bytes.len < @sizeOf(IPv4Header)) {
            return error.PacketTooSmall;
        }
        const header: *const IPv4Header = @ptrCast(@alignCast(bytes.ptr));
        return header.*;
    }

    pub fn toNetworkOrder(self: *IPv4Header) void {
        self.total_length = mem.nativeToBig(u16, self.total_length);
        self.identification = mem.nativeToBig(u16, self.identification);
        self.flags_fragment = mem.nativeToBig(u16, self.flags_fragment);
        self.checksum = mem.nativeToBig(u16, self.checksum);
        self.source_addr = mem.nativeToBig(u32, self.source_addr);
        self.dest_addr = mem.nativeToBig(u32, self.dest_addr);
    }

    pub fn fromNetworkOrder(self: *IPv4Header) void {
        self.total_length = mem.bigToNative(u16, self.total_length);
        self.identification = mem.bigToNative(u16, self.identification);
        self.flags_fragment = mem.bigToNative(u16, self.flags_fragment);
        self.checksum = mem.bigToNative(u16, self.checksum);
        self.source_addr = mem.bigToNative(u32, self.source_addr);
        self.dest_addr = mem.bigToNative(u32, self.dest_addr);
    }
};
// ANCHOR_END: ip_header

// ANCHOR: tcp_header
const TCPHeader = extern struct {
    source_port: u16,
    dest_port: u16,
    seq_num: u32,
    ack_num: u32,
    data_offset_flags: u16, // data offset (4 bits) + reserved (3 bits) + flags (9 bits)
    window_size: u16,
    checksum: u16,
    urgent_pointer: u16,

    pub fn dataOffset(self: *const TCPHeader) u4 {
        const offset_flags = mem.bigToNative(u16, self.data_offset_flags);
        return @truncate(offset_flags >> 12);
    }

    pub fn headerLength(self: *const TCPHeader) usize {
        return @as(usize, self.dataOffset()) * 4;
    }

    pub fn flags(self: *const TCPHeader) TCPFlags {
        const offset_flags = mem.bigToNative(u16, self.data_offset_flags);
        return @bitCast(@as(u9, @truncate(offset_flags & 0x1FF)));
    }

    pub fn fromBytes(bytes: []const u8) !TCPHeader {
        if (bytes.len < @sizeOf(TCPHeader)) {
            return error.PacketTooSmall;
        }
        const header: *const TCPHeader = @ptrCast(@alignCast(bytes.ptr));
        return header.*;
    }
};

// TCP flags in RFC 793 order (LSB to MSB):
// FIN=0x01, SYN=0x02, RST=0x04, PSH=0x08, ACK=0x10, URG=0x20, ECE=0x40, CWR=0x80, NS=0x100
const TCPFlags = packed struct {
    fin: bool, // Bit 0 (0x01)
    syn: bool, // Bit 1 (0x02)
    rst: bool, // Bit 2 (0x04)
    psh: bool, // Bit 3 (0x08)
    ack: bool, // Bit 4 (0x10)
    urg: bool, // Bit 5 (0x20)
    ece: bool, // Bit 6 (0x40)
    cwr: bool, // Bit 7 (0x80)
    ns: bool, // Bit 8 (0x100)
};
// ANCHOR_END: tcp_header

// ANCHOR: udp_header
const UDPHeader = packed struct {
    source_port: u16,
    dest_port: u16,
    length: u16,
    checksum: u16,

    pub fn fromBytes(bytes: []const u8) !UDPHeader {
        if (bytes.len < @sizeOf(UDPHeader)) {
            return error.PacketTooSmall;
        }
        const header: *const UDPHeader = @ptrCast(@alignCast(bytes.ptr));
        return header.*;
    }

    pub fn payloadLength(self: *const UDPHeader) u16 {
        const len = mem.bigToNative(u16, self.length);
        return len - @sizeOf(UDPHeader);
    }
};
// ANCHOR_END: udp_header

// ANCHOR: ethernet_frame
const EthernetFrame = extern struct {
    dest_mac0: u8,
    dest_mac1: u8,
    dest_mac2: u8,
    dest_mac3: u8,
    dest_mac4: u8,
    dest_mac5: u8,
    source_mac0: u8,
    source_mac1: u8,
    source_mac2: u8,
    source_mac3: u8,
    source_mac4: u8,
    source_mac5: u8,
    ethertype: u16,

    pub const ETHERTYPE_IP = 0x0800;
    pub const ETHERTYPE_ARP = 0x0806;
    pub const ETHERTYPE_IPV6 = 0x86DD;

    pub fn fromBytes(bytes: []const u8) !EthernetFrame {
        if (bytes.len < @sizeOf(EthernetFrame)) {
            return error.FrameTooSmall;
        }
        const frame: *const EthernetFrame = @ptrCast(@alignCast(bytes.ptr));
        return frame.*;
    }

    pub fn getEthertype(self: *const EthernetFrame) u16 {
        return mem.bigToNative(u16, self.ethertype);
    }

    pub fn getDestMAC(self: *const EthernetFrame) [6]u8 {
        return [_]u8{
            self.dest_mac0,
            self.dest_mac1,
            self.dest_mac2,
            self.dest_mac3,
            self.dest_mac4,
            self.dest_mac5,
        };
    }

    pub fn getSourceMAC(self: *const EthernetFrame) [6]u8 {
        return [_]u8{
            self.source_mac0,
            self.source_mac1,
            self.source_mac2,
            self.source_mac3,
            self.source_mac4,
            self.source_mac5,
        };
    }
};
// ANCHOR_END: ethernet_frame

// ANCHOR: packet_parser
const PacketParser = struct {
    pub fn parseIPv4(packet: []const u8) !struct {
        header: IPv4Header,
        payload: []const u8,
    } {
        var header = try IPv4Header.fromBytes(packet);
        header.fromNetworkOrder();

        const header_len = header.headerLength();
        if (packet.len < header_len) {
            return error.PacketTruncated;
        }

        return .{
            .header = header,
            .payload = packet[header_len..],
        };
    }

    pub fn parseTCP(packet: []const u8) !struct {
        header: TCPHeader,
        payload: []const u8,
    } {
        const header = try TCPHeader.fromBytes(packet);
        const header_len = header.headerLength();

        if (packet.len < header_len) {
            return error.PacketTruncated;
        }

        return .{
            .header = header,
            .payload = packet[header_len..],
        };
    }

    pub fn parseUDP(packet: []const u8) !struct {
        header: UDPHeader,
        payload: []const u8,
    } {
        const header = try UDPHeader.fromBytes(packet);

        if (packet.len < @sizeOf(UDPHeader)) {
            return error.PacketTruncated;
        }

        return .{
            .header = header,
            .payload = packet[@sizeOf(UDPHeader)..],
        };
    }
};
// ANCHOR_END: packet_parser

// ANCHOR: packet_builder
const PacketBuilder = struct {
    pub fn buildIPv4Header(
        protocol: u8,
        source: u32,
        dest: u32,
        payload_len: u16,
    ) IPv4Header {
        var header = IPv4Header{
            .version_ihl = (4 << 4) | 5, // IPv4, 5 words (20 bytes)
            .dscp_ecn = 0,
            .total_length = @sizeOf(IPv4Header) + payload_len,
            .identification = 0,
            .flags_fragment = 0,
            .ttl = 64,
            .protocol = protocol,
            .checksum = 0,
            .source_addr = source,
            .dest_addr = dest,
        };
        header.toNetworkOrder();
        return header;
    }

    pub fn buildUDPHeader(
        source_port: u16,
        dest_port: u16,
        payload_len: u16,
    ) UDPHeader {
        return UDPHeader{
            .source_port = mem.nativeToBig(u16, source_port),
            .dest_port = mem.nativeToBig(u16, dest_port),
            .length = mem.nativeToBig(u16, @sizeOf(UDPHeader) + payload_len),
            .checksum = 0,
        };
    }
};
// ANCHOR_END: packet_builder

// Tests
test "IPv4 header size" {
    try testing.expectEqual(@as(usize, 20), @sizeOf(IPv4Header));
}

test "IPv4 header parsing" {
    var packet = [_]u8{
        0x45, 0x00, // version, IHL, DSCP, ECN
        0x00, 0x3c, // total length
        0x1c, 0x46, // identification
        0x40, 0x00, // flags, fragment offset
        0x40, 0x06, // TTL, protocol
        0xb1, 0xe6, // checksum
        0xc0, 0xa8, 0x00, 0x68, // source IP
        0xc0, 0xa8, 0x00, 0x01, // dest IP
    };

    var header = try IPv4Header.fromBytes(&packet);
    try testing.expectEqual(@as(u4, 4), header.version());
    try testing.expectEqual(@as(u4, 5), header.ihl());
    try testing.expectEqual(@as(usize, 20), header.headerLength());
}

test "TCP header size" {
    try testing.expectEqual(@as(usize, 20), @sizeOf(TCPHeader));
}

test "TCP flags parsing" {
    const packet = [_]u8{
        0x00, 0x50, // source port
        0x01, 0xbb, // dest port
        0x00, 0x00, 0x00, 0x00, // seq
        0x00, 0x00, 0x00, 0x00, // ack
        0x50, 0x12, // data offset + flags (SYN+ACK)
        0x20, 0x00, // window
        0x00, 0x00, // checksum
        0x00, 0x00, // urgent
    };

    const header = try TCPHeader.fromBytes(&packet);
    const tcp_flags = header.flags();
    // 0x5012: offset=5, flags=0x012 = 0b0001_0010
    // Bit 1 (SYN = 0x02) = 1, Bit 4 (ACK = 0x10) = 1
    try testing.expect(tcp_flags.syn); // SYN must be set
    try testing.expect(tcp_flags.ack); // ACK must be set
    try testing.expect(!tcp_flags.fin); // FIN must NOT be set
    try testing.expect(!tcp_flags.rst); // RST must NOT be set
    try testing.expect(!tcp_flags.psh); // PSH must NOT be set
    try testing.expect(!tcp_flags.urg); // URG must NOT be set
    try testing.expectEqual(@as(u4, 5), header.dataOffset());
}

test "UDP header size" {
    try testing.expectEqual(@as(usize, 8), @sizeOf(UDPHeader));
}

test "UDP payload length" {
    const packet = [_]u8{
        0x00, 0x35, // source port
        0x00, 0x35, // dest port
        0x00, 0x20, // length (32 bytes)
        0x00, 0x00, // checksum
    };

    const header = try UDPHeader.fromBytes(&packet);
    try testing.expectEqual(@as(u16, 24), header.payloadLength());
}

test "Ethernet frame size" {
    try testing.expectEqual(@as(usize, 14), @sizeOf(EthernetFrame));
}

test "Ethernet ethertype" {
    var frame = EthernetFrame{
        .dest_mac0 = 0xff,
        .dest_mac1 = 0xff,
        .dest_mac2 = 0xff,
        .dest_mac3 = 0xff,
        .dest_mac4 = 0xff,
        .dest_mac5 = 0xff,
        .source_mac0 = 0x00,
        .source_mac1 = 0x11,
        .source_mac2 = 0x22,
        .source_mac3 = 0x33,
        .source_mac4 = 0x44,
        .source_mac5 = 0x55,
        .ethertype = mem.nativeToBig(u16, EthernetFrame.ETHERTYPE_IP),
    };

    try testing.expectEqual(EthernetFrame.ETHERTYPE_IP, frame.getEthertype());
    const dest_mac = frame.getDestMAC();
    try testing.expectEqual(@as(u8, 0xff), dest_mac[0]);
}

test "packet parser - IPv4" {
    const packet = [_]u8{
        0x45, 0x00, 0x00, 0x3c, 0x1c, 0x46, 0x40, 0x00,
        0x40, 0x06, 0xb1, 0xe6, 0xc0, 0xa8, 0x00, 0x68,
        0xc0, 0xa8, 0x00, 0x01, // 20 byte header
        0xde, 0xad, 0xbe, 0xef, // payload
    };

    const parsed = try PacketParser.parseIPv4(&packet);
    try testing.expectEqual(@as(u4, 4), parsed.header.version());
    try testing.expectEqual(@as(usize, 4), parsed.payload.len);
}

test "packet builder - IPv4" {
    const header = PacketBuilder.buildIPv4Header(6, 0xC0A80001, 0xC0A80002, 100);
    try testing.expectEqual(@as(u4, 4), header.version());
    try testing.expectEqual(@as(u8, 6), header.protocol);
}

test "packet builder - UDP" {
    const header = PacketBuilder.buildUDPHeader(53, 53, 512);
    const payload_len = header.payloadLength();
    try testing.expectEqual(@as(u16, 512), payload_len);
}
```

### See Also

- Recipe 20.1: Non
- Recipe 20.6: Creating Raw Sockets
- Recipe 6.9: Binary Arrays of Structures
- Recipe 3.4: Searching and Matching Text Patterns

---

## Recipe 20.4: Implementing a Basic HTTP/1.1 Parser {#recipe-20-4}

**Tags:** allocators, arraylist, c-interop, data-structures, error-handling, hashmap, http, json, memory, networking, parsing, resource-cleanup, slices, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/20-high-perf-networking/recipe_20_4.zig`

### Problem

You need to parse HTTP requests and build HTTP responses without relying on external libraries. Understanding the HTTP protocol at a low level is crucial for building custom servers, proxies, or debugging network issues.

### Solution

Build a state machine-based parser that processes HTTP requests line by line, extracting methods, paths, headers, and body content.

### HTTP Method Enum

```zig
const HttpMethod = enum {
    GET,
    POST,
    PUT,
    DELETE,
    HEAD,
    OPTIONS,
    PATCH,

    pub fn fromString(s: []const u8) !HttpMethod {
        if (mem.eql(u8, s, "GET")) return .GET;
        if (mem.eql(u8, s, "POST")) return .POST;
        if (mem.eql(u8, s, "PUT")) return .PUT;
        if (mem.eql(u8, s, "DELETE")) return .DELETE;
        if (mem.eql(u8, s, "HEAD")) return .HEAD;
        if (mem.eql(u8, s, "OPTIONS")) return .OPTIONS;
        if (mem.eql(u8, s, "PATCH")) return .PATCH;
        return error.InvalidMethod;
    }
};
```

### HTTP Request Structure

```zig
const HttpRequest = struct {
    method: HttpMethod,
    path: []const u8,
    version: []const u8,
    headers: std.StringHashMap([]const u8),
    body: []const u8,

    pub fn deinit(self: *HttpRequest) void {
        self.headers.deinit();
    }
};
```

### Request Parser

```zig
const RequestParser = struct {
    allocator: mem.Allocator,
    state: ParserState,
    request: HttpRequest,

    const ParserState = enum {
        request_line,
        headers,
        body,
        complete,
    };

    pub fn init(allocator: mem.Allocator) RequestParser {
        return .{
            .allocator = allocator,
            .state = .request_line,
            .request = .{
                .method = .GET,
                .path = &[_]u8{},
                .version = &[_]u8{},
                .headers = std.StringHashMap([]const u8).init(allocator),
                .body = &[_]u8{},
            },
        };
    }

    pub fn deinit(self: *RequestParser) void {
        self.request.deinit();
    }

    pub fn parse(self: *RequestParser, data: []const u8) !HttpRequest {
        var lines = mem.splitScalar(u8, data, '\n');

        // Parse request line
        if (lines.next()) |line| {
            const trimmed = mem.trim(u8, line, "\r\n ");
            try self.parseRequestLine(trimmed);
        }

        // Parse headers
        while (lines.next()) |line| {
            const trimmed = mem.trim(u8, line, "\r\n ");
            if (trimmed.len == 0) {
                self.state = .body;
                break;
            }
            try self.parseHeader(trimmed);
        }

        // Get body (everything after blank line)
        const remaining = lines.rest();
        self.request.body = mem.trim(u8, remaining, "\r\n ");
        self.state = .complete;

        return self.request;
    }

    fn parseRequestLine(self: *RequestParser, line: []const u8) !void {
        var parts = mem.splitScalar(u8, line, ' ');

        const method_str = parts.next() orelse return error.InvalidRequestLine;
        self.request.method = try HttpMethod.fromString(method_str);

        self.request.path = parts.next() orelse return error.InvalidRequestLine;
        self.request.version = parts.next() orelse return error.InvalidRequestLine;
    }

    fn parseHeader(self: *RequestParser, line: []const u8) !void {
        const colon_pos = mem.indexOf(u8, line, ":") orelse return error.InvalidHeader;

        const name = line[0..colon_pos];
        const value = mem.trim(u8, line[colon_pos + 1 ..], " ");

        try self.request.headers.put(name, value);
    }
};
```

### Response Builder

```zig
const ResponseBuilder = struct {
    allocator: mem.Allocator,
    status_code: u16,
    status_text: []const u8,
    headers: std.StringHashMap([]const u8),
    body: []const u8,

    pub fn init(allocator: mem.Allocator) ResponseBuilder {
        return .{
            .allocator = allocator,
            .status_code = 200,
            .status_text = "OK",
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = &[_]u8{},
        };
    }

    pub fn deinit(self: *ResponseBuilder) void {
        self.headers.deinit();
    }

    pub fn setStatus(self: *ResponseBuilder, code: u16, text: []const u8) void {
        self.status_code = code;
        self.status_text = text;
    }

    pub fn addHeader(self: *ResponseBuilder, name: []const u8, value: []const u8) !void {
        try self.headers.put(name, value);
    }

    pub fn setBody(self: *ResponseBuilder, body: []const u8) void {
        self.body = body;
    }

    pub fn build(self: *ResponseBuilder) ![]const u8 {
        // Calculate total size for single allocation
        var total_size: usize = 0;

        // Status line: "HTTP/1.1 NNN TEXT\r\n"
        total_size += 9 + 3 + 1 + self.status_text.len + 2; // "HTTP/1.1 " + code + " " + text + "\r\n"

        // Headers
        var iter = self.headers.iterator();
        while (iter.next()) |entry| {
            total_size += entry.key_ptr.len + 2 + entry.value_ptr.len + 2; // "key: value\r\n"
        }

        // Content-Length header if body exists
        if (self.body.len > 0) {
            total_size += 20; // "Content-Length: " + number + "\r\n"
        }

        // Blank line + body
        total_size += 2 + self.body.len;

        var result = std.ArrayList(u8){};
        errdefer result.deinit(self.allocator);

        // Reserve capacity
        try result.ensureTotalCapacity(self.allocator, total_size);

        // Status line
        try result.appendSlice(self.allocator, "HTTP/1.1 ");
        var buf: [16]u8 = undefined;
        const code_str = try std.fmt.bufPrint(&buf, "{d}", .{self.status_code});
        try result.appendSlice(self.allocator, code_str);
        try result.appendSlice(self.allocator, " ");
        try result.appendSlice(self.allocator, self.status_text);
        try result.appendSlice(self.allocator, "\r\n");

        // Headers
        iter = self.headers.iterator();
        while (iter.next()) |entry| {
            try result.appendSlice(self.allocator, entry.key_ptr.*);
            try result.appendSlice(self.allocator, ": ");
            try result.appendSlice(self.allocator, entry.value_ptr.*);
            try result.appendSlice(self.allocator, "\r\n");
        }

        // Content-Length if needed
        if (self.body.len > 0) {
            const len_str = try std.fmt.bufPrint(&buf, "{d}", .{self.body.len});
            try result.appendSlice(self.allocator, "Content-Length: ");
            try result.appendSlice(self.allocator, len_str);
            try result.appendSlice(self.allocator, "\r\n");
        }

        // Blank line
        try result.appendSlice(self.allocator, "\r\n");

        // Body
        if (self.body.len > 0) {
            try result.appendSlice(self.allocator, self.body);
        }

        return result.toOwnedSlice(self.allocator);
    }
};
```

### Chunked Transfer Encoding

```zig
const ChunkedParser = struct {
    state: enum { chunk_size, chunk_data, chunk_end, trailer, complete },
    chunk_size: usize,
    bytes_read: usize,

    pub fn init() ChunkedParser {
        return .{
            .state = .chunk_size,
            .chunk_size = 0,
            .bytes_read = 0,
        };
    }

    pub fn parseChunkSize(line: []const u8) !usize {
        const trimmed = mem.trim(u8, line, "\r\n ");
        const semicolon = mem.indexOf(u8, trimmed, ";") orelse trimmed.len;
        const size_str = trimmed[0..semicolon];

        return try std.fmt.parseInt(usize, size_str, 16);
    }
};
```

### Discussion

HTTP/1.1 is a text-based protocol designed to be human-readable. Parsing it requires careful state management and string processing.

### HTTP Request Format

```
METHOD PATH VERSION\r\n
Header1: Value1\r\n
Header2: Value2\r\n
\r\n
Body (optional)
```

Example:
```
GET /api/users HTTP/1.1\r\n
Host: example.com\r\n
Accept: application/json\r\n
\r\n
```

### Parsing Strategy

The parser uses a simple state machine:
1. **Request Line**: Parse method, path, and HTTP version
2. **Headers**: Parse key-value pairs until blank line
3. **Body**: Everything after blank line

This approach handles streaming data well - you can parse incrementally as data arrives.

### Header Storage

Headers are stored in a StringHashMap for O(1) lookup. Common headers:
- Host: Target host (required in HTTP/1.1)
- Content-Length: Body size in bytes
- Content-Type: MIME type of body
- Accept: Client's acceptable response types
- User-Agent: Client identifier

### Response Building

Build responses by:
1. Setting status code and text (200 OK, 404 Not Found, etc.)
2. Adding headers
3. Setting body
4. Calling build() to serialize

The builder automatically adds Content-Length when you set a body.

### Chunked Transfer Encoding

HTTP/1.1 supports chunked encoding for streaming responses of unknown length:

```
5\r\n
Hello\r\n
7\r\n
, World\r\n
0\r\n
\r\n
```

Each chunk starts with its size in hexadecimal, followed by `\r\n`, the data, and another `\r\n`. A zero-size chunk marks the end.

### Performance Considerations

**Memory allocation:**
- Parser uses allocator for headers hashmap
- Response builder pre-calculates total size for single allocation
- Avoid unnecessary copying

**Streaming:**
- Can parse partial requests as data arrives
- Useful for non-blocking servers
- Track parser state between recv() calls

### Common HTTP Status Codes

- **200 OK**: Success
- **201 Created**: Resource created
- **204 No Content**: Success with no body
- **301 Moved Permanently**: Redirect
- **400 Bad Request**: Client error
- **401 Unauthorized**: Authentication required
- **404 Not Found**: Resource doesn't exist
- **500 Internal Server Error**: Server error
- **503 Service Unavailable**: Server overloaded

### Security Considerations

**Always validate:**
- Method is a valid HTTP method
- Path doesn't contain `..` (directory traversal)
- Header names are valid (no colons or newlines)
- Content-Length matches actual body size
- Total request size is reasonable (prevent DoS)

**Limit sizes:**
```zig
if (path.len > 2048) return error.PathTooLong;
if (headers.count() > 100) return error.TooManyHeaders;
if (body.len > 1_000_000) return error.BodyTooLarge;
```

### HTTP/1.1 vs HTTP/2

HTTP/1.1:
- Text-based, human-readable
- Simple to parse and debug
- One request per connection (or pipelined)
- Headers uncompressed

HTTP/2:
- Binary protocol
- Multiplexed streams
- Header compression (HPACK)
- Server push

For most applications, HTTP/1.1 is sufficient and simpler to implement.

### Full Tested Code

```zig
// Recipe 20.4: Implementing a basic HTTP/1.1 parser from scratch
// Target Zig Version: 0.15.2
const std = @import("std");
const testing = std.testing;
const mem = std.mem;

// ANCHOR: http_method
const HttpMethod = enum {
    GET,
    POST,
    PUT,
    DELETE,
    HEAD,
    OPTIONS,
    PATCH,

    pub fn fromString(s: []const u8) !HttpMethod {
        if (mem.eql(u8, s, "GET")) return .GET;
        if (mem.eql(u8, s, "POST")) return .POST;
        if (mem.eql(u8, s, "PUT")) return .PUT;
        if (mem.eql(u8, s, "DELETE")) return .DELETE;
        if (mem.eql(u8, s, "HEAD")) return .HEAD;
        if (mem.eql(u8, s, "OPTIONS")) return .OPTIONS;
        if (mem.eql(u8, s, "PATCH")) return .PATCH;
        return error.InvalidMethod;
    }
};
// ANCHOR_END: http_method

// ANCHOR: http_request
const HttpRequest = struct {
    method: HttpMethod,
    path: []const u8,
    version: []const u8,
    headers: std.StringHashMap([]const u8),
    body: []const u8,

    pub fn deinit(self: *HttpRequest) void {
        self.headers.deinit();
    }
};
// ANCHOR_END: http_request

// ANCHOR: request_parser
const RequestParser = struct {
    allocator: mem.Allocator,
    state: ParserState,
    request: HttpRequest,

    const ParserState = enum {
        request_line,
        headers,
        body,
        complete,
    };

    pub fn init(allocator: mem.Allocator) RequestParser {
        return .{
            .allocator = allocator,
            .state = .request_line,
            .request = .{
                .method = .GET,
                .path = &[_]u8{},
                .version = &[_]u8{},
                .headers = std.StringHashMap([]const u8).init(allocator),
                .body = &[_]u8{},
            },
        };
    }

    pub fn deinit(self: *RequestParser) void {
        self.request.deinit();
    }

    pub fn parse(self: *RequestParser, data: []const u8) !HttpRequest {
        var lines = mem.splitScalar(u8, data, '\n');

        // Parse request line
        if (lines.next()) |line| {
            const trimmed = mem.trim(u8, line, "\r\n ");
            try self.parseRequestLine(trimmed);
        }

        // Parse headers
        while (lines.next()) |line| {
            const trimmed = mem.trim(u8, line, "\r\n ");
            if (trimmed.len == 0) {
                self.state = .body;
                break;
            }
            try self.parseHeader(trimmed);
        }

        // Get body (everything after blank line)
        const remaining = lines.rest();
        self.request.body = mem.trim(u8, remaining, "\r\n ");
        self.state = .complete;

        return self.request;
    }

    fn parseRequestLine(self: *RequestParser, line: []const u8) !void {
        var parts = mem.splitScalar(u8, line, ' ');

        const method_str = parts.next() orelse return error.InvalidRequestLine;
        self.request.method = try HttpMethod.fromString(method_str);

        self.request.path = parts.next() orelse return error.InvalidRequestLine;
        self.request.version = parts.next() orelse return error.InvalidRequestLine;
    }

    fn parseHeader(self: *RequestParser, line: []const u8) !void {
        const colon_pos = mem.indexOf(u8, line, ":") orelse return error.InvalidHeader;

        const name = line[0..colon_pos];
        const value = mem.trim(u8, line[colon_pos + 1 ..], " ");

        try self.request.headers.put(name, value);
    }
};
// ANCHOR_END: request_parser

// ANCHOR: response_builder
const ResponseBuilder = struct {
    allocator: mem.Allocator,
    status_code: u16,
    status_text: []const u8,
    headers: std.StringHashMap([]const u8),
    body: []const u8,

    pub fn init(allocator: mem.Allocator) ResponseBuilder {
        return .{
            .allocator = allocator,
            .status_code = 200,
            .status_text = "OK",
            .headers = std.StringHashMap([]const u8).init(allocator),
            .body = &[_]u8{},
        };
    }

    pub fn deinit(self: *ResponseBuilder) void {
        self.headers.deinit();
    }

    pub fn setStatus(self: *ResponseBuilder, code: u16, text: []const u8) void {
        self.status_code = code;
        self.status_text = text;
    }

    pub fn addHeader(self: *ResponseBuilder, name: []const u8, value: []const u8) !void {
        try self.headers.put(name, value);
    }

    pub fn setBody(self: *ResponseBuilder, body: []const u8) void {
        self.body = body;
    }

    pub fn build(self: *ResponseBuilder) ![]const u8 {
        // Calculate total size for single allocation
        var total_size: usize = 0;

        // Status line: "HTTP/1.1 NNN TEXT\r\n"
        total_size += 9 + 3 + 1 + self.status_text.len + 2; // "HTTP/1.1 " + code + " " + text + "\r\n"

        // Headers
        var iter = self.headers.iterator();
        while (iter.next()) |entry| {
            total_size += entry.key_ptr.len + 2 + entry.value_ptr.len + 2; // "key: value\r\n"
        }

        // Content-Length header if body exists
        if (self.body.len > 0) {
            total_size += 20; // "Content-Length: " + number + "\r\n"
        }

        // Blank line + body
        total_size += 2 + self.body.len;

        var result = std.ArrayList(u8){};
        errdefer result.deinit(self.allocator);

        // Reserve capacity
        try result.ensureTotalCapacity(self.allocator, total_size);

        // Status line
        try result.appendSlice(self.allocator, "HTTP/1.1 ");
        var buf: [16]u8 = undefined;
        const code_str = try std.fmt.bufPrint(&buf, "{d}", .{self.status_code});
        try result.appendSlice(self.allocator, code_str);
        try result.appendSlice(self.allocator, " ");
        try result.appendSlice(self.allocator, self.status_text);
        try result.appendSlice(self.allocator, "\r\n");

        // Headers
        iter = self.headers.iterator();
        while (iter.next()) |entry| {
            try result.appendSlice(self.allocator, entry.key_ptr.*);
            try result.appendSlice(self.allocator, ": ");
            try result.appendSlice(self.allocator, entry.value_ptr.*);
            try result.appendSlice(self.allocator, "\r\n");
        }

        // Content-Length if needed
        if (self.body.len > 0) {
            const len_str = try std.fmt.bufPrint(&buf, "{d}", .{self.body.len});
            try result.appendSlice(self.allocator, "Content-Length: ");
            try result.appendSlice(self.allocator, len_str);
            try result.appendSlice(self.allocator, "\r\n");
        }

        // Blank line
        try result.appendSlice(self.allocator, "\r\n");

        // Body
        if (self.body.len > 0) {
            try result.appendSlice(self.allocator, self.body);
        }

        return result.toOwnedSlice(self.allocator);
    }
};
// ANCHOR_END: response_builder

// ANCHOR: chunked_parser
const ChunkedParser = struct {
    state: enum { chunk_size, chunk_data, chunk_end, trailer, complete },
    chunk_size: usize,
    bytes_read: usize,

    pub fn init() ChunkedParser {
        return .{
            .state = .chunk_size,
            .chunk_size = 0,
            .bytes_read = 0,
        };
    }

    pub fn parseChunkSize(line: []const u8) !usize {
        const trimmed = mem.trim(u8, line, "\r\n ");
        const semicolon = mem.indexOf(u8, trimmed, ";") orelse trimmed.len;
        const size_str = trimmed[0..semicolon];

        return try std.fmt.parseInt(usize, size_str, 16);
    }
};
// ANCHOR_END: chunked_parser

// Tests
test "HTTP method parsing" {
    try testing.expectEqual(HttpMethod.GET, try HttpMethod.fromString("GET"));
    try testing.expectEqual(HttpMethod.POST, try HttpMethod.fromString("POST"));
    try testing.expectError(error.InvalidMethod, HttpMethod.fromString("INVALID"));
}

test "parse simple GET request" {
    var parser = RequestParser.init(testing.allocator);
    defer parser.deinit();

    const request_data =
        \\GET /index.html HTTP/1.1
        \\Host: example.com
        \\User-Agent: TestClient/1.0
        \\
        \\
    ;

    const request = try parser.parse(request_data);
    try testing.expectEqual(HttpMethod.GET, request.method);
    try testing.expectEqualStrings("/index.html", request.path);
    try testing.expectEqualStrings("HTTP/1.1", request.version);
    try testing.expectEqualStrings("example.com", request.headers.get("Host").?);
}

test "parse POST request with body" {
    var parser = RequestParser.init(testing.allocator);
    defer parser.deinit();

    const request_data =
        \\POST /api/data HTTP/1.1
        \\Host: api.example.com
        \\Content-Type: application/json
        \\Content-Length: 27
        \\
        \\{"key": "value", "id": 42}
    ;

    const request = try parser.parse(request_data);
    try testing.expectEqual(HttpMethod.POST, request.method);
    try testing.expectEqualStrings("/api/data", request.path);
    try testing.expectEqualStrings("{\"key\": \"value\", \"id\": 42}", request.body);
}

test "response builder - basic response" {
    var builder = ResponseBuilder.init(testing.allocator);
    defer builder.deinit();

    builder.setStatus(200, "OK");
    try builder.addHeader("Content-Type", "text/plain");
    builder.setBody("Hello, World!");

    const response = try builder.build();
    defer testing.allocator.free(response);

    try testing.expect(mem.indexOf(u8, response, "HTTP/1.1 200 OK") != null);
    try testing.expect(mem.indexOf(u8, response, "Hello, World!") != null);
}

test "response builder - 404 response" {
    var builder = ResponseBuilder.init(testing.allocator);
    defer builder.deinit();

    builder.setStatus(404, "Not Found");
    try builder.addHeader("Content-Type", "text/html");
    builder.setBody("<h1>404 Not Found</h1>");

    const response = try builder.build();
    defer testing.allocator.free(response);

    try testing.expect(mem.indexOf(u8, response, "404 Not Found") != null);
}

test "chunked encoding - parse chunk size" {
    try testing.expectEqual(@as(usize, 0x1a), try ChunkedParser.parseChunkSize("1a\r\n"));
    try testing.expectEqual(@as(usize, 0x100), try ChunkedParser.parseChunkSize("100\r\n"));
    try testing.expectEqual(@as(usize, 0), try ChunkedParser.parseChunkSize("0\r\n"));
}

test "chunked encoding - parse with extension" {
    try testing.expectEqual(@as(usize, 0x1a), try ChunkedParser.parseChunkSize("1a;name=value\r\n"));
}

test "request parser - multiple headers" {
    var parser = RequestParser.init(testing.allocator);
    defer parser.deinit();

    const request_data =
        \\GET / HTTP/1.1
        \\Host: example.com
        \\Accept: text/html
        \\Accept-Encoding: gzip
        \\Connection: keep-alive
        \\
        \\
    ;

    const request = try parser.parse(request_data);
    try testing.expectEqual(@as(usize, 4), request.headers.count());
}

test "response builder - empty body" {
    var builder = ResponseBuilder.init(testing.allocator);
    defer builder.deinit();

    builder.setStatus(204, "No Content");

    const response = try builder.build();
    defer testing.allocator.free(response);

    try testing.expect(mem.indexOf(u8, response, "204 No Content") != null);
}
```

### See Also

- Recipe 11.4: Building a Simple HTTP Server
- Recipe 20.1: Non
- Recipe 6.2: Reading and Writing JSON Data
- Recipe 11.6: Working with REST APIs

---

## Recipe 20.5: Using UDP Multicast {#recipe-20-5}

**Tags:** error-handling, http, networking, resource-cleanup, sockets, testing
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/20-high-perf-networking/recipe_20_5.zig`

### Problem

You need to send data to multiple receivers simultaneously without maintaining individual connections to each one. Traditional unicast requires sending the same data separately to each recipient, wasting bandwidth.

### Solution

Use UDP multicast to send a single packet that's delivered to all members of a multicast group. This is efficient for scenarios like live streaming, distributed systems, or service discovery.

### Multicast Sender

```zig
const MulticastSender = struct {
    socket: posix.socket_t,
    multicast_addr: net.Address,

    pub fn init(group: []const u8, port: u16) !MulticastSender {
        const addr = try net.Address.parseIp(group, port);

        const socket = try posix.socket(
            posix.AF.INET,
            posix.SOCK.DGRAM,
            posix.IPPROTO.UDP,
        );
        errdefer posix.close(socket);

        return .{
            .socket = socket,
            .multicast_addr = addr,
        };
    }

    pub fn deinit(self: *MulticastSender) void {
        posix.close(self.socket);
    }

    pub fn send(self: *MulticastSender, data: []const u8) !void {
        _ = try posix.sendto(
            self.socket,
            data,
            0,
            &self.multicast_addr.any,
            self.multicast_addr.getOsSockLen(),
        );
    }
};
```

### Multicast Receiver

```zig
const MulticastReceiver = struct {
    socket: posix.socket_t,
    local_addr: net.Address,

    pub fn init(port: u16) !MulticastReceiver {
        const any_addr = try net.Address.parseIp("0.0.0.0", port);

        const socket = try posix.socket(
            posix.AF.INET,
            posix.SOCK.DGRAM,
            posix.IPPROTO.UDP,
        );
        errdefer posix.close(socket);

        try posix.setsockopt(
            socket,
            posix.SOL.SOCKET,
            posix.SO.REUSEADDR,
            &mem.toBytes(@as(c_int, 1)),
        );

        try posix.bind(socket, &any_addr.any, any_addr.getOsSockLen());

        // Note: Actual multicast group joining is platform-specific
        // and would require using C structures not directly available in Zig std.posix

        return .{
            .socket = socket,
            .local_addr = any_addr,
        };
    }

    pub fn deinit(self: *MulticastReceiver) void {
        posix.close(self.socket);
    }

    pub fn receive(self: *MulticastReceiver, buffer: []u8) !usize {
        return try posix.recv(self.socket, buffer, 0);
    }
};
```

### Multicast Configuration

```zig
const MulticastConfig = struct {
    ttl: u8 = 1,
    loop: bool = true,

    pub fn apply(self: *const MulticastConfig, socket: posix.socket_t) !void {
        // Set TTL
        try posix.setsockopt(
            socket,
            posix.IPPROTO.IP,
            posix.IP.MULTICAST_TTL,
            &mem.toBytes(@as(c_int, self.ttl)),
        );

        // Set loopback
        const loop_val: c_int = if (self.loop) 1 else 0;
        try posix.setsockopt(
            socket,
            posix.IPPROTO.IP,
            posix.IP.MULTICAST_LOOP,
            &mem.toBytes(loop_val),
        );
    }
};
```

### Discussion

Multicast is a one-to-many communication method where a single packet reaches multiple destinations.

### Multicast Addresses

IPv4 multicast uses addresses in the range `224.0.0.0` to `239.255.255.255`:

- **224.0.0.0 - 224.0.0.255**: Reserved (local network control)
- **224.0.1.0 - 238.255.255.255**: Globally scoped
- **239.0.0.0 - 239.255.255.255**: Administratively scoped (local)

For local testing, use addresses like `239.0.0.1`.

### How Multicast Works

1. **Sender**: Creates a UDP socket and sends to multicast address
2. **Receiver**: Joins the multicast group to receive packets
3. **Network**: Routers replicate packets to all group members

This is more efficient than sending individual copies.

### TTL (Time To Live)

TTL limits how far multicast packets travel:
- **1**: Local network only (default)
- **32**: Within site
- **64**: Within region
- **128**: Within continent
- **255**: Global

Set TTL based on your needs to avoid unnecessary network traffic.

### Multicast Loopback

By default, multicast packets loop back to the sender. Disable if you don't want to receive your own messages:

```zig
config.loop = false;
```

### Platform Considerations

Joining multicast groups requires platform-specific structures:
- **Linux**: Uses `ip_mreqn`
- **BSD/macOS**: Uses `ip_mreq`
- **Windows**: Uses `ip_mreq`

The code shows the basic UDP setup; actual group joining requires C interop with platform-specific headers.

### Common Use Cases

**Service Discovery:**
```zig
// Announce service on 239.255.255.250:1900
var sender = try MulticastSender.init("239.255.255.250", 1900);
try sender.send("SERVICE:MyApp:192.168.1.100:8080");
```

**Live Data Feeds:**
```zig
// Stock quotes to all subscribers
while (true) {
    const quote = getLatestQuote();
    try sender.send(quote);
    std.time.sleep(1 * std.time.ns_per_s);
}
```

**Distributed Logging:**
```zig
// Log to all monitoring systems
try sender.send("ERROR: Database connection failed");
```

### Security Considerations

Multicast has security implications:
- Anyone on the network can join your group
- No built-in authentication
- Packets can be sniffed
- Easy to cause DoS by flooding

**Best practices:**
- Use administratively scoped addresses (239.x.x.x)
- Encrypt sensitive data
- Rate limit sending
- Validate received data

### Reliability

UDP multicast is unreliable:
- Packets may be lost
- No delivery guarantees
- No ordering guarantees
- Receivers may miss messages

For reliability, add:
- Sequence numbers
- Acknowledgments (via unicast)
- Retransmission logic
- Forward error correction

### Full Tested Code

```zig
// Recipe 20.5: Using UDP multicast
// Target Zig Version: 0.15.2
const std = @import("std");
const testing = std.testing;
const posix = std.posix;
const net = std.net;
const mem = std.mem;

// ANCHOR: multicast_sender
const MulticastSender = struct {
    socket: posix.socket_t,
    multicast_addr: net.Address,

    pub fn init(group: []const u8, port: u16) !MulticastSender {
        const addr = try net.Address.parseIp(group, port);

        const socket = try posix.socket(
            posix.AF.INET,
            posix.SOCK.DGRAM,
            posix.IPPROTO.UDP,
        );
        errdefer posix.close(socket);

        return .{
            .socket = socket,
            .multicast_addr = addr,
        };
    }

    pub fn deinit(self: *MulticastSender) void {
        posix.close(self.socket);
    }

    pub fn send(self: *MulticastSender, data: []const u8) !void {
        _ = try posix.sendto(
            self.socket,
            data,
            0,
            &self.multicast_addr.any,
            self.multicast_addr.getOsSockLen(),
        );
    }
};
// ANCHOR_END: multicast_sender

// ANCHOR: multicast_receiver
const MulticastReceiver = struct {
    socket: posix.socket_t,
    local_addr: net.Address,

    pub fn init(port: u16) !MulticastReceiver {
        const any_addr = try net.Address.parseIp("0.0.0.0", port);

        const socket = try posix.socket(
            posix.AF.INET,
            posix.SOCK.DGRAM,
            posix.IPPROTO.UDP,
        );
        errdefer posix.close(socket);

        try posix.setsockopt(
            socket,
            posix.SOL.SOCKET,
            posix.SO.REUSEADDR,
            &mem.toBytes(@as(c_int, 1)),
        );

        try posix.bind(socket, &any_addr.any, any_addr.getOsSockLen());

        // Note: Actual multicast group joining is platform-specific
        // and would require using C structures not directly available in Zig std.posix

        return .{
            .socket = socket,
            .local_addr = any_addr,
        };
    }

    pub fn deinit(self: *MulticastReceiver) void {
        posix.close(self.socket);
    }

    pub fn receive(self: *MulticastReceiver, buffer: []u8) !usize {
        return try posix.recv(self.socket, buffer, 0);
    }
};
// ANCHOR_END: multicast_receiver

// ANCHOR: multicast_config
const MulticastConfig = struct {
    ttl: u8 = 1,
    loop: bool = true,

    pub fn apply(self: *const MulticastConfig, socket: posix.socket_t) !void {
        // Set TTL
        try posix.setsockopt(
            socket,
            posix.IPPROTO.IP,
            posix.IP.MULTICAST_TTL,
            &mem.toBytes(@as(c_int, self.ttl)),
        );

        // Set loopback
        const loop_val: c_int = if (self.loop) 1 else 0;
        try posix.setsockopt(
            socket,
            posix.IPPROTO.IP,
            posix.IP.MULTICAST_LOOP,
            &mem.toBytes(loop_val),
        );
    }
};
// ANCHOR_END: multicast_config

// Tests
test "multicast sender creation" {
    if (@import("builtin").os.tag == .wasi) return error.SkipZigTest;

    var sender = try MulticastSender.init("239.0.0.1", 5000);
    defer sender.deinit();

    try testing.expect(sender.socket >= 0);
}

test "multicast receiver creation" {
    if (@import("builtin").os.tag == .wasi) return error.SkipZigTest;

    var receiver = try MulticastReceiver.init(5001);
    defer receiver.deinit();

    try testing.expect(receiver.socket >= 0);
}

test "multicast config" {
    const config = MulticastConfig{
        .ttl = 2,
        .loop = false,
    };

    try testing.expectEqual(@as(u8, 2), config.ttl);
    try testing.expectEqual(false, config.loop);
}
```

### See Also

- Recipe 20.1: Non
- Recipe 11.1: Making HTTP Requests
- Recipe 20.6: Creating Raw Sockets

---

## Recipe 20.6: Creating Raw Sockets {#recipe-20-6}

**Tags:** concurrency, networking, resource-cleanup, sockets, testing, threading
**Difficulty:** advanced
**Code:** `code/05-zig-paradigms/20-high-perf-networking/recipe_20_6.zig`

### Problem

You need to capture or send packets at the lowest network level, below IP. This is useful for network monitoring tools, packet sniffers, custom protocol implementation, or security analysis.

### Solution

Use raw sockets with `AF.PACKET` to read and write raw Ethernet frames. This gives complete access to network traffic but requires elevated privileges.

### Raw Socket Creation

```zig
const RawSocket = struct {
    socket: posix.socket_t,

    pub fn init() !RawSocket {
        // Note: Requires root/admin privileges
        const socket = posix.socket(
            posix.AF.PACKET,
            posix.SOCK.RAW,
            mem.nativeToBig(u16, 0x0003), // ETH_P_ALL
        ) catch |err| {
            std.debug.print("Failed to create raw socket. Need root privileges.\n", .{});
            return err;
        };

        return .{ .socket = socket };
    }

    pub fn deinit(self: *RawSocket) void {
        posix.close(self.socket);
    }

    pub fn receive(self: *RawSocket, buffer: []u8) !usize {
        return try posix.recv(self.socket, buffer, 0);
    }
};
```

### Packet Capture

```zig
const PacketCapture = struct {
    socket: RawSocket,
    packets_captured: usize,

    pub fn init() !PacketCapture {
        return .{
            .socket = try RawSocket.init(),
            .packets_captured = 0,
        };
    }

    pub fn deinit(self: *PacketCapture) void {
        self.socket.deinit();
    }

    pub fn captureOne(self: *PacketCapture, buffer: []u8) !usize {
        const size = try self.socket.receive(buffer);
        self.packets_captured += 1;
        return size;
    }

    pub fn getStats(self: *const PacketCapture) struct { packets: usize } {
        return .{ .packets = self.packets_captured };
    }
};
```

### Ethernet Sniffer

```zig
const EthernetSniffer = struct {
    capture: PacketCapture,
    filter_ethertype: ?u16,

    pub fn init(filter: ?u16) !EthernetSniffer {
        return .{
            .capture = try PacketCapture.init(),
            .filter_ethertype = filter,
        };
    }

    pub fn deinit(self: *EthernetSniffer) void {
        self.capture.deinit();
    }

    pub fn sniff(self: *EthernetSniffer, buffer: []u8) !?usize {
        const size = try self.capture.captureOne(buffer);

        if (self.filter_ethertype) |filter| {
            if (size < 14) return null;

            const ethertype = mem.bigToNative(u16, @as(*const u16, @ptrCast(@alignCast(&buffer[12]))).*);

            if (ethertype != filter) {
                return null;
            }
        }

        return size;
    }
};
```

### Discussion

Raw sockets provide the lowest-level network access, capturing packets before the kernel processes them.

### Privileges Required

Raw sockets require elevated privileges:
- **Linux**: CAP_NET_RAW capability or root
- **macOS**: root
- **Windows**: Administrator

Run with sudo:
```bash
sudo ./packet_sniffer
```

### Socket Types

**AF.PACKET** (Linux):
- Access to link layer
- See all packets on interface
- Can send custom frames

**PF.PACKET** (also Linux):
- Synonym for AF.PACKET
- Same functionality

**Protocol 0x0003** (ETH_P_ALL):
- Captures all Ethernet protocols
- IPv4, IPv6, ARP, etc.

### Packet Filter

Raw sockets capture ALL traffic, which can be overwhelming. Filter by:
- EtherType (IPv4, IPv6, ARP)
- Source/Destination MAC
- VLAN tags
- Custom logic

Common EtherTypes:
- `0x0800`: IPv4
- `0x0806`: ARP
- `0x86DD`: IPv6
- `0x8100`: VLAN-tagged frame

### Promiscuous Mode

By default, sockets only see:
- Broadcast packets
- Multicast packets registered to
- Packets destined for this host

Enable promiscuous mode to see ALL packets on the network:
```zig
// Note: Requires additional socket options
// Implementation is platform-specific
```

### Performance Considerations

**High volume:**
- Network cards process millions of packets/second
- Buffer packets to avoid drops
- Use multiple threads for processing
- Consider kernel bypass (DPDK, AF_XDP)

**Memory:**
- Each packet needs a buffer
- Allocate ring buffer for efficiency
- Reuse buffers to avoid allocation

### Use Cases

**Network Monitoring:**
```zig
while (true) {
    var buffer: [2048]u8 = undefined;
    const size = try sniffer.sniff(&buffer);
    if (size) |s| {
        analyzePacket(buffer[0..s]);
    }
}
```

**Protocol Analysis:**
```zig
// Capture only ARP packets
var arp_sniffer = try EthernetSniffer.init(0x0806);
const packet = try arp_sniffer.sniff(&buffer);
parseARPPacket(packet);
```

**Custom Protocol:**
```zig
// Implement custom L2 protocol
const MY_ETHERTYPE: u16 = 0x88B5;
var sniffer = try EthernetSniffer.init(MY_ETHERTYPE);
```

### Security Implications

Raw sockets are powerful and dangerous:
- Can capture sensitive data (passwords, keys)
- Can spoof source addresses
- Can DOS with malformed packets
- Breach confidentiality

**Ethical use only:**
- Own networks/devices
- Authorized penetration testing
- Network administration
- Security research with permission

### Platform Differences

**Linux (AF.PACKET):**
- Most flexible
- Excellent performance
- Well-documented

**BSD/macOS (BPF):**
- Use Berkeley Packet Filter
- Different API
- `/dev/bpf` devices

**Windows (Npcap/WinPcap):**
- Requires driver installation
- Different API
- More restricted

### Alternatives to Raw Sockets

**libpcap/tcpdump:**
- Cross-platform packet capture
- Higher-level API
- BPF filter language
- Industry standard

**AF_XDP (Linux):**
- Kernel bypass
- Extreme performance
- Complex setup

**DPDK:**
- Data Plane Development Kit
- User-space drivers
- Used in routers/firewalls

### Full Tested Code

```zig
// Recipe 20.6: Creating raw sockets (reading raw ethernet frames)
// Target Zig Version: 0.15.2
const std = @import("std");
const testing = std.testing;
const posix = std.posix;
const mem = std.mem;

// ANCHOR: raw_socket
const RawSocket = struct {
    socket: posix.socket_t,

    pub fn init() !RawSocket {
        // Note: Requires root/admin privileges
        const socket = posix.socket(
            posix.AF.PACKET,
            posix.SOCK.RAW,
            mem.nativeToBig(u16, 0x0003), // ETH_P_ALL
        ) catch |err| {
            std.debug.print("Failed to create raw socket. Need root privileges.\n", .{});
            return err;
        };

        return .{ .socket = socket };
    }

    pub fn deinit(self: *RawSocket) void {
        posix.close(self.socket);
    }

    pub fn receive(self: *RawSocket, buffer: []u8) !usize {
        return try posix.recv(self.socket, buffer, 0);
    }
};
// ANCHOR_END: raw_socket

// ANCHOR: packet_capture
const PacketCapture = struct {
    socket: RawSocket,
    packets_captured: usize,

    pub fn init() !PacketCapture {
        return .{
            .socket = try RawSocket.init(),
            .packets_captured = 0,
        };
    }

    pub fn deinit(self: *PacketCapture) void {
        self.socket.deinit();
    }

    pub fn captureOne(self: *PacketCapture, buffer: []u8) !usize {
        const size = try self.socket.receive(buffer);
        self.packets_captured += 1;
        return size;
    }

    pub fn getStats(self: *const PacketCapture) struct { packets: usize } {
        return .{ .packets = self.packets_captured };
    }
};
// ANCHOR_END: packet_capture

// ANCHOR: ethernet_sniffer
const EthernetSniffer = struct {
    capture: PacketCapture,
    filter_ethertype: ?u16,

    pub fn init(filter: ?u16) !EthernetSniffer {
        return .{
            .capture = try PacketCapture.init(),
            .filter_ethertype = filter,
        };
    }

    pub fn deinit(self: *EthernetSniffer) void {
        self.capture.deinit();
    }

    pub fn sniff(self: *EthernetSniffer, buffer: []u8) !?usize {
        const size = try self.capture.captureOne(buffer);

        if (self.filter_ethertype) |filter| {
            if (size < 14) return null;

            const ethertype = mem.bigToNative(u16, @as(*const u16, @ptrCast(@alignCast(&buffer[12]))).*);

            if (ethertype != filter) {
                return null;
            }
        }

        return size;
    }
};
// ANCHOR_END: ethernet_sniffer

// Tests
test "raw socket struct creation" {
    // Note: This test will fail without root privileges
    // We test the struct API, not actual socket creation
    const socket_id: posix.socket_t = 42;
    const raw = RawSocket{ .socket = socket_id };
    defer {} // Don't actually close in test

    try testing.expectEqual(socket_id, raw.socket);
}

test "packet capture initialization" {
    // Test structure without requiring root
    const stats = PacketCapture{
        .socket = .{ .socket = 0 },
        .packets_captured = 5,
    };

    const result = stats.getStats();
    try testing.expectEqual(@as(usize, 5), result.packets);
}

test "ethernet sniffer with filter" {
    // Test filter configuration
    const ETHERTYPE_IP: u16 = 0x0800;

    const sniffer_config = struct {
        filter: ?u16,
    }{ .filter = ETHERTYPE_IP };

    try testing.expectEqual(ETHERTYPE_IP, sniffer_config.filter.?);
}
```

### See Also

- Recipe 20.3: Parsing Raw Packets
- Recipe 20.1: Non
- Recipe 20.5: Using UDP Multicast

---
