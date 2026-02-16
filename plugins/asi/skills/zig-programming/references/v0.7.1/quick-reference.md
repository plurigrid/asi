# Quick Reference

| Keyword | Description |
| --- | --- |
| `align` | `align` can be used to specify the alignment of a pointer. It can also be used after a variable or function declaration to specify the alignment of pointers to that variable or function.  - See also [Alignment](#Alignment) |
| `allowzero` | The pointer attribute `allowzero` allows a pointer to have address zero.  - See also [allowzero](#allowzero) |
| `and` | The boolean operator `and`.  - See also [Operators](08-operators.md#Operators) |
| `anyframe` | `anyframe` can be used as a type for variables which hold pointers to function frames.  - See also [Async Functions](35-async-functions.md#Async-Functions) |
| `anytype` | Function parameters and struct fields can be declared with `anytype` in place of the type. The type will be inferred where the function is called or the struct is instantiated.  - See also [Function Parameter Type Inference](#Function-Parameter-Type-Inference) |
| `asm` | `asm` begins an inline assembly expression. This allows for directly controlling the machine code generated on compilation.  - See also [Assembly](33-assembly.md#Assembly) |
| `async` | `async` can be used before a function call to get a pointer to the function's frame when it suspends.  - See also [Async Functions](35-async-functions.md#Async-Functions) |
| `await` | `await` can be used to suspend the current function until the frame provided after the `await` completes. `await` copies the value returned from the target function's frame to the caller.  - See also [Async Functions](35-async-functions.md#Async-Functions) |
| `break` | `break` can be used with a block label to return a value from the block. It can also be used to exit a loop before iteration completes naturally.  - See also [blocks](17-blocks.md#blocks), [while](19-while.md#while), [for](20-for.md#for) |
| `catch` | `catch` can be used to evaluate an expression if the expression before it evaluates to an error. The expression after the `catch` can optionally capture the error value.  - See also [catch](#catch), [Operators](08-operators.md#Operators) |
| `comptime` | `comptime` before a declaration can be used to label variables or function parameters as known at compile time. It can also be used to guarantee an expression is run at compile time.  - See also [comptime](32-comptime.md#comptime) |
| `const` | `const` declares a variable that can not be modified. Used as a pointer attribute, it denotes the value referenced by the pointer cannot be modified.  - See also [Variables](05-variables.md#Variables) |
| `continue` | `continue` can be used in a loop to jump back to the beginning of the loop.  - See also [while](19-while.md#while), [for](20-for.md#for) |
| `defer` | `defer` will execute an expression when control flow leaves the current block.  - See also [defer](22-defer.md#defer) |
| `else` | `else` can be used to provide an alternate branch for `if`, `switch`, `while`, and `for` expressions.  - If used after an if expression, the else branch will be executed if the test value returns false, null, or an error. - If used within a switch expression, the else branch will be executed if the test value matches no other cases. - If used after a loop expression, the else branch will be executed if the loop finishes without breaking. - See also [if](21-if.md#if), [switch](18-switch.md#switch), [while](19-while.md#while), [for](20-for.md#for) |
| `enum` | `enum` defines an enum type.  - See also [enum](14-enum.md#enum) |
| `errdefer` | `errdefer` will execute an expression when control flow leaves the current block if the function returns an error.  - See also [errdefer](#errdefer) |
| `error` | `error` defines an error type.  - See also [Errors](26-errors.md#Errors) |
| `export` | `export` makes a function or variable externally visible in the generated object file. Exported functions default to the C calling convention.  - See also [Functions](25-functions.md#Functions) |
| `extern` | `extern` can be used to declare a function or variable that will be resolved at link time, when linking statically or at runtime, when linking dynamically.  - See also [Functions](25-functions.md#Functions) |
| `false` | The boolean value `false`.  - See also [Primitive Values](#Primitive-Values) |
| `fn` | `fn` declares a function.  - See also [Functions](25-functions.md#Functions) |
| `for` | A `for` expression can be used to iterate over the elements of a slice, array, or tuple.  - See also [for](20-for.md#for) |
| `if` | An `if` expression can test boolean expressions, optional values, or error unions. For optional values or error unions, the if expression can capture the unwrapped value.  - See also [if](21-if.md#if) |
| `inline` | `inline` can be used to label a loop expression such that it will be unrolled at compile time. It can also be used to force a function to be inlined at all call sites.  - See also [inline while](#inline-while), [inline for](#inline-for), [Functions](25-functions.md#Functions) |
| `noalias` | The `noalias` keyword.  - TODO add documentation for noalias |
| `nosuspend` | The `nosuspend` keyword.  - TODO add documentation for nosuspend |
| `null` | The optional value `null`.  - See also [null](#null) |
| `or` | The boolean operator `or`.  - See also [Operators](08-operators.md#Operators) |
| `orelse` | `orelse` can be used to evaluate an expression if the expression before it evaluates to null.  - See also [Optionals](27-optionals.md#Optionals), [Operators](08-operators.md#Operators) |
| `packed` | The `packed` keyword before a struct definition changes the struct's in-memory layout to the guaranteed `packed` layout.  - See also [packed struct](#packed-struct) |
| `pub` | The `pub` in front of a top level declaration makes the declaration available to reference from a different file than the one it is declared in.  - See also [import](#import) |
| `resume` | `resume` will continue execution of a function frame after the point the function was suspended.  - See also [Suspend and Resume](#Suspend-and-Resume) |
| `return` | `return` exits a function with a value.  - See also [Functions](25-functions.md#Functions) |
| `linksection` | The `linksection` keyword.  - TODO add documentation for linksection |
| `struct` | `struct` defines a struct.  - See also [struct](13-struct.md#struct) |
| `suspend` | `suspend` will cause control flow to return to the call site or resumer of the function. `suspend` can also be used before a block within a function, to allow the function access to its frame before control flow returns to the call site.  - See also [Suspend and Resume](#Suspend-and-Resume) |
| `switch` | A `switch` expression can be used to test values of a common type. `switch` cases can capture field values of a [Tagged union](#Tagged-union).  - See also [switch](18-switch.md#switch) |
| `test` | The `test` keyword can be used to denote a top-level block of code used to make sure behavior meets expectations.  - See also [Zig Test](43-zig-test.md#Zig-Test) |
| `threadlocal` | `threadlocal` can be used to specify a variable as thread-local.  - See also [Thread Local Variables](#Thread-Local-Variables) |
| `true` | The boolean value `true`.  - See also [Primitive Values](#Primitive-Values) |
| `try` | `try` evaluates an error union expression. If it is an error, it returns from the current function with the same error. Otherwise, the expression results in the unwrapped value.  - See also [try](#try) |
| `undefined` | `undefined` can be used to leave a value uninitialized.  - See also [undefined](#undefined) |
| `union` | `union` defines a union.  - See also [union](15-union.md#union) |
| `unreachable` | `unreachable` can be used to assert that control flow will never happen upon a particular location. Depending on the build mode, `unreachable` may emit a panic.  - Emits a panic in `Debug` and `ReleaseSafe` mode, or when using `zig test`. - Does not emit a panic in `ReleaseFast` mode, unless `zig test` is being used. - See also [unreachable](23-unreachable.md#unreachable) |
| `usingnamespace` | `usingnamespace` is a top-level declaration that imports all the public declarations of the operand, which must be a struct, union, or enum, into the current scope.  - See also [usingnamespace](31-usingnamespace.md#usingnamespace) |
| `var` | `var` declares a variable that may be modified.  - See also [Variables](05-variables.md#Variables) |
| `volatile` | `volatile` can be used to denote loads or stores of a pointer have side effects. It can also modify an inline assembly expression to denote it has side effects.  - See also [volatile](#volatile), [Assembly](33-assembly.md#Assembly) |
| `while` | A `while` expression can be used to repeatedly test a boolean, optional, or error union expression, and cease looping when that expression evaluates to false, null, or an error, respectively.  - See also [while](19-while.md#while) |
