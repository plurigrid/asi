---
name: code-refactoring
description: Code refactoring patterns and techniques for improving code quality without
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Code Refactoring

## Refactoring Principles

### When to Refactor
- Before adding new features (make change easy, then make easy change)
- After getting tests passing (red-green-refactor)
- When you see code smells
- During code review feedback

### When NOT to Refactor
- Without tests covering the code
- Under tight deadlines with no safety net
- Code that will be replaced soon
- When you don't understand what the code does

## Common Code Smells

### Long Methods
```typescript
// BEFORE: Method doing too much
function processOrder(order: Order) {
  // 100 lines of validation, calculation, notification, logging...
}

// AFTER: Extract into focused methods
function processOrder(order: Order) {
  validateOrder(order);
  const total = calculateTotal(order);
  saveOrder(order, total);
  notifyCustomer(order);
}
```

### Deeply Nested Conditionals
```typescript
// BEFORE: Arrow code
function getDiscount(user: User, order: Order) {
  if (user) {
    if (user.isPremium) {
      if (order.total > 100) {
        if (order.items.length > 5) {
          return 0.2;
        }
      }
    }
  }
  return 0;
}

// AFTER: Early returns (guard clauses)
function getDiscount(user: User, order: Order) {
  if (!user) return 0;
  if (!user.isPremium) return 0;
  if (order.total <= 100) return 0;
  if (order.items.length <= 5) return 0;
  return 0.2;
}
```

### Primitive Obsession
```typescript
// BEFORE: Primitives everywhere
function createUser(name: string, email: string, phone: string) {
  if (!email.includes('@')) throw new Error('Invalid email');
  // more validation...
}

// AFTER: Value objects
class Email {
  constructor(private value: string) {
    if (!value.includes('@')) throw new Error('Invalid email');
  }
  toString() { return this.value; }
}

function createUser(name: string, email: Email, phone: Phone) {
  // Email is already validated
}
```

### Feature Envy
```typescript
// BEFORE: Method uses another object's data extensively
function calculateShipping(order: Order