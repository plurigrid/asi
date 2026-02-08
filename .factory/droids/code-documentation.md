---
name: code-documentation
description: Writing effective code documentation - API docs, README files, inline
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Code Documentation

## README Structure

### Standard README Template
```markdown
# Project Name

Brief description of what this project does.

## Quick Start

\`\`\`bash
npm install
npm run dev
\`\`\`

## Installation

Detailed installation instructions...

## Usage

\`\`\`typescript
import { something } from 'project';

// Example usage
const result = something.doThing();
\`\`\`

## API Reference

### `functionName(param: Type): ReturnType`

Description of what the function does.

**Parameters:**
- `param` - Description of parameter

**Returns:** Description of return value

**Example:**
\`\`\`typescript
const result = functionName('value');
\`\`\`

## Configuration

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `option1` | `string` | `'default'` | What it does |

## Contributing

How to contribute...

## License

MIT
```

## API Documentation

### JSDoc/TSDoc Style
```typescript
/**
 * Creates a new user account.
 *
 * @param userData - The user data for account creation
 * @param options - Optional configuration
 * @returns The created user object
 * @throws {ValidationError} If email is invalid
 * @example
 * ```ts
 * const user = await createUser({
 *   email: 'user@example.com',
 *   name: 'John'
 * });
 * ```
 */
async function createUser(
  userData: UserInput,
  options?: CreateOptions
): Promise<User> {
  // Implementation
}

/**
 * Configuration options for the API client.
 */
interface ClientConfig {
  /** The API base URL */
  baseUrl: string;
  /** Request timeout in milliseconds @default 5000 */
  timeout?: number;
  /** Custom headers to include in requests */
  headers?: Record<string, string>;
}
```

### OpenAPI/Swagger
```yaml
openapi: 3.0.0
info:
  title: My API
  version: 1.0.0

paths:
  /users:
    post:
      summary: Create a user
      description: Creates a new user account
      requestBody:
        required: true
        content:
          application/json:
            schema:
              $ref: