---
name: qa-regression
description: Automate QA regression testing with reusable test skills. Create login
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# QA Regression Testing

Build and run automated regression tests using Playwright. Each test is a reusable skill that can be composed into full test suites.

## Setup

```bash
npm init -y
npm install playwright @playwright/test
npx playwright install
```

## Test Structure

Create tests in `tests/` folder:

```
tests/
├── auth/
│   ├── login.spec.ts
│   └── logout.spec.ts
├── dashboard/
│   └── load.spec.ts
├── users/
│   ├── create.spec.ts
│   └── delete.spec.ts
└── regression.spec.ts   # Full suite
```

## Common Test Skills

### Login Test

```typescript
// tests/auth/login.spec.ts
import { test, expect } from '@playwright/test';

test.describe('Login Flow', () => {
  test('should login with valid credentials', async ({ page }) => {
    await page.goto('/login');

    await page.fill('[data-testid="email"]', process.env.TEST_EMAIL!);
    await page.fill('[data-testid="password"]', process.env.TEST_PASSWORD!);
    await page.click('[data-testid="submit"]');

    // Verify redirect to dashboard
    await expect(page).toHaveURL(/dashboard/);
    await expect(page.locator('[data-testid="user-menu"]')).toBeVisible();
  });

  test('should show error for invalid credentials', async ({ page }) => {
    await page.goto('/login');

    await page.fill('[data-testid="email"]', 'wrong@example.com');
    await page.fill('[data-testid="password"]', 'wrongpassword');
    await page.click('[data-testid="submit"]');

    await expect(page.locator('[data-testid="error-message"]')).toBeVisible();
  });
});
```

### Dashboard Load Test

```typescript
// tests/dashboard/load.spec.ts
import { test, expect } from '@playwright/test';
import { login } from '../helpers/auth';

test.describe('Dashboard', () => {
  test.beforeEach(async ({ page }) => {
    await login(page);
  });

  test('should load dashboard within 3 seconds', async ({ page }) => {
    const start = Date.now();
    await page.goto('/dashboard');
    await page.waitForSelector('[data-testid="dashboard-content"]');
    c