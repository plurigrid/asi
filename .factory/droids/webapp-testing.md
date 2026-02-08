---
name: webapp-testing
description: Toolkit for interacting with and testing local web applications using
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Web App Testing with Playwright

## Setup

```bash
npm init playwright@latest
```

## Basic Test Structure

```typescript
import { test, expect } from '@playwright/test';

test('homepage has title', async ({ page }) => {
  await page.goto('http://localhost:3000');
  await expect(page).toHaveTitle(/My App/);
});

test('can navigate to about page', async ({ page }) => {
  await page.goto('http://localhost:3000');
  await page.click('text=About');
  await expect(page).toHaveURL(/.*about/);
});
```

## Common Actions

### Navigation
```typescript
await page.goto('http://localhost:3000');
await page.goBack();
await page.reload();
```

### Clicking
```typescript
await page.click('button');
await page.click('text=Submit');
await page.click('#submit-btn');
await page.click('[data-testid="submit"]');
```

### Form Input
```typescript
await page.fill('input[name="email"]', 'test@example.com');
await page.fill('#password', 'secret123');
await page.selectOption('select#country', 'USA');
await page.check('input[type="checkbox"]');
```

### Waiting
```typescript
await page.waitForSelector('.loaded');
await page.waitForURL('**/dashboard');
await page.waitForResponse('**/api/data');
await page.waitForTimeout(1000); // Avoid if possible
```

## Assertions

```typescript
await expect(page.locator('h1')).toHaveText('Welcome');
await expect(page.locator('.items')).toHaveCount(5);
await expect(page.locator('button')).toBeEnabled();
await expect(page.locator('.modal')).toBeVisible();
await expect(page.locator('input')).toHaveValue('test');
```

## Screenshots

```typescript
// Full page
await page.screenshot({ path: 'screenshot.png', fullPage: true });

// Element only
await page.locator('.chart').screenshot({ path: 'chart.png' });
```

## Console Logs

```typescript
page.on('console', msg => console.log(msg.text()));
page.on('pageerror', err => console.error(err.message));
```

## Network Interception

```typescript
await page.route('**/api/data', route => {
  route.fulfill({
    stat