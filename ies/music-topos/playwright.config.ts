import { defineConfig, devices } from '@playwright/test';

/**
 * Ramanujan CRDT Network - Playwright Configuration
 * Runs 12 test suites across all 11 components
 */

export default defineConfig({
  testDir: '.', // Current directory
  testMatch: '**/test_playwright.ts',

  // Number of parallel workers
  workers: 4,

  // Maximum time for single test
  timeout: 30 * 1000,

  // Configuration for tests
  use: {
    // Base URL for all navigation
    baseURL: 'http://localhost:3000',

    // Timeout for navigation
    navigationTimeout: 30000,

    // Screenshot on failure
    screenshot: 'only-on-failure',

    // Video on failure
    video: 'retain-on-failure',

    // Trace on failure
    trace: 'on-first-retry',
  },

  // Projects (browsers to test)
  projects: [
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'] },
    },
    {
      name: 'firefox',
      use: { ...devices['Desktop Firefox'] },
    },
    {
      name: 'webkit',
      use: { ...devices['Desktop Safari'] },
    },
  ],

  // Run web server before tests
  webServer: {
    command: 'cargo run',
    url: 'http://localhost:3000',
    reuseExistingServer: !process.env.CI,
    timeout: 120 * 1000,
  },

  // Reporter configuration
  reporter: [
    ['html', { outputFolder: 'playwright-report' }],
    ['json', { outputFile: 'test-results.json' }],
    ['junit', { outputFile: 'junit-results.xml' }],
    ['list'],
  ],

  // Retry failed tests
  retries: process.env.CI ? 2 : 0,

  // Forbid only tests in CI
  forbidOnly: !!process.env.CI,
});
