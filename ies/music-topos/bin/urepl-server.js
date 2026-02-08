#!/usr/bin/env node

/**
 * UREPL WebSocket Server Entry Point
 * Standalone server startup script
 */

const path = require('path');
const port = process.env.UREPL_PORT || process.argv[2] || 8765;

console.log('');
console.log('\x1b[36m🚀 UREPL WebSocket Server\x1b[0m');
console.log('\x1b[2m' + '━'.repeat(70) + '\x1b[0m');
console.log('');

// Start server
try {
  const UReplServer = require('../src/urepl/server.js');

  const server = new UReplServer({
    port: parseInt(port),
    host: 'localhost'
  });

  server.on('ready', () => {
    console.log('\x1b[32m✓\x1b[0m Server started on port ' + port);
    console.log('');
    console.log('Endpoints:');
    console.log(`  \x1b[36mPOST\x1b[0m http://localhost:${port}/urepl/execute`);
    console.log(`  \x1b[36mPOST\x1b[0m http://localhost:${port}/urepl/bootstrap`);
    console.log(`  \x1b[36mGET\x1b[0m  http://localhost:${port}/health`);
    console.log(`  \x1b[36mGET\x1b[0m  http://localhost:${port}/status`);
    console.log('');
    console.log('\x1b[33mPress Ctrl+C to stop\x1b[0m');
  });

  server.on('error', (err) => {
    console.error('\x1b[31m✗\x1b[0m Server error: ' + err.message);
    process.exit(1);
  });

  // Graceful shutdown
  process.on('SIGINT', () => {
    console.log('');
    console.log('\x1b[33mShutting down...\x1b[0m');
    server.close(() => {
      console.log('\x1b[32m✓\x1b[0m Server stopped');
      process.exit(0);
    });
  });

  server.start();

} catch (err) {
  console.error('\x1b[31m✗ Failed to start server:\x1b[0m', err.message);
  process.exit(1);
}
