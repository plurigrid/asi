#!/usr/bin/env node

/**
 * UREPL Phase 2: Universal REPL CLI
 *
 * Usage:
 *   urepl execute <dialect> <code> [seed]
 *   urepl bootstrap [seed]
 *   urepl load-srfi <number>
 *   urepl list-srfis
 *   urepl status
 *   urepl server [port]
 */

const fs = require('fs');
const path = require('path');

// Color utilities for CLI output
const colors = {
  reset: '\x1b[0m',
  bright: '\x1b[1m',
  dim: '\x1b[2m',
  red: '\x1b[31m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  blue: '\x1b[34m',
  magenta: '\x1b[35m',
  cyan: '\x1b[36m',
};

function colorize(text, color) {
  return `${colors[color]}${text}${colors.reset}`;
}

function printHeader(title) {
  console.log('');
  console.log(colorize('🎨 ' + title, 'cyan'));
  console.log(colorize('━'.repeat(70), 'dim'));
  console.log('');
}

function printSuccess(msg) {
  console.log(colorize('✓', 'green') + ' ' + msg);
}

function printError(msg) {
  console.log(colorize('✗', 'red') + ' ' + msg);
}

function printInfo(msg) {
  console.log(colorize('ℹ', 'blue') + ' ' + msg);
}

function printWarning(msg) {
  console.log(colorize('⚠', 'yellow') + ' ' + msg);
}

// UREPL Commands
const commands = {
  execute: async (args) => {
    printHeader('UREPL Execute');

    if (args.length < 2) {
      printError('Usage: urepl execute <dialect> <code> [seed]');
      process.exit(1);
    }

    const [dialect, code] = args;
    const seed = args[2] || '42';
    const dialects = ['scheme', 'clojure', 'lisp'];

    if (!dialects.includes(dialect)) {
      printError(`Unknown dialect: ${dialect}`);
      printInfo(`Available: ${dialects.join(', ')}`);
      process.exit(1);
    }

    printInfo(`Dialect: ${colorize(dialect, 'magenta')}`);
    printInfo(`Code: ${colorize(code, 'green')}`);
    printInfo(`Seed: ${colorize(seed, 'yellow')}`);
    console.log('');

    // Send to UREPL server
    try {
      const client = require('../src/urepl/client.js');
      const result = await client.execute(dialect, code, seed);

      printSuccess('Execution completed');
      console.log('');
      console.log(colorize('Result:', 'cyan'));
      console.log(JSON.stringify(result, null, 2));
    } catch (err) {
      printError('Execution failed: ' + err.message);
      process.exit(1);
    }
  },

  bootstrap: async (args) => {
    printHeader('UREPL Bootstrap Sequence');

    const seed = args[0] || '42';
    printInfo(`Seed: ${colorize(seed, 'yellow')}`);
    console.log('');

    try {
      const client = require('../src/urepl/client.js');
      const result = await client.bootstrap(seed);

      console.log('Bootstrap steps:');
      result.steps.forEach((step, i) => {
        const status = step.success ? colorize('✓', 'green') : colorize('✗', 'red');
        const color = step.color ? ` [${step.color.hex}]` : '';
        console.log(`  ${status} ${step.name}${color}`);
      });

      console.log('');
      if (result.success) {
        printSuccess(`Bootstrap complete: ${result.steps_completed}/${result.steps_total}`);
      } else {
        printWarning(`Bootstrap partial: ${result.steps_completed}/${result.steps_total}`);
      }
    } catch (err) {
      printError('Bootstrap failed: ' + err.message);
      process.exit(1);
    }
  },

  'load-srfi': async (args) => {
    printHeader('Load SRFI');

    if (args.length === 0) {
      printError('Usage: urepl load-srfi <number>');
      process.exit(1);
    }

    const num = parseInt(args[0]);
    if (isNaN(num)) {
      printError('SRFI number must be an integer');
      process.exit(1);
    }

    printInfo(`Loading SRFI ${colorize(num.toString(), 'yellow')}`);
    console.log('');

    try {
      const client = require('../src/urepl/client.js');
      const result = await client.loadSRFI(num);

      if (result.success) {
        printSuccess(`SRFI ${num} loaded: ${result.srfi_title}`);
        console.log('');
        console.log('Provides:');
        result.symbols.forEach(sym => {
          console.log(`  • ${colorize(sym, 'green')}`);
        });
      } else {
        printError(result.error);
      }
    } catch (err) {
      printError('Failed to load SRFI: ' + err.message);
      process.exit(1);
    }
  },

  'list-srfis': async (args) => {
    printHeader('Available SRFIs');

    try {
      const client = require('../src/urepl/client.js');
      const srfis = await client.listSRFIs();

      console.log('Implemented SRFIs:');
      srfis.implemented.forEach(srfi => {
        console.log(`  SRFI ${String(srfi.number).padStart(3, ' ')}: ${srfi.title}`);
      });

      if (srfis.planned.length > 0) {
        console.log('');
        console.log('Planned SRFIs:');
        srfis.planned.forEach(srfi => {
          console.log(`  SRFI ${String(srfi.number).padStart(3, ' ')}: ${srfi.title}`);
        });
      }

      console.log('');
      printInfo(`Total: ${srfis.implemented.length} implemented, ${srfis.planned.length} planned`);
    } catch (err) {
      printError('Failed to list SRFIs: ' + err.message);
      process.exit(1);
    }
  },

  status: async (args) => {
    printHeader('UREPL Status');

    try {
      const client = require('../src/urepl/client.js');
      const status = await client.status();

      console.log('Server Status:');
      console.log(`  Messages: ${colorize(status.message_count.toString(), 'cyan')}`);
      console.log(`  Errors: ${colorize(status.error_count.toString(), 'red')}`);
      console.log('');

      console.log('REPL Connections:');
      Object.entries(status.repl_status).forEach(([repl, state]) => {
        const color = state === 'connected' ? 'green' : 'yellow';
        console.log(`  ${repl}: ${colorize(state, color)}`);
      });

      console.log('');
      console.log(`Loaded SRFIs: ${status.loaded_srfis.join(', ') || 'none'}`);
    } catch (err) {
      printWarning('Cannot connect to UREPL server');
      printInfo('Start server with: urepl server');
    }
  },

  server: async (args) => {
    printHeader('UREPL WebSocket Server');

    const port = args[0] || '8765';
    printInfo(`Starting on port ${colorize(port, 'yellow')}`);
    console.log('');

    try {
      const server = require('../src/urepl/server.js');
      const instance = await server.start(parseInt(port));

      printSuccess(`Server running on port ${port}`);
      printInfo('Endpoints:');
      console.log(`  POST http://localhost:${port}/urepl/execute`);
      console.log(`  POST http://localhost:${port}/urepl/bootstrap`);
      console.log(`  GET  http://localhost:${port}/health`);
      console.log(`  GET  http://localhost:${port}/status`);
      console.log('');
      printInfo('Press Ctrl+C to stop');

      // Keep server running
      process.stdin.on('SIGINT', () => {
        printInfo('Shutting down...');
        server.stop(instance);
        process.exit(0);
      });
    } catch (err) {
      printError('Failed to start server: ' + err.message);
      process.exit(1);
    }
  },

  help: () => {
    console.log('');
    console.log(colorize('UREPL - Universal REPL Protocol', 'cyan'));
    console.log(colorize('Phase 2: Self-Hosting', 'dim'));
    console.log('');
    console.log('Usage: urepl <command> [options]');
    console.log('');
    console.log('Commands:');
    console.log('  execute <dialect> <code> [seed]  Execute code');
    console.log('  bootstrap [seed]                 Run bootstrap sequence');
    console.log('  load-srfi <number>               Load SRFI');
    console.log('  list-srfis                       List available SRFIs');
    console.log('  status                           Check server status');
    console.log('  server [port]                    Start WebSocket server');
    console.log('  help                             Show this help');
    console.log('');
    console.log('Examples:');
    console.log('  urepl execute scheme "(+ 1 2 3)" 42');
    console.log('  urepl execute clojure "(+ 1 2 3)"');
    console.log('  urepl bootstrap');
    console.log('  urepl load-srfi 26');
    console.log('  urepl server 8765');
    console.log('');
  }
};

// Main CLI handler
async function main() {
  const args = process.argv.slice(2);

  if (args.length === 0) {
    commands.help();
    process.exit(0);
  }

  const [command, ...cmdArgs] = args;

  if (command === 'help' || command === '-h' || command === '--help') {
    commands.help();
    process.exit(0);
  }

  if (command === 'version' || command === '-v' || command === '--version') {
    const pkg = require('../package.json');
    console.log(`UREPL v${pkg.version}`);
    process.exit(0);
  }

  if (!commands[command]) {
    printError(`Unknown command: ${command}`);
    printInfo('Run "urepl help" for usage');
    process.exit(1);
  }

  try {
    await commands[command](cmdArgs);
  } catch (err) {
    printError(err.message);
    process.exit(1);
  }
}

// Run if called directly
if (require.main === module) {
  main();
}

module.exports = commands;
