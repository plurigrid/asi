#!/usr/bin/env node
const pako = require('pako');
const fs = require('fs');

const mode = process.argv[2];
const arg = process.argv[3];

function decode(url) {
  const hash = url.includes('#') ? url.split('#')[1] : url;
  if (hash.startsWith('base64:')) {
    return JSON.parse(Buffer.from(hash.slice(7), 'base64').toString()).code;
  }
  if (hash.startsWith('pako:')) {
    return JSON.parse(pako.inflate(Buffer.from(hash.slice(5), 'base64'), { to: 'string' })).code;
  }
  try {
    return JSON.parse(Buffer.from(hash, 'base64').toString()).code;
  } catch { return 'Unknown format'; }
}

function encodePako(diagram) {
  const compressed = pako.deflate(JSON.stringify({ code: diagram }), { level: 9 });
  return `https://mermaid.live/edit#pako:${Buffer.from(compressed).toString('base64')}`;
}

function encodeBase64(diagram) {
  return `https://mermaid.live/edit#base64:${Buffer.from(JSON.stringify({ code: diagram })).toString('base64')}`;
}

if (mode === 'decode') {
  console.log(decode(arg));
} else if (mode === 'encode-pako') {
  const input = arg || fs.readFileSync(0, 'utf8');
  console.log(encodePako(input));
} else if (mode === 'encode-base64') {
  const input = arg || fs.readFileSync(0, 'utf8');
  console.log(encodeBase64(input));
} else {
  console.log('Usage: codec.js <decode|encode-pako|encode-base64> [url-or-diagram]');
}
