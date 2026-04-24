import { JSDOM } from "jsdom";

// Penrose/MathJax needs a browser-like DOM
const dom = new JSDOM("<!DOCTYPE html><html><body></body></html>");
globalThis.window = dom.window;
globalThis.document = dom.window.document;
Object.defineProperty(globalThis, 'navigator', { value: dom.window.navigator, writable: true, configurable: true });
globalThis.DOMParser = dom.window.DOMParser;
globalThis.XMLSerializer = dom.window.XMLSerializer;
globalThis.Element = dom.window.Element;
globalThis.HTMLElement = dom.window.HTMLElement;
globalThis.Node = dom.window.Node;

import { compile, optimize, toSVG } from "@penrose/core";
import { readFileSync, writeFileSync } from "fs";

const domain = readFileSync("kb360.domain", "utf-8");
const substance = readFileSync("kb360.substance", "utf-8");
const style = readFileSync("kb360.style", "utf-8");

async function render() {
  console.log("Compiling...");
  const compiled = await compile({ domain, substance, style, variation: "kb360pro" });
  if (compiled.isErr()) {
    console.error("Compile error:", JSON.stringify(compiled.error, null, 2));
    process.exit(1);
  }
  console.log("Compiled OK. Optimizing...");

  const state = compiled.value;
  const optimized = optimize(state);
  if (optimized.isErr()) {
    console.error("Optimize error:", optimized.error);
    process.exit(1);
  }
  console.log("Optimized. Rendering SVG...");

  const svg = await toSVG(optimized.value, async () => "", "kb360pro-schematic");
  const svgStr = typeof svg === "string" ? svg : (svg.outerHTML || new dom.window.XMLSerializer().serializeToString(svg));
  writeFileSync("../figures/kb360pro-penrose.svg", svgStr);
  console.log("SVG written to ../figures/kb360pro-penrose.svg");
}

render().catch(e => { console.error(e); process.exit(1); });
