const PHI = (1 + Math.sqrt(5)) / 2;

const palette = {
  bg: "#f4f0e9",
  acute: "#d45d3d",
  obtuse: "#2f6f6c",
  accent: "#e1b145",
  stroke: "#1c1c1c",
};

const state = {
  tiling: "P2",
  iterations: 7,
  scale: 1.7,
  seed: 42,
  showEdges: true,
};

let ui = {};

function setup() {
  const canvas = createCanvas(windowWidth, windowHeight);
  canvas.parent("canvas-container");
  pixelDensity(Math.min(window.devicePixelRatio || 1, 2));
  noLoop();

  setupControls();
  regenerate();
}

function draw() {
  background(palette.bg);
  randomSeed(state.seed);
  noiseSeed(state.seed);

  const triangles = buildTiling();
  const bounds = getBounds(triangles);
  const windowRect = pickWindow(bounds, width, height);

  push();
  translate(-windowRect.x, -windowRect.y);

  const acuteColor = color(palette.acute);
  const obtuseColor = color(palette.obtuse);
  const accentColor = color(palette.accent);
  const strokeColor = color(palette.stroke);
  strokeColor.setAlpha(state.showEdges ? 110 : 0);

  stroke(strokeColor);
  strokeWeight(1);

  for (const tri of triangles) {
    if (!tri.intersects(windowRect)) continue;
    const c = tri.centroid();
    const base = tri.type === "acute" ? acuteColor : obtuseColor;
    const mix = noise(c.x * 0.006, c.y * 0.006) * 0.35;
    const fillColor = lerpColor(base, accentColor, mix);
    fill(fillColor);
    tri.draw();
  }

  pop();
}

function windowResized() {
  resizeCanvas(windowWidth, windowHeight);
  regenerate();
}

function regenerate() {
  redraw();
}

function buildTiling() {
  const base = initialTriangle();
  let tris = [base];
  const iterations = Math.round(state.iterations);

  for (let i = 0; i < iterations; i++) {
    const next = [];
    for (const tri of tris) {
      const children = tri.subdivide(state.tiling);
      for (const child of children) {
        next.push(child);
      }
    }
    tris = next;
  }

  return tris;
}

function initialTriangle() {
  const size = Math.min(width, height) * state.scale;
  const half = size / 2;
  const baseAngle = radians(36);
  const height = half * Math.tan(baseAngle);

  const apex = createVector(0, -height);
  const left = createVector(-half, 0);
  const right = createVector(half, 0);

  const rotation = radians(36 * floor(random(10)));
  const offset = createVector(random(-size * 0.25, size * 0.25), random(-size * 0.25, size * 0.25));

  const a = rotatePoint(apex, rotation).add(offset);
  const b = rotatePoint(left, rotation).add(offset);
  const c = rotatePoint(right, rotation).add(offset);

  return new Triangle(a, b, c, "obtuse");
}

function rotatePoint(vec, angle) {
  const cosA = Math.cos(angle);
  const sinA = Math.sin(angle);
  return createVector(vec.x * cosA - vec.y * sinA, vec.x * sinA + vec.y * cosA);
}

function pickWindow(bounds, w, h) {
  const spanX = bounds.maxX - bounds.minX;
  const spanY = bounds.maxY - bounds.minY;
  let x = bounds.minX - (w - spanX) / 2;
  let y = bounds.minY - (h - spanY) / 2;

  if (spanX > w) {
    x = random(bounds.minX, bounds.maxX - w);
  }
  if (spanY > h) {
    y = random(bounds.minY, bounds.maxY - h);
  }

  return { x, y, w, h };
}

function getBounds(triangles) {
  let minX = Infinity;
  let maxX = -Infinity;
  let minY = Infinity;
  let maxY = -Infinity;

  for (const tri of triangles) {
    const b = tri.bounds();
    minX = Math.min(minX, b.minX);
    maxX = Math.max(maxX, b.maxX);
    minY = Math.min(minY, b.minY);
    maxY = Math.max(maxY, b.maxY);
  }

  return { minX, maxX, minY, maxY };
}

function setupControls() {
  const controls = select("#controls");

  ui.tiling = addSelectRow(
    controls,
    "Tiling",
    [
      { label: "P2 (kites/darts)", value: "P2" },
      { label: "P3 (rhombs)", value: "P3" },
    ],
    state.tiling,
    (value) => {
      state.tiling = value;
      regenerate();
    }
  );

  ui.iterations = addSliderRow(
    controls,
    "Iterations",
    3,
    9,
    1,
    state.iterations,
    (value) => {
      state.iterations = value;
      regenerate();
    }
  );

  ui.scale = addSliderRow(
    controls,
    "Scale",
    1.2,
    2.4,
    0.05,
    state.scale,
    (value) => {
      state.scale = value;
      regenerate();
    }
  );

  const seedRow = createDiv();
  seedRow.class("control-row");
  seedRow.parent(controls);

  const seedLabel = createSpan("Seed");
  seedLabel.parent(seedRow);

  const seedInput = createInput(String(state.seed), "number");
  seedInput.class("p5-input");
  seedInput.parent(seedRow);
  seedInput.input(() => {
    const next = parseInt(seedInput.value(), 10);
    state.seed = Number.isFinite(next) ? next : 0;
    regenerate();
  });

  const reseedRow = createDiv();
  reseedRow.class("control-row");
  reseedRow.parent(controls);

  const reseedButton = createButton("Randomize");
  reseedButton.class("p5-button");
  reseedButton.parent(reseedRow);
  reseedButton.mousePressed(() => {
    state.seed = Math.floor(Math.random() * 1000000);
    seedInput.value(state.seed);
    regenerate();
  });

  const edgeRow = createDiv();
  edgeRow.class("control-row");
  edgeRow.parent(controls);

  const edgeLabel = createSpan("Edges");
  edgeLabel.parent(edgeRow);

  const edgeToggle = createCheckbox("", state.showEdges);
  edgeToggle.class("p5-checkbox");
  edgeToggle.parent(edgeRow);
  edgeToggle.changed(() => {
    state.showEdges = edgeToggle.checked();
    regenerate();
  });
}

function addSliderRow(parent, labelText, min, max, step, initial, onChange) {
  const row = createDiv();
  row.class("control-row");
  row.parent(parent);

  const initialText = step < 1 ? initial.toFixed(2) : initial;
  const label = createSpan(`${labelText}: ${initialText}`);
  label.parent(row);

  const slider = createSlider(min, max, initial, step);
  slider.class("p5-input");
  slider.parent(row);
  slider.style("width", "140px");

  slider.input(() => {
    const value = parseFloat(slider.value());
    const labelValue = step < 1 ? value.toFixed(2) : value;
    label.html(`${labelText}: ${labelValue}`);
    onChange(value);
  });

  return slider;
}

function addSelectRow(parent, labelText, options, initial, onChange) {
  const row = createDiv();
  row.class("control-row");
  row.parent(parent);

  const label = createSpan(labelText);
  label.parent(row);

  const select = createSelect();
  select.class("p5-select");
  select.parent(row);
  options.forEach((opt) => {
    select.option(opt.label, opt.value);
  });
  select.value(initial);
  select.changed(() => onChange(select.value()));

  return select;
}

class Triangle {
  constructor(a, b, c, type) {
    this.a = a.copy();
    this.b = b.copy();
    this.c = c.copy();
    this.type = type;
    this.ensureCCW();
  }

  ensureCCW() {
    if (cross2(this.a, this.b, this.c) < 0) {
      const tmp = this.b;
      this.b = this.c;
      this.c = tmp;
    }
  }

  vertices() {
    return [this.a, this.b, this.c];
  }

  bounds() {
    if (this._bounds) return this._bounds;
    const xs = [this.a.x, this.b.x, this.c.x];
    const ys = [this.a.y, this.b.y, this.c.y];
    this._bounds = {
      minX: Math.min(...xs),
      maxX: Math.max(...xs),
      minY: Math.min(...ys),
      maxY: Math.max(...ys),
    };
    return this._bounds;
  }

  centroid() {
    if (this._centroid) return this._centroid;
    this._centroid = createVector(
      (this.a.x + this.b.x + this.c.x) / 3,
      (this.a.y + this.b.y + this.c.y) / 3
    );
    return this._centroid;
  }

  intersects(rect) {
    const b = this.bounds();
    return !(
      b.maxX < rect.x ||
      b.minX > rect.x + rect.w ||
      b.maxY < rect.y ||
      b.minY > rect.y + rect.h
    );
  }

  apexBase() {
    const v = this.vertices();
    const d01 = dist(v[0].x, v[0].y, v[1].x, v[1].y);
    const d12 = dist(v[1].x, v[1].y, v[2].x, v[2].y);
    const d20 = dist(v[2].x, v[2].y, v[0].x, v[0].y);
    const opp = [d12, d20, d01];

    let idx = 0;
    if (this.type === "acute") {
      idx = opp.indexOf(Math.min(...opp));
    } else {
      idx = opp.indexOf(Math.max(...opp));
    }

    const apex = v[idx];
    const base1 = v[(idx + 2) % 3];
    const base2 = v[(idx + 1) % 3];

    return { apex, base1, base2 };
  }

  subdivide(tiling) {
    const { apex, base1, base2 } = this.apexBase();

    if (tiling === "P2") {
      return this.subdivideP2(apex, base1, base2);
    }

    return this.subdivideP3(apex, base1, base2);
  }

  subdivideP2(apex, base1, base2) {
    if (this.type === "acute") {
      const p = lerpPoint(base1, apex, 1 / PHI);
      const q = lerpPoint(apex, base2, 1 / PHI);
      return [
        new Triangle(base1, base2, q, "acute"),
        new Triangle(base1, p, q, "acute"),
        new Triangle(p, q, apex, "obtuse"),
      ];
    }

    const q = lerpPoint(base1, base2, 1 / PHI);
    return [
      new Triangle(base1, q, apex, "acute"),
      new Triangle(q, base2, apex, "obtuse"),
    ];
  }

  subdivideP3(apex, base1, base2) {
    if (this.type === "acute") {
      const p = lerpPoint(apex, base1, 1 / PHI);
      return [
        new Triangle(base1, base2, p, "acute"),
        new Triangle(base2, p, apex, "obtuse"),
      ];
    }

    const d = lerpPoint(base1, base2, 1 / PHI);
    const e = lerpPoint(base1, apex, 1 / PHI);
    return [
      new Triangle(apex, d, e, "acute"),
      new Triangle(base2, apex, d, "obtuse"),
      new Triangle(d, e, base1, "obtuse"),
    ];
  }

  draw() {
    beginShape();
    vertex(this.a.x, this.a.y);
    vertex(this.b.x, this.b.y);
    vertex(this.c.x, this.c.y);
    endShape(CLOSE);
  }
}

function lerpPoint(a, b, t) {
  return createVector(lerp(a.x, b.x, t), lerp(a.y, b.y, t));
}

function cross2(a, b, c) {
  return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
}
