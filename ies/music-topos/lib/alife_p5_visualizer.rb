# lib/alife_p5_visualizer.rb
#
# p5.js Visualization Generator for Artificial Life Patterns
#
# Converts Lenia grids and particle swarms into interactive p5.js sketches
# that can be rendered in real-time or saved as HTML files for display.
#
# Integrates with: AlifeVisualSynthesis, algorithmic-art skill
# Uses: p5.js library (via CDN)

require 'json'

class AlifeP5Visualizer
  SAMPLE_RATE = 44100

  def initialize(width: 512, height: 512, title: "Alife Visualization")
    @width = width
    @height = height
    @title = title
    @color_palette = default_palette
  end

  # ===========================================================================
  # COLOR PALETTES
  # ===========================================================================
  # Pre-defined color schemes for visualization

  def default_palette
    # Viridis-inspired: dark → yellow
    {
      background: '#0d0221',
      low: '#440154',
      mid: '#31688e',
      high: '#35b779',
      peak: '#fde724'
    }
  end

  def set_palette(palette_name)
    palettes = {
      viridis: {
        background: '#0d0221',
        low: '#440154',
        mid: '#31688e',
        high: '#35b779',
        peak: '#fde724'
      },
      inferno: {
        background: '#000004',
        low: '#420a68',
        mid: '#932667',
        high: '#fca50a',
        peak: '#fcfdbf'
      },
      plasma: {
        background: '#0d0887',
        low: '#46039f',
        mid: '#ab63fa',
        high: '#ef553b',
        peak: '#fef47e'
      },
      cool: {
        background: '#001a33',
        low: '#0033cc',
        mid: '#00ccff',
        high: '#00ff99',
        peak: '#ffffff'
      },
      warm: {
        background: '#330000',
        low: '#990000',
        mid: '#ff6600',
        high: '#ffcc00',
        peak: '#ffff99'
      }
    }
    @color_palette = palettes[palette_name.to_sym] || default_palette
  end

  # ===========================================================================
  # LENIA VISUALIZATION
  # ===========================================================================

  def generate_lenia_sketch(grid_frames, output_file: 'alife_lenia.html',
                           color_scale: :viridis, playback_speed: 1.0)
    set_palette(color_scale)

    # Convert grid frames to JSON-safe format
    grid_json = grid_frames.map { |grid| grid.map { |row| row.map { |cell| (cell * 255).to_i } } }

    html = <<~HTML
      <!DOCTYPE html>
      <html lang="en">
      <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>#{@title}</title>
        <script src="https://cdnjs.cloudflare.com/ajax/libs/p5.js/1.5.0/p5.min.js"></script>
        <style>
          * { margin: 0; padding: 0; box-sizing: border-box; }
          body {
            font-family: 'Monaco', 'Courier New', monospace;
            background: #{@color_palette[:background]};
            color: #ffffff;
            display: flex;
            justify-content: center;
            align-items: center;
            min-height: 100vh;
            flex-direction: column;
            gap: 20px;
          }
          #p5-container {
            display: flex;
            justify-content: center;
          }
          .controls {
            display: flex;
            gap: 20px;
            align-items: center;
            flex-wrap: wrap;
            justify-content: center;
            max-width: 800px;
            padding: 20px;
            background: rgba(255, 255, 255, 0.05);
            border-radius: 8px;
          }
          button {
            padding: 8px 16px;
            background: #35b779;
            color: white;
            border: none;
            border-radius: 4px;
            cursor: pointer;
            font-family: inherit;
            font-size: 14px;
            transition: background 0.2s;
          }
          button:hover { background: #31688e; }
          button:active { transform: scale(0.98); }
          input[type="range"] {
            width: 200px;
            cursor: pointer;
          }
          label {
            font-size: 14px;
            white-space: nowrap;
          }
          .info {
            text-align: center;
            font-size: 12px;
            color: #aaaaaa;
          }
          canvas {
            display: block;
            image-rendering: pixelated;
            image-rendering: crisp-edges;
          }
        </style>
      </head>
      <body>
        <h1>🧬 Lenia Cellular Automata</h1>

        <div id="p5-container"></div>

        <div class="controls">
          <button id="playBtn">▶ Play</button>
          <button id="pauseBtn">⏸ Pause</button>
          <button id="resetBtn">↻ Reset</button>
          <label>
            Speed:
            <input type="range" id="speedSlider" min="0.1" max="2" step="0.1" value="1">
            <span id="speedValue">1.0x</span>
          </label>
          <label>
            Smoothing:
            <input type="range" id="smoothSlider" min="0" max="1" step="0.1" value="0">
            <span id="smoothValue">0</span>
          </label>
        </div>

        <div class="info">
          <p>Frame <span id="frameNum">0</span> / #{grid_frames.length}</p>
          <p>Resolution: #{@width}x#{@height} | Frames: #{grid_frames.length}</p>
        </div>

        <script>
          // Color palette
          const palette = {
            background: '#{@color_palette[:background]}',
            low: '#{@color_palette[:low]}',
            mid: '#{@color_palette[:mid]}',
            high: '#{@color_palette[:high]}',
            peak: '#{@color_palette[:peak]}'
          };

          // Grid data (embedded)
          const gridFrames = #{grid_json.to_json};

          let currentFrame = 0;
          let isPlaying = false;
          let playbackSpeed = #{playback_speed};
          let smoothing = 0;
          let frameSkip = 1;
          let lastUpdateTime = 0;
          let frameTime = 1000 / (30 * playbackSpeed); // 30 FPS base

          function interpolateColor(value) {
            // Map 0-255 to color gradient
            value = Math.max(0, Math.min(255, value));
            const t = value / 255;

            if (t < 0.33) {
              // low to mid
              const s = (t * 3);
              return lerpColor(palette.low, palette.mid, s);
            } else if (t < 0.66) {
              // mid to high
              const s = ((t - 0.33) * 3);
              return lerpColor(palette.mid, palette.high, s);
            } else {
              // high to peak
              const s = ((t - 0.66) * 3);
              return lerpColor(palette.high, palette.peak, s);
            }
          }

          function lerpColor(c1, c2, t) {
            // Linear interpolation between two hex colors
            const hex1 = c1.slice(1);
            const hex2 = c2.slice(1);

            const r1 = parseInt(hex1.substring(0, 2), 16);
            const g1 = parseInt(hex1.substring(2, 4), 16);
            const b1 = parseInt(hex1.substring(4, 6), 16);

            const r2 = parseInt(hex2.substring(0, 2), 16);
            const g2 = parseInt(hex2.substring(2, 4), 16);
            const b2 = parseInt(hex2.substring(4, 6), 16);

            const r = Math.round(r1 * (1 - t) + r2 * t);
            const g = Math.round(g1 * (1 - t) + g2 * t);
            const b = Math.round(b1 * (1 - t) + b2 * t);

            return [r, g, b];
          }

          function getSketchDimensions() {
            const maxWidth = Math.min(window.innerWidth - 40, 800);
            const maxHeight = Math.min(window.innerHeight - 300, 600);
            const aspectRatio = #{@width} / #{@height};

            let w = maxWidth;
            let h = w / aspectRatio;
            if (h > maxHeight) {
              h = maxHeight;
              w = h * aspectRatio;
            }
            return [w, h];
          }

          const sketch = (p) => {
            let canvasW, canvasH;
            let pixelSize;

            p.setup = function() {
              const [w, h] = getSketchDimensions();
              canvasW = w;
              canvasH = h;
              pixelSize = canvasW / #{@width};

              p.createCanvas(canvasW, canvasH);
              p.pixelDensity(1);
            };

            p.draw = function() {
              const now = Date.now();

              // Update based on playback speed
              if (isPlaying && (now - lastUpdateTime) > frameTime) {
                lastUpdateTime = now;
                currentFrame = (currentFrame + frameSkip) % gridFrames.length;
                document.getElementById('frameNum').textContent = currentFrame;
              }

              // Draw frame
              const frame = gridFrames[currentFrame];
              drawLeniaFrame(p, frame, canvasW, canvasH, pixelSize);
            };

            function drawLeniaFrame(p, frame, w, h, pSize) {
              p.background(palette.background);
              p.noStroke();

              for (let y = 0; y < #{@height}; y++) {
                for (let x = 0; x < #{@width}; x++) {
                  const value = frame[y][x];
                  const color = interpolateColor(value);
                  p.fill(color[0], color[1], color[2]);
                  p.rect(x * pSize, y * pSize, pSize, pSize);
                }
              }
            }

            p.windowResized = function() {
              if (document.getElementById('p5-container').offsetParent !== null) {
                const [w, h] = getSketchDimensions();
                if (Math.abs(w - canvasW) > 10) {
                  canvasW = w;
                  canvasH = h;
                  pixelSize = canvasW / #{@width};
                  p.resizeCanvas(canvasW, canvasH);
                }
              }
            };
          };

          // Create sketch
          const mySketch = new p5(sketch, 'p5-container');

          // Controls
          document.getElementById('playBtn').addEventListener('click', () => {
            isPlaying = true;
            lastUpdateTime = Date.now();
          });

          document.getElementById('pauseBtn').addEventListener('click', () => {
            isPlaying = false;
          });

          document.getElementById('resetBtn').addEventListener('click', () => {
            currentFrame = 0;
            isPlaying = false;
            document.getElementById('frameNum').textContent = '0';
          });

          document.getElementById('speedSlider').addEventListener('input', (e) => {
            playbackSpeed = parseFloat(e.target.value);
            frameTime = 1000 / (30 * playbackSpeed);
            frameSkip = Math.max(1, Math.floor(playbackSpeed));
            document.getElementById('speedValue').textContent = playbackSpeed.toFixed(1) + 'x';
          });

          document.getElementById('smoothSlider').addEventListener('input', (e) => {
            smoothing = parseFloat(e.target.value);
            document.getElementById('smoothValue').textContent = smoothing.toFixed(1);
          });
        </script>
      </body>
      </html>
    HTML

    File.write(output_file, html)
    { file: output_file, frames: grid_frames.length, width: @width, height: @height }
  end

  # ===========================================================================
  # PARTICLE SWARM VISUALIZATION
  # ===========================================================================

  def generate_particle_sketch(particle_frames, output_file: 'alife_swarm.html',
                              color_scale: :cool, playback_speed: 1.0)
    set_palette(color_scale)

    # Convert particles to drawable format
    particle_json = particle_frames.map do |particles|
      particles.map { |p| { x: p.x, y: p.y, energy: (p.energy * 255).to_i } }
    end

    html = <<~HTML
      <!DOCTYPE html>
      <html lang="en">
      <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>#{@title}</title>
        <script src="https://cdnjs.cloudflare.com/ajax/libs/p5.js/1.5.0/p5.min.js"></script>
        <style>
          * { margin: 0; padding: 0; box-sizing: border-box; }
          body {
            font-family: 'Monaco', 'Courier New', monospace;
            background: #{@color_palette[:background]};
            color: #ffffff;
            display: flex;
            justify-content: center;
            align-items: center;
            min-height: 100vh;
            flex-direction: column;
            gap: 20px;
          }
          #p5-container { display: flex; justify-content: center; }
          .controls {
            display: flex;
            gap: 20px;
            align-items: center;
            flex-wrap: wrap;
            justify-content: center;
            max-width: 800px;
            padding: 20px;
            background: rgba(255, 255, 255, 0.05);
            border-radius: 8px;
          }
          button {
            padding: 8px 16px;
            background: #35b779;
            color: white;
            border: none;
            border-radius: 4px;
            cursor: pointer;
            font-family: inherit;
            font-size: 14px;
            transition: background 0.2s;
          }
          button:hover { background: #31688e; }
          input[type="range"] { width: 200px; cursor: pointer; }
          label { font-size: 14px; white-space: nowrap; }
          .info {
            text-align: center;
            font-size: 12px;
            color: #aaaaaa;
          }
          canvas { display: block; }
        </style>
      </head>
      <body>
        <h1>🐦 Particle Swarm - Boid Dynamics</h1>

        <div id="p5-container"></div>

        <div class="controls">
          <button id="playBtn">▶ Play</button>
          <button id="pauseBtn">⏸ Pause</button>
          <button id="resetBtn">↻ Reset</button>
          <label>
            Speed:
            <input type="range" id="speedSlider" min="0.1" max="2" step="0.1" value="1">
            <span id="speedValue">1.0x</span>
          </label>
          <label>
            Particle Size:
            <input type="range" id="sizeSlider" min="2" max="20" step="1" value="8">
            <span id="sizeValue">8</span>
          </label>
        </div>

        <div class="info">
          <p>Frame <span id="frameNum">0</span> / #{particle_frames.length}</p>
          <p>World: #{@width}x#{@height} | Particles: ~#{particle_frames[0].length}</p>
        </div>

        <script>
          const palette = {
            background: '#{@color_palette[:background]}',
            low: '#{@color_palette[:low]}',
            mid: '#{@color_palette[:mid]}',
            high: '#{@color_palette[:high]}',
            peak: '#{@color_palette[:peak]}'
          };

          const particleFrames = #{particle_json.to_json};

          let currentFrame = 0;
          let isPlaying = false;
          let playbackSpeed = #{playback_speed};
          let particleSize = 8;
          let lastUpdateTime = 0;
          let frameTime = 1000 / (30 * playbackSpeed);
          let frameSkip = 1;

          function energyToColor(energy) {
            const t = energy / 255;
            if (t < 0.33) {
              return lerpColor(palette.low, palette.mid, t * 3);
            } else if (t < 0.66) {
              return lerpColor(palette.mid, palette.high, (t - 0.33) * 3);
            } else {
              return lerpColor(palette.high, palette.peak, (t - 0.66) * 3);
            }
          }

          function lerpColor(c1, c2, t) {
            const hex1 = c1.slice(1);
            const hex2 = c2.slice(1);

            const r1 = parseInt(hex1.substring(0, 2), 16);
            const g1 = parseInt(hex1.substring(2, 4), 16);
            const b1 = parseInt(hex1.substring(4, 6), 16);

            const r2 = parseInt(hex2.substring(0, 2), 16);
            const g2 = parseInt(hex2.substring(2, 4), 16);
            const b2 = parseInt(hex2.substring(4, 6), 16);

            const r = Math.round(r1 * (1 - t) + r2 * t);
            const g = Math.round(g1 * (1 - t) + g2 * t);
            const b = Math.round(b1 * (1 - t) + b2 * t);

            return [r, g, b];
          }

          function getSketchDimensions() {
            const maxWidth = Math.min(window.innerWidth - 40, 800);
            const maxHeight = Math.min(window.innerHeight - 300, 600);
            const aspectRatio = #{@width} / #{@height};

            let w = maxWidth;
            let h = w / aspectRatio;
            if (h > maxHeight) {
              h = maxHeight;
              w = h * aspectRatio;
            }
            return [w, h];
          }

          const sketch = (p) => {
            let canvasW, canvasH;
            let scaleX, scaleY;

            p.setup = function() {
              const [w, h] = getSketchDimensions();
              canvasW = w;
              canvasH = h;
              scaleX = canvasW / #{@width};
              scaleY = canvasH / #{@height};

              p.createCanvas(canvasW, canvasH);
              p.pixelDensity(1);
            };

            p.draw = function() {
              const now = Date.now();

              if (isPlaying && (now - lastUpdateTime) > frameTime) {
                lastUpdateTime = now;
                currentFrame = (currentFrame + frameSkip) % particleFrames.length;
                document.getElementById('frameNum').textContent = currentFrame;
              }

              const frame = particleFrames[currentFrame];
              drawParticles(p, frame, canvasW, canvasH, scaleX, scaleY);
            };

            function drawParticles(p, particles, w, h, sX, sY) {
              p.background(palette.background);
              p.noStroke();

              for (let i = 0; i < particles.length; i++) {
                const pt = particles[i];
                const color = energyToColor(pt.energy);
                p.fill(color[0], color[1], color[2]);
                p.circle(pt.x * sX, pt.y * sY, particleSize);
              }
            }

            p.windowResized = function() {
              if (document.getElementById('p5-container').offsetParent !== null) {
                const [w, h] = getSketchDimensions();
                if (Math.abs(w - canvasW) > 10) {
                  canvasW = w;
                  canvasH = h;
                  scaleX = canvasW / #{@width};
                  scaleY = canvasH / #{@height};
                  p.resizeCanvas(canvasW, canvasH);
                }
              }
            };
          };

          new p5(sketch, 'p5-container');

          document.getElementById('playBtn').addEventListener('click', () => {
            isPlaying = true;
            lastUpdateTime = Date.now();
          });

          document.getElementById('pauseBtn').addEventListener('click', () => {
            isPlaying = false;
          });

          document.getElementById('resetBtn').addEventListener('click', () => {
            currentFrame = 0;
            isPlaying = false;
            document.getElementById('frameNum').textContent = '0';
          });

          document.getElementById('speedSlider').addEventListener('input', (e) => {
            playbackSpeed = parseFloat(e.target.value);
            frameTime = 1000 / (30 * playbackSpeed);
            frameSkip = Math.max(1, Math.floor(playbackSpeed));
            document.getElementById('speedValue').textContent = playbackSpeed.toFixed(1) + 'x';
          });

          document.getElementById('sizeSlider').addEventListener('input', (e) => {
            particleSize = parseInt(e.target.value);
            document.getElementById('sizeValue').textContent = particleSize;
          });
        </script>
      </body>
      </html>
    HTML

    File.write(output_file, html)
    { file: output_file, frames: particle_frames.length, particles: particle_frames[0].length }
  end

  # ===========================================================================
  # COMBINED AUDIO-VISUAL EXPORT
  # ===========================================================================
  # Generate visualization + document playback together

  def generate_audiovisual_page(result, audio_file, output_file: 'alife_audiovisual.html')
    visual_frames = result[:visual_frames]
    duration_seconds = result[:duration_seconds]

    # Detect if frames are grids (Lenia) or particles (swarms)
    is_particles = visual_frames[0].is_a?(Array) && visual_frames[0][0].respond_to?(:x)

    # Convert appropriately
    if is_particles
      # Particle frames - convert to grid visualization
      grid_json = visual_frames.map do |particles|
        grid = Array.new(@height) { Array.new(@width, 0) }
        particles.each do |p|
          x = (p.x / @width * @width).to_i
          y = (p.y / @height * @height).to_i
          x = [@width - 1, [0, x].max].min
          y = [@height - 1, [0, y].max].min
          grid[y][x] = [(grid[y][x] + (p.energy * 255).to_i) / 2, 255].min
        end
        grid
      end
    else
      # Grid frames (Lenia) - standard conversion
      grid_json = visual_frames.map { |grid| grid.map { |row| row.map { |cell| (cell * 255).to_i } } }
    end

    set_palette(:viridis)

    html = <<~HTML
      <!DOCTYPE html>
      <html lang="en">
      <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>Audio-Visual Life Synthesis</title>
        <script src="https://cdnjs.cloudflare.com/ajax/libs/p5.js/1.5.0/p5.min.js"></script>
        <style>
          * { margin: 0; padding: 0; box-sizing: border-box; }
          body {
            font-family: 'Monaco', 'Courier New', monospace;
            background: #{@color_palette[:background]};
            color: #ffffff;
            padding: 20px;
            display: flex;
            flex-direction: column;
            align-items: center;
            gap: 20px;
          }
          h1 { font-size: 28px; margin-bottom: 10px; }
          .main-container {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 20px;
            max-width: 1400px;
            width: 100%;
          }
          .section {
            background: rgba(255, 255, 255, 0.05);
            border-radius: 8px;
            padding: 20px;
            display: flex;
            flex-direction: column;
            gap: 15px;
          }
          #p5-container {
            display: flex;
            justify-content: center;
            flex: 1;
          }
          .audio-player {
            background: rgba(0, 0, 0, 0.3);
            padding: 15px;
            border-radius: 4px;
            display: flex;
            flex-direction: column;
            gap: 10px;
          }
          audio {
            width: 100%;
            height: 30px;
            cursor: pointer;
          }
          .controls {
            display: flex;
            gap: 10px;
            flex-wrap: wrap;
          }
          button {
            padding: 8px 12px;
            background: #35b779;
            color: white;
            border: none;
            border-radius: 4px;
            cursor: pointer;
            font-family: inherit;
            font-size: 12px;
            flex: 1;
            min-width: 80px;
          }
          button:hover { background: #31688e; }
          .info { font-size: 12px; color: #aaaaaa; }
          .spectrum {
            height: 60px;
            background: linear-gradient(90deg,
              #{@color_palette[:low]} 0%,
              #{@color_palette[:mid]} 33%,
              #{@color_palette[:high]} 66%,
              #{@color_palette[:peak]} 100%
            );
            border-radius: 4px;
          }
          @media (max-width: 1200px) {
            .main-container {
              grid-template-columns: 1fr;
            }
          }
        </style>
      </head>
      <body>
        <h1>🎨 Audio-Visual Life Synthesis</h1>

        <div class="main-container">
          <div class="section">
            <h2>Visual Pattern Evolution</h2>
            <div id="p5-container"></div>
            <div class="controls">
              <button id="playVisBtn">▶ Visual</button>
              <button id="pauseVisBtn">⏸ Visual</button>
              <button id="resetVisBtn">↻ Reset</button>
            </div>
            <div class="info">
              Frame <span id="frameNum">0</span> / #{visual_frames.length}
            </div>
            <div class="spectrum"></div>
          </div>

          <div class="section">
            <h2>Audio Synthesis</h2>
            <div class="audio-player">
              <p style="font-size: 11px; margin-bottom: 5px;">
                Duration: #{duration_seconds.round(2)}s | Bitrate: 16-bit @ 44.1kHz
              </p>
              <audio id="audioPlayer" controls>
                <source src="#{File.basename(audio_file)}" type="audio/wav">
                Your browser does not support the audio element.
              </audio>
              <div class="controls">
                <button id="syncBtn">🔗 Sync Audio-Visual</button>
              </div>
              <div class="info">
                <p>Generated from cellular automata evolution</p>
                <p>Frequency mapping: Grid activation → Pitch</p>
              </div>
            </div>
          </div>
        </div>

        <script>
          const palette = {
            background: '#{@color_palette[:background]}',
            low: '#{@color_palette[:low]}',
            mid: '#{@color_palette[:mid]}',
            high: '#{@color_palette[:high]}',
            peak: '#{@color_palette[:peak]}'
          };

          const gridFrames = #{grid_json.to_json};

          let currentFrame = 0;
          let isPlaying = false;
          let audioSynced = false;
          let lastUpdateTime = 0;
          let frameTime = (#{duration_seconds} * 1000) / gridFrames.length;

          function interpolateColor(value) {
            value = Math.max(0, Math.min(255, value));
            const t = value / 255;

            if (t < 0.33) {
              const s = (t * 3);
              return lerpColor(palette.low, palette.mid, s);
            } else if (t < 0.66) {
              const s = ((t - 0.33) * 3);
              return lerpColor(palette.mid, palette.high, s);
            } else {
              const s = ((t - 0.66) * 3);
              return lerpColor(palette.high, palette.peak, s);
            }
          }

          function lerpColor(c1, c2, t) {
            const hex1 = c1.slice(1);
            const hex2 = c2.slice(1);

            const r1 = parseInt(hex1.substring(0, 2), 16);
            const g1 = parseInt(hex1.substring(2, 4), 16);
            const b1 = parseInt(hex1.substring(4, 6), 16);

            const r2 = parseInt(hex2.substring(0, 2), 16);
            const g2 = parseInt(hex2.substring(2, 4), 16);
            const b2 = parseInt(hex2.substring(4, 6), 16);

            const r = Math.round(r1 * (1 - t) + r2 * t);
            const g = Math.round(g1 * (1 - t) + g2 * t);
            const b = Math.round(b1 * (1 - t) + b2 * t);

            return [r, g, b];
          }

          function getSketchDimensions() {
            const maxWidth = Math.min(window.innerWidth - 100, 500);
            const maxHeight = Math.min(window.innerHeight - 200, 500);
            const aspectRatio = #{@width} / #{@height};

            let w = maxWidth;
            let h = w / aspectRatio;
            if (h > maxHeight) {
              h = maxHeight;
              w = h * aspectRatio;
            }
            return [w, h];
          }

          const sketch = (p) => {
            let canvasW, canvasH;
            let pixelSize;

            p.setup = function() {
              const [w, h] = getSketchDimensions();
              canvasW = w;
              canvasH = h;
              pixelSize = canvasW / #{@width};

              p.createCanvas(canvasW, canvasH);
              p.pixelDensity(1);
            };

            p.draw = function() {
              const now = Date.now();

              if (isPlaying && (now - lastUpdateTime) > frameTime) {
                lastUpdateTime = now;
                currentFrame = (currentFrame + 1) % gridFrames.length;
                document.getElementById('frameNum').textContent = currentFrame;

                if (audioSynced) {
                  const audioEl = document.getElementById('audioPlayer');
                  audioEl.currentTime = (currentFrame * frameTime) / 1000;
                }
              }

              const frame = gridFrames[currentFrame];
              p.background(palette.background);
              p.noStroke();

              for (let y = 0; y < #{@width}; y++) {
                for (let x = 0; x < #{@height}; x++) {
                  const value = frame[y][x];
                  const color = interpolateColor(value);
                  p.fill(color[0], color[1], color[2]);
                  p.rect(x * pixelSize, y * pixelSize, pixelSize, pixelSize);
                }
              }
            };

            p.windowResized = function() {
              const [w, h] = getSketchDimensions();
              if (Math.abs(w - canvasW) > 10) {
                canvasW = w;
                canvasH = h;
                pixelSize = canvasW / #{@width};
                p.resizeCanvas(canvasW, canvasH);
              }
            };
          };

          new p5(sketch, 'p5-container');

          // Controls
          document.getElementById('playVisBtn').addEventListener('click', () => {
            isPlaying = true;
            lastUpdateTime = Date.now();
          });

          document.getElementById('pauseVisBtn').addEventListener('click', () => {
            isPlaying = false;
          });

          document.getElementById('resetVisBtn').addEventListener('click', () => {
            currentFrame = 0;
            isPlaying = false;
            document.getElementById('frameNum').textContent = '0';
          });

          document.getElementById('syncBtn').addEventListener('click', () => {
            audioSynced = !audioSynced;
            const btn = document.getElementById('syncBtn');
            btn.style.background = audioSynced ? '#31688e' : '#35b779';
            btn.textContent = audioSynced ? '🔗 Synced' : '🔗 Sync Audio-Visual';
          });
        </script>
      </body>
      </html>
    HTML

    File.write(output_file, html)
    { file: output_file, duration: duration_seconds, frames: visual_frames.length }
  end
end
