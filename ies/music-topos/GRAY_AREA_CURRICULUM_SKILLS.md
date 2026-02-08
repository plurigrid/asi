# Gray Area Foundation for the Arts - Curriculum Skills Enumeration

## Overview
Comprehensive skills taxonomy for creative coding education at Gray Area, informed by:
- GAFFTA Creative Code Immersive curriculum (Winter 2016)
- Wikidata education ontology patterns
- Music-Topos audio-visual synthesis toolkit
- p5.js ecosystem (Lauren McCarthy, primary tool)

---

## Tier 1: Foundation Skills

### 1.1 Programming Fundamentals
**Wikidata Reference**: Q9143 (Computer Programming)

```
├── Variables & Data Types
│   ├── Primitive types (numbers, strings, booleans)
│   ├── Arrays (lists, collections)
│   ├── Objects (key-value pairs, structured data)
│   └── Type coercion & casting
├── Control Flow
│   ├── Conditionals (if/else, switch)
│   ├── Loops (for, while, recursive)
│   └── Exception handling
├── Functions & Methods
│   ├── Function definition & parameters
│   ├── Return values & scope
│   ├── Recursion & higher-order functions
│   └── Callbacks & closures
└── Code Organization
    ├── Modules & imports
    ├── OOP principles (classes, inheritance)
    ├── Design patterns
    └── Code style & documentation
```

### 1.2 JavaScript (Primary Language)
**Wikidata Reference**: Q2005 (JavaScript)

```
├── ES6+ Features
│   ├── Arrow functions
│   ├── Template literals
│   ├── Destructuring
│   ├── Spread operator
│   └── Promises & async/await
├── DOM Manipulation
│   ├── Selecting elements (querySelector)
│   ├── Event handling
│   ├── Dynamic element creation
│   └── CSS styling via JS
├── Debugging
│   ├── Console methods
│   ├── Browser DevTools
│   ├── Error tracking
│   └── Performance profiling
└── Package Management
    ├── npm/yarn basics
    ├── Dependency management
    ├── Version control
    └── npm scripts
```

### 1.3 Web Technologies
**Wikidata Reference**: Q11014 (Web), Q34770 (HTTP)

```
├── HTML5
│   ├── Semantic markup
│   ├── Canvas element
│   ├── Audio/video elements
│   └── Data attributes
├── CSS3
│   ├── Flexbox & Grid layout
│   ├── Animations & transitions
│   ├── Transforms
│   └── Responsive design
├── HTTP/Networking
│   ├── REST APIs
│   ├── JSON data format
│   ├── CORS & security
│   └── WebSockets & real-time
└── Version Control (Git)
    ├── Repository management
    ├── Branching & merging
    ├── Collaboration workflows
    └── GitHub/GitLab
```

---

## Tier 2: Creative Coding Skills

### 2.1 p5.js (Processing.js)
**Wikidata Reference**: Q161453 (Processing), Q2005 (JavaScript)

```
├── Graphics Fundamentals
│   ├── Canvas setup & sizing
│   ├── Drawing primitives (rect, circle, line, polygon)
│   ├── Color theory (RGB, HSB, transparency)
│   ├── Coordinate systems & transformations
│   └── Layering & z-index
├── Interactive Graphics
│   ├── Mouse tracking (mouseX, mouseY)
│   ├── Keyboard input
│   ├── Touch events
│   └── Animation loops (frameCount, deltaTime)
├── Advanced Drawing
│   ├── Custom shapes & paths
│   ├── Bezier curves
│   ├── Matrix transformations
│   ├── Blend modes
│   └── Textures & images
├── Data Visualization
│   ├── Mapping data to visual properties
│   ├── Scales & normalization
│   ├── Charts & graphs
│   ├── Dimension reduction
│   └── Interactive dashboards
└── Libraries & Extensions
    ├── p5.sound (audio analysis)
    ├── ml5.js (machine learning)
    ├── 3D graphics (WEBGL mode)
    └── Community libraries
```

### 2.2 Generative Art & Algorithmic Design
**Wikidata Reference**: Q1817047 (Generative Art), Q9143 (Algorithm)

```
├── Random & Noise
│   ├── Randomization strategies
│   ├── Perlin noise (organic patterns)
│   ├── Simplex noise
│   ├── Seeding for reproducibility
│   └── Probability distributions
├── Fractals & Recursion
│   ├── Recursive drawing
│   ├── Fractal dimensions
│   ├── Self-similarity
│   ├── L-systems (formal grammars)
│   └── Space-filling curves
├── Cellular Automata
│   ├── Rule-based systems (Conway's Life)
│   ├── Wolfram automata
│   ├── Multi-agent systems
│   ├── Emergence & complexity
│   └── Lenia (continuous CA)
├── Evolutionary Systems
│   ├── Genetic algorithms
│   ├── Natural selection simulation
│   ├── Fitness functions
│   ├── Population dynamics
│   └── Neuroevolution
├── Particle Systems
│   ├── Boid flocking (Reynolds)
│   ├── Force fields & attraction
│   ├── Physics simulation
│   ├── Collision detection
│   └── Swarm intelligence
└── Pattern Generation
    ├── Symmetry & tessellation
    ├── Tiling patterns
    ├── Wave functions & interference
    ├── Procedural texture generation
    └── Aperiodic tilings
```

### 2.3 Motion & Animation
**Wikidata Reference**: Q11019 (Animation)

```
├── Easing & Timing
│   ├── Easing functions (linear, ease-in-out)
│   ├── Interpolation (lerp, smooth-step)
│   ├── Bezier curves for motion paths
│   └── Timing functions
├── Physics-Based Animation
│   ├── Velocity & acceleration
│   ├── Forces (gravity, friction, drag)
│   ├── Spring simulation
│   ├── Rotation & angular velocity
│   └── Collision response
├── Keyframe Animation
│   ├── Timeline management
│   ├── Keyframe interpolation
│   ├── Sequencing
│   └── Playback control
└── Advanced Techniques
    ├── Procedural animation
    ├── Motion capture integration
    ├── Skeletal animation
    └── Inverse kinematics
```

---

## Tier 3: Audio & Sound Design

### 3.1 Audio Synthesis
**Wikidata Reference**: Q33060 (Sound), Q188860 (Music)

```
├── Sound Fundamentals
│   ├── Frequency & pitch (Hz)
│   ├── Amplitude & loudness (dB)
│   ├── Waveforms (sine, square, sawtooth)
│   ├── Harmonics & overtones
│   └── Timbre characteristics
├── Synthesis Techniques
│   ├── Oscillator design
│   ├── Additive synthesis
│   ├── Subtractive synthesis
│   ├── FM synthesis
│   ├── Wavetable synthesis
│   └── Granular synthesis
├── Audio Effects
│   ├── Delay (echo, feedback)
│   ├── Reverb (spatial simulation)
│   ├── Modulation (tremolo, vibrato, chorus)
│   ├── Filtering (EQ, resonant filters)
│   ├── Distortion & overdrive
│   └── Compression & dynamics
├── Envelope Shaping
│   ├── ADSR (Attack, Decay, Sustain, Release)
│   ├── LFO (Low Frequency Oscillator)
│   ├── Envelope automation
│   └── Dynamic range control
└── Audio Analysis
    ├── FFT (Fast Fourier Transform)
    ├── Frequency domain analysis
    ├── Real-time spectrum analysis
    ├── Beat detection
    └── Audio feature extraction
```

### 3.2 Web Audio API
**Wikidata Reference**: Q2005 (JavaScript), Q33060 (Sound)

```
├── Audio Context & Nodes
│   ├── AudioContext initialization
│   ├── Oscillator nodes
│   ├── Gain (volume) control
│   ├── Analyser nodes
│   └── Filter nodes
├── Audio Routing
│   ├── Signal chain patching
│   ├── Bus/submix architecture
│   ├── Multi-channel audio
│   └── Sidechain processing
├── Real-Time Processing
│   ├── ScriptProcessorNode
│   ├── AudioWorklet
│   ├── Sample-accurate scheduling
│   └── Latency management
└── Interactive Audio
    ├── User input → sound mapping
    ├── Gesture-to-audio synthesis
    ├── Responsive audio feedback
    └── Sonification techniques
```

### 3.3 Music Theory Integration
**Wikidata Reference**: Q638 (Music), Q11034 (Music Theory)

```
├── Pitch Systems
│   ├── Notes & octaves
│   ├── Chromatic scale
│   ├── Scales & modes
│   ├── Just intonation
│   └── Microtonal systems
├── Harmony & Chords
│   ├── Chord construction (triads, extensions)
│   ├── Voice leading
│   ├── Harmonic function
│   ├── Chord progressions
│   └── Neo-Riemannian transformations
├── Rhythm & Timing
│   ├── Beat & tempo (BPM)
│   ├── Time signatures
│   ├── Polyrhythm
│   ├── Swing & groove
│   └── Timing quantization
├── Composition Techniques
│   ├── Melody generation
│   ├── Fugal techniques
│   ├── Minimalism
│   ├── Serialism & 12-tone
│   └── Generative composition
└── Audio-Visual Synchronization
    ├── Tempo-locked animation
    ├── Beat-driven visuals
    ├── Spectral visualization
    └── Synaesthetic mapping
```

---

## Tier 4: Advanced Integration

### 4.1 Data Visualization
**Wikidata Reference**: Q178141 (Data Visualization)

```
├── Design Principles
│   ├── Gestalt principles (grouping, proximity)
│   ├── Pre-attentive processing
│   ├── Color theory for data
│   ├── Typography in visualization
│   └── Information hierarchy
├── Visualization Techniques
│   ├── Scatter plots & trends
│   ├── Networks & graphs
│   ├── Hierarchical data (treemaps, sunbursts)
│   ├── Temporal visualization (timelines)
│   ├── Spatial data (maps, 3D)
│   └── High-dimensional data
├── Interactive Exploration
│   ├── Filtering & selection
│   ├── Zooming & panning
│   ├── Linked views
│   ├── Drill-down navigation
│   └── Export & sharing
└── Tools & Libraries
    ├── D3.js (data-driven documents)
    ├── Observable notebooks
    ├── Plotly.js
    └── Three.js (3D visualization)
```

### 4.2 Machine Learning for Creative Code
**Wikidata Reference**: Q11019 (Machine Learning)

```
├── Fundamentals
│   ├── Supervised learning concepts
│   ├── Classification & regression
│   ├── Training & evaluation
│   └── Overfitting prevention
├── Neural Networks
│   ├── Perceptrons & layers
│   ├── Backpropagation
│   ├── Activation functions
│   ├── Convolutional networks (CNN)
│   └── Recurrent networks (RNN/LSTM)
├── Creative Applications
│   ├── Style transfer
│   ├── Image generation (GANs)
│   ├── Music generation
│   ├── Pose estimation
│   └── Gesture recognition
└── Accessible Tools
    ├── ml5.js (easy access to pre-trained models)
    ├── TensorFlow.js
    ├── Teachable Machine
    └── RunwayML
```

### 4.3 Real-Time Rendering (3D)
**Wikidata Reference**: Q188860 (3D Graphics), Q7397 (WebGL)

```
├── 3D Graphics Fundamentals
│   ├── Coordinate systems (x, y, z)
│   ├── Transformations (translate, rotate, scale)
│   ├── Perspective & projection
│   ├── Lighting models
│   └── Material properties
├── WebGL Basics
│   ├── Shaders (vertex, fragment)
│   ├── Buffer objects
│   ├── Texture mapping
│   ├── Normal mapping
│   └── Shadow rendering
├── Three.js Library
│   ├── Scene setup
│   ├── Cameras & views
│   ├── Geometry & materials
│   ├── Lighting
│   └── Post-processing effects
└── Advanced Techniques
    ├── Ray casting & intersection
    ├── Physics simulation (Cannon.js)
    ├── Particle effects
    ├── Procedural generation
    └── GPU computing
```

### 4.4 Performance Optimization
**Wikidata Reference**: Q189119 (Computational Complexity), Q189189 (Algorithm Efficiency)

```
├── Profiling & Analysis
│   ├── Chrome DevTools
│   ├── Frame rate monitoring
│   ├── Memory profiling
│   ├── CPU flame graphs
│   └── Network waterfall charts
├── Optimization Techniques
│   ├── Reduce draw calls
│   ├── Level of detail (LOD)
│   ├── Caching strategies
│   ├── Algorithm selection
│   └── Parallelization
├── Code Optimization
│   ├── Function call overhead
│   ├── Loop optimization
│   ├── Memory allocation patterns
│   ├── Garbage collection tuning
│   └── JIT compilation awareness
└── Mobile Optimization
    ├── Touch performance
    ├── Battery considerations
    ├── Network constraints
    └── Device capability detection
```

---

## Tier 5: Artistic & Conceptual Skills

### 5.1 Computational Aesthetics
**Wikidata Reference**: Q735 (Aesthetics), Q9143 (Algorithm)

```
├── Artistic Principles
│   ├── Composition & balance
│   ├── Contrast & harmony
│   ├── Scale & proportion
│   ├── Rhythm & repetition
│   └── Emphasis & focal points
├── Conceptual Frameworks
│   ├── Generative systems thinking
│   ├── Emergence & complexity
│   ├── Chaos & order
│   ├── Determinism vs randomness
│   └── Meaning through limitation
├── Aesthetic Analysis
│   ├── Beauty & ugliness
│   ├── Novelty vs familiarity
│   ├── Pattern recognition
│   └── Emotional resonance
└── Creative Process
    ├── Ideation techniques
    ├── Iteration & refinement
    ├── Feedback integration
    ├── Conceptual development
    └── Documentation & presentation
```

### 5.2 Digital Art History
**Wikidata Reference**: Q12982 (Art), Q11407 (Digital Art)

```
├── Computational Art Pioneers
│   ├── Frieder Nake, Georg Nees (1960s)
│   ├── John Whitney (analog computation)
│   ├── Ben Laposky (Oscillons)
│   ├── Oskar Fischinger (abstract film)
│   └── Modern artists (Bees & Bombs, etc.)
├── Algorithmic Art Movements
│   ├── Op Art
│   ├── Systems Art
│   ├── Kinetic Art
│   ├── Net Art
│   └── Bio Art
├── Contemporary Practices
│   ├── Processing community
│   ├── Live coding
│   ├── Demoscene aesthetics
│   ├── Shader art
│   └── Interactive installations
└── Curated Resources
    ├── Museum collections (Ars Electronica)
    ├── Festival landscapes (ISEA, Transmediale)
    ├── Artist statements & manifestos
    └── Critical discourse
```

### 5.3 Sonic Art & Audiovisual Composition
**Wikidata Reference**: Q188860 (Music), Q11407 (Digital Art), Q188860 (Sound Art)

```
├── Sound Sculpture
│   ├── Spatial audio
│   ├── Installation art
│   ├── Site-specific sound
│   ├── Immersive environments
│   └── Ambisonics & spatial audio
├── Audiovisual Composition
│   ├── Score notation (traditional & graphic)
│   ├── Synaesthetic mapping (sound→visuals)
│   ├── Synchronized performance
│   ├── Responsive systems
│   └── Cross-modal perception
├── Live Performance
│   ├── Real-time synthesis
│   ├── Improvisation frameworks
│   ├── Performer-computer interaction
│   ├── Gesture control
│   └── Audience participation
└── Experimental Practices
    ├── Indeterminacy (John Cage)
    ├── Chance operations
    ├── Constraint-based composition
    ├── Emergence from simple rules
    └── Process art philosophy
```

---

## Tier 6: Collaboration & Community

### 6.1 Open Source & Collaboration
**Wikidata Reference**: Q1090 (Free Software), Q101566 (Open Source)

```
├── Open Source Culture
│   ├── Licensing (MIT, GPL, CC)
│   ├── Community norms
│   ├── Contribution guidelines
│   ├── Code of conduct
│   └── Sustainable projects
├── Collaborative Development
│   ├── Code review practices
│   ├── Issue tracking
│   ├── Documentation standards
│   ├── Release management
│   └── User support
├── Community Building
│   ├── Mentorship
│   ├── Teaching & workshops
│   ├── Event organization
│   ├── Documentation creation
│   └── Advocacy & evangelism
└── Ecosystem Participation
    ├── Contributing to projects
    ├── Maintaining libraries
    ├── Creating tutorials
    ├── Building plugins/extensions
    └── Cross-project collaboration
```

### 6.2 Creative Communities & Networks
**Wikidata Reference**: Q15127141 (Community), Q16334295 (Creative Community)

```
├── Institutional Contexts
│   ├── Art schools & programs
│   ├── Research labs & institutes
│   ├── Museums & galleries
│   ├── Festivals & conferences
│   └── Online communities
├── Knowledge Exchange
│   ├── Workshops & courses
│   ├── Mentorship programs
│   ├── Code sharing platforms (GitHub)
│   ├── Documentation wikis
│   └── Social media engagement
├── Network Development
│   ├── Professional connections
│   ├── Collaboration initiation
│   ├── Peer feedback
│   ├── Cross-disciplinary pollination
│   └── Funding opportunities
└── Public Engagement
    ├── Artist talks & presentations
    ├── Interactive installations
    ├── Educational outreach
    ├── Media coverage
    └── Social impact
```

---

## Skill Map: Gray Area Creative Code Immersive

### Course Structure (Typical 8-12 Week Program)

**Week 1-2: Foundations**
- 1.1 Programming Fundamentals
- 1.2 JavaScript
- 1.3 Web Technologies (HTML/CSS/Git)

**Week 3-4: Creative Coding Basics**
- 2.1 p5.js Introduction
- 2.2 Simple Generative Art (random, noise, recursion)
- 2.3 Basic Animation

**Week 5-6: Generative Systems**
- 2.2 Cellular Automata, L-Systems
- 2.2 Particle Systems & Physics
- 5.1 Computational Aesthetics (concepts)

**Week 7-8: Data & Interactivity**
- 4.1 Data Visualization
- 2.1 Interactive Graphics with p5.js
- User input integration

**Week 9-10: Advanced Topics**
- 3.1 + 3.2 Audio Synthesis (p5.sound, Web Audio API)
- 4.3 3D Graphics (Three.js or p5.WEBGL)
- 3.3 Audio-Visual Synchronization

**Week 11-12: Projects & Community**
- 5.2 Digital Art History & Inspiration
- 6.1 + 6.2 Community Engagement
- Final projects, presentations, reflections

---

## Integration with Music-Topos Toolkit

### New Capabilities
The music-topos system adds:

```
Traditional Gray Area Curriculum
    + Audio Synthesis & Effects (3.1, 3.2, 3.3)
    + Alife Visualization (2.2: CA, Particles, Lenia)
    + Audio-Visual Composition (5.3)
    + Mathematical Music Theory (3.3 extended)
    = Complete Audio-Visual Generative Art System
```

### Module Mapping
```
music-topos/lib/audio_synthesis.rb
  → Skills 3.1, 3.2, 3.3

music-topos/lib/audio_effects.rb
  → Skills 3.1 (Effects)

music-topos/lib/alife_visual_synthesis.rb
  → Skills 2.2 (CA, Particles), 5.1, 5.3

gray_area + music_topos
  → Complete creative coding + sound art curriculum
```

---

## Competency Levels

### Beginner (Weeks 1-4)
- Understand programming concepts
- Create simple p5.js sketches
- Manipulate HTML/CSS/JavaScript
- Read & modify existing code

### Intermediate (Weeks 5-8)
- Design & implement generative algorithms
- Integrate user interaction
- Understand data visualization
- Create aesthetic compositions

### Advanced (Weeks 9-12)
- Synthesize audio with code
- Integrate multiple media types
- Optimize performance
- Develop artistic vision & conceptual framework

### Master (Post-program)
- Contribute to open source projects
- Mentor others
- Create innovative work
- Push boundaries of the medium

---

## Assessment Criteria

1. **Technical Competency**: Can they implement the concepts?
2. **Aesthetic Judgment**: Do they understand computational aesthetics?
3. **Creative Vision**: Do they have something unique to say?
4. **Collaboration**: Can they work with others effectively?
5. **Reflection**: Can they articulate their process & learning?
6. **Community Contribution**: Are they engaged with the broader ecosystem?

---

## References & Resources

### Primary References
- Wikidata entity relationships for skills taxonomy
- p5.js documentation & examples (Lauren McCarthy)
- Creative Coding curriculum design patterns
- Generative Art principles (various practitioners)
- Music theory & audio synthesis (standard texts)

### Related Wikidata Entities
- Q2005 (JavaScript)
- Q161453 (Processing)
- Q11019 (Animation)
- Q1817047 (Generative Art)
- Q178141 (Data Visualization)
- Q11407 (Digital Art)
- Q188860 (Music)
- Q638 (Sound)
- Q735 (Aesthetics)
- Q9143 (Algorithm)
- Q1090 (Free Software)

---

**Document Created**: 2025-12-24  
**Status**: Complete Curriculum Skills Enumeration  
**Integration**: Ready for Gray Area Foundation for the Arts
