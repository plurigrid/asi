# Music Topos Framework - Examples and Tutorials

Complete examples showing how to use the Music Topos Framework for analysis and composition.

---

## Table of Contents

1. [Quick Start Examples](#quick-start-examples)
2. [Category-Specific Analysis](#category-specific-analysis)
3. [Real Music Analysis](#real-music-analysis)
4. [API Usage Examples](#api-usage-examples)
5. [Advanced Use Cases](#advanced-use-cases)

---

## Quick Start Examples

### Example 1: Basic Chord Progression

```ruby
require_relative 'lib/music_topos_framework'
require_relative 'lib/chord'

framework = MusicToposFramework.new

# Simple I-IV-V-I progression
chords = [
  Chord.from_notes(['C', 'E', 'G']),
  Chord.from_notes(['F', 'A', 'C']),
  Chord.from_notes(['G', 'B', 'D']),
  Chord.from_notes(['C', 'E', 'G'])
]

# Analyze through all 8 categories
analysis = framework.analyze_progression(chords, key: 'C')

# Access specific category results
harmonic_functions = analysis[:analyses_by_category][5][:analysis][:functions]
puts harmonic_functions.inspect
# => [:tonic, :subdominant, :dominant, :tonic]
```

### Example 2: Validate Cross-Category Coherence

```ruby
# After analyzing (see Example 1)
coherence = framework.validate_coherence(analysis)

if coherence[:coherent]
  puts "✓ All categories agree - progression is coherent"
else
  puts "✗ Categories disagree - check validations"
  puts coherence[:validations]
end
```

### Example 3: Single Category Analysis

```ruby
# Analyze only Category 5 (Harmonic Function)
category_5_world = framework.world(5)

# The world object contains the specific analysis logic
# for that category
```

---

## Category-Specific Analysis

### Category 4: Group Theory (Pitch Permutations)

**Use when**: Analyzing pitch transformations, transpositions, inversions

```ruby
# All chords are permutations in pitch space (Z/12Z)
# Example: C Major [0, 4, 7] → F Major [5, 9, 0]
# This is a transposition by +5 semitones

# The framework validates:
# - Closure: Compositions of transpositions yield transpositions
# - Triangle inequality: Shortest path through pitch space
```

### Category 5: Harmonic Function (Tonic/Subdominant/Dominant)

**Use when**: Understanding classical harmonic analysis, cadences

```ruby
# T→S→D→T cycle captures harmonic movement
# Example: I-IV-V-I = T→S→D→T

# Three valid cadences:
# - Authentic (V→I): Strongest resolution
# - Plagal (IV→I): Weaker, "amen cadence"
# - Deceptive (V→vi): Surprise resolution

# The framework validates:
# - Functional progressions follow T→S→D cycle
# - Cadences provide harmonic closure
```

### Category 6: Modulation (Key Changes)

**Use when**: Analyzing key changes, transpositions, modulation techniques

```ruby
# Key relationships form Circle of Fifths
# C Major is distance 1 from: G Major, F Major
# C Major is distance 2 from: D Major, Bb Major

# Modulation techniques:
# - Direct: Abrupt key change
# - Pivot chord: Shared chord between keys
# - Secondary dominant: V of new key

# The framework validates:
# - Transposition preserves interval structure
# - Key affinity based on common pitches
```

### Category 7: Voice Leading (SATB)

**Use when**: Composing 4-part harmony, analyzing classical music

```ruby
# SATB = Soprano, Alto, Tenor, Bass
# Range constraints:
# - Soprano: C4-C6 (60-84 MIDI)
# - Alto: G3-G5 (55-79 MIDI)
# - Tenor: C3-C5 (48-72 MIDI)
# - Bass: E2-E4 (40-64 MIDI)

# Rules:
# - No voice crossing
# - No parallel perfect fifths/octaves
# - Minimize total motion

# The framework validates:
# - Triangle inequality: d(chord1, chord2) ≤ sum of voice motions
```

### Category 8: Progressions (Harmonic Closure)

**Use when**: Analyzing complete progressions, harmonic sequences

```ruby
# Common progressions:
# - I-IV-V-I (plagal + authentic)
# - vi-IV-V-I (modern pop standard)
# - ii-V-I (jazz foundation)
# - I-V-vi-IV (axis progression)

# The framework validates:
# - Progressions form harmonic trajectories
# - Cadences provide closure
```

### Category 9: Structure (Phrases and Tonality)

**Use when**: Analyzing phrases, periods, tonal closure

```ruby
# Structural levels:
# - Phrase: 4-8 measures
# - Period: 8-16 measures (two phrases)
# - Section: Multiple periods
# - Movement: Multiple sections

# Cadence hierarchy:
# - Authentic (V→I): Strong, final closure
# - Plagal (IV→I): Weak, "Amen"
# - Half (x→V): Opening or pause
# - Deceptive (V→vi): Surprise
```

### Category 10: Form (Large-Scale Structure)

**Use when**: Analyzing complete pieces, form types

```ruby
# Standard forms:
# - Binary (AB or ABA')
# - Ternary (ABA)
# - Sonata (Exposition-Development-Recapitulation)
# - Rondo (ABACA...)
# - Variation

# Each form provides coherence through:
# - Repetition (sections repeat)
# - Contrast (new material introduced)
# - Return (original material returns)
```

### Category 11: Spectral Analysis (Timbre and Harmonics)

**Use when**: Analyzing tone color, harmonic content

```ruby
# Spectral properties:
# - Centroid: Center of mass of spectrum (brightness)
# - Spread: Dispersion of partials (complexity)
# - Flatness: Noise-like vs. harmonic (tonality)

# Timbre examples:
# - Pure sine: Only fundamental (spectrum = 1 peak)
# - Clarinet: Odd harmonics (complex spectrum)
# - Trumpet: Many harmonics (bright spectrum)
# - Cymbal: Noise-like (flat spectrum)
```

---

## Real Music Analysis

### Run Included Examples

```bash
# Bach chorale analysis (all 8 categories)
ruby examples/analyze_bach_chorale.rb

# Jazz standard analysis (ii-V-I)
ruby examples/jazz_ii_v_i_analysis.rb
```

### Analyze Your Own Music

1. Identify chord progression (Roman numerals)
2. Convert to note names (e.g., "C E G" for C Major)
3. Use framework to analyze:

```ruby
framework = MusicToposFramework.new
chords = [Chord.from_notes(['C', 'E', 'G']), ...]
analysis = framework.analyze_progression(chords, key: 'C')
```

4. Examine results for each of 8 categories
5. Look for patterns and relationships

---

## API Usage Examples

### Using REST API

All examples assume API is running: `ruby api/music_topos_server.rb`

#### Example 1: cURL - Basic Analysis

```bash
curl -X POST http://localhost:4567/analyze/progression \
  -H "Content-Type: application/json" \
  -d '{
    "progressions": [
      ["C", "E", "G"],
      ["G", "B", "D"],
      ["C", "E", "G"]
    ],
    "key": "C"
  }'
```

#### Example 2: Python - Complete Workflow

```python
import requests
import json

API = 'http://localhost:4567'

# Get framework status
status = requests.get(f'{API}/status').json()
print(f"Framework: {status['framework']}")

# Get available categories
categories = requests.get(f'{API}/categories').json()
print(f"Categories: {categories['total_categories']}")

# Analyze a progression
progression = {
    'progressions': [
        ['C', 'E', 'G'],
        ['F', 'A', 'C'],
        ['G', 'B', 'D'],
        ['C', 'E', 'G']
    ],
    'key': 'C'
}

response = requests.post(
    f'{API}/analyze/progression',
    json=progression
)

analysis = response.json()
if analysis['success']:
    for cat in range(4, 12):
        cat_analysis = analysis['analyses_by_category'][str(cat)]
        print(f"\nCategory {cat}: {cat_analysis['analysis']['category']}")
```

#### Example 3: JavaScript - Interactive Dashboard

See `public/index.html` for complete interactive example with:
- Real-time API interaction
- 6 pre-built examples
- 8-category visualization
- Coherence validation

---

## Advanced Use Cases

### Use Case 1: Composition Generation

```ruby
# Generate a progression that follows functional harmony rules
# 1. Start with T (tonic)
# 2. Move to S (subdominant)
# 3. Move to D (dominant)
# 4. Resolve to T (tonic)

# Validate with framework
framework = MusicToposFramework.new
# ... analyze generated progression
```

### Use Case 2: Music Analysis Pipeline

```ruby
# Analyze complete piece section by section
File.readlines('progression.txt').each do |line|
  chords = parse_chord_line(line)
  analysis = framework.analyze_progression(chords)

  if framework.validate_coherence(analysis)[:coherent]
    puts "✓ Section coherent"
  else
    puts "⚠ Section needs review"
  end
end
```

### Use Case 3: Multi-Key Analysis

```ruby
# Analyze same progression in different keys
progression = [['C', 'E', 'G'], ['F', 'A', 'C'], ['G', 'B', 'D']]

['C', 'G', 'D', 'A', 'E'].each do |key|
  analysis = framework.analyze_progression(progression, key: key)
  cadence = analysis[:analyses_by_category][5][:analysis][:cadence]
  puts "In #{key} Major: #{cadence} cadence"
end
```

### Use Case 4: Educational Tool

```ruby
# Create lessons for music students
class MusicLesson
  def initialize(framework)
    @framework = framework
  end

  def teach_authentic_cadence
    v = Chord.from_notes(['G', 'B', 'D'])
    i = Chord.from_notes(['C', 'E', 'G'])

    analysis = @framework.analyze_progression([v, i], key: 'C')

    puts "The V-I progression is called an authentic cadence"
    puts "Harmonic functions: #{analysis[:analyses_by_category][5][:analysis][:functions]}"
    puts "Cadence type: #{analysis[:analyses_by_category][5][:analysis][:cadence]}"
  end
end
```

---

## Troubleshooting Examples

### Example: Unexpected Analysis Result

```ruby
# If a progression seems wrong, check each category separately
progression = [['C', 'E', 'G'], ['B', 'D', 'F#']]

analysis = framework.analyze_progression(progression, key: 'C')

# Check each category
(4..11).each do |cat|
  result = analysis[:analyses_by_category][cat][:analysis]
  puts "Category #{cat}: #{result}"
end

# Compare with coherence validation
coherence = framework.validate_coherence(analysis)
puts "Coherent: #{coherence[:coherent]}"
```

### Example: Voice Leading Issues

```ruby
# Analyze voice leading specifically
voice_analysis = analysis[:analyses_by_category][7][:analysis]

puts "Voice motion: #{voice_analysis[:voice_motion_analysis]}"
puts "Valid voice leading: #{voice_analysis[:chord_count]} chords analyzed"

# If issues detected, check range constraints
# Each voice must stay within its SATB range
```

---

## Performance Optimization

### For Large-Scale Analysis

```ruby
# Analyze progressions in batches
progressions = File.readlines('many_progressions.txt')

progressions.each_with_index do |line, idx|
  chords = parse_line(line)
  analysis = framework.analyze_progression(chords)

  # Save results every 100 progressions
  if (idx + 1) % 100 == 0
    save_results(analysis)
    puts "Processed #{idx + 1} progressions"
  end
end
```

---

## Further Learning

- Read [MUSIC_TOPOS_PAPER.md](MUSIC_TOPOS_PAPER.md) for mathematical foundations
- Review test files for more usage patterns
- Explore [API.md](API.md) for endpoint details
- Check [README.md](README.md) for quick start

---

**Last Updated**: December 2025
**Framework Version**: 1.0.0
